
/// A handle to an object in the arena.
/// It is essentially an index into the arena's storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Handle(u32);

impl Handle {
    #[inline(always)]
    pub const fn index(&self) -> usize {
        self.0 as usize
    }

    /// Creates a handle from a raw index.
    /// Unsafe because it doesn't check if the index is valid.
    pub const unsafe fn from_raw(idx: u32) -> Self {
        Handle(idx)
    }
}

/// A slot in the arena.
enum Slot<T> {
    /// An occupied slot containing a value.
    Occupied(T),
    /// A forwarding pointer to the new location of the object (used during GC).
    Forwarded(Handle),
}

impl<T> Clone for Slot<T> {
    fn clone(&self) -> Self {
        match self {
            Slot::Forwarded(h) => Slot::Forwarded(*h),
            Slot::Occupied(_) => panic!("Cannot clone occupied slot!"),
        }
    }
}

const CHUNK_SIZE: usize = 256 * 1024;

/// A simple semi-space copying collector.
pub struct Arena<T> {
    chunks: Vec<Vec<Slot<T>>>,
    // Bump pointer state
    current_chunk: usize,
    
    // Fast allocation pointers (pointers into the current chunk's buffer)
    alloc_ptr: *mut Slot<T>,
    alloc_limit: *mut Slot<T>,
    chunk_base: *mut Slot<T>, // To calculate slot index

    // Statistics
    pub allocated_objects: usize,
    pub next_gc_threshold: usize,
}

pub trait GcVisitor {
    fn visit(&mut self, handle: &mut Handle);
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            chunks: Vec::new(),
            current_chunk: 0,
            alloc_ptr: std::ptr::null_mut(),
            alloc_limit: std::ptr::null_mut(),
            chunk_base: std::ptr::null_mut(),
            allocated_objects: 0,
            next_gc_threshold: 4 * 1024 * 1024, // 4MB start
        }
    }
    
    // Internal: expands the arena by adding a new chunk
    #[inline(never)]
    fn expand(&mut self) {
        if let Some(chunk) = self.chunks.last_mut() {
            unsafe { chunk.set_len(CHUNK_SIZE); }
        }

        // Use uninitialized memory to avoid overhead
        let mut new_chunk = Vec::with_capacity(CHUNK_SIZE);
        
        self.chunk_base = new_chunk.as_mut_ptr();
        self.chunks.push(new_chunk);
        self.current_chunk = self.chunks.len() - 1;

        self.alloc_ptr = self.chunk_base;
        unsafe {
            self.alloc_limit = self.chunk_base.add(CHUNK_SIZE);
        }
    }

    /// Allocates a new object in the arena and returns a handle to it.
    #[inline(always)]
    pub fn alloc(&mut self, value: T) -> Handle {
        if self.alloc_ptr >= self.alloc_limit {
            self.expand();
        }
        
        unsafe {
            std::ptr::write(self.alloc_ptr, Slot::Occupied(value));
            let slot_idx = self.alloc_ptr.offset_from(self.chunk_base) as u32;
            let handle = Handle::new(self.current_chunk as u32, slot_idx);
            
            self.alloc_ptr = self.alloc_ptr.add(1);
            self.allocated_objects += 1;
            handle
        }
    }

    pub fn alloc_contiguous<F>(&mut self, count: usize, mut generator: F) -> Handle 
    where F: FnMut(usize, Handle) -> T
    {
        unsafe {
            if self.alloc_ptr.add(count) > self.alloc_limit {
                self.expand();
                if count > CHUNK_SIZE {
                    panic!("Allocation too large for contiguous block");
                }
            }
            
            let start_idx = self.alloc_ptr.offset_from(self.chunk_base) as u32;
            let start_handle = Handle::new(self.current_chunk as u32, start_idx);
            
            for i in 0..count {
                let current_handle = Handle::new(self.current_chunk as u32, start_idx + i as u32);
                let val = generator(i, current_handle);
                std::ptr::write(self.alloc_ptr.add(i), Slot::Occupied(val));
            }
            
            self.alloc_ptr = self.alloc_ptr.add(count);
            self.allocated_objects += count;
            
            start_handle
        }
    }

    /// Gets a reference to an object.
    #[inline(always)]
    pub fn get(&self, handle: Handle) -> Option<&T> {
        let (chunk_idx, slot_idx) = handle.decode();
        
        // Safety: We assume handles are valid and point to allocated memory.
        if let Some(chunk) = self.chunks.get(chunk_idx) {
             unsafe {
                 let ptr = chunk.as_ptr().add(slot_idx);
                 if let Slot::Occupied(value) = &*ptr {
                     return Some(value);
                 }
             }
        }
        None
    }

    /// Gets a mutable reference to an object.
    #[inline(always)]
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        let (chunk_idx, slot_idx) = handle.decode();
        
        if let Some(chunk) = self.chunks.get_mut(chunk_idx) {
            unsafe {
                 let ptr = chunk.as_mut_ptr().add(slot_idx);
                 if let Slot::Occupied(value) = &mut *ptr {
                     return Some(value);
                 }
            }
        }
        None
    }
    
    // Unsafe access remains similar but uses decode
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, handle: Handle) -> &T {
        let (chunk_idx, slot_idx) = handle.decode();
        let chunk = self.chunks.get_unchecked(chunk_idx);
        match &*chunk.as_ptr().add(slot_idx) {
            Slot::Occupied(value) => value,
            _ => std::hint::unreachable_unchecked(),
        }
    }

    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, handle: Handle) -> &mut T {
        let (chunk_idx, slot_idx) = handle.decode();
        let chunk = self.chunks.get_unchecked_mut(chunk_idx);
        match &mut *chunk.as_mut_ptr().add(slot_idx) {
            Slot::Occupied(value) => value,
            _ => std::hint::unreachable_unchecked(),
        }
    }
}

impl<T> Drop for Arena<T> {
    fn drop(&mut self) {
        if !self.alloc_ptr.is_null() && !self.chunks.is_empty() {
             let used = unsafe { self.alloc_ptr.offset_from(self.chunk_base) as usize };
             unsafe {
                 self.chunks.last_mut().unwrap().set_len(used);
             }
        }
    }
}

impl Handle {
    #[inline(always)]
    fn new(chunk: u32, slot: u32) -> Self {
        Handle( (chunk << 20) | slot )
    }
    
    #[inline(always)]
    fn decode(&self) -> (usize, usize) {
        ((self.0 >> 20) as usize, (self.0 & 0xFFFFF) as usize)
    }

    #[inline(always)]
    pub fn offset(&self, n: usize) -> Self {
        let (c, s) = self.decode();
        Handle::new(c as u32, (s + n) as u32)
    }
}

/// Trait for objects that can be traced by the garbage collector.
pub trait Trace<T> {
    fn trace(&mut self, visitor: &mut impl GcVisitor);
}

// Copying Collector Implementation
impl<T> Arena<T> 
where T: Trace<T> + Clone
{
    pub fn collect_from_roots(&mut self, root_visitor: impl FnOnce(&mut CopyingVisitor<T>)) {
        if !self.alloc_ptr.is_null() && !self.chunks.is_empty() {
             let used = unsafe { self.alloc_ptr.offset_from(self.chunk_base) as usize };
             unsafe {
                 self.chunks.last_mut().unwrap().set_len(used);
             }
        }

        // Take ownership of old chunks to avoid self-borrow issues
        let mut old_chunks = std::mem::take(&mut self.chunks);
        
        let mut visitor = CopyingVisitor {
            new_chunks: Vec::new(),
            current_chunk: 0,
            next_slot: CHUNK_SIZE,
            // Allocator state for visitor
            alloc_ptr: std::ptr::null_mut(),
            alloc_limit: std::ptr::null_mut(),
            chunk_base: std::ptr::null_mut(),
            
            old_chunks: &mut old_chunks,
            gray_queue: Vec::new(),
        };
        
        // 1. Visit Roots (moves them to new space and updates handles)
        root_visitor(&mut visitor);
        
        // 2. Process Gray Queue (Trace children of moved objects)
        let mut head = 0;
        while head < visitor.gray_queue.len() {
             let handle = visitor.gray_queue[head];
             head += 1;
             
             // Access the object in NEW space (it's already moved)
             // We need to unsafe access it because of borrow checker rules
             // (visitor holds mutable ref to new_chunks)
             let (c_idx, s_idx) = handle.decode();
             
             // Raw pointer to new_chunks to avoid borrowing visitor
             let new_chunks_ptr = visitor.new_chunks.as_mut_ptr();
             unsafe {
                 let chunk = new_chunks_ptr.add(c_idx);
                 let slot = (*chunk).get_unchecked_mut(s_idx);
                 if let Slot::Occupied(val) = slot {
                     // To avoid borrowing conflicts when tracing `val` (which is inside `visitor.new_chunks`)
                     // while passing `visitor` to `trace`, we clone the value, trace it, and write it back.
                     // This ensures memory safety even if `new_chunks` reallocates.
                     
                     let mut temp_val = val.clone();
                     temp_val.trace(&mut visitor);
                     *val = temp_val;
                 }
             }
        }
        
        // 3. Swap spaces
        // 3. Swap spaces
        self.chunks = visitor.new_chunks;
        self.current_chunk = self.chunks.len().saturating_sub(1);
        
        if let Some(chunk) = self.chunks.last_mut() {
            self.chunk_base = chunk.as_mut_ptr();
            unsafe {
                self.alloc_ptr = self.chunk_base.add(visitor.next_slot);
                self.alloc_limit = self.chunk_base.add(CHUNK_SIZE);
            }
        } else {
            self.alloc_ptr = std::ptr::null_mut();
            self.alloc_limit = std::ptr::null_mut();
            self.chunk_base = std::ptr::null_mut();
        }

        self.allocated_objects = 0; // recalc loop or ignore
        
        // Update threshold
        self.next_gc_threshold = (self.chunks.len() * CHUNK_SIZE * 2).max(4 * 1024 * 1024);
    }
}

pub struct CopyingVisitor<'a, T> {
    new_chunks: Vec<Vec<Slot<T>>>,
    current_chunk: usize,
    next_slot: usize,
    old_chunks: &'a mut Vec<Vec<Slot<T>>>,
    gray_queue: Vec<Handle>,
    
    // Allocator state
    alloc_ptr: *mut Slot<T>,
    alloc_limit: *mut Slot<T>,
    chunk_base: *mut Slot<T>,
}

impl<'a, T: Clone> CopyingVisitor<'a, T> {
    #[inline(never)]
    fn expand(&mut self) {
        if let Some(chunk) = self.new_chunks.last_mut() {
            unsafe { chunk.set_len(CHUNK_SIZE); }
        }

        // Use uninitialized memory to avoid overhead
        let mut new_chunk = Vec::with_capacity(CHUNK_SIZE);
        
        self.chunk_base = new_chunk.as_mut_ptr();
        self.new_chunks.push(new_chunk);
        self.current_chunk = self.new_chunks.len() - 1;

        self.alloc_ptr = self.chunk_base;
        unsafe {
            self.alloc_limit = self.chunk_base.add(CHUNK_SIZE);
        }
    }

    fn alloc_raw(&mut self, value: T) -> Handle {
        if self.alloc_ptr >= self.alloc_limit {
            self.expand();
        }

        unsafe {
            std::ptr::write(self.alloc_ptr, Slot::Occupied(value));
            let slot_idx = self.alloc_ptr.offset_from(self.chunk_base) as u32;
            let handle = Handle::new(self.current_chunk as u32, slot_idx);
            
            self.alloc_ptr = self.alloc_ptr.add(1);
            self.next_slot = slot_idx as usize + 1; // Keep tracking for final state
            handle
        }
    }
}

impl<'a, T: Clone> GcVisitor for CopyingVisitor<'a, T> {
    fn visit(&mut self, handle: &mut Handle) {
        let (c_idx, s_idx) = handle.decode();
        
        // Use raw pointer to bypass borrow checker for old_chunks
        let old_chunks_ptr = self.old_chunks as *mut Vec<Vec<Slot<T>>>;
        
        let slot = unsafe {
            if let Some(chunk) = (*old_chunks_ptr).get_mut(c_idx) {
                 chunk.get_unchecked_mut(s_idx)
            } else {
                return;
            }
        };

         match slot {
             Slot::Occupied(val) => {
                 // Unsafe move: Read value out (effectively memcpy), then overwrite with Forwarded.
                 // This avoids cloning heap-allocated strings/vectors.
                 unsafe {
                     let moved_val = std::ptr::read(val);
                     let new_handle = self.alloc_raw(moved_val);
                     std::ptr::write(slot, Slot::Forwarded(new_handle));
                     *handle = new_handle;
                     self.gray_queue.push(new_handle);
                 }
             },
             Slot::Forwarded(new_handle) => {
                 *handle = *new_handle;
             },
         }
    }
}
