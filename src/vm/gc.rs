
/// A handle to an object in the arena.
/// It is essentially an index into the arena's storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Handle(u32);

impl Handle {
    /// Returns the raw index of the handle.
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
    /// A free slot, pointing to the next free slot.
    Free { next_free: Option<u32> },
    /// An occupied slot containing a value.
    Occupied { value: T, marked: bool },
}

const CHUNK_SIZE: usize = 1024;

/// A simple mark-and-sweep arena allocator with multiple memory chunks.
/// 
/// This allocator stores objects in multiple `Vec` chunks to avoid reallocating
/// a single massive vector and to support better memory usage patterns.
pub struct Arena<T> {
    chunks: Vec<Vec<Slot<T>>>,
    free_head: Option<u32>,
    gray_stack: Vec<u32>,
    // Statistics
    pub allocated_objects: usize,
    pub next_gc_threshold: usize,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            chunks: Vec::new(),
            free_head: None,
            gray_stack: Vec::with_capacity(256),
            allocated_objects: 0,
            next_gc_threshold: 1024 * 1024, // Start with 1MB equivalent (approx)
        }
    }

    fn expand(&mut self) {
        let chunk_idx = self.chunks.len();
        let base = (chunk_idx * CHUNK_SIZE) as u32;
        let mut new_chunk = Vec::with_capacity(CHUNK_SIZE);
        for i in 0..CHUNK_SIZE {
            let next = if i < CHUNK_SIZE - 1 { Some(base + i as u32 + 1) } else { self.free_head };
            new_chunk.push(Slot::Free { next_free: next });
        }
        self.chunks.push(new_chunk);
        self.free_head = Some(base);
    }

    /// Allocates a new object in the arena and returns a handle to it.
    pub fn alloc(&mut self, value: T) -> Handle {
        if self.free_head.is_none() {
            self.expand();
        }

        self.allocated_objects += 1;
        
        let idx = self.free_head.unwrap();
        let chunk_idx = (idx as usize) / CHUNK_SIZE;
        let slot_idx = (idx as usize) % CHUNK_SIZE;

        let next = match &self.chunks[chunk_idx][slot_idx] {
            Slot::Free { next_free } => *next_free,
            _ => unreachable!("Corrupt free list"),
        };
        self.free_head = next;
        self.chunks[chunk_idx][slot_idx] = Slot::Occupied { value, marked: false };
        Handle(idx)
    }

    /// Gets a reference to an object.
    /// Returns None if the handle is invalid or points to a free slot.
    #[inline(always)]
    pub fn get(&self, handle: Handle) -> Option<&T> {
        let idx = handle.index();
        let chunk_idx = idx / CHUNK_SIZE;
        let slot_idx = idx % CHUNK_SIZE;
        
        if let Some(chunk) = self.chunks.get(chunk_idx) {
            if let Some(Slot::Occupied { value, .. }) = chunk.get(slot_idx) {
                return Some(value);
            }
        }
        None
    }

    /// Gets a mutable reference to an object.
    #[inline(always)]
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        let idx = handle.index();
        let chunk_idx = idx / CHUNK_SIZE;
        let slot_idx = idx % CHUNK_SIZE;
        
        if let Some(chunk) = self.chunks.get_mut(chunk_idx) {
            if let Some(Slot::Occupied { value, .. }) = chunk.get_mut(slot_idx) {
                return Some(value);
            }
        }
        None
    }
    
    /// Unsafe access for performance (skips checks).
    /// Use only when you are sure the handle is valid.
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, handle: Handle) -> &T {
        let idx = handle.index();
        let chunk_idx = idx / CHUNK_SIZE;
        let slot_idx = idx % CHUNK_SIZE;
        
        match self.chunks.get_unchecked(chunk_idx).get_unchecked(slot_idx) {
            Slot::Occupied { value, .. } => value,
            _ => std::hint::unreachable_unchecked(),
        }
    }

    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, handle: Handle) -> &mut T {
        let idx = handle.index();
        let chunk_idx = idx / CHUNK_SIZE;
        let slot_idx = idx % CHUNK_SIZE;
        
        match self.chunks.get_unchecked_mut(chunk_idx).get_unchecked_mut(slot_idx) {
            Slot::Occupied { value, .. } => value,
            _ => std::hint::unreachable_unchecked(),
        }
    }
}

/// Trait for objects that can be traced by the garbage collector.
pub trait Trace<T> {
    fn trace(&self, arena: &mut Arena<T>);
}

impl<T> Arena<T> 
where T: Trace<T> 
{
    /// Marks an object as reachable.
    /// This should be called by `Trace` implementations for their children.
    pub fn mark(&mut self, handle: Handle) {
        let idx = handle.index();
        let chunk_idx = idx / CHUNK_SIZE;
        let slot_idx = idx % CHUNK_SIZE;
        
        if let Some(chunk) = self.chunks.get_mut(chunk_idx) {
            if let Some(Slot::Occupied { marked, .. }) = chunk.get_mut(slot_idx) {
                if !*marked {
                    *marked = true;
                    self.gray_stack.push(idx as u32);
                }
            }
        }
    }

    /// Performs a full garbage collection cycle.
    /// 
    /// `roots` is a list of handles that are known to be reachable (e.g., from registers).
    pub fn collect(&mut self, roots: &[Handle]) {
        // 1. Mark roots
        for &root in roots {
            self.mark(root);
        }

        // 2. Trace (Mark phase)
        while let Some(idx) = self.gray_stack.pop() {
            let chunk_idx = (idx as usize) / CHUNK_SIZE;
            let slot_idx = (idx as usize) % CHUNK_SIZE;
            
            // SAFETY: We are iterating indices. We won't invalidate the vector storage here.
            // We just need to read the value at `idx`.
            let value_ptr = match &self.chunks[chunk_idx][slot_idx] {
                Slot::Occupied { value, .. } => value as *const T,
                _ => continue,
            };
            
            unsafe {
                (*value_ptr).trace(self);
            }
        }

        // 3. Sweep phase
        let mut free_count = 0;
        let mut total_slots = 0;
        
        for (c_idx, chunk) in self.chunks.iter_mut().enumerate() {
            for (s_idx, slot) in chunk.iter_mut().enumerate() {
                total_slots += 1;
                match slot {
                    Slot::Occupied { marked, .. } => {
                        if *marked {
                            // Reset mark for next cycle
                            *marked = false;
                        } else {
                            // Reclaim
                            let idx = (c_idx * CHUNK_SIZE + s_idx) as u32;
                            *slot = Slot::Free { next_free: self.free_head };
                            self.free_head = Some(idx);
                            free_count += 1;
                        }
                    },
                    Slot::Free { .. } => {
                        // Already free
                        free_count += 1;
                    }
                }
            }
        }
        
        self.allocated_objects = total_slots - free_count;
        
        // Adjust threshold
        self.next_gc_threshold = (self.allocated_objects * 2).max(1024 * 1024);
    }
}
