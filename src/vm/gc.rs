
/// A handle to an object in the arena.
/// It is essentially an index into the arena's storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Handle(u32);

impl Handle {
    /// Returns the raw index of the handle.
    #[inline(always)]
    pub fn index(&self) -> usize {
        self.0 as usize
    }
    
    /// Creates a handle from a raw index.
    /// Unsafe because it doesn't check if the index is valid.
    pub unsafe fn from_raw(idx: u32) -> Self {
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

/// A simple mark-and-sweep arena allocator.
/// 
/// This allocator stores objects in a contiguous `Vec`, which improves cache locality
/// compared to individual `Box` allocations. It also avoids the overhead of `malloc`
/// for every object.
pub struct Arena<T> {
    slots: Vec<Slot<T>>,
    free_head: Option<u32>,
    gray_stack: Vec<u32>,
    // Statistics
    pub allocated_objects: usize,
    pub next_gc_threshold: usize,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            slots: Vec::with_capacity(4096),
            free_head: None,
            gray_stack: Vec::with_capacity(256),
            allocated_objects: 0,
            next_gc_threshold: 1024 * 1024, // Start with 1MB equivalent (approx)
        }
    }

    /// Allocates a new object in the arena and returns a handle to it.
    pub fn alloc(&mut self, value: T) -> Handle {
        self.allocated_objects += 1;
        
        if let Some(idx) = self.free_head {
            // Reuse a free slot
            let next = match &self.slots[idx as usize] {
                Slot::Free { next_free } => *next_free,
                _ => unreachable!("Corrupt free list"),
            };
            self.free_head = next;
            self.slots[idx as usize] = Slot::Occupied { value, marked: false };
            Handle(idx)
        } else {
            // Append a new slot
            let idx = self.slots.len() as u32;
            self.slots.push(Slot::Occupied { value, marked: false });
            Handle(idx)
        }
    }

    /// Gets a reference to an object.
    /// Returns None if the handle is invalid or points to a free slot.
    #[inline(always)]
    pub fn get(&self, handle: Handle) -> Option<&T> {
        match self.slots.get(handle.index()) {
            Some(Slot::Occupied { value, .. }) => Some(value),
            _ => None,
        }
    }

    /// Gets a mutable reference to an object.
    #[inline(always)]
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        match self.slots.get_mut(handle.index()) {
            Some(Slot::Occupied { value, .. }) => Some(value),
            _ => None,
        }
    }
    
    /// Unsafe access for performance (skips checks).
    /// Use only when you are sure the handle is valid.
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, handle: Handle) -> &T {
        match self.slots.get_unchecked(handle.index()) {
            Slot::Occupied { value, .. } => value,
            _ => std::hint::unreachable_unchecked(),
        }
    }

    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, handle: Handle) -> &mut T {
        match self.slots.get_unchecked_mut(handle.index()) {
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
        if let Some(Slot::Occupied { marked, .. }) = self.slots.get_mut(idx) {
            if !*marked {
                *marked = true;
                self.gray_stack.push(idx as u32);
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
            // We need to temporarily extract the value to trace it to avoid borrowing issues.
            // Or we can use unsafe to get a reference while holding the mutable borrow of the arena.
            // Since we are single-threaded, this is safe if we are careful.
            
            // SAFETY: We are iterating indices. We won't invalidate the vector storage here.
            // We just need to read the value at `idx`.
            let value_ptr = match &self.slots[idx as usize] {
                Slot::Occupied { value, .. } => value as *const T,
                _ => continue,
            };
            
            unsafe {
                (*value_ptr).trace(self);
            }
        }

        // 3. Sweep phase
        let mut free_count = 0;
        for (i, slot) in self.slots.iter_mut().enumerate() {
            match slot {
                Slot::Occupied { marked, .. } => {
                    if *marked {
                        // Reset mark for next cycle
                        *marked = false;
                    } else {
                        // Reclaim
                        *slot = Slot::Free { next_free: self.free_head };
                        self.free_head = Some(i as u32);
                        free_count += 1;
                    }
                },
                Slot::Free { .. } => {
                    // Already free
                    free_count += 1;
                }
            }
        }
        
        self.allocated_objects = self.slots.len() - free_count;
        
        // Adjust threshold
        self.next_gc_threshold = (self.allocated_objects * 2).max(1024 * 1024);
    }
}
