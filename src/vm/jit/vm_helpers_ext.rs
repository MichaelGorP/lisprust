use crate::vm::vm::Vm;
use crate::vm::vp::{Value as LispValue};

pub unsafe extern "C" fn helper_get_jit_constant(vm: *mut Vm, idx: usize) -> u64 {
    let vm = &mut *vm;
    // idx is verified at compile time to be within bounds of what we pushed
    // but at runtime, vm.jit_constants is the backing store.
    let handle = *vm.jit_constants.get_unchecked(idx);
    LispValue::object(handle).raw()
}
