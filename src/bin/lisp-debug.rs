use lisp::debug_adapter::adapter::DebugAdapter;

fn main() {
    let mut adapter = DebugAdapter::new();
    adapter.run();
}
