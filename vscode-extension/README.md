# Lisp VS Code Extension

This extension provides debugging support for the Lisp language using the `lisp-debug` adapter.

## Setup

1.  **Build the Debug Adapter:**
    Ensure you have built the Rust debug adapter:
    ```bash
    cd ..
    cargo build --bin lisp-debug
    ```

2.  **Install Dependencies:**
    ```bash
    npm install
    ```

3.  **Compile:**
    ```bash
    npm run compile
    ```

## Usage

1.  Open this folder (`vscode-extension`) in VS Code.
2.  Press `F5` to launch the **Extension Development Host**.
3.  In the new window, open your Lisp project folder (the root `Lisp` folder).
4.  Open a `.lisp` file (e.g., `main.lisp`).
5.  Go to the **Run and Debug** view.
6.  Click "create a launch.json file" and select "Lisp Debug".
7.  Start debugging!

## Configuration

*   `lisp.debugAdapterPath`: Path to the `lisp-debug` executable. Defaults to `target/debug/lisp-debug.exe` in the workspace root.
