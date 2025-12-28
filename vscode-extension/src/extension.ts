import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

export function activate(context: vscode.ExtensionContext) {
    const provider = new LispConfigurationProvider();
    context.subscriptions.push(vscode.debug.registerDebugConfigurationProvider('lisp', provider));

    const factory = new LispDebugAdapterDescriptorFactory();
    context.subscriptions.push(vscode.debug.registerDebugAdapterDescriptorFactory('lisp', factory));
}

export function deactivate() {
}

class LispConfigurationProvider implements vscode.DebugConfigurationProvider {
    resolveDebugConfiguration(folder: vscode.WorkspaceFolder | undefined, config: vscode.DebugConfiguration, token?: vscode.CancellationToken): vscode.ProviderResult<vscode.DebugConfiguration> {

        // if launch.json is missing or empty
        if (!config.type && !config.request && !config.name) {
            const editor = vscode.window.activeTextEditor;
            if (editor && (editor.document.languageId === 'lisp' || editor.document.languageId === 'scheme' || editor.document.fileName.endsWith('.scm') || editor.document.fileName.endsWith('.lisp'))) {
                config.type = 'lisp';
                config.name = 'Launch';
                config.request = 'launch';
                config.program = '${file}';
                config.stopOnEntry = true;
            }
        }

        if (!config.program) {
            return vscode.window.showInformationMessage("Cannot find a program to debug").then(_ => {
                return undefined; // abort launch
            });
        }

        return config;
    }
}

class LispDebugAdapterDescriptorFactory implements vscode.DebugAdapterDescriptorFactory {
    createDebugAdapterDescriptor(session: vscode.DebugSession, executable: vscode.DebugAdapterExecutable | undefined): vscode.ProviderResult<vscode.DebugAdapterDescriptor> {
        
        const config = vscode.workspace.getConfiguration('lisp');
        let adapterPath = config.get<string>('debugAdapterPath');

        if (!adapterPath) {
            // Default to looking in target/debug relative to workspace root if available
            if (vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 0) {
                const root = vscode.workspace.workspaceFolders[0].uri.fsPath;
                adapterPath = path.join(root, 'target', 'debug', 'lisp-debug.exe');
            } else {
                vscode.window.showErrorMessage("Lisp debug adapter path not configured.");
                return undefined;
            }
        } else {
             // Resolve relative path
             if (!path.isAbsolute(adapterPath) && vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 0) {
                 adapterPath = path.join(vscode.workspace.workspaceFolders[0].uri.fsPath, adapterPath);
             }
        }

        if (!fs.existsSync(adapterPath)) {
             // Try adding .exe if on windows and missing
             if (process.platform === 'win32' && !adapterPath.endsWith('.exe')) {
                 if (fs.existsSync(adapterPath + '.exe')) {
                     adapterPath += '.exe';
                 }
             }
        }

        if (!fs.existsSync(adapterPath)) {
            vscode.window.showErrorMessage(`Lisp debug adapter not found at: ${adapterPath}`);
            return undefined;
        }

        return new vscode.DebugAdapterExecutable(adapterPath, []);
    }
}
