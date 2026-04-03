import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext) {
  const config = vscode.workspace.getConfiguration("abra");
  const lspPath = config.get<string>("lspPath") || "abra-lsp";
  const rootFile = config.get<string>("rootFile") || "";
  const standardModulesDir = config.get<string>("standardModulesDir") || "";

  const serverOptions: ServerOptions = {
    command: lspPath,
    transport: TransportKind.stdio,
  };

  const initializationOptions: Record<string, string> = {};
  if (rootFile) {
    initializationOptions.rootFile = rootFile;
  }
  if (standardModulesDir) {
    initializationOptions.standardModulesDir = standardModulesDir;
  }

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "abra" }],
    initializationOptions,
  };

  client = new LanguageClient(
    "abra-lsp",
    "Abra Language Server",
    serverOptions,
    clientOptions
  );

  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
