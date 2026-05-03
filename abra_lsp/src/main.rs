/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::collections::HashMap;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use abra_core::{AnalysisResult, CompletionCandidateKind, FileData, FileProvider};
use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument, Notification as _};
use lsp_types::request::{Completion, GotoDefinition, HoverRequest, Request as _};
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionOptions, CompletionResponse, Diagnostic,
    DiagnosticSeverity, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
    GotoDefinitionResponse, Hover, HoverContents, HoverProviderCapability, InitializeParams,
    Location, MarkupContent, MarkupKind, OneOf, Position, Range, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Uri,
};

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    eprintln!("abra-lsp: starting");

    let (connection, io_threads) = Connection::stdio();
    let server_capabilities = serde_json::to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec![".".to_string()]),
            ..Default::default()
        }),
        ..Default::default()
    })?;

    let init_params =
        serde_json::from_value::<InitializeParams>(connection.initialize(server_capabilities)?)?;

    main_loop(&connection, init_params)?;
    io_threads.join()?;

    eprintln!("abra-lsp: shutting down");
    Ok(())
}

fn main_loop(
    connection: &Connection,
    init_params: InitializeParams,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let standard_modules_dir = init_params
        .initialization_options
        .as_ref()
        .and_then(|opts| opts.get("standardModulesDir"))
        .and_then(|v| v.as_str())
        .map(PathBuf::from)
        .unwrap_or_else(|| home_dir().join(".abra").join("abra").join("modules"));

    // Optional override: if set, always compile from this root file instead of the active file
    let root_file_override = init_params
        .initialization_options
        .as_ref()
        .and_then(|opts| opts.get("rootFile"))
        .and_then(|v| v.as_str())
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string());

    let workspace_root = init_params
        .workspace_folders
        .as_ref()
        .and_then(|folders| folders.first())
        .and_then(|f| uri_to_path(&f.uri))
        .unwrap_or_else(|| PathBuf::from("."));

    eprintln!(
        "abra-lsp: workspace={}, root_file_override={:?}, modules={}",
        workspace_root.display(),
        root_file_override,
        standard_modules_dir.display()
    );

    let mut state = ServerState {
        documents: Rc::new(HashMap::new()),
        analysis: None,
        active_file_uri: None,
        workspace_root,
        root_file_override,
        standard_modules_dir: Rc::new(standard_modules_dir),
    };

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                handle_request(connection, &state, req)?;
            }
            Message::Notification(not) => {
                handle_notification(connection, &mut state, not)?;
            }
            Message::Response(_) => {}
        }
    }
    Ok(())
}

struct ServerState {
    /// Maps URI strings to document contents for open files
    documents: Rc<HashMap<String, String>>,
    analysis: Option<AnalysisResult>,
    /// URI of the most recently opened/changed file
    active_file_uri: Option<String>,
    workspace_root: PathBuf,
    /// If set, always compile from this file instead of the active file
    root_file_override: Option<String>,
    standard_modules_dir: Rc<PathBuf>,
}

impl ServerState {
    fn recheck(&mut self, connection: &Connection) -> Result<(), Box<dyn Error + Sync + Send>> {
        // Determine root file: use override if set, otherwise the active file
        let (root_file_name, root_dir) = if let Some(ref override_name) = self.root_file_override {
            (override_name.clone(), self.workspace_root.clone())
        } else if let Some(ref uri_str) = self.active_file_uri {
            let uri = Uri::from_str(uri_str).ok();
            let path = uri.as_ref().and_then(uri_to_path);
            match path {
                Some(p) => {
                    let file_name = p
                        .file_name()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .to_string();
                    let dir = p.parent().unwrap_or(&self.workspace_root).to_owned();
                    (file_name, dir)
                }
                None => return Ok(()),
            }
        } else {
            return Ok(());
        };

        let file_provider = LspFileProvider {
            documents: Rc::clone(&self.documents),
            workspace_root: root_dir,
            standard_modules_dir: Rc::clone(&self.standard_modules_dir),
        };

        let result = abra_core::check(&root_file_name, Box::new(file_provider));
        let errors = result.errors();

        // Group errors by file, ensuring every file gets an entry (to clear old diagnostics)
        let mut diags_by_file: HashMap<u32, Vec<Diagnostic>> = HashMap::new();
        for file_id in 0..result.file_db.files.len() as u32 {
            diags_by_file.entry(file_id).or_default();
        }

        for error in &errors {
            let file_data = match result.file_db.get(error.file_id) {
                Ok(f) => f,
                Err(_) => continue,
            };
            let start = byte_offset_to_position(file_data, error.range.start);
            let end = byte_offset_to_position(file_data, error.range.end);

            diags_by_file
                .entry(error.file_id)
                .or_default()
                .push(Diagnostic {
                    range: Range { start, end },
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: error.message.clone(),
                    ..Default::default()
                });
        }

        for (file_id, diagnostics) in &diags_by_file {
            let file_data = match result.file_db.get(*file_id) {
                Ok(f) => f,
                Err(_) => continue,
            };
            if let Some(uri) = path_to_uri(&file_data.absolute_path) {
                let params = lsp_types::PublishDiagnosticsParams {
                    uri,
                    diagnostics: diagnostics.clone(),
                    version: None,
                };
                connection
                    .sender
                    .send(Message::Notification(Notification::new(
                        lsp_types::notification::PublishDiagnostics::METHOD.to_string(),
                        params,
                    )))?;
            }
        }

        self.analysis = Some(result);
        Ok(())
    }
}

fn handle_notification(
    connection: &Connection,
    state: &mut ServerState,
    not: Notification,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    match not.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: DidOpenTextDocumentParams = serde_json::from_value(not.params)?;
            let uri_str = params.text_document.uri.as_str().to_string();
            Rc::make_mut(&mut state.documents).insert(uri_str.clone(), params.text_document.text);
            state.active_file_uri = Some(uri_str);
            state.recheck(connection)?;
        }
        DidChangeTextDocument::METHOD => {
            let params: DidChangeTextDocumentParams = serde_json::from_value(not.params)?;
            let uri_str = params.text_document.uri.as_str().to_string();
            if let Some(change) = params.content_changes.into_iter().last() {
                Rc::make_mut(&mut state.documents).insert(uri_str.clone(), change.text);
            }
            state.active_file_uri = Some(uri_str);
            state.recheck(connection)?;
        }
        _ => {}
    }
    Ok(())
}

fn handle_request(
    connection: &Connection,
    state: &ServerState,
    req: Request,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    fn respond<R: lsp_types::request::Request>(
        connection: &Connection,
        req: Request,
        handler: impl FnOnce(&R::Params) -> R::Result,
    ) -> Result<(), Box<dyn Error + Sync + Send>> {
        let (id, params) = req.extract(R::METHOD)?;
        let result = handler(&params);
        connection
            .sender
            .send(Message::Response(Response::new_ok(id, result)))?;
        Ok(())
    }

    match req.method.as_str() {
        GotoDefinition::METHOD => {
            respond::<GotoDefinition>(connection, req, |p| go_to_definition(state, p))
        }
        HoverRequest::METHOD => respond::<HoverRequest>(connection, req, |p| hover(state, p)),
        Completion::METHOD => respond::<Completion>(connection, req, |p| completion(state, p)),
        _ => Ok(()),
    }
}

/// Resolve a text document position to an analysis result, file ID, and byte offset.
fn resolve_position<'a>(
    state: &'a ServerState,
    uri: &Uri,
    position: Position,
) -> Option<(&'a AnalysisResult, u32, usize)> {
    let analysis = state.analysis.as_ref()?;
    let file_path = uri_to_path(uri)?;
    let file_id = analysis.file_id_for_path(&file_path)?;
    let file_data = analysis.file_db.get(file_id).ok()?;
    let offset = position_to_byte_offset(file_data, position)?;
    Some((analysis, file_id, offset))
}

fn go_to_definition(
    state: &ServerState,
    params: &lsp_types::GotoDefinitionParams,
) -> Option<GotoDefinitionResponse> {
    let pos = &params.text_document_position_params;
    let (analysis, file_id, offset) =
        resolve_position(state, &pos.text_document.uri, pos.position)?;

    let def = analysis.definition_at(file_id, offset)?;
    let def_file = analysis.file_db.get(def.file_id).ok()?;
    let start = byte_offset_to_position(def_file, def.range.start);
    let end = byte_offset_to_position(def_file, def.range.end);

    Some(GotoDefinitionResponse::Scalar(Location {
        uri: path_to_uri(&def_file.absolute_path)?,
        range: Range { start, end },
    }))
}

fn hover(state: &ServerState, params: &lsp_types::HoverParams) -> Option<Hover> {
    let pos = &params.text_document_position_params;
    let (analysis, file_id, offset) =
        resolve_position(state, &pos.text_document.uri, pos.position)?;

    let type_str = analysis.type_at(file_id, offset)?;

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```abra\n{type_str}\n```"),
        }),
        range: None,
    })
}

fn completion(
    state: &ServerState,
    params: &lsp_types::CompletionParams,
) -> Option<CompletionResponse> {
    let pos = &params.text_document_position;
    let (analysis, file_id, offset) =
        resolve_position(state, &pos.text_document.uri, pos.position)?;

    let candidates = analysis.completions_at(file_id, offset);
    if candidates.is_empty() {
        return None;
    }

    let items: Vec<CompletionItem> = candidates
        .into_iter()
        .map(|c| CompletionItem {
            label: c.label,
            kind: Some(match c.kind {
                CompletionCandidateKind::Function => CompletionItemKind::FUNCTION,
                CompletionCandidateKind::Field => CompletionItemKind::FIELD,
                CompletionCandidateKind::EnumVariant => CompletionItemKind::ENUM_MEMBER,
                CompletionCandidateKind::Type => CompletionItemKind::CLASS,
            }),
            ..Default::default()
        })
        .collect();

    Some(CompletionResponse::Array(items))
}

// --- File provider for LSP ---

struct LspFileProvider {
    documents: Rc<HashMap<String, String>>,
    workspace_root: PathBuf,
    standard_modules_dir: Rc<PathBuf>,
}

impl FileProvider for LspFileProvider {
    fn search_for_file(&self, path: &Path, is_root: bool) -> Result<FileData, Box<dyn Error>> {
        let mut package_name = path.to_owned();
        package_name.set_extension("");

        let absolute_path = if path.is_absolute() {
            path.to_owned()
        } else {
            self.workspace_root.join(path)
        };

        // Check open documents first (by matching URI)
        if let Some(uri) = path_to_uri(&absolute_path) {
            if let Some(contents) = self.documents.get(uri.as_str()) {
                return Ok(FileData::new(package_name, absolute_path, contents.clone()));
            }
        }

        // Fall back to disk (in workspace root dir)
        if let Ok(contents) = std::fs::read_to_string(&absolute_path) {
            return Ok(FileData::new(package_name, absolute_path, contents));
        }

        if is_root {
            return Err(format!(
                "could not find root file `{}` in `{}`",
                path.display(),
                self.workspace_root.display()
            )
            .into());
        }

        // Check standard modules
        let modules_path = self.standard_modules_dir.join(path);
        if let Some(uri) = path_to_uri(&modules_path) {
            if let Some(contents) = self.documents.get(uri.as_str()) {
                return Ok(FileData::new(package_name, modules_path, contents.clone()));
            }
        }
        if let Ok(contents) = std::fs::read_to_string(&modules_path) {
            return Ok(FileData::new(package_name, modules_path, contents));
        }

        Err(format!("could not find file `{}`", path.display()).into())
    }
}

// --- Conversion helpers ---

fn byte_offset_to_position(file_data: &FileData, offset: usize) -> Position {
    let line = file_data.line_index(offset).unwrap_or(0);
    let line_start = file_data.line_start(line).unwrap_or(0);
    Position {
        line: line as u32,
        character: offset.saturating_sub(line_start) as u32,
    }
}

fn position_to_byte_offset(file_data: &FileData, position: Position) -> Option<usize> {
    let line_start = file_data.line_start(position.line as usize).ok()?;
    Some(line_start + position.character as usize)
}

/// Convert a file:// URI to a filesystem path.
fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    let s = uri.as_str();
    let path_str = s.strip_prefix("file://")?;
    Some(PathBuf::from(percent_decode(path_str)))
}

/// Convert a filesystem path to a file:// URI.
fn path_to_uri(path: &Path) -> Option<Uri> {
    Uri::from_str(&format!("file://{}", path.display())).ok()
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut result = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let (Some(h), Some(l)) = (hex_val(bytes[i + 1]), hex_val(bytes[i + 2])) {
                result.push(h << 4 | l);
                i += 3;
                continue;
            }
        }
        result.push(bytes[i]);
        i += 1;
    }
    String::from_utf8(result).unwrap_or_else(|_| s.to_string())
}

fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn home_dir() -> PathBuf {
    std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."))
}
