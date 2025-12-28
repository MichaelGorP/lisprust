use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(tag = "type")]
pub enum ProtocolMessage {
    #[serde(rename = "request")]
    Request(Request),
    #[serde(rename = "response")]
    Response(Response),
    #[serde(rename = "event")]
    Event(Event),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Request {
    pub seq: i64,
    pub command: String,
    #[serde(default)]
    pub arguments: Option<Value>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Response {
    pub seq: i64,
    pub request_seq: i64,
    pub success: bool,
    pub command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body: Option<Value>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Event {
    pub seq: i64,
    pub event: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body: Option<Value>,
}

// --- Specific Arguments ---

#[derive(Deserialize, Debug)]
pub struct InitializeRequestArguments {
    #[serde(rename = "adapterID")]
    pub adapter_id: String,
    #[serde(rename = "linesStartAt1")]
    pub lines_start_at1: Option<bool>,
    #[serde(rename = "columnsStartAt1")]
    pub columns_start_at1: Option<bool>,
    #[serde(rename = "pathFormat")]
    pub path_format: Option<String>,
}

#[derive(Deserialize, Debug)]
pub struct LaunchRequestArguments {
    pub program: String,
    #[serde(default)]
    pub stop_on_entry: bool,
}

#[derive(Deserialize, Debug)]
pub struct SetBreakpointsArguments {
    pub source: Source,
    pub breakpoints: Option<Vec<SourceBreakpoint>>,
}

#[derive(Deserialize, Debug)]
pub struct SourceBreakpoint {
    pub line: i64,
    pub column: Option<i64>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Source {
    pub name: Option<String>,
    pub path: Option<String>,
}

#[derive(Serialize, Debug)]
pub struct Breakpoint {
    pub verified: bool,
    pub line: Option<i64>,
    pub message: Option<String>,
}

#[derive(Serialize, Debug)]
pub struct StackFrame {
    pub id: i64,
    pub name: String,
    pub source: Option<Source>,
    pub line: i64,
    pub column: i64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_line: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_column: Option<i64>,
}

#[derive(Serialize, Debug)]
pub struct Scope {
    pub name: String,
    #[serde(rename = "variablesReference")]
    pub variables_reference: i64,
    pub expensive: bool,
}

#[derive(Serialize, Debug)]
pub struct Variable {
    pub name: String,
    pub value: String,
    #[serde(rename = "type", skip_serializing_if = "Option::is_none")]
    pub type_: Option<String>,
    #[serde(rename = "variablesReference")]
    pub variables_reference: i64,
}

#[derive(Serialize, Debug)]
pub struct Thread {
    pub id: i64,
    pub name: String,
}

#[derive(Serialize, Debug)]
pub struct StoppedEventBody {
    pub reason: String,
    #[serde(rename = "threadId")]
    pub thread_id: Option<i64>,
    pub text: Option<String>,
    #[serde(rename = "allThreadsStopped")]
    pub all_threads_stopped: Option<bool>,
}
