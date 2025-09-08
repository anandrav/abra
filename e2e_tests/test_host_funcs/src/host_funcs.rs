// This is an auto-generated file.
pub enum HostFunction {
    PrintString,
    Foo,
    Bar,
}
pub enum HostFunctionArgs {
    PrintString(String),
    Foo(i64),
    Bar(i64, i64),
}
pub enum HostFunctionRet {
    PrintString,
    Foo(i64),
    Bar(i64),
}
impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
            0 => HostFunction::PrintString,
            1 => HostFunction::Foo,
            2 => HostFunction::Bar,
            i => panic!("unrecognized host func: {i}"),
        }
    }
}
