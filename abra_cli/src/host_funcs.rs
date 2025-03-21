// This is an auto-generated file.
pub enum HostFunction {
    PrintString,
    }impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
0 => HostFunction::PrintString,i => panic!("unrecognized host func: {}", i)}
    }
}
