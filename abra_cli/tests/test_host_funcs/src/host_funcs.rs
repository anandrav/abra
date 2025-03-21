// This is an auto-generated file.
pub enum HostFunction {
    foo,
    }impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
0 => HostFunction::foo,i => panic!("unrecognized effect: {}", i)}
    }
}
