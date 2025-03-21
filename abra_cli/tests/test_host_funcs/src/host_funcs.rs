// This is an auto-generated file.
pub enum HostFunction {
    print_string,foo,bar,
    }impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
0 => HostFunction::print_string,1 => HostFunction::foo,2 => HostFunction::bar,i => panic!("unrecognized host func: {}", i)}
    }
}
