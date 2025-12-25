pub struct Blah {
       pub n: AbraInt,
       }impl VmType for Blah {
       fn from_vm(vm: &mut Vm) -> Self {
{vm.deconstruct_struct();let n = <AbraInt>::from_vm(vm);
       Self {
n,}}}fn to_vm(self, vm: &mut Vm) {
{self.n.to_vm(vm, vm_funcs);
       (vm_funcs.construct_struct)(vm, 1);}}}