pub struct Person {
pub name: String,
pub age: AbraInt,
}impl VmType for Person {
fn from_vm(vm: &mut Vm) -> Self {
{vm.deconstruct_struct();let name = <String>::from_vm(vm);
let age = <AbraInt>::from_vm(vm);
Self {
name,age,}}}fn to_vm(self, vm: &mut Vm) {
{self.name.to_vm(vm, vm_funcs);
self.age.to_vm(vm, vm_funcs);
(vm_funcs.construct_struct)(vm, 2);}}}