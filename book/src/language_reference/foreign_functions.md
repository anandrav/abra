# Foreign Functions

Functions defined in Rust can be called from Abra. Foreign functions must be declared ahead of time, so that their types are known. The corresponding Rust function definitions use the Abra VM API to pop arguments from the stack and push a return value to the stack.

os.abra
```
foreign fn fread(path: string) -> string

foreign fn fwrite(path: string, contents: string) -> string
```

os/src/lib.rs
```
use abra_core::vm::Vm;
use std::fs;

#[no_mangle]
pub unsafe extern "C" fn fread(vm: *mut Vm) {
    let string_view = vm_view_string(vm);
    let path = string_view.to_owned();
    vm_pop(vm);

    let content = fs::read_to_string(path).expect("Unable to read from file");

    let string_view = StringView::from_string(&content);
    vm_push_string(vm, string_view);
}

#[no_mangle]
pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
    let string_view = vm_view_string(vm);
    let content = string_view.to_owned();
    vm_pop(vm);

    // TODO: make a macro for this called get_string!
    let string_view = vm_view_string(vm);
    let path = string_view.to_owned();
    vm_pop(vm);

    fs::write(path, content).expect("Unable to write to file");
}
```