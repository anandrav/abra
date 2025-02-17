// Rust addon API

use core::str;
use std::{
    ffi::c_char,
    fs::{self, read_to_string},
    path::{Path, PathBuf},
    rc::Rc,
};

pub use crate::vm::Vm;
use crate::{
    ast::{FileDatabase, ForeignFuncDecl, NodeMap, TypeDefKind},
    parse::parse_or_err,
    FileAst, FileData, ItemKind,
};

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_int(vm: *mut Vm, n: i64) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.push_int(n);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_nil(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.push_nil();
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_pop_int(vm: *mut Vm) -> i64 {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().get_int();
    vm.pop();
    top
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_pop(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.pop();
}

#[repr(C)]
pub struct StringView {
    pub ptr: *const c_char,
    pub len: usize,
}

impl StringView {
    pub fn to_owned(self) -> String {
        unsafe {
            let byte_slice = std::slice::from_raw_parts(self.ptr as *const u8, self.len);
            str::from_utf8(byte_slice).unwrap().to_string()
        }
    }

    pub fn from_string(s: &str) -> Self {
        StringView {
            ptr: s.as_ptr() as *const c_char,
            len: s.len(),
        }
    }
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_view_string(vm: *mut Vm) -> StringView {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().view_string(vm);
    StringView {
        ptr: top.as_ptr() as *const c_char,
        len: top.len(),
    }
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_string(vm: *mut Vm, string_view: StringView) {
    let vm = unsafe { vm.as_mut().unwrap() };
    let s = string_view.to_owned();
    vm.push_str(s);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_construct(vm: *mut Vm, arity: u16) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.construct_struct(arity);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_deconstruct(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.deconstruct();
}

use std::env::current_dir;

pub fn generate() {
    let current_dir = current_dir().unwrap();
    let mut package_dir = current_dir.clone();
    package_dir.pop();
    let package_name = package_dir
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    let mut toplevel_abra_file = package_dir.clone();
    toplevel_abra_file.pop();
    toplevel_abra_file = toplevel_abra_file.join(format!("{}.abra", package_name));

    let mut output = String::new();

    write_header(&mut output, &package_name);

    let mut file_db = FileDatabase::new();
    // let mut node_map = NodeMap::new();
    // let mut file_asts: Vec<Rc<FileAst>> = vec![];

    // handle toplevel .abra file
    {
        let source = read_to_string(&toplevel_abra_file).unwrap();
        let file_data = FileData::new(
            format!("{}.abra", package_name).into(),
            toplevel_abra_file,
            source,
        );
        let file_id = file_db.add(file_data);
        let file_data = file_db.get(file_id).unwrap();
        let ast = parse_or_err(file_id, file_data).unwrap();

        add_items_from_ast(ast, &mut output);

        // ast::initialize_node_map(&mut node_map, &(file_ast.clone() as Rc<dyn ast::Node>));
    }

    // handle all other .abra files
    find_abra_files(&package_dir, &mut output).unwrap();

    // write_footer
    {
        output.push_str(
            r#" 
    }
}
"#,
        );
    }

    let output_path = current_dir.join("src").join("gen.rs");

    std::fs::write(&output_path, output).unwrap();

    let status = std::process::Command::new("rustfmt")
        .arg(&output_path)
        .status()
        .expect("failed to run rustfmt");

    if !status.success() {
        panic!("rustfmt failed on {:?}", output_path);
    }

    if !status.success() {
        panic!("cargo fmt failed");
    }

    // panic!("current_dir={}", current_dir.to_str().unwrap());
}

fn write_header(output: &mut String, package_name: &str) {
    output.push_str(&format!(
        r#"mod {};
        pub mod ffi {{
            pub mod {} {{
            use crate::{};
            use abra_core::addons::*;"#,
        package_name, package_name, package_name
    ));
}

fn add_items_from_ast(ast: Rc<FileAst>, output: &mut String) {
    for item in ast.items.iter() {
        match &*item.kind {
            ItemKind::TypeDef(tydef) => match &**tydef {
                TypeDefKind::Struct(s) => {
                    output.push_str(&format!(
                        r#"pub struct {} {{
                    "#,
                        s.name.v
                    ));
                    // TODO: impl for all types
                    let tyname = "int";
                    for field in &s.fields {
                        output.push_str(&format!(
                            r#"pub {}: {},
                        "#,
                            field.name.v, tyname
                        ));
                    }
                    output.push_str("}");

                    output.push_str(&format!(
                        r#"pub struct {} {{
                    "#,
                        s.name.v
                    ));
                    // TODO: impl for all types
                    let tyname = "int";
                    for field in &s.fields {
                        output.push_str(&format!(
                            r#"pub {}: {},
                        "#,
                            field.name.v, tyname
                        ));
                    }
                    output.push('}');
                }
                _ => unimplemented!(),
            },
            ItemKind::ForeignFuncDecl(f) => {
                // TODO: duplicated with code in resolve.rs
                let elems: Vec<_> = ast.name.split(std::path::MAIN_SEPARATOR_STR).collect();
                let mut symbol = "abra_ffi".to_string();
                for elem in elems {
                    symbol.push('$');
                    symbol.push_str(elem);
                }
                symbol.push('$');
                symbol.push_str(&f.name.v);

                output.push_str(&format!("#[export_name = \"{}\"]", symbol));
                output.push_str(&format!(
                    "pub unsafe extern \"C\" fn {}(vm: *mut Vm) {{",
                    f.name.v,
                ));

                output.push('}');
            }
            _ => {}
        }
    }
}

fn find_abra_files(dir: &Path, output: &mut String) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            // Recursively search this directory.
            find_abra_files(&path, output)?;
        } else if let Some(ext) = path.extension() {
            // Check if the extension is "abra".
            if ext == "abra" {
                let file_name = path.file_name().unwrap().to_str().unwrap().to_string();

                let no_extension = &file_name[0..(file_name.len() - ".abra".len())];

                // panic!("no_extension={}", no_extension);
            }
        }
    }
    Ok(())
}
