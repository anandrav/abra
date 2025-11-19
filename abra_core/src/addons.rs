/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// Rust addon API

use crate::vm::Vm;
use crate::{
    FileAst, FileData, ItemKind,
    ast::{FileDatabase, Type, TypeDefKind, TypeKind},
    parse::parse_or_err,
};
use core::str;
use std::{
    ffi::{c_char, c_void},
    fs::{self, read_to_string},
    path::{Path, PathBuf},
    rc::Rc,
};
use utils::swrite;

//
// C-compatible table of function pointers
//
#[repr(C)]
pub struct AbraVmFunctions {
    pub push_int: unsafe extern "C" fn(vm: *mut c_void, n: i64),
    pub push_float: unsafe extern "C" fn(vm: *mut c_void, f: f64),
    pub push_bool: unsafe extern "C" fn(vm: *mut c_void, b: bool),
    pub push_nil: unsafe extern "C" fn(vm: *mut c_void),
    pub pop_nil: unsafe extern "C" fn(vm: *mut c_void),
    pub pop_int: unsafe extern "C" fn(vm: *mut c_void) -> i64,
    pub pop_float: unsafe extern "C" fn(vm: *mut c_void) -> f64,
    pub pop_bool: unsafe extern "C" fn(vm: *mut c_void) -> bool,
    pub pop: unsafe extern "C" fn(vm: *mut c_void),
    pub view_string: unsafe extern "C" fn(vm: *mut c_void) -> StringView,
    pub push_string: unsafe extern "C" fn(vm: *mut c_void, string_view: StringView),
    pub construct_struct: unsafe extern "C" fn(vm: *mut c_void, arity: usize),
    pub construct_array: unsafe extern "C" fn(vm: *mut c_void, len: usize),
    pub construct_variant: unsafe extern "C" fn(vm: *mut c_void, tag: u16),
    pub deconstruct_struct: unsafe extern "C" fn(vm: *mut c_void),
    pub deconstruct_array: unsafe extern "C" fn(vm: *mut c_void),
    pub deconstruct_variant: unsafe extern "C" fn(vm: *mut c_void),
    pub array_len: unsafe extern "C" fn(vm: *mut c_void) -> usize,
}

pub const ABRA_VM_FUNCS: AbraVmFunctions = AbraVmFunctions {
    push_int: abra_vm_push_int,
    push_float: abra_vm_push_float,
    push_bool: abra_vm_push_bool,
    push_nil: abra_vm_push_nil,
    pop_nil: abra_vm_pop_nil,
    pop_int: abra_vm_pop_int,
    pop_float: abra_vm_pop_float,
    pop_bool: abra_vm_pop_bool,
    pop: abra_vm_pop,
    view_string: abra_vm_view_string,
    push_string: abra_vm_push_string,
    construct_struct: abra_vm_construct_struct,
    construct_array: abra_vm_construct_array,
    construct_variant: abra_vm_construct_variant,
    deconstruct_struct: abra_vm_deconstruct_struct,
    deconstruct_array: abra_vm_deconstruct_array,
    deconstruct_variant: abra_vm_deconstruct_enum,
    array_len: abra_vm_array_len,
};

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_push_int(vm: *mut c_void, n: i64) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.push_int(n);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_push_float(vm: *mut c_void, f: f64) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.push_float(f);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_push_bool(vm: *mut c_void, b: bool) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.push_bool(b);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_push_nil(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.push_nil();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_nil(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.pop();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_int(vm: *mut c_void) -> i64 {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_int(vm);
    vm.pop();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_float(vm: *mut c_void) -> f64 {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_float(vm);
    vm.pop();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_bool(vm: *mut c_void) -> bool {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_bool(vm);
    vm.pop();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
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
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_view_string(vm: *mut c_void) -> StringView {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().view_string(vm);
    StringView {
        ptr: top.as_ptr() as *const c_char,
        len: top.len(),
    }
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_push_string(vm: *mut c_void, string_view: StringView) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let s = string_view.to_owned();
    vm.push_str(s);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_construct_struct(vm: *mut c_void, arity: usize) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.construct_struct(arity);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_construct_array(vm: *mut c_void, len: usize) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.construct_array(len); // TODO: annoying conversions everywhere
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_construct_variant(vm: *mut c_void, tag: u16) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.construct_variant(tag);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_deconstruct_struct(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.deconstruct_struct();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_deconstruct_array(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.deconstruct_array();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_deconstruct_enum(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.deconstruct_variant();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_array_len(vm: *mut c_void) -> usize {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.array_len()
}

use std::env::current_dir;

pub fn generate_bindings_for_crate() {
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
    toplevel_abra_file = toplevel_abra_file.join(format!("{package_name}.abra"));

    let output = &mut String::new();

    write_header(output, &package_name);

    let mut file_db = FileDatabase::new();

    // handle toplevel .abra file
    {
        let source = read_to_string(&toplevel_abra_file).unwrap();
        let file_data = FileData::new(
            format!("{package_name}.abra").into(),
            toplevel_abra_file,
            source,
        );
        let file_id = file_db.add(file_data);
        let file_data = file_db.get(file_id).unwrap();
        let ast = parse_or_err(file_id, file_data).unwrap();

        add_items_from_ast(ast, output);
    }

    // handle all other .abra files
    let mut prefixes = vec![package_name.clone()];
    find_abra_files(&package_dir, &mut prefixes, &mut file_db, output).unwrap();

    // write_footer
    {
        output.push_str(
            r#" 
    }
}
"#,
        );
    }

    let output_path = current_dir.join("src").join("lib.rs");

    std::fs::write(&output_path, output).unwrap();

    let status = std::process::Command::new("cargo")
        .arg("fmt")
        .status()
        .expect("failed to run rustfmt");
    if !status.success() {
        panic!("rustfmt failed on {output_path:?}");
    }
}

fn write_header(output: &mut String, package_name: &str) {
    swrite!(
        output,
        r#"// This is an auto-generated file.
        
mod {package_name};
pub mod ffi {{
    pub mod {package_name} {{
    use crate::{package_name};
    use abra_core::addons::*;
    use std::ffi::c_void;
    "#
    )
}

fn add_items_from_ast(ast: Rc<FileAst>, output: &mut String) {
    for item in ast.items.iter() {
        match &*item.kind {
            ItemKind::TypeDef(tydef) => match &**tydef {
                TypeDefKind::Struct(s) => {
                    swrite!(
                        output,
                        r#"pub struct {} {{
"#,
                        s.name.v
                    );
                    for field in &s.fields {
                        let tyname = name_of_ty(&field.ty);
                        swrite!(
                            output,
                            r#"pub {}: {},
"#,
                            field.name.v,
                            tyname
                        );
                    }
                    output.push('}');

                    swrite!(
                        output,
                        r#"impl VmFfiType for {} {{
"#,
                        s.name.v
                    );
                    output.push_str(
                        r#"unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
"#,
                    );
                    output.push_str("unsafe {");
                    output.push_str("(vm_funcs.deconstruct_struct)(vm);");
                    for field in s.fields.iter() {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            //     output.push_str(
                            //         r#"(vm_funcs.pop_nil)(vm);
                            // "#,
                            //     );
                        } else {
                            let tyname = name_of_ty(&field.ty);
                            swrite!(
                                output,
                                r#"let {} = <{}>::from_vm_unsafe(vm, vm_funcs);
"#,
                                field.name.v,
                                tyname
                            );
                        }
                    }
                    output.push_str(
                        r#"Self {
"#,
                    );
                    for field in &s.fields {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            swrite!(output, "{}: (),", field.name.v);
                        } else {
                            swrite!(output, "{},", field.name.v);
                        }
                    }
                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
"#,
                    );
                    output.push_str("unsafe {");
                    for field in s.fields.iter() {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            // output.push_str("(vm_funcs.push_nil)(vm);");
                        } else {
                            swrite!(
                                output,
                                r#"self.{}.to_vm_unsafe(vm, vm_funcs);
"#,
                                field.name.v
                            );
                        }
                    }

                    let mut nfields = 0;
                    for field in &*s.fields {
                        if !matches!(*field.ty.kind, TypeKind::Void) {
                            nfields += 1;
                        }
                    }
                    swrite!(output, "(vm_funcs.construct_struct)(vm, {});", nfields);

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
                TypeDefKind::Enum(e) => {
                    swrite!(
                        output,
                        r#"pub enum {} {{
"#,
                        e.name.v
                    );
                    for variant in &e.variants {
                        swrite!(output, "{}", variant.ctor.v);
                        if let Some(ty) = &variant.data {
                            output.push('(');
                            output.push_str(&name_of_ty(ty));
                            output.push(')');
                        }
                        output.push(',');
                    }
                    output.push('}');

                    swrite!(
                        output,
                        r#"impl VmFfiType for {} {{
"#,
                        e.name.v
                    );
                    output.push_str(
                        r#"unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
"#,
                    );

                    output.push_str("unsafe {");
                    output.push_str("(vm_funcs.deconstruct_variant)(vm);");
                    output.push_str("let tag = (vm_funcs.pop_int)(vm);");
                    output.push_str("match tag {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        output.push_str(&format!("{i} => {{"));
                        if let Some(ty) = &variant.data {
                            let tyname = name_of_ty(ty);
                            swrite!(
                                output,
                                r#"let value: {tyname} = <{tyname}>::from_vm_unsafe(vm, vm_funcs);
"#
                            );
                            swrite!(output, "{}::{}(value)", e.name.v, variant.ctor.v);
                        } else {
                            output.push_str("(vm_funcs.pop_nil)(vm);");
                            swrite!(output, "{}::{}", e.name.v, variant.ctor.v);
                        }
                        output.push('}');
                    }
                    output.push_str(r#"_ => panic!("unexpected tag encountered: {tag}")"#);

                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
"#,
                    );
                    output.push_str("unsafe {");

                    output.push_str("match self {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        if variant.data.is_some() {
                            swrite!(output, "{}::{}(value) => {{", e.name.v, variant.ctor.v);
                            output.push_str("value.to_vm_unsafe(vm, vm_funcs);");
                            swrite!(output, "(vm_funcs.construct_variant)(vm, {i});");
                        } else {
                            swrite!(output, "{}::{} => {{", e.name.v, variant.ctor.v);
                            output.push_str("(vm_funcs.push_nil)(vm);");
                            swrite!(output, "(vm_funcs.construct_variant)(vm, {i});");
                        }
                        output.push('}');
                    }
                    output.push('}');

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
            },
            ItemKind::ForeignFuncDecl(f) => {
                output.push_str(
                    r#"/// # Safety
                              /// `vm` must be non-null and valid.
                              "#,
                );
                let elems: Vec<_> = ast.name.split(std::path::MAIN_SEPARATOR_STR).collect();
                let package_name = elems.last().unwrap().to_string();
                let symbol = make_foreign_func_name(&f.name.v, &elems);

                swrite!(output, "#[unsafe(export_name = \"{symbol}\")]");
                swrite!(
                    output,
                    "pub unsafe extern \"C\" fn {}(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {{",
                    f.name.v,
                );
                output.push_str("unsafe {");

                output.push_str("let _vm_funcs: &AbraVmFunctions = &*vm_funcs;");
                // get args in reverse order
                for (name, ty) in f.args.iter().rev() {
                    let Some(ty) = ty else { panic!() };
                    if matches!(&*ty.kind, TypeKind::Void) {
                        //                         output.push_str(
                        //                             r#"(vm_funcs.pop_nil)(vm);
                        // "#,
                        //                         );
                    } else {
                        let tyname = name_of_ty(ty);
                        swrite!(
                            output,
                            r#"let {} = <{}>::from_vm_unsafe(_vm, _vm_funcs);
"#,
                            name.v,
                            tyname
                        );
                    }
                }
                // call the user's implementation
                let out_ty = &f.ret_type;
                let out_ty_name = name_of_ty(out_ty);
                if matches!(&*out_ty.kind, TypeKind::Void) {
                    swrite!(output, "{}::{}(", package_name, f.name.v);
                } else {
                    swrite!(
                        output,
                        "let ret: {} = {}::{}(",
                        out_ty_name,
                        package_name,
                        f.name.v
                    );
                }

                for (name, typ) in f.args.iter() {
                    let Some(typ) = typ else { panic!() };
                    if matches!(&*typ.kind, TypeKind::Void) {
                        output.push_str("(),");
                    } else {
                        swrite!(output, "{},", name.v);
                    }
                }
                output.push_str(");");
                // push return value
                if *out_ty.kind != TypeKind::Void {
                    output.push_str("ret.to_vm_unsafe(_vm, _vm_funcs);");
                }
                output.push('}');
                output.push('}');
            }
            _ => {}
        }
    }
}

pub(crate) fn name_of_ty(ty: &Rc<Type>) -> String {
    match &*ty.kind {
        TypeKind::Bool => "bool".to_string(),
        TypeKind::Float => "f64".to_string(),
        TypeKind::Int => "i64".to_string(),
        TypeKind::Str => "String".to_string(),
        TypeKind::Void => "()".to_string(),
        TypeKind::Tuple(elems) => {
            let mut s = "(".to_string();
            for elem in elems {
                s.push_str(&name_of_ty(elem));
                s.push(',');
            }
            s.push(')');
            s
        }
        TypeKind::NamedWithParams(ident, params) => {
            // special-case
            let mut s = ident.v.clone();
            if s == "option" {
                s = "Option".into();
            } else if s == "array" {
                s = "Vec".into();
            }
            s.push('<');
            for param in params {
                s.push_str(&name_of_ty(param));
                s.push(',');
            }
            s.push('>');
            s
        }
        TypeKind::Function(..) => "FunctionNotSupported".into(),
        TypeKind::Poly(..) => "PolyNotSupported".into(),
    }
}

fn find_abra_files(
    search_dir: &Path,
    prefixes: &mut Vec<String>,
    file_db: &mut FileDatabase,
    output: &mut String,
) -> std::io::Result<()> {
    for entry in fs::read_dir(search_dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            // Recursively search this directory.
            prefixes.push(path.file_name().unwrap().to_str().unwrap().to_string());
            find_abra_files(&path, prefixes, file_db, output)?;
            prefixes.pop();
        } else if let Some(ext) = path.extension() {
            // Check if the extension is "abra".
            if ext == "abra" {
                let file_name = path.file_name().unwrap().to_str().unwrap().to_string();

                let no_extension = &file_name[0..(file_name.len() - ".abra".len())];

                let mut crate_import = String::new();
                for prefix in prefixes.iter() {
                    crate_import.push_str(prefix);
                    crate_import.push_str("::");
                }
                crate_import.push_str(no_extension);

                output.push_str(&format!(
                    r#" pub mod {no_extension} {{
                        use crate::{crate_import};
                        use abra_core::addons::*;
                        use std::ffi::c_void;
                        "#
                ));

                let source = read_to_string(&path).unwrap();
                let mut nominal_path = PathBuf::new();
                for prefix in prefixes.iter() {
                    nominal_path = nominal_path.join(prefix);
                }
                nominal_path = nominal_path.join(format!("{no_extension}.abra"));
                let file_data = FileData::new(nominal_path, path.clone(), source);
                let file_id = file_db.add(file_data);
                let file_data = file_db.get(file_id).unwrap();
                let ast = parse_or_err(file_id, file_data).unwrap();

                add_items_from_ast(ast, output);

                output.push('}');
            }
        }
    }
    Ok(())
}

pub(crate) fn make_foreign_func_name(base_name: &str, qualifiers: &[&str]) -> String {
    let mut symbol = "abra_ffi".to_string();
    for elem in qualifiers {
        symbol.push('$');
        symbol.push_str(elem);
    }
    symbol.push('$');
    symbol.push_str(base_name);
    symbol
}

pub trait VmFfiType {
    /// # Safety
    /// vm is non-null and valid
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self;

    /// # Safety
    /// vm is non-null and valid
    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions);
}

impl VmFfiType for i64 {
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_int)(vm) }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_int)(vm, self);
        }
    }
}

impl VmFfiType for f64 {
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_float)(vm) }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_float)(vm, self);
        }
    }
}

impl VmFfiType for () {
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop)(vm) }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_nil)(vm);
        }
    }
}

impl VmFfiType for bool {
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_bool)(vm) }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_bool)(vm, self);
        }
    }
}

impl VmFfiType for String {
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            let string_view = (vm_funcs.view_string)(vm);
            let content = string_view.to_owned();
            (vm_funcs.pop)(vm);
            content
        }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            let string_view = StringView::from_string(&self);
            (vm_funcs.push_string)(vm, string_view);
        }
    }
}

impl<T> VmFfiType for Option<T>
where
    T: VmFfiType,
{
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            (vm_funcs.deconstruct_variant)(vm);
            let tag = (vm_funcs.pop_int)(vm);
            match tag {
                0 => {
                    let t = T::from_vm_unsafe(vm, vm_funcs);
                    Some(t)
                }
                1 => None,
                _ => panic!("unexpected tag for Option type {tag}"),
            }
        }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            match self {
                Some(t) => {
                    t.to_vm_unsafe(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 0);
                }
                None => {
                    ().to_vm_unsafe(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 1);
                }
            }
        }
    }
}

impl<T, E> VmFfiType for Result<T, E>
where
    T: VmFfiType,
    E: VmFfiType,
{
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            (vm_funcs.deconstruct_variant)(vm);
            let tag = (vm_funcs.pop_int)(vm);
            match tag {
                0 => {
                    let t = T::from_vm_unsafe(vm, vm_funcs);
                    Ok(t)
                }
                1 => {
                    let e = E::from_vm_unsafe(vm, vm_funcs);
                    Err(e)
                }
                _ => panic!("unexpected tag for Result type {tag}"),
            }
        }
    }

    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            match self {
                Ok(t) => {
                    t.to_vm_unsafe(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 0);
                }
                Err(e) => {
                    e.to_vm_unsafe(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 1);
                }
            }
        }
    }
}

impl<T> VmFfiType for Vec<T>
where
    T: VmFfiType,
{
    unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            let len = (vm_funcs.array_len)(vm);
            (vm_funcs.deconstruct_array)(vm);
            let mut ret = vec![];
            for _ in 0..len {
                let val = <T>::from_vm_unsafe(vm, vm_funcs);
                ret.push(val);
            }
            ret
        }
    }
    unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            let len = self.len();
            for elem in self.into_iter() {
                elem.to_vm_unsafe(vm, vm_funcs);
            }
            (vm_funcs.construct_array)(vm, len);
        }
    }
}

macro_rules! replace_expr {
    ($t:tt, $e:expr_2021) => {
        $e
    };
}

macro_rules! tuple_impls {
    ( $( $name:ident ),+ $(,)? ) => {
        impl< $($name: VmFfiType),+ > VmFfiType for ( $($name,)+ ) {
            unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self { unsafe {
                // Deconstruct the tuple on the VM.
                (vm_funcs.deconstruct_struct)(vm);
                // Pop values in normal order.
                #[allow(non_snake_case)]
                let ($($name,)+) = ($( $name::from_vm_unsafe(vm, vm_funcs), )+);
                ($($name,)+)
            }}
            unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) { unsafe {
                // Destructure the tuple.
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                // Push each element onto the VM in order.
                $( $name.to_vm_unsafe(vm, vm_funcs); )+
                // Count the number of elements in the tuple.
                let count: usize = [$( replace_expr!($name, 1) ),+].len();
                // Reconstruct the tuple on the VM.
                (vm_funcs.construct_struct)(vm, count);
            }}
        }
    };
}

tuple_impls!(A);
tuple_impls!(A, B);
tuple_impls!(A, B, C);
tuple_impls!(A, B, C, D);
tuple_impls!(A, B, C, D, E);
tuple_impls!(A, B, C, D, E, F);
tuple_impls!(A, B, C, D, E, F, G);
tuple_impls!(A, B, C, D, E, F, G, H);
tuple_impls!(A, B, C, D, E, F, G, H, I);
tuple_impls!(A, B, C, D, E, F, G, H, I, J);
tuple_impls!(A, B, C, D, E, F, G, H, I, J, K);
tuple_impls!(A, B, C, D, E, F, G, H, I, J, K, L);
