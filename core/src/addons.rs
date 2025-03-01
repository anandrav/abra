// Rust addon API

use crate::vm::Vm;
use crate::{
    FileAst, FileData, ItemKind,
    ast::{FileDatabase, PatKind, Type, TypeDefKind, TypeKind},
    parse::parse_or_err,
};
use core::str;
use std::{
    ffi::{c_char, c_void},
    fs::{self, read_to_string},
    path::{Path, PathBuf},
    rc::Rc,
};

// TODO: Move this to a separate crate entirely
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
    pub construct: unsafe extern "C" fn(vm: *mut c_void, arity: u16),
    pub construct_variant: unsafe extern "C" fn(vm: *mut c_void, tag: u16),
    pub deconstruct: unsafe extern "C" fn(vm: *mut c_void),
}

impl AbraVmFunctions {
    pub fn new() -> Self {
        AbraVmFunctions {
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
            construct: abra_vm_construct,
            construct_variant: abra_vm_construct_variant,
            deconstruct: abra_vm_deconstruct,
        }
    }
}

impl Default for AbraVmFunctions {
    fn default() -> Self {
        Self::new()
    }
}

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
    // println!("pushing bool {}", b);
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
    vm.pop().unwrap();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_int(vm: *mut c_void) -> i64 {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_int(vm).unwrap();
    vm.pop().unwrap();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_float(vm: *mut c_void) -> f64 {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_float(vm).unwrap();
    vm.pop().unwrap();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop_bool(vm: *mut c_void) -> bool {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    let top = vm.top().get_bool(vm).unwrap();
    vm.pop().unwrap();
    top
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_pop(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.pop().unwrap();
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
    // println!("pushing string to stack: {}", s);
    vm.push_str(s);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_construct(vm: *mut c_void, arity: u16) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.construct_struct(arity);
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_construct_variant(vm: *mut c_void, tag: u16) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.construct_variant(tag).unwrap();
}

/// # Safety
/// vm: *mut c_void must be valid and non-null
#[unsafe(no_mangle)]
unsafe extern "C" fn abra_vm_deconstruct(vm: *mut c_void) {
    let vm = unsafe { (vm as *mut Vm).as_mut().unwrap() };
    vm.deconstruct().unwrap();
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
    let mut prefixes = vec![package_name.clone()];
    find_abra_files(&package_dir, &mut prefixes, &mut file_db, &mut output).unwrap();

    // write_footer
    {
        output.push_str(
            r#" 
    }
}
"#,
        );
    }

    let out_dir: PathBuf = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    // let proper_output_path = out_dir.join("gen.rs");

    let output_path = current_dir.join("src").join("lib.rs");

    std::fs::write(&output_path, output).unwrap();

    let status = std::process::Command::new("rustfmt")
        .arg(&output_path)
        .status()
        .expect("failed to run rustfmt");

    if !status.success() {
        panic!("rustfmt failed on {:?}", output_path);
    }

    // panic!("current_dir={}", current_dir.to_str().unwrap());
}

fn write_header(output: &mut String, package_name: &str) {
    output.push_str(&format!(
        r#"// This is an auto-generated file.
        
        mod {};
        pub mod ffi {{
            pub mod {} {{
            use crate::{};
            use abra_core::addons::*;
            use std::ffi::c_void;
            "#,
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
                    for field in &s.fields {
                        let tyname = name_of_ty(field.ty.clone());
                        output.push_str(&format!(
                            r#"pub {}: {},
                        "#,
                            field.name.v, tyname
                        ));
                    }
                    output.push_str("}");

                    output.push_str(&format!(
                        r#"impl VmType for {} {{
                    "#,
                        s.name.v
                    ));
                    output.push_str(
                        r#"unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                        "#,
                    );
                    output.push_str("unsafe {");
                    output.push_str("(vm_funcs.deconstruct)(vm);");
                    for field in s.fields.iter().rev() {
                        let tyname = name_of_ty(field.ty.clone());
                        output.push_str(&format!(
                            r#"let {} = <{}>::from_vm(vm, vm_funcs);
                        "#,
                            field.name.v, tyname
                        ));
                    }
                    output.push_str(
                        r#"Self {
                    "#,
                    );
                    for field in &s.fields {
                        output.push_str(&format!("{},", field.name.v));
                    }
                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                        "#,
                    );
                    output.push_str("unsafe {");
                    // TODO: impl for all types
                    for field in s.fields.iter() {
                        output.push_str(&format!(
                            r#"self.{}.to_vm(vm, vm_funcs);
                        "#,
                            field.name.v
                        ));
                    }

                    output.push_str(&format!("(vm_funcs.construct)(vm, {});", s.fields.len()));

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
                TypeDefKind::Enum(e) => {
                    output.push_str(&format!(
                        r#"pub enum {} {{
                    "#,
                        e.name.v
                    ));
                    for variant in &e.variants {
                        output.push_str(&format!(
                            r#"{}
                        "#,
                            variant.ctor.v
                        ));
                        if let Some(ty) = &variant.data {
                            output.push('(');
                            output.push_str(&name_of_ty(ty.clone()));
                            output.push(')');
                        }
                        output.push(',');
                    }
                    output.push('}');

                    output.push_str(&format!(
                        r#"impl VmType for {} {{
                    "#,
                        e.name.v
                    ));
                    output.push_str(
                        r#"unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                        "#,
                    );

                    output.push_str("unsafe {");
                    output.push_str("(vm_funcs.deconstruct)(vm);");
                    output.push_str("let tag = (vm_funcs.pop_int)(vm);");
                    output.push_str("match tag {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        output.push_str(&format!("{} => {{", i));
                        if let Some(ty) = &variant.data {
                            let tyname = name_of_ty(ty.clone());
                            output.push_str(&format!(
                                r#"let value: {} = <{}>::from_vm(vm, vm_funcs);
                            "#,
                                tyname, tyname
                            ));
                            output.push_str(&format!("{}::{}(value)", e.name.v, variant.ctor.v));
                        } else {
                            output.push_str("(vm_funcs.pop_nil)(vm);");
                            output.push_str(&format!("{}::{}", e.name.v, variant.ctor.v));
                        }
                        output.push('}');
                    }
                    output.push_str(r#"_ => panic!("unexpected tag encountered: {}", tag)"#);

                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                        "#,
                    );
                    output.push_str("unsafe {");

                    output.push_str("match self {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        if variant.data.is_some() {
                            output.push_str(&format!(
                                "{}::{}(value) => {{",
                                e.name.v, variant.ctor.v
                            ));
                            output.push_str("value.to_vm(vm, vm_funcs);");
                            output.push_str(&format!("(vm_funcs.construct_variant)(vm, {});", i));
                        } else {
                            output.push_str(&format!("{}::{} => {{", e.name.v, variant.ctor.v));
                            output.push_str("(vm_funcs.push_nil)(vm);");
                            output.push_str(&format!("(vm_funcs.construct_variant)(vm, {});", i));
                        }
                        output.push('}');
                    }
                    output.push('}');

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
                _ => unimplemented!(),
            },
            ItemKind::ForeignFuncDecl(f) => {
                output.push_str(
                    r#"/// # Safety
                              /// `vm` must be non-null and valid.
                              "#,
                );
                // TODO: duplicated with code in resolve.rs
                let elems: Vec<_> = ast.name.split(std::path::MAIN_SEPARATOR_STR).collect();
                let package_name = elems.last().unwrap().to_string();
                let mut symbol = "abra_ffi".to_string();
                for elem in elems {
                    symbol.push('$');
                    symbol.push_str(elem);
                }
                symbol.push('$');
                symbol.push_str(&f.name.v);

                output.push_str(&format!("#[unsafe(export_name = \"{}\")]", symbol));
                output.push_str(&format!(
                    "pub unsafe extern \"C\" fn {}(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {{",
                    f.name.v,
                ));
                output.push_str("unsafe {");
                // output.push_str(&format!(
                //     r#"println!("{}()"); panic!("ruh roh");"#,
                //     f.name.v
                // ));
                output.push_str("let vm_funcs: &AbraVmFunctions = &*vm_funcs;");
                // get args in reverse order
                for (name, ty) in f.args.iter().rev() {
                    // TODO: why the fuck is name a Pat still.
                    let PatKind::Binding(ident) = &*name.kind else {
                        panic!()
                    };
                    // TODO: ty shouldn't be optional for foreign fn
                    let ty = ty.clone().unwrap();
                    let tyname = name_of_ty(ty);
                    output.push_str(&format!(
                        "let {} = <{}>::from_vm(vm, vm_funcs);",
                        ident, tyname
                    ));
                }
                // call the user's implementation
                let out_ty = &f.ret_type;
                let out_ty_name = name_of_ty(out_ty.clone());
                output.push_str(&format!(
                    "let ret: {} = {}::{}(",
                    out_ty_name, package_name, f.name.v
                ));
                for (name, _) in f.args.iter() {
                    // TODO: why the fuck is name a Pat still.
                    let PatKind::Binding(ident) = &*name.kind else {
                        panic!()
                    };
                    output.push_str(&format!("{},", ident));
                }
                output.push_str(");");
                // push return value
                output.push_str("ret.to_vm(vm, vm_funcs);");
                output.push('}');
                output.push('}');
            }
            _ => {}
        }
    }
}

fn name_of_ty(ty: Rc<Type>) -> String {
    match &*ty.kind {
        TypeKind::Bool => "bool".to_string(),
        TypeKind::Float => "f64".to_string(),
        TypeKind::Int => "i64".to_string(),
        TypeKind::Str => "String".to_string(),
        TypeKind::Identifier(s) => s.clone(),
        TypeKind::Unit => "()".to_string(),
        TypeKind::Tuple(elems) => {
            let mut s = "(".to_string();
            for elem in elems {
                s.push_str(&name_of_ty(elem.clone()));
                s.push(',');
            }
            s.push(')');
            s
        }
        TypeKind::Ap(ident, params) => {
            // special-case
            let mut s = ident.v.clone();
            if s == "maybe" {
                s = "Result".into();
            }
            s.push('<');
            for param in params {
                s.push_str(&name_of_ty(param.clone()));
                s.push(',');
            }
            s.push('>');
            s
        }
        TypeKind::Function(..) | TypeKind::Poly(..) => {
            format!("<{:?} not supported>", ty.kind)
        }
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
                    r#" pub mod {} {{
                        use crate::{};
                        use abra_core::addons::*;
                        use std::ffi::c_void;
                        "#,
                    no_extension, crate_import
                ));

                let source = read_to_string(&path).unwrap();
                let mut nominal_path = PathBuf::new();
                for prefix in prefixes.iter() {
                    nominal_path = nominal_path.join(prefix);
                }
                nominal_path = nominal_path.join(format!("{}.abra", no_extension));
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

pub trait VmType {
    /// # Safety
    /// vm is non-null and valid
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self;

    /// # Safety
    /// vm is non-null and valid
    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions);
}

impl VmType for i64 {
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_int)(vm) }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_int)(vm, self);
        }
    }
}

impl VmType for f64 {
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_float)(vm) }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_float)(vm, self);
        }
    }
}

impl VmType for () {
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop)(vm) }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_nil)(vm);
        }
    }
}

impl VmType for bool {
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe { (vm_funcs.pop_bool)(vm) }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            (vm_funcs.push_bool)(vm, self);
        }
    }
}

impl VmType for String {
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            let string_view = (vm_funcs.view_string)(vm);
            let content = string_view.to_owned();
            (vm_funcs.pop)(vm);
            content
        }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            let string_view = StringView::from_string(&self);
            (vm_funcs.push_string)(vm, string_view);
        }
    }
}

impl<T, E> VmType for Result<T, E>
where
    T: VmType,
    E: VmType,
{
    unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
        unsafe {
            (vm_funcs.deconstruct)(vm);
            let tag = (vm_funcs.pop_int)(vm);
            match tag {
                0 => {
                    let t = T::from_vm(vm, vm_funcs);
                    Ok(t)
                }
                1 => {
                    let e = E::from_vm(vm, vm_funcs);
                    Err(e)
                }
                _ => panic!("unexpected tag for Result type {}", tag),
            }
        }
    }

    unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
        unsafe {
            match self {
                Ok(t) => {
                    t.to_vm(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 0);
                }
                Err(e) => {
                    e.to_vm(vm, vm_funcs);
                    (vm_funcs.construct_variant)(vm, 1);
                }
            }
        }
    }
}

// A helper macro to replace a token with an expression (for counting)
macro_rules! replace_expr {
    ($t:tt, $e:expr_2021) => {
        $e
    };
}

// Our main macro: for a list of identifiers, implement VmType for the corresponding tuple.
macro_rules! tuple_impls {
    ( $( $name:ident ),+ $(,)? ) => {
        impl< $($name: VmType),+ > VmType for ( $($name,)+ ) {
            unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self { unsafe {
                // Deconstruct the tuple on the VM.
                (vm_funcs.deconstruct)(vm);
                // Pop values in reverse order.
                tuple_impls!(@reverse vm, vm_funcs, $($name),+);
                // Now rebuild the tuple (using the identifiers in the original order).
                ($($name,)+)
            }}
            unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) { unsafe {
                // Destructure the tuple.
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                // Push each element onto the VM in order.
                $( $name.to_vm(vm, vm_funcs); )+
                // Count the number of elements in the tuple.
                let count: usize = [$( replace_expr!($name, 1) ),+].len();
                // Reconstruct the tuple on the VM.
                (vm_funcs.construct)(vm, count as u16);
            }}
        }
    };

    // Helper rule to generate from_vm calls in reverse order.
    (@reverse $vm:expr_2021, $vm_funcs:expr_2021, $x:ident) => {
        #[allow(non_snake_case)]
        let $x = $x::from_vm($vm, $vm_funcs);
    };
    (@reverse $vm:expr_2021, $vm_funcs:expr_2021, $x:ident, $($rest:ident),+) => {
        tuple_impls!(@reverse $vm, $vm_funcs, $($rest),+);
        #[allow(non_snake_case)]
        let $x = $x::from_vm($vm, $vm_funcs);
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
