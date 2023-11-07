use std::{cell::RefCell, collections::HashMap, rc::Rc};

use environment::Environment;
use side_effects::EffectTrait;

use debug_print::debug_println;

pub mod ast;
pub mod environment;
pub mod eval_tree;
pub mod interpreter;
mod operators;
pub mod side_effects;
pub mod statics;
pub mod translate;

use interpreter::{Interpreter, OverloadedFuncMap};

pub fn abra_hello_world() {
    println!("Hello, world!");
}

pub struct SourceFile {
    pub name: String,
    pub contents: String,
}

pub fn compile<Effect: EffectTrait>(source_files: Vec<SourceFile>) -> Result<Runtime, String> {
    // TODO remove this source files conversion garbage
    let mut filename_to_source = HashMap::new();
    let mut filenames = Vec::new();
    for source_file in source_files {
        filenames.push(source_file.name.clone());
        filename_to_source.insert(source_file.name, source_file.contents);
    }
    let sources = ast::Sources {
        filename_to_source,
        files: filenames,
    };

    let toplevels = ast::parse_or_err(&sources)?;

    debug_println!("successfully parsed.");
    let mut node_map = ast::NodeMap::new();
    for parse_tree in &toplevels {
        ast::initialize_node_map(&mut node_map, &(parse_tree.clone() as Rc<dyn ast::Node>));
    }
    debug_println!("initialized node map.");
    let mut inference_ctx = statics::InferenceContext::new();
    let tyctx = statics::make_new_gamma();
    for parse_tree in &toplevels {
        statics::gather_definitions_toplevel(&mut inference_ctx, tyctx.clone(), parse_tree.clone());
    }
    for parse_tree in &toplevels {
        statics::generate_constraints_toplevel(
            tyctx.clone(),
            parse_tree.clone(),
            &mut inference_ctx,
        );
    }
    debug_println!("generated constraints.");
    statics::result_of_constraint_solving(&mut inference_ctx, tyctx.clone(), &node_map, &sources)?;

    debug_println!("solved constraints.");
    let env: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Environment::new(None)));
    let (eval_tree, overloaded_func_map) =
        translate::translate(&inference_ctx, tyctx, &node_map, &toplevels, env.clone());
    interpreter::add_builtins_and_variants::<side_effects::Effect>(env.clone(), &inference_ctx);
    Ok(Runtime {
        toplevel_eval_tree: eval_tree,
        toplevel_env: env,
        overloaded_func_map,
    })
}

pub struct Runtime {
    toplevel_eval_tree: Rc<eval_tree::Expr>,
    toplevel_env: Rc<RefCell<Environment>>,
    overloaded_func_map: OverloadedFuncMap,
}

impl Runtime {
    pub fn toplevel_interpreter(&self) -> Interpreter {
        Interpreter::new(
            self.overloaded_func_map.clone(),
            self.toplevel_eval_tree.clone(),
            self.toplevel_env.clone(),
        )
    }

    pub fn func_interpreter(&self, func_name: &str, args: Vec<Rc<eval_tree::Expr>>) -> Interpreter {
        let func = self
            .toplevel_env
            .borrow()
            .lookup(&func_name.to_string())
            .unwrap();
        let func_ap = eval_tree::Expr::FuncAp(func, args, None);
        Interpreter::new(
            self.overloaded_func_map.clone(),
            Rc::new(func_ap),
            self.toplevel_env.clone(),
        )
    }

    pub fn make_int(&self, i: i32) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Int(i))
    }

    pub fn make_bool(&self, b: bool) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Bool(b))
    }

    pub fn make_tuple(&self, elems: Vec<Rc<eval_tree::Expr>>) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Tuple(elems))
    }
}
