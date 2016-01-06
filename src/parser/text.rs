use nom::{digit,multispace,ErrorKind};
use ast::{Export,Expr,Function,Import,Memory,Module,Segment,Typ,Var,SExpression};
use std::str;
use std::str::FromStr;

// Error codes

const EXPORT_ERROR: u32 = 1;
const I32_ADD_ERROR: u32 = 2;
const RETURN_ERROR: u32 = 3;
const EXPR_ERROR: u32 = 4;
const FUNC_ERROR: u32 = 5;
const IMPORT_ERROR: u32 = 6;
const LOCAL_ERROR: u32 = 7;
const MEMORY_ERROR: u32 = 8;
const MODULE_ERROR: u32 = 9;
const PARAM_ERROR: u32 = 10;
const RESULT_ERROR: u32 = 11;
const SEGMENT_ERROR: u32 = 12;
const IDENTIFIER_ERROR: u32 = 13;

// Separators

named!(pub multi_line_comment,
    preceded!(
        tag!("(;"),
        take_until_and_consume!(";)")
    )
);

named!(pub one_line_comment,
    preceded!(
        tag!(";;"),
        take_until_either_and_consume!("\r\n")
    )
);

named!(pub sep,
    chain!(
        many0!(alt!(is_a!(" \t\r\n") | one_line_comment | multi_line_comment)),
        || { &b""[..] }
    )
);   

// Literals

named!(pub string_literal<&str>,
    // TODO: Escape sequences
    delimited!(
        tag!("\""),
        map_res!(take_until!("\""), str::from_utf8),
        terminated!(tag!("\""), sep)
    )
);

named!(pub usize_literal<usize>,
    // TODO: hex/octal
    terminated!(
        map_res!(map_res!(digit, str::from_utf8), usize::from_str),
        sep
    )
);

// Identifiers

fn is_identifier_byte(c : u8) -> bool {
    (c <= b'0' && b'9' <= c) ||
    (c <= b'a' && b'z' <= c) ||
    (c <= b'A' && b'Z' <= c) ||
    (c == b'_') || (c == b'.')
}

named!(pub identifier<&str>,
    error!(ErrorKind::Custom(IDENTIFIER_ERROR),delimited!(
        tag!("$"),
        map_res!(take_while!(is_identifier_byte), str::from_utf8),
        sep
    ))
);

// Types

named!(pub typ<Typ>,
    terminated!(alt!(
        map!(tag!("f32"), |_| { Typ::F32 }) |
        map!(tag!("f64"), |_| { Typ::F64 }) |
        map!(tag!("i32"), |_| { Typ::I32 }) |
        map!(tag!("i64"), |_| { Typ::I64 })
    ), sep)
);

// AST

named!(pub exports< Vec<Export> >,
    many0!(preceded!(terminated!(tag!("(export"), sep), error!(ErrorKind::Custom(EXPORT_ERROR), chain!(
name:   string_literal ~
func:   identifier ~
        terminated!(tag!(")"), sep),
        || { Export{ name: name.to_owned(), func: func.to_owned() } }
    ))))
);

named!(pub expr<Expr>,
    preceded!(tag!("("), error!(ErrorKind::Custom(EXPR_ERROR), alt!(
        expr_return |
        expr_i32_add
    )))
);

named!(pub exprs< Vec<Expr> >,
    many0!(expr)
);

named!(pub expr_i32_add<Expr>,
    preceded!(terminated!(tag!("i32.add"), sep), add_error!(ErrorKind::Custom(I32_ADD_ERROR), chain!(
lhs:    expr ~
rhs:    expr ~
        terminated!(tag!(")"), sep) ,
        || { Expr::Add(Typ::I32, Box::new(lhs), Box::new(rhs)) }
    )))
);

named!(pub expr_return<Expr>,
    preceded!(terminated!(tag!("return"), sep), add_error!(ErrorKind::Custom(RETURN_ERROR), chain!(
result: usize_literal ~
        terminated!(tag!(")"), sep),
        || { Expr::Return(result) }
    )))
);

named!(pub functions< Vec<Function> >,
    many0!(preceded!(terminated!(tag!("(func"), sep), error!(ErrorKind::Custom(FUNC_ERROR), chain!(
name:   identifier ~
params: params ~
result: result ~
locals: locals ~
body:   exprs ~
        terminated!(tag!(")"), sep),
        || { Function{ name: name.to_owned(), params: params, result: result, locals: locals, body: body } }
    ))))
);
    
named!(pub imports< Vec<Import> >,
    many0!(preceded!(terminated!(tag!("(import"), sep), error!(ErrorKind::Custom(IMPORT_ERROR), chain!(
func:   identifier ~
module: string_literal ~
name:   string_literal ~ 
        terminated!(tag!(")"), sep),
        || { Import{ func: func.to_owned(), module: module.to_owned(), name: name.to_owned() } }
    ))))
);

named!(pub locals< Vec<Var> >,
    many0!(preceded!(terminated!(tag!("(local"), sep), error!(ErrorKind::Custom(LOCAL_ERROR), chain!(
name:   identifier ~
typ:    typ ~
        terminated!(tag!(")"), sep),
        || { Var{ name: name.to_owned(), typ: typ } }
    ))))
);      

named!(pub memory< Option<Memory> >,
    opt!(preceded!(terminated!(tag!("(memory"), sep), error!(ErrorKind::Custom(MEMORY_ERROR), chain!(
init:   usize_literal ~
max:    opt!(usize_literal) ~
segs:   many0!(segment) ~
        terminated!(tag!(")"), sep), 
        || { Memory{ init: init, max: max, segments: segs } }
    ))))
);

named!(pub module<Module>,
    preceded!(terminated!(tag!("(module"), sep), add_error!(ErrorKind::Custom(MODULE_ERROR), chain!(
mem:    memory ~
imps:   imports ~
exps:   exports ~
funcs:  functions ~
        terminated!(tag!(")"), sep), 
        || { Module{ memory: mem, imports: imps, exports: exps, functions: funcs } }
    )))
);      

named!(pub params< Vec<Var> >,
    many0!(preceded!(terminated!(tag!("(param"), sep), error!(ErrorKind::Custom(PARAM_ERROR), chain!(
name:   identifier ~
typ:    typ ~
        terminated!(tag!(")"), sep), 
        || { Var{ name: name.to_owned(), typ: typ } }
    ))))
);      

named!(pub result< Option<Typ> >,
    opt!(preceded!(terminated!(tag!("(result"), sep), add_error!(ErrorKind::Custom(RESULT_ERROR), chain!(
typ:    typ ~
        terminated!(tag!(")"), sep), 
        || { typ }
    ))))
);      

named!(pub segment<Segment>,
    preceded!(terminated!(tag!("(segment"), sep), add_error!(ErrorKind::Custom(SEGMENT_ERROR), chain!(
addr:   usize_literal ~
data:   string_literal ~
        terminated!(tag!(")"), sep), 
        || { Segment{ addr: addr, data: data.to_owned() } }
    )))
);      

// Top-level

named!(pub top_level<Module>,
   add_error!(ErrorKind::Custom(MODULE_ERROR), preceded!(sep, module))
);    
