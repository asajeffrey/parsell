use nom::{digit,multispace};
use ast::{Export,Expr,Function,Import,Memory,Module,Segment,Typ,Var};
use std::str;
use std::str::FromStr;

// Separators

named!(pub multi_line_comment<()>,
    chain!(
        tag!("(;") ~
        take_until_and_consume!(";)") ,
        || {}
    )
);

named!(pub one_line_comment<()>,
    chain!(
        tag!(";;") ~
        take_until_either_and_consume!("\r\n") ,
        || {}
    )
);

named!(pub whitespace<()>,
    chain!(
        multispace,
        || {}
    )
);

named!(pub sep<()>,
    chain!(
        many0!(alt!(whitespace | one_line_comment | multi_line_comment)),    
        || {}
    )
);   

// Literals

named!(pub string_literal<&str>,
    delimited!(
        tag!("\""),
        map_res!(take_until!("\""), str::from_utf8),
        tag!("\"")
    )
);

named!(pub usize_literal<usize>,
    map_res!(
        map_res!(digit, str::from_utf8),
        |string| { usize::from_str(string) }
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
   preceded!(
        tag!("$"),   
        map_res!(take_while!(is_identifier_byte), str::from_utf8)
   )
);

// AST

named!(pub export<Export>,
    chain!(
        tag!("(") ~ sep ~
        tag!("export") ~ sep ~
name:   string_literal ~ sep ~    
func:   identifier ~ sep ~    
        tag!(")") ,
        || { Export{ name: name.to_owned(), func: func.to_owned() } }
    )
);

named!(pub expr<Expr>,
    alt!(
        expr_return |
        expr_add
    )
);

named!(pub expr_add<Expr>,
    chain!(
        tag!("(") ~ sep ~
typ:    typ ~ tag!(".add") ~ sep ~
lhs:    expr ~ sep ~
rhs:    expr ~ sep ~
        tag!(")") ,
        || { Expr::Add(typ,Box::new(lhs),Box::new(rhs)) }
    )
);

named!(pub expr_return<Expr>,
    chain!(
        tag!("(") ~ sep ~
        tag!("return") ~ sep ~
result: usize_literal ~ sep ~
        tag!(")") ,
        || { Expr::Return(result) }
    )
);

named!(pub function<Function>,
    chain!(
        tag!("(") ~ sep ~
        tag!("func") ~ sep ~
name:   identifier ~ sep ~
params: separated_list!(sep, param) ~ sep ~
result: opt!(result) ~ sep ~
locals: separated_list!(sep, local) ~ sep ~
body:   separated_list!(sep, expr) ~ sep ~
        tag!(")") ,
        || { Function{ name: name.to_owned(), params: params, result: result, locals: locals, body: body } }
    )
);

named!(pub import<Import>,
    chain!(
        tag!("(") ~ sep ~
        tag!("import") ~ sep ~
func:   identifier ~ sep ~    
module: string_literal ~ sep ~    
name:   string_literal ~ sep ~    
        tag!(")") ,
        || { Import{ func: func.to_owned(), module: module.to_owned(), name: name.to_owned() } }
    )
);

named!(pub local<Var>,
    chain!(
        tag!("(") ~ sep ~
        tag!("local") ~ sep ~
name:   identifier ~ sep ~
typ:    typ ~ sep ~
        tag!(")") ,
        || { Var{ name: name.to_owned(), typ: typ } }
    )
);      

named!(pub memory<Memory>,
    chain!(
        tag!("(") ~ sep ~
        tag!("memory") ~ sep ~
init:   usize_literal ~ sep ~
max:    opt!(usize_literal) ~ sep ~
segs:   separated_list!(sep, segment) ~ sep ~
        tag!(")")  ,
        || { Memory{ init: init, max: max, segments: segs } }
    )
);

named!(pub module<Module>,
    chain!(
        tag!("(") ~ sep ~
        tag!("module") ~ sep ~
mem:    opt!(memory) ~ sep ~ 
funcs:  separated_list!(sep, function) ~ sep ~ 
        tag!(")") ,
        || { Module{ memory: mem, functions: funcs } }
    )
);      

named!(pub param<Var>,
    chain!(
        tag!("(") ~ sep ~
        tag!("param") ~ sep ~
name:   identifier ~ sep ~
typ:    typ ~ sep ~
        tag!(")") ,
        || { Var{ name: name.to_owned(), typ: typ } }
    )
);      

named!(pub result<Typ>,
    chain!(
        tag!("(") ~ sep ~
        tag!("result") ~ sep ~
typ:    typ ~ sep ~
        tag!(")") ,
        || { typ }
    )
);      

named!(pub segment<Segment>,
    chain!(
        tag!("(") ~ sep ~
        tag!("segment") ~ sep ~
addr:   usize_literal ~ sep ~
data:   string_literal ~ sep ~
        tag!(")") ,
        || { Segment{ addr: addr, data: data.to_owned() } }
    )
);      

named!(pub typ<Typ>,
    alt!(
        map!(tag!("f32"), |_| { Typ::F32 }) |
        map!(tag!("f64"), |_| { Typ::F64 }) |
        map!(tag!("i32"), |_| { Typ::I32 }) |
        map!(tag!("i64"), |_| { Typ::I64 })
    )
);

// Top-level

named!(pub top_level<Module>,
    delimited!(sep, module, sep)
);    
