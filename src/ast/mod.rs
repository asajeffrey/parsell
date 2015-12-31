pub struct Export {
    pub name: String,
    pub func: String,
}

pub enum Expr {
    Add(Typ,Box<Expr>,Box<Expr>),
    Return(usize),
}

pub struct Function {
    pub name: String,
    pub params: Vec<Var>,
    pub result: Option<Typ>,
    pub locals: Vec<Var>,
    pub body: Vec<Expr>,
}

pub struct Import {
    pub func: String,
    pub module: String,
    pub name: String,
}

pub struct Memory {
    pub init: usize,
    pub max: Option<usize>,
    pub segments: Vec<Segment>,
}

pub struct Module {
    pub memory: Option<Memory>,
    pub functions: Vec<Function>,
}

pub struct Segment {
    pub addr: usize,
    pub data: String,
}

pub enum Typ {
    I32,
    I64,
    F32,
    F64,
}


pub struct Var {
    pub name: String,
    pub typ: Typ,
}
