use anyhow::Result;
use std::collections::{HashMap, HashSet};
use serde::{Serialize, Deserialize};

/// OPKIND enum matching exactly the C symbolic-struct.h definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OpKind {
    Reserved = 0,
    IsConst = 1,
    IsSymbolic = 2,
    // Unary
    Neg = 3,
    Not = 4,
    // Binary
    Add = 5,
    Sub = 6,
    Mul = 7,
    Mulu = 8,
    Div = 9,
    Divu = 10,
    Rem = 11,
    Remu = 12,
    And = 13,
    Or = 14,
    Xor = 15,
    Shl = 16,
    Shr = 17,
    Sar = 18,
    Sal = 19,
    Rotl = 20,
    Rotr = 21,
    // Comparison
    Eq = 22,
    Ne = 23,
    Lt = 24,
    Le = 25,
    Ge = 26,
    Gt = 27,
    Ltu = 28,
    Leu = 29,
    Geu = 30,
    Gtu = 31,
    // Extensions
    Zext = 32,
    Sext = 33,
    // Concatenation and extraction
    Concat = 34,
    Concat8L = 35,
    Concat8R = 36,
    Extract8 = 37,
    Extract = 38,
    // Ternary
    Deposit = 39,
    QzExtract = 40,
    QsExtract = 41,
    QzExtract2 = 42,
    // Bit operations
    Ctz = 43,
    Clz = 44,
    Bswap = 45,
    Rcl = 46,
    Andc = 47,
    // Conditional
    Ite = 48,
    IteEqZero = 49,
    IteNeZero = 50,
    Or3 = 51,
    Xor3 = 52,
    // XMM operations
    Pmovmskb = 53,
    CmpEq = 54,
    CmpGt = 55,
    CmpGe = 56,
    CmpLe = 57,
    CmpLt = 58,
    Min = 59,
    Max = 60,
    SignedSaturation = 61,
    UnsignedSaturation = 62,
    Nand = 63,
    // Double operations
    MulHigh = 64,
    MuluHigh = 65,
    // EFLAGS operations (66-86)
    EflagsAllAdd = 66,
    EflagsAllAdcb = 67,
    EflagsAllAdcw = 68,
    EflagsAllAdcl = 69,
    EflagsAllAdcq = 70,
    EflagsAllSub = 71,
    EflagsAllMul = 72,
    EflagsAllSbbb = 73,
    EflagsAllSbbw = 74,
    EflagsAllSbbl = 75,
    EflagsAllSbbq = 76,
    EflagsAllLogic = 77,
    EflagsAllInc = 78,
    EflagsAllDec = 79,
    EflagsAllShl = 80,
    EflagsAllSar = 81,
    EflagsAllBmilg = 82,
    EflagsAllAdcx = 83,
    EflagsAllAdox = 84,
    EflagsAllAdcox = 85,
    EflagsAllRcl = 86,
    // EFLAGS C operations (87-100)
    EflagsCAdd = 87,
    EflagsCAdcb = 88,
    EflagsCAdcw = 89,
    EflagsCAdcl = 90,
    EflagsCAdcq = 91,
    EflagsCSub = 92,
    EflagsCMul = 93,
    EflagsCSbbb = 94,
    EflagsCSbbw = 95,
    EflagsCSbbl = 96,
    EflagsCSbbq = 97,
    EflagsCLogic = 98,
    EflagsCShl = 99,
    EflagsCBmilg = 100,
    // Symbolic operations
    SymbolicPc = 101,
    SymbolicJumpTableAccess = 102,
    MemorySlice = 103,
    MemorySliceAccess = 104,
    MemoryInputSliceAccess = 105,
    SymbolicLoad = 106,
    SymbolicStore = 107,
    MemoryConcretization = 108,
    ConsistencyCheck = 109,
    InputSlice = 110,
    // Movement
    Mov = 111,
    // Model
    Model = 112,
}

impl TryFrom<u8> for OpKind {
    type Error = anyhow::Error;
    
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(OpKind::Reserved),
            1 => Ok(OpKind::IsConst),
            2 => Ok(OpKind::IsSymbolic),
            3 => Ok(OpKind::Neg),
            4 => Ok(OpKind::Not),
            5..=100 => Ok(match value {
                5 => OpKind::Add,
                6 => OpKind::Sub,
                7 => OpKind::Mul,
                8 => OpKind::Mulu,
                9 => OpKind::Div,
                10 => OpKind::Divu,
                11 => OpKind::Rem,
                12 => OpKind::Remu,
                13 => OpKind::And,
                14 => OpKind::Or,
                15 => OpKind::Xor,
                16 => OpKind::Shl,
                17 => OpKind::Shr,
                18 => OpKind::Sar,
                19 => OpKind::Sal,
                20 => OpKind::Rotl,
                21 => OpKind::Rotr,
                22 => OpKind::Eq,
                23 => OpKind::Ne,
                24 => OpKind::Lt,
                25 => OpKind::Le,
                26 => OpKind::Ge,
                27 => OpKind::Gt,
                28 => OpKind::Ltu,
                29 => OpKind::Leu,
                30 => OpKind::Geu,
                31 => OpKind::Gtu,
                32 => OpKind::Zext,
                33 => OpKind::Sext,
                34 => OpKind::Concat,
                35 => OpKind::Concat8L,
                36 => OpKind::Concat8R,
                37 => OpKind::Extract8,
                38 => OpKind::Extract,
                39 => OpKind::Deposit,
                40 => OpKind::QzExtract,
                41 => OpKind::QsExtract,
                42 => OpKind::QzExtract2,
                43 => OpKind::Ctz,
                44 => OpKind::Clz,
                45 => OpKind::Bswap,
                46 => OpKind::Rcl,
                47 => OpKind::Andc,
                48 => OpKind::Ite,
                49 => OpKind::IteEqZero,
                50 => OpKind::IteNeZero,
                51 => OpKind::Or3,
                52 => OpKind::Xor3,
                53 => OpKind::Pmovmskb,
                54 => OpKind::CmpEq,
                55 => OpKind::CmpGt,
                56 => OpKind::CmpGe,
                57 => OpKind::CmpLe,
                58 => OpKind::CmpLt,
                59 => OpKind::Min,
                60 => OpKind::Max,
                61 => OpKind::SignedSaturation,
                62 => OpKind::UnsignedSaturation,
                63 => OpKind::Nand,
                64 => OpKind::MulHigh,
                65 => OpKind::MuluHigh,
                66 => OpKind::EflagsAllAdd,
                67 => OpKind::EflagsAllAdcb,
                68 => OpKind::EflagsAllAdcw,
                69 => OpKind::EflagsAllAdcl,
                70 => OpKind::EflagsAllAdcq,
                71 => OpKind::EflagsAllSub,
                72 => OpKind::EflagsAllMul,
                73 => OpKind::EflagsAllSbbb,
                74 => OpKind::EflagsAllSbbw,
                75 => OpKind::EflagsAllSbbl,
                76 => OpKind::EflagsAllSbbq,
                77 => OpKind::EflagsAllLogic,
                78 => OpKind::EflagsAllInc,
                79 => OpKind::EflagsAllDec,
                80 => OpKind::EflagsAllShl,
                81 => OpKind::EflagsAllSar,
                82 => OpKind::EflagsAllBmilg,
                83 => OpKind::EflagsAllAdcx,
                84 => OpKind::EflagsAllAdox,
                85 => OpKind::EflagsAllAdcox,
                86 => OpKind::EflagsAllRcl,
                87 => OpKind::EflagsCAdd,
                88 => OpKind::EflagsCAdcb,
                89 => OpKind::EflagsCAdcw,
                90 => OpKind::EflagsCAdcl,
                91 => OpKind::EflagsCAdcq,
                92 => OpKind::EflagsCSub,
                93 => OpKind::EflagsCMul,
                94 => OpKind::EflagsCSbbb,
                95 => OpKind::EflagsCSbbw,
                96 => OpKind::EflagsCSbbl,
                97 => OpKind::EflagsCSbbq,
                98 => OpKind::EflagsCLogic,
                99 => OpKind::EflagsCShl,
                100 => OpKind::EflagsCBmilg,
                _ => unreachable!(),
            }),
            101..=112 => Ok(match value {
                101 => OpKind::SymbolicPc,
                102 => OpKind::SymbolicJumpTableAccess,
                103 => OpKind::MemorySlice,
                104 => OpKind::MemorySliceAccess,
                105 => OpKind::MemoryInputSliceAccess,
                106 => OpKind::SymbolicLoad,
                107 => OpKind::SymbolicStore,
                108 => OpKind::MemoryConcretization,
                109 => OpKind::ConsistencyCheck,
                110 => OpKind::InputSlice,
                111 => OpKind::Mov,
                112 => OpKind::Model,
                _ => unreachable!(),
            }),
            _ => anyhow::bail!("Invalid OpKind value: {}", value),
        }
    }
}

/// EXTENDKIND enum matching C definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExtendKind {
    Zext8 = 0,
    Zext16 = 1,
    Zext32 = 2,
    Sext8 = 3,
    Sext16 = 4,
    Sext32 = 5,
}

/// MODEL_T enum matching C definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModelType {
    Strcmp = 0,
    Strlen = 1,
    Memchr = 2,
    Memcmp = 3,
    Malloc = 4,
    Calloc = 5,
    Realloc = 6,
}

/// C-compatible Expr struct matching symbolic-struct.h exactly
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Expr {
    pub op1: *mut Expr,
    pub op2: *mut Expr,
    pub op3: *mut Expr,
    pub opkind: u8,
    pub op1_is_const: u8,
    pub op2_is_const: u8,
    pub op3_is_const: u8,
}

/// QueryArgs8 struct matching C definition (fields arg0..arg7)
#[repr(C)]
#[derive(Default, Debug, Clone, Copy)]
pub struct QueryArgs8 {
    pub arg0: u8,
    pub arg1: u8,
    pub arg2: u8,
    pub arg3: u8,
    pub arg4: u8,
    pub arg5: u8,
    pub arg6: u8,
    pub arg7: u8,
}

/// Query union args matching C definition
#[repr(C)]
pub union QueryArgs {
    pub args8: std::mem::ManuallyDrop<QueryArgs8>,
    pub args64: usize,
    pub model: ModelType,
}

/// QueryArgs16 struct for packed arguments
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct QueryArgs16 {
    pub index: u16,
    pub count: u16,
    pub index_inv: u16,
    pub count_inv: u16,
}

/// QueryType enum matching C definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum QueryType {
    Branch = 0,
    Slice = 1,
    Model = 2,
    Dependency = 3,
}

/// Query structure matching C definition
/// Layout mirrors C (symbolic-struct.h):
/// struct Query { uintptr_t address; Expr* query; union { ... } args; uint8_t query_type; };
#[repr(C)]
pub struct Query {
    pub address: usize,
    pub query: *mut Expr,
    pub args: QueryArgs,
    pub query_type: QueryType,
}

impl Expr {
    /// Create a new constant expression
    pub fn new_const(value: usize) -> Self {
        Self {
            op1: value as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsConst as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new symbolic input expression
    pub fn new_symbolic(input_id: usize) -> Self {
        Self {
            op1: input_id as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new binary expression
    pub fn new_binary(opkind: OpKind, op1: *mut Expr, op2: *mut Expr) -> Self {
        Self {
            op1,
            op2,
            op3: std::ptr::null_mut(),
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }    
    /// Create a new unary expression
    pub fn new_unary(opkind: OpKind, op1: *mut Expr) -> Self {
        Self {
            op1,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new ternary expression
    pub fn new_ternary(opkind: OpKind, op1: *mut Expr, op2: *mut Expr, op3: *mut Expr) -> Self {
        Self {
            op1,
            op2,
            op3,
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Set operand as constant
    pub fn set_op1_const(&mut self, value: usize) {
        self.op1 = value as *mut Expr;
        self.op1_is_const = 1;
    }
    
    pub fn set_op2_const(&mut self, value: usize) {
        self.op2 = value as *mut Expr;
        self.op2_is_const = 1;
    }
    
    pub fn set_op3_const(&mut self, value: usize) {
        self.op3 = value as *mut Expr;
        self.op3_is_const = 1;
    }
    
    /// Get constant value from operand
    pub fn get_op1_const(&self) -> Option<usize> {
        if self.op1_is_const != 0 {
            Some(self.op1 as usize)
        } else {
            None
        }
    }
    
    pub fn get_op2_const(&self) -> Option<usize> {
        if self.op2_is_const != 0 {
            Some(self.op2 as usize)
        } else {
            None
        }
    }
    
    pub fn get_op3_const(&self) -> Option<usize> {
        if self.op3_is_const != 0 {
            Some(self.op3 as usize)
        } else {
            None
        }
    }
    
    /// Get operand size for operand at given index
    pub fn get_operand_size(&self, operand_index: usize) -> usize {
        match operand_index {
            0 => self.op1 as usize,
            1 => self.op2 as usize, 
            2 => self.op3 as usize,
            _ => 0,
        }
    }
}

/// Expression pool for managing shared expressions
pub struct ExprPool {
    expressions: Vec<Expr>,
    capacity: usize,
}

impl ExprPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            expressions: Vec::with_capacity(capacity),
            capacity,
        }
    }
    
    pub fn add_expr(&mut self, expr: Expr) -> Result<usize> {
        if self.expressions.len() >= self.capacity {
            anyhow::bail!("Expression pool is full");
        }
        
        let id = self.expressions.len();
        self.expressions.push(expr);
        Ok(id)
    }
    
    pub fn get_expr(&self, id: usize) -> Option<&Expr> {
        self.expressions.get(id)
    }
    
    pub fn len(&self) -> usize {
        self.expressions.len()
    }
}

/// Dependency tracking for expressions
#[derive(Debug, Clone)]
pub struct Dependency {
    pub inputs: HashSet<usize>,
    pub expressions: HashSet<usize>,
}

impl Dependency {
    pub fn new() -> Self {
        Self {
            inputs: HashSet::new(),
            expressions: HashSet::new(),
        }
    }
    
    pub fn add_input(&mut self, input_id: usize) {
        self.inputs.insert(input_id);
    }
    
    pub fn add_expression(&mut self, expr_id: usize) {
        self.expressions.insert(expr_id);
    }
    
    pub fn merge(&mut self, other: &Dependency) {
        self.inputs.extend(&other.inputs);
        self.expressions.extend(&other.expressions);
    }
}

/// Dependency graph for tracking expression relationships
pub struct DependencyGraph {
    dependencies: HashMap<usize, Dependency>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            dependencies: HashMap::new(),
        }
    }
    
    pub fn add_dependency(&mut self, input_id: usize, expr_id: usize) {
        let dep = self.dependencies.entry(input_id).or_insert_with(Dependency::new);
        dep.add_expression(expr_id);
    }
    
    pub fn get_dependency(&self, input_id: usize) -> Option<&Dependency> {
        self.dependencies.get(&input_id)
    }
    
    pub fn merge_dependencies(&self, inputs: &HashSet<usize>) -> Dependency {
        let mut merged = Dependency::new();
        
        for &input_id in inputs {
            merged.add_input(input_id);
            if let Some(dep) = self.dependencies.get(&input_id) {
                merged.merge(dep);
            }
        }
        
        merged
    }
}

impl Query {
    pub fn new() -> Self {
        Query {
            address: 0,
            query: std::ptr::null_mut(),
            args: QueryArgs { args8: std::mem::ManuallyDrop::new(QueryArgs8::default()) },
            query_type: QueryType::Branch, // Default
        }
    }
    
    pub fn get_index(&self) -> usize {
        unsafe { self.args.args64 } // Mirrors GET_QUERY_IDX(q) usage when index is stuffed here
    }
    
    pub fn get_query_type(&self) -> QueryType {
        self.query_type
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}
