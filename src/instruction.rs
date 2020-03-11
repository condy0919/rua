//! We assume that instructions are unsigned numbers. All instructions have an
//! opcode in the first 6 bits. Instruction can have the following modes:
//!
//! ```plain
//! | mode  | 31 .. 23 | 22 .. 14 | 13 .. 6 | 5 .. 0    |
//! |-------+----------+----------+---------+-----------|
//! | iABC  | B: 9     | C: 9     | A: 8    | OpCode: 6 |
//! | iABx  |        Bx: 18       | A: 8    | OpCode: 6 |
//! | iAsBx |       sBx: 18       | A: 8    | OpCode: 6 |
//! | iAx   |            Ax: 26             | OpCode: 6 |
//! ```
//!
//! `A`, `B`, `C`, `Ax`, `Bx` are unsinged while `sBx` is singed.
//!
//! A signed argument is represented in excess K; that is the number value is
//! the unsigned value minus K. K is exactly the maximum value for the argument
//! (so that -max is represented by 0, and +max is represented by 2 * max),
//! which is half the maximum for the corresponding unsigned argument.

pub type RegisterIndex = i16;
pub type ConstantIndex = i16;
pub type ConstantIndex18 = i32;

/// Register/Constant
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum RK {
    RegisterIndex(i16),
    ConstantIndex(i16),
}

/// TODO
///
/// Instruction
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Instruction {
    /// R(A) := R(B)
    Move {
        dst: RegisterIndex,
        src: RegisterIndex,
    },
    /// R(A) := Kst(Bx)
    LoadConstant {
        dst: RegisterIndex,
        kst: ConstantIndex18,
    },
    /// TODO
    /// R(A) := Kst(extra arg)
    ///
    /// The next instruction is always `EXTRAARG`
    LoadConstantExtra {},
    /// R(A) := (bool)B;
    /// if (C) pc++
    LoadBool {
        dst: RegisterIndex,
        value: bool,
        // If true, unconditionally skip the next instruction
        skip_next: bool,
    },
    /// R(A), R(A+1), ..., R(A+B) := nil
    LoadNil { dst: RegisterIndex, count: u16 },
    /// R(A) := UpValue[B]
    GetUpValue { dst: RegisterIndex, idx: u16 },
    /// R(A) := UpValue[B][RK(C)]
    GetUpTable {
        dst: RegisterIndex,
        table: u16,
        key: RK,
    },
    /// R(A) := R(B)[RK(C)]
    GetTable {
        dst: RegisterIndex,
        table: u16,
        key: RK,
    },
    /// UpValue[A][RK(B)] := RK(C)
    SetUpTable {
        table: RegisterIndex,
        key: RK,
        value: RK,
    },
    /// UpValue[B] := R(A)
    SetUpValue { dst: u16, src: RegisterIndex },
    /// R(A)[RK(B)] := RK(C)
    SetTable {
        table: RegisterIndex,
        key: RK,
        value: RK,
    },
    /// R(A) := {} (size = B,C)
    NewTable { dst: RegisterIndex },
    /// R(A+1) := R(B);
    /// R(A) := R(B)[RK(C)]
    ///
    /// Used for calling methods on tables
    Self_ {
        base: RegisterIndex,
        table: RegisterIndex,
        key: RK,
    },
    /// R(A) := RK(B) + RK(C)
    Add {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) - RK(C)
    Sub {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) * RK(C)
    Mul {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) % RK(C)
    Mod {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) ^ RK(C)
    Pow {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) / RK(C)
    Div {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) // RK(C)
    IDiv {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) & RK(C)
    BitAnd {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) | RK(C)
    BitOr {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) ~ RK(C)
    BitXor {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) << RK(C)
    ShiftLeft {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := RK(B) >> RK(C)
    ShiftRight {
        dst: RegisterIndex,
        left: RK,
        right: RK,
    },
    /// R(A) := -R(B)
    Minus {
        dst: RegisterIndex,
        src: RegisterIndex,
    },
    /// R(A) := ~R(B)
    BitNot {
        dst: RegisterIndex,
        src: RegisterIndex,
    },
    /// R(A) := not R(B)
    Not {
        dst: RegisterIndex,
        src: RegisterIndex,
    },
    /// R(A) := length of R(B)
    Length {
        dst: RegisterIndex,
        src: RegisterIndex,
    },
    /// R(A) := R(B) ... R(C)
    ///
    /// Concatenate the given arguments into a string
    Concat {
        dst: RegisterIndex,
        src: RegisterIndex,
        count: u16,
    },
    /// pc += sBx;
    /// if (A) close all upvalues >= R(A - 1)
    ///
    /// close_upvalues belongs to [0, 254]
    Jump { offset: i32, close_upvalues: u8 },
    /// if ((RK(B) == RK(C)) ~= A) then pc++
    Equal { skip_if: bool, left: RK, right: RK },
    /// if ((RK(B) <  RK(C)) ~= A) then pc++
    LessThan { skip_if: bool, left: RK, right: RK },
    /// if ((RK(B) <= RK(C)) ~= A) then pc++
    LessEqual { skip_if: bool, left: RK, right: RK },
    /// Test the register as a boolean, if its boolean value matches `is_true`,
    /// skip the next instruction.
    ///
    /// if not (R(A) <=> C) then pc++
    Test { value: RegisterIndex, is_true: bool },
    /// if (R(B) <=> C) then R(A) := R(B) else pc++
    ///
    /// Test the value at the `value` register as a boolean, if its boolean
    /// value matches `is_true`, skip the next instruction, otherwise assign the
    /// given value (not converted to a boolean) to the destination register.
    TestSet {
        dst: RegisterIndex,
        value: RegisterIndex,
        is_true: bool,
    },
    /// R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1))
    ///
    /// `args` and `returns` belongs to [0, 254]
    Call {
        func: RegisterIndex,
        args: u16,
        returns: u16,
    },
    /// return R(A)(R(A+1), ... ,R(A+B-1))
    ///
    /// ditto
    TailCall { func: RegisterIndex, args: u8 },
    /// return R(A), ... ,R(A+B-2)
    ///
    /// ditto
    Return { start: RegisterIndex, count: u8 },
    /// R(A) += R(A+2);
    /// if R(A) <?= R(A+1) then {
    ///     pc += sBx;
    ///     R(A+3) = R(A)
    /// }
    ///
    /// The `<?=` operator here means "less than" if the step (aka R(A+2)) is
    /// positive, and "greater than" if the step is negative
    ///
    /// Used to iterate a numeric forloop.
    NumericForLoop { base: RegisterIndex, jump: i32 },
    /// R(A) -= R(A+2);
    /// pc += sBx
    ///
    /// Used to setup for a numeric forloop.
    NumericForPrep { base: RegisterIndex, jump: i32 },
    /// R(A+3), ... ,R(A+2+C) := R(A)(R(A+1), R(A+2));
    ///
    /// Used to setup for a generic forloop.
    GenericForCall { base: RegisterIndex, var_count: u16 },
    /// if R(A+1) ~= nil then {
    ///     R(A)=R(A+1);
    ///     pc += sBx
    /// }
    ///
    /// Used to iterate a generic forloop.
    GenericForLoop { base: RegisterIndex, jump: i32 },
    /// TODO
    /// R(A)[(C-1) * FPF + i] := R(A + i), 1 <= i <= B
    SetList {},
    /// R(A) := closure(KPROTO[Bx])
    Closure { dst: RegisterIndex, proto: u32 },
    /// R(A), R(A+1), ..., R(A+B-2) = vararg
    VarArg { dst: RegisterIndex, count: u16 },
    /// TODO
    /// extra (larger) argument for previous opcode
    ExtraArg {},
}
