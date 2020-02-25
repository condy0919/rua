//! We assume that instructions are unsigned numbers. All instructions have an
//! opcode in the first 6 bits. Instruction can have the following modes:
//!
//! ```
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

/// Basic instruction format.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
#[repr(u8)]
pub enum Mode {
    iABC,
    iABx,
    iAsBx,
    iAx,
}

/// Argument kind
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
#[repr(u8)]
pub enum ArgKind {
    /// Argument is not used
    N,
    /// Argument is used
    U,
    /// Argument is a register or a jump offset
    R,
    /// Argument is a register or register/constant
    K,
}

///
pub struct OpCode {
    pub kind1: ArgKind,
    pub kind2: ArgKind,
    pub mode: Mode,
    pub name: &'static str,
}

/// an instruction
pub trait Instruction {
    fn name(&self) -> &'static str;
    fn mode(&self) -> Mode;
    fn opcode(&self) -> u8;
    fn kind1(&self) -> ArgKind;
    fn kind2(&self) -> ArgKind;
    fn get<T: ArgGetter>(&self) -> i32;
}

impl Instruction for u32 {
    fn name(&self) -> &'static str {
        OPCODES[self.opcode() as usize].name
    }

    fn mode(&self) -> Mode {
        OPCODES[self.opcode() as usize].mode
    }

    fn opcode(&self) -> u8 {
        (*self & 0b111111) as u8
    }

    fn kind1(&self) -> ArgKind {
        OPCODES[self.opcode() as usize].kind1
    }

    fn kind2(&self) -> ArgKind {
        OPCODES[self.opcode() as usize].kind2
    }

    fn get<T: ArgGetter>(&self) -> i32 {
        T::get_arg(*self)
    }
}

#[doc(hidden)]
macro_rules! generate_opcode {
    ($kind1:ident, $kind2:ident, $mode:ident, $name:expr) => {
        OpCode {
            kind1: ArgKind::$kind1,
            kind2: ArgKind::$kind2,
            mode: Mode::$mode,
            name: $name,
        }
    };
}

/// All opcodes
///
/// ```
/// R(x) -  register
/// Kst(x) - constant (in constant table) [the most significant bit is 1]
///                                       [i.e. larger than 0xff]
/// RK(x) == if ISK(x) then Kst(INDEXK(x)) else R(x)
/// ```
///
/// # Notes
///
/// - In `CALL`, if (B == 0) then B = top. If (C == 0), then `top` is set to
///   last_result+1. so next open instruction (`CALL`, `RETURN`, `SETLIST`) may
///   use `top`.
/// - In `VARARG`, if (B == 0) then use actual number of varargs and set top
///   (like in `CALL` with C == 0).
/// - In `RETURN`, if (B == 0) then return up to `top`.
/// - In `SETLIST`, if (B == 0) then B = `top`; if (C == 0) then next
///   instruction is `EXTRAARG(real c)`.
/// - In `LOADKX`, the next instruction is always `EXTRAARG`.
/// - For comparisons, A sppecifies what condition the test should accept
///   (true or false)
/// - All `skips` (pc++) assume that next instruction is a jump.
const OPCODES: &'static [OpCode] = &[
    //               B  C  Mode    Name
    generate_opcode!(R, N, iABC, "MOVE"),      // R(A) := R(B)
    generate_opcode!(K, N, iABx, "LOADK"),     // R(A) := Kst(Bx)
    generate_opcode!(N, N, iABx, "LOADKX"),    // R(A) := Kst(extra arg)
    generate_opcode!(U, U, iABC, "LOADBOOL"),  // R(A) := (bool)B; if (C) pc++
    generate_opcode!(U, N, iABC, "LOADNIL"),   // R(A), R(A+1), ..., R(A+B) := nil
    generate_opcode!(U, N, iABC, "GETUPVAL"),  // R(A) := UpValue[B]
    generate_opcode!(U, K, iABC, "GETTABUP"),  // R(A) := UpValue[B][RK(C)]
    generate_opcode!(R, K, iABC, "GETTABLE"),  // R(A) := R(B)[RK(C)]
    generate_opcode!(K, K, iABC, "SETTABUP"),  // UpValue[A][RK(B)] := RK(C)
    generate_opcode!(U, N, iABC, "SETUPVAL"),  // UpValue[B] := R(A)
    generate_opcode!(K, K, iABC, "SETTABLE"),  // R(A)[RK(B)] := RK(C)
    generate_opcode!(U, U, iABC, "NEWTABLE"),  // R(A) := {} (size = B,C)
    generate_opcode!(R, K, iABC, "SELF"),      // R(A+1) := R(B); R(A) := R(B)[RK(C)]
    generate_opcode!(K, K, iABC, "ADD"),       // R(A) := RK(B) + RK(C)
    generate_opcode!(K, K, iABC, "SUB"),       // R(A) := RK(B) - RK(C)
    generate_opcode!(K, K, iABC, "MUL"),       // R(A) := RK(B) * RK(C)
    generate_opcode!(K, K, iABC, "MOD"),       // R(A) := RK(B) % RK(C)
    generate_opcode!(K, K, iABC, "POW"),       // R(A) := RK(B) ^ RK(C)
    generate_opcode!(K, K, iABC, "DIV"),       // R(A) := RK(B) / RK(C)
    generate_opcode!(K, K, iABC, "IDIV"),      // R(A) := RK(B) // RK(C)
    generate_opcode!(K, K, iABC, "BAND"),      // R(A) := RK(B) & RK(C)
    generate_opcode!(K, K, iABC, "BOR"),       // R(A) := RK(B) | RK(C)
    generate_opcode!(K, K, iABC, "BXOR"),      // R(A) := RK(B) ~ RK(C)
    generate_opcode!(K, K, iABC, "SHL"),       // R(A) := RK(B) << RK(C)
    generate_opcode!(K, K, iABC, "SHR"),       // R(A) := RK(B) >> RK(C)
    generate_opcode!(R, N, iABC, "UNM"),       // R(A) := -R(B)
    generate_opcode!(R, N, iABC, "BNOT"),      // R(A) := ~R(B)
    generate_opcode!(R, N, iABC, "NOT"),       // R(A) := not R(B)
    generate_opcode!(R, N, iABC, "LEN"),       // R(A) := length of R(B)
    generate_opcode!(R, R, iABC, "CONCAT"),    // R(A) := R(B) ... R(C)
    generate_opcode!(R, N, iAsBx, "JMP"),      // pc+=sBx; if (A) close all upvalues >= R(A - 1)
    generate_opcode!(K, K, iABC, "EQ"),        // if ((RK(B) == RK(C)) ~= A) then pc++
    generate_opcode!(K, K, iABC, "LT"),        // if ((RK(B) <  RK(C)) ~= A) then pc++
    generate_opcode!(K, K, iABC, "LE"),        // if ((RK(B) <= RK(C)) ~= A) then pc++
    generate_opcode!(N, U, iABC, "TEST"),      // if not (R(A) <=> C) then pc++
    generate_opcode!(R, U, iABC, "TESTSET"),   // if (R(B) <=> C) then R(A) := R(B) else pc++
    generate_opcode!(U, U, iABC, "CALL"),      // R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1))
    generate_opcode!(U, U, iABC, "TAILCALL"),  // return R(A)(R(A+1), ... ,R(A+B-1))
    generate_opcode!(U, N, iABC, "RETURN"),    // return R(A), ... ,R(A+B-2)
    generate_opcode!(R, N, iAsBx, "FORLOOP"), // R(A)+=R(A+2); if R(A) <?= R(A+1) then { pc+=sBx; R(A+3)=R(A) }
    generate_opcode!(R, N, iAsBx, "FORPREP"), // R(A)-=R(A+2); pc+=sBx
    generate_opcode!(N, U, iABC, "TFORCALL"), // R(A+3), ... ,R(A+2+C) := R(A)(R(A+1), R(A+2));
    generate_opcode!(R, N, iAsBx, "TFORLOOP"), // if R(A+1) ~= nil then { R(A)=R(A+1); pc += sBx }
    generate_opcode!(U, U, iABC, "SETLIST"),  // R(A)[(C-1)*FPF+i] := R(A+i), 1 <= i <= B
    generate_opcode!(U, N, iABx, "CLOSURE"),  // R(A) := closure(KPROTO[Bx])
    generate_opcode!(U, N, iABC, "VARARG"),   // R(A), R(A+1), ..., R(A+B-2) = vararg
    generate_opcode!(U, U, iAx, "EXTRAARG"),  // extra (larger) argument for previous opcode
];

// boilerplate follows

/// Helpful trait for static dispatch over types
pub trait ArgGetter {
    fn get_arg(x: u32) -> i32;
}

#[doc(hidden)]
macro_rules! generate_arg_getter_impl {
    ($name:ident, $signed:expr, $rshift:expr, $mask:expr) => {
        #[allow(non_camel_case_types)]
        pub struct $name;

        impl $name {
            const RSHIFT: u32 = $rshift;
            const MASK: u32 = $mask;
        }

        impl ArgGetter for $name {
            fn get_arg(x: u32) -> i32 {
                if ($signed) {
                    // NOTE A signed argument is represented in excess K.
                    (((x >> Self::RSHIFT) & Self::MASK) - Self::MASK / 2) as i32
                } else {
                    ((x >> Self::RSHIFT) & Self::MASK) as i32
                }
            }
        }
    };
}

generate_arg_getter_impl!(gA, false, 6, 0xff);
generate_arg_getter_impl!(gB, false, 23, 0x1ff);
generate_arg_getter_impl!(gC, false, 14, 0x1ff);
generate_arg_getter_impl!(gBx, false, 14, 0x3ffff);
generate_arg_getter_impl!(gsBx, true, 14, 0x3ffff);
generate_arg_getter_impl!(gAx, false, 6, 0x3ffffff);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instruction_zero() {
        let instruction: u32 = 0;
        assert_eq!(instruction.name(), "MOVE     ");
        assert_eq!(instruction.mode(), Mode::iABC);
        assert_eq!(instruction.opcode(), 0);
        assert_eq!(instruction.kind1(), ArgKind::R);
        assert_eq!(instruction.kind2(), ArgKind::N);
        assert_eq!(instruction.get::<gA>(), 0);
        assert_eq!(instruction.get::<gB>(), 0);
        assert_eq!(instruction.get::<gC>(), 0);
    }
}
