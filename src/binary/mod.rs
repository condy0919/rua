use std::fs::File;
use std::io::{self, BufReader};
use std::mem;

mod reader;
use reader::Reader;

const RUA_SIGNATURE: &[u8; 4] = b"\x1bLua";

const RUA_MAJOR_VERSION: u8 = 5;
const RUA_MINOR_VERSION: u8 = 3;
const RUA_RELEASE_VERSION: u8 = 0;
const RUA_VERSION: u8 = RUA_MAJOR_VERSION * 16 + RUA_MINOR_VERSION;

const RUA_FORMAT: u8 = 0; // This it the official format
const RUA_DATA: &[u8; 6] = b"\x19\x93\r\n\x1a\n"; // Lua 1.0 released at 1993
const RUA_INT_SIZE: u8 = mem::size_of::<u32>() as u8;
const RUA_SIZET_SIZE: u8 = mem::size_of::<usize>() as u8;
const RUA_INSTRUCTION_SIZE: u8 = mem::size_of::<u32>() as u8;
const RUA_INTEGER_SIZE: u8 = mem::size_of::<i64>() as u8;
const RUA_NUMBER_SIZE: u8 = mem::size_of::<f64>() as u8;
const RUA_INTEGER_DATA: i64 = 0x5678;
const RUA_NUMBER_DATA: f64 = 370.5;

/// The constants in Lua
#[derive(PartialEq, Debug)]
pub enum Constant {
    Nil,
    Boolean(bool),
    Number(f64),
    Integer(i64),
    Str(String),
}

/// The local variable in Lua
#[derive(Eq, PartialEq, Debug, Hash)]
pub struct LocalVariable {
    pub name: String,
    pub start_pc: u32,
    pub end_pc: u32,
}

/// TODO
#[derive(Eq, PartialEq, Debug, Hash)]
pub struct UpValue {
    pub instack: u8,
    pub idx: u8,
}

/// The prototype of a function
#[derive(PartialEq, Debug)]
pub struct Prototype {
    /// The source name where defined current function.
    ///
    /// If the function is anonymous function, the source name is empty.
    ///
    /// If the source starts with "@", it means the binary chunk is indeed
    /// compiled from the `Lua` source file. After removing the '@', the real
    /// file name is obtained.
    ///
    /// If the source starts with "=", it has special meaning (e.g. "=stdin"
    /// indicates that the binary chunk is compiled from standard input).
    ///
    /// If there is no "=", it indicates that the binary chunk is compiled from
    /// the string provided by the programmer, the source stores the string.
    pub source: Option<String>,
    /// The first line of the function
    pub first_line: u32,
    /// The last line of the function
    pub last_line: u32,
    /// The number of fixed parameters of the function. The fixed parameters
    /// here are relative to the variadic length parameters (vararg).
    pub params: u8,
    /// Is it a variadic function?
    pub variadic: u8,
    /// TODO The number of register
    pub max_stack_size: u8,
    /// The instructions table.
    ///
    /// Each instruction occupied 4 bytes.
    pub instructions: Vec<u32>,
    /// The constant table is used to store literals that appear in Lua code,
    /// including `nil`, `boolean`, `integer`, `floating point number`, and
    /// `string`.
    ///
    /// Each constant starts with a 1-byte tag to identify what type of constant
    /// value is stored subsequently.
    pub constants: Vec<Constant>,
    /// TODO
    ///
    /// an `UpValue` takes 2 bytes
    pub upvalues: Vec<UpValue>,
    /// Sub-prototypes
    pub protos: Vec<Prototype>,
    /// The line information of each instruction.
    pub line_infos: Vec<u32>,
    /// The local variable table
    pub local_vars: Vec<LocalVariable>,
    /// TODO
    ///
    /// The name of an `UpValue`
    pub upvalue_names: Vec<String>,
}

///
pub fn undump(file: File) -> io::Result<Prototype> {
    let mut bufr = BufReader::new(file);
    let mut reader = Reader::new(&mut bufr);

    // Checks the magic number
    assert_eq!(
        reader.read_bytes(4)?,
        RUA_SIGNATURE,
        "not a precompiled chunk"
    );

    // Checks version
    assert_eq!(reader.read_byte()?, RUA_VERSION, "version mismatch");

    // Checks format
    assert_eq!(reader.read_byte()?, RUA_FORMAT, "format mismatch");

    // Checks data
    assert_eq!(reader.read_bytes(6)?, RUA_DATA, "corrupted");

    // Checks the size of int
    assert_eq!(reader.read_byte()?, RUA_INT_SIZE, "sizeof(int) mismatch");

    // Checks the size of size_t
    assert_eq!(
        reader.read_byte()?,
        RUA_SIZET_SIZE,
        "sizeof(size_t) mismatch"
    );

    // Checks the size of instruction
    assert_eq!(
        reader.read_byte()?,
        RUA_INSTRUCTION_SIZE,
        "sizeof(instruction) mismatch"
    );

    // Checks the size of Integer
    assert_eq!(
        reader.read_byte()?,
        RUA_INTEGER_SIZE,
        "sizeof(Integer) mismatch"
    );

    // Checks the size of Number
    assert_eq!(
        reader.read_byte()?,
        RUA_NUMBER_SIZE,
        "sizeof(Number) mismatch"
    );

    // Checks the endianness of Integer
    assert_eq!(
        reader.read_integer()?,
        RUA_INTEGER_DATA,
        "endianness mismatch"
    );

    // Checks the format of Number
    assert!(
        (reader.read_number()? - RUA_NUMBER_DATA).abs() < std::f64::EPSILON,
        "float format mismatch"
    );

    // TODO
    let _upvalues = reader.read_byte()?;

    Ok(reader.read_prototype()?)
}
