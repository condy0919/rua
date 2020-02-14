use std::io;

use byteorder::{NativeEndian, ReadBytesExt};

use super::{Constant, LocalVariable, Prototype, UpValue};

const TAG_NIL: u8 = 0x00;
const TAG_BOOLEAN: u8 = 0x01;
const TAG_NUMBER: u8 = 0x03;
const TAG_INTEGER: u8 = 0x13;
const TAG_SHORT_STR: u8 = 0x04;
const TAG_LONG_STR: u8 = 0x14;

/// A reader adaptor for Rua binary chunk
pub struct Reader<'a, T: ReadBytesExt> {
    src: &'a mut T,
}

impl<'a, T: ReadBytesExt> Reader<'a, T> {
    /// Constructs a `Reader` from `File`, `BufReader` and etc...
    pub fn new(src: &'a mut T) -> Self {
        Self { src }
    }

    /// Returns 1-byte or yields an `io::Result::Err`
    pub fn read_byte(&mut self) -> io::Result<u8> {
        self.src.read_u8()
    }

    /// Returns n-bytes or yields an `io::Result::Err`
    pub fn read_bytes(&mut self, n: usize) -> io::Result<Vec<u8>> {
        let mut buf = Vec::with_capacity(n);
        buf.resize(n, b'\x00');
        self.src.read_exact(buf.as_mut())?;
        Ok(buf)
    }

    /// Returns an `u32` or yields an `io::Result::Err`
    pub fn read_u32(&mut self) -> io::Result<u32> {
        self.src.read_u32::<NativeEndian>()
    }

    /// Returns an `u64` or yields an `io::Result::Err`
    pub fn read_u64(&mut self) -> io::Result<u64> {
        self.src.read_u64::<NativeEndian>()
    }

    /// Returns an `Integer` (represented by i64) or yields an `io::Result::Err`
    pub fn read_integer(&mut self) -> io::Result<i64> {
        self.src.read_i64::<NativeEndian>()
    }

    /// Returns a `Number` (represented by f64) or yields an `io::Result::Err`
    pub fn read_number(&mut self) -> io::Result<f64> {
        self.src.read_f64::<NativeEndian>()
    }

    /// Returns a `String` or yields an `io::Result::Err`
    pub fn read_string(&mut self) -> io::Result<String> {
        Ok(self.read_string_impl()?.unwrap_or_else(String::new))
    }

    /// Returns a `Vec` that is applied with `f`
    pub fn read_vec<R, F>(&mut self, f: F) -> io::Result<Vec<R>>
    where
        F: Fn(&mut Self) -> io::Result<R>,
    {
        let n = self.read_u32()? as usize;
        let mut vec = Vec::with_capacity(n);
        for _i in 0..n {
            vec.push(f(self)?);
        }
        Ok(vec)
    }

    /// Returns a [`Constant`] in Rua or yields an `io::Result::Err`.
    ///
    /// It can be:
    ///
    /// - Nil
    /// - Boolean
    /// - Number
    /// - Integer
    /// - Str
    ///
    /// [`Constant`]: ../enum.Constant.html
    pub fn read_constant(&mut self) -> io::Result<Constant> {
        use Constant::*;

        let tag = self.read_byte()?;
        let c = match tag {
            TAG_NIL => Nil,
            TAG_BOOLEAN => Boolean(self.read_byte()? != 0),
            TAG_NUMBER => Number(self.read_number()?),
            TAG_INTEGER => Integer(self.read_integer()?),
            TAG_SHORT_STR | TAG_LONG_STR => Str(self.read_string()?),
            _ => panic!("corrupted!"),
        };
        Ok(c)
    }

    /// Returns an [`UpValue`] in Rua or yields an `io::Result::Err`
    ///
    /// [`UpValue`]: ../struct.UpValue.html
    pub fn read_upvalue(&mut self) -> io::Result<UpValue> {
        Ok(UpValue {
            instack: self.read_byte()?,
            idx: self.read_byte()?,
        })
    }

    /// Returns a [`LocalVariable`] in Rua or yields an `io::Result::Err`
    ///
    /// [`LocalVariable`]: ../struct.LocalVariable.html
    pub fn read_local_variable(&mut self) -> io::Result<LocalVariable> {
        Ok(LocalVariable {
            name: self.read_string()?,
            start_pc: self.read_u32()?,
            end_pc: self.read_u32()?,
        })
    }

    /// Returns a [`Prototype`] in Rua or yields an `io::Result::Err`
    ///
    /// [`Prototype`]: ../struct.Prototype.html
    pub fn read_prototype(&mut self) -> io::Result<Prototype> {
        self.read_prototype_impl(None)
    }

    fn read_prototype_impl(&mut self, parent: Option<String>) -> io::Result<Prototype> {
        let src = self.read_string_impl()?.or(parent);
        Ok(Prototype {
            source: src,
            first_line: self.read_u32()?,
            last_line: self.read_u32()?,
            params: self.read_byte()?,
            variadic: self.read_byte()?,
            max_stack_size: self.read_byte()?,
            instructions: self.read_vec(|r| r.read_u32())?,
            constants: self.read_vec(|r| r.read_constant())?,
            upvalues: self.read_vec(|r| r.read_upvalue())?,
            protos: self.read_vec(|r| r.read_prototype())?,
            line_infos: self.read_vec(|r| r.read_u32())?,
            local_vars: self.read_vec(|r| r.read_local_variable())?,
            upvalue_names: self.read_vec(|r| r.read_string())?,
        })
    }

    fn read_string_impl(&mut self) -> io::Result<Option<String>> {
        let mut sz = self.read_byte()? as usize;
        if sz == 0 {
            return Ok(None);
        }
        if sz == 0xff {
            sz = self.read_u64()? as usize;
        }

        let s = unsafe { String::from_utf8_unchecked(self.read_bytes(sz - 1)?) };
        Ok(Some(s))
    }
}

#[cfg(all(target_arch = "x86_64", target_endian = "little"))]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reader_new() {
        let mut src = b"0\n" as &[u8];
        let _reader = Reader::new(&mut src);
    }

    #[test]
    fn reader_read_byte() {
        let mut src = b"\xff" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_byte().unwrap(), b'\xff');
    }

    #[test]
    fn reader_read_bytes() {
        let mut src = b"\xff\xfe\x00" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_bytes(2).unwrap(), vec![b'\xff', b'\xfe']);
    }

    #[test]
    fn reader_read_u32() {
        let mut src = b"\x00\x01\x02\x03" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_u32().unwrap(), 0x03020100);
    }

    #[test]
    fn reader_read_u64() {
        let mut src = b"\x00\x01\x02\x03\x04\x05\x06\x07" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_u64().unwrap(), 0x0706050403020100);
    }

    #[test]
    fn reader_read_integer() {
        let mut src = b"\x00\x01\x02\x03\x04\x05\x06\x07" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_integer().unwrap(), 0x0706050403020100);
    }

    #[test]
    fn reader_read_number() {
        let mut src = b"\x00\x00\x00\x00\x00\x28\x77\x40" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_number().unwrap(), 370.5);
    }

    #[test]
    fn reader_read_string() {
        // null string
        let mut src = b"\x00" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_string().unwrap(), "");

        // short string
        let mut src = b"\x02A" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_string().unwrap(), "A");

        // long string
        let mut src = b"\xff\x00\x01\x00\x00\x00\x00\x00\x00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_string().unwrap(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
    }

    #[test]
    fn reader_read_vec() {
        let mut src = b"\x03\x00\x00\x00bbb" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_vec(|r| r.read_byte()).unwrap(),
            vec![b'b', b'b', b'b']
        );
    }

    #[test]
    fn reader_read_constant() {
        let mut src = &[TAG_NIL] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_constant().unwrap(), Constant::Nil);

        let mut src = &[TAG_BOOLEAN, b'\x01'] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_constant().unwrap(), Constant::Boolean(true));

        let mut src = &[TAG_BOOLEAN, b'\x00'] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_constant().unwrap(), Constant::Boolean(false));

        let mut src = &[
            TAG_NUMBER, b'\x00', b'\x00', b'\x00', b'\x00', b'\x00', b'\x28', b'\x77', b'\x40',
        ] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(reader.read_constant().unwrap(), Constant::Number(370.5));

        let mut src = &[
            TAG_INTEGER,
            b'\x01',
            b'\x02',
            b'\x03',
            b'\x04',
            b'\x05',
            b'\x06',
            b'\x07',
            b'\x08',
        ] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_constant().unwrap(),
            Constant::Integer(0x0807060504030201)
        );

        let mut src = &[TAG_SHORT_STR, b'\x00'] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_constant().unwrap(),
            Constant::Str("".to_string())
        );

        let mut src = &[TAG_SHORT_STR, b'\x02', b'A'] as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_constant().unwrap(),
            Constant::Str("A".to_string())
        );
    }

    #[test]
    fn reader_read_upvalue() {
        let mut src = b"\x01\x02" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_upvalue().unwrap(),
            UpValue {
                instack: b'\x01',
                idx: b'\x02',
            }
        );
    }

    #[test]
    fn reader_read_local_variable() {
        let mut src = b"\x00\x01\x00\x00\x00\x03\x00\x00\x00" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_local_variable().unwrap(),
            LocalVariable {
                name: "".to_string(),
                start_pc: 0x01,
                end_pc: 0x03,
            }
        );
    }

    #[test]
    fn reader_read_prototype() {
        let mut src = b"\x00\x00\x01\x02\x03\x01\x02\x03\x04\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" as &[u8];
        let mut reader = Reader::new(&mut src);
        assert_eq!(
            reader.read_prototype().unwrap(),
            Prototype {
                source: None,
                first_line: 0x03020100,
                last_line: 0x04030201,
                params: b'\x00',
                variadic: b'\x01',
                max_stack_size: b'\x00',
                instructions: Vec::new(),
                constants: Vec::new(),
                upvalues: Vec::new(),
                protos: Vec::new(),
                line_infos: Vec::new(),
                local_vars: Vec::new(),
                upvalue_names: Vec::new(),
            }
        );
    }
}
