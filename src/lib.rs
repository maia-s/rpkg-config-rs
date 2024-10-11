#![doc = include_str!("../README.md")]

#[cfg(test)]
mod tests;

use std::{
    collections::HashMap,
    error::Error,
    ffi::{OsStr, OsString},
    fmt::{self, Display},
    fs, io,
    iter::FusedIterator,
    path::{Path, PathBuf},
    str::{self, FromStr},
};

const VARIABLE_RECURSION_LIMIT: usize = 1000;

/// Error returned by `PkgConfig::open`
#[derive(Debug)]
pub enum OpenError {
    Io(io::Error),
    Parse(ParseError),
    Encoding(EncodingError),
}

impl Display for OpenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => Display::fmt(&e, f),
            Self::Parse(e) => Display::fmt(&e, f),
            Self::Encoding(e) => Display::fmt(&e, f),
        }
    }
}

impl Error for OpenError {}

impl From<io::Error> for OpenError {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}

impl From<ParseError> for OpenError {
    fn from(value: ParseError) -> Self {
        Self::Parse(value)
    }
}

impl From<EncodingError> for OpenError {
    fn from(value: EncodingError) -> Self {
        Self::Encoding(value)
    }
}

/// Error returned if there's a problem with the text encoding
#[derive(Clone, Copy, Debug)]
pub struct EncodingError;

impl Display for EncodingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "data must be valid utf-8 on this platform")
    }
}

impl Error for EncodingError {}

/// Error returned when something couldn't be parsed
#[derive(Clone, Copy, Debug)]
pub struct ParseError {
    line: usize,
    description: &'static str,
}

impl ParseError {
    pub fn new(line: usize, description: &'static str) -> Self {
        Self { line, description }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at line {}: {}", self.line, self.description)
    }
}

impl Error for ParseError {}

/// Error returned when a variable couldn't be resolved
#[derive(Debug)]
pub enum VariableError {
    Undefined(Vec<u8>),
    RecursionLimit,
}

impl Display for VariableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undefined(var) => Display::fmt(&VariableErrorRef::Undefined(var), f),
            Self::RecursionLimit => Display::fmt(&VariableErrorRef::RecursionLimit, f),
        }
    }
}

impl Error for VariableError {}

impl From<VariableErrorRef<'_>> for VariableError {
    fn from(value: VariableErrorRef) -> Self {
        match value {
            VariableErrorRef::Undefined(var) => VariableError::Undefined(var.to_owned()),
            VariableErrorRef::RecursionLimit => VariableError::RecursionLimit,
        }
    }
}

#[derive(Debug)]
enum VariableErrorRef<'a> {
    Undefined(&'a [u8]),
    RecursionLimit,
}

impl Display for VariableErrorRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undefined(var) => {
                write!(f, "undefined variable: `{}`", String::from_utf8_lossy(var))
            }
            Self::RecursionLimit => write!(f, "recursion limit reached"),
        }
    }
}

impl Error for VariableErrorRef<'_> {}

fn split_bytes_once(bytes: &[u8], m: impl Fn(u8) -> bool) -> Option<(&[u8], &[u8])> {
    bytes
        .iter()
        .copied()
        .position(m)
        .map(|i| (&bytes[..i], &bytes[i + 1..]))
}

fn trim_bytes(bytes: &[u8]) -> &[u8] {
    let Some(s) = bytes.iter().position(|b| !b.is_ascii_whitespace()) else {
        return &bytes[bytes.len()..];
    };
    let e = bytes
        .iter()
        .rev()
        .position(|b| !b.is_ascii_whitespace())
        .unwrap();
    &bytes[s..bytes.len() - e]
}

fn bytes_to_pathbuf(bytes: &[u8]) -> Result<PathBuf, EncodingError> {
    byte_vec_to_pathbuf(bytes.to_owned())
}

fn byte_vec_to_pathbuf(bytes: Vec<u8>) -> Result<PathBuf, EncodingError> {
    Ok(PathBuf::from(OsString::from_byte_vec(bytes)?))
}

fn escape_bytes(bytes: &[u8]) -> Vec<u8> {
    let mut escaped = Vec::new();
    for b in bytes.iter().copied() {
        match b {
            b'\\' | b'\"' | b' ' => {
                escaped.push(b'\\');
                escaped.push(b);
            }
            _ => escaped.push(b),
        }
    }
    escaped
}

trait BytesConv {
    fn as_bytes(&self) -> Result<&[u8], EncodingError>;
    fn from_bytes(bytes: &[u8]) -> Result<&Self, EncodingError>;
}

trait ByteVecConv: Sized {
    #[allow(dead_code)]
    fn into_byte_vec(self) -> Result<Vec<u8>, EncodingError>;
    fn from_byte_vec(bytes: Vec<u8>) -> Result<Self, EncodingError>;
}

#[cfg(unix)]
impl BytesConv for OsStr {
    fn as_bytes(&self) -> Result<&[u8], EncodingError> {
        Ok(std::os::unix::ffi::OsStrExt::as_bytes(self))
    }

    fn from_bytes(bytes: &[u8]) -> Result<&Self, EncodingError> {
        Ok(std::os::unix::ffi::OsStrExt::from_bytes(bytes))
    }
}

#[cfg(unix)]
impl ByteVecConv for OsString {
    fn into_byte_vec(self) -> Result<Vec<u8>, EncodingError> {
        Ok(std::os::unix::ffi::OsStringExt::into_vec(self))
    }

    fn from_byte_vec(bytes: Vec<u8>) -> Result<Self, EncodingError> {
        Ok(std::os::unix::ffi::OsStringExt::from_vec(bytes))
    }
}

#[cfg(not(unix))]
impl BytesConv for OsStr {
    fn as_bytes(&self) -> Result<&[u8], EncodingError> {
        self.to_str().map(|s| s.as_bytes()).ok_or(EncodingError)
    }

    fn from_bytes(bytes: &[u8]) -> Result<&Self, EncodingError> {
        Ok(OsStr::new(
            str::from_utf8(bytes).map_err(|_| EncodingError)?,
        ))
    }
}

#[cfg(not(unix))]
impl ByteVecConv for OsString {
    fn into_byte_vec(self) -> Result<Vec<u8>, EncodingError> {
        Ok(self.into_string().map_err(|_| EncodingError)?.into_bytes())
    }

    fn from_byte_vec(bytes: Vec<u8>) -> Result<Self, EncodingError> {
        Ok(String::from_utf8(bytes).map_err(|_| EncodingError)?.into())
    }
}

/// Items parsed from `Libs` or `Libs.private` keys
#[non_exhaustive]
#[derive(Clone, Debug)]
pub enum Link {
    /// Library search path
    SearchLib(PathBuf),

    /// Framework search path
    SearchFramework(PathBuf),

    /// Link a library (static or dynamic)
    Lib(PathBuf),

    /// Link a framework
    Framework(PathBuf),

    /// Link a weak framework
    WeakFramework(PathBuf),

    /// Set rpath
    Rpath(PathBuf),

    /// Anything else. In the future, items that currently use this variant
    /// may get their own variants instead.
    Verbatim(PathBuf),
}

/// A parsed pkg-config pc file
#[derive(Clone, Default)]
pub struct PkgConfig {
    variables: HashMap<Vec<u8>, Vec<u8>>,
    keys: HashMap<Vec<u8>, Vec<u8>>,
}

impl PkgConfig {
    /// Open and parse a `pkg-config` `.pc` file. This defines the `pcfiledir` variable as the given path.
    pub fn open(path: &Path) -> Result<Self, OpenError> {
        let mut cfg = Self::default();
        cfg.set_variable_escaped(
            "pcfiledir",
            path.parent().unwrap().as_os_str().as_bytes()?,
            true,
        );
        cfg.extend_from_bytes(&fs::read(path)?)?;
        Ok(cfg)
    }

    /// Read a `pkg-config` `.pc` file from a byte slice
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ParseError> {
        let mut cfg = Self::default();
        cfg.extend_from_bytes(bytes)?;
        Ok(cfg)
    }

    fn extend_from_bytes(&mut self, bytes: &[u8]) -> Result<(), ParseError> {
        for (line_no, line) in PcLines::new(bytes) {
            let line = trim_bytes(&line);
            if line.is_empty() {
                continue;
            }

            OsStr::from_bytes(line).map_err(|_| {
                ParseError::new(line_no, "data must be valid utf-8 on this platform")
            })?;

            if let Some(i) = line.iter().position(|b| matches!(b, b':' | b'=')) {
                if line[i] == b'=' {
                    // variable
                    let (key, value) = split_bytes_once(line, |b| b == b'=').unwrap();
                    let key = trim_bytes(key);
                    if key.iter().any(u8::is_ascii_whitespace) {
                        return Err(ParseError::new(line_no, "space in variable name"));
                    }
                    if !self.set_variable(key, value, false) {
                        return Err(ParseError::new(line_no, "duplicate variable definition"));
                    }
                } else {
                    // key
                    let (key, value) = split_bytes_once(line, |b| b == b':').unwrap();
                    let mut key = trim_bytes(key).to_owned();
                    if key == b"CFlags" {
                        // map CFlags to Cflags
                        key[1] = b'f';
                    }
                    let value = trim_bytes(value).to_owned();
                    if self.keys.insert(key, value).is_some() {
                        return Err(ParseError::new(line_no, "key already set"));
                    }
                }
            } else {
                return Err(ParseError::new(line_no, "not a variable or key definition"));
            }
        }
        Ok(())
    }

    /// Get an iterator over the items in the `Libs` key
    pub fn libs(&self) -> Result<Links, VariableError> {
        Ok(Links {
            split: self
                .key_bytes_expanded_unescaped_split("Libs")?
                .unwrap_or(UnescapeAndSplit::new(b"")),
        })
    }

    /// Get an iterator over the items in the `Libs.private` key
    pub fn libs_private(&self) -> Result<Links, VariableError> {
        Ok(Links {
            split: self
                .key_bytes_expanded_unescaped_split("Libs.private")?
                .unwrap_or(UnescapeAndSplit::new(b"")),
        })
    }

    /// Get a variable
    pub fn variable(&self, var: impl AsRef<[u8]>) -> Option<&[u8]> {
        self.variables.get(var.as_ref()).map(|v| v as &[u8])
    }

    /// Set a variable
    pub fn set_variable(
        &mut self,
        var: impl AsRef<[u8]>,
        value: impl AsRef<[u8]>,
        allow_overwrite: bool,
    ) -> bool {
        self.variables
            .insert(
                trim_bytes(var.as_ref()).to_owned(),
                trim_bytes(value.as_ref()).to_owned(),
            )
            .is_none()
            || allow_overwrite
    }

    /// Set a variable and escape it
    pub fn set_variable_escaped(
        &mut self,
        var: impl AsRef<[u8]>,
        value: impl AsRef<[u8]>,
        allow_overwrite: bool,
    ) -> bool {
        self.set_variable(var, escape_bytes(value.as_ref()), allow_overwrite)
    }

    /// Get a variable and expand all variables it references
    pub fn expand_variable(&self, var: impl AsRef<[u8]>) -> Result<Vec<u8>, VariableError> {
        Ok(self.expand_variable_r(var.as_ref(), VARIABLE_RECURSION_LIMIT)?)
    }

    fn expand_variable_r<'e, 's: 'e, 'k: 'e>(
        &'s self,
        var: &'k [u8],
        limit: usize,
    ) -> Result<Vec<u8>, VariableErrorRef<'e>> {
        self.expand_variables_in_byte_string_r(
            self.variable(var).ok_or(VariableErrorRef::Undefined(var))?,
            limit,
        )
    }

    /// Expand all variables in the input
    pub fn expand_variables_in(&self, input: impl AsRef<[u8]>) -> Result<Vec<u8>, VariableError> {
        Ok(self.expand_variables_in_byte_string_r(input.as_ref(), VARIABLE_RECURSION_LIMIT)?)
    }

    fn expand_variables_in_byte_string_r<'e, 's: 'e, 'k: 'e>(
        &'s self,
        input: &'k [u8],
        limit: usize,
    ) -> Result<Vec<u8>, VariableErrorRef<'e>> {
        let mut output = Vec::new();
        let mut bytes = input.iter().copied().enumerate();
        // - '$' followed by '$' outputs '$'
        // - '$' followed by '{' variable-name '}' expands variable
        // - anything else is copied verbatim
        while let Some((_, b)) = bytes.next() {
            if b == b'$' {
                if let Some((ni, nb)) = bytes.next() {
                    match nb {
                        b'$' => output.push(b),
                        b'{' => {
                            if limit == 0 {
                                return Err(VariableErrorRef::RecursionLimit);
                            }
                            let e = 'end_pos: {
                                for (nni, nnb) in bytes.by_ref() {
                                    if nnb == b'}' {
                                        break 'end_pos nni;
                                    }
                                }
                                // unterminated variable is still expanded
                                input.len()
                            };
                            output.extend(self.expand_variable_r(&input[ni + 1..e], limit - 1)?);
                        }
                        _ => {
                            output.push(b);
                            output.push(nb);
                        }
                    }
                }
            } else {
                output.push(b);
            }
        }
        Ok(output)
    }

    /// Get the raw bytes of a key
    pub fn key_bytes(&self, key: impl AsRef<[u8]>) -> Option<&[u8]> {
        self.keys.get(key.as_ref()).map(|v| v as &[u8])
    }

    /// Get the raw bytes of a key with variables expanded
    pub fn key_bytes_expanded(
        &self,
        key: impl AsRef<[u8]>,
    ) -> Result<Option<Vec<u8>>, VariableError> {
        if let Some(bytes) = self.key_bytes(key) {
            Ok(Some(self.expand_variables_in(bytes)?))
        } else {
            Ok(None)
        }
    }

    /// Get the raw bytes of a key with variables expanded, unescaped and split by spaces
    pub fn key_bytes_expanded_unescaped_split(
        &self,
        key: impl AsRef<[u8]>,
    ) -> Result<Option<UnescapeAndSplit>, VariableError> {
        Ok(self.key_bytes_expanded(key)?.map(UnescapeAndSplit::new))
    }
}

impl FromStr for PkgConfig {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_bytes(s.as_bytes())
    }
}

/// Iterator over a pkg-config key that handles escapes and splits by unescaped whitespace
pub struct UnescapeAndSplit {
    bytes: Vec<u8>,
    index: usize,
}

impl UnescapeAndSplit {
    fn new(bytes: impl AsRef<[u8]>) -> Self {
        Self {
            bytes: trim_bytes(bytes.as_ref()).to_owned(),
            index: 0,
        }
    }
}

impl Iterator for UnescapeAndSplit {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.bytes[self.index..]
            .iter()
            .position(|b| !b.is_ascii_whitespace())
            .unwrap_or(self.bytes.len() - self.index);
        self.index += i;

        if self.bytes.len() == self.index {
            return None;
        }

        let mut it = self.bytes[self.index..].iter().copied().enumerate();
        let mut quoted = false;
        let mut item = Vec::new();

        while let Some((i, b)) = it.next() {
            match b {
                b'\\' => {
                    if let Some((_, b2)) = it.next() {
                        match b2 {
                            b'\\' | b'\"' | b' ' => {
                                // escaped
                                item.push(b2)
                            }
                            _ => {
                                // may be a windows path
                                item.push(b);
                                item.push(b2);
                            }
                        }
                    } else {
                        // lone escape at end of input
                        item.push(b);
                    }
                }

                b'\"' => {
                    quoted = !quoted;
                }

                _ => {
                    if !quoted && b.is_ascii_whitespace() {
                        self.index += i;
                        return Some(item);
                    } else {
                        item.push(b);
                    }
                }
            }
        }

        self.index = self.bytes.len();
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some((self.bytes.len() + 1) / 2))
    }
}

impl FusedIterator for UnescapeAndSplit {}

/// Iterator over items in `Libs` or `Libs.private`
pub struct Links {
    split: UnescapeAndSplit,
}

impl Iterator for Links {
    type Item = Link;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(part) = self.split.next() {
            if let Some(part) = part.strip_prefix(b"-L") {
                Some(Link::SearchLib(bytes_to_pathbuf(part).unwrap()))
            } else if let Some(part) = part.strip_prefix(b"-F") {
                Some(Link::SearchFramework(bytes_to_pathbuf(part).unwrap()))
            } else if let Some(part) = part.strip_prefix(b"-l") {
                Some(Link::Lib(bytes_to_pathbuf(part).unwrap()))
            } else if let Some(part) = part.strip_prefix(b"-Wl,-framework,") {
                Some(Link::Framework(bytes_to_pathbuf(part).unwrap()))
            } else if part == b"-framework" {
                self.split
                    .next()
                    .map(|part| Link::Framework(byte_vec_to_pathbuf(part).unwrap()))
            } else if let Some(part) = part.strip_prefix(b"-Wl,-weak_framework,") {
                Some(Link::WeakFramework(bytes_to_pathbuf(part).unwrap()))
            } else if part == b"-weak_framework" {
                self.split
                    .next()
                    .map(|part| Link::WeakFramework(byte_vec_to_pathbuf(part).unwrap()))
            } else if let Some(part) = part.strip_prefix(b"-Wl,-rpath,") {
                Some(Link::Rpath(bytes_to_pathbuf(part).unwrap()))
            } else if part == b"-rpath" {
                self.split
                    .next()
                    .map(|part| Link::Rpath(byte_vec_to_pathbuf(part).unwrap()))
            } else {
                Some(Link::Verbatim(byte_vec_to_pathbuf(part).unwrap()))
            }
        } else {
            None
        }
    }
}

struct PcLines<'a> {
    bytes: &'a [u8],
    line_no: usize,
}

impl<'a> PcLines<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, line_no: 0 }
    }
}

impl Iterator for PcLines<'_> {
    type Item = (usize, Vec<u8>);

    fn next(&mut self) -> Option<Self::Item> {
        // .pc parsing rules:
        // - newline is one of '\n', '\r', '\r\n' or '\n\r'
        // - '#' starts a comment that goes until the next newline
        // - '\' escapes '#' or newline only. newline in comments can't be escaped
        if self.bytes.is_empty() {
            return None;
        }
        let mut it = self.bytes.iter().copied().enumerate().peekable();
        let mut line = Vec::new();
        self.line_no += 1;
        let line_no = self.line_no;
        while let Some((i, b)) = it.next() {
            match b {
                b'\\' => {
                    // escapes
                    if let Some((_, nb)) = it.next() {
                        match nb {
                            b'#' => line.push(nb),
                            b'\r' | b'\n' => {
                                if let Some((_, nnb)) = it.peek() {
                                    if *nnb == if nb == b'\r' { b'\n' } else { b'\r' } {
                                        it.next();
                                    }
                                }
                                self.line_no += 1;
                            }
                            _ => {
                                line.push(b);
                                line.push(nb);
                            }
                        }
                    } else {
                        line.push(b);
                        self.bytes = &self.bytes[i + 1..];
                        return Some((line_no, line));
                    }
                }
                b'#' => {
                    // comment
                    while let Some((ni, nc)) = it.next() {
                        if matches!(nc, b'\r' | b'\n') {
                            self.bytes = &self.bytes[ni + 1..];
                            if let Some((_, nnc)) = it.peek() {
                                if *nnc == if nc == b'\r' { b'\n' } else { b'\r' } {
                                    self.bytes = &self.bytes[1..];
                                }
                            }
                            break;
                        }
                    }
                    return Some((line_no, line));
                }
                b'\r' | b'\n' => {
                    // newline
                    if let Some((_, nc)) = it.next() {
                        if nc == if b == b'\r' { b'\n' } else { b'\r' } {
                            self.bytes = &self.bytes[i + 2..];
                        } else {
                            self.bytes = &self.bytes[i + 1..];
                        }
                        return Some((line_no, line));
                    } else {
                        self.bytes = &self.bytes[i + 1..];
                        return Some((line_no, line));
                    }
                }
                _ => line.push(b),
            }
        }
        Some((line_no, line))
    }
}
