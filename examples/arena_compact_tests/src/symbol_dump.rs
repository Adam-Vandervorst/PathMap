use std::io::{
    Write, Seek, SeekFrom, BufWriter,
    Error as IoError,
};
use std::path::Path;
use std::fs::{File, OpenOptions};

pub struct SymbolDumper {
    file: BufWriter<File>,
    position: u64,
    offsets: Vec<u64>,
}

const SYMTAB_MAGIC: [u8; 8] = *b"Symtab00";

impl SymbolDumper {
    pub fn new<'a>(path: impl AsRef<std::path::Path>)
        -> Result<Self, IoError>
    {
        let mut file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path.as_ref())?;
        // Write symtab magic string
        file.write_all(&SYMTAB_MAGIC)?;
        // Leave 2x u64 for offset table and symbol count
        file.write_all(&[0; 16])?;
        Ok(Self {
            file: BufWriter::new(file),
            position: 24,
            offsets: Vec::new(),
        })
    }

    pub fn push(&mut self, symbol: impl AsRef<[u8]>) -> Result<(), IoError> {
        let symbol = symbol.as_ref();
        // Write the symbol
        self.file.write_all(symbol)?;
        // Remember where this symbol has started
        self.offsets.push(self.position);
        self.position += symbol.len() as u64;
        Ok(())
    }

    pub fn finalize(&mut self) -> Result<(), IoError> {
        // Align the data to 8 bytes so that mmap can read `u64`s directly
        let padding = (8 - (self.position % 8)) % 8;
        self.file.write_all(&[0xcc; 8][..padding as usize])?;
        self.offsets.push(self.position);
        self.position += padding;

        let count = (self.offsets.len() as u64).to_le_bytes();

        #[cfg(target_endian = "little")]
        let slice = {
            let ptr = self.offsets.as_ptr() as *const u8;
            let len = self.offsets.len() * core::mem::size_of::<u64>();
            // Read offset bytes directly from memory, since they're already LE
            unsafe { core::slice::from_raw_parts(ptr, len) }
        };

        #[cfg(target_endian = "big")]
        compile_error!("Big endian targets are not implemented for SymbolDumper");

        self.file.write_all(&slice)?;
        self.file.seek(SeekFrom::Start(8))?;
        // Write offset table position
        self.file.write_all(&self.position.to_le_bytes())?;
        // Write the number of symbols
        self.file.write_all(&count)?;
        Ok(())
    }
}

impl Drop for SymbolDumper {
    fn drop(&mut self) {
        self.finalize().expect("failed to finalize");
    }
}

use memmap2::{Mmap};

pub struct SymbolMmap {
    mapping: Mmap,
    offsets: usize,
    count: usize,
}

fn read_u64(slice: &[u8]) -> u64 {
    let mut buf = [0; 8];
    buf.copy_from_slice(slice);
    u64::from_le_bytes(buf)
}

#[cfg(target_endian = "little")]
fn get_at_offset(mapping: &[u8], offset: usize) -> Option<&[u8]> {
    let mapping_ptr =  mapping.as_ptr();
    let [start, end] = unsafe {
        *(mapping_ptr.add(offset).cast::<[u64; 2]>())
    };
    mapping.get(start as usize..end as usize)
}

impl SymbolMmap {
    pub fn new(path: impl AsRef<Path>) -> Result<Self, IoError> {
        let file = OpenOptions::new()
            .read(true)
            .open(path.as_ref())?;
        let mapping = unsafe { Mmap::map(&file)? };
        if mapping.len() < 24 {
            return Err(IoError::other("Symtab file is too short for header"));
        }
        if &mapping[..8] != &SYMTAB_MAGIC {
            return Err(IoError::other("Invalid Symtab file magic"));
        }
        let offsets = read_u64(&mapping[8..16]) as usize;
        if offsets % 8 != 0 {
            return Err(IoError::other("Symyab offset table is not aligned"));
        }
        let count = (read_u64(&mapping[16..24]) as usize)
            .checked_sub(1).ok_or(IoError::other("Count can't be zero"))?;
        if mapping.len() < count * 8 + offsets {
            return Err(IoError::other("Symtab file is too short"));
        }
        Ok(Self {
            mapping,
            offsets: offsets / 8,
            count,
        })
    }

    pub fn len(&self) -> usize {
        self.count
    }

    pub fn get(&self, index: usize) -> Option<&[u8]> {
        if index >= self.count {
            return None;
        }
        get_at_offset(&self.mapping, (self.offsets + index) * 8)
    }

    pub fn get_range<'a>(&'a self, range: core::ops::Range<usize>) -> Option<SymbolIter<'a>> {
        if range.start >= self.count || range.end > self.count {
            return None;
        }
        Some(SymbolIter {
            mapping: &self.mapping,
            start: self.offsets + range.start,
            end: self.offsets + range.end,
        })
    }

    pub fn iter<'a>(&'a self) -> SymbolIter<'a> {
        SymbolIter {
            mapping: &*self.mapping,
            start: self.offsets,
            end: self.offsets + self.count,
        }
    }
}

impl core::ops::Index<usize> for SymbolMmap {
    type Output = [u8];
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

pub struct SymbolIter<'mapping> {
    mapping: &'mapping [u8],
    start: usize,
    end: usize,
}

impl<'mapping> Iterator for SymbolIter<'mapping> {
    type Item = &'mapping [u8];
    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            return None;
        }
        let rv = get_at_offset(self.mapping, self.start * 8);
        self.start += 1;
        rv
    }
}

impl<'mapping> DoubleEndedIterator for SymbolIter<'mapping> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            return None;
        }
        self.end -= 1;
        get_at_offset(self.mapping, self.end * 8)
    }
}

#[cfg(test)]
mod tests {
    use super::{SymbolDumper, SymbolMmap};
    #[test]
    fn test_roundtrip() {
        let symbols: &[&[u8]] = &["hello", "world", "123"]
            .map(|s| s.as_ref());
        let path = "dumper_test.sym";
        let mut dumper = SymbolDumper::new(path)
            .expect("failed to open file for dumping");
        for sym in symbols {
            dumper.push(sym).expect("failed to dump symbol");
        }
        drop(dumper);
        let sym_map = SymbolMmap::new(path).expect("failed to mmap symtab");
        // Iterator
        let recovered: Vec<&[u8]> = sym_map.iter().collect::<Vec<_>>();
        assert_eq!(&symbols[..], &recovered);
        // DoubleEndedIterator
        let mut recovered: Vec<&[u8]> = sym_map.iter().rev().collect::<Vec<_>>();
        recovered.reverse();
        assert_eq!(&symbols[..], &recovered);
        drop(sym_map);
        std::fs::remove_file(path).expect("failed to remove file");
    }
    #[test]
    fn test_range() {
        let symbols: &[&[u8]] = &["hello", "world", "123"]
            .map(|s| s.as_ref());
        let path = "dumper_test_range.sym";
        let mut dumper = SymbolDumper::new(path)
            .expect("failed to open file for dumping");
        for sym in symbols {
            dumper.push(sym).expect("failed to dump symbol");
        }
        drop(dumper);
        let sym_map = SymbolMmap::new(path).expect("failed to mmap symtab");
        for start in 0..3 {
            for end in start..3 {
                let recovered: Vec<&[u8]> = sym_map
                    .get_range(start..end).expect("failed range")
                    .collect::<Vec<_>>();
                assert_eq!(&symbols[start..end], &recovered);
            }
        }
        std::fs::remove_file(path).expect("failed to remove file");
    }
}
