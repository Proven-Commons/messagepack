# MessagePack codec: specification

This is the specification of the first slice for the
`messagepack` package: the MessagePack format at the level of
bytes, in Lean, with the round trip proved. The format itself is
defined by the MessagePack specification (the type table at
github.com/msgpack/msgpack, spec.md); this file states what the
slice does with it.

What the slice is: a reader and a printer for one MessagePack
value. What it is not: a streaming reader, a schema layer, or any
reading of the insides of an extension value. An extension value
is a type code and raw bytes, and nothing more.

## The value type

A value is one of:

- nil
- a boolean
- an integer, held as a Lean `Int`
- a 32 bit float, held as its 32 bit pattern (a natural number
  below 2^32)
- a 64 bit float, held as its 64 bit pattern (a natural number
  below 2^64)
- a string, held as a list of bytes; the bytes are not checked
  as UTF-8
- a binary blob, held as a list of bytes
- an array, held as a list of values
- a map, held as a list of key and value pairs, in order;
  duplicate keys are kept as written
- an extension value: a type code held as an `Int`, and a list
  of bytes

## The marker table

Every value starts with one marker byte. Multi byte numbers are
big endian: the first byte after the marker is the most
significant.

| Marker | Form | What follows |
| --- | --- | --- |
| 0x00 to 0x7f | positive fixint | the marker itself is the value, 0 to 127 |
| 0x80 to 0x8f | fixmap | the low 4 bits are the pair count; that many key and value pairs follow |
| 0x90 to 0x9f | fixarray | the low 4 bits are the element count; that many values follow |
| 0xa0 to 0xbf | fixstr | the low 5 bits are the byte length; that many bytes follow |
| 0xc0 | nil | nothing |
| 0xc1 | never used | always rejected |
| 0xc2 | false | nothing |
| 0xc3 | true | nothing |
| 0xc4 | bin 8 | a 1 byte length, then that many bytes |
| 0xc5 | bin 16 | a 2 byte length, then that many bytes |
| 0xc6 | bin 32 | a 4 byte length, then that many bytes |
| 0xc7 | ext 8 | a 1 byte length, a type byte, then that many bytes |
| 0xc8 | ext 16 | a 2 byte length, a type byte, then that many bytes |
| 0xc9 | ext 32 | a 4 byte length, a type byte, then that many bytes |
| 0xca | float 32 | the 4 bytes of the pattern |
| 0xcb | float 64 | the 8 bytes of the pattern |
| 0xcc | uint 8 | 1 byte, unsigned |
| 0xcd | uint 16 | 2 bytes, unsigned |
| 0xce | uint 32 | 4 bytes, unsigned |
| 0xcf | uint 64 | 8 bytes, unsigned |
| 0xd0 | int 8 | 1 byte, signed |
| 0xd1 | int 16 | 2 bytes, signed |
| 0xd2 | int 32 | 4 bytes, signed |
| 0xd3 | int 64 | 8 bytes, signed |
| 0xd4 | fixext 1 | a type byte, then 1 byte |
| 0xd5 | fixext 2 | a type byte, then 2 bytes |
| 0xd6 | fixext 4 | a type byte, then 4 bytes |
| 0xd7 | fixext 8 | a type byte, then 8 bytes |
| 0xd8 | fixext 16 | a type byte, then 16 bytes |
| 0xd9 | str 8 | a 1 byte length, then that many bytes |
| 0xda | str 16 | a 2 byte length, then that many bytes |
| 0xdb | str 32 | a 4 byte length, then that many bytes |
| 0xdc | array 16 | a 2 byte count, then that many values |
| 0xdd | array 32 | a 4 byte count, then that many values |
| 0xde | map 16 | a 2 byte count, then that many key and value pairs |
| 0xdf | map 32 | a 4 byte count, then that many key and value pairs |
| 0xe0 to 0xff | negative fixint | the marker read as a signed byte is the value, -32 to -1 |

A signed integer is stored in two's complement in its width:
the pattern at or above half the width reads as the pattern
minus the full width. An extension type byte reads the same
way, as a signed byte: the byte 255 is the code -1.

## The reader

The reader reads every form in the table, not only the smallest
form of a value. A value carried in a wider form than it needs
reads to the same value. It reads exactly one value and rejects:

- the marker 0xc1, anywhere a value is read,
- a value cut short at any point: a missing width byte, a string
  or blob whose length runs past the end of the input, an array
  or map whose elements run out,
- bytes left over after one complete value.

Nested values recurse. The reader carries a fuel bounded by the
input length; each nesting level eats at least its marker byte,
so the fuel always lasts for a value the input can hold, and a
hostile nesting cannot loop.

## Well formed values

A value is well formed when:

- an integer lies from -2^63 to 2^64 - 1,
- a float pattern fits its width,
- an extension code lies from -128 to 127,
- every string, blob, extension body, array, and map is shorter
  than 2^32, and every value inside an array or map is well
  formed too.

The length bound is there because the widest length form is 32
bits: a longer body could not be printed, so it could not round
trip.

## The printer

The printer writes one fixed canonical form, the smallest form
that holds the value:

- Integers: 0 to 127 as positive fixint; -32 to -1 as negative
  fixint; a nonnegative integer then in the smallest unsigned
  form that holds it (uint 8 to 255, uint 16, uint 32, uint 64);
  a negative integer then in the smallest signed form that holds
  it (int 8 down to -128, int 16, int 32, int 64). A nonnegative
  value never prints in a signed form, and a negative value
  never in an unsigned form.
- Strings: fixstr below 32 bytes, then str 8, str 16, str 32.
- Binary blobs: bin 8, bin 16, bin 32 (there is no fix form).
- Arrays: fixarray below 16 elements, then array 16, array 32.
- Maps: fixmap below 16 pairs, then map 16, map 32.
- Floats: their width's marker and the pattern, big endian.
- Extension values: fixext when the length is 1, 2, 4, 8, or
  16, else the smallest of ext 8, ext 16, ext 32. The type code
  prints as its signed byte pattern.
- nil and the booleans print as their single markers.

## The line protocol

The command line tool reads one request per line: the operation
and a payload, parted by one space. The payload is decimal byte
numbers parted by commas, with no spaces. A number is plain
decimal: no sign, no leading zeros (the number 0 itself is
written `0`), at most twenty digits. An empty line gets no
answer. A request that breaks these rules prints `error`, as
does an unknown operation.

The one operation is `parse`. It parses the bytes as one value
and prints `ok:` followed by the bytes of the canonical reprint,
comma parted, when the bytes are exactly one value this slice
reads. It prints `none` when the bytes are well formed as a
request but are not one value this slice reads. The empty
payload is the empty byte list and answers `none`.

Example: the request `parse 207,0,0,0,0,0,0,0,1` is the value 1
carried in a uint64. The answer is `ok:1`: the value read back,
reprinted in its smallest form.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The refusal theorems
are single inputs, one for each named rejection case in the
test harness; the tests in `tests/` cover each rule on many
more inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed value gives the value back | `Spec.parse_print` |
| A str 8 header claiming more bytes than stand after it is refused | `Spec.rejects_str8_size_lie` |
| A bin 16 header claiming more bytes than stand after it is refused | `Spec.rejects_bin16_size_lie` |
| An ext 8 header claiming more payload bytes than stand after it is refused | `Spec.rejects_ext8_size_lie` |
| An array 16 header claiming more values than stand after it is refused | `Spec.rejects_array16_cut_short` |
| A fixarray claiming more values than stand after it is refused | `Spec.rejects_fixarray_count_runs_out` |
| A map 32 header claiming 2^32 - 1 pairs with none after it is refused | `Spec.rejects_map32_cut_short` |
| A fixext 4 value cut short in its data bytes is refused | `Spec.rejects_fixext4_cut_short` |
| The never used marker 0xc1 is refused | `Spec.rejects_never_used` |
| The never used marker is refused wherever a value is read, here inside an array | `Spec.rejects_never_used_inside_array` |
| Bytes left over after one complete value are refused | `Spec.rejects_trailing_byte` |
| A value cut short, here a uint 16 marker with no bytes after it, is refused | `Spec.rejects_truncated_uint16` |
| The empty input is refused | `Spec.rejects_empty_input` |
