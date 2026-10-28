# messagepack: a MessagePack reader and printer, with a proved round trip

Status: in-progress

A MessagePack reader and printer in Lean, following the MessagePack specification's format table. The reader reads one value in any of the format's forms; the printer writes a value back in one fixed canonical form, the smallest form that holds it. The main claim is proved: parsing what the printer wrote returns the same value. The definitions are in `MessagePack/Value.lean` (the value type, the printer, and the well-formedness rules) and `MessagePack/Parse.lean` (the reader). The rules are written out in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`, with their proofs in `Proofs/SpecProofs.lean`. No reviewer has approved them yet, so this project is not called verified.

## How to run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 207,0,0,0,0,0,0,0,1" | .lake/build/bin/messagepack
```

That request is the value 1 carried in a uint64, and the answer is `ok:1`: the value read back and reprinted in its smallest form. Bytes the reader rejects, such as the single byte 193 (the never used marker 0xc1), answer `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the fixed cases, the width boundaries, the differential against the strict oracle, the differential against Python's `msgpack` library when the interpreter running it has that library (without it, that part is skipped and the results file says so), and the mutation cases, and writes the counts to `tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The theorems are stated in `Spec.lean` (the challenge file, where they end in `sorry`) and proved in `Proofs/SpecProofs.lean`, under the same names. `comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed value gives the value back. | `Spec.parse_print` |
| A str 8 header claiming 10 bytes with only 3 standing after it is refused: the length runs past the end of the input. | `Spec.rejects_str8_size_lie` |
| A bin 16 header claiming 256 bytes with only 2 standing after it is refused. | `Spec.rejects_bin16_size_lie` |
| An ext 8 header claiming 9 payload bytes with a type byte and only 2 standing after it is refused. | `Spec.rejects_ext8_size_lie` |
| An array 16 header claiming 5 values with only 2 standing after it is refused: the members run out. | `Spec.rejects_array16_cut_short` |
| A fixarray claiming 3 values with only 2 standing after it is refused. | `Spec.rejects_fixarray_count_runs_out` |
| A map 32 header claiming 2^32 - 1 pairs with none standing after it is refused. | `Spec.rejects_map32_cut_short` |
| A fixext 4 value holding its type byte and only 2 of its 4 data bytes is refused. | `Spec.rejects_fixext4_cut_short` |
| The never used marker 0xc1 is refused. | `Spec.rejects_never_used` |
| The never used marker is refused inside an array too: it is rejected wherever a value is read. | `Spec.rejects_never_used_inside_array` |
| Two complete values in a row are refused: the reader reads exactly one value, and bytes left over turn it away. | `Spec.rejects_trailing_byte` |
| A uint 16 marker with none of its two bytes standing after it is refused: the value is cut short. | `Spec.rejects_truncated_uint16` |
| The empty input is refused: it holds no value. | `Spec.rejects_empty_input` |

A value is well formed when an integer lies from -2^63 to 2^64 - 1, a float pattern fits its width, an extension code lies from -128 to 127, every string, blob, extension body, array, and map is shorter than 2^32, and every value inside an array or map is well formed too. The length bound is there because the widest length form is 32 bits: a longer body could not be printed, so it could not round trip.

The round trip theorem rests on the proofs in `Proofs/RoundTrip.lean`, where it is `MessagePack.Proofs.parse_print`. Under it, the same file proves the form the induction needs, with the bytes after the value left in place (`MessagePack.Proofs.parseGo_print`), and the byte level round trips the reader and printer share (`MessagePack.Proofs.readNat_writeBE` and `MessagePack.Proofs.readSigned_writeBE`). Worked examples from the specification, one value of every family and the width boundaries among them, are proved in `Proofs/Examples.lean`. The round trip checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with `#print axioms MessagePack.Proofs.parse_print`, or by running `lake env lean MessagePack/Verify.lean`. The refusal theorems are single inputs checked in the kernel with `decide +kernel`.

The command-line tool in `Main.lean` calls `MessagePack.parse` and `MessagePack.print` directly, the same functions the theorems are about.

## What is not proved

- That the reader accepts every byte string the format allows, and rejects every one it forbids. The round trip does not need either, and the refusal theorems pin single inputs only, so neither holds in general as a proof. The oracle differential and the mutation tests check that behaviour instead, and the results file records the outcome.
- Anything about the insides of an extension value. An extension value is a type code and raw bytes; what the bytes mean for a given code is the business of the application that owns the code.
- Anything about string contents. A string is held as raw bytes and is never checked as UTF-8, so a string this slice reads need not be text any other reader would accept as text.
- Anything about float values. A float is held as its bit pattern and printed back pattern for pattern; the library never turns a pattern into a number, so it cannot say that two patterns are the same float.
- Which pair a map lookup would find. Duplicate keys are kept as written, in order. There is no lookup function.
- Reading requests and printing answers in `Main.lean`: splitting lines, and the decimal number reader. The tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits proofs, not large data. The reader also bounds nesting by the length of the input, which very deep inputs can reach.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in `lean-toolchain`), which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, which turns the proved definitions into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest lists no packages, so there are no library dependencies to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the MessagePack format as you intend it. The proofs are about the reader and printer in this repo following each other exactly; the fidelity of the spec to the format is a reading of the specification's type table, pinned in `SPEC.md` where the format leaves a choice open.
- The strict oracle in the test harness, written from the specification's format table, and Python's `msgpack` library in the differential tests. Both are evidence, not proof. The results file names the version used.
- The line handling in `Main.lean` (splitting a request line, reading decimal numbers). The tests drive it, and no proof covers it.
- There are no exceptions to item 4 of the bar: the project uses none of the features it forbids.

## Re-check it

Needs Linux, elan, and Python 3.

1. `lake comparator --paranoid`: builds the challenge file `Spec.lean` and the proofs in a sandbox and checks that each theorem named in `comparator.json` proves exactly the statement in the challenge file, uses no axiom but the three standard ones, and is accepted by Lean's kernel and every other kernel shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the width boundaries, the differential against the strict oracle, the differential against Python's `msgpack` library when the interpreter running it has that library, and the mutation cases, with counts and any failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool build clean, and `lake env lean MessagePack/Verify.lean` prints the axiom list for the claims.
4. Read `SPEC.md` against the MessagePack specification and check the format table is the one you want.
