# messagepack: a MessagePack reader and printer, with a proved round trip

A MessagePack reader and printer in Lean, following the MessagePack specification's format table. The reader reads one value in any of the format's forms; the printer writes a value back in one fixed canonical form, the smallest form that holds it. The main claim is proved: parsing what the printer wrote returns the same value. The tests run the tool against a strict oracle written from the specification and against Python's `msgpack` library; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `MessagePack/Value.lean` (the value type, the printer, and the well-formedness rules) and `MessagePack/Parse.lean` (the reader). The proofs are in `Proofs/RoundTrip.lean`, and worked examples from the specification are proved in `Proofs/Examples.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed value gives the value back. | `MessagePack.Proofs.parse_print` |
| The same with the bytes after the value left in place, at a fuel that covers the printed length: the form the induction proves. | `MessagePack.Proofs.parseGo_print` |
| Reading back a printed unsigned integer of any width gives the number back. | `MessagePack.Proofs.readNat_writeBE` |
| Reading back a printed signed integer of any width gives the number back. | `MessagePack.Proofs.readSigned_writeBE` |

A value is well formed when an integer lies from -2^63 to 2^64 - 1, a float pattern fits its width, an extension code lies from -128 to 127, every string, blob, extension body, array, and map is shorter than 2^32, and every value inside an array or map is well formed too. The length bound is there because the widest length form is 32 bits: a longer body could not be printed, so it could not round trip. `parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with `#print axioms MessagePack.Proofs.parse_print`, or by running `lake env lean MessagePack/Verify.lean`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the reader accepts every byte string the format allows, and rejects every one it forbids. The round trip does not need either, so neither is proved. The oracle differential and the mutation tests check that behaviour instead, and the results file records the outcome.
- Anything about the insides of an extension value. An extension value is a type code and raw bytes; what the bytes mean for a given code is the business of the application that owns the code.
- Anything about string contents. A string is held as raw bytes and is never checked as UTF-8, so a string this slice reads need not be text any other reader would accept as text.
- Anything about float values. A float is held as its bit pattern and printed back pattern for pattern; the library never turns a pattern into a number, so it cannot say that two patterns are the same float.
- Which pair a map lookup would find. Duplicate keys are kept as written, in order. There is no lookup function.
- Reading requests and printing answers in `Main.lean`: splitting lines, and the decimal number reader. The tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits proofs, not large data. The reader also bounds nesting by the length of the input, which very deep inputs can reach.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict oracle in the test harness, written from the specification's format table, and Python's `msgpack` library in the differential tests. The results file names the version used.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 207,0,0,0,0,0,0,0,1" | .lake/build/bin/messagepack
```

That request is the value 1 carried in a uint64, and the answer is `ok:1`: the value read back and reprinted in its smallest form. Bytes the reader rejects, such as the single byte 193 (the never used marker 0xc1), answer `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.

```
lake build
grep -rn "sorry" --include="*.lean" MessagePack Proofs Main.lean MessagePack.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, runs the fixed cases, the width boundaries, the differential against the strict oracle, the differential against Python's `msgpack` library when the interpreter running it has that library (without it, that part is skipped and the results file says so), and the mutation cases, and writes the counts to `tests/TEST-RESULTS.md`.
