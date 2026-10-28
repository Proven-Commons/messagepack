/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `MessagePack/Value.lean`
  and `MessagePack/Parse.lean`, the code under proof named in
  `bar.toml`. No definition of their own is needed, so this project
  has no `Spec/Defs.lean`.
-/

import MessagePack

open MessagePack

/-! ## The round trip

The statement the slice stands on. It is the statement of the
proved theorem of the same shape in `Proofs/RoundTrip.lean`,
over the same well formedness predicate, `MessagePack.WF`. -/

/-- Parsing the printed form of a well formed value gives the
    value back. So a printer that wrote nothing, or wrote the
    wrong bytes, fails this statement. -/
theorem Spec.parse_print (v : Value) (h : WF v) :
    parse (print v) = some v := sorry

/-! ## Refused inputs

Single inputs the reader refuses, one for each headline rule of
`SPEC.md`. Each input is one of the named rejection cases in the
test harness. The differential tests cover these rules on many
more inputs; these statements pin them so a reader of the
specification can check each rule against one concrete case. -/

/-- A str 8 header claiming 10 bytes with only 3 standing after
    it is refused: the length runs past the end of the input. -/
theorem Spec.rejects_str8_size_lie :
    parse [0xd9, 10, 0x61, 0x62, 0x63] = none := sorry

/-- A bin 16 header claiming 256 bytes with only 2 standing
    after it is refused. -/
theorem Spec.rejects_bin16_size_lie :
    parse [0xc5, 1, 0, 9, 9] = none := sorry

/-- An ext 8 header claiming 9 payload bytes with a type byte
    and only 2 standing after it is refused. -/
theorem Spec.rejects_ext8_size_lie :
    parse [0xc7, 9, 5, 1, 2] = none := sorry

/-- An array 16 header claiming 5 values with only 2 standing
    after it is refused: the members run out. -/
theorem Spec.rejects_array16_cut_short :
    parse [0xdc, 0, 5, 1, 2] = none := sorry

/-- A fixarray claiming 3 values with only 2 standing after it
    is refused. -/
theorem Spec.rejects_fixarray_count_runs_out :
    parse [0x93, 1, 2] = none := sorry

/-- A map 32 header claiming 2^32 - 1 pairs with none standing
    after it is refused. -/
theorem Spec.rejects_map32_cut_short :
    parse [0xdf, 255, 255, 255, 255] = none := sorry

/-- A fixext 4 value holding its type byte and only 2 of its 4
    data bytes is refused. -/
theorem Spec.rejects_fixext4_cut_short :
    parse [0xd6, 5, 1, 2] = none := sorry

/-- The never used marker 0xc1 is refused. -/
theorem Spec.rejects_never_used :
    parse [0xc1] = none := sorry

/-- The never used marker is refused inside an array too: it is
    rejected wherever a value is read. -/
theorem Spec.rejects_never_used_inside_array :
    parse [0x92, 1, 0xc1] = none := sorry

/-- Two complete values in a row are refused: the reader reads
    exactly one value, and bytes left over turn it away. -/
theorem Spec.rejects_trailing_byte :
    parse [0x01, 0x02] = none := sorry

/-- A uint 16 marker with none of its two bytes standing after
    it is refused: the value is cut short. -/
theorem Spec.rejects_truncated_uint16 :
    parse [0xcd] = none := sorry

/-- The empty input is refused: it holds no value. -/
theorem Spec.rejects_empty_input :
    parse [] = none := sorry
