/-
  Worked examples from the MessagePack specification, proved.
  The same examples run through the command line tool in the
  test harness, where they are checked byte by byte a second
  time.

  The examples cover one value of every family, the integer
  widths at their boundaries, one non canonical width read back
  to its canonical form, and the rejections this slice promises:
  the never used marker 0xc1, a truncated value, and trailing
  bytes after one complete value.
-/

import MessagePack

namespace MessagePack.Examples

open MessagePack

theorem parse_nil : parse [0xc0] = some .nil := by decide

theorem parse_false : parse [0xc2] = some (.bool false) := by decide

theorem parse_true : parse [0xc3] = some (.bool true) := by decide

/-- The never used marker is rejected. -/
theorem parse_never_used : parse [0xc1] = none := by decide

theorem parse_pos_fixint : parse [0x01] = some (.int 1) := by decide

theorem parse_pos_fixint_max : parse [0x7f] = some (.int 127) := by decide

theorem parse_neg_fixint : parse [0xe0] = some (.int (-32)) := by decide

theorem parse_neg_fixint_last : parse [0xff] = some (.int (-1)) := by decide

theorem parse_uint8 : parse [0xcc, 0xff] = some (.int 255) := by decide

theorem parse_uint16 : parse [0xcd, 0x01, 0x00] = some (.int 256) := by decide

/-- A value carried in a wider form than it needs still reads,
    here 1 in a uint64. It reprints in the smallest form. -/
theorem parse_uint64_of_one :
    parse [0xcf, 0, 0, 0, 0, 0, 0, 0, 1] = some (.int 1) := by decide

theorem print_uint64_max :
    print (.int 18446744073709551615) =
      [0xcf, 255, 255, 255, 255, 255, 255, 255, 255] := by decide

theorem parse_int8_min : parse [0xd0, 0x80] = some (.int (-128)) := by decide

theorem parse_int64_min :
    parse [0xd3, 0x80, 0, 0, 0, 0, 0, 0, 0] =
      some (.int (-9223372036854775808)) := by decide

theorem print_neg_fixint : print (.int (-32)) = [0xe0] := by decide

/-- The float 1.0 in both widths, held as its bit pattern. -/
theorem parse_float32_one :
    parse [0xca, 0x3f, 0x80, 0, 0] = some (.float32 1065353216) := by decide

theorem parse_float64_one :
    parse [0xcb, 0x3f, 0xf0, 0, 0, 0, 0, 0, 0] =
      some (.float64 4607182418800017408) := by decide

theorem parse_fixstr :
    parse [0xa3, 0x61, 0x62, 0x63] = some (.str [0x61, 0x62, 0x63]) := by decide

theorem parse_bin8 : parse [0xc4, 0x02, 0x01, 0x02] =
    some (.bin [0x01, 0x02]) := by decide

theorem parse_fixarray : parse [0x91, 0x01] = some (.array [.int 1]) := by decide

theorem parse_fixmap :
    parse [0x81, 0x01, 0x02] = some (.map [(.int 1, .int 2)]) := by decide

theorem parse_fixext1 :
    parse [0xd4, 0x05, 0xaa] = some (.ext 5 [0xaa]) := by decide

/-- An extension type byte of 255 is the code -1. -/
theorem parse_fixext_negative_type :
    parse [0xd4, 0xff, 0xaa] = some (.ext (-1) [0xaa]) := by decide

/-- Two complete values in a row are rejected: one value only. -/
theorem parse_trailing : parse [0x01, 0x02] = none := by decide

/-- A truncated value is rejected. -/
theorem parse_truncated : parse [0xcd, 0x01] = none := by decide

/-- A nested value, read back whole. -/
theorem parse_nested :
    parse [0x92, 0x01, 0x81, 0xa1, 0x61, 0xc3] =
      some (.array [.int 1, .map [(.str [0x61], .bool true)]]) := by decide

end MessagePack.Examples
