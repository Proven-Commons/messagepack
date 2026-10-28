/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trip is the theorem proved in
  `Proofs/RoundTrip.lean`. The refusals are single inputs,
  checked in the kernel with `decide +kernel`: no native
  evaluation, which the bar forbids.
-/

import MessagePack
import Proofs.RoundTrip

open MessagePack

theorem Spec.parse_print (v : Value) (h : WF v) :
    parse (print v) = some v :=
  MessagePack.Proofs.parse_print h


theorem Spec.rejects_str8_size_lie :
    parse [0xd9, 10, 0x61, 0x62, 0x63] = none := by
  decide +kernel


theorem Spec.rejects_bin16_size_lie :
    parse [0xc5, 1, 0, 9, 9] = none := by
  decide +kernel


theorem Spec.rejects_ext8_size_lie :
    parse [0xc7, 9, 5, 1, 2] = none := by
  decide +kernel


theorem Spec.rejects_array16_cut_short :
    parse [0xdc, 0, 5, 1, 2] = none := by
  decide +kernel


theorem Spec.rejects_fixarray_count_runs_out :
    parse [0x93, 1, 2] = none := by
  decide +kernel


theorem Spec.rejects_map32_cut_short :
    parse [0xdf, 255, 255, 255, 255] = none := by
  decide +kernel


theorem Spec.rejects_fixext4_cut_short :
    parse [0xd6, 5, 1, 2] = none := by
  decide +kernel


theorem Spec.rejects_never_used :
    parse [0xc1] = none := by
  decide +kernel


theorem Spec.rejects_never_used_inside_array :
    parse [0x92, 1, 0xc1] = none := by
  decide +kernel


theorem Spec.rejects_trailing_byte :
    parse [0x01, 0x02] = none := by
  decide +kernel


theorem Spec.rejects_truncated_uint16 :
    parse [0xcd] = none := by
  decide +kernel


theorem Spec.rejects_empty_input :
    parse [] = none := by
  decide +kernel
