/-
  The round trip proof: parsing the printed form of a well
  formed value gives the value back.

  The statements proved here are `parse_print` and its fuelled
  form `parseGo_print`. A matching statement in a spec file
  still has to be added by a reviewer, so this file builds on its
  own, in the same shape as the codec and json proofs.

  The work goes in stages. First, case lemmas for the printer's
  own choices: the integer width chain and the length headers
  each get an eliminator that hands every branch its condition
  and the failure of every earlier condition. Then the readers:
  a big endian writing reads back at every width, a signed
  writing reads back at every width, and a byte run reads back
  whole. Then the member readers, and at last the value reader
  itself, by induction on a bound for the value's size.
-/

import MessagePack

namespace MessagePack.Proofs

open MessagePack

/-! ## Unfolding rules for the headers -/

/-- The unfolding rule for `strHeader`. -/
theorem strHeader_def (len : Nat) :
    strHeader len =
      if len < 32 then [(0xa0 + len).toUInt8]
      else if len ≤ 255 then (0xd9 : UInt8) :: writeBE 1 len
      else if len ≤ 65535 then (0xda : UInt8) :: writeBE 2 len
      else (0xdb : UInt8) :: writeBE 4 len := by
  rw [strHeader]

/-- The unfolding rule for `binHeader`. -/
theorem binHeader_def (len : Nat) :
    binHeader len =
      if len ≤ 255 then (0xc4 : UInt8) :: writeBE 1 len
      else if len ≤ 65535 then (0xc5 : UInt8) :: writeBE 2 len
      else (0xc6 : UInt8) :: writeBE 4 len := by
  rw [binHeader]

/-- The unfolding rule for `arrayHeader`. -/
theorem arrayHeader_def (len : Nat) :
    arrayHeader len =
      if len < 16 then [(0x90 + len).toUInt8]
      else if len ≤ 65535 then (0xdc : UInt8) :: writeBE 2 len
      else (0xdd : UInt8) :: writeBE 4 len := by
  rw [arrayHeader]

/-- The unfolding rule for `mapHeader`. -/
theorem mapHeader_def (len : Nat) :
    mapHeader len =
      if len < 16 then [(0x80 + len).toUInt8]
      else if len ≤ 65535 then (0xde : UInt8) :: writeBE 2 len
      else (0xdf : UInt8) :: writeBE 4 len := by
  rw [mapHeader]

/-! ## Case lemmas for the printer's choices -/

/-- The integer printer's ten cases. Each branch is handed its
    own condition and the failure of every earlier condition, so
    a caller with the well formed bounds in hand can pin the
    exact range by arithmetic. -/
theorem printInt_elim {P : List UInt8 → Prop} (n : Int)
    (h1 : (0 ≤ n ∧ n ≤ 127) → P [n.toNat.toUInt8])
    (h2 : ¬ (0 ≤ n ∧ n ≤ 127) → (-32 ≤ n ∧ n ≤ -1) → P [(n + 256).toNat.toUInt8])
    (h3 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → (0 ≤ n ∧ n ≤ 255) →
      P ((0xcc : UInt8) :: writeBE 1 n.toNat))
    (h4 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      (0 ≤ n ∧ n ≤ 65535) → P ((0xcd : UInt8) :: writeBE 2 n.toNat))
    (h5 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → (0 ≤ n ∧ n ≤ 4294967295) →
      P ((0xce : UInt8) :: writeBE 4 n.toNat))
    (h6 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → ¬ (0 ≤ n ∧ n ≤ 4294967295) →
      (0 ≤ n ∧ n ≤ 18446744073709551615) → P ((0xcf : UInt8) :: writeBE 8 n.toNat))
    (h7 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → ¬ (0 ≤ n ∧ n ≤ 4294967295) →
      ¬ (0 ≤ n ∧ n ≤ 18446744073709551615) → (-128 ≤ n) →
      P ((0xd0 : UInt8) :: writeBE 1 (signedPattern 1 n)))
    (h8 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → ¬ (0 ≤ n ∧ n ≤ 4294967295) →
      ¬ (0 ≤ n ∧ n ≤ 18446744073709551615) → ¬ (-128 ≤ n) → (-32768 ≤ n) →
      P ((0xd1 : UInt8) :: writeBE 2 (signedPattern 2 n)))
    (h9 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → ¬ (0 ≤ n ∧ n ≤ 4294967295) →
      ¬ (0 ≤ n ∧ n ≤ 18446744073709551615) → ¬ (-128 ≤ n) → ¬ (-32768 ≤ n) →
      (-2147483648 ≤ n) → P ((0xd2 : UInt8) :: writeBE 4 (signedPattern 4 n)))
    (h10 : ¬ (0 ≤ n ∧ n ≤ 127) → ¬ (-32 ≤ n ∧ n ≤ -1) → ¬ (0 ≤ n ∧ n ≤ 255) →
      ¬ (0 ≤ n ∧ n ≤ 65535) → ¬ (0 ≤ n ∧ n ≤ 4294967295) →
      ¬ (0 ≤ n ∧ n ≤ 18446744073709551615) → ¬ (-128 ≤ n) → ¬ (-32768 ≤ n) →
      ¬ (-2147483648 ≤ n) → P ((0xd3 : UInt8) :: writeBE 8 (signedPattern 8 n))) :
    P (printInt n) := by
  rw [printInt_def]
  by_cases c1 : 0 ≤ n ∧ n ≤ 127
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : -32 ≤ n ∧ n ≤ -1
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]
      by_cases c3 : 0 ≤ n ∧ n ≤ 255
      · rw [if_pos c3]; exact h3 c1 c2 c3
      · rw [if_neg c3]
        by_cases c4 : 0 ≤ n ∧ n ≤ 65535
        · rw [if_pos c4]; exact h4 c1 c2 c3 c4
        · rw [if_neg c4]
          by_cases c5 : 0 ≤ n ∧ n ≤ 4294967295
          · rw [if_pos c5]; exact h5 c1 c2 c3 c4 c5
          · rw [if_neg c5]
            by_cases c6 : 0 ≤ n ∧ n ≤ 18446744073709551615
            · rw [if_pos c6]; exact h6 c1 c2 c3 c4 c5 c6
            · rw [if_neg c6]
              by_cases c7 : -128 ≤ n
              · rw [if_pos c7]; exact h7 c1 c2 c3 c4 c5 c6 c7
              · rw [if_neg c7]
                by_cases c8 : -32768 ≤ n
                · rw [if_pos c8]; exact h8 c1 c2 c3 c4 c5 c6 c7 c8
                · rw [if_neg c8]
                  by_cases c9 : -2147483648 ≤ n
                  · rw [if_pos c9]; exact h9 c1 c2 c3 c4 c5 c6 c7 c8 c9
                  · rw [if_neg c9]; exact h10 c1 c2 c3 c4 c5 c6 c7 c8 c9

/-- The string header's four cases. -/
theorem strHeader_elim {P : List UInt8 → Prop} (len : Nat)
    (h1 : len < 32 → P [(0xa0 + len).toUInt8])
    (h2 : ¬ len < 32 → len ≤ 255 → P ((0xd9 : UInt8) :: writeBE 1 len))
    (h3 : ¬ len < 32 → ¬ len ≤ 255 → len ≤ 65535 → P ((0xda : UInt8) :: writeBE 2 len))
    (h4 : ¬ len < 32 → ¬ len ≤ 255 → ¬ len ≤ 65535 → P ((0xdb : UInt8) :: writeBE 4 len)) :
    P (strHeader len) := by
  rw [strHeader_def]
  by_cases c1 : len < 32
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : len ≤ 255
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]
      by_cases c3 : len ≤ 65535
      · rw [if_pos c3]; exact h3 c1 c2 c3
      · rw [if_neg c3]; exact h4 c1 c2 c3

/-- The blob header's three cases. -/
theorem binHeader_elim {P : List UInt8 → Prop} (len : Nat)
    (h1 : len ≤ 255 → P ((0xc4 : UInt8) :: writeBE 1 len))
    (h2 : ¬ len ≤ 255 → len ≤ 65535 → P ((0xc5 : UInt8) :: writeBE 2 len))
    (h3 : ¬ len ≤ 255 → ¬ len ≤ 65535 → P ((0xc6 : UInt8) :: writeBE 4 len)) :
    P (binHeader len) := by
  rw [binHeader_def]
  by_cases c1 : len ≤ 255
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : len ≤ 65535
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]; exact h3 c1 c2

/-- The array header's three cases. -/
theorem arrayHeader_elim {P : List UInt8 → Prop} (len : Nat)
    (h1 : len < 16 → P [(0x90 + len).toUInt8])
    (h2 : ¬ len < 16 → len ≤ 65535 → P ((0xdc : UInt8) :: writeBE 2 len))
    (h3 : ¬ len < 16 → ¬ len ≤ 65535 → P ((0xdd : UInt8) :: writeBE 4 len)) :
    P (arrayHeader len) := by
  rw [arrayHeader_def]
  by_cases c1 : len < 16
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : len ≤ 65535
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]; exact h3 c1 c2

/-- The map header's three cases. -/
theorem mapHeader_elim {P : List UInt8 → Prop} (len : Nat)
    (h1 : len < 16 → P [(0x80 + len).toUInt8])
    (h2 : ¬ len < 16 → len ≤ 65535 → P ((0xde : UInt8) :: writeBE 2 len))
    (h3 : ¬ len < 16 → ¬ len ≤ 65535 → P ((0xdf : UInt8) :: writeBE 4 len)) :
    P (mapHeader len) := by
  rw [mapHeader_def]
  by_cases c1 : len < 16
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : len ≤ 65535
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]; exact h3 c1 c2

/-- The extension printer's eight cases. -/
theorem printExt_elim {P : List UInt8 → Prop} (code : Int) (bs : List UInt8)
    (h1 : bs.length = 1 → P ((0xd4 : UInt8) :: extTypeByte code :: bs))
    (h2 : bs.length ≠ 1 → bs.length = 2 → P ((0xd5 : UInt8) :: extTypeByte code :: bs))
    (h3 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length = 4 →
      P ((0xd6 : UInt8) :: extTypeByte code :: bs))
    (h4 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length ≠ 4 → bs.length = 8 →
      P ((0xd7 : UInt8) :: extTypeByte code :: bs))
    (h5 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length ≠ 4 → bs.length ≠ 8 →
      bs.length = 16 → P ((0xd8 : UInt8) :: extTypeByte code :: bs))
    (h6 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length ≠ 4 → bs.length ≠ 8 →
      bs.length ≠ 16 → bs.length ≤ 255 →
      P ((0xc7 : UInt8) :: writeBE 1 bs.length ++ extTypeByte code :: bs))
    (h7 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length ≠ 4 → bs.length ≠ 8 →
      bs.length ≠ 16 → ¬ bs.length ≤ 255 → bs.length ≤ 65535 →
      P ((0xc8 : UInt8) :: writeBE 2 bs.length ++ extTypeByte code :: bs))
    (h8 : bs.length ≠ 1 → bs.length ≠ 2 → bs.length ≠ 4 → bs.length ≠ 8 →
      bs.length ≠ 16 → ¬ bs.length ≤ 255 → ¬ bs.length ≤ 65535 →
      P ((0xc9 : UInt8) :: writeBE 4 bs.length ++ extTypeByte code :: bs)) :
    P (printExt code bs) := by
  rw [printExt_def]
  by_cases c1 : bs.length = 1
  · rw [if_pos c1]; exact h1 c1
  · rw [if_neg c1]
    by_cases c2 : bs.length = 2
    · rw [if_pos c2]; exact h2 c1 c2
    · rw [if_neg c2]
      by_cases c3 : bs.length = 4
      · rw [if_pos c3]; exact h3 c1 c2 c3
      · rw [if_neg c3]
        by_cases c4 : bs.length = 8
        · rw [if_pos c4]; exact h4 c1 c2 c3 c4
        · rw [if_neg c4]
          by_cases c5 : bs.length = 16
          · rw [if_pos c5]; exact h5 c1 c2 c3 c4 c5
          · rw [if_neg c5]
            by_cases c6 : bs.length ≤ 255
            · rw [if_pos c6]; exact h6 c1 c2 c3 c4 c5 c6
            · rw [if_neg c6]
              by_cases c7 : bs.length ≤ 65535
              · rw [if_pos c7]; exact h7 c1 c2 c3 c4 c5 c6 c7
              · rw [if_neg c7]; exact h8 c1 c2 c3 c4 c5 c6 c7

/-! ## The readers on writings -/

/-- A big endian writing reads back: at every width, the number
    written is the number read, and the bytes after the writing
    are left alone. Induction on the width: the top byte of the
    writing carries the top digit of the number, and the rest of
    the writing is the writing of the remainder. -/
theorem readNat_writeBE : ∀ (k n : Nat) (rest : List UInt8),
    n < 256 ^ k → readNat k (writeBE k n ++ rest) = some (n, rest) := by
  intro k
  induction k with
  | zero =>
    intro n rest hn
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0]
    rfl
  | succ k ih =>
    intro n rest hn
    have hP : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hlt : n / 256 ^ k < 256 := by
      rw [Nat.pow_succ] at hn
      exact Nat.div_lt_of_lt_mul hn
    have hd : ((n / 256 ^ k) % 256).toUInt8.toNat = n / 256 ^ k := by
      have h1 : ((n / 256 ^ k) % 256).toUInt8.toNat = (n / 256 ^ k) % 256 :=
        UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by decide : 0 < 256))
      rw [h1, Nat.mod_eq_of_lt hlt]
    rw [writeBE_succ, List.cons_append, readNat_succ_cons,
      ih (n % 256 ^ k) rest (Nat.mod_lt _ hP), hd]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    · trivial

/-- A byte run reads back whole: taking the front of a list that
    starts with the run gives the run, and leaves the rest. -/
theorem readBytes_append : ∀ (n : Nat) (bs rest : List UInt8),
    bs.length = n → readBytes n (bs ++ rest) = some (bs, rest) := by
  intro n bs rest h
  unfold readBytes
  rw [if_pos (by simp [List.length_append, h] : (bs ++ rest).length ≥ n),
    ← h, List.take_left, List.drop_left]

/-- Casting a power of 256 from the naturals to the integers
    gives the integer power. Stated once, so that arithmetic
    across the two can go through. -/
theorem cast_pow256 (k : Nat) : ((256 ^ k : Nat) : Int) = (256 : Int) ^ k := by
  simp

/-- A signed writing reads back: at every width from one byte
    up, a number in the signed range of the width is the number
    read. The two cases are the sign of the number. A nonnegative
    number's pattern is the number itself, which sits below the
    half modulus, so the reader keeps it. A negative number's
    pattern is the number plus the modulus, which sits at or
    above the half modulus, so the reader takes the modulus back
    off. -/
theorem readSigned_writeBE (k : Nat) (n : Int) (rest : List UInt8)
    (hk : 1 ≤ k) (hn1 : -((256 ^ k / 2 : Nat) : Int) ≤ n)
    (hn2 : n < ((256 ^ k / 2 : Nat) : Int)) :
    readSigned k (writeBE k (signedPattern k n) ++ rest) = some (n, rest) := by
  have hdvd : 2 ∣ 256 ^ k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨256 ^ k' * 128, by rw [Nat.pow_succ']; omega⟩
  have h2T : 256 ^ k / 2 * 2 = 256 ^ k := Nat.div_mul_cancel hdvd
  have hM : ((256 ^ k : Nat) : Int) = (256 : Int) ^ k := cast_pow256 k
  unfold readSigned
  by_cases hn : 0 ≤ n
  · have hsp : signedPattern k n = n.toNat := by
      unfold signedPattern
      rw [if_neg (by omega : ¬ n < 0)]
    have hlt : n.toNat < 256 ^ k := by omega
    have hif : n.toNat < 256 ^ k / 2 := by omega
    rw [hsp, readNat_writeBE k n.toNat rest hlt]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by rw [if_pos hif]; exact Int.toNat_of_nonneg hn, by trivial⟩
  · have hsp : signedPattern k n = (n + 256 ^ k).toNat := by
      unfold signedPattern
      rw [if_pos (by omega : n < 0)]
    have hnn : (0 : Int) ≤ n + 256 ^ k := by omega
    have hcast : ((n + 256 ^ k).toNat : Int) = n + 256 ^ k := Int.toNat_of_nonneg hnn
    have hlt : (n + 256 ^ k).toNat < 256 ^ k := by omega
    have hif : ¬ (n + 256 ^ k).toNat < 256 ^ k / 2 := by omega
    rw [hsp, readNat_writeBE k (n + 256 ^ k).toNat rest hlt]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, by trivial⟩
    rw [if_neg hif, hcast]
    omega

/-- The type byte of an extension value reads back as its code:
    the byte carries the code itself when the code is not
    negative, and the code plus 256 when it is, and the reader's
    rule (the value itself below 128, the value less 256 above)
    undoes both. -/
theorem extTypeByte_code {c : Int} (h1 : -128 ≤ c) (h2 : c ≤ 127) :
    (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
      else ((extTypeByte c).toNat : Int) - 256) = c := by
  have htb : (extTypeByte c).toNat = (if c < 0 then c + 256 else c).toNat := by
    unfold extTypeByte
    apply UInt8.toNat_ofNat_of_lt
    have hsz : UInt8.size = 256 := rfl
    rw [hsz]
    by_cases hc : c < 0
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  by_cases hc : c < 0
  · have h1' : (extTypeByte c).toNat = (c + 256).toNat := by rw [htb, if_pos hc]
    have hge : ¬ (extTypeByte c).toNat < 128 := by rw [h1']; omega
    rw [if_neg hge, h1']
    have hcast : ((c + 256).toNat : Int) = c + 256 :=
      Int.toNat_of_nonneg (by omega)
    omega
  · have h1' : (extTypeByte c).toNat = c.toNat := by rw [htb, if_neg hc]
    have hlt : (extTypeByte c).toNat < 128 := by rw [h1']; omega
    rw [if_pos hlt, h1']
    exact Int.toNat_of_nonneg (by omega)


/-! Part 3: member readers and print length facts. -/

theorem readExtBody_cons (len : Nat) (tb : UInt8) (bs : List UInt8) :
    readExtBody len (tb :: bs) = (readBytes len bs).map fun (chunk, r) =>
      (.ext (if tb.toNat < 128 then (tb.toNat : Int)
        else (tb.toNat : Int) - 256) chunk, r) := by
  rw [readExtBody]

theorem parseMany_of_parse : ∀ (xs : List Value)
    (rec : List UInt8 → Option (Value × List UInt8)),
    (∀ (v : Value), v ∈ xs → ∀ (rest : List UInt8),
      rec (print v ++ rest) = some (v, rest)) →
    ∀ (rest : List UInt8),
      parseMany rec xs.length (printList xs ++ rest) = some (xs, rest) := by
  intro xs rec
  induction xs with
  | nil =>
    intro _ rest
    rfl
  | cons a as ih =>
    intro hrec rest
    have ha : rec (print a ++ (printList as ++ rest)) =
        some (a, printList as ++ rest) :=
      hrec a List.mem_cons_self _
    have ih' := ih (fun v hv rest' => hrec v (List.mem_cons_of_mem a hv) rest') rest
    have hlen : (a :: as).length = as.length + 1 := List.length_cons
    have hpl : printList (a :: as) = print a ++ printList as := by rw [printList]
    rw [hlen, hpl, List.append_assoc]
    simp only [parseMany, ha, ih']

theorem parsePairs_of_parse : ∀ (ps : List (Value × Value))
    (rec : List UInt8 → Option (Value × List UInt8)),
    (∀ (p : Value × Value), p ∈ ps → ∀ (rest : List UInt8),
      rec (print p.1 ++ rest) = some (p.1, rest)) →
    (∀ (p : Value × Value), p ∈ ps → ∀ (rest : List UInt8),
      rec (print p.2 ++ rest) = some (p.2, rest)) →
    ∀ (rest : List UInt8),
      parsePairs rec ps.length (printPairs ps ++ rest) = some (ps, rest) := by
  intro ps rec
  induction ps with
  | nil =>
    intro _ _ rest
    rfl
  | cons p ps ih =>
    intro hk hv rest
    have hk' : rec (print p.1 ++ (print p.2 ++ (printPairs ps ++ rest))) =
        some (p.1, print p.2 ++ (printPairs ps ++ rest)) :=
      hk p List.mem_cons_self _
    have hv' : rec (print p.2 ++ (printPairs ps ++ rest)) =
        some (p.2, printPairs ps ++ rest) :=
      hv p List.mem_cons_self _
    have ih' := ih (fun q hq rest' => hk q (List.mem_cons_of_mem p hq) rest')
      (fun q hq rest' => hv q (List.mem_cons_of_mem p hq) rest') rest
    have hlen : (p :: ps).length = ps.length + 1 := List.length_cons
    have hpp : printPairs (p :: ps) = print p.1 ++ print p.2 ++ printPairs ps := by
      rw [printPairs]
    rw [hlen, hpp, List.append_assoc, List.append_assoc]
    simp only [parsePairs, hk', hv', ih']

theorem strHeader_pos (len : Nat) : 0 < (strHeader len).length :=
  strHeader_elim (P := fun l => 0 < l.length) len (fun _ => by simp only [List.length_cons, List.length_nil]; omega)
    (fun _ _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)

theorem binHeader_pos (len : Nat) : 0 < (binHeader len).length :=
  binHeader_elim (P := fun l => 0 < l.length) len (fun _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ => by simp only [List.length_cons, writeBE_length]; omega)

theorem arrayHeader_pos (len : Nat) : 0 < (arrayHeader len).length :=
  arrayHeader_elim (P := fun l => 0 < l.length) len (fun _ => by simp only [List.length_cons, List.length_nil]; omega)
    (fun _ _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ => by simp only [List.length_cons, writeBE_length]; omega)

theorem mapHeader_pos (len : Nat) : 0 < (mapHeader len).length :=
  mapHeader_elim (P := fun l => 0 < l.length) len (fun _ => by simp only [List.length_cons, List.length_nil]; omega)
    (fun _ _ => by simp only [List.length_cons, writeBE_length]; omega)
    (fun _ => by simp only [List.length_cons, writeBE_length]; omega)

theorem printExt_pos (code : Int) (bs : List UInt8) : 0 < (printExt code bs).length :=
  printExt_elim (P := fun l => 0 < l.length) code bs
    (fun _ => by simp only [List.length_cons]; omega)
    (fun _ => by simp only [List.length_cons]; omega)
    (fun _ => by simp only [List.length_cons]; omega)
    (fun _ => by simp only [List.length_cons]; omega)
    (fun _ => by simp only [List.length_cons]; omega)
    (fun _ _ => by simp only [List.length_cons, List.length_append, writeBE_length]; omega)
    (fun _ _ _ => by simp only [List.length_cons, List.length_append, writeBE_length]; omega)
    (fun _ => by simp only [List.length_cons, List.length_append, writeBE_length]; omega)

theorem print_length_pos (v : Value) : 0 < (print v).length := by
  cases v with
  | nil => rw [print_nil]; simp only [List.length_cons, List.length_nil]; omega
  | bool b =>
    cases b with
    | false => rw [print_bool_false]; simp only [List.length_cons, List.length_nil]; omega
    | true => rw [print_bool_true]; simp only [List.length_cons, List.length_nil]; omega
  | int n =>
    rw [print_int]
    exact printInt_elim (P := fun l => 0 < l.length) n
      (fun _ => by simp only [List.length_cons, List.length_nil]; omega)
      (fun _ _ => by simp only [List.length_cons, List.length_nil]; omega)
      (fun _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
      (fun _ _ _ _ _ _ _ _ _ => by simp only [List.length_cons, writeBE_length]; omega)
  | float32 _ =>
    rw [print_float32]
    simp only [List.length_cons, writeBE_length]; omega
  | float64 _ =>
    rw [print_float64]
    simp only [List.length_cons, writeBE_length]; omega
  | str bs =>
    rw [print_str, List.length_append]
    have h := strHeader_pos bs.length
    omega
  | bin bs =>
    rw [print_bin, List.length_append]
    have h := binHeader_pos bs.length
    omega
  | array vs =>
    rw [print_array, List.length_append]
    have h := arrayHeader_pos vs.length
    omega
  | map ps =>
    rw [print_map, List.length_append]
    have h := mapHeader_pos ps.length
    omega
  | ext c bs =>
    rw [print_ext]
    exact printExt_pos c bs

theorem printList_length_ge : ∀ (xs : List Value) (v : Value), v ∈ xs →
    (print v).length ≤ (printList xs).length := by
  intro xs
  induction xs with
  | nil => intro v hv; cases hv
  | cons a as ih =>
    intro v hv
    have hpl : printList (a :: as) = print a ++ printList as := by rw [printList]
    rw [hpl, List.length_append]
    cases List.mem_cons.mp hv with
    | inl h => subst h; omega
    | inr h => have h2 := ih v h; omega

theorem printPairs_length_ge_fst : ∀ (ps : List (Value × Value)) (p : Value × Value),
    p ∈ ps → (print p.1).length ≤ (printPairs ps).length := by
  intro ps
  induction ps with
  | nil => intro p hp; cases hp
  | cons q qs ih =>
    intro p hp
    have hpp : printPairs (q :: qs) = print q.1 ++ print q.2 ++ printPairs qs := by
      rw [printPairs]
    rw [hpp, List.length_append, List.length_append]
    cases List.mem_cons.mp hp with
    | inl h => subst h; omega
    | inr h => have h2 := ih p h; omega

theorem printPairs_length_ge_snd : ∀ (ps : List (Value × Value)) (p : Value × Value),
    p ∈ ps → (print p.2).length ≤ (printPairs ps).length := by
  intro ps
  induction ps with
  | nil => intro p hp; cases hp
  | cons q qs ih =>
    intro p hp
    have hpp : printPairs (q :: qs) = print q.1 ++ print q.2 ++ printPairs qs := by
      rw [printPairs]
    rw [hpp, List.length_append, List.length_append]
    cases List.mem_cons.mp hp with
    | inl h => subst h; omega
    | inr h => have h2 := ih p h; omega

/-! Part 4: the main round trip. -/

theorem parseGo_print : ∀ (v : Value), WF v → ∀ (fuel : Nat) (rest : List UInt8),
    (print v).length ≤ fuel → parseGo fuel (print v ++ rest) = some (v, rest) := by
  have key : ∀ (n : Nat) (v : Value), size v ≤ n → WF v →
      ∀ (fuel : Nat) (rest : List UInt8),
      (print v).length ≤ fuel → parseGo fuel (print v ++ rest) = some (v, rest) := by
    intro n
    induction n with
    | zero =>
      intro v hv _hWF _fuel _rest _hfuel
      have hpos := size_pos v
      omega
    | succ n ih =>
      intro v hv hWF fuel rest hfuel
      have hlen : 0 < (print v).length := print_length_pos v
      obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
      cases v with
      | nil =>
        rw [print_nil]
        simp only [List.cons_append, List.nil_append, parseGo,
          show classify (0xc0 : UInt8).toNat = some Kind.nil from by decide]
      | bool b =>
        cases b with
        | false =>
          rw [print_bool_false]
          simp only [List.cons_append, List.nil_append, parseGo,
            show classify (0xc2 : UInt8).toNat = some Kind.false_ from by decide]
        | true =>
          rw [print_bool_true]
          simp only [List.cons_append, List.nil_append, parseGo,
            show classify (0xc3 : UInt8).toNat = some Kind.true_ from by decide]
      | int m =>
        cases hWF with
        | int hWFm =>
        rw [print_int]
        refine printInt_elim
          (P := fun l => parseGo (F + 1) (l ++ rest) = some (.int m, rest)) m
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro hc
          have hbt : (m.toNat.toUInt8).toNat = m.toNat :=
            UInt8.toNat_ofNat_of_lt (by omega : m.toNat < 256)
          have hc' : classify (m.toNat.toUInt8).toNat = some .posFixint := by
            rw [hbt]; exact classify_of_lt (by omega)
          simp only [List.cons_append, List.nil_append, parseGo, hc']
          rw [hbt, Int.toNat_of_nonneg (show (0 : Int) ≤ m by omega)]
        · intro _ hc
          have hbt : ((m + 256).toNat.toUInt8).toNat = (m + 256).toNat :=
            UInt8.toNat_ofNat_of_lt (by omega : (m + 256).toNat < 256)
          have hc' : classify ((m + 256).toNat.toUInt8).toNat = some .negFixint := by
            rw [hbt]; exact classify_negFixint (by omega)
          simp only [List.cons_append, List.nil_append, parseGo, hc']
          rw [hbt]
          have hcast : ((m + 256).toNat : Int) = m + 256 :=
            Int.toNat_of_nonneg (by omega)
          rw [hcast]
          simp only [show (m + 256 - 256 : Int) = m by omega]
        · intro _ _ hc
          have hc' : classify (0xcc : UInt8).toNat = some (.uint 1) := by decide
          have hread : readNat 1 (writeBE 1 m.toNat ++ rest) = some (m.toNat, rest) :=
            readNat_writeBE 1 m.toNat rest (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
          exact ⟨by rw [Int.toNat_of_nonneg (show (0 : Int) ≤ m by omega)], by trivial⟩
        · intro _ _ _ hc
          have hc' : classify (0xcd : UInt8).toNat = some (.uint 2) := by decide
          have hread : readNat 2 (writeBE 2 m.toNat ++ rest) = some (m.toNat, rest) :=
            readNat_writeBE 2 m.toNat rest (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
          exact ⟨by rw [Int.toNat_of_nonneg (show (0 : Int) ≤ m by omega)], by trivial⟩
        · intro _ _ _ _ hc
          have hc' : classify (0xce : UInt8).toNat = some (.uint 4) := by decide
          have hread : readNat 4 (writeBE 4 m.toNat ++ rest) = some (m.toNat, rest) :=
            readNat_writeBE 4 m.toNat rest (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
          exact ⟨by rw [Int.toNat_of_nonneg (show (0 : Int) ≤ m by omega)], by trivial⟩
        · intro _ _ _ _ _ hc
          have hc' : classify (0xcf : UInt8).toNat = some (.uint 8) := by decide
          have hread : readNat 8 (writeBE 8 m.toNat ++ rest) = some (m.toNat, rest) :=
            readNat_writeBE 8 m.toNat rest (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
          exact ⟨by rw [Int.toNat_of_nonneg (show (0 : Int) ≤ m by omega)], by trivial⟩
        · intro _ _ _ _ _ _ hc
          have hc' : classify (0xd0 : UInt8).toNat = some (.int 1) := by decide
          have hread : readSigned 1 (writeBE 1 (signedPattern 1 m) ++ rest) =
              some (m, rest) :=
            readSigned_writeBE 1 m rest (by decide) (by omega) (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ _ _ hc
          have hc' : classify (0xd1 : UInt8).toNat = some (.int 2) := by decide
          have hread : readSigned 2 (writeBE 2 (signedPattern 2 m) ++ rest) =
              some (m, rest) :=
            readSigned_writeBE 2 m rest (by decide) (by omega) (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ _ _ _ hc
          have hc' : classify (0xd2 : UInt8).toNat = some (.int 4) := by decide
          have hread : readSigned 4 (writeBE 4 (signedPattern 4 m) ++ rest) =
              some (m, rest) :=
            readSigned_writeBE 4 m rest (by decide) (by omega) (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ _ _ _ _
          have hc' : classify (0xd3 : UInt8).toNat = some (.int 8) := by decide
          have hread : readSigned 8 (writeBE 8 (signedPattern 8 m) ++ rest) =
              some (m, rest) :=
            readSigned_writeBE 8 m rest (by decide) (by omega) (by omega)
          simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
            Option.some.injEq, Prod.mk.injEq]
      | float32 p =>
        cases hWF with
        | float32 hp =>
        rw [print_float32]
        have hc' : classify (0xca : UInt8).toNat = some Kind.float32 := by decide
        have hread : readNat 4 (writeBE 4 p ++ rest) = some (p, rest) :=
          readNat_writeBE 4 p rest (by omega)
        simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
          Option.some.injEq, Prod.mk.injEq]
      | float64 p =>
        cases hWF with
        | float64 hp =>
        rw [print_float64]
        have hc' : classify (0xcb : UInt8).toNat = some Kind.float64 := by decide
        have hread : readNat 8 (writeBE 8 p ++ rest) = some (p, rest) :=
          readNat_writeBE 8 p rest (by omega)
        simp only [List.cons_append, parseGo, hc', hread, Option.map_some,
          Option.some.injEq, Prod.mk.injEq]
      | str bs =>
        cases hWF with
        | str hlen =>
        rw [print_str, List.append_assoc]
        refine strHeader_elim
          (P := fun l => parseGo (F + 1) (l ++ (bs ++ rest)) = some (.str bs, rest))
          bs.length ?_ ?_ ?_ ?_
        · intro hc
          have hbt : ((0xa0 + bs.length).toUInt8).toNat = 0xa0 + bs.length :=
            UInt8.toNat_ofNat_of_lt (by omega : 0xa0 + bs.length < 256)
          have hc' : classify ((0xa0 + bs.length).toUInt8).toNat =
              some (.fixstr bs.length) := by
            rw [hbt]
            have h := classify_fixstr (m := 0xa0 + bs.length) (by omega) (by omega)
            simpa using h
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, List.nil_append, parseGo, hc', hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ hc
          have hc' : classify (0xd9 : UInt8).toNat = some (.str 1) := by decide
          have hn : readNat 1 (writeBE 1 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 1 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ hc
          have hc' : classify (0xda : UInt8).toNat = some (.str 2) := by decide
          have hn : readNat 2 (writeBE 2 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 2 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _
          have hc' : classify (0xdb : UInt8).toNat = some (.str 4) := by decide
          have hn : readNat 4 (writeBE 4 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 4 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
      | bin bs =>
        cases hWF with
        | bin hlen =>
        rw [print_bin, List.append_assoc]
        refine binHeader_elim
          (P := fun l => parseGo (F + 1) (l ++ (bs ++ rest)) = some (.bin bs, rest))
          bs.length ?_ ?_ ?_
        · intro hc
          have hc' : classify (0xc4 : UInt8).toNat = some (.bin 1) := by decide
          have hn : readNat 1 (writeBE 1 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 1 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ hc
          have hc' : classify (0xc5 : UInt8).toNat = some (.bin 2) := by decide
          have hn : readNat 2 (writeBE 2 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 2 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ _
          have hc' : classify (0xc6 : UInt8).toNat = some (.bin 4) := by decide
          have hn : readNat 4 (writeBE 4 bs.length ++ (bs ++ rest)) =
              some (bs.length, bs ++ rest) :=
            readNat_writeBE 4 bs.length (bs ++ rest) (by omega)
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, parseGo, hc', hn, hbytes,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
      | array vs =>
        cases hWF with
        | array hWFv hlen =>
        have hF : ∀ v ∈ vs, (print v).length ≤ F := by
          intro a ha
          have h1 : (print a).length ≤ (printList vs).length :=
            printList_length_ge vs a ha
          have h2 : (print (.array vs)).length =
              (arrayHeader vs.length).length + (printList vs).length := by
            rw [print_array, List.length_append]
          have h3 : 0 < (arrayHeader vs.length).length := arrayHeader_pos vs.length
          omega
        have elem : ∀ v ∈ vs, ∀ (rest' : List UInt8),
            parseGo F (print v ++ rest') = some (v, rest') := by
          intro a ha rest'
          have hb : size a ≤ sizeList vs := sizeList_bound a vs ha
          have hsize : size (.array vs) = 1 + sizeList vs := size_array vs
          exact ih a (by omega) (hWFv a ha) F rest' (hF a ha)
        rw [print_array, List.append_assoc]
        refine arrayHeader_elim
          (P := fun l => parseGo (F + 1) (l ++ (printList vs ++ rest)) =
            some (.array vs, rest))
          vs.length ?_ ?_ ?_
        · intro hc
          have hbt : ((0x90 + vs.length).toUInt8).toNat = 0x90 + vs.length :=
            UInt8.toNat_ofNat_of_lt (by omega : 0x90 + vs.length < 256)
          have hc' : classify ((0x90 + vs.length).toUInt8).toNat =
              some (.fixarray vs.length) := by
            rw [hbt]
            have h := classify_fixarray (m := 0x90 + vs.length) (by omega) (by omega)
            simpa using h
          have hread : parseMany (parseGo F) vs.length (printList vs ++ rest) =
              some (vs, rest) :=
            parseMany_of_parse vs (parseGo F) elem rest
          simp only [List.cons_append, List.nil_append, parseGo, hc', hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ hc
          have hc' : classify (0xdc : UInt8).toNat = some (.array 2) := by decide
          have hn : readNat 2 (writeBE 2 vs.length ++ (printList vs ++ rest)) =
              some (vs.length, printList vs ++ rest) :=
            readNat_writeBE 2 vs.length _ (by omega)
          have hread : parseMany (parseGo F) vs.length (printList vs ++ rest) =
              some (vs, rest) :=
            parseMany_of_parse vs (parseGo F) elem rest
          simp only [List.cons_append, parseGo, hc', hn, hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ _
          have hc' : classify (0xdd : UInt8).toNat = some (.array 4) := by decide
          have hn : readNat 4 (writeBE 4 vs.length ++ (printList vs ++ rest)) =
              some (vs.length, printList vs ++ rest) :=
            readNat_writeBE 4 vs.length _ (by omega)
          have hread : parseMany (parseGo F) vs.length (printList vs ++ rest) =
              some (vs, rest) :=
            parseMany_of_parse vs (parseGo F) elem rest
          simp only [List.cons_append, parseGo, hc', hn, hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
      | map ps =>
        cases hWF with
        | map hk hv hlen =>
        have hF1 : ∀ p ∈ ps, (print p.1).length ≤ F := by
          intro q hq
          have h1 : (print q.1).length ≤ (printPairs ps).length :=
            printPairs_length_ge_fst ps q hq
          have h2 : (print (.map ps)).length =
              (mapHeader ps.length).length + (printPairs ps).length := by
            rw [print_map, List.length_append]
          have h3 : 0 < (mapHeader ps.length).length := mapHeader_pos ps.length
          omega
        have hF2 : ∀ p ∈ ps, (print p.2).length ≤ F := by
          intro q hq
          have h1 : (print q.2).length ≤ (printPairs ps).length :=
            printPairs_length_ge_snd ps q hq
          have h2 : (print (.map ps)).length =
              (mapHeader ps.length).length + (printPairs ps).length := by
            rw [print_map, List.length_append]
          have h3 : 0 < (mapHeader ps.length).length := mapHeader_pos ps.length
          omega
        have elem1 : ∀ p ∈ ps, ∀ (rest' : List UInt8),
            parseGo F (print p.1 ++ rest') = some (p.1, rest') := by
          intro q hq rest'
          obtain ⟨a, b⟩ := q
          have hb : size a ≤ sizePairs ps := sizePairs_bound_fst (a, b) ps hq
          have hsize : size (.map ps) = 1 + sizePairs ps := size_map ps
          exact ih a (by omega) (hk a b hq) F rest' (hF1 (a, b) hq)
        have elem2 : ∀ p ∈ ps, ∀ (rest' : List UInt8),
            parseGo F (print p.2 ++ rest') = some (p.2, rest') := by
          intro q hq rest'
          obtain ⟨a, b⟩ := q
          have hb : size b ≤ sizePairs ps := sizePairs_bound_snd (a, b) ps hq
          have hsize : size (.map ps) = 1 + sizePairs ps := size_map ps
          exact ih b (by omega) (hv a b hq) F rest' (hF2 (a, b) hq)
        rw [print_map, List.append_assoc]
        refine mapHeader_elim
          (P := fun l => parseGo (F + 1) (l ++ (printPairs ps ++ rest)) =
            some (.map ps, rest))
          ps.length ?_ ?_ ?_
        · intro hc
          have hbt : ((0x80 + ps.length).toUInt8).toNat = 0x80 + ps.length :=
            UInt8.toNat_ofNat_of_lt (by omega : 0x80 + ps.length < 256)
          have hc' : classify ((0x80 + ps.length).toUInt8).toNat =
              some (.fixmap ps.length) := by
            rw [hbt]
            have h := classify_fixmap (m := 0x80 + ps.length) (by omega) (by omega)
            simpa using h
          have hread : parsePairs (parseGo F) ps.length (printPairs ps ++ rest) =
              some (ps, rest) :=
            parsePairs_of_parse ps (parseGo F) elem1 elem2 rest
          simp only [List.cons_append, List.nil_append, parseGo, hc', hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ hc
          have hc' : classify (0xde : UInt8).toNat = some (.map 2) := by decide
          have hn : readNat 2 (writeBE 2 ps.length ++ (printPairs ps ++ rest)) =
              some (ps.length, printPairs ps ++ rest) :=
            readNat_writeBE 2 ps.length _ (by omega)
          have hread : parsePairs (parseGo F) ps.length (printPairs ps ++ rest) =
              some (ps, rest) :=
            parsePairs_of_parse ps (parseGo F) elem1 elem2 rest
          simp only [List.cons_append, parseGo, hc', hn, hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · intro _ _
          have hc' : classify (0xdf : UInt8).toNat = some (.map 4) := by decide
          have hn : readNat 4 (writeBE 4 ps.length ++ (printPairs ps ++ rest)) =
              some (ps.length, printPairs ps ++ rest) :=
            readNat_writeBE 4 ps.length _ (by omega)
          have hread : parsePairs (parseGo F) ps.length (printPairs ps ++ rest) =
              some (ps, rest) :=
            parsePairs_of_parse ps (parseGo F) elem1 elem2 rest
          simp only [List.cons_append, parseGo, hc', hn, hread,
            Option.map_some, Option.some.injEq, Prod.mk.injEq]
      | ext c bs =>
        cases hWF with
        | ext hc hlen =>
        rw [print_ext]
        refine printExt_elim
          (P := fun l => parseGo (F + 1) (l ++ rest) = some (.ext c bs, rest))
          c bs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro h1
          have hc' : classify (0xd4 : UInt8).toNat = some (.fixext 1) := by decide
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes 1 (bs ++ rest) = some (bs, rest) :=
            readBytes_append 1 bs rest h1
          simp only [List.cons_append, parseGo, hc', readExtBody_cons, hbytes,
            Option.map_some, hcode, Option.some.injEq, Prod.mk.injEq]
        · intro _ h2
          have hc' : classify (0xd5 : UInt8).toNat = some (.fixext 2) := by decide
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes 2 (bs ++ rest) = some (bs, rest) :=
            readBytes_append 2 bs rest h2
          simp only [List.cons_append, parseGo, hc', readExtBody_cons, hbytes,
            Option.map_some, hcode, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ h4
          have hc' : classify (0xd6 : UInt8).toNat = some (.fixext 4) := by decide
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes 4 (bs ++ rest) = some (bs, rest) :=
            readBytes_append 4 bs rest h4
          simp only [List.cons_append, parseGo, hc', readExtBody_cons, hbytes,
            Option.map_some, hcode, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ h8
          have hc' : classify (0xd7 : UInt8).toNat = some (.fixext 8) := by decide
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes 8 (bs ++ rest) = some (bs, rest) :=
            readBytes_append 8 bs rest h8
          simp only [List.cons_append, parseGo, hc', readExtBody_cons, hbytes,
            Option.map_some, hcode, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ h16
          have hc' : classify (0xd8 : UInt8).toNat = some (.fixext 16) := by decide
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes 16 (bs ++ rest) = some (bs, rest) :=
            readBytes_append 16 bs rest h16
          simp only [List.cons_append, parseGo, hc', readExtBody_cons, hbytes,
            Option.map_some, hcode, Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ hle
          have hc' : classify (0xc7 : UInt8).toNat = some (.ext 1) := by decide
          have hn : readNat 1 (writeBE 1 bs.length ++ (extTypeByte c :: (bs ++ rest))) =
              some (bs.length, extTypeByte c :: (bs ++ rest)) :=
            readNat_writeBE 1 bs.length _ (by omega)
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, List.append_assoc, parseGo, hc', hn,
            readExtBody_cons, hbytes, Option.map_some, hcode,
            Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ _ hle
          have hc' : classify (0xc8 : UInt8).toNat = some (.ext 2) := by decide
          have hn : readNat 2 (writeBE 2 bs.length ++ (extTypeByte c :: (bs ++ rest))) =
              some (bs.length, extTypeByte c :: (bs ++ rest)) :=
            readNat_writeBE 2 bs.length _ (by omega)
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, List.append_assoc, parseGo, hc', hn,
            readExtBody_cons, hbytes, Option.map_some, hcode,
            Option.some.injEq, Prod.mk.injEq]
        · intro _ _ _ _ _ _ _
          have hc' : classify (0xc9 : UInt8).toNat = some (.ext 4) := by decide
          have hn : readNat 4 (writeBE 4 bs.length ++ (extTypeByte c :: (bs ++ rest))) =
              some (bs.length, extTypeByte c :: (bs ++ rest)) :=
            readNat_writeBE 4 bs.length _ (by omega)
          have hcode : (if (extTypeByte c).toNat < 128 then ((extTypeByte c).toNat : Int)
              else ((extTypeByte c).toNat : Int) - 256) = c :=
            extTypeByte_code hc.1 hc.2
          have hbytes : readBytes bs.length (bs ++ rest) = some (bs, rest) :=
            readBytes_append bs.length bs rest rfl
          simp only [List.cons_append, List.append_assoc, parseGo, hc', hn,
            readExtBody_cons, hbytes, Option.map_some, hcode,
            Option.some.injEq, Prod.mk.injEq]
  intro v hWF fuel rest hfuel
  exact key (size v) v (by omega) hWF fuel rest hfuel

theorem parse_print {v : Value} (h : WF v) : parse (print v) = some v := by
  have hgo := parseGo_print v h (print v).length [] (by omega)
  rw [List.append_nil] at hgo
  unfold parse
  simp only [hgo]

end MessagePack.Proofs

