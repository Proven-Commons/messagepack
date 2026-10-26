/-
  MessagePack values and the canonical printer.

  A value is one of the families the MessagePack specification
  names: nil, a boolean, an integer, a float held as its raw bit
  pattern, a string held as bytes, a binary blob held as bytes, an
  array of values, a map of value pairs, and an extension value
  (a small signed type code and a run of bytes).

  A string's bytes are held as they stand. Whether they are valid
  UTF-8 is not checked in this slice; the utf repo owns that
  question. An extension value's bytes are likewise opaque: the
  registered extension types, timestamps among them, get no
  reading of their insides here.

  The printer writes the canonical form the specification's
  ecosystem uses: the smallest encoding for each integer, and the
  smallest length form for strings, blobs, arrays, and maps.
  Floats print with their own width's marker and their pattern in
  big endian order.
-/

namespace MessagePack

/-- A MessagePack value. A `float32` holds a 32 bit pattern and a
    `float64` a 64 bit pattern, each as a plain number; the well
    formedness rules below bound them. An `ext` holds its type
    code as a signed number and its payload as bytes. -/
inductive Value where
  | nil : Value
  | bool : Bool → Value
  | int : Int → Value
  | float32 : Nat → Value
  | float64 : Nat → Value
  | str : List UInt8 → Value
  | bin : List UInt8 → Value
  | array : List Value → Value
  | map : List (Value × Value) → Value
  | ext : Int → List UInt8 → Value
  deriving Repr

/-! ## Decidable equality

  The deriving handler does not cover a value type that recurses
  through lists, so equality is built by hand: a boolean test,
  a proof that the test agrees with equality, and the instance
  the test gives. -/

mutual

/-- The boolean equality test on values. -/
def beq : Value → Value → Bool
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .float32 a, .float32 b => a == b
  | .float64 a, .float64 b => a == b
  | .str a, .str b => a == b
  | .bin a, .bin b => a == b
  | .array a, .array b => beqList a b
  | .map a, .map b => beqPairs a b
  | .ext c₁ a, .ext c₂ b => (c₁ == c₂) && (a == b)
  | _, _ => false

/-- The boolean equality test on value lists. -/
def beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

/-- The boolean equality test on pair lists. -/
def beqPairs : List (Value × Value) → List (Value × Value) → Bool
  | [], [] => true
  | p :: ps, q :: qs => beq p.1 q.1 && beq p.2 q.2 && beqPairs ps qs
  | _, _ => false

end

/-! ## Size

  A size for values, used to run inductions over the nesting:
  the `induction` tactic does not support this nested type, so
  the proofs induct on a bound for the size instead. A member of
  a container is always smaller than the container. -/

mutual

/-- The size of a value: one for a leaf, one plus the members'
    sizes for a container. -/
def size : Value → Nat
  | .nil => 1
  | .bool _ => 1
  | .int _ => 1
  | .float32 _ => 1
  | .float64 _ => 1
  | .str _ => 1
  | .bin _ => 1
  | .array vs => 1 + sizeList vs
  | .map ps => 1 + sizePairs ps
  | .ext _ _ => 1

/-- The size of a value list: the sum of the members' sizes. -/
def sizeList : List Value → Nat
  | [] => 0
  | v :: vs => size v + sizeList vs

/-- The size of a pair list: the sum of the pairs' sizes. -/
def sizePairs : List (Value × Value) → Nat
  | [] => 0
  | p :: ps => size p.1 + size p.2 + sizePairs ps

end

/-- The size of an array value unfolds to one plus the list
    size. -/
theorem size_array (vs : List Value) : size (.array vs) = 1 + sizeList vs := by
  rw [size]

/-- The size of a map value unfolds to one plus the pair list
    size. -/
theorem size_map (ps : List (Value × Value)) : size (.map ps) = 1 + sizePairs ps := by
  rw [size]

/-- The size of a nonempty value list unfolds to the head size
    plus the tail size. -/
theorem sizeList_cons (v : Value) (vs : List Value) :
    sizeList (v :: vs) = size v + sizeList vs := by
  rw [sizeList]

/-- The size of a nonempty pair list unfolds to the head pair's
    size plus the tail size. -/
theorem sizePairs_cons (p : Value × Value) (ps : List (Value × Value)) :
    sizePairs (p :: ps) = size p.1 + size p.2 + sizePairs ps := by
  rw [sizePairs]

/-- Every value has positive size. -/
theorem size_pos : ∀ (v : Value), 0 < size v := by
  intro v
  cases v with
  | array vs => rw [size_array]; omega
  | map ps => rw [size_map]; omega
  | nil => rw [size]; exact Nat.one_pos
  | bool _ => rw [size]; exact Nat.one_pos
  | int _ => rw [size]; exact Nat.one_pos
  | float32 _ => rw [size]; exact Nat.one_pos
  | float64 _ => rw [size]; exact Nat.one_pos
  | str _ => rw [size]; exact Nat.one_pos
  | bin _ => rw [size]; exact Nat.one_pos
  | ext _ _ => rw [size]; exact Nat.one_pos

/-- A member's size is at most its list's size. -/
theorem sizeList_bound : ∀ (a : Value) (vs : List Value), a ∈ vs → size a ≤ sizeList vs := by
  intro a vs
  induction vs with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    rw [sizeList_cons]
    cases List.mem_cons.mp h with
    | inl h' => subst h'; omega
    | inr h' => have := ih h'; omega

/-- A member pair's key size is at most its list's size. -/
theorem sizePairs_bound_fst : ∀ (p : Value × Value) (ps : List (Value × Value)),
    p ∈ ps → size p.1 ≤ sizePairs ps := by
  intro p ps
  induction ps with
  | nil => intro h; cases h
  | cons q qs ih =>
    intro h
    rw [sizePairs_cons]
    cases List.mem_cons.mp h with
    | inl h' => subst h'; omega
    | inr h' => have := ih h'; omega

/-- A member pair's value size is at most its list's size. -/
theorem sizePairs_bound_snd : ∀ (p : Value × Value) (ps : List (Value × Value)),
    p ∈ ps → size p.2 ≤ sizePairs ps := by
  intro p ps
  induction ps with
  | nil => intro h; cases h
  | cons q qs ih =>
    intro h
    rw [sizePairs_cons]
    cases List.mem_cons.mp h with
    | inl h' => subst h'; omega
    | inr h' => have := ih h'; omega

/-- The boolean test agrees with equality, in both directions.
    The induction runs on a bound for the size of the first
    value, since the type is nested. -/
theorem beq_iff : ∀ (v w : Value), beq v w = true ↔ v = w := by
  have key : ∀ (n : Nat) (v : Value), size v ≤ n → ∀ (w : Value),
      beq v w = true ↔ v = w := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hpos := size_pos v
      omega
    | succ n ih =>
      intro v hv w
      cases v with
      | nil => cases w <;> simp [beq]
      | bool b => cases w <;> simp [beq, beq_iff_eq]
      | int m => cases w <;> simp [beq, beq_iff_eq]
      | float32 p => cases w <;> simp [beq, beq_iff_eq]
      | float64 p => cases w <;> simp [beq, beq_iff_eq]
      | str bs => cases w <;> simp [beq, beq_iff_eq]
      | bin bs => cases w <;> simp [beq, beq_iff_eq]
      | ext c bs => cases w <;> simp [beq, beq_iff_eq]
      | array vs =>
        have elem : ∀ (a : Value), a ∈ vs → ∀ (u : Value),
            beq a u = true ↔ a = u := by
          intro a ha u
          apply ih a _ u
          have h1 : size a ≤ sizeList vs := sizeList_bound a vs ha
          rw [size_array] at hv
          omega
        have list_aux : ∀ (xs : List Value),
            (∀ (a : Value), a ∈ xs → ∀ (u : Value), beq a u = true ↔ a = u) →
            ∀ (ys : List Value), beqList xs ys = true ↔ xs = ys := by
          intro xs
          induction xs with
          | nil => intro _ ys; cases ys <;> simp [beqList]
          | cons a as ihl =>
            intro hxs ys
            cases ys with
            | nil => simp [beqList]
            | cons b bs =>
              have ea := hxs a (by simp)
              have ihl' := ihl (fun a' ha' =>
                hxs a' (by simp_all))
              constructor
              · intro h
                simp only [beqList, Bool.and_eq_true] at h
                obtain ⟨h1, h2⟩ := h
                have ha : a = b := (ea b).mp h1
                have hs : as = bs := (ihl' bs).mp h2
                rw [ha, hs]
              · intro h
                cases h
                simp only [beqList, Bool.and_eq_true]
                exact ⟨(ea a).mpr rfl, (ihl' as).mpr rfl⟩
        cases w with
        | array ws => simp [beq, list_aux vs elem ws]
        | _ => simp [beq]
      | map ps =>
        have elem1 : ∀ (p : Value × Value), p ∈ ps → ∀ (u : Value),
            beq p.1 u = true ↔ p.1 = u := by
          intro p hp u
          apply ih p.1 _ u
          have h1 : size p.1 ≤ sizePairs ps := sizePairs_bound_fst p ps hp
          rw [size_map] at hv
          omega
        have elem2 : ∀ (p : Value × Value), p ∈ ps → ∀ (u : Value),
            beq p.2 u = true ↔ p.2 = u := by
          intro p hp u
          apply ih p.2 _ u
          have h1 : size p.2 ≤ sizePairs ps := sizePairs_bound_snd p ps hp
          rw [size_map] at hv
          omega
        have pairs_aux : ∀ (xs : List (Value × Value)),
            (∀ (p : Value × Value), p ∈ xs → ∀ (u : Value),
              beq p.1 u = true ↔ p.1 = u) →
            (∀ (p : Value × Value), p ∈ xs → ∀ (u : Value),
              beq p.2 u = true ↔ p.2 = u) →
            ∀ (ys : List (Value × Value)), beqPairs xs ys = true ↔ xs = ys := by
          intro xs
          induction xs with
          | nil => intro _ _ ys; cases ys <;> simp [beqPairs]
          | cons p ps' ihl =>
            intro h1 h2 ys
            cases ys with
            | nil => simp [beqPairs]
            | cons q qs =>
              obtain ⟨a1, a2⟩ := p
              obtain ⟨b1, b2⟩ := q
              have e1 := h1 (a1, a2) (by simp)
              have e2 := h2 (a1, a2) (by simp)
              have ihl' := ihl
                (fun p' hp' => h1 p' (by simp_all))
                (fun p' hp' => h2 p' (by simp_all))
              constructor
              · intro h
                simp only [beqPairs, Bool.and_eq_true] at h
                obtain ⟨⟨h1', h2'⟩, h3⟩ := h
                have hk : a1 = b1 := (e1 b1).mp h1'
                have hv2 : a2 = b2 := (e2 b2).mp h2'
                have hs : ps' = qs := (ihl' qs).mp h3
                rw [hk, hv2, hs]
              · intro h
                cases h
                simp only [beqPairs, Bool.and_eq_true]
                exact ⟨⟨(e1 a1).mpr rfl, (e2 a2).mpr rfl⟩, (ihl' ps').mpr rfl⟩
        cases w with
        | map ws => simp [beq, pairs_aux ps elem1 elem2 ws]
        | _ => simp [beq]
  exact fun v w => key (size v) v Nat.le.refl w

/-- Equality of values is decidable, by the boolean test. -/
instance : DecidableEq Value :=
  fun a b =>
    if h : beq a b = true then isTrue ((beq_iff a b).mp h)
    else isFalse (fun he => h ((beq_iff a b).mpr he))

/-! ## Big endian byte strings -/

/-- Write a number in exactly `k` bytes, most significant byte
    first. Bytes past the number's own width are zero, and a
    number too wide for `k` bytes loses its top bytes: the
    printer only calls this with a width the number fits. -/
def writeBE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k)

/-- The unfolding rule for `writeBE` at a successor width. -/
theorem writeBE_succ (k n : Nat) :
    writeBE (k + 1) n = ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k) := by
  rw [writeBE]

/-- A big endian writing is exactly as long as its width. -/
theorem writeBE_length : ∀ (k n : Nat), (writeBE k n).length = k
  | 0, _ => rfl
  | k + 1, n => by rw [writeBE_succ]; simp [writeBE_length k]

/-! ## Integers -/

/-- The byte pattern of a signed integer in `k` bytes: the number
    itself when it is not negative, and the number plus the
    modulus when it is. In the branches that use it the number is
    always in the signed range of the width, so the pattern fits
    in `k` bytes. -/
def signedPattern (k : Nat) (n : Int) : Nat :=
  if n < 0 then (n + 256 ^ k).toNat else n.toNat

/-- Print an integer in its smallest form. Nonnegative numbers
    climb the unsigned widths and never print in a signed form;
    negative numbers take the negative fixint form when they fit
    and climb the signed widths otherwise. -/
def printInt (n : Int) : List UInt8 :=
  if 0 ≤ n ∧ n ≤ 127 then [n.toNat.toUInt8]
  else if -32 ≤ n ∧ n ≤ -1 then [(n + 256).toNat.toUInt8]
  else if 0 ≤ n ∧ n ≤ 255 then (0xcc : UInt8) :: writeBE 1 n.toNat
  else if 0 ≤ n ∧ n ≤ 65535 then (0xcd : UInt8) :: writeBE 2 n.toNat
  else if 0 ≤ n ∧ n ≤ 4294967295 then (0xce : UInt8) :: writeBE 4 n.toNat
  else if 0 ≤ n ∧ n ≤ 18446744073709551615 then (0xcf : UInt8) :: writeBE 8 n.toNat
  else if -128 ≤ n then (0xd0 : UInt8) :: writeBE 1 (signedPattern 1 n)
  else if -32768 ≤ n then (0xd1 : UInt8) :: writeBE 2 (signedPattern 2 n)
  else if -2147483648 ≤ n then (0xd2 : UInt8) :: writeBE 4 (signedPattern 4 n)
  else (0xd3 : UInt8) :: writeBE 8 (signedPattern 8 n)

/-- The unfolding rule for `printInt`. -/
theorem printInt_def (n : Int) :
    printInt n =
      if 0 ≤ n ∧ n ≤ 127 then [n.toNat.toUInt8]
      else if -32 ≤ n ∧ n ≤ -1 then [(n + 256).toNat.toUInt8]
      else if 0 ≤ n ∧ n ≤ 255 then (0xcc : UInt8) :: writeBE 1 n.toNat
      else if 0 ≤ n ∧ n ≤ 65535 then (0xcd : UInt8) :: writeBE 2 n.toNat
      else if 0 ≤ n ∧ n ≤ 4294967295 then (0xce : UInt8) :: writeBE 4 n.toNat
      else if 0 ≤ n ∧ n ≤ 18446744073709551615 then (0xcf : UInt8) :: writeBE 8 n.toNat
      else if -128 ≤ n then (0xd0 : UInt8) :: writeBE 1 (signedPattern 1 n)
      else if -32768 ≤ n then (0xd1 : UInt8) :: writeBE 2 (signedPattern 2 n)
      else if -2147483648 ≤ n then (0xd2 : UInt8) :: writeBE 4 (signedPattern 4 n)
      else (0xd3 : UInt8) :: writeBE 8 (signedPattern 8 n) := by
  rw [printInt]

/-! ## Length headers -/

/-- The header of a string of the given length: the fixstr form
    below 32, then the 8, 16, and 32 bit length forms. -/
def strHeader (len : Nat) : List UInt8 :=
  if len < 32 then [(0xa0 + len).toUInt8]
  else if len ≤ 255 then (0xd9 : UInt8) :: writeBE 1 len
  else if len ≤ 65535 then (0xda : UInt8) :: writeBE 2 len
  else (0xdb : UInt8) :: writeBE 4 len

/-- The header of a binary blob of the given length: the 8, 16,
    and 32 bit length forms. There is no fix form for blobs. -/
def binHeader (len : Nat) : List UInt8 :=
  if len ≤ 255 then (0xc4 : UInt8) :: writeBE 1 len
  else if len ≤ 65535 then (0xc5 : UInt8) :: writeBE 2 len
  else (0xc6 : UInt8) :: writeBE 4 len

/-- The header of an array of the given count: the fixarray form
    below 16, then the 16 and 32 bit count forms. -/
def arrayHeader (len : Nat) : List UInt8 :=
  if len < 16 then [(0x90 + len).toUInt8]
  else if len ≤ 65535 then (0xdc : UInt8) :: writeBE 2 len
  else (0xdd : UInt8) :: writeBE 4 len

/-- The header of a map of the given count: the fixmap form below
    16, then the 16 and 32 bit count forms. -/
def mapHeader (len : Nat) : List UInt8 :=
  if len < 16 then [(0x80 + len).toUInt8]
  else if len ≤ 65535 then (0xde : UInt8) :: writeBE 2 len
  else (0xdf : UInt8) :: writeBE 4 len

/-- The type byte of an extension value: the code itself when it
    is not negative, the code plus 256 when it is. -/
def extTypeByte (code : Int) : UInt8 :=
  (if code < 0 then code + 256 else code).toNat.toUInt8

/-- Print an extension value: a fixext form when the payload
    length is 1, 2, 4, 8, or 16, and the smallest of the 8, 16,
    and 32 bit length forms otherwise. The type byte follows the
    marker (and the length, in the length forms). -/
def printExt (code : Int) (bs : List UInt8) : List UInt8 :=
  let tb := extTypeByte code
  if bs.length = 1 then (0xd4 : UInt8) :: tb :: bs
  else if bs.length = 2 then (0xd5 : UInt8) :: tb :: bs
  else if bs.length = 4 then (0xd6 : UInt8) :: tb :: bs
  else if bs.length = 8 then (0xd7 : UInt8) :: tb :: bs
  else if bs.length = 16 then (0xd8 : UInt8) :: tb :: bs
  else if bs.length ≤ 255 then (0xc7 : UInt8) :: writeBE 1 bs.length ++ tb :: bs
  else if bs.length ≤ 65535 then (0xc8 : UInt8) :: writeBE 2 bs.length ++ tb :: bs
  else (0xc9 : UInt8) :: writeBE 4 bs.length ++ tb :: bs

/-- The unfolding rule for `printExt`. -/
theorem printExt_def (code : Int) (bs : List UInt8) :
    printExt code bs =
      if bs.length = 1 then (0xd4 : UInt8) :: extTypeByte code :: bs
      else if bs.length = 2 then (0xd5 : UInt8) :: extTypeByte code :: bs
      else if bs.length = 4 then (0xd6 : UInt8) :: extTypeByte code :: bs
      else if bs.length = 8 then (0xd7 : UInt8) :: extTypeByte code :: bs
      else if bs.length = 16 then (0xd8 : UInt8) :: extTypeByte code :: bs
      else if bs.length ≤ 255 then (0xc7 : UInt8) :: writeBE 1 bs.length ++ extTypeByte code :: bs
      else if bs.length ≤ 65535 then (0xc8 : UInt8) :: writeBE 2 bs.length ++ extTypeByte code :: bs
      else (0xc9 : UInt8) :: writeBE 4 bs.length ++ extTypeByte code :: bs := by
  rw [printExt]

/-! ## The printer -/

mutual

/-- Print a value in its canonical form. -/
def print : Value → List UInt8
  | .nil => [0xc0]
  | .bool false => [0xc2]
  | .bool true => [0xc3]
  | .int n => printInt n
  | .float32 p => (0xca : UInt8) :: writeBE 4 p
  | .float64 p => (0xcb : UInt8) :: writeBE 8 p
  | .str bs => strHeader bs.length ++ bs
  | .bin bs => binHeader bs.length ++ bs
  | .array vs => arrayHeader vs.length ++ printList vs
  | .map ps => mapHeader ps.length ++ printPairs ps
  | .ext c bs => printExt c bs

/-- Print a list of values, one after the other. -/
def printList : List Value → List UInt8
  | [] => []
  | v :: vs => print v ++ printList vs

/-- Print a list of key and value pairs, one after the other. -/
def printPairs : List (Value × Value) → List UInt8
  | [] => []
  | p :: ps => print p.1 ++ print p.2 ++ printPairs ps

end

/-- The list printer is the flat map of the printer. -/
theorem printList_eq : ∀ (vs : List Value), printList vs = vs.flatMap print
  | [] => rfl
  | v :: vs => by rw [printList, List.flatMap_cons, printList_eq vs]

/-- The pair list printer is the flat map of the pair printer. -/
theorem printPairs_eq :
    ∀ (ps : List (Value × Value)),
      printPairs ps = ps.flatMap (fun p => print p.1 ++ print p.2)
  | [] => rfl
  | p :: ps => by rw [printPairs, List.flatMap_cons, printPairs_eq ps]

/-- The unfolding rule for `print` on nil. -/
theorem print_nil : print .nil = [(0xc0 : UInt8)] := by rw [print]

/-- The unfolding rule for `print` on false. -/
theorem print_bool_false : print (.bool false) = [(0xc2 : UInt8)] := by rw [print]

/-- The unfolding rule for `print` on true. -/
theorem print_bool_true : print (.bool true) = [(0xc3 : UInt8)] := by rw [print]

/-- The unfolding rule for `print` on an integer. -/
theorem print_int (n : Int) : print (.int n) = printInt n := by rw [print]

/-- The unfolding rule for `print` on a 32 bit float. -/
theorem print_float32 (p : Nat) : print (.float32 p) = (0xca : UInt8) :: writeBE 4 p := by
  rw [print]

/-- The unfolding rule for `print` on a 64 bit float. -/
theorem print_float64 (p : Nat) : print (.float64 p) = (0xcb : UInt8) :: writeBE 8 p := by
  rw [print]

/-- The unfolding rule for `print` on a string. -/
theorem print_str (bs : List UInt8) : print (.str bs) = strHeader bs.length ++ bs := by
  rw [print]

/-- The unfolding rule for `print` on a binary blob. -/
theorem print_bin (bs : List UInt8) : print (.bin bs) = binHeader bs.length ++ bs := by
  rw [print]

/-- The unfolding rule for `print` on an array. -/
theorem print_array (vs : List Value) :
    print (.array vs) = arrayHeader vs.length ++ printList vs := by
  rw [print]

/-- The unfolding rule for `print` on a map. -/
theorem print_map (ps : List (Value × Value)) :
    print (.map ps) = mapHeader ps.length ++ printPairs ps := by
  rw [print]

/-- The unfolding rule for `print` on an extension value. -/
theorem print_ext (c : Int) (bs : List UInt8) : print (.ext c bs) = printExt c bs := by
  rw [print]

/-! ## Well formed values

  The round trip claims in `Proofs` hold for well formed values.
  An integer sits in the range the format's integer families
  cover together, from -2^63 to 2^64 - 1. A float pattern fits
  its width. An extension type code sits in its signed byte
  range. A length (a string, blob, payload, or count) fits in
  32 bits: any list a program can hold does in practice, but the
  proof needs the bound stated, since the widest length form
  carries 32 bits. -/

/-- A value in the shape the printer and the round trip proofs
    rely on. -/
inductive WF : Value → Prop where
  | nil : WF .nil
  | bool (b : Bool) : WF (.bool b)
  | int {n : Int} (h : -9223372036854775808 ≤ n ∧ n ≤ 18446744073709551615) : WF (.int n)
  | float32 {p : Nat} (h : p < 4294967296) : WF (.float32 p)
  | float64 {p : Nat} (h : p < 18446744073709551616) : WF (.float64 p)
  | str {bs : List UInt8} (h : bs.length < 4294967296) : WF (.str bs)
  | bin {bs : List UInt8} (h : bs.length < 4294967296) : WF (.bin bs)
  | array {vs : List Value} (h : ∀ v ∈ vs, WF v) (hl : vs.length < 4294967296) :
      WF (.array vs)
  | map {ps : List (Value × Value)} (hk : ∀ a b : Value, (a, b) ∈ ps → WF a)
      (hv : ∀ a b : Value, (a, b) ∈ ps → WF b) (hl : ps.length < 4294967296) :
      WF (.map ps)
  | ext {c : Int} {bs : List UInt8} (hc : -128 ≤ c ∧ c ≤ 127) (h : bs.length < 4294967296) :
      WF (.ext c bs)

end MessagePack
