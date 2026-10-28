/-
  The MessagePack parser: marker classification, big endian
  readers, and the value reader itself.

  The parser reads every form the format allows, not only the
  smallest: an integer carried in the 64 bit form reads the same
  as the same integer in its fix form, and a string carried in
  the 16 bit length form reads the same as in its fix form. The
  value is what is read, not the width it arrived in.

  Rules the parser follows:

  - The byte 0xc1 is never used by the format. It is rejected
    wherever a value is read.
  - A value cut short at any point is rejected: a number or a
    length that runs past the input, a payload shorter than its
    length, an array or map whose members run out.
  - The reader for a whole input asks for exactly one value with
    nothing after it. Trailing bytes are rejected there (the
    inner reader returns them, and the whole input reader turns
    them away).
  - Nested values recurse with a fuel count bounded by the input
    length. Each nesting level eats at least its marker byte, so
    the input length is always fuel enough, and a hostile nesting
    cannot loop.
-/

import MessagePack.Value

namespace MessagePack

/-! ## Marker classification -/

/-- The form a marker byte names. The number a form carries is a
    count (for the fix forms) or a width in bytes (for the length
    and number forms). The `fixext` number is a payload length. -/
inductive Kind where
  | posFixint : Kind
  | negFixint : Kind
  | fixmap (n : Nat) : Kind
  | fixarray (n : Nat) : Kind
  | fixstr (n : Nat) : Kind
  | nil : Kind
  | false_ : Kind
  | true_ : Kind
  | bin (w : Nat) : Kind
  | ext (w : Nat) : Kind
  | fixext (n : Nat) : Kind
  | float32 : Kind
  | float64 : Kind
  | uint (w : Nat) : Kind
  | int (w : Nat) : Kind
  | str (w : Nat) : Kind
  | array (w : Nat) : Kind
  | map (w : Nat) : Kind
  deriving DecidableEq, Repr

/-- Read a marker byte's number as the form it names, following
    the specification's layout table. The byte 0xc1 names
    nothing. The last test catches the negative fixint range; a
    marker number always comes from a byte, so it is at most 255. -/
def classify (m : Nat) : Option Kind :=
  if m < 0x80 then some .posFixint
  else if m < 0x90 then some (.fixmap (m - 0x80))
  else if m < 0xa0 then some (.fixarray (m - 0x90))
  else if m < 0xc0 then some (.fixstr (m - 0xa0))
  else if m = 0xc0 then some .nil
  else if m = 0xc1 then none
  else if m = 0xc2 then some .false_
  else if m = 0xc3 then some .true_
  else if m = 0xc4 then some (.bin 1)
  else if m = 0xc5 then some (.bin 2)
  else if m = 0xc6 then some (.bin 4)
  else if m = 0xc7 then some (.ext 1)
  else if m = 0xc8 then some (.ext 2)
  else if m = 0xc9 then some (.ext 4)
  else if m = 0xca then some .float32
  else if m = 0xcb then some .float64
  else if m = 0xcc then some (.uint 1)
  else if m = 0xcd then some (.uint 2)
  else if m = 0xce then some (.uint 4)
  else if m = 0xcf then some (.uint 8)
  else if m = 0xd0 then some (.int 1)
  else if m = 0xd1 then some (.int 2)
  else if m = 0xd2 then some (.int 4)
  else if m = 0xd3 then some (.int 8)
  else if m = 0xd4 then some (.fixext 1)
  else if m = 0xd5 then some (.fixext 2)
  else if m = 0xd6 then some (.fixext 4)
  else if m = 0xd7 then some (.fixext 8)
  else if m = 0xd8 then some (.fixext 16)
  else if m = 0xd9 then some (.str 1)
  else if m = 0xda then some (.str 2)
  else if m = 0xdb then some (.str 4)
  else if m = 0xdc then some (.array 2)
  else if m = 0xdd then some (.array 4)
  else if m = 0xde then some (.map 2)
  else if m = 0xdf then some (.map 4)
  else if 0xe0 ≤ m then some .negFixint
  else none

/-- A marker number below 0x80 is a positive fixint. -/
theorem classify_of_lt {m : Nat} (h : m < 0x80) : classify m = some .posFixint := by
  unfold classify
  rw [if_pos h]

/-- A marker number in the fixmap range names a fixmap of the
    count it carries. -/
theorem classify_fixmap {m : Nat} (h1 : 0x80 ≤ m) (h2 : m < 0x90) :
    classify m = some (.fixmap (m - 0x80)) := by
  unfold classify
  rw [if_neg (by omega : ¬ m < 0x80), if_pos h2]

/-- A marker number in the fixarray range names a fixarray of
    the count it carries. -/
theorem classify_fixarray {m : Nat} (h1 : 0x90 ≤ m) (h2 : m < 0xa0) :
    classify m = some (.fixarray (m - 0x90)) := by
  unfold classify
  rw [if_neg (by omega : ¬ m < 0x80), if_neg (by omega : ¬ m < 0x90), if_pos h2]

/-- A marker number in the fixstr range names a fixstr of the
    length it carries. -/
theorem classify_fixstr {m : Nat} (h1 : 0xa0 ≤ m) (h2 : m < 0xc0) :
    classify m = some (.fixstr (m - 0xa0)) := by
  unfold classify
  rw [if_neg (by omega : ¬ m < 0x80), if_neg (by omega : ¬ m < 0x90),
    if_neg (by omega : ¬ m < 0xa0), if_pos h2]

/-- A marker number in the negative fixint range names a
    negative fixint. Proved by walking the layout table: every
    earlier test fails on a number of 0xe0 or more. -/
theorem classify_negFixint {m : Nat} (h : 0xe0 ≤ m) : classify m = some .negFixint := by
  unfold classify
  rw [if_neg (by omega : ¬ m < 128),
    if_neg (by omega : ¬ m < 144),
    if_neg (by omega : ¬ m < 160),
    if_neg (by omega : ¬ m < 192),
    if_neg (by omega : ¬ m = 192),
    if_neg (by omega : ¬ m = 193),
    if_neg (by omega : ¬ m = 194),
    if_neg (by omega : ¬ m = 195),
    if_neg (by omega : ¬ m = 196),
    if_neg (by omega : ¬ m = 197),
    if_neg (by omega : ¬ m = 198),
    if_neg (by omega : ¬ m = 199),
    if_neg (by omega : ¬ m = 200),
    if_neg (by omega : ¬ m = 201),
    if_neg (by omega : ¬ m = 202),
    if_neg (by omega : ¬ m = 203),
    if_neg (by omega : ¬ m = 204),
    if_neg (by omega : ¬ m = 205),
    if_neg (by omega : ¬ m = 206),
    if_neg (by omega : ¬ m = 207),
    if_neg (by omega : ¬ m = 208),
    if_neg (by omega : ¬ m = 209),
    if_neg (by omega : ¬ m = 210),
    if_neg (by omega : ¬ m = 211),
    if_neg (by omega : ¬ m = 212),
    if_neg (by omega : ¬ m = 213),
    if_neg (by omega : ¬ m = 214),
    if_neg (by omega : ¬ m = 215),
    if_neg (by omega : ¬ m = 216),
    if_neg (by omega : ¬ m = 217),
    if_neg (by omega : ¬ m = 218),
    if_neg (by omega : ¬ m = 219),
    if_neg (by omega : ¬ m = 220),
    if_neg (by omega : ¬ m = 221),
    if_neg (by omega : ¬ m = 222),
    if_neg (by omega : ¬ m = 223),
    if_pos h]

/-! ## Byte readers -/

/-- Read a big endian number of exactly `k` bytes from the front
    of a byte list. Returns the number and the bytes after it, or
    `none` when fewer than `k` bytes stand there. -/
def readNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    (readNat k bs).map fun (u, r) => (b.toNat * 256 ^ k + u, r)

/-- The unfolding rule for `readNat` at a successor width on a
    list with a head byte. -/
theorem readNat_succ_cons (k : Nat) (b : UInt8) (bs : List UInt8) :
    readNat (k + 1) (b :: bs) =
      (readNat k bs).map fun (u, r) => (b.toNat * 256 ^ k + u, r) := by
  rw [readNat]

/-- Read a signed big endian number of exactly `k` bytes: the
    unsigned reading, less the modulus when its top bit stands.
    Widths here are 1, 2, 4, or 8. -/
def readSigned (k : Nat) (bs : List UInt8) : Option (Int × List UInt8) :=
  (readNat k bs).map fun (u, r) =>
    (if u < 256 ^ k / 2 then (u : Int) else (u : Int) - 256 ^ k, r)

/-- Take `n` bytes off the front of a byte list, or `none` when
    fewer than `n` bytes stand there. Returns the bytes taken
    and the bytes after them. -/
def readBytes (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bs.length ≥ n then some (bs.take n, bs.drop n) else none

/-- Read an extension body: one type byte, then `len` payload
    bytes. The type byte reads as a signed code: its own value
    when its top bit is clear, that value less 256 when it
    stands. -/
def readExtBody (len : Nat) (bs : List UInt8) : Option (Value × List UInt8) :=
  match bs with
  | [] => none
  | tb :: rest =>
    (readBytes len rest).map fun (chunk, r) =>
      (.ext (if tb.toNat < 128 then (tb.toNat : Int) else (tb.toNat : Int) - 256) chunk, r)

/-! ## Member readers -/

/-- Read `n` values, one after the other, with the reader `rec`.
    Returns the values and the bytes after them, or `none` when
    any one of them fails to read. -/
def parseMany (rec : List UInt8 → Option (Value × List UInt8)) :
    Nat → List UInt8 → Option (List Value × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match rec bs with
    | none => none
    | some (v, rest1) =>
      match parseMany rec n rest1 with
      | none => none
      | some (vs, rest2) => some (v :: vs, rest2)

/-- Read `n` key and value pairs, one after the other, with the
    reader `rec`. Returns the pairs and the bytes after them, or
    `none` when any one of them fails to read. -/
def parsePairs (rec : List UInt8 → Option (Value × List UInt8)) :
    Nat → List UInt8 → Option (List (Value × Value) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match rec bs with
    | none => none
    | some (k, r1) =>
      match rec r1 with
      | none => none
      | some (v, r2) =>
        match parsePairs rec n r2 with
        | none => none
        | some (ps, r3) => some ((k, v) :: ps, r3)

/-! ## The value reader -/

/-- Read one value from the front of a byte list, with at most
    `fuel` nesting levels. Returns the value and the bytes after
    it, or `none` when the front of the list holds no value this
    slice reads. -/
def parseGo : Nat → List UInt8 → Option (Value × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    match classify b.toNat with
    | none => none
    | some .posFixint => some (.int (b.toNat : Int), bs)
    | some .negFixint => some (.int ((b.toNat : Int) - 256), bs)
    | some (.fixmap n) =>
      (parsePairs (parseGo fuel) n bs).map fun (ps, r) => (.map ps, r)
    | some (.fixarray n) =>
      (parseMany (parseGo fuel) n bs).map fun (vs, r) => (.array vs, r)
    | some (.fixstr n) =>
      (readBytes n bs).map fun (chunk, r) => (.str chunk, r)
    | some .nil => some (.nil, bs)
    | some .false_ => some (.bool false, bs)
    | some .true_ => some (.bool true, bs)
    | some (.bin w) =>
      match readNat w bs with
      | none => none
      | some (len, r1) =>
        (readBytes len r1).map fun (chunk, r2) => (.bin chunk, r2)
    | some (.str w) =>
      match readNat w bs with
      | none => none
      | some (len, r1) =>
        (readBytes len r1).map fun (chunk, r2) => (.str chunk, r2)
    | some (.array w) =>
      match readNat w bs with
      | none => none
      | some (n, r1) =>
        (parseMany (parseGo fuel) n r1).map fun (vs, r2) => (.array vs, r2)
    | some (.map w) =>
      match readNat w bs with
      | none => none
      | some (n, r1) =>
        (parsePairs (parseGo fuel) n r1).map fun (ps, r2) => (.map ps, r2)
    | some (.uint w) => (readNat w bs).map fun (u, r) => (.int (u : Int), r)
    | some (.int w) => (readSigned w bs).map fun (v, r) => (.int v, r)
    | some .float32 => (readNat 4 bs).map fun (u, r) => (.float32 u, r)
    | some .float64 => (readNat 8 bs).map fun (u, r) => (.float64 u, r)
    | some (.fixext len) => readExtBody len bs
    | some (.ext w) =>
      match readNat w bs with
      | none => none
      | some (len, r1) => readExtBody len r1

/-- Read one whole value: exactly one value, with nothing after
    it. The fuel is the input length, which always lasts, as each
    nesting level eats at least its marker byte. -/
def parse (bs : List UInt8) : Option Value :=
  match parseGo bs.length bs with
  | some (v, []) => some v
  | _ => none

end MessagePack
