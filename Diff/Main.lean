import Agentica

/-!
# The cases of the differential test

`lake exe diffcases` prints one line per case, tab-separated:

    id  function  arguments  expected

It is the only source of cases: `diff/run.agc` reads the same lines, runs each
case on agentica, and `scripts/difftest.py` compares. An argument is an `Int`
in decimal, or a `Bytes` as a comma list (`-` for no bytes). The expected
result is one of:

- `int N`, `bool B`, `text S`: a value that cannot halt;
- `halt CODE`: a runtime error, by its diagnostic code (never its message);
- `ok N`, `error KIND MESSAGE`: a `Result`. The kind and the message of its
  `Error` are values the function documents, so both are compared (a kind is
  a dotted name, with no space).

Nothing is escaped: no argument or result may hold a tab or a newline. A
future `String` function needs an escape on both sides first.
-/

open Agentica

/-- A case: the function name, its arguments as text, the expected result. -/
structure Case where
  fn : String
  args : List String
  expected : String

def showInt (a : AInt) : String := toString a.bits.toInt

def showM (r : M AInt) : String :=
  match r with
  | .ok v => s!"int {showInt v}"
  | .error e => s!"halt {e.code}"

def showResult (r : M (Result AInt)) : String :=
  match r with
  | .ok (.ok v) => s!"ok {showInt v}"
  | .ok (.error e) => s!"error {e.kind} {e.message}"
  | .error e => s!"halt {e.code}"

def showBytes (b : List UInt8) : String :=
  if b.isEmpty then "-" else ",".intercalate (b.map (toString ·.toNat))

def showInts (xs : List Int) : String :=
  if xs.isEmpty then "-" else ",".intercalate (xs.map toString)

def showBytesResult (r : Result Bytes) : String :=
  match r with
  | .ok b => s!"ok {showBytes b.data.toList}"
  | .error e => s!"error {e.kind} {e.message}"

def showUnwrap (r : M Bytes) : String :=
  match r with
  | .ok b => s!"bytes {showBytes b.data.toList}"
  | .error e => s!"halt {e.code}"

def toBytes (b : List UInt8) : Bytes :=
  if h : b.toArray.size < 2 ^ 63 then ⟨b.toArray, h⟩ else ⟨#[], by decide⟩

def intMax : Int := 9223372036854775807
def intMin : Int := -9223372036854775808

/-- The values that the edge cases of every function start from. -/
def edges : List Int :=
  [0, 1, -1, 2, 255, 256, 4294967296, -4294967296, intMax, intMax - 1, intMin, intMin + 1]

/-- Shift counts: negative, 0, inside, 63, 64 and above, and the extremes. -/
def counts : List Int := [-1, 0, 1, 8, 63, 64, 65, 100, intMax, intMin]

/-- Shifted values, with and without the sign bit. -/
def shifted : List Int := [0, 1, -1, 5, -7, intMax, intMin, intMin + 1, 255]

/-- SplitMix64: a fixed seed gives the same cases on every run. -/
def next (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A random `Int`: the full range, or a small value, half of the time each. -/
def randomInt (s : UInt64) : Int × UInt64 :=
  let (a, s) := next s
  let (b, s) := next s
  if a % 2 == 0 then ((BitVec.ofNat 64 b.toNat).toInt, s)
  else ((b % 2001).toNat - 1000, s)

/-- A random value in `[lo, lo + span)`. -/
def randomIn (s : UInt64) (lo : Int) (span : Nat) : Int × UInt64 :=
  let (a, s) := next s
  (lo + (a.toNat % span), s)

/-- Up to 8 Ints, most of them bytes, some just outside, a few anything. -/
def randomInts (s : UInt64) : List Int × UInt64 := Id.run do
  let (n, s0) := next s
  let mut s := s0
  let mut out : List Int := []
  for _ in [0:(n.toNat % 9)] do
    let (k, s1) := next s
    let (x, s2) := if k % 16 == 0 then randomInt s1 else randomIn s1 (-2) 260
    s := s2
    out := out ++ [x]
  return (out, s)

def randomBytes (s : UInt64) : List UInt8 × UInt64 := Id.run do
  let (n, s0) := next s
  let mut s := s0
  let mut out : List UInt8 := []
  for _ in [0:(n.toNat % 13)] do
    let (b, s') := next s
    s := s'
    out := out ++ [b.toUInt8]
  return (out, s)

def binaryInt : List (String × (AInt → AInt → M AInt)) :=
  [("add", AInt.add), ("sub", AInt.sub), ("shift_left", AInt.shift_left),
   ("shift_right", AInt.shift_right), ("shift_right_unsigned", AInt.shift_right_unsigned)]

def binaryPure : List (String × (AInt → AInt → AInt)) :=
  [("bit_and", AInt.bit_and), ("bit_or", AInt.bit_or), ("bit_xor", AInt.bit_xor)]

def compares : List (String × (AInt → AInt → Bool)) :=
  [("eq", AInt.eq), ("ne", AInt.ne), ("lt", AInt.lt), ("le", AInt.le), ("gt", AInt.gt),
   ("ge", AInt.ge)]

def binaryCase (fn : String) (a b : Int) (expected : String) : Case :=
  { fn, args := [toString a, toString b], expected }

def intCases (fn : String) (f : AInt → AInt → M AInt) (a b : Int) : Case :=
  binaryCase fn a b (showM (f (AInt.ofInt a) (AInt.ofInt b)))

def pureCases (fn : String) (f : AInt → AInt → AInt) (a b : Int) : Case :=
  binaryCase fn a b s!"int {showInt (f (AInt.ofInt a) (AInt.ofInt b))}"

def compareCase (fn : String) (f : AInt → AInt → Bool) (a b : Int) : Case :=
  binaryCase fn a b s!"bool {f (AInt.ofInt a) (AInt.ofInt b)}"

/-- `Bytes.from_list` and `unwrap!` of it on a list of Ints. -/
def listCases (xs : List Int) : List Case :=
  let items := xs.map AInt.ofInt
  [{ fn := "from_list", args := [showInts xs], expected := showBytesResult (Bytes.from_list items) },
   { fn := "unwrap", args := [showInts xs],
     expected := showUnwrap (Result.unwrap! (Bytes.from_list items)) }]

def plusCase (a b : List UInt8) : Case :=
  { fn := "plus", args := [showBytes a, showBytes b],
    expected := s!"bytes {showBytes (Bytes.plus (toBytes a) (toBytes b)).data.toList}" }

def unaryCases (a : Int) : List Case :=
  [{ fn := "neg", args := [toString a], expected := showM (AInt.neg (AInt.ofInt a)) },
   { fn := "bit_not", args := [toString a],
     expected := s!"int {showInt (AInt.bit_not (AInt.ofInt a))}" },
   { fn := "from_int", args := [toString a],
     expected := s!"text {String.from_int (AInt.ofInt a)}" }]

/-- The other readers of `std/binary`, as `translator/` writes them (`Agentica/Std/Binary.lean`). -/
def readers : List (String × (Bytes → AInt → M (Result AInt))) :=
  [("read_u16_be", Std.Binary.read_u16_be), ("read_u32_le", Std.Binary.read_u32_le),
   ("read_u64_le", Std.Binary.read_u64_le), ("read_i64_le", Std.Binary.read_i64_le),
   ("read_i16_le", Std.Binary.read_i16_le), ("read_i32_le", Std.Binary.read_i32_le),
   ("read_u8", Std.Binary.read_u8), ("read_i8", Std.Binary.read_i8),
   ("read_u32_be", Std.Binary.read_u32_be), ("read_u64_be", Std.Binary.read_u64_be),
   ("read_i16_be", Std.Binary.read_i16_be), ("read_i32_be", Std.Binary.read_i32_be),
   ("read_i64_be", Std.Binary.read_i64_be)]

def bytesCases (b : List UInt8) (i : Int) : List Case :=
  let bytes := toBytes b
  [{ fn := "length", args := [showBytes b], expected := s!"int {showInt (Bytes.length bytes)}" },
   { fn := "at", args := [showBytes b, toString i],
     expected := showM (Bytes.at bytes (AInt.ofInt i)) },
   { fn := "read_u16_le", args := [showBytes b, toString i],
     expected := showResult (Std.Binary.read_u16_le bytes (AInt.ofInt i)) }] ++
  readers.map (fun (fn, f) =>
    { fn, args := [showBytes b, toString i], expected := showResult (f bytes (AInt.ofInt i)) }) ++
  -- A frame limit below, at and above the length, and the edges.
  [-1, 0, 1, 258, 33554432, 4294967295, intMax, intMin].map fun m =>
    { fn := "read_frame_length", args := [showBytes b, toString i, toString m],
      expected := showResult (Std.Binary.read_frame_length bytes (AInt.ofInt i) (AInt.ofInt m)) }

/-- The fixed cases: the edges of every function. -/
def fixedCases : List Case := Id.run do
  let mut out : List Case := []
  for a in edges do
    for b in edges do
      for (fn, f) in [("add", AInt.add), ("sub", AInt.sub)] do
        out := out ++ [intCases fn f a b]
      for (fn, f) in binaryPure do
        out := out ++ [pureCases fn f a b]
      for (fn, f) in compares do
        out := out ++ [compareCase fn f a b]
    out := out ++ unaryCases a
  for a in shifted do
    for n in counts do
      for (fn, f) in binaryInt.drop 2 do
        out := out ++ [intCases fn f a n]
  let sample : List UInt8 := [1, 2, 255]
  for i in [-1, 0, 1, 2, 3, intMax, intMin] do
    out := out ++ bytesCases sample i
  -- Ten bytes, with the sign bit set at several places, so every reader has
  -- in-range offsets, negative values and a u64 above Int.MAX.
  let long : List UInt8 := [1, 2, 255, 128, 0, 127, 254, 129, 200, 3]
  for i in [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] do
    out := out ++ bytesCases long i
  out := out ++ bytesCases [] 0
  -- The sign edges of each reader, at offset 0.
  for b in [[0, 0, 0, 0, 0, 0, 0, 127], [0, 0, 0, 0, 0, 0, 0, 128], [255, 127], [0, 128],
      [255, 255, 255, 127], [0, 0, 0, 128], List.replicate 8 255, [127], [128],
      [127, 255], [128, 0], [127, 255, 255, 255], [128, 0, 0, 0], [127, 0, 0, 0, 0, 0, 0, 0],
      [128, 0, 0, 0, 0, 0, 0, 0]] do
    out := out ++ bytesCases b 0
  -- Lists of Ints: empty, the byte edges, an item outside at each place.
  for xs in [[], [0], [255], [256], [-1], [0, 255], [1, 2, 3], [1, 256, -1], [1, 2, -1],
      [intMax], [intMin], [255, 255, 255, 255, 255, 255, 255, 255], [0, 0, 300]] do
    out := out ++ listCases xs
  for a in [[], [1], [1, 2, 255]] do
    for b in [[], [0], [128, 255]] do
      out := out ++ [plusCase a b]
  return out

/-- Random cases from a fixed seed: `perFunction` for each function. -/
def randomCases (seed : UInt64) (perFunction : Nat) : List Case := Id.run do
  let mut s := seed
  let mut out : List Case := []
  for _ in [0:perFunction] do
    let (a, s1) := randomInt s
    let (b, s2) := randomInt s1
    let (n, s3) := randomIn s2 (-3) 72
    let (bytes, s4) := randomBytes s3
    let (i, s5) := randomIn s4 (-2) (bytes.length + 4)
    let (xs, s6) := randomInts s5
    let (more, s7) := randomBytes s6
    s := s7
    out := out ++ listCases xs ++ [plusCase bytes more]
    for (fn, f) in binaryInt do
      out := out ++ [intCases fn f a (if fn.startsWith "shift" then n else b)]
    for (fn, f) in binaryPure do
      out := out ++ [pureCases fn f a b]
    for (fn, f) in compares do
      out := out ++ [compareCase fn f a b]
    out := out ++ unaryCases a ++ bytesCases bytes i
  return out

def main : IO Unit := do
  let cases := fixedCases ++ randomCases 20261109 40
  let mut id := 0
  for c in cases do
    IO.println s!"{id}\t{c.fn}\t{" ".intercalate c.args}\t{c.expected}"
    id := id + 1
