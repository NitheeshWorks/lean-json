import LeanJson.RepoImpl.Digits

/-!
# RepoImpl: the printer

`printWith o d v` is the bytes of `v` at nesting depth `d` under options `o`.
The compact form (`PrintOpts` default) is what pydantic-core's `to_json` and
Starlette's `JSONResponse` emit: `,` and `:` separators, no whitespace.
Strings are escaped as serde_json does (`\"`, `\\`, `\b \f \n \r \t`,
other control characters as lowercase `\u00XX`, everything else raw UTF-8);
with `ensureAscii` every non-ASCII character becomes `\uXXXX` (a surrogate
pair above the BMP). Floats use the shortest-form layout of the `ryu` crate
that serde_json formats with (`1.0`, `0.001`, `1e+16`, `1.5e-7`).

The printer produces a `List UInt8`; the API turns it into a `ByteArray`.
-/

namespace LeanJson

/-- `null`, `true`, `false` as bytes. -/
def litNull : List UInt8 := [110, 117, 108, 108]
def litTrue : List UInt8 := [116, 114, 117, 101]
def litFalse : List UInt8 := [102, 97, 108, 115, 101]

/-- `n` zeros as ASCII. -/
def zeros (n : Nat) : List UInt8 := List.replicate n 48

/-- An exponent as serde_json/ryu writes it: `+` or `-`, then digits. -/
def printExp (i : Int) : List UInt8 :=
  if i < 0 then 45 :: printNat i.natAbs else 43 :: printNat i.toNat

/-- The digits of a normalised mantissa with the decimal point placed as ryu
places it. `ds` are the mantissa's digits and `k` its exponent; `kk` is the
position of the point relative to the first digit. -/
def layoutDecimal (ds : List Nat) (k : Int) : List UInt8 :=
  let L : Int := ds.length
  let kk := L + k
  if 0 ≤ k ∧ kk ≤ 16 then
    ds.map digitByte ++ zeros k.toNat ++ [46, 48]
  else if 0 < kk ∧ kk ≤ 16 then
    (ds.take kk.toNat).map digitByte ++ 46 :: (ds.drop kk.toNat).map digitByte
  else if -5 < kk ∧ kk ≤ 0 then
    [48, 46] ++ zeros (-kk).toNat ++ ds.map digitByte
  else if ds.length = 1 then
    ds.map digitByte ++ 101 :: printExp (kk - 1)
  else
    (ds.take 1).map digitByte ++ 46 :: (ds.drop 1).map digitByte ++ 101 :: printExp (kk - 1)

/-- How many integer-part digits `layoutDecimal ds k` writes. -/
def layoutIntLen (L : Nat) (k : Int) : Nat :=
  if 0 ≤ k ∧ (L : Int) + k ≤ 16 then ((L : Int) + k).toNat
  else if 0 < (L : Int) + k ∧ (L : Int) + k ≤ 16 then ((L : Int) + k).toNat
  else 1

/-- A float, serde_json/ryu style; `-0.0` keeps its sign. -/
def printDecimal (d : Decimal) : List UInt8 :=
  (if d.neg then [45] else []) ++ layoutDecimal (natDigits d.mant) d.exp

def printNumber : Number → List UInt8
  | .int i => printInt i
  | .float d => printDecimal d

/-- The bytes of the sign and integer part of `printNumber n`: what jiter's
4300 limit (`ParseCfg.maxIntLen`) counts. -/
def Number.intLen : Number → Nat
  | .int i => (printInt i).length
  | .float d => (if d.neg then 1 else 0) + layoutIntLen (natDigits d.mant).length d.exp

/-- `\uXXXX` for `n < 65536`, lowercase hex. -/
def hex4 (n : Nat) : List UInt8 :=
  [92, 117, hexByte (n / 4096 % 16), hexByte (n / 256 % 16), hexByte (n / 16 % 16), hexByte (n % 16)]

/-- The escaped form of one character inside a string literal. -/
def escapeChar (ascii : Bool) (c : Char) : List UInt8 :=
  let n := c.toNat
  if n = 34 then [92, 34]
  else if n = 92 then [92, 92]
  else if n = 8 then [92, 98]
  else if n = 12 then [92, 102]
  else if n = 10 then [92, 110]
  else if n = 13 then [92, 114]
  else if n = 9 then [92, 116]
  else if n < 32 then hex4 n
  else if ascii ∧ 128 ≤ n then
    if n < 65536 then hex4 n
    else hex4 (0xD800 + (n - 0x10000) / 1024) ++ hex4 (0xDC00 + (n - 0x10000) % 1024)
  else String.utf8EncodeChar c

/-- A string literal, quotes included. -/
def printString (ascii : Bool) (s : String) : List UInt8 :=
  34 :: s.toList.flatMap (escapeChar ascii) ++ [34]

/-- The line break and indentation before an item at depth `d` (pretty
form), or nothing (compact form). -/
def PrintOpts.nl (o : PrintOpts) (d : Nat) : List UInt8 :=
  match o.indent with
  | none => []
  | some k => 10 :: List.replicate (k * d) 32

/-- The key/value separator: `:` compact, `: ` pretty. -/
def PrintOpts.colon (o : PrintOpts) : List UInt8 :=
  match o.indent with
  | none => [58]
  | some _ => [58, 32]

mutual
/-- `v` printed at depth `d`. -/
def printWith (o : PrintOpts) (d : Nat) : Json → List UInt8
  | .null => litNull
  | .bool true => litTrue
  | .bool false => litFalse
  | .num n => printNumber n
  | .str s => printString o.ensureAscii s
  | .arr [] => [91, 93]
  | .arr (x :: xs) =>
    91 :: o.nl (d + 1) ++ printWith o (d + 1) x ++ printElems o (d + 1) xs ++ o.nl d ++ [93]
  | .obj [] => [123, 125]
  | .obj ((k, v) :: kvs) =>
    123 :: o.nl (d + 1) ++ printString o.ensureAscii k ++ o.colon ++ printWith o (d + 1) v ++
      printMembers o (d + 1) kvs ++ o.nl d ++ [125]
/-- The array elements after the first, each preceded by `,`. -/
def printElems (o : PrintOpts) (d : Nat) : List Json → List UInt8
  | [] => []
  | x :: xs => 44 :: o.nl d ++ printWith o d x ++ printElems o d xs
/-- The object members after the first, each preceded by `,`. -/
def printMembers (o : PrintOpts) (d : Nat) : List (String × Json) → List UInt8
  | [] => []
  | (k, v) :: kvs =>
    44 :: o.nl d ++ printString o.ensureAscii k ++ o.colon ++ printWith o d v ++ printMembers o d kvs
end

/-- The compact printing of `v`: what `to_json(v)` returns. -/
def printBytes (v : Json) : List UInt8 := printWith {} 0 v

end LeanJson
