import LeanJson.RepoImpl.Access

/-!
# RepoImpl: building values, `json%`

`IntoJson α` turns a plain Lean value into a `Json` value, the way Python
values become JSON in `to_json`: `String`, `Bool`, `Nat`, `Int`, `Float`,
`Option` (`none` is `null`), `List`, `Array`, and `Json` itself.

`json% …` is JSON literal syntax with Lean terms spliced in, for handlers:

```
json% {"message": "Hello World"}
json% {"item_id": item_id, "q": q, "tags": ["a", "b"], "price": 1.5, "ok": true, "x": null}
json% {"total": (a + b)}
```

An identifier or a parenthesised term is converted with `IntoJson`.

Lean core declares a `json%` of its own (for `Lean.Json`), seen by every
module that imports `Lean`. This one is declared at `priority := high`, so it
wins there too and needs no type ascription (`tests/Notation.lean`).
-/

namespace LeanJson

/-- How a Lean value is written as JSON. -/
class IntoJson (α : Type) where
  intoJson : α → Json

export IntoJson (intoJson)

instance : IntoJson Json := ⟨id⟩
instance : IntoJson String := ⟨.str⟩
instance : IntoJson Bool := ⟨.bool⟩
instance : IntoJson Nat := ⟨fun n => .num (.int n)⟩
instance : IntoJson Int := ⟨fun i => .num (.int i)⟩
instance : IntoJson Number := ⟨.num⟩
instance : IntoJson Decimal := ⟨fun d => .num (.float d)⟩
/-- A float as its shortest round-tripping decimal; NaN and the infinities as
`Number.nan`, `.inf`, `.negInf`, which `to_json` prints per its
`inf_nan_mode` (`NaN`/`Infinity` by default, as pydantic-core). -/
instance : IntoJson Float := ⟨fun x => .num (Number.ofFloat x)⟩
instance {α : Type} [IntoJson α] : IntoJson (Option α) := ⟨fun
  | some a => intoJson a
  | none => .null⟩
instance {α : Type} [IntoJson α] : IntoJson (List α) := ⟨fun xs => .arr (xs.map intoJson).toArray⟩
instance {α : Type} [IntoJson α] : IntoJson (Array α) := ⟨fun xs => .arr (xs.map intoJson)⟩

/-- A decimal literal `m × 10^±e`, as `json%` and `OfScientific` read it. -/
def Number.ofScientific (m : Nat) (neg : Bool) (e : Nat) : Number :=
  .float (Decimal.normalize false m (if neg then -(e : Int) else e))

instance : OfScientific Json := ⟨fun m s e => .num (Number.ofScientific m s e)⟩
instance : Neg Json := ⟨fun
  | .num (.int i) => .num (.int (-i))
  | .num (.float d) => .num (.float { d with neg := !d.neg, h_norm := d.h_norm })
  | j => j⟩

declare_syntax_cat jsonv
syntax str : jsonv
syntax num : jsonv
syntax scientific : jsonv
syntax "-" num : jsonv
syntax "-" scientific : jsonv
syntax ident : jsonv
syntax "(" term ")" : jsonv
syntax "(" term " : " term ")" : jsonv
syntax "[" jsonv,* "]" : jsonv
syntax jsonMember := str ":" jsonv
syntax "{" jsonMember,* "}" : jsonv

open Lean in
/-- The term a `jsonv` literal denotes; `depth` bounds the nesting (so the
expander is total), far beyond any literal written by hand. -/
def expandJsonv : (depth : Nat) → TSyntax `jsonv → MacroM Term
  | 0, _ => Macro.throwError "json%: literal nested too deeply"
  | depth + 1, stx => match stx with
    | `(jsonv| $s:str) => `(Json.str $s)
    | `(jsonv| $n:num) => `(Json.num (Number.int $n))
    | `(jsonv| $n:scientific) => `(($n : Json))
    | `(jsonv| - $n:num) => `(Json.num (Number.int (-$n)))
    | `(jsonv| - $n:scientific) => `(-($n : Json))
    | `(jsonv| $x:ident) =>
      if x.getId == `null then `(Json.null) else `(intoJson $x)
    | `(jsonv| ($t)) => `(intoJson $t)
    | `(jsonv| ($t : $ty)) => `(intoJson ($t : $ty))
    | `(jsonv| [$xs,*]) => do
      let items ← xs.getElems.mapM (expandJsonv depth)
      `(Json.arr #[$items,*])
    | `(jsonv| {$ms,*}) => do
      let items ← ms.getElems.mapM fun m => match m with
        | `(jsonMember| $k:str : $v) => do `(($k, $(← expandJsonv depth v)))
        | _ => Macro.throwUnsupported
      `(Json.obj #[$items,*])
    | _ => Macro.throwUnsupported

/-- JSON literal syntax with spliced Lean terms. Higher priority than Lean
core's `json%`, so a literal is a `LeanJson.Json` even when `Lean` is
imported. -/
macro (priority := high) "json% " v:jsonv : term => expandJsonv 1000 v

end LeanJson
