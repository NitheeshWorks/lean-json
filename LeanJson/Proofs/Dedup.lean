import LeanJson.Proofs.Fields

/-!
# Proofs: the collapsing parser is the `dict` specification, at every depth

`parseDocumentIn_dedup`: the parser with repeated keys collapsed
(`ParseCfg.dedupKeys`, the default) returns exactly `Json.dedupDeep` of what
the parser that keeps every member returns, errors included. `dedupDeep`
applies the specification `Json.dedupKeysList` (first position, last value)
to every object at every depth. So the index the parser collapses keys
through (`KeyIndex`, seeded per process) is invisible in what it returns.

The proof follows the parser's loops: each `Fields.add` step is `insertLast`
(`Fields.add_exact`), so an object's members, collapsed as they are read, are
the specification applied to the members read without collapsing.
-/

namespace LeanJson

open Json

variable {get : Nat → Option UInt8} {n : Nat}

theorem dedupDeepList_eq : ∀ xs : List Json, dedupDeepList xs = xs.map dedupDeep
  | [] => rfl
  | x :: xs => by simp [dedupDeepList, dedupDeepList_eq xs]

/-- One member with its value collapsed. -/
abbrev ddkv (kv : String × Json) : String × Json := (kv.1, kv.2.dedupDeep)

theorem dedupDeepFields_eq : ∀ kvs : List (String × Json), dedupDeepFields kvs = kvs.map ddkv
  | [] => rfl
  | (k, v) :: kvs => by simp [dedupDeepFields, dedupDeepFields_eq kvs]

theorem dedupDeep_arr (a : Array Json) : (Json.arr a).dedupDeep = .arr (a.map dedupDeep) := by
  obtain ⟨xs⟩ := a
  simp [dedupDeep, dedupDeepList_eq]

theorem dedupDeep_obj (a : Array (String × Json)) :
    (Json.obj a).dedupDeep = .obj (dedupKeysList (a.toList.map ddkv)).toArray := by
  obtain ⟨kvs⟩ := a
  simp only [dedupDeep, dedupDeepFields_eq]

/-- A result with its value collapsed. -/
abbrev dd (r : Json × Nat) : Json × Nat := (r.1.dedupDeep, r.2)

/-- The collapsing child answers what the plain one does, collapsed. -/
def DedupOn (ct cf : Nat → Except ParseErr (Json × Nat)) : Prop := ∀ j, ct j = (cf j).map dd

theorem parseElems_dedup {ct cf : Nat → Except ParseErr (Json × Nat)} (hc : DedupOn ct cf) :
    ∀ (pos : Nat) (acc : Array Json),
    parseElems ct get n pos (acc.map dedupDeep) = (parseElems cf get n pos acc).map dd := by
  intro pos acc
  rw [parseElems, parseElems, hc pos]
  cases cf pos with
  | error e => rfl
  | ok r =>
    obtain ⟨v, j⟩ := r
    simp only [Except.map]
    generalize get (skipWs get n j) = g1
    generalize get (skipWs get n (skipWs get n j + 1)) = g2
    split
    · split
      · rfl
      · split
        · rw [← Array.map_push]; exact parseElems_dedup hc _ _
        · rfl
      · rfl
    · simp only [dd, dedupDeep_arr, Array.map_push]
    · rfl
    · rfl
termination_by pos => n - pos
decreasing_by omega

/-- A collapsed object under construction, against the plain one: the index
is exact, and its members are the specification applied to the plain
members. -/
def DRel (st sf : Fields) : Prop := st.Exact ∧ st.1.toList = dedupKeysList (sf.1.toList.map ddkv)

theorem DRel.empty : DRel Fields.empty Fields.empty := ⟨Fields.exact_empty, rfl⟩

theorem DRel.add {st sf : Fields} (h : DRel st sf) (k : String) (v : Json) :
    DRel (st.add true k v.dedupDeep) (sf.add false k v) := by
  obtain ⟨h1, h2⟩ := Fields.add_exact (k := k) (v := v.dedupDeep) h.1
  refine ⟨h2, ?_⟩
  rw [h1, h.2]
  simp only [Fields.add, Bool.false_eq_true, ↓reduceIte, Array.toList_push, List.map_append,
    List.map_cons, List.map_nil, dedupKeysList, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem DRel.obj {st sf : Fields} (h : DRel st sf) : Json.obj st.1 = (Json.obj sf.1).dedupDeep := by
  rw [dedupDeep_obj]
  congr 1
  apply Array.toList_inj.mp
  rw [h.2, List.toList_toArray]

theorem parseMembers_dedup {ct cf : Nat → Except ParseErr (Json × Nat)} (hc : DedupOn ct cf) :
    ∀ (pos : Nat) (st sf : Fields), DRel st sf →
    parseMembers true ct get n pos st = (parseMembers false cf get n pos sf).map dd := by
  intro pos st sf hr
  rw [parseMembers, parseMembers]
  cases parseString get n pos with
  | error e => rfl
  | ok r =>
    obtain ⟨k, kn⟩ := r
    simp only
    generalize get (skipWs get n kn) = g1
    split
    · generalize get (skipWs get n (skipWs get n kn + 1)) = g2
      split
      · rfl
      · rw [hc]
        cases cf (skipWs get n (skipWs get n kn + 1)) with
        | error e => rfl
        | ok r =>
          obtain ⟨v, j⟩ := r
          simp only [Except.map]
          generalize get (skipWs get n j) = g3
          generalize get (skipWs get n (skipWs get n j + 1)) = g4
          split
          · split
            · split
              · exact parseMembers_dedup hc _ _ _ (hr.add k v)
              · rfl
            all_goals rfl
          · simp only [dd, (hr.add k v).obj]
          all_goals rfl
    all_goals rfl
termination_by pos => n - pos
decreasing_by omega

theorem dedupDeep_ofNumber (x : Number) : (Json.ofNumber x).dedupDeep = Json.ofNumber x := by
  rw [Json.ofNumber_eq]; rfl

/-- One step, collapsing, is the plain step collapsed. -/
theorem valueStep_dedup (cfg : ParseCfg) (hd : cfg.dedupKeys = true)
    {ct cf : Nat → Except ParseErr (Json × Nat)} (hc : DedupOn ct cf) :
    valueStep cfg ct get n = (valueStep { cfg with dedupKeys := false } cf get n).map dd := by
  unfold valueStep
  split
  · rfl
  rename_i b _
  dsimp only
  by_cases c34 : (b == 34) = true
  · rw [ite_eq_left c34, ite_eq_left c34]
    cases parseString get n 0 <;> rfl
  rw [ite_eq_right c34, ite_eq_right c34]
  by_cases c91 : (b == 91) = true
  · rw [ite_eq_left c91, ite_eq_left c91]
    generalize get (skipWs get n 1) = g
    split
    · rfl
    · have := parseElems_dedup (get := get) (n := n) hc (skipWs get n 1) #[]
      rwa [Array.map_empty] at this
    · rfl
  rw [ite_eq_right c91, ite_eq_right c91]
  by_cases c123 : (b == 123) = true
  · rw [ite_eq_left c123, ite_eq_left c123]
    generalize get (skipWs get n 1) = g
    split
    · rfl
    · rw [hd]; exact parseMembers_dedup hc _ _ _ DRel.empty
    · rfl
    · rfl
  rw [ite_eq_right c123, ite_eq_right c123]
  repeat' split
  all_goals first
    | rfl
    | (cases expectLit get 1 _ <;> rfl)
    | (show _ = Except.map dd (Except.map _ (parseNumber cfg get n 0))
       cases parseNumber cfg get n 0 with
       | error e => rfl
       | ok r => simp only [Except.map, dd, dedupDeep_ofNumber])

theorem shiftRes_dedup (k : Nat) (r : Except ParseErr (Json × Nat)) :
    shiftRes k (r.map dd) = (shiftRes k r).map dd := by
  cases r <;> rfl

/-- The nesting loop, collapsing, is the plain loop collapsed. -/
theorem valueGo_dedup (cfg : ParseCfg) (hd : cfg.dedupKeys = true) : ∀ d base : Nat,
    valueGo cfg get n d base = (valueGo { cfg with dedupKeys := false } get n d base).map dd
  | 0, _ => rfl
  | d + 1, base => by
    rw [valueGo, valueGo]
    exact valueStep_dedup cfg hd fun j => by rw [valueGo_dedup cfg hd d (base + j), shiftRes_dedup]

/-- **The collapsing parser is the `dict` specification at every depth**:
with repeated keys collapsed, a document parses to `Json.dedupDeep` of what
it parses to with every member kept, and fails exactly where that does. -/
theorem parseDocumentIn_dedup (cfg : ParseCfg) (hd : cfg.dedupKeys = true) :
    parseDocumentIn cfg get n = (parseDocumentIn { cfg with dedupKeys := false } get n).map dedupDeep := by
  unfold parseDocumentIn parseValueIn
  dsimp only
  generalize get (skipWs get n 0) = g
  cases g with
  | none => rfl
  | some b =>
    dsimp only
    rw [show ParseCfg.budget { cfg with dedupKeys := false } n = cfg.budget n from rfl,
      valueGo_dedup cfg hd, shiftRes_dedup]
    cases shiftRes (skipWs get n 0) (valueGo { cfg with dedupKeys := false } get n (cfg.budget n) (skipWs get n 0)) with
    | error e => rfl
    | ok r =>
      obtain ⟨v, p⟩ := r
      dsimp only [Except.map, dd]
      split <;> rfl

/-- `parseDocumentIn_dedup` on a buffer: `from_json`'s `dict` collapsing. -/
theorem parse_dedup (cfg : ParseCfg) (hd : cfg.dedupKeys = true) (bs : ByteArray) :
    parseDocumentWith cfg bs = (parseDocumentWith { cfg with dedupKeys := false } bs).map dedupDeep :=
  parseDocumentIn_dedup cfg hd

end LeanJson
