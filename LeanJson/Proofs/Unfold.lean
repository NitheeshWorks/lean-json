import LeanJson.RepoImpl.Parse

/-!
# The value parser without its progress proofs

`parseValueWith` returns `Step`s, which carry progress proofs. The `…At`
forms forget them (`Step.out`), and the equations below restate each
production in that form, reading bytes with `bs[i]?`, so every theorem about
the parser rewrites with an ordinary equation. Two small lemmas about
`Step.lift` and `Step.cast` do all the bookkeeping.
-/

namespace LeanJson

/-- The value parser inside `depth` containers, progress forgotten. -/
def parseValueAtD (cfg : ParseCfg) (bs : ByteArray) (depth pos : Nat) : Except ParseErr (Json × Nat) :=
  (parseValueWith cfg bs depth pos).map Step.out

/-- The element loop, progress forgotten. The guard `start ≤ pos` holds at
every call the parser makes; it lets the equations below name the loop
without a proof argument. -/
def parseElemsAt (cfg : ParseCfg) (bs : ByteArray) (depth start pos : Nat) (acc : List Json) :
    Except ParseErr (Json × Nat) :=
  if h : start ≤ pos then (parseElems cfg bs depth start pos h acc).map Step.out
  else .error ⟨.expectedSomeValue, pos⟩

def parseMembersAt (cfg : ParseCfg) (bs : ByteArray) (depth start pos : Nat)
    (acc : List (String × Json)) : Except ParseErr (Json × Nat) :=
  if h : start ≤ pos then (parseMembers cfg bs depth start pos h acc).map Step.out
  else .error ⟨.expectedSomeValue, pos⟩

theorem parseValueAt_zero (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) :
    parseValueAt cfg bs pos = parseValueAtD cfg bs 0 pos := rfl

theorem lift_cast_out {bs : ByteArray} {p q : Nat} {α β : Type} (r : Except ParseErr (α × Nat))
    (h : ∀ x, r = .ok x → Adv bs q x.2 ∧ q < x.2) (f : α → β) (hle : p ≤ q) :
    ((Step.lift r h).map (·.cast f hle)).map Step.out = r.map (fun x => (f x.1, x.2)) := by
  cases r <;> rfl

theorem lift_cast_out' {bs : ByteArray} {p q : Nat} {α β : Type} (r : Except ParseErr (α × Nat))
    (h : ∀ x, r = .ok x → Adv bs q x.2 ∧ q < x.2) (f : α → β) (hle : p ≤ q) :
    (Step.lift r h).map (fun x => (x.cast f hle).out) = r.map (fun x => (f x.1, x.2)) := by
  cases r <;> rfl

theorem lift_out {bs : ByteArray} {q : Nat} {α : Type} (r : Except ParseErr (α × Nat))
    (h : ∀ x, r = .ok x → Adv bs q x.2 ∧ q < x.2) : (Step.lift r h).map Step.out = r := by
  cases r <;> rfl

theorem cast_out' {bs : ByteArray} {p q : Nat} {α : Type} (r : Except ParseErr (Step bs q α))
    (hle : p ≤ q) : r.map (fun x => (x.cast id hle).out) = r.map Step.out := by
  cases r <;> rfl

theorem cast_out {bs : ByteArray} {p q : Nat} {α : Type} (r : Except ParseErr (Step bs q α))
    (hle : p ≤ q) : (r.map (·.cast id hle)).map Step.out = r.map Step.out := by
  cases r <;> rfl

theorem get_of_lt {bs : ByteArray} {i : Nat} (h : i < bs.size) : bs[i]? = some bs[i] :=
  getElem?_pos bs i h

theorem get_of_ge {bs : ByteArray} {i : Nat} (h : ¬ i < bs.size) : bs[i]? = none :=
  getElem?_neg bs i h

theorem map_map_ok {α β γ : Type} (r : Except ParseErr α) (f : α → β) (g : β → γ) :
    (r.map f).map g = r.map (fun x => g (f x)) := by cases r <;> rfl

@[simp] theorem map_error {α β : Type} (f : α → β) (e : ParseErr) :
    (Except.error e : Except ParseErr α).map f = .error e := rfl

@[simp] theorem map_ok {α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ParseErr α).map f = .ok (f a) := rfl

theorem map_id_pair {α : Type} (r : Except ParseErr (α × Nat)) :
    r.map (fun x => (id x.1, x.2)) = r := by cases r <;> rfl

theorem parseValueAtD_eq (cfg : ParseCfg) (bs : ByteArray) (depth pos : Nat) :
    parseValueAtD cfg bs depth pos =
      match bs[skipWs bs pos]? with
      | none => .error ⟨.eofWhileParsingValue, skipWs bs pos⟩
      | some b =>
        if cfg.depthOk depth = false then .error ⟨.recursionLimitExceeded, skipWs bs pos⟩
        else if b == 34 then (parseString bs (skipWs bs pos)).map (fun x => (.str x.1, x.2))
        else if b == 91 then
          match bs[skipWs bs (skipWs bs pos + 1)]? with
          | none => .error ⟨.eofWhileParsingList, skipWs bs (skipWs bs pos + 1)⟩
          | some c =>
            if c == 93 then .ok (.arr [], skipWs bs (skipWs bs pos + 1) + 1)
            else parseElemsAt cfg bs (depth + 1) pos (skipWs bs (skipWs bs pos + 1)) []
        else if b == 123 then
          match bs[skipWs bs (skipWs bs pos + 1)]? with
          | none => .error ⟨.eofWhileParsingObject, skipWs bs (skipWs bs pos + 1)⟩
          | some c =>
            if c == 125 then .ok (.obj [], skipWs bs (skipWs bs pos + 1) + 1)
            else if c == 34 then parseMembersAt cfg bs (depth + 1) pos (skipWs bs (skipWs bs pos + 1)) []
            else .error ⟨.keyMustBeAString, skipWs bs (skipWs bs pos + 1)⟩
        else if b == 116 then (expectLit bs (skipWs bs pos + 1) [114, 117, 101]).map (fun p => (.bool true, p))
        else if b == 102 then
          (expectLit bs (skipWs bs pos + 1) [97, 108, 115, 101]).map (fun p => (.bool false, p))
        else if b == 110 then (expectLit bs (skipWs bs pos + 1) [117, 108, 108]).map (fun p => (.null, p))
        else if b == 45 || isDigit b then (parseNumber cfg bs (skipWs bs pos)).map (fun x => (.num x.1, x.2))
        else if b == 78 && cfg.allowInfNan then
          (expectLit bs (skipWs bs pos + 1) [97, 78]).map (fun p => (.num .nan, p))
        else if b == 73 && cfg.allowInfNan then
          (expectLit bs (skipWs bs pos + 1) [110, 102, 105, 110, 105, 116, 121]).map (fun p => (.num .inf, p))
        else .error ⟨.expectedSomeValue, skipWs bs pos⟩ := by
  unfold parseValueAtD
  rw [parseValueWith]
  simp only
  have g0 := skipWs_ge bs pos
  have g1 := skipWs_ge bs (skipWs bs pos + 1)
  by_cases hqs : skipWs bs pos < bs.size
  · rw [dite_eq_left hqs, get_of_lt hqs]
    simp only
    by_cases hd : cfg.depthOk depth = false
    · rw [ite_eq_left hd, ite_eq_left hd]; rfl
    rw [ite_eq_right hd, ite_eq_right hd]
    simp only [apply_ite (Except.map Step.out), apply_dite (Except.map Step.out), map_map_ok,
      lift_cast_out', cast_out', lift_out, map_error, map_ok]
    by_cases hp : skipWs bs (skipWs bs pos + 1) < bs.size
    · simp only [dite_eq_left hp, get_of_lt hp, parseElemsAt, parseMembersAt, dite_eq_left (by omega : pos ≤ skipWs bs (skipWs bs pos + 1))]
      rfl
    · simp only [dite_eq_right hp, get_of_ge hp]
  · rw [dite_eq_right hqs, get_of_ge hqs]; rfl

theorem parseElemsAt_eq (cfg : ParseCfg) (bs : ByteArray) (depth start pos : Nat) (acc : List Json)
    (hsp : start ≤ pos) :
    parseElemsAt cfg bs depth start pos acc =
      match parseValueAtD cfg bs depth pos with
      | .error e => .error e
      | .ok (v, p1) =>
        match bs[skipWs bs p1]? with
        | none => .error ⟨.eofWhileParsingList, skipWs bs p1⟩
        | some c =>
          if c == 44 then
            if bs[skipWs bs (skipWs bs p1 + 1)]? == some 93 then
              .error ⟨.trailingComma, skipWs bs (skipWs bs p1 + 1)⟩
            else parseElemsAt cfg bs depth start (skipWs bs (skipWs bs p1 + 1)) (v :: acc)
          else if c == 93 then .ok (.arr (v :: acc).reverse, skipWs bs p1 + 1)
          else .error ⟨.expectedListCommaOrEnd, skipWs bs p1⟩ := by
  unfold parseElemsAt
  rw [dite_eq_left hsp, parseElems]
  unfold parseValueAtD
  cases hv : parseValueWith cfg bs depth pos with
  | error e => rfl
  | ok s =>
    have := s.lt
    simp only [map_ok, Step.out]
    have g1 := skipWs_ge bs s.next
    have g2 := skipWs_ge bs (skipWs bs s.next + 1)
    by_cases hp : skipWs bs s.next < bs.size
    · rw [dite_eq_left hp, get_of_lt hp]
      simp only [apply_ite (Except.map Step.out), map_error, map_ok,
        dite_eq_left (by omega : start ≤ skipWs bs (skipWs bs s.next + 1))]
      rfl
    · rw [dite_eq_right hp, get_of_ge hp]; rfl

theorem parseMembersAt_eq (cfg : ParseCfg) (bs : ByteArray) (depth start pos : Nat)
    (acc : List (String × Json)) (hsp : start ≤ pos) :
    parseMembersAt cfg bs depth start pos acc =
      match parseString bs pos with
      | .error e => .error e
      | .ok (k, p1) =>
        match bs[skipWs bs p1]? with
        | none => .error ⟨.eofWhileParsingObject, skipWs bs p1⟩
        | some c =>
          if c == 58 then
            match parseValueAtD cfg bs depth (skipWs bs p1 + 1) with
            | .error e => .error e
            | .ok (v, p2) =>
              match bs[skipWs bs p2]? with
              | none => .error ⟨.eofWhileParsingObject, skipWs bs p2⟩
              | some d =>
                if d == 44 then
                  match bs[skipWs bs (skipWs bs p2 + 1)]? with
                  | none => .error ⟨.eofWhileParsingValue, skipWs bs (skipWs bs p2 + 1)⟩
                  | some e =>
                    if e == 34 then
                      parseMembersAt cfg bs depth start (skipWs bs (skipWs bs p2 + 1)) ((k, v) :: acc)
                    else if e == 125 then .error ⟨.trailingComma, skipWs bs (skipWs bs p2 + 1)⟩
                    else .error ⟨.keyMustBeAString, skipWs bs (skipWs bs p2 + 1)⟩
                else if d == 125 then .ok (.obj ((k, v) :: acc).reverse, skipWs bs p2 + 1)
                else .error ⟨.expectedObjectCommaOrEnd, skipWs bs p2⟩
          else .error ⟨.expectedColon, skipWs bs p1⟩ := by
  unfold parseMembersAt
  rw [dite_eq_left hsp, parseMembers]
  generalize hl : Step.lift (bs := bs) (parseString bs pos) (fun _ h => parseString_adv h) = L
  have hr : parseString bs pos = L.map Step.out := by rw [← hl, lift_out]
  rw [hr]
  cases L with
  | error e => rfl
  | ok k =>
    have := k.lt
    simp only [map_ok, Step.out]
    have g1 := skipWs_ge bs k.next
    by_cases hp : skipWs bs k.next < bs.size
    · rw [dite_eq_left hp, get_of_lt hp]
      simp only [apply_ite (Except.map Step.out), map_error]
      by_cases c58 : (bs[skipWs bs k.next] == 58) = true
      · simp only [c58, ↓reduceIte]
        unfold parseValueAtD
        cases hv : parseValueWith cfg bs depth (skipWs bs k.next + 1) with
        | error e => rfl
        | ok s =>
          have := s.lt
          have g2 := skipWs_ge bs s.next
          have g3 := skipWs_ge bs (skipWs bs s.next + 1)
          simp only [map_ok, Step.out]
          by_cases h3 : skipWs bs s.next < bs.size
          · rw [dite_eq_left h3, get_of_lt h3]
            simp only [apply_ite (Except.map Step.out), apply_dite (Except.map Step.out), map_error,
              map_ok]
            by_cases c44 : (bs[skipWs bs s.next] == 44) = true
            · simp only [c44, ↓reduceIte]
              by_cases hq : skipWs bs (skipWs bs s.next + 1) < bs.size
              · rw [dite_eq_left hq, get_of_lt hq]
                simp only [dite_eq_left (by omega : start ≤ skipWs bs (skipWs bs s.next + 1))]
              · rw [dite_eq_right hq, get_of_ge hq]
            · simp only [c44, Bool.false_eq_true, ↓reduceIte]
              rfl
          · rw [dite_eq_right h3, get_of_ge h3]; rfl
      · simp only [c58, Bool.false_eq_true, ↓reduceIte]
    · rw [dite_eq_right hp, get_of_ge hp]; rfl

end LeanJson
