import LeanJson.Specifications.Json
import LeanJson.RepoImpl.Parse

/-!
# Proofs: reading a view

The parser reads its input through a view, `get : Nat → Option UInt8` with
length `n`. `AtV get n pos l rest` says the view holds `l ++ rest` from `pos`
on, and ends there. The lemmas turn the parser's `get` reads into facts
about `l`, so the codec proofs never index into a buffer directly. A
`ByteArray` (`Spec.At`), a list, and a view rebased at a nested value's first
byte are all views (`AtV.ofAt`, `AtV.ofList`, `AtV.shift`).
-/

namespace LeanJson

/-- From `pos` on, the view `get` (of length `n`) holds `l` and then `rest`,
and nothing after. -/
structure AtV (get : Nat → Option UInt8) (n pos : Nat) (l rest : List UInt8) : Prop where
  get_eq : ∀ k, get (pos + k) = (l ++ rest)[k]?
  len : pos + (l ++ rest).length = n

/-- A view reads nothing past its length. -/
def ViewOk (get : Nat → Option UInt8) (n : Nat) : Prop := ∀ i b, get i = some b → i < n

namespace AtV

variable {get : Nat → Option UInt8} {n pos : Nat} {l rest : List UInt8}


theorem next {b : UInt8} (h : AtV get n pos (b :: l) rest) : AtV get n (pos + 1) l rest :=
  ⟨fun k => by rw [Nat.add_assoc, Nat.add_comm 1 k, h.get_eq (k + 1)]; simp,
   by have := h.len; simp at this ⊢; omega⟩

theorem app {l₁ l₂ : List UInt8} (h : AtV get n pos (l₁ ++ l₂) rest) : AtV get n (pos + l₁.length) l₂ rest :=
  ⟨fun k => by
    rw [Nat.add_assoc, h.get_eq (l₁.length + k), List.append_assoc, List.getElem?_append_right (by omega)]
    simp,
   by have := h.len; simp at this ⊢; omega⟩

theorem app' {l₁ l₂ : List UInt8} (h : AtV get n pos l₁ (l₂ ++ rest)) : AtV get n pos (l₁ ++ l₂) rest :=
  ⟨fun k => by rw [h.get_eq k, List.append_assoc], by have := h.len; simp at this ⊢; omega⟩

theorem assoc {l₁ l₂ : List UInt8} (h : AtV get n pos (l₁ ++ l₂) rest) : AtV get n pos l₁ (l₂ ++ rest) :=
  ⟨fun k => by rw [h.get_eq k, List.append_assoc], by have := h.len; simp at this ⊢; omega⟩

theorem drop {m r : List UInt8} (h : AtV get n pos l (m ++ r)) : AtV get n (pos + l.length) m r :=
  app (app' h)

theorem re {pos' : Nat} {l' r' : List UInt8} (h : AtV get n pos l rest) (hp : pos = pos')
    (e : l ++ rest = l' ++ r') : AtV get n pos' l' r' := by
  subst hp; exact ⟨fun k => by rw [h.get_eq k, e], by rw [← e]; exact h.len⟩

theorem nil (h : AtV get n pos [] rest) : get pos = rest.head? := by
  have := h.get_eq 0; simpa [List.head?_eq_getElem?] using this

theorem le_size (h : AtV get n pos l rest) : pos + l.length ≤ n := by
  have := h.len; simp at this; omega

theorem size_eq (h : AtV get n pos l rest) : pos + l.length + rest.length = n := by
  have := h.len; simp at this; omega

/-- Past the end of the view there is nothing. -/
theorem get_end (h : AtV get n pos [] []) : get pos = none := by simpa using h.nil

/-- A view rebased at `base`: the bytes from `base + p` on. -/
theorem shift {base p : Nat} (h : AtV get n (base + p) l rest) :
    AtV (fun k => get (base + k)) (n - base) p l rest :=
  ⟨fun k => by rw [← Nat.add_assoc]; exact h.get_eq k, by have := h.len; omega⟩

theorem unshift {base p : Nat} (hb : base ≤ n) (h : AtV (fun k => get (base + k)) (n - base) p l rest) :
    AtV get n (base + p) l rest :=
  ⟨fun k => by rw [Nat.add_assoc]; exact h.get_eq k, by have := h.len; omega⟩

/-- A buffer at a position is a view. -/
theorem ofAt {bs : ByteArray} (h : Spec.At bs pos l rest) (hp : pos ≤ bs.size) :
    AtV (bv bs) bs.size pos l rest :=
  ⟨fun k => by
    have e := congrArg (·[k]?) h
    simp only [List.getElem?_drop] at e
    rw [← e]; simp only [bv]
    by_cases hk : pos + k < bs.size
    · rw [getElem?_pos bs _ hk, List.getElem?_eq_getElem (by simpa using hk)]
      simp [ByteArray.getElem_eq_getElem_data]
    · rw [getElem?_neg bs _ hk, List.getElem?_eq_none (by simp; omega)],
   by
    have e := congrArg List.length h
    simp only [List.length_drop, Array.length_toList] at e
    have : bs.data.size = bs.size := rfl
    omega⟩

/-- A list is a view of itself. -/
theorem ofList (l rest : List UInt8) : AtV (lv (l ++ rest)) (l ++ rest).length 0 l rest :=
  ⟨fun k => by simp [lv], by simp⟩

end AtV

theorem AtV.get {g : Nat → Option UInt8} {m pos : Nat} {b : UInt8} {l rest : List UInt8}
    (h : AtV g m pos (b :: l) rest) : g pos = some b := by
  simpa using h.get_eq 0

theorem AtV.lt {g : Nat → Option UInt8} {m pos : Nat} {b : UInt8} {l rest : List UInt8}
    (h : AtV g m pos (b :: l) rest) : pos < m := by
  have := h.le_size; simp at this; omega

theorem viewOk_lv (L : List UInt8) : ViewOk (lv L) L.length := by
  intro i b h
  by_cases hi : i < L.length
  · exact hi
  · simp [lv, List.getElem?_eq_none (Nat.le_of_not_lt hi)] at h

theorem viewOk_bv (bs : ByteArray) : ViewOk (bv bs) bs.size := by
  intro i b h
  by_cases hi : i < bs.size
  · exact hi
  · simp [bv, getElem?_neg bs i hi] at h

theorem ViewOk.shift {get : Nat → Option UInt8} {n : Nat} (h : ViewOk get n) (base : Nat) :
    ViewOk (fun k => get (base + k)) (n - base) := by
  intro i b hb; have := h _ _ hb; omega

/-- The cursor moved forward from `p` to `q`, and if it moved at all it stayed
within the view. -/
def Adv (n p q : Nat) : Prop := p ≤ q ∧ (p < q → q ≤ n)

theorem Adv.refl (n p : Nat) : Adv n p p := ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem Adv.trans {n p q r : Nat} (h1 : Adv n p q) (h2 : Adv n q r) : Adv n p r := by
  obtain ⟨a1, b1⟩ := h1; obtain ⟨a2, b2⟩ := h2
  refine ⟨Nat.le_trans a1 a2, fun h => ?_⟩
  by_cases hqr : q < r
  · exact b2 hqr
  · have : q = r := by omega
    subst this; exact b1 h

theorem Adv.of_lt {n p q : Nat} (h1 : p ≤ q) (h2 : q ≤ n) : Adv n p q := ⟨h1, fun _ => h2⟩

theorem Adv.step {get : Nat → Option UInt8} {n p : Nat} {b : UInt8} (hv : ViewOk get n)
    (h : get p = some b) : Adv n p (p + 1) :=
  ⟨by omega, fun _ => hv _ _ h⟩

end LeanJson
