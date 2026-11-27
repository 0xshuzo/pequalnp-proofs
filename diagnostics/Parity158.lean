import PEqualNP.Defs

namespace Parity158Aux

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- resolution lines, newest first; a hint (i, j, v): the premises are entries i and j of the tail, pivot v
def chkR {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => true
  | (R, none) :: t => ax R && chkR ax t
  | (R, some (i, j, v)) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((v, true) ∈ (t.map Prod.fst).getD i ∅ ∧ (v, false) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (v, true) ∪ ((t.map Prod.fst).getD j ∅).erase (v, false)) &&
      chkR ax t

theorem chkR_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkR ax l = true → IsDerivation F (l.map Prod.fst)
  | [], _ => IsDerivation.nil
  | (R, none) :: t, h => by
    simp only [chkR, Bool.and_eq_true] at h
    exact IsDerivation.ax (chkR_sound F ax hax t h.2) (hax R h.1)
  | (R, some (i, j, v)) :: t, h => by
    simp only [chkR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsDerivation.res (chkR_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨v, h1, h2, h3⟩

-- Res(lin): the assignment check of a weakening runs over the variables vs only
def ext {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (b : Bool) : V → Bool :=
  fun w => if w = v then b else a w

def allA {V : Type} [DecidableEq V] : List V → List (V → Bool)
  | [] => [fun _ => false]
  | v :: vs => (allA vs).flatMap (fun a => [ext a v false, ext a v true])

theorem allA_cover {V : Type} [DecidableEq V] :
    ∀ (vs : List V) (a : V → Bool), ∃ b ∈ allA vs, ∀ v ∈ vs, b v = a v
  | [], a => ⟨fun _ => false, by simp [allA], by simp⟩
  | v :: vs, a => by
    obtain ⟨b, hb, hba⟩ := allA_cover vs a
    refine ⟨ext b v (a v), ?_, ?_⟩
    · simp only [allA, List.mem_flatMap]
      exact ⟨b, hb, by cases a v <;> simp⟩
    · intro w hw
      simp only [ext]
      split_ifs with hwv
      · rw [hwv]
      · exact hba w (by simpa [hwv] using hw)

def satB {V : Type} (a : V → Bool) (C : LinClause V) : Bool :=
  decide (∃ q ∈ C, decide (Odd (q.1.filter (fun v => a v = true)).card) = q.2)

theorem satB_iff {V : Type} (a : V → Bool) (C : LinClause V) :
    satB a C = true ↔ LinClauseSat a C := by
  unfold satB LinClauseSat LinEqSat
  simp only [decide_eq_true_eq]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rcases q with ⟨f, b⟩
  cases b <;> simp

theorem sat_congr {V : Type} (a b : V → Bool) (C : LinClause V) (vs : List V)
    (hv : ∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) (hab : ∀ v ∈ vs, b v = a v) :
    LinClauseSat b C ↔ LinClauseSat a C := by
  unfold LinClauseSat LinEqSat
  refine exists_congr fun q => and_congr_right fun hq => ?_
  rw [Finset.filter_congr (fun v hv' => by rw [hab v (hv q hq v hv')])]

def wkB {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V) : Bool :=
  decide (∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) && decide (∀ q ∈ D, ∀ v ∈ q.1, v ∈ vs) &&
    (allA vs).all (fun a => !satB a C || satB a D)

theorem wkB_sound {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V)
    (h : wkB vs C D = true) : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  simp only [wkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hC, hD⟩, hall⟩ := h
  intro a ha
  obtain ⟨b, hb, hba⟩ := allA_cover vs a
  have hh := hall b hb
  rw [← sat_congr a b D vs hD hba]
  rw [← sat_congr a b C vs hC hba, ← satB_iff] at ha
  rw [← satB_iff]
  simpa [ha] using hh

inductive Step (V : Type) where
  | ax : Clause V → Step V
  | rs : ℕ → ℕ → Finset V → Step V
  | wk : ℕ → List V → Step V

def chkL {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (LinClause V × Step V) → Bool
  | [] => true
  | (R, .ax C) :: t => ax C && decide (linOfClause C = R) && chkL ax t
  | (R, .rs i j f) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((f, false) ∈ (t.map Prod.fst).getD i ∅ ∧ (f, true) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (f, false) ∪ ((t.map Prod.fst).getD j ∅).erase (f, true)) &&
      chkL ax t
  | (R, .wk i vs) :: t => decide (i < t.length) && wkB vs ((t.map Prod.fst).getD i ∅) R && chkL ax t

theorem chkL_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkL ax l = true → IsLinDerivation ((fun C => linOfClause C) '' F) (l.map Prod.fst)
  | [], _ => IsLinDerivation.nil
  | (R, .ax C) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, ht⟩ := h
    exact IsLinDerivation.ax (chkL_sound F ax hax t ht) ⟨C, hax C h1, h2⟩
  | (R, .rs i j f) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsLinDerivation.res (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨f, h1, h2, h3⟩
  | (R, .wk i vs) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h1⟩, ht⟩ := h
    exact IsLinDerivation.weak (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (wkB_sound vs _ R h1)

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def bitF (c0 c1 : Bool) : Fin 2 → Bool := fun b => if b.val = 0 then c0 else c1

def axBPHP (m : ℕ) (C : Clause (Fin m × Fin 2)) : Bool :=
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ c0 : Bool, ∃ c1 : Bool, i ≠ i' ∧
    C = Finset.univ.image (fun b : Fin 2 => ((i, b), !bitF c0 c1 b)) ∪
        Finset.univ.image (fun b : Fin 2 => ((i', b), !bitF c0 c1 b)))

theorem axBPHP_sound (m : ℕ) : ∀ C, axBPHP m C = true → C ∈ BPHP m 2 := by
  intro C h
  simp only [axBPHP, decide_eq_true_eq] at h
  obtain ⟨i, i', c0, c1, hne, hC⟩ := h
  exact ⟨i, i', bitF c0 c1, hne, hC⟩

def cert : List (LinClause (Fin 5 × Fin 4) × Step (Fin 5 × Fin 4)) := [

  (∅, .rs 0 19 {(4, 3)}),
  ({({(4, 3)}, false)}, .rs 3 0 {(1, 3)}),
  ({({(1, 3)}, true), ({(4, 3)}, false)}, .rs 3 0 {(0, 3)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(4, 3)}, false)}, .rs 3 0 {(3, 3)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(3, 3)}, true), ({(4, 3)}, false)}, .rs 3 4 {(2, 3)}),
  ({({(1, 3)}, false), ({(4, 3)}, false)}, .ax {((1, 3), false), ((4, 3), false)}),
  ({({(0, 3)}, false), ({(4, 3)}, false)}, .ax {((0, 3), false), ((4, 3), false)}),
  ({({(3, 3)}, false), ({(4, 3)}, false)}, .ax {((3, 3), false), ((4, 3), false)}),
  ({({(2, 3)}, false), ({(4, 3)}, false)}, .ax {((2, 3), false), ((4, 3), false)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 3)}, true)}, .rs 0 3 {(3, 2)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 2)}, false)}, .rs 100 0 {(1, 2)}),
  ({({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 2)}, false)}, .rs 100 0 {(0, 2)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 2)}, false)}, .rs 100 20 {(2, 2)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .rs 0 3 {(3, 1)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 1)}, false)}, .rs 114 0 {(1, 1)}),
  ({({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 1)}, false)}, .rs 114 0 {(0, 1)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 1)}, false)}, .rs 114 40 {(2, 1)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 1)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .rs 0 136 {(3, 0)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 0)}, false)}, .rs 60 0 {(0, 0), (1, 0)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 3)}, true), ({(3, 0)}, false), ({(0, 0), (1, 0)}, true)}, .rs 63 81 {(2, 0)}),
  ({({(4, 3)}, true)}, .rs 0 23 {(4, 2)}),
  ({({(4, 2)}, false)}, .rs 3 0 {(1, 2)}),
  ({({(1, 2)}, true), ({(4, 2)}, false)}, .rs 3 0 {(0, 2)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(4, 2)}, false)}, .rs 3 0 {(3, 2)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(3, 2)}, true), ({(4, 2)}, false)}, .rs 3 4 {(2, 2)}),
  ({({(1, 2)}, false), ({(4, 2)}, false)}, .ax {((1, 2), false), ((4, 2), false)}),
  ({({(0, 2)}, false), ({(4, 2)}, false)}, .ax {((0, 2), false), ((4, 2), false)}),
  ({({(3, 2)}, false), ({(4, 2)}, false)}, .ax {((3, 2), false), ((4, 2), false)}),
  ({({(2, 2)}, false), ({(4, 2)}, false)}, .ax {((2, 2), false), ((4, 2), false)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 2)}, true)}, .rs 0 7 {(3, 3)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 3)}, false)}, .rs 67 0 {(1, 3)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 2)}, true), ({(3, 3)}, false)}, .rs 67 0 {(0, 3)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 2)}, true), ({(3, 3)}, false)}, .rs 67 0 {(2, 3)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 2)}, true), ({(2, 3)}, true)}, .rs 0 2 {(2, 1)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 1)}, false)}, .rs 88 0 {(1, 1)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 1)}, false)}, .rs 88 32 {(0, 1)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 1)}, true), ({(2, 2)}, true), ({(2, 3)}, true)}, .rs 34 80 {(0, 0), (1, 0)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .rs 0 3 {(3, 1)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 1)}, false)}, .rs 90 0 {(1, 1)}),
  ({({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 1)}, false)}, .rs 90 0 {(0, 1)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 1)}, false)}, .rs 90 24 {(2, 1)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 1)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .rs 0 112 {(3, 0)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 0)}, false)}, .rs 36 0 {(0, 0), (1, 0)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 2)}, true), ({(3, 0)}, false), ({(0, 0), (1, 0)}, true)}, .rs 39 70 {(2, 0)}),
  ({({(4, 2)}, true), ({(4, 3)}, true)}, .rs 0 39 {(4, 1)}),
  ({({(4, 1)}, false)}, .rs 3 0 {(1, 1)}),
  ({({(1, 1)}, true), ({(4, 1)}, false)}, .rs 3 0 {(0, 1)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(4, 1)}, false)}, .rs 3 0 {(3, 1)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(3, 1)}, true), ({(4, 1)}, false)}, .rs 3 4 {(2, 1)}),
  ({({(1, 1)}, false), ({(4, 1)}, false)}, .ax {((1, 1), false), ((4, 1), false)}),
  ({({(0, 1)}, false), ({(4, 1)}, false)}, .ax {((0, 1), false), ((4, 1), false)}),
  ({({(3, 1)}, false), ({(4, 1)}, false)}, .ax {((3, 1), false), ((4, 1), false)}),
  ({({(2, 1)}, false), ({(4, 1)}, false)}, .ax {((2, 1), false), ((4, 1), false)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 1)}, true)}, .rs 0 7 {(3, 3)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 3)}, false)}, .rs 43 0 {(1, 3)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 1)}, true), ({(3, 3)}, false)}, .rs 43 0 {(0, 3)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 1)}, true), ({(3, 3)}, false)}, .rs 43 0 {(2, 3)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 1)}, true), ({(2, 3)}, true)}, .rs 0 2 {(2, 2)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 2)}, false)}, .rs 84 0 {(1, 2)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 2)}, false)}, .rs 84 8 {(0, 2)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 1)}, true), ({(2, 2)}, true), ({(2, 3)}, true)}, .rs 10 76 {(0, 0), (1, 0)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 1)}, true), ({(3, 3)}, true)}, .rs 0 14 {(3, 2)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 2)}, false)}, .rs 48 0 {(1, 2)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 1)}, true), ({(3, 2)}, false)}, .rs 48 0 {(0, 2)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 1)}, true), ({(3, 2)}, false)}, .rs 48 0 {(2, 2)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 1)}, true), ({(2, 2)}, true)}, .rs 0 4 {(2, 3)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 3)}, false)}, .rs 68 0 {(1, 3)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 3)}, false)}, .rs 68 0 {(0, 3)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true)}, .rs 0 87 {(1, 0)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(0, 3)}, true), ({(1, 0)}, false)}, .rs 82 87 {(0, 0)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 1)}, true), ({(2, 2)}, true), ({(2, 3)}, true)}, .rs 0 74 {(0, 0), (1, 0)}),
  ({({(2, 1)}, true), ({(2, 2)}, true), ({(2, 3)}, true), ({(0, 0), (1, 0)}, false)}, .rs 0 83 {(2, 0)}),
  ({({(2, 0)}, false), ({(0, 0), (1, 0)}, false)}, .rs 2 0 {(0, 0)}),
  ({({(0, 0)}, true), ({(2, 0)}, false), ({(0, 0), (1, 0)}, false)}, .wk 0 [(0, 0), (1, 0), (2, 0)]),
  ({({(1, 0)}, false), ({(2, 0)}, false)}, .ax {((1, 0), false), ((2, 0), false)}),
  ({({(0, 0)}, false), ({(2, 0)}, false)}, .ax {((0, 0), false), ((2, 0), false)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 1)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .rs 0 77 {(3, 0)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 0)}, false)}, .rs 1 0 {(0, 0), (1, 0)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 1)}, true), ({(3, 0)}, false), ({(0, 0), (1, 0)}, true)}, .rs 4 53 {(2, 0)}),
  ({({(3, 0)}, false), ({(0, 0), (1, 0)}, false)}, .rs 2 0 {(0, 0)}),
  ({({(0, 0)}, true), ({(3, 0)}, false), ({(0, 0), (1, 0)}, false)}, .wk 0 [(0, 0), (1, 0), (3, 0)]),
  ({({(1, 0)}, false), ({(3, 0)}, false)}, .ax {((1, 0), false), ((3, 0), false)}),
  ({({(0, 0)}, false), ({(3, 0)}, false)}, .ax {((0, 0), false), ((3, 0), false)}),
  ({({(2, 0)}, false), ({(3, 0)}, false)}, .ax {((2, 0), false), ((3, 0), false)}),
  ({({(4, 1)}, true), ({(4, 2)}, true), ({(4, 3)}, true)}, .rs 0 68 {(4, 0)}),
  ({({(4, 0)}, false)}, .rs 2 0 {(0, 0), (1, 0)}),
  ({({(4, 0)}, false), ({(0, 0), (1, 0)}, true)}, .rs 5 0 {(3, 0)}),
  ({({(3, 0)}, true), ({(4, 0)}, false), ({(0, 0), (1, 0)}, true)}, .rs 5 6 {(2, 0)}),
  ({({(4, 0)}, false), ({(0, 0), (1, 0)}, false)}, .rs 2 0 {(0, 0)}),
  ({({(0, 0)}, true), ({(4, 0)}, false), ({(0, 0), (1, 0)}, false)}, .wk 0 [(0, 0), (1, 0), (4, 0)]),
  ({({(1, 0)}, false), ({(4, 0)}, false)}, .ax {((1, 0), false), ((4, 0), false)}),
  ({({(0, 0)}, false), ({(4, 0)}, false)}, .ax {((0, 0), false), ((4, 0), false)}),
  ({({(3, 0)}, false), ({(4, 0)}, false)}, .ax {((3, 0), false), ((4, 0), false)}),
  ({({(2, 0)}, false), ({(4, 0)}, false)}, .ax {((2, 0), false), ((4, 0), false)}),
  ({({(2, 0)}, true), ({(3, 0)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 12 {(3, 3)}),
  ({({(2, 0)}, true), ({(3, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(1, 3)}),
  ({({(1, 3)}, true), ({(2, 0)}, true), ({(3, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(0, 3)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 0)}, true), ({(3, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 3 {(2, 3)}),
  ({({(1, 3)}, false), ({(3, 3)}, false)}, .ax {((1, 3), false), ((3, 3), false)}),
  ({({(0, 3)}, false), ({(3, 3)}, false)}, .ax {((0, 3), false), ((3, 3), false)}),
  ({({(2, 3)}, false), ({(3, 3)}, false)}, .ax {((2, 3), false), ((3, 3), false)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 0)}, true), ({(2, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 2 {(2, 2)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 40 0 {(1, 2)}),
  ({({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 40 13 {(0, 2)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 0)}, true), ({(2, 2)}, true), ({(2, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 50 {(2, 1)}),
  ({({(0, 3)}, true), ({(1, 3)}, true), ({(2, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 17 0 {(1, 1)}),
  ({({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 17 30 {(0, 1)}),
  ({({(2, 0)}, true), ({(3, 0)}, true), ({(3, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 17 {(3, 2)}),
  ({({(2, 0)}, true), ({(3, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(1, 2)}),
  ({({(1, 2)}, true), ({(2, 0)}, true), ({(3, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(0, 2)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 0)}, true), ({(3, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 3 {(2, 2)}),
  ({({(1, 2)}, false), ({(3, 2)}, false)}, .ax {((1, 2), false), ((3, 2), false)}),
  ({({(0, 2)}, false), ({(3, 2)}, false)}, .ax {((0, 2), false), ((3, 2), false)}),
  ({({(2, 2)}, false), ({(3, 2)}, false)}, .ax {((2, 2), false), ((3, 2), false)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 0)}, true), ({(2, 2)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 5 {(2, 3)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 19 0 {(1, 3)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(2, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 19 0 {(0, 3)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 30 {(1, 1)}),
  ({({(0, 2)}, true), ({(0, 3)}, true), ({(1, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 0 31 {(0, 1)}),
  ({({(0, 1)}, false), ({(1, 1)}, false)}, .ax {((0, 1), false), ((1, 1), false)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 0)}, true), ({(2, 2)}, true), ({(2, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 34 {(2, 1)}),
  ({({(0, 2)}, true), ({(1, 2)}, true), ({(2, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 0 {(1, 1)}),
  ({({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 22 {(0, 1)}),
  ({({(1, 1)}, false), ({(2, 1)}, false)}, .ax {((1, 1), false), ((2, 1), false)}),
  ({({(0, 1)}, false), ({(2, 1)}, false)}, .ax {((0, 1), false), ((2, 1), false)}),
  ({({(2, 0)}, true), ({(3, 0)}, true), ({(3, 2)}, true), ({(3, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 28 {(3, 1)}),
  ({({(2, 0)}, true), ({(3, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(1, 1)}),
  ({({(1, 1)}, true), ({(2, 0)}, true), ({(3, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 0 {(0, 1)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 0)}, true), ({(3, 1)}, false), ({(0, 0), (1, 0)}, true)}, .rs 2 3 {(2, 1)}),
  ({({(1, 1)}, false), ({(3, 1)}, false)}, .ax {((1, 1), false), ((3, 1), false)}),
  ({({(0, 1)}, false), ({(3, 1)}, false)}, .ax {((0, 1), false), ((3, 1), false)}),
  ({({(2, 1)}, false), ({(3, 1)}, false)}, .ax {((2, 1), false), ((3, 1), false)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 0)}, true), ({(2, 1)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 7 {(2, 3)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 0 {(1, 3)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(2, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 2 {(0, 3)}),
  ({({(1, 3)}, false), ({(2, 3)}, false)}, .ax {((1, 3), false), ((2, 3), false)}),
  ({({(0, 3)}, false), ({(2, 3)}, false)}, .ax {((0, 3), false), ((2, 3), false)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 1)}, true), ({(1, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 10 {(1, 2)}),
  ({({(0, 1)}, true), ({(0, 3)}, true), ({(1, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 0 11 {(0, 2)}),
  ({({(0, 2)}, false), ({(1, 2)}, false)}, .ax {((0, 2), false), ((1, 2), false)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 0)}, true), ({(2, 1)}, true), ({(2, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 14 {(2, 2)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(2, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 0 {(1, 2)}),
  ({({(0, 1)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(2, 2)}, false), ({(0, 0), (1, 0)}, true)}, .rs 1 2 {(0, 2)}),
  ({({(1, 2)}, false), ({(2, 2)}, false)}, .ax {((1, 2), false), ((2, 2), false)}),
  ({({(0, 2)}, false), ({(2, 2)}, false)}, .ax {((0, 2), false), ((2, 2), false)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 2 {(1, 3)}),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(1, 3)}, false), ({(0, 0), (1, 0)}, true)}, .rs 0 3 {(0, 3)}),
  ({({(0, 3)}, false), ({(1, 3)}, false)}, .ax {((0, 3), false), ((1, 3), false)}),
  ({({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 7 {(1, 0)}),
  ({({(1, 0)}, false), ({(0, 0), (1, 0)}, true)}, .wk 2 [(0, 0), (1, 0)]),
  ({({(0, 1)}, true), ({(0, 2)}, true), ({(0, 3)}, true), ({(0, 0), (1, 0)}, true)}, .rs 0 6 {(0, 0)}),
  ({({(0, 0)}, false), ({(0, 0), (1, 0)}, true)}, .wk 0 [(0, 0), (1, 0)]),
  ({({(0, 0)}, false), ({(1, 0)}, false)}, .ax {((0, 0), false), ((1, 0), false)}),
  ({({(4, 0)}, true), ({(4, 1)}, true), ({(4, 2)}, true), ({(4, 3)}, true)}, .ax {((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)}),
  ({({(3, 0)}, true), ({(3, 1)}, true), ({(3, 2)}, true), ({(3, 3)}, true)}, .ax {((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}),
  ({({(2, 0)}, true), ({(2, 1)}, true), ({(2, 2)}, true), ({(2, 3)}, true)}, .ax {((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}),
  ({({(1, 0)}, true), ({(1, 1)}, true), ({(1, 2)}, true), ({(1, 3)}, true)}, .ax {((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}),
  ({({(0, 0)}, true), ({(0, 1)}, true), ({(0, 2)}, true), ({(0, 3)}, true)}, .ax {((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)})]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkL (axPHP 5 4) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : LinClause (Fin 5 × Fin 4)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ 158 := by decide +kernel

end Parity158Aux

theorem Parity158Aux.bound : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 158 := by
  exact ⟨Parity158Aux.cert.map Prod.fst, ⟨Parity158Aux.chkL_sound _ (Parity158Aux.axPHP 5 4) (Parity158Aux.axPHP_sound 5 4) _ Parity158Aux.hc, Parity158Aux.hm⟩, Parity158Aux.hl⟩
