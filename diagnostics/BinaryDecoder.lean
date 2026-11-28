import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx177Binary

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

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
  | ax : Step V
  | rs : ℕ → ℕ → Finset V → Step V
  | wk : ℕ → List V → Step V

def chkL {V : Type} [DecidableEq V] (ax : LinClause V → Bool) :
    List (LinClause V × Step V) → Bool
  | [] => true
  | (R, .ax) :: t => ax R && chkL ax t
  | (R, .rs i j f) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((f, false) ∈ (t.map Prod.fst).getD i ∅ ∧ (f, true) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (f, false) ∪ ((t.map Prod.fst).getD j ∅).erase (f, true)) &&
      chkL ax t
  | (R, .wk i vs) :: t => decide (i < t.length) && wkB vs ((t.map Prod.fst).getD i ∅) R && chkL ax t

theorem chkL_sound {V : Type} [DecidableEq V] (F : Set (LinClause V)) (ax : LinClause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkL ax l = true → IsLinDerivation F (l.map Prod.fst)
  | [], _ => IsLinDerivation.nil
  | (R, .ax) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    exact IsLinDerivation.ax (chkL_sound F ax hax t h.2) (hax R h.1)
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


abbrev V := Fin 8
def bank : Finset (LinClause V) := {{({0, 2}, true), ({1, 3}, true)}, {({0, 4}, true), ({1, 5}, true)}, {({0, 6}, true), ({1, 7}, true)}, {({0}, true), ({1}, true)}, {({2, 4}, true), ({3, 5}, true)}, {({2, 6}, true), ({3, 7}, true)}, {({2}, true), ({3}, true)}, {({4, 6}, true), ({5, 7}, true)}, {({4}, true), ({5}, true)}, {({6}, true), ({7}, true)}}

def cert : List (LinClause V × Step V) := [
  (∅, .rs 0 28 {2}),
  ({({2}, false)}, .rs 0 14 {6}),
  ({({6}, false), ({2}, false)}, .rs 1 0 {3, 7}),
  ({({6}, false), ({2}, false), ({3, 7}, true)}, .wk 47 [2, 3, 6, 7]),
  ({({3, 7}, false), ({6}, false), ({2}, false)}, .rs 3 0 {4, 6}),
  ({({3, 7}, false), ({6}, false), ({2}, false), ({4, 6}, true)}, .rs 1 0 {4, 5, 6, 7}),
  ({({4, 6}, true), ({4, 5, 6, 7}, true)}, .wk 42 [4, 5, 6, 7]),
  ({({4, 5, 6, 7}, false), ({3, 7}, false), ({6}, false), ({2}, false), ({4, 6}, true)}, .wk 44 [2, 3, 4, 5, 6, 7]),
  ({({3, 7}, false), ({4, 6}, false), ({6}, false), ({2}, false)}, .rs 0 5 {0, 6}),
  ({({4, 6}, false), ({0, 6}, false), ({6}, false)}, .rs 0 3 {1, 5}),
  ({({4, 6}, false), ({0, 6}, false), ({6}, false), ({1, 5}, false)}, .rs 1 0 {0, 1}),
  ({({0, 6}, false), ({6}, false), ({0, 1}, true)}, .wk 41 [0, 1, 6]),
  ({({4, 6}, false), ({0, 6}, false), ({6}, false), ({1, 5}, false), ({0, 1}, false)}, .wk 35 [0, 1, 4, 5, 6]),
  ({({4, 6}, false), ({0, 6}, false), ({1, 5}, true)}, .wk 10 [0, 1, 4, 5, 6]),
  ({({3, 7}, false), ({6}, false), ({2}, false), ({0, 6}, true)}, .rs 0 39 {1, 7}),
  ({({3, 7}, false), ({1, 7}, false), ({6}, false), ({2}, false), ({0, 6}, true)}, .wk 40 [0, 1, 2, 3, 6, 7]),
  ({({2}, false), ({6}, true)}, .rs 3 0 {0, 6}),
  ({({6}, true), ({0, 6}, true)}, .rs 0 29 {7}),
  ({({7}, false), ({6}, true), ({0, 6}, true)}, .rs 0 35 {1, 7}),
  ({({1, 7}, false), ({7}, false), ({6}, true), ({0, 6}, true)}, .wk 33 [0, 1, 6, 7]),
  ({({0, 6}, false), ({2}, false), ({6}, true)}, .rs 1 0 {1, 3}),
  ({({0, 6}, false), ({2}, false), ({1, 3}, true), ({6}, true)}, .wk 34 [0, 1, 2, 3, 6]),
  ({({0, 6}, false), ({1, 3}, false), ({2}, false), ({6}, true)}, .rs 0 3 {4, 6}),
  ({({4, 6}, false), ({0, 6}, false), ({1, 3}, false), ({2}, false), ({6}, true)}, .rs 1 0 {0, 1, 4, 5}),
  ({({4, 6}, false), ({0, 6}, false), ({0, 1, 4, 5}, true)}, .wk 30 [0, 1, 4, 5, 6]),
  ({({4, 6}, false), ({0, 6}, false), ({0, 1, 4, 5}, false), ({1, 3}, false), ({2}, false), ({6}, true)}, .wk 26 [0, 1, 2, 3, 4, 5, 6]),
  ({({6}, true), ({4, 6}, true)}, .rs 0 20 {7}),
  ({({7}, false), ({6}, true), ({4, 6}, true)}, .rs 0 21 {5, 7}),
  ({({5, 7}, false), ({7}, false), ({6}, true), ({4, 6}, true)}, .wk 19 [4, 5, 6, 7]),
  ({({2}, true)}, .rs 3 0 {0}),
  ({({0}, true), ({2}, true)}, .rs 0 19 {3}),
  ({({3}, false), ({0}, true), ({2}, true)}, .rs 0 21 {1}),
  ({({3}, false), ({1}, false), ({0}, true), ({2}, true)}, .wk 23 [0, 1, 2, 3]),
  ({({0}, false), ({2}, true)}, .rs 3 0 {2, 6}),
  ({({2}, true), ({2, 6}, true)}, .rs 0 16 {3, 7}),
  ({({3, 7}, false), ({2}, true), ({2, 6}, true)}, .rs 0 14 {3}),
  ({({3, 7}, false), ({3}, false), ({2}, true), ({2, 6}, true)}, .wk 10 [2, 3, 6, 7]),
  ({({2, 6}, false), ({0}, false), ({2}, true)}, .rs 1 0 {0, 1, 6, 7}),
  ({({2, 6}, false), ({0}, false), ({2}, true), ({0, 1, 6, 7}, true)}, .wk 15 [0, 1, 2, 6, 7]),
  ({({0, 1, 6, 7}, false), ({2, 6}, false), ({0}, false), ({2}, true)}, .rs 4 0 {2, 4}),
  ({({2}, true), ({2, 4}, true)}, .rs 1 0 {5}),
  ({({2}, true), ({2, 4}, true), ({5}, true)}, .wk 6 [2, 4, 5]),
  ({({5}, false), ({2}, true), ({2, 4}, true)}, .rs 0 9 {3, 5}),
  ({({3, 5}, false), ({5}, false), ({2}, true)}, .wk 6 [2, 3, 5]),
  ({({0, 1, 6, 7}, false), ({2, 6}, false), ({2, 4}, false), ({0}, false), ({2}, true)}, .rs 1 0 {1, 5}),
  ({({2, 4}, false), ({0}, false), ({2}, true), ({1, 5}, true)}, .wk 9 [0, 1, 2, 4, 5]),
  ({({0, 1, 6, 7}, false), ({2, 6}, false), ({1, 5}, false), ({2, 4}, false), ({0}, false), ({2}, true)}, .wk 2 [0, 1, 2, 4, 5, 6, 7]),
  ({({6}, true), ({7}, true)}, .ax),
  ({({4}, true), ({5}, true)}, .ax),
  ({({4, 6}, true), ({5, 7}, true)}, .ax),
  ({({2}, true), ({3}, true)}, .ax),
  ({({2, 6}, true), ({3, 7}, true)}, .ax),
  ({({2, 4}, true), ({3, 5}, true)}, .ax),
  ({({0}, true), ({1}, true)}, .ax),
  ({({0, 6}, true), ({1, 7}, true)}, .ax),
  ({({0, 4}, true), ({1, 5}, true)}, .ax),
  ({({0, 2}, true), ({1, 3}, true)}, .ax)]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : chkL (fun q => decide (q ∈ bank)) cert = true := by decide +kernel

theorem refuteBank : ∃ p : List (LinClause V), IsLinDerivation (↑bank : Set (LinClause V)) p ∧
    ∅ ∈ p ∧ p.length = 57 := by
  refine ⟨cert.map Prod.fst, chkL_sound (↑bank : Set (LinClause V)) _ ?_ _ checked, ?_, ?_⟩
  · intro C h
    exact of_decide_eq_true h
  · exact List.mem_cons_self
  · rfl
end PEqualNP.Outside.Pcx177Binary
