import Mathlib

namespace Matching1768
variable {k : ℕ}

abbrev Input (k : ℕ) := Fin k → Bool → Bool
abbrev Cover (k : ℕ) := Fin k → Bool
def matching (x : Input k) : Prop := ∃ i, x i false = true ∧ x i true = true
def clause (x : Input k) (c : Cover k) : Prop := ∃ i, x i (c i) = true
def leftCover : Cover k := fun _ => false
def rest (x : Input k) : Prop := ∀ c : Cover k, c ≠ leftCover → clause x c
def complementInput (c : Cover k) : Input k := fun i b => decide (b ≠ c i)
def pair (i : Fin k) : Input k := fun j _ => decide (j = i)
def unit (i : Fin k) (b : Bool) : Input k := fun j t => decide (j = i ∧ t = b)

lemma clause_on_pair (i : Fin k) (c : Cover k) : clause (pair i) c :=
  ⟨i,by simp [pair]⟩

lemma omit_iff (c d : Cover k) : clause (complementInput c) d ↔ d ≠ c := by
  constructor
  · rintro ⟨i,h⟩ eq
    subst d
    simpa [complementInput] using h
  · intro h
    by_contra hc
    apply h
    funext i
    by_contra neq
    exact hc ⟨i,by simpa [complementInput] using neq⟩

lemma omit_independent (c : Cover k) : ¬ matching (complementInput c) := by
  rintro ⟨i,h0,h1⟩
  cases h : c i <;> simp [complementInput,h] at h0 h1

lemma last_and (x : Input k) : rest x ↔ matching x ∨ ∀ i, x i true = true := by
  constructor
  · intro hr
    by_cases hm : matching x
    · exact Or.inl hm
    right
    intro i
    by_contra hi
    let c : Cover k := fun j => !x j true
    have hc : c ≠ leftCover := by
      intro eq
      have ee := congrFun eq i
      simp [c,leftCover,Bool.eq_false_iff.mpr hi] at ee
    obtain ⟨j,hj⟩ := hr c hc
    cases h : x j true with
    | false => simp [c,h] at hj
    | true =>
      have h0 : x j false = true := by simpa [c,h] using hj
      exact hm ⟨j,h0,h⟩
  · rintro (⟨i,h0,h1⟩ | all) c hc
    · refine ⟨i,?_⟩
      cases h : c i <;> assumption
    · by_contra h
      apply hc
      funext i
      cases e : c i with
      | false => rfl
      | true => exact (h ⟨i,by rw [e]; exact all i⟩).elim

lemma exact (x : Input k) : (clause x leftCover ∧ rest x) ↔ matching x := by
  rw [last_and]
  constructor
  · rintro ⟨⟨i,hi⟩,h | h⟩
    · exact h
    · exact ⟨i,hi,h i⟩
  · rintro ⟨i,h0,h1⟩
    exact ⟨⟨i,h0⟩,Or.inl ⟨i,h0,h1⟩⟩

lemma sole_match (i : Fin k) (c : Cover k) (j : Fin k) :
    pair i j (c j) = true ↔ j=i := by simp [pair]

lemma rest_rejects_unit (hk : 2 ≤ k) (i : Fin k) (b : Bool) : ¬ rest (unit i b) := by
  rw [last_and]
  rintro (⟨j,h0,h1⟩ | all)
  · cases b <;> simp [unit] at h0 h1
  · have many : 1 < (Finset.univ : Finset (Fin k)).card := by simpa using (show 1 < k by omega)
    obtain ⟨a,_,d,_,had⟩ := Finset.one_lt_card.mp many
    have ha := (of_decide_eq_true (all a)).1
    have hd := (of_decide_eq_true (all d)).1
    exact had (ha.trans hd.symm)

end Matching1768
