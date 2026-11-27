import PEqualNP.Defs

open PEqualNP.ProofComplexity
open scoped BigOperators

namespace BlockQuota
variable {n m h : ℕ}

def fiber {a d : ℕ} (f : Fin a → Fin d) (i : Fin d) : Finset (Fin a) :=
  Finset.univ.filter (fun e => f e = i)

def lits {V : Type} [DecidableEq V] (T : Finset (Fin n)) (inj : Fin n → V) (s : Bool) :
    Clause V := T.image (fun e => (inj e,s))

def base {V : Type} [DecidableEq V] (inj : Fin n → V) (row : Fin n → Fin m)
    (col : Fin n → Fin h) (lo : Fin m → ℕ) (hi : Fin h → ℕ) : Set (Clause V) :=
  {D | (∃ i T, T ⊆ fiber row i ∧ T.card + lo i = (fiber row i).card + 1 ∧ D = lits T inj true) ∨
       (∃ j T, T ⊆ fiber col j ∧ T.card = hi j + 1 ∧ D = lits T inj false)}

theorem count_fibers {a d : ℕ} (f : Fin a → Fin d) (X : Finset (Fin a)) :
    ∑ i, ((fiber f i) ∩ X).card = X.card := by
  have eqf (i : Fin d) : fiber f i ∩ X = X.filter (fun e => f e = i) := by
    ext e
    simp [fiber, and_comm]
  simp only [eqf]
  exact (Finset.card_eq_sum_card_fiberwise (f := f) (s := X) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

theorem obstruct (row : Fin n → Fin m) (col : Fin n → Fin h)
    (lo : Fin m → ℕ) (hi : Fin h → ℕ) (bad : ∑ j, hi j < ∑ i, lo i)
    (X : Finset (Fin n)) :
    (∃ i, ((fiber row i) ∩ X).card < lo i) ∨ (∃ j, hi j < ((fiber col j) ∩ X).card) := by
  by_contra! hh
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh.1 i)
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh.2 j)
  rw [count_fibers] at hr hc
  omega

theorem unsat {V : Type} [DecidableEq V] (inj : Fin n → V) (row : Fin n → Fin m)
    (col : Fin n → Fin h) (lo : Fin m → ℕ) (hi : Fin h → ℕ)
    (hr : ∀ i, lo i ≤ (fiber row i).card) (bad : ∑ j, hi j < ∑ i, lo i) :
    ¬ Satisfiable (base inj row col lo hi) := by
  classical
  rintro ⟨a,ha⟩
  let X := Finset.univ.filter (fun e : Fin n => a (inj e) = true)
  rcases obstruct row col lo hi bad X with ⟨i,hi'⟩ | ⟨j,hj⟩
  · let R := fiber row i
    have hpart : (R \ X).card + (R ∩ X).card = R.card :=
      Finset.card_sdiff_add_card_inter _ _
    have hlo := hr i
    change (R ∩ X).card < lo i at hi'
    change lo i ≤ R.card at hlo
    have hk : R.card + 1 - lo i ≤ (R \ X).card := by omega
    obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq hk
    have hmem : lits T inj true ∈ base inj row col lo hi :=
      Or.inl ⟨i,T,(fun e he => (Finset.mem_sdiff.mp (hT he)).1),by change T.card + lo i = R.card + 1; omega,rfl⟩
    obtain ⟨l,hl,hal⟩ := ha _ hmem
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
    have hnot := (Finset.mem_sdiff.mp (hT he)).2
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hal⟩)
  · obtain ⟨T,hT,ht⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hj)
    have hmem : lits T inj false ∈ base inj row col lo hi :=
      Or.inr ⟨j,T,(fun e he => (Finset.mem_inter.mp (hT he)).1),ht,rfl⟩
    obtain ⟨l,hl,hal⟩ := ha _ hmem
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
    have hpos := (Finset.mem_filter.mp (Finset.mem_inter.mp (hT he)).2).2
    change a (inj e) = false at hal
    rw [hal] at hpos
    contradiction

end BlockQuota
