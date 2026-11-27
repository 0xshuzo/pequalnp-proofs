import PEqualNP.Defs

namespace Lpcx178AffineMerge
open PEqualNP.ProofComplexity

abbrev Cell := Fin 5 × Fin 4
def zero : Cell → Bool := fun _ => false
def single (v : Cell) : Cell → Bool := fun u => decide (u = v)
def clear (x : Cell → Bool) : Prop :=
  ∀ i j : Cell, i.2 = j.2 → x i = true → x j = true → i = j

theorem zeroClear : clear zero := by
  intro i j _ h
  simp [zero] at h

theorem singleClear (v : Cell) : clear (single v) := by
  intro i j _ hi hj
  exact (of_decide_eq_true hi).trans (of_decide_eq_true hj).symm

theorem singleOdd (f : Finset Cell) {v : Cell} (h : v ∈ f) :
    LinEqSat (single v) (f,true) := by
  have e : f.filter (fun u => single v u = true) = {v} := by
    ext u
    by_cases uv : u = v <;> simp_all [single]
  change Odd (f.filter (fun u => single v u = true)).card ↔ true = true
  rw [e]
  simp

theorem sparseSat (K : LinClause Cell) {x : Cell → Bool} (sat : LinClauseSat x K) :
    LinClauseSat zero K ∨ ∃ v, LinClauseSat (single v) K := by
  obtain ⟨⟨f,b⟩,mem,hit⟩ := sat
  cases b with
  | false =>
    left
    exact ⟨(f,false),mem,by simp [LinEqSat,zero]⟩
  | true =>
    by_cases ne : f.Nonempty
    · obtain ⟨v,hv⟩ := ne
      exact Or.inr ⟨v,(f,true),mem,singleOdd f hv⟩
    · have e : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp ne
      subst f
      simp [LinEqSat] at hit

theorem cannotMerge (K : LinClause Cell)
    (reach : ∀ x, clear x → ¬ LinClauseSat x K) : ∀ x, ¬ LinClauseSat x K := by
  intro x hx
  rcases sparseSat K hx with z|⟨v,s⟩
  · exact reach _ zeroClear z
  · exact reach _ (singleClear v) s

end Lpcx178AffineMerge
