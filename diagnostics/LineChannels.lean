import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.LineChannels

variable {P L : Type} (A : P → L → Bool) (E : P → L → Bool → Bool)
    (D : (L → Bool) → Bool) (base : P)

def Computes : Prop :=
  ∀ (x : P) (y : L → Bool),
    D (fun i => E x i (y i)) = true ↔ ∃ i, A x i = true ∧ y i = true

theorem bitSeparation (h : Computes A E D) (allOn : ∀ i, A base i = true) (j : L) :
    E base j false ≠ E base j true := by
  classical
  intro same
  let one : L → Bool := fun i => decide (i=j)
  have eqv : (fun i => E base i false) = (fun i => E base i (one i)) := by
    funext i
    by_cases hit : i=j
    · subst i; simpa [one] using same
    · simp [one,hit]
  have yes := (h base one).2 ⟨j,allOn j,by simp [one]⟩
  rw [← eqv] at yes
  obtain ⟨_,_,bad⟩ := (h base (fun _ => false)).1 yes
  cases bad

theorem table (h : Computes A E D) (allOn : ∀ i, A base i = true) (z : L → Bool) :
    D z = true ↔ ∃ i, z i ≠ E base i false := by
  classical
  let test : L → Bool := fun i => decide (z i ≠ E base i false)
  have full : (fun i => E base i (test i)) = z := by
    funext i
    have dist := bitSeparation A E D base h allOn i
    dsimp [test]
    cases hz : z i <;> cases h0 : E base i false <;> cases h1 : E base i true <;>
      simp_all
  constructor
  · intro on
    have yes : D (fun i => E base i (test i)) = true := full.symm ▸ on
    obtain ⟨i,_,hi⟩ := (h base test).1 yes
    exact ⟨i,by simpa [test] using hi⟩
  · rintro ⟨i,hi⟩
    rw [← full]
    exact (h base test).2 ⟨i,allOn i,by simpa [test] using hi⟩

theorem offChannels (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x : P) (i : L) : E x i false = E base i false := by
  by_contra diff
  have on := (table A E D base h allOn (fun j => E x j false)).2 ⟨i,diff⟩
  obtain ⟨_,_,bad⟩ := (h x (fun _ => false)).1 on
  cases bad

theorem activeChannel (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x : P) (j : L) : E x j true ≠ E base j false ↔ A x j = true := by
  classical
  let one : L → Bool := fun i => decide (i=j)
  have hj : one j = true := by simp [one]
  constructor
  · intro changeBit
    have on := (table A E D base h allOn (fun i => E x i (one i))).2
      ⟨j,by simpa only [hj] using changeBit⟩
    obtain ⟨i,hi,fi⟩ := (h x one).1 on
    have eqij : i=j := by simpa [one] using fi
    simpa [eqij] using hi
  · intro active
    have on := (h x one).2 ⟨j,active,hj⟩
    obtain ⟨i,hi⟩ := (table A E D base h allOn _).1 on
    by_cases ij : i=j
    · subst i; simpa only [hj] using hi
    · have low : one i=false := by simp [one,ij]
      rw [low,offChannels A E D base h allOn x i] at hi
      exact (hi rfl).elim

theorem requiredInput (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x y : P) (j : L) (off : A x j=false) (on : A y j=true) :
    E x j true ≠ E y j true := by
  intro same
  have hy := (activeChannel A E D base h allOn y j).2 on
  rw [← same] at hy
  have hx := (activeChannel A E D base h allOn x j).1 hy
  rw [off] at hx
  cases hx

end PEqualNP.Outside.L_meta_9829.LineChannels
