import PEqualNP.Defs
namespace Trace18597
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem fuelS {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) : ∀ (k : ℕ) (i : Fin C.size), (i : ℕ) < k → ∀ d e : ℕ, (i : ℕ) < d → (i : ℕ) < e → gateValFuel C U d i = gateValFuel C U e i := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi d e hd he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hs : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)), sideTrue U B F i (gateValFuel C U d) = sideTrue U B F i (gateValFuel C U e) := by
      intro B F
      unfold sideTrue
      congr 1
      apply propext
      refine or_congr_right (exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj => ?_)
      have hj' : (j : ℕ) < (i : ℕ) := hj
      rw [ih j (by omega) d e (by omega) (by omega)]
    simp only [Nat.succ_eq_add_one, gateValFuel]
    rw [hs, hs]

theorem gv {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) && sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h : C.gateVal U i = gateValFuel C U (C.size + 1) i := fuelS C U (i + 1) i (by omega) _ _ i.isLt (by have := i.isLt; omega)
  rw [h]
  rfl


variable {n : Nat} (C : AndCountCircuit n)
def arm (U : Finset (Fin n)) (i : Fin C.size) (s : Bool) :=
  if s then sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)
  else sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)
def chooseLeft (U:Finset (Fin n)) (i:Fin C.size) := !(arm C U i true)
lemma gateOff (U : Finset (Fin n)) (i:Fin C.size) (hi:C.gateVal U i=false) :
    arm C U i (chooseLeft C U i)=false := by
  rw [gv] at hi
  unfold chooseLeft arm
  simp only [if_true]
  cases ha : sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) <;> simp [ha] at hi ⊢
  all_goals assumption
lemma chosenOff (U : Finset (Fin n)) (i:Fin C.size) (s:Bool) (h : arm C U i s=false) :
    C.gateVal U i=false := by
  rw [gv]
  cases s <;> simp [arm] at h <;> simp [h]
lemma commonOff (X Y:Finset (Fin n)) (eq:chooseLeft C X=chooseLeft C Y) :
    ∀i:Fin C.size,C.gateVal X i=false → C.gateVal Y i=false → C.gateVal (X∪Y) i=false := by
  intro i
  induction i using Fin.strongInductionOn with
  | ind i ih =>
    intro hx hy
    have a := gateOff C X i hx
    have b := gateOff C Y i hy
    rw [←eq] at b
    apply chosenOff C _ _ (chooseLeft C X i)
    have step (V:Finset (Fin n)) (F:Finset (Fin C.size)) :
        sideTrue X V F i (C.gateVal X)=false →
        sideTrue Y V F i (C.gateVal Y)=false →
        sideTrue (X∪Y) V F i (C.gateVal (X∪Y))=false := by
      intro x y
      apply Bool.eq_false_iff.mpr
      intro z
      simp only [sideTrue,decide_eq_true_eq] at z
      have badX := Bool.eq_false_iff.mp x
      have badY := Bool.eq_false_iff.mp y
      simp only [sideTrue,decide_eq_true_eq] at badX badY
      rcases z with ⟨v,hv,h⟩ | ⟨j,hj,lt,h⟩
      · exact (Finset.mem_union.mp h).elim (fun h => badX (Or.inl ⟨v,hv,h⟩)) (fun h => badY (Or.inl ⟨v,hv,h⟩))
      · have offX := Bool.eq_false_iff.mpr (fun H => badX (Or.inr ⟨j,hj,lt,H⟩))
        have offY := Bool.eq_false_iff.mpr (fun H => badY (Or.inr ⟨j,hj,lt,H⟩))
        exact Bool.eq_false_iff.mp (ih j lt offX offY) h
    cases s : chooseLeft C X i <;> simp only [arm,s,Bool.false_eq_true,if_false,if_true] at a b ⊢ <;>
      exact step _ _ a b
theorem traceBound {ι : Type} [Fintype ι] (rows:ι → Finset (Fin n))
    (off:∀i,C.eval (rows i)=false)
    (collision:∀i j,i≠j → C.eval (rows i ∪ rows j)=true) : Fintype.card ι ≤ 2^C.size := by
  classical
  have inj : Function.Injective (fun i => chooseLeft C (rows i)) := by
    intro i j h
    by_contra ne
    have hi := Bool.eq_false_iff.mp (off i)
    have hj := Bool.eq_false_iff.mp (off j)
    have hU := collision i j ne
    simp only [eval,decide_eq_true_eq] at hi hj hU
    rcases hU with ⟨v,hv,hu⟩|⟨g,hg,fires⟩
    · exact (Finset.mem_union.mp hu).elim (fun h => hi (Or.inl ⟨v,hv,h⟩)) (fun h => hj (Or.inl ⟨v,hv,h⟩))
    · have a := Bool.eq_false_iff.mpr (fun H => hi (Or.inr ⟨g,hg,H⟩))
      have b := Bool.eq_false_iff.mpr (fun H => hj (Or.inr ⟨g,hg,H⟩))
      exact Bool.eq_false_iff.mp (commonOff C _ _ h g a b) fires
  simpa using Fintype.card_le_of_injective _ inj
end Trace18597
