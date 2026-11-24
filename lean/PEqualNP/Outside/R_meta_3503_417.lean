import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3503_417
    (flat : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l r, p ≠ q → l ≠ r → ¬(I p l ∧ I p r ∧ I q l ∧ I q r)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size ≤ C.size ∧ circuitFun (n+m) D = circuitFun (n+m) C ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → ¬ InCone (n+m) D i j) ∧
          ∀ z, gateVal (n+m) D j z = true → circuitFun (n+m) D z = true)
    (bands : ∀ (N : ℕ) (C : Circuit), IsAO2 N C →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ¬ InCone N C i j) →
      ∃ U : Finset ℕ, (∀ w ∈ U, w < N ∨ ∃ j < C.gates.length, w = N+j ∧ (gateAt C j).op = GateOp.or ∧
         ∀ a ∈ (gateAt C j).inputs, a ∈ U) ∧ ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ a ∈ (gateAt C j).inputs, a ∈ U)
    (paint : ∀ (n m : ℕ) (C : Circuit) (U : Finset ℕ), let N := n+m
      IsAO2 N C → (∀ w ∈ U, w < N ∨ ∃ j < C.gates.length, w = N+j ∧ (gateAt C j).op = GateOp.or ∧
         ∀ a ∈ (gateAt C j).inputs, a ∈ U) → (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ a ∈ (gateAt C j).inputs, a ∈ U) → (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ t : Bool,
       gateVal N C j (fun i => decide (i.val < n) == t) = false) → ∃ S : Bool → Finset ℕ,
      (∀ t w, w ∈ S t → (w < N ∧ decide (w < n) = t) ∨
        ∃ j < C.gates.length, w = N+j ∧ (gateAt C j).op = GateOp.or ∧ ∀ a ∈ (gateAt C j).inputs, a ∈ S t) ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ a b t, (gateAt C j).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  intro n m I inst C square ao computes
  obtain ⟨D,dAO,budget,eqfun,shape⟩ := flat n m I C square ao computes
  obtain ⟨U,closed,under⟩ := bands (n+m) D dAO (fun j hj ho => (shape j hj ho).1)
  have rejects (t : Bool) : circuitFun (n+m) D (fun i => decide (i.val < n) == t) = false := by
    rw [eqfun,computes]
    apply decide_eq_false
    rintro ⟨p,l,inc,hp,hl⟩
    have pp : (Fin.castAdd m p).val < n := p.isLt
    have ll : ¬ (Fin.natAdd n l).val < n := by change ¬ n+l.val < n; omega
    cases t <;> simp [pp,ll] at hp hl
  have zeros (j : ℕ) (hj : j < D.gates.length) (ho : (gateAt D j).op = GateOp.and) (t : Bool) :
      gateVal (n+m) D j (fun i => decide (i.val < n) == t) = false := by
    cases h : gateVal (n+m) D j (fun i => decide (i.val < n) == t) with
    | false => rfl
    | true => have force := (shape j hj ho).2 _ h; rw [rejects] at force; contradiction
  obtain ⟨S,side,hands⟩ := paint n m D U dAO closed under zeros
  refine ⟨D,S true,S false,dAO,fun z => (congrFun eqfun z).trans (computes z),budget,?_,?_,?_⟩
  · intro w hw
    rcases side true w hw with ⟨_,hs⟩ | h
    · exact Or.inl (of_decide_eq_true hs)
    · exact Or.inr h
  · intro w hw
    rcases side false w hw with ⟨ht,hs⟩ | h
    · exact Or.inl ⟨Nat.le_of_not_gt (of_decide_eq_false hs),ht⟩
    · exact Or.inr h
  · intro j hj ho
    obtain ⟨a,b,t,hab,ha,hb⟩ := hands j hj ho
    refine ⟨a,b,hab,?_⟩
    cases t with
    | false => exact Or.inr ⟨ha,hb⟩
    | true => exact Or.inl ⟨ha,hb⟩
