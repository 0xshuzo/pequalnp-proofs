import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4217_215
    (unique : ∀ C : Circuit, let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
    let hit (a : ℕ) := (gateAt C a).op=.and ∧
      ∃ b : Fin 2, V (opnd C a b) 0 0=true ∧ V (opnd C a (1-b)) 7 7=true
    C.size≤27 → IsAO2 14 C → circuitFun 14 C = (fun x => decide (∃ p l : Fin 7, p∈fanoLines l ∧
      x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true)) →
    (∀ p l : Fin 7, p∈fanoLines l → readsAtMost C 14 [p.val,7+l.val] 1=true) →
    ∀ a b, hit a → hit b → a=b)
    (missing : ∀ C : Circuit, let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
    let off (w : ℕ) := V w 0 0=false ∧ V w 7 7=false
    let B (w a : ℕ) := (14+a=w ∨ InCone 14 C a (w-14)) ∧ (gateAt C a).op=.and ∧
      off (14+a) ∧
      ∃ b : Fin 2, V (opnd C a b) 0 0=true ∧ V (opnd C a (1-b)) 7 7=true
    C.size≤27 → IsAO2 14 C → (∀ j<C.gates.length, (gateAt C j).inputs.Nodup) →
    circuitFun 14 C = (fun x => decide (∃ p l : Fin 7, p∈fanoLines l ∧
      x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true)) →
    (∃ p l : Fin 7, p∈fanoLines l ∧ readsAtMost C 14 [p.val,7+l.val] 1=false) →
    ∀ g, (gateAt C g).op=.and → (14+g=C.output ∨ InCone 14 C g (C.output-14)) →
    V (14+g) 0 7=true → (∀ b, off (opnd C g b)) →
    ∃ j, B (opnd C g 0) j ∧ B (opnd C g 1) j) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → (¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13) → ¬∃ (x14 : ℕ) (x15 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x14 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x15 := by
  intro C V B size ao nodup computes g kind inside yes singles separate
  by_cases hole : ∃ p l : Fin 7, p∈fanoLines l ∧ readsAtMost C 14 [p.val,7+l.val] 1=false
  · obtain ⟨j,left,right⟩ := missing C size ao nodup computes hole g kind inside yes singles
    exact False.elim (separate ⟨j,
      ⟨left.1,left.2.1,left.2.2.1.1,left.2.2.1.2,left.2.2.2⟩,
      ⟨right.1,right.2.1,right.2.2.1.1,right.2.2.1.2,right.2.2.2⟩⟩)
  · have good (p l : Fin 7) (edge : p∈fanoLines l) : readsAtMost C 14 [p.val,7+l.val] 1=true := by
      cases h : readsAtMost C 14 [p.val,7+l.val] 1 with
      | true => rfl
      | false => exact False.elim (hole ⟨p,l,edge,h⟩)
    rintro ⟨a,b,ha,hb⟩
    have same := unique C size ao computes good a b
        ⟨ha.2.1,ha.2.2.2.2⟩ ⟨hb.2.1,hb.2.2.2.2⟩
    subst b
    exact separate ⟨a,ha,hb⟩
