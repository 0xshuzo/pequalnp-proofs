import PEqualNP.Outside.L_meta_17415
import PEqualNP.Outside.L_meta_18546
import PEqualNP.Outside.L_meta_2225
import PEqualNP.Outside.L_meta_5775

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.Outside.L_meta_17415_aux
open PEqualNP.Outside.L_meta_5775

namespace FanoFlagObstruction

theorem incidence (p l : Fin 7) :
    p ∈ fanoLines l ↔ FanoGeometry.incident p l := by
  revert p l
  decide +kernel

theorem shape (C : Circuit) (ao : IsAO2 14 C)
    (nd : ∀ g ∈ C.gates, g.inputs.Nodup) : ConcreteModel.Valid C := by
  intro j g hit
  have mem := List.mem_of_getElem? hit
  have early (i : ℕ) (hi : i ∈ g.inputs) : i < 14+j := by
    have bound := (List.getElem?_eq_some_iff.mp hit).1
    have e : gateAt C j = g := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, hit]
      rfl
    exact ao.2.1 j bound i (e.symm ▸ hi)
  obtain ⟨a,b,args⟩ := List.length_eq_two.mp (ao.2.2 g mem)
  have ne : a ≠ b := by simpa [args] using nd g mem
  exact ⟨ao.1 g mem, a,b,args,ne,early a (by simp [args]),early b (by simp [args])⟩

theorem computed (C : Circuit) (hc : ComputesIncidence fanoLines C) (x : Fin 14 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, FanoGeometry.incident p l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  have h : C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_18546.Er.FanoF x :=
    congrFun (PEqualNP.Outside.L_meta_18546.Er.toFun C hc) x
  rw [h]
  simp only [PEqualNP.Outside.L_meta_18546.Er.FanoF, decide_eq_true_eq, incidence]

theorem impossibleFormula (C : Circuit) (hc : ComputesIncidence fanoLines C)
    (p l : Fin 7) (flag : p ∈ fanoLines l) (F : DMFormula 14) (hf : valid F)
    (leaves : F.leaves ≤ 28) (evaluate : ∀ x, F.eval x = C.eval (List.ofFn x)) :
    fDeg p.val F ≤ 1 ∨ fDeg (7+l.val) F ≤ 1 := by
  obtain ⟨ao,nd,sz,tree,ev,deg⟩ := compile_spec F hf
  let D := compile F
  have hsize : D.size ≤ 27 := by dsimp only [D]; omega
  have htree : ((D.output :: D.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup := tree
  have hcorrect (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ q m : Fin 7, FanoGeometry.incident q m ∧
        x (Fin.castAdd 7 q) = true ∧ x (Fin.natAdd 7 m) = true := by
    change (compile F).eval (List.ofFn x) = true ↔ _
    rw [ev x, evaluate x]
    exact computed C hc x
  have bound := PEqualNP.Outside.L_meta_2225 D p l
    ⟨hsize,shape D ao nd,hcorrect⟩ htree ((incidence p l).mp flag)
  change (compile F).lineDeg 14 {p.val} ≤ 1 ∨ (compile F).lineDeg 14 {7+l.val} ≤ 1 at bound
  simpa only [deg] using bound

theorem dirtyWitness (C : Circuit) (p l : Fin 7) (size : C.size ≤ 27)
    (ao : IsAO2 14 C) (nd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hc : ComputesIncidence fanoLines C) (flag : p ∈ fanoLines l)
    (dp : 2 ≤ C.lineDeg 14 {p.val}) (dl : 2 ≤ C.lineDeg 14 {7+l.val}) :
    ∃ j, PEqualNP.ReadTwo.isAnd C j ∧ ∃ a b : Fin 14,
      PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput a b) = true ∧
      C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = false := by
  classical
  by_contra no
  have clean : ∀ j, PEqualNP.ReadTwo.isAnd C j → ∀ a b : Fin 14,
      let x := PEqualNP.EdgeOwnership.pairInput a b
      PEqualNP.EdgeOwnership.gateVal 14 C j x = true → C.eval (List.ofFn x) = true := by
    intro j hand a b active
    cases ev : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) with
    | true => rfl
    | false => exact (no ⟨j,hand,a,b,active,ev⟩).elim
  have ex := FanoExternal.flagTests C (shape C ao nd) size (computed C hc) clean p l
    ((incidence p l).mp flag)
  omega

end FanoFlagObstruction
