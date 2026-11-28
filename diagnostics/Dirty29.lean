import PEqualNP.Defs

namespace Dirty29Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection
attribute [local instance] gateOpDecEq
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768

def C : Circuit := ⟨[
  ⟨.or,[0,13]⟩,
  ⟨.or,[7,13]⟩,
  ⟨.or,[11,15]⟩,
  ⟨.and,[14,16]⟩,
  ⟨.and,[0,17]⟩,
  ⟨.or,[9,17]⟩,
  ⟨.or,[2,18]⟩,
  ⟨.or,[8,19]⟩,
  ⟨.and,[20,21]⟩,
  ⟨.or,[7,8]⟩,
  ⟨.or,[23,12]⟩,
  ⟨.and,[1,24]⟩,
  ⟨.or,[22,25]⟩,
  ⟨.or,[7,9]⟩,
  ⟨.or,[27,10]⟩,
  ⟨.and,[3,28]⟩,
  ⟨.or,[26,29]⟩,
  ⟨.or,[8,10]⟩,
  ⟨.or,[31,11]⟩,
  ⟨.and,[4,32]⟩,
  ⟨.or,[30,33]⟩,
  ⟨.or,[9,11]⟩,
  ⟨.or,[35,12]⟩,
  ⟨.and,[5,36]⟩,
  ⟨.or,[34,37]⟩,
  ⟨.or,[10,12]⟩,
  ⟨.or,[39,13]⟩,
  ⟨.and,[6,40]⟩,
  ⟨.or,[38,41]⟩],42⟩

def edges : List (Fin 7 × Fin 7) := [
  (0,0), (0,4), (0,6), (1,0), (1,1), (1,5), (2,1), (2,2), (2,6), (3,0), (3,2), (3,3), (4,1), (4,3), (4,4), (5,2), (5,4), (5,5), (6,3), (6,5), (6,6)]

theorem gateTable : ∀ j : Fin C.gates.length,
      let g := C.gates[j.val]'(j.isLt)
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j.val ∧ b < 14+j.val := by decide

theorem legal (i : Nat) (g : Gate) (h : C.gates[i]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+i ∧ b < 14+i := by
  have hi : i < C.gates.length := by
    by_contra! bad
    rw [List.getElem?_eq_none bad] at h
    contradiction
  have he : g = C.gates[i] := by simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using h.symm
  subst g
  obtain ⟨op, ins, ne, ha, hb⟩ := gateTable ⟨i,hi⟩
  exact ⟨op, _, _, ins, ne, ha, hb⟩


private theorem rawEq : ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Bool), (((((((x2 || (x0 && ((x0 || x13) && (x11 || (x7 || x13))))) && (x8 || (x9 || ((x0 || x13) && (x11 || (x7 || x13)))))) || (x1 && ((x7 || x8) || x12))) || (x3 && ((x7 || x9) || x10))) || (x4 && ((x8 || x10) || x11))) || (x5 && ((x9 || x11) || x12))) || (x6 && ((x10 || x12) || x13))) = ((x0 && x7) || ((x0 && x11) || ((x0 && x13) || ((x1 && x7) || ((x1 && x8) || ((x1 && x12) || ((x2 && x8) || ((x2 && x9) || ((x2 && x13) || ((x3 && x7) || ((x3 && x9) || ((x3 && x10) || ((x4 && x8) || ((x4 && x10) || ((x4 && x11) || ((x5 && x9) || ((x5 && x11) || ((x5 && x12) || ((x6 && x10) || ((x6 && x12) || ((x6 && x13) || false))))))))))))))))))))) := by decide +kernel

theorem outputCorrect (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  have memEdge : ∀ p l : Fin 7, (p,l) ∈ edges ↔ p ∈ fanoLines l := by decide
  have he : C.eval (List.ofFn x) =
      edges.any (fun e => x (Fin.castAdd 7 e.1) && x (Fin.natAdd 7 e.2)) := by
    change C.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] = _
    simpa [C, edges, Circuit.eval, Circuit.wires, GateOp.eval] using
      rawEq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)
  rw [he,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,m,h⟩
    exact ⟨p,l,(memEdge p l).mp m,by simpa using h⟩
  · rintro ⟨p,l,m,h⟩
    exact ⟨(p,l),(memEdge p l).mpr m,by simpa using h⟩

theorem sizeAndMarks : C.size = 29 ∧ (0 : Fin 7) ∈ fanoLines 0 ∧
    2 ≤ C.lineDeg 14 {0} ∧ 2 ≤ C.lineDeg 14 {7} := by decide

theorem wellFormed : IsAO2 14 C ∧ ∀ g ∈ C.gates, g.inputs.Nodup := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
      exact (legal j g hj).1
    · intro j hj i hi
      have lookup : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      rw [lookup] at hi
      obtain ⟨_,a,b,eq,_,ha,hb⟩ := legal j C.gates[j] (List.getElem?_eq_getElem hj)
      simp only [eq,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
      obtain ⟨_,a,b,eq,_,_,_⟩ := legal j g hj
      simp [eq]
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨_,a,b,eq,ne,_,_⟩ := legal j g hj
    simp [eq,ne]

theorem incidence : ComputesIncidence fanoLines C := by
  intro X Y
  let x : Fin 14 → Bool := Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y))
  have eq : List.ofFn x = incidenceInput X Y := List.ofFn_fin_append _ _
  rw [← eq]
  apply Bool.eq_iff_iff.mpr
  rw [outputCorrect x]
  change _ ↔ decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ fanoLines l) = true
  simp only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq]
  constructor
  · rintro ⟨u,v,hit,hu,hv⟩
    exact ⟨u,hu,v,hv,hit⟩
  · rintro ⟨u,hu,v,hv,hit⟩
    exact ⟨u,v,hit,hu,hv⟩

theorem shared_dirty :
    (gateAt C 3).op = .and ∧ 2 ≤ (C.output::C.gates.flatMap Gate.inputs).count 17 ∧
    gateVal 14 C 3 (pairInput 13 13)=true ∧ C.eval (List.ofFn (pairInput (13:Fin 14) 13))=false := by decide +kernel

end Dirty29Fano
