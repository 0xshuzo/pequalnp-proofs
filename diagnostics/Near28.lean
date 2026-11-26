import PEqualNP.Defs
namespace Research5962.Near
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
attribute [local instance] PEqualNP.GenericRejection.gateOpDecEq
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768
def C : Circuit := ⟨[
  ⟨.or, [8,9]⟩,
  ⟨.or, [7,11]⟩,
  ⟨.and, [0,15]⟩,
  ⟨.or, [13,16]⟩,
  ⟨.and, [0,17]⟩,
  ⟨.or, [14,17]⟩,
  ⟨.or, [2,18]⟩,
  ⟨.and, [19,20]⟩,
  ⟨.or, [7,8]⟩,
  ⟨.or, [22,12]⟩,
  ⟨.and, [1,23]⟩,
  ⟨.or, [21,24]⟩,
  ⟨.or, [7,9]⟩,
  ⟨.or, [26,10]⟩,
  ⟨.and, [3,27]⟩,
  ⟨.or, [25,28]⟩,
  ⟨.or, [8,10]⟩,
  ⟨.or, [30,11]⟩,
  ⟨.and, [4,31]⟩,
  ⟨.or, [29,32]⟩,
  ⟨.or, [9,11]⟩,
  ⟨.or, [34,12]⟩,
  ⟨.and, [5,35]⟩,
  ⟨.or, [33,36]⟩,
  ⟨.or, [10,12]⟩,
  ⟨.or, [38,13]⟩,
  ⟨.and, [6,39]⟩,
  ⟨.or, [37,40]⟩], 41⟩
def edges : List (Fin 7 × Fin 7) := [(0,0), (0,4), (0,6), (1,0), (1,1), (1,5), (2,1), (2,2), (2,6), (3,0), (3,2), (3,3), (4,1), (4,3), (4,4), (5,2), (5,4), (5,5), (6,3), (6,5), (6,6)]
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


theorem outputCorrect (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  have memEdge : ∀ p l : Fin 7, (p,l) ∈ edges ↔ (p=l ∨ p=l+1 ∨ p=l+3) := by decide
  have he : C.eval (List.ofFn x) =
      edges.any (fun e => x (Fin.castAdd 7 e.1) && x (Fin.natAdd 7 e.2)) := by
    change C.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] = _
    simp [C, edges, Circuit.eval, Circuit.wires, GateOp.eval]
    bv_decide
  rw [he,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,m,h⟩
    exact ⟨p,l,(memEdge p l).mp m,by simpa using h⟩
  · rintro ⟨p,l,m,h⟩
    exact ⟨(p,l),(memEdge p l).mpr m,by simpa using h⟩


theorem size : C.size = 28 := by decide +kernel
def marker (j : ℕ) (k : Fin 14) : Prop :=
  (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
  gateVal 14 C j (pairInput 0 7) = true ∧
  ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput k k) = false
instance (j : ℕ) (k : Fin 14) : Decidable (marker j k) := by unfold marker; infer_instance
theorem nested : InCone 14 C 4 7 ∧ marker 7 0 ∧ marker 4 7 := by decide +kernel
theorem shared : 14 ≤ 17 ∧ 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 17 := by decide +kernel
def witness (k : Fin 16) (i : Fin 14) : Bool :=
  if k.val=14 ∨ k.val=13 then decide (i=0 ∨ i=7)
  else if k.val=15 then false else decide (i.val=k.val)
theorem nonprojection : ∀ k : Fin 16,
    wireVal 14 C 17 (witness k) = C.eval (List.ofFn (witness k)) ∧
    wireVal 14 C 17 (witness k) ≠
      (if h : k.val<14 then witness k ⟨k.val,h⟩ else decide (k.val=15)) := by decide +kernel

end Research5962.Near
