import Mathlib
import PEqualNP.Defs

namespace ProjectiveMeet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) w

lemma wfLength (gs : List Gate) : ∀ s : List Bool, (wf gs s).length = s.length + gs.length := by
  induction gs with
  | nil => intro s; simp [wf]
  | cons g gs ih =>
    intro s
    have h := ih (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
    simp only [wf,List.foldl_cons] at h ⊢
    rw [h]
    simp
    omega

theorem appendMeet (n : ℕ) (D : Circuit) (a b : ℕ)
    (hm : IsAO2 n D) (ha : a < n+D.size) (hb : b < n+D.size) :
    let C : Circuit := ⟨D.gates ++ [⟨.and,[a,b]⟩], n+D.size⟩
    IsAO2 n C ∧ ∀ x : Fin n → Bool,
      let W := D.wires (List.ofFn x)
      let V := C.wires (List.ofFn x)
      C.eval (List.ofFn x) = (W.getD a false && W.getD b false) ∧
      V.getD a false = W.getD a false ∧ V.getD b false = W.getD b false := by
  let g : Gate := ⟨.and,[a,b]⟩
  let C : Circuit := ⟨D.gates ++ [g],n+D.size⟩
  change IsAO2 n C ∧ _
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hm.1 z hz
      · have eq : z = g := List.mem_singleton.mp hz
        subst z
        exact Or.inl rfl
    · intro i hi j hj
      by_cases hl : i < D.gates.length
      · have eq : gateAt C i = gateAt D i := List.getD_append _ _ _ _ hl
        exact hm.2.1 i hl j (eq ▸ hj)
      · have upper : i < D.gates.length + 1 := by simpa [C] using hi
        have eq : i = D.gates.length := by omega
        subst i
        have last : gateAt C D.gates.length = g := by
          simp [gateAt,C,List.getD_eq_getElem?_getD]
        rw [last] at hj
        change j ∈ [a,b] at hj
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl
        · exact ha
        · exact hb
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hm.2.2 z hz
      · have eq : z = g := List.mem_singleton.mp hz
        subst z
        rfl
  · intro x
    let W := D.wires (List.ofFn x)
    let bit := W.getD a false && W.getD b false
    have len : W.length = n+D.size := by
      change (wf D.gates (List.ofFn x)).length = _
      simpa [Circuit.size] using wfLength D.gates (List.ofFn x)
    have wires : C.wires (List.ofFn x) = W ++ [bit] := by
      simp [C,g,W,bit,Circuit.wires,List.foldl_append,GateOp.eval]
    change (C.wires _).getD (n+D.size) false = bit ∧
      (C.wires _).getD a false = W.getD a false ∧ (C.wires _).getD b false = W.getD b false
    rw [wires,← len]
    exact ⟨by simp [List.getD_eq_getElem?_getD],
      List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)⟩

end ProjectiveMeet
