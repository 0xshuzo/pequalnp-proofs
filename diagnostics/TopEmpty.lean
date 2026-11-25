import Mathlib
import PEqualNP.Outside.L_meta_1485

namespace TopEmpty2846
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Outside.L_meta_1485

def stuck (n : Nat) (F : (Fin n → Bool) → Bool) (C : Circuit) :=
  ∃ T : Finset Nat, (∀ i ∈ T, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
    (n+i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, n+i ∈ (gateAt C k').inputs ↔ k'=k)) ∧
    ∀ w, (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → F z = true) →
      (∃ k < C.gates.length, (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) →
      ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → k ∈ T

theorem all_dirty {n : Nat} (hn : 0 < n) {F : (Fin n → Bool) → Bool} {C : Circuit}
    (ha : IsAO2 n C) (exact' : ∀ z, circuitFun n C z = F z)
    (least : ∀ D, IsAO2 n D → (∀ z, circuitFun n D z = F z) → C.size ≤ D.size)
    (stop : stuck n F C) (j : Nat) (out : n+j=C.output) (op : (gateAt C j).op=GateOp.and)
    (i : Nat) (hi : i<C.gates.length) (hne : i≠j) :
    ∃ z : Fin n → Bool, val C (List.ofFn z) (n+i) = true ∧ F z = false := by
  classical
  obtain ⟨T,hT,quarantine⟩ := stop
  have empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    let m := T.max' ⟨u,hu⟩
    have hm : m ∈ T := Finset.max'_mem _ _
    obtain ⟨hmL,hmop,cut⟩ := hT m hm
    rcases cut with e | ⟨s,hs,read⟩
    · have eq : m=j := by omega
      rw [eq,op] at hmop
      contradiction
    · have hsL := (hT s hs).1
      have le : s ≤ m := Finset.le_max' _ _ hs
      have back := ha.2.1 s hsL (n+m) ((read s hsL).2 rfl)
      omega
  have hAO (k) (hk : k<C.gates.length) := ha.1 _ (gateAt_mem hk)
  by_contra! nogo
  have under (z : Fin n → Bool) (hw : val C (List.ofFn z) (n+i) = true) : F z = true := by
    simpa only [Bool.not_eq_false] using nogo z hw
  have under' (z : Fin n → Bool) (hw : val C (List.ofFn z) (n+i) = true) :
      C.eval (List.ofFn z) = true := (exact' z).trans (under z hw)
  have no (r : Nat) (hr : r<C.gates.length) (hm : n+i ∈ (gateAt C r).inputs) : False := by
    have rb := ha.2.1 r hr (n+i) hm
    rcases hAO r hr with hand | hor
    · have bound := least (bypass n C r (n+i)) (isAO2_bypass ha rb) (fun z =>
        (caseB (by simp) hAO hr (by omega) hm hand (under' z)).trans (exact' z))
      have len := bypass_length n C r (n+i)
      change C.gates.length ≤ (bypass n C r (n+i)).gates.length at bound
      omega
    · have top := quarantine (n+i) under ⟨r,hr,hor,hm⟩ r hr hm
      simpa [empty] using top
  have bound := least (bypass n C i 0) (isAO2_bypass ha (by omega)) (fun z =>
    (bypass_eval_unread (by simp) hAO hi (Or.inl (by omega)) (by omega) no).trans (exact' z))
  have len := bypass_length n C i 0
  change C.gates.length ≤ (bypass n C i 0).gates.length at bound
  omega

end TopEmpty2846
