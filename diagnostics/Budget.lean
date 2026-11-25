import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3610
import PEqualNP.Outside.L_meta_4360
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Budget3338
set_option maxHeartbeats 1000000 in
theorem necessary : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6];
    ∀ C : Circuit, FanInTwo C → C.size≤14 → (∀ x, C.eval (R x)=F x) →
    C.size=14 ∧ C.output=23 ∧ 13 ≤ C.gates.countP (fun g => g.op.eval [true]) := by
  intro F R C fan lim exactC
  have no13 (D : Circuit) (ok : FanInTwo D) (sm : D.size≤13) (eq : ∀ x, D.eval (R x)=F x) : False := by
    obtain ⟨x,bad⟩ := PEqualNP.Outside.L_meta_3610 D ok sm
    exact bad (eq x)
  have sz : C.size=14 := by by_contra h;exact no13 C fan (by omega) exactC
  have len : C.gates.length=14 := sz
  let emit (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have sizeW (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length=w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl emit (emit w g)).length = _
      rw [ih]
      simp [emit] <;> omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i<w.length) : (gs.foldl emit w).getD i false=w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit];omega)]
      exact List.getD_append _ _ _ _ h
  have out23 : C.output=23 := by
    have valid : C.output<24 := by
      by_contra bad
      let z (i : Fin 9) := true
      have yes : F z=true := by decide
      have q := exactC z
      change (C.gates.foldl emit (R z)).getD C.output false=F z at q
      rw [List.getD_eq_default _ _ (by rw [sizeW,len];simp [R];omega),yes] at q
      contradiction
    by_contra wrong
    let D : Circuit := ⟨C.gates.take 13,C.output⟩
    apply no13 D (fun g hg => fan g (List.mem_of_mem_take hg)) (by change (C.gates.take 13).length≤13;simp)
    intro x
    have e := exactC x
    change (C.gates.foldl emit (R x)).getD C.output false=F x at e
    rwa [←List.take_append_drop 13 C.gates,List.foldl_append,keep _ _ _ (by rw [sizeW];simp [R,len];omega)] at e
  have charged := PEqualNP.Outside.L_meta_4360 C fan (by
    intro x
    change C.eval (R x)=_
    rw [exactC]
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] <;> rfl)
  refine ⟨sz,out23,?_⟩
  convert charged using 1
  apply List.countP_congr
  intro g hg
  rcases (fan g hg).1 with h|h|h <;> change g.op=_ at h
  all_goals rw [h] <;> decide
end Budget3338
