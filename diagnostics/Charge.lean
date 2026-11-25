import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_4360
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Charge4643
set_option maxHeartbeats 2200000 in
theorem charge : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool), FanInTwo C → 10≤k → k<10+C.size →
    (∀ g∈C.gates.take (k+1-10), v.val∉g.inputs) →
    (∀ x, C.eval ((R x).set v.val (if b then x v || (C.wires (R x)).getD k false else
      x v && (C.wires (R x)).getD k false)) = F x) →
    12≤C.gates.countP (fun g => g.op.eval [true]) := by
  intro target row
  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let maskBit (x h disj : Bool) := if disj then x || h else x && h

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i+1

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (rename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (rename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have row_pivot (x : Fin 9 → Bool) (v : Fin 9) : (row x).getD v.val false = x v := by
    unfold row
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]

  have mask_value (x : Fin 9 → Bool) (v : Fin 9) (k : ℕ) (disj : Bool) (old : List Bool)
      (hv : v.val < old.length) (oldv : old.getD v.val false = x v) :
      emit old ⟨if disj then .or else .and,[v.val,k]⟩ =
        old ++ [maskBit (x v) (old.getD k false) disj] := by
    unfold emit maskBit
    cases disj
    · change old ++ [(old.getD v.val false && (old.getD k false && true))] =
        old ++ [x v && old.getD k false]
      rw [Bool.and_true,oldv]
    · change old ++ [(old.getD v.val false || (old.getD k false || false))] =
        old ++ [x v || old.getD k false]
      rw [Bool.or_false,oldv]

  let q (g : Gate) := g.op.eval [true]
  have insert_mask (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (fan : FanInTwo C) (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) :
      ∃ D : Circuit, FanInTwo D ∧ D.gates.countP q=C.gates.countP q+1 ∧
        ∀ x : Fin 9 → Bool, D.eval (row x) = C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) := by
    let pre := C.gates.take (k+1-10)
    let suf := C.gates.drop (k+1-10)
    let mask : Gate := ⟨if disj then .or else .and,[v.val,k]⟩
    let shift := rename (redirect v.val (k+1))
    let D : Circuit := ⟨pre ++ mask :: suf.map shift,redirect v.val (k+1) C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have maskLegal : mask.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ mask.inputs.length ≤ 2 := by
      cases disj <;> simp [mask]
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ pre ++ mask :: suf.map shift at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact fan g (by rw [← split]; exact List.mem_append_left _ hg)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact maskLegal
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [← split]; exact List.mem_append_right _ hg')
      exact ⟨op,by simpa [shift,rename] using arity⟩
    have costs : D.gates.countP q=C.gates.countP q+1 := by
      change (pre ++ mask :: suf.map shift).countP q=C.gates.countP q+1
      have mapQ : (suf.map shift).countP q=suf.countP q := by
        rw [List.countP_map]
        rfl
      have m : q mask=true := by cases disj <;> rfl
      rw [← split,List.countP_append,List.countP_append,List.countP_cons,mapQ]
      simp [m] <;> omega
    refine ⟨D,legal,costs,?_⟩
    intro x
    let old := pre.foldl emit (row x)
    have kBound : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
    have length : old.length = k+1 := by
      rw [show old = pre.foldl emit (row x) by rfl,fold_size]
      simp [pre,row,Nat.min_eq_left kBound]
      omega
    have vBound : v.val < old.length := by rw [length]; have := v.isLt; omega
    have saved : (C.wires (row x)).getD k false = old.getD k false := by
      change (C.gates.foldl emit (row x)).getD k false = _
      rw [← split,List.foldl_append]
      exact fold_preserves suf old k (by omega)
    have savedV : old.getD v.val false = x v := by
      rw [fold_preserves pre (row x) _ (by simp [row]; have := v.isLt; omega),row_pivot]
    let bit := maskBit (x v) (old.getD k false) disj
    have oldSet : pre.foldl emit ((row x).set v.val bit) = old.set v.val bit :=
      fold_set_avoid pre (row x) v.val bit (by simp [row]; have := v.isLt; omega) avoid
    have law (i : ℕ) : (old ++ [bit]).getD (redirect v.val (k+1) i) false =
        (old.set v.val bit).getD i false := by rw [← length]; exact append_with_mask v.val old vBound bit i
    have simulated := suffix_shift suf v.val (k+1) (old.set v.val bit) (old++[bit])
      (by have := v.isLt; omega) (by simp [length]) (by simp) law C.output
    change ((pre ++ mask :: suf.map shift).foldl emit (row x)).getD
        (redirect v.val (k+1) C.output) false =
      (C.gates.foldl emit ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj))).getD C.output false
    rw [List.foldl_append, List.foldl_cons,mask_value x v k disj old vBound savedV,
      saved,← split,List.foldl_append,oldSet]
    exact simulated

  intro v C k b fan lo hi avoid correct
  obtain ⟨D,dfan,count,agrees⟩ := insert_mask C v k b fan lo hi avoid
  have equal (x : Fin 9 → Bool) : D.eval (row x)=target x := (agrees x).trans (correct x)
  have recBound := PEqualNP.Outside.L_meta_4360 D dfan (by
    intro x
    have e := equal x
    change D.eval (row x) = _
    rw [e]
    simp only [target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] <;> rfl)
  have convert : D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) = D.gates.countP q := by
    apply List.countP_congr
    intro g hg
    rcases (dfan g hg).1 with h|h|h <;> change g.op=_ at h
    all_goals simp only [q,h] <;> rfl
  rw [convert,count] at recBound
  exact Nat.le_of_succ_le_succ (by simpa only [Nat.succ_eq_add_one] using recBound)

end Charge4643
