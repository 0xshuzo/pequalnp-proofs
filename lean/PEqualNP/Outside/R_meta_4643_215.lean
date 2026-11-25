import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4643_215
    (charge : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6];
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool), FanInTwo C → 10≤k → k<10+C.size →
    (∀ g∈C.gates.take (k+1-10), v.val∉g.inputs) →
    (∀ x, C.eval ((R x).set v.val (if b then x v || (C.wires (R x)).getD k false else
      x v && (C.wires (R x)).getD k false)) = F x) →
    12≤C.gates.countP (fun g => g.op.eval [true]))
    (headLaw : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6];
    ∀ (v : Fin 9) (g : Gate) (b : Bool), let H (x : Fin 9 → Bool) := g.op.eval (g.inputs.map fun i => (R x).getD i false);
    (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) →
    (∀ x y, (∀ i, i≠v → x i=y i) → F x≠F y → H x = !b) →
    (∃ x, H x=b) → g.op=if b then .and else .or)
    (remaining : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6];
    ∀ (v : Fin 9) (g : Gate) (D : Circuit) (k : ℕ) (b : Bool),
    let Y (x : Fin 9 → Bool) := R x ++ [g.op.eval (g.inputs.map fun i => (R x).getD i false)];
    let U (x : Fin 9 → Bool) := (D.wires (Y x)).getD k false;
    v≠0 → v≠6 → FanInTwo (⟨g::D.gates,D.output⟩ : Circuit) → D.size=12 → D.output=22 →
    12≤(g::D.gates).countP (fun a => a.op.eval [true]) →
    10≤k → k<22 → (k=10 → g.op=if b then .and else .or) → v.val∉g.inputs →
    (∀ h∈D.gates.take (k-10), v.val∉h.inputs) →
    ∃ x, D.eval ((Y x).set v.val (if b then x v || U x else x v && U x))≠F x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (9 : ℕ) → Bool) => (x3.wires (x2 x5)).getD x4 Bool.false; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool), x4 ≠ (0 : Fin (9 : ℕ)) → x4 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size = (13 : ℕ) → x5.output = (22 : ℕ) → (10 : ℕ) ≤ x6 → x6 < (22 : ℕ) → (x7 = Bool.false → x6 = (10 : ℕ) → x4 = (1 : Fin (9 : ℕ)) ∨ x4 = (4 : Fin (9 : ℕ)) ∨ x4 = (7 : Fin (9 : ℕ))) → (∀ x16 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x16.inputs) → (∀ (x17 x18 : Fin (9 : ℕ) → Bool), (∀ (x19 : Fin (9 : ℕ)), x19 ≠ x4 → x17 x19 = x18 x19) → x1 x17 ≠ x1 x18 → x3 x5 x6 x17 = !x7) → (∃ x18 ∈ x5.gates, (9 : ℕ) ∈ x18.inputs) → (∃ (x19 : Fin (9 : ℕ) → Bool), x19 x4 = !x7 ∧ x3 x5 x6 x19 = x7 ∧ x5.eval (x2 x19) ≠ x1 x19) → ∃ (x20 : Fin (9 : ℕ) → Bool), x5.eval ((x2 x20).set (↑x4) (if x7 = Bool.true then x20 x4 || x3 x5 x6 x20 else x20 x4 && x3 x5 x6 x20)) ≠ x1 x20 := by
  classical
  intro F R V v C k b v0 v6 fan size out lo hi early avoid sense seed witness
  by_contra! correct
  have paid := charge v C k b fan lo (by omega) avoid correct
  obtain ⟨gs,o⟩ := C
  change gs.length=13 at size
  cases gs with
  | nil => cases size
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    let H (x : Fin 9 → Bool) := g.op.eval (g.inputs.map fun i => (R x).getD i false)
    let Y (x : Fin 9 → Bool) := R x ++ [H x]
    let emit (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold_pre (ts : List Gate) (w : List Bool) (i : ℕ) (below : i<w.length) :
        (ts.foldl emit w).getD i false=w.getD i false := by
      induction ts generalizing w with
      | nil => rfl
      | cons t ts ih =>
        rw [List.foldl_cons,ih (emit w t) (by simp [emit];omega)]
        exact List.getD_append _ _ _ _ below
    have rowlen (x : Fin 9 → Bool) : (R x).length=10 := by simp [R]
    have first (x : Fin 9 → Bool) : V ⟨g::gs,o⟩ 10 x=H x := by
      change (gs.foldl emit (Y x)).getD 10 false=H x
      rw [fold_pre _ _ _ (by simp [Y,rowlen])]
      change (R x ++ [H x]).getD 10 false=H x
      rw [List.getD_append_right _ _ _ _ (by rw [rowlen]),rowlen] <;> rfl
    have comp (x : Fin 9 → Bool) : (D.wires (Y x)).getD k false=V ⟨g::gs,o⟩ k x := rfl
    obtain ⟨m,me⟩ : ∃ m, k+1-10=m+1 := ⟨k-10,by omega⟩
    have ban : v.val∉g.inputs := by
      apply avoid g
      rw [me]
      simp
    have tail : ∀ t∈gs.take (k-10), v.val∉t.inputs := by
      intro t ht
      apply avoid t
      rw [show k+1-10=(k-10)+1 by omega,List.take_succ_cons]
      exact List.mem_cons_of_mem _ ht
    have gateLaw (eq : k=10) : g.op=if b then .and else .or := by
      subst k
      apply headLaw v g b (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g (by simp)).1)
      · intro x y agree diff
        exact (first x).symm.trans (sense x y agree diff)
      · obtain ⟨x,_,atX,_⟩ := witness
        exact ⟨x,(first x).symm.trans atX⟩
    have sz : D.size=12 := by change gs.length=12;simp only [List.length_cons] at size;omega
    obtain ⟨x,bad⟩ := remaining v g D k b v0 v6 fan sz out paid lo hi gateLaw ban tail
    let z := if b then x v || V ⟨g::gs,o⟩ k x else x v && V ⟨g::gs,o⟩ k x
    have bound : v.val<(R x).length := by rw [rowlen];have := v.isLt;omega
    have stable : g.op.eval (g.inputs.map fun i => ((R x).set v.val z).getD i false)=H x := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i mem
      have ne : v.val≠i := fun eq => ban (eq ▸ mem)
      by_cases valid : i<(R x).length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
    have edit : (Y x).set v.val z=(R x).set v.val z ++ [H x] := by
      exact List.set_append_left v.val z bound
    apply bad
    change D.eval ((Y x).set v.val z)=F x
    rw [edit]
    have e := correct x
    change (gs.foldl emit ((R x).set v.val z ++ [g.op.eval (g.inputs.map fun i =>
      ((R x).set v.val z).getD i false)])).getD o false=F x at e
    rw [stable] at e
    exact e
