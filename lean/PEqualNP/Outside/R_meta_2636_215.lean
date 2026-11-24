import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2636_215
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
    (∀ i j, G.Adj i j → i ∉ A) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    ∀ (v : Fin n) (P Z : Finset (Fin n)), (G.neighborSet v).ncard = 3 →
      v ∉ P → v ∉ Z → Disjoint P A → Disjoint P Z →
      (∀ p ∈ P, ∀ q ∈ P, ¬ G.Adj p q) → P.card+Z.card ≤ 2 →
      ∃ x : Fin n → Bool, x v = false ∧ (∀ p ∈ P, x p = true) ∧ (∀ z ∈ Z, x z = false) ∧
        graphFun G A x ≠ graphFun G A (Function.update x v true))
    (escape : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (P Z : Finset (Fin n)),
    FanInTwo C → C.output ≠ v.val → v ∉ P → v ∉ Z →
    (∃ x : Fin n → Bool, (∀ p ∈ P, x p=true) ∧ (∀ z ∈ Z, x z=false) ∧
      circuitFun n C x ≠ circuitFun n C (Function.update x v true)) →
    ∃ g ∈ C.gates, v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) ∧
      (g.op=.or → ∀ p ∈ P, p.val ∉ g.inputs) ∧ (g.op=.and → ∀ z ∈ Z, z.val ∉ g.inputs))
    (dense : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (v : Fin n),
      FanInTwo C → circuitFun n C = f → (∀ t, HasCircuitSize n f t → C.size ≤ t) →
      (∃ x y : Fin n → Bool, f (Function.update x v false) ≠ f (Function.update y v false)) →
      (let r := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
       4 ≤ r.length ∨ r.length = 3 ∧ ∃ g ∈ r, g.op ≠ .or) →
      ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, (G.neighborSet v).ncard=3) → (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      (∀ v ∉ A, let r := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        r.length ≤ 3 ∧ (r.length=3 → ∀ g ∈ r, g.op=.or) ∧
        ∀ P Z : Finset (Fin n), v∉P → v∉Z → Disjoint P A → Disjoint P Z →
          (∀ p ∈ P, ∀ q ∈ P, ¬ G.Adj p q) → P.card+Z.card ≤ 2 →
          ∃ g ∈ r, (g.op=.or → ∀ p ∈ P, p.val ∉ g.inputs) ∧ (g.op=.and → ∀ z ∈ Z, z.val ∉ g.inputs)) →
      ∃ v ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  intro n G A f degree girth iso edge spec s budget
  let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have eqF : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change f x=true ↔ (decide (∃ a ∈ A, x a=true) || decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true))=true
    rw [spec,Bool.or_eq_true]
    simp only [decide_eq_true_eq]
  have any : ∃ t, HasCircuitSize n f t := ⟨s,budget⟩
  obtain ⟨C,fan,cs,values⟩ := Nat.find_spec any
  have eval : circuitFun n C = f := funext values
  have least (t : ℕ) (h : HasCircuitSize n f t) : C.size ≤ t := cs.trans (Nat.find_min' any h)
  have minimal : IsMinimalCircuit n C :=
    ⟨fan,fun D hd same => least D.size ⟨D,hd,le_rfl,congrFun (same.trans eval)⟩⟩
  have cofactor (v : Fin n) :
      ∃ x y : Fin n → Bool, f (Function.update x v false) ≠ f (Function.update y v false) := by
    obtain ⟨i,j,ij⟩ := edge
    obtain ⟨w,wv,wa⟩ : ∃ w : Fin n, w ≠ v ∧ w ∉ A := by
      by_cases eq : i=v
      · exact ⟨j,eq ▸ ij.ne.symm,iso _ _ ij.symm⟩
      · exact ⟨i,eq,iso _ _ ij⟩
    obtain ⟨x,_,_,hz,diff⟩ := geometry n G A iso girth w ∅ {v} (degree _ wa)
      (by simp) (by simpa using wv) (by simp) (by simp) (by simp) (by simp)
    have xv := hz v (by simp)
    let y := Function.update x w true
    have yv : y v=false := (Function.update_of_ne wv.symm true x).trans xv
    refine ⟨x,y,?_⟩
    rwa [show Function.update x v false = x by rw [← xv,Function.update_eq_self],
      show Function.update y v false = y by rw [← yv,Function.update_eq_self],eqF]
  have keep (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i<xs.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp; omega),List.getD_append _ _ _ _ hi]
  have noOutput (v : Fin n) : C.output ≠ v.val := by
    intro bad
    obtain ⟨x,y,diff⟩ := cofactor v
    have off (z : Fin n → Bool) : f (Function.update z v false)=false := by
      rw [← values]
      unfold Circuit.eval Circuit.wires
      rw [bad,keep _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    exact diff ((off x).trans (off y).symm)
  let readers (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  by_cases heavy : ∃ v ∉ A, 4 ≤ (readers v).length ∨ (readers v).length=3 ∧ ∃ g ∈ readers v, g.op ≠ .or
  · obtain ⟨v,va,h⟩ := heavy
    obtain ⟨t,paid,restricted⟩ := dense n f C v fan eval least (cofactor v) h
    exact ⟨v,va,t,paid.trans (least s budget),restricted⟩
  · have good (v : Fin n) (va : v∉A) := fun h => heavy ⟨v,va,h⟩
    obtain ⟨v,va,t,paid,restricted⟩ := residual n G A C minimal (eval.trans eqF) degree girth iso edge (by
      intro v va
      have h := good v va
      refine ⟨by change (readers v).length ≤ 3; by_contra b; exact h (Or.inl (by omega)),?_,?_⟩
      · intro count g hg
        by_contra no
        exact h (Or.inr ⟨count,g,hg,no⟩)
      · intro P Z vp vz a d ind sz
        obtain ⟨x,_,xp,xz,changeAt⟩ := geometry n G A iso girth v P Z (degree v va) vp vz a d ind sz
        obtain ⟨g,hg,reads,yes,no⟩ := escape n C v P Z fan (noOutput v) vp vz
          ⟨x,xp,xz,by rw [eval,eqF]; exact changeAt⟩
        exact ⟨g,List.mem_filter.mpr ⟨hg,List.contains_iff_mem.mpr reads⟩,yes,no⟩)
    rw [eval] at restricted
    exact ⟨v,va,t,paid.trans (least s budget),restricted⟩
