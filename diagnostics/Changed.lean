import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Changed4267

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem child : ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → List.Forall₂ (fun g h : Gate => g.op = h.op ∧
      List.Forall₂ (fun i j => j = i+1 ∨ j=0 ∧ (i=a ∨ i=b)) g.inputs h.inputs) C.gates D.gates →
    (C.wires [false,false,true,false,false,false,false]).getD C.output false ≠
      (D.wires [true,false,false,true,false,false,false,false]).getD (C.output+1) false →
    0 < ((C.gates.zip D.gates).filter (fun z : Gate × Gate =>
       !(z.1.op.eval [true,false] && z.1.inputs.contains 2) && z.2.inputs.contains 0)).length := by
  intro C D a b fan edits different
  let sel := (fun g : Gate => g.op.eval [true,false] && g.inputs.contains 2)
  let exc := (fun z : Gate × Gate =>
       !(z.1.op.eval [true,false] && z.1.inputs.contains 2) && z.2.inputs.contains 0)
  let R (g h : Gate) := g.op = h.op ∧
    List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ (i=a ∨ i=b)) g.inputs h.inputs
  by_contra hbad
  have empty : ((C.gates.zip D.gates).filter exc) = [] := by
    apply List.length_eq_zero_iff.mp
    change ¬ 0 < ((C.gates.zip D.gates).filter exc).length at hbad
    omega
  have onlyOr (p : Gate × Gate) (hp : p∈C.gates.zip D.gates) (hz : 0∈p.2.inputs) : sel p.1=true := by
    by_contra no
    have sf : sel p.1=false := by cases h : sel p.1 <;> simp_all
    have m : p∈(C.gates.zip D.gates).filter exc := List.mem_filter.mpr ⟨hp,by
      change (!sel p.1 && p.2.inputs.contains 0) = true
      simp [sf,hz]⟩
    rw [empty] at m
    contradiction
  have intact {l m : List Nat} (r : List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ (i=a ∨ i=b)) l m)
      (no : 0∉m) (w : List Bool) :
      m.map (fun j => (true::w).getD j false) = l.map (fun i => w.getD i false) := by
    induction r with
    | nil => rfl
    | @cons i j l m hr rr ih =>
      have nj : j≠0 := fun h => no (List.mem_cons.mpr (Or.inl h.symm))
      have tail : 0∉m := fun h => no (List.mem_cons_of_mem j h)
      have s : j=i+1 := hr.resolve_right (fun e => nj e.1)
      simp only [List.map_cons,s,List.getD_cons_succ,ih tail]
  let ok (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)
  have same {gs hs : List Gate} (r : List.Forall₂ R gs hs) :
      (∀ g∈gs, ok g) → (∀ p∈gs.zip hs, 0∈p.2.inputs → sel p.1=true) →
      ∀ w : List Bool, 2<w.length → w.getD 2 false=true →
      hs.foldl step (true::w) = true :: gs.foldl step w := by
    induction r with
    | nil => intros; rfl
    | @cons g h gs hs hr rr ih =>
      intro ops only w len bit
      obtain ⟨op,pins⟩ := hr
      have state : step (true::w) h = true :: step w g := by
        unfold step
        change true :: (w ++ [_]) = true :: (w ++ [_])
        apply congrArg (fun z : Bool => true :: (w ++ [z]))
        by_cases hz : 0∈h.inputs
        · have picked := only (g,h) (by simp) hz
          obtain ⟨ao,has2⟩ : g.op.eval [true,false]=true ∧ 2∈g.inputs := by simpa [sel] using picked
          have legal := ops g List.mem_cons_self
          change g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at legal
          have og : g.op=GateOp.or := by
            rcases legal with h | h | h
            · simp [h,GateOp.eval] at ao
            · exact h
            · simp [h,GateOp.eval] at ao
          have oh := op.symm.trans og
          rw [oh,og]
          apply Bool.eq_iff_iff.mpr
          simp only [GateOp.eval,List.any_eq_true,List.mem_map]
          constructor <;> intro _
          · exact ⟨true,⟨2,has2,bit⟩,rfl⟩
          · exact ⟨true,⟨0,hz,rfl⟩,rfl⟩
        · rw [← op,intact pins hz w]
      rw [List.foldl_cons,List.foldl_cons,state]
      apply ih (fun q hq => ops q (List.mem_cons_of_mem _ hq))
        (fun p hp hz => only p (List.mem_cons_of_mem _ hp) hz)
      · simp [step]; omega
      · change (w ++ [_]).getD 2 false=true
        rw [List.getD_append _ _ _ _ len,bit]
  have row := same (show List.Forall₂ R C.gates D.gates from edits)
    (fun g hg => (fan g hg).1) onlyOr [false,false,true,false,false,false,false] (by decide) rfl
  apply different
  change (C.gates.foldl step _).getD C.output false = (D.gates.foldl step _).getD (C.output+1) false
  rw [row]
  rfl

end Changed4267
