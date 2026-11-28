import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3310
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section
variable {α : Type} [DecidableEq α]

private def readSets (w : List (Finset α)) (g : Gate) :=
  g.inputs.map (fun i => w.getD i ∅)

private def outSet (w : List (Finset α)) (g : Gate) : Finset α :=
  if g.op = GateOp.or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅

def ports (o : ℕ) : List Gate → List (Finset α) → List (Finset α)
  | [], w => [w.getD o ∅]
  | g::gs, w =>
    (if g.op = GateOp.or then [] else readSets w g) ++ ports o gs (w++[outSet w g])

theorem ports_length (o : ℕ) (gs : List Gate)
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (w : List (Finset α)) :
    (ports o gs w).length ≤ 2*(gs.filter (fun g => !(g.op.eval [true,false]))).length+1 := by
  induction gs generalizing w with
  | nil => simp [ports]
  | cons g gs ih =>
    have tail := ih (fun k h => hm k (List.mem_cons_of_mem g h)) (w++[outSet w g])
    obtain ⟨op,ar⟩ := hm g (by simp)
    rcases op with h|h <;> simp [ports,h,GateOp.eval,readSets] at * <;> omega

private theorem at_append {β : Type} (w : List β) (x d : β) (i : ℕ) :
    (w++[x]).getD i d = if i<w.length then w.getD i d else if i=w.length then x else d := by
  rcases lt_trichotomy i w.length with hi|hi|hi
  · rw [List.getD_append _ _ _ _ hi, if_pos hi]
  · subst i
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k,hk⟩ : ∃ k, i-w.length=k+1 := ⟨i-w.length-1,by omega⟩
    simp [hk,show ¬i<w.length by omega,show i≠w.length by omega]

private def evG (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun vs g => vs++[g.op.eval (g.inputs.map fun i => vs.getD i false)]) w

private def Invariant (p : α) (L : Finset α) (w : List (Finset α)) (a b : List Bool) :=
  ∀ i, (b.getD i false=false → w.getD i ∅ ⊆ L) ∧
    (a.getD i false=true → b.getD i false=false → p ∈ w.getD i ∅)

private theorem forward (o : ℕ) (p : α) (L : Finset α) (gs : List Gate)
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (w : List (Finset α)) (a b : List Bool) (ha : a.length=w.length) (hb : b.length=w.length)
    (inv : Invariant p L w a b)
    (on : (evG gs a).getD o false=true) (off : (evG gs b).getD o false=false) :
    ∃ S ∈ ports o gs w, p∈S ∧ S⊆L := by
  induction gs generalizing w a b with
  | nil => exact ⟨w.getD o ∅,by simp [ports],(inv o).2 on off,(inv o).1 off⟩
  | cons g gs ih =>
    classical
    let rd (v : List Bool) := g.op.eval (g.inputs.map fun i => v.getD i false)
    let S := outSet w g
    let here := if g.op = GateOp.or then [] else readSets w g
    by_cases hit : ∃ s ∈ here, p∈s ∧ s⊆L
    · obtain ⟨s,hs,hp,hl⟩ := hit
      exact ⟨s,List.mem_append_left _ hs,hp,hl⟩
    have hstep : (rd b=false → S⊆L) ∧ (rd a=true → rd b=false → p∈S) := by
      obtain ⟨op,_⟩ := hm g (by simp)
      rcases op with hand | hor
      · constructor
        · simp [S,outSet,hand]
        · intro oa ob
          have allA : ∀ i ∈ g.inputs, a.getD i false=true := by
            simpa [rd,hand,GateOp.eval,List.all_map,Function.comp_def] using oa
          have exB : ∃ i ∈ g.inputs, b.getD i false=false := by
            by_contra! h
            have allB : ∀ i ∈ g.inputs, b.getD i false=true := by
              intro i hi
              cases v : b.getD i false <;> simp_all
            have eb : rd b=true := by
              simpa [rd,hand,GateOp.eval,List.all_map,Function.comp_def] using allB
            simp [eb] at ob
          obtain ⟨i,hi,hb'⟩ := exB
          exact (hit ⟨w.getD i ∅, by simp [here,hand,readSets]; exact ⟨i,hi,rfl⟩,
            (inv i).2 (allA i hi) hb',(inv i).1 hb'⟩).elim
      · have noB (h : rd b=false) (i) (hi : i ∈ g.inputs) : b.getD i false=false := by
          by_contra! bad
          have v : b.getD i false=true := by cases v : b.getD i false <;> simp_all
          have anyB : rd b=true := by
            simpa [rd,hor,GateOp.eval,List.any_map,Function.comp_def] using
              (show ∃ j ∈ g.inputs, b.getD j false=true from ⟨i,hi,v⟩)
          simp [anyB] at h
        constructor
        · intro f r hr
          have h : ∃ i ∈ g.inputs, r∈w.getD i ∅ := by simpa [S,outSet,hor] using hr
          obtain ⟨i,hi,mem⟩ := h
          exact (inv i).1 (noB f i hi) mem
        · intro oa ob
          have h : ∃ i ∈ g.inputs, a.getD i false=true := by
            simpa [rd,hor,GateOp.eval,List.any_map,Function.comp_def] using oa
          obtain ⟨i,hi,va⟩ := h
          have hp := (inv i).2 va (noB ob i hi)
          simpa [S,outSet,hor] using (show ∃ j ∈ g.inputs, p∈w.getD j ∅ from ⟨i,hi,hp⟩)
    have next : Invariant p L (w++[S]) (a++[rd a]) (b++[rd b]) := by
      intro i
      simp only [at_append,ha,hb]
      by_cases lo : i < w.length
      · simpa [lo] using inv i
      by_cases eq : i=w.length
      · simpa [lo,eq] using hstep
      · simp [lo,eq]
    obtain ⟨s,hs,hp,hl⟩ := ih (fun k h => hm k (List.mem_cons_of_mem g h))
      (w++[S]) (a++[rd a]) (b++[rd b]) (by simp [ha]) (by simp [hb]) next on off
    exact ⟨s,List.mem_append_right _ hs,hp,hl⟩
end

end PEqualNP.Outside.L_meta_3310
