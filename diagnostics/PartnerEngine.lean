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

private noncomputable def onePair (U V : Finset α) : Option (α × α) := by
  classical
  exact if h : ∃ z : α × α, U={z.1} ∧ z.2∈V ∧ z.2≠z.1 then some h.choose else none

private theorem onePair_spec (U V : Finset α) (p r : α) (u : U={p}) (hr : r∈V) (ne : r≠p) :
    ∃ t∈V, t≠p ∧ onePair U V = some (p,t) := by
  classical
  have ex : ∃ z : α × α, U={z.1} ∧ z.2∈V ∧ z.2≠z.1 := ⟨(p,r),u,hr,ne⟩
  let z := ex.choose
  have hz : U={z.1} ∧ z.2∈V ∧ z.2≠z.1 := ex.choose_spec
  have ep : z.1=p := by
    have inc : z.1∈U := hz.1 ▸ Finset.mem_singleton_self _
    simpa [u] using inc
  refine ⟨z.2,hz.2.1,by simpa [←ep] using hz.2.2,?_⟩
  rw [onePair,dif_pos ex]
  apply congrArg some
  exact Prod.ext ep rfl

noncomputable def earned (w : List (Finset α)) (g : Gate) : List (α × α) :=
  if g.op = GateOp.or then (readSets w g).filterMap (fun U => onePair U (outSet w g)) else []

noncomputable def partners : List Gate → List (Finset α) → List (α × α)
  | [], _ => []
  | g::gs,w => earned w g ++ partners gs (w++[outSet w g])

private def Signs (E : List (α × α)) (U : Finset α) :=
    ∀ p∈U, U={p} ∨ ∃ r∈U, r≠p ∧ (p,r)∈E

private theorem signs_mono {E F : List (α × α)} (h : ∀ e∈E, e∈F) {U : Finset α}
    (s : Signs E U) : Signs F U := by
  intro p hp
  rcases s p hp with done | ⟨r,hr,ne,he⟩
  · exact Or.inl done
  · exact Or.inr ⟨r,hr,ne,h _ he⟩

private theorem signs_new (E : List (α × α)) (w : List (Finset α)) (g : Gate)
    (sw : ∀ U∈w, Signs E U) : Signs (E++earned w g) (outSet w g) := by
  classical
  intro p hp
  by_cases op : g.op=GateOp.or
  · have ins : ∃ i∈g.inputs, p∈w.getD i ∅ := by simpa [outSet,op] using hp
    obtain ⟨i,hi,pi⟩ := ins
    let U := w.getD i ∅
    have goodU : Signs E U := by
      by_cases h : i<w.length
      · rw [show U=w[i] by simp [U,List.getD_eq_getElem _ _ h]]
        exact sw _ (List.getElem_mem _)
      · have none : U=∅ := List.getD_eq_default _ _ (by omega)
        simp [none,Signs]
    have sub : U⊆outSet w g := by
      intro r hr
      simpa [outSet,op] using (show ∃ j∈g.inputs, r∈w.getD j ∅ from ⟨i,hi,hr⟩)
    rcases goodU p pi with lone | ⟨r,hr,ne,he⟩
    · by_cases done : outSet w g={p}
      · exact Or.inl done
      have extra : ∃ r∈outSet w g, r≠p := by
        by_contra! fail
        apply done
        ext r
        constructor
        · intro hr; simpa using fail r hr
        · intro hr
          have ep : r=p := by simpa using hr
          simpa [ep] using hp
      obtain ⟨r,hr,ne⟩ := extra
      obtain ⟨t,ht,nt,chosen⟩ := onePair_spec U (outSet w g) p r lone hr ne
      refine Or.inr ⟨t,ht,nt,List.mem_append_right _ ?_⟩
      simp only [earned,if_pos op,List.mem_filterMap]
      exact ⟨U,List.mem_map.mpr ⟨i,hi,rfl⟩,chosen⟩
    · exact Or.inr ⟨r,sub hr,ne,List.mem_append_left _ he⟩
  · simp [outSet,op] at hp

theorem partner_ports (o : ℕ) (gs : List Gate) (w : List (Finset α)) (E : List (α × α))
    (sw : ∀ U∈w, Signs E U) :
    ∀ U∈ports o gs w, Signs (E++partners gs w) U := by
  induction gs generalizing w E with
  | nil =>
    intro U hu
    have ep : U=w.getD o ∅ := by simpa [ports] using hu
    by_cases h : o<w.length
    · rw [ep,List.getD_eq_getElem _ _ h]
      simpa [partners] using sw w[o] (List.getElem_mem _)
    · simp [ep,List.getD_eq_default _ _ (by omega : w.length ≤ o),Signs]
  | cons g gs ih =>
    let fresh := E++earned w g
    have enlarged (a) (h : a∈E) : a∈fresh := List.mem_append_left _ h
    have next : ∀ U∈ w++[outSet w g], Signs fresh U := by
      intro U h
      rcases List.mem_append.mp h with old | new
      · exact signs_mono enlarged (sw _ old)
      · have eq : U=outSet w g := by simpa using new
        exact eq ▸ signs_new E w g sw
    intro U h
    rcases List.mem_append.mp h with first | rest
    · by_cases hor : g.op=GateOp.or
      · simp [hor] at first
      have hmem : U∈readSets w g := by simpa [hor] using first
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
      by_cases j : i<w.length
      · rw [List.getD_eq_getElem _ _ j]
        exact signs_mono (fun e he => List.mem_append_left _ he) (sw w[i] (List.getElem_mem _))
      · simp [List.getD_eq_default _ _ (by omega : w.length ≤ i),Signs]
    · simpa [fresh,partners,List.append_assoc] using ih (w++[outSet w g]) fresh next U rest

theorem partners_length (gs : List Gate) (w : List (Finset α))
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) :
    (partners gs w).length ≤ 2*(gs.filter (fun g => g.op.eval [true,false])).length := by
  induction gs generalizing w with
  | nil => simp [partners]
  | cons g gs ih =>
    have tail := ih (w++[outSet w g]) (fun k h => hm k (List.mem_cons_of_mem g h))
    obtain ⟨op,ar⟩ := hm g (by simp)
    have le : ((readSets w g).filterMap (fun U => onePair U (outSet w g))).length ≤ g.inputs.length :=
      (List.length_filterMap_le _ _).trans (by simp [readSets])
    rcases op with h | h <;> simp [partners,earned,h,GateOp.eval] at * <;> omega

end
end PEqualNP.Outside.L_meta_3310
