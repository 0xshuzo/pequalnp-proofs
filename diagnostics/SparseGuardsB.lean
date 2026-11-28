import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3310
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section
variable {α : Type} [DecidableEq α]

private instance gateOpDec : DecidableEq GateOp := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)


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
      · rw [show U=w[i] by exact List.getD_eq_getElem _ _ h]
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
    · rw [ep, List.getD_eq_default _ _ (by omega : w.length ≤ o)]; simp [Signs]
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
      · rw [List.getD_eq_default _ _ (by omega : w.length ≤ i)]; simp [Signs]
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
private def labels (N : ℕ) : Fin (N+N) → Finset (Fin N) :=
  Fin.addCases (fun p => {p}) (fun _ => ∅)

section
variable {α : Type} [DecidableEq α] [Fintype α]

noncomputable def guardSet (E : List (α × α)) (p : α) : Finset α :=
  ((E.toFinset.filter fun z => z.1=p ∧ z.2≠p).image Prod.snd)

theorem guard_mass (E : List (α × α)) : ∑ p : α, (guardSet E p).card ≤ E.length := by
  classical
  have localBound (p : α) : (guardSet E p).card ≤ (E.toFinset.filter (fun z => z.1=p)).card := by
    apply Finset.card_image_le.trans
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.1⟩
  calc
    _ ≤ ∑ p : α, (E.toFinset.filter (fun z => z.1=p)).card := Finset.sum_le_sum (fun p _ => localBound p)
    _ = E.toFinset.card := (Finset.card_eq_sum_card_fiberwise (s:=E.toFinset) (t:=Finset.univ)
          (f:=Prod.fst) (fun _ _ => Finset.mem_univ _)).symm
    _ ≤ E.length := List.toFinset_card_le _

theorem guard_hits {E : List (α × α)} {U : Finset α} (sig : Signs E U) (p : α) (hp : p∈U) :
    U={p} ∨ ∃ r∈U, r∈guardSet E p := by
  rcases sig p hp with single | ⟨r,hr,ne,he⟩
  · exact Or.inl single
  · refine Or.inr ⟨r,hr,Finset.mem_image.mpr ⟨(p,r),?_,rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨by simpa using he,rfl,ne⟩

theorem guard_omits (E : List (α × α)) (p : α) : p∉guardSet E p := by
  classical
  intro hp
  obtain ⟨z,hz,zp⟩ := Finset.mem_image.mp hp
  exact (Finset.mem_filter.mp hz).2.2 zp
end

theorem physical_guards (N : ℕ) (C : Circuit) (hm : Monotone2 C) :
    ∃ G : Fin N → Finset (Fin N), (∀ p, p∉G p) ∧
      (∑ p, (G p).card) ≤ 2*(C.gates.filter (fun g => g.op.eval [true,false])).length ∧
      ∀ U∈ports C.output C.gates (List.ofFn (labels N)), ∀ p∈U, U={p} ∨ ∃ r∈U, r∈G p := by
  classical
  let w := List.ofFn (labels N)
  let E := partners C.gates w
  have sw : ∀ U∈w, Signs [] U := by
    intro U h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · rw [show labels N (Fin.castAdd N p)={p} from Fin.addCases_left ..]
      intro r hr
      have eq : r=p := by simpa using hr
      exact Or.inl (by rw [eq])
    · rw [show labels N (Fin.natAdd N l)=∅ from Fin.addCases_right ..]
      simp [Signs]
  refine ⟨guardSet E,guard_omits E,(guard_mass E).trans ?_,?_⟩
  · apply partners_length
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm g hg
  · intro U hU p hp
    have sig := partner_ports C.output C.gates w [] sw U hU
    apply guard_hits (E:=E) _ p hp
    simpa [E] using sig

theorem strict_sparse_guards (N q : ℕ) (C : Circuit) (hm : Monotone2 C)
    (h : 100*(C.gates.filter (fun g => g.op.eval [true,false])).length < N*q) :
    ∃ G : Fin N → Finset (Fin N), (∀ p, p∉G p) ∧
      50*(∑ p, (G p).card)<N*q ∧
      ∀ U∈ports C.output C.gates (List.ofFn (labels N)), ∀ p∈U, U={p} ∨ ∃ r∈U, r∈G p := by
  obtain ⟨G,avoid,budget,hit⟩ := physical_guards N C hm
  exact ⟨G,avoid,by omega,hit⟩

end PEqualNP.Outside.L_meta_3310
