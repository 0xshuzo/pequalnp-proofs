import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18723.Accounting

abbrev Edges (n : ℕ) := Finset (Fin n × Fin n)
def cover (A : Edges n) (T : Finset (Fin n)) := ∀ e ∈ A, e.1 ∈ T ∨ e.2 ∈ T
def cut (A : Edges n) (S : Finset (Fin n)) : Edges n :=
  A.filter fun e => e.1 ∉ S ∧ e.2 ∉ S
def touches (e : Fin n × Fin n) (v : Fin n) := e.1=v ∨ e.2=v

theorem cut_cover (A : Edges n) (T S : Finset (Fin n)) (h : cover A T) : cover (cut A S) (T\S) := by
  intro e he
  obtain ⟨ha,x,y⟩ := Finset.mem_filter.mp he
  rcases h e ha with left | right
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨left,x⟩)
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨right,y⟩)

private theorem countDrop {A B W : Finset α} [DecidableEq α] (sub : B ⊆ A) (inside : W ⊆ A)
    (apart : Disjoint B W) : B.card + W.card ≤ A.card := by
  rw [← Finset.card_union_of_disjoint apart]
  exact Finset.card_le_card (Finset.union_subset sub inside)

theorem accounting (A : Edges n) (v u w : Fin n) (T : Finset (Fin n)) (hc : cover A T)
    (uw : u ≠ w) (vu : v ≠ u) (vw : v ≠ w)
    (eu : (v,u) ∈ A ∨ (u,v) ∈ A) (ew : (v,w) ∈ A ∨ (w,v) ∈ A) :
    (∃ R, cover (cut A {v}) R ∧ (cut A {v}).card + R.card + 3 ≤ A.card+T.card) ∨
    (∃ R, cover (cut A {v,u,w}) R ∧ (cut A {v,u,w}).card + R.card + 6 ≤ A.card+T.card) := by
  classical
  let B := cut A {v}
  let K := cut A {v,u,w}
  have endpoints (z : Fin n) (hz : (v,z) ∈ A ∨ (z,v) ∈ A) :
      ∃ e ∈ A, touches e v ∧ touches e z ∧ (∀ p, touches e p → p=v ∨ p=z) := by
    rcases hz with h|h
    · exact ⟨(v,z),h,Or.inl rfl,Or.inr rfl,fun p hp => hp.elim (fun q => Or.inl q.symm) (fun q => Or.inr q.symm)⟩
    · exact ⟨(z,v),h,Or.inr rfl,Or.inl rfl,fun p hp => hp.elim (fun q => Or.inr q.symm) (fun q => Or.inl q.symm)⟩
  obtain ⟨a,ha,av,au,ends⟩ := endpoints u eu
  obtain ⟨b,hb,bv,bw,_⟩ := endpoints w ew
  have ab : a ≠ b := by
    intro q
    rcases ends w (q.symm ▸ bw) with h|h
    · exact vw h.symm
    · exact uw h.symm
  have away {e : Fin n × Fin n} {S : Finset (Fin n)} (z : Fin n) (ts : touches e z) (mem : z ∈ S) :
      e ∉ cut A S := by
    intro h
    have no := (Finset.mem_filter.mp h).2
    rcases ts with l | r
    · exact no.1 (l.symm ▸ mem)
    · exact no.2 (r.symm ▸ mem)
  have na : a ∉ B := away v av (by simp)
  have nb : b ∉ B := away v bv (by simp)
  have cutTwo : B.card+2 ≤ A.card := by
    have pay := countDrop (Finset.filter_subset _ _) (show ({a,b} : Edges n) ⊆ A by simpa using And.intro ha hb)
      (show Disjoint B {a,b} by simpa [Finset.disjoint_insert_right] using And.intro na nb)
    simpa [ab] using pay
  have left (R : Finset (Fin n)) (hr : cover B R) (size : R.card < T.card) :
      ∃ R, cover (cut A {v}) R ∧ (cut A {v}).card + R.card + 3 ≤ A.card+T.card :=
    ⟨R,hr,by change B.card + R.card + 3 ≤ _; omega⟩
  by_cases vin : v ∈ T
  · apply Or.inl
    apply left (T.erase v)
    · simpa [Finset.sdiff_singleton_eq_erase] using cut_cover A T {v} hc
    · exact Finset.card_erase_lt_of_mem vin
  have inT (z : Fin n) (ez : (v,z)∈A ∨ (z,v)∈A) : z ∈ T := by
    rcases ez with h|h
    · exact (hc _ h).resolve_left vin
    · exact (hc _ h).resolve_right vin
  have ut := inT u eu
  have wt := inT w ew
  by_cases uc : cover B (T.erase u)
  · exact Or.inl (left _ uc (Finset.card_erase_lt_of_mem ut))
  by_cases wc : cover B (T.erase w)
  · exact Or.inl (left _ wc (Finset.card_erase_lt_of_mem wt))
  have privateEdge (z : Fin n) (fail : ¬ cover B (T.erase z)) :
      ∃ e ∈ B, touches e z ∧ e.1 ∉ T.erase z ∧ e.2 ∉ T.erase z := by
    unfold cover at fail
    push_neg at fail
    obtain ⟨e,he,h1,h2⟩ := fail
    refine ⟨e,he,?_,h1,h2⟩
    rcases hc e ((Finset.mem_filter.mp he).1) with h|h
    · exact Or.inl (by by_contra q; exact h1 (Finset.mem_erase.mpr ⟨q,h⟩))
    · exact Or.inr (by by_contra q; exact h2 (Finset.mem_erase.mpr ⟨q,h⟩))
  obtain ⟨c,hcB,cu,c1,c2⟩ := privateEdge u uc
  obtain ⟨d,hdB,dw,_,_⟩ := privateEdge w wc
  have cd : c ≠ d := by
    intro eq
    have ww : w ∈ T.erase u := Finset.mem_erase.mpr ⟨uw.symm,wt⟩
    rcases (show touches c w from eq.symm ▸ dw) with e|e
    · exact c1 (e.symm ▸ ww)
    · exact c2 (e.symm ▸ ww)
  have ac : a ≠ c := fun e => na (e.symm ▸ hcB)
  have ad : a ≠ d := fun e => na (e.symm ▸ hdB)
  have bc : b ≠ c := fun e => nb (e.symm ▸ hcB)
  have bd : b ≠ d := fun e => nb (e.symm ▸ hdB)
  have nc : c ∉ K := away u cu (by simp)
  have nd : d ∉ K := away w dw (by simp)
  have nkA : a ∉ K := away v av (by simp)
  have nkB : b ∉ K := away v bv (by simp)
  have cutFour : K.card+4 ≤ A.card := by
    have cc : c∈A := (Finset.mem_filter.mp hcB).1
    have dd : d∈A := (Finset.mem_filter.mp hdB).1
    have pay := countDrop (Finset.filter_subset _ _) (show ({a,b,c,d} : Edges n) ⊆ A by simp [ha,hb,cc,dd])
      (show Disjoint K {a,b,c,d} by simp [Finset.disjoint_insert_right,nkA,nkB,nc,nd])
    simpa [ab,ac,ad,bc,bd,cd] using pay
  apply Or.inr
  refine ⟨T\{v,u,w},cut_cover A T _ hc,?_⟩
  have sub : T\{v,u,w} ⊆ T := Finset.sdiff_subset
  have wid : ({u,w} : Finset (Fin n)) ⊆ T := by simp [ut,wt]
  have dis : Disjoint (T\{v,u,w}) {u,w} := by simp [Finset.disjoint_insert_right]
  have two := countDrop sub wid dis
  simp [uw] at two
  change K.card+_+6 ≤ _
  omega

end PEqualNP.Outside.L_meta_18723.Accounting
