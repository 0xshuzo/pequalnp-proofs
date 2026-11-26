import PEqualNP.Defs

open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_166.Normal
variable {V : Type} [DecidableEq V]
abbrev C (V : Type) := Clause V
def Clean (D : C V) : Prop := ∀ x, (x,true)∈D → (x,false)∉D
theorem clean_sub {D E : C V} (sub : D⊆E) (clean : Clean E) : Clean D :=
  fun x hp hn => clean x (sub hp) (sub hn)

def covered (new : List (C V)) (D : C V) := ∃ E ∈ new, E ⊆ D
def tight : List (C V) → Prop
  | [] => True
  | d::ds => Clean d ∧ ¬ covered ds d ∧ tight ds

theorem skip_taut_left {P N R : C V} {v : V} (pv : (v,true)∈P) (nv : (v,false)∈N)
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Clean R) (hp : ¬Clean P) :
    N⊆R := by
  classical
  obtain ⟨w,yes,no⟩ : ∃w, (w,true)∈P ∧ (w,false)∈P := by simpa [Clean] using hp
  have same : w=v := by
    by_contra ne
    apply hr w
    · rw [eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp [ne],yes⟩)
    · rw [eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,no⟩)
  subst w
  intro l hl
  rw [eq]
  by_cases e : l=(v,false)
  · subst l; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,no⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e,hl⟩)

theorem skip_taut_right {P N R : C V} {v : V} (pv : (v,true)∈P) (nv : (v,false)∈N)
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Clean R) (hn : ¬Clean N) :
    P⊆R := by
  classical
  obtain ⟨w,yes,no⟩ : ∃w, (w,true)∈N ∧ (w,false)∈N := by simpa [Clean] using hn
  have same : w=v := by
    by_contra ne
    apply hr w
    · rw [eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp,yes⟩)
    · rw [eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp [ne],no⟩)
  subst w
  intro l hl
  rw [eq]
  by_cases e : l=(v,true)
  · subst l; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp,yes⟩)
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hl⟩)

theorem normalize {F : Set (C V)} {ds : List (C V)} (d : IsDerivation F ds) :
    ∃ es, IsDerivation F es ∧ tight es ∧ es.length ≤ ds.length ∧
      ∀ R∈ds, Clean R → covered es R := by
  classical
  induction d with
  | nil => exact ⟨[],.nil,True.intro,by simp,by simp⟩
  | @ax ds R prev ax ih =>
    obtain ⟨es,trace,ok,size,cover⟩ := ih
    by_cases incl : Clean R ∧ ¬covered es R
    · refine ⟨R::es,IsDerivation.ax trace ax,⟨incl.1,incl.2,ok⟩,by simpa using size,?_⟩
      intro q mq cq
      rcases List.mem_cons.mp mq with rfl|m
      · exact ⟨_,by simp,Finset.Subset.rfl⟩
      · obtain ⟨E,h,sub⟩ := cover q m cq
        exact ⟨E,List.mem_cons_of_mem _ h,sub⟩
    · refine ⟨es,trace,ok,by simp; omega,?_⟩
      intro q mq cq
      rcases List.mem_cons.mp mq with rfl|m
      · exact Classical.byContradiction (fun nc => incl ⟨cq,nc⟩)
      · exact cover _ m cq
  | @res ds P N R prev p n res ih =>
    obtain ⟨es,trace,ok,size,cover⟩ := ih
    by_cases incl : Clean R ∧ ¬covered es R
    · obtain ⟨v,pv,nv,eq⟩ := res
      have cp : Clean P := by
        by_contra bad
        have sub := skip_taut_left pv nv eq incl.1 bad
        obtain ⟨E,h,s⟩ := cover N n (clean_sub sub incl.1)
        exact incl.2 ⟨E,h,Finset.Subset.trans s sub⟩
      have cn : Clean N := by
        by_contra bad
        have sub := skip_taut_right pv nv eq incl.1 bad
        obtain ⟨E,h,s⟩ := cover P p (clean_sub sub incl.1)
        exact incl.2 ⟨E,h,Finset.Subset.trans s sub⟩
      obtain ⟨A,ha,sa⟩ := cover P p cp
      obtain ⟨B,hb,sb⟩ := cover N n cn
      have av : (v,true)∈A := by
        by_contra miss
        apply incl.2
        refine ⟨A,ha,?_⟩
        intro l hl; rw [eq]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => miss (e ▸ hl),sa hl⟩)
      have bv : (v,false)∈B := by
        by_contra miss
        apply incl.2
        refine ⟨B,hb,?_⟩
        intro l hl; rw [eq]
        exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => miss (e ▸ hl),sb hl⟩)
      let E := A.erase (v,true) ∪ B.erase (v,false)
      have sub : E⊆R := by
        intro l hl
        rw [eq]
        rcases Finset.mem_union.mp hl with h|h
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,sa (Finset.mem_erase.mp h).2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,sb (Finset.mem_erase.mp h).2⟩)
      have fresh : ¬covered es E := by
        rintro ⟨T,m,s⟩
        exact incl.2 ⟨T,m,Finset.Subset.trans s sub⟩
      refine ⟨E::es,.res trace ha hb ⟨v,av,bv,rfl⟩,⟨clean_sub sub incl.1,fresh,ok⟩,by simpa using size,?_⟩
      intro q mq cq
      rcases List.mem_cons.mp mq with rfl|m
      · exact ⟨E,by simp,sub⟩
      · obtain ⟨T,h,st⟩ := cover q m cq
        exact ⟨T,List.mem_cons_of_mem _ h,st⟩
    · refine ⟨es,trace,ok,by simp; omega,?_⟩
      intro q mq cq
      rcases List.mem_cons.mp mq with rfl|m
      · exact Classical.byContradiction (fun nc => incl ⟨cq,nc⟩)
      · exact cover _ m cq

theorem refutation_tight {F : Set (C V)} {ds : List (C V)} (d : IsRefutation F ds) :
    ∃ es, IsRefutation F es ∧ tight es ∧ es.length≤ds.length := by
  obtain ⟨es,proof,form,size,cover⟩ := normalize d.1
  obtain ⟨E,m,sub⟩ := cover ∅ d.2 (by simp [Clean])
  have e : E=∅ := Finset.subset_empty.mp sub
  exact ⟨es,⟨proof,e ▸ m⟩,form,size⟩
end PEqualNP.Outside.L_pcx_166.Normal
