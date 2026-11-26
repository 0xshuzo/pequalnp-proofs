import Mathlib

namespace PlaneCover

variable {α : Type*} [DecidableEq α]

/-- B and A are the singleton supports before and after enabling a point.
A zero weight certifies that the wire is insensitive to enabling that point. -/
theorem allocate (B A : ℕ → Finset α) (quiet : ℕ → Prop) (weight : ℕ → ℕ)
    (zero : ∀ k, weight k=0 → A k ⊆ B k)
    (step : ∀ k, quiet k → A k ⊆ B k ∨ ∃ u<k, ∃ v<k, weight u+weight v≤weight k ∧
      ((A k=A u ∪ A v ∧ B k=B u ∪ B v ∧ quiet u ∧ quiet v) ∨
       (A k=A u ∩ A v ∧ B k=B u ∩ B v ∧ (quiet u ∨ quiet v))))
    (k : ℕ) (silent : quiet k) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (k+1) ∧ (∀ t∈S, quiet t) ∧ S.card ≤ weight k ∧
      (A k \ B k) ⊆ S.biUnion B := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases step k silent with same | ⟨u,uk,v,vk,budget,mode⟩
    · refine ⟨∅,by simp,by simp,by simp,?_⟩
      intro a ha
      exact ((Finset.mem_sdiff.mp ha).2 (same (Finset.mem_sdiff.mp ha).1)).elim
    rcases mode with ⟨ap,bp,qu,qv⟩|⟨ap,bp,fall⟩
    · obtain ⟨U,ru,cu,su,hu⟩ := ih u uk qu
      obtain ⟨V,rv,cv,sv,hv⟩ := ih v vk qv
      refine ⟨U ∪ V,Finset.union_subset (ru.trans (Finset.range_mono (by omega)))
        (rv.trans (Finset.range_mono (by omega))),fun w hw => (Finset.mem_union.mp hw).elim (cu w) (cv w),?_,?_⟩
      · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add su sv).trans budget)
      · intro a ha
        obtain ⟨on,off⟩ := Finset.mem_sdiff.mp ha
        rw [ap,Finset.mem_union] at on
        rw [bp,Finset.mem_union,not_or] at off
        rcases on with on|on
        · obtain ⟨w,wu,aw⟩ := Finset.mem_biUnion.mp (hu (Finset.mem_sdiff.mpr ⟨on,off.1⟩))
          exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ wu,aw⟩
        · obtain ⟨w,wv,aw⟩ := Finset.mem_biUnion.mp (hv (Finset.mem_sdiff.mpr ⟨on,off.2⟩))
          exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_right _ wv,aw⟩
    · have chooseSide (l r : ℕ) (lk : l<k) (q : quiet l)
          (aE : A k=A l ∩ A r) (bE : B k=B l ∩ B r) (wt : weight l+weight r≤weight k) :
          ∃ S : Finset ℕ, S ⊆ Finset.range (k+1) ∧ (∀ t∈S, quiet t) ∧ S.card ≤ weight k ∧
            (A k \ B k) ⊆ S.biUnion B := by
        obtain ⟨S,rs,cs,ss,hs⟩ := ih l lk q
        by_cases fixed : weight r=0
        · refine ⟨S,rs.trans (Finset.range_mono (by omega)),cs,by omega,?_⟩
          intro a ha
          obtain ⟨on,off⟩ := Finset.mem_sdiff.mp ha
          rw [aE,Finset.mem_inter] at on
          rw [bE,Finset.mem_inter] at off
          exact hs (Finset.mem_sdiff.mpr ⟨on.1,fun ab => off ⟨ab,zero r fixed on.2⟩⟩)
        · refine ⟨insert l S,Finset.insert_subset (Finset.mem_range.mpr (by omega))
            (rs.trans (Finset.range_mono (by omega))),?_,?_,?_⟩
          · intro t ht
            exact (Finset.mem_insert.mp ht).elim (fun e => e ▸ q) (cs t)
          · have h := Finset.card_insert_le l S
            omega
          · intro a ha
            have on := (Finset.mem_sdiff.mp ha).1
            rw [aE,Finset.mem_inter] at on
            by_cases already : a ∈ B l
            · exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_insert_self _ _,already⟩
            · obtain ⟨w,ws,aw⟩ := Finset.mem_biUnion.mp (hs (Finset.mem_sdiff.mpr ⟨on.1,already⟩))
              exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_insert_of_mem ws,aw⟩
      rcases fall with qu|qv
      · exact chooseSide u v uk qu ap bp budget
      · exact chooseSide v u vk qv (ap.trans (Finset.inter_comm _ _)) (bp.trans (Finset.inter_comm _ _)) (by omega)

end PlaneCover
