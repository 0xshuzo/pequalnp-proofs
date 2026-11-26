import Mathlib
import PEqualNP.Outside.L_meta_17589

namespace DegreeTwoLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_17589_aux

variable {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}

def SeparatedAt (G : Fin n → Fin n → Prop) (v : Fin n) : Prop :=
  ∀ w, v ≠ w → ∃ z, G v z ∧ ¬ G w z

theorem local_dom_pure (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hsep : SeparatedAt G v) (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨z, hvz, huz⟩ := hsep u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

theorem local_first_branch (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hsep : SeparatedAt G v) (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (local_dom_pure hsym hirr hS hC v hsep _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

theorem local_inelig_pure (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hsep : SeparatedAt G v) (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (local_dom_pure hsym hirr hS hC v hsep w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem local_meeting (hzero : supp n D (outW n D) = ∅) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [hzero]; simp,
      by rw [hzero]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩


theorem strict_core_cover (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hfree : NoFourCycle H) (h : StrictLive n D) (hC : sem_Comp n H.Adj D) :
    ∃ T : Finset (Fin n),
      (∀ u v, H.Adj u v → 2 ≤ H.degree u → 2 ≤ H.degree v → u ∈ T ∨ v ∈ T) ∧
      n + T.card ≤ D.length+1 := by
  classical
  have hsym : ∀ u v, H.Adj u v → H.Adj v u := fun _ _ h => h.symm
  have hirr := H.loopless.irrefl
  have hzero : supp n D (outW n D) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨a,b,hab,ha,hb⟩ := (hC _).mp (mem_supp.mp hu)
    have hau : a = u := of_decide_eq_true ha
    have hbu : b = u := of_decide_eq_true hb
    exact hab.ne (hau.trans hbu.symm)
  have two (v : Fin n) (hd : 2 ≤ H.degree v) : ∃ a b, H.Adj v a ∧ H.Adj v b ∧ a ≠ b := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < (H.neighborFinset v).card from hd)
    exact ⟨a,b,(H.mem_neighborFinset v a).mp ha,(H.mem_neighborFinset v b).mp hb,hab⟩
  have sep (v : Fin n) (hd : 2 ≤ H.degree v) : SeparatedAt H.Adj v := by
    intro w hvw
    obtain ⟨a,b,ha,hb,hab⟩ := two v hd
    by_cases hwa : H.Adj w a
    · refine ⟨b,hb,fun hwb => ?_⟩
      have both : 1 < (Finset.univ.filter fun t => H.Adj v t ∧ H.Adj w t).card :=
        Finset.one_lt_card.mpr ⟨a, by simp [ha,hwa], b, by simp [hb,hwb], hab⟩
      exact (Nat.not_lt_of_ge (hfree v w hvw)) both
    · exact ⟨a,ha,hwa⟩
  let T := (eligSet n D).filter (fun v => 2 ≤ H.degree v)
  have source (v : Fin n) (hv : v ∈ T) :
      ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} := by
    obtain ⟨b,hb,hs,_⟩ := local_first_branch hsym hirr h.1 hC v
      (sep _ (Finset.mem_filter.mp hv).2) (Finset.mem_filter.mp hv).1
    exact ⟨b,hb,hs⟩
  let b (v : Fin n) := if hv : v ∈ T then (source v hv).choose else 0
  have bs (v : Fin n) (hv : v ∈ T) : 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} := by
    simpa only [b,dif_pos hv] using (source v hv).choose_spec
  have hit : ∀ u v, H.Adj u v → 2 ≤ H.degree u → 2 ≤ H.degree v → u ∈ T ∨ v ∈ T := by
    intro u v huv huDeg hvDeg
    by_contra hc
    have hu : u ∈ ineligSet n D := sem_mem_inelig.mpr
      (fun hue => hc (Or.inl (Finset.mem_filter.mpr ⟨hue,huDeg⟩)))
    have hv : v ∈ ineligSet n D := sem_mem_inelig.mpr
      (fun hve => hc (Or.inr (Finset.mem_filter.mpr ⟨hve,hvDeg⟩)))
    obtain ⟨j,hj,_,_,hju,_,s,hsu,_,hsv,_⟩ := local_meeting hzero h.1 hC huv
    obtain ⟨a,b',ha,hb',hab⟩ := two u huDeg
    have other : ∃ z, H.Adj u z ∧ z ≠ v := by
      by_cases he : a = v
      · exact ⟨b',hb',fun h => hab (he.trans h.symm)⟩
      · exact ⟨a,ha,he⟩
    obtain ⟨z,hz,hzv⟩ := other
    obtain ⟨k,hk,_,_,hku,_,t,htu,_,htz,_⟩ := local_meeting hzero h.1 hC hz
    have one := carrier_flow_union h {u} (by rw [hzero]; simp)
    rw [sem_inelig_surplus hu,Finset.card_singleton] at one
    have le : (exitArcs n D (carrierT n D {u})).card ≤ 1 := by omega
    have same := Finset.card_le_one.mp le (j,s) (sem_mem_exit1.mpr ⟨hj,hsu,hju⟩)
      (k,t) (sem_mem_exit1.mpr ⟨hk,htu,hku⟩)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    have pure := local_inelig_pure hsym hirr h.1 hC (sep v hvDeg) hv hsv
    rw [pure,Finset.mem_singleton] at htz
    exact hzv htz
  have inj : Set.InjOn (fun v : Fin n => (⟨b v,0⟩ : Σ _ : ℕ, ℕ)) T := by
    intro u hu v hv eq
    have w : b u = b v := congrArg Sigma.fst eq
    have s1 := (bs u hu).2
    rw [w,(bs v hv).2] at s1
    simpa using s1.symm
  have counted : T.card ≤ (units n D).card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin n => (⟨b v,0⟩ : Σ _ : ℕ, ℕ))
    · intro v hv
      have hb := (bs v hv).1
      have hj := lt_of_fanout_pos h.1 (show 1 ≤ fanout D (b v) by omega)
      simp only [units, Finset.mem_sigma, sb_mem_inner, Finset.mem_range]
      exact ⟨hj,by omega⟩
    · exact inj
  rw [card_units] at counted
  have hbudget := surplus_identity h
  exact ⟨T,hit,by omega⟩

end DegreeTwoLocal

namespace DegreeTwoLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_17589_aux

theorem circuit_core_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : NoFourCycle G) (nonisolated : ∀ v, ∃ u, G.Adj v u)
    (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G.Adj x) :
    ∃ T : Finset (Fin n),
      (∀ u v, G.Adj u v → 2 ≤ G.degree u → 2 ≤ G.degree v → u ∈ T ∨ v ∈ T) ∧
      n + T.card ≤ C.size+1 := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨∅,fun u => Fin.elim0 u,by simp⟩
  have nosingle (i : Fin n) : ¬ sem_Edge G.Adj (fun k => decide (k = i)) := by
    rintro ⟨u,v,huv,hu,hv⟩
    have hui : u = i := of_decide_eq_true hu
    have hvi : v = i := of_decide_eq_true hv
    exact huv.ne (hui.trans hvi.symm)
  have positive (i j : Fin n) (hij : G.Adj i j) :
      sem_Edge G.Adj (fun k => decide (k = i) || decide (k = j)) :=
    ⟨i,j,hij,by simp,by simp⟩
  obtain ⟨D,hlive,hlen,hval⟩ := normalize_strictLive (n := n) C hmono
    (by
      intro b
      let v : Fin n := ⟨0, by omega⟩
      cases b
      · obtain ⟨u,hu⟩ := nonisolated v
        refine ⟨_, ?_⟩
        rw [Ne, Bool.not_eq_false]
        exact (hC _).2 (positive v u hu)
      · exact ⟨_, fun he => nosingle v ((hC _).1 he)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun he => nosingle i ((hC _).1 ?_)⟩
      rw [he]
      simp)
    (by
      intro i
      obtain ⟨j,hij⟩ := nonisolated i
      refine ⟨fun k => decide (k = j), fun k => decide (k = i) || decide (k = j),
        fun k hk => by simp [hk], fun he => nosingle j ((hC _).1 ?_)⟩
      rw [he]
      exact (hC _).2 (positive i j hij))
  have hcomp : sem_Comp n G.Adj D := fun x => by rw [hval x]; exact hC x
  obtain ⟨T,hcov,hs⟩ := strict_core_cover G hfree hlive hcomp
  exact ⟨T,hcov,by omega⟩

end DegreeTwoLocal
