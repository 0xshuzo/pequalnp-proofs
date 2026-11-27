import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8181

open PEqualNP.TopForm

theorem leafless_cover_square {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (color : ∀ a b, G.Adj a b → c a ≠ c b)
    (four : NoFourCycle G)
    (leafless : ¬ ∃ v w, G.Adj v w ∧ ∀ a, G.Adj v a → a = w)
    (T : Finset (Fin n)) (cov : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) :
    G.edgeFinset.card ≤ T.card * (T.card - 1) := by
  classical
  have triangle {u v w : Fin n} (uv : G.Adj u v) (uw : G.Adj u w) (vw : G.Adj v w) : False := by
    have h := color _ _ uv
    have k := color _ _ uw
    have l := color _ _ vw
    cases c u <;> cases c v <;> cases c w <;> simp_all
  have deg (u : Fin n) (hu : u ∈ T) : G.degree u ≤ T.card-1 := by
    have alt (v : Fin n) (uv : G.Adj u v) : ∃ w ∈ T.erase u, w = v ∨ G.Adj v w := by
      by_cases hv : v ∈ T
      · exact ⟨v,Finset.mem_erase.mpr ⟨uv.ne.symm,hv⟩,Or.inl rfl⟩
      · by_contra! no
        apply leafless
        refine ⟨v,u,uv.symm,?_⟩
        intro w vw
        by_contra neq
        have hw := (cov v w vw).resolve_left hv
        exact (no w (Finset.mem_erase.mpr ⟨neq,hw⟩)).2 vw
    let key (v : Fin n) := if h : G.Adj u v then (alt v h).choose else u
    have spec (v : Fin n) (h : G.Adj u v) : key v ∈ T.erase u ∧
        (key v = v ∨ G.Adj v (key v)) := by
      simpa only [key,dif_pos h] using (alt v h).choose_spec
    rw [← G.card_neighborFinset_eq_degree,← Finset.card_erase_of_mem hu]
    apply Finset.card_le_card_of_injOn key
    · exact fun v hv => (spec v (G.mem_neighborFinset.mp hv)).1
    · intro v hv w hw eq
      have uv := G.mem_neighborFinset.mp hv
      have uw := G.mem_neighborFinset.mp hw
      have sv := spec v uv
      have sw := spec w uw
      rw [← eq] at sw
      rcases sv.2 with kv | vk <;> rcases sw.2 with kw | wk
      · exact kv.symm.trans kw
      · exact (triangle uv uw (kv ▸ wk).symm).elim
      · exact (triangle uv uw (kw ▸ vk)).elim
      · have ne := (Finset.mem_erase.mp sv.1).1.symm
        apply Finset.card_le_one.mp (four u (key v) ne)
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,uv,vk.symm⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,uw,wk.symm⟩
  have incl : G.edgeFinset ⊆ T.biUnion G.incidenceFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have h := SimpleGraph.mem_edgeFinset.mp he
      rcases cov a b h with ha | hb
      · exact Finset.mem_biUnion.mpr ⟨a,ha,SimpleGraph.mem_incidenceFinset.mpr ⟨h,Sym2.mem_mk_left _ _⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨b,hb,SimpleGraph.mem_incidenceFinset.mpr ⟨h,Sym2.mem_mk_right _ _⟩⟩
  calc
    _ ≤ (T.biUnion G.incidenceFinset).card := Finset.card_le_card incl
    _ ≤ ∑ u ∈ T, (G.incidenceFinset u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ T, (T.card-1) := Finset.sum_le_sum fun u hu => by
      rw [G.card_incidenceFinset_eq_degree]
      exact deg u hu
    _ = _ := by simp

end PEqualNP.Outside.L_meta_8181
