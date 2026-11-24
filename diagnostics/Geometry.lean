import Mathlib
import PEqualNP.Defs

namespace Geometry2636
open PEqualNP.MetaComplexity.NestedCover

theorem geometry (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    (∀ i j, G.Adj i j → i ∉ A) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    ∀ (v : Fin n) (P Z : Finset (Fin n)), (G.neighborSet v).ncard = 3 →
      v ∉ P → v ∉ Z → Disjoint P A → Disjoint P Z →
      (∀ p ∈ P, ∀ q ∈ P, ¬ G.Adj p q) → P.card+Z.card ≤ 2 →
      ∃ x : Fin n → Bool, x v = false ∧ (∀ p ∈ P, x p = true) ∧ (∀ z ∈ Z, x z = false) ∧
        graphFun G A x ≠ graphFun G A (Function.update x v true) := by
  classical
  intro iso girth v P Z degree vp vz clean dis ind small
  have unique (p z a b : Fin n) (hpz : p ≠ z) (hpa : G.Adj p a) (hza : G.Adj z a)
      (hpb : G.Adj p b) (hzb : G.Adj z b) : a=b := by
    by_contra hab
    let w : G.Walk p p := .cons hpa (.cons hza.symm (.cons hzb (.cons hpb.symm .nil)))
    have hc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [w,hpz.symm,hab,hza.ne.symm,hpa.ne.symm,hzb.ne,hpb.ne.symm]
      · simp [w]
    have h := girth p w hc
    simp [w] at h
  let N := G.neighborFinset v
  have hN : N.card=3 := by
    change (G.neighborFinset v).card=3
    simpa only [← Set.ncard_coe_finset,SimpleGraph.coe_neighborFinset] using degree
  let conflict (p : Fin n) := N.filter (G.Adj p)
  have one : ∀ p ∈ P, (conflict p).card ≤ 1 := by
    intro p hp
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hpb⟩ := Finset.mem_filter.mp hb
    exact unique v p a b (fun e => vp (e ▸ hp)) (G.mem_neighborFinset.mp ha) hpa (G.mem_neighborFinset.mp hb) hpb
  have conflictBound := Finset.card_biUnion_le_card_mul P conflict 1 one
  have someU : ∃ u ∈ N, u ∉ Z ∪ P.biUnion conflict := by
    by_contra! hn
    have sub : N ⊆ Z ∪ P.biUnion conflict := hn
    have a := Finset.card_le_card sub
    have b := Finset.card_union_le Z (P.biUnion conflict)
    omega
  obtain ⟨u,un,free⟩ := someU
  have vu : G.Adj v u := G.mem_neighborFinset.mp un
  have uz : u ∉ Z := fun h => free (Finset.mem_union_left _ h)
  have noCross (p : Fin n) (hp : p∈P) : ¬ G.Adj p u := fun h =>
    free (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨un,h⟩⟩))
  let x (i : Fin n) := decide (i∈P ∨ i=u)
  have desc (i : Fin n) : x i=true ↔ i∈P ∨ i=u := by simp [x]
  have zero : graphFun G A x = false := by
    cases h : graphFun G A x with
    | false => rfl
    | true =>
      change (decide (∃ a ∈ A, x a = true) || decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) = true at h
      simp only [Bool.or_eq_true,decide_eq_true_eq] at h
      rcases h with ⟨a,ha,hx⟩|⟨a,b,ab,ha,hb⟩
      · rcases (desc _).mp hx with hp|rfl
        · exact False.elim (Finset.disjoint_left.mp clean hp ha)
        · exact False.elim (iso _ _ vu.symm ha)
      · rcases (desc _).mp ha with ap|rfl <;> rcases (desc _).mp hb with bp|rfl
        · exact False.elim (ind _ ap _ bp ab)
        · exact False.elim (noCross _ ap ab)
        · exact False.elim (noCross _ bp ab.symm)
        · exact False.elim (G.loopless.irrefl _ ab)
  have yes : graphFun G A (Function.update x v true) = true := by
    change (decide _ || decide _) = true
    apply Bool.or_eq_true.mpr
    apply Or.inr
    apply decide_eq_true
    exact ⟨v,u,vu,by simp,by rw [Function.update_of_ne vu.ne.symm]; exact (desc _).mpr (Or.inr rfl)⟩
  refine ⟨x,by simp [x,vp,vu.ne],fun p hp => (desc p).mpr (Or.inl hp),?_,by rw [zero,yes]; decide⟩
  intro z hz
  have hzp : z∉P := fun hp => Finset.disjoint_left.mp dis hp hz
  have hzu : z≠u := fun eq => uz (eq ▸ hz)
  simp [x,hzp,hzu]

end Geometry2636
