import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5365_417
    (dichotomy : ∀ k : ℕ, ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ t (w : G.Walk t t), w.IsCycle → 5 ≤ w.length) → ∀ R : Fin n → Fin n → Prop,
      let ind := fun S : Finset (Fin n) => ∀ p ∈ S, ∀ q ∈ S, ¬ G.Adj p q
      (∃ I : Finset (Fin n), ind I ∧ ∀ Z : Finset (Fin n), Z.card ≤ k → ∃ p ∈ I \ Z, ∃ q ∈ I \ Z, R p q) ∨ ∃ H : Finset (Fin n), H.card ≤ d ∧ (∀ p q, ¬ G.Adj p q → R p q → p ∈ H ∨ q ∈ H))
    (localize : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (R : Fin n → Fin n → Prop),
      Symmetric R → ∀ (H I : Finset (Fin n)) (u v : Fin n), G.Adj u v →
      let ind := fun S : Finset (Fin n) => ∀ p ∈ S, ∀ q ∈ S, ¬ G.Adj p q
      ind I → (∀ p q, ¬ G.Adj p q → R p q → p ∈ H ∨ q ∈ H) →
      (∀ Z : Finset (Fin n), Z.card ≤ k+H.card → u ∉ Z → v ∉ Z →
         ∃ p ∈ I \ Z, ∃ q ∈ I \ Z, R p q) → ∃ a ∈ H, (a = u ∨ a = v) ∧ (R a a ∨ ∃ Y : Finset (Fin n), k < Y.card ∧ ind (insert a Y) ∧ ∀ z ∈ Y, R a z))
    (normal : ∃ k : ℕ, ∀ d : ℕ, ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → (∀ t (w : G.Walk t t), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset, (∀ j : Fin C.gates.length,
        let R := fun p q : Fin n => gateVal n C j.val (pairInput p q) = true
        let ind := fun S : Finset (Fin n) => ∀ p ∈ S, ∀ q ∈ S, ¬ G.Adj p q
        (∃ I : Finset (Fin n), ind I ∧ ∀ Z : Finset (Fin n), Z.card ≤ k → ∃ p ∈ I \ Z, ∃ q ∈ I \ Z, R p q) ∨ ∃ H : Finset (Fin n), H.card ≤ d ∧ (∀ p q, ¬ G.Adj p q → R p q → p ∈ H ∨ q ∈ H) ∧
          ∀ u v : Fin n, s(u,v) ∈ T → Owns n C j.val u v → ∃ a ∈ H, (a = u ∨ a = v) ∧ (R a a ∨ ∃ Y : Finset (Fin n), k < Y.card ∧ ind (insert a Y) ∧ ∀ z ∈ Y, R a z)) →
      T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             ∃ (x21 : Finset (Fin x3)), Maximal (fun (x22 : Finset (Fin x3)) => ∀ x23 ∈ x22, ∀ x25 ∈ x22, ¬x4.Adj x23 x25) x21 ∧ ∀ (x22 : Finset (Fin x3)), x22.card ≤ x1 → x15 ∉ x22 → x16 ∉ x22 → ∃ x26 ∈ x21 \ x22, ∃ x27 ∈ x21 \ x22, x20 x26 x27) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨k,price⟩ := normal
  obtain ⟨d,classify⟩ := dichotomy k
  obtain ⟨c,bound⟩ := price d
  refine ⟨k+d,c,?_⟩
  intro n G inst degree girth C least computes T sub test
  apply bound n G degree girth C least computes T sub
  intro j
  let R := fun p q : Fin n => gateVal n C j.val (pairInput p q) = true
  have sym : Symmetric R := by
    intro p q hp
    have sw : @pairInput n p q = pairInput q p := by
      funext z
      change decide (z=p ∨ z=q) = decide (z=q ∨ z=p)
      simp only [or_comm]
    change gateVal n C j.val (pairInput q p) = true
    rw [← sw]
    exact hp
  rcases classify n G girth R with large | ⟨H,small,cover⟩
  · exact Or.inl large
  · refine Or.inr ⟨H,small,cover,?_⟩
    intro u v edge own
    obtain ⟨I,maximal,robust⟩ := test _ edge u v rfl j own
    have adj : G.Adj u v := G.mem_edgeFinset.mp (sub edge)
    apply localize n k G R sym H I u v adj maximal.1 cover
    intro Z sz hu hv
    exact robust Z (by omega) hu hv
