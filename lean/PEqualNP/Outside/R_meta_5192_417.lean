import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5192_417
    (blocks : ∀ k : ℕ, ∃ r : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ t (w : G.Walk t t), w.IsCycle → 5 ≤ w.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), G.Adj u v → r ≤ F.card →
      (∀ p ∈ F, ¬ G.Adj p.1 p.2) →
      (let E := fun p : Fin n × Fin n => ({p.1,p.2} : Finset (Fin n)) \ {u,v}
       ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (E p) (E q)) →
      ∃ (b : Finset (Fin n)) (B : Fin k → Finset (Fin n)), b ⊆ {u,v} ∧ b.card ≤ 1 ∧
      (∀ i, (B i).Nonempty ∧ (B i).card ≤ 2 ∧ Disjoint (B i) {u,v}) ∧
      Pairwise (fun i h => Disjoint (B i) (B h)) ∧
      (∀ i, ∃ p ∈ F, p.1 ∈ b ∪ B i ∧ p.2 ∈ b ∪ B i) ∧ (∀ p ∈ b ∪ Finset.univ.biUnion B, ∀ q ∈ b ∪ Finset.univ.biUnion B, ¬ G.Adj p q))
    (slice : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (j : ℕ) (b : Finset (Fin n)) (B : Fin k → Finset (Fin n)), Monotone2 C →
      circuitFun n C = graphFun G ∅ → (∀ p ∈ b ∪ Finset.univ.biUnion B, ∀ q ∈ b ∪ Finset.univ.biUnion B, ¬ G.Adj p q) → (∀ i, ∃ p ∈ b ∪ B i, ∃ q ∈ b ∪ B i, gateVal n C j (pairInput p q) = true) → ∀ X : Finset (Fin k), let x : Fin n → Bool := fun w => decide (w ∈ b ∪ X.biUnion B)
        circuitFun n C x = false ∧ (X.Nonempty → gateVal n C j x = true))
    (negative : ∃ k c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ t (w : G.Walk t t), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset, (∀ u v : Fin n, s(u,v) ∈ T → ∀ j : Fin C.gates.length,
        Owns n C j.val u v → ∃ (b : Finset (Fin n)) (B : Fin k → Finset (Fin n)),
        b ⊆ {u,v} ∧ b.card ≤ 1 ∧
      (∀ i, (B i).Nonempty ∧ (B i).card ≤ 2 ∧ Disjoint (B i) {u,v}) ∧
      Pairwise (fun i h => Disjoint (B i) (B h)) ∧ ∀ X : Finset (Fin k), let x : Fin n → Bool := fun w => decide (w ∈ b ∪ X.biUnion B)
        circuitFun n C x = false ∧ (X.Nonempty → gateVal n C j.val x = true)) → T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨k,c,bound⟩ := negative
  obtain ⟨r,extract⟩ := blocks k
  refine ⟨r,c,?_⟩
  intro n G inst deg girth C minimal evaluates T sub witnesses
  apply bound n G deg girth C minimal evaluates T sub
  intro u v hT j owns
  obtain ⟨F,card,valid,apart⟩ := witnesses _ hT u v rfl j owns
  have uv : G.Adj u v := G.mem_edgeFinset.mp (sub hT)
  obtain ⟨b,B,hb,hcard,hB,disj,kept,indep⟩ :=
    extract n G girth u v F uv (by omega) (fun p hp => (valid p hp).2) apart
  refine ⟨b,B,hb,hcard,hB,disj,slice n k G C j.val b B minimal.1 evaluates indep ?_⟩
  intro i
  obtain ⟨p,hp,h1,h2⟩ := kept i
  exact ⟨p.1,h1,p.2,h2,(valid p hp).1⟩
