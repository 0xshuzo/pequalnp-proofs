import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4715_215
  (shell : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
        (orT G C).card + 1 = (tops G C).card)
  (extract : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
    ∃ (D : Circuit) (T : List (ℕ × ℕ)), IsAO2 n D ∧
      D.size + (tops G C).card + (orT G C).card ≤ C.size ∧
      T.length ≤ (tops G C).card ∧
      (junk G C).card ≤ D.gates.countP (fun g => !g.op.eval [true,false]) ∧
      (∀ j < D.gates.length, ¬ BelowF G D j) ∧
      ∀ x : Fin n → Bool, let w := D.wires (List.ofFn x)
        (T.any fun p => w.getD p.1 false && w.getD p.2 false) = graphFun G ∅ x)
  (small : let es : List ℕ := [9,10,20,24,37,42,54,55,72,74,88,89,103,106,121,137]
    let G := edgeGraph 11 (es.map fun k => (k / 16, k % 16))
    ∀ (D : Circuit) (T : List (ℕ × ℕ)), IsAO2 11 D →
      D.size + 2*T.length ≤ 22 →
      2 ≤ D.gates.countP (fun g => !g.op.eval [true,false]) →
      (∀ j < D.gates.length, ¬ BelowF G D j) →
      ∃ x : Fin 11 → Bool,
        (Minimal (fun y => graphFun G ∅ y = true) x ∨ Maximal (fun y => graphFun G ∅ y = false) x) ∧
        (T.any fun p => let w := D.wires (List.ofFn x)
          w.getD p.1 false && w.getD p.2 false) ≠ graphFun G ∅ x) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card := by
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C short least top dirty
  have hn : G.edgeFinset.Nonempty := by
    exact ⟨s(0,9), by decide⟩
  obtain ⟨D,T,model,budget,count,ands,negative,correct⟩ := extract 11 G C hn least top
  have eq := shell 11 G C hn least top
  have total : D.size + 2*T.length ≤ 22 := by omega
  have two : 2 ≤ D.gates.countP (fun g => !g.op.eval [true,false]) := by
    exact dirty.trans ands
  obtain ⟨x,_,diff⟩ := small D T model total two negative
  exact False.elim (diff (correct x))
