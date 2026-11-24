import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_1768_729
    (entry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 5 ≤ p.length) →
      IsAO2 n C → PEqualNP.TopForm.TopForm G C → ∀ (u v : Fin n), G.Adj u v →
      ∀ a ∈ tops G C, ∀ (b : Fin 2) (g : ℕ), g ∈ junk G C →
      u ∈ side C a b → OrReaches n C (opnd C a (1-b)) g →
      gateVal n C g (pairInput u v) = true →
      ∃ h ∈ junk G C, (h = g ∨ InCone n C h g) ∧
        gateVal n C h (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C h d ∧ ∀ w ∈ side C h d, ¬ G.Adj v w)
    (direct : ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, e ∈ Ustar G C ∧ (∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C g d ∧ ∀ w ∈ side C g d, ¬ G.Adj v w)) →
      E.card ≤ K * (C.size+1))
    (nested : ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, e ∈ Ustar G C ∧ (∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        (¬ (∃ d : Fin 2, v ∈ side C g d ∧ ∀ w ∈ side C g d, ¬ G.Adj v w)) ∧
        ∃ h ∈ junk G C, InCone n C h g ∧ gateVal n C h (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C h d ∧ ∀ w ∈ side C h d, ¬ G.Adj v w)) →
      E.card ≤ K * (C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k, hk⟩ := direct
  obtain ⟨l, hl⟩ := nested
  refine ⟨k+l, ?_⟩
  intro n G inst C hg hL hT
  let Direct (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C g d ∧ ∀ w ∈ side C g d, ¬ G.Adj v w
  let Nested (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
        gateVal n C g (pairInput u v) = true ∧
        (¬ (∃ d : Fin 2, v ∈ side C g d ∧ ∀ w ∈ side C g d, ¬ G.Adj v w)) ∧
        ∃ h ∈ junk G C, InCone n C h g ∧ gateVal n C h (pairInput u v) = true ∧
        ∃ d : Fin 2, v ∈ side C h d ∧ ∀ w ∈ side C h d, ¬ G.Adj v w
  let Target (e : Sym2 (Fin n)) : Prop := ∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
        gateVal n C g (pairInput u v) = true
  let E := (Ustar G C).filter Target
  change E.card ≤ (k+l)*(C.size+1)
  classical
  let A := (Ustar G C).filter Direct
  let B := (Ustar G C).filter Nested
  have cover : E ⊆ A ∪ B := by
    intro e he
    obtain ⟨heU, hx⟩ := Finset.mem_filter.mp he
    obtain ⟨u,v,rfl,a,ha,b,g,hgJ,hu,hr,hval⟩ := hx
    have heG : s(u,v) ∈ G.edgeFinset := (Finset.sdiff_subset : Ustar G C ⊆ G.edgeFinset) heU
    have huv : G.Adj u v := by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
    by_cases here : ∃ d : Fin 2, v ∈ side C g d ∧ ∀ w ∈ side C g d, ¬ G.Adj v w
    · apply Finset.mem_union_left
      change s(u,v) ∈ (Ustar G C).filter Direct
      apply Finset.mem_filter.mpr
      exact ⟨heU,u,v,rfl,a,ha,b,g,hgJ,hu,hr,hval,here⟩
    · obtain ⟨h,hh,eqc,hpair,hport⟩ := entry n G C hg hL.1 hT u v huv a ha b g hgJ hu hr hval
      have hcone : InCone n C h g := eqc.resolve_left (fun eq => here (eq ▸ hport))
      apply Finset.mem_union_right
      change s(u,v) ∈ (Ustar G C).filter Nested
      apply Finset.mem_filter.mpr
      exact ⟨heU,u,v,rfl,a,ha,b,g,hgJ,hu,hr,hval,here,h,hh,hcone,hpair,hport⟩
  have sizeA := hk n G C hg hL hT A (fun _ he => Finset.mem_filter.mp he)
  have sizeB := hl n G C hg hL hT B (fun _ he => Finset.mem_filter.mp he)
  calc
    E.card ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card+B.card := Finset.card_union_le _ _
    _ ≤ k*(C.size+1)+l*(C.size+1) := Nat.add_le_add sizeA sizeB
    _ = (k+l)*(C.size+1) := (Nat.add_mul _ _ _).symm
