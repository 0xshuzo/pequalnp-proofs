import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5264_729
    (nearCount : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (R : ℕ), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
        ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, ∃ (u v : Fin n) (w r : ℕ), e = s(u,v) ∧ v ∈ orIn n C w ∧
          r ≤ R ∧ 2*r+2 ≤ (orIn n C w).card ∧
          ((orIn n C w).filter (fun z => ¬ G.Adj u z)).card ≤ r) →
        E.card ≤ ((R+1)*(2*(2*R+1)))*C.size)
    (residual : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, e ∈ Ustar G C ∧
        (∃ a ∈ tops G C \ centreless G C, e ∈ gammaE G C a ∧
          ∃ z ∈ side C a 0 ∪ side C a 1, z ∈ e) ∧ ¬ (∃ (u v : Fin n) (w r : ℕ), e = s(u,v) ∧ v ∈ orIn n C w ∧
          r ≤ 2 ∧ 2*r+2 ≤ (orIn n C w).card ∧
          ((orIn n C w).filter (fun z => ¬ G.Adj u z)).card ≤ r)) →
        E.card ≤ k*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∃ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∈ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,hk⟩ := residual
  refine ⟨30+k, ?_⟩
  intro n G inst hg hn C least top
  let P : Sym2 (Fin n) → Prop := fun e => ∃ (u v : Fin n) (w r : ℕ), e = s(u,v) ∧ v ∈ orIn n C w ∧
          r ≤ 2 ∧ 2*r+2 ≤ (orIn n C w).card ∧
          ((orIn n C w).filter (fun z => ¬ G.Adj u z)).card ≤ r
  let T : Sym2 (Fin n) → Prop := fun e => ∃ a ∈ tops G C \ centreless G C, e ∈ gammaE G C a ∧
          ∃ z ∈ side C a 0 ∪ side C a 1, z ∈ e
  let A := (Ustar G C).filter P
  let B := (Ustar G C).filter (fun e => T e ∧ ¬P e)
  have ca : A.card ≤ 30*C.size := nearCount n G C 2 hg least.1 A
    (fun _ he => (Finset.mem_filter.mp he).2)
  have cb : B.card ≤ k*(C.size+1) := hk n G hg hn C least top B (by
    intro e he
    exact Finset.mem_filter.mp he)
  have cover : {x10 ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (x11 : Fin n) (x12 : Fin n), x10 = s(x11, x12) ∧ ∃ x13 < C.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn n C (n + x13), G.Adj x11 x15) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, x10 ∈ PEqualNP.TopForm.gammaE G C x11 ∧ ∃ x12 ∈ PEqualNP.TopForm.side C x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side C x11 (1 : Fin (2 : ℕ)), x12 ∈ x10} ⊆ A ∪ B := by
    intro e he
    by_cases hp : P e
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2.2,hp⟩)
  calc
    _ ≤ (A ∪ B).card := Finset.card_le_card cover
    _ ≤ A.card+B.card := Finset.card_union_le _ _
    _ ≤ 30*C.size+k*(C.size+1) := Nat.add_le_add ca cb
    _ ≤ (30+k)*(C.size+1) := by rw [Nat.add_mul]; omega
