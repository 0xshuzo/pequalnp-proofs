import PEqualNP.Outside.L_meta_2970
import PEqualNP.Outside.L_meta_2972

namespace PlaneFraction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem fraction (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (huniq : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hmodel : IsAO2 (N+N) C)
    (hsound : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) :
    let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ circuitFun (N+N) C
      (fun z => decide (z=Fin.castAdd N e.1 ∨ z=Fin.natAdd N e.2))=true
    let D := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ circuitFun (N+N) C
      (fun z => decide (z=Fin.castAdd N e.1 ∨ z=Fin.natAdd N e.2))=true ∧
        lineSingle C (N+N) (fun i => decide (N≤i)) e.1.val (N+e.2.val)=false ∧
        lineSingle C (N+N) (fun i => decide (i<N)) e.1.val (N+e.2.val)=false
    11*D.card ≤ 6*E.card → E.card ≤ 44*C.size := by
  classical
  intro E D frac
  have noRectangle : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ (I p l ∧ I r l ∧ I p m ∧ I r m) := by
    rintro p r l m hpr hlm ⟨hpl, hrl, hpm, hrm⟩
    obtain ⟨_, _, uniqueLine⟩ := huniq p r hpr
    exact hlm ((uniqueLine l ⟨hpl, hrl⟩).trans (uniqueLine m ⟨hpm, hrm⟩).symm)
  have hL := PEqualNP.Outside.L_meta_2970 N I C noRectangle hmodel
    (fun z hz => hsound z (hz.trans (by omega)))
  have hP := PEqualNP.Outside.L_meta_2972 q N I C (by omega) hN hcol huniq hmodel hsound
  let accepts (e : Fin N × Fin N) := PEqualNP.MetaComplexity.circuitFun (N + N) C
    (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2))
  let readLine (e : Fin N × Fin N) := PEqualNP.ReadK.lineSingle C (N + N)
    (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
  let readPoint (e : Fin N × Fin N) := PEqualNP.ReadK.lineSingle C (N + N)
    (fun i => decide (i < N)) e.1.val (N + e.2.val)
  let hits := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ accepts e = true
  let lines := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readLine e = true
  let points := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readPoint e = true
  let rest := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ accepts e = true ∧ readLine e = false ∧ readPoint e = false
  have cover : hits ⊆ (lines ∪ points) ∪ rest := by
    intro e he
    obtain ⟨hi, ha⟩ := (Finset.mem_filter.mp he).2
    simp only [lines, points, rest, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases readLine e <;> cases readPoint e <;> simp [hi, ha]
  rw [Fintype.card_subtype] at hL hP
  change lines.card ≤ 10 * C.size at hL
  change points.card ≤ 10 * C.size at hP
  change 11 * rest.card ≤ 6 * hits.card at frac
  change hits.card ≤ 44 * C.size
  have h := Finset.card_le_card cover
  have hp := Finset.card_union_le lines points
  have hr := Finset.card_union_le (lines ∪ points) rest
  omega

end PlaneFraction
