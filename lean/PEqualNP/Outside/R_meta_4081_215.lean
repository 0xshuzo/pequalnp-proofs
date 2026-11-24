import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4081_215
  (controlled : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → (∀ v w : Fin 11, s(v,w) ∈ Ustar G C → ∃ j ∈ junk G C, gateVal 11 C j (pairInput v w) = true) →
    ¬(∃ j ∈ junk G C, 2 ≤ ((Ustar G C).filter (fun e => e ∈ gammaE G C j ∧ ∀ h ∈ junk G C, h < j → e ∉ gammaE G C h)).card ∧
      ((∃ v : Fin 11, gateVal 11 C j (pairInput v v) = true) ∨
       ∃ (b : Fin 2) (h : ℕ), h ∈ orN G C \ lam G C ∧ opnd C j b = 11+h)) → (Ustar G C).card ≤ (junk G C).card+3)
  (low : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card → (∀ v w : Fin 11, s(v,w) ∈ Ustar G C → ∃ j ∈ junk G C, gateVal 11 C j (pairInput v w) = true) →
    3 ≤ (Ustar G C).card → 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
    2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 2 → (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
  (exceptions : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card → (∀ v w : Fin 11, s(v,w) ∈ Ustar G C → ∃ j ∈ junk G C, gateVal 11 C j (pairInput v w) = true) →
    3 ≤ (Ustar G C).card → 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
    3 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card → (∃ j ∈ junk G C, 2 ≤ ((Ustar G C).filter (fun e => e ∈ gammaE G C j ∧ ∀ h ∈ junk G C, h < j → e ∉ gammaE G C h)).card ∧
      ((∃ v : Fin 11, gateVal 11 C j (pairInput v v) = true) ∨
       ∃ (b : Fin 2) (h : ℕ), h ∈ orN G C \ lam G C ∧ opnd C j b = 11+h)) → (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C size least top junk3 cover rest ratio
  by_cases small : 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 2
  · exact low C size least top junk3 cover rest ratio small
  · have margin : 3 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by omega
    by_cases special : (∃ j ∈ junk G C, 2 ≤ ((Ustar G C).filter (fun e => e ∈ gammaE G C j ∧ ∀ h ∈ junk G C, h < j → e ∉ gammaE G C h)).card ∧
      ((∃ v : Fin 11, gateVal 11 C j (pairInput v v) = true) ∨
       ∃ (b : Fin 2) (h : ℕ), h ∈ orN G C \ lam G C ∧ opnd C j b = 11+h))
    · exact exceptions C size least top junk3 cover rest ratio margin special
    · have h := controlled C least top cover special
      change (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      change (Ustar G C).card ≤ (junk G C).card+3 at h
      omega
