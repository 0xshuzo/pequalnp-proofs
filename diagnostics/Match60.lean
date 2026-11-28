import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9737.Match60
open Finset
abbrev P := Fin 13
abbrev L := Fin 12
def lineMatch : L → P := ![1, 2, 3, 4, 5, 6, 8, 11, 9, 10, 7, 0]
def degree : P → Nat := ![3, 3, 4, 3, 4, 4, 4, 4, 4, 3, 4, 4, 4]
def actualEdge (p : P) (l : L) : Bool := ((#[1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357] : Array Nat)[l.val]?.getD 0).testBit p.val
theorem matchedFlag : ∀l, actualEdge (lineMatch l) l = true := by decide +kernel
theorem measuredDegree : ∀p, ((List.finRange 12).filter (actualEdge p)).length=degree p := by decide +kernel
theorem allDegrees : ∑ p : P, degree p = 48 := by decide +kernel
theorem injMatch : Function.Injective lineMatch := by decide +kernel
theorem matchSum (x : P → Nat) : (∑ l : L, x (lineMatch l)) ≤ ∑ p : P, x p := by
  have eq : (∑ l : L, x (lineMatch l)) =
      ∑ p ∈ (Finset.univ : Finset L).image lineMatch, x p := by
    rw [Finset.sum_image]
    intro a _ b _ e
    exact injMatch e
  rw [eq]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Each modified incidence is charged once at each endpoint. A fully modified
line has a distinct matched point with at least one modification. -/
theorem aggregate (payP mP bonus : P → Nat) (payL mL loss : L → Nat)
    (count : ∑ p, mP p = ∑ l, mL l)
    (pt : ∀ p, degree p + bonus p ≤ payP p + mP p)
    (ln : ∀ l, 1 + mL l ≤ payL l + loss l)
    (share : ∀ l, loss l ≤ bonus (lineMatch l)) :
    60 ≤ (∑ p, payP p) + ∑ l, payL l := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => pt p)
  have k := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => ln l)
  have s := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => share l)
  have z := matchSum bonus
  simp only [Finset.sum_add_distrib,allDegrees,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,Nat.nsmul_eq_mul,mul_one] at h k
  omega

end PEqualNP.Outside.L_meta_9737.Match60
