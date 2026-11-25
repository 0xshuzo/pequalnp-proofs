import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- The four difference classes are disjoint matchings of size twelve in the punctured plane.
-- A small least circuit must leave a flag unpaid in each matching when its residual has size four.
theorem PEqualNP.Outside.R_meta_4043_17
    (normalize : ∀ (C : Circuit) (v : Fin 26), Monotone2 C → (∀ x : Fin 26 → Bool, x v=false → (C.eval (List.ofFn x)=true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+(1 : Fin 13) ∨ p=l+(3 : Fin 13) ∨ p=l+(9 : Fin 13)) ∧
          x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)) →
      ∃ (G : SimpleGraph (Fin 25)) (D : Circuit), (∀ u v : Fin 25, G.Adj u v ↔
        (u.val < 12 ∧ 12 ≤ v.val ∧ (u.val+26-v.val)%13 ∈ [0,1,3,9]) ∨
        (v.val < 12 ∧ 12 ≤ u.val ∧ (v.val+26-u.val)%13 ∈ [0,1,3,9])) ∧
        ∀ [DecidableRel G.Adj], IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size≤C.size)
    (matchingPrice : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (D : Circuit),
      (∀ u v : Fin 25, G.Adj u v ↔
        (u.val < 12 ∧ 12 ≤ v.val ∧ (u.val+26-v.val)%13 ∈ [0,1,3,9]) ∨
        (v.val < 12 ∧ 12 ≤ u.val ∧ (v.val+26-u.val)%13 ∈ [0,1,3,9])) → IsLeastAO G D → PEqualNP.TopForm.TopForm G D → D.size≤57 →
      4≤(Ustar G D).card ∧ ((Ustar G D).card=4 → (∀ t : ℕ, t ∈ [0,1,3,9] → ∃ p l : Fin 25,
        p.val<12 ∧ 12≤l.val ∧ (p.val+26-l.val)%13=t ∧ s(p,l)∈Ustar G D)))
    (remaining : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (D : Circuit),
      (∀ u v : Fin 25, G.Adj u v ↔
        (u.val < 12 ∧ 12 ≤ v.val ∧ (u.val+26-v.val)%13 ∈ [0,1,3,9]) ∨
        (v.val < 12 ∧ 12 ≤ u.val ∧ (v.val+26-u.val)%13 ∈ [0,1,3,9])) → IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
      4≤(Ustar G D).card → ((Ustar G D).card=4 → (∀ t : ℕ, t ∈ [0,1,3,9] → ∃ p l : Fin 25,
        p.val<12 ∧ 12≤l.val ∧ (p.val+26-l.val)%13=t ∧ s(p,l)∈Ustar G D)) → 58≤D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  classical
  intro C v mono computes
  obtain ⟨G,D,shape,details⟩ := normalize C v mono computes
  letI := Classical.decRel G.Adj
  obtain ⟨least,top,size⟩ := @details (Classical.decRel G.Adj)
  by_contra! short
  have sm : D.size≤57 := by omega
  obtain ⟨four,hit⟩ := matchingPrice G D shape least top sm
  have lb := remaining G D shape least top four hit
  omega
