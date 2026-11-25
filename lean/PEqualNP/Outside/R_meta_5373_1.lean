import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_5373_1
    (construct : ∀ (n m : ℕ) (F : Finset (Fin n × Fin m)),
      ∃ (T : Finset (Fin n × Fin m)) (D : Circuit),
        T ⊆ F ∧ (∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e = f) ∧
        (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e = f) ∧
        D.size ≤ F.card + T.card - 1 ∧ IsAO2 (n+m) D ∧
        ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
          (∃ p l, (p,l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true))
    (core : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit) (G : SimpleGraph (Fin (n+m))),
      let fits (F : Finset (Fin n × Fin m)) (D : Circuit) :=
        IsAO2 (n+m) D ∧ ∀ x : Fin (n+m) → Bool,
          circuitFun (n+m) D x = decide (∃ p l, (p,l) ∈ F ∧
            x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
      let matching (T : Finset (Fin n × Fin m)) :=
        (∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e = f) ∧
        (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e = f)
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E,
        (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
      ¬ G.IsAcyclic →
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      fits E C → M ⊆ E → matching M →
      (∀ e ∈ E, ((∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e)) →
        (E.erase e).Nonempty → e ∈ M) →
      (∀ D : Circuit, fits E D → C.size ≤ D.size) →
      (∀ e ∈ E, e ∉ M → ∃ T ⊆ E.erase e, matching T ∧ C.size ≤ (E.erase e).card + T.card - 1) →
      ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ fits (E.erase e) D)
    : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  intro n m E M C G adj cyc square ao val sub rows cols leaves
  let fits (F : Finset (Fin n × Fin m)) (D : Circuit) :=
        IsAO2 (n+m) D ∧ ∀ x : Fin (n+m) → Bool,
          circuitFun (n+m) D x = decide (∃ p l, (p,l) ∈ F ∧
            x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
  have has : ∃ k : ℕ, ∃ D : Circuit, fits E D ∧ D.size = k :=
    ⟨C.size,C,⟨ao,val⟩,rfl⟩
  obtain ⟨B,hB,hsize⟩ := Nat.find_spec has
  have least (D : Circuit) (hd : fits E D) : B.size ≤ D.size := by
    rw [hsize]
    exact Nat.find_min' has ⟨D,hd,rfl⟩
  have leC := least C ⟨ao,val⟩
  by_contra hno
  have price (e) (he : e ∈ E) (outside : e ∉ M) :
      ∃ T ⊆ E.erase e,
        ((∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e = f) ∧ (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e = f)) ∧
        B.size ≤ (E.erase e).card + T.card - 1 := by
    obtain ⟨T,D,ss,hp,hl,bound,dAO,dval⟩ := construct n m (E.erase e)
    refine ⟨T,ss,⟨hp,hl⟩,?_⟩
    by_contra! short
    exact hno ⟨e,he,outside,D,by omega,dAO,dval⟩
  obtain ⟨e,he,outside,D,hd,hD⟩ := core n m E M B G adj cyc square hB sub
    ⟨rows,cols⟩ leaves least price
  exact hno ⟨e,he,outside,D,by omega,hD⟩
