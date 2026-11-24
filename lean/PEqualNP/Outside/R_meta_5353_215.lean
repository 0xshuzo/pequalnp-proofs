import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5353_215
    (factor : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → n ≤ C.output →
      (∃ g : Gate, C.gates[C.output-n]? = some g ∧ g.op = GateOp.and) →
      ∃ D E : Circuit, D.gates = E.gates ∧ IsAO2 n D ∧ IsAO2 n E ∧
        D.output < n+D.size ∧ E.output < n+E.size ∧ D.size < C.size ∧
        ∀ x : List Bool, x.length = n → C.eval x = (D.eval x && E.eval x))
    (rows : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (D E : Circuit),
      let row (B : Circuit) (Y : Finset (Fin N)) := ∀ Z : Finset (Fin N),
        B.eval (incidenceInput (zeroSet S Y) Z) = decide (¬ Z ⊆ Y)
      (∀ l, (S l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N+N) D → IsAO2 (N+N) E →
      RightOnIncidentPairs S D → RightOnIncidentPairs S E →
      (∀ Y : Finset (Fin N), Y.card ≤ q →
        D.eval (incidenceInput (zeroSet S Y) Y) = false ∨ E.eval (incidenceInput (zeroSet S Y) Y) = false) →
      ∀ Y : Finset (Fin N), Y.card ≤ q → row D Y ∨ row E Y)
    (charge : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (D E : Circuit),
      let row (B : Circuit) (Y : Finset (Fin N)) := ∀ Z : Finset (Fin N),
        B.eval (incidenceInput (zeroSet S Y) Z) = decide (¬ Z ⊆ Y)
      350 ≤ q → N = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      D.gates = E.gates → IsAO2 (N+N) D → IsAO2 (N+N) E →
      D.output < (N+N)+D.size → E.output < (N+N)+E.size →
      RightOnIncidentPairs S D → RightOnIncidentPairs S E →
      (∀ Y : Finset (Fin N), Y.card ≤ q → row D Y ∨ row E Y) →
      N*q ≤ 100*(D.size+1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (350 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * (x1 - (349 : ℕ)) ≤ (100 : ℕ) * x4.size - (349 : ℕ) * x2 := by
  intro q N S C hq hN weight join ao lo hi last flags neg
  obtain ⟨D,E,shared,ad,ae,bd,be,shrink,split⟩ := factor (N+N) C ao lo last
  have lengthInput (X Y : Finset (Fin N)) : (incidenceInput X Y).length = N+N := by
    change (List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y))).length = N+N
    simp only [List.length_append, List.length_ofFn]
  have flags' : RightOnIncidentPairs S D ∧ RightOnIncidentPairs S E := by
    have both (l p : Fin N) (hp : p ∈ S l) := (split (incidenceInput {p} {l}) (lengthInput _ _)).symm.trans (flags l p hp)
    exact ⟨fun l p hp => (Bool.and_eq_true_iff.mp (both l p hp)).1,
      fun l p hp => (Bool.and_eq_true_iff.mp (both l p hp)).2⟩
  have diag (Y : Finset (Fin N)) (hy : Y.card ≤ q) :
      D.eval (incidenceInput (zeroSet S Y) Y) = false ∨ E.eval (incidenceInput (zeroSet S Y) Y) = false := by
    have right : IsFalseInput S (zeroSet S Y) Y := fun l hl =>
      Finset.disjoint_left.mpr fun p hp hz => (Finset.mem_filter.mp hz).2 l hl hp
    have hh := (split (incidenceInput (zeroSet S Y) Y) (lengthInput _ _)).symm.trans (neg _ _ hy right)
    cases h : D.eval (incidenceInput (zeroSet S Y) Y) with
    | false => exact Or.inl rfl
    | true => exact Or.inr (by simpa [h] using hh)
  have bound := charge q N S D E hq hN weight join shared ad ae bd be flags'.1 flags'.2
    (rows q N S D E weight join ad ae flags'.1 flags'.2 diag)
  have hb : N*q ≤ 100*C.size := by omega
  rw [Nat.mul_sub, Nat.mul_comm N 349]
  exact Nat.sub_le_sub_right hb (349*N)
