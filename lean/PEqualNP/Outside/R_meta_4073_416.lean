import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4073_416
    (extract : ∀ (n : ℕ) (C : Circuit) (u v : ℕ), FanInTwo C →
      n ≤ u → u < n + C.size → n ≤ v → v < n + C.size → u ≠ v →
      ∃ (P : Circuit) (a b : Gate), FanInTwo ⟨a :: b :: P.gates, 0⟩ ∧
        P.size + 2 ≤ C.size ∧ ∀ z : List Bool, z.length = n →
          let w := P.wires z
          let e := fun g : Gate => g.op.eval (g.inputs.map fun k => w.getD k false)
          (e a && e b) = ((C.wires z).getD u false && (C.wires z).getD v false))
    (obstruction : ∀ (P : Circuit) (a b : Gate), FanInTwo ⟨a :: b :: P.gates, 0⟩ →
      P.size ≤ 15 →
      let e := fun (x : Fin 10 → Bool) (g : Gate) =>
        g.op.eval (g.inputs.map fun k => (P.wires (List.ofFn x ++ [!x 0])).getD k false)
      (∃ g ∈ [a,b], ∀ i : Fin 10, ∃ x, e x g = false ∧ e (Function.update x i true) g = true) →
      ∃ x, (e x a && e x b) ≠ (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ));       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x1.wires (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))])).getD x8 Bool.false;       (∃ (x8 : Fin (10 : ℕ) → Bool), x7 x8 x2 = Bool.true ∧ x7 x8 x3 = Bool.false) → (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x2 = Bool.false ∧ x7 x9 x3 = Bool.true) → (∀ (x10 : Fin (10 : ℕ) → Bool), x6 x10 = Bool.true → x7 x10 x2 = Bool.true ∧ x7 x10 x3 = Bool.true) → ∃ (x11 : Fin (10 : ℕ) → Bool), x6 x11 = Bool.false ∧ x7 x11 x2 = Bool.true ∧ x7 x11 x3 = Bool.true := by
  intro C u v legal budget F W cross₁ cross₂ positive
  let input := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
  let step := fun (l : List Bool) (g : Gate) =>
    l ++ [g.op.eval (g.inputs.map fun k => l.getD k false)]
  have keep (gs : List Gate) (l : List Bool) (k : ℕ) (hk : k < l.length) :
      (gs.foldl step l).getD k false = l.getD k false := by
    induction gs generalizing l with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step l g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have length (gs : List Gate) (l : List Bool) :
      (gs.foldl step l).length = l.length + gs.length := by
    induction gs generalizing l with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have leftBound (k : ℕ) (hk : ∀ x, F x = true → W x k = true) : 11 ≤ k := by
    by_contra! h
    let p : Fin 11 := ⟨k, h⟩
    have rows (p : Fin 11) :
        let x := fun i : Fin 10 => decide (i.val ≠ p.val)
        F x = true ∧ (input x).getD p.val false = false := by
      fin_cases p <;> exact ⟨rfl, rfl⟩
    let x := fun i : Fin 10 => decide (i.val ≠ p.val)
    obtain ⟨on, off⟩ := rows p
    have he := hk x on
    change (C.gates.foldl step (input x)).getD k false = true at he
    rw [keep _ _ _ (by simpa [input] using h)] at he
    exact Bool.noConfusion (he.symm.trans off)
  have rightBound (k : ℕ) (hk : ∃ x, W x k = true) : k < 11 + C.size := by
    obtain ⟨x, hx⟩ := hk
    by_contra! h
    change (C.gates.foldl step (input x)).getD k false = true at hx
    change 11 + C.gates.length ≤ k at h
    rw [List.getD_eq_default _ _ (by simpa [length, input] using h)] at hx
    contradiction
  obtain ⟨p, pu, pv⟩ := cross₁
  obtain ⟨q, _, qv⟩ := cross₂
  have distinct : u ≠ v := by
    rintro rfl
    exact Bool.noConfusion (pu.symm.trans pv)
  obtain ⟨P, a, b, hP, cost, extracted⟩ := extract 11 C u v legal
    (leftBound u (fun x hx => (positive x hx).1)) (rightBound u ⟨p, pu⟩)
    (leftBound v (fun x hx => (positive x hx).2)) (rightBound v ⟨q, qv⟩) distinct
  let e := fun (x : Fin 10 → Bool) (g : Gate) =>
    g.op.eval (g.inputs.map fun k => (P.wires (input x)).getD k false)
  by_contra missed
  have exactRows (x : Fin 10 → Bool) : (e x a && e x b) = F x := by
    have h := extracted (input x) (by simp [input])
    change (e x a && e x b) = (W x u && W x v) at h
    rw [h]
    cases hF : F x with
    | false =>
      cases hu : W x u <;> cases hv : W x v
      all_goals first | rfl | exact False.elim (missed ⟨x, hF, hu, hv⟩)
    | true =>
      obtain ⟨hu,hv⟩ := positive x hF
      rw [hu,hv] <;> rfl
  let pick := fun (i j : Fin 10) =>
    let mask := ([116, 201, 402, 554, 773] : List ℕ).find? (fun m =>
      !(m.testBit i.val || m.testBit j.val))
    fun k : Fin 10 => (mask.getD 0).testBit k.val
  have rows : ∀ i j : Fin 10,
      F (pick i j) = false ∧ F (Function.update (pick i j) i true) = true ∧
        F (Function.update (pick i j) j true) = true := by
    dsimp only [F, pick]
    decide +kernel
  let rises := fun (g : Gate) (i : Fin 10) =>
    ∃ x, e x g = false ∧ e (Function.update x i true) g = true
  have full : ∃ g ∈ [a,b], ∀ i, rises g i := by
    by_cases ha : ∀ i, rises a i
    · exact ⟨a, by simp, ha⟩
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      refine ⟨b, by simp, fun j => ?_⟩
      let x := pick i j
      obtain ⟨hx, hxi, hxj⟩ := rows i j
      have hpair : (e x a && e x b) = false := (exactRows x).trans hx
      have pairI := Bool.and_eq_true_iff.mp ((exactRows _).trans hxi)
      have pairJ := Bool.and_eq_true_iff.mp ((exactRows _).trans hxj)
      have aOn : e x a = true := by
        cases h : e x a with
        | true => rfl
        | false => exact False.elim (hi ⟨x, h, pairI.1⟩)
      rw [aOn, Bool.true_and] at hpair
      exact ⟨x, hpair, pairJ.2⟩
  obtain ⟨x, mismatch⟩ := obstruction P a b hP (by omega) full
  apply mismatch
  change (e x a && e x b) = _
  rw [exactRows]
  change _ = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
    (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
    (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
    (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
    (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
  dsimp only [F]
  simp only [Bool.or_false]
  ac_rfl
