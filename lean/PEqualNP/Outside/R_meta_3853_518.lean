import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3853_518
    (restrict : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ),
      i < 11 → PEqualNP.MetaComplexity.FanInTwo C →
      (∃ w u : List Bool, w.length = 11 ∧ u.length = 11 ∧
        (∀ j : Fin 11, j.val ≠ i → w.getD j.val false = u.getD j.val false) ∧ C.eval w ≠ C.eval u) →
      (∃ c : Bool, ∀ w : List Bool, w.length = 11 → w.getD i false = false → C.eval w = c) ∨
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧
        ∀ w : List Bool, w.length = 11 → w.getD i false = false → D.eval w = C.eval w)
    (four : ∀ (b : Fin 9) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 9 → Bool, x 4 = false ∧
        D.eval (List.ofFn x ++ [!x 0, x b]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (six : ∀ (b : Fin 9) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 9 → Bool, x 6 = false ∧
        D.eval (List.ofFn x ++ [!x 0, x b]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 x2 : Fin (9 : ℕ)),   x1 = (4 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))] ∨ x1 = (6 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           have x7 : (Fin (9 : ℕ) → Bool) → Bool → Bool → Bool := fun (x7 : Fin (9 : ℕ) → Bool) (x8 x9 : Bool) => x4.eval (List.ofFn x7 ++ [x8, x9]);           have x8 : (Fin (9 : ℕ) → Bool) → Bool := fun (x8 : Fin (9 : ℕ) → Bool) => x8 x1 || x8 x2;           (∀ x9 ∈ [x1, x2], ∃ (x11 : Fin (9 : ℕ) → Bool), x11 x9 = Bool.false ∧ x8 x11 = Bool.true ∧ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.false ≠ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.true) → (∃ (x10 : Fin (9 : ℕ) → Bool), x10 (0 : Fin (9 : ℕ)) = Bool.false ∧ x7 x10 Bool.false (x8 x10) ≠ x7 x10 Bool.true (x8 x10)) → ∃ (x11 : Fin (9 : ℕ) → Bool), x7 x11 (!x11 (0 : Fin (9 : ℕ))) (x8 x11) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro a b hab C hf hs _ _ _ _
  by_contra! hc
  let F : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let W := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0, x a || x b]
  change ∀ x, C.eval (W x) = F x at hc
  let legal := fun a b : Fin 9 =>
    a = 4 ∧ b ∈ [1,2,3,6] ∨ a = 6 ∧ b ∈ [1,2,3,5,7,8]
  change legal a b at hab
  let pt := fun (m : ℕ) (i : Fin 9) => m.testBit i.val
  let rows := fun a b : Fin 9 =>
    if a = 4 then (if b = 1 then 10 else if b = 2 then 5 else if b = 3 then 8 else 65)
    else (if b = 1 then 2 else if b = 2 then 260 else if b = 3 then 10 else
      if b = 5 then 34 else if b = 7 then 130 else 256)
  have hwit : ∀ a b : Fin 9, legal a b →
      let l := pt (rows a b)
      let h := pt (rows a b ||| (1 <<< a.val))
      (∀ j : Fin 11, j.val ≠ a.val →
        (List.ofFn l ++ [!l 0,l a || l b]).getD j.val false =
        (List.ofFn h ++ [!h 0,h a || h b]).getD j.val false) ∧ F l ≠ F h := by
    decide +kernel
  obtain ⟨heq, hdiff⟩ := hwit a b hab
  let l := pt (rows a b)
  let h := pt (rows a b ||| (1 <<< a.val))
  have ex : C.eval (W l) ≠ C.eval (W h) := by rw [hc,hc]; exact hdiff
  have cut := restrict C a.val (by have := a.isLt; omega) hf
    ⟨W l, W h, by simp [W], by simp [W], heq, ex⟩
  have wz : ∀ x : Fin 9 → Bool, (W x).getD a.val false = x a := by
    intro x
    change (List.ofFn x ++ [!x 0,x a || x b]).getD a.val false = x a
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using a.isLt)]
    exact (show ∀ (n : ℕ) (f : Fin n → Bool) (j : Fin n),
      (List.ofFn f).getD j.val false = f j from
        fun n f j => by simp [List.getD_eq_getElem?_getD]) 9 x a
  rcases cut with ⟨c, hconst⟩ | ⟨D, hD, hlt, hsim⟩
  · have h0 := hconst (W (pt 0)) (by simp [W]) (by rw [wz]; simp [pt])
    have h1 := hconst (W (pt 3)) (by simp [W]) (by
      rw [wz]; rcases hab with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide)
    rw [hc] at h0 h1
    have contra : F (pt 0) ≠ F (pt 3) := by decide
    exact contra (h0.trans h1.symm)
  · have h12 : D.size ≤ 12 := by omega
    have hbad : ∃ x : Fin 9 → Bool, x a = false ∧
        D.eval (List.ofFn x ++ [!x 0, x b]) ≠ F x := by
      rcases hab with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact four b D hD h12
      · exact six b D hD h12
    obtain ⟨x,hx,he⟩ := hbad
    have heq := hsim (W x) (by simp [W]) ((wz x).trans hx)
    rw [hc] at heq
    exact he (by simpa [W,hx] using heq)
