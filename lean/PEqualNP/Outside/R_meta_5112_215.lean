import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5112_215
    (transfer : ∀ gs : List (Bool × Nat × Nat), (gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) ([709697, 1356164, 2308120, 4543010, 11542531, 9994288, 13123596, 11141888, 13896704, 14745792, 16277519, 16351472, 16649984] : List Nat)).getD 26 0 = 4095 → (gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) ([256463372304, 8521482511360, 14003410187716736, 55389823206179104, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088, 192860064594267704, 288166778660192704, 283797140973809664] : List Nat)).getD 26 0 = 1764784)
    (synth : ∃ code : Fin 14 → Bool × Fin 27 × Fin 27,
      let gs := (List.ofFn code).map (fun g => (g.1, g.2.1.val, g.2.2.val))
      (gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]) ([709697, 1356164, 2308120, 4543010, 11542531, 9994288, 13123596, 11141888, 13896704, 14745792, 16277519, 16351472, 16649984] : List Nat)).getD 26 0 = 4095) :
    ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (14 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  obtain ⟨code, h⟩ := synth
  let gs := (List.ofFn code).map (fun g => (g.1, g.2.1.val, g.2.2.val))
  have len : gs.length = 14 := by simp [gs]
  refine ⟨gs, by omega, by omega, ?_⟩
  have result := transfer gs h
  have idx : 13 + gs.length - 1 = 26 := by omega
  rw [idx]
  exact result
