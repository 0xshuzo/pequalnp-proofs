import PEqualNP.Defs

namespace Plane2583.ThreeLines

open PEqualNP.MetaComplexity

def hexagon (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)

def one (x : Fin 9 → Bool) : Bool := hexagon x || (x 6 && x 1)
def two (x : Fin 9 → Bool) : Bool := one x || (x 7 && x 3)
def three (x : Fin 9 → Bool) : Bool := two x || (x 8 && x 5)

def endMap (i : Fin 9) : Fin 6 := ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩

def cycle (x : Fin 6 → Bool) : Bool :=
  decide (∃ i j : Fin 6, (i.val + 1) % 6 = j.val ∧ x i = true ∧ x j = true)

theorem remove8 : (fun x => three (Function.update x 8 false)) = two := by
  funext x
  simp [three,two,one,hexagon,Function.update]

theorem remove7 : (fun x => two (Function.update x 7 false)) = one := by
  funext x
  simp [two,one,hexagon,Function.update]

theorem remove6 : (fun x => one (Function.update x 6 false)) = hexagon := by
  funext x
  simp [one,hexagon,Function.update]

theorem endMap_eq : (fun x => hexagon (x ∘ endMap)) = cycle :=
  funext (by decide +kernel)

-- These three hypotheses are checked theorems Forest.one_gate_at, PermInputs.relabel_size,
-- and L106. They are passed explicitly so this diagnostic only has to import the definitions.
theorem lower
    (erase : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
      (s : ℕ), (∃ x, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y, f (Function.update x p b) ≠ f (Function.update y p b)) →
      HasCircuitSize (n+1) f (s+1) → HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s)
    (rename : ∀ {n m : ℕ} (π : Fin n → Fin m) (f : (Fin n → Bool) → Bool) (s : ℕ),
      HasCircuitSize n f s → HasCircuitSize m (fun x => f (x ∘ π)) s)
    (cycles : ∀ n s : ℕ, 5 ≤ n → (HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + (n+1)/2 ≤ s+1)) :
    ¬ HasCircuitSize 9 three 10 := by
  intro h
  have r2 := erase 8 three 8 false 9
    ⟨fun i => decide (i = 5), by decide +kernel⟩
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide +kernel⟩ h
  rw [remove8] at r2
  have r1 := erase 8 two 7 false 8
    ⟨fun i => decide (i = 3), by decide +kernel⟩
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide +kernel⟩ r2
  rw [remove7] at r1
  have r0 := erase 8 one 6 false 7
    ⟨fun i => decide (i = 1), by decide +kernel⟩
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide +kernel⟩ r1
  rw [remove6] at r0
  have closed := rename endMap hexagon 7 r0
  rw [endMap_eq] at closed
  have bad := (cycles 6 7 (by decide)).mp closed
  omega

end Plane2583.ThreeLines
