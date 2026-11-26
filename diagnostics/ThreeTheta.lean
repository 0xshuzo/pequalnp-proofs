import PEqualNP.Outside.L_meta_516
import PEqualNP.Outside.L_meta_7398

namespace PEqualNP.Outside.L_meta_9737_theta
open PEqualNP.MetaComplexity

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def value (edges : List (Fin 11 × Fin 11)) (x : Fin 11 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def required : Fin 3 → List (Fin 11 × Fin 11) := ![[(0, 4), (1, 5), (1, 6), (0, 7), (2, 7), (1, 8), (2, 8), (0, 9), (3, 9), (1, 10), (3, 10)], [(0, 4), (1, 5), (0, 6), (0, 7), (2, 7), (1, 8), (2, 8), (0, 9), (3, 9), (1, 10), (3, 10)], [(0, 5), (1, 5), (0, 6), (2, 6), (0, 7), (3, 7), (1, 8), (4, 8), (2, 9), (4, 9), (3, 10), (4, 10)]]
def allowed : Fin 3 → List (Fin 11 × Fin 11) := ![[(0, 4), (1, 5), (0, 6), (1, 6), (0, 7), (2, 7), (1, 8), (2, 8), (0, 9), (3, 9), (1, 10), (3, 10)], [(0, 4), (1, 5), (0, 6), (1, 6), (0, 7), (2, 7), (1, 8), (2, 8), (0, 9), (3, 9), (1, 10), (3, 10)], [(0, 5), (1, 5), (0, 6), (2, 6), (0, 7), (3, 7), (1, 8), (4, 8), (2, 9), (4, 9), (3, 10), (4, 10)]]
def projection : Fin 3 → Fin 11 → Fin 8 := ![![0, 3, 5, 7, 2, 1, 2, 4, 1, 6, 1], ![0, 3, 5, 7, 2, 2, 2, 4, 1, 6, 1], ![0, 0, 3, 5, 7, 2, 2, 4, 6, 1, 1]]

def theta (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) ||
  (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) ||
  (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)

private theorem mapped : ∀ (tag : Fin 3) (x : Fin 8 → Bool),
    value (required tag) (x ∘ projection tag) = theta x ∧
    value (allowed tag) (x ∘ projection tag) = theta x := by decide +kernel

theorem lower (tag : Fin 3) {f : (Fin 11 → Bool) → Bool} {k : Nat}
    (c : HasCircuitSize 11 f k)
    (lo : ∀ x, value (required tag) x = true → f x = true)
    (hi : ∀ x, f x = true → value (allowed tag) x = true) : 12 ≤ k := by
  have rep := PEqualNP.Outside.L_meta_7398_aux.yn (projection tag) f k c
  have eqn : (fun x : Fin 8 → Bool => f (x ∘ projection tag)) = theta := by
    funext x
    obtain ⟨a,b⟩ := mapped tag x
    cases h : theta x with
    | true => exact lo _ (a.trans h)
    | false =>
      cases v : f (x ∘ projection tag) with
      | false => rfl
      | true =>
        have bad : false = true := (b.trans h).symm.trans (hi _ v)
        cases bad
  rw [eqn] at rep
  exact PEqualNP.Outside.L_meta_516 k rep

end PEqualNP.Outside.L_meta_9737_theta
