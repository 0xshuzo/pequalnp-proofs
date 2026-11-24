import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- First active conjunctions have witnesses inside one independent pair.
-- A point stabilizer reduces every such pair to two fixed representatives.
theorem PEqualNP.Outside.R_meta_1894_17
    (small : let X := fun i : Fin 42 => decide (i.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))
      let pair := fun (a b i : Fin 42) => decide (i = a ∨ i = b)
      let active := fun (C : Circuit) (x : Fin 42 → Bool) => ∃ (j : ℕ) (g : Gate),
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧ (C.wires (List.ofFn x)).getD (42+j) false = true
      ∀ C : Circuit, Monotone2 C → active C X →
        ∃ a b : Fin 42, X a = true ∧ X b = true ∧ active C (pair a b))
    (transport : let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let good := fun C : Circuit => ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, E u v ∧ x u = true ∧ x v = true
      let pair := fun (a b i : Fin 42) => decide (i = a ∨ i = b)
      let active := fun (C : Circuit) (x : Fin 42 → Bool) => ∃ (j : ℕ) (g : Gate),
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧ (C.wires (List.ofFn x)).getD (42+j) false = true
      ∀ (C : Circuit) (a b : Fin 42), Monotone2 C → good C → ¬(E a b ∨ E b a) → active C (pair a b) →
        ∃ (K : Circuit) (t : Fin 42), Monotone2 K ∧ K.size = C.size ∧ good K ∧
          (t = 1 ∨ t = 23) ∧ active K (pair 0 t))
    (bound : let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let good := fun C : Circuit => ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, E u v ∧ x u = true ∧ x v = true
      let pair := fun (a b i : Fin 42) => decide (i = a ∨ i = b)
      let active := fun (C : Circuit) (x : Fin 42 → Bool) => ∃ (j : ℕ) (g : Gate),
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧ (C.wires (List.ofFn x)).getD (42+j) false = true
      ∀ (C : Circuit) (t : Fin 42), (t = 1 ∨ t = 23) → Monotone2 C → good C →
        active C (pair 0 t) → 125 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  intro C hm hs hot
  by_contra fail
  let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let X := fun i : Fin 42 => decide (i.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))
  have correct (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, E u v ∧ x u = true ∧ x v = true := by
    by_contra hx
    exact fail ⟨x,hx⟩
  have independent : ∀ a b : Fin 42, X a = true → X b = true → ¬(E a b ∨ E b a) := by decide +kernel
  obtain ⟨a,b,ha,hb,dirty⟩ := small C hm hot
  obtain ⟨K,t,hK,lengthK,correctK,rep,activeK⟩ := transport C a b hm correct (independent a b ha hb) dirty
  have lower := bound K t rep hK correctK activeK
  omega
