import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4035_461
    (budget : let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = F x) →
        15 + C.gates.countP (fun g => g.op.eval [false]) ≤ C.size)
    (sign : let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
      let read := (fun g : Gate => g.inputs.take (if g.op.eval [false] then 1 else 2))
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = F x) →
        (∀ g ∈ C.gates, 0 ∉ read g) → 0 < C.gates.countP (fun g => g.op.eval [false]))
    (search : let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
      let read := (fun g : Gate => g.inputs.take (if g.op.eval [false] then 1 else 2))
      ∀ C : Circuit, FanInTwo C → (∀ g ∈ C.gates, 0 ∉ read g) →
        0 < C.gates.countP (fun g => g.op.eval [false]) → C.gates.countP (fun g => g.op.eval [false]) ≤ 3 →
        C.size ≤ 18 → (∃ a b : Fin C.gates.length, ∀ j : Fin C.gates.length,
          10 ∈ read (C.gates.get j) → j = a ∨ j = b) →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ F x)
 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  intro C fan size correct avoid wit
  let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
  let read := (fun g : Gate => g.inputs.take (if g.op.eval [false] then 1 else 2))
  have ev : (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = F x) := by
    intro x
    rw [correct]
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have mem (g : Gate) (hg : g ∈ C.gates) (i : ℕ) (hi : i ∈ read g) :
      (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs) := by
    by_cases hn : g.op = .not
    · left
      refine ⟨hn,?_⟩
      change i ∈ g.inputs.take (if g.op.eval [false] then 1 else 2) at hi
      rw [hn] at hi
      change i ∈ g.inputs.take 1 at hi
      cases h : g.inputs with
      | nil => simp [h] at hi
      | cons a l =>
        simpa [h,eq_comm] using hi
    · exact Or.inr ⟨hn,List.mem_of_mem_take hi⟩
  have zero (g : Gate) (hg : g ∈ C.gates) : 0 ∉ read g := by
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
    intro hit
    obtain h | h := mem _ (List.get_mem _ _) 0 hit
    · exact (avoid j).1 h.1 h.2
    · exact (avoid j).2 h.1 h.2
  have lo := budget C fan ev
  have pos := sign C fan ev zero
  obtain ⟨a,b,hab⟩ := wit
  have M (j : Fin C.gates.length) (hj : 10 ∈ read (C.gates.get j)) : j=a ∨ j=b := by
    obtain h | h := mem _ (List.get_mem _ _) 10 hj
    · exact (hab j).1 h.1 h.2
    · exact (hab j).2 h.1 h.2
  obtain ⟨x,hx⟩ := search C fan zero pos (by omega) size ⟨a,b,M⟩
  exact hx (ev x)
