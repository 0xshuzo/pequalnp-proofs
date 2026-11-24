import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Five pairs of line inputs supply one reusable OR for each outer row.
theorem PEqualNP.Outside.R_meta_2571_17
  (patch : ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 20 ∧ C.output < 30+C.size ∧
      q < 30+C.size ∧ ∀ x : Fin 25 → Bool,
      let u := List.ofFn x ++ [x 14 || x 18, x 13 || x 17, x 15 || x 16, x 14 || x 15, x 13 || x 14]
      ((∃ p l : Fin 25, p.val ∈ ([1,3,4,5] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true) → C.eval u = true) ∧
      ((¬ ∃ p l : Fin 25, p.val < 12 ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ) ∧ x p = true ∧ x l = true) →
        C.eval u = false ∧ (C.wires u).getD q false = (x 13 || x 15 || x 21)))
  (restore : ∀ C : Circuit, Monotone2 C → C.output < 30+C.size →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size+25 ∧ D.output < 25+D.size ∧
      ∀ x : Fin 25 → Bool,
      let u := List.ofFn x ++ [x 14 || x 18, x 13 || x 17, x 15 || x 16, x 14 || x 15, x 13 || x 14]
      (D.eval (List.ofFn x) = true ↔ C.eval u = true ∨
        ∃ p l : Fin 25, p.val ∈ ([6,7,9,10,11] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true) ∧
      (∀ a : ℕ, a < 30+C.size → (D.wires (List.ofFn x)).getD a false = (C.wires u).getD a false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C,q,hC,h20,ho,hq,hw⟩ := patch
  obtain ⟨D,hD,hs,hd,hv⟩ := restore C hC ho
  refine ⟨D,q,hD,by omega,hd,by omega,?_⟩
  intro x
  let G := ∃ p l : Fin 25, p.val < 12 ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ) ∧ x p = true ∧ x l = true
  let A := ∃ p l : Fin 25, p.val ∈ ([1,3,4,5] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true
  let B := ∃ p l : Fin 25, p.val ∈ ([6,7,9,10,11] : List ℕ) ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x p = true ∧ x l = true
  have partition : G ↔ A ∨ B := by
    have part : ∀ p : Fin 25, (p.val < 12 ∧ p.val ∉ ([0,2,8] : List ℕ)) ↔
        (p.val ∈ ([1,3,4,5] : List ℕ) ∨ p.val ∈ ([6,7,9,10,11] : List ℕ)) := by decide
    constructor
    · rintro ⟨p,l,hp,hl,he,hv,hx,hy⟩
      rcases (part p).mp ⟨hp,hv⟩ with h | h
      · exact Or.inl ⟨p,l,h,hl,he,hx,hy⟩
      · exact Or.inr ⟨p,l,h,hl,he,hx,hy⟩
    · rintro (⟨p,l,h,hl,he,hx,hy⟩ | ⟨p,l,h,hl,he,hx,hy⟩)
      · obtain ⟨hp,hv⟩ := (part p).mpr (Or.inl h)
        exact ⟨p,l,hp,hl,he,hv,hx,hy⟩
      · obtain ⟨hp,hv⟩ := (part p).mpr (Or.inr h)
        exact ⟨p,l,hp,hl,he,hv,hx,hy⟩
  have out : D.eval (List.ofFn x) = true ↔ G := by
    constructor
    · intro hp
      by_contra hn
      rcases (hv x).1.mp hp with h | h
      · exact Bool.false_ne_true (((hw x).2 hn).1.symm.trans h)
      · exact hn (partition.mpr (Or.inr h))
    · intro h
      rcases partition.mp h with a | b
      · exact (hv x).1.mpr (Or.inl ((hw x).1 a))
      · exact (hv x).1.mpr (Or.inr b)
  refine ⟨out,?_⟩
  intro h
  have hn : ¬ G := fun hg => Bool.false_ne_true (h.symm.trans (out.mpr hg))
  exact ((hv x).2 q hq).trans (((hw x).2 hn).2)
