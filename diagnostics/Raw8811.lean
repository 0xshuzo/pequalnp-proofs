import PEqualNP.Defs
namespace Raw8811
theorem rawOutput : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x13 : ℕ := x2 + x2;             have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);             x10 < x13 →               (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                 (∀ x17 < x9,                     ∃ x19 < x13 + x17,                       ∃ x20 < x13 + x17,                         have x21 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x13 + x17);                         x21 = x12 x19 ∪ x12 x20 ∨ x21 = x12 x19 ∨ x21 = ∅ ∨ x21 = x12 x19 ∩ x12 x20 ∧ (x17 ∈ x11 ∨ ∃ (x22 : Set (Fin x2 → Bool)) (x23 : Set (Fin x2 → Bool)), x12 x19 = x22 ×ˢ Set.univ ∧ x12 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hn deg uniq s o M W ho raw step pos neg budget
  exfalso
  by_cases hp : o<N
  · let p : Fin N := ⟨o,hp⟩
    apply neg (fun _ => false) (by simp)
    rw [show W o = {z | z.1 p=true} from (raw p).1]
    simp
  · let l : Fin N := ⟨o-N,by omega⟩
    have e : N+l.val=o := by dsimp [l]; omega
    let Y : Fin N → Bool := fun i => decide (i=l)
    have lim : Fintype.card {i : Fin N // Y i=true} ≤ q := by
      simp [Y,Fintype.card_subtype] <;> omega
    apply neg Y lim
    rw [←e,(raw l).2]
    simp [Y]
end Raw8811
