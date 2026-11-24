import Mathlib
import PEqualNP.Defs

namespace Sym4801

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem flags :
    let adj (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
    ∀ p l, adj p l → ∃ (f g : Equiv.Perm (Fin 13)),
      f 0 = p ∧ g 0 = l ∧ ∀ a b, adj (f a) (g b) ↔ adj a b := by
  intro adj p l incident
  let point : Fin 4 → Fin 13 → Fin 13 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![1, 0, 4, 3, 5, 6, 11, 8, 10, 9, 7, 12, 2],
      ![3, 0, 4, 1, 7, 10, 11, 8, 6, 9, 5, 2, 12],
      ![9, 0, 4, 1, 5, 10, 6, 12, 11, 3, 7, 2, 8]]
  let line : Fin 4 → Fin 13 → Fin 13 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 4, 3, 2, 5, 10, 8, 7, 9, 6, 11, 12, 1],
      ![0, 4, 1, 11, 7, 10, 8, 5, 6, 9, 2, 12, 3],
      ![0, 4, 1, 5, 9, 10, 3, 11, 2, 7, 6, 12, 8]]
  have table : (∀ k, Function.Bijective (point k) ∧ Function.Bijective (line k)) ∧
      (∀ k, line k 0 = 0) ∧ (∀ k a b, adj (point k a) (line k b) ↔ adj a b) ∧
      (∀ a b, adj a b → ∃ k, point k 0 + b = a) := by decide +kernel
  obtain ⟨k,hk⟩ := table.2.2.2 p l incident
  let turn (z : Fin 13) : Equiv.Perm (Fin 13) :=
    ⟨fun i => i+z, fun i => i-z, fun i => by simp, fun i => by simp⟩
  let f := (Equiv.ofBijective (point k) (table.1 k).1).trans (turn l)
  let g := (Equiv.ofBijective (line k) (table.1 k).2).trans (turn l)
  have shift : ∀ a b z : Fin 13, adj (a+z) (b+z) ↔ adj a b := by decide +kernel
  refine ⟨f,g,hk,?_,fun a b => (shift _ _ _).trans (table.2.2.1 k a b)⟩
  change line k 0 + l = l
  rw [table.2.1,zero_add]

end Sym4801
