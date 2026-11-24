import Mathlib

namespace FirstSplit4684

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem shifted_heptad : ∀ t : Fin 13,
    let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
    let X : Finset (Fin 13) := {t,t+1,t+2}
    let Y : Finset (Fin 13) := {t+3,t+7,t+8,t+9}
    (∀ l, l ∈ Y ↔ ∀ p ∈ X, ¬ I p l) ∧
    (∀ p ∉ X, ∃ l ∈ Y, I p l) ∧
    (¬ ∃ l, ∀ p ∈ X, I p l) ∧ (¬ ∃ p, ∀ l ∈ Y, I p l) := by
  decide

theorem first_split {E : Type*} (s : ℕ) (G : Fin s → Bool → Set E)
    (bare : Set E → Prop) (D : Set E) (e f : E)
    (be : e ∈ D) (bf : f ∈ D) (apart : ∀ W, bare W → e ∈ W → f ∉ W)
    (T : Set (Fin s))
    (steps : ∀ j ∈ T, ∀ b, bare (G j b) ∨ ∃ i ∈ T, i < j ∧ G j b ⊆ G i false ∪ G i true)
    (root : bare D ∨ ∃ i ∈ T, D ⊆ G i false ∪ G i true) :
    ∃ i ∈ T,
      (e ∈ G i false ∧ e ∉ G i true ∧ f ∈ G i true ∧ f ∉ G i false) ∨
      (f ∈ G i false ∧ f ∉ G i true ∧ e ∈ G i true ∧ e ∉ G i false) := by
  classical
  let both (i : Fin s) := e ∈ G i false ∪ G i true ∧ f ∈ G i false ∪ G i true
  let P := Finset.univ.filter (fun i : Fin s => i ∈ T ∧ both i)
  have ne : P.Nonempty := by
    rcases root with hb | ⟨i,hi,sub⟩
    · exact (apart D hb be bf).elim
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, sub be, sub bf⟩⟩
  let i := P.min' ne
  have hi : i ∈ P := Finset.min'_mem P ne
  obtain ⟨it,he,hf⟩ := (Finset.mem_filter.mp hi).2
  have gap (b : Bool) : ¬ (e ∈ G i b ∧ f ∈ G i b) := by
    rintro ⟨eb,fb⟩
    rcases steps i it b with h | ⟨j,jt,lt,sub⟩
    · exact apart _ h eb fb
    · have jm : j ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,jt,sub eb,sub fb⟩
      exact (not_lt_of_ge (Finset.min'_le P j jm)) lt
  refine ⟨i,it,?_⟩
  have gl := gap false
  have gr := gap true
  change e ∈ G i false ∨ e ∈ G i true at he
  change f ∈ G i false ∨ f ∈ G i true at hf
  tauto

end FirstSplit4684
