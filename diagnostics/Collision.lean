import Mathlib
import PEqualNP.Defs

namespace Collision3781

theorem collision : ∀ (m s : ℕ) (F : ℕ → Set (Finset ℕ)),
      (∀ v < m, F v = {{v}}) →
      (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) →
      let K (w : ℕ) : Set ℕ := {v | ∀ A ∈ F w, v ∈ A}
      (∃ g < s, (K (m+g)).Nonempty ∧
        ¬ ∃ a < m+g, ∃ b < m+g, K (m+g) = K a ∪ K b) →
      ∃ g < s, ∃ a < m+g, ∃ b < m+g, F (m+g) = F a ∪ F b ∧
        ∃ A ∈ F a, ∃ B ∈ F b, ¬ Disjoint A B := by
  classical
  intro m s F leaves gates K bad
  have populated (w : ℕ) (hw : w < m+s) : (F w).Nonempty := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hm : w < m
      · rw [leaves w hm]
        exact ⟨{w},rfl⟩
      · let g := w-m
        have e : m+g = w := by dsimp [g]; omega
        have hg : g < s := by omega
        obtain ⟨a,ha,b,hb,law⟩ := gates g hg
        rw [e] at ha hb law
        obtain ⟨A,hA⟩ := ih a ha (by omega)
        obtain ⟨B,hB⟩ := ih b hb (by omega)
        rcases law with h|h|h|h
        · rw [h]
          exact ⟨A ∪ B,A,hA,B,hB,rfl⟩
        · rw [h]; exact ⟨A,hA⟩
        · rw [h]; exact ⟨∅,rfl⟩
        · rw [h]; exact ⟨A,Or.inl hA⟩
  obtain ⟨g,hg,⟨v,hv⟩,novel⟩ := bad
  obtain ⟨a,ha,b,hb,law⟩ := gates g hg
  rcases law with join|copy|empty|merge
  · exfalso
    apply novel
    refine ⟨a,ha,b,hb,?_⟩
    ext x
    change (∀ C ∈ F (m+g), x ∈ C) ↔ (∀ A ∈ F a, x ∈ A) ∨ ∀ B ∈ F b, x ∈ B
    rw [join]
    constructor
    · intro h
      by_cases left : ∀ A ∈ F a, x ∈ A
      · exact Or.inl left
      · push_neg at left
        obtain ⟨A,hA,hx⟩ := left
        exact Or.inr (fun B hB => (Finset.mem_union.mp (h (A ∪ B) ⟨A,hA,B,hB,rfl⟩)).resolve_left hx)
    · rintro (left|right) _ ⟨A,hA,B,hB,rfl⟩
      · exact Finset.mem_union_left _ (left A hA)
      · exact Finset.mem_union_right _ (right B hB)
  · exfalso
    apply novel
    refine ⟨a,ha,a,ha,?_⟩
    have e : K (m+g) = K a := by dsimp only [K]; rw [copy]
    rw [e, Set.union_self]
  · exfalso
    have mem : (∅ : Finset ℕ) ∈ F (m+g) := by rw [empty]; exact rfl
    exact Finset.notMem_empty v (hv ∅ mem)
  · obtain ⟨A,hA⟩ := populated a (by omega)
    obtain ⟨B,hB⟩ := populated b (by omega)
    refine ⟨g,hg,a,ha,b,hb,merge,A,hA,B,hB,?_⟩
    intro d
    have am : A ∈ F (m+g) := by rw [merge]; exact Or.inl hA
    have bm : B ∈ F (m+g) := by rw [merge]; exact Or.inr hB
    exact Finset.disjoint_left.mp d (hv A am) (hv B bm)

end Collision3781
