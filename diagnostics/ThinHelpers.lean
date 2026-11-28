import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9737.ThinHelpers

variable {X Y : Type}
def Rect (h : X → Y → Prop) : Prop :=
  ∃(r : X → Prop) (c : Y → Prop), ∀i j, h i j ↔ r i ∧ c j

def TwoLabels (hit : X → Y → Prop) (p q : X → Prop) (s t : Y → Prop) : Prop :=
  ∃a b : X → Y → Prop, Rect a ∧ Rect b ∧
    (∀i j, hit i j ↔ a i j ∨ b i j) ∧
    (∀i j, ¬(a i j ∧ b i j)) ∧
    (∀i j, a i j → p i ∧ ¬s j) ∧ (∀i j, b i j → q i ∧ ¬t j)

/-- Every occurrence of an AND helper can be merged into two disjoint endpoint
rectangles if its positive support on the protocol rows is a singleton. -/
theorem conjThin (hit : X → Y → Prop) (p q : X → Prop) (s t : Y → Prop)
    (i₀ : X) (single : ∀i, p i → q i → i=i₀)
    (sound : ∀i j, hit i j → (p i ∧ q i) ∧ ¬(s j ∧ t j)) :
    TwoLabels hit p q s t := by
  classical
  let a := fun i j => i=i₀ ∧ hit i₀ j ∧ ¬s j
  let b := fun i j => i=i₀ ∧ hit i₀ j ∧ s j
  refine ⟨a,b,⟨fun i => i=i₀,fun j => hit i₀ j ∧ ¬s j,fun _ _ => Iff.rfl⟩,
    ⟨fun i => i=i₀,fun j => hit i₀ j ∧ s j,fun _ _ => Iff.rfl⟩,?_,?_,?_,?_⟩
  · intro i j
    constructor
    · intro h
      obtain ⟨⟨hp,hq⟩,_⟩ := sound i j h
      obtain rfl := single i hp hq
      by_cases hs : s j
      · exact Or.inr ⟨rfl,h,hs⟩
      · exact Or.inl ⟨rfl,h,hs⟩
    · rintro (⟨rfl,h,_⟩|⟨rfl,h,_⟩) <;> exact h
  · rintro i j ⟨ha,hb⟩
    exact ha.2.2 hb.2.2
  · rintro i j ⟨rfl,h,hs⟩
    exact ⟨(sound _ _ h).1.1,hs⟩
  · rintro i j ⟨rfl,h,hs⟩
    exact ⟨(sound _ _ h).1.2,fun ht => (sound _ _ h).2 ⟨hs,ht⟩⟩

/-- Dual partition when the OR helper is false on at most one protocol column. -/
theorem disjThin (hit : X → Y → Prop) (p q : X → Prop) (s t : Y → Prop)
    (j₀ : Y) (single : ∀j, (¬s j) → (¬t j) → j=j₀)
    (sound : ∀i j, hit i j → (p i ∨ q i) ∧ ¬(s j ∨ t j)) :
    TwoLabels hit p q s t := by
  classical
  let a := fun i j => (hit i j₀ ∧ p i) ∧ j=j₀
  let b := fun i j => (hit i j₀ ∧ ¬p i) ∧ j=j₀
  refine ⟨a,b,⟨fun i => hit i j₀ ∧ p i,fun j => j=j₀,fun _ _ => Iff.rfl⟩,
    ⟨fun i => hit i j₀ ∧ ¬p i,fun j => j=j₀,fun _ _ => Iff.rfl⟩,?_,?_,?_,?_⟩
  · intro i j
    constructor
    · intro h
      have hj := (sound i j h).2
      obtain rfl := single j (fun hs => hj (Or.inl hs)) (fun ht => hj (Or.inr ht))
      by_cases hp : p i
      · exact Or.inl ⟨⟨h,hp⟩,rfl⟩
      · exact Or.inr ⟨⟨h,hp⟩,rfl⟩
    · rintro (⟨⟨h,_⟩,rfl⟩|⟨⟨h,_⟩,rfl⟩) <;> exact h
  · rintro i j ⟨ha,hb⟩
    exact hb.1.2 ha.1.2
  · rintro i j ⟨⟨h,hp⟩,rfl⟩
    exact ⟨hp,fun hs => (sound _ _ h).2 (Or.inl hs)⟩
  · rintro i j ⟨⟨h,hp⟩,rfl⟩
    exact ⟨(sound _ _ h).1.resolve_left hp,fun ht => (sound _ _ h).2 (Or.inr ht)⟩

end PEqualNP.Outside.L_meta_9737.ThinHelpers
