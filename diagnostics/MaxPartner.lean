import Mathlib

namespace MaxPartner3321
variable {P L : Type*}

def active (I : P → L → Prop) (X : P → Prop) (Y : L → Prop) :=
  ∃ p l, X p ∧ Y l ∧ I p l

def addOne {A : Type*} (X : A → Prop) (u : A) (x : A) := X x ∨ x=u

def maximal (I H : P → L → Prop) (X : P → Prop) (Y : L → Prop) :=
  ∀ p l, H p l → ¬ I p l → active I (addOne X p) (addOne Y l)

theorem when_added (I : P → L → Prop) (X : P → Prop) (Y : L → Prop)
    (p : P) (l : L) (ne : ¬I p l) :
    active I (addOne X p) (addOne Y l) ↔
      active I X Y ∨ (∃ j, Y j ∧ I p j) ∨ ∃ i, X i ∧ I i l := by
  constructor
  · rintro ⟨i,j,hi,hj,h⟩
    rcases hi with hx | rfl
    · rcases hj with hy | rfl
      · exact Or.inl ⟨i,j,hx,hy,h⟩
      · exact Or.inr (Or.inr ⟨i,hx,h⟩)
    · rcases hj with hy | rfl
      · exact Or.inr (Or.inl ⟨j,hy,h⟩)
      · exact (ne h).elim
  · rintro (⟨i,j,hx,hy,h⟩ | ⟨j,hy,h⟩ | ⟨i,hx,h⟩)
    · exact ⟨i,j,Or.inl hx,Or.inl hy,h⟩
    · exact ⟨p,j,Or.inr rfl,Or.inl hy,h⟩
    · exact ⟨i,l,Or.inl hx,Or.inr rfl,h⟩

theorem classify (I H : P → L → Prop) (incl : ∀ p l, I p l → H p l)
    (K : (P → Prop) → (L → Prop) → Prop)
    (mono : ∀ X Y X' Y', (∀ p, X p → X' p) → (∀ l, Y l → Y' l) → K X Y → K X' Y') :
    (∀ X Y, (active H X Y ∧ K X Y) ↔ active I X Y) ↔
      (∀ X Y, active I X Y → K X Y) ∧ (∀ X Y, K X Y → maximal I H X Y) := by
  classical
  constructor
  · intro eqn
    refine ⟨fun X Y h => ((eqn X Y).mpr h).2,?_⟩
    intro X Y k p l hp _
    have up := mono X Y (addOne X p) (addOne Y l) (fun _ h => Or.inl h) (fun _ h => Or.inl h) k
    exact (eqn _ _).mp ⟨⟨p,l,Or.inr rfl,Or.inr rfl,hp⟩,up⟩
  · rintro ⟨lower,upper⟩ X Y
    constructor
    · rintro ⟨⟨p,l,xp,yl,hp⟩,k⟩
      by_cases already : I p l
      · exact ⟨p,l,xp,yl,already⟩
      obtain ⟨i,j,hi,hj,ij⟩ := upper X Y k p l hp already
      have xi : X i := by
        rcases hi with hx | h
        · exact hx
        · simpa only [h] using xp
      have yj : Y j := by
        rcases hj with hy | h
        · exact hy
        · simpa only [h] using yl
      exact ⟨i,j,xi,yj,ij⟩
    · intro h
      obtain ⟨p,l,xp,yl,il⟩ := h
      exact ⟨⟨p,l,xp,yl,incl p l il⟩,lower X Y ⟨p,l,xp,yl,il⟩⟩

end MaxPartner3321
