import Mathlib

namespace Alignment3321

variable {α β : Type*}

def leF (f g : α → Prop) := ∀ x, f x → g x

def aligned (p q : α → Prop) (l r : β → Prop) :=
  (leF p q ∨ leF r l) ∧ (leF q p ∨ leF l r)

theorem merge_iff (p q : α → Prop) (l r : β → Prop) :
    (∀ x y, ((p x ∨ l y) ∧ (q x ∨ r y)) → (p x ∧ q x) ∨ (l y ∧ r y)) ↔
    aligned p q l r := by
  classical
  constructor
  · intro h
    constructor
    · by_cases sub : leF p q
      · exact Or.inl sub
      · right
        obtain ⟨x,px,nq⟩ : ∃ x, p x ∧ ¬ q x := by
          by_contra! all
          exact sub all
        intro y ry
        rcases h x y ⟨Or.inl px,Or.inr ry⟩ with a | b
        · exact (nq a.2).elim
        · exact b.1
    · by_cases sub : leF q p
      · exact Or.inl sub
      · right
        obtain ⟨x,qx,np⟩ : ∃ x, q x ∧ ¬ p x := by
          by_contra! all
          exact sub all
        intro y ly
        rcases h x y ⟨Or.inr ly,Or.inl qx⟩ with a | b
        · exact (np a.1).elim
        · exact b.2
  · rintro ⟨s,t⟩ x y ⟨hp,hq⟩
    rcases hp with px | ly <;> rcases hq with qx | ry
    · exact Or.inl ⟨px,qx⟩
    · rcases s with pq | rl
      · exact Or.inl ⟨px,pq x px⟩
      · exact Or.inr ⟨rl y ry,ry⟩
    · rcases t with qp | lr
      · exact Or.inl ⟨qp x qx,qx⟩
      · exact Or.inr ⟨ly,lr y ly⟩
    · exact Or.inr ⟨ly,ry⟩

theorem classify (p q : α → Prop) (l r : β → Prop) :
    aligned p q l r ↔ p=q ∨ l=r ∨
      (leF p q ∧ leF l r) ∨ (leF q p ∧ leF r l) := by
  constructor
  · rintro ⟨a,b⟩
    rcases a with a | a <;> rcases b with b | b
    · exact Or.inl (funext fun x => propext ⟨a x,b x⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a,b⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b,a⟩))
    · exact Or.inr (Or.inl (funext fun y => propext ⟨b y,a y⟩))
  · rintro (rfl | rfl | ⟨pq,lr⟩ | ⟨qp,rl⟩)
    · exact ⟨Or.inl (fun _ => id),Or.inl (fun _ => id)⟩
    · exact ⟨Or.inr (fun _ => id),Or.inr (fun _ => id)⟩
    · exact ⟨Or.inl pq,Or.inr lr⟩
    · exact ⟨Or.inr rl,Or.inl qp⟩

theorem sep {γ : Type*} (f g : γ → Prop) (h : ¬ leF f g) : ∃ z, f z ∧ ¬ g z := by
  classical
  by_contra! all
  exact h all

theorem cross_witness (p q : α → Prop) (l r : β → Prop) :
    ¬ aligned p q l r ↔
    (∃ x y, p x ∧ ¬ q x ∧ r y ∧ ¬ l y) ∨ (∃ x y, q x ∧ ¬ p x ∧ l y ∧ ¬ r y) := by
  classical
  constructor
  · intro bad
    by_cases first' : leF p q ∨ leF r l
    · right
      have second' := not_or.mp (show ¬(leF q p ∨ leF l r) from fun h => bad ⟨first',h⟩)
      obtain ⟨x,hx,nx⟩ := sep _ _ second'.1
      obtain ⟨y,hy,ny⟩ := sep _ _ second'.2
      exact ⟨x,y,hx,nx,hy,ny⟩
    · left
      obtain ⟨x,hx,nx⟩ := sep _ _ (not_or.mp first').1
      obtain ⟨y,hy,ny⟩ := sep _ _ (not_or.mp first').2
      exact ⟨x,y,hx,nx,hy,ny⟩
  · rintro (⟨x,y,hx,nx,hy,ny⟩ | ⟨x,y,hx,nx,hy,ny⟩) ⟨a,b⟩
    · exact a.elim (fun h => nx (h x hx)) (fun h => ny (h y hy))
    · exact b.elim (fun h => nx (h x hx)) (fun h => ny (h y hy))

end Alignment3321
