import Mathlib

namespace Triple9798
variable {P L : Type}
def hit (G : P → L → Prop) (X : Set P) (Y : Set L) : Prop :=
  ∃ p ∈ X, ∃ l ∈ Y, G p l
def row (G : P → L → Prop) (a b : P) (p : P) (l : L) : Prop :=
  G p l ∨ ((p=a ∨ p=b) ∧ (G a l ∨ G b l))
def col (G : P → L → Prop) (a b : L) (p : P) (l : L) : Prop :=
  G p l ∨ ((l=a ∨ l=b) ∧ (G p a ∨ G p b))

theorem upRow {G : P → L → Prop} {X : Set P} {Y : Set L} (a b : P)
    (h : hit G X Y) : hit (row G a b) X Y := by
  obtain ⟨p,hp,l,hl,ed⟩ := h
  exact ⟨p,hp,l,hl,Or.inl ed⟩
theorem upCol {G : P → L → Prop} {X : Set P} {Y : Set L} (a b : L)
    (h : hit G X Y) : hit (col G a b) X Y := by
  obtain ⟨p,hp,l,hl,ed⟩ := h
  exact ⟨p,hp,l,hl,Or.inl ed⟩

theorem rowEq {G : P → L → Prop} {X : Set P} {Y : Set L} {a b : P}
    (agree : a∈X ↔ b∈X) (h : hit (row G a b) X Y) : hit G X Y := by
  obtain ⟨p,hp,l,hl,base | ⟨pair,edge⟩⟩ := h
  · exact ⟨p,hp,l,hl,base⟩
  · have both : a∈X ∧ b∈X := by
      rcases pair with rfl | rfl
      · exact ⟨hp,agree.mp hp⟩
      · exact ⟨agree.mpr hp,hp⟩
    rcases edge with u | v
    · exact ⟨a,both.1,l,hl,u⟩
    · exact ⟨b,both.2,l,hl,v⟩

theorem triangle (G : P → L → Prop) (a b c : P) (X : Set P) (Y : Set L) :
    hit G X Y ↔ hit (row G a b) X Y ∧ hit (row G b c) X Y ∧ hit (row G a c) X Y := by
  constructor
  · exact fun h => ⟨upRow _ _ h,upRow _ _ h,upRow _ _ h⟩
  · rintro ⟨u,v,w⟩
    classical
    have eqs : (a∈X ↔ b∈X) ∨ (b∈X ↔ c∈X) ∨ (a∈X ↔ c∈X) := by tauto
    rcases eqs with ab | bc | ac
    · exact rowEq ab u
    · exact rowEq bc v
    · exact rowEq ac w

theorem blocked {G : P → L → Prop} {a : P} {l m : L} {X : Set P} {Y : Set L}
    (active : a∈X) (h1 : G a l) (h2 : G a m)
    (h : hit (col G l m) X Y) : hit G X Y := by
  obtain ⟨p,hp,k,hk,base | ⟨pair,_⟩⟩ := h
  · exact ⟨p,hp,k,hk,base⟩
  · rcases pair with rfl | rfl
    · exact ⟨a,active,_,hk,h1⟩
    · exact ⟨a,active,_,hk,h2⟩

theorem mixed (G : P → L → Prop) (a b : P) (l m r s : L)
    (al : G a l) (am : G a m) (br : G b r) (bs : G b s) (X : Set P) (Y : Set L) :
    hit G X Y ↔ hit (row G a b) X Y ∧ hit (col G l m) X Y ∧ hit (col G r s) X Y := by
  constructor
  · exact fun h => ⟨upRow _ _ h,upCol _ _ h,upCol _ _ h⟩
  · rintro ⟨⟨p,hp,k,hk,base | ⟨pair,_⟩⟩,u,v⟩
    · exact ⟨p,hp,k,hk,base⟩
    · rcases pair with rfl | rfl
      · exact blocked hp al am u
      · exact blocked hp br bs v

end Triple9798
