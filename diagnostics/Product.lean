import PEqualNP.Defs

namespace Product9798

variable {P L : Type*}

def hits (E : P → L → Prop) (X : P → Prop) (Y : L → Prop) : Prop :=
  ∃ p l, E p l ∧ X p ∧ Y l

def compatible (E A B : P → L → Prop) : Prop :=
  ∀ p l q m, A p l → ¬ E p l → B q m → ¬ E q m → E p m ∨ E q l

theorem exactProduct {E A B : P → L → Prop}
    (ea : ∀ p l, E p l → A p l) (eb : ∀ p l, E p l → B p l) :
    (∀ X Y, hits E X Y ↔ hits A X Y ∧ hits B X Y) ↔ compatible E A B := by
  classical
  constructor
  · intro eqn p l q m apl epl bqm eqm
    let X : P → Prop := fun x => x=p ∨ x=q
    let Y : L → Prop := fun y => y=l ∨ y=m
    have ah : hits A X Y := ⟨p,l,apl,Or.inl rfl,Or.inl rfl⟩
    have bh : hits B X Y := ⟨q,m,bqm,Or.inr rfl,Or.inr rfl⟩
    obtain ⟨u,v,edge,hx,hy⟩ := (eqn X Y).mpr ⟨ah,bh⟩
    change u=p ∨ u=q at hx
    change v=l ∨ v=m at hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> tauto
  · intro good X Y
    constructor
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨⟨p,l,ea p l h,hp,hl⟩,⟨p,l,eb p l h,hp,hl⟩⟩
    · rintro ⟨⟨p,l,apl,hp,hl⟩,⟨q,m,bqm,hq,hm⟩⟩
      by_cases h : E p l
      · exact ⟨p,l,h,hp,hl⟩
      by_cases k : E q m
      · exact ⟨q,m,k,hq,hm⟩
      rcases good p l q m apl h bqm k with g|g
      · exact ⟨p,m,g,hp,hm⟩
      · exact ⟨q,l,g,hq,hl⟩

def privatePair (E : P → L → Prop) (l m : L) : Prop :=
  ∃ u v, u≠v ∧ E u l ∧ ¬E u m ∧ E v l ∧ ¬E v m

theorem foldForces {E A B : P → L → Prop} {l m : L}
    (rect : ∀ u v i j, E u i → E v i → E u j → E v j → u=v ∨ i=j)
    (distinct : l≠m) (privL : privatePair E l m) (privM : privatePair E m l)
    (folded : ∀ p, E p l ∨ E p m → A p l ∧ A p m)
    (good : compatible E A B) {q : P} {s : L} (accepted : B q s) (extra : ¬E q s) :
    E q l ∧ E q m := by
  classical
  have force (i j : L) (priv : privatePair E j i) (extend : ∀ p, E p j → A p i) :
      E q i ∨ s=j := by
    by_cases qi : E q i
    · exact Or.inl qi
    obtain ⟨u,v,uv,uj,ui,vj,vi⟩ := priv
    have us := (good u i q s (extend u uj) ui accepted extra).resolve_right qi
    have vs := (good v i q s (extend v vj) vi accepted extra).resolve_right qi
    exact Or.inr ((rect u v j s uj vj us vs).resolve_left uv).symm
  have left := force l m privM (fun p h => (folded p (Or.inr h)).1)
  have right := force m l privL (fun p h => (folded p (Or.inl h)).2)
  rcases left with h|h
  · rcases right with k|k
    · exact ⟨h,k⟩
    · exact False.elim (extra (k.symm ▸ h))
  · rcases right with k|k
    · exact False.elim (extra (h.symm ▸ k))
    · exact False.elim (distinct (k.symm.trans h))

end Product9798
