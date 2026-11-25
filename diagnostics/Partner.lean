import Mathlib

namespace TwoFolds3321
variable {P L : Type*}

def edge (I : P → L → Prop) (X : P → Prop) (Y : L → Prop) :=
  ∃ p l, X p ∧ Y l ∧ I p l

def free (I : P → L → Prop) := ∀ p q s t, p≠q → s≠t →
  ¬ (I p s ∧ I p t ∧ I q s ∧ I q t)

def three (I : P → L → Prop) := ∀ p, ∃ s t u, s≠t ∧ s≠u ∧ t≠u ∧ I p s ∧ I p t ∧ I p u

def fold (I : P → L → Prop) (p q : P) (X : P → Prop) (Y : L → Prop) :=
  edge I X Y ∨ ((X p ∨ X q) ∧ ∃ s, Y s ∧ (I p s ∨ I q s))

theorem symm_fold (I : P → L → Prop) (p q : P) (X : P → Prop) (Y : L → Prop) :
    fold I p q X Y ↔ fold I q p X Y := by
  simp only [fold]
  constructor <;> rintro (h | ⟨h,s,t,k⟩)
  · exact Or.inl h
  · exact Or.inr ⟨h.symm,s,t,k.symm⟩
  · exact Or.inl h
  · exact Or.inr ⟨h.symm,s,t,k.symm⟩

theorem split (I : P → L → Prop) (nf : free I) (deg : three I) {p q : P} (ne : p≠q) :
    ∃ s t, s≠t ∧ I q s ∧ I q t ∧ ¬I p s ∧ ¬I p t := by
  obtain ⟨s,t,u,st,su,tu,qs,qt,qu⟩ := deg q
  by_cases ps : I p s
  · exact ⟨t,u,tu,qt,qu,fun pt => nf p q s t ne st ⟨ps,pt,qs,qt⟩,
      fun pu => nf p q s u ne su ⟨ps,pu,qs,qu⟩⟩
  by_cases pt : I p t
  · exact ⟨s,u,su,qs,qu,ps,fun pu => nf p q t u ne tu ⟨pt,pu,qt,qu⟩⟩
  · exact ⟨s,t,st,qs,qt,ps,pt⟩

theorem away (I : P → L → Prop) (nf : free I) (deg : three I)
    {p q r : P} (pq : p≠q) (rq : r≠q) : ∃ s, I q s ∧ ¬ I p s ∧ ¬ I r s := by
  obtain ⟨s,t,st,qs,qt,ps,pt⟩ := split I nf deg pq
  by_cases rs : I r s
  · exact ⟨t,qt,pt,fun rt => nf r q s t rq st ⟨rs,rt,qs,qt⟩⟩
  · exact ⟨s,qs,ps,rs⟩

theorem aligned_rows (I : P → L → Prop) (nf : free I) (deg : three I)
    (p q r s : P) (pq : p≠q) (ps : p≠s) (rq : r≠q) (rs : r≠s) :
    ∃ X Y, ¬edge I X Y ∧ fold I p q X Y ∧ fold I r s X Y := by
  obtain ⟨a,qa,pa,ra⟩ := away I nf deg pq rq
  obtain ⟨b,sb,pb,rb⟩ := away I nf deg ps rs
  refine ⟨fun i => i=p ∨ i=r,fun j => j=a ∨ j=b,?_,?_,?_⟩
  · rintro ⟨i,j,(rfl|rfl),(rfl|rfl),h⟩ <;> contradiction
  · exact Or.inr ⟨Or.inl (Or.inl rfl),a,Or.inl rfl,Or.inr qa⟩
  · exact Or.inr ⟨Or.inl (Or.inr rfl),b,Or.inr rfl,Or.inr sb⟩

theorem rows (I : P → L → Prop) (nf : free I) (deg : three I)
    (p q r s : P) (pq : p≠q) (rs : r≠s) :
    ∃ X Y, ¬edge I X Y ∧ fold I p q X Y ∧ fold I r s X Y := by
  by_cases pr : p=r
  · subst r
    exact aligned_rows I nf deg _ _ _ _ pq rs pq rs
  by_cases ps : p=s
  · subst s
    obtain ⟨X,Y,h,a,b⟩ := aligned_rows I nf deg _ _ _ _ pq rs.symm pq rs.symm
    exact ⟨X,Y,h,a,(symm_fold I _ _ X Y).mp b⟩
  by_cases qr : q=r
  · subst r
    obtain ⟨X,Y,h,a,b⟩ := aligned_rows I nf deg _ _ _ _ pq.symm rs pq.symm rs
    exact ⟨X,Y,h,(symm_fold I _ _ X Y).mp a,b⟩
  by_cases qs : q=s
  · subst s
    obtain ⟨X,Y,h,a,b⟩ := aligned_rows I nf deg _ _ _ _ pq.symm rs.symm pq.symm rs.symm
    exact ⟨X,Y,h,(symm_fold I _ _ X Y).mp a,(symm_fold I _ _ X Y).mp b⟩
  exact aligned_rows I nf deg _ _ _ _ pq ps (Ne.symm qr) rs

def rev (I : P → L → Prop) (l : L) (p : P) := I p l

theorem rev_free (I : P → L → Prop) (nf : free I) : free (rev I) := by
  intro l m p q lm pq
  rintro ⟨a,b,c,d⟩
  exact nf p q l m pq lm ⟨a,c,b,d⟩

theorem aligned_mixed (I : P → L → Prop) (nf : free I) (dr : three I) (dc : three (rev I))
    (p q : P) (s t : L) (pq : p≠q) (st : s≠t) (ps : ¬ I p s) :
    ∃ X Y, ¬edge I X Y ∧ fold I p q X Y ∧ fold (rev I) s t Y X := by
  obtain ⟨a,b,ab,qa,qb,pa,pb⟩ := split I nf dr pq
  obtain ⟨u,v,uv,ut,vt,us,vs⟩ := split (rev I) (rev_free I nf) dc st
  have one : ∃ j i, I q j ∧ ¬I p j ∧ I i t ∧ ¬I i s ∧ ¬I i j := by
    by_cases ua : I u a
    · by_cases ub : I u b
      · by_cases va : I v a
        · exact ⟨b,v,qb,pb,vt,vs,fun vb => nf u v a b uv ab ⟨ua,ub,va,vb⟩⟩
        · exact ⟨a,v,qa,pa,vt,vs,va⟩
      · exact ⟨b,u,qb,pb,ut,us,ub⟩
    · exact ⟨a,u,qa,pa,ut,us,ua⟩
  obtain ⟨j,i,qj,pj,it,is,ij⟩ := one
  refine ⟨fun k => k=p ∨ k=i,fun m => m=s ∨ m=j,?_,?_,?_⟩
  · rintro ⟨k,m,(rfl|rfl),(rfl|rfl),h⟩ <;> contradiction
  · exact Or.inr ⟨Or.inl (Or.inl rfl),j,Or.inr rfl,Or.inr qj⟩
  · exact Or.inr ⟨Or.inl (Or.inl rfl),i,Or.inr rfl,Or.inr it⟩

theorem mixed (I : P → L → Prop) (nf : free I) (dr : three I) (dc : three (rev I))
    (p q : P) (s t : L) (pq : p≠q) (st : s≠t) :
    ∃ X Y, ¬edge I X Y ∧ fold I p q X Y ∧ fold (rev I) s t Y X := by
  by_cases ps : I p s
  · by_cases pt : I p t
    · by_cases qs : I q s
      · obtain ⟨X,Y,h,a,b⟩ := aligned_mixed I nf dr dc q p t s pq.symm st.symm
          (fun qt => nf p q s t pq st ⟨ps,pt,qs,qt⟩)
        exact ⟨X,Y,h,(symm_fold _ _ _ X Y).mp a,(symm_fold _ _ _ Y X).mp b⟩
      · obtain ⟨X,Y,h,a,b⟩ := aligned_mixed I nf dr dc q p s t pq.symm st qs
        exact ⟨X,Y,h,(symm_fold _ _ _ X Y).mp a,b⟩
    · obtain ⟨X,Y,h,a,b⟩ := aligned_mixed I nf dr dc p q t s pq st.symm pt
      exact ⟨X,Y,h,a,(symm_fold _ _ _ Y X).mp b⟩
  · exact aligned_mixed I nf dr dc p q s t pq st ps

theorem folded_exact (I : P → L → Prop) (p q : P) (X : P → Prop) (Y : L → Prop)
    (same : X p ↔ X q) : fold I p q X Y ↔ edge I X Y := by
  constructor
  · rintro (h | ⟨h,j,y,k⟩)
    · exact h
    · rcases k with a | b
      · exact ⟨p,j,h.elim id same.mpr,y,a⟩
      · exact ⟨q,j,h.elim same.mp id,y,b⟩
  · exact Or.inl

theorem triangle (I : P → L → Prop) (p q r : P) (X : P → Prop) (Y : L → Prop) :
    fold I p q X Y ∧ fold I q r X Y ∧ fold I r p X Y ↔ edge I X Y := by
  classical
  constructor
  · rintro ⟨a,b,c⟩
    by_cases h : X p ↔ X q
    · exact (folded_exact I p q X Y h).mp a
    by_cases k : X q ↔ X r
    · exact (folded_exact I q r X Y k).mp b
    · exact (folded_exact I r p X Y (by tauto)).mp c
  · exact fun h => ⟨Or.inl h,Or.inl h,Or.inl h⟩

end TwoFolds3321

namespace TwoFolds3321
variable {P L : Type*}

theorem partner_side (I J : P → L → Prop) (nf : free I) (deg : three I)
    {a b : P} (ab : a≠b)
    (safe : ∀ X Y, fold I a b X Y → edge J X Y → edge I X Y)
    {p : P} {l : L} (jl : J p l) (nl : ¬ I p l) : I a l ∨ p=b := by
  classical
  by_cases al : I a l
  · exact Or.inl al
  by_cases pb : p=b
  · exact Or.inr pb
  obtain ⟨t,bt,at0,pt0⟩ := away I nf deg ab pb
  let X := fun x => x=a ∨ x=p
  let Y := fun y => y=t ∨ y=l
  have folded : fold I a b X Y :=
    Or.inr ⟨Or.inl (Or.inl rfl),t,Or.inl rfl,Or.inr bt⟩
  have partner : edge J X Y := ⟨p,l,Or.inr rfl,Or.inr rfl,jl⟩
  obtain ⟨x,y,hx,hy,hxy⟩ := safe X Y folded partner
  change x=a ∨ x=p at hx
  change y=t ∨ y=l at hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> contradiction

theorem all_partners (I J : P → L → Prop) (nf : free I) (deg : three I)
    {a b : P} (ab : a≠b) :
    (∀ X Y, (fold I a b X Y ∧ edge J X Y) ↔ edge I X Y) ↔
    (∀ p l, I p l → J p l) ∧ (∀ p l, J p l → ¬I p l → I a l ∧ I b l) := by
  classical
  constructor
  · intro eqn
    have safe := fun X Y f j => (eqn X Y).mp ⟨f,j⟩
    have reverseSafe : ∀ X Y, fold I b a X Y → edge J X Y → edge I X Y :=
      fun X Y h j => safe X Y ((symm_fold I b a X Y).mp h) j
    constructor
    · intro p l h
      let X := fun x => x=p
      let Y := fun y => y=l
      obtain ⟨x,y,hx,hy,hxy⟩ := ((eqn X Y).mpr ⟨p,l,rfl,rfl,h⟩).2
      change x=p at hx
      change y=l at hy
      simpa only [hx,hy] using hxy
    · intro p l jl nl
      have af := partner_side I J nf deg ab safe jl nl
      have bf := partner_side I J nf deg ab.symm reverseSafe jl nl
      rcases af with al | rfl
      · rcases bf with bl | rfl
        · exact ⟨al,bl⟩
        · exact (nl al).elim
      · rcases bf with bl | ba
        · exact (nl bl).elim
        · exact (ab ba.symm).elim
  · rintro ⟨cover,extra⟩ X Y
    constructor
    · rintro ⟨direct|⟨hit,_⟩,partner⟩
      · exact direct
      obtain ⟨p,l,xp,yl,jl⟩ := partner
      by_cases il : I p l
      · exact ⟨p,l,xp,yl,il⟩
      have sides := extra p l jl il
      rcases hit with xa | xb
      · exact ⟨a,l,xa,yl,sides.1⟩
      · exact ⟨b,l,xb,yl,sides.2⟩
    · intro h
      obtain ⟨p,l,xp,yl,il⟩ := h
      exact ⟨Or.inl ⟨p,l,xp,yl,il⟩,p,l,xp,yl,cover p l il⟩

end TwoFolds3321
