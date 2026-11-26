import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804_Guard
universe u v w z
variable {L : Type u} {R : Type v} {J : Type w} {K : Type z}

-- Each leaf operand is either raw or belongs to a lambda cone with an ordinary
-- opposite center. The latter makes all its incident cells ordinary.
def centered (A : J → L → Prop) (T : L → R → Prop) : Prop :=
  ∀ j a c, A j a → A j c → a ≠ c → ∃ b, ∀ x, A j x → T x b

def thin (G : L → R → Prop) : Prop :=
  ∀ a c b d, b ≠ d → G a b → G a d → G c b → G c d → a = c

private theorem guardLine (G T U : L → R → Prop) (B : K → R → Prop) (W : L → Prop)
    (thinG : thin G) (ordinary : ∀ a b, T a b → G a b)
    (apart : ∀ a b, U a b → ¬ T a b)
    (accepts : ∀ k a b, U a b → B k b)
    (lambda : centered B (fun b a => T a b))
    (clause : ∀ a b, U a b → W a → Nonempty K)
    (safe : ∀ a b c d, U a b → U c d → W a → G a d) :
    ∀ a b, U a b → W a → ∀ c d, U c d → d=b := by
  intro a b h w c d g
  by_contra ne
  obtain ⟨k⟩ := clause a b h w
  obtain ⟨x,row⟩ := lambda k d b (accepts k c d g) (accepts k a b h) ne
  have xb := row b (accepts k a b h)
  have xd := row d (accepts k c d g)
  have eq := thinG x a d b ne (ordinary _ _ xd) (ordinary _ _ xb)
    (safe a b c d h g w) (safe a b a b h h w)
  exact apart a b h (eq ▸ xb)

private theorem noOpposite (G T U : L → R → Prop) (A : J → L → Prop)
    (thinG : thin (fun b a => G a b)) (ordinary : ∀ a b,T a b → G a b)
    (realEdge : ∀ a b,U a b → G a b) (apart : ∀ a b,U a b → ¬ T a b)
    (accepts : ∀ j a b,U a b → A j a) (lambda : centered A T)
    (two : ∃ a b c d, U a b ∧ U c d ∧ (a ≠ c ∨ b ≠ d))
    (col : R) (same : ∀ a b, U a b → b=col) : ∀ j : J, False := by
  intro j
  obtain ⟨a,b,c,d,h,g,distinct⟩ := two
  have ha := same a b h
  have hc := same c d g
  subst b
  subst d
  have ne : a≠c := distinct.resolve_right (fun z => z rfl)
  obtain ⟨y,side⟩ := lambda j a c (accepts j a col h) (accepts j c col g) ne
  have ya := side a (accepts j a col h)
  have yc := side c (accepts j c col g)
  have eq := thinG y col a c ne (ordinary _ _ ya) (ordinary _ _ yc)
    (realEdge a col h) (realEdge c col g)
  exact apart a col h (eq ▸ ya)

-- U consists of the exceptional cells, T of the ordinary cells. A and B
-- describe the two shores of the raw OR operands of the final dirty AND.
-- guardL and guardR are the exposed top guards. The singleton tests say that a guard
-- on one shore requires at least one conjunction operand on the other shore.
theorem chain_is_star (G T U : L → R → Prop) (A : J → L → Prop) (B : K → R → Prop)
    (guardL : L → Prop) (guardR : R → Prop) (tl : thin G) (tr : thin (fun b a => G a b))
    (ordinary : ∀ a b,T a b → G a b) (realEdge : ∀ a b,U a b → G a b)
    (apart : ∀ a b,U a b → ¬ T a b)
    (al : ∀ j a b,U a b → A j a) (ar : ∀ k a b,U a b → B k b)
    (cl : centered A T) (cr : centered B (fun b a => T a b))
    (two : ∃ a b c d, U a b ∧ U c d ∧ (a ≠ c ∨ b ≠ d))
    (guards : ∀ a b,U a b → guardL a ∨ guardR b)
    (singleL : ∀ a b,U a b → guardL a → Nonempty K)
    (singleR : ∀ a b,U a b → guardR b → Nonempty J)
    (safeL : ∀ a b c d, U a b → U c d → guardL a → G a d)
    (safeR : ∀ a b c d, U a b → U c d → guardR b → G c b) :
    (∃ b, (∀ a d, U a d → d=b) ∧ (∀ j : J, False)) ∨
    (∃ a, (∀ c b, U c b → c=a) ∧ (∀ k : K, False)) := by
  obtain ⟨a,b,c,d,h,g,ne⟩ := two
  have witnesses : ∃ x y z q, U x y ∧ U z q ∧ (x ≠ z ∨ y ≠ q) :=
    ⟨a,b,c,d,h,g,ne⟩
  rcases guards a b h with wl|wr
  · have line := guardLine G T U B guardL tl ordinary apart ar cr singleL safeL a b h wl
    exact Or.inl ⟨b,line,noOpposite G T U A tr ordinary realEdge apart al cl witnesses b line⟩
  · let u : R → L → Prop := fun y x => U x y
    have line := guardLine (fun y x => G x y) (fun y x => T x y) u A guardR tr
      (fun y x => ordinary x y) (fun y x => apart x y) (fun j y x => al j x y)
      cl (fun y x => singleR x y) (fun y x z q => safeR x y q z) b a h wr
    have pair : ∃ d c f e, u d c ∧ u f e ∧ (d ≠ f ∨ c ≠ e) := by
      obtain ⟨x,y,z,q,p,r,t⟩ := witnesses
      exact ⟨y,x,q,z,p,r,t.symm⟩
    have empty := noOpposite (fun y x => G x y) (fun y x => T x y) u B tl
      (fun y x => ordinary x y) (fun y x => realEdge x y) (fun y x => apart x y)
      (fun j y x => ar j x y) cr pair a line
    exact Or.inr ⟨a,fun x y => line y x,empty⟩


def cell (U : L → R → Prop) (X : L → Prop) (Y : R → Prop) : Prop :=
  ∃ a b, U a b ∧ X a ∧ Y b
def conjunction (A : J → L → Prop) (B : K → R → Prop)
    (X : L → Prop) (Y : R → Prop) : Prop :=
  (∀ j, ∃ a, A j a ∧ X a) ∧ (∀ k, ∃ b, B k b ∧ Y b)
def guard (guardL : L → Prop) (guardR : R → Prop) (X : L → Prop) (Y : R → Prop) : Prop :=
  (∃ a, guardL a ∧ X a) ∨ (∃ b, guardR b ∧ Y b)

-- Reachability plus physical wmax gives the two operational premises here.
-- All conclusions quantify over unrestricted assignments on both shores.
theorem raw_replacement (G T U : L → R → Prop) (A : J → L → Prop) (B : K → R → Prop)
    (guardL : L → Prop) (guardR : R → Prop) (tl : thin G) (tr : thin (fun b a => G a b))
    (ordinary : ∀ a b,T a b → G a b) (realEdge : ∀ a b,U a b → G a b)
    (apart : ∀ a b,U a b → ¬ T a b) (partition : ∀ a b, G a b → T a b ∨ U a b)
    (cl : centered A T) (cr : centered B (fun b a => T a b))
    (two : ∃ a b c d, U a b ∧ U c d ∧ (a ≠ c ∨ b ≠ d))
    (fires : ∀ a b, U a b →
      conjunction A B (fun x => x=a) (fun y => y=b) ∧ (guardL a ∨ guardR b))
    (safe : ∀ X Y, conjunction A B X Y → guard guardL guardR X Y → cell G X Y) :
    (∃ c : L, (∀ X Y, X c → conjunction A B X Y) ∧
      ∀ X Y, cell G X Y ↔ cell T X Y ∨ (X c ∧ guard guardL guardR X Y)) ∨
    (∃ d : R, (∀ X Y, Y d → conjunction A B X Y) ∧
      ∀ X Y, cell G X Y ↔ cell T X Y ∨ (Y d ∧ guard guardL guardR X Y)) := by
  classical
  have al (j : J) (a b) (h : U a b) : A j a := by
    obtain ⟨_,v,rfl⟩ := (fires a b h).1.1 j
    exact v
  have ar (k : K) (a b) (h : U a b) : B k b := by
    obtain ⟨_,v,rfl⟩ := (fires a b h).1.2 k
    exact v
  have singleL (a b) (h : U a b) (wa : guardL a) : Nonempty K := by
    by_contra no
    have c : conjunction A B (fun x => x=a) (fun _ => False) :=
      ⟨fun j => ⟨a,al j a b h,rfl⟩,fun k => (no ⟨k⟩).elim⟩
    obtain ⟨_,_,_,_,bad⟩ := safe _ _ c (Or.inl ⟨a,wa,rfl⟩)
    exact bad
  have singleR (a b) (h : U a b) (wb : guardR b) : Nonempty J := by
    by_contra no
    have c : conjunction A B (fun _ => False) (fun y => y=b) :=
      ⟨fun j => (no ⟨j⟩).elim,fun k => ⟨b,ar k a b h,rfl⟩⟩
    obtain ⟨_,_,_,bad,_⟩ := safe _ _ c (Or.inr ⟨b,wb,rfl⟩)
    exact bad
  have cross (a b c d) (h : U a b) (g : U c d) (w : guardL a ∨ guardR d) : G a d := by
    have on : conjunction A B (fun x => x=a) (fun y => y=d) :=
      ⟨fun j => ⟨a,al j a b h,rfl⟩,fun k => ⟨d,ar k c d g,rfl⟩⟩
    have w' : guard guardL guardR (fun x => x=a) (fun y => y=d) :=
      w.elim (fun v => Or.inl ⟨_,v,rfl⟩) (fun v => Or.inr ⟨_,v,rfl⟩)
    obtain ⟨_,_,gg,rfl,rfl⟩ := safe _ _ on w'
    exact gg
  have ch := chain_is_star G T U A B guardL guardR tl tr ordinary realEdge apart al ar cl cr
    two (fun a b h => (fires a b h).2) singleL singleR
    (fun a b c d h g w => cross a b c d h g (Or.inl w))
    (fun a b c d h g w => cross c d a b g h (Or.inr w))
  obtain ⟨a,b,_,_,hh,_,_⟩ := two
  have keep {X Y} (h : cell T X Y) : cell G X Y := by
    obtain ⟨a,b,t,x,y⟩ := h
    exact ⟨a,b,ordinary a b t,x,y⟩
  have touched {x y X Y} (h : U x y) (on : X x) (yes : Y y) : guard guardL guardR X Y :=
    ((fires x y h).2).elim (fun v => Or.inl ⟨x,v,on⟩) (fun v => Or.inr ⟨y,v,yes⟩)
  rcases ch with ⟨d,line,empty⟩ | ⟨c,line,empty⟩
  · have bd := line a b hh
    subst d
    have trig (X Y) (on : Y b) : conjunction A B X Y :=
      ⟨fun j => (empty j).elim,fun k => ⟨b,ar k a b hh,on⟩⟩
    refine Or.inr ⟨b,trig,?_⟩
    intro X Y
    constructor
    · rintro ⟨x,y,g,on,yes⟩
      rcases partition x y g with t|u
      · exact Or.inl ⟨x,y,t,on,yes⟩
      · exact Or.inr ⟨line x y u ▸ yes,touched u on yes⟩
    · exact fun w => w.elim keep (fun h => safe X Y (trig X Y h.1) h.2)
  · have ac := line a b hh
    subst c
    have trig (X Y) (on : X a) : conjunction A B X Y :=
      ⟨fun j => ⟨a,al j a b hh,on⟩,fun k => (empty k).elim⟩
    refine Or.inl ⟨a,trig,?_⟩
    intro X Y
    constructor
    · rintro ⟨x,y,g,on,yes⟩
      rcases partition x y g with t|u
      · exact Or.inl ⟨x,y,t,on,yes⟩
      · exact Or.inr ⟨line x y u ▸ on,touched u on yes⟩
    · exact fun w => w.elim keep (fun h => safe X Y (trig X Y h.1) h.2)

end PEqualNP.Outside.L_meta_9804_Guard
