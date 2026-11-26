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
-- GL and GR are the exposed top guards. The singleton tests say that a guard
-- on one shore requires at least one conjunction operand on the other shore.
theorem chain_is_star (G T U : L → R → Prop) (A : J → L → Prop) (B : K → R → Prop)
    (GL : L → Prop) (GR : R → Prop) (tl : thin G) (tr : thin (fun b a => G a b))
    (ordinary : ∀ a b,T a b → G a b) (realEdge : ∀ a b,U a b → G a b)
    (apart : ∀ a b,U a b → ¬ T a b)
    (al : ∀ j a b,U a b → A j a) (ar : ∀ k a b,U a b → B k b)
    (cl : centered A T) (cr : centered B (fun b a => T a b))
    (two : ∃ a b c d, U a b ∧ U c d ∧ (a ≠ c ∨ b ≠ d))
    (guards : ∀ a b,U a b → GL a ∨ GR b)
    (singleL : ∀ a b,U a b → GL a → Nonempty K)
    (singleR : ∀ a b,U a b → GR b → Nonempty J)
    (safeL : ∀ a b c d, U a b → U c d → GL a → G a d)
    (safeR : ∀ a b c d, U a b → U c d → GR b → G c b) :
    (∃ b, (∀ a d, U a d → d=b) ∧ (∀ j : J, False)) ∨
    (∃ a, (∀ c b, U c b → c=a) ∧ (∀ k : K, False)) := by
  obtain ⟨a,b,_,_,h,_,_⟩ := two
  rcases guards a b h with wl|wr
  · have line := guardLine G T U B GL tl ordinary apart ar cr singleL safeL a b h wl
    exact Or.inl ⟨b,line,noOpposite G T U A tr ordinary realEdge apart al cl two b line⟩
  · let u : R → L → Prop := fun y x => U x y
    have line := guardLine (fun y x => G x y) (fun y x => T x y) u A GR tr
      (fun y x => ordinary x y) (fun y x => apart x y) (fun j y x => al j x y)
      cl (fun y x => singleR x y) (fun y x z q => safeR x y q z) b a h wr
    have pair : ∃ d c f e, u d c ∧ u f e ∧ (d ≠ f ∨ c ≠ e) := by
      obtain ⟨x,y,z,q,p,r,t⟩ := two
      exact ⟨y,x,q,z,p,r,t.symm⟩
    have empty := noOpposite (fun y x => G x y) (fun y x => T x y) u B tl
      (fun y x => ordinary x y) (fun y x => realEdge x y) (fun y x => apart x y)
      (fun j y x => ar j x y) cr pair a line
    exact Or.inr ⟨a,fun x y => line y x,empty⟩

end PEqualNP.Outside.L_meta_9804_Guard
