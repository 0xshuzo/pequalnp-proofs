import PEqualNP.Defs

namespace Triple1749

/-- Three arbitrary disjunctions of raw ports, evaluated on the indicated pair. -/
def pairVal {V : Type*} (f : Fin 3 → V → Bool) (x y : V) : Bool :=
  (f 0 x || f 0 y) && (f 1 x || f 1 y) && (f 2 x || f 2 y)

private theorem fourPorts : ∀ a0 a1 a2 u0 u1 u2 c0 c1 c2 v0 v1 v2 : Bool,
    ((a0 || u0) && (a1 || u1) && (a2 || u2))=false → ((c0 || v0) && (c1 || v1) && (c2 || v2))=false →
    ((a0 || c0) && (a1 || c1) && (a2 || c2))=true → ((u0 || v0) && (u1 || v1) && (u2 || v2))=true →
    ((a0 || v0) && (a1 || v1) && (a2 || v2))=true ∨ ((u0 || c0) && (u1 || c1) && (u2 || c2))=true := by decide +kernel

/-- A negative same-side pair in each half already prevents an induced matching
    inside the relation accepted by three conjunctive clauses. -/
theorem crosses {A B : Type*} (f : Fin 3 → A ⊕ B → Bool)
    (a u : A) (c v : B)
    (hp : pairVal f (.inl a) (.inl u) = false)
    (hl : pairVal f (.inr c) (.inr v) = false)
    (h₁ : pairVal f (.inl a) (.inr c) = true)
    (h₂ : pairVal f (.inl u) (.inr v) = true) :
    pairVal f (.inl a) (.inr v) = true ∨ pairVal f (.inl u) (.inr c) = true := by
  exact fourPorts (f 0 (.inl a)) (f 1 (.inl a)) (f 2 (.inl a)) (f 0 (.inl u)) (f 1 (.inl u)) (f 2 (.inl u)) (f 0 (.inr c)) (f 1 (.inr c)) (f 2 (.inr c)) (f 0 (.inr v)) (f 1 (.inr v)) (f 2 (.inr v)) hp hl h₁ h₂

/-- A four-cycle-free relation in which disjoint edges always cross is a
    double star as soon as its three-edge path has been specified. -/
theorem centered {A B : Type*} (R : A → B → Prop)
    (free : ∀ a u c v, a ≠ u → c ≠ v → R a c → R a v → R u c → R u v → False)
    (cross : ∀ a u c v, R a c → R u v → R a v ∨ R u c)
    {a u : A} {c v : B} (au : a ≠ u) (cv : c ≠ v)
    (uc : R u c) (ac : R a c) (av : R a v) :
    ∀ x y, R x y → x = a ∨ y = c := by
  intro x y h
  by_cases hx : x=a
  · exact Or.inl hx
  by_cases hy : y=c
  · exact Or.inr hy
  apply False.elim
  have miss : R a y → R x c → False :=
    fun ay xc => free a x c y (Ne.symm hx) (Ne.symm hy) ac ay xc h
  rcases cross a x c y ac h with ay|xc
  · rcases cross u x c y uc h with uy|xc
    · exact free a u c y au (Ne.symm hy) ac ay uc uy
    · exact miss ay xc
  · rcases cross a x v y av h with ay|xv
    · exact miss ay xc
    · exact free a x c v (Ne.symm hx) cv ac av xc xv

/-- On the central three-edge path the three raw clauses are forced up to
    reordering. The four bits are the central point, central line, leaf point,
    leaf line, in that order. -/
def val (s t w r : BitVec 4) : Prop :=
  s &&& r ≠ 0 ∧ t &&& r ≠ 0 ∧ w &&& r ≠ 0

theorem forced (s t w : BitVec 4)
    (ac : val s t w 3) (uc : val s t w 6) (av : val s t w 9)
    (pp : ¬val s t w 5) (ll : ¬val s t w 10) (off : ¬val s t w 12) :
    (s=3 ∧ t=5 ∧ w=10) ∨ (s=3 ∧ t=10 ∧ w=5) ∨
    (s=5 ∧ t=3 ∧ w=10) ∨ (s=5 ∧ t=10 ∧ w=3) ∨
    (s=10 ∧ t=3 ∧ w=5) ∨ (s=10 ∧ t=5 ∧ w=3) := by
  revert s t w
  decide +kernel

end Triple1749
