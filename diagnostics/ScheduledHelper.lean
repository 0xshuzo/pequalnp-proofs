import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search

namespace PEqualNP.Outside.L_meta_9248.Shared
variable {V : Type} [DecidableEq V]

abbrev BoardClause (V : Type) := Clause V
def conflict (G : Set (Clause V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ G, ∀ l ∈ d, UPForces G A (negLit l)
def db (F : Set (Clause V)) (cs : List (Clause V)) := F ∪ {d | d ∈ cs}

@[simp] theorem inv (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨x,b⟩
  cases b <;> rfl

theorem not_inv (l : Literal V) : negLit l ≠ l := by
  rcases l with ⟨x,b⟩
  cases b <;> simp [negLit]

theorem carry {G H : Set (Clause V)} {A B : Set (Literal V)}
    (sub : G ⊆ H) (initial : ∀ l ∈ A, UPForces H B l)
    {l} (force : UPForces G A l) : UPForces H B l := by
  induction force with
  | hyp h => exact initial _ h
  | unit hd hl _ ih => exact .unit (sub hd) hl ih

theorem substitute {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (learn : IsRUP G c) (assumeC : ∀ l ∈ c, UPForces G B (negLit l)) : conflict G B := by
  obtain ⟨d,hd,h⟩ := learn
  refine ⟨d, hd, fun l hl => carry (fun _ hs => hs) ?_ (h l hl)⟩
  rintro _ ⟨m,hm,rfl⟩
  exact assumeC _ hm

theorem splitClause {G : Set (Clause V)} {c : Clause V} {A B : Set (Literal V)}
    (lift : ∀ z∈A, UPForces G B z)
    (extra : ∀ k ∈ c, (∀ m ∈ c, m ≠ k → UPForces G B (negLit m)) → UPForces G B k)
    {l} (force : UPForces (G ∪ {c}) A l) : UPForces G B l := by
  induction force with
  | hyp h => exact lift _ h
  | @unit d k hd hk _ ih =>
    rcases hd with hd | hd
    · exact .unit hd hk ih
    · have e : d = c := hd
      subst d
      exact extra k hk ih

theorem terminalPair {G : Set (Clause V)} {c : Clause V} {A : Set (Literal V)}
    (base : ¬ conflict G A) (learn : IsRUP G c) (finish : conflict (G ∪ {c}) A) :
    ∃ l ∈ c, (∀ m∈c, m≠l → UPForces G A (negLit m)) ∧ conflict G (A ∪ {negLit l}) ∧ conflict G (A ∪ {l}) := by
  classical
  have unitExists : ∃ l ∈ c, ∀ m ∈ c, m ≠ l → UPForces G A (negLit m) := by
    by_contra missing
    have pass {z} (h : UPForces (G ∪ {c}) A z) : UPForces G A z :=
      splitClause (fun _ hm => .hyp hm) (fun k hk other => False.elim (missing ⟨k,hk,other⟩)) h
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact base ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact base (substitute learn (fun k hk => pass (dead k hk)))
  obtain ⟨l,ml,other⟩ := unitExists
  refine ⟨l,ml,other,?_,?_⟩
  · show conflict G (A ∪ {negLit l})

    apply substitute learn
    intro m hm
    by_cases eq : m = l
    · subst m
      exact .hyp (Or.inr rfl)
    · exact carry (fun _ h => h) (fun _ ha => .hyp (Or.inl ha)) (other m hm eq)

  · show conflict G (A ∪ {l})
    by_contra clean
    have notOpp (h : UPForces G (A ∪ {l}) (negLit l)) : False := by
      generalize e : negLit l = z at h
      cases h with
      | hyp hz =>
        rcases hz with ha|eq
        · apply base
          apply substitute learn
          intro m hm
          by_cases same : m=l
          · subst m
            exact .hyp (e.symm ▸ ha)
          · exact other m hm same
        · exact not_inv l (e.trans eq)
      | @unit d k hd hk rest =>
        apply clean
        refine ⟨d,hd,?_⟩
        intro m hm
        by_cases eq : m = negLit l
        · subst m
          rw [inv]
          exact .hyp (Or.inr rfl)
        · exact rest m hm (fun hk => eq (hk.trans e.symm))
    have pass {z} (h : UPForces (G ∪ {c}) A z) : UPForces G (A ∪ {l}) z := by
      apply splitClause (c:=c) (B:=A ∪ {l}) (fun _ ha => .hyp (Or.inl ha)) _ h
      intro k hk other'
      by_cases eq : k = l
      · subst k
        exact .hyp (Or.inr rfl)
      · exact False.elim (notOpp (other' l ml (Ne.symm eq)))
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact clean ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact notOpp (pass (dead l ml))



variable {I : Type} [Fintype V]
noncomputable def maximal (G : Set (Clause V)) (A : I → Set (Literal V))
    (p : I → Literal V) : Clause V := by
  classical
  exact Finset.univ.filter (fun z => ∀ i, z=p i ∨ UPForces G (A i) (negLit z))
theorem member (G : Set (Clause V)) (A : I → Set (Literal V)) (p : I → Literal V) (z : Literal V) :
    z∈maximal G A p ↔ ∀ i, z=p i ∨ UPForces G (A i) (negLit z) := by
  classical
  simp [maximal]
theorem weaken {G : Set (Clause V)} {c d : Clause V} (sub : c⊆d) (ok : IsRUP G c) : IsRUP G d := by
  obtain ⟨q,hq,all⟩ := ok
  refine ⟨q,hq,fun k hk => carry (fun _ h => h) ?_ (all k hk)⟩
  rintro _ ⟨z,hz,rfl⟩
  exact .hyp ⟨z,sub hz,rfl⟩

theorem common_helper (G : Set (Clause V)) (A : I → Set (Literal V))
    (openGoals : ∀ i, ¬conflict G (A i)) :
    (∃ c : Clause V, IsRUP G c ∧ ∀ i, conflict (G ∪ {c}) (A i)) ↔
    ∃ p : I → Literal V,
      IsRUP G (maximal G A p) ∧
      (∀ i, p i ∈ maximal G A p) ∧
      (∀ i, conflict G (A i ∪ {p i})) := by
  classical
  constructor
  · rintro ⟨c,learn,done⟩
    have pivots (i : I) := terminalPair (openGoals i) learn (done i)
    choose p mem forced _ split using pivots
    have sub : c ⊆ maximal G A p := by
      intro z hz
      apply (member G A p z).mpr
      intro i
      by_cases eq : z=p i
      · exact Or.inl eq
      · exact Or.inr (forced i z hz eq)
    exact ⟨p,weaken sub learn,fun i => sub (mem i),split⟩
  · rintro ⟨p,learn,mem,split⟩
    let c := maximal G A p
    refine ⟨c,learn,?_⟩
    intro i
    have got : UPForces (G ∪ {c}) (A i) (p i) := by
      apply UPForces.unit (Or.inr (rfl : c=c)) (mem i)
      intro m hm ne
      have v := ((member G A p m).mp hm i).resolve_left ne
      exact carry (fun _ h => Or.inl h) (fun _ h => .hyp h) v
    obtain ⟨d,hd,hf⟩ := split i
    refine ⟨d,Or.inl hd,fun m hm => carry (fun _ h => Or.inl h) ?_ (hf m hm)⟩
    rintro z (hz|hz)
    · exact .hyp hz
    · have eq : z=p i := hz
      exact eq.symm ▸ got
variable {I : Type} [Fintype V]
noncomputable def commonClause (H : I → Set (Clause V)) (A : I → Set (Literal V))
    (p : I → Literal V) : Clause V := by
  classical
  exact Finset.univ.filter (fun z => ∀ i, z=p i ∨ UPForces (H i) (A i) (negLit z))
theorem eligible (H : I → Set (Clause V)) (A : I → Set (Literal V)) (p : I → Literal V) (z : Literal V) :
    z∈commonClause H A p ↔ ∀ i, z=p i ∨ UPForces (H i) (A i) (negLit z) := by
  classical
  simp [commonClause]
theorem scheduled_helper (G : Set (Clause V)) (H : I → Set (Clause V))
    (base : ∀ i, G ⊆ H i) (A : I → Set (Literal V))
    (openGoals : ∀ i, ¬conflict (H i) (A i)) :
    (∃ c : Clause V, IsRUP G c ∧ ∀ i, conflict (H i ∪ {c}) (A i)) ↔
    ∃ p : I → Literal V,
      IsRUP G (commonClause H A p) ∧
      (∀ i, p i ∈ commonClause H A p) ∧
      (∀ i, conflict (H i) (A i ∪ {p i})) := by
  classical
  constructor
  · rintro ⟨c,learn,done⟩
    have localLearn (i : I) : IsRUP (H i) c := by
      obtain ⟨d,hd,rest⟩ := learn
      exact ⟨d,base i hd,fun m hm => carry (base i) (fun _ h => .hyp h) (rest m hm)⟩
    have pivots (i : I) := terminalPair (openGoals i) (localLearn i) (done i)
    choose p mem forced _ split using pivots
    have sub : c ⊆ commonClause H A p := by
      intro z hz
      apply (eligible H A p z).mpr
      intro i
      by_cases eq : z=p i
      · exact Or.inl eq
      · exact Or.inr (forced i z hz eq)
    exact ⟨p,weaken sub learn,fun i => sub (mem i),split⟩
  · rintro ⟨p,learn,mem,split⟩
    let c := commonClause H A p
    refine ⟨c,learn,?_⟩
    intro i
    have got : UPForces (H i ∪ {c}) (A i) (p i) := by
      apply UPForces.unit (Or.inr (rfl : c=c)) (mem i)
      intro m hm ne
      have v := ((eligible H A p m).mp hm i).resolve_left ne
      exact carry (fun _ h => Or.inl h) (fun _ h => .hyp h) v
    obtain ⟨d,hd,hf⟩ := split i
    refine ⟨d,Or.inl hd,fun m hm => carry (fun _ h => Or.inl h) ?_ (hf m hm)⟩
    rintro z (hz|hz)
    · exact .hyp hz
    · have eq : z=p i := hz
      exact eq.symm ▸ got
end PEqualNP.Outside.L_meta_9248.Shared
