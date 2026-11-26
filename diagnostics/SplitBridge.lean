import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search

namespace PEqualNP.Outside.L_meta_9246.SplitBridge
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
    ∃ l ∈ c, conflict G (A ∪ {negLit l}) ∧ conflict G (A ∪ {l}) := by
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
  refine ⟨l,ml,?_,?_⟩
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


theorem oneHelper {G : Set (Clause V)} (t : Clause V) :
    (∃ q : Clause V, IsRUP G q ∧ IsRUP (G ∪ {q}) t) ↔
      IsRUP G t ∨ ∃ l : Literal V,
        conflict G ((negLit '' (↑t : Set (Literal V))) ∪ {negLit l}) ∧
        conflict G ((negLit '' (↑t : Set (Literal V))) ∪ {l}) := by
  classical
  let A := negLit '' (↑t : Set (Literal V))
  constructor
  · rintro ⟨q,learn,finish⟩
    by_cases yes : IsRUP G t
    · exact Or.inl yes
    · obtain ⟨l,_,u,v⟩ := terminalPair (A:=A) yes learn finish
      exact Or.inr ⟨l,u,v⟩
  · rintro (orig|⟨l,no,yes⟩)
    · refine ⟨t,orig,?_⟩
      obtain ⟨d,hd,dead⟩ := orig
      exact ⟨d,Or.inl hd,fun m hm => carry (fun _ hg => Or.inl hg) (fun _ ha => .hyp ha) (dead m hm)⟩
    · let q := insert l t
      refine ⟨q,?_,?_⟩
      · obtain ⟨d,hd,dead⟩ := no
        refine ⟨d,hd,fun m hm => carry (fun _ hg => hg) ?_ (dead m hm)⟩
        rintro k (⟨z,hz,rfl⟩|eq)
        · exact .hyp ⟨z,Finset.mem_insert_of_mem hz,rfl⟩
        · have same : k=negLit l := eq
          subst k
          exact .hyp ⟨l,Finset.mem_insert_self ..,rfl⟩
      · have derives : UPForces (G ∪ {q}) A l := by
          apply UPForces.unit (Or.inr (rfl : q=q)) (Finset.mem_insert_self ..)
          intro m hm ne
          obtain h|h := Finset.mem_insert.mp hm
          · exact False.elim (ne h)
          · exact .hyp ⟨m,h,rfl⟩
        obtain ⟨d,hd,dead⟩ := yes
        refine ⟨d,Or.inl hd,fun m hm => carry (fun _ hg => Or.inl hg) ?_ (dead m hm)⟩
        rintro k (ha|eq)
        · exact .hyp ha
        · have same : k=l := eq
          subst k
          exact derives
end PEqualNP.Outside.L_meta_9246.SplitBridge
