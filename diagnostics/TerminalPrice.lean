import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search

namespace PEqualNP.Outside.L_meta_9471.TerminalPrice
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



theorem db_cons (F : Set (Clause V)) (h : Clause V) (ys : List (Clause V)) :
    db F (h::ys) = db F ys ∪ {h} := by
  ext z
  simp [db,or_assoc,or_left_comm,or_comm]

theorem insertion {G : Set (Clause V)} {a : Clause V} {l : Literal V}
    (h : conflict G ((negLit '' (↑a : Set (Literal V))) ∪ {negLit l})) :
    IsRUP G (insert l a) := by
  have eq : (negLit '' (↑(insert l a) : Set (Literal V))) =
      (negLit '' (↑a : Set (Literal V))) ∪ {negLit l} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rcases Finset.mem_insert.mp hy with e | m
      · exact Or.inr (congrArg negLit e)
      · exact Or.inl ⟨y,m,rfl⟩
    · rintro (⟨y,hy,rfl⟩ | e)
      · exact ⟨y,Finset.mem_insert_of_mem hy,rfl⟩
      · exact ⟨l,Finset.mem_insert_self _ _,e.symm⟩
  change conflict G (negLit '' (↑(insert l a) : Set (Literal V)))
  rw [eq]
  exact h

theorem physical_split {F : Set (Clause V)} (a : Clause V) (xs : List (Clause V))
    (run : IsRUPRun F xs) (target : IsRUP (db F xs) a) :
    IsRUP F a ∨
    ∃ (ys : List (Clause V)) (l : Literal V), ys.length < xs.length ∧
      IsRUPRun F ys ∧ IsRUP (db F ys) (insert l a) ∧
      IsRUP (db F ys) (insert (negLit l) a) := by
  induction run with
  | nil => left; simpa [db] using target
  | @learn ys h prior learn ih =>
    by_cases early : IsRUP (db F ys) a
    · rcases ih early with cheap | ⟨zs,l,lt,ord,one,two⟩
      · exact Or.inl cheap
      · exact Or.inr ⟨zs,l,by simp only [List.length_cons]; omega,ord,one,two⟩
    · let A := negLit '' (↑a : Set (Literal V))
      have late : conflict (db F ys ∪ {h}) A := by
        change conflict (db F (h::ys)) A at target
        simpa only [db_cons] using target
      obtain ⟨l,_,_,left,right⟩ := terminalPair (G:=db F ys) (c:=h) (A:=A) early learn late
      exact Or.inr ⟨ys,l,by simp,prior,insertion left,insertion (by simpa [inv] using right)⟩

end PEqualNP.Outside.L_meta_9471.TerminalPrice
