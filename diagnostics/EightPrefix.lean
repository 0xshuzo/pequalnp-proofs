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

namespace PEqualNP.Outside.L_meta_9248.Shared
variable {V : Type} [Fintype V] [DecidableEq V]
def extendBoard (A : Set (Literal V)) : Option (Literal V) → Set (Literal V)
  | none => A
  | some l => A ∪ {l}

-- Before conflict, adding a single learned clause to a saturated board is
-- equivalent to making either zero or one additional literal assumption.
theorem virtual (G : Set (Clause V)) (A : Set (Literal V)) {c : Clause V}
    (learn : IsRUP G c) (clean : ¬ conflict (G ∪ {c}) A) :
    ∃ o : Option (Literal V), ∀ k, UPForces (G ∪ {c}) A k ↔ UPForces G (extendBoard A o) k := by
  classical
  let G' := G ∪ {c}
  have inc {z} (h : UPForces G A z) : UPForces G' A z :=
    carry (fun _ hd => Or.inl hd) (fun _ ha => .hyp ha) h
  by_cases readyUnit : ∃ l∈c,∀ m∈c,m≠l → UPForces G A (negLit m)
  · obtain ⟨l,hl,all⟩ := readyUnit
    have got : UPForces G' A l :=
      UPForces.unit (Or.inr (rfl : c=c)) hl (fun m hm ne => inc (all m hm ne))
    have back {k} (h : UPForces G (A ∪ {l}) k) : UPForces G' A k := by
      apply carry (fun _ hd => Or.inl hd) _ h
      rintro z (ha|eq)
      · exact .hyp ha
      · have e : z=l := eq
        exact e.symm ▸ got
    have no : ¬ UPForces G (A ∪ {l}) (negLit l) := by
      intro opp
      apply clean
      refine ⟨c,Or.inr rfl,?_⟩
      intro m hm
      by_cases same : m=l
      · subst m
        exact back opp
      · exact inc (all m hm same)
    refine ⟨some l,fun k => ⟨?_,fun h => back h⟩⟩
    intro h
    apply splitClause (c:=c) (B:=A ∪ {l}) (fun _ ha => .hyp (Or.inl ha)) _ h
    intro z hz other
    by_cases e : z=l
    · subst z
      exact .hyp (Or.inr rfl)
    · exact (no (other l hl e.symm)).elim
  · refine ⟨none,fun k => ⟨?_,inc⟩⟩
    intro h
    exact splitClause (fun _ ha => .hyp ha)
      (fun l hl other => False.elim (readyUnit ⟨l,hl,other⟩)) h

variable {I : Type}
def candidates (G : Set (Clause V)) (A : I → Set (Literal V)) (q : Clause V) : Prop :=
  ∃ used : Set I, ∃ first : used → Option (Literal V), ∃ second : used → Literal V,
    q=maximal G (fun i => extendBoard (A i.val) (first i)) second

theorem two_canonical (G : Set (Clause V)) (A : I → Set (Literal V)) :
    (∃ c q : Clause V, IsRUP G c ∧ IsRUP (G ∪ {c}) q ∧
      ∀ i, conflict ((G ∪ {c}) ∪ {q}) (A i)) ↔
    ∃ q : Clause V, candidates G A q ∧ ∃ c : Clause V, IsRUP G c ∧
      IsRUP (G ∪ {c}) q ∧ ∀ i, conflict ((G ∪ {c}) ∪ {q}) (A i) := by
  classical
  constructor
  · rintro ⟨c,q,hc,hq,go⟩
    let H := G ∪ {c}
    let used : Set I := {i | ¬conflict H (A i)}
    have v (i : used) := virtual G (A i.val) hc i.property
    choose first eqv using v
    have goals (i : used) : ¬conflict H (A i.val) := i.property
    obtain ⟨second,learn,mem,yes⟩ :=
      (common_helper H (fun i : used => A i.val) goals).mp ⟨q,hq,fun i => go i.val⟩
    let Q := maximal H (fun i : used => A i.val) second
    have same : Q=maximal G (fun i => extendBoard (A i.val) (first i)) second := by
      ext z
      rw [show Q=maximal H (fun i : used => A i.val) second from rfl,member,member]
      exact forall_congr' (fun i => or_congr_right (fun _ => eqv i (negLit z)))
    refine ⟨Q,⟨used,first,second,same⟩,c,hc,learn,?_⟩
    intro i
    by_cases already : conflict H (A i)
    · obtain ⟨d,hd,all⟩ := already
      exact ⟨d,Or.inl hd,fun m hm => carry (fun _ h => Or.inl h) (fun _ h => .hyp h) (all m hm)⟩
    · let j : used := ⟨i,already⟩
      have derive : UPForces (H ∪ {Q}) (A i) (second j) := by
        apply UPForces.unit (Or.inr (rfl : Q=Q)) (mem j)
        intro z hz ne
        have h := ((member H (fun i : used => A i.val) second z).mp hz j).resolve_left ne
        exact carry (fun _ hd => Or.inl hd) (fun _ ha => .hyp ha) h
      obtain ⟨d,hd,all⟩ := yes j
      refine ⟨d,Or.inl hd,fun m hm => carry (fun _ hd => Or.inl hd) ?_ (all m hm)⟩
      rintro z (ha|eq)
      · exact .hyp ha
      · have e : z=second j := eq
        exact e.symm ▸ derive
  · rintro ⟨q,_,c,hc,hq,go⟩
    exact ⟨c,q,hc,hq,go⟩
end PEqualNP.Outside.L_meta_9248.Shared


open PEqualNP.ProofComplexity PEqualNP.Search

namespace RUP9248
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

theorem splitClause {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (extra : ∀ k ∈ c, (∀ m ∈ c, m ≠ k → UPForces G B (negLit m)) → UPForces G B k)
    {l} (force : UPForces (G ∪ {c}) ∅ l) : UPForces G B l := by
  induction force with
  | hyp h => simp at h
  | @unit d k hd hk _ ih =>
    rcases hd with hd | hd
    · exact .unit hd hk ih
    · have e : d = c := hd
      subst d
      exact extra k hk ih

theorem terminalPair {G : Set (Clause V)} {c : Clause V}
    (base : ¬ conflict G ∅) (learn : IsRUP G c) (finish : conflict (G ∪ {c}) ∅) :
    ∃ l ∈ c, IsRUP G {l} ∧ IsRUP G {negLit l} := by
  classical
  have unitExists : ∃ l ∈ c, ∀ m ∈ c, m ≠ l → UPForces G ∅ (negLit m) := by
    by_contra missing
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G ∅ z :=
      splitClause (fun k hk other => False.elim (missing ⟨k,hk,other⟩)) h
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact base ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact base (substitute learn (fun k hk => pass (dead k hk)))
  obtain ⟨l,ml,other⟩ := unitExists
  refine ⟨l,ml,?_,?_⟩
  · have bad : conflict G {negLit l} := by
      apply substitute learn
      intro m hm
      by_cases eq : m = l
      · subst m
        exact .hyp (by simp)
      · exact carry (fun _ h => h) (by simp) (other m hm eq)
    simpa [IsRUP,conflict] using bad
  · suffices bad : conflict G {l} by simpa [IsRUP,conflict] using bad
    by_contra clean
    have notOpp (h : UPForces G {l} (negLit l)) : False := by
      generalize e : negLit l = z at h
      cases h with
      | hyp hz =>
        have eq : _ = l := hz
        exact not_inv l (e.trans eq)
      | @unit d k hd hk rest =>
        apply clean
        refine ⟨d,hd,?_⟩
        intro m hm
        by_cases eq : m = negLit l
        · subst m
          rw [inv]
          exact .hyp (by simp)
        · exact rest m hm (fun hk => eq (hk.trans e.symm))
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G {l} z := by
      apply splitClause (c:=c) (B:={l}) _ h
      intro k hk other'
      by_cases eq : k = l
      · subst k
        exact .hyp (by simp)
      · exact False.elim (notOpp (other' l ml (Ne.symm eq)))
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact clean ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact notOpp (pass (dead l ml))

theorem dbCons (F : Set (Clause V)) (c : Clause V) (cs : List (Clause V)) :
    db F (c :: cs) = db F cs ∪ {c} := by
  ext d
  simp [db,or_comm,or_left_comm,or_assoc]

theorem preceding {F : Set (Clause V)} {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧ conflict (db F ps) ∅ := by
  induction run with
  | nil => simp at member
  | @learn ps c prev learn ih =>
    rcases List.mem_cons.mp member with eq | inTail
    · subst c
      exact ⟨ps,prev,by simp,by simpa [db,conflict,IsRUP] using learn⟩
    · obtain ⟨ts,tv,tl,tc⟩ := ih inTail
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,tc⟩

theorem pairFromRoot {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (root : conflict (db F cs) ∅) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  induction run with
  | nil => exact False.elim (clean (by simpa [db] using root))
  | @learn ps c prev learn ih =>
    by_cases earlier : conflict (db F ps) ∅
    · obtain ⟨ts,tv,tl,more⟩ := ih earlier
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,more⟩
    · rw [dbCons] at root
      obtain ⟨l,_,a,b⟩ := terminalPair earlier learn root
      exact ⟨ps,prev,by simp,l,a,b⟩

theorem pairPrefix {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length + 2 ≤ cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  obtain ⟨qs,qv,ql,qc⟩ := preceding run member
  obtain ⟨ps,pv,pl,goal⟩ := pairFromRoot clean qv qc
  exact ⟨ps,pv,by omega,goal⟩

theorem pairSuffices {F : Set (Clause V)} {ps : List (Clause V)} (run : IsRUPRun F ps)
    (l : Literal V) (left : IsRUP (db F ps) {l}) (right : IsRUP (db F ps) {negLit l}) :
    IsRUPRun F ((∅ : Clause V) :: {l} :: ps) := by
  have one : IsRUPRun F ({l} :: ps) := .learn run left
  apply IsRUPRun.learn one
  change IsRUP (db F ({l} :: ps)) ∅
  rw [dbCons]
  have assumeL : UPForces (db F ps ∪ {{l}}) ∅ l :=
    .unit (D:={l}) (Or.inr rfl) (by simp) (by simp)
  obtain ⟨d,hd,dead⟩ := right
  have bad : conflict (db F ps ∪ {{l}}) ∅ := by
    refine ⟨d,Or.inl hd,fun k hk => carry (fun _ h => Or.inl h) ?_ (dead k hk)⟩
    rintro _ ⟨q,hq,rfl⟩
    have e : q = negLit l := Finset.mem_singleton.mp hq
    simpa [e] using assumeL
  simpa [conflict,IsRUP] using bad

abbrev V54 := Fin 5 × Fin 4

theorem clean54 : ¬conflict (PHP 5 4) ∅ := by
  have rows : ∀ p : Fin 5, 1 < (Finset.univ.image
      (fun h : Fin 4 => (((p,h),true) : Literal V54))).card := by decide +kernel
  have cols : ∀ p q : Fin 5, ∀ h : Fin 4, p ≠ q →
      1 < ({((p,h),false),((q,h),false)} : Clause V54).card := by decide +kernel
  have wide : ∀ d ∈ PHP 5 4, 1 < d.card := by
    rintro d (⟨p,rfl⟩|⟨p,q,h,ne,rfl⟩)
    · exact rows p
    · exact cols p q h ne
  have impossible {l : Literal V54} (f : UPForces (PHP 5 4) ∅ l) : False := by
    induction f with
    | hyp h => simp at h
    | @unit d k hd hk rest ih =>
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (wide d hd)
      by_cases e : a=k
      · subst k
        exact ih b hb (Ne.symm ne)
      · exact ih a ha e
  rintro ⟨d,hd,dead⟩
  obtain ⟨k,hk,_,_,_⟩ := Finset.one_lt_card.mp (wide d hd)
  exact impossible (dead k hk)

theorem exact54 :
    (∃ cs : List (Clause V54), IsRUPRun (PHP 5 4) cs ∧ (∅ : Clause V54) ∈ cs ∧ cs.length ≤ 12) ↔
    ∃ ps : List (Clause V54), IsRUPRun (PHP 5 4) ps ∧ ps.length ≤ 10 ∧
      ∃ l : Literal V54, IsRUP (db (PHP 5 4) ps) {l} ∧ IsRUP (db (PHP 5 4) ps) {negLit l} := by
  constructor
  · rintro ⟨cs,run,member,length⟩
    obtain ⟨ps,prev,lim,more⟩ := pairPrefix clean54 run member
    exact ⟨ps,prev,by omega,more⟩
  · rintro ⟨ps,run,lim,l,one,two⟩
    exact ⟨_,pairSuffices run l one two,by simp,by simp only [List.length_cons]; omega⟩

end RUP9248

namespace PEqualNP.Outside.L_meta_9248.Shared
variable {V : Type} [Fintype V] [DecidableEq V]
def goalClause (l : Literal V) (b : Bool) : Clause V :=
  if b then {l} else {negLit l}
abbrev opened (G : Set (Clause V)) (l : Literal V) := {b : Bool // ¬IsRUP G (goalClause l b)}
def boardOf (G : Set (Clause V)) (l : Literal V) (i : opened G l) : Set (Literal V) :=
  negLit '' (↑(goalClause l i.val) : Set (Literal V))

def ready (G : Set (Clause V)) (l : Literal V) : Prop :=
  (∀ b, IsRUP G (goalClause l b)) ∨
  ∃ p : opened G l → Literal V, IsRUP G (maximal G (boardOf G l) p) ∧
    (∀ i, p i ∈ maximal G (boardOf G l) p) ∧
    (∀ i, conflict G (boardOf G l i ∪ {p i}))

theorem ready_iff (G : Set (Clause V)) (l : Literal V) :
    ready G l ↔ (∀ b, IsRUP G (goalClause l b)) ∨
      ∃ q : Clause V, IsRUP G q ∧ ∀ b, IsRUP (G ∪ {q}) (goalClause l b) := by
  classical
  have criterion := common_helper G (boardOf G l) (fun i => i.property)
  constructor
  · rintro (short|cand)
    · exact Or.inl short
    · obtain ⟨q,good,all⟩ := criterion.mpr cand
      refine Or.inr ⟨q,good,?_⟩
      intro b
      by_cases done : IsRUP G (goalClause l b)
      · obtain ⟨c,hc,hf⟩ := done
        exact ⟨c,Or.inl hc,fun m hm => carry (fun _ h => Or.inl h) (fun _ h => .hyp h) (hf m hm)⟩
      · exact all ⟨b,done⟩
  · rintro (short|⟨q,good,all⟩)
    · exact Or.inl short
    · exact Or.inr (criterion.mp ⟨q,good,fun i => all i.val⟩)

abbrev V54 := Fin 5 × Fin 4
theorem ninePrefix :
    (∃ cs : List (Clause V54), IsRUPRun (PHP 5 4) cs ∧ (∅ : Clause V54) ∈ cs ∧ cs.length ≤ 12) ↔
    ∃ ps : List (Clause V54), IsRUPRun (PHP 5 4) ps ∧ ps.length ≤ 9 ∧
      ∃ l : Literal V54, ready (RUP9248.db (PHP 5 4) ps) l := by
  classical
  rw [RUP9248.exact54]
  constructor
  · rintro ⟨ps,rv,lim,l,pos,neg⟩
    have both (b : Bool) : IsRUP (RUP9248.db (PHP 5 4) ps) (goalClause l b) := by
      cases b <;> simp_all [goalClause]
    cases rv with
    | nil => exact ⟨[],.nil,by simp,l,Or.inl both⟩
    | @learn ts c run good =>
      have last : IsRUP (RUP9248.db (PHP 5 4) ts) c := good
      refine ⟨ts,run,by simp only [List.length_cons] at lim; omega,l,(ready_iff _ _).mpr (Or.inr ⟨c,last,?_⟩)⟩
      intro b
      rw [←RUP9248.dbCons]
      exact both b
  · rintro ⟨ts,run,lim,l,ok⟩
    rcases (ready_iff _ _).mp ok with both|⟨c,good,both⟩
    · exact ⟨ts,run,by omega,l,by simpa [goalClause] using both true,by simpa [goalClause] using both false⟩
    · refine ⟨c::ts,IsRUPRun.learn run good,by simp only [List.length_cons]; omega,l,?_,?_⟩
      · rw [RUP9248.dbCons]
        simpa [goalClause] using both true
      · rw [RUP9248.dbCons]
        simpa [goalClause] using both false
end PEqualNP.Outside.L_meta_9248.Shared

namespace PEqualNP.Outside.L_meta_9248.Shared
variable {I V : Type} [Fintype V] [DecidableEq V]
def firstDB (G : Set (Clause V)) (q : Clause V) : Option I → Set (Clause V)
  | none => G
  | some _ => G ∪ {q}
def firstA (A : I → Set (Literal V)) (q : Clause V) : Option I → Set (Literal V)
  | none => negLit '' (↑q : Set (Literal V))
  | some i => A i
abbrev firstOpen (G : Set (Clause V)) (A : I → Set (Literal V)) (q : Clause V) :=
  {i : Option I // ¬conflict (firstDB G q i) (firstA A q i)}
def firstCheck (G : Set (Clause V)) (A : I → Set (Literal V)) (q : Clause V) : Prop :=
  ∃ p : firstOpen G A q → Literal V,
    let H := fun i : firstOpen G A q => firstDB G q i.val
    let B := fun i : firstOpen G A q => firstA A q i.val
    IsRUP G (commonClause H B p) ∧ (∀ i,p i∈commonClause H B p) ∧
      (∀ i,conflict (H i) (B i ∪ {p i}))
theorem firstCheck_iff (G : Set (Clause V)) (A : I → Set (Literal V)) (q : Clause V) :
    firstCheck G A q ↔ ∃ c : Clause V, IsRUP G c ∧ IsRUP (G ∪ {c}) q ∧
        ∀ i,conflict ((G ∪ {c}) ∪ {q}) (A i) := by
  classical
  let H := fun i : firstOpen G A q => firstDB G q i.val
  let B := fun i : firstOpen G A q => firstA A q i.val
  have sub (i : firstOpen G A q) : G ⊆ H i := by
    intro x hx
    dsimp [H]
    cases i.val with
    | none => exact hx
    | some t => exact Or.inl hx
  have check := scheduled_helper G H sub B (fun i => i.property)
  have comm (c : Clause V) : (G ∪ {c}) ∪ {q} = (G ∪ {q}) ∪ {c} := by
    ext x
    simp [or_comm,or_left_comm,or_assoc]
  constructor
  · intro hit
    obtain ⟨c,learn,yes⟩ := check.mpr hit
    have all (i : Option I) : conflict (firstDB G q i ∪ {c}) (firstA A q i) := by
      by_cases ok : conflict (firstDB G q i) (firstA A q i)
      · obtain ⟨d,hd,rest⟩ := ok
        exact ⟨d,Or.inl hd,fun m hm => carry (fun _ h => Or.inl h) (fun _ h => .hyp h) (rest m hm)⟩
      · exact yes ⟨i,ok⟩
    refine ⟨c,learn,all none,?_⟩
    intro i
    rw [comm]
    exact all (some i)
  · rintro ⟨c,learn,qok,done⟩
    apply check.mp
    refine ⟨c,learn,?_⟩
    rintro ⟨i,_⟩
    cases i with
    | none => exact qok
    | some i =>
      rw [comm] at done
      exact done i

def twoCheck (G : Set (Clause V)) (A : I → Set (Literal V)) : Prop :=
  ∃ used : Set I, ∃ first : used → Option (Literal V), ∃ second : used → Literal V,
    firstCheck G A (maximal G (fun i => extendBoard (A i.val) (first i)) second)
theorem twoCheck_iff (G : Set (Clause V)) (A : I → Set (Literal V)) :
    twoCheck G A ↔ ∃ c q : Clause V, IsRUP G c ∧ IsRUP (G ∪ {c}) q ∧
      ∀ i, conflict ((G ∪ {c}) ∪ {q}) (A i) := by
  rw [two_canonical]
  constructor
  · rintro ⟨used,o,p,h⟩
    exact ⟨_,⟨used,o,p,rfl⟩,(firstCheck_iff _ _ _).mp h⟩
  · rintro ⟨q,⟨used,o,p,rfl⟩,h⟩
    exact ⟨used,o,p,(firstCheck_iff _ _ _).mpr h⟩
def aims (l : Literal V) (b : Bool) : Set (Literal V) :=
  negLit '' (↑(goalClause l b) : Set (Literal V))

theorem eightPrefix :
    (∃ cs : List (Clause V54), IsRUPRun (PHP 5 4) cs ∧ (∅ : Clause V54)∈cs ∧ cs.length≤12) ↔
    ∃ ts : List (Clause V54), IsRUPRun (PHP 5 4) ts ∧ ts.length≤8 ∧ ∃ l : Literal V54,
      ready (RUP9248.db (PHP 5 4) ts) l ∨ twoCheck (RUP9248.db (PHP 5 4) ts) (aims l) := by
  classical
  rw [RUP9248.exact54]
  constructor
  · rintro ⟨ps,run,len,l,pos,neg⟩
    have both (b : Bool) : IsRUP (RUP9248.db (PHP 5 4) ps) (goalClause l b) := by
      cases b <;> simp_all [goalClause]
    by_cases sh : ps.length≤8
    · exact ⟨ps,run,sh,l,Or.inl (Or.inl both)⟩
    cases run with
    | nil => simp at sh
    | @learn rs q mid qok =>
      cases mid with
      | nil => simp at sh
      | @learn ts c start cok =>
        refine ⟨ts,start,by simp only [List.length_cons] at len; omega,l,Or.inr ((twoCheck_iff _ _).mpr ?_)⟩
        refine ⟨c,q,cok,?_,?_⟩
        · rw [←RUP9248.dbCons]
          exact qok
        · intro b
          rw [←RUP9248.dbCons,←RUP9248.dbCons]
          exact both b
  · rintro ⟨ts,run,len,l,ok|ok⟩
    · rcases (ready_iff _ _).mp ok with both|⟨c,good,both⟩
      · exact ⟨ts,run,by omega,l,by simpa [goalClause] using both true,by simpa [goalClause] using both false⟩
      · refine ⟨c::ts,IsRUPRun.learn run good,by simp only [List.length_cons]; omega,l,?_,?_⟩
        · rw [RUP9248.dbCons]
          simpa [goalClause] using both true
        · rw [RUP9248.dbCons]
          simpa [goalClause] using both false
    · obtain ⟨c,q,good,learn,both⟩ := (twoCheck_iff _ _).mp ok
      have learn' : IsRUP (RUP9248.db (PHP 5 4) (c::ts)) q := by rwa [RUP9248.dbCons]
      refine ⟨q::c::ts,IsRUPRun.learn (IsRUPRun.learn run good) learn',by simp only [List.length_cons]; omega,l,?_,?_⟩
      · rw [RUP9248.dbCons,RUP9248.dbCons]
        simpa [aims,goalClause,conflict,IsRUP] using both true
      · rw [RUP9248.dbCons,RUP9248.dbCons]
        simpa [aims,goalClause,conflict,IsRUP] using both false
end PEqualNP.Outside.L_meta_9248.Shared
