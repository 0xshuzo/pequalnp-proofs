import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9471.Restriction
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]
abbrev C (V : Type) := Clause V
abbrev Val (V : Type) := V → Option Bool
def satisfied (s : Val V) (d : C V) := ∃ l ∈ d, s l.1 = some l.2
def residue (s : Val V) (d : C V) := d.filter fun l => s l.1 = none
def kept (s : Val V) (d : C V) : Option (C V) := restrictClause s d
theorem yes_keep {s : Val V} {d : C V} (h : ¬satisfied s d) :
    kept s d = some (residue s d) := by
  unfold satisfied at h
  simp [kept,restrictClause,residue,h]
theorem no_keep {s : Val V} {d : C V} (h : satisfied s d) : kept s d=none := by
  unfold satisfied at h
  simp [kept,restrictClause,h]
def faithful (s : Val V) (G H : Set (C V)) := ∀ d ∈ G, ¬satisfied s d → residue s d ∈ H
def consistent (s : Val V) (H : Set (C V)) (B : Set (Literal V)) (l : Literal V) :=
  (∀ b, s l.1=some b → l.2=b) ∧ (s l.1=none → UPForces H B l)

theorem transfer_forces {s : Val V} {G H : Set (C V)} {A B : Set (Literal V)}
    (pass : faithful s G H) (prem : ∀ l∈A, consistent s H B l)
    (noConflict : ¬ ∃ d ∈ H, ∀ l∈d, UPForces H B (negLit l))
    {l : Literal V} (der : UPForces G A l) : consistent s H B l := by
  induction der with
  | hyp h => exact prem _ h
  | @unit d l hd hl other ih =>
    by_cases alive : satisfied s d
    · obtain ⟨a,ha,holds⟩ := alive
      by_cases eq : a=l
      · subst a
        constructor
        · intro b e
          exact Option.some.inj (holds.symm.trans e)
        · intro e
          rw [holds] at e
          contradiction
      · have bad := (ih a ha eq).1 a.2 holds
        change (!a.2)=a.2 at bad
        cases a.2 <;> simp_all
    · have mem := pass d hd alive
      constructor
      · intro b eh
        by_contra diff
        apply noConflict
        refine ⟨residue s d,mem,?_⟩
        intro a ha
        obtain ⟨hm,unk⟩ := Finset.mem_filter.mp ha
        have ne : a≠l := by intro e; subst a; rw [eh] at unk; contradiction
        exact (ih a hm ne).2 unk
      · intro un
        apply UPForces.unit mem (Finset.mem_filter.mpr ⟨hl,un⟩)
        intro a ha ne
        obtain ⟨hm,unk⟩ := Finset.mem_filter.mp ha
        exact (ih a hm ne).2 unk

theorem transfer_clause {s : Val V} {G H : Set (C V)} {c : C V}
    (pass : faithful s G H) (openC : ¬satisfied s c) (r : IsRUP G c) :
    IsRUP H (residue s c) := by
  classical
  by_contra no
  let A := negLit '' (↑c : Set (Literal V))
  let B := negLit '' (↑(residue s c) : Set (Literal V))
  have pr : ∀ l∈A, consistent s H B l := by
    rintro _ ⟨a,ha,rfl⟩
    constructor
    · intro b e
      change (!a.2)=b
      have neq : a.2≠b := by intro q; exact openC ⟨a,ha,q.symm ▸ e⟩
      exact (by decide : ∀ x y : Bool, x≠y → (!x)=y) a.2 b neq
    · intro un
      apply UPForces.hyp
      exact ⟨a,Finset.mem_filter.mpr ⟨ha,un⟩,rfl⟩
  obtain ⟨d,hd,die⟩ := r
  have force (a) (ha : a∈d) := transfer_forces pass pr no (die a ha)
  by_cases sat : satisfied s d
  · obtain ⟨a,ha,yes⟩ := sat
    have bad := (force a ha).1 a.2 yes
    change (!a.2)=a.2 at bad
    cases a.2 <;> simp_all
  · apply no
    refine ⟨residue s d,pass d hd sat,?_⟩
    intro a ha
    obtain ⟨hm,un⟩ := Finset.mem_filter.mp ha
    exact (force a hm).2 un

theorem transfer_run {s : Val V} {G H : Set (C V)} (pass : faithful s G H)
    {rs : List (C V)} (run : IsRUPRun G rs) : IsRUPRun H (rs.filterMap (kept s)) := by
  classical
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn rs c earlier curr ih =>
    by_cases sat : satisfied s c
    · simpa [List.filterMap_cons,no_keep sat] using ih
    · rw [List.filterMap_cons,yes_keep sat]
      apply IsRUPRun.learn ih
      apply transfer_clause _ sat curr
      intro d hd free
      rcases hd with raw|old
      · exact Or.inl (pass d raw free)
      · apply Or.inr
        exact List.mem_filterMap.mpr ⟨d,old,yes_keep free⟩

theorem transfer_empty (s : Val V) {rs : List (C V)} (m : (∅ : C V) ∈ rs) :
    (∅ : C V) ∈ rs.filterMap (kept s) := by
  apply List.mem_filterMap.mpr
  exact ⟨∅,m,by simp [kept,restrictClause]⟩

theorem kept_info {s : Val V} {c a : C V} (h : kept s c = some a) :
    ¬satisfied s c ∧ residue s c = a := by
  classical
  by_cases yes : satisfied s c
  · rw [no_keep yes] at h
    contradiction
  · exact ⟨yes,Option.some.inj ((yes_keep yes).symm.trans h)⟩

theorem double_keep {s t : Val V} {c a b : C V} (ha : kept s c = some a)
    (hb : kept t c = some b) : ∃ d, kept t a = some d ∧ kept s b = some d := by
  classical
  obtain ⟨sa,ra⟩ := kept_info ha
  obtain ⟨sb,rb⟩ := kept_info hb
  subst a
  subst b
  have left : ¬satisfied t (residue s c) := by
    rintro ⟨l,hl,yes⟩
    exact sb ⟨l,(Finset.mem_filter.mp hl).1,yes⟩
  have right : ¬satisfied s (residue t c) := by
    rintro ⟨l,hl,yes⟩
    exact sa ⟨l,(Finset.mem_filter.mp hl).1,yes⟩
  refine ⟨_,yes_keep left,?_⟩
  rw [yes_keep right]
  congr 1
  ext l
  simp [residue,and_assoc,and_left_comm,and_comm]

abbrev twice (s t : Val V) (rs : List (C V)) := (rs.filterMap (kept s)).filterMap (kept t)

theorem optional_cons {α : Type} {w b : List α} (h : w.Sublist b) (o : Option α) :
    w.Sublist (match o with | none => b | some a => a :: b) := by
  cases o with
  | none => exact h
  | some a => exact .cons a h

theorem synchronization (s t : Val V) (rs : List (C V)) :
    ∃ w : List (C V), w.Sublist (twice s t rs) ∧ w.Sublist (twice t s rs) ∧
      (rs.filterMap (kept s)).length + (rs.filterMap (kept t)).length ≤ rs.length + w.length := by
  induction rs with
  | nil => exact ⟨[],List.Sublist.slnil,List.Sublist.slnil,by simp⟩
  | cons c cs ih =>
    obtain ⟨w,ha,hb,sz⟩ := ih
    cases ea : kept s c with
    | none =>
      cases eb : kept t c with
      | none =>
        refine ⟨w,?_,?_,?_⟩
        · simpa [twice,List.filterMap_cons,ea] using ha
        · simpa [twice,List.filterMap_cons,eb] using hb
        · simp [List.filterMap_cons,ea,eb]; omega
      | some b =>
        refine ⟨w,?_,?_,?_⟩
        · simpa [twice,List.filterMap_cons,ea] using ha
        · cases q : kept s b with
          | none => simpa [twice,List.filterMap_cons,eb,q] using hb
          | some y => simpa [twice,List.filterMap_cons,eb,q] using List.Sublist.cons y hb
        · simp [List.filterMap_cons,ea,eb]; omega
    | some a =>
      cases eb : kept t c with
      | none =>
        refine ⟨w,?_,?_,?_⟩
        · cases q : kept t a with
          | none => simpa [twice,List.filterMap_cons,ea,q] using ha
          | some y => simpa [twice,List.filterMap_cons,ea,q] using List.Sublist.cons y ha
        · simpa [twice,List.filterMap_cons,eb] using hb
        · simp [List.filterMap_cons,ea,eb]; omega
      | some b =>
        obtain ⟨d,da,db⟩ := double_keep ea eb
        refine ⟨d::w,?_,?_,?_⟩
        · simpa [twice,List.filterMap_cons,ea,da] using List.Sublist.cons₂ d ha
        · simpa [twice,List.filterMap_cons,eb,db] using List.Sublist.cons₂ d hb
        · simp [List.filterMap_cons,ea,eb]; omega

theorem twenty_shared {s t : Val V} {rs : List (C V)} (cap : rs.length ≤ 20)
    (a : 14 ≤ (rs.filterMap (kept s)).length) (b : 14 ≤ (rs.filterMap (kept t)).length) :
    ∃ w : List (C V), w.Sublist (twice s t rs) ∧ w.Sublist (twice t s rs) ∧ 8 ≤ w.length := by
  obtain ⟨w,wa,wb,l⟩ := synchronization s t rs
  exact ⟨w,wa,wb,by omega⟩

inductive Chosen (s : Val V) : List (C V) → List (C V) → Prop
  | nil : Chosen s [] []
  | skip {cs ds} (c : C V) : Chosen s cs ds → Chosen s (c :: cs) ds
  | take {cs ds c d} : kept s c = some d → Chosen s cs ds → Chosen s (c :: cs) (d :: ds)

theorem selection {s : Val V} {cs ds : List (C V)} (choice : Chosen s cs ds) :
    ds.Sublist (cs.filterMap (kept s)) := by
  induction choice with
  | nil => exact .slnil
  | skip c _ ih =>
    cases q : kept s c with
    | none => simpa [List.filterMap_cons,q] using ih
    | some z => simpa [List.filterMap_cons,q] using List.Sublist.cons z ih
  | take h _ ih =>
    simpa [List.filterMap_cons,h] using List.Sublist.cons₂ _ ih

theorem chosen_order (s t : Val V) {rs as bs : List (C V)}
    (left : Chosen s rs as) (right : Chosen t rs bs) :
    ∃ w : List (C V), w.Sublist (as.filterMap (kept t)) ∧ w.Sublist (bs.filterMap (kept s)) ∧
      as.length + bs.length ≤ rs.length + w.length := by
  induction left generalizing bs with
  | nil =>
    cases right
    exact ⟨[],List.Sublist.slnil,List.Sublist.slnil,by simp⟩
  | @skip cs ds c rest ih =>
    cases right with
    | skip _ r =>
      obtain ⟨w,x,y,sz⟩ := ih r
      exact ⟨w,x,y,by simp only [List.length_cons] <;> omega⟩
    | @take _ more _ b eb r =>
      obtain ⟨w,x,y,sz⟩ := ih r
      refine ⟨w,x,?_,by simp only [List.length_cons] <;> omega⟩
      cases q : kept s b with
      | none => simpa [List.filterMap_cons,q] using y
      | some z => simpa [List.filterMap_cons,q] using List.Sublist.cons z y
  | @take cs ds c a ea rest ih =>
    cases right with
    | skip _ r =>
      obtain ⟨w,x,y,sz⟩ := ih r
      refine ⟨w,?_,y,by simp only [List.length_cons] <;> omega⟩
      cases q : kept t a with
      | none => simpa [List.filterMap_cons,q] using x
      | some z => simpa [List.filterMap_cons,q] using List.Sublist.cons z x
    | @take _ more _ b eb r =>
      obtain ⟨w,x,y,sz⟩ := ih r
      obtain ⟨d,p,q⟩ := double_keep ea eb
      refine ⟨d::w,?_,?_,by simp only [List.length_cons] <;> omega⟩
      · simpa [List.filterMap_cons,p] using List.Sublist.cons₂ d x
      · simpa [List.filterMap_cons,q] using List.Sublist.cons₂ d y

theorem chosen_twenty {rs as bs : List (C V)} {s t : Val V} (a : Chosen s rs as) (b : Chosen t rs bs)
    (cap : rs.length ≤ 20) (al : as.length = 14) (bl : bs.length = 14) :
    ∃ w : List (C V), w.Sublist (as.filterMap (kept t)) ∧ w.Sublist (bs.filterMap (kept s)) ∧ 8 ≤ w.length := by
  obtain ⟨w,x,y,sz⟩ := chosen_order s t a b
  exact ⟨w,x,y,by omega⟩

end PEqualNP.Outside.L_meta_9471.Restriction
