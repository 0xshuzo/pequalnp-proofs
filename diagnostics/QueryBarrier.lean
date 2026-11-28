import PEqualNP.Defs
open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Chart
namespace Generic
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


end Generic
namespace Restrict
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


variable {W : Type} [DecidableEq W]
def pushLit (f : V → W) (l : Literal V) : Literal W := (f l.1,l.2)
def push (f : V → W) (c : C V) := c.image (pushLit f)
theorem push_forces {G : Set (C V)} {H : Set (C W)} {A B} (f : V → W)
    (pass : ∀c∈G, push f c∈H) (hyp : ∀ l∈A, pushLit f l∈B) {l}
    (h : UPForces G A l) : UPForces H B (pushLit f l) := by
  induction h with
  | hyp h => exact UPForces.hyp (hyp _ h)
  | @unit d l hd hl oth ih =>
    apply UPForces.unit (pass d hd) (Finset.mem_image_of_mem (pushLit f) hl)
    rintro _ hm ne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
    exact ih a ha (fun eq => ne (congrArg (pushLit f) eq))
theorem push_clause {G : Set (C V)} {H : Set (C W)} (f : V → W)
    (pass : ∀c∈G, push f c∈H) {c} (h : IsRUP G c) : IsRUP H (push f c) := by
  obtain ⟨d,hd,die⟩ := h
  refine ⟨push f d,pass d hd,?_⟩
  intro a ha
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
  apply push_forces f pass _ (die l hl)
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨pushLit f v,Finset.mem_image_of_mem (pushLit f) hv,rfl⟩
theorem push_run {G : Set (C V)} {H : Set (C W)} (f : V → W)
    (pass : ∀c∈G, push f c∈H) {rs} (run : IsRUPRun G rs) :
    IsRUPRun H (rs.map (push f)) := by
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn rs c good step ih =>
    apply IsRUPRun.learn ih (push_clause f _ step)
    intro d hd
    rcases hd with a|b
    · exact Or.inl (pass d a)
    · exact Or.inr (List.mem_map.mpr ⟨d,b,rfl⟩)

def Lower (F : Set (C V)) (n : Nat) : Prop :=
  ∀ rs : List (C V), IsRUPRun F rs → (∅ : C V) ∈ rs → n ≤ rs.length

def faithfulMap (F : Set (C V)) (H : Set (C W)) (s : Val V) (f : V → W) : Prop :=
  ∀ d ∈ F, ¬satisfied s d → push f (residue s d) ∈ H

theorem mapped_run {F : Set (C V)} {H : Set (C W)}
    (s : Val V) (f : V → W) (h : faithfulMap F H s f)
    {rs : List (C V)} (run : IsRUPRun F rs) :
    IsRUPRun H ((rs.filterMap (kept s)).map (push f)) := by
  let F' : Set (C V) := {e | ∃ d∈F, ¬satisfied s d ∧ residue s d=e}
  have raw : faithful s F F' := fun d hd free => ⟨d,hd,free,rfl⟩
  apply push_run f _ (transfer_run raw run)
  rintro _ ⟨d,hd,free,rfl⟩
  exact h d hd free

theorem one_more {F : Set (C V)} {n : Nat}
    (consistent : ¬ Generic.conflict F ∅)
    (answers : ∀ v : V, ∃ (s : Val V) (f : V → W) (H : Set (C W)),
      s v≠none ∧ faithfulMap F H s f ∧ Lower H n) : Lower F (n+1) := by
  intro rs run empty
  obtain ⟨ps,rp,len,l,plus,minus⟩ := Generic.pairPrefix consistent run empty
  obtain ⟨s,f,H,set,pass,floor⟩ := answers l.1
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp set
  have existsBad : ∃ k : Literal V, s k.1=some (!k.2) ∧ IsRUP (Generic.db F ps) {k} := by
    by_cases e : v=l.2
    · refine ⟨negLit l,?_,minus⟩
      simpa [negLit,e] using hv
    · refine ⟨l,?_,plus⟩
      have ne : v = !l.2 := by cases v <;> cases h : l.2 <;> simp_all
      simpa [ne] using hv
  obtain ⟨k,hk,learn⟩ := existsBad
  have newRun : IsRUPRun F ({k} :: ps) := .learn rp learn
  have fixed : kept s ({k} : C V) = some ∅ := by
    rcases k with ⟨x,b⟩
    cases b <;> simp_all [kept,restrictClause]
  have smaller := mapped_run s f pass newRun
  rw [List.filterMap_cons,fixed] at smaller
  have smallRun : IsRUPRun H (∅ :: (ps.filterMap (kept s)).map (push f)) := by
    simpa [push] using smaller
  have numeric := floor _ smallRun List.mem_cons_self
  have bound := List.length_filterMap_le (f:=kept s) (l:=ps)
  simp only [List.length_cons,List.length_map] at numeric
  omega


def Upper (G : Set (C V)) (n : Nat) : Prop :=
  ∃ cs : List (C V), IsRUPRun G cs ∧ (∅ : C V)∈cs ∧ cs.length≤n

theorem upper_map {G : Set (C V)} {H : Set (C W)} (s : Val V) (f : V→W)
    (good : faithfulMap G H s f) {n} (bound : Upper G n) : Upper H n := by
  obtain ⟨cs,run,out,sz⟩ := bound
  refine ⟨_,mapped_run s f good run,?_,?_⟩
  · exact List.mem_map.mpr ⟨∅,transfer_empty s out,by simp [push]⟩
  · simpa only [List.length_map] using (List.length_filterMap_le (f:=kept s) (l:=cs)).trans sz

def terminals (G : Set (C V)) (pins : List V) (b : V→Bool) : Set (C V) :=
  G ∪ {d | ∃ x∈pins, d={(x,b x)}}

def deep : Nat → Set (C V) → Nat → Prop
  | 0,G,k => Lower G k
  | t+1,G,k => ∀ v : V, ∃ (s : Val V) (f : V→V) (H : Set (C V)),
      s v≠none ∧ faithfulMap G H s f ∧ deep t H k

theorem pass_pins {G H : Set (C V)} {s : Val V} {f : V→V} {v : V}
    (hard : s v≠none) (pass : faithfulMap G H s f) (tail : List V) (b : V→Bool) :
    faithfulMap (terminals G (v::tail) (fun x => (s x).getD (b (f x))))
      (terminals H (tail.map f) b) s f := by
  rintro d (base|⟨x,hx,rfl⟩) alive
  · exact Or.inl (pass _ base alive)
  · cases h : s x with
    | none =>
      have inTail : x∈tail := by
        rcases List.mem_cons.mp hx with eq|later
        · exact (hard (by simpa only [eq] using h)).elim
        · exact later
      refine Or.inr ⟨f x,List.mem_map.mpr ⟨x,inTail,rfl⟩,?_⟩
      simp [residue,push,pushLit,h]
    | some value =>
      exact (alive ⟨(x,value),by simp [h],h⟩).elim

theorem query_barrier (pins : List V) (G : Set (C V)) (k : Nat)
    (small : ∀ b : V→Bool, Upper (terminals G pins b) k) : ¬deep pins.length G (k+1) := by
  have aux : ∀ t : Nat, ∀ (ps : List V) (F : Set (C V)), ps.length=t →
      (∀ b : V→Bool, Upper (terminals F ps b) k) → ¬deep t F (k+1) := by
    intro t
    induction t with
    | zero =>
      intro ps F hp bounds game
      have e : ps=[] := by cases ps <;> simp_all
      subst ps
      have same : terminals F [] (fun _ => false)=F := by
        ext c
        simp [terminals]
      have ub := bounds (fun _=>false)
      rw [same] at ub
      obtain ⟨cs,run,out,sz⟩ := ub
      have lim := game cs run out
      omega
    | succ t inductionHyp =>
      intro ps F hp bounds game
      cases ps with
      | nil => simp at hp
      | cons v rest =>
        obtain ⟨s,f,H,fixed,pass,child⟩ := game v
        have residual (b : V→Bool) : Upper (terminals H (rest.map f) b) k :=
          upper_map s f (pass_pins fixed pass rest b) (bounds _)
        have len : (rest.map f).length=t := by simpa using hp
        exact inductionHyp (rest.map f) H len residual child
  exact aux pins.length pins G rfl small
end Restrict
end PEqualNP.Outside.L_meta_9248.Chart
