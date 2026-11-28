import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9248.Leaf
open PEqualNP.ProofComplexity PEqualNP.Search
abbrev V := Fin 12
abbrev L := Literal V
abbrev C := Clause V
abbrev Val := V → Option Bool
def clauseOf (p n : Nat) : C := Finset.univ.filter (fun l : L => (if l.2 then p else n).testBit l.1.val)
abbrev RawId := Fin 22
def terms : Array C := #[clauseOf 7 0, clauseOf 56 0, clauseOf 448 0, clauseOf 1536 0, clauseOf 0 9, clauseOf 0 18, clauseOf 0 36, clauseOf 0 65, clauseOf 0 72, clauseOf 0 130, clauseOf 0 144, clauseOf 0 260, clauseOf 0 288, clauseOf 0 513, clauseOf 0 520, clauseOf 0 576, clauseOf 0 1026, clauseOf 0 1040, clauseOf 0 1152, clauseOf 0 2052, clauseOf 0 2080, clauseOf 0 2304]
def term (i : RawId) := terms[i.val]!
def axs : Finset C := Finset.univ.image term
def Raw : Set C := ↑axs
end PEqualNP.Outside.L_meta_9248.Leaf
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


abbrev X := Fin 5 × Fin 4
abbrev Ix := Fin 17
def states : Array (Nat × Nat) := #[(3171,2),(101542,2),(103655,3),(105703,4),(236775,5),(3249484,2),(3256719,3),(3317069,3),(3324399,4),(3387823,4),(3390959,5),(3586543,5),(3653103,6),(7585263,6),(7716335,6),(7847407,7),(16236015,8)]
def e0 : Array (Nat × Nat × Nat × Nat) := #[(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672)]
def e1 : Array (Nat × Nat × Nat × Nat) := #[(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672)]
def e2 : Array (Nat × Nat × Nat × Nat) := #[(1,0,16915,1602),(0,65536,14465,1112),(0,4096,13569,1224),(2,0,18056,1672),(1,0,16922,1602),(0,65536,14472,1112),(0,4096,13576,1224),(2,0,18056,1672),(0,4096,13576,1224),(2,0,18056,1672),(0,4096,13576,1224),(2,0,18056,1672),(0,65536,14472,1112),(0,65536,14472,1112),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672)]
def e3 : Array (Nat × Nat × Nat × Nat) := #[(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672)]
def e4 : Array (Nat × Nat × Nat × Nat) := #[(3,0,17475,1602),(3,0,17475,1616),(3,0,17475,1672),(4,0,18056,1672),(3,0,17496,1602),(3,0,17496,1616),(3,0,17496,1672),(4,0,18056,1672),(3,0,17608,1602),(3,0,17608,1616),(3,0,17608,1672),(4,0,18056,1672),(3,0,18056,1602),(3,0,18056,1616),(3,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672)]
def e5 : Array (Nat × Nat × Nat × Nat) := #[(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672)]
def e6 : Array (Nat × Nat × Nat × Nat) := #[(0,2129920,14472,531),(0,1114112,14472,531),(0,8320,8928,1224),(0,4352,8928,1224),(6,0,18056,1672),(6,0,18056,1672),(0,4352,8928,1224),(0,8320,8928,1224),(6,0,18056,1672),(6,0,18056,1672),(0,8320,8928,1224),(0,4352,8928,1224),(0,1114112,14472,531),(0,2129920,14472,531),(6,0,18056,1672),(6,0,18056,1672),(0,2129920,14472,531),(0,1114112,14472,531),(6,0,18056,1672),(6,0,18056,1672)]
def e7 : Array (Nat × Nat × Nat × Nat) := #[(5,0,10433,1616),(7,0,18056,1672),(1,131072,14465,1224),(0,2097408,13345,1112),(7,0,18056,1672),(0,2097408,13345,1112),(7,0,18056,1672),(0,2097408,13345,1112),(1,256,5666,1616),(0,2097408,13408,1112),(1,131072,14465,1224),(7,0,18056,1672),(1,131072,14465,1224),(7,0,18056,1672),(1,131072,14465,1224),(7,0,18056,1672),(0,2097408,13408,1112),(0,2097408,13408,1112),(7,0,18056,1672),(7,0,18056,1672)]
def e8 : Array (Nat × Nat × Nat × Nat) := #[(7,0,6163,1049),(2,2097152,18049,1049),(2,131072,14465,1217),(2,8192,13569,1672),(7,0,6170,1049),(2,2097152,18056,1049),(2,131072,14472,1217),(2,8192,13576,1672),(8,0,18056,1672),(2,8192,9992,1616),(2,8192,13576,1672),(2,8192,13576,1672),(2,131072,14472,1217),(8,0,18056,1672),(2,131072,14472,1217),(8,0,18056,1672),(2,2097152,18056,1049),(2,2097152,18056,1049),(8,0,18056,1672),(8,0,18056,1672)]
def e9 : Array (Nat × Nat × Nat × Nat) := #[(7,0,6338,1035),(2,2097152,17608,538),(7,0,12386,720),(2,8192,13072,1672),(6,0,8984,538),(9,0,18056,1672),(7,0,12386,720),(2,8192,8984,1616),(9,0,18056,1672),(9,0,18056,1672),(2,8192,13072,1672),(2,8192,13072,1672),(7,0,6338,1035),(2,2097152,18056,1049),(6,0,18056,1672),(9,0,18056,1672),(2,2097152,18056,1049),(2,2097152,18056,1049),(9,0,18056,1672),(9,0,18056,1672)]
def e10 : Array (Nat × Nat × Nat × Nat) := #[(3,8,13380,1665),(3,8,13380,1672),(3,8,13380,1672),(3,256,13345,1672),(3,256,13408,1665),(3,256,13408,1672),(3,256,13408,1672),(3,8,13324,1672),(3,8192,13576,1665),(3,8192,13576,1672),(3,8192,13576,1672),(3,8,13380,1672),(3,131072,14472,1217),(3,131072,14472,1224),(3,131072,14472,1224),(10,0,18056,1672),(3,2097152,18056,1112),(3,1048576,18056,1091),(10,0,18056,1672),(10,0,18056,1672)]
def e11 : Array (Nat × Nat × Nat × Nat) := #[(3,1048576,18049,531),(3,2097152,17601,538),(9,0,17027,1224),(9,0,17027,1672),(3,1048576,18056,531),(3,2097152,17608,538),(9,0,17048,1224),(9,0,17048,1672),(11,0,18056,1672),(3,2097152,17608,538),(8,0,17608,1217),(8,0,17608,1665),(3,1048576,18056,531),(11,0,18056,1672),(8,0,18056,1224),(8,0,18056,1672),(3,2097152,17608,538),(3,1048576,18056,531),(11,0,18056,1672),(11,0,18056,1672)]
def e12 : Array (Nat × Nat × Nat × Nat) := #[(4,1048576,17475,1091),(4,2097152,17475,1112),(10,0,17475,1224),(10,0,17475,1672),(4,1048576,17496,1091),(4,2097152,17496,1112),(10,0,17496,1224),(10,0,17496,1672),(4,1048576,17608,1091),(4,2097152,17608,1112),(10,0,17608,1224),(10,0,17608,1672),(4,1048576,18056,1091),(4,2097152,18056,1112),(10,0,18056,1224),(10,0,18056,1672),(4,2097152,18056,1112),(4,1048576,18056,1091),(12,0,18056,1672),(12,0,18056,1672)]
def e13 : Array (Nat × Nat × Nat × Nat) := #[(4,8,13380,1602),(4,8,13380,1616),(4,8,13380,1672),(4,256,13345,1672),(4,256,13408,1602),(4,256,13408,1616),(4,256,13408,1672),(4,8,13324,1672),(4,8192,13576,1602),(4,8192,13576,1616),(4,8192,13576,1672),(4,8,13380,1672),(10,0,14472,1602),(10,0,14472,1616),(10,0,14472,1672),(13,0,18056,1672),(10,0,18056,1602),(10,0,18056,1616),(10,0,18056,1672),(13,0,18056,1672)]
def e14 : Array (Nat × Nat × Nat × Nat) := #[(11,0,13380,531),(11,0,13380,538),(4,4194304,17986,1224),(4,262144,14402,1672),(11,0,13408,531),(11,0,13408,538),(4,4194304,18000,1224),(4,262144,14416,1672),(11,0,13576,531),(11,0,13576,538),(4,4194304,18056,1224),(4,262144,14472,1672),(4,262144,14472,1665),(4,262144,14472,1672),(14,0,18056,1672),(4,262144,14472,1672),(4,4194304,18056,1217),(4,4194304,18056,1224),(4,4194304,18056,1224),(14,0,18056,1672)]
def e15 : Array (Nat × Nat × Nat × Nat) := #[(14,0,17475,1602),(14,0,17475,1616),(14,0,17475,1672),(13,0,17475,1672),(14,0,17496,1602),(14,0,17496,1616),(14,0,17496,1672),(13,0,17496,1672),(14,0,17608,1602),(14,0,17608,1616),(14,0,17608,1672),(13,0,17608,1672),(14,0,18056,1602),(14,0,18056,1616),(14,0,18056,1672),(13,0,18056,1672),(12,0,18056,1602),(12,0,18056,1616),(12,0,18056,1672),(15,0,18056,1672)]
def e16 : Array (Nat × Nat × Nat × Nat) := #[(15,0,13380,1091),(15,0,13380,1112),(15,0,13380,1224),(15,0,13380,1672),(15,0,13408,1091),(15,0,13408,1112),(15,0,13408,1224),(15,0,13408,1672),(15,0,13576,1091),(15,0,13576,1112),(15,0,13576,1224),(15,0,13576,1672),(15,0,14472,1091),(15,0,14472,1112),(15,0,14472,1224),(15,0,14472,1672),(15,0,18056,1091),(15,0,18056,1112),(15,0,18056,1224),(15,0,18056,1672)]
def edges := #[e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16]
def root : Ix := 16
def leaf : Ix := 3

def graph (i : Ix) := (states[i.val]!).1
def depth (i : Ix) := (states[i.val]!).2
def cell (x : X) := 5*x.1.val+x.2.val
def on (g : Nat) (v : X) : Bool := g.testBit (cell v)
def active (g : Nat) (r : Fin 5) : Bool := ((g / 2^(5*r.val))%32) != 0
def row (g : Nat) (r : Fin 5) : Clause X :=
  (Finset.univ.filter (fun h : Fin 4 => on g (r,h))).image (fun h : Fin 4 => ((r,h),true))
def col (a b : Fin 5) (j : Fin 4) : Clause X := {((a,j),false),((b,j),false)}
def Raw (g : Nat) : Set (Clause X) := {d |
 (∃ r : Fin 5, active g r ∧ d=row g r) ∨
 (∃ (a b : Fin 5) (j : Fin 4), a≠b ∧ on g (a,j) ∧ on g (b,j) ∧ d=col a b j)}
def entry (i : Ix) (v : X) := (edges[i.val]!)[4*v.1.val+v.2.val]!
def dest (i : Ix) (v : X) : Ix :=
 ⟨(entry i v).1 % _,Nat.mod_lt _ (by decide)⟩
def readIndex {n : Nat} [NeZero n] (s : Nat) (x : Fin n) : Fin n :=
 ⟨((s / 2^(3*x.val))%8)%n,Nat.mod_lt _ (NeZero.pos n)⟩
def rf (i : Ix) (v : X) : Fin 5 → Fin 5 := readIndex (entry i v).2.2.1
def cf (i : Ix) (v : X) : Fin 4 → Fin 4 := readIndex (entry i v).2.2.2
def rename (i : Ix) (v y : X) : X := (rf i v y.1,cf i v y.2)
def assign (i : Ix) (v y : X) : Option Bool :=
 if on (entry i v).2.1 y then some true
 else if on (graph (dest i v)) (rename i v y) then none else some false
def sat (s : Val X) (c : Clause X) : Bool := decide (∃ (r : Fin 5) (h : Fin 4) (b : Bool), ((r,h),b)∈c ∧ s (r,h)=some b)
theorem sat_iff (s : Val X) (c : Clause X) : sat s c = true ↔ satisfied s c := by
 simp only [sat,decide_eq_true_eq]
 constructor
 · rintro ⟨r,h,b,m,e⟩
   exact ⟨((r,h),b),m,e⟩
 · rintro ⟨⟨⟨r,h⟩,b⟩,m,e⟩
   exact ⟨r,h,b,m,e⟩
def guardedRow (i : Ix) (v : X) (r : Fin 5) : Prop :=
 let g:=graph i; let h:=graph (dest i v); let s:=assign i v; let d:=row g r
 active g r = true → sat s d = true ∨
   (active h (rf i v r)=true ∧ push (rename i v) (residue s d)=row h (rf i v r))
def guardedPair (i : Ix) (v : X) (a b : Fin 5) (j : Fin 4) : Prop :=
 let g:=graph i; let h:=graph (dest i v); let s:=assign i v; let d:=col a b j
 a≠b → on g (a,j)=true → on g (b,j)=true → sat s d=true ∨
  (rf i v a≠rf i v b ∧ on h (rf i v a, cf i v j)=true ∧ on h (rf i v b,cf i v j)=true ∧
   push (rename i v) (residue s d)=col (rf i v a) (rf i v b) (cf i v j))
def Check (i : Ix) (v : X) : Prop :=
 depth i≤2 ∨ i=leaf ∨
 (assign i v v≠none ∧ depth i≤depth (dest i v)+1 ∧
  (∀ r, guardedRow i v r) ∧ (∀ a b j, guardedPair i v a b j))
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance (i : Ix) (v : X) (r : Fin 5) : Decidable (guardedRow i v r) := by unfold guardedRow; infer_instance
local instance (i : Ix) (v : X) (a b : Fin 5) (j : Fin 4) : Decidable (guardedPair i v a b j) := by unfold guardedPair; infer_instance
local instance (i : Ix) (v : X) : Decidable (Check i v) := by unfold Check; infer_instance

abbrev Small := PEqualNP.Outside.L_meta_9248.Leaf.V
abbrev smallRaw := PEqualNP.Outside.L_meta_9248.Leaf.Raw
def toSmall (v : X) : Small := ⟨(3*v.1.val+v.2.val)%12,Nat.mod_lt _ (by decide)⟩
def leafFix (v : X) : Option Bool := if on (graph leaf) v then none else some false
theorem smallRows : ∀ r : Fin 5, active (graph leaf) r=true →
  push toSmall (residue leafFix (row (graph leaf) r)) ∈ PEqualNP.Outside.L_meta_9248.Leaf.axs := by decide +kernel
theorem smallCols : ∀ (a b : Fin 5) (j : Fin 4), a≠b → on (graph leaf) (a,j)=true →
  on (graph leaf) (b,j)=true → push toSmall (residue leafFix (col a b j)) ∈ PEqualNP.Outside.L_meta_9248.Leaf.axs := by decide +kernel
theorem leafMap : faithfulMap (Raw (graph leaf)) smallRaw leafFix toSmall := by
  rintro d (⟨r,act,rfl⟩|⟨a,b,j,ne,oa,ob,rfl⟩) alive
  · exact smallRows r act
  · exact smallCols a b j ne oa ob
theorem leaf_transfer (small : Lower smallRaw 4) : Lower (Raw (graph leaf)) 4 := by
  intro cs run empty
  have legal := mapped_run leafFix toSmall leafMap run
  have mem := transfer_empty leafFix empty
  have translated : (∅ : Clause Small) ∈ (cs.filterMap (kept leafFix)).map (push toSmall) :=
    List.mem_map.mpr ⟨∅,mem,by simp [push]⟩
  have bound := small _ legal translated
  simp only [List.length_map] at bound
  exact bound.trans (List.length_filterMap_le (f:=kept leafFix) (l:=cs))
end Restrict
end PEqualNP.Outside.L_meta_9248.Chart
