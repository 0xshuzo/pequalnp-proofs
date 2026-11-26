import PEqualNP.Defs

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

namespace PEqualNP.Outside.L_meta_9246.FixedCell
open RUP9248
variable {V : Type} [DecidableEq V]
def lit (f : V → V) (l : Literal V) : Literal V := (f l.1,l.2)
def image (f : V → V) (c : Clause V) := c.image (lit f)
theorem flip (f : V → V) (l : Literal V) : lit f (negLit l)=negLit (lit f l) := rfl
theorem mapForce (f : V → V) {G H : Set (Clause V)} {A B : Set (Literal V)}
    (inc : ∀ d∈G, image f d∈H) (hyp : ∀ l∈A, UPForces H B (lit f l))
    {l} (h : UPForces G A l) : UPForces H B (lit f l) := by
  induction h with
  | hyp h => exact hyp _ h
  | @unit d k hd hk other ih =>
    refine .unit (inc d hd) (Finset.mem_image_of_mem _ hk) ?_
    intro t ht ne
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    exact ih j hj (fun eq => ne (congrArg (lit f) eq))
theorem mapRup (f : V → V) {G H : Set (Clause V)} (inc : ∀ d∈G,image f d∈H)
    {c} (ok : IsRUP G c) : IsRUP H (image f c) := by
  obtain ⟨d,hd,dead⟩ := ok
  refine ⟨image f d,inc d hd,?_⟩
  intro t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  apply mapForce f inc _ (dead j hj)
  rintro _ ⟨k,hk,rfl⟩
  exact .hyp ⟨lit f k,Finset.mem_image_of_mem _ hk,rfl⟩
theorem mapDB (f : V → V) {F H : Set (Clause V)} (inc : ∀d∈F,image f d∈H)
    (cs : List (Clause V)) : ∀ d∈db F cs, image f d∈db H (cs.map (image f)) := by
  rintro d (h|h)
  · exact Or.inl (inc d h)
  · exact Or.inr (List.mem_map_of_mem h)
theorem mapRun (f : V → V) {F H : Set (Clause V)} (inc : ∀d∈F,image f d∈H)
    {cs : List (Clause V)} (ok : IsRUPRun F cs) : IsRUPRun H (cs.map (image f)) := by
  induction ok with
  | nil => exact .nil
  | @learn cs c step rule ih => exact .learn ih (mapRup f (mapDB f inc cs) rule)

def exchange {n : Nat} (a b i : Fin n) : Fin n := if i=a then b else if i=b then a else i
def place (a : V54) (v : V54) : V54 := (exchange a.1 0 v.1,exchange a.2 3 v.2)
def row (p : Fin 5) : Clause V54 := Finset.univ.image (fun h : Fin 4 => (((p,h),true) : Literal V54))
def collision (p q : Fin 5) (h : Fin 4) : Clause V54 := {((p,h),false),((q,h),false)}
theorem rowEq : ∀ (a : V54) (p : Fin 5), image (place a) (row p) = row (exchange a.1 0 p) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem blockEq : ∀ (a : V54) (p q : Fin 5) (h : Fin 4), p≠q →
    exchange a.1 0 p≠exchange a.1 0 q ∧
    image (place a) (collision p q h)=collision (exchange a.1 0 p) (exchange a.1 0 q) (exchange a.2 3 h) := by decide +kernel
theorem shiftPHP (a : V54) : ∀d∈PHP 5 4, image (place a) d∈ PHP 5 4 := by
  rintro d (⟨p,rfl⟩|⟨p,q,h,ne,rfl⟩)
  · exact Or.inl ⟨_,rowEq a p⟩
  · obtain ⟨neq,eq⟩ := blockEq a p q h ne
    exact Or.inr ⟨_,_,_,neq,eq⟩
def site : V54 := (0,3)
theorem site_image : ∀ l : Literal V54, image (place l.1) {l} = {(site,l.2)} ∧
    image (place l.1) {negLit l} = {(site,!l.2)} := by decide +kernel
def posted : Prop := ∃ cs : List (Clause V54), IsRUPRun (PHP 5 4) cs ∧
    (∅ : Clause V54)∈cs ∧ cs.length≤12
theorem fixed : posted ↔ ∃ cs : List (Clause V54), IsRUPRun (PHP 5 4) cs ∧ cs.length≤10 ∧
    ∀ b : Bool, IsRUP (db (PHP 5 4) cs) {(site,b)} := by
  change (∃ cs : List (Clause V54), _ ∧ _ ∧ _) ↔ _
  rw [exact54]
  constructor
  · rintro ⟨cs,ok,sz,l,yes,no⟩
    let f := place l.1
    refine ⟨cs.map (image f),mapRun f (shiftPHP _) ok,by simpa using sz,?_⟩
    have a := mapRup f (mapDB f (shiftPHP _) cs) yes
    have b := mapRup f (mapDB f (shiftPHP _) cs) no
    change IsRUP _ (image (place l.1) {l}) at a
    change IsRUP _ (image (place l.1) {negLit l}) at b
    rw [(site_image l).1] at a
    rw [(site_image l).2] at b
    intro v
    cases hv : l.2 <;> cases v <;> simp_all
  · rintro ⟨cs,ok,sz,both⟩
    exact ⟨cs,ok,sz,(site,true),both true,both false⟩

theorem liftRun {F H : Set (Clause V)} (inc : F⊆H) {cs} (ok : IsRUPRun F cs) : IsRUPRun H cs := by
  induction ok with
  | nil => exact .nil
  | @learn cs c prev good ih =>
    apply IsRUPRun.learn ih
    obtain ⟨d,hd,dead⟩ := good
    have sub : db F cs ⊆ db H cs := fun _ z => z.elim (fun r => Or.inl (inc r)) Or.inr
    exact ⟨d,sub hd,fun l hl => carry sub (fun _ p => .hyp p) (dead l hl)⟩
theorem both_conditioned (h : posted) : ∃ cs : List (Clause V54),
    cs.length≤11 ∧ (∅ : Clause V54)∈cs ∧
    ∀ b : Bool, IsRUPRun (PHP 5 4 ∪ {{(site,b)}}) cs := by
  obtain ⟨ps,run,len,dual⟩ := fixed.mp h
  refine ⟨∅::ps,by simp; omega,by simp,?_⟩
  intro b
  let H : Set (Clause V54) := PHP 5 4 ∪ {{(site,b)}}
  have sub : db (PHP 5 4) ps ⊆ db H ps := by
    rintro d (h|h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  apply IsRUPRun.learn (liftRun (H:=H) (fun _ h => Or.inl h) run)
  obtain ⟨d,hd,dead⟩ := dual (!b)
  refine ⟨d,sub hd,fun l hl => carry sub ?_ (dead l hl)⟩
  rintro _ ⟨k,m,rfl⟩
  have eq : k=(site,!b) := Finset.mem_singleton.mp m
  subst k
  have un : UPForces (db H ps) (negLit '' (↑(∅ : Clause V54) : Set (Literal V54))) (site,b) :=
    .unit (D:={(site,b)}) (Or.inl (Or.inr rfl)) (by simp) (by simp)
  simpa [negLit] using un
end PEqualNP.Outside.L_meta_9246.FixedCell
