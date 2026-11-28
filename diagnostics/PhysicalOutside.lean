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

namespace UnitContraction
variable {V : Type} [DecidableEq V]
abbrev assumptions (c : Clause V) := negLit '' (↑c : Set (Literal V))
def clashes (G : Set (Clause V)) (B : Set (Literal V)) :=
  ∃ d∈G, ∀ l∈d, UPForces G B (negLit l)

theorem simulate {G H : Set (Clause V)} {A B : Set (Literal V)}
    (shrinks : ∀ d∈G, ∃ e∈H, e⊆d)
    (hypotheses : ∀ l∈A, UPForces H B l)
    (clean : ¬clashes H B) {l} (old : UPForces G A l) : UPForces H B l := by
  induction old with
  | hyp m => exact hypotheses _ m
  | @unit d k md hk other ih =>
    obtain ⟨e,he,sub⟩ := shrinks d md
    by_cases member : k∈e
    · exact .unit he member (fun z hz ne => ih z (sub hz) ne)
    · exact False.elim (clean ⟨e,he,fun z hz => ih z (sub hz) (fun eq => member (eq ▸ hz))⟩)

theorem shortenClause {G H : Set (Clause V)} {c e : Clause V}
    (shrinks : ∀ d∈G, ∃ f∈H, f⊆d)
    (reconstruct : ∀ l∈c, UPForces H (assumptions e) (negLit l))
    (old : IsRUP G c) : IsRUP H e := by
  change clashes H (assumptions e)
  by_contra clean
  obtain ⟨d,hd,dead⟩ := old
  obtain ⟨f,hf,sub⟩ := shrinks d hd
  apply clean
  refine ⟨f,hf,fun l hl => simulate shrinks ?_ clean (dead l (sub hl))⟩
  rintro _ ⟨z,hz,rfl⟩
  exact reconstruct z hz

def eraseUnit (u : Literal V) (c : Clause V) : Option (Clause V) :=
  if u∈c then none else some (c.erase (negLit u))

theorem coversOld {F : Set (Clause V)} (u : Literal V) (raw : {u} ∈ F) (xs : List (Clause V)) :
    ∀d∈ F∪{q | q∈xs}, ∃e∈ F∪{q | q∈xs.filterMap (eraseUnit u)},e⊆d := by
  rintro d (hd|hd)
  · exact ⟨d,Or.inl hd,Finset.Subset.rfl⟩
  · by_cases inside : u∈d
    · exact ⟨{u},Or.inl raw,Finset.singleton_subset_iff.mpr inside⟩
    · exact ⟨d.erase (negLit u),Or.inr (List.mem_filterMap.mpr ⟨d,hd,by simp [eraseUnit,inside]⟩),Finset.erase_subset _ _⟩

/-- Remove every learned clause made true by a raw singleton, and erase its
opposite literal from every other entry. The very same raw database is kept. -/
theorem contractRun {F : Set (Clause V)} (u : Literal V) (raw : {u} ∈ F)
    {xs : List (Clause V)} (run : IsRUPRun F xs) : IsRUPRun F (xs.filterMap (eraseUnit u)) := by
  induction run with
  | nil => exact .nil
  | @learn xs c old step ih =>
    by_cases inside : u∈c
    · simpa [eraseUnit,inside] using ih
    · rw [List.filterMap_cons]
      simp only [eraseUnit,if_neg inside]
      apply IsRUPRun.learn ih
      apply shortenClause (coversOld u raw xs) _ step
      intro l hl
      by_cases drop : l=negLit u
      · subst l
        have h : UPForces (F∪{q | q∈xs.filterMap (eraseUnit u)})
            (assumptions (c.erase (negLit u))) u :=
          .unit (D:={u}) (Or.inl raw) (by simp) (by simp)
        simpa only [RUP9248.inv] using h
      · exact .hyp ⟨l,Finset.mem_erase.mpr ⟨drop,hl⟩,rfl⟩

def directHits (u : Literal V) (xs : List (Clause V)) :=
  (xs.filter (fun c => decide (u∈c))).length

theorem countCharges (u : Literal V) (xs : List (Clause V)) :
    (xs.filterMap (eraseUnit u)).length + directHits u xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    by_cases h : u∈c <;>
      simp [eraseUnit,directHits,List.filter_cons,h] at ih ⊢ <;> omega

end UnitContraction
namespace PEqualNP.Outside.L_meta_9248.Projection
open RUP9248 UnitContraction
open PEqualNP.Outside.L_meta_9246.FixedCell
abbrev X := Fin 5 × Fin 4
theorem sharedResidues (h : posted) : ∃ps : List (Clause X),
    IsRUPRun (PHP 5 4) ps ∧ ps.length≤10 ∧ ∀ b : Bool,
    IsRUPRun (PHP 5 4 ∪ {{(site,b)}}) (∅ :: ps.filterMap (eraseUnit (site,b))) := by
  obtain ⟨ps,run,len,dual⟩ := fixed.mp h
  refine ⟨ps,run,len,?_⟩
  intro b
  let H : Set (Clause X) := PHP 5 4 ∪ {{(site,b)}}
  have sub : db (PHP 5 4) ps ⊆ db H ps := by
    rintro d (q|q)
    · exact Or.inl (Or.inl q)
    · exact Or.inr q
  have go : IsRUPRun H (∅::ps) := by
    apply IsRUPRun.learn (liftRun (H:=H) (fun _ z => Or.inl z) run)
    obtain ⟨d,m,die⟩ := dual (!b)
    refine ⟨d,sub m,fun l hl => carry sub ?_ (die l hl)⟩
    rintro _ ⟨k,hk,rfl⟩
    have e : k=(site,!b) := Finset.mem_singleton.mp hk
    subst k
    have un : UPForces (db H ps) (negLit '' (↑(∅ : Clause X) : Set (Literal X))) (site,b) :=
      .unit (D:={(site,b)}) (Or.inl (Or.inr rfl)) (by simp) (by simp)
    simpa [negLit] using un
  have shrink := contractRun (F:=H) (site,b) (Or.inr rfl) go
  simpa [H,eraseUnit] using shrink

end PEqualNP.Outside.L_meta_9248.Projection


open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.CofactorCuts

abbrev V := Fin 5 × Fin 4
abbrev L := Literal V
abbrev C := Clause V
abbrev Val := V → Option Bool
def Holds (s : Val) (l : L) := s l.1 = some l.2
def Safe (s : Val) (c : C) : Prop :=
  (∃ l ∈ c, Holds s l) ∨
  ∃ a ∈ c, ∃ b ∈ c, a ≠ b ∧ s a.1 = none ∧ s b.1 = none
def Single (s : Val) (c : C) : Prop :=
  ∃ a ∈ c, s a.1 = none ∧ ∀ b ∈ c, b ≠ a → Holds s (negLit b)
def Ext (s t : Val) := ∀ v b, s v = some b → t v = some b
def BaseSafe (s : Val) := ∀ c ∈ PHP 5 4, Safe s c

theorem clash_holds {s : Val} {l : L} (a : Holds s l) (b : Holds s (negLit l)) : False := by
  simp only [Holds,negLit] at a b
  cases l.2 <;> simp_all

theorem unknown_of_neither {s : Val} {l : L} (a : ¬ Holds s l) (b : ¬ Holds s (negLit l)) :
    s l.1 = none := by
  simp only [Holds,negLit] at a b
  cases e : s l.1 with
  | none => rfl
  | some v => cases v <;> cases l.2 <;> simp_all

theorem safe_forces {s : Val} {G : Set C} {A : Set L}
    (gs : ∀ c ∈ G, Safe s c) (hs : ∀ l ∈ A, Holds s l) {l : L} (h : UPForces G A l) : Holds s l := by
  induction h with
  | hyp a => exact hs _ a
  | @unit d l hd hl others ih =>
    rcases gs d hd with ⟨v,hv,yes⟩ | ⟨a,ha,b,hb,ne,ua,ub⟩
    · by_cases eq : v = l
      · exact eq ▸ yes
      · exact (clash_holds yes (ih v hv eq)).elim
    · by_cases eq : a = l
      · have hit := ih b hb (by simpa [← eq] using Ne.symm ne)
        simp [Holds,negLit,ub] at hit
      · have hit := ih a ha eq
        simp [Holds,negLit,ua] at hit

theorem rup_not_dead {s : Val} {G : Set C} (gs : ∀ c ∈ G, Safe s c) {c : C} (r : IsRUP G c) :
    ¬ (∀ l ∈ c, Holds s (negLit l)) := by
  intro dead
  obtain ⟨d,hd,forces⟩ := r
  have prem : ∀ l ∈ negLit '' (↑c : Set L), Holds s l := by
    rintro l ⟨v,hv,rfl⟩
    exact dead v hv
  rcases gs d hd with ⟨v,hv,yes⟩ | ⟨v,hv,_,_,_,uv,_⟩
  · exact clash_holds yes (safe_forces gs prem (forces v hv))
  · have hit := safe_forces gs prem (forces v hv)
    simp [Holds,negLit,uv] at hit

theorem single_of_not_safe {s : Val} {c : C} (ns : ¬ Safe s c) (nd : ¬ ∀ l ∈ c, Holds s (negLit l)) :
    Single s c := by
  classical
  push Not at nd
  obtain ⟨a,ha,hna⟩ := nd
  have noyes : ∀ l ∈ c, ¬ Holds s l := fun l hl yes => ns (Or.inl ⟨l,hl,yes⟩)
  have ua := unknown_of_neither (noyes a ha) hna
  refine ⟨a,ha,ua,?_⟩
  intro b hb ne
  by_contra nb
  exact ns (Or.inr ⟨a,ha,b,hb,Ne.symm ne,ua,unknown_of_neither (noyes b hb) nb⟩)

def Proper (c : C) : Prop := ∀ l∈c, negLit l∉c
def Dead (s : Val) (c : C) : Prop := ∀ l∈c, Holds s (negLit l)

theorem negneg (l : L) : negLit (negLit l)=l := by
  obtain ⟨v,b⟩ := l
  cases b <;> rfl

theorem capture {G : Set C} {c : C} (ok : Proper c) (bad : ¬ IsRUP G c) :
    ∃ s : Val, (∀ d∈G, Safe s d) ∧ Dead s c := by
  classical
  let A := negLit '' (↑c : Set L)
  let F := UPForces G A
  have fromAssum {l : L} (hl : F l) (hn : F (negLit l)) : l∈A := by
    cases hl with
    | hyp a => exact a
    | @unit d p hd hp other =>
      exfalso
      apply bad
      refine ⟨d,hd,?_⟩
      intro u hu
      by_cases e : u=l
      · subst u
        exact hn
      · exact other u hu e
  have noPair {l : L} (hl : F l) (hn : F (negLit l)) : False := by
    obtain ⟨a,ha,ra⟩ := fromAssum hl hn
    obtain ⟨b,hb,rb⟩ := fromAssum hn (by simpa only [negneg] using hl)
    have eq : b=l := by simpa only [negneg] using congrArg negLit rb
    exact ok a ha ((ra.trans eq.symm).symm ▸ hb)
  let s : Val := fun i => if F (i,true) then some true else if F (i,false) then some false else none
  have same (l : L) : Holds s l ↔ F l := by
    rcases l with ⟨v,b⟩
    have imp : F (v,true) → ¬ F (v,false) := fun x y => noPair x y
    cases b <;> by_cases ht : F (v,true) <;> by_cases hf : F (v,false) <;>
      simp_all [Holds,s]
  refine ⟨s,?_,?_⟩
  · intro d hd
    have live : ¬Dead s d := fun dead => bad ⟨d,hd,fun l hl => (same _).1 (dead l hl)⟩
    by_contra ns
    obtain ⟨l,hl,unknown,rest⟩ := single_of_not_safe ns live
    have h : Holds s l := (same l).2 (.unit hd hl (fun k hk ne => (same _).1 (rest k hk ne)))
    simp [Holds,unknown] at h
  · intro l hl
    exact (same _).2 (.hyp ⟨l,hl,rfl⟩)

def Ordered (s : Val) : List C → Prop
  | [] => True
  | c::cs => Ordered s cs ∧ ((∀ d∈cs, Safe s d) → ¬Dead s c)

theorem simulate {G : Set C} {cs} (h : IsRUPRun G cs) (s : Val)
    (base : ∀ c∈G, Safe s c) : Ordered s cs := by
  induction h with
  | nil => trivial
  | learn _ learn ih =>
    refine ⟨ih,fun old => rup_not_dead ?_ learn⟩
    rintro d (hd|hd)
    · exact base d hd
    · exact old d hd

theorem reconstruct (G : Set C) (cs : List C) (proper : ∀ c∈cs, Proper c)
    (test : ∀ s : Val,(∀ d∈G, Safe s d) → Ordered s cs) : IsRUPRun G cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    refine .learn (ih (fun d hd => proper d (List.mem_cons_of_mem _ hd))
      (fun s base => (test s base).1)) ?_
    by_contra bad
    obtain ⟨s,all,dead⟩ := capture (proper c List.mem_cons_self) bad
    exact (test s (fun d hd => all d (Or.inl hd))).2 (fun d hd => all d (Or.inr hd)) dead

/-- A unique unassigned literal is exactly the obstruction to stability whenever a
    clause is physically learnable from the current database. -/
theorem single_not_safe {s : Val} {h : C} (single : Single s h) : ¬ Safe s h := by
  obtain ⟨a, ha, ua, rest⟩ := single
  rintro (⟨b,hb,yes⟩ | ⟨b,hb,c,hc,bc,ub,uc⟩)
  · by_cases eq : b=a
    · subst b
      simp [Holds,ua] at yes
    · exact clash_holds yes (rest b hb eq)
  · by_cases eq : b=a
    · have ne : c≠a := fun q => bc (eq.trans q.symm)
      have hit := rest c hc ne
      simp [Holds,negLit,uc] at hit
    · have hit := rest b hb eq
      simp [Holds,negLit,ub] at hit

/-- After one paid helper, any fixed list of proper entries is physically legal
    precisely when the helper is unit on every previously obstructing board.
    The fixed list can include further nonunit clauses and learned singletons in
    any chronological order. -/
theorem oneHelperAll {G : Set C} {h : C} (paid : IsRUP G h) {cs : List C}
    (proper : ∀ c∈cs, Proper c) :
    IsRUPRun (insert h G) cs ↔
      ∀ s : Val, (∀ c∈G, Safe s c) → ¬ Ordered s cs → Single s h := by
  constructor
  · intro run s db bad
    apply single_of_not_safe _ (rup_not_dead db paid)
    intro good
    apply bad
    apply simulate run s
    intro c hc
    rcases Set.mem_insert_iff.mp hc with eq | old
    · subst c
      exact good
    · exact db c old
  · intro covering
    apply reconstruct _ _ proper
    intro s db
    by_contra bad
    have small : ∀ c∈G, Safe s c := fun c hc => db c (Set.mem_insert_of_mem _ hc)
    exact single_not_safe (covering s small bad) (db h (Set.mem_insert _ _))


theorem paidUnit {G : Set C} {hs : List C} (paid : IsRUPRun G hs) (s : Val)
    (base : ∀ c∈G, Safe s c) :
    (∀ h∈hs, Safe s h) ∨ ∃ h∈hs, Single s h := by
  classical
  induction paid with
  | nil => exact Or.inl (by simp)
  | @learn hs h old learn ih =>
    rcases ih with all | ⟨v,hv,one⟩
    · by_cases good : Safe s h
      · exact Or.inl (fun x hx => (List.mem_cons.mp hx).elim (fun eq => eq.symm ▸ good) (all x))
      · have alive := rup_not_dead (fun c hc => Or.elim hc (base c) (all c)) learn
        exact Or.inr ⟨h,List.mem_cons_self,single_of_not_safe good alive⟩
    · exact Or.inr ⟨v,List.mem_cons_of_mem _ hv,one⟩

/-- Arbitrarily many paid and potentially dependent helpers give an exact covering
    formulation for the remaining chronological suffix. -/
theorem manyHelpersAll {G : Set C} {hs cs : List C} (paid : IsRUPRun G hs)
    (proper : ∀ c∈cs, Proper c) :
    IsRUPRun (G ∪ {c | c∈hs}) cs ↔
      ∀ s : Val, (∀ c∈G, Safe s c) → ¬ Ordered s cs → ∃ h∈hs, Single s h := by
  constructor
  · intro run s base bad
    rcases paidUnit paid s base with all | someUnit
    · exact (bad (simulate run s (fun c hc => Or.elim hc (base c) (all c)))).elim
    · exact someUnit
  · intro cover
    apply reconstruct _ _ proper
    intro s db
    by_contra bad
    obtain ⟨h,hh,one⟩ := cover s (fun c hc => db c (Or.inl hc)) bad
    exact single_not_safe one (db h (Or.inr hh))

theorem dbForces {G H : Set C} {A : Set L} (sub : G ⊆ H) {l : L}
    (proof : UPForces G A l) : UPForces H A l := by
  induction proof with
  | hyp h => exact .hyp h
  | unit hd hl prev ih => exact .unit (sub hd) hl ih

theorem dbRUP {G H : Set C} (sub : G⊆H) {c : C} (proof : IsRUP G c) : IsRUP H c := by
  obtain ⟨d,hd,old⟩ := proof
  exact ⟨d,sub hd,fun l hl => dbForces sub (old l hl)⟩

/-- Every physical run leaving an arbitrary bank must purchase an entry
    available to the bank before it leaves. This gives an order-free hitting
    constraint, valid even if the bank itself cannot be learned. -/
theorem firstOutside {G K : Set C} {cs : List C} (run : IsRUPRun G cs) :
    (∀ c∈cs, c∈K) ∨ ∃ c∈cs, c∉K ∧ IsRUP (G∪K) c := by
  classical
  induction run with
  | nil => exact Or.inl (by simp)
  | @learn cs c old learned ih =>
    rcases ih with all | ⟨v,hv,notin,available⟩
    · by_cases known : c∈K
      · exact Or.inl (fun x hx => (List.mem_cons.mp hx).elim (fun eq => eq.symm ▸ known) (all x))
      · apply Or.inr
        refine ⟨c,List.mem_cons_self,known,dbRUP ?_ learned⟩
        intro d hd
        exact Or.elim hd Or.inl (fun h => Or.inr (all d h))
    · exact Or.inr ⟨v,List.mem_cons_of_mem _ hv,notin,available⟩

def RowRule (s : Val) : Prop := ∀ i : Fin 5, (∃ j : Fin 4, s (i,j)=some true) ∨
  ∃ j k : Fin 4, j≠k ∧ s (i,j)=none ∧ s (i,k)=none
def ColumnRule (s : Val) : Prop := ∀ (i k : Fin 5) (j : Fin 4), i≠k →
  s (i,j)=some true → s (k,j)=some false

theorem rowCriterion (s : Val) (i : Fin 5) :
    Safe s (Finset.univ.image (fun j : Fin 4 => ((i,j),true))) ↔
    (∃ j : Fin 4, s (i,j)=some true) ∨
    ∃ j k : Fin 4, j≠k ∧ s (i,j)=none ∧ s (i,k)=none := by
  constructor
  · rintro (⟨z,mem,yes⟩|⟨z,mz,w,mw,ne,az,aw⟩)
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mem
      exact Or.inl ⟨j,yes⟩
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mz
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp mw
      exact Or.inr ⟨j,k,fun e => ne (e ▸ rfl),az,aw⟩
  · rintro (⟨j,yes⟩|⟨j,k,ne,aj,ak⟩)
    · exact Or.inl ⟨_,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,yes⟩
    · refine Or.inr ⟨_,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
        _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,?_,aj,ak⟩
      intro eq
      exact ne (congrArg (fun z : L => z.1.2) eq)

theorem pairCriterion (s : Val) (a b : V) (ne : a≠b) :
    Safe s {(a,false),(b,false)} ↔
      (s a=some true → s b=some false) ∧ (s b=some true → s a=some false) := by
  have pattern : Safe s {(a,false),(b,false)} ↔
      s a=some false ∨ s b=some false ∨ (s a=none ∧ s b=none) := by
    simp [Safe,Holds,ne,Ne.symm ne]
    <;> tauto
  rw [pattern]
  cases p : s a with
  | none => cases q : s b with
            | none => simp
            | some x => cases x <;> simp
  | some v => cases q : s b with
              | none => cases v <;> simp
              | some x => cases v <;> cases x <;> simp

theorem boardCriterion (s : Val) : BaseSafe s ↔ RowRule s ∧ ColumnRule s := by
  constructor
  · intro guard
    constructor
    · intro i
      exact (rowCriterion s i).1 (guard _ (Or.inl ⟨i,rfl⟩))
    · intro i k j ne
      have diff : (i,j)≠(k,j) := fun e => ne (congrArg Prod.fst e)
      exact ((pairCriterion s _ _ diff).1 (guard _ (Or.inr ⟨i,k,j,ne,rfl⟩))).1
  · rintro ⟨rows,cols⟩ _ (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact (rowCriterion s i).2 (rows i)
    · refine (pairCriterion s _ _ ?_).2 ⟨cols i k j ne,cols k i j ne.symm⟩
      exact fun e => ne (congrArg Prod.fst e)

abbrev Ix := Fin 16
def forms : Array C := #[{((0,2),false)},{((3,0),false)},{((3,2),false)},{((4,0),false)},{((0,0),true)},{((1,0),true),((1,1),true),((2,3),false)},{((1,2),true),((1,3),true),((2,0),false)},{((2,0),true),((2,1),true),((1,3),false)},{((1,2),true),((2,2),true),((4,3),false)},{((2,2),true),((2,3),true),((1,0),false)},{((3,0),true),((3,1),true)},{((3,2),true),((3,3),true),((4,0),false)},{((3,0),true),((3,1),true),((4,1),true)},{((0,2),true),((0,3),true),((1,3),true),((2,3),true),((3,0),true),((3,1),true),((3,2),true),((4,0),true),((4,1),true),((4,3),true),((3,3),false)},{((3,2),true),((3,3),true),((4,2),true),((4,3),true)},∅]
def term (i : Ix) : C := forms[i.val]!
def board (o f : Nat) : Val := fun v =>
  if o.testBit (4*v.1.val+v.2.val) then some true else
  if f.testBit (4*v.1.val+v.2.val) then some false else none
local instance (s : Val) : Decidable (RowRule s) := by unfold RowRule; infer_instance
local instance (s : Val) : Decidable (ColumnRule s) := by unfold ColumnRule; infer_instance
local instance (s : Val) (c : C) : Decidable (Safe s c) := by unfold Safe Holds; infer_instance
local instance (s : Val) (c : C) : Decidable (Dead s c) := by unfold Dead Holds; infer_instance

def offClause : C := {(((0,3):V),false)}
def Fixed : Set C := PHP 5 4 ∪ {offClause}
def Passed (s : Val) (a : Nat) (i : Ix) : Prop := RowRule s ∧ ColumnRule s ∧ Safe s offClause ∧
  (∀ j : Ix, a.testBit j.val=true → Safe s (term j)) ∧ Dead s (term i)
local instance (s : Val) (a : Nat) (i : Ix) : Decidable (Passed s a i) := by unfold Passed; infer_instance

theorem witnessedCut {G : Set C} (allowed : G⊆Fixed)
    {xs : List C} (legal : IsRUPRun G xs) (empty : (∅:C)∈xs)
    (within : ∀ c∈xs, ∃ i : Ix, term i=c)
    (incoming ready : Nat)
    (unreached : ∀ j : Ix, ready.testBit j.val=true → term j≠∅)
    (reject : ∀ i : Ix, incoming.testBit i.val=false → ready.testBit i.val=false →
       ∃ s : Val, Passed s ready i) :
    ∃ i : Ix, incoming.testBit i.val=true ∧ term i∈xs := by
  classical
  let K : Set C := { c | ∃ j : Ix,ready.testBit j.val=true ∧ term j=c }
  rcases firstOutside (K:=K) legal with all|⟨c,m,fresh,rup⟩
  · obtain ⟨j,live,e⟩ := all ∅ empty
    exact (unreached j live e).elim
  · obtain ⟨i,eq⟩ := within c m
    subst c
    cases cut : incoming.testBit i.val with
    | true => exact ⟨i,cut,m⟩
    | false =>
      have nd : ready.testBit i.val=false := by
        cases h : ready.testBit i.val with
        | false => rfl
        | true => exact (fresh ⟨i,h,rfl⟩).elim
      obtain ⟨s,rows,cols,off,safe,dead⟩ := reject i cut nd
      apply False.elim
      apply rup_not_dead (s:=s) (G:=G∪K) _ rup dead
      rintro q (hq|⟨j,r,rfl⟩)
      · rcases allowed hq with hbase|hcell
        · exact (boardCriterion s).2 ⟨rows,cols⟩ q hbase
        · have eq : q=offClause := hcell
          simpa [eq] using off
      · exact safe j r
abbrev Group := Fin 11
def excluded : Array Nat := #[1,18,4,8,160,576,256,1024,2048,12288,16384]
def reached : Array Nat := #[27616,32749,27627,27619,27457,18592,27360,31743,9024,19455,11232]
def label (i : Ix) : Nat := (#[0,1,2,3,1,4,5,4,6,5,7,8,9,9,10,11] : Array Nat)[i.val]!
def masks : Array (Array (Nat × Nat)) := #[#[(0,8),(4096,65817),(16384,787532),(65536,4377),(0,9),(0,8),(0,8),(0,8),(0,8),(0,8),(0,12296),(0,8),(0,143368),(0,8),(0,8),(0,8)],#[(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,81932)],#[(0,8),(0,8),(0,8),(0,8),(2,209453),(0,8),(0,8),(0,8),(0,8),(0,8),(0,77836),(0,8),(0,208908),(0,8),(0,8),(0,69644)],#[(0,8),(0,8),(16384,791628),(0,8),(2,143917),(0,8),(0,8),(0,8),(0,8),(0,8),(0,12300),(0,8),(0,143372),(0,8),(0,8),(0,4108)],#[(0,8),(4098,205629),(16384,787532),(65538,144189),(2,139821),(0,8),(0,8),(0,8),(0,8),(0,8),(0,12300),(0,8),(0,143372),(0,8),(0,8),(0,12)],#[(4,279624),(4096,65817),(16384,263244),(65536,4377),(0,9),(0,8),(0,8),(0,8),(524288,36040),(0,8),(0,12296),(0,8),(0,143368),(294912,752844),(0,8),(0,8)],#[(4,279624),(4096,65817),(16384,263244),(65536,4377),(0,9),(0,8),(0,8),(0,8),(0,8),(0,8),(0,12296),(0,8),(0,143368),(0,8),(0,8),(0,8)],#[(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(1,86300)],#[(4,803912),(4096,65817),(16384,787532),(65536,4377),(0,9),(2112,836796),(0,8),(1152,838476),(0,8),(0,8),(0,12296),(0,8),(0,143368),(0,8),(0,835592),(0,8)],#[(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(0,8),(32769,620956),(0,8),(0,8),(0,8),(0,8),(1,86300)],#[(4,803912),(4096,65817),(16384,787532),(65536,4377),(0,9),(0,8),(0,8),(0,8),(0,8),(0,8),(0,12296),(0,8),(0,143368),(0,8),(0,8),(0,8)]]
def mask (k : Group) := excluded[k.val]!
def seen (k : Group) := reached[k.val]!
def check (k : Group) (i : Ix) : Prop := (mask k).testBit i.val=false →
  (seen k).testBit i.val=false →
  let w := (masks[k.val]!)[i.val]!
  Passed (board w.1 w.2) (seen k) i
local instance (k : Group) (i : Ix) : Decidable (check k i) := by unfold check; infer_instance
set_option maxRecDepth 15000
set_option maxHeartbeats 0
theorem row0 : ∀ i, check 0 i := by decide +kernel
theorem row1 : ∀ i, check 1 i := by decide +kernel
theorem row2 : ∀ i, check 2 i := by decide +kernel
theorem row3 : ∀ i, check 3 i := by decide +kernel
theorem row4 : ∀ i, check 4 i := by decide +kernel
theorem row5 : ∀ i, check 5 i := by decide +kernel
theorem row6 : ∀ i, check 6 i := by decide +kernel
theorem row7 : ∀ i, check 7 i := by decide +kernel
theorem row8 : ∀ i, check 8 i := by decide +kernel
theorem row9 : ∀ i, check 9 i := by decide +kernel
theorem row10 : ∀ i, check 10 i := by decide +kernel
theorem checks (k : Group) : ∀i, check k i := by
  fin_cases k
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
theorem nonempty : ∀ (k : Group) (i : Ix), (seen k).testBit i.val=true → term i≠∅ := by decide +kernel
theorem numbered : ∀ (k : Group) (i : Ix), (mask k).testBit i.val=true → label i=k.val := by decide +kernel
theorem separate : Function.Injective term := by decide +kernel
theorem cohort {xs : List C} (run : IsRUPRun Fixed xs) (empty : (∅:C)∈xs)
    (within : ∀ c∈xs, ∃ i : Ix,term i=c) : 12≤xs.length := by
  classical
  have paid (t : Fin 12) : ∃i : Ix, label i=t.val ∧ term i∈xs := by
    by_cases h : t.val<11
    · let k : Group := ⟨t.val,h⟩
      obtain ⟨i,hit,mem⟩ := witnessedCut (G:=Fixed) (fun _ h' => h') run empty within
        (mask k) (seen k) (nonempty k) (fun i h₁ h₂ => ⟨_,checks k i h₁ h₂⟩)
      exact ⟨i,numbered k i hit,mem⟩
    · have eq : t.val=11 := by omega
      exact ⟨15,(by rw [eq]; decide),empty⟩
  choose pick lab present using paid
  let pay (t : Fin 12) : {q // q∈xs.toFinset} :=
    ⟨term (pick t),List.mem_toFinset.mpr (present t)⟩
  have inj : Function.Injective pay := by
    intro i j eq
    have et : term (pick i)=term (pick j) := congrArg Subtype.val eq
    exact Fin.ext ((lab i).symm.trans ((congrArg label (separate et)).trans (lab j)))
  have size : 12≤xs.toFinset.card := by
    calc
      12 = Fintype.card (Fin 12) := (Fintype.card_fin _).symm
      _ ≤ Fintype.card ↥xs.toFinset := Fintype.card_le_of_injective pay inj
      _ = xs.toFinset.card := Fintype.card_coe xs.toFinset
  exact size.trans (List.toFinset_card_le xs)

end PEqualNP.Outside.L_meta_9248.CofactorCuts

namespace PEqualNP.Outside.L_meta_9248.Projection
open UnitContraction PEqualNP.Outside.L_meta_9246.FixedCell
open PEqualNP.Outside.L_meta_9248.CofactorCuts
theorem physicalOutside (h : posted) : ∃ps : List (Clause X), IsRUPRun (PHP 5 4) ps ∧ ps.length≤10 ∧
    ∃c∈ps.filterMap (eraseUnit (site,false)), ∀i : Ix, term i≠c := by
  classical
  obtain ⟨ps,ok,len,sides⟩ := sharedResidues h
  refine ⟨ps,ok,len,?_⟩
  by_contra none
  push_neg at none
  let xs := ps.filterMap (eraseUnit (site,false))
  have live : IsRUPRun Fixed (∅::xs) := sides false
  have size := cohort live List.mem_cons_self (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl|inX
    · exact ⟨15,rfl⟩
    · exact none c inX)
  have smaller := List.length_filterMap_le (f:=eraseUnit (site,false)) (l:=ps)
  change 12≤xs.length+1 at size
  change xs.length≤ps.length at smaller
  omega
end PEqualNP.Outside.L_meta_9248.Projection
