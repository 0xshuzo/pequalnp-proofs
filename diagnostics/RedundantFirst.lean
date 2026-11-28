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

namespace PEqualNP.Outside.L_meta_9248.Prune
open RUP9248
variable {V : Type} [DecidableEq V]

def minus (d : Clause V) (k : Literal V) : Set (Literal V) :=
  {z | ∃ m∈d, m≠k ∧ z=negLit m}
def falses (d : Clause V) : Set (Literal V) := negLit '' (↑d : Set (Literal V))

def Absorbs (H : Set (Clause V)) (B : Set (Literal V)) (d : Clause V) : Prop :=
  conflict H (B ∪ falses d) ∧ ∀ k∈d,
    conflict H (B ∪ minus d k) ∨ UPForces H (B ∪ minus d k) k

theorem reuseConflict {H : Set (Clause V)} {A B : Set (Literal V)}
    (seed : ∀ l∈A, UPForces H B l) (fail : conflict H A) : conflict H B := by
  obtain ⟨d,hd,dead⟩ := fail
  exact ⟨d,hd,fun l hl => carry (fun _ h => h) seed (dead l hl)⟩

theorem absorbForce {G H : Set (Clause V)} {A B : Set (Literal V)}
    (bank : ∀ d∈G, Absorbs H B d) (hyp : ∀ k∈A,UPForces H B k)
    (safe : ¬ conflict H B) {l} (h : UPForces G A l) : UPForces H B l := by
  induction h with
  | hyp m => exact hyp _ m
  | @unit d k hd hk rest ih =>
    have seed : ∀ z∈B ∪ minus d k, UPForces H B z := by
      rintro z (h|⟨m,hm,ne,rfl⟩)
      · exact .hyp h
      · exact ih m hm ne
    rcases (bank d hd).2 k hk with clash|found
    · exact False.elim (safe (reuseConflict seed clash))
    · exact carry (fun _ m => m) seed found

theorem absorbConflict {G H : Set (Clause V)} {A B : Set (Literal V)}
    (bank : ∀ d∈G, Absorbs H B d) (hyp : ∀ k∈A,UPForces H B k)
    (fail : conflict G A) : conflict H B := by
  by_contra safe
  obtain ⟨d,hd,dead⟩ := fail
  apply safe
  apply reuseConflict (A := B ∪ falses d) _ (bank d hd).1
  rintro k (m|⟨l,hl,rfl⟩)
  · exact .hyp m
  · exact absorbForce bank hyp safe (dead l hl)

theorem existing {H : Set (Clause V)} (B : Set (Literal V)) {d : Clause V} (hd : d∈H) :
    Absorbs H B d := by
  constructor
  · exact ⟨d,hd,fun k hk => .hyp (Or.inr ⟨k,hk,rfl⟩)⟩
  · intro k hk
    exact Or.inr (.unit hd hk (fun m hm ne => .hyp (Or.inr ⟨m,hm,ne,rfl⟩)))


theorem raiseConflict {G H : Set (Clause V)} {A B : Set (Literal V)} (base : G⊆H) (given : A⊆B)
    (bad : conflict G A) : conflict H B := by
  obtain ⟨d,m,die⟩ := bad
  exact ⟨d,base m,fun l hl => carry base (fun _ h => .hyp (given h)) (die l hl)⟩

theorem raiseAbs {G H : Set (Clause V)} {d : Clause V} (base : G⊆H)
    (old : Absorbs G ∅ d) (B : Set (Literal V)) : Absorbs H B d := by
  have inc (S : Set (Literal V)) : (∅ : Set (Literal V))∪S ⊆ B∪S := by
    rintro z (empty|mem)
    · exact False.elim empty
    · exact Or.inr mem
  constructor
  · exact raiseConflict base (inc _) old.1
  · intro k hk
    rcases old.2 k hk with h|h
    · exact Or.inl (raiseConflict base (inc _) h)
    · exact Or.inr (carry base (fun _ h => .hyp ((inc (minus d k)) h)) h)

theorem erase_initial {G : Set (Clause V)} {d : Clause V} (abs : Absorbs G ∅ d)
   {cs : List (Clause V)} (run : IsRUPRun (G∪{d}) cs) : IsRUPRun G cs := by
  induction run with
  | nil => exact .nil
  | @learn rs t prev learn ih =>
    apply IsRUPRun.learn ih
    apply absorbConflict (A:=falses t) (B:=falses t) _ (fun _ h => .hyp h) learn
    rintro e ((base|eq)|paid)
    · exact existing _ (Or.inl base)
    · have same : e=d := eq
      subst e
      exact raiseAbs (fun _ h => Or.inl h) abs _
    · exact existing _ (Or.inr paid)
def replay (db : List (List (Literal V))) (fs : List (Literal V)) : List Nat → Bool
  | [] => false
  | i :: trail =>
    match db[i]? with
    | none => false
    | some d =>
      match d.filter (fun l => !fs.contains l) with
      | [] => true
      | [l] => replay db (negLit l :: fs) trail
      | _ => false

theorem replay_sound (db : List (List (Literal V))) (Γ : Set (Clause V))
    (A : Set (Literal V)) (hd : ∀ d ∈ db, d.toFinset ∈ Γ)
    (trail : List Nat) (fs : List (Literal V))
    (hf : ∀ l ∈ fs, UPForces Γ A (negLit l)) (h : replay db fs trail = true) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction trail generalizing fs with
  | nil => simp [replay] at h
  | cons i trail ih =>
    simp only [replay] at h
    split at h
    · contradiction
    next d he =>
      have hm := hd d (List.mem_of_getElem? he)
      split at h
      next hnil =>
        refine ⟨d.toFinset, hm, ?_⟩
        intro l hl
        have hld : l ∈ d := List.mem_toFinset.mp hl
        apply hf
        by_contra hn
        have : l ∈ d.filter (fun l => !fs.contains l) := by simp [hld, hn]
        rw [hnil] at this
        exact List.not_mem_nil this
      next l hsingle =>
        have hld : l ∈ d.filter (fun v => !fs.contains v) := by
          rw [hsingle]
          exact List.mem_cons_self
        have hu : UPForces Γ A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp hld).1)
          intro v hv hne
          apply hf
          by_contra hn
          have hvd : v ∈ d := List.mem_toFinset.mp hv
          have : v ∈ d.filter (fun x => !fs.contains x) := by simp [hvd, hn]
          rw [hsingle] at this
          exact hne (List.mem_singleton.mp this)
        apply ih (negLit l :: fs) _ h
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simpa [negLit] using hu
        · exact hf v hv
      next => contradiction

abbrev Board := Fin 5 × Fin 4

def row (p : Fin 5) : List (Literal Board) :=
  (List.finRange 4).map (fun h => ((p, h), true))

def block (p q : Fin 5) (h : Fin 4) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

def input : List (List (Literal Board)) :=
  (List.finRange 5).map row ++ (List.finRange 4).flatMap (fun h =>
    (List.finRange 5).flatMap (fun p =>
      ((List.finRange 5).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP 5 4 := by
  rcases List.mem_append.mp hd with hr | hb
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    left
    refine ⟨p, ?_⟩
    ext l
    simp [row]
  · obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hb
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    right
    exact ⟨p, q, h, ne_of_lt (of_decide_eq_true (List.mem_filter.mp hq).2), by simp [block]⟩

def readLiteral (k : Nat) : Literal Board :=
  ((Fin.ofNat 5 (k / 2 / 4), Fin.ofNat 4 (k / 2)), decide (k % 2 = 0))



def derive (db : List (List (Literal V))) (fs : List (Literal V)) (k : Literal V) : List Nat → Bool
  | [] => fs.contains (negLit k)
  | i::is => match db[i]? with
    | none => false
    | some d => match d.filter (fun l => !fs.contains l) with
      | [l] => derive db (negLit l ::fs) k is
      | _ => false

theorem derive_sound (db : List (List (Literal V))) (G : Set (Clause V)) (A : Set (Literal V))
    (raw : ∀d∈db,d.toFinset∈G) (trail : List Nat) (fs : List (Literal V)) (k : Literal V)
    (init : ∀l∈fs, UPForces G A (negLit l)) (test : derive db fs k trail=true) : UPForces G A k := by
  induction trail generalizing fs with
  | nil =>
    have h : negLit k∈fs := by simpa [derive] using test
    simpa using init _ h
  | cons i is ih =>
    simp only [derive] at test
    split at test
    · contradiction
    next d get =>
      have hm := raw d (List.mem_of_getElem? get)
      split at test
      next l single =>
        have mem : l∈d.filter (fun v=> !fs.contains v) := by rw [single]; exact List.mem_cons_self
        have force : UPForces G A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp mem).1) 
          intro v hv ne
          apply init
          by_contra hn
          have live : v∈d.filter (fun z => !fs.contains z) := by simp [List.mem_toFinset.mp hv,hn]
          rw [single] at live
          exact ne (List.mem_singleton.mp live)
        apply ih (negLit l::fs) _ test
        intro v hv
        rcases List.mem_cons.mp hv with rfl|old
        · simpa using force
        · exact init v old
      next => contradiction

def idx (k : Literal Board) := 2*(4*k.1.1.val+k.1.2.val)+(if k.2 then 0 else 1)
def ls0 : List (Literal Board) := ([0, 2, 4, 8, 10, 12] : List Nat).map readLiteral
def ts0 : Array (List Nat) := #[[1, 35, 0], [], [1, 35, 0], [], [1, 35, 0], [], [], [], [0, 35, 1], [], [0, 35, 1], [], [0, 35, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem success0 : ∀ (r : Fin 5) (h : Fin 4) (b : Bool), let k : Literal Board:=((r,h),b)
  k∈ls0 → derive input (ls0.filter (fun z => z != k)) k ts0[idx k]! = true := by decide +kernel
theorem prune0 : Absorbs (PHP 5 4) ∅ ls0.toFinset := by
  constructor
  · apply replay_sound input _ _ input_sound [0, 1, 35] ls0 _ (by decide +kernel)
    intro l hl
    exact .hyp (Or.inr ⟨l,List.mem_toFinset.mpr hl,rfl⟩)
  · intro k hk
    apply Or.inr
    apply derive_sound input _ _ input_sound ts0[idx k]! (ls0.filter (fun z => z != k)) k _
      (success0 k.1.1 k.1.2 k.2 (List.mem_toFinset.mp hk))
    intro z hz
    have mem := List.mem_filter.mp hz
    exact .hyp (Or.inr ⟨z,List.mem_toFinset.mpr mem.1,by simpa using mem.2,rfl⟩)
def ls1 : List (Literal Board) := ([1, 10, 12, 14] : List Nat).map readLiteral
def ts1 : Array (List Nat) := #[[], [1, 5], [], [], [], [], [], [], [], [], [5, 1], [], [5, 1], [], [5, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem success1 : ∀ (r : Fin 5) (h : Fin 4) (b : Bool), let k : Literal Board:=((r,h),b)
  k∈ls1 → derive input (ls1.filter (fun z => z != k)) k ts1[idx k]! = true := by decide +kernel
theorem prune1 : Absorbs (PHP 5 4) ∅ ls1.toFinset := by
  constructor
  · apply replay_sound input _ _ input_sound [1, 5] ls1 _ (by decide +kernel)
    intro l hl
    exact .hyp (Or.inr ⟨l,List.mem_toFinset.mpr hl,rfl⟩)
  · intro k hk
    apply Or.inr
    apply derive_sound input _ _ input_sound ts1[idx k]! (ls1.filter (fun z => z != k)) k _
      (success1 k.1.1 k.1.2 k.2 (List.mem_toFinset.mp hk))
    intro z hz
    have mem := List.mem_filter.mp hz
    exact .hyp (Or.inr ⟨z,List.mem_toFinset.mpr mem.1,by simpa using mem.2,rfl⟩)
end PEqualNP.Outside.L_meta_9248.Prune
