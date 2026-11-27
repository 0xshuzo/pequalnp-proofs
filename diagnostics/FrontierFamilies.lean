import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9246.Stable

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

def CrossesEveryCut (G : Set C) (bank : Finset C) (target : C) : Prop :=
  ∀ A : Finset C, A ⊆ bank → target∉A →
    ∃ c∈bank, c∉A ∧ IsRUP (G ∪ (A : Set C)) c

theorem runCrosses {G : Set C} {bank : Finset C} {target : C} {xs : List C}
    (run : IsRUPRun G xs) (endMem : target∈xs) (within : ∀ c∈xs,c∈bank) :
    CrossesEveryCut G bank target := by
  intro A sub absent
  rcases firstOutside (K := (A : Set C)) run with all|⟨c,m,new,step⟩
  · exact (absent (all target endMem)).elim
  · exact ⟨c,within c m,new,step⟩

theorem paidRunFromCuts {G : Set C} {bank : Finset C} {target : C}
    (cuts : CrossesEveryCut G bank target) :
    ∃ xs : List C, IsRUPRun G xs ∧ target∈xs ∧ xs.Nodup ∧
      xs.length≤bank.card ∧ ∀ c∈xs,c∈bank := by
  classical
  have fill : ∀ (fuel : Nat) (xs : List C), IsRUPRun G xs → xs.Nodup →
      (∀ c∈xs,c∈bank) → bank.card≤xs.length+fuel →
      ∃ ys : List C, IsRUPRun G ys ∧ target∈ys ∧ ys.Nodup ∧
        ys.length≤bank.card ∧ ∀ c∈ys,c∈bank := by
    intro fuel
    induction fuel with
    | zero =>
      intro xs valid unique within price
      have sub : xs.toFinset ⊆ bank := fun c hc => within c (List.mem_toFinset.mp hc)
      have size := Finset.card_le_card sub
      rw [List.toFinset_card_of_nodup unique] at size
      by_cases found : target∈xs
      · exact ⟨xs,valid,found,unique,size,within⟩
      obtain ⟨c,cb,fresh,_⟩ := cuts xs.toFinset sub (fun h=>found (List.mem_toFinset.mp h))
      have larger : insert c xs.toFinset ⊆ bank := Finset.insert_subset cb sub
      have too := Finset.card_le_card larger
      rw [Finset.card_insert_of_notMem fresh, List.toFinset_card_of_nodup unique] at too
      omega
    | succ fuel ih =>
      intro xs valid unique within price
      have sub : xs.toFinset ⊆ bank := fun c hc => within c (List.mem_toFinset.mp hc)
      by_cases found : target∈xs
      · have size := Finset.card_le_card sub
        rw [List.toFinset_card_of_nodup unique] at size
        exact ⟨xs,valid,found,unique,size,within⟩
      obtain ⟨c,cb,fresh,available⟩ := cuts xs.toFinset sub (fun h=>found (List.mem_toFinset.mp h))
      have nov : c∉xs := fun h => fresh (List.mem_toFinset.mpr h)
      have step : IsRUP (G ∪ {v | v∈xs}) c := dbRUP (by
        intro d hd
        exact hd.elim Or.inl (fun h => Or.inr (List.mem_toFinset.mp h))) available
      apply ih (c::xs) (.learn valid step) (List.nodup_cons.mpr ⟨nov,unique⟩)
      · intro v m
        rcases List.mem_cons.mp m with rfl|old
        · exact cb
        · exact within v old
      · simp only [List.length_cons]; omega
  exact fill bank.card [] .nil (by simp) (by simp) (by simp)

theorem physicalBudgetCuts (G : Set C) (target : C) (budget : Nat) :
    (∃ xs : List C, IsRUPRun G xs ∧ target∈xs ∧ xs.length≤budget) ↔
    ∃ bank : Finset C, bank.card≤budget ∧ CrossesEveryCut G bank target := by
  classical
  constructor
  · rintro ⟨xs,h,mem,cost⟩
    exact ⟨xs.toFinset,(List.toFinset_card_le xs).trans cost,
      runCrosses h mem (fun _ m => List.mem_toFinset.mpr m)⟩
  · rintro ⟨bank,price,test⟩
    obtain ⟨xs,valid,m,_,cost,_⟩ := paidRunFromCuts test
    exact ⟨xs,valid,m,cost.trans price⟩

theorem postedAsCut (budget : Nat) :
    (∃ xs : List C, IsRUPRun (PHP 5 4) xs ∧ (∅:C)∈xs ∧ xs.length≤budget) ↔
    ∃ bank : Finset C, bank.card≤budget ∧ CrossesEveryCut (PHP 5 4) bank ∅ :=
  physicalBudgetCuts _ _ _

/-- A family of raw-stable boards remains simultaneously safe until a purchased
clause unlocks one of them. That clause is not false on any member. -/
theorem unrestrictedFrontier {G : Set C} {xs : List C} (run : IsRUPRun G xs)
    (empty : (∅:C)∈xs) (W : Set Val) (existsBoard : W.Nonempty)
    (base : ∀ s∈W,∀ d∈G,Safe s d) :
    ∃ c∈xs, (∀ s∈W,¬Dead s c) ∧ ∃ s∈W,Single s c := by
  classical
  let K : Set C := {c | ∀ s∈W,Safe s c}
  rcases firstOutside (K:=K) run with all|⟨c,mem,fresh,rup⟩
  · obtain ⟨s,sw⟩ := existsBoard
    have fail : Safe s (∅:C) := all ∅ empty s sw
    have impossible : False := by simpa [Safe] using fail
    exact impossible.elim
  · have nd (s : Val) (sw : s∈W) : ¬Dead s c := by
      apply rup_not_dead _ rup
      rintro d (raw|preserved)
      · exact base s sw d raw
      · exact preserved s sw
    have notall : ¬∀ s∈W,Safe s c := fresh
    push_neg at notall
    obtain ⟨s,m,ns⟩ := notall
    exact ⟨c,mem,nd,s,m,single_of_not_safe ns (nd s m)⟩

end PEqualNP.Outside.L_meta_9246.Stable
