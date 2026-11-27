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

abbrev Ix := Fin 70
def forms : Array C := #[
{((0,0),true),((0,1),true),((2,1),true),((4,3),false)},
{((1,0),true),((1,2),true),((1,3),true),((3,2),true),((3,3),true)},
{((1,2),true),((1,3),true),((3,2),true),((3,3),true)},
{((1,2),true),((1,3),true),((2,0),false)},
{((1,1),true),((2,2),false),((3,0),true),((3,1),true)},
{((2,2),true),((2,3),true),((3,0),true),((3,2),true),((3,3),true)},
{((1,2),false),((2,3),true),((3,3),true)},
{((1,3),false),((2,2),true),((3,2),true)},
{((2,0),false),((3,2),true),((3,3),true)},
{((0,0),true),((1,0),true),((1,1),true),((4,2),false)},
{((0,0),true),((0,1),true),((2,1),true),((3,2),false)},
{((0,1),false),((2,2),true),((2,3),true)},
{((0,3),true),((2,3),true),((3,2),false)},
{((2,2),true),((2,3),true),((3,0),false)},
{((2,2),true),((2,3),true),((3,2),true),((3,3),true)},
{((0,2),true),((0,3),true),((3,0),false)},
{((0,2),true),((2,2),true),((3,3),false)},
{((0,3),true),((3,1),true),((3,3),true),((4,2),false)},
{((0,1),false),((1,0),true),((1,2),true)},
{((0,1),true),((0,3),true),((1,1),true),((2,2),false)},
{((1,0),true),((1,2),true),((2,3),false)},
{((0,0),true),((0,2),true),((2,3),false)},
{((0,2),true),((1,0),false),((2,2),true)},
{((1,0),true),((1,2),true),((2,0),true),((2,2),true)},
{((0,0),true),((1,2),false),((2,0),true)},
{((0,0),true),((0,1),true),((0,2),true),((2,1),true),((4,0),true),((4,1),true)},
{((1,0),true),((1,2),true),((1,3),true),((2,2),true),((2,3),true)},
{((0,0),true),((0,1),true),((0,2),true),((4,2),true),((4,3),true)},
{((0,1),true),((0,2),true)},
{((0,0),true)},
{((0,0),false)},
{((0,1),true)},
{((0,1),false)},
{((0,2),true)},
{((0,2),false)},
{((0,3),true)},
{((0,3),false)},
{((1,0),true)},
{((1,0),false)},
{((1,1),true)},
{((1,1),false)},
{((1,2),true)},
{((1,2),false)},
{((1,3),true)},
{((1,3),false)},
{((2,0),true)},
{((2,0),false)},
{((2,1),true)},
{((2,1),false)},
{((2,2),true)},
{((2,2),false)},
{((2,3),true)},
{((2,3),false)},
{((3,0),true)},
{((3,0),false)},
{((3,1),true)},
{((3,1),false)},
{((3,2),true)},
{((3,2),false)},
{((3,3),true)},
{((3,3),false)},
{((4,0),true)},
{((4,0),false)},
{((4,1),true)},
{((4,1),false)},
{((4,2),true)},
{((4,2),false)},
{((4,3),true)},
{((4,3),false)},
∅
]
def term (i : Ix) : C := forms[i.val]!
def board (o f : Nat) : Val := fun v =>
  if o.testBit (4*v.1.val+v.2.val) then some true else
  if f.testBit (4*v.1.val+v.2.val) then some false else none
local instance (s : Val) : Decidable (RowRule s) := by unfold RowRule; infer_instance
local instance (s : Val) : Decidable (ColumnRule s) := by unfold ColumnRule; infer_instance
local instance (s : Val) (c : C) : Decidable (Safe s c) := by unfold Safe Holds; infer_instance
local instance (s : Val) (c : C) : Decidable (Dead s c) := by unfold Dead Holds; infer_instance

def Passed (s : Val) (a : Nat) (i : Ix) : Prop := RowRule s ∧ ColumnRule s ∧
  (∀ j : Ix, a.testBit j.val=true → Safe s (term j)) ∧ Dead s (term i)
local instance (s : Val) (a : Nat) (i : Ix) : Decidable (Passed s a i) := by unfold Passed; infer_instance

theorem witnessedCut {G : Set C} (allowed : ∀ c, c∈G → c∈PHP 5 4)
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
      obtain ⟨s,rows,cols,safe,dead⟩ := reject i cut nd
      apply False.elim
      apply rup_not_dead (s:=s) (G:=G∪K) _ rup dead
      rintro q (hq|⟨j,r,rfl⟩)
      · exact (boardCriterion s).2 ⟨rows,cols⟩ q (allowed q hq)
      · exact safe j r

def witness68 : Array (Nat×Nat) := #[(0,0),(0,0),(0,311746),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,263506),(0,0),(0,0),(0,0),(8,821703),(0,262470),(0,262467),(1,332114),(0,262466),(0,0),(0,262470),(4,280002),(0,262474),(8,821698),(0,262482),(16,332099),(0,262498),(32,402242),(0,262466),(0,0),(0,262594),(128,821578),(0,262466),(0,0),(0,262978),(512,401762),(0,263490),(1024,278854),(0,264514),(2048,819658),(0,266562),(4096,328019),(0,270658),(8192,394082),(0,278850),(16384,296278),(0,295234),(32768,788938),(0,328002),(65536,266579),(0,393538),(131072,271202),(0,262466),(0,0),(0,786754),(524288,297418),(0,262466)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem verified68 : ∀ i : Ix, (1052674 : Nat).testBit i.val=false → (73787051066048638969 : Nat).testBit i.val=false →
  let x := witness68[i.val]!
  Passed (board x.1 x.2) 73787051066048638969 i := by decide +kernel

set_option maxRecDepth 10000 in
theorem physicalCut68 {xs : List C} (legal : IsRUPRun (PHP 5 4) xs)
    (empty : (∅:C)∈xs) (within : ∀ c∈xs, ∃ i : Ix,term i=c) :
    ∃ i : Ix, (1052674 : Nat).testBit i.val = true ∧ term i∈xs := by
  apply witnessedCut (fun _ h=>h) legal empty within 1052674 73787051066048638969
  · decide +kernel
  · intro i h n
    exact ⟨_,verified68 i h n⟩

end PEqualNP.Outside.L_meta_9246.Stable
