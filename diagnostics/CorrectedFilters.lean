import PEqualNP.Defs

namespace Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

deriving instance DecidableEq for GateOp

def value (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun s g => s++[value g s]) w

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[value g w])).getD i false = _
    rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]

def check (s : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => (g.op=.and → value g s=false) ∧ check (s++[if g.op=.and then false else value g s]) gs

theorem check_iff (w : List Bool) (gs : List Gate) : check w gs ↔
    ∀ j (hj : j < gs.length), gs[j].op=.and → (run gs w).getD (w.length+j) false=false := by
  induction gs generalizing w with
  | nil => simp [check]
  | cons g gs ih =>
    have first : (run (g::gs) w).getD w.length false=value g w := by
      change (run gs (w++[value g w])).getD _ _=_
      rw [keep _ _ _ (by simp)]
      simp
    have alltail (j : ℕ) :
        (run gs (w++[value g w])).getD ((w++[value g w]).length+j) false =
        (run (g::gs) w).getD (w.length+(j+1)) false := by
      change (run gs _).getD _ _ = (run gs _).getD _ _
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    constructor
    · rintro ⟨head,tail⟩
      have eq : (if g.op=.and then false else value g w)=value g w := by split <;> simp_all
      rw [eq] at tail
      intro j hj op
      cases j with
      | zero => simpa only [Nat.add_zero,first] using head op
      | succ j =>
        exact (alltail j) ▸ (ih _).mp tail j (by simpa using hj) op
    · intro all
      have head : g.op=.and → value g w=false := by
        intro op
        have v := all 0 (by simp) op
        simpa only [Nat.add_zero,first] using v
      refine ⟨head,?_⟩
      have eq : (if g.op=.and then false else value g w)=value g w := by split <;> simp_all
      rw [eq]
      apply (ih _).mpr
      intro j hj op
      rw [alltail]
      exact all (j+1) (by simpa using hj) op

def hit {α : Type} [DecidableEq α] (S A : Finset α) : Bool := decide (∃ a ∈ S, a∈A)

def cone {α : Type} [DecidableEq α] (g : Gate) (ss : List (Finset α)) : Finset α :=
  if g.op=.and then ∅ else g.inputs.foldr (fun i v => ss.getD i ∅ ∪ v) ∅

def missing {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) : List Gate → Prop
  | [] => True
  | g::gs => (g.op=.and → ∃ i∈g.inputs, hit (ss.getD i ∅) A=false) ∧ missing A (ss++[cone g ss]) gs

theorem hits_default {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) (i : ℕ) :
    (ss.map (fun S => hit S A)).getD i false=hit (ss.getD i ∅) A := by
  by_cases h : i < ss.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
    simp [hit]

theorem hits_fold {α : Type} [DecidableEq α] (A : Finset α) (ss : List (Finset α)) (ins : List ℕ) :
    hit (ins.foldr (fun i v => ss.getD i ∅ ∪ v) ∅) A = (ins.map fun i => hit (ss.getD i ∅) A).any id := by
  induction ins with
  | nil => simp [hit]
  | cons i t ih =>
    rw [List.foldr_cons,List.map_cons,List.any_cons,←ih]
    apply Bool.eq_iff_iff.mpr
    simp [hit,or_and_right,exists_or]

theorem cone_check {α : Type} [DecidableEq α] (A : Finset α) (gs : List Gate)
    (mono : ∀ g∈gs, g.op=.and ∨ g.op=.or) (ss : List (Finset α)) :
    check (ss.map (fun S => hit S A)) gs ↔ missing A ss gs := by
  induction gs generalizing ss with
  | nil => rfl
  | cons g gs ih =>
    let w := ss.map (fun S => hit S A)
    have vals : value g w = g.op.eval (g.inputs.map fun i => hit (ss.getD i ∅) A) := by
      simp only [value,w,hits_default]
    have cval : hit (cone g ss) A = (if g.op=.and then false else value g w) := by
      rcases mono g List.mem_cons_self with op|op
      · simp [op,cone,hit]
      · rw [if_neg (by simp [op]),vals]
        simp only [cone,op,reduceCtorEq,if_false,GateOp.eval,hits_fold]
    have ts := ih (fun h mem => mono h (List.mem_cons_of_mem _ mem)) (ss++[cone g ss])
    simp only [List.map_append,List.map_cons,List.map_nil,cval] at ts
    change ((g.op=.and → value g w=false) ∧ _) ↔ ((g.op=.and → _) ∧ _)
    apply and_congr _ ts
    apply forall_congr'
    intro op
    rw [vals,op]
    simp [GateOp.eval]

theorem singleton_hit {n : ℕ} (A : Finset (Fin n)) :
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))).map (fun S => hit S A)=List.ofFn (fun i => decide (i∈A)) := by
  simp [List.map_ofFn,Function.comp_def,hit]

theorem circuit {n : ℕ} (A : Finset (Fin n)) (C : Circuit) (mono : Monotone2 C) :
    missing A (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) C.gates ↔
    ∀ j (hj : j < C.gates.length), (gateAt C j).op=.and →
      (C.wires (List.ofFn fun i => decide (i∈A))).getD (n+j) false=false := by
  have ok (g : Gate) (h : g∈C.gates) : g.op=.and ∨ g.op=.or := by simpa using (mono g h).1
  rw [←cone_check A _ ok _,singleton_hit,check_iff]
  have atgate (j : ℕ) (hj : j < C.gates.length) : gateAt C j=C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
  simp only [List.length_ofFn]
  constructor
  · intro h j hj op
    exact h j hj ((atgate j hj) ▸ op)
  · intro h j hj op
    exact h j hj ((atgate j hj).symm ▸ op)

end Ports3451

namespace Mask3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Ports3451
variable {α : Type} [DecidableEq α]

def zeroGate : Gate := ⟨.or, []⟩

def Flag (F : Finset (Finset α)) (ss : List (Finset α)) (g : Gate) : Prop :=
  g.op=.and ∧ ∃A∈F, ∀i∈g.inputs, hit (ss.getD i ∅) A=true

noncomputable def choose (F : Finset (Finset α)) (ss : List (Finset α)) (g : Gate) : Gate := by
  classical
  exact if Flag F ss g then zeroGate else g

noncomputable def fix (F : Finset (Finset α)) (ss : List (Finset α)) : List Gate → List Gate
  | [] => []
  | g::gs => choose F ss g :: fix F (ss++[cone g ss]) gs

inductive Cut : List Gate → List Gate → Prop
  | nil : Cut [] []
  | keep {gs ds : List Gate} (g : Gate) (tail : Cut gs ds) : Cut (g::gs) (g::ds)
  | drop {gs ds : List Gate} (g : Gate) (op : g.op=.and) (tail : Cut gs ds) : Cut (g::gs) (zeroGate::ds)

@[simp] theorem coneZero (ss : List (Finset α)) : cone zeroGate ss=∅ := by
  simp [cone,zeroGate]

theorem coneChoose (F : Finset (Finset α)) (ss : List (Finset α)) (g : Gate) :
    cone (choose F ss g) ss=cone g ss := by
  classical
  by_cases b : Flag F ss g
  · rw [choose,if_pos b,coneZero]; simp [cone,b.1]
  · simp [choose,b]

theorem cuts (F : Finset (Finset α)) (ss : List (Finset α)) (gs : List Gate) : Cut gs (fix F ss gs) := by
  classical
  induction gs generalizing ss with
  | nil => exact .nil
  | cons g gs ih =>
    by_cases b : Flag F ss g
    · simpa only [fix,choose,if_pos b] using Cut.drop g b.1 (ih (ss++[cone g ss]))
    · simpa only [fix,choose,if_neg b] using Cut.keep g (ih (ss++[cone g ss]))

theorem clears (F : Finset (Finset α)) (ss : List (Finset α)) (gs : List Gate) (A : Finset α) (mem : A∈F) :
    missing A ss (fix F ss gs) := by
  classical
  induction gs generalizing ss with
  | nil => trivial
  | cons g gs ih =>
    change (_ → _) ∧ missing A (ss++[cone (choose F ss g) ss]) _
    refine ⟨?_,by rw [coneChoose];exact ih _⟩
    by_cases b : Flag F ss g
    · simp [choose,b,zeroGate]
    · rw [choose,if_neg b]
      intro op
      by_contra! all
      apply b
      exact ⟨op,A,mem,fun i hi=>by simpa using all i hi⟩

theorem preserve {gs ds : List Gate} (h : Cut gs ds) (ss : List (Finset α)) (A : Finset α) :
    missing A ss gs → missing A ss ds := by
  induction h generalizing ss with
  | nil => exact id
  | keep g tail ih => intro hold;exact ⟨hold.1,ih _ hold.2⟩
  | drop g op tail ih =>
    intro hold
    refine ⟨by simp [zeroGate],?_⟩
    have e : cone zeroGate ss=cone g ss := by simp [cone,zeroGate,op]
    change missing A (ss++[cone zeroGate ss]) _
    rw [e]
    exact ih _ hold.2

theorem greatest (F : Finset (Finset α)) (ss : List (Finset α)) {gs ds : List Gate} (h : Cut gs ds)
    (clean : ∀A∈F,missing A ss ds) : Cut (fix F ss gs) ds := by
  classical
  induction h generalizing ss with
  | nil => exact .nil
  | keep g tail ih =>
    have safe : ¬Flag F ss g := by
      rintro ⟨op,A,mem,all⟩
      obtain ⟨i,hi,no⟩ := (clean A mem).1 op
      exact Bool.false_ne_true (no.symm.trans (all i hi))
    rw [fix,choose,if_neg safe]
    exact .keep g (ih _ (fun A mem=>(clean A mem).2))
  | drop g op tail ih =>
    have e : cone zeroGate ss=cone g ss := by simp [cone,zeroGate,op]
    have sub := ih (ss++[cone g ss]) (fun A mem=>by rw [←e];exact (clean A mem).2)
    by_cases b : Flag F ss g
    · simpa only [fix,choose,if_pos b] using Cut.keep zeroGate sub
    · simpa only [fix,choose,if_neg b] using Cut.drop g op sub

end Mask3457

namespace Mask3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Ports3451

theorem lengthEq {gs ds : List Gate} (h : Cut gs ds) : ds.length=gs.length := by induction h <;> simp_all

theorem monoCut {gs ds : List Gate} (h : Cut gs ds) (ok : ∀g∈gs, g.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2) :
    ∀g∈ds, g.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2 := by
  induction h with
  | nil => exact ok
  | keep g tail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact ok _ List.mem_cons_self
    · exact ih (fun x hx=>ok x (List.mem_cons_of_mem _ hx)) _ ha
  | drop g op tail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · simp [zeroGate]
    · exact ih (fun x hx=>ok x (List.mem_cons_of_mem _ hx)) _ ha

theorem backCut {gs ds : List Gate} (h : Cut gs ds) (n : Nat)
    (ok : ∀ j (h : j<gs.length),∀i∈gs[j].inputs,i<n+j) :
    ∀ j (h : j<ds.length),∀i∈ds[j].inputs,i<n+j := by
  induction h generalizing n with
  | nil => exact ok
  | keep g tail ih =>
    intro j hj i hi
    cases j with
    | zero => exact ok 0 (by simp) i hi
    | succ k =>
      have e := ih (n+1) (fun t ht b m=>by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ok (t+1) (by simpa using ht) b m)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using e k (by simpa using hj) i hi
  | drop g op tail ih =>
    intro j hj i hi
    cases j with
    | zero => simp [zeroGate] at hi
    | succ k =>
      have e := ih (n+1) (fun t ht b m=>by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ok (t+1) (by simpa using ht) b m)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using e k (by simpa using hj) i hi

def LE (a b : List Bool) := ∀i,a.getD i false=true → b.getD i false=true

theorem stepLE {a b : List Bool} {u v : Bool} (hl : a.length=b.length) (h : LE a b) (s : u=true→v=true) :
    LE (a++[u]) (b++[v]) := by
  intro i on
  by_cases lt : i<a.length
  · rw [List.getD_append _ _ _ _ lt] at on
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i on
  · by_cases e : i=a.length
    · subst i
      rw [hl]
      simpa using s (by simpa using on)
    · rw [List.getD_eq_default _ _ (by simp;omega)] at on
      contradiction

theorem valueLE {a b : List Bool} (g : Gate) (op : g.op=.and ∨ g.op=.or) (h : LE a b) :
    value g a=true → value g b=true := by
  rcases op with eq|eq
  · simpa [value,eq,GateOp.eval,List.all_eq_true] using
      (show (∀i∈g.inputs,a.getD i false=true) → ∀i∈g.inputs,b.getD i false=true from fun s i hi=>h i (s i hi))
  · simpa [value,eq,GateOp.eval,List.any_eq_true] using
      (show (∃i∈g.inputs,a.getD i false=true) → ∃i∈g.inputs,b.getD i false=true from fun ⟨i,mem,on⟩=>⟨i,mem,h i on⟩)

theorem evalLE {gs ds : List Gate} (cut : Cut gs ds) (op : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (a b : List Bool) (len : a.length=b.length) (le : LE a b) : LE (run ds a) (run gs b) := by
  induction cut generalizing a b with
  | nil => exact le
  | keep g tail ih =>
    apply ih (fun t ht=>op t (List.mem_cons_of_mem _ ht)) _ _ (by simp [len])
    exact stepLE len le (valueLE g (op _ List.mem_cons_self) le)
  | drop g andOp tail ih =>
    apply ih (fun t ht=>op t (List.mem_cons_of_mem _ ht)) _ _ (by simp [len])
    exact stepLE len le (by simp [value,zeroGate,GateOp.eval])

def init (n : Nat) := List.ofFn (fun i : Fin n=>({i}:Finset (Fin n)))
noncomputable def repaired (n : Nat) (F : Finset (Finset (Fin n))) (C : Circuit) : Circuit :=
  ⟨fix F (init n) C.gates, C.output⟩

def low (n : Nat) (A : Finset (Fin n)) (C : Circuit) :=
  ∀j<C.gates.length,(gateAt C j).op=.and→(C.wires (List.ofFn fun i=>decide (i∈A))).getD (n+j) false=false

theorem atEq (C : Circuit) (j : Nat) (h : j<C.gates.length) : gateAt C j=C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,h]

theorem properties (n : Nat) (F : Finset (Finset (Fin n))) (C : Circuit)
    (hm : Monotone2 C) (hb : ReadsBack n C) :
    let D := repaired n F C
    Monotone2 D ∧ ReadsBack n D ∧ D.size=C.size ∧ (∀A∈F,low n A D) ∧
    (∀A,low n A C→low n A D) ∧ (∀x,circuitFun n D x=true→circuitFun n C x=true) := by
  let D := repaired n F C
  have h : Cut C.gates D.gates := cuts F (init n) C.gates
  have md : Monotone2 D := monoCut h hm
  have mo (g : Gate) (m : g∈C.gates) : g.op=.and ∨ g.op=.or := by simpa using (hm g m).1
  have bk := backCut h n (fun j hj i mem=>hb j hj i (by rwa [atEq C j hj]))
  refine ⟨md,fun j hj i mem=>bk j hj i (by rwa [←atEq D j hj]),lengthEq h,?_,?_,?_⟩
  · intro A ha
    exact (circuit A D md).mp (clears F (init n) C.gates A ha)
  · intro A ha
    exact (circuit A D md).mp (preserve h _ A ((circuit A C hm).mpr ha))
  · intro x hx
    exact evalLE h mo (List.ofFn x) (List.ofFn x) rfl (fun _ p=>p) C.output hx

end Mask3457

namespace Mask3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Ports3451
variable {N : Nat}
abbrev pt (p : Fin N) := Fin.castAdd N p
abbrev ln (l : Fin N) := Fin.natAdd N l
def pairSet (p l : Fin N) : Finset (Fin (N+N)) := {pt p,ln l}
def pairInput (p l : Fin N) (k : Fin (N+N)) := decide (k=pt p ∨ k=ln l)
def spec (I : Fin N→Fin N→Prop) (C : Circuit) := ∀x,circuitFun (N+N) C x=true ↔
  ∃p l,I p l ∧ x (pt p)=true ∧ x (ln l)=true
noncomputable def nonedges (I : Fin N→Fin N→Prop) : Finset (Finset (Fin (N+N))) := by
  classical
  exact Finset.univ.filter (fun A=>∃p l,¬I p l ∧ A=pairSet p l)

def unitTests (C : Circuit) := ∀ j<C.gates.length,(gateAt C j).op=.and→
  (∀p : Fin N,(C.wires (List.ofFn fun k=>decide (k=pt p))).getD (N+N+j) false=false) ∧
   ∀l : Fin N,(C.wires (List.ofFn fun k=>decide (k=ln l))).getD (N+N+j) false=false

def pairTests (I : Fin N→Fin N→Prop) (C : Circuit) := ∀ j<C.gates.length,(gateAt C j).op=.and→
  ∀ p l,¬I p l→(C.wires (List.ofFn (pairInput p l))).getD (N+N+j) false=false

noncomputable def core (I : Fin N→Fin N→Prop) (C : Circuit) := repaired (N+N) (nonedges I) C

theorem pairCriterion (I : Fin N→Fin N→Prop) (C : Circuit) :
    pairTests I C ↔ ∀A∈nonedges I,low (N+N) A C := by
  classical
  have term (p l : Fin N) : (fun k : Fin (N+N)=>decide (k∈pairSet p l))=pairInput p l := by
    funext k
    apply Bool.eq_iff_iff.mpr
    simp [pairInput,pairSet]
  constructor
  · intro chk A ha
    obtain ⟨p,l,no,rfl⟩ := (Finset.mem_filter.mp ha).2
    intro j hj op
    rw [term p l]
    exact chk j hj op p l no
  · intro chk j hj op p l no
    have mem : pairSet p l∈nonedges I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,l,no,rfl⟩
    rw [←term p l]
    exact chk _ mem j hj op

theorem unitsCriterion (C : Circuit) : unitTests (N:=N) C ↔
    (∀p : Fin N,low (N+N) {pt p} C) ∧ ∀l : Fin N,low (N+N) {ln l} C := by
  constructor
  · intro h
    exact ⟨fun p j hj op=>by simpa using (h j hj op).1 p,
           fun l j hj op=>by simpa using (h j hj op).2 l⟩
  · rintro ⟨left,right⟩ j hj op
    exact ⟨fun p=>by simpa using left p j hj op,fun l=>by simpa using right l j hj op⟩

theorem inputLE {n : Nat} {x y : Fin n→Bool} (h : ∀k,x k=true→y k=true) : LE (List.ofFn x) (List.ofFn y) := by
  intro j hi
  by_cases sm : j<n
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,sm,dite_true,Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [List.getD_eq_getElem?_getD,sm] at hi

theorem sameCut (gs : List Gate) : Cut gs gs := by induction gs with
  | nil => exact .nil
  | cons g gs ih => exact .keep g ih

theorem coreResult (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack (N+N) C)
    (co : spec I C) (unit : unitTests (N:=N) C) :
    let D := core I C
    Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size=C.size ∧ pairTests I D ∧ unitTests (N:=N) D ∧
    (spec I D ↔ ∀p l,I p l→circuitFun (N+N) D (pairInput p l)=true) := by
  let D := core I C
  obtain ⟨md,bd,sz,clean,preserve,down⟩ := properties (N+N) (nonedges I) C hm hb
  have ud := (unitsCriterion C).mp unit
  refine ⟨md,bd,sz,(pairCriterion I D).mpr clean,(unitsCriterion D).mpr ⟨fun p=>preserve _ (ud.1 p),fun l=>preserve _ (ud.2 l)⟩,?_⟩
  constructor
  · intro s p l inc
    exact (s _).mpr ⟨p,l,inc,by simp [pairInput],by simp [pairInput]⟩
  · intro all x
    constructor
    · exact fun d=>(co x).mp (down x d)
    · rintro ⟨p,l,inc,px,lx⟩
      have op (g : Gate) (h : g∈D.gates) : g.op=.and ∨ g.op=.or := by simpa using (md g h).1
      have le : LE (List.ofFn (pairInput p l)) (List.ofFn x) := by
        apply inputLE
        intro k on
        rcases (of_decide_eq_true on : k=pt p ∨ k=ln l) with rfl|rfl
        · exact px
        · exact lx
      exact evalLE (sameCut D.gates) op _ _ (by simp) le D.output (all p l inc)

theorem optimal (I : Fin N→Fin N→Prop) (C E : Circuit) (hm : Monotone2 C) (hb : ReadsBack (N+N) C)
    (h : Cut C.gates E.gates) (out : E.output=C.output) (clear : pairTests I E) :
    ∀x,circuitFun (N+N) E x=true→circuitFun (N+N) (core I C) x=true := by
  let D := core I C
  have em : Monotone2 E := monoCut h hm
  have cs := (pairCriterion I E).mp clear
  have dh : Cut D.gates E.gates := greatest (nonedges I) (init (N+N)) h
    (fun A mem=>(circuit A E em).mpr (cs A mem))
  have dm := (properties (N+N) (nonedges I) C hm hb).1
  have op (g : Gate) (m : g∈D.gates) : g.op=.and ∨ g.op=.or := by simpa using (dm g m).1
  intro x on
  change (run E.gates (List.ofFn x)).getD E.output false=true at on
  rw [out] at on
  exact evalLE dh op _ _ rfl (fun _ q=>q) C.output on

end Mask3457

namespace Repair3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Mask3457

-- Wire evaluation facts from the published L8933.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

/-- Compare two circuits on one input by inspecting only the edited slots. -/
theorem compareAt {n : Nat} (A B : Circuit) (hlen : B.gates.length = A.gates.length)
    (hm : Monotone2 A) (x : Fin n → Bool)
    (edit : ∀ j < A.gates.length, gateAt A j ≠ gateAt B j →
      val A (List.ofFn x) (n+j) = true → val B (List.ofFn x) (n+j) = true) :
    ∀ w, val A (List.ofFn x) w = true → val B (List.ofFn x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro on
    by_cases raw : w < n
    · rwa [val_input (n:=n) (by simp) raw, ← val_input (C:=A) (n:=n) (by simp) raw]
    by_cases ok : w < n+A.gates.length
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt raw)
      have hj : j < A.gates.length := by omega
      have hk : j < B.gates.length := by omega
      by_cases eq : gateAt A j = gateAt B j
      · have ops : (gateAt A j).op = .and ∨ (gateAt A j).op = .or := by
          simpa using (hm _ (gateAt_mem hj)).1
        rcases ops with op|op
        · rw [val_and (by simp) hj op] at on
          rw [val_and (by simp) hk (by rwa [←eq]), ←eq]
          exact fun i h => ⟨(on i h).1, ih i (on i h).1 (on i h).2⟩
        · rw [val_or (by simp) hj op] at on
          rw [val_or (by simp) hk (by rwa [←eq]), ←eq]
          obtain ⟨i,h,lt,v⟩ := on
          exact ⟨i,h,lt,ih i lt v⟩
      · exact edit j hj eq on
    · rw [val_ge (n:=n) (by simp) (by omega)] at on
      cases on

theorem cutAt {gs bs : List Gate} (c : Cut gs bs) :
    ∀ j (hj : j<gs.length) (hk : j<bs.length), gs[j]=bs[j] ∨ bs[j]=zeroGate := by
  induction c with
  | nil => simp
  | keep g t ih =>
    intro j hj hk
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact ih j (by simpa using hj) (by simpa using hk)
  | drop g op t ih =>
    intro j hj hk
    cases j with
    | zero => exact Or.inr rfl
    | succ j => exact ih j (by simpa using hj) (by simpa using hk)

variable {N : Nat}
abbrev Edge (N : Nat) := Fin N × Fin N
def raw (e : Edge N) : Gate := ⟨.and,[(pt e.1).val,(ln e.2).val]⟩
def Lost (I : Fin N → Fin N → Prop) (B : Circuit) (e : Edge N) :=
  I e.1 e.2 ∧ circuitFun (N+N) B (pairInput e.1 e.2) = false
def Hit (I : Fin N → Fin N → Prop) (C B : Circuit) (j : Nat) (e : Edge N) :=
  Lost I B e ∧ val C (List.ofFn (pairInput e.1 e.2)) (N+N+j) = true

noncomputable def fill (C B : Circuit) (pick : Nat → Edge N) : Circuit := by
  classical
  exact ⟨(List.range C.gates.length).map fun j =>
    if gateAt C j=gateAt B j then gateAt B j else raw (pick j), C.output⟩

lemma fill_len (C B : Circuit) (pick : Nat → Edge N) :
    (fill C B pick).gates.length=C.gates.length := by simp [fill]

lemma fill_gate (C B : Circuit) (pick : Nat → Edge N) (j : Nat) (hj : j<C.gates.length) :
    gateAt (fill C B pick) j = @ite Gate (gateAt C j=gateAt B j) (Classical.propDecidable _)
      (gateAt B j) (raw (pick j)) := by
  classical
  have h : j<(fill C B pick).gates.length := by rwa [fill_len]
  rw [gateAt_eq h]
  simp [fill]

lemma raw_on (D : Circuit) (j : Nat) (h : j<D.gates.length) (e : Edge N)
    (g : gateAt D j=raw e) (x : Fin (N+N)→Bool) :
    val D (List.ofFn x) (N+N+j)=true ↔ x (pt e.1)=true ∧ x (ln e.2)=true := by
  rw [val_and (by simp) h (congrArg Gate.op g),g]
  have hp : (pt e.1).val<N+N+j := by have := (pt e.1).isLt; omega
  have hl : (ln e.2).val<N+N+j := by have := (ln e.2).isLt; omega
  constructor
  · intro on
    have a := (on (pt e.1).val List.mem_cons_self).2
    have b := (on (ln e.2).val (List.mem_cons_of_mem _ List.mem_cons_self)).2
    exact ⟨(val_ofFn D x (pt e.1)).symm.trans a,(val_ofFn D x (ln e.2)).symm.trans b⟩
  · rintro ⟨a,b⟩ i hi
    change i ∈ [(pt e.1).val,(ln e.2).val] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · exact ⟨hp,(val_ofFn D x (pt e.1)).trans a⟩
    · exact ⟨hl,(val_ofFn D x (ln e.2)).trans b⟩

lemma fill_shape (C B : Circuit) (pick : Nat → Edge N) (len : B.gates.length=C.gates.length)
    (hm : Monotone2 B) (hb : ReadsBack (N+N) B) :
    Monotone2 (fill C B pick) ∧ ReadsBack (N+N) (fill C B pick) := by
  classical
  let D := fill C B pick
  have slot (j : Nat) (hj : j<D.gates.length) :
      ((gateAt D j).op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ (gateAt D j).inputs.length≤2) ∧
      ∀ i∈(gateAt D j).inputs,i<N+N+j := by
    have hc : j<C.gates.length := by simpa only [D,fill_len] using hj
    have hbj : j<B.gates.length := by omega
    rw [show gateAt D j = _ from fill_gate C B pick j hc]
    split_ifs
    · exact ⟨hm _ (gateAt_mem hbj),hb j hbj⟩
    · refine ⟨by simp [raw],?_⟩
      intro i h
      simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl
      · have := (pt (pick j).1).isLt; omega
      · have := (ln (pick j).2).isLt; omega
  refine ⟨?_,fun j hj => (slot j hj).2⟩
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
  rw [← gateAt_eq hj]
  exact (slot j hj).1

def Positive (I : Fin N → Fin N → Prop) (x : Fin (N+N)→Bool) :=
  ∃ p l,I p l ∧ x (pt p)=true ∧ x (ln l)=true

lemma separate (p l : Fin N) : pt p < ln l := by
  change p.val<N+l.val
  have h := p.isLt
  omega

lemma unit_off (I : Fin N → Fin N → Prop) (v : Fin (N+N)) :
    ¬Positive I (fun k => decide (k=v)) := by
  rintro ⟨p,l,_,a,b⟩
  exact (ne_of_lt (separate p l)) ((of_decide_eq_true a).trans (of_decide_eq_true b).symm)

lemma nonpair_off (I : Fin N → Fin N → Prop) (p l : Fin N) (no : ¬I p l) :
    ¬Positive I (pairInput p l) := by
  rintro ⟨a,b,ab,x,y⟩
  have xp := (of_decide_eq_true x : pt a=pt p ∨ pt a=ln l).resolve_right (ne_of_lt (separate a l))
  have yl := (of_decide_eq_true y : ln b=pt p ∨ ln b=ln l).resolve_left (ne_of_gt (separate p b))
  have pa : a=p := Fin.ext (congrArg (fun z : Fin (N+N)=>z.val) xp)
  have v := congrArg Fin.val yl
  change N+b.val=N+l.val at v
  have bl : b=l := Fin.ext (Nat.add_left_cancel v)
  exact no (pa ▸ bl ▸ ab)

theorem localRepair (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (co : spec I C) (unit : unitTests (N:=N) C)
    (unique : ∀ j<C.gates.length, gateAt C j ≠ gateAt (core I C) j →
      ∀ e f, Hit I C (core I C) j e → Hit I C (core I C) j f → e=f) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let B := core I C
  obtain ⟨mb,bb,sz,pb,ub,full⟩ := coreResult I C hm hb co unit
  change Monotone2 B at mb
  change ReadsBack (N+N) B at bb
  have len : B.gates.length=C.gates.length := sz
  by_cases need : ∃e, Lost I B e
  case neg =>
    refine ⟨B,mb,bb,sz.le,full.mpr ?_,pb,ub⟩
    intro p l inc
    cases h : circuitFun (N+N) B (pairInput p l) with
    | true => rfl
    | false => exact False.elim (need ⟨(p,l),inc,h⟩)
  obtain ⟨base,hbase⟩ := need
  let pick (j : Nat) := if h : ∃e,Hit I C B j e then h.choose else base
  have inc (j : Nat) : I (pick j).1 (pick j).2 := by
    dsimp only [pick]
    split
    next h => exact h.choose_spec.1.1
    next => exact hbase.1
  have owned (j : Nat) (hj : j<C.gates.length) (hc : gateAt C j≠gateAt B j)
      (e : Edge N) (he : Hit I C B j e) : pick j=e := by
    have h : ∃f, Hit I C B j f := ⟨e,he⟩
    dsimp only [pick]
    rw [dif_pos h]
    exact unique j hj hc _ _ h.choose_spec he
  let D := fill C B pick
  have lenD : D.gates.length=C.gates.length := fill_len C B pick
  obtain ⟨md,bd⟩ := fill_shape C B pick len mb bb
  have kept (j : Nat) (hj : j<C.gates.length) (h : gateAt C j=gateAt B j) :
      gateAt D j=gateAt B j := (fill_gate C B pick j hj).trans (if_pos h)
  have fixed (j : Nat) (hj : j<C.gates.length) (h : gateAt C j≠gateAt B j) :
      gateAt D j=raw (pick j) := (fill_gate C B pick j hj).trans (if_neg h)
  have zero (j : Nat) (hj : j<C.gates.length) (hc : gateAt C j≠gateAt B j) : gateAt B j=zeroGate := by
    have h : Cut C.gates B.gates := cuts _ _ _
    have hk : j<B.gates.length := by omega
    rcases cutAt h j hj hk with eq|eq
    · exact False.elim (hc (by rwa [gateAt_eq hj,gateAt_eq hk]))
    · rwa [gateAt_eq hk]
  have fromB (x : Fin (N+N)→Bool) := compareAt B D (lenD.trans len.symm) mb x (by
    intro j hj ne on
    have hc : j<C.gates.length := by omega
    by_cases same : gateAt C j=gateAt B j
    · exact False.elim (ne (kept j hc same).symm)
    · have hz := zero j hc same
      obtain ⟨i,mem,_,_⟩ := (val_or (by simp) hj (congrArg Gate.op hz)).mp on
      simp [hz,zeroGate] at mem)
  have toB (x : Fin (N+N)→Bool) (neg : ¬Positive I x) := compareAt D B (len.trans lenD.symm) md x (by
    intro j hj ne on
    have hc : j<C.gates.length := by omega
    by_cases same : gateAt C j=gateAt B j
    · exact False.elim (ne (kept j hc same))
    · obtain ⟨xp,xl⟩ := (raw_on D j hj _ (fixed j hc same) x).mp on
      exact False.elim (neg ⟨_,_,inc j,xp,xl⟩))
  have lossRecover (e : Edge N) (he : Lost I B e) :
      circuitFun (N+N) D (pairInput e.1 e.2)=true := by
    let x := pairInput e.1 e.2
    have tr := compareAt C D lenD hm x (by
      intro j hj ne on
      have diff : gateAt C j ≠ gateAt B j := fun h => ne (h.trans (kept j hj h).symm)
      have own := owned j hj diff e ⟨he,on⟩
      apply (raw_on D j (by omega) _ (fixed j hj diff) x).mpr
      simp [own,x,pairInput])
    exact tr C.output ((co x).mpr ⟨_,_,he.1,by simp [x,pairInput],by simp [x,pairInput]⟩)
  have edgeOK (p l : Fin N) (h : I p l) : circuitFun (N+N) D (pairInput p l)=true := by
    cases b : circuitFun (N+N) B (pairInput p l) with
    | false => exact lossRecover (p,l) ⟨h,b⟩
    | true => exact fromB _ C.output b
  have down := (properties (N+N) (nonedges I) C hm hb).2.2.2.2.2
  have correct : spec I D := by
    intro x
    constructor
    · intro on
      by_contra neg
      exact neg ((co x).mp (down x (toB x neg C.output on)))
    · rintro ⟨p,l,pi,xp,xl⟩
      have le : LE (List.ofFn (pairInput p l)) (List.ofFn x) := by
        apply inputLE
        intro k on
        rcases (of_decide_eq_true on : k=pt p ∨ k=ln l) with rfl|rfl
        · exact xp
        · exact xl
      exact evalLE (sameCut D.gates) (fun g h=>by simpa using (md g h).1) _ _ (by simp) le D.output (edgeOK p l pi)
  have clean (x : Fin (N+N)→Bool) (neg : ¬ Positive I x)
      (orig : ∀ j < B.gates.length, (gateAt B j).op=.and → val B (List.ofFn x) (N+N+j)=false) :
      ∀ j < D.gates.length, (gateAt D j).op=.and → val D (List.ofFn x) (N+N+j)=false := by
    intro j hj op
    have hc : j<C.gates.length := by omega
    cases v : val D (List.ofFn x) (N+N+j) with
    | false => rfl
    | true =>
      exfalso
      by_cases same : gateAt C j=gateAt B j
      · rw [kept j hc same] at op
        have z := orig j (by omega) op
        exact Bool.false_ne_true (z.symm.trans (toB x neg _ v))
      · obtain ⟨a,b⟩ := (raw_on D j hj _ (fixed j hc same) x).mp v
        exact neg ⟨_,_,inc j,a,b⟩
  refine ⟨D,md,bd,lenD.le,correct,?_,?_⟩
  · intro j hj op p l no
    exact clean _ (nonpair_off I p l no) (fun t ht ot=>pb t ht ot p l no) j hj op
  · intro j hj op
    exact ⟨fun p=>clean _ (unit_off I (pt p)) (fun t ht ot=>(ub t ht ot).1 p) j hj op,
           fun l=>clean _ (unit_off I (ln l)) (fun t ht ot=>(ub t ht ot).2 l) j hj op⟩

end Repair3457


namespace Repair3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : ℕ}

theorem labeled_repair (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (co : spec I C) (unit : unitTests (N:=N) C)
    (pick : Nat→Edge N) (inc : ∀ j,I (pick j).1 (pick j).2)
    (lossRecover : ∀ e,Lost I (core I C) e →
      circuitFun (N+N) (fill C (core I C) pick) (pairInput e.1 e.2)=true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let B := core I C
  obtain ⟨mb,bb,sz,pb,ub,full⟩ := coreResult I C hm hb co unit
  change Monotone2 B at mb
  change ReadsBack (N+N) B at bb
  have len : B.gates.length=C.gates.length := sz
  change ∀ e, Lost I B e → circuitFun (N+N) (fill C B pick) (pairInput e.1 e.2)=true at lossRecover
  let D := fill C B pick
  have lenD : D.gates.length=C.gates.length := fill_len C B pick
  obtain ⟨md,bd⟩ := fill_shape C B pick len mb bb
  have kept (j : Nat) (hj : j<C.gates.length) (h : gateAt C j=gateAt B j) :
      gateAt D j=gateAt B j := (fill_gate C B pick j hj).trans (if_pos h)
  have fixed (j : Nat) (hj : j<C.gates.length) (h : gateAt C j≠gateAt B j) :
      gateAt D j=raw (pick j) := (fill_gate C B pick j hj).trans (if_neg h)
  have zero (j : Nat) (hj : j<C.gates.length) (hc : gateAt C j≠gateAt B j) : gateAt B j=zeroGate := by
    have h : Cut C.gates B.gates := cuts _ _ _
    have hk : j<B.gates.length := by omega
    rcases cutAt h j hj hk with eq|eq
    · exact False.elim (hc (by rwa [gateAt_eq hj,gateAt_eq hk]))
    · rwa [gateAt_eq hk]
  have fromB (x : Fin (N+N)→Bool) := compareAt B D (lenD.trans len.symm) mb x (by
    intro j hj ne on
    have hc : j<C.gates.length := by omega
    by_cases same : gateAt C j=gateAt B j
    · exact False.elim (ne (kept j hc same).symm)
    · have hz := zero j hc same
      obtain ⟨i,mem,_,_⟩ := (val_or (by simp) hj (congrArg Gate.op hz)).mp on
      simp [hz,zeroGate] at mem)
  have toB (x : Fin (N+N)→Bool) (neg : ¬Positive I x) := compareAt D B (len.trans lenD.symm) md x (by
    intro j hj ne on
    have hc : j<C.gates.length := by omega
    by_cases same : gateAt C j=gateAt B j
    · exact False.elim (ne (kept j hc same))
    · obtain ⟨xp,xl⟩ := (raw_on D j hj _ (fixed j hc same) x).mp on
      exact False.elim (neg ⟨_,_,inc j,xp,xl⟩))
  have edgeOK (p l : Fin N) (h : I p l) : circuitFun (N+N) D (pairInput p l)=true := by
    cases b : circuitFun (N+N) B (pairInput p l) with
    | false => exact lossRecover (p,l) ⟨h,b⟩
    | true => exact fromB _ C.output b
  have down := (properties (N+N) (nonedges I) C hm hb).2.2.2.2.2
  have correct : spec I D := by
    intro x
    constructor
    · intro on
      by_contra neg
      exact neg ((co x).mp (down x (toB x neg C.output on)))
    · rintro ⟨p,l,pi,xp,xl⟩
      have le : LE (List.ofFn (pairInput p l)) (List.ofFn x) := by
        apply inputLE
        intro k on
        rcases (of_decide_eq_true on : k=pt p ∨ k=ln l) with rfl|rfl
        · exact xp
        · exact xl
      exact evalLE (sameCut D.gates) (fun g h=>by simpa using (md g h).1) _ _ (by simp) le D.output (edgeOK p l pi)
  have clean (x : Fin (N+N)→Bool) (neg : ¬ Positive I x)
      (orig : ∀ j < B.gates.length, (gateAt B j).op=.and → val B (List.ofFn x) (N+N+j)=false) :
      ∀ j < D.gates.length, (gateAt D j).op=.and → val D (List.ofFn x) (N+N+j)=false := by
    intro j hj op
    have hc : j<C.gates.length := by omega
    cases v : val D (List.ofFn x) (N+N+j) with
    | false => rfl
    | true =>
      exfalso
      by_cases same : gateAt C j=gateAt B j
      · rw [kept j hc same] at op
        have z := orig j (by omega) op
        exact Bool.false_ne_true (z.symm.trans (toB x neg _ v))
      · obtain ⟨a,b⟩ := (raw_on D j hj _ (fixed j hc same) x).mp v
        exact neg ⟨_,_,inc j,a,b⟩
  refine ⟨D,md,bd,lenD.le,correct,?_,?_⟩
  · intro j hj op p l no
    exact clean _ (nonpair_off I p l no) (fun t ht ot=>pb t ht ot p l no) j hj op
  · intro j hj op
    exact ⟨fun p=>clean _ (unit_off I (pt p)) (fun t ht ot=>(ub t ht ot).1 p) j hj op,
           fun l=>clean _ (unit_off I (ln l)) (fun t ht ot=>(ub t ht ot).2 l) j hj op⟩


def Trace (C B : Circuit) (e : Edge N) (S : Finset Nat) : Prop :=
  C.output∈S ∧ (∀ w∈S, w<N+N+C.size) ∧
  (∀ i : Fin (N+N), i.val∈S → pairInput e.1 e.2 i=true) ∧
  ∀ j<C.size, N+N+j∈S → gateAt C j=gateAt B j →
    ((gateAt C j).op=.and → ∀ i∈(gateAt C j).inputs, i∈S) ∧
    ((gateAt C j).op=.or → ∃ i∈(gateAt C j).inputs, i∈S)

def Labels (C B : Circuit) (e : Edge N) (S : Finset Nat) (pick : Nat→Edge N) : Prop :=
  ∀ j<C.size, gateAt C j ≠ gateAt B j → N+N+j∈S → pick j=e

theorem raw_pair (D : Circuit) (j : ℕ) (hj : j<D.gates.length) (e f : Edge N)
    (eq : gateAt D j=raw f) :
    val D (List.ofFn (pairInput e.1 e.2)) (N+N+j)=true ↔ f=e := by
  rw [raw_on D j hj f eq]
  constructor
  · rintro ⟨p,l⟩
    have pe := (of_decide_eq_true p : pt f.1=pt e.1 ∨ pt f.1=ln e.2).resolve_right (ne_of_lt (separate f.1 e.2))
    have le := (of_decide_eq_true l : ln f.2=pt e.1 ∨ ln f.2=ln e.2).resolve_left (ne_of_gt (separate e.1 f.2))
    apply Prod.ext
    · exact Fin.castAdd_injective N N pe
    · apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val le)
  · rintro rfl
    simp [pairInput]

theorem marked_iff (C B : Circuit) (hm : Monotone2 C) (hb : ReadsBack (N+N) C)
    (pick : Nat→Edge N) (e : Edge N) :
    circuitFun (N+N) (fill C B pick) (pairInput e.1 e.2)=true ↔
      ∃ S, Trace C B e S ∧ Labels C B e S pick := by
  classical
  let D := fill C B pick
  let x := pairInput e.1 e.2
  have len : D.gates.length=C.size := fill_len C B pick
  have kept (j : ℕ) (hj : j<C.size) (eq : gateAt C j=gateAt B j) : gateAt D j=gateAt C j :=
    ((fill_gate C B pick j hj).trans (if_pos eq)).trans eq.symm
  have changed (j : ℕ) (hj : j<C.size) (ne : gateAt C j≠gateAt B j) : gateAt D j=raw (pick j) :=
    (fill_gate C B pick j hj).trans (if_neg ne)
  constructor
  · intro hit
    let S := (Finset.range (N+N+C.size)).filter fun i => val D (List.ofFn x) i=true
    have mem (i : ℕ) : i∈S ↔ i<N+N+C.size ∧ val D (List.ofFn x) i=true := by simp [S]
    change val D (List.ofFn x) C.output=true at hit
    have out : C.output<N+N+C.size := by
      by_contra! huge
      rw [val_ge (n:=N+N) (by simp) (by omega)] at hit
      contradiction
    refine ⟨S,⟨(mem _).mpr ⟨out,hit⟩,fun w hw => ((mem w).mp hw).1,?_,?_⟩,?_⟩
    · intro i hi
      exact (val_ofFn D x i).symm.trans ((mem _).mp hi).2
    · intro j hj hs eq
      have h := ((mem _).mp hs).2
      have dj : j<D.gates.length := by omega
      constructor
      · intro op i hi
        have q := (val_and (n:=N+N) (by simp) dj (by rwa [kept j hj eq])).mp h i (by rwa [kept j hj eq])
        exact (mem i).mpr ⟨by have := q.1; omega,q.2⟩
      · intro op
        obtain ⟨i,hi,lt,win⟩ := (val_or (n:=N+N) (by simp) dj (by rwa [kept j hj eq])).mp h
        exact ⟨i,by rwa [kept j hj eq] at hi,(mem i).mpr ⟨by omega,win⟩⟩
    · intro j hj diff hs
      exact (raw_pair D j (by omega) e (pick j) (changed j hj diff)).mp ((mem _).mp hs).2
  · rintro ⟨S,⟨out,range,rawS,gates⟩,labels⟩
    have go (w : Nat) : w∈S → val D (List.ofFn x) w=true := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases rawW : w<N+N
        · let i : Fin (N+N) := ⟨w,rawW⟩
          exact (val_ofFn D x i).trans (rawS i hw)
        obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt rawW)
        have lt := range _ hw
        have hj : j<C.size := by omega
        have dj : j<D.gates.length := by omega
        by_cases eq : gateAt C j=gateAt B j
        · have op := (hm _ (gateAt_mem hj)).1
          rcases op with op|op
          · apply (val_and (n:=N+N) (by simp) dj (by rwa [kept j hj eq])).mpr
            intro i hi
            rw [kept j hj eq] at hi
            have lt := hb j hj i hi
            exact ⟨lt,ih i lt ((gates j hj hw eq).1 op i hi)⟩
          · obtain ⟨i,hi,hs⟩ := (gates j hj hw eq).2 op
            have lt := hb j hj i hi
            exact (val_or (n:=N+N) (by simp) dj (by rwa [kept j hj eq])).mpr
              ⟨i,by rwa [kept j hj eq],lt,ih i lt hs⟩
        · exact (raw_pair D j dj e (pick j) (changed j hj eq)).mpr (labels j hj eq hw)
    exact go C.output out

def Compatible (I : Fin N→Fin N→Prop) (C B : Circuit) (A : Edge N→Finset Nat) : Prop :=
  (∀ e, Lost I B e → Trace C B e (A e)) ∧
  ∀ e f, Lost I B e → Lost I B f → ∀ j<C.size, gateAt C j≠gateAt B j →
    N+N+j∈A e → N+N+j∈A f → e=f

theorem allocation_iff (I : Fin N→Fin N→Prop) (C B : Circuit)
    (hm : Monotone2 C) (hb : ReadsBack (N+N) C) (someLost : ∃ e, Lost I B e) :
    (∃ pick : Nat→Edge N, (∀ j,I (pick j).1 (pick j).2) ∧
      ∀ e, Lost I B e → circuitFun (N+N) (fill C B pick) (pairInput e.1 e.2)=true) ↔
    ∃ A, Compatible I C B A := by
  classical
  constructor
  · rintro ⟨pick,_,ok⟩
    have traces (e : Edge N) (lost : Lost I B e) := (marked_iff C B hm hb pick e).mp (ok e lost)
    let A (e : Edge N) := if h : Lost I B e then (traces e h).choose else ∅
    have works (e : Edge N) (lost : Lost I B e) : Trace C B e (A e) ∧ Labels C B e (A e) pick := by
      simpa only [A,dif_pos lost] using (traces e lost).choose_spec
    refine ⟨A,fun e he => (works e he).1,?_⟩
    intro e f he hf j hj neq ej fj
    exact ((works e he).2 j hj neq ej).symm.trans ((works f hf).2 j hj neq fj)
  · rintro ⟨A,paths,noConflict⟩
    obtain ⟨base,eb⟩ := someLost
    let owner (j : Nat) (e : Edge N) := Lost I B e ∧ N+N+j∈A e
    let pick (j : Nat) := if h : ∃ e,owner j e then h.choose else base
    have inc (j : Nat) : I (pick j).1 (pick j).2 := by
      dsimp only [pick]
      split
      next h => exact h.choose_spec.1.1
      next => exact eb.1
    refine ⟨pick,inc,?_⟩
    intro e he
    apply (marked_iff C B hm hb pick e).mpr
    refine ⟨A e,paths e he,?_⟩
    intro j hj ne ej
    have existsOwner : ∃ f,owner j f := ⟨e,he,ej⟩
    dsimp only [pick]
    rw [dif_pos existsOwner]
    exact noConflict _ _ existsOwner.choose_spec.1 he j hj ne existsOwner.choose_spec.2 ej

theorem trace_normalization (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (co : spec I C) (unit : unitTests (N:=N) C)
    (allocate : ∃ A, Compatible I C (core I C) A) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  by_cases e : ∃ f, Lost I (core I C) f
  · obtain ⟨pick,inc,hit⟩ := (allocation_iff I C _ hm hb e).mpr allocate
    exact labeled_repair I C hm hb co unit pick inc hit
  · apply localRepair I C hm hb co unit
    intro j hj ed a b h _
    exact (e ⟨a,h.1⟩).elim

end Repair3457
namespace Repair3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : ℕ}

def prodGate (w : Nat × Nat) : Gate := ⟨.and,[w.1,w.2]⟩

noncomputable def plug (C B : Circuit) (port : Nat→Nat×Nat) : Circuit := by
  classical
  exact ⟨(List.range C.size).map (fun j => if gateAt C j=gateAt B j then gateAt B j else prodGate (port j)), C.output⟩

theorem plug_len (C B : Circuit) (port : Nat→Nat×Nat) : (plug C B port).gates.length=C.size := by simp [plug]

theorem plug_gate (C B : Circuit) (port : Nat→Nat×Nat) (j : Nat) (hj : j<C.size) :
    gateAt (plug C B port) j=@ite Gate (gateAt C j=gateAt B j) (Classical.propDecidable _)
      (gateAt B j) (prodGate (port j)) := by
  classical
  have h : j<(plug C B port).gates.length := by rwa [plug_len]
  rw [gateAt_eq h]
  simp [plug]

def ValidPorts (N : ℕ) (C B : Circuit) (port : Nat→Nat×Nat) : Prop :=
  ∀ j<C.size, gateAt C j≠gateAt B j →
    (port j).1<N+N+j ∧ (port j).2<N+N+j

def SafePorts (I : Fin N→Fin N→Prop) (C B : Circuit) (port : Nat→Nat×Nat) : Prop :=
  ∀ j<C.size, gateAt C j≠gateAt B j → ∀ x : Fin (N+N)→Bool,
    val B (List.ofFn x) (port j).1=true → val B (List.ofFn x) (port j).2=true →
    Positive I x

def Supplies (C B : Circuit) (port : Nat→Nat×Nat) (S : Finset Nat) : Prop :=
  ∀ j<C.size, gateAt C j≠gateAt B j → N+N+j∈S → (port j).1∈S ∧ (port j).2∈S

theorem plug_model (C B : Circuit) (port : Nat→Nat×Nat) (sameLen : B.gates.length=C.size)
    (bm : Monotone2 B) (bb : ReadsBack (N+N) B) (valid : ValidPorts N C B port) :
    Monotone2 (plug C B port) ∧ ReadsBack (N+N) (plug C B port) := by
  classical
  let D := plug C B port
  have slot (j) (hj : j<D.gates.length) :
      ((gateAt D j).op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ (gateAt D j).inputs.length≤2) ∧
      ∀ i∈(gateAt D j).inputs,i<N+N+j := by
    have jc : j<C.size := by simpa only [D,plug_len] using hj
    have jb : j<B.gates.length := by omega
    rw [show gateAt D j = _ from plug_gate C B port j jc]
    split_ifs with eq
    · exact ⟨bm _ (gateAt_mem jb),bb j jb⟩
    · have q := valid j jc eq
      refine ⟨by simp [prodGate],?_⟩
      intro i hi
      rcases (show i=(port j).1 ∨ i=(port j).2 by simpa [prodGate] using hi) with rfl|rfl
      · exact q.1
      · exact q.2
  refine ⟨?_,fun j hj => (slot j hj).2⟩
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
  rw [←gateAt_eq hj]
  exact (slot j hj).1

theorem transfer_wire {n : ℕ} {A B : Circuit} (x : Fin n→Bool) {j : Nat} (ha : j<A.gates.length)
    (hb : j<B.gates.length) (hm : Monotone2 A) (eq : gateAt A j=gateAt B j)
    (ih : ∀ i<n+j,val A (List.ofFn x) i=true → val B (List.ofFn x) i=true)
    (on : val A (List.ofFn x) (n+j)=true) : val B (List.ofFn x) (n+j)=true := by
  have op := (hm _ (gateAt_mem ha)).1
  rcases op with op|op
  · rw [val_and (by simp) ha op] at on
    rw [val_and (by simp) hb (by rwa [←eq]),←eq]
    exact fun i hi => ⟨(on i hi).1,ih i (on i hi).1 (on i hi).2⟩
  · obtain ⟨i,hi,lt,active⟩ := (val_or (by simp) ha op).mp on
    exact (val_or (by simp) hb (by rwa [←eq])).mpr ⟨i,by rwa [←eq],lt,ih i lt active⟩

theorem plug_negative (I : Fin N→Fin N→Prop) (C B : Circuit) (port : Nat→Nat×Nat)
    (sameLen : B.gates.length=C.size) (safe : SafePorts I C B port)
    (dm : Monotone2 (plug C B port)) (x : Fin (N+N)→Bool) (neg : ¬Positive I x) :
    ∀ w,val (plug C B port) (List.ofFn x) w=true → val B (List.ofFn x) w=true := by
  classical
  let D := plug C B port
  have len : D.gates.length=C.size := plug_len C B port
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro on
    change val D (List.ofFn x) w=true at on
    by_cases rawW : w<N+N
    · rwa [val_input (n:=N+N) (by simp) rawW,←val_input (C:=D) (n:=N+N) (by simp) rawW]
    by_cases past : N+N+C.size≤w
    · rw [val_ge (n:=N+N) (by simp) (by omega)] at on
      contradiction
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt rawW)
    have jc : j<C.size := by omega
    have jd : j<D.gates.length := by omega
    by_cases eq : gateAt C j=gateAt B j
    · exact transfer_wire x jd (by omega) dm ((plug_gate C B port j jc).trans (if_pos eq)) ih on
    · have edit : gateAt D j=prodGate (port j) := (plug_gate C B port j jc).trans (if_neg eq)
      have gate := (val_and (n:=N+N) (by simp) jd (congrArg Gate.op edit)).mp on
      rw [edit] at gate
      have a := gate (port j).1 List.mem_cons_self
      have b := gate (port j).2 (List.mem_cons_of_mem _ List.mem_cons_self)
      exact (neg (safe j jc eq x (ih _ a.1 a.2) (ih _ b.1 b.2))).elim

theorem port_trace (C B : Circuit) (hm : Monotone2 C) (hb : ReadsBack (N+N) C)
    (port : Nat→Nat×Nat) (valid : ValidPorts N C B port) (e : Edge N) (S : Finset Nat)
    (tr : Trace C B e S) (supply : Supplies (N:=N) C B port S) :
    circuitFun (N+N) (plug C B port) (pairInput e.1 e.2)=true := by
  classical
  let D := plug C B port
  let x := pairInput e.1 e.2
  obtain ⟨out,range,rawS,gates⟩ := tr
  have len : D.gates.length=C.size := plug_len C B port
  have go (w : Nat) : w∈S → val D (List.ofFn x) w=true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases rawW : w<N+N
      · let i : Fin (N+N) := ⟨w,rawW⟩
        exact (val_ofFn D x i).trans (rawS i hw)
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt rawW)
      have lt := range _ hw
      have hj : j<C.size := by omega
      have jd : j<D.gates.length := by omega
      by_cases eq : gateAt C j=gateAt B j
      · have same : gateAt D j=gateAt C j := ((plug_gate C B port j hj).trans (if_pos eq)).trans eq.symm
        have op := (hm _ (gateAt_mem hj)).1
        rcases op with op|op
        · apply (val_and (n:=N+N) (by simp) jd (by rwa [same])).mpr
          intro i hi
          rw [same] at hi
          have back := hb j hj i hi
          exact ⟨back,ih i back ((gates j hj hw eq).1 op i hi)⟩
        · obtain ⟨i,hi,hs⟩ := (gates j hj hw eq).2 op
          have back := hb j hj i hi
          exact (val_or (n:=N+N) (by simp) jd (by rwa [same])).mpr
            ⟨i,by rwa [same],back,ih i back hs⟩
      · have edit : gateAt D j=prodGate (port j) := (plug_gate C B port j hj).trans (if_neg eq)
        have back := valid j hj eq
        have haveBoth := supply j hj eq hw
        apply (val_and (n:=N+N) (by simp) jd (congrArg Gate.op edit)).mpr
        rw [edit]
        intro i hi
        rcases (show i=(port j).1 ∨ i=(port j).2 by simpa [prodGate] using hi) with rfl|rfl
        · exact ⟨back.1,ih _ back.1 haveBoth.1⟩
        · exact ⟨back.2,ih _ back.2 haveBoth.2⟩
  exact go C.output out

theorem port_normalization (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (co : spec I C) (unit : unitTests (N:=N) C) (port : Nat→Nat×Nat)
    (valid : ValidPorts N C (core I C) port) (safe : SafePorts I C (core I C) port)
    (paths : ∀ e,Lost I (core I C) e → ∃ S,Trace C (core I C) e S ∧ Supplies (N:=N) C (core I C) port S) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let B := core I C
  obtain ⟨mb,bb,sz,pb,ub,_⟩ := coreResult I C hm hb co unit
  have len : B.gates.length=C.size := sz
  let D := plug C B port
  have lenD : D.gates.length=C.size := plug_len C B port
  obtain ⟨md,bd⟩ := plug_model C B port len mb bb valid
  have kept (j : Nat) (hj : j<C.size) (eq : gateAt C j=gateAt B j) : gateAt D j=gateAt B j :=
    (plug_gate C B port j hj).trans (if_pos eq)
  have zero (j : Nat) (hj : j<C.size) (hc : gateAt C j≠gateAt B j) : gateAt B j=zeroGate := by
    have h : Cut C.gates B.gates := cuts _ _ _
    have hk : j<B.gates.length := by omega
    rcases cutAt h j hj hk with eq|eq
    · exact False.elim (hc (by rwa [gateAt_eq hj,gateAt_eq hk]))
    · rwa [gateAt_eq hk]
  have fromB (x : Fin (N+N)→Bool) := compareAt B D (lenD.trans len.symm) mb x (by
    intro j hj ne on
    have hc : j<C.size := by omega
    by_cases same : gateAt C j=gateAt B j
    · exact False.elim (ne (kept j hc same).symm)
    · have hz := zero j hc same
      obtain ⟨i,mem,_,_⟩ := (val_or (by simp) hj (congrArg Gate.op hz)).mp on
      simp [hz,zeroGate] at mem)
  have toB (x : Fin (N+N)→Bool) (neg : ¬Positive I x) := plug_negative I C B port len safe md x neg
  have edges (p l : Fin N) (inc : I p l) : circuitFun (N+N) D (pairInput p l)=true := by
    cases h : circuitFun (N+N) B (pairInput p l) with
    | true => exact fromB _ C.output h
    | false =>
      obtain ⟨S,tr,supply⟩ := paths (p,l) ⟨inc,h⟩
      exact port_trace C B hm hb port valid _ S tr supply
  have down := (properties (N+N) (nonedges I) C hm hb).2.2.2.2.2
  have correct : spec I D := by
    intro x
    constructor
    · intro on
      by_contra neg
      exact neg ((co x).mp (down x (toB x neg C.output on)))
    · rintro ⟨p,l,pi,xp,xl⟩
      have le : LE (List.ofFn (pairInput p l)) (List.ofFn x) := by
        apply inputLE
        intro k on
        rcases (of_decide_eq_true on : k=pt p ∨ k=ln l) with rfl|rfl
        · exact xp
        · exact xl
      exact evalLE (sameCut D.gates) (fun g h=>by simpa using (md g h).1) _ _ (by simp) le D.output (edges p l pi)
  have clean (x : Fin (N+N)→Bool) (neg : ¬Positive I x)
      (orig : ∀ j<B.gates.length,(gateAt B j).op=.and → val B (List.ofFn x) (N+N+j)=false) :
      ∀ j<D.gates.length,(gateAt D j).op=.and → val D (List.ofFn x) (N+N+j)=false := by
    intro j hj op
    apply Bool.eq_false_iff.mpr
    intro hit
    have jc : j<C.size := by omega
    have block := toB x neg (N+N+j) hit
    by_cases eq : gateAt C j=gateAt B j
    · rw [kept j jc eq] at op
      exact Bool.false_ne_true ((orig j (by omega) op).symm.trans block)
    · have hz := zero j jc eq
      obtain ⟨i,mem,_,_⟩ := (val_or (by simp) (by omega) (congrArg Gate.op hz)).mp block
      simp [hz,zeroGate] at mem
  refine ⟨D,md,bd,lenD.le,correct,?_,?_⟩
  · intro j hj op p l no
    exact clean _ (nonpair_off I p l no) (fun t ht ot=>pb t ht ot p l no) j hj op
  · intro j hj op
    exact ⟨fun p=>clean _ (unit_off I (pt p)) (fun t ht ot=>(ub t ht ot).1 p) j hj op,
           fun l=>clean _ (unit_off I (ln l)) (fun t ht ot=>(ub t ht ot).2 l) j hj op⟩

end Repair3457
namespace Binary3457

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

end Binary3457

namespace Census3457

namespace ThetaAnd3241

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadK

theorem switchProgram5180 : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
    let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
        let a := w.getD (g.inputs.getD 0 0) ∅
        let b := w.getD (g.inputs.getD 1 0) ∅
        w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
        ((List.finRange n).map fun i => {i})).getD C.output ∅
    ∀ X : Finset (Fin n), circuitFun n C (setInput X) = false ↔ ∃ s, Disjoint (M s) X := by
  classical
  intro n C ao M X
  let hit (P : Finset (Fin n)) := decide (¬ Disjoint P X)
  let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
  let read (l : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => l.getD i false)
  let run (l : List Bool) (g : Gate) := l ++ [read l g]
  let select (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
    let a := w.getD (g.inputs.getD 0 0) ∅
    let b := w.getD (g.inputs.getD 1 0) ∅
    if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b
  let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) := w ++ [select s w g]
  have emptyHit : hit ∅ = false := by simp [hit]
  have hitUnion (a b : Finset (Fin n)) : hit (a ∪ b) = (hit a || hit b) := by
    by_cases ha : Disjoint a X <;> by_cases hb : Disjoint b X <;>
      simp [hit,ha,hb]
  have readMap (w : List (Finset (Fin n))) (i : ℕ) :
      (w.map hit).getD i false = hit (w.getD i ∅) := by
    induction w generalizing i with
    | nil => cases i <;> exact emptyHit.symm
    | cons a w ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  have snoc {α : Type} (l : List α) (d z : α) (i : ℕ) :
      (l ++ [d]).getD i z = if i = l.length then d else l.getD i z := by
    induction l generalizing i with
    | nil => cases i <;> rfl
    | cons x l ih => cases i with
      | zero => rfl
      | succ i => simpa using ih i
  let Shape (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ, g.inputs = [u,v]
  have gateShape (g : Gate) (hg : g ∈ C.gates) : Shape g := by
    have pair (l : List ℕ) (h : l.length = 2) : ∃ u v, l = [u,v] := by
      cases l with
      | nil => simp at h
      | cons u tl =>
        cases tl with
        | nil => simp at h
        | cons v tl =>
          have z : tl = [] := List.length_eq_zero_iff.mp (by simpa using h)
          exact ⟨u,v,by rw [z]⟩
    exact ⟨ao.1 g hg,pair g.inputs (ao.2.2 g hg)⟩
  have readAnd (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .and)
      (pins : g.inputs = [u,v]) : read l g = (l.getD u false && l.getD v false) := by
    simp only [read,kind,pins,List.map_cons,List.map_nil]
    cases l.getD u false <;> cases l.getD v false <;> rfl
  have readOr (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .or)
      (pins : g.inputs = [u,v]) : read l g = (l.getD u false || l.getD v false) := by
    simp only [read,kind,pins,List.map_cons,List.map_nil]
    cases l.getD u false <;> cases l.getD v false <;> rfl
  have selAnd (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
      (kind : g.op = .and) (pins : g.inputs = [u,v]) :
      select s w g = if s w.length then w.getD u ∅ else w.getD v ∅ := by
    simp only [select,kind,pins]
    rfl
  have selOr (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
      (kind : g.op = .or) (pins : g.inputs = [u,v]) :
      select s w g = w.getD u ∅ ∪ w.getD v ∅ := by
    simp only [select,kind,pins]
    rfl
  let Safe (l : List Bool) (w : List (Finset (Fin n))) :=
    ∀ i, hit (w.getD i ∅) = false → l.getD i false = false
  have sound (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (s : ℕ → Bool)
      (l : List Bool) (w : List (Finset (Fin n))) (len : l.length = w.length)
      (old : Safe l w) : Safe (gs.foldl run l) (gs.foldl (go s) w) := by
    induction gs generalizing l w with
    | nil => exact old
    | cons g gs ih =>
      obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
      have next : hit (select s w g) = false → read l g = false := by
        rcases kind with andG | orG
        · rw [readAnd l g u v andG pins,selAnd s w g u v andG pins]
          cases h : s w.length with
          | false =>
            intro off
            have f : hit (w.getD v ∅) = false := off
            rw [old v f,Bool.and_false]
          | true =>
            intro off
            have f : hit (w.getD u ∅) = false := off
            rw [old u f,Bool.false_and]
        · rw [readOr l g u v orG pins,selOr s w g u v orG pins,hitUnion]
          intro off
          have both : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by
            intro a b
            cases a <;> cases b <;> simp
          obtain ⟨fa,fb⟩ := both _ _ off
          rw [old u fa,old v fb]
          rfl
      apply ih (fun k hk => hg k (by simp [hk])) (run l g) (go s w g) (by simp [run,go,len])
      intro i
      change hit ((w ++ [select s w g]).getD i ∅) = false →
        (l ++ [read l g]).getD i false = false
      rw [snoc,snoc,len]
      by_cases atEnd : i = w.length
      · simpa only [ite_eq_left atEnd] using next
      · simpa only [ite_eq_right atEnd] using old i
  have future (gs : List Gate) (s t : ℕ → Bool) (w : List (Finset (Fin n)))
      (agree : ∀ j, w.length ≤ j → s j = t j) :
      gs.foldl (go s) w = gs.foldl (go t) w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have now : go s w g = go t w g := by simp only [go,select,agree w.length (le_refl _)]
      simp only [List.foldl_cons,now]
      apply ih
      intro j hj
      have a : w.length + 1 ≤ j := by simpa [go] using hj
      exact agree j (by omega)
  have realize (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (w : List (Finset (Fin n))) :
      ∃ s : ℕ → Bool, gs.foldl run (w.map hit) = (gs.foldl (go s) w).map hit := by
    induction gs generalizing w with
    | nil => exact ⟨fun _ => false,rfl⟩
    | cons g gs ih =>
      obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
      let side := !(hit (w.getD u ∅))
      let now : ℕ → Bool := fun _ => side
      have one : run (w.map hit) g = (go now w g).map hit := by
        change w.map hit ++ [read (w.map hit) g] = (w ++ [select now w g]).map hit
        rw [List.map_append]
        congr 1
        change [read (w.map hit) g] = [hit (select now w g)]
        rcases kind with andG | orG
        · rw [readAnd _ g u v andG pins,selAnd _ _ g u v andG pins,readMap,readMap]
          change [(hit (w.getD u ∅) && hit (w.getD v ∅))] =
            [hit (if !(hit (w.getD u ∅)) then w.getD u ∅ else w.getD v ∅)]
          cases e : hit (w.getD u ∅) <;> simp only [Bool.not_true,Bool.not_false,
            Bool.false_eq_true,ite_true,ite_false,e,Bool.false_and,Bool.true_and]
        · rw [readOr _ g u v orG pins,selOr _ _ g u v orG pins,hitUnion,readMap,readMap]
      obtain ⟨t,rest⟩ := ih (fun k hk => hg k (by simp [hk])) (go now w g)
      let s : ℕ → Bool := fun j => if j = w.length then side else t j
      have first : go s w g = go now w g := by simp only [go,select,s,now,ite_true]
      have tail : gs.foldl (go s) (go now w g) = gs.foldl (go t) (go now w g) := by
        apply future
        intro j hj
        have a : w.length + 1 ≤ j := by simpa [go] using hj
        simp only [s,ite_eq_right (show j ≠ w.length by omega)]
      refine ⟨s,?_⟩
      simp only [List.foldl_cons,one,first,tail]
      exact rest
  have initial : List.ofFn (setInput X) = seed.map hit := by
    change List.ofFn (setInput X) = ((List.finRange n).map fun i => ({i} : Finset (Fin n))).map hit
    rw [List.map_map]
    have finRange : List.finRange n = List.ofFn id := rfl
    rw [finRange,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change decide (i ∈ X) = hit {i}
    simp [hit]
  have hitZero (P : Finset (Fin n)) : hit P = false ↔ Disjoint P X := by
    simp [hit]
  change (C.gates.foldl run (List.ofFn (setInput X))).getD C.output false = false ↔
    ∃ s, Disjoint ((C.gates.foldl (go s) seed).getD C.output ∅) X
  rw [initial]
  constructor
  · intro rejected
    obtain ⟨s,eq⟩ := realize C.gates gateShape seed
    rw [eq,readMap] at rejected
    exact ⟨s,(hitZero _).mp rejected⟩
  · rintro ⟨s,h⟩
    have seedSafe : Safe (seed.map hit) seed := fun i => by rw [readMap]; exact id
    exact sound C.gates gateShape s (seed.map hit) seed (by simp) seedSafe C.output ((hitZero _).mpr h)

theorem switchCount5180 (n : ℕ) (C : Circuit) :
    let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
        let a := w.getD (g.inputs.getD 0 0) ∅
        let b := w.getD (g.inputs.getD 1 0) ∅
        w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
        ((List.finRange n).map fun i => {i})).getD C.output ∅
    ∃ F : Finset (Finset (Fin n)), (∀ s, M s ∈ F) ∧
      F.card ≤ 2 ^ (C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) := by
  classical
  intro M
  let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
    let a := w.getD (g.inputs.getD 0 0) ∅
    let b := w.getD (g.inputs.getD 1 0) ∅
    w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b]
  let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
  let fixed (gs : List Gate) := gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
  let free (gs : List Gate) := gs.countP (fun g => !(PEqualNP.SharedBlockCost.isOrOp g.op))
  have fixedCons (g : Gate) (gs : List Gate) :
      fixed (g::gs) = fixed gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 1 else 0) := by
    cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [fixed,eq]
  have freeCons (g : Gate) (gs : List Gate) :
      free (g::gs) = free gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 0 else 1) := by
    cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [free,eq]
  have total (gs : List Gate) : fixed gs + free gs = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rw [fixedCons,freeCons,List.length_cons]
      cases PEqualNP.SharedBlockCost.isOrOp g.op <;> simp <;> omega
  let yes : ℕ → Bool := fun _ => true
  let no : ℕ → Bool := fun _ => false
  have family (gs : List Gate) (w : List (Finset (Fin n))) :
      ∃ T : Finset (List (Finset (Fin n))), (∀ s, gs.foldl (go s) w ∈ T) ∧ T.card ≤ 2 ^ free gs := by
    induction gs generalizing w with
    | nil => exact ⟨{w},fun _ => Finset.mem_singleton_self _,by simp [free]⟩
    | cons g gs ih =>
      obtain ⟨Tno,hasNo,sizeNo⟩ := ih (go no w g)
      by_cases hg : PEqualNP.SharedBlockCost.isOrOp g.op = true
      · have same (s : ℕ → Bool) : go s w g = go no w g := by simp [go,hg]
        refine ⟨Tno,fun s => ?_,?_⟩
        · simpa only [List.foldl_cons,same s] using hasNo s
        · simpa only [freeCons,ite_eq_left hg,Nat.add_zero] using sizeNo
      · obtain ⟨Tyes,hasYes,sizeYes⟩ := ih (go yes w g)
        refine ⟨Tno ∪ Tyes,?_,?_⟩
        · intro s
          simp only [List.foldl_cons]
          cases hs : s w.length with
          | false =>
            have eq : go s w g = go no w g := by simp only [go,no,hs]
            rw [eq]
            exact Finset.mem_union_left _ (hasNo s)
          | true =>
            have eq : go s w g = go yes w g := by simp only [go,yes,hs]
            rw [eq]
            exact Finset.mem_union_right _ (hasYes s)
        · rw [freeCons,ite_eq_right hg,pow_succ]
          have limit := (Finset.card_union_le Tno Tyes).trans (Nat.add_le_add sizeNo sizeYes)
          omega
  obtain ⟨T,rep,bound⟩ := family C.gates seed
  let extract (w : List (Finset (Fin n))) := w.getD C.output ∅
  refine ⟨T.image extract,?_,?_⟩
  · intro s
    exact Finset.mem_image.mpr ⟨C.gates.foldl (go s) seed,rep s,rfl⟩
  · have eq : C.size - fixed C.gates = free C.gates := by
      have h := total C.gates
      change C.gates.length - fixed C.gates = free C.gates
      omega
    change (T.image extract).card ≤ 2 ^ (C.size - fixed C.gates)
    rw [eq]
    exact Finset.card_image_le.trans bound

theorem false_family_bound {n k : Nat} (C : Circuit) (ao : IsAO2 n C)
    (X : Fin k → Finset (Fin n))
    (no : ∀ i, circuitFun n C (setInput (X i)) = false)
    (cross : ∀ i j, i ≠ j → circuitFun n C (setInput (X i ∪ X j)) = true) :
    k ≤ 2 ^ (C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) := by
  classical
  let M (s : Nat → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
      ((List.finRange n).map fun i => {i})).getD C.output ∅
  obtain ⟨F, mem, size⟩ := switchCount5180 n C
  have exists_code (i : Fin k) : ∃ s, Disjoint (M s) (X i) :=
    (switchProgram5180 n C ao (X i)).mp (no i)
  choose sel avoids using exists_code
  let code (i : Fin k) : F := ⟨M (sel i), mem (sel i)⟩
  have inj : Function.Injective code := by
    intro i j h
    by_contra ne
    have same : M (sel i) = M (sel j) := congrArg Subtype.val h
    have other : Disjoint (M (sel i)) (X j) := same ▸ avoids j
    have together : Disjoint (M (sel i)) (X i ∪ X j) :=
      Finset.disjoint_union_right.mpr ⟨avoids i,other⟩
    have reject := (switchProgram5180 n C ao (X i ∪ X j)).mpr ⟨sel i,together⟩
    simp [cross i j ne] at reject
  have card : k ≤ F.card := by simpa using Fintype.card_le_of_injective code inj
  exact card.trans size

def thetaAdj (i j : Fin 4) : Bool := (13726 : Nat).testBit (4*i.val+j.val)

def theta (x : Fin 8 → Bool) : Bool :=
  decide (∃ i j : Fin 4, thetaAdj i j = true ∧
    x (Fin.castAdd 4 i) = true ∧ x (Fin.natAdd 4 j) = true)

def nine : Fin 9 → Finset (Fin 8) :=
  ![{0,1,2,3}, {0,4}, {1,2,5}, {1,3,6}, {1,5,6}, {2,3,7}, {2,5,7}, {3,6,7}, {4,5,6,7}]

theorem theta_and_count (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x) :
    4 ≤ C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) := by
  have no : ∀ i, theta (setInput (nine i)) = false := by decide +kernel
  have yes : ∀ i j, i ≠ j → theta (setInput (nine i ∪ nine j)) = true := by decide +kernel
  have bound := false_family_bound C ao nine (fun i => (correct _).trans (no i))
    (fun i j h => (correct _).trans (yes i j h))
  by_contra low
  have h : C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) ≤ 3 := by omega
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) h
  omega

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

theorem subtract_or_eq_and {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) =
      C.gates.countP andGate := by
  have total (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      gs.countP andGate + gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have tail := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      rcases ok g List.mem_cons_self with h | h
      · have a : andGate g = true := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = false := by rw [h]; rfl
        simp [a,o]
        omega
      · have a : andGate g = false := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = true := by rw [h]; rfl
        simp [a,o]
        omega
  have count := total C.gates ao.1
  unfold Circuit.size
  omega

theorem theta_four_and (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x) : 4 ≤ C.gates.countP andGate := by
  rw [← subtract_or_eq_and C ao]
  exact theta_and_count C ao correct

theorem theta_twelve_of_eight_or (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x)
    (or_lb : 8 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) :
    12 ≤ C.size := by
  have and_lb := theta_and_count C ao correct
  omega

end ThetaAnd3241

namespace ThetaPin3241

abbrev Signal (α : Type) := α → Bool
abbrev Gate (α : Type) := Signal α × Signal α

def join {α : Type} (a b : Signal α) : Signal α := fun x => a x || b x
def meet {α : Type} (a b : Signal α) : Signal α := fun x => a x && b x

def Free {α : Type} (B : Set (Signal α)) (a : Signal α) : Prop :=
  ∀ S : Set (Signal α), B ⊆ S → (fun _ => false) ∈ S → (fun _ => true) ∈ S →
    (∀ u ∈ S, ∀ v ∈ S, meet u v ∈ S) → a ∈ S

theorem atom {α : Type} {B : Set (Signal α)} {a : Signal α} (ha : a ∈ B) : Free B a :=
  fun _ h _ _ _ => h ha

theorem free_zero {α : Type} {B : Set (Signal α)} : Free B (fun _ => false) :=
  fun _ _ h _ _ => h

theorem free_one {α : Type} {B : Set (Signal α)} : Free B (fun _ => true) :=
  fun _ _ _ h _ => h

theorem free_meet {α : Type} {B : Set (Signal α)} {u v : Signal α} (hu : Free B u)
    (hv : Free B v) : Free B (meet u v) :=
  fun S incl h0 h1 hc => hc _ (hu S incl h0 h1 hc) _ (hv S incl h0 h1 hc)

theorem widen {α : Type} {B D : Set (Signal α)} {a : Signal α}
    (incl : B ⊆ D) (h : Free B a) : Free D a :=
  fun S incl' => h S (incl.trans incl')

theorem transport {α β : Type} (p : β → α) {B : Set (Signal α)} {D : Set (Signal β)}
    (base : ∀ a ∈ B, Free D (a ∘ p)) {a : Signal α} (ha : Free B a) : Free D (a ∘ p) := by
  apply ha {a | Free D (a ∘ p)}
  · exact base
  · exact free_zero
  · exact free_one
  · intro u hu v hv
    exact free_meet hu hv

theorem factors {α : Type} {B : Set (Signal α)} {f : Signal α} (ok : Free B f) :
    f = (fun _ => false) ∨ ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧
      f = (fun x => xs.all (fun a => a x)) := by
  let S : Set (Signal α) := {f | f = (fun _ => false) ∨
    ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧ f = (fun x => xs.all (fun a => a x))}
  apply ok S
  · intro a ha
    exact Or.inr ⟨[a],by simpa using ha,funext (fun x => by simp)⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨[],by simp,rfl⟩
  · intro a ha b hb
    rcases ha with rfl | ⟨xs,hh,rfl⟩
    · exact Or.inl rfl
    rcases hb with rfl | ⟨ys,ii,rfl⟩
    · exact Or.inl (funext (fun x => by simp [meet]))
    · refine Or.inr ⟨xs++ys,?_,?_⟩
      · intro u hu
        exact (List.mem_append.mp hu).elim (hh u) (ii u)
      · exact funext (fun x => by simp [meet])

theorem separating_factor {α : Type} {B : Set (Signal α)} {f : Signal α}
    (ok : Free B f) (P : Set α) (nonempty : P.Nonempty) (z : α)
    (yes : ∀ x ∈ P, f x = true) (no : f z = false) :
    ∃ a ∈ B, (∀ x ∈ P, a x = true) ∧ a z = false := by
  rcases factors ok with rfl | ⟨xs,inside,rfl⟩
  · obtain ⟨x,hx⟩ := nonempty
    exact False.elim (Bool.noConfusion (yes x hx))
  · obtain ⟨a,ha,bad⟩ := List.all_eq_false.mp no
    exact ⟨a,inside _ ha,fun x hx => List.all_eq_true.mp (yes x hx) a ha,by simpa using bad⟩

def Valid {α : Type} (B : Set (Signal α)) (gs : List (Gate α)) (f : Signal α) : Prop :=
  match gs with
  | [] => Free B f
  | g :: rest => Free B g.1 ∧ Free B g.2 ∧ Valid (insert (join g.1 g.2) B) rest f

def Pass {α : Type} (t e z : α) (f : Signal α) : Prop :=
  f t = true → f e = true → f z = true

theorem free_pass {α : Type} {B : Set (Signal α)} {t e z : α} {f : Signal α}
    (base : ∀ a ∈ B, Pass t e z a) (ok : Free B f) : Pass t e z f := by
  apply ok {a | Pass t e z a}
  · exact base
  · intro h; contradiction
  · intro _ _; rfl
  · intro u hu v hv ht he
    have ⟨tu,tv⟩ : u t = true ∧ v t = true := by simpa [meet] using ht
    have ⟨eu,ev⟩ : u e = true ∧ v e = true := by simpa [meet] using he
    simp [meet,hu tu eu,hv tv ev]

theorem critical_gate {α : Type} (gs : List (Gate α)) (B : Set (Signal α)) (f : Signal α)
    (t e z : α) (base : ∀ a ∈ B, Pass t e z a) (ok : Valid B gs f)
    (ft : f t = true) (fe : f e = true) (fz : f z = false) :
    ∃ g ∈ gs, (g.1 t = false ∨ g.2 t = false) ∧
      join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  classical
  induction gs generalizing B with
  | nil =>
    have impossible := free_pass base ok ft fe
    simp [fz] at impossible
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    by_cases passes : Pass t e z (join g.1 g.2)
    · have next : ∀ a ∈ insert (join g.1 g.2) B, Pass t e z a := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact passes
        · exact base _ h
      obtain ⟨m,hm,p⟩ := ih _ next tail
      exact ⟨m,List.mem_cons_of_mem _ hm,p⟩
    · have hp : join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧
          join g.1 g.2 z = false := by simpa [Pass] using passes
      refine ⟨g,List.mem_cons_self,?_,hp⟩
      by_contra no
      have both : g.1 t = true ∧ g.2 t = true := by simpa using no
      have either : g.1 e = true ∨ g.2 e = true := by simpa [join] using hp.2.1
      rcases either with h | h
      · have yes := free_pass base ha both.1 h
        have nz := hp.2.2
        simp [join,yes] at nz
      · have yes := free_pass base hb both.2 h
        have nz := hp.2.2
        simp [join,yes] at nz

def Killed {α β : Type} (p : β → α) (g : Gate α) : Prop :=
  (∀ x, g.1 (p x) = false) ∨ (∀ x, g.2 (p x) = false)

def deadAt {α : Type} (t : α) (g : Gate α) : Bool := !(g.1 t && g.2 t)

theorem count_one_unique {α : Type} (gs : List α) (p : α → Bool) (a b : α)
    (ha : a ∈ gs) (hb : b ∈ gs) (pa : p a = true) (pb : p b = true)
    (one : gs.countP p ≤ 1) : a = b := by
  rw [List.countP_eq_length_filter] at one
  have a' := List.mem_filter.mpr ⟨ha,pa⟩
  have b' := List.mem_filter.mpr ⟨hb,pb⟩
  cases h : gs.filter p with
  | nil => simp [h] at a'
  | cons c rest =>
    have numeric : rest.length+1 ≤ 1 := by simpa only [h,List.length_cons] using one
    have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h,nil] at a' b'
    exact a'.trans b'.symm

theorem single_charge_passes {α : Type} {B : Set (Signal α)} {gs : List (Gate α)}
    {f : Signal α} (ok : Valid B gs f) (g : Gate α) (hg : g ∈ gs) (t e z : α)
    (base : ∀ a ∈ B, Pass t e z a) (ft : f t = true) (fe : f e = true)
    (fz : f z = false) (dg : deadAt t g = true) (one : gs.countP (deadAt t) ≤ 1) :
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  obtain ⟨j,hj,charge,h⟩ := critical_gate gs B f t e z base ok ft fe fz
  have dj : deadAt t j = true := by simpa [deadAt] using charge
  exact (count_one_unique gs (deadAt t) j g hj hg dj dg one) ▸ h

theorem propagate_property {α : Type} (B S : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (incl : B ⊆ S) (ok : Valid B gs f)
    (stable : ∀ g ∈ gs, Free S g.1 → Free S g.2 → join g.1 g.2 ∈ S) :
    Free S f := by
  induction gs generalizing B with
  | nil => exact widen incl ok
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have mem := stable g List.mem_cons_self (widen incl ha) (widen incl hb)
    exact ih (insert (join g.1 g.2) B) (Set.insert_subset mem incl) tail
      (fun a h => stable a (List.mem_cons_of_mem _ h))

noncomputable def killedBit {α β : Type} (p : β → α) (g : Gate α) : Bool :=
  @decide (Killed p g) (Classical.propDecidable _)

theorem restrict_transfer {α β : Type} (p : β → α) (gs : List (Gate α))
    (B : Set (Signal α)) (D : Set (Signal β)) (f : Signal α)
    (base : ∀ a ∈ B, Free D (a ∘ p)) (ok : Valid B gs f) :
    ∃ out : List (Gate β), Valid D out (f ∘ p) ∧
      out.length + gs.countP (killedBit p) = gs.length := by
  classical
  induction gs generalizing B D with
  | nil => exact ⟨[], transport p base ok, rfl⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have left := transport p base ha
    have right := transport p base hb
    by_cases dead : Killed p g
    · have combined : Free D (join g.1 g.2 ∘ p) := by
        rcases dead with l | r
        · have e : join g.1 g.2 ∘ p = g.2 ∘ p := funext (fun x => by simp [join,l])
          exact e ▸ right
        · have e : join g.1 g.2 ∘ p = g.1 ∘ p := funext (fun x => by simp [join,r])
          exact e ▸ left
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free D (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact combined
        · exact base _ h
      obtain ⟨out,sem,cost⟩ := ih _ D next tail
      refine ⟨out,sem,?_⟩
      have k : killedBit p g = true := by simp [killedBit,dead]
      simp [k]
      omega
    · let new := join (g.1 ∘ p) (g.2 ∘ p)
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free (insert new D) (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact atom (Set.mem_insert _ _)
        · exact widen (Set.subset_insert _ _) (base _ h)
      obtain ⟨out,sem,cost⟩ := ih _ (insert new D) next tail
      refine ⟨(g.1 ∘ p,g.2 ∘ p)::out,⟨left,right,sem⟩,?_⟩
      have k : killedBit p g = false := by simp [killedBit,dead]
      simp [k]
      omega

abbrev PhysicalGate := PEqualNP.CircuitLowerBounds.Gate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wire {α : Type} (w : List (Signal α)) (i : Nat) : Signal α := w.getD i (fun _ => false)

def step {α : Type} (w : List (Signal α)) (g : PhysicalGate) : List (Signal α) :=
  w ++ [fun x => g.op.eval (g.inputs.map fun i => wire w i x)]

def pairShape (g : PhysicalGate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b]

theorem free_wire {α : Type} {B : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ a ∈ w, Free B a) (i : Nat) : Free B (wire w i) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_zero
  | cons a w ih =>
    cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

def isOr (g : PhysicalGate) : Bool := PEqualNP.SharedBlockCost.isOrOp g.op

theorem compress {α : Type} (gs : List PhysicalGate) (output : Nat) (w : List (Signal α))
    (B : Set (Signal α)) (hw : ∀ a ∈ w, Free B a) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (Gate α), Valid B ops (wire (gs.foldl step w) output) ∧
      ops.length = gs.countP isOr := by
  induction gs generalizing w B with
  | nil => exact ⟨[],free_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    rcases hop with kind | kind
    · have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have ext : ∀ a ∈ step w g, Free B a := by
        intro a ha
        rw [eq,List.mem_append,List.mem_singleton] at ha
        rcases ha with old | rfl
        · exact hw a old
        · exact free_meet (free_wire hw i) (free_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : isOr g = false := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simpa [no] using cost
    · let a := wire w i
      let b := wire w j
      let D := insert (join a b) B
      have eq : step w g = w ++ [join a b] := by
        simp [step,pins,kind,GateOp.eval,a,b]
        rfl
      have ext : ∀ v ∈ step w g, Free D v := by
        intro v hv
        rw [eq,List.mem_append,List.mem_singleton] at hv
        rcases hv with old | rfl
        · exact widen (Set.subset_insert _ _) (hw v old)
        · exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨free_wire hw i,free_wire hw j,sem⟩,?_⟩
      have yes : isOr g = true := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simp [cost,yes]

theorem wire_point {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = wire w i x := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons f fs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem run_point {α : Type} (gs : List PhysicalGate) (w : List (Signal α)) (x : α) :
    (gs.foldl step w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    simp only [step,List.map_append,List.map_cons,List.map_nil,wire_point]

def inputs (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (fun (i : Fin n) x => x i)

def topMiss {n : Nat} (v : Fin n) (i : Fin n) : Bool := decide (i ≠ v)

theorem pass_inputs {n : Nat} (t e z : Fin n → Bool)
    (h : ∀ i, t i = true → e i = true → z i = true) : ∀ a ∈ inputs n, Pass t e z a := by
  rintro a ⟨i,rfl⟩
  exact h i

theorem one_charge {n : Nat} {gs f} (ok : Valid (inputs n) gs f)
    (v : Fin n) (e z : Fin n → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false) :
    1 ≤ gs.countP (deadAt (topMiss v)) := by
  obtain ⟨j,hj,hk,_⟩ := critical_gate gs (inputs n) f (topMiss v) e z
    (pass_inputs _ _ _ h) ok ft fe fz
  exact List.countP_pos_iff.mpr ⟨j,hj,by simpa [deadAt] using hk⟩

def Admissible {α : Type} (B : Set (Signal α)) (f : Signal α) (t : α) (g : Gate α) : Prop :=
  ∀ e z, (∀ a ∈ B, Pass t e z a) → f t = true → f e = true → f z = false →
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false

theorem double_from_classifier {n : Nat} (low : Set (Fin n)) (f : Signal (Fin n → Bool))
    (S : Set (Signal (Fin n → Bool))) (inc : inputs n ⊆ S) (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S)
    (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ v ∈ low, 2 ≤ gs.countP (deadAt (topMiss v)) := by
  classical
  by_contra no
  apply nonfree
  apply propagate_property (inputs n) S gs f inc ok
  intro g hg ha hb
  apply classify g ha hb
  intro v hv dg e z raw ft fe fz
  have small : gs.countP (deadAt (topMiss v)) ≤ 1 := by
    by_contra h
    exact no ⟨v,hv,by omega⟩
  exact single_charge_passes ok g hg (topMiss v) e z raw ft fe fz dg small

def Increasing {n : Nat} (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem free_increasing {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {a} (ha : Free B a) : Increasing a := by
  apply ha {v | Increasing v}
  · exact base
  · intro _ _ _ h; contradiction
  · intro _ _ _ _; rfl
  · intro u hu v hv x y le hx
    obtain ⟨lu,lv⟩ : u x = true ∧ v x = true := by simpa [meet] using hx
    simp [meet,hu x y le lu,hv x y le lv]

theorem active_monotone {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) :
    ∀ g ∈ gs, Increasing g.1 ∧ Increasing g.2 := by
  induction gs generalizing B with
  | nil => simp
  | cons h gs ih =>
    obtain ⟨left,right,tail⟩ := ok
    have l := free_increasing base left
    have r := free_increasing base right
    have next : ∀ a ∈ insert (join h.1 h.2) B, Increasing a := by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · intro x y le hx
        have one : h.1 x = true ∨ h.2 x = true := by simpa [join] using hx
        rcases one with p | p
        · simp [join,l x y le p]
        · simp [join,r x y le p]
      · exact base _ old
    intro g hg
    rcases List.mem_cons.mp hg with rfl | later
    · exact ⟨l,r⟩
    · exact ih next tail _ later

def pin {n : Nat} (v : Fin (n+1)) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  v.insertNth false x

theorem pin_raw {n : Nat} (v : Fin (n+1)) :
    ∀ a ∈ inputs (n+1), Free (inputs n) (a ∘ pin v) := by
  rintro a ⟨i,rfl⟩
  refine v.succAboveCases ?_ (fun j => ?_) i
  · have eq : (fun t : Fin (n+1) → Bool => t v) ∘ pin v = (fun _ => false) :=
      funext (fun x => by simp [pin])
    exact eq ▸ free_zero
  · have eq : (fun t : Fin (n+1) → Bool => t (v.succAbove j)) ∘ pin v = (fun x => x j) :=
      funext (fun x => by simp [pin])
    exact eq ▸ atom ⟨j,rfl⟩

theorem delete_charge {n : Nat} {gs f} (ok : Valid (inputs (n+1)) gs f) (v : Fin (n+1)) :
    ∃ out, Valid (inputs n) out (f ∘ pin v) ∧
      out.length + gs.countP (deadAt (topMiss v)) ≤ gs.length := by
  obtain ⟨out,sem,cost⟩ := restrict_transfer (pin v) gs _ _ f (pin_raw v) ok
  refine ⟨out,sem,?_⟩
  have base : ∀ a ∈ inputs (n+1), Increasing a := by
    rintro a ⟨i,rfl⟩ x y le hx
    exact le i hx
  have zero {a : Signal (Fin (n+1) → Bool)} (inc : Increasing a) (ha : a (topMiss v) = false) :
      ∀ x, a (pin v x) = false := by
    intro x
    cases h : a (pin v x) with
    | false => rfl
    | true =>
      have le : ∀ i, pin v x i = true → topMiss v i = true := by
        intro i
        by_cases hi : i = v
        · subst i; simp [pin]
        · simp [topMiss,hi]
      simp [inc _ _ le h] at ha
  have keep (g) (hg : g ∈ gs) (h : deadAt (topMiss v) g = true) : killedBit (pin v) g = true := by
    obtain ⟨l,r⟩ := active_monotone base ok _ hg
    have either : g.1 (topMiss v) = false ∨ g.2 (topMiss v) = false := by simpa [deadAt] using h
    have killed : Killed (pin v) g := either.imp (zero l) (zero r)
    simp [killedBit,killed]
  have count : gs.countP (deadAt (topMiss v)) ≤ gs.countP (killedBit (pin v)) :=
    List.countP_mono_left keep
  omega

theorem of_circuit {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∃ ops : List (Gate (Fin n → Bool)), Valid (inputs n) ops (circuitFun n C) ∧
      ops.length = C.gates.countP isOr := by
  let w : List (Signal (Fin n → Bool)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) a := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact atom ⟨i,rfl⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := compress C.gates C.output w (inputs n) ok shapes
  refine ⟨ops,?_,cost⟩
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  exact eq ▸ sem

def Lower {n : Nat} (f : Signal (Fin n → Bool)) (k : Nat) : Prop :=
  ∀ ops, Valid (inputs n) ops f → k ≤ ops.length

theorem lower_zero {n : Nat} (f : Signal (Fin n → Bool)) : Lower f 0 :=
  fun _ _ => Nat.zero_le _

theorem lower_one_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (v : Fin (n+1)) (e z : Fin (n+1) → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false)
    (rec : Lower (f ∘ pin v) k) : Lower f (k+1) := by
  intro gs ok
  have saved := one_charge ok v e z h ft fe fz
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec out sem
  omega

theorem lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool)) (low : Set (Fin (n+1)))
    (S : Set (Signal (Fin (n+1) → Bool))) (inc : inputs (n+1) ⊆ S)
    (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  intro gs ok
  obtain ⟨v,mem,saved⟩ := double_from_classifier low f S inc nonfree classify gs ok
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec v mem out sem
  omega

theorem lower_circuit {n k : Nat} {f : Signal (Fin n → Bool)} (lb : Lower f k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP isOr := by
  obtain ⟨ops,sem,cost⟩ := of_circuit C ao
  exact cost ▸ lb ops (correct ▸ sem)

theorem lower_transport {m n k : Nat} {f : Signal (Fin n → Bool)}
    (p : (Fin m → Bool) → (Fin n → Bool))
    (raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (sub : Lower (f ∘ p) k) : Lower f k := by
  intro gs ok
  obtain ⟨out,sem,budget⟩ := restrict_transfer p gs (inputs n) (inputs m) f raw ok
  have bound := sub out sem
  omega

theorem lower_rename {m n k : Nat} {f : Signal (Fin n → Bool)} (r : Fin n → Fin m)
    (sub : Lower (fun x => f (x ∘ r)) k) : Lower f k := by
  apply lower_transport (fun x => x ∘ r) _ sub
  rintro a ⟨i,rfl⟩
  exact atom ⟨r i,rfl⟩

end ThetaPin3241

namespace ThetaCores3241
open ThetaPin3241

def row {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val
def path2 (x : Fin 2 → Bool) : Bool := (x 0 && x 1)
def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def path5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
def cycle6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def pendant7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6)

def low : Set (Fin 8) := {v | v ≠ 0 ∧ v ≠ 4}

theorem path2_lower : Lower path2 0 := lower_zero path2

theorem path3_from_core (rec : Lower path2 0) : Lower path3 1 := by
  have eq : path3 ∘ pin (2 : Fin 3) = path2 := by
    funext x
    exact (by decide +kernel : ∀ y, path3 (pin (2 : Fin 3) y) = path2 y) x
  apply lower_one_step path3 2 (row 6) (row 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path4_from_core (rec : Lower path3 1) : Lower path4 2 := by
  have eq : path4 ∘ pin (3 : Fin 4) = path3 := by
    funext x
    exact (by decide +kernel : ∀ y, path4 (pin (3 : Fin 4) y) = path3 y) x
  apply lower_one_step path4 3 (row 12) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_from_core (rec : Lower path4 2) : Lower path5 3 := by
  have eq : path5 ∘ pin (4 : Fin 5) = path4 := by
    funext x
    exact (by decide +kernel : ∀ y, path5 (pin (4 : Fin 5) y) = path4 y) x
  apply lower_one_step path5 4 (row 24) (row 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_lower : Lower path5 3 := path5_from_core (path4_from_core (path3_from_core path2_lower))

theorem pendant7_from_core (rec : Lower cycle6 5) : Lower pendant7 6 := by
  have eq : pendant7 ∘ pin (6 : Fin 7) = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, pendant7 (pin (6 : Fin 7) y) = cycle6 y) x
  apply lower_one_step pendant7 6 (row 65) (row 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRename : Fin 6 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,4,3,2,1],![1,0,4,3,2],![2,1,0,4,3],![1,2,3,4,0],![0,1,2,3,4]]

theorem cycle6_deleted (v : Fin 6) : Lower (cycle6 ∘ pin v) 3 := by
  have all : ∀ i x, (cycle6 ∘ pin i) (x ∘ cycleRename i) = path5 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle6 ∘ pin v) (x ∘ cycleRename v)) = path5 := funext (all v)
  exact eq.symm ▸ path5_lower

def thetaRename : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,2,4,3,5,1,6],![0,2,4,3,5,6,1],![0,2,4,3,6,5,1],![0,1,2,3,4,5,6],![3,1,5,6,0,4,2],![3,1,6,5,0,4,2],![3,6,1,5,0,4,2]]

theorem theta_deleted (rec : Lower cycle6 5) (v : Fin 8) (hv : v ∈ low) :
    Lower (ThetaAnd3241.theta ∘ pin v) 6 := by
  have all : ∀ i : Fin 8, i ≠ 0 ∧ i ≠ 4 → ∀ x,
      (ThetaAnd3241.theta ∘ pin i) (x ∘ thetaRename i) = pendant7 x := by
    decide +kernel
  apply lower_rename (thetaRename v)
  have eq : (fun x => (ThetaAnd3241.theta ∘ pin v) (x ∘ thetaRename v)) = pendant7 :=
    funext (all v hv)
  exact eq.symm ▸ pendant7_from_core rec

def Classifier {n : Nat} (f : Signal (Fin n → Bool)) (L : Set (Fin n))
    (S : Set (Signal (Fin n → Bool))) : Prop :=
  inputs n ⊆ S ∧ ¬ Free S f ∧
    ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ L, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S

theorem cycle6_of_classifier {S} (h : Classifier cycle6 Set.univ S) : Lower cycle6 5 :=
  lower_two_step cycle6 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle6_deleted v)

theorem theta_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) : Lower ThetaAnd3241.theta 8 :=
  lower_two_step ThetaAnd3241.theta low T th.1 th.2.1 th.2.2
    (theta_deleted (cycle6_of_classifier cycle))

theorem total_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ao : PEqualNP.TopForm.IsAO2 8 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 8 C x = ThetaAnd3241.theta x) : 12 ≤ C.size :=
  ThetaAnd3241.theta_twelve_of_eight_or C ao sem
    (lower_circuit (theta_of_classifiers cycle th) C ao (funext sem))

end ThetaCores3241

namespace ThetaClass3241
open ThetaPin3241

abbrev X (n : Nat) := Fin n → Bool
abbrev Sig (n : Nat) := Signal (X n)
def raw {n} (v : Fin n) : Sig n := fun x => x v
def bits {n} (s : Finset (Fin n)) : X n := fun i => decide (i ∈ s)

def High {n} (H : Finset (Fin n)) (a : Sig n) : Prop :=
  Monotone a ∧ ∀ x y : X n, (∀ i ∈ H, x i = y i) → a x = a y
def pool {n} (H : Finset (Fin n)) : Set (Sig n) :=
  {a | High H a ∨ ∃ i ∉ H, a = raw i}

theorem base_subset {n} (H : Finset (Fin n)) : inputs n ⊆ pool H := by
  rintro _ ⟨i,rfl⟩
  by_cases hi : i ∈ H
  · exact Or.inl ⟨fun _ _ h => h i, fun _ _ h => h i hi⟩
  · exact Or.inr ⟨i,hi,rfl⟩

theorem high_const {n} (H : Finset (Fin n)) (b : Bool) : High H (fun _ => b) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩

theorem high_join {n} {H : Finset (Fin n)} {a b : Sig n} (ha : High H a) (hb : High H b) :
    High H (join a b) := by
  constructor
  · intro x y xy
    exact sup_le_sup (ha.1 xy) (hb.1 xy)
  · intro x y h
    simp only [join,ha.2 x y h,hb.2 x y h]

theorem high_all {n} (H : Finset (Fin n)) (xs : List (Sig n))
    (hx : ∀ a ∈ xs, High H a) : High H (fun x => xs.all (fun a => a x)) := by
  induction xs with
  | nil => exact high_const H true
  | cons a xs ih =>
    have ha := hx a List.mem_cons_self
    have ht := ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))
    constructor
    · intro x y xy
      exact inf_le_inf (ha.1 xy) (ht.1 xy)
    · intro x y eq
      simp only [List.all_cons, ha.2 x y eq, ht.2 x y eq]

theorem high_or_dead {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a) :
    High H a ∨ ∃ v ∉ H, a (topMiss v) = false := by
  classical
  by_contra! bad
  obtain ⟨notHigh,live⟩ := bad
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · exact notHigh (high_const _ _)
  apply notHigh (high_all H xs ?_)
  intro f hf
  rcases hxs f hf with h | ⟨v,hv,rfl⟩
  · exact h
  · have alive : xs.all (fun g => g (topMiss v)) = true := by simpa using live v hv
    have one := List.all_eq_true.mp alive (raw v) hf
    simp [raw,topMiss] at one

theorem arm_invariant {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v : Fin n} (low : v ∉ H) (alive : a (topMiss v) = true)
    (x y : X n) (same : ∀ i, i ≠ v → x i = y i) : a x = a y := by
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · rfl
  have equal (f : Sig n) (hf : f ∈ xs) : f x = f y := by
    rcases hxs f hf with h | ⟨i,_,rfl⟩
    · exact h.2 x y (fun j hj => same j (fun eq => low (eq ▸ hj)))
    · have val := List.all_eq_true.mp alive (raw i) hf
      exact same i (by simpa [raw,topMiss] using val)
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun all f hf => equal f hf ▸ all f hf, fun all f hf => (equal f hf).symm ▸ all f hf⟩

theorem forced_raw {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v u w : Fin n} (low : v ∉ H) (ulow : u ∉ H) (diff : u ≠ w)
    (dead : a (topMiss v) = false)
    (e1 : a (bits {v,u}) = true) (e2 : a (bits {v,w}) = true) : a = raw v := by
  classical
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · contradiction
  have classify (z : Sig n) (hz : z ∈ xs) : z = (fun _ => true) ∨ z = raw v := by
    have first := List.all_eq_true.mp e1 z hz
    have second := List.all_eq_true.mp e2 z hz
    rcases hxs z hz with high | ⟨i,_,rfl⟩
    · left
      have atZero : z (fun _ => false) = true := by
        rw [← first]
        apply high.2
        intro i hi
        have iv : i ≠ v := fun eq => low (eq ▸ hi)
        have iu : i ≠ u := fun eq => ulow (eq ▸ hi)
        simp [bits,iv,iu]
      funext x
      have le := high.1 (show (fun _ : Fin n => false) ≤ x from fun _ => bot_le)
      exact Bool.eq_true_of_true_le (atZero ▸ le)
    · right
      have h1 : i = v ∨ i = u := by simpa [raw,bits] using first
      have h2 : i = v ∨ i = w := by simpa [raw,bits] using second
      have eq : i = v := by grind
      rw [eq]
  have contains : raw v ∈ xs := by
    by_contra hn
    have t : xs.all (fun a => a (topMiss v)) = true := List.all_eq_true.mpr (by
      intro z hz
      rcases classify z hz with rfl | rfl
      · rfl
      · contradiction)
    simp [t] at dead
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro all
    exact List.all_eq_true.mp all _ contains
  · intro hv
    apply List.all_eq_true.mpr
    intro z hz
    rcases classify z hz with rfl | rfl
    · rfl
    · exact hv

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241

structure Geometry {n : Nat} (H : Finset (Fin n)) (f : Sig n) : Prop where
  surviving : ∀ v ∉ H, f (topMiss v) = true
  singleton_false : ∀ u, f (bits {u}) = false
  neighbors : ∀ v ∉ H, ∃ u w, u ∉ H ∧ u ≠ w ∧
    f (bits {v,u}) = true ∧ f (bits {v,w}) = true
  poles : ∀ v ∉ H, ∃ u, f (bits {v,u}) = true ∧ f (bits (insert u H)) = false
  twins : ∀ v ∉ H, ∀ w ∉ H, v ≠ w → ∃ u, f (bits {v,u}) = true ∧ f (bits {u,w}) = false

def Checks {n} (H : Finset (Fin n)) (f a b : Sig n) : Prop := ∀ v ∉ H,
  deadAt (topMiss v) (a,b) = true → Admissible (inputs n) f (topMiss v) (a,b)

theorem checks_swap {n} {H : Finset (Fin n)} {f a b : Sig n} (c : Checks H f a b) :
    Checks H f b a := by
  intro v hv hd e z pass ft fe fz
  have h := c v hv (by simpa [deadAt,Bool.and_comm] using hd) e z pass ft fe fz
  simpa only [join,Bool.or_comm] using h

theorem probe {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    {v u : Fin n} (hv : v ∉ H) (c : Checks H f a b) (dead : a (topMiss v) = false)
    (z : Finset (Fin n)) (inside : u ∈ z) (fe : f (bits {v,u}) = true) (fz : f (bits z) = false) :
    join a b (topMiss v) = true ∧ join a b (bits {v,u}) = true ∧ join a b (bits z) = false := by
  apply c v hv (by simp [deadAt,dead]) _ _ _ (geo.surviving v hv) fe fz
  apply pass_inputs
  intro i ti ei
  have ne : i ≠ v := by simpa [topMiss] using ti
  have eq : i = u := by simpa [bits,ne] using ei
  simpa [bits,eq] using inside

theorem collapse {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : a = raw v := by
  obtain ⟨u,w,lu,ne,eu,ew⟩ := geo.neighbors v hv
  have activate (i : Fin n) (e : f (bits {v,i}) = true) : a (bits {v,i}) = true := by
    obtain ⟨st,se,sz⟩ := probe geo hv c dead {i} (by simp) e (geo.singleton_false i)
    have live : b (topMiss v) = true := by simpa [join,dead] using st
    have same := arm_invariant hb hv live (bits {v,i}) (bits {i}) (fun j hj => by simp [bits,hj])
    have bz : b (bits {i}) = false := (Bool.or_eq_false_iff.mp sz).2
    simpa [join,same,bz] using se
  exact forced_raw ha hv lu ne dead (activate u eu) (activate w ew)

theorem reject_side {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : False := by
  have av := collapse geo ha hb c hv dead
  rcases high_or_dead hb with high | ⟨w,hw,dw⟩
  · obtain ⟨u,eu,zu⟩ := geo.poles v hv
    obtain ⟨st,_,sz⟩ := probe geo hv c dead (insert u H) (by simp) eu zu
    have bt : b (topMiss v) = true := by simpa [join,dead] using st
    have bz : b (bits (insert u H)) = false := (Bool.or_eq_false_iff.mp sz).2
    have eq := high.2 (topMiss v) (bits (insert u H)) (fun i hi => by
      have ne : i ≠ v := fun e => hv (e ▸ hi)
      simp [topMiss,bits,ne,hi])
    simp [bt,bz] at eq
  · have bw := collapse geo hb ha (checks_swap c) hw dw
    have ne : v ≠ w := by
      rintro rfl
      obtain ⟨u,_,_,_,eu,_⟩ := geo.neighbors v hv
      have st := (probe geo hv c dead {u} (by simp) eu (geo.singleton_false u)).1
      simp [join,dead,dw] at st
    obtain ⟨u,eu,zu⟩ := geo.twins v hv w hw ne
    have sz := (probe geo hv c dead {u,w} (by simp) eu zu).2.2
    simp [join,bw,raw,bits] at sz

theorem classify {n} {H : Finset (Fin n)} {f : Sig n} (geo : Geometry H f)
    (g : Gate (X n)) (ha : Free (pool H) g.1) (hb : Free (pool H) g.2)
    (c : ∀ v ∈ {v | v ∉ H}, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) :
    join g.1 g.2 ∈ pool H := by
  have ck : Checks H f g.1 g.2 := c
  rcases high_or_dead ha with aa | ⟨v,hv,dead⟩
  · rcases high_or_dead hb with bb | ⟨v,hv,dead⟩
    · exact Or.inl (high_join aa bb)
    · exact (reject_side geo hb ha (checks_swap ck) hv dead).elim
  · exact (reject_side geo ha hb ck hv dead).elim

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241 ThetaCores3241

theorem nonfree {n} (f : Sig n) (H : Finset (Fin n)) (x y z : X n)
    (hhigh : ∀ i ∈ H, x i = z i) (draw : ∀ i, x i = true → y i = true → z i = true)
    (fx : f x = true) (fy : f y = true) (fz : f z = false) : ¬ Free (pool H) f := by
  intro ok
  have base : ∀ a ∈ pool H, Pass x y z a := by
    intro a ha
    rcases ha with h | ⟨i,_,rfl⟩
    · intro ax _
      exact (h.2 x z hhigh) ▸ ax
    · exact draw i
  have pos := free_pass base ok fx fy
  simp [fz] at pos

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cycle_geo : Geometry ∅ cycle6 := by constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem theta_geo : Geometry {0,4} ThetaAnd3241.theta := by constructor <;> decide +kernel

theorem cycle_classifier : Classifier cycle6 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle6 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem theta_classifier : Classifier ThetaAnd3241.theta low (pool {0,4}) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree ThetaAnd3241.theta {0,4} (bits {1,7}) (bits {2,6}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    apply classify theta_geo g a b
    intro v hv
    apply h v
    simpa [low,Set.mem_ofPred_eq,not_or] using hv

theorem theta_total (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 8 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 8 C x = ThetaAnd3241.theta x) : 12 ≤ C.size :=
  total_of_classifiers cycle_classifier theta_classifier C ao sem

end ThetaClass3241

namespace ThetaPrune3241
open ThetaPin3241

def Private {α : Type} (P : Set α) (g : Gate α) : Prop :=
  (∃ e ∈ P, g.1 e = true ∧ g.2 e = false) ∧
  (∃ e ∈ P, g.2 e = true ∧ g.1 e = false)

def Refines {α : Type} (P : Set α) (new old : Signal α) : Prop :=
  (∀ e ∈ P, new e = old e) ∧ (∀ x, new x = true → old x = true)

theorem self_refines {α : Type} (P : Set α) (f : Signal α) : Refines P f f :=
  ⟨fun _ _ => rfl,fun _ h => h⟩

theorem ref_meet {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (meet a c) (meet b d) := by
  constructor
  · intro e he
    simp [meet,h.1 e he,i.1 e he]
  · intro x hx
    obtain ⟨hx,hy⟩ : a x = true ∧ c x = true := by simpa [meet] using hx
    simp [meet,h.2 x hx,i.2 x hy]

theorem ref_join {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (join a c) (join b d) := by
  constructor
  · intro e he
    simp [join,h.1 e he,i.1 e he]
  · intro x hx
    have one : a x = true ∨ c x = true := by simpa [join] using hx
    rcases one with p | p
    · simp [join,h.2 x p]
    · simp [join,i.2 x p]

theorem ref_comp {α : Type} {P : Set α} {a b c : Signal α}
    (h : Refines P a b) (i : Refines P b c) : Refines P a c :=
  ⟨fun e he => (h.1 e he).trans (i.1 e he),fun x p => i.2 x (h.2 x p)⟩

theorem refine_free {α : Type} (P : Set α) {B D : Set (Signal α)}
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) {a} (ok : Free B a) :
    ∃ b, Free D b ∧ Refines P b a := by
  apply ok {a | ∃ b, Free D b ∧ Refines P b a}
  · exact base
  · exact ⟨_,free_zero,self_refines _ _⟩
  · exact ⟨_,free_one,self_refines _ _⟩
  · intro a ha b hb
    obtain ⟨c,hc,rc⟩ := ha
    obtain ⟨d,hd,rd⟩ := hb
    exact ⟨meet c d,free_meet hc hd,ref_meet rc rd⟩

theorem choose_arm {α : Type} {P : Set α} {g : Gate α} (bad : ¬ Private P g) :
    ∃ u, (u = g.1 ∨ u = g.2) ∧ Refines P u (join g.1 g.2) := by
  classical
  by_cases left : ∃ e ∈ P, g.1 e = true ∧ g.2 e = false
  · have right : ¬∃ e ∈ P, g.2 e = true ∧ g.1 e = false := fun h => bad ⟨left,h⟩
    refine ⟨g.1,Or.inl rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact right ⟨e,he,b,a⟩
  · refine ⟨g.2,Or.inr rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact left ⟨e,he,a,b⟩

theorem prune {α : Type} (P : Set α) (B D : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) (ok : Valid B gs f) :
    ∃ out f', Valid D out f' ∧ Refines P f' f ∧ out.length ≤ gs.length ∧
      ∀ g ∈ out, Private P g := by
  classical
  induction gs generalizing B D with
  | nil =>
    obtain ⟨f',h,r⟩ := refine_free P base ok
    exact ⟨[],f',h,r,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    obtain ⟨a,fa,ra⟩ := refine_free P base ha
    obtain ⟨b,fb,rb⟩ := refine_free P base hb
    have combined := ref_join ra rb
    by_cases use : Private P (a,b)
    · let D' := insert (join a b) D
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D' w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨join a b, atom (Set.mem_insert _ _), combined⟩
        · obtain ⟨w,hw,hv⟩ := base _ old
          exact ⟨w,widen (Set.subset_insert _ _) hw,hv⟩
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D' next tail
      refine ⟨(a,b)::out,f',⟨fa,fb,sem⟩,r,by simpa using cost,?_⟩
      intro u hu
      exact (List.mem_cons.mp hu).elim (fun h => h ▸ use) (all u)
    · obtain ⟨u,side,ref⟩ := choose_arm use
      have fu : Free D u := side.elim (fun h => h ▸ fa) (fun h => h ▸ fb)
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨u,fu,ref_comp ref combined⟩
        · exact base _ old
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D next tail
      exact ⟨out,f',sem,r,by simp; omega,all⟩

theorem increasing_output {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) : Increasing f := by
  induction gs generalizing B with
  | nil => exact free_increasing base ok
  | cons g gs ih =>
    obtain ⟨l,r,tail⟩ := ok
    apply ih _ tail
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | old
    · intro x y le hx
      have either : g.1 x = true ∨ g.2 x = true := by simpa [join] using hx
      rcases either with h | h
      · simp [join,free_increasing base l x y le h]
      · simp [join,free_increasing base r x y le h]
    · exact base _ old

def Generates {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x, f x = true → ∃ e ∈ P, f e = true ∧ ∀ i, e i = true → x i = true

theorem private_program {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool))
    (cover : Generates P f) (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ out, Valid (inputs n) out f ∧ out.length ≤ gs.length ∧ ∀ g ∈ out, Private P g := by
  have ids : ∀ a ∈ inputs n, ∃ b, Free (inputs n) b ∧ Refines P b a :=
    fun a h => ⟨a,atom h,self_refines _ _⟩
  obtain ⟨out,v,sem,ref,cost,all⟩ := prune P _ _ gs f ids ok
  have mon := increasing_output (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) sem
  have eq : v = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨ref.2 x,?_⟩
    intro h
    obtain ⟨e,pe,pos,le⟩ := cover x h
    exact mon e x le ((ref.1 e pe).trans pos)
  exact ⟨out,eq ▸ sem,cost,all⟩

theorem private_lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (low : Set (Fin (n+1))) (S : Set (Signal (Fin (n+1) → Bool))) (P : Set (Fin (n+1) → Bool))
    (inc : inputs (n+1) ⊆ S) (nonfree : ¬ Free S f) (cover : Generates P f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  classical
  intro gs ok
  obtain ⟨out,sem,short,priv⟩ := private_program P f cover gs ok
  have hit : ∃ v ∈ low, 2 ≤ out.countP (deadAt (topMiss v)) := by
    by_contra no
    apply nonfree
    apply propagate_property (inputs _) S out f inc sem
    intro g hg a b
    apply classify g a b (priv g hg)
    intro v hv dg e z raw ft fe fz
    have small : out.countP (deadAt (topMiss v)) ≤ 1 := by
      by_contra h
      exact no ⟨v,hv,by omega⟩
    exact single_charge_passes sem g hg (topMiss v) e z raw ft fe fz dg small
  obtain ⟨v,hv,charge⟩ := hit
  obtain ⟨sub,sok,cost⟩ := delete_charge sem v
  have lb := rec v hv sub sok
  omega

end ThetaPrune3241

namespace Theta244Cores
open ThetaPin3241 ThetaCores3241 ThetaPrune3241
def path6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)
def path7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def cycle8 (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 0)
def twoEnds (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 2 && x 7)
def tailTwo (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 6 && x 7)
def theta (x : Fin 9 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)

theorem path6_lower (rec : Lower path5 3) : Lower path6 4 := by
  have eq : path6 ∘ pin (5 : Fin 6) = path5 := by
    funext x
    exact (by decide +kernel : ∀ y, path6 (pin (5 : Fin 6) y) = path5 y) x
  apply lower_one_step path6 5 (row 48) (row 16)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path7_lower (rec : Lower path6 4) : Lower path7 5 := by
  have eq : path7 ∘ pin (6 : Fin 7) = path6 := by
    funext x
    exact (by decide +kernel : ∀ y, path7 (pin (6 : Fin 7) y) = path6 y) x
  apply lower_one_step path7 6 (row 96) (row 32)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem twoEnds_lower (rec : Lower pendant7 6) : Lower twoEnds 7 := by
  have eq : twoEnds ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, twoEnds (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step twoEnds 7 (row 132) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem tailTwo_lower (rec : Lower pendant7 6) : Lower tailTwo 7 := by
  have eq : tailTwo ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, tailTwo (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step tailTwo 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRelabel : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,6,5,4,3,2,1],![1,0,6,5,4,3,2],![2,1,0,6,5,4,3],![3,2,1,0,6,5,4],![2,3,4,5,6,0,1],![1,2,3,4,5,6,0],![0,1,2,3,4,5,6]]
def thetaRelabel : Fin 9 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,4,1,2,3,7,6,5],![2,0,1,7,6,3,4,5],![0,2,1,6,7,5,4,3],![0,2,1,6,7,5,4,3],![2,0,1,3,4,5,7,6],![0,2,1,5,4,3,6,7],![0,2,1,5,4,3,6,7]]
def lows : Set (Fin 9) := {v | 2 ≤ v.val}
def cofactor (v : Fin 9) :=
  if v = 2 then cycle8 else if v = 4 ∨ v = 7 then twoEnds else tailTwo

theorem cycle8_deleted (v : Fin 8) : Lower (cycle8 ∘ pin v) 5 := by
  have all : ∀ i x, (cycle8 ∘ pin i) (x ∘ cycleRelabel i) = path7 x := by decide +kernel
  apply lower_rename (cycleRelabel v)
  have eq : (fun x => (cycle8 ∘ pin v) (x ∘ cycleRelabel v)) = path7 := funext (all v)
  exact eq.symm ▸ path7_lower (path6_lower path5_lower)

theorem theta_deleted (h6 : Lower cycle6 5) (h8 : Lower cycle8 7) (v : Fin 9) (hv : v ∈ lows) :
    Lower (theta ∘ pin v) 7 := by
  have all : ∀ i : Fin 9, 2 ≤ i.val → ∀ x, (theta ∘ pin i) (x ∘ thetaRelabel i) = cofactor i x := by
    decide +kernel
  apply lower_rename (thetaRelabel v)
  have eq : (fun x => (theta ∘ pin v) (x ∘ thetaRelabel v)) = cofactor v := funext (all v hv)
  rw [eq]
  unfold cofactor
  split
  · exact h8
  · split
    · exact twoEnds_lower (pendant7_from_core h6)
    · exact tailTwo_lower (pendant7_from_core h6)

theorem cycle8_of_classifier {S} (h : Classifier cycle8 Set.univ S) : Lower cycle8 7 :=
  lower_two_step cycle8 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle8_deleted v)

def positive : Set (Fin 9 → Bool) := {x |
  ∃ i j : Fin 9, ((i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat))) ∧
    x = row (2^i.val+2^j.val)}

theorem generates : Generates positive theta := by
  intro x hx
  have all : ∀ y : Fin 9 → Bool, theta y = true →
      ∃ i j : Fin 9, (i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat)) ∧
        theta (row (2^i.val+2^j.val)) = true ∧ ∀ l : Fin 9, row (2^i.val+2^j.val) l = true → y l = true := by
    decide +kernel
  obtain ⟨i,j,edge,yes,le⟩ := all x hx
  exact ⟨_,⟨i,j,edge,rfl⟩,yes,le⟩

end Theta244Cores

namespace Theta244Finish
open ThetaPin3241 ThetaPrune3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem cycle_geo : Geometry ∅ cycle8 := by constructor <;> decide +kernel

theorem cycle_classifier : ThetaCores3241.Classifier cycle8 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle8 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem deleted (v : Fin 9) (hv : v ∈ lows) : Lower (theta ∘ pin v) 7 :=
  theta_deleted (ThetaCores3241.cycle6_of_classifier ThetaClass3241.cycle_classifier)
    (cycle8_of_classifier cycle_classifier) v hv

theorem nine_of_classifier {P : Set (Fin 9 → Bool)} {S : Set (Signal (Fin 9 → Bool))}
    (base : inputs 9 ⊆ S) (nonfree : ¬ Free S theta) (cover : Generates P theta)
    (classify : ∀ g : Gate (Fin 9 → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ lows, deadAt (topMiss v) g = true → Admissible (inputs 9) theta (topMiss v) g) →
      join g.1 g.2 ∈ S) : Lower theta 9 :=
  private_lower_two_step theta lows S P base nonfree cover classify deleted

def eleven : Fin 11 → Finset (Fin 9) :=
  ![{1,3,6}, {1,4,6}, {1,3,7}, {0,1,4,7}, {2,4,7}, {0,5,7}, {2,3,5,7}, {0,4,8},
    {0,5,8}, {2,4,6,8}, {2,3,5,6,8}]

theorem theta_total_of_or (lb : Lower theta 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ao : PEqualNP.TopForm.IsAO2 9 C) (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = theta x) :
    13 ≤ C.size := by
  have no : ∀ i, theta (PEqualNP.ReadK.setInput (eleven i)) = false := by decide +kernel
  have yes : ∀ i j, i ≠ j → theta (PEqualNP.ReadK.setInput (eleven i ∪ eleven j)) = true := by
    decide +kernel
  have ands := ThetaAnd3241.false_family_bound C ao eleven (fun i => (sem _).trans (no i))
    (fun i j h => (sem _).trans (yes i j h))
  have ors := lower_circuit lb C ao (funext sem)
  change 9 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ors
  by_contra low
  have limit : C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) ≤ 3 := by omega
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) limit
  omega

def upper : PEqualNP.CircuitLowerBounds.Circuit := ⟨
  [⟨.or,[2,3]⟩,⟨.or,[9,6]⟩,⟨.and,[0,10]⟩,
   ⟨.or,[2,5]⟩,⟨.or,[12,8]⟩,⟨.and,[1,13]⟩,
   ⟨.or,[3,5]⟩,⟨.and,[4,15]⟩,⟨.or,[6,8]⟩,⟨.and,[7,17]⟩,
   ⟨.or,[11,14]⟩,⟨.or,[16,18]⟩,⟨.or,[19,20]⟩],21⟩

theorem upper_ok : PEqualNP.TopForm.IsAO2 9 upper ∧ upper.size = 13 ∧
    upper.gates.countP isOr = 9 ∧
    ∀ x, PEqualNP.MetaComplexity.circuitFun 9 upper x = theta x := by decide +kernel

end Theta244Finish

namespace Theta244
open ThetaPin3241
abbrev X := Fin 9 → Bool
abbrev W := BitVec 28
def readBit (w : W) (i : Fin 28) : Bool := w[i.val]
def rowMasks : List Nat := [5,6,9,24,48,34,65,192,384,258,74,82,138,147,148,161,172,273,289,340,364,507,503,495,479,447,383,255]
def row (i : Fin 28) (v : Fin 9) : Bool := (rowMasks.getD i.val 0).testBit v.val
def target (x : X) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)
def code : W := 266339327
def rawMasks : List W := [266772549,266354210,265895939,263263244,258631704,250970160,234360000,199356800,134087424]
def base : List W := [0,134087424,199356800,234360000,250970160,258631704,263263244,265895939,266346496,266354210,266772549,266780263,268435455]
def arm : List W := [0,2097152,4194304,6291456,8388608,10485760,12582912,14680064,16777216,18874368,20971520,23068672,25165824,27262976,29360128,31457280,33554432,35651584,37748736,39845888,41943040,44040192,46137344,48234496,50331648,52428800,54525952,56623104,58720256,60817408,62914560,65011712,65011968,67108864,69206016,71303168,73400320,75497472,76546048,77594624,78643200,79691776,80740352,81788928,82837504,83886080,85983232,88080384,88604672,90177536,90701824,92274688,93323264,94371840,95420416,96468992,98041856,98566144,100139008,100663296,102760448,104857600,106954752,109051904,110100480,111149056,112197632,113246208,114294784,115343360,115605504,116654080,117440512,119537664,121634816,122159104,123731968,123863040,124387328,125829120,126877696,127926272,128974848,130023424,131596288,132120576,132121088,132513792,132514304,134087424,134217728,136314880,138412032,140509184,142606336,144703488,146800640,148897792,150994944,153092096,155189248,157286400,159383552,161480704,163577856,165675008,165675136,167772160,169869312,171966464,174063616,176160768,176226304,178257920,178323456,180355072,180420608,182452224,182484992,182550528,184549376,186646528,188743680,188760064,190849024,190865408,192937984,193003520,195035136,195039232,195104768,197132288,197214208,199237632,199241728,199270400,199274496,199356800,201326592,203423744,205520896,207618048,209715200,210763776,211812352,212860928,213909504,214958080,216006656,217055232,218103808,220200960,222298112,222822400,224395264,224397312,224921600,226492416,227540992,228589568,228590592,229639168,230686720,232259584,232783872,232783936,232786944,232787008,234360000,234881024,236978176,239075328,241172480,241172496,243269632,244383744,245366784,246480896,247463936,248578048,249561088,249561120,249856000,249856032,250970160,251658240,253755392,253755400,255852544,256393216,257957888,257959936,258088960,258091008,258631704,260046848,261160960,262144000,262144004,262149120,262149124,263263244,264241152,264241153,264241154,264241155,265895939,266346496,266354210,266772549,266780263,268435455]
def posArm : List W := [65011968,132121088,132514304,134087424,165675136,199356800,232783936,232787008,234360000,241172496,249561120,249856032,250970160,253755400,258631704,262144004,262149124,263263244,264241153,264241154,264241155,265895939,266354210,266772549,266780263,268435455]
structure Test where
  v : Fin 9
  t : Fin 28
  e : Fin 28
  z : Fin 28
  deriving DecidableEq
def tests : List Test := [⟨2,21,0,13⟩,⟨2,21,0,15⟩,⟨2,21,0,17⟩,⟨2,21,0,18⟩,⟨2,21,1,10⟩,⟨2,21,1,11⟩,⟨2,21,1,12⟩,⟨2,21,1,13⟩,⟨3,22,2,13⟩,⟨3,22,2,15⟩,⟨3,22,2,17⟩,⟨3,22,2,18⟩,⟨3,22,3,11⟩,⟨3,22,3,13⟩,⟨3,22,3,14⟩,⟨3,22,3,17⟩,⟨3,22,3,19⟩,⟨4,23,3,10⟩,⟨4,23,3,12⟩,⟨4,23,3,16⟩,⟨4,23,3,20⟩,⟨4,23,4,15⟩,⟨4,23,4,16⟩,⟨4,23,4,18⟩,⟨4,23,4,20⟩,⟨5,24,4,11⟩,⟨5,24,4,13⟩,⟨5,24,4,14⟩,⟨5,24,4,17⟩,⟨5,24,4,19⟩,⟨5,24,5,10⟩,⟨5,24,5,11⟩,⟨5,24,5,12⟩,⟨5,24,5,13⟩,⟨6,25,6,13⟩,⟨6,25,6,15⟩,⟨6,25,6,17⟩,⟨6,25,6,18⟩,⟨6,25,7,12⟩,⟨6,25,7,13⟩,⟨6,25,7,14⟩,⟨6,25,7,15⟩,⟨6,25,7,16⟩,⟨7,26,7,10⟩,⟨7,26,7,11⟩,⟨7,26,7,19⟩,⟨7,26,7,20⟩,⟨7,26,8,17⟩,⟨7,26,8,18⟩,⟨7,26,8,19⟩,⟨7,26,8,20⟩,⟨8,27,8,12⟩,⟨8,27,8,13⟩,⟨8,27,8,14⟩,⟨8,27,8,15⟩,⟨8,27,8,16⟩,⟨8,27,9,10⟩,⟨8,27,9,11⟩,⟨8,27,9,12⟩,⟨8,27,9,13⟩]
def edgeIdx (i : Fin 10) : Fin 28 := i.castLE (by decide)
def positives : Set X := Set.range (fun i : Fin 10 => row (edgeIdx i))
def low : Set (Fin 9) := {v | 2 ≤ v.val}
def represents (a : Signal X) (w : W) : Prop := ∀ i, a (row i) = readBit w i
def pool : Set (Signal X) := {a | ∃ w ∈ base, represents a w}

def privateMask (a b : W) : Prop :=
  (∃ i : Fin 10, readBit a (edgeIdx i) = true ∧ readBit b (edgeIdx i) = false) ∧
  (∃ i : Fin 10, readBit b (edgeIdx i) = true ∧ readBit a (edgeIdx i) = false)

def good (a b : W) (q : Test) : Prop :=
  (readBit a q.t && readBit b q.t) = false →
    readBit (a ||| b) q.t = true ∧ readBit (a ||| b) q.e = true ∧ readBit (a ||| b) q.z = false

instance (a b : W) : Decidable (privateMask a b) := by unfold privateMask; infer_instance
instance (a b : W) (q : Test) : Decidable (good a b q) := by unfold good; infer_instance

theorem and_table (a b : W) (ha : a ∈ posArm) (hb : b ∈ base)
    (i : Fin 10) (hit : readBit (b &&& a) (edgeIdx i) = true) : (b &&& a) ∈ posArm := by
  have table : posArm.all (fun u => base.all (fun v => posArm.contains (v &&& u) ||
      decide (∀ j : Fin 10, readBit (v &&& u) (edgeIdx j) = false))) = true := by decide +kernel
  have either := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  rcases Bool.or_eq_true_iff.mp either with yes | no
  · simpa using yes
  · have v := of_decide_eq_true no i
    simp [hit] at v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem or_table (a : W) (ha : a ∈ posArm) (b : W) (hb : b ∈ posArm)
    (p : privateMask a b) (h : ∀ q ∈ tests, good a b q) : (a ||| b) ∈ base := by
  have table : posArm.all (fun u => posArm.all (fun v =>
      base.contains (u ||| v) || !decide (privateMask u v) ||
      !tests.all (fun q => decide (good u v q)))) = true := by decide +kernel
  have atPair := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  have gates : tests.all (fun q => decide (good a b q)) = true :=
    List.all_eq_true.mpr (fun q hq => decide_eq_true (h q hq))
  simpa [p,gates] using atPair

theorem probes : ∀ q ∈ tests, 2 ≤ q.v.val ∧ (∀ i, row q.t i = topMiss q.v i) ∧
    target (row q.t) = true ∧ target (row q.e) = true ∧ target (row q.z) = false ∧
    ∀ i, row q.t i = true → row q.e i = true → row q.z i = true := by decide +kernel

theorem represent_and {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (meet a b) (u &&& v) := by
  intro i
  simp [meet,ha i,hb i,readBit]

theorem represent_or {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (join a b) (u ||| v) := by
  intro i
  simp [join,ha i,hb i,readBit]

theorem free_arm {a : Signal X} (h : Free pool a) (i : Fin 10) (onEdge : a (row (edgeIdx i)) = true) :
    ∃ w ∈ posArm, represents a w := by
  rcases factors h with rfl | ⟨xs,hs,rfl⟩
  · contradiction
  · clear h
    induction xs with
    | nil => exact ⟨268435455,by decide +kernel,(by decide +kernel : ∀ i : Fin 28, true = readBit 268435455 i)⟩
    | cons a xs ih =>
      obtain ⟨u,hu,ra⟩ := hs a (by simp)
      obtain ⟨_,tail⟩ := Bool.and_eq_true_iff.mp onEdge
      obtain ⟨v,hv,rs⟩ := ih (fun b hb => hs b (by simp [hb])) tail
      have allRep : represents (fun x => (a::xs).all (fun f => f x)) (u &&& v) := by
        intro k
        change ((a::xs).all (fun f => f (row k))) = _
        rw [List.all_cons]
        exact (represent_and ra rs) k
      exact ⟨_,and_table v u hv hu i ((allRep _).symm.trans onEdge),allRep⟩

theorem inputs_pool : inputs 9 ⊆ pool := by
  rintro _ ⟨i,rfl⟩
  have tab : ∀ j : Fin 9, rawMasks.getD j.val 0 ∈ base ∧
      ∀ k, row k j = readBit (rawMasks.getD j.val 0) k := by decide +kernel
  exact ⟨_,(tab i).1,(tab i).2⟩

theorem target_nonfree : ¬ Free pool target := by
  intro h
  obtain ⟨a,ha,rep⟩ := free_arm h 0 (by decide +kernel)
  have fixed : ∀ i : Fin 28, target (row i) = readBit code i := by decide +kernel
  have different : code ∉ posArm := by decide +kernel
  have eq : a = code := by
    apply BitVec.eq_of_getElem_eq
    intro k hk
    exact (rep ⟨k,hk⟩).symm.trans (fixed ⟨k,hk⟩)
  exact different (eq ▸ ha)

theorem classify (g : Gate X) (fa : Free pool g.1) (fb : Free pool g.2)
    (priv : ThetaPrune3241.Private positives g)
    (valid : ∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs 9) target (topMiss v) g) :
    join g.1 g.2 ∈ pool := by
  obtain ⟨⟨_,⟨i,rfl⟩,ia,ib⟩,⟨_,⟨j,rfl⟩,jb,ja⟩⟩ := priv
  obtain ⟨a,pa,ra⟩ := free_arm fa i ia
  obtain ⟨b,pb,rb⟩ := free_arm fb j jb
  rw [ra] at ia ja
  rw [rb] at ib jb
  have joined := represent_or ra rb
  refine ⟨_,or_table a pa b pb ⟨⟨i,ia,ib⟩,⟨j,jb,ja⟩⟩ ?_,joined⟩
  intro q hq dead
  obtain ⟨lo,point,ft,fe,fz,pass⟩ := probes q hq
  have eq := funext point
  have dg : deadAt (topMiss q.v) g = true := by
    simp [← eq,deadAt,ra q.t,rb q.t,dead]
  have adm := valid q.v lo dg
  rw [← eq] at adm
  obtain ⟨st,se,sz⟩ := adm (row q.e) (row q.z) (pass_inputs _ _ _ pass) ft fe fz
  exact ⟨(joined q.t).symm.trans st,(joined q.e).symm.trans se,(joined q.z).symm.trans sz⟩

theorem generates : ThetaPrune3241.Generates positives target := by
  have all : ∀ x : X, target x = true → ∃ i : Fin 10, target (row (edgeIdx i)) = true ∧
      ∀ j, row (edgeIdx i) j = true → x j = true := by decide +kernel
  intro x hx
  obtain ⟨i,yes,le⟩ := all x hx
  exact ⟨_,⟨i,rfl⟩,yes,le⟩

theorem nine : Lower Theta244Cores.theta 9 :=
  Theta244Finish.nine_of_classifier inputs_pool target_nonfree generates classify

theorem thirteen (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 9 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = target x) : 13 ≤ C.size :=
  Theta244Finish.theta_total_of_or nine C ao sem

end Theta244

namespace LeafAnd3241
open ThetaPin3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev X (n : Nat) := Fin n → Bool
def dual {n : Nat} (f : Signal (X n)) : Signal (X n) := fun x => !(f fun i => !(x i))

theorem dual_wire {n : Nat} {B : Set (Signal (X n))} {w : List (Signal (X n))}
    (hw : ∀ a ∈ w, Free B (dual a)) (i : Nat) : Free B (dual (wire w i)) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_one
  | cons a w ih => cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

theorem dual_compress {n : Nat} (gs : List PhysicalGate) (output : Nat) (w : List (Signal (X n)))
    (B : Set (Signal (X n))) (hw : ∀ a ∈ w, Free B (dual a)) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (ThetaPin3241.Gate (X n)), Valid B ops (dual (wire (gs.foldl step w) output)) ∧
      ops.length = gs.countP ThetaAnd3241.andGate := by
  induction gs generalizing w B with
  | nil => exact ⟨[],dual_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    let a := dual (wire w i)
    let b := dual (wire w j)
    rcases hop with kind | kind
    · let D := insert (join a b) B
      have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_and : dual (meet (wire w i) (wire w j)) = join a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_and]
      have ext : ∀ f ∈ step w g, Free D (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact widen (Set.subset_insert _ _) (hw f old)
        · rw [dual_and]
          exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨dual_wire hw i,dual_wire hw j,sem⟩,?_⟩
      have yes : ThetaAnd3241.andGate g = true := by simp [ThetaAnd3241.andGate,kind]
      simp [cost,yes]
    · have eq : step w g = w ++ [join (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_or : dual (join (wire w i) (wire w j)) = meet a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_or]
      have ext : ∀ f ∈ step w g, Free B (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact hw f old
        · rw [dual_or]
          exact free_meet (dual_wire hw i) (dual_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : ThetaAnd3241.andGate g = false := by simp [ThetaAnd3241.andGate,kind]
      simpa [no] using cost

theorem and_lower_circuit {n k : Nat} (f : Signal (X n)) (lb : Lower (dual f) k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP ThetaAnd3241.andGate := by
  let w : List (Signal (X n)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) (dual a) := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    apply atom
    exact ⟨i,funext (fun x => by simp [dual])⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := dual_compress C.gates C.output w (inputs n) ok shapes
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  rw [eq,correct] at sem
  exact cost ▸ lb ops sem

theorem save_at {m n k : Nat} (f : Signal (X n)) (v : Fin n) (e z : X n) (p : X m → X n)
    (inputs_ok : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (bounded : ∀ x i, p x i = true → topMiss v i = true)
    (pass : ∀ i, topMiss v i = true → e i = true → z i = true)
    (top : f (topMiss v) = true) (edge : f e = true) (neg : f z = false)
    (sub : Lower (f ∘ p) k) : Lower f (k+1) := by
  intro gs ok
  obtain ⟨g,hg,dead,_⟩ := critical_gate gs (inputs n) f _ _ _ (pass_inputs _ _ _ pass) ok top edge neg
  obtain ⟨l,r⟩ := active_monotone (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) ok g hg
  have zero {a : Signal (X n)} (inc : Increasing a) (off : a (topMiss v) = false) :
      ∀ x, a (p x) = false := by
    intro x
    cases h : a (p x) with
    | false => rfl
    | true => simp [inc _ _ (bounded x) h] at off
  have killed : Killed p g := dead.imp (zero l) (zero r)
  have charge : 0 < gs.countP (killedBit p) :=
    List.countP_pos_iff.mpr ⟨g,hg,by simp [killedBit,killed]⟩
  obtain ⟨out,sem,cost⟩ := restrict_transfer p gs _ _ f inputs_ok ok
  have lower := sub out sem
  omega

def cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∀ a b, G.Adj a b → x a = true ∨ x b = true)

theorem cover_dual {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    dual (NestedCover.graphFun G ∅) = cover G := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [dual,NestedCover.graphFun,cover]
  grind

def pinLeaf {n : Nat} (v w : Fin n) (x : X n) (i : Fin n) : Bool :=
  if i = v then false else if i = w then true else x i

theorem leaf_step {n k : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (adj : G.Adj v w) (leaf : ∀ i, G.Adj v i → i = w)
    (sub : Lower (cover (G.deleteIncidenceSet w)) k) : Lower (cover G) (k+1) := by
  have ne := G.ne_of_adj adj
  have hi (i : Fin n) : cover G (topMiss i) = true := by
    simp only [cover,decide_eq_true_eq,topMiss]
    intro a b ab
    by_cases av : a = i
    · exact Or.inr (fun (bv : b = i) => G.ne_of_adj ab (av.trans bv.symm))
    · exact Or.inl (by simp [av])
  let z : X n := fun i => decide (i ≠ v ∧ i ≠ w)
  have neg : cover G z = false := by
    apply decide_eq_false_iff_not.mpr
    intro h
    simpa [z] using h v w adj
  have cof : cover G ∘ pinLeaf v w = cover (G.deleteIncidenceSet w) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · intro h a b ⟨ab,aw,bw⟩
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ab
    · intro h a b ab
      by_cases aw : a = w
      · simp [pinLeaf,aw,ne.symm]
      by_cases bw : b = w
      · simp [pinLeaf,bw,ne.symm]
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ⟨ab,aw,bw⟩
  apply save_at (cover G) v (topMiss w) z (pinLeaf v w) _ _ _ (hi v) (hi w) neg (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinLeaf,iv] using (free_zero (B := inputs n))
    by_cases iw : i = w
    · simpa [Function.comp_def,pinLeaf,iv,iw,ne.symm] using (free_one (B := inputs n))
    · simpa [Function.comp_def,pinLeaf,iv,iw] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i pi
    by_contra h
    have iv : i = v := by simpa [topMiss] using h
    simp [pinLeaf,iv] at pi
  · intro i tv tw
    simpa [z,topMiss] using And.intro tv tw

end LeafAnd3241

namespace LeafCore3241
open ThetaPin3241 LeafAnd3241 PEqualNP.MetaComplexity PEqualNP.TopForm

def edgeFun {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)

theorem ordinary_eq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    NestedCover.graphFun G ∅ = edgeFun G := by
  funext x
  simp [NestedCover.graphFun,edgeFun]

def Leafless {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ ∃ v w, G.Adj v w ∧ ∀ a, G.Adj v a → a = w

def Counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Lower (edgeFun G) (G.edgeFinset.card - 1) ∧
    ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ Lower (cover G) S.card

def pinZero {n : Nat} (v : Fin n) (x : X n) (i : Fin n) := if i = v then false else x i

theorem or_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (vw : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (sub : Lower (edgeFun (G.deleteIncidenceSet v)) ((G.deleteIncidenceSet v).edgeFinset.card - 1)) :
    Lower (edgeFun G) (G.edgeFinset.card - 1) := by
  have dg : G.degree v = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w,vw,leaf⟩
  have card := G.card_edgeFinset_deleteIncidenceSet v
  rw [dg] at card
  by_cases small : G.edgeFinset.card ≤ 1
  · have h : G.edgeFinset.card - 1 = 0 := by omega
    rw [h]
    exact lower_zero _
  have pos : (G.deleteIncidenceSet v).edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have nonzero := (G.deleteIncidenceSet v).edgeFinset_nonempty.mp pos
  have pair : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    by_contra! no
    exact nonzero (SimpleGraph.eq_bot_iff_forall_not_adj.mpr no)
  obtain ⟨a,b,ab⟩ := pair
  obtain ⟨edge,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
  have top : edgeFun G (topMiss v) = true := by
    exact decide_eq_true ⟨a,b,edge,by simp [topMiss,av],by simp [topMiss,bv]⟩
  let e : X n := fun i => decide (i = v ∨ i = w)
  let z : X n := fun i => decide (i = w)
  have fe : edgeFun G e = true := decide_eq_true ⟨v,w,vw,by simp [e],by simp [e]⟩
  have fz : edgeFun G z = false := by
    apply decide_eq_false_iff_not.mpr
    rintro ⟨c,d,hcd,hc,hd⟩
    exact hcd.ne ((by simpa [z] using hc : c = w).trans (by simpa [z] using hd : d = w).symm)
  have cof : edgeFun G ∘ pinZero v = edgeFun (G.deleteIncidenceSet v) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      have iv : i ≠ v := fun eq => by simp [pinZero,eq] at hi
      have jv : j ≠ v := fun eq => by simp [pinZero,eq] at hj
      exact ⟨i,j,⟨ij,iv,jv⟩,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
    · rintro ⟨i,j,⟨ij,iv,jv⟩,hi,hj⟩
      exact ⟨i,j,ij,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
  have eq : G.edgeFinset.card - 1 = ((G.deleteIncidenceSet v).edgeFinset.card - 1) + 1 := by omega
  rw [eq]
  apply save_at (edgeFun G) v e z (pinZero v) _ _ _ top fe fz (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinZero,iv] using (free_zero (B := inputs n))
    · simpa [Function.comp_def,pinZero,iv] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i h
    by_contra no
    have iv : i = v := by simpa [topMiss] using no
    simp [pinZero,iv] at h
  · intro i tv ei
    have iv : i ≠ v := by simpa [topMiss] using tv
    simpa [e,z,iv] using ei

theorem add_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (adj : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (dropV : Counts (G.deleteIncidenceSet v)) (dropW : Counts (G.deleteIncidenceSet w)) :
    Counts G := by
  refine ⟨or_leaf G v w adj leaf dropV.1,?_⟩
  obtain ⟨S,cv,lo⟩ := dropW.2
  refine ⟨insert w S,?_,?_⟩
  · intro a b ab
    by_cases aw : a = w
    · exact Or.inl (by simp [aw])
    by_cases bw : b = w
    · exact Or.inr (by simp [bw])
    exact (cv (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,aw,bw⟩)).imp
      (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
  · have pay := leaf_step G v w adj leaf lo
    intro ops valid
    exact (Finset.card_insert_le _ _).trans (pay ops valid)

theorem peel_to_core {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (base : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → Leafless H → Counts H) :
    Counts G := by
  classical
  have work (k : Nat) : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H ≤ G → H.edgeFinset.card = k → Counts H := by
    induction k using Nat.strong_induction_on with
    | ind k rec =>
      intro H _ hg count
      by_cases last : Leafless H
      · exact base H hg last
      obtain ⟨v,w,adj,leaf⟩ := not_not.mp last
      apply add_leaf H v w adj leaf
      all_goals
        apply rec _ _ _ (le_trans (H.deleteIncidenceSet_le _) hg) rfl
        rw [H.card_edgeFinset_deleteIncidenceSet,← count]
      · have h := (H.degree_pos_iff_exists_adj v).mpr ⟨w,adj⟩
        have c := H.degree_le_card_edgeFinset v
        omega
      · have h := (H.degree_pos_iff_exists_adj w).mpr ⟨v,adj.symm⟩
        have c := H.degree_le_card_edgeFinset w
        omega
  exact work _ G le_rfl rfl

theorem bound_of_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (proof : Counts G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : IsAO2 n C)
    (h : circuitFun n C = edgeFun G) : ∃ S : Finset (Fin n),
    G.IsVertexCover (S : Set (Fin n)) ∧ G.edgeFinset.card + S.card ≤ C.size + 1 := by
  obtain ⟨orr,S,cv,andd⟩ := proof
  have ol := lower_circuit orr C ao h
  rw [← ordinary_eq] at h
  have al := and_lower_circuit _ ((cover_dual G).symm ▸ andd) C ao h
  rw [← ThetaAnd3241.subtract_or_eq_and C ao] at al
  change G.edgeFinset.card - 1 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ol
  have le := List.countP_le_length (p := fun g => PEqualNP.SharedBlockCost.isOrOp g.op) (l := C.gates)
  change _ ≤ C.size at le
  exact ⟨S,cv,by omega⟩

end LeafCore3241

namespace ForestBipartite3241
open LeafCore3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev bip {n m : Nat} (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n+m)) :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ E, a = Fin.castAdd m e.1 ∧ b = Fin.natAdd n e.2

theorem sides {n m : Nat} (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro eq
  have h := congrArg Fin.val eq
  change a.val = n + b.val at h
  omega

def pair {n m : Nat} (e : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(Fin.castAdd m e.1,Fin.natAdd n e.2)

theorem injective_pair {n m : Nat} : Function.Injective (pair (n := n) (m := m)) := by
  intro e f eq
  rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,_⟩
  · exact Prod.ext (Fin.castAdd_injective n m a) (Fin.ext (by
      have h := congrArg Fin.val b
      change n + e.2.val = n + f.2.val at h
      omega))
  · exact (sides _ _ a).elim

theorem bip_adjacency {n m : Nat} {E : Finset (Fin n × Fin m)} {e : Fin n × Fin m} (he : e ∈ E) :
    (bip E).Adj (Fin.castAdd m e.1) (Fin.natAdd n e.2) :=
  ⟨sides _ _,Or.inl ⟨e,he,rfl,rfl⟩⟩

theorem bip_edges {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj] :
    (bip E).edgeFinset.card = E.card := by
  have eq : (bip E).edgeFinset = E.image pair := by
    ext t
    induction t using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨e,he,rfl⟩
        · exact Finset.mem_image.mpr ⟨e,he,Sym2.eq_swap⟩
      · intro h
        obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,b⟩
        · exact a ▸ b ▸ bip_adjacency he
        · exact a ▸ b ▸ (bip_adjacency he).symm
  rw [eq,Finset.card_image_of_injective _ injective_pair]

theorem formula {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj]
    (x : Fin (n+m) → Bool) : edgeFun (bip E) x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFun,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩,ha,hb⟩
    · exact ⟨e,he,ha,hb⟩
    · exact ⟨e,he,hb,ha⟩
  · rintro ⟨e,he,l,r⟩
    exact ⟨_,_,bip_adjacency he,l,r⟩

end ForestBipartite3241

namespace CoreTransfer3241
open ThetaPin3241 LeafAnd3241 LeafCore3241

theorem padded {m n : Nat} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : Fin m → Fin n) (inj : Function.Injective f)
    (adj : ∀ i j, H.Adj i j ↔ ∃ u v, G.Adj u v ∧ f u = i ∧ f v = j)
    (src : Counts G) : Counts H := by
  classical
  let p : X m → X n := fun x => Function.extend f x (fun _ => false)
  have put (x : X m) (i : Fin m) : p x (f i) = x i := inj.extend_apply x _ i
  have raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p) := by
    rintro _ ⟨i,rfl⟩
    by_cases mem : ∃ t, f t = i
    · obtain ⟨t,rfl⟩ := mem
      have eq : (fun (x : X n) => x (f t)) ∘ p = (fun (x : X m) => x t) := funext (fun x => put x t)
      exact eq ▸ atom ⟨t,rfl⟩
    · have eq : (fun (x : X n) => x i) ∘ p = (fun _ => false) :=
        funext (fun x => Function.extend_apply' x (fun _ => false) i mem)
      exact eq ▸ free_zero
  have spec (u v : Fin m) (uv : G.Adj u v) : H.Adj (f u) (f v) := (adj _ _).mpr ⟨u,v,uv,rfl,rfl⟩
  have edge : edgeFun H ∘ p = edgeFun G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,yes,also⟩
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      exact ⟨u,v,uv,(put x u).symm.trans yes,(put x v).symm.trans also⟩
    · rintro ⟨u,v,uv,yes,also⟩
      exact ⟨_,_,spec u v uv,(put x u).trans yes,(put x v).trans also⟩
  have covers : cover H ∘ p = cover G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok u v uv
      simpa only [put] using ok _ _ (spec u v uv)
    · intro ok i j ij
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      simpa only [put] using ok _ _ uv
  have subset : H.edgeFinset ⊆ G.edgeFinset.image (Sym2.map f) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j =>
      intro he
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp (H.mem_edgeFinset.mp he)
      exact Finset.mem_image.mpr ⟨s(u,v),G.mem_edgeFinset.mpr uv,rfl⟩
  have count := (Finset.card_le_card subset).trans Finset.card_image_le
  obtain ⟨ors,S,cv,ands⟩ := src
  refine ⟨?_,S.image f,?_,?_⟩
  · have lo : Lower (edgeFun H) (G.edgeFinset.card - 1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs ok => (Nat.sub_le_sub_right count 1).trans (lo gs ok)
  · intro i j ij
    obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp ij
    exact (cv uv).imp (fun hu => Finset.mem_image_of_mem _ hu) (fun hv => Finset.mem_image_of_mem _ hv)
  · rw [Finset.card_image_of_injective _ inj]
    exact lower_transport p raw (covers.symm ▸ ands)

theorem pass_of_choices {n : Nat} (gs : List (ThetaPin3241.Gate (X n))) (B : Set (Signal (X n)))
    (f : Signal (X n)) (x y z : X n) (base : ∀ a ∈ B, Pass x y z a)
    (agree : ∀ g ∈ gs, g.1 x = g.1 y) (ok : Valid B gs f) : Pass x y z f := by
  induction gs generalizing B with
  | nil => exact free_pass base ok
  | cons g gs ih =>
    obtain ⟨fa,fb,tail⟩ := ok
    have pass_a := free_pass base fa
    have pass_b := free_pass base fb
    have pass_g : Pass x y z (join g.1 g.2) := by
      have eq := agree g List.mem_cons_self
      intro gx gy
      cases ax : g.1 x with
      | true =>
        have az := pass_a ax (eq.symm.trans ax)
        simp [join,az]
      | false =>
        have ay := eq.symm.trans ax
        have bz := pass_b (by simpa [join,ax] using gx) (by simpa [join,ay] using gy)
        simp [join,bz]
    refine ih (insert (join g.1 g.2) B) ?_ ?_ tail
    · intro a ha
      exact (Set.mem_insert_iff.mp ha).elim (fun eq => eq ▸ pass_g) (base a)
    · exact fun g hg => agree g (List.mem_cons_of_mem _ hg)

theorem separated_rows {n k r : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i) = true)
    (off : ∀ i j, i ≠ j → f (fun v => rows i v && rows j v) = false)
    (many : 2^(k-1) < r) : Lower f k := by
  intro gs ok
  let key (i : Fin r) (g : Fin gs.length) := (gs.get g).1 (rows i)
  have distinguish : Function.Injective key := by
    intro i j eq
    by_contra ne
    have agree (g) (hg : g ∈ gs) : g.1 (rows i) = g.1 (rows j) := by
      obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hg
      exact congrFun eq t
    have pass := pass_of_choices gs (inputs n) f (rows i) (rows j) (fun v => rows i v && rows j v)
      (pass_inputs _ _ _ (fun v a b => by simp [a,b])) agree ok
    have both := pass (yes i) (yes j)
    simp [off i j ne] at both
  have count := Fintype.card_le_of_injective key distinguish
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at count
  by_contra bad
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) (show gs.length ≤ k-1 by omega)
  omega

end CoreTransfer3241

namespace SmallCores3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 CoreTransfer3241
open ThetaCores3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path8 (x : LeafAnd3241.X 8) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path8_lower (rec : Lower path7 5) : Lower path8 6 := by
  have eq : path8 ∘ pin (7 : Fin 8) = path7 := by
    funext x
    exact (by decide +kernel : ∀ y, path8 (pin (7 : Fin 8) y) = path7 y) x
  apply lower_one_step path8 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path9 (x : LeafAnd3241.X 9) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path9_lower (rec : Lower path8 6) : Lower path9 7 := by
  have eq : path9 ∘ pin (8 : Fin 9) = path8 := by
    funext x
    exact (by decide +kernel : ∀ y, path9 (pin (8 : Fin 9) y) = path8 y) x
  apply lower_one_step path9 8 (row 384) (row 128)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycle10 (x : LeafAnd3241.X 10) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycleRename : Fin 10 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],![8,0,1,2,3,4,5,6,7],![7,8,0,1,2,3,4,5,6],![6,7,8,0,1,2,3,4,5],![5,6,7,8,0,1,2,3,4],![4,5,6,7,8,0,1,2,3],![3,4,5,6,7,8,0,1,2],![2,3,4,5,6,7,8,0,1],![1,2,3,4,5,6,7,8,0],![0,1,2,3,4,5,6,7,8]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_deleted (v : Fin 10) : Lower (cycle10 ∘ pin v) 7 := by
  have all : ∀ i x, (cycle10 ∘ pin i) (x ∘ cycleRename i) = path9 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle10 ∘ pin v) (x ∘ cycleRename v)) = path9 := funext (all v)
  exact eq.symm ▸ path9_lower (path8_lower (path7_lower (path6_lower path5_lower)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_geometry : Geometry ∅ cycle10 := by constructor <;> decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_lower : Lower cycle10 9 := by
  apply lower_two_step cycle10 Set.univ (pool ∅) (base_subset _)
  · exact nonfree cycle10 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle10_geometry g a b (fun v _ => h v (Set.mem_univ v))
  · exact fun v _ => cycle10_deleted v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev graph (n : Nat) (edges : List (Nat × Nat)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun (i j : Fin n) => (i.val,j.val) ∈ edges)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev six := graph 6 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def sixRows : Fin 5 → Nat := ![21,27,42,45,54]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem sixCounts : Counts six := by
  have eq : edgeFun six = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun six y = cycle6 y) x
  have card : six.edgeFinset.card - 1 = 5 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle6_of_classifier ThetaClass3241.cycle_classifier
  · let S : Finset (Fin 6) := {0,2,4}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, six.Adj a b → a ∈ ({0,2,4} : Finset (Fin 6)) ∨ b ∈ ({0,2,4} : Finset (Fin 6)))
    have sc : S.card = 3 := by decide +kernel
    have dualEq : cover six = dual cycle6 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle6) (fun i => row (sixRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev eight := graph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def eightRows : Fin 9 → Nat := ![85,91,107,109,170,173,181,182,214]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem eightCounts : Counts eight := by
  have eq : edgeFun eight = cycle8 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun eight y = cycle8 y) x
  have card : eight.edgeFinset.card - 1 = 7 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle8_of_classifier Theta244Finish.cycle_classifier
  · let S : Finset (Fin 8) := {0,2,4,6}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, eight.Adj a b → a ∈ ({0,2,4,6} : Finset (Fin 8)) ∨ b ∈ ({0,2,4,6} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover eight = dual cycle8 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle8) (fun i => row (eightRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev ten := graph 10 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def tenRows : Fin 17 → Nat := ![341,347,363,365,427,429,437,682,685,693,694,725,726,730,854,858,874]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem tenCounts : Counts ten := by
  have eq : edgeFun ten = cycle10 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun ten y = cycle10 y) x
  have card : ten.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle10_lower
  · let S : Finset (Fin 10) := {0,2,4,6,8}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, ten.Adj a b → a ∈ ({0,2,4,6,8} : Finset (Fin 10)) ∨ b ∈ ({0,2,4,6,8} : Finset (Fin 10)))
    have sc : S.card = 5 := by decide +kernel
    have dualEq : cover ten = dual cycle10 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle10) (fun i => row (tenRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev threeThreeThree := graph 8 [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def threeThreeThreeRows : Fin 9 → Nat := ![15,55,91,115,157,181,217,238,240]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem threeThreeThreeCounts : Counts threeThreeThree := by
  have eq : edgeFun threeThreeThree = ThetaAnd3241.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun threeThreeThree y = ThetaAnd3241.theta y) x
  have card : threeThreeThree.edgeFinset.card - 1 = 8 := by decide +kernel
  constructor
  · rw [eq,card]
    exact theta_of_classifiers ThetaClass3241.cycle_classifier theta_classifier
  · let S : Finset (Fin 8) := {0,1,2,3}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, threeThreeThree.Adj a b → a ∈ ({0,1,2,3} : Finset (Fin 8)) ∨ b ∈ ({0,1,2,3} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover threeThreeThree = dual ThetaAnd3241.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual ThetaAnd3241.theta) (fun i => row (threeThreeThreeRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev twoFourFour := graph 9 [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def twoFourFourRows : Fin 9 → Nat := ![147,171,222,238,339,350,363,364,373]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem twoFourFourCounts (extra : Lower Theta244Cores.theta 9) : Counts twoFourFour := by
  have eq : edgeFun twoFourFour = Theta244Cores.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun twoFourFour y = Theta244Cores.theta y) x
  have card : twoFourFour.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact extra
  · let S : Finset (Fin 9) := {0,1,4,7}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, twoFourFour.Adj a b → a ∈ ({0,1,4,7} : Finset (Fin 9)) ∨ b ∈ ({0,1,4,7} : Finset (Fin 9)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover twoFourFour = dual Theta244Cores.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual Theta244Cores.theta) (fun i => row (twoFourFourRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

end SmallCores3241

namespace GraphPacking3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 ForestBipartite3241

abbrev Matrix (n m : Nat) := Finset (Fin n × Fin m)
abbrev Left {n m : Nat} (a : Fin n) := Fin.castAdd m a
abbrev Right {n m : Nat} (b : Fin m) := Fin.natAdd n b

def FourFree {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ p q l s, p ≠ q → l ≠ s → ¬((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)

def HasPartners {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ a b, (a,b) ∈ E →
    (∃ c, c ≠ b ∧ (a,c) ∈ E) ∧ (∃ d, d ≠ a ∧ (d,b) ∈ E)

theorem adj_left {n m : Nat} (E : Matrix n m) (a : Fin n) (j : Fin (n+m)) :
    (bip E).Adj (Left a) j ↔ ∃ b, (a,b) ∈ E ∧ j = Right b := by
  constructor
  · rintro ⟨_,⟨e,he,eq,rfl⟩ | ⟨e,_,_,eq⟩⟩
    · have ea : a = e.1 := Fin.castAdd_injective n m eq
      exact ⟨e.2,ea ▸ he,rfl⟩
    · exact (sides _ _ eq).elim
  · rintro ⟨b,h,rfl⟩
    exact bip_adjacency h

theorem adj_right {n m : Nat} (E : Matrix n m) (b : Fin m) (i : Fin (n+m)) :
    (bip E).Adj (Right b) i ↔ ∃ a, (a,b) ∈ E ∧ i = Left a := by
  constructor
  · rintro ⟨_,⟨e,_,eq,_⟩ | ⟨e,he,rfl,eq⟩⟩
    · exact (sides _ _ eq.symm).elim
    · have eb : b = e.2 := Fin.natAdd_injective m n eq
      exact ⟨e.1,eb ▸ he,rfl⟩
  · rintro ⟨a,h,rfl⟩
    exact (bip_adjacency h).symm

theorem leafless_iff {n m : Nat} (E : Matrix n m) : Leafless (bip E) ↔ HasPartners E := by
  classical
  constructor
  · intro no a b ab
    constructor
    · by_contra! bad
      apply no
      refine ⟨Left a,Right b,bip_adjacency ab,?_⟩
      intro i hi
      obtain ⟨c,hc,rfl⟩ := (adj_left E a i).mp hi
      have cb : c = b := by_contra (fun ne => bad c ne hc)
      rw [cb]
    · by_contra! bad
      apply no
      refine ⟨Right b,Left a,(bip_adjacency ab).symm,?_⟩
      intro i hi
      obtain ⟨d,hd,rfl⟩ := (adj_right E b i).mp hi
      have da : d = a := by_contra (fun ne => bad d ne hd)
      rw [da]
  · rintro partners ⟨i,j,ij,leaf⟩
    rcases ij with ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨c,ne,hc⟩ := (partners a b h).1
      exact ne (Fin.natAdd_injective m n (leaf _ (bip_adjacency hc)))
    · obtain ⟨d,ne,hd⟩ := (partners a b h).2
      exact ne (Fin.castAdd_injective n m (leaf _ (bip_adjacency hd).symm))

theorem side_count {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (two : ∀ a b, (a,b) ∈ E → ∃ c, c ≠ b ∧ (a,c) ∈ E) :
    (E.image Prod.fst).card * 2 ≤ E.card := by
  classical
  let P := E.image Prod.fst
  have picks (p : P) : ∃ b c, b ≠ c ∧ (p.val,b) ∈ E ∧ (p.val,c) ∈ E := by
    obtain ⟨⟨a,b⟩,ab,e⟩ := Finset.mem_image.mp p.property
    change a = p.val at e
    obtain ⟨c,ne,ac⟩ := two a b ab
    exact ⟨b,c,ne.symm,e ▸ ab,e ▸ ac⟩
  choose first second diff one two using picks
  let edge (p : P) (b : Bool) : E := if b then ⟨(p.val,first p),one p⟩ else ⟨(p.val,second p),two p⟩
  have inj : Function.Injective (fun x : P × Bool => edge x.1 x.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have row (r : P) (b : Bool) : (edge r b).val.1 = r.val := by cases b <;> rfl
    have pe : p = q := Subtype.ext ((row p i).symm.trans ((congrArg (fun t : E => t.val.1) eq).trans (row q j)))
    subst q
    cases i <;> cases j
    · rfl
    · exact ((diff p).symm (congrArg (fun t : E => t.val.2) eq)).elim
    · exact (diff p (congrArg (fun t : E => t.val.2) eq)).elim
    · rfl
  have bound := Fintype.card_le_of_injective _ inj
  simpa [P] using bound

theorem both_sides {n m : Nat} (E : Matrix n m) (partners : HasPartners E) (small : E.card ≤ 10) :
    (E.image Prod.fst).card ≤ 5 ∧ (E.image Prod.snd).card ≤ 5 := by
  have left := side_count E (fun a b ab => (partners a b ab).1)
  have flip {a : Fin n} {b : Fin m} : (b,a) ∈ E.image Prod.swap ↔ (a,b) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨p,q⟩,pq,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact pq
    · exact fun h => Finset.mem_image_of_mem Prod.swap h
  have right := side_count (E.image Prod.swap) (fun b a ba => by
    obtain ⟨d,ne,db⟩ := (partners a b (flip.mp ba)).2
    exact ⟨d,ne,flip.mpr db⟩)
  rw [Finset.image_image,Finset.card_image_of_injective _ Prod.swap_injective] at right
  change (E.image Prod.snd).card * 2 ≤ E.card at right
  omega

theorem from_index {n k : Nat} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (lab : Fin n → Option (Fin k))
    (unique : ∀ i j a, lab i = some a → lab j = some a → i = j)
    (forward : ∀ i j, G.Adj i j → ∃ a b, lab i = some a ∧ lab j = some b ∧ H.Adj a b)
    (back : ∀ a b, H.Adj a b → ∃ i j, lab i = some a ∧ lab j = some b ∧ G.Adj i j)
    (size : G.edgeFinset.card ≤ H.edgeFinset.card) (h : Counts H) : Counts G := by
  classical
  let p : X k → X n := fun x i => (lab i).elim false x
  have read (x : X k) (i a) (hi : lab i = some a) : p x i = x a := by simp [p,hi]
  have raw : ∀ t ∈ inputs n, Free (inputs k) (t ∘ p) := by
    rintro _ ⟨i,rfl⟩
    cases hi : lab i with
    | none => simpa [Function.comp_def,p,hi] using (free_zero (B := inputs k))
    | some a => simpa [Function.comp_def,p,hi] using (atom (B := inputs k) ⟨a,rfl⟩)
  have edge : edgeFun G ∘ p = edgeFun H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,pi,pj⟩
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      exact ⟨a,b,ab,(read x i a li).symm.trans pi,(read x j b lj).symm.trans pj⟩
    · rintro ⟨a,b,ab,pa,pb⟩
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      exact ⟨i,j,ij,(read x i a li).trans pa,(read x j b lj).trans pb⟩
  have cover_eq : cover G ∘ p = cover H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok a b ab
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      simpa only [read x i a li,read x j b lj] using ok i j ij
    · intro ok i j ij
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      simpa only [read x i a li,read x j b lj] using ok a b ab
  obtain ⟨ors,S,cv,ands⟩ := h
  let T := Finset.univ.filter fun i => ∃ a ∈ S, lab i = some a
  have lift (i : T) : ∃ a : S, lab i.val = some a.val := by
    obtain ⟨a,ha,eq⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨a,ha⟩,eq⟩
  choose assign spec using lift
  have inj : Function.Injective assign := fun i j eq =>
    Subtype.ext (unique _ _ _ (spec i) (eq ▸ spec j))
  have card : T.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  refine ⟨?_,T,?_,?_⟩
  · have bound : Lower (edgeFun G) (H.edgeFinset.card-1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs val => (Nat.sub_le_sub_right size 1).trans (bound gs val)
  · intro i j ij
    obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
    exact (cv ab).imp (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,mem,li⟩)
      (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,mem,lj⟩)
  · have bound : Lower (cover G) S.card := lower_transport p raw (cover_eq.symm ▸ ands)
    exact fun gs val => card.trans (bound gs val)

end GraphPacking3241

namespace MatrixPacking3241
open GraphPacking3241 LeafCore3241 ForestBipartite3241

def optional {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β) (i : α) : Option β :=
  if h : i ∈ P then some (f ⟨i,h⟩) else none

theorem optional_unique {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β)
    (inj : Function.Injective f) (i j : α) (a : β) (hi : optional P f i = some a)
    (hj : optional P f j = some a) : i = j := by
  unfold optional at hi hj
  split at hi <;> rename_i pi
  · split at hj <;> rename_i pj
    · exact congrArg Subtype.val (inj ((Option.some.inj hi).trans (Option.some.inj hj).symm))
    · contradiction
  · contradiction

def combine {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5)) :
    Fin (n+m) → Option (Fin 10) :=
  Fin.addCases (fun a => (r a).map (Fin.castAdd 5)) (fun b => (c b).map (Fin.natAdd 5))

theorem combined_unique {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5))
    (ri : ∀ i j a, r i = some a → r j = some a → i = j)
    (ci : ∀ i j b, c i = some b → c j = some b → i = j) :
    ∀ i j t, combine r c i = some t → combine r c j = some t → i = j := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    intro j <;> refine Fin.addCases (fun u => ?_) (fun v => ?_) j <;>
    intro t hi hj <;> simp only [combine,Fin.addCases_left,Fin.addCases_right,Option.map_eq_some_iff] at hi hj <;>
    obtain ⟨x,hx,rfl⟩ := hi <;> obtain ⟨y,hy,eq⟩ := hj
  · obtain rfl : y = x := Fin.castAdd_injective 5 5 eq
    exact congrArg _ (ri _ _ _ hx hy)
  · exact (sides x y eq.symm).elim
  · exact (sides y x eq).elim
  · obtain rfl : y = x := Fin.natAdd_injective 5 5 eq
    exact congrArg _ (ci _ _ _ hx hy)

abbrev Rows {n m} (E : Matrix n m) := E.image Prod.fst
abbrev Cols {n m} (E : Matrix n m) := E.image Prod.snd
def erow {n m} {E : Matrix n m} (e : E) : Rows E := ⟨e.val.1,Finset.mem_image_of_mem _ e.property⟩
def ecol {n m} {E : Matrix n m} (e : E) : Cols E := ⟨e.val.2,Finset.mem_image_of_mem _ e.property⟩

def pack {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5) : Matrix 5 5 :=
  E.attach.image (fun e => (r (erow e),c (ecol e)))

theorem decode {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5} {a b} :
    (a,b) ∈ pack E r c ↔ ∃ e : E, r (erow e) = a ∧ c (ecol e) = b := by
  simp [pack]

theorem rows_eq {n m} {E : Matrix n m} {r : Rows E → Fin 5} (inj : Function.Injective r) (e f : E) :
    r (erow e) = r (erow f) ↔ e.val.1 = f.val.1 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg r (Subtype.ext h)⟩

theorem cols_eq {n m} {E : Matrix n m} {c : Cols E → Fin 5} (inj : Function.Injective c) (e f : E) :
    c (ecol e) = c (ecol f) ↔ e.val.2 = f.val.2 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg c (Subtype.ext h)⟩

theorem pack_card {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) : (pack E r c).card = E.card := by
  unfold pack
  rw [Finset.card_image_of_injective,Finset.card_attach]
  intro e f eq
  exact Subtype.ext (Prod.ext ((rows_eq ri _ _).mp (congrArg Prod.fst eq))
    ((cols_eq ci _ _).mp (congrArg Prod.snd eq)))

theorem pack_free {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (free : FourFree E) :
    FourFree (pack E r c) := by
  intro p q l s pq ls h
  obtain ⟨a,ap,al⟩ := decode.mp h.1
  obtain ⟨b,bp,bs⟩ := decode.mp h.2.1
  obtain ⟨d,dq,dl⟩ := decode.mp h.2.2.1
  obtain ⟨e,eq,es⟩ := decode.mp h.2.2.2
  have ab := (rows_eq ri a b).mp (ap.trans bp.symm)
  have de := (rows_eq ri d e).mp (dq.trans eq.symm)
  have ad := (cols_eq ci a d).mp (al.trans dl.symm)
  have be := (cols_eq ci b e).mp (bs.trans es.symm)
  have pr : a.val.1 ≠ d.val.1 := fun hh => pq (ap.symm.trans (((rows_eq ri a d).mpr hh).trans dq))
  have lc : a.val.2 ≠ b.val.2 := fun hh => ls (al.symm.trans (((cols_eq ci a b).mpr hh).trans bs))
  apply free _ _ _ _ pr lc
  exact ⟨a.property,ab ▸ b.property,ad ▸ d.property,de ▸ be ▸ e.property⟩

theorem pack_partners {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (has : HasPartners E) :
    HasPartners (pack E r c) := by
  intro a b ab
  obtain ⟨e,rfl,rfl⟩ := decode.mp ab
  obtain ⟨⟨v,ne,ev⟩,⟨u,diff,ue⟩⟩ := has _ _ e.property
  let f : E := ⟨(e.val.1,v),ev⟩
  let g : E := ⟨(u,e.val.2),ue⟩
  exact ⟨⟨c (ecol f),fun eq => ne ((cols_eq ci f e).mp eq),
      decode.mpr ⟨f,(rows_eq ri f e).mpr rfl,rfl⟩⟩,
    ⟨r (erow g),fun eq => diff ((rows_eq ri g e).mp eq),
      decode.mpr ⟨g,rfl,(cols_eq ci g e).mpr rfl⟩⟩⟩

theorem unpack_counts {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5)
    (ri : Function.Injective r) (ci : Function.Injective c)
    (src : Counts (bip (pack E r c))) : Counts (bip E) := by
  let lab := combine (optional (Rows E) r) (optional (Cols E) c)
  have l (e : E) : lab (Left e.val.1) = some (Fin.castAdd 5 (r (erow e))) := by
    simp only [lab,combine,Left,Fin.addCases_left,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (erow e).property).elim
  have rr (e : E) : lab (Right e.val.2) = some (Fin.natAdd 5 (c (ecol e))) := by
    simp only [lab,combine,Right,Fin.addCases_right,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (ecol e).property).elim
  apply from_index (bip E) (bip (pack E r c)) lab
    (combined_unique _ _ (optional_unique _ _ ri) (optional_unique _ _ ci)) _ _ _ src
  · rintro i j ⟨_,⟨p,h,rfl,rfl⟩ | ⟨p,h,rfl,rfl⟩⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,l e,rr e,bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,rr e,l e,(bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)).symm⟩
  · rintro i j ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,l e,rr e,bip_adjacency e.property⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,rr e,l e,(bip_adjacency e.property).symm⟩
  · rw [bip_edges,bip_edges,pack_card ri ci]

def Census : Prop := ∀ E : Matrix 5 5, E.card ≤ 10 → FourFree E → Leafless (bip E) → Counts (bip E)

theorem compressed {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (last : Leafless (bip E)) (census : Census) : Counts (bip E) := by
  let h := (leafless_iff E).mp last
  obtain ⟨pr,pc⟩ := both_sides E h size
  let r (p : Rows E) := Fin.castLE pr (((Rows E).orderIsoOfFin rfl).symm p)
  let c (p : Cols E) := Fin.castLE pc (((Cols E).orderIsoOfFin rfl).symm p)
  have ri : Function.Injective r := (Fin.castLE_injective pr).comp ((Rows E).orderIsoOfFin rfl).symm.injective
  have ci : Function.Injective c := (Fin.castLE_injective pc).comp ((Cols E).orderIsoOfFin rfl).symm.injective
  apply unpack_counts E r c ri ci
  apply census
  · simpa [pack_card ri ci] using size
  · exact pack_free ri ci free
  · exact (leafless_iff _).mpr (pack_partners ri ci h)

theorem full {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (census : Census) : Counts (bip E) := by
  classical
  apply peel_to_core (bip E)
  intro H _ sub last
  let F := E.filter (fun p => H.Adj (Left p.1) (Right p.2))
  have eq : H = bip F := by
    ext i j
    constructor
    · intro ij
      rcases sub ij with ⟨ne,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact bip_adjacency (Finset.mem_filter.mpr ⟨he,ij⟩ : e ∈ F)
      · exact (bip_adjacency (Finset.mem_filter.mpr ⟨he,ij.symm⟩ : e ∈ F)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact (Finset.mem_filter.mp he).2
      · exact ((Finset.mem_filter.mp he).2).symm
  have subset : F ⊆ E := Finset.filter_subset _ _
  have freeF : FourFree F := fun p q l s pq ls ⟨a,b,c,d⟩ =>
    free p q l s pq ls ⟨subset a,subset b,subset c,subset d⟩
  have carry {K L : SimpleGraph (Fin (n+m))} [d : DecidableRel K.Adj] [e : DecidableRel L.Adj]
      (same : K = L) (ok : Counts L) : Counts K := by
    subst L
    have sameInst : d = e := Subsingleton.elim _ _
    cases sameInst
    exact ok
  exact carry eq (compressed F freeF ((Finset.card_le_card subset).trans size) (eq ▸ last) census)

theorem officialBudget (census : Census) {n m} (E : Matrix n m) (free : FourFree E)
    (size : E.card ≤ 10) (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 (n+m) C)
    (correct : ∀ x, PEqualNP.MetaComplexity.circuitFun (n+m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) :
    ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  obtain ⟨S,cv,budget⟩ := bound_of_counts (bip E) (full E free size census) C ao
    (funext (fun x => (correct x).trans (formula E x).symm))
  let P := Finset.univ.filter (fun i : Fin n => Fin.castAdd m i ∈ S)
  let Q := Finset.univ.filter (fun j : Fin m => Fin.natAdd n j ∈ S)
  let push : (P ⊕ Q) → S := Sum.elim
    (fun i => ⟨Fin.castAdd m i.val,(Finset.mem_filter.mp i.property).2⟩)
    (fun j => ⟨Fin.natAdd n j.val,(Finset.mem_filter.mp j.property).2⟩)
  have inj : Function.Injective push := by
    intro i j eq
    have h := congrArg Subtype.val eq
    cases i with
    | inl a => cases j with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Fin.castAdd_injective n m h))
      | inr b => exact (sides a.val b.val h).elim
    | inr a => cases j with
      | inl b => exact (sides b.val a.val h.symm).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext (Fin.natAdd_injective m n h))
  have bound : P.card + Q.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  rw [bip_edges] at budget
  refine ⟨P,Q,?_,by omega⟩
  intro e he
  exact (cv (bip_adjacency he)).imp (fun hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
    (fun hq => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)

end MatrixPacking3241

namespace CoreCensus
open LeafCore3241 SmallCores3241 ForestBipartite3241

inductive Shape | six | eight | ten | theta333 | theta244 deriving DecidableEq, Repr

abbrev order : Shape → Nat
  | .six => 6 | .eight => 8 | .ten => 10 | .theta333 => 8 | .theta244 => 9

instance (s : Shape) : NeZero (order s) := by cases s <;> exact ⟨by decide⟩

def edges : Shape → List (Nat × Nat)
  | .six => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
  | .eight => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
  | .ten => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
  | .theta333 => [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
  | .theta244 => [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]

abbrev source (s : Shape) := graph (order s) (edges s)

theorem counts_source (s) (h : ThetaPin3241.Lower Theta244Cores.theta 9) : Counts (source s) := by
  cases s
  · exact sixCounts
  · exact eightCounts
  · exact tenCounts
  · exact threeThreeThreeCounts
  · exact twoFourFourCounts h

def pairs (rows : List Nat) : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun (i,j) => (rows.getD i.val 0).testBit j.val

def matrix (rows : List Nat) := bip (pairs rows)

instance (rows : List Nat) : DecidableRel (matrix rows).Adj := by unfold matrix bip; infer_instance

structure Item where
  rows : List Nat
  shape : Shape
  forward : List Nat
  backward : List Nat
  deriving Repr

def emb (r : Item) (i : Fin (order r.shape)) : Fin 10 := Fin.ofNat 10 (r.forward.getD i.val 0)
def inv (r : Item) (i : Fin 10) : Fin (order r.shape) := Fin.ofNat (order r.shape) (r.backward.getD i.val 0)

def Certified (r : Item) : Prop :=
  (∀ u, inv r (emb r u) = u) ∧ ∀ i j, (matrix r.rows).Adj i j ↔
     emb r (inv r i) = i ∧ emb r (inv r j) = j ∧ (source r.shape).Adj (inv r i) (inv r j)

instance (r : Item) : Decidable (Certified r) := by unfold Certified; infer_instance

theorem count_item (r : Item) (hc : Certified r) (h : ThetaPin3241.Lower Theta244Cores.theta 9) :
    Counts (matrix r.rows) := by
  apply CoreTransfer3241.padded (source r.shape) (matrix r.rows) (emb r) (Function.LeftInverse.injective hc.1) _ (counts_source _ h)
  intro i j
  constructor
  · intro a
    obtain ⟨hi,hj,adj⟩ := (hc.2 i j).mp a
    exact ⟨_,_,adj,hi,hj⟩
  · rintro ⟨u,v,a,rfl,rfl⟩
    apply (hc.2 _ _).mpr
    rw [hc.1 u,hc.1 v]
    exact ⟨rfl,rfl,a⟩

end CoreCensus

namespace CoreCensus

def batch0 : List Item := [
  ⟨[3, 5, 6],.six,[1, 5, 0, 6, 2, 7],[2, 0, 4, 0, 0, 1, 3, 5, 0, 0]⟩,
  ⟨[3, 5, 6, 9, 10],.theta244,[5, 6, 0, 1, 7, 2, 3, 8, 4],[2, 3, 5, 6, 8, 0, 1, 4, 7, 0]⟩,
  ⟨[3, 5, 6, 9, 12],.theta244,[5, 7, 1, 0, 6, 2, 3, 8, 4],[3, 2, 5, 6, 8, 0, 4, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 10, 12],.theta244,[6, 7, 2, 0, 5, 1, 3, 8, 4],[3, 5, 2, 6, 8, 4, 0, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 17, 18],.theta244,[5, 6, 0, 1, 7, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 4, 0, 7]⟩,
  ⟨[3, 5, 6, 17, 20],.theta244,[5, 7, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 1, 0, 7]⟩]

def batch1 : List Item := [
  ⟨[3, 5, 6, 18, 20],.theta244,[6, 7, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 1, 0, 7]⟩,
  ⟨[3, 5, 9, 10, 12],.theta244,[5, 8, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 1, 0]⟩,
  ⟨[3, 5, 9, 14],.theta333,[3, 2, 1, 0, 5, 6, 7, 8],[3, 2, 1, 0, 0, 4, 5, 6, 7, 0]⟩,
  ⟨[3, 5, 10, 12],.eight,[1, 5, 0, 6, 2, 8, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 5, 0]⟩,
  ⟨[3, 5, 10, 20, 24],.ten,[1, 5, 0, 6, 2, 8, 4, 9, 3, 7],[2, 0, 4, 8, 6, 1, 3, 9, 5, 7]⟩,
  ⟨[3, 5, 12, 18, 24],.ten,[1, 5, 0, 6, 3, 9, 4, 8, 2, 7],[2, 0, 8, 4, 6, 1, 3, 9, 7, 5]⟩]

def batch2 : List Item := [
  ⟨[3, 5, 17, 18, 20],.theta244,[5, 9, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 0, 1]⟩,
  ⟨[3, 5, 17, 22],.theta333,[3, 2, 1, 0, 5, 6, 7, 9],[3, 2, 1, 0, 0, 4, 5, 6, 0, 7]⟩,
  ⟨[3, 5, 18, 20],.eight,[1, 5, 0, 6, 2, 9, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 0, 5]⟩,
  ⟨[3, 6, 9, 10, 12],.theta244,[6, 8, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 1, 0]⟩,
  ⟨[3, 6, 9, 12],.eight,[2, 5, 0, 6, 1, 7, 3, 8],[2, 4, 0, 6, 0, 1, 3, 5, 7, 0]⟩,
  ⟨[3, 6, 9, 20, 24],.ten,[2, 5, 0, 6, 1, 7, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 3, 5, 9, 7]⟩]

def batch3 : List Item := [
  ⟨[3, 6, 10, 13],.theta333,[3, 2, 1, 0, 6, 5, 7, 8],[3, 2, 1, 0, 0, 5, 4, 6, 7, 0]⟩,
  ⟨[3, 6, 12, 17, 24],.ten,[3, 5, 0, 6, 1, 7, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 3, 5, 7, 9]⟩,
  ⟨[3, 6, 17, 18, 20],.theta244,[6, 9, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 0, 1]⟩,
  ⟨[3, 6, 17, 20],.eight,[2, 5, 0, 6, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 3, 5, 0, 7]⟩,
  ⟨[3, 6, 18, 21],.theta333,[3, 2, 1, 0, 6, 5, 7, 9],[3, 2, 1, 0, 0, 5, 4, 6, 0, 7]⟩,
  ⟨[3, 9, 10],.six,[1, 5, 0, 6, 2, 8],[2, 0, 4, 0, 0, 1, 3, 0, 5, 0]⟩]

def batch4 : List Item := [
  ⟨[3, 9, 10, 17, 18],.theta244,[5, 6, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 0, 4, 7]⟩,
  ⟨[3, 9, 10, 17, 24],.theta244,[5, 8, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[3, 9, 10, 18, 24],.theta244,[6, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[3, 9, 12, 18, 20],.ten,[1, 5, 0, 6, 3, 9, 4, 7, 2, 8],[2, 0, 8, 4, 6, 1, 3, 7, 9, 5]⟩,
  ⟨[3, 9, 17, 18, 24],.theta244,[5, 9, 2, 0, 6, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[3, 9, 17, 26],.theta333,[3, 2, 1, 0, 5, 6, 8, 9],[3, 2, 1, 0, 0, 4, 5, 0, 6, 7]⟩]

def batch5 : List Item := [
  ⟨[3, 9, 18, 24],.eight,[1, 5, 0, 6, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 3, 0, 7, 5]⟩,
  ⟨[3, 10, 12, 17, 20],.ten,[3, 5, 0, 6, 1, 8, 2, 7, 4, 9],[2, 4, 6, 0, 8, 1, 3, 7, 5, 9]⟩,
  ⟨[3, 10, 17, 18, 24],.theta244,[6, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[3, 10, 17, 24],.eight,[2, 5, 0, 6, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 3, 0, 5, 7]⟩,
  ⟨[3, 10, 18, 25],.theta333,[3, 2, 1, 0, 6, 5, 8, 9],[3, 2, 1, 0, 0, 5, 4, 0, 6, 7]⟩,
  ⟨[3, 12, 21, 26],.theta244,[2, 3, 9, 5, 0, 6, 7, 1, 8],[4, 7, 0, 1, 0, 3, 5, 6, 8, 2]⟩]

def batch6 : List Item := [
  ⟨[3, 12, 22, 25],.theta244,[3, 2, 9, 5, 0, 6, 8, 1, 7],[4, 7, 1, 0, 0, 3, 5, 8, 6, 2]⟩,
  ⟨[3, 13, 20, 26],.theta244,[1, 3, 8, 5, 0, 6, 7, 2, 9],[4, 0, 7, 1, 0, 3, 5, 6, 2, 8]⟩,
  ⟨[3, 13, 22, 24],.theta244,[1, 2, 7, 5, 0, 6, 8, 3, 9],[4, 0, 1, 7, 0, 3, 5, 2, 6, 8]⟩,
  ⟨[3, 14, 20, 25],.theta244,[3, 1, 8, 5, 0, 6, 9, 2, 7],[4, 1, 7, 0, 0, 3, 5, 8, 2, 6]⟩,
  ⟨[3, 14, 21, 24],.theta244,[2, 1, 7, 5, 0, 6, 9, 3, 8],[4, 1, 0, 7, 0, 3, 5, 2, 8, 6]⟩,
  ⟨[3, 17, 18],.six,[1, 5, 0, 6, 2, 9],[2, 0, 4, 0, 0, 1, 3, 0, 0, 5]⟩]

def batch7 : List Item := [
  ⟨[5, 6, 9, 10],.eight,[2, 5, 0, 7, 1, 6, 3, 8],[2, 4, 0, 6, 0, 1, 5, 3, 7, 0]⟩,
  ⟨[5, 6, 9, 10, 12],.theta244,[7, 8, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 1, 0]⟩,
  ⟨[5, 6, 9, 18, 24],.ten,[2, 5, 0, 7, 1, 6, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 5, 3, 9, 7]⟩,
  ⟨[5, 6, 10, 17, 24],.ten,[3, 5, 0, 7, 1, 6, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 5, 3, 7, 9]⟩,
  ⟨[5, 6, 11, 12],.theta333,[2, 3, 1, 0, 7, 5, 6, 8],[3, 2, 0, 1, 0, 5, 6, 4, 7, 0]⟩,
  ⟨[5, 6, 17, 18],.eight,[2, 5, 0, 7, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 3, 0, 7]⟩]

def batch8 : List Item := [
  ⟨[5, 6, 17, 18, 20],.theta244,[7, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[5, 6, 19, 20],.theta333,[2, 3, 1, 0, 7, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 4, 0, 7]⟩,
  ⟨[5, 9, 10, 18, 20],.ten,[1, 5, 0, 7, 4, 9, 3, 6, 2, 8],[2, 0, 8, 6, 4, 1, 7, 3, 9, 5]⟩,
  ⟨[5, 9, 12],.six,[1, 5, 0, 7, 2, 8],[2, 0, 4, 0, 0, 1, 0, 3, 5, 0]⟩,
  ⟨[5, 9, 12, 17, 20],.theta244,[5, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[5, 9, 12, 17, 24],.theta244,[5, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩]

def batch9 : List Item := [
  ⟨[5, 9, 12, 20, 24],.theta244,[7, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[5, 9, 17, 20, 24],.theta244,[5, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩,
  ⟨[5, 9, 17, 28],.theta333,[3, 2, 1, 0, 5, 7, 8, 9],[3, 2, 1, 0, 0, 4, 0, 5, 6, 7]⟩,
  ⟨[5, 9, 20, 24],.eight,[1, 5, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 0, 3, 7, 5]⟩,
  ⟨[5, 10, 12, 17, 18],.ten,[3, 5, 0, 7, 2, 8, 1, 6, 4, 9],[2, 6, 4, 0, 8, 1, 7, 3, 5, 9]⟩,
  ⟨[5, 10, 19, 28],.theta244,[2, 3, 9, 5, 0, 7, 6, 1, 8],[4, 7, 0, 1, 0, 3, 6, 5, 8, 2]⟩]

def batch10 : List Item := [
  ⟨[5, 10, 22, 25],.theta244,[3, 2, 9, 5, 0, 7, 8, 1, 6],[4, 7, 1, 0, 0, 3, 8, 5, 6, 2]⟩,
  ⟨[5, 11, 18, 28],.theta244,[1, 3, 8, 5, 0, 7, 6, 2, 9],[4, 0, 7, 1, 0, 3, 6, 5, 2, 8]⟩,
  ⟨[5, 11, 22, 24],.theta244,[1, 2, 6, 5, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 3, 2, 5, 6, 8]⟩,
  ⟨[5, 12, 17, 20, 24],.theta244,[7, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[5, 12, 17, 24],.eight,[2, 5, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 0, 3, 5, 7]⟩,
  ⟨[5, 12, 20, 25],.theta333,[3, 2, 1, 0, 7, 5, 8, 9],[3, 2, 1, 0, 0, 5, 0, 4, 6, 7]⟩]

def batch11 : List Item := [
  ⟨[5, 14, 18, 25],.theta244,[3, 1, 8, 5, 0, 7, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 5, 2, 6]⟩,
  ⟨[5, 14, 19, 24],.theta244,[2, 1, 6, 5, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 3, 2, 5, 8, 6]⟩,
  ⟨[5, 17, 20],.six,[1, 5, 0, 7, 2, 9],[2, 0, 4, 0, 0, 1, 0, 3, 0, 5]⟩,
  ⟨[6, 9, 10, 17, 20],.ten,[3, 5, 1, 8, 2, 6, 0, 7, 4, 9],[6, 2, 4, 0, 8, 1, 5, 7, 3, 9]⟩,
  ⟨[6, 9, 12, 17, 18],.ten,[3, 5, 1, 8, 2, 7, 0, 6, 4, 9],[6, 2, 4, 0, 8, 1, 7, 5, 3, 9]⟩,
  ⟨[6, 9, 19, 28],.theta244,[2, 3, 9, 5, 1, 8, 6, 0, 7],[7, 4, 0, 1, 0, 3, 6, 8, 5, 2]⟩]

def batch12 : List Item := [
  ⟨[6, 9, 21, 26],.theta244,[2, 3, 9, 5, 1, 8, 7, 0, 6],[7, 4, 0, 1, 0, 3, 8, 6, 5, 2]⟩,
  ⟨[6, 10, 12],.six,[1, 6, 0, 7, 2, 8],[2, 0, 4, 0, 0, 0, 1, 3, 5, 0]⟩,
  ⟨[6, 10, 12, 18, 20],.theta244,[6, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[6, 10, 12, 18, 24],.theta244,[6, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩,
  ⟨[6, 10, 12, 20, 24],.theta244,[7, 8, 2, 0, 6, 1, 3, 9, 4],[3, 5, 2, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[6, 10, 18, 20, 24],.theta244,[6, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩]

def batch13 : List Item := [
  ⟨[6, 10, 18, 28],.theta333,[3, 2, 1, 0, 6, 7, 8, 9],[3, 2, 1, 0, 0, 0, 4, 5, 6, 7]⟩,
  ⟨[6, 10, 20, 24],.eight,[1, 6, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 0, 1, 3, 7, 5]⟩,
  ⟨[6, 11, 17, 28],.theta244,[1, 3, 8, 5, 2, 9, 6, 0, 7],[7, 0, 4, 1, 0, 3, 6, 8, 2, 5]⟩,
  ⟨[6, 11, 21, 24],.theta244,[1, 2, 5, 6, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 2, 3, 5, 6, 8]⟩,
  ⟨[6, 12, 18, 20, 24],.theta244,[7, 9, 3, 0, 6, 2, 1, 8, 4],[3, 6, 5, 2, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[6, 12, 18, 24],.eight,[2, 6, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 0, 1, 3, 5, 7]⟩]

def batch14 : List Item := [
  ⟨[6, 12, 20, 26],.theta333,[3, 2, 1, 0, 7, 6, 8, 9],[3, 2, 1, 0, 0, 0, 5, 4, 6, 7]⟩,
  ⟨[6, 13, 17, 26],.theta244,[1, 3, 8, 5, 2, 9, 7, 0, 6],[7, 0, 4, 1, 0, 3, 8, 6, 2, 5]⟩,
  ⟨[6, 13, 19, 24],.theta244,[2, 1, 5, 6, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 2, 3, 5, 8, 6]⟩,
  ⟨[6, 18, 20],.six,[1, 6, 0, 7, 2, 9],[2, 0, 4, 0, 0, 0, 1, 3, 0, 5]⟩,
  ⟨[7, 9, 10, 12],.theta333,[0, 3, 2, 1, 8, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 4, 0]⟩,
  ⟨[7, 9, 18, 28],.theta244,[0, 3, 7, 5, 1, 8, 6, 2, 9],[0, 4, 7, 1, 0, 3, 6, 2, 5, 8]⟩]

def batch15 : List Item := [
  ⟨[7, 9, 20, 26],.theta244,[0, 3, 6, 5, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 3, 2, 6, 5, 8]⟩,
  ⟨[7, 10, 17, 28],.theta244,[0, 3, 7, 5, 2, 9, 6, 1, 8],[0, 7, 4, 1, 0, 3, 6, 2, 8, 5]⟩,
  ⟨[7, 10, 20, 25],.theta244,[0, 3, 5, 6, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 2, 3, 6, 5, 8]⟩,
  ⟨[7, 12, 17, 26],.theta244,[0, 3, 6, 5, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 3, 2, 6, 8, 5]⟩,
  ⟨[7, 12, 18, 25],.theta244,[0, 3, 5, 6, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 2, 3, 6, 8, 5]⟩,
  ⟨[7, 17, 18, 20],.theta333,[0, 3, 2, 1, 9, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 0, 4]⟩]

def batch16 : List Item := [
  ⟨[9, 10, 17, 18],.eight,[2, 5, 0, 8, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 0, 3, 7]⟩,
  ⟨[9, 10, 17, 18, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[9, 10, 19, 24],.theta333,[2, 3, 1, 0, 8, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 0, 4, 7]⟩,
  ⟨[9, 12, 17, 20],.eight,[2, 5, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 0, 5, 3, 7]⟩,
  ⟨[9, 12, 17, 20, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 7, 3],[3, 6, 5, 8, 2, 4, 0, 7, 0, 1]⟩,
  ⟨[9, 12, 21, 24],.theta333,[2, 3, 1, 0, 8, 5, 7, 9],[3, 2, 0, 1, 0, 5, 0, 6, 4, 7]⟩]

def batch17 : List Item := [
  ⟨[9, 14, 18, 21],.theta244,[3, 1, 7, 5, 0, 8, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 2, 5, 6]⟩,
  ⟨[9, 14, 19, 20],.theta244,[2, 1, 6, 5, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 3, 2, 8, 5, 6]⟩,
  ⟨[9, 17, 24],.six,[1, 5, 0, 8, 2, 9],[2, 0, 4, 0, 0, 1, 0, 0, 3, 5]⟩,
  ⟨[10, 12, 18, 20],.eight,[2, 6, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 0, 1, 5, 3, 7]⟩,
  ⟨[10, 12, 18, 20, 24],.theta244,[8, 9, 4, 0, 6, 2, 1, 7, 3],[3, 6, 5, 8, 2, 0, 4, 7, 0, 1]⟩,
  ⟨[10, 12, 22, 24],.theta333,[2, 3, 1, 0, 8, 6, 7, 9],[3, 2, 0, 1, 0, 0, 5, 6, 4, 7]⟩]

def batch18 : List Item := [
  ⟨[10, 13, 17, 22],.theta244,[1, 3, 7, 5, 2, 9, 8, 0, 6],[7, 0, 4, 1, 0, 3, 8, 2, 6, 5]⟩,
  ⟨[10, 13, 19, 20],.theta244,[2, 1, 5, 6, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 2, 3, 8, 5, 6]⟩,
  ⟨[10, 18, 24],.six,[1, 6, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 1, 0, 3, 5]⟩,
  ⟨[11, 12, 17, 22],.theta244,[0, 3, 6, 5, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 3, 2, 8, 6, 5]⟩,
  ⟨[11, 12, 18, 21],.theta244,[0, 3, 5, 6, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 2, 3, 8, 6, 5]⟩,
  ⟨[11, 17, 18, 24],.theta333,[0, 3, 2, 1, 9, 5, 6, 8],[0, 3, 2, 1, 0, 5, 6, 0, 7, 4]⟩]

def batch19 : List Item := [
  ⟨[12, 20, 24],.six,[1, 7, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 0, 1, 3, 5]⟩,
  ⟨[13, 17, 20, 24],.theta333,[0, 3, 2, 1, 9, 5, 7, 8],[0, 3, 2, 1, 0, 5, 0, 6, 7, 4]⟩,
  ⟨[14, 18, 20, 24],.theta333,[0, 3, 2, 1, 9, 6, 7, 8],[0, 3, 2, 1, 0, 0, 5, 6, 7, 4]⟩]

def items := batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6 ++ batch7 ++ batch8 ++ batch9 ++ batch10 ++ batch11 ++ batch12 ++ batch13 ++ batch14 ++ batch15 ++ batch16 ++ batch17 ++ batch18 ++ batch19

end CoreCensus

namespace CoreCensus

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check0 : batch0.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check1 : batch1.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check2 : batch2.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check3 : batch3.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check4 : batch4.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check5 : batch5.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check6 : batch6.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check7 : batch7.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check8 : batch8.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check9 : batch9.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check10 : batch10.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check11 : batch11.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check12 : batch12.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check13 : batch13.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check14 : batch14.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check15 : batch15.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check16 : batch16.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check17 : batch17.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check18 : batch18.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check19 : batch19.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem validated {r : Item} (hr : r ∈ items) : Certified r := by
  have h : items.all (fun e => decide (Certified e)) = true := by
    simp only [items,List.all_append,check0,check1,check2,check3,check4,check5,check6,check7,check8,check9,check10,check11,check12,check13,check14,check15,check16,check17,check18,check19,Bool.true_and]
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

end CoreCensus

namespace CoreCensus
open List

def wt (r : Nat) := (r % 2) + (r / 2 % 2) + (r / 4 % 2) + (r / 8 % 2) + (r / 16 % 2)

def eligible (lo budget : Nat) (pre : List Nat) (r : Nat) : Bool :=
  decide (lo < r ∧ 2 ≤ wt r ∧ wt r ≤ budget) && pre.all (fun p => decide (wt (p &&& r) ≤ 1))

def generate : Nat → Nat → Nat → List Nat → List (List Nat)
  | 0, _, _, pre => [pre]
  | k+1, lo, budget, pre => pre :: ((range 32).filter (eligible lo budget pre)).flatMap
      fun r => generate k r (budget - wt r) (pre ++ [r])

theorem current_mem (k lo budget) (pre : List Nat) : pre ∈ generate k lo budget pre := by
  cases k <;> simp [generate]

def Compatible (r s : Nat) := r < s ∧ wt (r &&& s) ≤ 1

theorem listed (ys : List Nat) (fuel lo budget : Nat) (pre : List Nat)
    (len : ys.length ≤ fuel) (bounds : ∀ r ∈ ys, lo < r ∧ r < 32 ∧ 2 ≤ wt r)
    (total : (ys.map wt).sum ≤ budget) (pair : ys.Pairwise Compatible)
    (past : ∀ r ∈ ys, ∀ p ∈ pre, wt (p &&& r) ≤ 1) :
    pre ++ ys ∈ generate fuel lo budget pre := by
  induction ys generalizing fuel lo budget pre with
  | nil => simpa using current_mem fuel lo budget pre
  | cons r rs ih =>
    cases fuel with
    | zero => simp at len
    | succ k =>
      obtain ⟨rtop,rr,rlower⟩ := bounds r (by simp)
      have cost : wt r + (rs.map wt).sum ≤ budget := by simpa using total
      obtain ⟨first,tail⟩ := List.pairwise_cons.mp pair
      have elig : eligible lo budget pre r = true := by
        unfold eligible
        apply Bool.and_eq_true_iff.mpr
        exact ⟨decide_eq_true ⟨rtop,rlower,by omega⟩,
          List.all_eq_true.mpr (fun p hp => decide_eq_true (past r (by simp) p hp))⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr rr,elig⟩,?_⟩
      have hmem := ih k r (budget - wt r) (pre ++ [r]) (by simpa using len)
          (fun s hs => ⟨(first s hs).1,(bounds s (by simp [hs])).2⟩) (by omega) tail (by
            intro s hs p hp
            rcases List.mem_append.mp hp with old | new
            · exact past s (by simp [hs]) p old
            · obtain rfl : p = r := by simpa using new
              exact (first s hs).2)
      simpa only [List.append_assoc,List.singleton_append] using hmem

def liveCols (xs : List Nat) : Bool :=
  (range 5).all fun i => decide (xs.countP (fun r => r.testBit i) ≠ 1)

def recognized (xs : List Nat) : Bool := items.any (fun c => c.rows == xs)

def acceptedRows (xs : List Nat) : Bool := xs.isEmpty || !liveCols xs || recognized xs

theorem exists_item {xs : List Nat} (h : recognized xs = true) : ∃ r ∈ items, r.rows = xs := by
  obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp h
  exact ⟨r,hr,by simpa using eq⟩

end CoreCensus

namespace CoreCensus
open List

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first3 : (generate 4 3 (10 - wt 3) [3]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first5 : (generate 4 5 (10 - wt 5) [5]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first6 : (generate 4 6 (10 - wt 6) [6]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first7 : (generate 4 7 (10 - wt 7) [7]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first9 : (generate 4 9 (10 - wt 9) [9]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first10 : (generate 4 10 (10 - wt 10) [10]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first11 : (generate 4 11 (10 - wt 11) [11]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first12 : (generate 4 12 (10 - wt 12) [12]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first13 : (generate 4 13 (10 - wt 13) [13]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first14 : (generate 4 14 (10 - wt 14) [14]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first15 : (generate 4 15 (10 - wt 15) [15]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first17 : (generate 4 17 (10 - wt 17) [17]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first18 : (generate 4 18 (10 - wt 18) [18]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first19 : (generate 4 19 (10 - wt 19) [19]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first20 : (generate 4 20 (10 - wt 20) [20]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first21 : (generate 4 21 (10 - wt 21) [21]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first22 : (generate 4 22 (10 - wt 22) [22]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first23 : (generate 4 23 (10 - wt 23) [23]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first24 : (generate 4 24 (10 - wt 24) [24]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first25 : (generate 4 25 (10 - wt 25) [25]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first26 : (generate 4 26 (10 - wt 26) [26]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first27 : (generate 4 27 (10 - wt 27) [27]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first28 : (generate 4 28 (10 - wt 28) [28]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first29 : (generate 4 29 (10 - wt 29) [29]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first30 : (generate 4 30 (10 - wt 30) [30]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first31 : (generate 4 31 (10 - wt 31) [31]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem all_rows : (generate 5 0 10 []).all acceptedRows = true := by
  have opts : (range 32).filter (eligible 0 10 []) = [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  change (acceptedRows [] && (((range 32).filter (eligible 0 10 [])).flatMap (fun r => generate 4 r (10 - wt r) ([] ++ [r]))).all acceptedRows) = true
  rw [List.all_flatMap,opts]
  have empty : acceptedRows [] = true := rfl
  simp only [empty,List.nil_append,List.all_cons,List.all_nil,Bool.true_and,first3,first5,first6,first7,first9,first10,first11,first12,first13,first14,first15,first17,first18,first19,first20,first21,first22,first23,first24,first25,first26,first27,first28,first29,first30,first31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem recognized_of_rows (xs : List Nat) (hne : xs ≠ [])
    (len : xs.length ≤ 5) (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r)
    (w : (xs.map wt).sum ≤ 10) (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) :
    ∃ c ∈ items, c.rows = xs := by
  have mem := listed xs 5 0 10 [] len bounds w s (by simp)
  have result := List.all_eq_true.mp all_rows xs (by simpa using mem)
  apply exists_item
  have notEmpty : xs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simpa [acceptedRows,notEmpty,hcol] using result

end CoreCensus

namespace CoreCensus
open LeafCore3241

theorem sorted_counts (xs : List Nat) (hne : xs ≠ []) (len : xs.length ≤ 5)
    (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) (w : (xs.map wt).sum ≤ 10)
    (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) : Counts (matrix xs) := by
  obtain ⟨r,member,rfl⟩ := recognized_of_rows xs hne len bounds w s hcol
  exact count_item r (validated member) Theta244.nine

end CoreCensus

namespace NormalizeCores3241
open CoreCensus GraphPacking3241 MatrixPacking3241 LeafCore3241 ForestBipartite3241

def encode (x : Fin 5 → Bool) : Nat :=
  (x 0).toNat + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16

theorem encode_bound : ∀ x : Fin 5 → Bool, encode x < 32 := by decide +kernel
theorem encode_bit : ∀ (x : Fin 5 → Bool) (i : Fin 5), (encode x).testBit i.val = x i := by decide +kernel
theorem encode_weight : ∀ x : Fin 5 → Bool, wt (encode x) = (Finset.univ.filter (fun i => x i)).card := by
  decide +kernel
theorem weight_two : ∀ (r : Fin 32) (a b : Fin 5), a ≠ b → r.val.testBit a.val = true →
    r.val.testBit b.val = true → 2 ≤ wt r.val := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem weight_shared : ∀ a b : Fin 32,
    (∀ i j : Fin 5, a.val.testBit i.val = true → b.val.testBit i.val = true →
      a.val.testBit j.val = true → b.val.testBit j.val = true → i = j) → wt (a.val &&& b.val) ≤ 1 := by
  decide +kernel

def mask (E : Matrix 5 5) (i : Fin 5) : Nat := encode fun j => decide ((i,j) ∈ E)

theorem bit_iff (E : Matrix 5 5) (i j : Fin 5) : (mask E i).testBit j.val = true ↔ (i,j) ∈ E := by
  simp [mask,encode_bit]

theorem wt_fiber (E : Matrix 5 5) (i : Fin 5) :
    wt (mask E i) = (E.filter (fun p => p.1 = i)).card := by
  let T := Finset.univ.filter (fun j : Fin 5 => (i,j) ∈ E)
  have eq : E.filter (fun p => p.1 = i) = T.image (Prod.mk i) := by
    ext p
    constructor
    · rintro h
      obtain ⟨he,pi⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [← pi] using he⟩,
        Prod.ext pi.symm rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2,rfl⟩
  have wt_eq := encode_weight (fun j : Fin 5 => decide ((i,j) ∈ E))
  rw [eq,Finset.card_image_of_injective _ (fun j k h => congrArg Prod.snd h)]
  simpa [mask,T] using wt_eq

theorem separated (E : Matrix 5 5) (free : FourFree E) (p q : Fin 5) (ne : p ≠ q) :
    wt (mask E p &&& mask E q) ≤ 1 := by
  apply weight_shared ⟨mask E p,encode_bound _⟩ ⟨mask E q,encode_bound _⟩
  intro i j pi qi pj qj
  by_contra ij
  exact free p q i j ne ij ⟨(bit_iff E p i).mp pi,(bit_iff E p j).mp pj,
    (bit_iff E q i).mp qi,(bit_iff E q j).mp qj⟩

theorem row_bounds (E : Matrix 5 5) (rich : HasPartners E) (p : Fin 5) (hp : p ∈ Rows E) :
    0 < mask E p ∧ mask E p < 32 ∧ 2 ≤ wt (mask E p) := by
  obtain ⟨⟨a,b⟩,ab,eq⟩ := Finset.mem_image.mp hp
  change a = p at eq
  subst a
  obtain ⟨c,cb,pc⟩ := (rich p b ab).1
  have positive : mask E p ≠ 0 := by
    intro bad
    have bit := (bit_iff E p b).mpr ab
    simp [bad] at bit
  exact ⟨Nat.pos_of_ne_zero positive,encode_bound _,
    weight_two ⟨mask E p,encode_bound _⟩ c b cb ((bit_iff E p c).mpr pc) ((bit_iff E p b).mpr ab)⟩

theorem mask_inj (E : Matrix 5 5) (free : FourFree E) (rich : HasPartners E) :
    Set.InjOn (mask E) (Rows E : Set (Fin 5)) := by
  intro a ha b _ eq
  by_contra ne
  have cap := separated E free a b ne
  rw [← eq,Nat.and_self] at cap
  have low := (row_bounds E rich a ha).2.2
  omega

theorem sum_list (xs : List Nat) (f : Nat → Nat) (distinct : xs.Nodup) :
    (xs.map f).sum = ∑ i ∈ xs.toFinset, f i := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := List.nodup_cons.mp distinct
    simp [h.1,ih h.2]

def SortedProof := ∀ xs : List Nat, xs ≠ [] → xs.length ≤ 5 →
  (∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) → (xs.map wt).sum ≤ 10 →
  xs.Pairwise Compatible → liveCols xs = true → Counts (matrix xs)

theorem census_of_sorted (done : SortedProof) : MatrixPacking3241.Census := by
  classical
  intro E size free last
  by_cases zero : E = ∅
  · have none (u v) : ¬ (bip E).Adj u v := by
      rintro ⟨_,⟨e,he,_,_⟩ | ⟨e,he,_,_⟩⟩ <;> simp [zero] at he
    have card : (bip E).edgeFinset.card = 0 := by rw [bip_edges,zero]; rfl
    refine ⟨?_,∅,?_,ThetaPin3241.lower_zero _⟩
    · rw [card]
      exact ThetaPin3241.lower_zero _
    · exact fun a b ab => (none a b ab).elim
  have rich := (leafless_iff E).mp last
  let A := (Rows E).image (mask E)
  let xs := A.sort
  have inj := mask_inj E free rich
  have cap : A.card ≤ 5 := (Finset.card_image_le).trans (Finset.card_le_univ (Rows E))
  have len : xs.length ≤ 5 := by simpa [xs] using cap
  have mem (r : Nat) : r ∈ xs ↔ ∃ p ∈ Rows E, mask E p = r := by simp [xs,A]
  have nonempty : xs ≠ [] := by
    obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    have hm := (mem _).mpr ⟨e.1,Finset.mem_image_of_mem _ he,rfl⟩
    intro eq
    simp [eq] at hm
  have rn : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    exact row_bounds E rich p hp
  have total : (xs.map wt).sum = E.card := by
    rw [sum_list _ _ (A.sort_nodup _)]
    have eq : xs.toFinset = A := by ext r; simp [xs]
    rw [eq,Finset.sum_image]
    · rw [Finset.card_eq_sum_card_image Prod.fst E]
      exact Finset.sum_congr rfl (fun x _ => wt_fiber E x)
    · exact inj
  have sorted : xs.Pairwise (· < ·) := A.sortedLT_sort.pairwise
  have pair : xs.Pairwise Compatible := by
    apply sorted.imp_of_mem
    intro a b ha hb lt
    obtain ⟨p,_,rfl⟩ := (mem a).mp ha
    obtain ⟨q,_,rfl⟩ := (mem b).mp hb
    exact ⟨lt,separated E free p q (fun eq => (Nat.ne_of_lt lt) (congrArg (mask E) eq))⟩
  have cols : liveCols xs = true := by
    apply List.all_eq_true.mpr
    intro j hj
    apply decide_eq_true
    intro unique
    have pos : 0 < xs.countP (fun r => r.testBit j) := by omega
    obtain ⟨r,hr,bit⟩ := List.countP_pos_iff.mp pos
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    let c : Fin 5 := ⟨j,List.mem_range.mp hj⟩
    have pc : (p,c) ∈ E := (bit_iff E p c).mp bit
    obtain ⟨q,qp,qc⟩ := (rich p c pc).2
    have hq : q ∈ Rows E := Finset.mem_image_of_mem Prod.fst qc
    have hq' := (mem _).mpr ⟨q,hq,rfl⟩
    have diff := ThetaPin3241.count_one_unique xs (fun a => a.testBit j) _ _ hq' hr
      ((bit_iff E q c).mpr qc) bit (by omega)
    exact qp (inj hq hp diff)
  have ok := done xs nonempty len rn (total ▸ size) pair cols
  let val (p : Rows E) : A := ⟨mask E p.val,Finset.mem_image_of_mem _ p.property⟩
  have bij : Function.Bijective val := by
    refine ⟨fun p q eq => Subtype.ext (inj p.property q.property (congrArg Subtype.val eq)),?_⟩
    intro a
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨p,hp⟩,Subtype.ext eq⟩
  let order := (Equiv.ofBijective val bij).trans ((A.orderIsoOfFin rfl).symm.toEquiv)
  let r (p : Rows E) : Fin 5 := (order p).castLE cap
  have ri : Function.Injective r := (Fin.castLE_injective cap).comp order.injective
  let c (p : Cols E) : Fin 5 := p.val
  have read (p : Rows E) : xs.getD (r p).val 0 = mask E p.val := by
    have hl : (r p).val < xs.length := by simp [xs,r]
    rw [List.getD_eq_getElem _ _ hl]
    have ev := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply (val p))
    exact ev
  have pe : pack E r c = pairs xs := by
    ext ij
    obtain ⟨i,j⟩ := ij
    change (i,j) ∈ pack E r c ↔ (i,j) ∈ pairs xs
    rw [decode]
    simp only [pairs,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨e,rfl,rfl⟩
      rw [read]
      exact (bit_iff E _ _).mpr e.property
    · intro bit
      have hl : i.val < xs.length := by
        by_contra! bad
        rw [List.getD_eq_default _ _ bad] at bit
        simp at bit
      have ha : i.val < A.card := by simpa [xs] using hl
      let p := order.symm ⟨i.val,ha⟩
      have pos : r p = i := Fin.ext (by simp [r,p])
      rw [← pos,read] at bit
      have cell := (bit_iff E p.val j).mp bit
      let e : E := ⟨(p.val,j),cell⟩
      exact ⟨e,pos,rfl⟩
  apply unpack_counts E r c ri Subtype.val_injective
  rw [pe]
  exact ok

theorem census : MatrixPacking3241.Census := census_of_sorted CoreCensus.sorted_counts

end NormalizeCores3241

end Census3457
namespace Builder3457
namespace CleanStars

open PEqualNP PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def OkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, OkM g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ (∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)) ∧
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD (m + j) false = true → P (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {P} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n P F s)
    (hs : s ≤ s') : Bld n P F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev, ha⟩

theorem bld_congr {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n P F s)
    (e : ∀ x, F x = H x) : Bld n P H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e], ha⟩

theorem bld_var {n : ℕ} {P} (i : Fin n) : Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_, ?_⟩
  · intro w _
    simp [wiresFrom]
  · intro j g hj
    simp at hj

theorem bld_bin {n : ℕ} {P} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (hA : op = GateOp.and → ∀ x, c (F x) (H x) = true → P x) :
    Bld n P (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1, ha1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2, ha2⟩ := h2 (m + gs1.length) (by omega)
  have main : ∀ w : List Bool, w.length = m →
      (wiresFrom gs2 (wiresFrom gs1 w)).length = m + gs1.length + gs2.length ∧
      (wiresFrom (gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩]) w)
        = wiresFrom gs2 (wiresFrom gs1 w) ++
          [c (F (fun i : Fin n => w.getD i false)) (H (fun i : Fin n => w.getD i false))] ∧
      (fun i : Fin n => (wiresFrom gs1 w).getD i false) = (fun i : Fin n => w.getD i false) := by
    intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have hvw : (fun i : Fin n => v.getD i false) = (fun i : Fin n => w.getD i false) := by
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    refine ⟨lu, ?_, hvw⟩
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv, hvw]
    rw [e1, e2]
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [OkM, h]
  · simp; omega
  · simp; omega
  · intro w hw
    obtain ⟨lu, hm2, _⟩ := main w hw
    rw [hm2, ← lu, getD_snoc_eq]
  · intro j g hj hop' w hw hval
    obtain ⟨lu, hm2, hvw⟩ := main w hw
    rw [hm2] at hval
    rcases lt_or_ge j gs1.length with hj1 | hj1
    · have hg : gs1[j]? = some g := by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hj1] at hj
        exact hj
      apply ha1 j g hg hop' w hw
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_wiresFrom _ _ _ (by
        rw [length_wiresFrom, hw]; omega)] at hval
      exact hval
    · rcases lt_or_ge j (gs1.length + gs2.length) with hj2 | hj2
      · obtain ⟨j', rfl⟩ : ∃ j', j = gs1.length + j' := ⟨j - gs1.length, by omega⟩
        have hg : gs2[j']? = some g := by
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (by omega)] at hj
          simpa using hj
        have lv : (wiresFrom gs1 w).length = m + gs1.length := by rw [length_wiresFrom, hw]
        have := ha2 j' g hg hop' (wiresFrom gs1 w) lv
        rw [hvw] at this
        apply this
        rw [getD_snoc_ne _ _ _ _ (by omega)] at hval
        rw [← add_assoc] at hval
        exact hval
      · have hjeq : j = gs1.length + gs2.length := by
          by_contra hne
          have : (gs1 ++ gs2 ++ [(⟨op, [o1, o2]⟩ : Gate)])[j]? = none :=
            List.getElem?_eq_none (by simp; omega)
          rw [this] at hj
          simp at hj
        subst hjeq
        have hg : g = ⟨op, [o1, o2]⟩ := by
          rw [List.getElem?_append_right (by simp)] at hj
          simp at hj
          exact hj.symm
        subst hg
        rw [show m + (gs1.length + gs2.length) = (wiresFrom gs2 (wiresFrom gs1 w)).length by
          omega, getD_snoc_eq] at hval
        exact hA hop' _ hval

theorem bld_or {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) : Bld n P (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by intro h; cases h)

theorem bld_and {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) (hP : ∀ x, F x = true → H x = true → P x) :
    Bld n P (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by
      intro _ x hx
      simp only [Bool.and_eq_true] at hx
      exact hP x hx.1 hx.2)

theorem bld_anyList {n : ℕ} {P} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var (P := P) v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} {P} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
theorem bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) :
    ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) → (∀ x, (∃ e ∈ E, ∀ v ∈ e, x v = true) → P x) →
    Bld n P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc _
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hPE
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    have p2 : ∀ x, (∃ e ∈ E2, ∀ v ∈ e, x v = true) → P x := by
      rintro x ⟨e, he, h⟩
      exact hPE x ⟨e, (Finset.mem_filter.1 he).1, h⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have star : E1.Nonempty → Bld n P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var (P := P) t) (bld_anyFinset S hSne) (by
        intro x ht hv
        rw [decide_eq_true_iff] at hv
        obtain ⟨v, hv, hxv⟩ := hv
        refine hPE x ⟨s(t, v), (Finset.mem_filter.1 (Finset.mem_filter.1 hv).2).1, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2 p2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2 p2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x)
        = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · obtain ⟨i0, j0, h0⟩ := hE
    have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
    have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hc a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    have conv : ∀ x : Fin n → Bool, (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      intro x
      constructor
      · rintro ⟨e, he, h⟩
        revert he h
        refine Sym2.ind (fun a b => ?_) e
        intro he h
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨s(i, j), by simpa using hij, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
    have hb := bld_edges n (fun x => ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) T
      G.edgeFinset hne cov (fun x h => (conv x).1 h)
    obtain ⟨gs, out, ok, len, _, ev, ha⟩ := hb n le_rfl
    have hx : ∀ x : Fin n → Bool, (fun i : Fin n => (List.ofFn x).getD i false) = x := by
      intro x; funext i; exact getD_ofFn x i
    refine ⟨⟨gs, out⟩, ok, ?_, len, ?_⟩
    · intro x
      have e := ev (List.ofFn x) (by simp)
      rw [hx] at e
      simp only [Circuit.eval, wires_eq, e]
      exact decide_eq_decide.2 (conv x)
    · intro j g hj hop x hv
      have := ha j g hj hop (List.ofFn x) (by simp) hv
      rw [hx] at this
      exact this
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro x
      have : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u, v, h, _⟩; exact hE ⟨u, v, h⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil, this, decide_false]
      exact List.getD_eq_default _ _ (by simp)
    · simp [Circuit.size]
    · intro j g hj; simp at hj

end CleanStars

end Builder3457
namespace Forest3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457 Ports3451
variable {N : Nat}
def Positive (I : Fin N → Fin N → Prop) (x : Fin (N+N)→Bool) :=
  ∃ p l,I p l ∧ x (pt p)=true ∧ x (ln l)=true

lemma separate (p l : Fin N) : pt p < ln l := by
  change p.val<N+l.val
  have h := p.isLt
  omega

lemma unit_off (I : Fin N → Fin N → Prop) (v : Fin (N+N)) :
    ¬Positive I (fun k => decide (k=v)) := by
  rintro ⟨p,l,_,a,b⟩
  exact (ne_of_lt (separate p l)) ((of_decide_eq_true a).trans (of_decide_eq_true b).symm)

lemma nonpair_off (I : Fin N → Fin N → Prop) (p l : Fin N) (no : ¬I p l) :
    ¬Positive I (pairInput p l) := by
  rintro ⟨a,b,ab,x,y⟩
  have xp := (of_decide_eq_true x : pt a=pt p ∨ pt a=ln l).resolve_right (ne_of_lt (separate a l))
  have yl := (of_decide_eq_true y : ln b=pt p ∨ ln b=ln l).resolve_left (ne_of_gt (separate p b))
  have pa : a=p := Fin.ext (congrArg (fun z : Fin (N+N)=>z.val) xp)
  have v := congrArg Fin.val yl
  change N+b.val=N+l.val at v
  have bl : b=l := Fin.ext (Nat.add_left_cancel v)
  exact no (pa ▸ bl ▸ ab)


def tidy (m : Nat) (g : Gate) : Gate :=
  if g.op=.and then
    if ∀ i∈g.inputs,i < m then g else zeroGate
  else ⟨g.op,g.inputs.filter (· < m)⟩

def tidyList : Nat  →  List Gate  →  List Gate
  | _, [] => []
  | m, g::gs => tidy m g :: tidyList (m+1) gs

lemma shape (m : Nat) (g : Gate) (ok : g.op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length ≤ 2) :
    ((tidy m g).op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ (tidy m g).inputs.length ≤ 2) ∧
    (∀ i ∈ (tidy m g).inputs,i < m) ∧ ((tidy m g).op=.and  →  g.op=.and) := by
  unfold tidy
  split_ifs with ha hb
  · exact ⟨ok,hb,fun _=>ha⟩
  · simp [zeroGate]
  · refine ⟨⟨ok.1,(List.length_filter_le ..).trans ok.2⟩,?_,id⟩
    intro i hi
    simpa using (List.mem_filter.mp hi).2

lemma tidy_val (g : Gate) (w : List Bool) (m : Nat) (hw : w.length=m) (hop : g.op=.and ∨ g.op=.or) :
    value (tidy m g) w=value g w := by
  rcases hop with ha|ho
  · by_cases hb : ∀ i∈g.inputs,i < m
    · unfold tidy
      rw [if_pos ha,if_pos hb]
    · push_neg at hb
      obtain ⟨i,hi,ho⟩ := hb
      have no : ¬∀ i∈g.inputs,i < m := fun h=>Nat.not_lt_of_ge ho (h i hi)
      apply Bool.eq_iff_iff.mpr
      simp only [tidy,if_pos ha,if_neg no]
      have z : w.getD i false=false := List.getD_eq_default _ _ (by omega)
      constructor
      · simp [zeroGate,value,GateOp.eval]
      · intro on
        have all : ∀t∈g.inputs,w.getD t false=true := by simpa [value,ha,GateOp.eval,List.all_eq_true] using on
        exact False.elim (Bool.false_ne_true (z.symm.trans (all i hi)))
  · have hn : g.op≠.and := by simp [ho]
    unfold tidy
    rw [if_neg hn]
    apply Bool.eq_iff_iff.mpr
    simp only [value,ho,GateOp.eval,List.any_map,List.any_eq_true,
      Function.comp_apply,id_eq,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨i,⟨hi,_⟩,v⟩; exact ⟨i,hi,v⟩
    · rintro ⟨i,hi,v⟩
      refine ⟨i,⟨hi,?_⟩,v⟩
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at v
      contradiction

lemma tidies (gs : List Gate) (ok : ∀g∈gs,g.op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2) (m : Nat) :
    (tidyList m gs).length=gs.length ∧
    (∀g∈tidyList m gs,g.op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2) ∧
    (∀ j (h : j<(tidyList m gs).length), ∀i∈(tidyList m gs)[j].inputs,i < m+j) ∧
    (∀ j (h : j<(tidyList m gs).length) (h' : j<gs.length),
       (tidyList m gs)[j].op=.and  →  gs[j].op=.and) ∧
    (∀w : List Bool,w.length=m → run (tidyList m gs) w=run gs w) := by
  induction gs generalizing m with
  | nil => simp [tidyList,run]
  | cons g gs ih =>
    have o := ok g List.mem_cons_self
    obtain ⟨sz,mono,back,orig,eq⟩ := ih (fun a h=>ok a (List.mem_cons_of_mem _ h)) (m+1)
    obtain ⟨sg,bg,ag⟩ := shape m g o
    refine ⟨by simp [tidyList,sz],?_,?_,?_,?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl|ht
      · exact sg
      · exact mono a ht
    · intro j hj i hi
      cases j with
      | zero => simpa using bg i hi
      | succ j =>
        have h := back j (by simpa [tidyList] using hj) i hi
        omega
    · intro j hj hk
      cases j with
      | zero => exact ag
      | succ j => exact orig j (by simpa [tidyList] using hj) (by simpa using hk)
    · intro w hw
      change run (tidyList (m+1) gs) (w++[value (tidy m g) w])=run gs (w++[value g w])
      rw [tidy_val g w m hw (by simpa using o.1)]
      exact eq _ (by simp [hw])

def graph (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l,I p l ∧ ((u=pt p ∧ v=ln l) ∨ (v=pt p ∧ u=ln l))
  symm := ⟨by
    intro u v
    rintro ⟨p,l,inc,h|h⟩
    · exact ⟨p,l,inc,Or.inr h⟩
    · exact ⟨p,l,inc,Or.inl h⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨p,l,inc,h|h⟩ <;> exact (ne_of_lt (separate p l)) (h.1.symm.trans h.2)⟩

lemma graph_spec (I : Fin N → Fin N → Prop) (x : Fin (N+N) → Bool) :
    (∃u v,(graph I).Adj u v ∧ x u=true ∧ x v=true) ↔ Positive I x := by
  constructor
  · rintro ⟨u,v,⟨p,l,inc,h|h⟩,a,b⟩
    · exact ⟨p,l,inc,h.1 ▸ a,h.2 ▸ b⟩
    · exact ⟨p,l,inc,h.1 ▸ b,h.2 ▸ a⟩
  · rintro ⟨p,l,inc,a,b⟩
    exact ⟨pt p,ln l,⟨p,l,inc,Or.inl ⟨rfl,rfl⟩⟩,a,b⟩

theorem budget (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C) (co : spec I C)
    (small : ∃ T : Finset (Fin (N+N)),
      (∀u v,(graph I).Adj u v  →  u∈T ∨ v∈T) ∧
        (graph I).edgeSet.ncard + T.card - 1 ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let G := graph I
  have cand : ∃ A : Circuit, Monotone2 A ∧
        (∀x : Fin (N+N) → Bool,A.eval (List.ofFn x) = decide (∃u v,G.Adj u v ∧ x u=true ∧ x v=true)) ∧
        A.size≤C.size ∧
        ∀ j (g : Gate), A.gates[j]?=some g  →  g.op=.and  →  ∀x : Fin (N+N) → Bool,
          (A.wires (List.ofFn x)).getD (N+N+j) false=true  →  ∃u v,G.Adj u v ∧ x u=true ∧ x v=true := by
    obtain ⟨T,cov,cost⟩ := small
    obtain ⟨A,ma,ev,sz,aclean⟩ := Builder3457.CleanStars.main _ G T cov
    have e : G.edgeSet.ncard=G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    change G.edgeSet.ncard+T.card-1 ≤ C.size at cost
    rw [e] at cost
    exact ⟨A,ma,ev,sz.trans cost,aclean⟩
  obtain ⟨A,ma,ev,sz,aclean⟩ := cand
  let D : Circuit := ⟨tidyList (N+N) A.gates,A.output⟩
  obtain ⟨len,md,bd,orig,eq⟩ := tidies A.gates ma (N+N)
  have back : ReadsBack (N+N) D := fun j hj i hi=>bd j hj i (by rwa [← atEq D j hj])
  have wires (x : Fin (N+N) → Bool) : D.wires (List.ofFn x)=A.wires (List.ofFn x) := eq _ (by simp)
  have exactD : spec I D := by
    intro x
    change (D.wires _).getD A.output false=true ↔ _
    rw [wires]
    change A.eval _=true ↔ _
    rw [ev,decide_eq_true_eq]
    exact graph_spec I x
  have anyOff (x : Fin (N+N) → Bool) (neg : ¬Positive I x) (j : Nat)
      (hj : j<D.gates.length) (op : (gateAt D j).op=.and) :
      (D.wires (List.ofFn x)).getD (N+N+j) false=false := by
    have ha : j<A.gates.length := by change j<(tidyList _ _).length at hj; omega
    have ga : A.gates[j].op=.and := orig j hj ha (by rwa [←atEq D j hj])
    rw [wires]
    cases h : (A.wires (List.ofFn x)).getD (N+N+j) false with
    | false => rfl
    | true =>
      exact False.elim (neg ((graph_spec I x).mp (aclean j A.gates[j] (by simp [ha]) ga x h)))
  refine ⟨D,md,back,(show D.size=A.size from len).le.trans sz,exactD,?_,?_⟩
  · intro j hj op p l no
    exact anyOff _ (nonpair_off I p l no) j hj op
  · intro j hj op
    exact ⟨fun p=>anyOff _ (unit_off I (pt p)) j hj op, fun l=>anyOff _ (unit_off I (ln l)) j hj op⟩


end Forest3457
namespace Census3457.MatrixPacking3241
open LeafCore3241 ForestBipartite3241 GraphPacking3241
theorem boundedHeart {n m} (E : Matrix n m) (free : FourFree E) (size : ∀ F ⊆ E, HasPartners F → F.card ≤ 10)
    (census : Census) : Counts (bip E) := by
  classical
  apply peel_to_core (bip E)
  intro H _ sub last
  let F := E.filter (fun p => H.Adj (Left p.1) (Right p.2))
  have eq : H = bip F := by
    ext i j
    constructor
    · intro ij
      rcases sub ij with ⟨ne,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact bip_adjacency (Finset.mem_filter.mpr ⟨he,ij⟩ : e ∈ F)
      · exact (bip_adjacency (Finset.mem_filter.mpr ⟨he,ij.symm⟩ : e ∈ F)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact (Finset.mem_filter.mp he).2
      · exact ((Finset.mem_filter.mp he).2).symm
  have subset : F ⊆ E := Finset.filter_subset _ _
  have freeF : FourFree F := fun p q l s pq ls ⟨a,b,c,d⟩ =>
    free p q l s pq ls ⟨subset a,subset b,subset c,subset d⟩
  have carry {K L : SimpleGraph (Fin (n+m))} [d : DecidableRel K.Adj] [e : DecidableRel L.Adj]
      (same : K = L) (ok : Counts L) : Counts K := by
    subst L
    have sameInst : d = e := Subsingleton.elim _ _
    cases sameInst
    exact ok
  exact carry eq (compressed F freeF (size F subset ((leafless_iff _).mp (eq ▸ last))) (eq ▸ last) census)

end Census3457.MatrixPacking3241
namespace Heart3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Mask3457 Census3457 Census3457.LeafCore3241 Census3457.ForestBipartite3241
open Census3457.GraphPacking3241 Census3457.MatrixPacking3241

variable {N : Nat}

def SmallHeart (I : Fin N → Fin N → Prop) : Prop :=
  ∀ F : Finset (Fin N × Fin N), (∀ e ∈ F, I e.1 e.2) → HasPartners F → F.card ≤ 10

theorem normalization (I : Fin N → Fin N → Prop) (C : Circuit)
    (free : ∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s))
    (small : SmallHeart I) (hm : Monotone2 C) (co : spec I C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E]
  have geom : Forest3457.graph I = bip E := by
    ext i j
    constructor
    · rintro ⟨p,l,inc,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
      · exact bip_adjacency ((mem p l).mpr inc)
      · exact (bip_adjacency ((mem p l).mpr inc)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩|⟨e,he,rfl,rfl⟩⟩
      · exact ⟨e.1,e.2,(mem _ _).mp he,Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨e.1,e.2,(mem _ _).mp he,Or.inr ⟨rfl,rfl⟩⟩
  have freeE : FourFree E := by
    rintro p q l s pq ls ⟨a,b,c,d⟩
    exact free p q l s pq ls ⟨(mem _ _).mp a,(mem _ _).mp b,(mem _ _).mp c,(mem _ _).mp d⟩
  have counts := boundedHeart E freeE
    (fun F sub pair => small F (fun e he => (mem _ _).mp (sub he)) pair) NormalizeCores3241.census
  have cgraph (x : Fin (N+N) → Bool) : C.eval (List.ofFn x)=true ↔
      ∃ u v,(bip E).Adj u v ∧ x u=true ∧ x v=true := by
    rw [←geom]
    exact (co x).trans (Forest3457.graph_spec I x).symm
  obtain ⟨K,km,kf,ks⟩ := Binary3457.main_aux (N+N) (bip E) _ C hm cgraph
  obtain ⟨T,cov,bound⟩ := bound_of_counts (bip E) counts K km (kf.trans (ordinary_eq _))
  apply Forest3457.budget I C hm co
  refine ⟨T,?_,?_⟩
  · intro i j ij
    exact cov (geom ▸ ij)
  · rw [geom,←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
    omega

end Heart3457
namespace Heart3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Mask3457 Census3457.GraphPacking3241

private abbrev Charge := Fin 4 ⊕ {e : Fin 4 × Fin 4 // e.1 < e.2}

private theorem charges : Fintype.card Charge = 10 := by decide +kernel

theorem four_by_four (N : ℕ) (small : N ≤ 4) (E : Finset (Fin N × Fin N)) (free : FourFree E) :
    E.card ≤ 10 := by
  classical
  by_cases empty : E = ∅
  · simp [empty]
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  let row (p : Fin N) := Finset.univ.filter (fun l : Fin N => (p,l) ∈ E)
  let a (p : Fin N) : Fin N := if h : (row p).Nonempty then (row p).min' h else e.2
  have amin (p l : Fin N) (pl : (p,l) ∈ E) : (p,a p) ∈ E ∧ a p ≤ l := by
    have mem : l ∈ row p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩
    have ne : (row p).Nonempty := ⟨l,mem⟩
    simp only [a,dif_pos ne]
    exact ⟨(Finset.mem_filter.mp ((row p).min'_mem ne)).2,(row p).min'_le l mem⟩
  let embed (p : Fin N) : Fin 4 := p.castLE small
  have inj : Function.Injective embed := Fin.castLE_injective small
  let charge (t : E) : Charge :=
    if h : t.val.2 = a t.val.1 then Sum.inl (embed t.val.1)
    else Sum.inr ⟨(embed (a t.val.1),embed t.val.2),
      (show a t.val.1 < t.val.2 from lt_of_le_of_ne (amin _ _ t.property).2 (Ne.symm h))⟩
  have distinct : Function.Injective charge := by
    rintro ⟨⟨p,l⟩,pl⟩ ⟨⟨q,k⟩,qk⟩ eq
    by_cases hl : l=a p <;> by_cases hk : k=a q
    · have ep : embed p=embed q := Sum.inl.inj (by simpa only [charge,dif_pos hl,dif_pos hk] using eq)
      have pq := inj ep
      exact Subtype.ext (Prod.ext pq (hl.trans ((congrArg a pq).trans hk.symm)))
    · simp [charge,hl,hk] at eq
    · simp [charge,hl,hk] at eq
    · have en := Sum.inr.inj (by simpa only [charge,dif_neg hl,dif_neg hk] using eq :
          (Sum.inr _ : Charge) = Sum.inr _)
      have ap : a p=a q := inj (congrArg (fun s : {v : Fin 4 × Fin 4 // v.1<v.2} => s.val.1) en)
      have lk : l=k := inj (congrArg (fun s : {v : Fin 4 × Fin 4 // v.1<v.2} => s.val.2) en)
      have pq : p=q := by
        by_contra neq
        apply free p q (a p) l neq (Ne.symm hl)
        exact ⟨(amin p l pl).1,pl,ap ▸ (amin q k qk).1,lk ▸ qk⟩
      exact Subtype.ext (Prod.ext pq lk)
  have total := Fintype.card_le_of_injective charge distinct
  simpa only [Fintype.card_coe,charges] using total

theorem atMostFour {N : Nat} (small : N ≤ 4) (I : Fin N → Fin N → Prop) (C : Circuit)
    (free : ∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s))
    (hm : Monotone2 C) (co : spec I C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  apply normalization I C free _ hm co
  intro F sub _
  apply four_by_four N small F
  rintro p q l s pq ls ⟨u,v,w,x⟩
  exact free p q l s pq ls ⟨sub _ u,sub _ v,sub _ w,sub _ x⟩

end Heart3457
namespace SharedFilters3457
open Ports3451
open scoped Sym2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Ports3451 Mask3457
variable {N : Nat}

def port {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (i : Fin (n+pre.length)) :=
  (run pre (List.ofFn x)).getD i.val false

lemma run_size (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[value g w])).length=_
    rw [ih]
    simp
    omega

lemma true_inputs {n : Nat} (pre : List Gate) (x : Fin n → Bool) :
    List.ofFn (port pre x)=run pre (List.ofFn x) := by
  apply List.ext_getElem
  · simp [run_size]
  · intro i hi hj
    have lt : i<n+pre.length := by simpa [run_size] using hj
    simp only [List.getElem_ofFn]
    change (run pre (List.ofFn x)).getD i false = _
    exact List.getD_eq_getElem _ _ hj

/-- A clean star circuit over arbitrary available prefix wires can be placed after the prefix
with only its own physical cost. The virtual wire valuations may have arbitrary dependencies. -/
theorem prefix_budget (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (G : SimpleGraph (Fin ((N+N)+pre.length))) [DecidableRel G.Adj]
    (T : Finset (Fin ((N+N)+pre.length))) (cover : ∀u v,G.Adj u v → u∈T ∨ v∈T)
    (paid : pre.length+(G.edgeFinset.card+T.card-1)≤C.size)
    (sem : ∀x, (∃u v,G.Adj u v ∧ port pre x u=true ∧ port pre x v=true) ↔ Repair3457.Positive I x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let n := N+N
  let m := n+pre.length
  obtain ⟨A,ma,ev,sz,low⟩ := Builder3457.CleanStars.main m G T cover
  let B : Circuit := ⟨pre++A.gates,A.output⟩
  have mb : Monotone2 B := by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact ⟨by simp [(pure g h).1],(pure g h).2⟩
    · exact ma g h
  have wires (x : Fin n→Bool) : B.wires (List.ofFn x)=A.wires (List.ofFn (port pre x)) := by
    change run (pre++A.gates) (List.ofFn x)=run A.gates _
    rw [true_inputs]
    simp [run,List.foldl_append]
  have eqB (x : Fin n→Bool) : B.eval (List.ofFn x)=true ↔ Repair3457.Positive I x := by
    change (B.wires _).getD A.output false=true ↔ _
    rw [wires]
    change A.eval (List.ofFn (port pre x))=true ↔ _
    rw [ev,decide_eq_true_eq]
    exact sem x
  have cleanB (j : Nat) (hj : j<B.gates.length) (andj : B.gates[j].op=.and) (x : Fin n→Bool)
      (on : (B.wires (List.ofFn x)).getD (n+j) false=true) : Repair3457.Positive I x := by
    change (pre++A.gates)[j].op=.and at andj
    by_cases early : j<pre.length
    · rw [List.getElem_append_left early] at andj
      rw [(pure _ (List.getElem_mem early)).1] at andj
      contradiction
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt early)
      have kA : k<A.gates.length := by
        change pre.length+k<(pre++A.gates).length at hj
        simp at hj
        exact hj
      have ka : A.gates[k].op=.and := by
        simpa only [List.getElem_append_right (by omega : pre.length≤pre.length+k),Nat.add_sub_cancel_left] using andj
      have hit : (A.wires (List.ofFn (port pre x))).getD (m+k) false=true := by
        rw [wires] at on
        simpa only [m,Nat.add_assoc] using on
      exact (sem x).mp (low k A.gates[k] (by simp [kA]) ka (port pre x) hit)
  let D : Circuit := ⟨Forest3457.tidyList n B.gates,B.output⟩
  obtain ⟨len,md,bk,orig,eq⟩ := Forest3457.tidies B.gates mb n
  have sized : D.size=B.size := len
  have budget : D.size≤C.size := by
    rw [sized]
    change (pre++A.gates).length ≤ _
    rw [List.length_append]
    exact (Nat.add_le_add_left sz _).trans paid
  have result (x : Fin n→Bool) : D.wires (List.ofFn x)=B.wires (List.ofFn x) := eq _ (by simp)
  have clean (x : Fin n→Bool) (neg : ¬Repair3457.Positive I x) (j : Nat) (hj : j<D.gates.length)
      (op : (gateAt D j).op=.and) : (D.wires (List.ofFn x)).getD (n+j) false=false := by
    have hB : j<B.gates.length := by change j<(Forest3457.tidyList _ _).length at hj; omega
    have aB := orig j hj hB (by rwa [←atEq D j hj])
    rw [result]
    exact Bool.eq_false_iff.mpr (fun h => neg (cleanB j hB aB x h))
  refine ⟨D,md,fun j hj i hi=>bk j hj i (by rwa [←atEq D j hj]),budget,?_,?_,?_⟩
  · intro x
    change (D.wires _).getD B.output false=true ↔ _
    rw [result]
    exact eqB x
  · intro j hj op p l no
    exact clean _ (Repair3457.nonpair_off I p l no) j hj op
  · intro j hj op
    exact ⟨fun p => clean _ (Repair3457.unit_off I (pt p)) j hj op,
           fun l => clean _ (Repair3457.unit_off I (ln l)) j hj op⟩

end SharedFilters3457

namespace SharedFilters3457
open Ports3451
open scoped Sym2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : Nat}

theorem virtual_edges (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (m : Nat) (M : m=(N+N)+pre.length)
    (Arms : Finset (Fin m × Fin m)) (T : Finset (Fin m))
    (dist : ∀ e∈Arms,e.1≠e.2) (cov : ∀ e∈Arms,e.1∈T ∨ e.2∈T)
    (paid : pre.length+(Arms.card+T.card-1)≤C.size)
    (sem : ∀x, (∃e∈Arms,port pre x (e.1.cast M)=true ∧ port pre x (e.2.cast M)=true) ↔ Repair3457.Positive I x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  subst m
  classical
  let G := SimpleGraph.fromRel (fun u v => (u,v) ∈ Arms)
  have directed (e) (he : e∈Arms) : G.Adj e.1 e.2 := ⟨dist e he,Or.inl he⟩
  apply prefix_budget I C pre pure G T
  · rintro u v ⟨_,uv|vu⟩
    · exact cov (u,v) uv
    · exact (cov (v,u) vu).symm
  · let tag (e : Fin ((N+N)+pre.length) × Fin ((N+N)+pre.length)) := s(e.1,e.2)
    have sub : G.edgeFinset ⊆ Arms.image tag := by
      intro z hz
      induction z using Sym2.ind with
      | _ a b =>
        rcases SimpleGraph.mem_edgeFinset.mp hz with ⟨_,ab|ba⟩
        · exact Finset.mem_image.mpr ⟨(a,b),ab,rfl⟩
        · exact Finset.mem_image.mpr ⟨(b,a),ba,Sym2.eq_swap⟩
    have card := (Finset.card_le_card sub).trans Finset.card_image_le
    omega
  · intro x
    rw [←sem x]
    constructor
    · rintro ⟨u,v,⟨_,uv|vu⟩,a,b⟩
      · exact ⟨(u,v),uv,a,b⟩
      · exact ⟨(v,u),vu,b,a⟩
    · rintro ⟨e,he,a,b⟩
      exact ⟨e.1,e.2,directed e he,a,b⟩

abbrev VPort (N : Nat) (pre : List Gate) := Fin ((N+N)+pre.length)

private theorem two_images {N : Nat} {pre : List Gate} {Y : Type*} [Fintype Y] (h k : Y → VPort N pre) :
      (Finset.univ.image h ∪ Finset.univ.image k).card ≤ 2*Fintype.card Y := by
    have lim := Finset.card_union_le (Finset.univ.image h) (Finset.univ.image k)
    have h1 := Finset.card_image_le (f:=h) (s:=Finset.univ)
    have h2 := Finset.card_image_le (f:=k) (s:=Finset.univ)
    rw [Finset.card_univ] at h1 h2
    omega

theorem two_sided {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (u v : R→VPort N pre) (a b : S→VPort N pre)
    (all row line : Finset (R×S)) (rs : row⊆all) (ls : line⊆all)
    (rd : ∀ e∈row, a e.2≠v e.1) (ld : ∀e∈line,u e.1≠b e.2)
    (paid : pre.length+(2*all.card+Fintype.card R+Fintype.card S-1)≤C.size)
    (sem : ∀x, ((∃e∈row,port pre x (a e.2)=true ∧ port pre x (v e.1)=true) ∨
      (∃e∈line,port pre x (u e.1)=true ∧ port pre x (b e.2)=true)) ↔ Repair3457.Positive I x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let f (e : R×S) := (a e.2,v e.1)
  let g (e : R×S) := (u e.1,b e.2)
  let A := row.image f ∪ line.image g
  have which (z) : z∈A ↔ (∃e∈row,f e=z) ∨ (∃e∈line,g e=z) := by
    simp only [A,Finset.mem_union,Finset.mem_image]
  have ca : A.card≤2*all.card := by
    have bound := Finset.card_union_le (row.image f) (line.image g)
    have fr : (row.image f).card≤all.card := Finset.card_image_le.trans (Finset.card_le_card rs)
    have fl : (line.image g).card≤all.card := Finset.card_image_le.trans (Finset.card_le_card ls)
    dsimp [A]; omega
  let U := Finset.univ.image u ∪ Finset.univ.image v
  let V := Finset.univ.image a ∪ Finset.univ.image b
  have smallCover : ∃T : Finset (VPort N pre),T.card≤Fintype.card R+Fintype.card S ∧
      ∀z∈A,z.1∈T ∨ z.2∈T := by
    by_cases small : Fintype.card R ≤ Fintype.card S
    · refine ⟨U,by have h := two_images u v; dsimp [U]; omega,?_⟩
      intro z hz
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem v (Finset.mem_univ e.1)))
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ e.1)))
    · refine ⟨V,by have h := two_images a b; dsimp [V]; omega,?_⟩
      intro z hz
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ e.2)))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ e.2)))
  obtain ⟨T,ct,covers⟩ := smallCover
  refine virtual_edges I C pre pure _ rfl A T ?_ covers (by omega) ?_
  · intro z hz
    rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
    · exact rd e he
    · exact ld e he
  · intro x
    rw [←sem x]
    constructor
    · rintro ⟨z,hz,p,q⟩
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inl ⟨e,he,p,q⟩
      · exact Or.inr ⟨e,he,p,q⟩
    · rintro (⟨e,he,p,q⟩|⟨e,he,p,q⟩)
      · exact ⟨f e,(which _).mpr (Or.inl ⟨e,he,rfl⟩),p,q⟩
      · exact ⟨g e,(which _).mpr (Or.inr ⟨e,he,rfl⟩),p,q⟩

end SharedFilters3457
namespace SharedFilters3457
open Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : Nat}

/-- A rectangle wire may feed many mixed selectors and each selector may serve many rectangles.
Both sorts of sharing are charged just once. Only acceptance of actual pair inputs is needed. -/
theorem mixed_selectors {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (U V : R→Finset (Fin N)) (u v : R→VPort N pre)
    (us : ∀r x,port pre x (u r)=true ↔ ∃p∈U r,x (pt p)=true)
    (vs : ∀r x,port pre x (v r)=true ↔ ∃l∈V r,x (ln l)=true)
    (a b : S→Fin N) (all : Finset (R×S))
    (pairs : ∀p l,I p l ↔ ∃e∈all,p∈U e.1 ∧ l∈V e.1 ∧ (p=a e.2 ∨ l=b e.2))
    (paid : pre.length+(2*all.card+Fintype.card R+Fintype.card S-1)≤C.size) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let raw (i : Fin (N+N)) : VPort N pre := ⟨i.val,by have := i.isLt;omega⟩
  have source (i : Fin (N+N)) (x : Fin (N+N)→Bool) : port pre x (raw i)=x i := by
    change (run pre (List.ofFn x)).getD i.val false=x i
    rw [keep _ _ _ (by simp)]
    simp
  let row := all.filter (fun e => a e.2∈U e.1)
  let line := all.filter (fun e => b e.2∈V e.1)
  refine two_sided I C pre pure u v (fun t=>raw (pt (a t))) (fun t=>raw (ln (b t))) all row line
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) ?_ ?_ paid ?_
  · intro e _ eq
    let x (i : Fin (N+N)) := decide (i=pt (a e.2))
    have on : port pre x (v e.1)=true := by rw [←eq,source]; simp [x]
    obtain ⟨l,_,ll⟩ := (vs _ _).mp on
    exact (ne_of_gt (Repair3457.separate (a e.2) l)) (of_decide_eq_true ll)
  · intro e _ eq
    let x (i : Fin (N+N)) := decide (i=ln (b e.2))
    have on : port pre x (u e.1)=true := by rw [eq,source]; simp [x]
    obtain ⟨p,_,pp⟩ := (us _ _).mp on
    exact (ne_of_lt (Repair3457.separate p (b e.2))) (of_decide_eq_true pp)
  · intro x
    constructor
    · rintro (⟨e,mem,hp,hv⟩|⟨e,mem,hu,hl⟩)
      · obtain ⟨l,lv,lx⟩ := (vs _ _).mp hv
        obtain ⟨he,au⟩ := Finset.mem_filter.mp mem
        exact ⟨a e.2,l,(pairs _ _).mpr ⟨e,he,au,lv,Or.inl rfl⟩,(source _ x) ▸ hp,lx⟩
      · obtain ⟨p,pu,px⟩ := (us _ _).mp hu
        obtain ⟨he,bv⟩ := Finset.mem_filter.mp mem
        exact ⟨p,b e.2,(pairs _ _).mpr ⟨e,he,pu,bv,Or.inr rfl⟩,px,(source _ x) ▸ hl⟩
    · rintro ⟨p,l,pl,px,lx⟩
      obtain ⟨e,he,pu,lv,rfl|rfl⟩ := (pairs _ _).mp pl
      · exact Or.inl ⟨e,Finset.mem_filter.mpr ⟨he,pu⟩,(source _ x).trans px,(vs _ _).mpr ⟨l,lv,lx⟩⟩
      · exact Or.inr ⟨e,Finset.mem_filter.mpr ⟨he,lv⟩,(us _ _).mpr ⟨p,pu,px⟩,(source _ x).trans lx⟩

end SharedFilters3457
namespace SharedFilters3457
open Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : Nat}
theorem two_pool {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (u v : R→VPort N pre) (a b : R×S→VPort N pre)
    (all row line : Finset (R×S)) (rs : row⊆all) (ls : line⊆all)
    (rd : ∀ e∈row, a e≠v e.1) (ld : ∀e∈line,u e.1≠b e)
    (q : Nat) (rawPool : Finset (VPort N pre)) (poolCard : rawPool.card≤2*q)
    (pa : ∀e∈row,a e∈rawPool) (pb : ∀e∈line,b e∈rawPool)
    (paid : pre.length+(2*all.card+Fintype.card R+q-1)≤C.size)
    (sem : ∀x, ((∃e∈row,port pre x (a e)=true ∧ port pre x (v e.1)=true) ∨
      (∃e∈line,port pre x (u e.1)=true ∧ port pre x (b e)=true)) ↔ Repair3457.Positive I x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let f (e : R×S) := (a e,v e.1)
  let g (e : R×S) := (u e.1,b e)
  let A := row.image f ∪ line.image g
  have which (z) : z∈A ↔ (∃e∈row,f e=z) ∨ (∃e∈line,g e=z) := by
    simp only [A,Finset.mem_union,Finset.mem_image]
  have ca : A.card≤2*all.card := by
    have bound := Finset.card_union_le (row.image f) (line.image g)
    have fr : (row.image f).card≤all.card := Finset.card_image_le.trans (Finset.card_le_card rs)
    have fl : (line.image g).card≤all.card := Finset.card_image_le.trans (Finset.card_le_card ls)
    dsimp [A]; omega
  let U := Finset.univ.image u ∪ Finset.univ.image v
  have smallCover : ∃T : Finset (VPort N pre),T.card≤Fintype.card R+q ∧
      ∀z∈A,z.1∈T ∨ z.2∈T := by
    by_cases small : Fintype.card R ≤ q
    · refine ⟨U,by have h := two_images u v; dsimp [U]; omega,?_⟩
      intro z hz
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem v (Finset.mem_univ e.1)))
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ e.1)))
    · refine ⟨rawPool,by omega,?_⟩
      intro z hz
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inl (pa e he)
      · exact Or.inr (pb e he)
  obtain ⟨T,ct,covers⟩ := smallCover
  refine virtual_edges I C pre pure _ rfl A T ?_ covers (by omega) ?_
  · intro z hz
    rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
    · exact rd e he
    · exact ld e he
  · intro x
    rw [←sem x]
    constructor
    · rintro ⟨z,hz,p,q⟩
      rcases (which _).mp hz with ⟨e,he,rfl⟩|⟨e,he,rfl⟩
      · exact Or.inl ⟨e,he,p,q⟩
      · exact Or.inr ⟨e,he,p,q⟩
    · rintro (⟨e,he,p,q⟩|⟨e,he,p,q⟩)
      · exact ⟨f e,(which _).mpr (Or.inl ⟨e,he,rfl⟩),p,q⟩
      · exact ⟨g e,(which _).mpr (Or.inr ⟨e,he,rfl⟩),p,q⟩


end SharedFilters3457
namespace SharedFilters3457
open Ports3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : Nat}

theorem wide_selectors {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (positiveN : 0<N) (I : Fin N→Fin N→Prop) (C : Circuit) (pre : List Gate)
    (free : ∀p q l k,p≠q → l≠k → ¬(I p l ∧ I p k ∧ I q l ∧ I q k))
    (pure : ∀g∈pre,g.op=.or ∧ g.inputs.length≤2)
    (U V : R→Finset (Fin N)) (u v : R→VPort N pre)
    (us : ∀r x,port pre x (u r)=true ↔ ∃p∈U r,x (pt p)=true)
    (vs : ∀r x,port pre x (v r)=true ↔ ∃l∈V r,x (ln l)=true)
    (A B : S→Finset (Fin N)) (all : Finset (R×S))
    (wide : ∀e∈all,1<(U e.1).card ∧ 1<(V e.1).card)
    (pairs : ∀p l,I p l ↔ ∃e∈all,p∈U e.1 ∧ l∈V e.1 ∧ (p∈A e.2 ∨ l∈B e.2))
    (q : Nat) (inputs : Finset (Fin (N+N))) (small : inputs.card≤2*q)
    (rows : ∀t p,p∈A t → pt p∈inputs) (cols : ∀t l,l∈B t → ln l∈inputs)
    (paid : pre.length+(2*all.card+Fintype.card R+q-1)≤C.size) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let raw (i : Fin (N+N)) : VPort N pre := ⟨i.val,by have := i.isLt;omega⟩
  have source (i : Fin (N+N)) (x : Fin (N+N)→Bool) : port pre x (raw i)=x i := by
    change (run pre (List.ofFn x)).getD i.val false=x i
    rw [keep _ _ _ (by simp)]
    simp
  let X (e : R×S) := U e.1 ∩ A e.2
  let Y (e : R×S) := V e.1 ∩ B e.2
  let p (e : R×S) : Fin N := if h : (X e).Nonempty then h.choose else ⟨0,positiveN⟩
  let l (e : R×S) : Fin N := if h : (Y e).Nonempty then h.choose else ⟨0,positiveN⟩
  have xp (e) (h : (X e).Nonempty) : p e∈X e := by simpa only [p,dif_pos h] using h.choose_spec
  have yl (e) (h : (Y e).Nonempty) : l e∈Y e := by simpa only [l,dif_pos h] using h.choose_spec
  have singletonX (e) (he : e∈all) (i : Fin N) (hi : i∈X e) : i=p e := by
    by_contra ne
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (wide e he).2
    have other := Finset.mem_inter.mp (xp e ⟨i,hi⟩)
    obtain ⟨ir,iq⟩ := Finset.mem_inter.mp hi
    exact free i (p e) a b ne ab
      ⟨(pairs _ _).mpr ⟨e,he,ir,ha,Or.inl iq⟩,(pairs _ _).mpr ⟨e,he,ir,hb,Or.inl iq⟩,
       (pairs _ _).mpr ⟨e,he,other.1,ha,Or.inl other.2⟩,(pairs _ _).mpr ⟨e,he,other.1,hb,Or.inl other.2⟩⟩
  have singletonY (e) (he : e∈all) (j : Fin N) (hj : j∈Y e) : j=l e := by
    by_contra ne
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (wide e he).1
    have other := Finset.mem_inter.mp (yl e ⟨j,hj⟩)
    obtain ⟨jr,jq⟩ := Finset.mem_inter.mp hj
    exact free a b j (l e) ab ne
      ⟨(pairs _ _).mpr ⟨e,he,ha,jr,Or.inr jq⟩,(pairs _ _).mpr ⟨e,he,ha,other.1,Or.inr other.2⟩,
       (pairs _ _).mpr ⟨e,he,hb,jr,Or.inr jq⟩,(pairs _ _).mpr ⟨e,he,hb,other.1,Or.inr other.2⟩⟩
  let row := all.filter (fun e => (X e).Nonempty)
  let line := all.filter (fun e => (Y e).Nonempty)
  refine two_pool I C pre pure u v (fun e=>raw (pt (p e))) (fun e=>raw (ln (l e))) all row line
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) ?_ ?_ q (inputs.image raw)
      (Finset.card_image_le.trans small) ?_ ?_ paid ?_
  · intro e _ eq
    let x (i : Fin (N+N)) := decide (i=pt (p e))
    have on : port pre x (v e.1)=true := by rw [←eq,source]; simp [x]
    obtain ⟨j,_,hit⟩ := (vs _ _).mp on
    exact (ne_of_gt (Repair3457.separate (p e) j)) (of_decide_eq_true hit)
  · intro e _ eq
    let x (i : Fin (N+N)) := decide (i=ln (l e))
    have on : port pre x (u e.1)=true := by rw [eq,source]; simp [x]
    obtain ⟨i,_,hit⟩ := (us _ _).mp on
    exact (ne_of_lt (Repair3457.separate i (l e))) (of_decide_eq_true hit)
  · intro e mem
    exact Finset.mem_image_of_mem raw (rows _ _ (Finset.mem_inter.mp (xp e (Finset.mem_filter.mp mem).2)).2)
  · intro e mem
    exact Finset.mem_image_of_mem raw (cols _ _ (Finset.mem_inter.mp (yl e (Finset.mem_filter.mp mem).2)).2)
  · intro x
    constructor
    · rintro (⟨e,mem,hp,hv⟩|⟨e,mem,hu,hl⟩)
      · obtain ⟨j,jv,jx⟩ := (vs _ _).mp hv
        obtain ⟨he,non⟩ := Finset.mem_filter.mp mem
        obtain ⟨pr,pa⟩ := Finset.mem_inter.mp (xp e non)
        exact ⟨p e,j,(pairs _ _).mpr ⟨e,he,pr,jv,Or.inl pa⟩,(source _ x) ▸ hp,jx⟩
      · obtain ⟨i,iu,ix⟩ := (us _ _).mp hu
        obtain ⟨he,non⟩ := Finset.mem_filter.mp mem
        obtain ⟨lv,lb⟩ := Finset.mem_inter.mp (yl e non)
        exact ⟨i,l e,(pairs _ _).mpr ⟨e,he,iu,lv,Or.inr lb⟩,ix,(source _ x) ▸ hl⟩
    · rintro ⟨i,j,ij,ix,jx⟩
      obtain ⟨e,he,iu,jv,ia|jb⟩ := (pairs _ _).mp ij
      · have hi : i∈X e := Finset.mem_inter.mpr ⟨iu,ia⟩
        have eq := singletonX e he i hi
        exact Or.inl ⟨e,Finset.mem_filter.mpr ⟨he,i,hi⟩,(source _ x).trans (eq ▸ ix),(vs _ _).mpr ⟨j,jv,jx⟩⟩
      · have hj : j∈Y e := Finset.mem_inter.mpr ⟨jv,jb⟩
        have eq := singletonY e he j hj
        exact Or.inr ⟨e,Finset.mem_filter.mpr ⟨he,j,hj⟩,(us _ _).mpr ⟨i,iu,ix⟩,(source _ x).trans (eq ▸ jx)⟩

end SharedFilters3457

namespace SharedFilters3457
open Ports3451
variable {P L : Type*} [DecidableEq P] [DecidableEq L]

def Pass (K : Finset (P×L)) (p : P) (l : L) : Prop :=
  ∀e∈K,p=e.1 ∨ l=e.2

/-- An arbitrary conjunction of mixed two-literal selectors has one of four possible
minimal-pair profiles. In the last case only the two crossed pairs can survive. -/
theorem classify (K : Finset (P×L)) (ne : K.Nonempty) :
    (∃a b,K={(a,b)} ∧ ∀p l, Pass K p l ↔ p=a ∨ l=b) ∨
    (∃a,∀p l,Pass K p l ↔ p=a) ∨
    (∃b,∀p l,Pass K p l ↔ l=b) ∨
    (∃a b c d,(a,b)∈K ∧ (c,d)∈K ∧ a≠c ∧ b≠d ∧
      ∀p l,Pass K p l → (p=a ∧ l=d) ∨ (p=c ∧ l=b)) := by
  classical
  obtain ⟨⟨a,b⟩,ab⟩ := ne
  by_cases one : K={(a,b)}
  · exact Or.inl ⟨a,b,one,by simp [Pass,one]⟩
  have another : ∃e∈K,e≠(a,b) := by
    by_contra! no
    apply one
    ext e
    exact ⟨fun he=>Finset.mem_singleton.mpr (no e he),fun he=>(Finset.mem_singleton.mp he) ▸ ab⟩
  by_cases sameP : ∀e∈K,e.1=a
  · obtain ⟨⟨c,d⟩,cd,diff⟩ := another
    have ca : c=a := sameP _ cd
    have db : d≠b := fun h=>diff (Prod.ext ca h)
    right;left;refine ⟨a,?_⟩
    intro p l
    constructor
    · intro ok
      rcases ok (a,b) ab with h|lb
      · exact h
      · rcases ok (c,d) cd with pc|ld
        · exact pc.trans ca
        · exact (db (ld.symm.trans lb)).elim
    · intro pa e he
      exact Or.inl (pa.trans (sameP e he).symm)
  by_cases sameL : ∀e∈K,e.2=b
  · obtain ⟨⟨c,d⟩,cd,diff⟩ := another
    have db : d=b := sameL _ cd
    have ca : c≠a := fun h=>diff (Prod.ext h db)
    right;right;left;refine ⟨b,?_⟩
    intro p l
    constructor
    · intro ok
      rcases ok (a,b) ab with pa|h
      · rcases ok (c,d) cd with pc|ld
        · exact (ca (pc.symm.trans pa)).elim
        · exact ld.trans db
      · exact h
    · intro lb e he
      exact Or.inr (lb.trans (sameL e he).symm)
  have split : ∃ i∈K,∃j∈K,i.1≠j.1 ∧ i.2≠j.2 := by
    push_neg at sameP sameL
    obtain ⟨⟨c,d⟩,cd,ca⟩ := sameP
    obtain ⟨⟨f,g⟩,fg,gb⟩ := sameL
    by_cases db : d=b
    · by_cases fa : f=a
      · exact ⟨(c,d),cd,(f,g),fg,fun h=>ca (h.trans fa),fun h=>gb (h.symm.trans db)⟩
      · exact ⟨(f,g),fg,(a,b),ab,fa,gb⟩
    · exact ⟨(c,d),cd,(a,b),ab,ca,db⟩
  obtain ⟨⟨i,j⟩,ij,⟨k,h⟩,kh,d1,d2⟩ := split
  right;right;right
  refine ⟨i,j,k,h,ij,kh,d1,d2,?_⟩
  intro p l ok
  rcases ok (i,j) ij with pi|lj <;> rcases ok (k,h) kh with pk|lh
  · exact (d1 (pi.symm.trans pk)).elim
  · exact Or.inl ⟨pi,lh⟩
  · exact Or.inr ⟨pk,lj⟩
  · exact (d2 (lj.symm.trans lh)).elim

end SharedFilters3457

namespace SharedFilters3457
open Ports3451
open PEqualNP.CircuitLowerBounds

def direct (n : Nat) (gs : List Gate) :=
  (Finset.univ : Finset (Fin n)).filter (fun p => p.val∈gs.flatMap Gate.inputs)

theorem direct_card (n : Nat) (gs : List Gate) (fan : ∀g∈gs,g.inputs.length≤2) :
    (direct n gs).card≤2*gs.length := by
  have bound (xs : List Gate) (h : ∀g∈xs,g.inputs.length≤2) :
      (xs.flatMap Gate.inputs).length ≤ 2*xs.length := by
    induction xs with
    | nil => simp
    | cons g xs ih =>
      have a := h g List.mem_cons_self
      have b := ih (fun t ht=>h t (List.mem_cons_of_mem _ ht))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  have sub : (direct n gs).image Fin.val ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hp).2
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  exact card.trans ((List.toFinset_card_le _).trans (bound gs fan))

end SharedFilters3457
namespace Repair3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mask3457
variable {N : Nat}

noncomputable def saturated (I : Fin N→Fin N→Prop) (p : Fin N→Bool) : Fin (N+N)→Bool := by
  classical
  exact Fin.addCases p (fun l => decide (∀i,p i=true→¬I i l))

theorem sat_pt (I : Fin N→Fin N→Prop) (p : Fin N→Bool) (i : Fin N) :
    saturated I p (pt i)=p i := by simp [saturated,pt]

theorem sat_ln (I : Fin N→Fin N→Prop) (p : Fin N→Bool) (l : Fin N) :
    saturated I p (ln l)=true ↔ ∀i,p i=true→¬I i l := by
  classical
  simp [saturated,ln]

theorem sat_neg (I : Fin N→Fin N→Prop) (p : Fin N→Bool) : ¬Positive I (saturated I p) := by
  rintro ⟨i,l,il,ip,ll⟩
  exact (sat_ln I p l).mp ll i ((sat_pt I p i) ▸ ip) il

theorem sat_grows (I : Fin N→Fin N→Prop) (x : Fin (N+N)→Bool) (neg : ¬Positive I x) :
    ∀ k,x k = true → saturated I (fun i => x (pt i)) k=true := by
  refine Fin.addCases ?_ ?_
  · intro i hi
    simpa only [sat_pt] using hi
  · intro l hi
    apply (sat_ln _ _ _).mpr
    intro i pi il
    exact neg ⟨i,l,il,pi,hi⟩

theorem sat_ports (I : Fin N→Fin N→Prop) (C B : Circuit) (bm : Monotone2 B) (port : Nat→Nat×Nat) :
    SafePorts I C B port ↔
    ∀j<C.size,gateAt C j≠gateAt B j → ∀p : Fin N→Bool,
      ¬(val B (List.ofFn (saturated I p)) (port j).1=true ∧
        val B (List.ofFn (saturated I p)) (port j).2=true) := by
  constructor
  · rintro safe j hj diff p ⟨a,b⟩
    exact sat_neg I p (safe j hj diff _ a b)
  · intro tests j hj diff x a b
    by_contra neg
    let p (i : Fin N) := x (pt i)
    have low := inputLE (sat_grows I x neg)
    have high := evalLE (sameCut B.gates) (fun g hg=>by simpa using (bm g hg).1)
      _ _ (by simp) low
    exact tests j hj diff p ⟨high _ a,high _ b⟩

end Repair3457
