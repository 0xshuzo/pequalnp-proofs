import Mathlib
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
