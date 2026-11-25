import PEqualNP.Outside.L_meta_2235
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

namespace Top3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_2235
open Mask3457

def mark (P : Nat → Bool) (k : Nat) : List Gate → List Gate
  | [] => []
  | g::gs => (if g.op=.and ∧ P k=false then zeroGate else g)::mark P (k+1) gs

theorem marked (P : Nat→Bool) (k : Nat) (gs : List Gate) : Cut gs (mark P k gs) := by
  induction gs generalizing k with
  | nil => exact .nil
  | cons g gs ih =>
    by_cases q : g.op=.and ∧ P k=false
    · simpa only [mark,if_pos q] using Cut.drop g q.1 (ih (k+1))
    · simpa only [mark,if_neg q] using Cut.keep g (ih (k+1))

theorem markAt (P : Nat→Bool) (k : Nat) (gs : List Gate) (j : Nat) (h : j<gs.length) :
    (mark P k gs).getD j ⟨.or,[]⟩ = if gs[j].op=.and ∧ P (k+j)=false then zeroGate else gs[j] := by
  induction gs generalizing k j with
  | nil => simp at h
  | cons g gs ih =>
    cases j with
    | zero => simp [mark,List.getD_eq_getElem?_getD]
    | succ j =>
      have q := ih (k+1) j (by simpa using h)
      simpa [mark,List.getD_eq_getElem?_getD,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using q

noncomputable def exposed (n : Nat) (C : Circuit) : Circuit :=
  ⟨mark (fun j=>decide (OrReaches n C C.output j)) 0 C.gates,C.output⟩

theorem exposure (n : Nat) (C : Circuit) (j : Nat) (h : j<C.gates.length) :
    gateAt (exposed n C) j = if (gateAt C j).op=.and ∧ ¬OrReaches n C C.output j then zeroGate else gateAt C j := by
  simpa only [exposed,gateAt,Nat.zero_add,decide_eq_false_iff_not,List.getD_eq_getElem _ _ h] using
    markAt (fun j=>decide (OrReaches n C C.output j)) 0 C.gates j h

theorem sameClosures (n : Nat) {gs ds : List Gate} (h : Cut gs ds) (cs : List (List Nat)) :
    ds.foldl (orStep n) cs=gs.foldl (orStep n) cs := by
  induction h generalizing cs with
  | nil => rfl
  | keep g t ih => exact ih _
  | drop g op t ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have e : orStep n cs zeroGate=orStep n cs g := by simp [orStep,zeroGate,op]
    rw [e]

theorem reaches (n : Nat) (C : Circuit) (w j : Nat) :
    OrReaches n (exposed n C) w j ↔ OrReaches n C w j := by
  unfold OrReaches orSets
  have cut : Cut C.gates (exposed n C).gates := marked _ _ _
  rw [sameClosures n cut]

theorem feeds (n : Nat) (C : Circuit) (w : Nat) (a : Fin n) (h : a∈orIn n C w) : a∈orIn n (exposed n C) w := by
  rw [s2234_qmem_orIn] at h ⊢
  rcases h with h|⟨j,hj,rr,op,mem⟩
  · exact Or.inl h
  · have len := lengthEq (marked (fun j=>decide (OrReaches n C C.output j)) 0 C.gates)
    have keep : gateAt (exposed n C) j=gateAt C j := by simp [exposure n C j hj,op]
    exact Or.inr ⟨j,by change j<(mark _ 0 C.gates).length;omega,(reaches n C w j).mpr rr,keep.symm ▸ op,keep.symm ▸ mem⟩

theorem topSafe (n : Nat) (C : Circuit) (j : Nat) (hd : j<(exposed n C).gates.length)
    (op : (gateAt (exposed n C) j).op=.and) (x : Fin n→Bool) :
    s2231_W n (exposed n C) x (n+j)=true → circuitFun n (exposed n C) x=true := by
  have len : (exposed n C).gates.length=C.gates.length := lengthEq (marked _ _ _)
  have hj : j<C.gates.length := hd.trans_le len.le
  have top : OrReaches n C C.output j := by
    by_contra no
    rw [exposure n C j hj] at op
    split at op
    · simp [zeroGate] at op
    · rename_i notBoth
      exact notBoth ⟨op,no⟩
  exact s2231_reach_up n (exposed n C) x C.output j ((reaches n C C.output j).mpr top)

theorem lowRead (n : Nat) (C : Circuit) (ao : IsAO2 n C) (hm : Monotone2 C) (a b : Fin n)
    (ab : a<b) (off : ∀v : Fin n,circuitFun n C (fun i=>decide (i=v))=false)
    (read : PEqualNP.ReadK.readsAtMost C n [a.val,b.val] 1=true) :
    circuitFun n (exposed n C) (fun i=>decide (i=a ∨ i=b))=true := by
  obtain ⟨j,hj,op,top,ways⟩ := s2230 n C a b ao off ab read
  let D := exposed n C
  have cut : Cut C.gates D.gates := marked _ _ _
  have len := lengthEq cut
  have keep : gateAt D j=gateAt C j := by simp [D,exposure n C j hj,top]
  have md : Monotone2 D := monoCut cut hm
  have spare (g : Gate) (h : g∈D.gates) : g.op=.and ∨ g.op=.or := by simpa using (md g h).1
  let x (i : Fin n) := decide (i=a ∨ i=b)
  have load (w : Nat) (v : Fin n) (vab : v=a ∨ v=b) (hv : v∈orIn n C w) : s2231_W n D x w=true := by
    have before := s2234_qval_orIn n D w v (feeds n C w v hv)
    have le : LE (List.ofFn fun i : Fin n=>decide (i=v)) (List.ofFn x) := by
      apply inputLE;intro i hi
      obtain rfl := of_decide_eq_true hi
      exact decide_eq_true vab
    exact evalLE (sameCut D.gates) spare _ _ (by simp) le w before
  have ar := ao.2.2 (gateAt C j) (by rw [atEq C j hj];exact List.getElem_mem hj)
  obtain ⟨u,v,ins⟩ : ∃u v,(gateAt C j).inputs=[u,v] := by
    generalize e : (gateAt C j).inputs=is at ar ⊢
    cases is with
    | nil => simp at ar
    | cons u us => cases us with
      | nil => simp at ar
      | cons v vs => have : vs=[] := List.length_eq_zero_iff.mp (by simpa using ar);exact ⟨u,v,by rw [this]⟩
  have first : side (n:=n) C j 0=orIn n C u := by simp [side,opnd,ins,List.getD_eq_getElem?_getD]
  have last : side (n:=n) C j 1=orIn n C v := by simp [side,opnd,ins,List.getD_eq_getElem?_getD]
  rw [first,last] at ways
  have vals : s2231_W n D x u=true ∧ s2231_W n D x v=true := by
    rcases ways with ⟨ha,hb⟩|⟨hb,ha⟩
    · exact ⟨load _ _ (Or.inl rfl) ha,load _ _ (Or.inr rfl) hb⟩
    · exact ⟨load _ _ (Or.inr rfl) hb,load _ _ (Or.inl rfl) ha⟩
  have dh : j<D.gates.length := by omega
  apply topSafe n C j dh (keep.symm ▸ op)
  apply s2231_W_and n D x j dh (keep.symm ▸ op)
  intro i mem
  rw [keep] at mem
  exact ⟨ao.2.1 j hj i mem,by rw [ins] at mem; simp only [List.mem_cons,List.not_mem_nil,or_false] at mem;rcases mem with rfl|rfl;exact vals.1;exact vals.2⟩

end Top3457

namespace Top3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_2235 Mask3457
variable {N : Nat}

theorem separate (p l : Fin N) : pt p<ln l := by
  change p.val<N+l.val
  have h := p.isLt
  omega

theorem offUnit (I : Fin N→Fin N→Prop) (C : Circuit) (co : spec I C) (v : Fin (N+N)) :
    circuitFun (N+N) C (fun i=>decide (i=v))=false := by
  cases e : circuitFun (N+N) C (fun i=>decide (i=v)) with
  | false => rfl
  | true =>
    obtain ⟨p,l,_,a,b⟩ := (co _).mp e
    exact False.elim ((ne_of_lt (separate p l)) ((of_decide_eq_true a).trans (of_decide_eq_true b).symm))

theorem offPair (I : Fin N→Fin N→Prop) (C : Circuit) (co : spec I C) (p l : Fin N) (no : ¬I p l) :
    circuitFun (N+N) C (pairInput p l)=false := by
  cases e : circuitFun (N+N) C (pairInput p l) with
  | false => rfl
  | true =>
    obtain ⟨a,b,ab,x,y⟩ := (co _).mp e
    have xp := (of_decide_eq_true x : pt a=pt p ∨ pt a=ln l).resolve_right (ne_of_lt (separate a l))
    have yl := (of_decide_eq_true y : ln b=pt p ∨ ln b=ln l).resolve_left (ne_of_gt (separate p b))
    have pa : a=p := Fin.ext (congrArg (fun z : Fin (N+N)=>z.val) xp)
    have v := congrArg Fin.val yl
    change N+b.val=N+l.val at v
    have bl : b=l := Fin.ext (Nat.add_left_cancel v)
    exact False.elim (no (pa ▸ bl ▸ ab))

theorem topPairs (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C) (co : spec I C) :
    pairTests I (exposed (N+N) C) := by
  let D := exposed (N+N) C
  have cut : Cut C.gates D.gates := marked _ _ _
  have ops (g : Gate) (h : g∈C.gates) : g.op=.and ∨ g.op=.or := by simpa using (hm g h).1
  intro j hj op p l no
  cases e : (D.wires (List.ofFn (pairInput p l))).getD (N+N+j) false with
  | false => rfl
  | true =>
    have live := topSafe (N+N) C j hj op (pairInput p l) e
    have orig : circuitFun (N+N) C (pairInput p l)=true := evalLE cut ops _ _ rfl (fun _ h=>h) C.output live
    exact False.elim (Bool.false_ne_true ((offPair I C co p l no).symm.trans orig))

theorem retained (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C) (ao : IsAO2 (N+N) C)
    (co : spec I C) (p l : Fin N) (r : PEqualNP.ReadK.readsAtMost C (N+N) [(pt p).val,(ln l).val] 1=true) :
    circuitFun (N+N) (core I C) (pairInput p l)=true := by
  have low := lowRead (N+N) C ao hm (pt p) (ln l) (separate p l) (offUnit I C co) r
  exact optimal I C (exposed (N+N) C) hm ao.2.1 (marked _ _ _) rfl (topPairs I C hm co) (pairInput p l) low

theorem sufficient (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C) (ao : IsAO2 (N+N) C)
    (co : spec I C) (singles : unitTests (N:=N) C)
    (hard : ∀ p l,I p l → PEqualNP.ReadK.readsAtMost C (N+N) [(pt p).val,(ln l).val] 1=false →
       circuitFun (N+N) (core I C) (pairInput p l)=true) :
    ∃D : Circuit,Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧ spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  obtain ⟨md,bd,sz,pairs,units,full⟩ := coreResult I C hm ao.2.1 co singles
  refine ⟨core I C,md,bd,sz.le,full.mpr ?_,pairs,units⟩
  intro p l inc
  cases e : PEqualNP.ReadK.readsAtMost C (N+N) [(pt p).val,(ln l).val] 1 with
  | false => exact hard p l inc e
  | true => exact retained I C hm ao co p l e

end Top3457
