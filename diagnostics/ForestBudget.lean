import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_5733

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

def tidyList : Nat → List Gate → List Gate
  | _, [] => []
  | m, g::gs => tidy m g :: tidyList (m+1) gs

lemma shape (m : Nat) (g : Gate) (ok : g.op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length ≤ 2) :
    ((tidy m g).op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ (tidy m g).inputs.length ≤ 2) ∧
    (∀ i ∈ (tidy m g).inputs,i < m) ∧ ((tidy m g).op=.and → g.op=.and) := by
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
    · simp [tidy,ha,hb]
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
    apply Bool.eq_iff_iff.mpr
    simp only [tidy,if_neg hn,value,ho,GateOp.eval,List.any_map,List.any_eq_true,
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
       (tidyList m gs)[j].op=.and → gs[j].op=.and) ∧
    (∀w : List Bool,w.length=m→run (tidyList m gs) w=run gs w) := by
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

def graph (I : Fin N→Fin N→Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l,I p l ∧ ((u=pt p ∧ v=ln l) ∨ (v=pt p ∧ u=ln l))
  symm := ⟨by
    intro u v
    rintro ⟨p,l,inc,h|h⟩
    · exact ⟨p,l,inc,Or.inr h⟩
    · exact ⟨p,l,inc,Or.inl h⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨p,l,inc,h|h⟩ <;> exact (ne_of_lt (separate p l)) (h.1.symm.trans h.2)⟩

lemma graph_spec (I : Fin N→Fin N→Prop) (x : Fin (N+N)→Bool) :
    (∃u v,(graph I).Adj u v ∧ x u=true ∧ x v=true) ↔ Positive I x := by
  constructor
  · rintro ⟨u,v,⟨p,l,inc,h|h⟩,a,b⟩
    · exact ⟨p,l,inc,h.1 ▸ a,h.2 ▸ b⟩
    · exact ⟨p,l,inc,h.1 ▸ b,h.2 ▸ a⟩
  · rintro ⟨p,l,inc,a,b⟩
    exact ⟨pt p,ln l,⟨p,l,inc,Or.inl ⟨rfl,rfl⟩⟩,a,b⟩

def SimpleCase {n : Nat} (G : SimpleGraph (Fin n)) :=
  G.IsAcyclic ∨ 5≤n ∧ ∃ a : Fin n ≃ Fin n, ∀u v,G.Adj u v ↔
    ((a u).val+1)%n=(a v).val ∨ ((a v).val+1)%n=(a u).val

/-- A graph-specific numerical budget, or just the forest/cycle hypothesis, suffices. -/
theorem forestOrBudget (I : Fin N→Fin N→Prop) (C : Circuit)
    (hm : Monotone2 C) (co : spec I C)
    (small : SimpleCase (graph I) ∨ ∃ T : Finset (Fin (N+N)),
      (∀u v,(graph I).Adj u v → u∈T ∨ v∈T) ∧
        (graph I).edgeSet.ncard + T.card - 1 ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧
      spec I D ∧ pairTests I D ∧ unitTests (N:=N) D := by
  classical
  let G := graph I
  have cand : ∃ A : Circuit, Monotone2 A ∧
        (∀x : Fin (N+N)→Bool,A.eval (List.ofFn x) = decide (∃u v,G.Adj u v ∧ x u=true ∧ x v=true)) ∧
        A.size≤C.size ∧
        ∀ j (g : Gate), A.gates[j]?=some g → g.op=.and → ∀x : Fin (N+N)→Bool,
          (A.wires (List.ofFn x)).getD (N+N+j) false=true → ∃u v,G.Adj u v ∧ x u=true ∧ x v=true := by
    rcases small with easy|⟨T,cov,cost⟩
    · obtain ⟨A,ma,ev,least,aclean⟩ := PEqualNP.Outside.L_meta_5733 _ G easy
      refine ⟨A,ma,ev,least C hm ?_,aclean⟩
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact (co x).trans (graph_spec I x).symm
    · obtain ⟨A,ma,ev,sz,aclean⟩ := PEqualNP.Outside.L_meta_5733.CleanStars.main _ G T cov
      have e : G.edgeSet.ncard=G.edgeFinset.card := by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
      change G.edgeSet.ncard+T.card-1 ≤ C.size at cost
      rw [e] at cost
      exact ⟨A,ma,ev,sz.trans cost,aclean⟩
  obtain ⟨A,ma,ev,sz,aclean⟩ := cand
  let D : Circuit := ⟨tidyList (N+N) A.gates,A.output⟩
  obtain ⟨len,md,bd,orig,eq⟩ := tidies A.gates ma (N+N)
  have back : ReadsBack (N+N) D := fun j hj i hi=>bd j hj i (by rwa [← atEq D j hj])
  have wires (x : Fin (N+N)→Bool) : D.wires (List.ofFn x)=A.wires (List.ofFn x) := eq _ (by simp)
  have exactD : spec I D := by
    intro x
    change (D.wires _).getD A.output false=true ↔ _
    rw [wires]
    change A.eval _=true ↔ _
    rw [ev,decide_eq_true_eq]
    exact graph_spec I x
  have anyOff (x : Fin (N+N)→Bool) (neg : ¬Positive I x) (j : Nat)
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
