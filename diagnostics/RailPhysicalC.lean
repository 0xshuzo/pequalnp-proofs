import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Split
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))


def finish (post : List Gate) (out : Nat) (w : List Bool) (bit : Bool) :=
  (run post (w ++ [bit])).getD out false

theorem finish_order (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (w : List Bool) :
    finish post out w false = true → finish post out w true = true := by
  have same : below w w := ⟨rfl, fun _ h => h⟩
  have ord : below (w ++ [false]) (w ++ [true]) := extend same (by simp)
  exact (run_mono post goodPost ord).2 out

abbrev Inp := Fin 14 → Bool
theorem retained (pre : List Gate) (w : List Bool) : ∃ t, run pre w=w++t := by
  induction pre generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨t,ht⟩ := ih (stage w g)
    exact ⟨[readGate g w]++t,by simpa [run,stage,List.append_assoc] using ht⟩

theorem rawRead (pre : List Gate) (x : Inp) (i : Fin 14) :
    (run pre (List.ofFn x)).getD i.val false=x i := by
  obtain ⟨t,ht⟩ := retained pre (List.ofFn x)
  rw [ht]
  have lt : i.val < (List.ofFn x).length := by simpa using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
  fin_cases i <;> rfl

def physical (pre : List Gate) (tap : Gate) (post : List Gate) (out : Nat) : Circuit :=
  ⟨pre++tap::post,out⟩

def setRow (x : Inp) (i : Fin 14) (p : Bool) : Inp := fun j => if j=i then p else x j

theorem rowSame (x : Inp) (i : Fin 14) : setRow x i (x i)=x := by
  funext j
  by_cases h : j=i <;> simp [setRow,h]

def constGate : Bool → Gate
  | true => ⟨.and,[]⟩
  | false => ⟨.or,[]⟩

theorem constEval (pre post : List Gate) (i : Nat) (x : Inp) (c : Bool) :
    (physical pre (constGate c) post i).eval (List.ofFn x)=
      finish post i (run pre (List.ofFn x)) c := by
  change ((pre++constGate c::post).foldl stage (List.ofFn x)).getD i false=_
  cases c <;> simp [finish,run,List.foldl_append,stage,readGate,constGate,GateOp.eval]

theorem rawEval (pre post : List Gate) (i : Nat) (x : Inp) (v : Fin 14) :
    (physical pre ⟨.not,[v.val]⟩ post i).eval (List.ofFn x)=
      finish post i (run pre (List.ofFn x)) (!(x v)) := by
  have rr := rawRead pre x v
  change (pre.foldl stage (List.ofFn x)).getD v.val false=x v at rr
  change ((pre++(⟨.not,[v.val]⟩ : Gate)::post).foldl stage (List.ofFn x)).getD i false=_
  rw [←rr]
  simp [List.foldl_append,finish,run,stage,readGate,GateOp.eval]

theorem guardedConst (pre post : List Gate) (out : Nat) (c : Bool)
    (a : ∀ g∈pre,good g) (b : ∀ g∈post,good g) :
    Monotone2 (physical pre (constGate c) post out) := by
  intro g hg
  change g∈pre++constGate c::post at hg
  rcases List.mem_append.mp hg with hp|hp
  · exact a g hp
  · rcases List.mem_cons.mp hp with rfl|hp
    · cases c <;> simp [constGate,good]
    · exact b g hp

def split (pre post : List Gate) (out : Nat) (v : Fin 14) (x : Inp) (p n : Bool) : Bool :=
  finish post out (run pre (List.ofFn (setRow x v p))) n

def andRow (u : Bool → Bool → Bool) : Prop :=
  u false false=false ∧ u false true=false ∧ u true false=false ∧ u true true=true
def orRow (u : Bool → Bool → Bool) : Prop :=
  u false false=false ∧ u false true=true ∧ u true false=true ∧ u true true=true

theorem fourLaw (a b c d : Bool) (lo : a=true → b=true) (diag : b=true → c=true)
    (hi : c=true → d=true) :
    ((¬(a=false ∧ b=false ∧ c=false ∧ d=true)) → d=c) ∧
    ((¬(a=false ∧ b=true ∧ c=true ∧ d=true)) → a=b) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem witnesses (pre post : List Gate) (out : Nat) (v : Fin 14)
    (a : ∀ g∈pre,good g) (b : ∀ g∈post,good g) (f : Inp → Bool)
    (up : ∀ x, f (setRow x v false)=true → f (setRow x v true)=true)
    (old : ∀ x, (physical pre ⟨.not,[v.val]⟩ post out).eval (List.ofFn x)=f x)
    (floor : ∀ C : Circuit, Monotone2 C →
      C.size≤(physical pre ⟨.not,[v.val]⟩ post out).size → ¬∀ x : Inp,C.eval (List.ofFn x)=f x) :
    (∃ x,andRow (split pre post out v x)) ∧ (∃ x,orRow (split pre post out v x)) := by
  classical
  let S := split pre post out v
  have actual (x : Inp) (p : Bool) : S x p (!p)=f (setRow x v p) := by
    have ho := old (setRow x v p)
    rw [rawEval] at ho
    simpa [S,split,setRow] using ho
  have law (x : Inp) :=
    fourLaw (S x false false) (S x false true) (S x true false) (S x true true)
      (finish_order post b out _)
      (by intro h; have low := actual x false; have high := actual x true
          simp only [Bool.not_false,Bool.not_true] at low high
          exact high.trans (up x (low.symm.trans h)))
      (finish_order post b out _)
  have cannot (c : Bool) : ¬∀ x : Inp, S x (x v) c=f x := by
    intro agree
    apply floor (physical pre (constGate c) post out) (guardedConst pre post out c a b)
      (by simp [physical,Circuit.size])
    intro x
    have h := agree x
    rw [constEval]
    simpa [S,split,rowSame] using h
  constructor
  · by_contra! no
    apply cannot true
    intro x
    cases e : x v with
    | false =>
      have h := actual x false
      have row : setRow x v false=x := e ▸ rowSame x v
      rw [row] at h
      exact h
    | true =>
      have eq := (law x).1 (no x)
      have h := actual x true
      have row : setRow x v true=x := e ▸ rowSame x v
      rw [row] at h
      exact eq.trans h
  · by_contra! no
    apply cannot false
    intro x
    cases e : x v with
    | false =>
      have eq := (law x).2 (no x)
      have h := actual x false
      have row : setRow x v false=x := e ▸ rowSame x v
      rw [row] at h
      exact eq.trans h
    | true =>
      have h := actual x true
      have row : setRow x v true=x := e ▸ rowSame x v
      rw [row] at h
      exact h

theorem separator {Y : Type} (gs : List Gate) (ok : ∀ g∈gs,good g) (out : Nat)
    (bank : Y → Bool → Bool → List Bool) (y z : Y)
    (ha : andRow (fun p n => (run gs (bank y p n)).getD out false))
    (ho : orRow (fun p n => (run gs (bank z p n)).getD out false)) :
    (¬below (bank y true true) (bank z false false)) ∧
    (∀ t p,(run gs (bank t p (!p))).getD out false=false →
      ¬below (bank y true true) (bank t p (!p))) ∧
    (∀ t p,(run gs (bank t p (!p))).getD out false=true →
      ¬below (bank t p (!p)) (bank z false false)) := by
  have sep (u v : List Bool) (yes : (run gs u).getD out false=true)
      (no : (run gs v).getD out false=false) : ¬below u v := by
    intro ord
    have bad := (run_mono gs ok ord).2 out yes
    exact Bool.noConfusion (no.symm.trans bad)
  exact ⟨sep _ _ ha.2.2.2 ho.1,fun _ _ h => sep _ _ ha.2.2.2 h,fun _ _ h => sep _ _ h ho.1⟩

end PEqualNP.Outside.L_meta_9809.Split


namespace PEqualNP.Outside.L_meta_9809.Rail
open PEqualNP.CircuitLowerBounds

inductive Pat where
  | lo | left | right | meet | join | hi
  deriving DecidableEq

def bits : Pat → Nat
  | .lo => 0 | .left => 12 | .right => 10 | .meet => 8 | .join => 14 | .hi => 15

def decode : Nat → Pat
  | 0 => .lo | 12 => .left | 10 => .right | 8 => .meet | 14 => .join | _ => .hi

def mix (d : Bool) (u v : Pat) : Pat :=
  decode (if d then bits u ||| bits v else bits u &&& bits v)

def aim (d : Bool) : Pat := if d then .join else .meet
def op (d : Bool) : GateOp := if d then .or else .and
def paired (u v : Pat) : Prop :=
  (u = .left ∧ v = .right) ∨ (u = .right ∧ v = .left)

theorem creates (d e : Bool) (u v : Pat) :
    u ≠ aim d → v ≠ aim d → mix e u v = aim d → e = d ∧ paired u v := by
  unfold paired
  cases d <;> cases e <;> cases u <;> cases v <;> decide

theorem traces (d leftRail : Bool) (u v : Pat) :
    let tag : Pat := if leftRail then .left else .right
    mix d u v = tag → u = tag ∨ v = tag := by
  cases d <;> cases leftRail <;> cases u <;> cases v <;> decide

def val : Pat → Bool → Bool → Bool
  | .lo, _, _ => false | .hi, _, _ => true | .left, a, _ => a | .right, _, b => b
  | .meet, a,b => a && b | .join, a,b => a || b

theorem mixVal (d : Bool) (u v : Pat) (a b : Bool) :
    val (mix d u v) a b = (if d then val u a b || val v a b else val u a b && val v a b) := by
  cases d <;> cases u <;> cases v <;> cases a <;> cases b <;> decide

def wire (w : List Pat) (j : Nat) := w.getD j .lo

def gate (w : List Pat) (g : Gate) : Pat :=
  match g.inputs with
  | [] => match g.op with | .and => .hi | _ => .lo
  | [i] => wire w i
  | i::j::_ => mix (match g.op with | .or => true | _ => false) (wire w i) (wire w j)

def push (w : List Pat) (g : Gate) := w ++ [gate w g]
def run (gs : List Gate) (w : List Pat) := gs.foldl push w

def joined (d : Bool) (w : List Pat) (g : Gate) : Prop :=
  g.op = op d ∧ ∃ i j, g.inputs = [i,j] ∧ paired (wire w i) (wire w j)

def occurs (d : Bool) : List Gate → List Pat → Prop
  | [], _ => False
  | g::gs, w => joined d w g ∨ occurs d gs (push w g)

def good (g : Gate) : Prop := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2

theorem fromList {A : Type} (w : List A) (i : Nat) (a : A) :
    w.getD i a=a ∨ w.getD i a∈w := by
  induction w generalizing i with
  | nil => simp [List.getD_eq_getElem?_getD]
  | cons x w ih =>
    cases i with
    | zero => simp [List.getD_eq_getElem?_getD]
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl (by simpa [List.getD_eq_getElem?_getD] using h)
      · exact Or.inr (List.mem_cons_of_mem _ (by simpa [List.getD_eq_getElem?_getD] using h))

theorem clean {d : Bool} {w : List Pat} (abs : aim d ∉ w) (j : Nat) : wire w j ≠ aim d := by
  intro eqn
  rcases fromList w j Pat.lo with h | h
  · have e : Pat.lo = aim d := h.symm.trans eqn
    cases d <;> cases e
  · change wire w j ∈ w at h
    exact abs (eqn ▸ h)

theorem newGate {d : Bool} {w : List Pat} {g : Gate} (well : good g)
    (abs : aim d ∉ w) (eqn : gate w g = aim d) : joined d w g := by
  rcases g with ⟨tag,args⟩
  rcases well with ⟨tagOk,arity⟩
  change tag=.and ∨ tag=.or at tagOk
  change args.length ≤ 2 at arity
  cases args with
  | nil =>
    rcases tagOk with rfl | rfl <;> cases d <;> cases eqn
  | cons i rem =>
    cases rem with
    | nil => exact False.elim (clean abs i eqn)
    | cons j rem =>
      cases rem with
      | cons k rest => simp at arity
      | nil =>
        rcases tagOk with rfl | rfl
        · have h := creates d false (wire w i) (wire w j) (clean abs i) (clean abs j) eqn
          obtain ⟨rfl,pp⟩ := h
          exact ⟨rfl,i,j,rfl,pp⟩
        · have h := creates d true (wire w i) (wire w j) (clean abs i) (clean abs j) eqn
          obtain ⟨rfl,pp⟩ := h
          exact ⟨rfl,i,j,rfl,pp⟩

theorem discover {d : Bool} (w : List Pat) (gs : List Gate)
    (valid : ∀ g∈gs,good g) (abs : aim d ∉ w) (found : aim d ∈ run gs w) : occurs d gs w := by
  induction gs generalizing w with
  | nil => exact False.elim (abs found)
  | cons g gs ih =>
    by_cases fresh : gate w g=aim d
    · exact Or.inl (newGate (valid _ (by simp)) abs fresh)
    · apply Or.inr
      apply ih (push w g) (fun t h => valid t (by simp [h])) _ found
      intro m
      rcases List.mem_append.mp m with h | h
      · exact abs h
      · have z : aim d = gate w g := by simpa using h
        exact fresh z.symm

theorem findsOutput {d : Bool} (w : List Pat) (gs : List Gate) (out : Nat)
    (valid : ∀ g∈gs,good g) (abs : aim d ∉ w) (found : wire (run gs w) out=aim d) :
    occurs d gs w := by
  apply discover w gs valid abs
  by_contra h
  exact clean h out found

end PEqualNP.Outside.L_meta_9809.Rail
namespace PEqualNP.Outside.L_meta_9809.Rail
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev SInp := Fin 14 → Bool

def row (w : List Pat) (a b : Bool) := w.map fun p => val p a b

theorem getVal (w : List Pat) (i : Nat) (a b : Bool) :
    val (wire w i) a b = (row w a b).getD i false := by
  induction w generalizing i with
  | nil => simp [row,wire,List.getD_eq_getElem?_getD,val]
  | cons p w ih =>
    cases i with
    | zero => simp [row,wire,List.getD_eq_getElem?_getD]
    | succ i => simpa [row,wire,List.getD_eq_getElem?_getD] using ih i

theorem decodeGate (w : List Pat) (g : Gate) (a b : Bool) (ok : good g) :
    val (gate w g) a b = Split.readGate g (row w a b) := by
  rcases g with ⟨t,ins⟩
  rcases ok with ⟨t_ok,bound⟩
  change t=.and ∨ t=.or at t_ok
  change ins.length ≤ 2 at bound
  cases ins with
  | nil => rcases t_ok with rfl | rfl <;> rfl
  | cons i rem =>
    cases rem with
    | nil =>
      rcases t_ok with rfl | rfl <;> simp [gate,Split.readGate,GateOp.eval,getVal]
    | cons j rem =>
      cases rem with
      | cons k more => simp at bound
      | nil =>
        rcases t_ok with rfl | rfl <;> simp [gate,Split.readGate,GateOp.eval,mixVal,getVal]

theorem decodeProgram (w : List Pat) (gs : List Gate) (a b : Bool)
    (ok : ∀ g∈gs,good g) : row (run gs w) a b = Split.run gs (row w a b) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change row (run gs (push w g)) a b=Split.run gs (Split.stage (row w a b) g)
    rw [ih _ (fun t ht => ok _ (by simp [ht]))]
    have one : row (push w g) a b=Split.stage (row w a b) g := by
      simp [row,push,Split.stage,decodeGate w g a b (ok _ (by simp))]
    rw [one]

def rawPat (x : SInp) (v : Fin 14) : List Pat :=
  List.ofFn fun i => if i=v then .left else if x i then .hi else .lo

theorem rowInputs (x : SInp) (v : Fin 14) (a b : Bool) :
    row (rawPat x v) a b=List.ofFn (Split.setRow x v a) := by
  have point (i : Fin 14) : val (if i=v then .left else if x i then .hi else .lo) a b=Split.setRow x v a i := by
    by_cases eqn : i=v <;> cases hx : x i <;> simp [eqn,hx,Split.setRow,val]
  apply List.ext_getElem
  · simp [row,rawPat]
  · intro i h k
    simp only [row,List.getElem_map,rawPat,List.getElem_ofFn,Split.setRow]
    exact point _

def start (pre : List Gate) (x : SInp) (v : Fin 14) :=
  run pre (rawPat x v) ++ [Pat.right]

theorem startRow (pre : List Gate) (x : SInp) (v : Fin 14) (a b : Bool)
    (ok : ∀ g∈pre,good g) :
    row (start pre x v) a b = Split.run pre (List.ofFn (Split.setRow x v a)) ++ [b] := by
  change (run pre (rawPat x v) ++ [Pat.right]).map _ = _
  rw [List.map_append]
  change row (run pre (rawPat x v)) a b ++ [b] = _
  rw [decodeProgram _ _ _ _ ok,rowInputs]

theorem splitVal (pre post : List Gate) (out : Nat) (x : SInp) (v : Fin 14) (a b : Bool)
    (preOK : ∀ g∈pre,good g) (postOK : ∀ g∈post,good g) :
    val (wire (run post (start pre x v)) out) a b=Split.split pre post out v x a b := by
  rw [getVal,decodeProgram _ _ _ _ postOK,startRow _ _ _ _ _ preOK]
  rfl

theorem unaryPat (p : Pat) :
    (∀ a : Bool,val p a false=val p a true) → p≠.meet ∧ p≠.join := by
  cases p <;> decide

theorem startsWithout (pre : List Gate) (ok : ∀ g∈pre,good g) (x : SInp)
    (v : Fin 14) (d : Bool) : aim d ∉ start pre x v := by
  intro h
  rcases List.mem_append.mp h with hp | hx
  · obtain ⟨i,hi,eqn⟩ := List.getElem_of_mem hp
    have atIndex : wire (run pre (rawPat x v)) i = aim d := by
      rw [wire,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      exact eqn
    have unary (a : Bool) : val (aim d) a false = val (aim d) a true := by
      rw [←atIndex,getVal,getVal,decodeProgram _ _ _ _ ok,decodeProgram _ _ _ _ ok,rowInputs,rowInputs]
    have bad := unaryPat _ unary
    cases d with
    | false => exact bad.1 rfl
    | true => exact bad.2 rfl
  · cases d <;> simpa [aim] using hx

theorem classifyAnd (p : Pat) : Split.andRow (val p) → p=.meet := by unfold Split.andRow; cases p <;> decide
theorem classifyOr (p : Pat) : Split.orRow (val p) → p=.join := by unfold Split.orRow; cases p <;> decide

theorem physicalMeetings (pre post : List Gate) (out : Nat) (v : Fin 14)
    (a : ∀ g∈pre,Split.good g) (b : ∀ g∈post,Split.good g) (f : SInp → Bool)
    (up : ∀ x, f (Split.setRow x v false)=true → f (Split.setRow x v true)=true)
    (correct : ∀ x, (Split.physical pre ⟨.not,[v.val]⟩ post out).eval (List.ofFn x)=f x)
    (floor : ∀ C : Circuit, Monotone2 C →
      C.size≤(Split.physical pre ⟨.not,[v.val]⟩ post out).size → ¬∀ x : SInp,C.eval (List.ofFn x)=f x) :
    (∃ x,occurs false post (start pre x v)) ∧ (∃ x,occurs true post (start pre x v)) := by
  have convert (g : Gate) (h : Split.good g) : good g := ⟨by simpa using h.1,h.2⟩
  have pgood (g) (h : g∈pre) := convert g (a g h)
  have sgood (g) (h : g∈post) := convert g (b g h)
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := Split.witnesses pre post out v a b f up correct floor
  have qr (z : SInp) : val (wire (run post (start pre z v)) out)=Split.split pre post out v z := by
    funext i j
    exact splitVal _ _ _ _ _ _ _ pgood sgood
  rw [←qr] at hx hy
  exact ⟨⟨x,findsOutput _ _ out sgood (startsWithout _ pgood _ _ _) (classifyAnd _ hx)⟩,
    ⟨y,findsOutput _ _ out sgood (startsWithout _ pgood _ _ _) (classifyOr _ hy)⟩⟩

end PEqualNP.Outside.L_meta_9809.Rail
