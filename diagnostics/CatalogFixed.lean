import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8123.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm
set_option maxRecDepth 10000
set_option maxHeartbeats 0

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

def adjacent (p l : Fin 42) : Prop := p.val<21 ∧ 21≤l.val ∧ (l.val+21-p.val)%21∈([0,5,7,17,20]:List Nat)
instance (p l : Fin 42) : Decidable (adjacent p l) := by unfold adjacent; infer_instance
def hasEdge (x : Fin 42 → Bool) : Prop := ∃p l,adjacent p l ∧ x p=true ∧ x l=true
def right (K : Circuit) := ∀ x : Fin 42 → Bool,K.eval (List.ofFn x)=true ↔ hasEdge x
def valid (K : Circuit) := IsAO2 42 K ∧ right K
def isOr (g : Gate) : Bool := GateOp.casesOn g.op false true false (fun _=>false) false
def cost (K : Circuit) := K.gates.countP isOr
def line (i : Nat) := decide (21 ≤ i)
def edges : List (Nat × Nat) := (List.range 21).flatMap (fun p => ([0,5,7,17,20]:List Nat).map (fun k=>(p,21+(p+k)%21)))
def bad (K : Circuit) := doubleReread K 42 line edges
def best (K : Circuit) := ∀ D,valid D → cost K≤cost D
def Descent := ∀ K,valid K → best K → bad K≠[] → ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length

end PEqualNP.Outside.L_meta_8123.Work

namespace PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit (step, val, val_snoc, val_ge, val_lt) copied from the L_meta_2986 / L_meta_1406 files

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = val ([] : List Gate) x i := by
  rw [val_lt gs x i hi, val_lt [] x i hi]

/-- re-indexing of the wires: the first `a` inputs stay, everything else moves up by `n`. -/
def phi (a n : ℕ) (w : ℕ) : ℕ := if w < a then w else w + n

def rho (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi a n)⟩

lemma phi_lt (a n : ℕ) (ha : a ≤ n) (i : ℕ) (hi : i < n) : phi a n i < n + n := by
  unfold phi
  split_ifs <;> omega

def zof (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) : Fin n → Bool :=
  fun i => x ⟨phi a n i.val, phi_lt a n ha i.val i.isLt⟩

lemma reidx (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) (z : Fin n → Bool)
    (hz : ∀ (i : ℕ) (hi : i < n) (h2 : phi a n i < n + n), z ⟨i, hi⟩ = x ⟨phi a n i, h2⟩) :
    ∀ (gs : List Gate) (w : ℕ), val (gs.map (rho a n)) x (phi a n w) = val gs z w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil]
    rw [val_nil, val_nil]
    by_cases hw : w < n
    · have hp := phi_lt a n ha w hw
      rw [dif_pos hp, dif_pos hw]
      exact (hz w hw hp).symm
    · have hp : ¬ phi a n w < n + n := by
        unfold phi
        split_ifs <;> omega
      rw [dif_neg hp, dif_neg hw]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_cons, List.map_nil, val_snoc, val_snoc, List.length_map]
    have key : phi a n w = n + n + gs.length ↔ w = n + gs.length := by
      unfold phi
      split_ifs <;> omega
    by_cases hw : w = n + gs.length
    · rw [if_pos (key.2 hw), if_pos hw]
      show g.op.eval (List.map (fun j => val (gs.map (rho a n)) x j) (g.inputs.map (phi a n))) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hw (key.1 h)), if_neg hw]
      exact ih w

/-- well-formed gate lists: AND/OR, two inputs, each input earlier. -/
def WF (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m + j

lemma wf_two (m : ℕ) (gs : List Gate) (a b c : ℕ) (hwf : WF m gs)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    WF m (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h | h
  · rw [List.getElem?_append_left h] at hj
    exact hwf j g hj
  · rw [List.getElem?_append_right h] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = gs.length + k := ⟨j - gs.length, by omega⟩
    rw [Nat.add_sub_cancel_left] at hj
    match k, hj with
    | 0, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inl rfl, rfl, by intro i hi; simp at hi; omega⟩
    | 1, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
    | k + 2, hj => simp at hj

lemma val_two_new {m : ℕ} (gs : List Gate) (a b c : ℕ) (x : Fin m → Bool)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    val (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) x (m + gs.length + 1)
      = (val gs x c || (val gs x a && val gs x b)) := by
  have happ : gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [c, m + gs.length]⟩]
      = (gs ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [c, m + gs.length]⟩] := by simp
  have hl1 : (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
  rw [happ, val_snoc, if_pos (by omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [val_snoc, if_neg (by omega), val_snoc, if_pos rfl]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]

lemma isAO2_of_wf (m : ℕ) (gs : List Gate) (out : ℕ) (hwf : WF m gs) :
    PEqualNP.TopForm.IsAO2 m (⟨gs, out⟩ : Circuit) := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hi' : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact (hwf j _ (List.getElem?_eq_getElem hj')).2.2 i hi'
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).2.1

end PEqualNP.Outside.L_meta_3264_aux
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl


end PEqualNP.Outside.L_meta_3568.Slice
namespace PEqualNP.Outside.L_meta_8123.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.Outside.L_meta_3568.Slice
set_option maxRecDepth 32768
set_option maxHeartbeats 0

def adjoin (K : Circuit) (e : Nat × Nat) : Circuit :=
  ⟨K.gates ++ [⟨.and,[e.1,e.2]⟩,⟨.or,[K.output,42+K.gates.length]⟩],42+K.gates.length+1⟩

theorem cost_adjoin (K : Circuit) (e : Nat × Nat) : cost (adjoin K e)=cost K+1 := by
  simp [cost,adjoin,isOr,List.countP_append]

theorem wfOf {n : Nat} {K : Circuit} (ao : IsAO2 n K) : WF n K.gates := by
  intro j g hg
  have hj : j<K.gates.length := by
    by_contra! far
    rw [List.getElem?_eq_none far] at hg
    contradiction
  have mem := List.mem_of_getElem? hg
  refine ⟨ao.1 _ mem,ao.2.2 _ mem,?_⟩
  intro v hv
  apply ao.2.1 j hj v
  change v∈(K.gates.getD j _).inputs
  simpa [List.getD_eq_getElem?_getD,hg] using hv

theorem bounds : ∀e∈edges,e.1<42 ∧ e.2<42 := by decide +kernel

theorem legal_adjoin {K : Circuit} (ao : IsAO2 42 K) (out : K.output<42+K.gates.length) {e}
    (he : e∈edges) : IsAO2 42 (adjoin K e) := by
  have h := bounds e he
  exact isAO2_of_wf _ _ _ (wf_two 42 K.gates e.1 e.2 K.output (wfOf ao) (by omega) (by omega) out)

theorem eval_adjoin (K : Circuit) (out : K.output<42+K.gates.length) {e} (he:e∈edges)
    (x : Fin 42 → Bool) : (adjoin K e).eval (List.ofFn x) =
      (K.eval (List.ofFn x) || (x ⟨e.1,(bounds e he).1⟩ && x ⟨e.2,(bounds e he).2⟩)) := by
  have h := bounds e he
  have eq := val_two_new K.gates e.1 e.2 K.output x (by omega) (by omega) out
  rw [val_lt _ _ _ h.1,val_lt _ _ _ h.2] at eq
  exact eq

def colour (b : Bool) : Nat→Bool := if b then line else (fun i=> !line i)
def init (b : Bool) (q : Nat × Nat) : List (Bool × Bool) :=
  (((List.range 42).map fun i => i==q.1 || i==q.2).zipIdx).map
    fun (x,i)=>if colour b i then (false,x) else (x,false)
private theorem init_len (b : Bool) (q) : (init b q).length=42 := by simp [init]
private theorem marked : ∀e∈edges,∀b : Bool,
    ((init b e).getD e.1 (false,false),(init b e).getD e.2 (false,false)) =
    (if b then ((true,false),(false,true)) else ((false,true),(true,false))) := by decide +kernel

def single (K : Circuit) (b : Bool) (q : Nat × Nat) := lineSingle K 42 (colour b) q.1 q.2
def dirty (K : Circuit) (q : Nat × Nat) := !(single K true q) && !(single K false q)
theorem bad_filter (K : Circuit) : bad K = edges.filter (dirty K) := rfl

private theorem finalGet {α : Type} (w : List α) (a d : α) (i : Nat) (eq:i=w.length) :
    (w++[a]).getD i d=a := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [show i-w.length=0 by omega]
  rfl

private theorem single_adjoin (K : Circuit) (out : K.output<42+K.gates.length) (e q : Nat × Nat)
    (b : Bool) :
    single (adjoin K e) b q =
      (single K b q || (linStep (scan linStep K.gates (init b q)) ⟨.and,[e.1,e.2]⟩).2) := by
  let w := scan linStep K.gates (init b q)
  let a := linStep w ⟨.and,[e.1,e.2]⟩
  have len : w.length=42+K.gates.length := by simp [w,scan_length,init_len]
  change ((scan linStep (K.gates ++ [⟨.and,[e.1,e.2]⟩,⟨.or,[K.output,42+K.gates.length]⟩]) (init b q)).getD
    (42+K.gates.length+1) (false,false)).2 = _
  rw [scan_append]
  change ((w ++ [a] ++ [linStep (w++[a]) ⟨.or,[K.output,42+K.gates.length]⟩]).getD
    (42+K.gates.length+1) (false,false)).2 = _
  rw [finalGet _ _ _ _ (by simp [len])]
  simp only [linStep,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false]
  rw [List.getD_append _ _ _ _ (show K.output < w.length by omega),finalGet w a _ _ len.symm]
  rfl

theorem protects (K : Circuit) (out : K.output<42+K.gates.length) {e} (he:e∈edges) (b : Bool) :
    single (adjoin K e) b e=true := by
  rw [single_adjoin K out e e b]
  have bounds' := bounds e he
  have seen (v : Nat) (hv : v<42) :
      (scan linStep K.gates (init b e)).getD v (false,false)=(init b e).getD v (false,false) :=
    scan_prefix _ _ _ _ _ (by simpa [init_len] using hv)
  have pair := marked e he b
  have a := congrArg Prod.fst pair
  have c := congrArg Prod.snd pair
  simp only [linStep,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,seen e.1 bounds'.1,seen e.2 bounds'.2]
  cases b <;> simp_all

theorem dirty_down (K : Circuit) (out : K.output<42+K.gates.length) (e q) :
    dirty (adjoin K e) q=true → dirty K q=true := by
  unfold dirty
  rw [single_adjoin K out e q true,single_adjoin K out e q false]
  simp <;> grind

private theorem count_mono {α : Type} (l : List α) (p q : α→Bool)
    (sub : ∀a∈l,q a=true → p a=true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have rest := ih (fun b hb => sub b (List.mem_cons_of_mem _ hb))
    have head := sub a (List.mem_cons_self)
    cases h : p a <;> cases j : q a <;> simp_all [List.filter_cons] <;> omega

private theorem count_lt {α : Type} (l : List α) (p q : α→Bool) (e : α) (he:e∈l)
    (yes:p e=true) (no:q e=false) (sub : ∀a∈l,q a=true → p a=true) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at he
  | cons a t ih =>
    have shrink : ∀b∈t,q b=true → p b=true := fun b hb => sub b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.mp he with rfl|inside
    · have bound := count_mono t p q shrink
      simp [List.filter_cons,yes,no] <;> omega
    · have strict := ih inside shrink
      have head := sub a (List.mem_cons_self)
      cases h : p a <;> cases j : q a <;> simp_all [List.filter_cons] <;> omega

theorem recovered {K A : Circuit} {e : Nat × Nat} (he : e∈edges) (badE : dirty K e=true)
    (ao : IsAO2 42 A) (out : A.output<42+A.gates.length) (price : cost A+1≤cost K)
    (semantic : ∀x : Fin 42→Bool, (A.eval (List.ofFn x) ||
      (x ⟨e.1,(bounds e he).1⟩ && x ⟨e.2,(bounds e he).2⟩))=true ↔ hasEdge x)
    (retain : ∀q∈edges,q≠e → dirty A q=true → dirty K q=true) :
    ∃ D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length := by
  let D:=adjoin A e
  have clean : dirty D e=false := by simp [dirty,D,protects A out he true]
  refine ⟨D,⟨legal_adjoin ao out he,fun x => ?_⟩,by simpa [D,cost_adjoin] using price,?_⟩
  · rw [eval_adjoin A out he]
    exact semantic x
  · rw [bad_filter,bad_filter]
    apply count_lt _ _ _ e he badE clean
    intro q hq badD
    by_cases eq:q=e
    · subst q
      rw [clean] at badD
      contradiction
    exact retain q hq eq (dirty_down A out e q badD)

end PEqualNP.Outside.L_meta_8123.Work
namespace PEqualNP.Outside.L_meta_8123.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Outside.L_meta_3264_aux
set_option maxHeartbeats 0
set_option maxRecDepth 32768

def e0 : Nat × Nat := (0,21)
def seed : Circuit := ⟨[⟨.and,[0,21]⟩],42⟩
def make : List (Nat × Nat) → Circuit
  | [] => seed
  | e::t => adjoin (make t) e

private theorem zeroListed : e0∈edges := by decide +kernel
private theorem headEdges : edges=e0::edges.tail := by decide +kernel
private theorem tailSize : edges.tail.length=104 := by decide +kernel
private theorem actual (p l : Fin 42) : (p.val,l.val)∈edges ↔ adjacent p l := by
  revert p l; decide +kernel

def on (x : Fin 42 → Bool) (e : Nat × Nat) :=
  (List.ofFn x).getD e.1 false=true ∧ (List.ofFn x).getD e.2 false=true

private theorem seed_on (x : Fin 42→Bool) : seed.eval (List.ofFn x)=true ↔ on x e0 := by
  change val [⟨.and,[0,21]⟩] x 42=true ↔ _
  rw [show [⟨.and,[0,21]⟩] = ([]:List Gate)++[⟨.and,[0,21]⟩] from rfl,val_snoc]
  simp [on,e0,GateOp.eval,val_nil,ofFn_getD x 0 (by decide),ofFn_getD x 21 (by decide)]

private theorem built (t : List (Nat × Nat)) (sub:∀e∈t,e∈edges) :
    IsAO2 42 (make t) ∧ (make t).output<42+(make t).gates.length ∧
    cost (make t)=t.length ∧
    (∀ x : Fin 42→Bool,(make t).eval (List.ofFn x)=true ↔ on x e0 ∨ ∃e∈t,on x e) ∧
    ∀e∈e0::t,single (make t) true e=true := by
  induction t with
  | nil =>
    refine ⟨by decide +kernel,by decide +kernel,rfl,?_,?_⟩
    · intro x
      simpa [make] using seed_on x
    · intro e he
      simp at he
      subst e
      decide +kernel
  | cons e t ih =>
    have he:=sub e List.mem_cons_self
    obtain ⟨ao,ot,num,ev,safe⟩:=ih (fun q hq=>sub q (List.mem_cons_of_mem _ hq))
    refine ⟨legal_adjoin ao ot he,?_,?_,?_,?_⟩
    · simp [make,adjoin] <;> omega
    · simp [make,cost_adjoin,num]
    · intro x
      rw [make,eval_adjoin _ ot he,Bool.or_eq_true,ev,Bool.and_eq_true]
      have h : (x ⟨e.1,(bounds e he).1⟩=true ∧ x ⟨e.2,(bounds e he).2⟩=true) ↔ on x e := by
        unfold on
        rw [ofFn_getD x e.1 (bounds e he).1,ofFn_getD x e.2 (bounds e he).2]
      rw [h]
      simp only [List.mem_cons]
      grind
    · intro q hq
      by_cases eq:q=e
      · subst q
        exact protects (make t) ot he true
      · have old : q∈e0::t := by simpa [eq] using hq
        rw [make,single_adjoin _ ot, safe q old]
        simp

def C : Circuit := make edges.tail
theorem baseline : valid C ∧ cost C=104 ∧ bad C=[] := by
  have sub : ∀e∈edges.tail,e∈edges := by
    intro e he
    rw [headEdges]
    exact List.mem_cons_of_mem _ he
  obtain ⟨ao,_,num,ev,safe⟩:=built edges.tail sub
  refine ⟨⟨ao,?_⟩,num.trans tailSize,?_⟩
  · intro x
    change (make edges.tail).eval (List.ofFn x) = true ↔ _
    rw [ev x]
    have normalize : (on x e0 ∨ ∃e∈edges.tail,on x e) ↔ ∃e∈edges,on x e := by
      conv_rhs => rw [headEdges]
      simp
    rw [normalize]
    constructor
    · rintro ⟨e,he,hp,hl⟩
      let p : Fin 42:=⟨e.1,(bounds e he).1⟩
      let l : Fin 42:=⟨e.2,(bounds e he).2⟩
      exact ⟨p,l,(actual p l).1 he,(ofFn_getD x _ p.isLt).symm.trans hp,(ofFn_getD x _ l.isLt).symm.trans hl⟩
    · rintro ⟨p,l,a,hp,hl⟩
      exact ⟨(p.val,l.val),(actual p l).2 a,(ofFn_getD x _ p.isLt).trans hp,(ofFn_getD x _ l.isLt).trans hl⟩
  · rw [bad_filter]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨inside,dirtyE⟩:=List.mem_filter.mp he
    have good:=safe e (headEdges ▸ inside)
    simp [dirty,C,good] at dirtyE

theorem clean_optimum_iff : Descent ↔ ∃K,valid K ∧ best K ∧ bad K=[] := by
  classical
  constructor
  · intro descent
    have existsCost : ∃s,∃K,valid K ∧ cost K=s := ⟨cost C,C,baseline.1,rfl⟩
    obtain ⟨A,va,ca⟩ := Nat.find_spec existsCost
    have least : best A := fun D vd => ca.le.trans (Nat.find_min' existsCost ⟨D,vd,rfl⟩)
    have sizes : ∃s,∃B,valid B ∧ best B ∧ (bad B).length=s := ⟨_,A,va,least,rfl⟩
    obtain ⟨B,vb,mb,bLen⟩ := Nat.find_spec sizes
    refine ⟨B,vb,mb,?_⟩
    by_contra nonempty
    obtain ⟨D,vd,cheap,short⟩ := descent B vb mb nonempty
    have md : best D := fun E ve => cheap.trans (mb E ve)
    have bound := Nat.find_min' sizes ⟨D,vd,md,rfl⟩
    omega
  · rintro ⟨D,vd,md,clean⟩ K vk _ nb
    refine ⟨D,vd,md K vk,?_⟩
    rw [clean]
    exact List.length_pos_iff.mpr nb

theorem any_104 (K : Circuit) (large : 104≤cost K) (nb : bad K≠[]) :
    ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length := by
  refine ⟨C,baseline.1,baseline.2.1.le.trans large,?_⟩
  rw [baseline.2.2]
  exact List.length_pos_iff.mpr nb

theorem low_cost_suffices (hard : ∀ K,valid K → best K → cost K≤103 → bad K≠[] →
      ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length) : Descent := by
  intro K vk mini db
  rcases le_or_gt 104 (cost K) with big|small
  · exact any_104 K big db
  · exact hard K vk mini (by omega) db

end PEqualNP.Outside.L_meta_8123.Work
