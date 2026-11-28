import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50442
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

abbrev Word := BitVec 6

private def raw : List Word := [62,60,56,48,32,0,63]

private def menu (s : List Word) : List Word :=
  s ++ s.map (fun a => ~~~a) ++ s.flatMap (fun a => s.flatMap (fun b => [a &&& b,a ||| b]))

private def addValue (v : Word) (s : List Word) := if v ∈ s then s else v::s

private def moves (s : List Word) :=
  s :: (((menu s).eraseDups.filter (fun v => v ∉ s)).map (fun v => v::s))

private theorem mem_add {s : List Word} {v a : Word} (h : a ∈ s) : a ∈ addValue v s := by
  by_cases e : v ∈ s <;> simp [addValue,e,h]

private theorem self_add (v : Word) (s : List Word) : v ∈ addValue v s := by
  by_cases e : v ∈ s <;> simp [addValue,e]

private theorem add_move {v : Word} {s : List Word} (h : v ∈ menu s) :
    addValue v s ∈ moves s := by
  by_cases e : v ∈ s
  · simp [addValue,e,moves]
  · simp only [addValue,if_neg e,moves,List.mem_cons,List.mem_map]
    right
    exact ⟨v,by simpa [e] using h,rfl⟩

private theorem read_mem (w s : List Word) (zero : (0 : Word) ∈ s) (sub : ∀ a ∈ w, a ∈ s)
    (i : Nat) : w.getD i 0 ∈ s := by
  induction w generalizing i with
  | nil => simpa using zero
  | cons a w ih =>
    cases i with
    | zero => exact sub a List.mem_cons_self
    | succ i => exact ih (fun b hb => sub b (List.mem_cons_of_mem _ hb)) i

private theorem and_full : ∀ a : Word, a &&& BitVec.allOnes 6 = a := by decide

private theorem gate_menu (w s : List Word) (z : (0 : Word) ∈ s) (u : (63 : Word) ∈ s)
    (sub : ∀ a ∈ w, a ∈ s) (g : Gate)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (arity : g.inputs.length ≤ 2) :
    hcsGateVal w g ∈ menu s := by
  have old {v : Word} (h : v ∈ s) : v ∈ menu s := by simp [menu,h]
  have neg {v : Word} (h : v ∈ s) : ~~~v ∈ menu s := by
    simp only [menu,List.mem_append,List.mem_map]
    exact Or.inl (Or.inr ⟨v,h,rfl⟩)
  have bin {a b : Word} (ha : a ∈ s) (hb : b ∈ s) :
      a &&& b ∈ menu s ∧ a ||| b ∈ menu s := by
    constructor <;> simp only [menu,List.mem_append,List.mem_flatMap] <;> right <;>
      refine ⟨a,ha,b,hb,?_⟩ <;> simp
  obtain ⟨op,args⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change args.length ≤ 2 at arity
  cases args with
  | nil =>
    rcases hop with rfl|rfl|rfl
    · exact old u
    · exact old z
    · change (~~~(0 : Word)) ∈ menu s
      rw [show (~~~(0 : Word)) = 63 from by decide]
      exact old u
  | cons i rest =>
    have hi := read_mem w s z sub i
    cases rest with
    | nil =>
      rcases hop with rfl|rfl|rfl
      · change w.getD i 0 &&& BitVec.allOnes 6 ∈ menu s
        rw [and_full]
        exact old hi
      · simpa [hcsGateVal] using old hi
      · exact neg hi
    | cons j tail =>
      have hj := read_mem w s z sub j
      have e : tail = [] := by simpa using arity
      subst tail
      rcases hop with rfl|rfl|rfl
      · change w.getD i 0 &&& (w.getD j 0 &&& BitVec.allOnes 6) ∈ menu s
        rw [and_full]
        exact (bin hi hj).1
      · simpa [hcsGateVal] using (bin hi hj).2
      · exact neg hi

private def need (s : List Word) : Nat :=
  (if (5 : Word) ∈ s then 0 else 1) + (if (33 : Word) ∈ s then 0 else 1) +
  (if (54 : Word) ∈ s then 0 else 1)

private theorem need_add (v : Word) (s : List Word) : need s ≤ need (addValue v s) + 1 := by
  by_cases h : v ∈ s
  · simp [addValue,h]
  · simp only [addValue,if_neg h,need,List.mem_cons]
    by_cases a : (5 : Word) = v <;> by_cases b : (33 : Word) = v <;> by_cases c : (54 : Word) = v <;>
      by_cases d : (5 : Word) ∈ s <;> by_cases e : (33 : Word) ∈ s <;> by_cases f : (54 : Word) ∈ s <;>
        simp_all <;> first
          | exact (by decide : (5 : Word) ≠ 33) (a.trans b.symm)
          | exact (by decide : (5 : Word) ≠ 54) (a.trans c.symm)
          | exact (by decide : (33 : Word) ≠ 54) (b.trans c.symm)

private def done (s : List Word) : Prop := 5 ∈ s ∧ 33 ∈ s ∧ 54 ∈ s
private instance (s : List Word) : Decidable (done s) := by unfold done; infer_instance

private def scan : Nat → List Word → Bool
  | 0,s => decide (done s)
  | n+1,s => decide (need s ≤ n+1) &&
    (if need s = n+1 then ([5,33,54] : List Word).any
      (fun v => decide (v ∈ menu s) && scan n (addValue v s))
     else (moves s).any (scan n))

private theorem same_need {v : Word} {s : List Word}
    (a : v ≠ 5) (b : v ≠ 33) (c : v ≠ 54) : need (addValue v s) = need s := by
  by_cases h : v ∈ s
  · rw [addValue,if_pos h]
  · simp only [addValue,if_neg h,need,List.mem_cons,Ne.symm a,Ne.symm b,Ne.symm c,false_or]

private theorem simulate (gs : List Gate) (w s : List Word)
    (z : (0 : Word) ∈ s) (u : (63 : Word) ∈ s) (sub : ∀ a ∈ w, a ∈ s)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (out : done (gs.foldl hcsStep w)) : need s ≤ gs.length ∧ scan gs.length s = true := by
  induction gs generalizing s w with
  | nil =>
    obtain ⟨a,b,c⟩ := out
    have aa := sub _ a
    have bb := sub _ b
    have cc := sub _ c
    constructor
    · change need s ≤ 0
      unfold need
      rw [if_pos aa,if_pos bb,if_pos cc] <;> decide
    · exact decide_eq_true (show done s from ⟨aa,bb,cc⟩)
  | cons g gs ih =>
    let v := hcsGateVal w g
    let s' := addValue v s
    have ms : s' ∈ moves s := add_move (gate_menu w s z u sub g (legal g List.mem_cons_self).1 (legal g List.mem_cons_self).2)
    have sub' : ∀ a ∈ hcsStep w g, a ∈ s' := by
      intro a ha
      simp only [hcsStep,List.mem_append,List.mem_singleton] at ha
      rcases ha with h|h
      · exact mem_add (sub _ h)
      · subst a; exact self_add _ _
    obtain ⟨hn,hr⟩ := ih (hcsStep w g) s' (mem_add z) (mem_add u) sub'
      (fun g' hg => legal g' (List.mem_cons_of_mem _ hg)) out
    have h := need_add v s
    change need s ≤ need s' + 1 at h
    have bound : need s ≤ gs.length + 1 := by omega
    refine ⟨bound, Bool.and_eq_true_iff.mpr ⟨decide_eq_true bound,?_⟩⟩
    by_cases tight : need s = gs.length+1
    · rw [if_pos tight]
      have choices : v = 5 ∨ v = 33 ∨ v = 54 := by
        by_contra! wrong
        have eq : need s' = need s := same_need wrong.1 wrong.2.1 wrong.2.2
        omega
      have hv : v ∈ ([5,33,54] : List Word) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using choices
      exact List.any_eq_true.mpr ⟨v,hv,Bool.and_eq_true_iff.mpr
        ⟨decide_eq_true (gate_menu w s z u sub g (legal g List.mem_cons_self).1 (legal g List.mem_cons_self).2),hr⟩⟩
    · rw [if_neg tight]
      exact List.any_eq_true.mpr ⟨s',ms,hr⟩

private theorem raw_bits : ∀ t : Fin 6, raw.map (fun w => w.getLsbD t.val) =
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true] := by decide

private theorem loose {n : Nat} {s : List Word} (h : need s ≤ n+1) (ne : need s ≠ n+1) :
    scan (n+1) s = (moves s).any (scan n) := by
  rw [scan,if_neg ne,decide_eq_true h,Bool.true_and]


private def allBlocked (n : Nat) : List (List Word) → Prop
  | [] => True
  | h::t => scan n h = false ∧ allBlocked n t

private theorem blocked_at (n : Nat) (pool : List (List Word)) (h : allBlocked n pool)
    {s : List Word} (hs : s ∈ pool) : scan n s = false := by
  induction pool with
  | nil => simp at hs
  | cons a pool ih =>
    obtain ⟨head,tail⟩ := h
    rcases List.mem_cons.mp hs with eq|mem
    · exact eq.symm ▸ head
    · exact ih tail mem

private theorem rejected_step {n : Nat} {s : List Word} (pool : List (List Word))
    (h : need s ≤ n+1) (ne : need s ≠ n+1)
    (covers : (moves s).all (fun t => decide (t ∈ pool)) = true)
    (hs : allBlocked n pool) : scan (n+1) s = false := by
  refine (loose h ne).trans ?_
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨t,ht,got⟩ := List.any_eq_true.mp yes
  have mem : t ∈ pool := of_decide_eq_true (List.all_eq_true.mp covers t ht)
  exact Bool.noConfusion ((blocked_at n pool hs mem).symm.trans got)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice0 : scan 0 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice1 : scan 1 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice2 : scan 2 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice3 : scan 3 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice4 : scan 4 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice5 : scan 3 (1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice6 : scan 3 (3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice7 : scan 3 (7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice8 : scan 3 (15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice9 : scan 3 (31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice10 : scan 3 (33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice11 : scan 3 (49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice12 : scan 3 (57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice13 : scan 3 (61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice14 : scan 4 (1::raw) = false := 
  rejected_step (n := 3) (s := (1::raw)) [(1::raw),(3::1::raw),(7::1::raw),(15::1::raw),(31::1::raw),(33::1::raw),(49::1::raw),(57::1::raw),(61::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice5,slice6,slice7,slice8,slice9,slice10,slice11,slice12,slice13,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice15 : scan 4 (3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice16 : scan 4 (7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice17 : scan 4 (15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice18 : scan 4 (31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice19 : scan 5 raw = false := 
  rejected_step (n := 4) (s := raw) [raw,(1::raw),(3::raw),(7::raw),(15::raw),(31::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice4,slice14,slice15,slice16,slice17,slice18,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice20 : scan 3 (2::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice21 : scan 3 (7::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice22 : scan 3 (15::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice23 : scan 3 (31::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice24 : scan 3 (33::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice25 : scan 3 (35::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice26 : scan 3 (49::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice27 : scan 3 (51::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice28 : scan 3 (57::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice29 : scan 3 (59::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice30 : scan 3 (61::3::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice31 : scan 4 (3::1::raw) = false := 
  rejected_step (n := 3) (s := (3::1::raw)) [(3::1::raw),(2::3::1::raw),(7::3::1::raw),(15::3::1::raw),(31::3::1::raw),(33::3::1::raw),(35::3::1::raw),(49::3::1::raw),(51::3::1::raw),(57::3::1::raw),(59::3::1::raw),(61::3::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice6,slice20,slice21,slice22,slice23,slice24,slice25,slice26,slice27,slice28,slice29,slice30,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice32 : scan 3 (3::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice33 : scan 3 (4::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice34 : scan 3 (6::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice35 : scan 3 (15::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice36 : scan 3 (31::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice37 : scan 3 (33::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice38 : scan 3 (39::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice39 : scan 3 (49::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice40 : scan 3 (55::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice41 : scan 3 (57::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice42 : scan 3 (61::7::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice43 : scan 4 (7::1::raw) = false := 
  rejected_step (n := 3) (s := (7::1::raw)) [(7::1::raw),(3::7::1::raw),(4::7::1::raw),(6::7::1::raw),(15::7::1::raw),(31::7::1::raw),(33::7::1::raw),(39::7::1::raw),(49::7::1::raw),(55::7::1::raw),(57::7::1::raw),(61::7::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice7,slice32,slice33,slice34,slice35,slice36,slice37,slice38,slice39,slice40,slice41,slice42,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice44 : scan 3 (3::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice45 : scan 3 (7::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice46 : scan 3 (8::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice47 : scan 3 (12::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice48 : scan 3 (14::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice49 : scan 3 (31::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice50 : scan 3 (33::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice51 : scan 3 (47::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice52 : scan 3 (49::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice53 : scan 3 (57::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice54 : scan 3 (61::15::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice55 : scan 4 (15::1::raw) = false := 
  rejected_step (n := 3) (s := (15::1::raw)) [(15::1::raw),(3::15::1::raw),(7::15::1::raw),(8::15::1::raw),(12::15::1::raw),(14::15::1::raw),(31::15::1::raw),(33::15::1::raw),(47::15::1::raw),(49::15::1::raw),(57::15::1::raw),(61::15::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice8,slice44,slice45,slice46,slice47,slice48,slice49,slice50,slice51,slice52,slice53,slice54,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice56 : scan 3 (3::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice57 : scan 3 (7::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice58 : scan 3 (15::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice59 : scan 3 (16::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice60 : scan 3 (24::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice61 : scan 3 (28::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice62 : scan 3 (30::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice63 : scan 3 (33::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice64 : scan 3 (49::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice65 : scan 3 (57::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice66 : scan 3 (61::31::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice67 : scan 4 (31::1::raw) = false := 
  rejected_step (n := 3) (s := (31::1::raw)) [(31::1::raw),(3::31::1::raw),(7::31::1::raw),(15::31::1::raw),(16::31::1::raw),(24::31::1::raw),(28::31::1::raw),(30::31::1::raw),(33::31::1::raw),(49::31::1::raw),(57::31::1::raw),(61::31::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice9,slice56,slice57,slice58,slice59,slice60,slice61,slice62,slice63,slice64,slice65,slice66,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice68 : scan 3 (3::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice69 : scan 3 (7::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice70 : scan 3 (15::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice71 : scan 3 (30::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice72 : scan 3 (31::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice73 : scan 3 (49::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice74 : scan 3 (57::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice75 : scan 3 (61::33::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice76 : scan 4 (33::1::raw) = false := 
  rejected_step (n := 3) (s := (33::1::raw)) [(33::1::raw),(3::33::1::raw),(7::33::1::raw),(15::33::1::raw),(30::33::1::raw),(31::33::1::raw),(49::33::1::raw),(57::33::1::raw),(61::33::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice10,slice68,slice69,slice70,slice71,slice72,slice73,slice74,slice75,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice77 : scan 3 (3::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice78 : scan 3 (7::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice79 : scan 3 (14::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice80 : scan 3 (15::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice81 : scan 3 (31::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice82 : scan 3 (33::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice83 : scan 3 (57::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice84 : scan 3 (61::49::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice85 : scan 4 (49::1::raw) = false := 
  rejected_step (n := 3) (s := (49::1::raw)) [(49::1::raw),(3::49::1::raw),(7::49::1::raw),(14::49::1::raw),(15::49::1::raw),(31::49::1::raw),(33::49::1::raw),(57::49::1::raw),(61::49::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice11,slice77,slice78,slice79,slice80,slice81,slice82,slice83,slice84,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice86 : scan 3 (3::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice87 : scan 3 (6::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice88 : scan 3 (7::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice89 : scan 3 (15::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice90 : scan 3 (31::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice91 : scan 3 (33::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice92 : scan 3 (49::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice93 : scan 3 (61::57::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice94 : scan 4 (57::1::raw) = false := 
  rejected_step (n := 3) (s := (57::1::raw)) [(57::1::raw),(3::57::1::raw),(6::57::1::raw),(7::57::1::raw),(15::57::1::raw),(31::57::1::raw),(33::57::1::raw),(49::57::1::raw),(61::57::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice12,slice86,slice87,slice88,slice89,slice90,slice91,slice92,slice93,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice95 : scan 3 (2::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice96 : scan 3 (3::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice97 : scan 3 (7::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice98 : scan 3 (15::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice99 : scan 3 (31::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice100 : scan 3 (33::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice101 : scan 3 (49::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice102 : scan 3 (57::61::1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice103 : scan 4 (61::1::raw) = false := 
  rejected_step (n := 3) (s := (61::1::raw)) [(61::1::raw),(2::61::1::raw),(3::61::1::raw),(7::61::1::raw),(15::61::1::raw),(31::61::1::raw),(33::61::1::raw),(49::61::1::raw),(57::61::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice13,slice95,slice96,slice97,slice98,slice99,slice100,slice101,slice102,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice104 : scan 5 (1::raw) = false := 
  rejected_step (n := 4) (s := (1::raw)) [(1::raw),(3::1::raw),(7::1::raw),(15::1::raw),(31::1::raw),(33::1::raw),(49::1::raw),(57::1::raw),(61::1::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice14,slice31,slice43,slice55,slice67,slice76,slice85,slice94,slice103,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice105 : scan 3 (1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice106 : scan 3 (2::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice107 : scan 3 (7::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice108 : scan 3 (15::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice109 : scan 3 (31::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice110 : scan 3 (33::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice111 : scan 3 (35::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice112 : scan 3 (49::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice113 : scan 3 (51::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice114 : scan 3 (57::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice115 : scan 3 (59::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice116 : scan 3 (61::1::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice117 : scan 4 (1::3::raw) = false := 
  rejected_step (n := 3) (s := (1::3::raw)) [(1::3::raw),(2::1::3::raw),(7::1::3::raw),(15::1::3::raw),(31::1::3::raw),(33::1::3::raw),(35::1::3::raw),(49::1::3::raw),(51::1::3::raw),(57::1::3::raw),(59::1::3::raw),(61::1::3::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice105,slice106,slice107,slice108,slice109,slice110,slice111,slice112,slice113,slice114,slice115,slice116,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice118 : scan 4 (2::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice119 : scan 4 (7::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice120 : scan 4 (15::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice121 : scan 4 (31::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice122 : scan 4 (35::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice123 : scan 4 (51::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice124 : scan 4 (59::3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice125 : scan 5 (3::raw) = false := 
  rejected_step (n := 4) (s := (3::raw)) [(3::raw),(1::3::raw),(2::3::raw),(7::3::raw),(15::3::raw),(31::3::raw),(35::3::raw),(51::3::raw),(59::3::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice15,slice117,slice118,slice119,slice120,slice121,slice122,slice123,slice124,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice126 : scan 3 (1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice127 : scan 3 (3::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice128 : scan 3 (4::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice129 : scan 3 (6::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice130 : scan 3 (15::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice131 : scan 3 (31::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice132 : scan 3 (33::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice133 : scan 3 (39::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice134 : scan 3 (49::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice135 : scan 3 (55::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice136 : scan 3 (57::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice137 : scan 3 (61::1::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice138 : scan 4 (1::7::raw) = false := 
  rejected_step (n := 3) (s := (1::7::raw)) [(1::7::raw),(3::1::7::raw),(4::1::7::raw),(6::1::7::raw),(15::1::7::raw),(31::1::7::raw),(33::1::7::raw),(39::1::7::raw),(49::1::7::raw),(55::1::7::raw),(57::1::7::raw),(61::1::7::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice126,slice127,slice128,slice129,slice130,slice131,slice132,slice133,slice134,slice135,slice136,slice137,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice139 : scan 4 (3::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice140 : scan 4 (4::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice141 : scan 3 (6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice142 : scan 3 (1::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice143 : scan 3 (3::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice144 : scan 3 (4::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice145 : scan 3 (15::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice146 : scan 3 (31::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice147 : scan 3 (38::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice148 : scan 3 (39::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice149 : scan 3 (54::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice150 : scan 3 (55::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice151 : scan 3 (57::6::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice152 : scan 4 (6::7::raw) = false := 
  rejected_step (n := 3) (s := (6::7::raw)) [(6::7::raw),(1::6::7::raw),(3::6::7::raw),(4::6::7::raw),(15::6::7::raw),(31::6::7::raw),(38::6::7::raw),(39::6::7::raw),(54::6::7::raw),(55::6::7::raw),(57::6::7::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice141,slice142,slice143,slice144,slice145,slice146,slice147,slice148,slice149,slice150,slice151,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice153 : scan 4 (15::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice154 : scan 4 (31::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice155 : scan 4 (39::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice156 : scan 3 (55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice157 : scan 3 (1::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice158 : scan 3 (3::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice159 : scan 3 (4::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice160 : scan 3 (6::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice161 : scan 3 (8::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice162 : scan 3 (15::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice163 : scan 3 (31::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice164 : scan 3 (39::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice165 : scan 3 (52::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice166 : scan 3 (54::55::7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice167 : scan 4 (55::7::raw) = false := 
  rejected_step (n := 3) (s := (55::7::raw)) [(55::7::raw),(1::55::7::raw),(3::55::7::raw),(4::55::7::raw),(6::55::7::raw),(8::55::7::raw),(15::55::7::raw),(31::55::7::raw),(39::55::7::raw),(52::55::7::raw),(54::55::7::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice156,slice157,slice158,slice159,slice160,slice161,slice162,slice163,slice164,slice165,slice166,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice168 : scan 5 (7::raw) = false := 
  rejected_step (n := 4) (s := (7::raw)) [(7::raw),(1::7::raw),(3::7::raw),(4::7::raw),(6::7::raw),(15::7::raw),(31::7::raw),(39::7::raw),(55::7::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice16,slice138,slice139,slice140,slice152,slice153,slice154,slice155,slice167,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice169 : scan 3 (1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice170 : scan 3 (3::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice171 : scan 3 (7::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice172 : scan 3 (8::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice173 : scan 3 (12::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice174 : scan 3 (14::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice175 : scan 3 (31::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice176 : scan 3 (33::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice177 : scan 3 (47::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice178 : scan 3 (49::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice179 : scan 3 (57::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice180 : scan 3 (61::1::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice181 : scan 4 (1::15::raw) = false := 
  rejected_step (n := 3) (s := (1::15::raw)) [(1::15::raw),(3::1::15::raw),(7::1::15::raw),(8::1::15::raw),(12::1::15::raw),(14::1::15::raw),(31::1::15::raw),(33::1::15::raw),(47::1::15::raw),(49::1::15::raw),(57::1::15::raw),(61::1::15::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice169,slice170,slice171,slice172,slice173,slice174,slice175,slice176,slice177,slice178,slice179,slice180,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice182 : scan 4 (3::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice183 : scan 4 (7::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice184 : scan 4 (8::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice185 : scan 4 (12::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice186 : scan 4 (14::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice187 : scan 4 (31::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice188 : scan 4 (47::15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice189 : scan 5 (15::raw) = false := 
  rejected_step (n := 4) (s := (15::raw)) [(15::raw),(1::15::raw),(3::15::raw),(7::15::raw),(8::15::raw),(12::15::raw),(14::15::raw),(31::15::raw),(47::15::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice17,slice181,slice182,slice183,slice184,slice185,slice186,slice187,slice188,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice190 : scan 3 (1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice191 : scan 3 (3::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice192 : scan 3 (7::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice193 : scan 3 (15::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice194 : scan 3 (16::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice195 : scan 3 (24::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice196 : scan 3 (28::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice197 : scan 3 (30::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice198 : scan 3 (33::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice199 : scan 3 (49::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice200 : scan 3 (57::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice201 : scan 3 (61::1::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice202 : scan 4 (1::31::raw) = false := 
  rejected_step (n := 3) (s := (1::31::raw)) [(1::31::raw),(3::1::31::raw),(7::1::31::raw),(15::1::31::raw),(16::1::31::raw),(24::1::31::raw),(28::1::31::raw),(30::1::31::raw),(33::1::31::raw),(49::1::31::raw),(57::1::31::raw),(61::1::31::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice190,slice191,slice192,slice193,slice194,slice195,slice196,slice197,slice198,slice199,slice200,slice201,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice203 : scan 4 (3::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice204 : scan 4 (7::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice205 : scan 4 (15::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice206 : scan 4 (16::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice207 : scan 4 (24::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice208 : scan 4 (28::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice209 : scan 3 (30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice210 : scan 3 (1::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice211 : scan 3 (3::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice212 : scan 3 (7::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice213 : scan 3 (15::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice214 : scan 3 (16::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice215 : scan 3 (24::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice216 : scan 3 (28::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice217 : scan 3 (33::30::31::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice218 : scan 4 (30::31::raw) = false := 
  rejected_step (n := 3) (s := (30::31::raw)) [(30::31::raw),(1::30::31::raw),(3::30::31::raw),(7::30::31::raw),(15::30::31::raw),(16::30::31::raw),(24::30::31::raw),(28::30::31::raw),(33::30::31::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice209,slice210,slice211,slice212,slice213,slice214,slice215,slice216,slice217,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice219 : scan 5 (31::raw) = false := 
  rejected_step (n := 4) (s := (31::raw)) [(31::raw),(1::31::raw),(3::31::raw),(7::31::raw),(15::31::raw),(16::31::raw),(24::31::raw),(28::31::raw),(30::31::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice18,slice202,slice203,slice204,slice205,slice206,slice207,slice208,slice218,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem slice220 : scan 6 raw = false := 
  rejected_step (n := 5) (s := raw) [raw,(1::raw),(3::raw),(7::raw),(15::raw),(31::raw)] (by decide) (by decide) (by decide +kernel)
    ⟨slice19,slice104,slice125,slice168,slice189,slice219,True.intro⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked : ∀ k : Fin 7, scan k.val raw = false := by
  intro k
  fin_cases k
  · exact slice0
  · exact slice1
  · exact slice2
  · exact slice3
  · exact slice4
  · exact slice19
  · exact slice220

private theorem atWire (D : Circuit) (fan : FanInTwo D) (p : Nat) (m : Word)
    (h : ∀ t : Fin 6, ((D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD p false)
      = m.getLsbD t.val) : (D.gates.foldl hcsStep raw).getD p 0 = m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let t : Fin 6 := ⟨i,hi⟩
  have bits := hcsFoldBits raw t D.gates fan
  rw [raw_bits t] at bits
  have out := h t
  rw [hcsGetDBit]
  change ((D.gates.foldl hcsStep raw).map (fun v => v.getLsbD t.val)).getD p false = _
  rw [bits]
  exact out

private theorem bits5 : ∀ t : Fin 6, (5 : Nat).testBit t.val = (5 : Word).getLsbD t.val := by decide

private theorem bits33 : ∀ t : Fin 6, (33 : Nat).testBit t.val = (33 : Word).getLsbD t.val := by decide

private theorem bits54 : ∀ t : Fin 6, (54 : Nat).testBit t.val = (54 : Word).getLsbD t.val := by decide

end PEqualNP.Outside.L_meta_50442

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_50442 in
theorem PEqualNP.Outside.L_meta_50442 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (33 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D,p,q,r,fan,_,_,size,spec⟩
  let final := D.gates.foldl hcsStep raw
  have m (i : Nat) (v : Word) (ne : v ≠ 0) (h : final.getD i 0 = v) : v ∈ final := by
    have : final.getD i 0 ∈ (0::final) :=
      read_mem final (0::final) List.mem_cons_self (fun _ hx => List.mem_cons_of_mem _ hx) i
    rw [h] at this
    exact (List.mem_cons.mp this).resolve_left ne
  have h5 : (5 : Word) ∈ final := m p.val 5 (by decide) (atWire D fan p.val 5 (fun t => ((spec t).1).trans (bits5 t)))
  have h33 : (33 : Word) ∈ final := m q.val 33 (by decide) (atWire D fan q.val 33 (fun t => ((spec t).2.1).trans (bits33 t)))
  have h54 : (54 : Word) ∈ final := m r.val 54 (by decide) (atWire D fan r.val 54 (fun t => ((spec t).2.2).trans (bits54 t)))
  obtain ⟨_,h⟩ := simulate D.gates raw raw (by decide) (by decide) (fun _ h => h) fan ⟨h5,h33,h54⟩
  have bad := checked ⟨D.gates.length,by change D.gates.length ≤ 6 at size; omega⟩
  exact Bool.noConfusion (h.symm.trans bad)
