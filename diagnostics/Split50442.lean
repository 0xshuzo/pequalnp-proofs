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
      have hv : v ∈ ([5,33,54] : List Word) := by simpa only [List.mem_cons,List.mem_singleton] using choices
      exact List.any_eq_true.mpr ⟨v,hv,Bool.and_eq_true_iff.mpr
        ⟨decide_eq_true (gate_menu w s z u sub g (legal g List.mem_cons_self).1 (legal g List.mem_cons_self).2),hr⟩⟩
    · rw [if_neg tight]
      exact List.any_eq_true.mpr ⟨s',ms,hr⟩

private theorem raw_bits : ∀ t : Fin 6, raw.map (fun w => w.getLsbD t.val) =
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero0 : scan 0 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero1 : scan 1 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero2 : scan 2 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero3 : scan 3 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero4 : scan 4 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem zero5 : scan 5 raw = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem child1 : scan 5 (1::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem child3 : scan 5 (3::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem child7 : scan 5 (7::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem child15 : scan 5 (15::raw) = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem child31 : scan 5 (31::raw) = false := by decide +kernel

private theorem first_cover : (moves raw).all
    (fun s => decide (s = raw ∨ s = 1::raw ∨ s = 3::raw ∨ s = 7::raw ∨ s = 15::raw ∨ s = 31::raw)) = true := by decide
private theorem last_root : scan 6 raw = false := by
  change (moves raw).any (scan 5) = false
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨s,hs,yes⟩ := List.any_eq_true.mp h
  have choices := of_decide_eq_true (List.all_eq_true.mp first_cover s hs)
  rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
  · rw [zero5] at yes; contradiction
  · rw [child1] at yes; contradiction
  · rw [child3] at yes; contradiction
  · rw [child7] at yes; contradiction
  · rw [child15] at yes; contradiction
  · rw [child31] at yes; contradiction

private theorem checked : ∀ k : Fin 7, scan k.val raw = false := by
  intro k
  fin_cases k <;> first | exact zero0 | exact zero1 | exact zero2 | exact zero3 | exact zero4 | exact zero5 | exact last_root

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
