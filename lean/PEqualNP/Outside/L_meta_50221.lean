import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50221
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
  (if (4 : Word) ∈ s then 0 else 1) + (if (40 : Word) ∈ s then 0 else 1) +
  (if (46 : Word) ∈ s then 0 else 1)

private theorem need_add (v : Word) (s : List Word) : need s ≤ need (addValue v s) + 1 := by
  by_cases h : v ∈ s
  · simp [addValue,h]
  · simp only [addValue,if_neg h,need,List.mem_cons]
    by_cases a : (4 : Word) = v <;> by_cases b : (40 : Word) = v <;> by_cases c : (46 : Word) = v <;>
      by_cases d : (4 : Word) ∈ s <;> by_cases e : (40 : Word) ∈ s <;> by_cases f : (46 : Word) ∈ s <;>
        simp_all <;> first
          | exact (by decide : (4 : Word) ≠ 40) (a.trans b.symm)
          | exact (by decide : (4 : Word) ≠ 46) (a.trans c.symm)
          | exact (by decide : (40 : Word) ≠ 46) (b.trans c.symm)

private def done (s : List Word) : Prop := 4 ∈ s ∧ 40 ∈ s ∧ 46 ∈ s
private instance (s : List Word) : Decidable (done s) := by unfold done; infer_instance

private def scan : Nat → List Word → Bool
  | 0,s => decide (done s)
  | n+1,s => decide (need s ≤ n+1) && (moves s).any (scan n)

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
    exact ⟨bound, Bool.and_eq_true_iff.mpr ⟨decide_eq_true bound,List.any_eq_true.mpr ⟨s',ms,hr⟩⟩⟩

private theorem raw_bits : ∀ t : Fin 6, raw.map (fun w => w.getLsbD t.val) =
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked : ∀ k : Fin 6, scan k.val raw = false := by decide +kernel

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

private theorem bits4 : ∀ t : Fin 6, (4 : Nat).testBit t.val = (4 : Word).getLsbD t.val := by decide

private theorem bits40 : ∀ t : Fin 6, (40 : Nat).testBit t.val = (40 : Word).getLsbD t.val := by decide

private theorem bits46 : ∀ t : Fin 6, (46 : Nat).testBit t.val = (46 : Word).getLsbD t.val := by decide

end PEqualNP.Outside.L_meta_50221

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_50221 in
theorem PEqualNP.Outside.L_meta_50221 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val) := by
  rintro ⟨D,p,q,r,fan,_,_,size,spec⟩
  let final := D.gates.foldl hcsStep raw
  have m (i : Nat) (v : Word) (ne : v ≠ 0) (h : final.getD i 0 = v) : v ∈ final := by
    have : final.getD i 0 ∈ (0::final) :=
      read_mem final (0::final) List.mem_cons_self (fun _ hx => List.mem_cons_of_mem _ hx) i
    rw [h] at this
    exact (List.mem_cons.mp this).resolve_left ne
  have h4 : (4 : Word) ∈ final := m p.val 4 (by decide) (atWire D fan p.val 4 (fun t => ((spec t).1).trans (bits4 t)))
  have h40 : (40 : Word) ∈ final := m q.val 40 (by decide) (atWire D fan q.val 40 (fun t => ((spec t).2.1).trans (bits40 t)))
  have h46 : (46 : Word) ∈ final := m r.val 46 (by decide) (atWire D fan r.val 46 (fun t => ((spec t).2.2).trans (bits46 t)))
  obtain ⟨_,h⟩ := simulate D.gates raw raw (by decide) (by decide) (fun _ h => h) fan ⟨h4,h40,h46⟩
  have bad := checked ⟨D.gates.length,by change D.gates.length ≤ 5 at size; omega⟩
  exact Bool.noConfusion (h.symm.trans bad)
