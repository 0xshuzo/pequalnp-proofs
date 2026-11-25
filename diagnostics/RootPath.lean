import Mathlib
import PEqualNP.Outside.L_meta_3017

namespace RootPath2846

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core PEqualNP.Outside.L_meta_3017

abbrev Sig := BitVec 16
abbrev Row := Fin 16
def table (f : Row → Bool) : Sig := (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
def bit (i : Row) (v : Sig) := v.getLsbD i.val
theorem observe (f : Row → Bool) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]; simp [r.isLt]
def input (r : Row) (i : Fin 4) := Nat.testBit r.val i.val
def path (z : Fin 4 → Bool) := (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)
def target := table (fun r => path (input r))
def roots := List.ofFn (fun i : Fin 4 => table (fun r => input r i))
def op (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
def choices (v : List Sig) := (v.flatMap fun a => v.flatMap fun b => [op false a b, op true a b]).eraseDups
def checks (v : List Sig) := v.all fun a => v.all fun b => (a &&& b) != target
def search : Nat → List Sig → Bool
  | 0,v => checks v
  | k+1,v => checks v && (choices v).all (fun w => if (w &&& target) = w then true else search k (w :: v))

theorem sound (s : Nat → Sig) (j : Nat)
    (steps : ∀ u < j, ∃ a < 4+u, ∃ b < 4+u, ∃ d : Bool, s (4+u) = op d (s a) (s b))
    (dirty : ∀ u < j, (s (4+u) &&& target) ≠ s (4+u))
    (root : ∃ a < 4+j, ∃ b < 4+j, (s a &&& s b) = target)
    (k i : Nat) (pool : List Sig) (ok : search k pool = true)
    (hi : i ≤ j) (hj : j ≤ i+k) (sub : ∀ u < 4+i, s u ∈ pool) : False := by
  induction k generalizing i pool with
  | zero =>
    have eq : j = i := by omega
    obtain ⟨a,ha,b,hb,h⟩ := root
    have t := List.all_eq_true.mp (List.all_eq_true.mp ok (s a) (sub a (by omega))) (s b) (sub b (by omega))
    simp [h] at t
  | succ k ind =>
    simp only [search,Bool.and_eq_true] at ok
    obtain ⟨h0,next⟩ := ok
    by_cases done' : i = j
    · obtain ⟨a,ha,b,hb,h⟩ := root
      have t := List.all_eq_true.mp (List.all_eq_true.mp h0 (s a) (sub a (by omega))) (s b) (sub b (by omega))
      simp [h] at t
    · obtain ⟨a,ha,b,hb,d,hd⟩ := steps i (by omega)
      have hm : s (4+i) ∈ choices pool := by
        rw [hd]
        unfold choices
        rw [List.mem_eraseDups]
        apply List.mem_flatMap.mpr
        refine ⟨s a,sub a ha, List.mem_flatMap.mpr ⟨s b,sub b hb,?_⟩⟩
        cases d <;> simp
      have move := List.all_eq_true.mp next _ hm
      rw [if_neg (dirty i (by omega))] at move
      apply ind (i+1) (s (4+i) :: pool) move (by omega) (by omega)
      intro u hu
      by_cases cut : u < 4+i
      · exact List.mem_cons_of_mem _ (sub u cut)
      · have eq : u = 4+i := by omega
        rw [eq]
        exact List.mem_cons_self

def sig (C : Circuit) (w : Nat) := table (fun r => wireVal 4 C w (input r))

theorem combine (C : Circuit) (ha : IsAO2 4 C) (j : Nat) (hj : j < C.gates.length)
    (a b : Nat) (h : (gateAt C j).inputs = [a,b]) :
    ((gateAt C j).op = GateOp.and → sig C (4+j) = op false (sig C a) (sig C b)) ∧
    ((gateAt C j).op = GateOp.or → sig C (4+j) = op true (sig C a) (sig C b)) := by
  have e (r : Row) := gateVal_eval 4 C j hj ha.2.1 (input r)
  constructor <;> intro ht <;> apply BitVec.eq_of_getLsbD_eq <;> intro z hz
  · let r : Row := ⟨z,hz⟩
    have eb (u : Nat) : (sig C u).getLsbD z = wireVal 4 C u (input r) := observe _ r
    change (sig C (4+j)).getLsbD z = ((sig C a) &&& (sig C b)).getLsbD z
    rw [BitVec.getLsbD_and,eb,eb,eb]
    simpa only [gateVal_eq_wireVal,ht,h,List.map_cons,List.map_nil,eval_and_two] using e r
  · let r : Row := ⟨z,hz⟩
    have eb (u : Nat) : (sig C u).getLsbD z = wireVal 4 C u (input r) := observe _ r
    change (sig C (4+j)).getLsbD z = ((sig C a) ||| (sig C b)).getLsbD z
    rw [BitVec.getLsbD_or,eb,eb,eb]
    simpa only [gateVal_eq_wireVal,ht,h,List.map_cons,List.map_nil,eval_or_two] using e r

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem data : search 3 roots = true := by decide +kernel

theorem root_lower (C : Circuit) (ha : IsAO2 4 C)
    (he : ∀ z, circuitFun 4 C z = path z) (j : Nat) (hj : j < C.gates.length)
    (ho : C.output = 4+j) (hand : (gateAt C j).op = GateOp.and)
    (dirty : ∀ t < j, ∃ r : Row, wireVal 4 C (4+t) (input r) = true ∧ path (input r) = false) :
    5 ≤ C.size := by
  by_contra! sz
  change C.gates.length < 5 at sz
  have indices (u : Nat) (hu : u < C.gates.length) :
      ∃ a < 4+u, ∃ b < 4+u, (gateAt C u).inputs = [a,b] := by
    obtain ⟨a,b,h⟩ := List.length_eq_two.mp (ha.2.2 _ (gateAt_mem C u hu))
    refine ⟨a,ha.2.1 u hu a (by simp [h]),b,ha.2.1 u hu b (by simp [h]),h⟩
  have steps (u : Nat) (hu : u < j) := indices u (lt_trans hu hj)
  obtain ⟨a,haa,b,hbb,hb⟩ := indices j hj
  have end' : sig C (4+j) = target := by
    unfold sig target
    congr 1
    funext r
    rw [← ho]
    exact he (input r)
  refine sound (sig C) j ?_ ?_ ?_ 3 0 roots data (Nat.zero_le _) (by omega) ?_
  · intro u hu
    obtain ⟨a,h1,b,h2,eq⟩ := steps u hu
    obtain h | h := ha.1 _ (gateAt_mem C u (lt_trans hu hj))
    · exact ⟨a,h1,b,h2,false,(combine C ha u (lt_trans hu hj) a b eq).1 h⟩
    · exact ⟨a,h1,b,h2,true,(combine C ha u (lt_trans hu hj) a b eq).2 h⟩
  · intro t ht eq
    obtain ⟨r,one,off⟩ := dirty t ht
    have e := congrArg (fun b : Sig => b.getLsbD r.val) eq
    have x : (sig C (4+t)).getLsbD r.val = true := (observe _ r).trans one
    have y : target.getLsbD r.val = false := (observe _ r).trans off
    change ((sig C (4+t)) &&& target).getLsbD r.val = (sig C (4+t)).getLsbD r.val at e
    rw [BitVec.getLsbD_and,x,y] at e
    contradiction
  · exact ⟨a,haa,b,hbb,((combine C ha j hj a b hb).1 hand).symm.trans end'⟩
  · intro u hu
    let i : Fin 4 := ⟨u,by omega⟩
    have e : sig C u = table (fun r => input r i) := by
      unfold sig
      congr 1
      funext r
      exact wireVal_input 4 C i (input r)
    simpa only [roots,e,List.mem_ofFn] using (show ∃ k : Fin 4, table (fun r => input r k) = table (fun r => input r i) from ⟨i,rfl⟩)

theorem fourGate (a b c d : Bool) :
    ((b || d) && (c || (a && b))) = ((a && b) || (b && c) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

end RootPath2846
