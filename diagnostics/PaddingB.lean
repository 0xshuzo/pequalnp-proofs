import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18755
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

def step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

lemma appended (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false = if i = a.length then v else a.getD i false := by
  by_cases h : i < a.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, Nat.ne_of_lt h]
  · by_cases he : i = a.length
    · subst i
      simp [List.getD_eq_getElem?_getD, List.getElem?_append]
    · have hp : 0 < i - a.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, he, List.getElem?_eq_none_iff.mpr (by omega : a.length ≤ i), List.getElem?_eq_none_iff.mpr (by change 1 ≤ i - a.length; omega : [v].length ≤ i - a.length)]

lemma oldWire (gs : List Gate) (a : List Bool) (i : ℕ) (h : i < a.length) :
    (gs.foldl step a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step,appended,if_neg (Nat.ne_of_lt h)]
end PEqualNP.Outside.L_meta_18755
namespace Pricing18757
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18755
abbrev V := Fin 42
abbrev Inc (p l : V) := p.val<21 ∧ 21≤l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20]:List Nat)
abbrev Yes (x : V→Bool) := ∃ p l : V, Inc p l ∧ x p=true ∧ x l=true
abbrev Good (C : Circuit) := ∀ x : V→Bool, C.eval (List.ofFn x)=true ↔ Yes x
abbrev Bad (C : Circuit) := ∃ j g, C.gates[j]?=some g ∧ g.op=.and ∧
  (C.wires (List.ofFn fun t : V => decide (t=0 ∨ t=1))).getD (42+j) false=true

theorem len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons,List.length_cons,ih,step,List.length_append,List.length_singleton,List.length_nil]
    omega

theorem output_bounds {C : Circuit} (ok : Good C) : 42≤C.output ∧ C.output<42+C.size := by
  constructor
  · by_contra! lo
    let v : V := ⟨C.output,lo⟩
    let x (i : V) := decide (i=v)
    have high : C.eval (List.ofFn x)=true := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false=true
      rw [oldWire _ _ _ (by simpa using lo)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos lo,Option.getD_some,x,v,decide_true]
    obtain ⟨a,b,h,ha,hb⟩ := (ok x).1 high
    have ea : a=v := of_decide_eq_true ha
    have eb : b=v := of_decide_eq_true hb
    obtain ⟨hp,hl,_⟩ := h
    rw [ea] at hp
    rw [eb] at hl
    omega
  · by_contra! bad
    let x : V→Bool := fun _ => true
    have high := (ok x).2 ⟨0,21,by decide,rfl,rfl⟩
    change (C.gates.foldl step (List.ofFn x)).getD C.output false=true at high
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by
      rw [len,List.length_ofFn]
      exact bad)] at high
    contradiction

def addFlag (C : Circuit) : Circuit := ⟨C.gates ++ [⟨.and,[]⟩],C.output⟩

theorem hit_pad (C : Circuit) (h : Monotone2 C) (ok : Good C) :
    Monotone2 (addFlag C) ∧ (addFlag C).size = C.size+1 ∧
    Good (addFlag C) ∧ Bad (addFlag C) := by
  obtain ⟨_,below⟩ := output_bounds ok
  refine ⟨?_,by simp [addFlag,Circuit.size],?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old|newG
    · exact h g old
    · have e : g = ⟨.and,[]⟩ := by simpa using newG
      subst g
      exact ⟨by simp,by decide⟩
  · intro x
    change ((C.gates++[_]).foldl step (List.ofFn x)).getD C.output false=true ↔ Yes x
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [show step (C.gates.foldl step (List.ofFn x)) ⟨.and,[]⟩ =
      (C.gates.foldl step (List.ofFn x)) ++ [true] by rfl, appended]
    rw [if_neg (by rw [len,List.length_ofFn]; exact Nat.ne_of_lt below)]
    exact ok x
  · refine ⟨C.gates.length,⟨.and,[]⟩,?_,rfl,?_⟩
    · simp [addFlag]
    · let x (i : V) := decide (i=0 ∨ i=1)
      change ((C.gates++[_]).foldl step (List.ofFn x)).getD (42+C.gates.length) false=true
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change ((C.gates.foldl step (List.ofFn x)) ++ [true]).getD _ false=true
      rw [appended, if_pos (by rw [len,List.length_ofFn])]

theorem lower (posted : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) : ∀ C : Circuit, Monotone2 C → Good C → 124 ≤ C.size := by
  intro C mono ok
  by_contra! hs
  obtain ⟨am,asize,aok,hit⟩ := hit_pad C mono ok
  exact posted (addFlag C) (output_bounds aok).1 am (by omega) aok hit
end Pricing18757
