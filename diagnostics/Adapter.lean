import Mathlib
import PEqualNP.Defs

namespace Adapter5186
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getLastWire (xs : List Bool) (v : Bool) :
    (xs ++ [v]).getD xs.length false = v := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getLastWire, getLastWire]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem main : ∀ (π : Fin 16 → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.output < 16 + C.size →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size + 1 ∧ D.output < 26 + D.size ∧
  ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 D x =
    PEqualNP.MetaComplexity.circuitFun 16 C (fun i => if h : π i < 26 then x ⟨π i,h⟩ else x 6 || x 12) := by
  intro π C hC hout
  let g : Gate := ⟨.or,[6,12]⟩
  let f (i : Fin 16) : Fin 27 := if h : π i < 26 then ⟨π i,by omega⟩ else 26
  let R := relabel 16 27 f C
  let D : Circuit := ⟨g :: R.gates,R.output⟩
  have hs : D.size = C.size + 1 := by simp [D,R,relabel,Circuit.size]
  refine ⟨D,?_,hs,?_,?_⟩
  · intro a ha
    change a ∈ g :: C.gates.map (relGate 16 27 f) at ha
    rcases List.mem_cons.mp ha with hh | hh
    · subst a
      simp [g]
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
      have hh := hC b hb
      simpa only [relGate,List.length_map] using hh
  · rw [hs]
    change wmap 16 27 f C.output < _
    unfold wmap
    split
    · rename_i h
      have := (f ⟨C.output,h⟩).isLt
      omega
    · omega
  · intro x
    let x' (j : Fin 27) : Bool := if h : j.val < 26 then x ⟨j.val,h⟩ else x 6 || x 12
    have v6 : (List.ofFn x).getD 6 false = x 6 := by
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      rfl
    have v12 : (List.ofFn x).getD 12 false = x 12 := by
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      rfl
    have gateValue : g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false)) = (x 6 || x 12) := by
      change GateOp.or.eval [(List.ofFn x).getD 6 false,(List.ofFn x).getD 12 false] = _
      rw [v6,v12]
      simp [GateOp.eval]
    have init : step (List.ofFn x) g = List.ofFn x' := by
      change List.ofFn x ++ [g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))] = List.ofFn x'
      rw [gateValue]
      rfl
    have eqf : x' ∘ f = fun i => if h : π i < 26 then x ⟨π i,h⟩ else x 6 || x 12 := by
      funext i
      by_cases h : π i < 26 <;> simp [Function.comp_def,x',f,h]
    have eval := (rel_fold 16 27 f C.gates _ _ (rel_init 16 27 f x')).2.2 C.output
    rw [← eqf]
    change ((C.gates.map (relGate 16 27 f)).foldl step (step (List.ofFn x) g)).getD (wmap 16 27 f C.output) false = _
    rw [init]
    exact eval

end Adapter5186
