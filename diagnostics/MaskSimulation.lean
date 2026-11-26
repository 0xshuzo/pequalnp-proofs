import PEqualNP.Defs

namespace Plane8311.MaskSimulation
open PEqualNP.CircuitLowerBounds

def step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map (fun i => xs.getD i false))]
def run (gs : List Gate) (xs : List Bool) := gs.foldl step xs
def index (n off zero i : ℕ) := if i<n then off+i else zero
def liftGate (n off zero : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (index n off zero)⟩
def lift (off zero : ℕ) : ℕ → List Gate → List Gate
  | _,[] => []
  | n,g::gs => liftGate n off zero g :: lift off zero (n+1) gs

theorem length (off zero n : ℕ) (gs : List Gate) : (lift off zero n gs).length=gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [lift,ih]

def Fits (off zero : ℕ) (xs ys : List Bool) :=
  ys.length=off+xs.length ∧ zero<ys.length ∧ ys.getD zero false=false ∧
    ∀ i<xs.length, ys.getD (off+i) false=xs.getD i false

theorem step_ok {off zero xs ys} (h : Fits off zero xs ys) (g : Gate) :
    Fits off zero (step xs g) (step ys (liftGate xs.length off zero g)) := by
  rcases h with ⟨len,lt,z,matchOld⟩
  have matchArg (i) : ys.getD (index xs.length off zero i) false=xs.getD i false := by
    by_cases hi : i<xs.length
    · simpa [index,hi] using matchOld i hi
    · simp only [index,if_neg hi,z,List.getD_eq_default _ _ (by omega : xs.length≤i)]
  have equiv : (g.inputs.map (index xs.length off zero)).map (fun i => ys.getD i false) =
      g.inputs.map (fun i => xs.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact matchArg i
  unfold step liftGate
  simp only [equiv]
  generalize g.op.eval (g.inputs.map (fun i => xs.getD i false))=v
  refine ⟨by simp [len,Nat.add_assoc],by simp; omega,?_,?_⟩
  · rwa [List.getD_append _ _ _ _ lt]
  · intro i hi
    simp only [List.length_append,List.length_singleton] at hi
    by_cases before : i<xs.length
    · rw [List.getD_append _ _ _ _ (by omega : off+i<ys.length),List.getD_append _ _ _ _ before]
      exact matchOld i before
    · have ends : i=xs.length := by omega
      subst i
      rw [←len]
      simp [List.getD_eq_getElem?_getD]

theorem simulation {off zero : ℕ} (xs ys : List Bool) (gs : List Gate) (h : Fits off zero xs ys) :
    Fits off zero (run gs xs) (run (lift off zero xs.length gs) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    have stepH := step_ok h g
    have rec := ih (step xs g) (step ys (liftGate xs.length off zero g)) stepH
    simpa only [run,lift,List.foldl_cons,step,List.length_append,List.length_singleton] using rec

theorem readResult {off zero} {xs ys : List Bool} (h : Fits off zero xs ys) (r : ℕ) :
    ys.getD (index xs.length off zero r) false=xs.getD r false := by
  by_cases hr : r<xs.length
  · simpa [index,hr] using h.2.2.2 r hr
  · rw [index,if_neg hr,h.2.2.1,List.getD_eq_default _ _ (by omega : xs.length≤r)]

theorem lift_mono (off zero n : ℕ) (gs : List Gate)
    (ok : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) :
    ∀ g∈lift off zero n gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2 := by
  induction gs generalizing n with
  | nil => simp [lift]
  | cons head gs ih =>
    intro g hg
    simp only [lift,List.mem_cons] at hg
    rcases hg with rfl|tail
    · simpa [liftGate] using ok head (List.mem_cons_self ..)
    · exact ih (n+1) (fun v hv => ok v (List.mem_cons_of_mem _ hv)) g tail

end Plane8311.MaskSimulation
