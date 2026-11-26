import PEqualNP.Defs

namespace Probe9739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000
abbrev T := Fin 5 → Bool
def zero : T := fun _ => false
def hold (t : T) : Prop :=
  (t 1=true → t 3=true) ∧ (t 2=true → t 4=true) ∧
  (t 0=true → t 1=true ∨ t 2=true ∨ (t 3=true ∧ t 4=true))
def probes (t : T) := t 0=true → (t 3=true ∨ t 4=true) → t 3=true ∧ t 4=true
def born (a b : T) := (a 1=true ∧ b 2=true) ∨ (a 2=true ∧ b 1=true)
def clean (t : T) := t 3=false ∧ t 4=false
def both (d : Bool) (a b : T) : T := fun k => if d then a k || b k else a k && b k
instance (t : T) : Decidable (hold t) := by unfold hold; infer_instance
instance (t : T) : Decidable (probes t) := by unfold probes; infer_instance
instance (a b : T) : Decidable (born a b) := by unfold born; infer_instance
instance (t : T) : Decidable (clean t) := by unfold clean; infer_instance

theorem combine : ∀ (d : Bool) (a b : T), hold a → hold b →
    (d=false → probes (both d a b)) →
    (d=false → ¬(clean (both d a b) ∧ born a b)) → hold (both d a b) := by decide +kernel
theorem zeroHold : hold zero := by decide +kernel
theorem oneHold : hold (fun _ => true) := by decide +kernel

def read (w : List T) (i : Nat) := w.getD i zero
def result (w : List T) (g : Gate) : T := fun k => g.op.eval (g.inputs.map fun i => read w i k)
def step (w : List T) (g : Gate) := w++[result w g]
def cleanBirth (w : List T) (g : Gate) : Prop :=
  g.op=.and ∧ clean (result w g) ∧ ∃ i j, g.inputs=[i,j] ∧ born (read w i) (read w j)
def cov (w : List T) (g : Gate) := g.op=.and → probes (result w g)
def allCov : List T → List Gate → Prop
  | _, [] => True
  | w, g::gs => cov w g ∧ allCov (step w g) gs
def someBirth : List T → List Gate → Prop
  | _, [] => False
  | w, g::gs => cleanBirth w g ∨ someBirth (step w g) gs

theorem readHold {w : List T} (hw : ∀ t∈w, hold t) (i : Nat) : hold (read w i) := by
  by_cases h : i<w.length
  · rw [read,List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem h)
  · simp [read,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : w.length≤i),zeroHold]

theorem gateHold (w : List T) (g : Gate) (hw : ∀ t∈w, hold t)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length≤2)
    (covered : cov w g) (none : ¬cleanBirth w g) : hold (result w g) := by
  obtain ⟨operation,ins⟩ := g
  change operation=.and ∨ operation=.or at op
  change ins.length≤2 at arity
  cases ins with
  | nil =>
    rcases op with rfl|rfl
    · exact oneHold
    · exact zeroHold
  | cons i rest =>
    cases rest with
    | nil =>
      rcases op with rfl|rfl <;> simpa [result,GateOp.eval] using readHold hw i
    | cons j tail =>
      cases tail with
      | cons a rest => simp at arity
      | nil =>
        rcases op with rfl|rfl
        · have eq : result w ⟨.and,[i,j]⟩ = both false (read w i) (read w j) := by
            funext k; simp [result,GateOp.eval,both]
          rw [eq]
          apply combine false _ _ (readHold hw i) (readHold hw j)
          · intro _
            rw [←eq]
            exact covered rfl
          · rintro _ ⟨cl,ab⟩
            exact none ⟨rfl,eq.symm ▸ cl,i,j,rfl,ab⟩
        · have eq : result w ⟨.or,[i,j]⟩ = both true (read w i) (read w j) := by
            funext k; simp [result,GateOp.eval,both]
          rw [eq]
          exact combine true _ _ (readHold hw i) (readHold hw j) (by simp) (by simp)

theorem inductionBound (w : List T) (gs : List Gate) (hw : ∀ t∈w, hold t)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (covered : allCov w gs) (noBirth : ¬someBirth w gs) :
    ∀ t∈gs.foldl step w, hold t := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    obtain ⟨op,arity⟩ := legal g List.mem_cons_self
    apply ih (step w g) _ (fun g' m => legal g' (List.mem_cons_of_mem _ m)) covered.2
      (fun h => noBirth (Or.inr h))
    intro t inw
    rcases List.mem_append.mp inw with ht|ht
    · exact hw _ ht
    · have eq : t=result w g := List.mem_singleton.mp ht
      exact eq ▸ gateHold w g hw op arity covered.1 (fun h => noBirth (Or.inl h))

theorem forceBirth (w : List T) (gs : List Gate) (o : Nat) (hw : ∀ t∈w, hold t)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (covered : allCov w gs) (out : read (gs.foldl step w) o = ![true,false,false,false,false]) :
    someBirth w gs := by
  by_contra no
  have h := readHold (inductionBound w gs hw legal covered no) o
  rw [out] at h
  exact (show ¬hold (![true,false,false,false,false] : T) by decide +kernel) h

def valueStep (w : List Bool) (g : Gate) :=
  w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def init {n : Nat} (rows : Fin 5 → Fin n → Bool) : List T := List.ofFn fun i k => rows k i
theorem project (w : List T) (gs : List Gate) (k : Fin 5) :
    (gs.foldl step w).map (fun t => t k) = gs.foldl valueStep (w.map fun t => t k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih]
    congr 1
    simp only [step,valueStep,List.map_append,List.map_cons,List.map_nil,result,read]
    congr 3
    apply List.map_congr_left
    intro i _
    by_cases h : i<w.length
    · simp [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h : i<(w.map fun t => t k).length)]
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : w.length≤i),
        List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt h) : (w.map fun t => t k).length≤i),zero]

theorem evalTrace {n} (C : Circuit) (rows : Fin 5 → Fin n → Bool) (k : Fin 5) :
    read (C.gates.foldl step (init rows)) C.output k = C.eval (List.ofFn (rows k)) := by
  let w := C.gates.foldl step (init rows)
  have ids : (init rows).map (fun t => t k) = List.ofFn (rows k) := by simp [init,List.map_ofFn,Function.comp_def]
  have p := project (init rows) C.gates k
  rw [ids] at p
  change (w.getD C.output zero) k = (C.gates.foldl valueStep _).getD C.output false
  rw [←p]
  change (w.getD C.output zero) k = (w.map fun t => t k).getD C.output false
  by_cases h : C.output<w.length
  · simp [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h : C.output<(w.map fun t => t k).length)]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : w.length≤C.output),
        List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt h) : (w.map fun t => t k).length≤C.output),zero]

end Probe9739
