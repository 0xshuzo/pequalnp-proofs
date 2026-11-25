import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.Compress4111
set_option maxHeartbeats 700000

/- The wire-prefix facts are from L-meta-1572 and L-meta-1353. -/
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def addGate (D : Circuit) (g : Gate) : Circuit :=
  ⟨D.gates ++ [g], D.output⟩

lemma length_wires {n : ℕ} (D : Circuit) (x : Fin n → Bool) :
    (D.wires (List.ofFn x)).length = n + D.size := by
  change (run D.gates (List.ofFn x)).length = n + D.gates.length
  simp only [run_length, List.length_ofFn]

lemma add_size (D : Circuit) (g : Gate) : (addGate D g).size = D.size + 1 := by
  simp [addGate, Circuit.size]

lemma add_wires {n : ℕ} (D : Circuit) (g : Gate) (x : Fin n → Bool) :
    (addGate D g).wires (List.ofFn x) =
      D.wires (List.ofFn x) ++ [g.op.eval (g.inputs.map (fun i => value D x i))] := by
  simp [addGate,Circuit.wires,value,List.foldl_append]

lemma add_old {n i : ℕ} (D : Circuit) (g : Gate) (h : i < n + D.size) (x : Fin n → Bool) :
    value (addGate D g) x i = value D x i := by
  change ((addGate D g).wires (List.ofFn x)).getD i false = _
  rw [add_wires, List.getD_append _ _ _ _ (by simpa only [length_wires] using h)]
  rfl

lemma add_new {n : ℕ} (D : Circuit) (g : Gate) (x : Fin n → Bool) :
    value (addGate D g) x (n+D.size) = g.op.eval (g.inputs.map (fun i => value D x i)) := by
  change ((addGate D g).wires (List.ofFn x)).getD (n+D.size) false = _
  rw [add_wires,List.getD_append_right _ _ _ _ (by rw [length_wires])]
  simp only [length_wires,Nat.sub_self,List.getD_cons_zero]

def Supplies {n : ℕ} (D : Circuit) (F : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, F x = false) ∨ ∃ i < n+D.size, ∀ x, value D x i = F x

lemma previous {n : ℕ} {D : Circuit} {F : (Fin n → Bool) → Bool} (h : Supplies D F) (g : Gate) :
    Supplies (addGate D g) F := by
  rcases h with z | ⟨i,hi,read⟩
  · exact Or.inl z
  · refine Or.inr ⟨i,by rw [add_size]; omega,fun x => (add_old D g hi x).trans (read x)⟩

lemma selectWire {n : ℕ} {D : Circuit} {F : (Fin n → Bool) → Bool} (h : Supplies D F) :
    ∃ i, ∀ x, value D x i = F x := by
  rcases h with z | ⟨i,_,read⟩
  · exact ⟨n+D.size,fun x => (missing_value D x _ le_rfl).trans (z x).symm⟩
  · exact ⟨i,read⟩

lemma cost_keep (S : Finset ℕ) (k : ℕ) (hk : k ∉ S) :
    ((Finset.range (k+1)) \ S).card = ((Finset.range k) \ S).card + 1 := by
  have e : Finset.range (k+1) \ S = insert k (Finset.range k \ S) := by
    ext t
    by_cases h : t = k
    · subst t
      simp [hk]
    · have same : t < k+1 ↔ t < k := by omega
      simp [Finset.mem_sdiff, same, h]
  rw [e, Finset.card_insert_of_notMem (by simp)]

lemma cost_skip (S : Finset ℕ) (k : ℕ) (hk : k ∈ S) :
    Finset.range (k+1) \ S = Finset.range k \ S := by
  ext t
  by_cases h : t = k
  · subst t
    simp [hk]
  · have same : t < k+1 ↔ t < k := by omega
    simp [Finset.mem_sdiff, same]

theorem compress : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
      let w := fun (u v : Fin n) (i : ℕ) (x : Fin n → Bool) =>
        (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD i false
      FanInTwo C → S ⊆ Finset.range C.size → (∀ j ∈ S, (∀ x, w u v (n+j) x = false) ∨
        ∃ i < n+j, ∀ x, w u v (n+j) x = w u v i x) →
      ∃ t, t + S.card ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t := by
  classical
  intro n C u v S
  dsimp only
  intro hfan sub aliases
  let fix (x : Fin n → Bool) := Function.update (Function.update x u false) v false
  let fn (i : ℕ) (x : Fin n → Bool) := value C (fix x) i
  let zero : Circuit := ⟨[],0⟩
  have build (k : ℕ) (hk : k ≤ C.size) :
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ (Finset.range k \ S).card ∧
        ∀ i < n+k, Supplies D (fn i) := by
    induction k with
    | zero =>
      refine ⟨zero,by simp [zero,FanInTwo],by simp [zero,Circuit.size],?_⟩
      intro i hi
      let a : Fin n := ⟨i,by omega⟩
      have raw (x : Fin n → Bool) : fn i x = fix x a := input_value C (fix x) a
      by_cases hv : a = v
      · left
        intro x
        rw [raw,hv]
        simp [fix]
      by_cases hu : a = u
      · left
        intro x
        rw [raw]
        simp [fix, Function.update_of_ne hv, hu]
      · right
        refine ⟨i,by dsimp [zero,Circuit.size]; omega,?_⟩
        intro x
        rw [raw]
        change value zero x a = fix x a
        rw [input_value]
        simp [fix,Function.update_of_ne hv,Function.update_of_ne hu]
    | succ k ih =>
      have hlt : k < C.size := by omega
      obtain ⟨D,hD,budget,prior⟩ := ih (by omega)
      by_cases saved : k ∈ S
      · refine ⟨D,hD,by rw [cost_skip S k saved]; exact budget,?_⟩
        intro i hi
        by_cases old : i < n+k
        · exact prior i old
        have index : i = n+k := by omega
        subst i
        rcases aliases k saved with c | ⟨a,ha,eq⟩
        · exact Or.inl c
        · have equal : fn (n+k) = fn a := funext eq
          rw [equal]
          exact prior a ha
      · let g := C.gates[k]'hlt
        have source (x : Fin n → Bool) : fn (n+k) x =
            g.op.eval (g.inputs.map fun i => if i < n+k then fn i x else false) := by
          have h := gate_value C (fix x) (n+k) (by omega) (by omega)
          simpa only [Nat.add_sub_cancel_left] using h
        have provide (i : ℕ) : ∃ a : ℕ, ∀ x : Fin n → Bool,
            value D x a = if i < n+k then fn i x else false := by
          by_cases h : i < n+k
          · obtain ⟨a,hw⟩ := selectWire (prior i h)
            exact ⟨a,fun x => by simpa only [if_pos h] using hw x⟩
          · exact ⟨n+D.size,fun x => by rw [if_neg h]; exact missing_value D x _ le_rfl⟩
        choose ren hren using provide
        let next : Gate := ⟨g.op,g.inputs.map ren⟩
        have sound (x : Fin n → Bool) : value (addGate D next) x (n+D.size) = fn (n+k) x := by
          rw [add_new,source]
          change g.op.eval ((g.inputs.map ren).map (fun i => value D x i)) = _
          rw [List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => hren i x)
        refine ⟨addGate D next,?_,by rw [add_size,cost_keep S k saved]; omega,?_⟩
        · intro g' hg'
          change g' ∈ D.gates ++ [next] at hg'
          rcases List.mem_append.mp hg' with h | h
          · exact hD g' h
          · obtain rfl := List.mem_singleton.mp h
            have hf := hfan g (List.getElem_mem hlt)
            exact ⟨hf.1,by simpa [next] using hf.2⟩
        · intro i hi
          by_cases old : i < n+k
          · exact previous (prior i old) next
          have index : i = n+k := by omega
          subst i
          exact Or.inr ⟨n+D.size,by rw [add_size]; omega,sound⟩
  obtain ⟨D,hD,size,supply⟩ := build C.size le_rfl
  have atOutput : Supplies D (fn C.output) := by
    by_cases h : C.output < n+C.size
    · exact supply C.output h
    · exact Or.inl (fun x => missing_value C (fix x) _ (by omega))
  obtain ⟨out,hout⟩ := selectWire atOutput
  have card := Finset.card_sdiff_add_card_eq_card sub
  rw [Finset.card_range] at card
  refine ⟨D.size,by omega,⟨⟨D.gates,out⟩,hD,le_rfl,?_⟩⟩
  intro x
  exact hout x

end PEqualNP.Outside.Compress4111
