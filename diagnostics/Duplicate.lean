import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20412.Duplicate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

variable {n m : Nat}

def ref (ρ : Fin n → Fin m) (j u : Fin n) : Fin (m+1) :=
  if u=j then Fin.last m else (ρ u).castSucc

def folded (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (x : Fin m → Bool) (u : Fin n) : Bool :=
  if u=j then x (ρ j) || x b else x (ρ u)

def headGate (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) : Gate :=
  ⟨.or, [(ρ j).val,b.val]⟩

def lift (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) : Circuit :=
  ⟨headGate ρ j b :: C.gates.map (relGate n (m+1) (ref ρ j)),
   wmap n (m+1) (ref ρ j) C.output⟩

theorem cost (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) :
    (lift ρ j b C).size = C.size + 1 := by simp [Circuit.size,lift]

theorem mono (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) {C : Circuit} (h : Monotone2 C) :
    Monotone2 (lift ρ j b C) := by
  intro g hg
  change g ∈ headGate ρ j b :: C.gates.map _ at hg
  rcases List.mem_cons.mp hg with rfl|hg
  · simp [headGate]
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h k hk

theorem evaluation (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) (x : Fin m → Bool) :
    (lift ρ j b C).eval (List.ofFn x) = C.eval (List.ofFn (folded ρ j b x)) := by
  let y := x (ρ j) || x b
  have startWire : step (List.ofFn x) (headGate ρ j b) = List.ofFn x ++ [y] := by
    simp [step,headGate,y,GateOp.eval,List.getD_eq_getElem?_getD]
  have base : Rel n (m+1) (ref ρ j) (List.ofFn (folded ρ j b x)) (List.ofFn x ++ [y]) := by
    refine ⟨by simp,by simp <;> omega,?_⟩
    intro w
    by_cases h : w<n
    · let u : Fin n := ⟨w,h⟩
      have raw : (List.ofFn (folded ρ j b x)).getD w false = folded ρ j b x u := by
        simp [u,List.getD_eq_getElem?_getD,h]
      rw [raw,show wmap n (m+1) (ref ρ j) w=((ref ρ j) u).val by simp [wmap,h,u]]
      by_cases hu : u=j
      · simp [ref,hu,folded,y,List.getD_eq_getElem?_getD]
      · rw [show ((ref ρ j) u).val=(ρ u).val by simp [ref,hu],
          List.getD_append _ _ _ _ (by simp)]
        simp [folded,hu,List.getD_eq_getElem?_getD]
    · have newIndex : (List.ofFn x ++ [y]).length ≤ wmap n (m+1) (ref ρ j) w := by
        simp [wmap,h]
      rw [List.getD_eq_default _ _ newIndex,List.getD_eq_default _ _ (by simp <;> omega)]
  have finish := (rel_fold n (m+1) (ref ρ j) C.gates _ _ base).2.2 C.output
  change ((C.gates.map _).foldl step (step (List.ofFn x) (headGate ρ j b))).getD _ false = _
  rw [startWire]
  exact finish

def oldPins : Fin 6 → Fin 7 := ![0,1,2,3,4,6]
def oldColumn : Fin 4 → Fin 3 := ![0,1,1,2]
def promised (u : Fin 3) (v : Fin 4) (k : Fin 7) : Bool :=
  decide (k.val = u.val ∨ k.val = 3+v.val)

theorem duplicateColumn (A : Fin 3 → Fin 3 → Bool) {s : Nat} (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun u v => A u (oldColumn v)) (s+1) := by
  obtain ⟨C,hC,hs,hA⟩ := h
  refine ⟨lift oldPins 4 5 C, mono oldPins 4 5 hC, ?_, ?_⟩
  · rw [cost]; omega
  · intro u v
    have input : ∀ u v, List.ofFn (promised u v) = oneEach u v := by decide +kernel
    have reduced : ∀ u v, List.ofFn (folded oldPins 4 5 (promised u v)) = oneEach u (oldColumn v) := by decide +kernel
    rw [← input u v, evaluation, reduced]
    exact hA u (oldColumn v)

end PEqualNP.Outside.L_meta_20412.Duplicate
