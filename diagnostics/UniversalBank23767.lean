import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23767.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
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


theorem relabelEval {n m : ℕ} (C : Circuit) (π : Fin n → Fin m) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
  (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem relabelFan {n m : ℕ} (C : Circuit) (π : Fin n → Fin m) (h : FanInTwo C) :
    FanInTwo (relabel n m π C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h old mem).1, by simpa [relGate] using (h old mem).2⟩

theorem relabelAO {n m : ℕ} (C : Circuit) (π : Fin n → Fin m) (h : Monotone2 C) :
    Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h old mem).1,by simpa [relGate] using (h old mem).2⟩
def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

def legal (C : Circuit) := C.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2))

theorem sound (C : Circuit) (h : legal C = true) : FanInTwo C := by
  intro g hg
  have passed := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩
def isAO (g : Gate) : Bool := match g.op with
  | .and | .or => true
  | _ => false
theorem aoSound (C : Circuit) (hf : FanInTwo C) (ha : C.gates.all isAO = true) : Monotone2 C := by
  intro g hg
  have good := List.all_eq_true.mp ha g hg
  refine ⟨?_, (hf g hg).2⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  cases hh : g.op <;> simp [isAO,hh] at good ⊢

def address (x : Fin 5 → Bool) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0)
def assignment (w : Fin 32) (i : Fin 5) := w.val.testBit i.val
theorem readAddress : ∀ x : Fin 5 → Bool, address x < 32 ∧
    ∀ i : Fin 5, (address x).testBit i.val = x i := by decide +kernel
abbrev Idx := Fin 240
def circuits : Array Circuit := #[⟨[⟨.and, [1, 2]⟩, ⟨.and, [0, 5]⟩], 6⟩,⟨[⟨.and, [1, 2]⟩, ⟨.and, [0, 5]⟩], 6⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.and, [2, 4]⟩], 5⟩,⟨[⟨.and, [2, 4]⟩], 5⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩,⟨[⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 6]⟩], 7⟩,⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 6]⟩], 7⟩,⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 6]⟩], 7⟩,⟨[⟨.not, [2]⟩, ⟨.and, [3, 5]⟩], 6⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [4, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [4, 7]⟩], 8⟩,⟨[], 2⟩,⟨[], 2⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [6]⟩], 7⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.not, [3]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 7]⟩], 8⟩,⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 6]⟩], 8⟩,⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 6]⟩], 8⟩,⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 6]⟩], 9⟩,⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.or, [2, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [2, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.not, [4]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.and, [1, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [5, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [3, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 5]⟩], 6⟩,⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 5]⟩], 6⟩,⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩], 9⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [0, 2]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.not, [3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [1]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 6]⟩], 7⟩,⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩], 9⟩,⟨[⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.and, [5, 6]⟩], 7⟩,⟨[⟨.not, [0]⟩, ⟨.not, [3]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 7]⟩], 9⟩,⟨[⟨.or, [2, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.not, [1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 6]⟩], 7⟩,⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.or, [2, 4]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.or, [1, 2]⟩], 5⟩,⟨[⟨.or, [1, 2]⟩], 5⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 4]⟩, ⟨.not, [5]⟩], 6⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.not, [0]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 0]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [2, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [0, 2]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.not, [8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [0, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 2]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [9, 11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [5]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.not, [1]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.not, [4]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [1, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩,⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩,⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [1]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.and, [2, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩], 8⟩,⟨[⟨.and, [2, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [2, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [6, 11]⟩], 12⟩,⟨[⟨.not, [0]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩,⟨[⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 2]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [2, 4]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [2, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [3]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [3, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [9, 11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [2, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 9]⟩], 10⟩,⟨[⟨.or, [2, 3]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [2, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 0]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [3, 8]⟩], 9⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩], 6⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 5]⟩], 6⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩], 10⟩,⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [6]⟩], 7⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩], 12⟩,⟨[⟨.or, [1, 2]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [9]⟩], 10⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩,⟨[⟨.and, [2, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.not, [3]⟩], 5⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [5]⟩, ⟨.or, [7, 8]⟩], 9⟩,⟨[⟨.not, [1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩], 10⟩,⟨[⟨.not, [3]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [0]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [7]⟩, ⟨.or, [6, 8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.or, [1, 5]⟩], 6⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.not, [0]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [1]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [2]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 11]⟩], 12⟩,⟨[⟨.not, [0]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.not, [1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 10]⟩], 11⟩,⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [0, 4]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.not, [2]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [3]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 11]⟩], 12⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [3]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 11]⟩], 12⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [1]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 3]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 11]⟩], 12⟩,⟨[⟨.or, [0, 2]⟩, ⟨.not, [1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩,⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩], 10⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.not, [7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩], 7⟩,⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.and, [2, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩], 9⟩,⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.not, [6]⟩], 7⟩,⟨[⟨.and, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [7]⟩], 8⟩,⟨[⟨.and, [1, 2]⟩, ⟨.not, [5]⟩], 6⟩,⟨[⟨.not, [0]⟩, ⟨.or, [0, 5]⟩], 6⟩,⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩], 8⟩]
def prices : Array Nat := #[2,2,4,1,1,4,2,2,3,3,3,2,4,4,0,0,3,7,5,7,5,4,4,4,5,3,3,4,4,5,5,5,4,4,4,5,5,5,4,2,2,4,7,6,7,5,6,5,6,7,4,3,3,7,5,5,5,5,5,6,7,7,5,5,5,5,6,6,3,3,5,3,5,5,6,3,4,4,6,6,6,4,4,4,1,1,5,4,8,7,8,2,7,6,6,4,5,6,6,3,8,8,8,8,7,8,7,7,5,8,6,5,7,6,7,4,7,7,7,6,6,7,7,7,7,7,7,5,5,5,6,7,7,7,5,4,4,6,7,7,7,7,6,6,7,5,5,5,7,7,5,6,6,7,7,6,3,3,8,4,6,7,7,7,6,4,6,8,6,6,6,7,4,6,6,4,4,6,6,7,4,4,6,5,2,2,5,4,7,8,6,3,8,8,8,6,7,5,1,4,5,6,7,5,7,2,6,7,8,7,6,7,6,3,7,8,7,8,8,6,8,4,6,6,4,4,6,3,3,5,5,4,4,5,5,3,4,2,2,4]
def tables : Array Nat := #[2155905152,2155905152,3,4042260480,4042260480,34,2861083272,2861083272,3084,4278251008,4278251008,251662080,4294836224,4294836224,4042322160,4042322160,1285,305,3342353,2863311372,65285,2863311547,4001951368,4001951368,4026594372,3941253312,3941253312,4290834624,4290834624,4280418338,4289374856,4289374856,64240,4241291400,4241291400,3424832546,4289243816,4289243816,4042325760,4006407884,4006407884,50529024,62769,269619218,2863309036,285234500,2862918308,4041404642,168442634,572924454,4042518768,4291603080,4291603080,2867765476,4291624128,4291624128,4291693066,4293699752,4293699752,3437415650,4209703648,4209703648,4294705392,4291619528,4291619528,4291621824,4293831336,4293831336,4294962688,4294962688,51118860,64764,1356615900,15732720,2868882088,4092850416,4289395880,4289395880,4210752202,4291624648,4291624648,4294897904,4294897904,252702960,4244438268,4244438268,16843013,196659,3211569,3211509,3272949,13107,1141982225,1769499,4042282308,3439263795,2863310245,572989991,2863312812,2863311615,3291595825,4121032097,1427197971,99942705,2947460868,4039962862,4293062882,2699866092,2945298317,3364113,4244582451,3435986175,4294904347,4293849314,2868558840,4294963443,4276682472,4276682472,4291743242,4277074056,4277074056,4293589696,4293589696,4242734306,4293458664,4293458664,4274716362,4276944620,4276944620,4126430532,4291480266,4290837226,4089510890,4059828684,4025397162,4294965384,4294965384,4042264332,2868161268,4043050956,4277992072,4277992072,4293720800,4293720800,4293587178,4277075626,4277075626,4042325964,4293962490,2948116408,4294954944,4293720808,4293720808,4293591016,4293591016,4284111450,4278123258,4278123258,185469710,1431655508,993737482,2863330788,39191126,174000730,2868882168,4042326012,4278910926,1430672710,4043109372,4291623658,4294945516,804401138,4210753278,4294639304,4294639304,4294769400,4294769400,4293850596,4294965962,3152983020,4278124282,4278124282,1432769894,4284153690,4294770684,4294770684,13111,286331187,3212597,19988981,825307637,986895,20250933,1363366211,3474741,31261149,19990005,268370739,16711935,3425946675,2946871205,287117597,2868751101,168451935,4043305198,3486502863,4243848435,4211079765,4293132259,2946346909,4076335863,4294966798,1532713819,4294949819,4294966479,4211014652,4294963708,4294769406,4294965996,4294966250,4294917070,4294966267,4294967020,4294967020,4294967034,4294967034,4294967130,4294967292,4294967292,54461247,3343671,1431655799,3346239,53675007,53675895,858993663,356455743,1061109567,4294967295,4294967294]
def pure : Array Bool := #[true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,false,false,false,false,false,false,true,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,false,false,false,false,false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,true,true,true,false,true,true,false,true,true,false,false,false,false,false,false,true,true,false,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,true]
def canonical (i : Idx) : Circuit := circuits[i.val]?.getD ⟨[],0⟩
def price (i : Idx) : Nat := prices[i.val]?.getD 0
def truth (i : Idx) : Nat := tables[i.val]?.getD 0
def onlyAO (i : Idx) : Bool := pure[i.val]?.getD false
def valid (i : Idx) : Prop :=
  legal (canonical i) = true ∧ (canonical i).size = price i ∧
  (canonical i).gates.all isAO = onlyAO i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allValid : ∀ i : Idx, legal (canonical i) = true ∧ (canonical i).size = price i ∧
    (canonical i).gates.all isAO = onlyAO i := by decide +kernel
def reads (i : Idx) (v : Fin 32) : Bool :=
  decide ((canonical i).eval (List.ofFn (assignment v)) = (truth i).testBit v.val)
def group0 : List Idx := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK0 : group0.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group1 : List Idx := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK1 : group1.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group2 : List Idx := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK2 : group2.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group3 : List Idx := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK3 : group3.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group4 : List Idx := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK4 : group4.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group5 : List Idx := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK5 : group5.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group6 : List Idx := [72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK6 : group6.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group7 : List Idx := [84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK7 : group7.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group8 : List Idx := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK8 : group8.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group9 : List Idx := [108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK9 : group9.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group10 : List Idx := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK10 : group10.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group11 : List Idx := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK11 : group11.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group12 : List Idx := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK12 : group12.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group13 : List Idx := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK13 : group13.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group14 : List Idx := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK14 : group14.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group15 : List Idx := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK15 : group15.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group16 : List Idx := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK16 : group16.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group17 : List Idx := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK17 : group17.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group18 : List Idx := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK18 : group18.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def group19 : List Idx := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem groupOK19 : group19.all (fun i => (List.finRange 32).all (reads i)) = true := by decide +kernel
def labels : List Idx := group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allLabels : ∀ i : Idx, i ∈ labels := by decide +kernel
theorem labelsOK : labels.all (fun i => (List.finRange 32).all (reads i)) = true := by
  simp only [labels,List.all_append,groupOK0,groupOK1,groupOK2,groupOK3,groupOK4,groupOK5,groupOK6,groupOK7,groupOK8,groupOK9,groupOK10,groupOK11,groupOK12,groupOK13,groupOK14,groupOK15,groupOK16,groupOK17,groupOK18,groupOK19,Bool.true_and]
theorem fullTruth (i : Idx) (x : Fin 5 → Bool) :
    (canonical i).eval (List.ofFn x) = (truth i).testBit (address x) := by
  let v : Fin 32 := ⟨address x,(readAddress x).1⟩
  have good := List.all_eq_true.mp (List.all_eq_true.mp labelsOK i (allLabels i)) v (List.mem_finRange _)
  have eq : assignment v = x := funext (readAddress x).2
  have ht := of_decide_eq_true good
  change (canonical i).eval (List.ofFn (assignment v)) = (truth i).testBit (address x) at ht
  simpa only [eq] using ht

theorem bank {n : ℕ} (i : Idx) (π : Fin 5 → Fin n) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = price i ∧ (onlyAO i = true → Monotone2 C) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (truth i).testBit (address (x ∘ π)) := by
  obtain ⟨legalC,sizeC,pureC⟩ := allValid i
  have hf := sound _ legalC
  refine ⟨relabel 5 n π (canonical i),relabelFan _ _ hf,?_,?_,?_⟩
  · simpa [relabel,Circuit.size] using sizeC
  · intro h
    exact relabelAO _ _ (aoSound _ hf (pureC.trans h))
  · intro x
    rw [relabelEval,fullTruth]
end PEqualNP.Outside.L_meta_23767.Bank
open PEqualNP.Outside.L_meta_23767.Bank in
theorem PEqualNP.Outside.L_meta_23767 {n : ℕ} (i : Idx) (π : Fin 5 → Fin n) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = price i ∧
      (onlyAO i = true → PEqualNP.MetaComplexity.Monotone2 C) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (truth i).testBit (address (x ∘ π)) := bank i π
