import PEqualNP.Defs

namespace L9736Transfer

def NoLarger {n : Nat} (x y : Fin n → Bool) : Prop :=
  ∀ i, x i = true → y i = true

def MonotoneTail {n : Nat} (K : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, NoLarger x y → K x = true → K y = true

def Covers {n : Nat} {A B : Type} (old : A → Fin n → Bool) (new : B → Fin n → Bool)
    (wantA : A → Bool) (wantB : B → Bool) : Prop :=
  ∀ b, ∃ a, wantA a = wantB b ∧
    (wantB b = true → NoLarger (old a) (new b)) ∧
    (wantB b = false → NoLarger (new b) (old a))

theorem sound {n : Nat} {A B : Type} {old : A → Fin n → Bool} {new : B → Fin n → Bool}
    {wantA : A → Bool} {wantB : B → Bool} {K : (Fin n → Bool) → Bool}
    (mono : MonotoneTail K) (h : Covers old new wantA wantB)
    (correct : ∀ a, K (old a) = wantA a) : ∀ b, K (new b) = wantB b := by
  intro b
  obtain ⟨a, ha, hpos, hneg⟩ := h b
  cases hb : wantB b
  · by_contra! hc
    have hn : K (new b) = true := by
      cases hv : K (new b) <;> simp_all
    have ht := mono _ _ (hneg hb) hn
    rw [correct a, ha, hb] at ht
    exact Bool.false_ne_true ht
  · exact mono _ _ (hpos hb) ((correct a).trans (ha.trans hb))

def bigger (n : Nat) (W Z : List Bool) : Prop :=
  W.length = n ∧ Z.length = n ∧ ∀ i, W.getD i false = true → Z.getD i false = true

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

theorem any_mono (args : List Nat) (a b : Nat → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (args.map a).any id = true → (args.map b).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id_eq]
  rintro ⟨_, ⟨i, hi, rfl⟩, hia⟩
  exact ⟨b i, ⟨i, hi, rfl⟩, h i hia⟩

theorem all_mono (args : List Nat) (a b : Nat → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (args.map a).all id = true → (args.map b).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id_eq]
  intro hg q hq
  obtain ⟨i, hi, rfl⟩ := hq
  exact h i (hg _ ⟨i, hi, rfl⟩)

theorem step_mono {n : Nat} {W Z : List Bool} (h : bigger n W Z) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) : bigger (n + 1) (step W g) (step Z g) := by
  obtain ⟨hw, hz, hab⟩ := h
  refine ⟨by simp [step,hw], by simp [step,hz], fun i hi => ?_⟩
  rcases lt_trichotomy i n with lt | rfl | gt
  · rw [step,List.getD_append _ _ _ _ (by omega)] at hi
    rw [step,List.getD_append _ _ _ _ (by omega)]
    exact hab i hi
  · have getLast (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
      simp [List.getD_eq_getElem?_getD]
    rw [step, ← hw, getLast] at hi
    rw [step, ← hz, getLast]
    rcases op with op | op
    · rw [op] at hi ⊢
      exact all_mono _ _ _ hab hi
    · rw [op] at hi ⊢
      exact any_mono _ _ _ hab hi
  · have hi' : (step W g).length ≤ i := by simp [step,hw] <;> omega
    rw [List.getD_eq_default _ _ hi'] at hi
    exact (Bool.false_ne_true hi).elim

theorem run_mono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {n : Nat} {W Z : List Bool} (h : bigger n W Z) :
    bigger (n + gs.length) (gs.foldl step W) (gs.foldl step Z) := by
  induction gs generalizing n W Z with
  | nil => simpa using h
  | cons g gs ih =>
    have next := ih (fun f hf => ops f (List.mem_cons_of_mem _ hf))
      (step_mono h g (ops g (by simp)))
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem circuit_tail (C : Circuit) (hm : Monotone2 C) (n : Nat) :
    MonotoneTail (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y xy
  have h : bigger n (List.ofFn x) (List.ofFn y) := by
    refine ⟨List.length_ofFn, List.length_ofFn, fun i h => ?_⟩
    by_cases hi : i < n
    · simpa [List.getD_eq_getElem?_getD, hi] using
        (xy ⟨i,hi⟩ (by simpa [List.getD_eq_getElem?_getD, hi] using h))
    · simp [List.getD_eq_getElem?_getD, hi] at h
  obtain ⟨-, -, hw⟩ := run_mono C.gates (fun g hg => (hm g hg).1) h
  exact hw C.output

end L9736Transfer
