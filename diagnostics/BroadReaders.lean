import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18611.Flat

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring

open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem disj {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 (fun v => decide (v ∉ L1)) (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

def MJ {n m : ℕ} (gates : List Gate) (L A : Fin m → Finset (Fin n)) (j : Fin m)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y)) g

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


end PEqualNP.Outside.L_meta_18611.Flat
namespace PEqualNP.Outside.L_meta_18611
namespace Formula5176

open PEqualNP.MetaComplexity

def leafLabel {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → Fin n
  | .lit v _, _ => v
  | .and a b, i => Fin.addCases (motive := fun _ => Fin n) (leafLabel a) (leafLabel b) i
  | .or a b, i => Fin.addCases (motive := fun _ => Fin n) (leafLabel a) (leafLabel b) i

private theorem cover531_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem cover531_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n), label = leafLabel φ ∧
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, rfl, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, hLA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, hLB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases (motive := fun _ => Fin n) LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · funext i; subst LA; subst LB; rfl
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply cover531_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, hLA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, hLB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases (motive := fun _ => Fin n) LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · funext i; subst LA; subst LB; rfl
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply cover531_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

private theorem cover531_formulaRectangles {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n), label = leafLabel φ ∧
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x y, φ.eval x = true → φ.eval y = false → X i x → Y i y →
          x (label i) = true ∧ y (label i) = false) := by
  obtain ⟨X, Y, label, same, total, goodX, goodY⟩ := cover531_formulaRectanglesStrong φ mono
  exact ⟨X, Y, label, same, total, fun i x y _ _ hx hy => ⟨(goodX i x hx).2, (goodY i y hy).2⟩⟩

private lemma cover531_starIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (v : Fin n) : ∀ u w, G.Adj u w → ¬ (G.Adj v u ∧ G.Adj v w) := by
  intro u w huw h
  exact triangle v u w ⟨h.1, huw, h.2.symm⟩

private lemma cover531_pairIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (square : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (a b : Fin n) (edge : G.Adj a b) : ∀ u w, G.Adj u w →
      ¬ (((G.Adj a u ∨ G.Adj b u) ∧ u ≠ a ∧ u ≠ b) ∧
         ((G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b)) := by
  intro u w huw h
  rcases h with ⟨⟨hu, hua, hub⟩, ⟨hw, hwa, hwb⟩⟩
  rcases hu with hau | hbu <;> rcases hw with haw | hbw
  · exact triangle a u w ⟨hau, huw, haw.symm⟩
  · exact square a u w b hwa.symm hub ⟨hau, huw, hbw.symm, edge.symm⟩
  · exact square b u w a hwb.symm hua ⟨hbu, huw, haw.symm, edge⟩
  · exact triangle b u w ⟨hbu, huw, hbw.symm⟩

private theorem cover531_rank {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {m : ℕ} (a b reject : E → V) (T : Finset V) (R : Fin m → (V × E → ℚ))
    (anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v))
    (units : ∀ e, Pi.single (reject e, e) 1 ∈ Submodule.span ℚ (Set.range R))
    (stars : ∀ v ∈ T, (fun p : V × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v)
      then 1 else 0) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card E + T.card ≤ m := by
  classical
  let unit (e : E) : V × E → ℚ := Pi.single (reject e, e) 1
  let star (v : V) : V × E → ℚ :=
    fun p => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0
  let family : E ⊕ ↥T → (V × E → ℚ) := Sum.elim unit (fun v => star v.val)
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (i : E ⊕ ↥T) : family i ∈ W := by
    cases i with
    | inl e => exact units e
    | inr v => exact stars v.val v.property
  have independent : LinearIndependent ℚ family := by
    rw [Fintype.linearIndependent_iff]
    intro c relation
    have atCoord (p : V × E) :
        (Finset.univ.sum fun e : E => c (Sum.inl e) * unit e p) +
          (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val p) = 0 := by
      simpa [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, family] using
        congrFun relation p
    have starZero (v : ↥T) : c (Sum.inr v) = 0 := by
      obtain ⟨e, different, incident⟩ := anchor v.val v.property
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (v.val, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h : (v.val, e) ≠ (reject j, j) := by
          intro same
          have ej : e = j := congrArg Prod.snd same
          subst j
          exact different (congrArg Prod.fst same)
        simp [unit, Pi.single_eq_of_ne h]
      have starSum : (Finset.univ.sum fun w : ↥T => c (Sum.inr w) * star w.val (v.val, e)) =
          c (Sum.inr v) := by
        rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
        · simp [star, incident]
        · intro w _ differentSub
          have h : v.val ≠ w.val := fun same => differentSub (Subtype.ext same.symm)
          simp [star, h]
      simpa only [unitSum, starSum, zero_add] using atCoord (v.val, e)
    intro i
    cases i with
    | inr v => exact starZero v
    | inl e =>
      have starSum : (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val (reject e, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [starZero v]
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (reject e, e)) = c (Sum.inl e) := by
        rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
        · simp [unit]
        · intro j _ different
          have h : (reject e, e) ≠ (reject j, j) := fun same =>
            different (congrArg Prod.snd same).symm
          simp [unit, Pi.single_eq_of_ne h]
      simpa only [unitSum, starSum, add_zero] using atCoord (reject e, e)
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (i : E ⊕ ↥T) : ↥W := ⟨family i, inSpan i⟩
  have liftedIndependent : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent ℚ family
    exact independent
  have lower : Fintype.card E + T.card ≤ Module.finrank ℚ ↥W := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using liftedIndependent.fintype_card_le_finrank
  have upper : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lower.trans upper

set_option maxHeartbeats 1000000 in
theorem colouredPrice : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ φ : PEqualNP.MetaComplexity.DMFormula n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → (∀ x : Fin n → Bool, φ.eval x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧ G.edgeFinset.card + T.card ≤ φ.leaves ∧
    ∀ Z : Finset (Fin n), (∀ u v, G.Adj u v → u∈T → v∈Z) →
    G.edgeFinset.card ≤ ((Finset.univ : Finset (Fin φ.leaves)).filter (fun i => leafLabel φ i∈Z)).card := by
  intro n G _ triangle square φ monotone evaluates
  classical
  obtain ⟨X, Y, label, sameLabel, partitions, labels⟩ := cover531_formulaRectangles φ monotone
  let E := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}
  have endpoints (e : E) : ∃ u v : Fin n, G.Adj u v ∧ Sym2.mk u v = e.val := by
    have member : e.val ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.property
    revert member
    refine Sym2.inductionOn e.val ?_
    intro u v member
    exact ⟨u, v, member, rfl⟩
  choose a b adjacent represented using endpoints
  let row (e : E) (v : Fin n) : Bool := decide (v = a e ∨ v = b e)
  let starColumn (v w : Fin n) : Bool := decide (G.Adj v w)
  let edgeColumn (e : E) (w : Fin n) : Bool :=
    decide ((G.Adj (a e) w ∨ G.Adj (b e) w) ∧ w ≠ a e ∧ w ≠ b e)
  have rowPositive (e : E) : φ.eval (row e) = true := by
    rw [evaluates]
    exact decide_eq_true ⟨a e, b e, adjacent e, by simp [row], by simp [row]⟩
  have starNegative (v : Fin n) : φ.eval (starColumn v) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_starIndependent G triangle v u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  have edgeNegative (e : E) : φ.eval (edgeColumn e) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_pairIndependent G triangle square (a e) (b e) (adjacent e) u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  let route (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) : Fin φ.leaves :=
    Classical.choose (partitions (row e) y (rowPositive e) hy)
  have routeMem (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      X (route e y hy) (row e) ∧ Y (route e y hy) y :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).1
  have routeUnique (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (i : Fin φ.leaves) (hi : X i (row e) ∧ Y i y) : i = route e y hy :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).2 i hi
  let selected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) := label (route e y hy)
  have labelProperties (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      (selected e y hy = a e ∨ selected e y hy = b e) ∧ y (selected e y hy) = false := by
    have result := labels (route e y hy) (row e) y (rowPositive e) hy
      (routeMem e y hy).1 (routeMem e y hy).2
    exact ⟨of_decide_eq_true result.1, result.2⟩
  have leftSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (b e) = true) : selected e y hy = a e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · exact chosen
    · simp [chosen, opposite] at missing
  have rightSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (a e) = true) : selected e y hy = b e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · simp [chosen, opposite] at missing
    · exact chosen
  let chosen (e : E) := selected e (edgeColumn e) (edgeNegative e)
  let reject (e : E) := if chosen e = a e then b e else a e
  have chosenEnd (e : E) : chosen e = a e ∨ chosen e = b e :=
    (labelProperties e (edgeColumn e) (edgeNegative e)).1
  have rejectEnd (e : E) : a e = reject e ∨ b e = reject e := by
    dsimp only [reject]
    split <;> simp
  have differentEnd (e : E) : chosen e ≠ reject e := by
    have distinct := (adjacent e).ne
    rcases chosenEnd e with left | right
    · simp [reject, left, distinct]
    · simp [reject, right, distinct.symm]
  let R (i : Fin φ.leaves) (p : Fin n × E) : ℚ :=
    if p.1 = label i ∧ X i (row p.2) then 1 else 0
  let col (v : Fin n) (y : Fin n → Bool) : Fin n × E → ℚ :=
    Finset.univ.sum fun i : Fin φ.leaves => if Y i y ∧ label i = v then R i else 0
  let span := Submodule.span ℚ (Set.range R)
  have colInSpan (v : Fin n) (y : Fin n → Bool) : col v y ∈ span := by
    apply Submodule.sum_mem
    intro i _
    split
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact span.zero_mem
  have colValue (v : Fin n) (y : Fin n → Bool) (hy : φ.eval y = false) (p : Fin n × E) :
      col v y p = if p.1 = v ∧ selected p.2 y hy = v then 1 else 0 := by
    simp only [col, Finset.sum_apply]
    rw [Finset.sum_eq_single (route p.2 y hy)]
    · by_cases same : label (route p.2 y hy) = v
      · simp [R, selected, same, (routeMem p.2 y hy).1, (routeMem p.2 y hy).2]
      · simp [selected, same]
    · intro i _ other
      by_cases inColumn : Y i y ∧ label i = v
      · have noRow : ¬ X i (row p.2) := fun hx => other (routeUnique p.2 y hy i ⟨hx, inColumn.1⟩)
        simp [inColumn, R, noRow]
      · simp [inColumn]
    · simp
  have columnOpposite (e : E) (v w : Fin n) (hv : a e = v ∨ b e = v)
      (edge : G.Adj v w) (other : Sym2.mk v w ≠ e.val) : edgeColumn e w = true := by
    rcases hv with rfl | rfl
    · have notLeft : w ≠ a e := edge.ne.symm
      have notRight : w ≠ b e := by
        intro equal
        apply other
        rw [equal]
        exact represented e
      exact decide_eq_true ⟨Or.inl edge, notLeft, notRight⟩
    · have notRight : w ≠ b e := edge.ne.symm
      have notLeft : w ≠ a e := by
        intro equal
        apply other
        rw [equal]
        exact Sym2.eq_swap.trans (represented e)
      exact decide_eq_true ⟨Or.inr edge, notLeft, notRight⟩
  have starSelected (v : Fin n) (e : E) :
      selected e (starColumn v) (starNegative v) = v ↔ a e = v ∨ b e = v := by
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e (starColumn v) (starNegative v)).1
    · rintro (rfl | rfl)
      · exact leftSelected e (starColumn (a e)) (starNegative (a e)) (decide_eq_true (adjacent e))
      · exact rightSelected e (starColumn (b e)) (starNegative (b e)) (decide_eq_true (adjacent e).symm)
  have otherSelected (e e' : E) (different : e' ≠ e) (v : Fin n) (hv : a e = v ∨ b e = v) :
      selected e' (edgeColumn e) (edgeNegative e) = v ↔ a e' = v ∨ b e' = v := by
    have diffRep : e'.val ≠ e.val := fun equals => different (Subtype.ext equals)
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e' (edgeColumn e) (edgeNegative e)).1
    · rintro (rfl | rfl)
      · exact leftSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e') (by simpa [represented e'] using diffRep))
      · have notReversed : Sym2.mk (b e') (a e') ≠ e.val := by
          rw [Sym2.eq_swap, represented e']
          exact diffRep
        exact rightSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e').symm notReversed)
  let T : Finset (Fin n) := Finset.univ.image chosen
  have starInSpan (v : Fin n) :
      (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) ∈ span := by
    have equals : col v (starColumn v) =
        (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) := by
      funext p
      simp only [colValue v _ (starNegative v), starSelected]
    rw [← equals]
    exact colInSpan v (starColumn v)
  have unitFrom (e : E) (W : Submodule ℚ (Fin n × E → ℚ))
      (hc : ∀ y, col (reject e) y∈W) : Pi.single (reject e, e) (1 : ℚ) ∈ W := by
    let v := reject e
    have equals : col v (starColumn v) - col v (edgeColumn e) = Pi.single (v, e) (1 : ℚ) := by
      funext p
      rcases p with ⟨w, e'⟩
      change col v (starColumn v) (w, e') - col v (edgeColumn e) (w, e') = (Pi.single (v, e) 1 : Fin n × E → ℚ) (w, e')
      simp only [colValue v _ (starNegative v), colValue v _ (edgeNegative e), starSelected]
      by_cases first : w = v
      · subst w
        by_cases second : e' = e
        · subst e'
          have miss : selected e (edgeColumn e) (edgeNegative e) ≠ v := differentEnd e
          simp [rejectEnd e, miss, v]
        · simp only [otherSelected e e' second v (rejectEnd e)]
          simp [second]
      · simp [first]
    rw [← equals]
    exact W.sub_mem (hc _) (hc _)
  have units (e : E) : Pi.single (reject e,e) (1 : ℚ) ∈ span :=
    unitFrom e span (colInSpan _)
  have anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v) := by
    intro v hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    rcases chosenEnd e with first | second
    · exact ⟨e, differentEnd e, Or.inl first.symm⟩
    · exact ⟨e, differentEnd e, Or.inr second.symm⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro u w edge
    let e : E := ⟨Sym2.mk u w, SimpleGraph.mem_edgeFinset.mpr edge⟩
    have inCover : chosen e ∈ T := Finset.mem_image_of_mem chosen (Finset.mem_univ e)
    have pair : Sym2.mk (a e) (b e) = Sym2.mk u w := represented e
    rcases Sym2.eq_iff.mp pair with ⟨left, right⟩ | ⟨left, right⟩
    · rcases chosenEnd e with first | second
      · exact Or.inl ((first.trans left) ▸ inCover)
      · exact Or.inr ((second.trans right) ▸ inCover)
    · rcases chosenEnd e with first | second
      · exact Or.inr ((first.trans left) ▸ inCover)
      · exact Or.inl ((second.trans right) ▸ inCover)
  · have bound := cover531_rank a b reject T R anchor units (fun v _ => starInSpan v)
    have count : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rwa [count] at bound

  · intro Z hz
    let I := (Finset.univ : Finset (Fin φ.leaves)).filter (fun i => label i∈Z)
    let ix : ↥I ≃ Fin I.card := by simpa only [Fintype.card_coe] using Fintype.equivFin (↥I)
    let rows (j : Fin I.card) := R (ix.symm j).val
    let W := Submodule.span ℚ (Set.range rows)
    have selectedIn (i : Fin φ.leaves) (hi : label i∈Z) : R i∈W := by
      let a : ↥I := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      apply Submodule.subset_span
      exact ⟨ix a,by simp [rows,a]⟩
    have otherIn (e : E) : reject e∈Z := by
      have hc : chosen e∈T := Finset.mem_image_of_mem _ (Finset.mem_univ e)
      rcases chosenEnd e with h|h
      · have hr : reject e=b e := by simp [reject,h]
        rw [hr]; exact hz _ _ (adjacent e) (h ▸ hc)
      · have diff : b e≠a e := (adjacent e).ne.symm
        have hr : reject e=a e := by simp [reject,h,diff]
        rw [hr]; exact hz _ _ (adjacent e).symm (h ▸ hc)
    have localUnits (e : E) : Pi.single (reject e,e) (1 : ℚ) ∈ W := by
      apply unitFrom e W
      intro y
      apply Submodule.sum_mem
      intro i _
      split
      next hh => exact selectedIn i (hh.2.symm ▸ otherIn e)
      next => exact W.zero_mem
    have z := cover531_rank a b reject ∅ rows (by simp) localUnits (by simp)
    have cnt : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rw [cnt] at z
    simpa [I,sameLabel] using z
end Formula5176


namespace CoverRigidity4801

abbrev pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
abbrev ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

/-- Two cyclic matchings already force every cover of size 13 to be a whole side. -/
theorem two_matchings (T : Finset (Fin 26)) (card : T.card = 13)
    (first : ∀ i, pt (i+1) ∈ T ∨ ln i ∈ T)
    (third : ∀ i, pt (i+3) ∈ T ∨ ln i ∈ T) :
    (∀ i, pt i ∈ T) ∨ (∀ i, ln i ∈ T) := by
  let pick (i : Fin 13) : T := if h : pt (i+1) ∈ T then ⟨pt (i+1),h⟩ else ⟨ln i,(first i).resolve_left h⟩
  let index : Fin 26 → Fin 13 := fun w => Fin.addCases (motive := fun _ => Fin 13) (fun p : Fin 13 => p-1) (fun l : Fin 13 => l) w
  have idxL (i : Fin 13) : index (ln i) = i := by
    change Fin.addCases (motive := fun _ => Fin 13) (fun p : Fin 13 => p-1) (fun l : Fin 13 => l) (Fin.natAdd 13 i) = i
    rw [Fin.addCases_right]
  have idxP (i : Fin 13) : index (pt (i+1)) = i := by simp [index,pt,Fin.addCases_left]
  have idx (i : Fin 13) : index (pick i).val = i := by
    dsimp only [pick]
    split <;> first | exact idxP i | exact idxL i
  have inj : Function.Injective pick := by
    intro i j h
    simpa only [idx] using congrArg (fun t : T => index t.val) h
  have sur := ((Fintype.bijective_iff_injective_and_card pick).mpr ⟨inj,by simp [card]⟩).surjective
  have apart : ∀ i j, pt i ≠ ln j := by decide
  have excl (i : Fin 13) (inP : pt (i+1) ∈ T) : ln i ∉ T := by
    intro inL
    obtain ⟨j,eq⟩ := sur ⟨ln i,inL⟩
    have v : (pick j).val = ln i := congrArg Subtype.val eq
    have same : j = i := by simpa only [idx,idxL] using congrArg index v
    subst j
    exact apart _ _ (by simpa [pick,inP] using v)
  let P (i : Fin 13) := pt (i+1) ∈ T
  have next (i : Fin 13) (h : P i) : P (i+2) := by
    have v := (third i).resolve_right (excl i h)
    change pt ((i+2)+1) ∈ T
    have plus : ∀ x : Fin 13, (x+2)+1 = x+3 := by decide
    rw [plus]
    exact v
  let step (x : Fin 13) := x+2
  have many (i : Fin 13) (k : ℕ) (h : P i) : P (step^[k] i) := by
    induction k with
    | zero => exact h
    | succ k ih => rw [Function.iterate_succ_apply']; exact next _ ih
  by_cases somePoint : ∃ i, P i
  · obtain ⟨i,h⟩ := somePoint
    have orbit : ∀ a b : Fin 13, ∃ k : Fin 13, step^[k.val] a = b := by decide
    left
    intro j
    obtain ⟨k,hk⟩ := orbit i (j-1)
    have a := many i k.val h
    rw [hk] at a
    have plus : ∀ x : Fin 13, (x-1)+1 = x := by decide
    change pt ((j-1)+1) ∈ T at a
    rwa [plus] at a
  · exact Or.inr (fun i => (first i).resolve_left (fun h => somePoint ⟨i,h⟩))

end CoverRigidity4801

namespace Tree5176

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (u v : Fin 26) : Bool :=
  if u.val < 13 then decide (13 ≤ v.val) && [0,1,3,9].contains ((u.val+26-v.val)%13)
  else decide (v.val < 13) && [0,1,3,9].contains ((v.val+26-u.val)%13)

def plane : SimpleGraph (Fin 26) where
  Adj u v := edge u v = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel plane.Adj := fun u v => inferInstanceAs (Decidable (edge u v = true))

open Formula5176 PEqualNP.MetaComplexity CoverRigidity4801

theorem onlyLeaves {n : ℕ} (φ : DMFormula n) (x y : Fin n → Bool)
    (equal : ∀ i, x (leafLabel φ i)=y (leafLabel φ i)) : φ.eval x = φ.eval y := by
  induction φ with
  | lit v t =>
    have h := equal ⟨0,by change 0<1; decide⟩
    change x v=y v at h
    simp [DMFormula.eval,h]
  | and a b ha hb =>
    have ea := ha (fun i => by simpa only [leafLabel,Fin.addCases_left] using equal (Fin.castAdd b.leaves i))
    have eb := hb (fun i => by simpa only [leafLabel,Fin.addCases_right] using equal (Fin.natAdd a.leaves i))
    simp only [DMFormula.eval,ea,eb]
  | or a b ha hb =>
    have ea := ha (fun i => by simpa only [leafLabel,Fin.addCases_left] using equal (Fin.castAdd b.leaves i))
    have eb := hb (fun i => by simpa only [leafLabel,Fin.addCases_right] using equal (Fin.natAdd a.leaves i))
    simp only [DMFormula.eval,ea,eb]

theorem allUsed (φ : DMFormula 26)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    Function.Surjective (leafLabel φ) := by
  intro t
  by_contra no
  have neighbor : ∀ t : Fin 26, ∃ v : Fin 26, plane.Adj t v := by decide
  obtain ⟨v,e⟩ := neighbor t
  let x := fun i : Fin 26 => decide (i=t ∨ i=v)
  let y := fun i : Fin 26 => decide (i=v)
  have eq := onlyLeaves φ x y (by
    intro i; have hn : leafLabel φ i ≠ t := fun h => no ⟨i,h⟩
    simp [x,y,hn])
  have hx : φ.eval x=true := (spec x).trans (decide_eq_true ⟨t,v,e,by simp [x],by simp [x]⟩)
  have hy : φ.eval y=false := by
    rw [spec]; apply decide_eq_false
    rintro ⟨u,w,ed,hu,hw⟩
    change decide (u=v)=true at hu
    change decide (w=v)=true at hw
    rw [of_decide_eq_true hu,of_decide_eq_true hw] at ed
    exact plane.loopless.irrefl _ ed
  exact Bool.noConfusion (hx.symm.trans (eq.trans hy))

theorem fibreOne {m : ℕ} (f : Fin m → Fin 26) (surj : Function.Surjective f)
    (hm : m≤65) (T : Finset (Fin 26)) (ht : T.card=13)
    (other : 52 ≤ (Finset.univ.filter (fun i => f i∉T)).card) :
    ∀ t∈T, ∃! i, f i=t := by
  let U := Finset.univ.filter (fun i => f i∈T)
  have split : U.card+(Finset.univ.filter (fun i => f i∉T)).card=m := by
    simpa [U] using (Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Fin m))) (fun i => f i∈T))
  let g (i : ↥U) : ↥T := ⟨f i.val,(Finset.mem_filter.mp i.property).2⟩
  have gs : Function.Surjective g := by
    intro t; obtain ⟨i,hi⟩ := surj t.val
    have iu : i∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.symm ▸ t.property⟩
    exact ⟨⟨i,iu⟩,Subtype.ext hi⟩
  have lb := Fintype.card_le_of_surjective g gs
  simp only [Fintype.card_coe] at lb
  have same : Fintype.card (↥U)=Fintype.card (↥T) := by simp only [Fintype.card_coe]; omega
  have gi : Function.Injective g := ((Fintype.bijective_iff_surjective_and_card g).2 ⟨gs,same⟩).injective
  intro t hT
  obtain ⟨i,hi⟩ := surj t
  refine ⟨i,hi,?_⟩
  intro j hj
  let ij (k : Fin m) (h : f k=t) : ↥U := ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.symm ▸ hT⟩⟩
  exact congrArg Subtype.val (gi (a₁:=ij j hj) (a₂:=ij i hi) (Subtype.ext (hj.trans hi.symm)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem wholeSide (φ : DMFormula 26) (hm : φ.leaves≤65)
    (positive : DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    (∀ p : Fin 13, ∃! i, leafLabel φ i=pt p) ∨ (∀ l : Fin 13, ∃! i, leafLabel φ i=ln l) := by
  let P : Finset (Fin 26) := Finset.univ.image pt
  let L : Finset (Fin 26) := Finset.univ.image ln
  have tri : ∀ a b c, ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c a) := by decide +kernel
  have thin : ∀ u v : Fin 26, u≠v → (Finset.univ.filter (fun t : Fin 26 => plane.Adj u t ∧ plane.Adj v t)).card≤1 := by decide +kernel
  have sq (a b c d : Fin 26) (hac : a≠c) (hbd : b≠d) :
      ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
    rintro ⟨hab,hbc,hcd,hda⟩
    exact hbd (Finset.card_le_one.mp (thin a c hac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hbc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hda.symm,hcd⟩))
  obtain ⟨T,cover,cost,colors⟩ := colouredPrice 26 plane tri sq φ positive spec
  have ec : plane.edgeFinset.card=52 := by decide +kernel
  have matchE : ∀ i : Fin 13, plane.Adj (pt i) (ln i) := by decide
  let pick (i : Fin 13) := if pt i∈T then pt i else ln i
  have inside (i : Fin 13) : pick i∈T := by
    by_cases h : pt i∈T
    · simpa [pick,h] using h
    · simpa [pick,h] using (cover _ _ (matchE i)).resolve_left h
  let left (i : Fin 26) := Fin.ofNat 13 i.val
  have inv : ∀ i : Fin 13, left (pt i)=i ∧ left (ln i)=i := by decide
  have back (i : Fin 13) : left (pick i)=i := by dsimp only [pick]; split <;> first | exact (inv i).1 | exact (inv i).2
  have inj : Function.Injective pick := fun i j h => (back i).symm.trans ((congrArg left h).trans (back j))
  have lb := Finset.card_le_card_of_injOn (s:=(Finset.univ : Finset (Fin 13))) (t:=T) pick (fun i _ => inside i) inj.injOn
  simp only [Finset.card_univ,Fintype.card_fin] at lb
  have ht : T.card=13 := by omega
  have eis : ∀ i : Fin 13, plane.Adj (pt (i+1)) (ln i) ∧ plane.Adj (pt (i+3)) (ln i) := by decide
  obtain pure|pure := two_matchings T ht (fun i => cover _ _ (eis i).1) (fun i => cover _ _ (eis i).2)
  · left
    have eq : P=T := Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr (fun i _ => pure i)) (by rw [ht]; decide)
    have neighbors : ∀ u v, plane.Adj u v → u∈P → v∈Pᶜ := by decide
    have other := colors Pᶜ (by simpa only [←eq] using neighbors)
    rw [ec] at other
    exact fun i => fibreOne _ (allUsed φ spec) hm T ht (by simpa [←eq] using other) _ (pure i)
  · right
    have eq : L=T := Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr (fun i _ => pure i)) (by rw [ht]; decide)
    have neighbors : ∀ u v, plane.Adj u v → u∈L → v∈Lᶜ := by decide
    have other := colors Lᶜ (by simpa only [←eq] using neighbors)
    rw [ec] at other
    exact fun i => fibreOne _ (allUsed φ spec) hm T ht (by simpa [←eq] using other) _ (pure i)

end Tree5176

-- The clean-gate cover certificate below is adapted from the project’s L_meta_1602.
namespace Singleton5176

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

theorem singleton_protection : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (z : Fin n → Bool) (S : Set ℕ),
    PEqualNP.TopForm.IsAO2 n C →
    let w := fun k => (C.wires (List.ofFn z)).getD k false
    (∀ i : Fin n, ↑i ∈ S → z i = false) →
    (∀ j g, C.gates[j]? = some g → n+j ∈ S →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∃ i ∈ g.inputs, i ∈ S) ∨ ∀ i ∈ g.inputs, w i = false)) →
    ∀ k ∈ S, w k = false := by
  intro n C z S model _ raw closed
  let w := fun (k : ℕ) => (wiresFrom C.gates (List.ofFn z)).getD k false
  change ∀ k ∈ S, w k = false
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro mem
    by_cases hk : k<n
    · change (wiresFrom _ _).getD k false = false
      rw [getD_wiresFrom_lt _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
      exact raw ⟨k,hk⟩ mem
    by_cases hend : k<n+C.gates.length
    · let j := k-n
      have hj : j<C.gates.length := by dsimp [j]; omega
      have pos : k=n+j := by dsimp [j]; omega
      let g := C.gates[j]
      have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
      have gin : g∈C.gates := List.mem_of_getElem? hit
      have prior (a) (ha : a∈g.inputs) : a<n+j := by
        apply model.2.1 j hj a
        change a∈(C.gates.getD j ⟨.or,[]⟩).inputs
        simpa only [List.getD_eq_getElem _ _ hj] using ha
      have eqv : w k = g.op.eval (g.inputs.map w) := by
        have h := getD_wiresFrom_gate C.gates (List.ofFn z) j hj
        rw [List.length_ofFn] at h
        rw [pos]
        change (wiresFrom C.gates _).getD (n+j) false = _
        refine h.trans ?_
        congr 1
        apply List.map_congr_left
        intro i hi
        exact if_pos (prior i hi)
      have stop := closed j g hit (pos ▸ mem)
      rw [eqv]
      rcases model.1 g gin with tag|tag
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro all
        simp only [GateOp.eval, List.all_eq_true, id_eq] at all
        have accepts (i) (hi : i∈g.inputs) : w i=true := all _ (List.mem_map_of_mem hi)
        rcases stop.2 tag with ⟨i,hi,si⟩|none
        · exact Bool.noConfusion ((ih i (by have := prior i hi; omega) si).symm.trans (accepts i hi))
        · obtain ⟨i,hi⟩ : ∃ i, i∈g.inputs := List.exists_mem_of_ne_nil _ (by
            intro emp; have h := model.2.2 g gin; simp [emp] at h)
          exact Bool.noConfusion ((none i hi).symm.trans (accepts i hi))
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro any
        simp only [GateOp.eval, List.any_eq_true, id_eq] at any
        obtain ⟨t,ht,vt⟩ := any
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
        exact Bool.noConfusion ((ih i (by have := prior i hi; omega) (stop.1 tag i hi)).symm.trans vt)
    · apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
      omega

end Singleton5176
namespace Occurrence5176
open PEqualNP.MetaComplexity

/-- Number of occurrences of the selected raw input in the unfolded circuit. -/
def copies {n} (t : Fin n) : DMFormula n → Nat
  | .lit v _ => if v=t then 1 else 0
  | .and a b | .or a b => copies t a + copies t b

/-- The linear trace for one raw input on the evaluation at `x`. -/
def trace {n} (t : Fin n) (x : Fin n → Bool) : DMFormula n → Bool
  | .lit v _ => decide (v=t)
  | .and a b => (trace t x a && b.eval x) || (a.eval x && trace t x b)
  | .or a b => trace t x a || trace t x b

theorem unchanged {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ=0) : φ.eval x = φ.eval y := by
  induction φ with
  | lit v c =>
    have hv : v≠t := by rintro rfl; simp [copies] at h
    simp only [DMFormula.eval,same v hv]
  | and a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]
  | or a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]

theorem trace_of_unique {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ≤1)
    (off : φ.eval x=false) (on_ : φ.eval y=true) : trace t x φ=true := by
  induction φ with
  | lit v c =>
    by_cases hv : v=t
    · simp [trace,hv]
    · have z := unchanged t x y same (.lit v c) (by simp [copies,hv]); simp_all
  | and a b ha hb =>
    change copies t a+copies t b≤1 at h
    have yes := Bool.and_eq_true_iff.mp on_
    change (a.eval x && b.eval x)=false at off
    change ((trace t x a && b.eval x) || (a.eval x && trace t x b))=true
    by_cases nz : copies t a=0
    · have at_ := (unchanged t x y same a nz).trans yes.1
      have bf : b.eval x=false := by simpa [at_] using off
      simp [at_,hb (by omega) bf yes.2]
    · have bt := (unchanged t x y same b (by omega)).trans yes.2
      have af : a.eval x=false := by simpa [bt] using off
      simp [bt,ha (by omega) af yes.1]
  | or a b ha hb =>
    change copies t a+copies t b≤1 at h
    have no := Bool.or_eq_false_iff.mp off
    change (trace t x a || trace t x b)=true
    cases h1 : a.eval y with
    | true => simp [ha (by omega) no.1 h1]
    | false =>
      have h2 : b.eval y=true := by simpa [DMFormula.eval,h1] using on_
      simp [hb (by omega) no.2 h2]

end Occurrence5176
namespace Occurrence5176
open Formula5176 PEqualNP.MetaComplexity

private theorem hasLeaf {n} (t : Fin n) (φ : DMFormula n) (h : 0<copies t φ) :
    ∃ i, leafLabel φ i=t := by
  induction φ with
  | lit v c =>
    refine ⟨(⟨0,by decide⟩ : Fin 1),?_⟩
    change v=t
    by_contra hne
    simp [copies,hne] at h
  | and a b ha hb | or a b ha hb =>
    change 0<copies t a+copies t b at h
    by_cases z : 0<copies t a
    · obtain ⟨i,hi⟩ := ha z
      exact ⟨Fin.castAdd _ i,by simpa [leafLabel] using hi⟩
    · obtain ⟨i,hi⟩ := hb (by omega)
      exact ⟨Fin.natAdd _ i,by simpa [leafLabel] using hi⟩

theorem copies_unique {n} (t : Fin n) (φ : DMFormula n)
    (one : ∀ i j, leafLabel φ i=t → leafLabel φ j=t → i=j) : copies t φ≤1 := by
  induction φ with
  | lit v b => by_cases h : v=t <;> simp [copies,h]
  | and a b ha hb | or a b ha hb =>
    change copies t a+copies t b≤1
    have la := ha (by intro i j hi hj; have z := one (Fin.castAdd b.leaves i) (Fin.castAdd b.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj); exact Fin.ext (congrArg (fun v : Fin (a.leaves+b.leaves) => v.val) z))
    have lb := hb (by
      intro i j hi hj
      have z := one (Fin.natAdd a.leaves i) (Fin.natAdd a.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj)
      have zz := congrArg Fin.val z
      exact Fin.ext (Nat.add_left_cancel zz))
    by_contra big
    obtain ⟨i,hi⟩ := hasLeaf t a (by omega)
    obtain ⟨j,hj⟩ := hasLeaf t b (by omega)
    have z := one (Fin.castAdd b.leaves i) (Fin.natAdd a.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj)
    have zz := congrArg Fin.val z
    change i.val = a.leaves+j.val at zz
    omega

end Occurrence5176
namespace Wires5176
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Singleton5176 Occurrence5176

abbrev F := DMFormula 26
abbrev raw0 : F := .lit 0 true

def tree (C : Circuit) (k : Nat) : F :=
  if h : k<26 then .lit ⟨k,h⟩ true else
    let g := C.gates.getD (k-26) ⟨.or,[]⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if ha : a<k then
      if hb : b<k then
        match g.op with
        | .and => .and (tree C a) (tree C b)
        | _ => .or (tree C a) (tree C b)
      else raw0
    else raw0
termination_by k

private theorem rawTree (C : Circuit) (i : Fin 26) : tree C i.val = .lit i true := by
  rw [tree]
  simp only [i.isLt, ↓reduceDIte]

private theorem childPrior {C : Circuit} (ao : IsAO2 26 C) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) {i : Nat} (mem : i∈g.inputs) : i<26+j := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  apply ao.2.1 j hj i
  change i∈(C.gates.getD j ⟨.or,[]⟩).inputs
  rw [List.getD_eq_getElem _ _ hj,hg]
  exact mem

private theorem atGate {C : Circuit} (ao : IsAO2 26 C) {j a b : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) (ins : g.inputs=[a,b]) :
    (g.op=.and → tree C (26+j)=.and (tree C a) (tree C b)) ∧
    (g.op=.or → tree C (26+j)=.or (tree C a) (tree C b)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have ga : a<26+j := childPrior ao hit (by simp [ins])
  have gb : b<26+j := childPrior ao hit (by simp [ins])
  have hget : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,hg]
  constructor <;> intro op <;> rw [tree] <;> simp [hit,ins,op,ga,gb]

abbrev Positive (φ : F) := DMFormula.rec (motive:=fun _ : F => Prop)
    (fun _ c => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

abbrev wire (C : Circuit) (x : Fin 26 → Bool) (k : Nat) := (C.wires (List.ofFn x)).getD k false

private theorem rawValue (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) : wire C x i.val=x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i.val false=_
  rw [getD_wiresFrom_lt _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]

private theorem gateValue {C : Circuit} (ao : IsAO2 26 C) (x : Fin 26 → Bool) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) : wire C x (26+j)=g.op.eval (g.inputs.map (wire C x)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn,hg] at h
  refine h.trans ?_
  congr 1
  apply List.map_congr_left
  intro i hi
  exact if_pos (childPrior ao hit hi)

theorem semantics {C : Circuit} (ao : IsAO2 26 C) (k : Nat) (valid : k<26+C.size) :
    Positive (tree C k) ∧ ∀ x, (tree C k).eval x=wire C x k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases raw : k<26
    · let i : Fin 26 := ⟨k,raw⟩
      change Positive (tree C i.val) ∧ _
      rw [rawTree]
      exact ⟨rfl,fun x => by simpa [DMFormula.eval] using (rawValue C x i).symm⟩
    let j := k-26
    have hj : j<C.gates.length := by change k<26+C.gates.length at valid; dsimp [j]; omega
    let g := C.gates[j]
    have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    have gin := List.mem_of_getElem? hit
    have pos : k=26+j := by dsimp [j]; omega
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    obtain ⟨pa,ea⟩ := ih a (by omega) (by omega)
    obtain ⟨pb,eb⟩ := ih b (by omega) (by omega)
    rw [pos]
    rcases ao.1 g gin with op|op
    · rw [(atGate ao hit ins).1 op]
      exact ⟨⟨pa,pb⟩,fun x => by rw [gateValue ao x hit]; simp [op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩
    · rw [(atGate ao hit ins).2 op]
      exact ⟨⟨pa,pb⟩,fun x => by rw [gateValue ao x hit]; simp [op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩

end Wires5176
namespace Wires5176
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Singleton5176 Occurrence5176 Formula5176 CoverRigidity4801

private abbrev oriented (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
private abbrev accepts (x : Fin 26→Bool) := ∃ p l : Fin 13, oriented p l ∧ x (pt p)=true ∧ x (ln l)=true
private abbrev bits (m : Nat) (i : Fin 26) := m.testBit i.val

private theorem graphAccept (x : Fin 26→Bool) : accepts x ↔ ∃ u v, Tree5176.plane.Adj u v ∧ x u=true ∧ x v=true := by
  have forward : ∀ p l, oriented p l → Tree5176.plane.Adj (pt p) (ln l) := by decide
  have back : ∀ u v : Fin 26, Tree5176.plane.Adj u v → ∃ p l, oriented p l ∧
      ((u=pt p ∧ v=ln l) ∨ (v=pt p ∧ u=ln l)) := by decide +kernel
  constructor
  · rintro ⟨p,l,h,hp,hl⟩; exact ⟨_,_,forward p l h,hp,hl⟩
  · rintro ⟨u,v,h,hu,hv⟩
    obtain ⟨p,l,e,s|s⟩ := back u v h
    · exact ⟨p,l,e,s.1 ▸ hu,s.2 ▸ hv⟩
    · exact ⟨p,l,e,s.1 ▸ hv,s.2 ▸ hu⟩


open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem childCopies {C : Circuit} (ao : IsAO2 26 C) (t : Fin 26) (j u : Nat)
    (hj : j<C.gates.length) (hu : u∈(gateAt C j).inputs) :
    copies t (tree C u) ≤ copies t (tree C (26+j)) := by
  let g := C.gates[j]
  have hit : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  have ga : gateAt C j = g := List.getD_eq_getElem _ _ hj
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hit))
  rw [ga,ins] at hu
  have hab : u=a ∨ u=b := by simpa using hu
  rcases ao.1 g (List.mem_of_getElem? hit) with op|op
  · rw [(atGate ao hit ins).1 op]; simp only [copies]; rcases hab with rfl|rfl <;> omega
  · rw [(atGate ao hit ins).2 op]; simp only [copies]; rcases hab with rfl|rfl <;> omega

theorem coneCopies {C : Circuit} (ao : IsAO2 26 C) (t : Fin 26) (i j : Nat)
    (hj : j<C.gates.length) (h : InCone 26 C i j) :
    copies t (tree C (26+i)) ≤ copies t (tree C (26+j)) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hw,hlo,hup,eq|below⟩ := (PEqualNP.Outside.L_meta_18611.Flat.inCone_iff 26 C i j hj).mp h
    · have e : 26+i=w := by omega
      rw [e]; exact childCopies ao t j w hj hw
    · have e : 26+(w-26)=w := by omega
      have cl := ih (w-26) (by omega) (by omega) below
      rw [e] at cl
      exact cl.trans (childCopies ao t j w hj hw)

theorem markedCopies {C : Circuit} (ao : IsAO2 26 C) (k : Nat)
    (op : (gateAt C k).op = .and)
    (live : 26+k=C.output ∨ InCone 26 C k (C.output-26))
    (pair : gateVal 26 C k (pairInput (0 : Fin 26) 13)=true)
    (quiet : ∀ b : Fin 2, wire C (pairInput (0 : Fin 26) 0) (opnd C k b)=false ∧
      wire C (pairInput (13 : Fin 26) 13) (opnd C k b)=false)
    (valid : C.output<26+C.size) : ∀ t ∈ ([0,13] : List (Fin 26)), 2 ≤ copies t (tree C C.output) := by
  have hk : k<C.gates.length := by
    by_contra h
    change (C.gates.getD k ⟨.or,[]⟩).op=.and at op
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at op
    cases op
  let g := C.gates[k]
  have hit : C.gates[k]?=some g := List.getElem?_eq_getElem hk
  have ga : gateAt C k=g := List.getD_eq_getElem _ _ hk
  have gand : g.op=.and := ga ▸ op
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hit))
  have ea : opnd C k 0 = a := by simp [opnd,ga,ins,List.getD_eq_getElem?_getD]
  have eb : opnd C k 1 = b := by simp [opnd,ga,ins,List.getD_eq_getElem?_getD]
  let xy := pairInput (0 : Fin 26) 13
  have both : wire C xy a=true ∧ wire C xy b=true := by
    change wire C xy (26+k)=true at pair
    rw [gateValue ao xy hit] at pair
    simpa [gand,ins,GateOp.eval] using pair
  intro t ht
  suffices hh : 2 ≤ copies t (tree C (26+k)) by
    rcases live with e|co
    · rwa [←e]
    · have gte : 26≤C.output := by
        by_contra! raw
        have z : C.output-26=0 := by omega
        rw [z] at co
        have h0 : 0<C.gates.length := by omega
        obtain ⟨w,_,hw1,hw2,_⟩ := (PEqualNP.Outside.L_meta_18611.Flat.inCone_iff 26 C k 0 h0).mp co
        omega
      have idx : C.output-26<C.gates.length := by change C.output<26+C.gates.length at valid; omega
      have e : 26+(C.output-26)=C.output := by omega
      have z := coneCopies ao t k (C.output-26) idx co
      rw [e] at z
      exact hh.trans z
  rw [(atGate ao hit ins).1 gand]
  simp only [copies]
  rcases (show t=0 ∨ t=13 by simpa using ht) with rfl|rfl
  · have hdiff : ∀ i : Fin 26, i≠0 → (pairInput (13 : Fin 26) 13) i=xy i := by decide
    have pos (w : Nat) (hw:w<26+k) (on:wire C xy w=true) (off:wire C (pairInput (13:Fin 26) 13) w=false) : 0<copies 0 (tree C w) := by
      by_contra! zz
      have eq := Occurrence5176.unchanged (0:Fin 26) _ _ hdiff (tree C w) (by omega)
      have val := (semantics ao w (by change w<26+C.gates.length;omega)).2
      rw [val,val,off,on] at eq; cases eq
    have ha := pos a (childPrior ao hit (by simp [ins])) both.1 (ea ▸ (quiet 0).2)
    have hb := pos b (childPrior ao hit (by simp [ins])) both.2 (eb ▸ (quiet 1).2)
    omega
  · have hdiff : ∀ i : Fin 26, i≠13 → (pairInput (0 : Fin 26) 0) i=xy i := by decide
    have pos (w : Nat) (hw:w<26+k) (on:wire C xy w=true) (off:wire C (pairInput (0:Fin 26) 0) w=false) : 0<copies 13 (tree C w) := by
      by_contra! zz
      have eq := Occurrence5176.unchanged (13:Fin 26) _ _ hdiff (tree C w) (by omega)
      have val := (semantics ao w (by change w<26+C.gates.length;omega)).2
      rw [val,val,off,on] at eq; cases eq
    have ha := pos a (childPrior ao hit (by simp [ins])) both.1 (ea ▸ (quiet 0).1)
    have hb := pos b (childPrior ao hit (by simp [ins])) both.2 (eb ▸ (quiet 1).1)
    omega


theorem markedLower {C : Circuit} (ao : IsAO2 26 C) (spec : ∀ x : Fin 26 → Bool,
    C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
      x (pt p)=true ∧ x (ln l)=true)
    {k : Nat} (op : (gateAt C k).op = .and)
    (live : 26+k=C.output ∨ InCone 26 C k (C.output-26))
    (pair : gateVal 26 C k (pairInput (0 : Fin 26) 13)=true)
    (quiet : ∀ b : Fin 2, wire C (pairInput (0 : Fin 26) 0) (opnd C k b)=false ∧
      wire C (pairInput (13 : Fin 26) 13) (opnd C k b)=false) : 66 ≤ (tree C C.output).leaves := by
  by_contra! small
  have inc : ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ oriented p l := by decide +kernel
  have spec' (x : Fin 26→Bool) : wire C x C.output=true ↔ accepts x :=
    (spec x).trans (exists_congr fun p => exists_congr fun l => and_congr_left fun _ => inc p l)
  have flag : wire C (bits 8193) C.output=true := (spec' _).2 ⟨0,0,Or.inl rfl,by decide,by decide⟩
  have valid : C.output<26+C.size := by
    by_contra h
    change (wiresFrom C.gates (List.ofFn (bits 8193))).getD C.output false=true at flag
    rw [List.getD_eq_default] at flag
    · contradiction
    · rw [length_wiresFrom,List.length_ofFn]; exact Nat.le_of_not_gt h
  obtain ⟨hp,he⟩ := semantics ao C.output valid
  have gr (x : Fin 26→Bool) : (tree C C.output).eval x=decide (∃ u v, Tree5176.plane.Adj u v ∧ x u=true ∧ x v=true) := by
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (spec' x).trans (graphAccept x)
  have many := markedCopies ao k op live pair quiet valid
  obtain side|side := Tree5176.wholeSide _ (by omega) hp gr
  · have one := side 0
    have upper := copies_unique (pt 0) _ (fun i j hi hj => one.unique hi hj)
    have lower := many 0 (by simp)
    change copies 0 (tree C C.output) ≤ 1 at upper
    omega
  · have one := side 0
    have upper := copies_unique (ln 0) _ (fun i j hi hj => one.unique hi hj)
    have lower := many 13 (by simp)
    change copies 13 (tree C C.output) ≤ 1 at upper
    omega
end Wires5176

namespace Tree5176
open PEqualNP.MetaComplexity Formula5176 CoverRigidity4801
theorem planeLeaves (φ : DMFormula 26)
    (positive : DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    65 ≤ φ.leaves := by
  let P : Finset (Fin 26) := Finset.univ.image pt
  let L : Finset (Fin 26) := Finset.univ.image ln
  have tri : ∀ a b c, ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c a) := by decide +kernel
  have thin : ∀ u v : Fin 26, u≠v → (Finset.univ.filter (fun t : Fin 26 => plane.Adj u t ∧ plane.Adj v t)).card≤1 := by decide +kernel
  have sq (a b c d : Fin 26) (hac : a≠c) (hbd : b≠d) :
      ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
    rintro ⟨hab,hbc,hcd,hda⟩
    exact hbd (Finset.card_le_one.mp (thin a c hac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hbc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hda.symm,hcd⟩))
  obtain ⟨T,cover,cost,colors⟩ := colouredPrice 26 plane tri sq φ positive spec
  have ec : plane.edgeFinset.card=52 := by decide +kernel
  have matchE : ∀ i : Fin 13, plane.Adj (pt i) (ln i) := by decide
  let pick (i : Fin 13) := if pt i∈T then pt i else ln i
  have inside (i : Fin 13) : pick i∈T := by
    by_cases h : pt i∈T
    · simpa [pick,h] using h
    · simpa [pick,h] using (cover _ _ (matchE i)).resolve_left h
  let left (i : Fin 26) := Fin.ofNat 13 i.val
  have inv : ∀ i : Fin 13, left (pt i)=i ∧ left (ln i)=i := by decide
  have back (i : Fin 13) : left (pick i)=i := by dsimp only [pick]; split <;> first | exact (inv i).1 | exact (inv i).2
  have inj : Function.Injective pick := fun i j h => (back i).symm.trans ((congrArg left h).trans (back j))
  have lb := Finset.card_le_card_of_injOn (s:=(Finset.univ : Finset (Fin 13))) (t:=T) pick (fun i _ => inside i) inj.injOn
  simp only [Finset.card_univ,Fintype.card_fin] at lb
  omega

inductive Cut where
  | raw (i : Fin 26)
  | port
  | meet (a b : Cut)
  | join (a b : Cut)

def Cut.eval (t : Cut) (x : Fin 26 → Bool) (h : Bool) : Bool :=
  match t with
  | .raw i => x i
  | .port => h
  | .meet a b => a.eval x h && b.eval x h
  | .join a b => a.eval x h || b.eval x h

def Cut.rawCount : Cut → ℕ
  | .raw _ => 1
  | .port => 0
  | .meet a b | .join a b => a.rawCount+b.rawCount

theorem Cut.mono (t : Cut) {x y : Fin 26 → Bool} {h k : Bool}
    (hin : ∀ i, x i=true → y i=true) (port : h=true → k=true) :
    t.eval x h=true → t.eval y k=true := by
  induction t with
  | raw i => exact hin i
  | port => exact port
  | meet a b ha hb =>
    simp only [Cut.eval,Bool.and_eq_true] at *
    exact fun h => ⟨ha h.1,hb h.2⟩
  | join a b ha hb =>
    simp only [Cut.eval,Bool.or_eq_true] at *
    exact fun h => h.elim (fun u => Or.inl (ha u)) (fun u => Or.inr (hb u))

abbrev Positive (φ : DMFormula 26) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
    (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

theorem Cut.zeroFormula (t : Cut) :
    (∀ x, t.eval x false=false) ∨
    (∃ φ : DMFormula 26, Positive φ ∧ φ.leaves ≤ t.rawCount ∧ ∀ x, φ.eval x=t.eval x false) := by
  induction t with
  | raw i => exact .inr ⟨.lit i true,rfl,by rfl,fun _ => rfl⟩
  | port => exact .inl (fun _ => rfl)
  | meet a b ha hb =>
    rcases ha with za | ⟨f,pf,cf,ef⟩
    · exact .inl (fun x => by simp [Cut.eval,za x])
    rcases hb with zb | ⟨g,pg,cg,eg⟩
    · exact .inl (fun x => by simp [Cut.eval,zb x])
    exact .inr ⟨.and f g,⟨pf,pg⟩,Nat.add_le_add cf cg,fun x => by simp only [DMFormula.eval,Cut.eval,ef,eg]⟩
  | join a b ha hb =>
    rcases ha with za | ⟨f,pf,cf,ef⟩ <;> rcases hb with zb | ⟨g,pg,cg,eg⟩
    · exact .inl (fun x => by simp [Cut.eval,za x,zb x])
    · exact .inr ⟨g,pg,by change _ ≤ a.rawCount+b.rawCount; omega,fun x => by simp [Cut.eval,za x,eg]⟩
    · exact .inr ⟨f,pf,by change _ ≤ a.rawCount+b.rawCount; omega,fun x => by simp [Cut.eval,zb x,ef]⟩
    · exact .inr ⟨.or f g,⟨pf,pg⟩,Nat.add_le_add cf cg,fun x => by simp only [DMFormula.eval,Cut.eval,ef,eg]⟩

def row (a b : Fin 26) (i : Fin 26) : Bool := decide (i=a ∨ i=b)

def flagFun (x : Fin 26 → Bool) : Bool := decide (∃ i j, plane.Adj i j ∧ x i=true ∧ x j=true)

inductive Cluster where
  | raw (i : Fin 26)
  | port (j : Nat)
  | bin (j : Nat) (isAnd : Bool) (l r : Cluster)

def Cluster.cut : Cluster → Cut
  | .raw i => .raw i
  | .port _ => .port
  | .bin _ true l r => .meet l.cut r.cut
  | .bin _ false l r => .join l.cut r.cut

def Cluster.tags : Cluster → List Nat
  | .raw _ | .port _ => []
  | .bin j _ l r => j::(l.tags++r.tags)
def Cluster.pins : Cluster → List Nat
  | .raw _ => []
  | .port j => [j]
  | .bin _ _ l r => l.pins++r.pins

def Cluster.ev (x : Fin 26→Bool) (v : Nat→Bool) : Cluster → Bool
  | .raw i => x i
  | .port j => v j
  | .bin _ true l r => l.ev x v && r.ev x v
  | .bin _ false l r => l.ev x v || r.ev x v

theorem Cluster.eraseEval (t : Cluster) (x : Fin 26→Bool) :
    t.cut.eval x false=t.ev x (fun _ => false) := by
  induction t with
  | raw i => rfl
  | port j => rfl
  | bin j q l r il ir => cases q <;> simp only [cut,Cut.eval,ev,il,ir]

theorem Cluster.ordered (t : Cluster) {x y : Fin 26→Bool} {h k : Nat→Bool}
    (inputs : ∀ i, x i=true → y i=true) (ps : ∀ j∈t.pins, h j=true → k j=true) :
    t.ev x h=true → t.ev y k=true := by
  induction t with
  | raw i => exact inputs i
  | port j => exact ps j (by simp [pins])
  | bin j q l r il ir =>
    have hl := il (fun i hi => ps i (by simp [pins,hi]))
    have hr := ir (fun i hi => ps i (by simp [pins,hi]))
    cases q
    · simp only [ev,Bool.or_eq_true]
      exact fun z => z.elim (fun a => Or.inl (hl a)) (fun b => Or.inr (hr b))
    · simp only [ev,Bool.and_eq_true]
      exact fun z => ⟨hl z.1,hr z.2⟩

theorem Cluster.balance (t : Cluster) : t.cut.rawCount+t.pins.length=t.tags.length+1 := by
  induction t with
  | raw i => rfl
  | port j => rfl
  | bin j q l r il ir =>
    cases q <;> simp only [cut,Cut.rawCount,pins,tags,List.length_append,List.length_cons] <;> omega

abbrev Row := Fin 26 → Bool
def Price (f : Row → Bool) (m : Nat) : Prop :=
  (∀ x, f x=false) ∨
    ∃ φ : DMFormula 26, Positive φ ∧ φ.leaves ≤ m ∧ ∀ x, φ.eval x=f x

def restore (f : Row→Bool) (u v : Nat→Fin 26) : List Nat → Row → Bool
  | [],x => f x
  | j::js,x => restore f u v js x || (x (u j) && x (v j))

theorem restoreIff (f : Row→Bool) (u v : Nat→Fin 26) (js : List Nat) (x : Row) :
    restore f u v js x=true ↔ f x=true ∨ ∃ j∈js, x (u j)=true ∧ x (v j)=true := by
  induction js with
  | nil => simp [restore]
  | cons j js ih =>
    simp only [restore,Bool.or_eq_true,Bool.and_eq_true,ih,List.mem_cons]
    aesop

theorem restorePrice (f : Row→Bool) (u v : Nat→Fin 26) (js : List Nat)
    (m : Nat) (hf : Price f m) : Price (restore f u v js) (m+2*js.length) := by
  induction js with
  | nil => simpa [restore] using hf
  | cons j js ih =>
    let e : DMFormula 26 := .and (.lit (u j) true) (.lit (v j) true)
    have p : Positive e := ⟨rfl,rfl⟩
    rcases ih with hz | ⟨g,pg,cg,eg⟩
    · exact .inr ⟨e,p,by change 2 ≤ m+2*(js.length+1); omega,fun x => by simp [restore,hz,e,DMFormula.eval]⟩
    · refine .inr ⟨.or g e,⟨pg,p⟩,?_,?_⟩
      · change g.leaves+2 ≤ m+2*(js.length+1)
        omega
      · intro x
        change (g.eval x || (x (u j) && x (v j)))=_
        rw [eg]
        rfl

/-- Each visible auxiliary wire has a designated flag containing its entire
positive incidence-flag support. There is no restriction on its false-input support. -/
theorem manyFlagRaw (t : Cluster) (H : Nat → Row → Bool) (u v : Nat→Fin 26)
    (spec : ∀ x, t.ev x (fun j => H j x)=flagFun x)
    (edges : ∀ j∈t.pins, plane.Adj (u j) (v j))
    (single : ∀ j∈t.pins, ∀ a b, plane.Adj a b → H j (row a b)=true →
      (a=u j ∧ b=v j) ∨ (a=v j ∧ b=u j)) :
    65 ≤ t.cut.rawCount + 2*t.pins.toFinset.card := by
  classical
  let js := t.pins.toFinset.toList
  have jm (j : Nat) : j∈js ↔ j∈t.pins := by simp [js]
  let f : Row→Bool := fun x => t.cut.eval x false
  have recover (x : Row) : restore f u v js x = flagFun x := by
    apply Bool.eq_iff_iff.mpr
    rw [restoreIff]
    change _ ↔ decide (∃ i j, plane.Adj i j ∧ x i=true ∧ x j=true)=true
    rw [decide_eq_true_eq]
    constructor
    · rintro (hx|⟨j,hj,xu,xv⟩)
      · change t.cut.eval x false=true at hx
        rw [t.eraseEval] at hx
        have hx' := t.ordered (x:=x) (y:=x) (k:=fun j => H j x) (fun _ hi => hi) (by simp) hx
        simpa only [spec,flagFun,decide_eq_true_eq] using hx'
      · exact ⟨_,_,edges j ((jm j).mp hj),xu,xv⟩
    · rintro ⟨a,b,ab,xa,xb⟩
      by_cases visible : ∃ j∈t.pins, H j (row a b)=true
      · obtain ⟨j,hj,on⟩ := visible
        right
        refine ⟨j,(jm j).mpr hj,?_⟩
        rcases single j hj a b ab on with ⟨aa,bb⟩|⟨aa,bb⟩
        · exact ⟨aa ▸ xa,bb ▸ xb⟩
        · exact ⟨bb ▸ xb,aa ▸ xa⟩
      · left
        have good : flagFun (row a b)=true := by
          apply decide_eq_true
          exact ⟨a,b,ab,by simp [row],by simp [row]⟩
        have atRow := (spec (row a b)).trans good
        change t.cut.eval x false=true
        rw [t.eraseEval]
        apply t.ordered (x:=row a b) (h:=fun j => H j (row a b)) _ _ atRow
        · intro i hi
          rcases (of_decide_eq_true hi : i=a ∨ i=b) with rfl|rfl
          · exact xa
          · exact xb
        · exact fun j hj h => False.elim (visible ⟨j,hj,h⟩)
  have bound := restorePrice f u v js t.cut.rawCount t.cut.zeroFormula
  have len : js.length=t.pins.toFinset.card := by simp [js]
  rcases bound with z | ⟨φ,p,c,e⟩
  · have hpos : flagFun (row 0 13)=true := by
      apply decide_eq_true
      exact ⟨0,13,by decide,by simp [row],by simp [row]⟩
    have bad := z (row 0 13)
    rw [recover,hpos] at bad
    contradiction
  · have lb := planeLeaves φ p (fun x => (e x).trans (recover x))
    omega

theorem multiPortCost (t : Cluster) (s : Nat) (small : s≤64)
    (H : Nat → Row → Bool) (u v : Nat→Fin 26)
    (spec : ∀ x, t.ev x (fun j => H j x)=flagFun x)
    (edges : ∀ j∈t.pins, plane.Adj (u j) (v j))
    (single : ∀ j∈t.pins, ∀ a b, plane.Adj a b → H j (row a b)=true →
      (a=u j ∧ b=v j) ∨ (a=v j ∧ b=u j))
    (fresh : t.tags.Nodup) (sep : Disjoint t.tags.toFinset t.pins.toFinset)
    (valid : t.tags.toFinset ∪ t.pins.toFinset ⊆ Finset.range s) :
    t.pins.length ≤ t.pins.toFinset.card := by
  have lower := manyFlagRaw t H u v spec edges single
  have cap := Finset.card_le_card valid
  rw [Finset.card_union_of_disjoint sep,List.toFinset_card_of_nodup fresh,Finset.card_range] at cap
  have balance := t.balance
  omega


def times (j : Nat) : List Nat → Nat
  | [] => 0
  | a::as => (if j=a then 1 else 0)+times j as

theorem times_append (j : Nat) (a b : List Nat) : times j (a++b)=times j a+times j b := by
  induction a with
  | nil => simp [times]
  | cons c a ih => simp [times,ih,Nat.add_assoc]

theorem times_zero_iff (j : Nat) (a : List Nat) : times j a=0 ↔ j∉a := by
  induction a with
  | nil => simp [times]
  | cons c a ih => by_cases h : j=c <;> simp [times,h,ih]

theorem uniqueOfTimes (a : List Nat) (h : ∀ j, times j a≤1) : a.Nodup := by
  induction a with
  | nil => simp
  | cons c a ih =>
    have h0 := h c
    simp [times] at h0
    apply List.nodup_cons.mpr
    refine ⟨(times_zero_iff c a).mp (by omega),ih ?_⟩
    intro j
    have hj := h j
    change (if j=c then 1 else 0)+times j a≤1 at hj
    omega

theorem timesOfUnique (a : List Nat) (h : a.Nodup) (j : Nat) : times j a≤1 := by
  induction a with
  | nil => simp [times]
  | cons c a ih =>
    obtain ⟨hc,ha⟩ := List.nodup_cons.mp h
    by_cases eq : j=c
    · subst j
      simp [times,(times_zero_iff c a).mpr hc]
    · simpa [times,eq] using ih ha

theorem uniqueOfCard (a : List Nat) (h : a.length≤a.toFinset.card) : a.Nodup := by
  induction a with
  | nil => simp
  | cons c a ih =>
    have base : a.toFinset.card≤a.length := List.toFinset_card_le a
    apply List.nodup_cons.mpr
    by_cases mem : c∈a
    · have eq : (c::a).toFinset=a.toFinset := by ext k; simp; aesop
      rw [eq,List.length_cons] at h
      omega
    · refine ⟨mem,ih ?_⟩
      simpa [mem] using h

def Cluster.orderedIndices : Cluster → Prop
  | .raw _ | .port _ => True
  | .bin j _ l r => (∀ k∈l.tags, k<j) ∧ (∀ k∈r.tags, k<j) ∧ l.orderedIndices ∧ r.orderedIndices

def Cluster.prune (S : Finset Nat) : Cluster → Cluster
  | .raw i => .raw i
  | .port j => .port j
  | .bin j q l r => if j∈S then .port j else .bin j q (l.prune S) (r.prune S)

theorem Cluster.prunedCounts (t : Cluster) (S : Finset Nat) (k : Nat) :
    times k (t.prune S).tags ≤ times k t.tags ∧ (k∈S → times k (t.prune S).tags=0) := by
  induction t with
  | raw i => simp [prune,tags,times]
  | port j => simp [prune,tags,times]
  | bin j q l r il ir =>
    by_cases hit : j∈S
    · simp [prune,hit,tags,times]
    · simp only [prune,if_neg hit,tags,times,times_append]
      constructor
      · omega
      · intro ks
        have ne : k≠j := fun eq => hit (eq ▸ ks)
        simp [ne,il.2 ks,ir.2 ks]

theorem Cluster.prunedPins (t : Cluster) (S : Finset Nat) (empty : t.pins=[]) :
    ∀ k∈(t.prune S).pins, k∈S ∧ k∈t.tags := by
  induction t with
  | raw i => simp [prune,pins]
  | port j => simp [pins] at empty
  | bin j q l r il ir =>
    have halves : l.pins=[] ∧ r.pins=[] := by simpa [pins] using empty
    by_cases hit : j∈S
    · simp [prune,hit,pins,tags]
    · intro k hk
      rcases (show k∈(l.prune S).pins ∨ k∈(r.prune S).pins by simpa [prune,hit,pins] using hk) with left|right
      · obtain ⟨ks,kl⟩ := il halves.1 k left
        exact ⟨ks,by simp [tags,kl]⟩
      · obtain ⟨ks,kr⟩ := ir halves.2 k right
        exact ⟨ks,by simp [tags,kr]⟩

theorem Cluster.maxCopies (t : Cluster) (S : Finset Nat) (k : Nat) (ks : k∈S)
    (maximal : ∀ j∈S, j≤k) (desc : t.orderedIndices) :
    times k t.tags ≤ times k (t.prune S).pins := by
  induction t with
  | raw i => simp [tags,pins,prune,times]
  | port j => simp [tags,pins,prune,times]
  | bin j q l r il ir =>
    obtain ⟨dl,dr,cl,cr⟩ := desc
    by_cases hit : j∈S
    · have le := maximal j hit
      have left : k∉l.tags := fun hm => (Nat.not_lt_of_ge le) (dl k hm)
      have right : k∉r.tags := fun hm => (Nat.not_lt_of_ge le) (dr k hm)
      simp [prune,hit,tags,pins,times,times_append,(times_zero_iff _ _).mpr left,(times_zero_iff _ _).mpr right]
    · have ne : k≠j := fun h => hit (h ▸ ks)
      simpa [prune,hit,tags,pins,times,times_append,ne] using Nat.add_le_add (il cl) (ir cr)

/-- A full output unfolding which repeats a gate has a valid nonempty cut at
the repeated labels. The cut has a repeated boundary wire. -/
theorem Cluster.maxCut (t : Cluster) (desc : t.orderedIndices) (empty : t.pins=[])
    (repeatLabel : ¬t.tags.Nodup) :
    ∃ S : Finset Nat, (∀ j, j∈S ↔ j∈t.tags ∧ 2≤times j t.tags) ∧ (t.prune S).tags.Nodup ∧
      Disjoint (t.prune S).tags.toFinset (t.prune S).pins.toFinset ∧
      (∀ k∈(t.prune S).pins, k∈t.tags ∧ 2≤times k t.tags) ∧
      ¬(t.prune S).pins.Nodup := by
  classical
  let S := t.tags.toFinset.filter (fun j => 2≤times j t.tags)
  have sm (j : Nat) : j∈S ↔ j∈t.tags ∧ 2≤times j t.tags := by simp [S]
  have ne : S.Nonempty := by
    by_contra z
    apply repeatLabel
    apply uniqueOfTimes
    intro j
    by_contra! big
    have mem : j∈t.tags := by
      by_contra h
      have hz := (times_zero_iff j t.tags).mpr h
      omega
    exact z ⟨j,(sm j).mpr ⟨mem,by omega⟩⟩
  let k := S.max' ne
  have ks : k∈S := Finset.max'_mem S ne
  have fresh : (t.prune S).tags.Nodup := by
    apply uniqueOfTimes
    intro j
    obtain ⟨le,off⟩ := t.prunedCounts S j
    by_cases js : j∈S
    · rw [off js]; decide
    by_cases mem : j∈t.tags
    · have no : ¬2≤times j t.tags := fun b => js ((sm j).mpr ⟨mem,b⟩)
      omega
    · have z := (times_zero_iff _ _).mpr mem
      omega
  refine ⟨S,sm,fresh,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro j inT inP
    have pin : j∈(t.prune S).pins := List.mem_toFinset.mp inP
    have cut := (t.prunedPins S empty j pin).1
    exact (times_zero_iff j _).mp ((t.prunedCounts S j).2 cut) (List.mem_toFinset.mp inT)
  · intro j pin
    exact (sm j).mp (t.prunedPins S empty j pin).1
  · intro unique
    have ub := timesOfUnique _ unique k
    have lb := t.maxCopies S k ks (fun j hj => Finset.le_max' S j hj) desc
    have many := ((sm k).mp ks).2
    omega


end Tree5176
namespace Wires5176
open Tree5176 PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity Singleton5176 CoverRigidity4801
def annotated (C : Circuit) (k : Nat) : Cluster :=
  if h : k<26 then .raw ⟨k,h⟩ else
    let g := C.gates.getD (k-26) ⟨.or,[]⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if ha : a<k then
      if hb : b<k then
        match g.op with
        | .and => .bin (k-26) true (annotated C a) (annotated C b)
        | _ => .bin (k-26) false (annotated C a) (annotated C b)
      else .raw 0
    else .raw 0
termination_by k

private theorem annotatedRaw (C : Circuit) (i : Fin 26) : annotated C i.val = .raw i := by
  rw [annotated]
  simp only [i.isLt, ↓reduceDIte]

private theorem annotatedAt {C : Circuit} (ao : IsAO2 26 C) {j a b : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) (ins : g.inputs=[a,b]) :
    (g.op=.and → annotated C (26+j)=.bin j true (annotated C a) (annotated C b)) ∧
    (g.op=.or → annotated C (26+j)=.bin j false (annotated C a) (annotated C b)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have ga : a<26+j := childPrior ao hit (by simp [ins])
  have gb : b<26+j := childPrior ao hit (by simp [ins])
  have hget : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,hg]
  constructor <;> intro op <;> rw [annotated] <;> simp [hit,ins,op,ga,gb]
theorem profile {C : Circuit} (ao : IsAO2 26 C) (w : Nat) (valid : w<26+C.size) :
    ∃ t : Cluster, t=annotated C w ∧ t.pins=[] ∧ t.orderedIndices ∧ (∀ k∈t.tags,26+k≤w) ∧
      t.tags.length+1=(tree C w).leaves ∧
      ∀ (S : Finset Nat) x, (t.prune S).ev x (fun j => wire C x (26+j))=wire C x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<26
    · let i : Fin 26 := ⟨w,raw⟩
      refine ⟨.raw i,(annotatedRaw C i).symm,rfl,True.intro,by simp [Cluster.tags],?_,?_⟩
      · change 1=(tree C i.val).leaves
        rw [rawTree]
        rfl
      · exact fun S x => (rawValue C x i).symm
    let j := w-26
    have hj : j<C.gates.length := by change w<26+C.gates.length at valid; dsimp [j]; omega
    have eqw : w=26+j := by dsimp [j]; omega
    let g := C.gates[j]
    have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    have gin := List.mem_of_getElem? hit
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    obtain ⟨l,cl,lp,ld,vl,bl,el⟩ := ih a (by omega) (by omega)
    obtain ⟨r,cr,rp,rd,vr,br,er⟩ := ih b (by omega) (by omega)
    rcases ao.1 g gin with op|op
    ·
      let out := Cluster.bin j true l r
      refine ⟨out,?_,?_,?_,?_,?_,?_⟩
      · rw [eqw,(annotatedAt ao hit ins).1 op,←cl,←cr]
      · simp [out,Cluster.pins,lp,rp]
      · exact ⟨fun k mem => by have := vl k mem; omega,fun k mem => by have := vr k mem; omega,ld,rd⟩
      · intro k mem
        rcases (show k=j ∨ k∈l.tags ∨ k∈r.tags by simpa [out,Cluster.tags] using mem) with rfl|hm|hm
        · omega
        · have := vl k hm; omega
        · have := vr k hm; omega
      · rw [eqw,(atGate ao hit ins).1 op]
        simp only [out,Cluster.tags,List.length_cons,List.length_append,DMFormula.leaves]
        omega
      · intro S x
        by_cases js : j∈S
        · simp [out,Cluster.prune,js,Cluster.ev,eqw]
        · rw [eqw,gateValue ao x hit]
          simp only [out,Cluster.prune,if_neg js,Cluster.ev,el S x,er S x]
          simp [ins,op,GateOp.eval]

    ·
      let out := Cluster.bin j false l r
      refine ⟨out,?_,?_,?_,?_,?_,?_⟩
      · rw [eqw,(annotatedAt ao hit ins).2 op,←cl,←cr]
      · simp [out,Cluster.pins,lp,rp]
      · exact ⟨fun k mem => by have := vl k mem; omega,fun k mem => by have := vr k mem; omega,ld,rd⟩
      · intro k mem
        rcases (show k=j ∨ k∈l.tags ∨ k∈r.tags by simpa [out,Cluster.tags] using mem) with rfl|hm|hm
        · omega
        · have := vl k hm; omega
        · have := vr k hm; omega
      · rw [eqw,(atGate ao hit ins).2 op]
        simp only [out,Cluster.tags,List.length_cons,List.length_append,DMFormula.leaves]
        omega
      · intro S x
        by_cases js : j∈S
        · simp [out,Cluster.prune,js,Cluster.ev,eqw]
        · rw [eqw,gateValue ao x hit]
          simp only [out,Cluster.prune,if_neg js,Cluster.ev,el S x,er S x]
          simp [ins,op,GateOp.eval]


open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def Reads (C : Circuit) (j k : Nat) : Prop :=
  ∃ g : Gate, C.gates[k]?=some g ∧ 26+j∈g.inputs

theorem labelFlow {C : Circuit} (ao : IsAO2 26 C)
    (distinct : ∀ g∈C.gates, g.inputs.Nodup) (j r : Nat)
    (only : ∀ k, Reads C j k → k=r) (w : Nat) (valid : w<26+C.size) :
    times j (annotated C w).tags ≤ times r (annotated C w).tags + (if w=26+j then 1 else 0) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<26
    · let i : Fin 26 := ⟨w,raw⟩
      change times j (annotated C i.val).tags ≤ times r (annotated C i.val).tags+_
      rw [annotatedRaw]
      simp [Cluster.tags,times]
    let k := w-26
    have hk : k<C.gates.length := by change w<26+C.gates.length at valid; dsimp [k]; omega
    have eqw : w=26+k := by dsimp [k]; omega
    let g := C.gates[k]
    have hit : C.gates[k]?=some g := List.getElem?_eq_getElem hk
    have gin := List.mem_of_getElem? hit
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    have ab : a≠b := by simpa [ins] using distinct g gin
    have la := ih a (by omega) (by omega)
    have lb := ih b (by omega) (by omega)
    have pay : (if a=26+j then 1 else 0)+(if b=26+j then 1 else 0) ≤ (if r=k then 1 else 0) := by
      by_cases ap : a=26+j
      · have bp : b≠26+j := by omega
        have kr := only k ⟨g,hit,by simp [ins,ap]⟩
        simp [ap,bp,kr]
      · by_cases bp : b=26+j
        · have kr := only k ⟨g,hit,by simp [ins,bp]⟩
          simp [ap,bp,kr]
        · simp [ap,bp]
    have ident : (if j=k then 1 else 0 : Nat)=(if w=26+j then 1 else 0) := by
      by_cases eq : j=k
      · simp [eq,eqw]
      · have ne : w≠26+j := by omega
        simp [eq,ne]
    rcases ao.1 g gin with op|op
    · rw [eqw,(annotatedAt ao hit ins).1 op]
      simp only [Cluster.tags,times,times_append]
      have same := ident
      rw [eqw] at same
      omega
    · rw [eqw,(annotatedAt ao hit ins).2 op]
      simp only [Cluster.tags,times,times_append]
      have same := ident
      rw [eqw] at same
      omega

theorem invisibleSingle {C : Circuit} (ao : IsAO2 26 C) (j r : Nat)
    (only : ∀ k, Reads C j k → k=r) (S : Finset Nat) (rs : r∈S)
    (w : Nat) (valid : w<26+C.size) (neq : w≠26+j) :
    j∉((annotated C w).prune S).pins := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<26
    · let i : Fin 26 := ⟨w,raw⟩
      change j∉((annotated C i.val).prune S).pins
      rw [annotatedRaw]
      simp [Cluster.prune,Cluster.pins]
    let k := w-26
    have hk : k<C.gates.length := by change w<26+C.gates.length at valid; dsimp [k]; omega
    have eqw : w=26+k := by dsimp [k]; omega
    let g := C.gates[k]
    have hit : C.gates[k]?=some g := List.getElem?_eq_getElem hk
    have gin := List.mem_of_getElem? hit
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    have ne : j≠k := by omega
    have sub (q : Bool) : j∉((Cluster.bin k q (annotated C a) (annotated C b)).prune S).pins := by
      by_cases ks : k∈S
      · simp [Cluster.prune,ks,Cluster.pins,ne]
      · have ab (z : Nat) (h : z∈g.inputs) : z≠26+j := by
          intro e
          have kr := only k ⟨g,hit,e ▸ h⟩
          exact ks (kr ▸ rs)
        have la := ih a (by omega) (by omega) (ab a (by simp [ins]))
        have lb := ih b (by omega) (by omega) (ab b (by simp [ins]))
        simp [Cluster.prune,ks,Cluster.pins,la,lb]
    rcases ao.1 g gin with op|op
    · rw [eqw,(annotatedAt ao hit ins).1 op]; exact sub true
    · rw [eqw,(annotatedAt ao hit ins).2 op]; exact sub false

theorem topCount (t : Cluster) (desc : t.orderedIndices) (j : Nat)
    (top : ∀ i∈t.tags, i≤j) : times j t.tags≤1 := by
  cases t with
  | raw i => simp [Cluster.tags,times]
  | port k => simp [Cluster.tags,times]
  | bin k q l r =>
    obtain ⟨dl,dr,_,_⟩ := desc
    have kle := top k (by simp [Cluster.tags])
    have nnl : j∉l.tags := fun h => (Nat.not_lt_of_ge kle) (dl j h)
    have nnr : j∉r.tags := fun h => (Nat.not_lt_of_ge kle) (dr j h)
    by_cases eq : j=k <;> simp [Cluster.tags,times,times_append,(times_zero_iff j _).mpr nnl,(times_zero_iff j _).mpr nnr,eq]

def Broad (C : Circuit) (k : Nat) : Prop :=
  ∀ u v, Tree5176.plane.Adj u v → ∃ a b, Tree5176.plane.Adj a b ∧
    wire C (row a b) (26+k)=true ∧ ¬((a=u ∧ b=v) ∨ (a=v ∧ b=u))

theorem broadReaders {C : Circuit} (ao : IsAO2 26 C) (small : C.size≤64)
    (distinct : ∀ g∈C.gates, g.inputs.Nodup)
    (spec : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔
      ∃ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x (pt p)=true ∧ x (ln l)=true)
    {k : Nat} (op : (gateAt C k).op = .and)
    (live : InCone 26 C k (C.output-26))
    (pair : gateVal 26 C k (pairInput (0 : Fin 26) 13)=true)
    (quiet : ∀ b : Fin 2, wire C (pairInput (0 : Fin 26) 0) (opnd C k b)=false ∧
      wire C (pairInput (13 : Fin 26) 13) (opnd C k b)=false) :
    ∃ j<C.size, 2≤times j (annotated C C.output).tags ∧ Broad C j ∧
      ∃ a b, a≠b ∧ Reads C j a ∧ Reads C j b := by
  classical
  have inc : ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ oriented p l := by decide +kernel
  have spec' (x : Fin 26→Bool) : wire C x C.output=true ↔ accepts x :=
    (spec x).trans (exists_congr fun p => exists_congr fun l => and_congr_left fun _ => inc p l)
  have flag : wire C (bits 8193) C.output=true := (spec' _).2 ⟨0,0,Or.inl rfl,by decide,by decide⟩
  have valid : C.output<26+C.size := by
    by_contra h
    change (wiresFrom C.gates (List.ofFn (bits 8193))).getD C.output false=true at flag
    rw [List.getD_eq_default] at flag
    · contradiction
    · rw [length_wiresFrom,List.length_ofFn]; exact Nat.le_of_not_gt h
  have target (x : Row) : wire C x C.output=flagFun x := Bool.eq_iff_iff.mpr (by
    simpa only [flagFun,decide_eq_true_eq] using (spec' x).trans (graphAccept x))
  have lower := markedLower ao spec op (Or.inr live) pair quiet
  obtain ⟨t,ct,empty,desc,tagValid,count,allSem⟩ := profile ao C.output valid
  have noFresh : ¬t.tags.Nodup := by
    intro nd
    have sub : t.tags.toFinset ⊆ Finset.range C.size := fun j hj => Finset.mem_range.mpr (by
      have := tagValid j (List.mem_toFinset.mp hj); omega)
    have z := Finset.card_le_card sub
    rw [Finset.card_range,List.toFinset_card_of_nodup nd] at z
    omega
  obtain ⟨S,members,fresh,sep,pinTag,repeats⟩ := t.maxCut desc empty noFresh
  let z := t.prune S
  have can (j : Nat) (mem : j∈z.pins) : j<C.size := by
    have := tagValid j (pinTag j mem).1; omega
  have readers (j : Nat) (mem : j∈z.pins) : ∃ k l, k≠l ∧ Reads C j k ∧ Reads C j l := by
    have copies := (pinTag j mem).2
    have root_ne : C.output≠26+j := by
      intro eqw
      have top : ∀ i∈t.tags, i≤j := by
        intro i hi
        have := tagValid i hi
        omega
      have lim := topCount t desc j top
      omega
    have narrowReader (r : Nat) (only : ∀ k, Reads C j k → k=r) : False := by
      have flow := labelFlow ao distinct j r only C.output valid
      rw [←ct,if_neg root_ne,Nat.add_zero] at flow
      have rm : 2≤times r t.tags := by omega
      have present : r∈t.tags := by
        by_contra h
        have zz := (times_zero_iff r t.tags).mpr h
        omega
      have rs := (members r).mpr ⟨present,rm⟩
      have absent := invisibleSingle ao j r only S rs C.output valid root_ne
      rw [←ct] at absent
      exact absent mem
    by_cases reader : ∃ k, Reads C j k
    · obtain ⟨k,hk⟩ := reader
      by_contra! one
      apply narrowReader k
      intro l hl
      by_contra diff
      exact one k l (Ne.symm diff) hk hl
    · exact (narrowReader 0 (fun k hk => (reader ⟨k,hk⟩).elim)).elim
  suffices has : ∃ j∈z.pins, Broad C j by
    obtain ⟨j,mem,wide⟩ := has
    exact ⟨j,can j mem,ct ▸ (pinTag j mem).2,wide,readers j mem⟩
  by_contra! none
  have choices (j : Nat) : ∃ u v, Tree5176.plane.Adj u v ∧
      (j∈z.pins → ∀ a b, Tree5176.plane.Adj a b → wire C (row a b) (26+j)=true →
        (a=u ∧ b=v) ∨ (a=v ∧ b=u)) := by
    by_cases mem : j∈z.pins
    · have bad := none j mem
      unfold Broad at bad
      push_neg at bad
      obtain ⟨u,v,e,cov⟩ := bad
      exact ⟨u,v,e,fun _ => cov⟩
    · exact ⟨0,13,by decide,fun yes => False.elim (mem yes)⟩
  choose u v args using choices
  have bound : z.tags.toFinset ∪ z.pins.toFinset ⊆ Finset.range C.size := by
    intro j hj
    apply Finset.mem_range.mpr
    rcases Finset.mem_union.mp hj with tag | pin
    · have pos : 0<times j z.tags := by
        by_contra! no
        have nn := (times_zero_iff j z.tags).mp (by omega)
        exact nn (List.mem_toFinset.mp tag)
      have le := (t.prunedCounts S j).1
      have orig : j∈t.tags := by
        by_contra h
        have zz := (times_zero_iff j t.tags).mpr h
        change times j z.tags≤_ at le
        omega
      have := tagValid j orig; omega
    · exact can j (List.mem_toFinset.mp pin)
  have price := multiPortCost z C.size small (fun j x => wire C x (26+j)) u v
    (fun x => (allSem S x).trans (target x)) (fun j _ => (args j).1)
    (fun j hj => (args j).2 hj) fresh sep bound
  exact repeats (uniqueOfCard z.pins price)

end Wires5176
end PEqualNP.Outside.L_meta_18611
