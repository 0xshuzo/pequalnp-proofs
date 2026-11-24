import Mathlib
import PEqualNP.Defs

-- The clean-gate cover certificate below is adapted from the project’s L_meta_1602.
namespace Drops3451

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

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem singleton_of_superpair {n : ℕ} (C : Circuit) (mono : Monotone2 C) (v w : Fin n) (k : ℕ)
    (bad : (C.wires (List.ofFn fun i : Fin n => decide (i=v ∨ i=w))).getD k false = false) :
    (C.wires (List.ofFn fun i : Fin n => decide (i=v))).getD k false = false ∧
      (C.wires (List.ofFn fun i : Fin n => decide (i=w))).getD k false = false := by
  have ops (g : Gate) (hg : g∈C.gates) : g.op = .and ∨ g.op = .or := by
    simpa using (mono g hg).1
  have lower (u : Fin n) (inPair : u=v ∨ u=w) :
      (C.wires (List.ofFn fun i : Fin n => decide (i=u))).getD k false=false := by
    cases h : (C.wires (List.ofFn fun i : Fin n => decide (i=u))).getD k false with
    | false => rfl
    | true =>
      have comp : ∀ i : ℕ, (List.ofFn fun j : Fin n => decide (j=u)).getD i false=true →
          (List.ofFn fun j : Fin n => decide (j=v ∨ j=w)).getD i false=true := by
        intro i hi
        by_cases range : i<n
        · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,range,dite_true,Option.getD_some,decide_eq_true_eq] at hi ⊢
          simpa only [hi] using inPair
        · simp [List.getD_eq_getElem?_getD,range] at hi
      have on := wiresFrom_mono C.gates ops _ _ (by simp) comp k h
      exact False.elim (Bool.noConfusion (bad.symm.trans on))
  exact ⟨lower _ (Or.inl rfl),lower _ (Or.inr rfl)⟩

theorem singles {N : ℕ} (I : Fin N → Fin N → Prop) (D : Circuit) (mono : Monotone2 D)
    (nonrow : ∀ p, ∃ l, ¬I p l) (noncol : ∀ l, ∃ p, ¬I p l)
    (pair : ∀ j < D.gates.length, (gateAt D j).op = .and → ∀ p l, ¬I p l →
      (D.wires (List.ofFn fun k : Fin (N+N) => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l))).getD (N+N+j) false = false) :
    ∀ j < D.gates.length, (gateAt D j).op = .and →
      (∀ p, (D.wires (List.ofFn fun k : Fin (N+N) => decide (k=Fin.castAdd N p))).getD (N+N+j) false=false) ∧
      ∀ l, (D.wires (List.ofFn fun k : Fin (N+N) => decide (k=Fin.natAdd N l))).getD (N+N+j) false=false := by
  intro j hj op
  constructor
  · intro p
    obtain ⟨l,no⟩ := nonrow p
    exact (singleton_of_superpair D mono _ _ _ (pair j hj op p l no)).1
  · intro l
    obtain ⟨p,no⟩ := noncol l
    exact (singleton_of_superpair D mono _ _ _ (pair j hj op p l no)).2

theorem universalRow {N : ℕ} (I : Fin N → Fin N → Prop)
    (free : ∀ p q a b, p≠q → a≠b → ¬(I p a ∧ I p b ∧ I q a ∧ I q b))
    (r : Fin N) (full : ∀ l, I r l) : ∀ p, p≠r → ∀ l l', I p l → I p l' → l=l' := by
  intro p pr l l' pl pl'
  by_contra distinct
  exact free p r l l' pr distinct ⟨pl,pl',full l,full l'⟩

end Drops3451
