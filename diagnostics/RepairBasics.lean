import Mathlib
import PEqualNP.Defs

-- The clean-gate cover certificate below is adapted from the project’s L_meta_1602.
namespace SparsePrice4697

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



end SparsePrice4697
namespace Repair4678
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SparsePrice4697
def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def build (f : ℕ → Gate → Gate) : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g::t => f k g :: build f (k+1) t

theorem buildLen (f : ℕ → Gate → Gate) (k : ℕ) (gs : List Gate) : (build f k gs).length=gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g t ih => simp [build,ih]

theorem buildAt (f : ℕ → Gate → Gate) (k j : ℕ) (gs : List Gate) :
    (build f k gs)[j]? = gs[j]?.map (f (k+j)) := by
  induction gs generalizing k j with
  | nil => simp [build]
  | cons g t ih =>
    cases j with
    | zero => simp [build]
    | succ j => simpa only [build,List.getElem?_cons_succ,show k+(j+1)=k+1+j by omega] using ih (k+1) j

theorem buildMono (f : ℕ → Gate → Gate) (k : ℕ) (gs : List Gate)
    (h : ∀ j (hj : j<gs.length), let g := f (k+j) gs[j]
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) : Monotone2 ⟨build f k gs,0⟩ := by
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
  have orig : j<gs.length := by simpa [buildLen] using hj
  have same : (build f k gs)[j] = f (k+j) gs[j] := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem orig] using buildAt f k j gs
  rw [same]
  exact h j orig

theorem origValue (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j<gs.length) :
    (wiresFrom gs w).getD (w.length+j) false=val gs[j] (wiresFrom (gs.take j) w) := by
  have split : gs=gs.take j++gs[j]::gs.drop (j+1) := by
    have e := (List.take_append_drop j gs).symm
    rwa [List.drop_eq_getElem_cons hj] at e
  let u := wiresFrom (gs.take j) w
  have dim : u.length=w.length+j := by simp [u,length_wiresFrom,Nat.min_eq_left hj.le]
  have step : wiresFrom gs w=wiresFrom (gs.drop (j+1)) (u++[val gs[j] u]) := by
    conv_lhs => rw [split,wiresFrom_append]
    rfl
  rw [step,←dim,getD_wiresFrom_lt _ _ _ (by simp),getD_snoc_eq]

theorem same (f : Nat → Gate → Gate) (k : ℕ) (gs : List Gate) (w : List Bool)
    (he : ∀ j (hj : j<gs.length),
      val (f (k+j) gs[j]) (wiresFrom (gs.take j) w)=val gs[j] (wiresFrom (gs.take j) w)) :
    wiresFrom (build f k gs) w=wiresFrom gs w := by
  induction gs generalizing k w with
  | nil => rfl
  | cons g t ih =>
    have e : val (f k g) w=val g w := by simpa [wiresFrom] using he 0 (by simp)
    change wiresFrom (build f (k+1) t) (w++[val (f k g) w]) = wiresFrom t (w++[val g w])
    rw [e]
    apply ih
    intro j hj
    simpa only [List.take_succ_cons,List.getElem_cons_succ,show k+(j+1)=k+1+j by omega] using he (j+1) (by simpa using hj)

theorem lower (f : Nat → Gate → Gate) (k : ℕ) (gs : List Gate) (w : List Bool)
    (hm : Monotone2 ⟨build f k gs,0⟩)
    (he : ∀ j (hj : j<gs.length),
      val (f (k+j) gs[j]) (wiresFrom (gs.take j) w)=true → val gs[j] (wiresFrom (gs.take j) w)=true) :
    ∀ i, (wiresFrom (build f k gs) w).getD i false=true → (wiresFrom gs w).getD i false=true := by
  induction gs generalizing k w with
  | nil => exact fun _ h => h
  | cons g t ih =>
    let u := w++[val (f k g) w]
    let v := w++[val g w]
    have initial : val (f k g) w=true → val g w=true := by simpa [wiresFrom] using he 0 (by simp)
    have le (i) : u.getD i false=true → v.getD i false=true := by
      by_cases h : i<w.length
      · simpa [u,v,List.getD_append _ _ _ _ h]
      · rw [show u=w++[_] from rfl,show v=w++[_] from rfl,
           List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
        cases e : i-w.length with
        | zero => exact initial
        | succ j => simp
    have mm : Monotone2 ⟨build f (k+1) t,0⟩ := fun a ha => hm a (List.mem_cons_of_mem _ ha)
    have pre := wiresFrom_mono (build f (k+1) t) (fun a ha => (mm a ha).1) u v (by simp [u,v]) le
    have rest := ih (k+1) v mm (by
      intro j hj
      simpa only [List.take_succ_cons,List.getElem_cons_succ,show k+(j+1)=k+1+j by omega] using he (j+1) (by simpa using hj))
    exact fun i h => rest i (pre i h)

end Repair4678
