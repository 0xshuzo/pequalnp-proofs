import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1972.Donor4113

-- The circuit simplifier below is copied from the checked file L_meta_1743.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default; rw [W_len]; exact hi

theorem W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (W gs x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + k then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g h; simp at h
  | append_singleton gs a ih =>
    intro k g h
    rw [W_snoc]
    rcases Nat.lt_or_ge k gs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + k
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp only [hi, if_false]
    · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
      · have hk2 : k = gs.length := by omega
        subst hk2
        have hag : a = g := by simpa using h
        subst hag
        rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + gs.length
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
          exact W_oob gs x i (by omega)
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h

def sh (p : ℕ) (i : ℕ) : ℕ := if p < i then i - 1 else i

def up (p : ℕ) (m : ℕ) : ℕ := if m < p then m else m + 1

def del (G : List Gate) (j : ℕ) (T : Gate → Gate) : List Gate :=
  G.take j ++ (G.drop (j + 1)).map T

theorem del_len (G : List Gate) (j : ℕ) (T : Gate → Gate) (hj : j < G.length) :
    (del G j T).length + 1 = G.length := by
  simp [del]; omega

theorem del_lt (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : k < j) (h : (del G j T)[k]? = some g) : G[k]? = some g := by
  unfold del at h
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take] at h
  simpa [hk] using h

theorem del_ge (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : j ≤ k) (h : (del G j T)[k]? = some g) : ∃ g0, G[k + 1]? = some g0 ∧ g = T g0 := by
  unfold del at h
  rw [List.getElem?_append_right (by simp; omega)] at h
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop] at h
  have e : j + 1 + (k - min j G.length) = k + 1 := by
    rw [Nat.min_eq_left (by omega)]; omega
  rw [e] at h
  cases hg : G[k + 1]? with
  | none => rw [hg] at h; simp at h
  | some g0 => rw [hg] at h; exact ⟨g0, rfl, by simpa using h.symm⟩

theorem sim (G : List Gate) (j : ℕ) (T : Gate → Gate) (x : List Bool) (n : ℕ) (hx : x.length = n)
    (hj : j < G.length)
    (hT : ∀ (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g → ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G x).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G x).getD i false) →
      (∀ i, i < n → ρ' i = x.getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ)) :
    ∀ m, (W (del G j T) x).getD m false = (W G x).getD (up (n + j) m) false := by
  subst hx
  have hlen := del_len G j T hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m x.length with hm | hm
  · rw [W_inp _ _ _ hm, show up (x.length + j) m = m by simp only [up]; split_ifs <;> omega,
      W_inp _ _ _ hm]
  · obtain ⟨k, rfl⟩ : ∃ k, m = x.length + k := ⟨m - x.length, by omega⟩
    rcases Nat.lt_or_ge k (del G j T).length with hk | hk
    · have hg : (del G j T)[k]? = some (del G j T)[k] := List.getElem?_eq_getElem hk
      rw [W_spec _ _ k _ hg]
      rcases Nat.lt_or_ge k j with hkj | hkj
      · have hg0 := del_lt G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + k by
          simp only [up]; split_ifs <;> omega, W_spec _ _ k _ hg0]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, if_true]
          rw [ih i hi, show up (x.length + j) i = i by simp only [up]; split_ifs <;> omega]
        · simp only [hi, if_false]
      · obtain ⟨g0, hg0, hgT⟩ := del_ge G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + (k + 1) by
          simp only [up]; split_ifs <;> omega, W_spec _ _ (k + 1) _ hg0, hgT]
        apply hT k g0 hkj hg0
        · intro i hi
          by_cases h1 : x.length + j < i
          · have e1 : sh (x.length + j) i = i - 1 := by simp only [sh]; split_ifs; rfl
            rw [e1]
            by_cases h2 : i < x.length + (k + 1)
            · have h3 : i - 1 < x.length + k := by omega
              simp only [h2, h3, if_true]
              rw [ih (i - 1) h3]
              congr 1
              simp only [up]; split_ifs <;> omega
            · have h3 : ¬ i - 1 < x.length + k := by omega
              simp only [h2, h3, if_false]
          · have e1 : sh (x.length + j) i = i := by simp only [sh]; split_ifs; rfl
            rw [e1]
            have h2 : i < x.length + (k + 1) := by omega
            have h3 : i < x.length + k := by omega
            simp only [h2, h3, if_true]
            rw [ih i h3]
            congr 1
            simp only [up]; split_ifs <;> omega
        · have h2 : x.length + j < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h2 : i < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h3 : i < x.length + k := by omega
          simp only [h3, if_true]
          exact W_inp _ _ _ hi
        · intro i hi
          have h3 : ¬ i < x.length + k := by omega
          simp only [h3, if_false]
    · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by simp only [up]; split_ifs <;> omega)]

def Ts (p t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = p then t else sh p i⟩

theorem Ts_eval (p t : ℕ) (g : Gate) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ' t = ρ p) :
    (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  simp only [Ts, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i = p
  · subst hi; simp only [Function.comp, if_true]; exact hp
  · simp only [Function.comp, hi, if_false]; exact h1 i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def Rn (v B : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = v then B else i⟩

theorem subst (G : List Gate) (n v : ℕ) (hv : v < n) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n)
    (hxy : ∀ i, i < n → i ≠ v → x.getD i false = y.getD i false)
    (hyv : y.getD v false = false) :
    ∀ m, m ≠ v →
      (W (G.map (Rn v (n + G.length))) x).getD m false = (W G y).getD m false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hmv
  rcases Nat.lt_or_ge m n with hm | hm
  · rw [W_inp (G.map (Rn v (n + G.length))) x m (by omega), W_inp G y m (by omega)]
    exact hxy m hm hmv
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    rcases Nat.lt_or_ge k G.length with hk | hk
    · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
      have hg1 : (G.map (Rn v (n + G.length)))[k]? = some (Rn v (n + G.length) G[k]) := by
        rw [List.getElem?_map, hg]; rfl
      have e1 := W_spec (G.map (Rn v (n + G.length))) x k _ hg1
      have e2 := W_spec G y k _ hg
      rw [hx] at e1
      rw [hy] at e2
      rw [e1, e2]
      simp only [Rn, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i = v
      · have h1 : ¬ (n + G.length < n + k) := by omega
        have h2 : i < n + k := by omega
        rw [if_pos hi, if_neg h1, if_pos h2, hi, W_inp G y v (by omega)]
        exact hyv.symm
      · rw [if_neg hi]
        by_cases h2 : i < n + k
        · rw [if_pos h2, if_pos h2]; exact ih i h2 hi
        · rw [if_neg h2, if_neg h2]
    · rw [W_oob (G.map (Rn v (n + G.length))) x (n + k) (by rw [List.length_map]; omega),
        W_oob G y (n + k) (by omega)]

def Tt (p : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => ⟨GateOp.and, (l.filter fun i => decide (i ≠ p)).map (sh p)⟩
  | ⟨GateOp.or, l⟩ => if p ∈ l then ⟨GateOp.and, []⟩ else ⟨GateOp.or, l.map (sh p)⟩
  | ⟨GateOp.not, l⟩ => if l.head? = some p then ⟨GateOp.or, []⟩ else ⟨GateOp.not, l.map (sh p)⟩
  | g => g

theorem all_filter (p : ℕ) (ρ ρ' : ℕ → Bool) (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i)
    (hp : ρ p = true) (l : List ℕ) :
    ((((l.filter fun i => decide (i ≠ p)).map (sh p)).map ρ').all id) = ((l.map ρ).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = p
    · have e : ((a :: l).filter fun i => decide (i ≠ p)) = (l.filter fun i => decide (i ≠ p)) := by
        simp [List.filter_cons, ha]
      rw [e, ih]
      simp [ha, hp]
    · have e : ((a :: l).filter fun i => decide (i ≠ p))
          = a :: (l.filter fun i => decide (i ≠ p)) := by
        simp [List.filter_cons, ha]
      rw [e]
      simp only [List.map_cons, List.all_cons]
      rw [ih, h1 a ha]

theorem Tt_eval (p : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ p = true) :
    (Tt p g).op.eval ((Tt p g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    simp only [Tt, GateOp.eval]
    exact all_filter p ρ ρ' h1 hp inputs
  | or =>
    by_cases hm : p ∈ inputs
    · simp only [Tt, hm, if_true, GateOp.eval]
      simp only [List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨p, hm, hp⟩, rfl⟩
    · simp only [Tt, hm, if_false, GateOp.eval, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h1 i (fun h => hm (h ▸ hi))
  | not =>
    cases inputs with
    | nil => simp [Tt, GateOp.eval]
    | cons a l =>
      by_cases ha : a = p
      · subst ha; simp [Tt, GateOp.eval, hp]
      · simp [Tt, GateOp.eval, ha, h1 a ha]
  | mod m => simp at hop
  | maj => simp at hop

theorem Tt_fan (p : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Tt p g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Tt p g).inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := h
  cases op with
  | and =>
    refine ⟨by simp [Tt], ?_⟩
    simp only [Tt, List.length_map]
    exact le_trans (List.length_filter_le _ _) hl
  | or =>
    by_cases hm : p ∈ inputs
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, if_false, List.length_map]
      exact hl
  | not =>
    by_cases hm : inputs.head? = some p
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, if_false, List.length_map]
      exact hl
  | mod m => simp at hop
  | maj => simp at hop

theorem Ts_fan (p t : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Ts p t g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Ts p t g).inputs.length ≤ 2 := by
  refine ⟨h.1, ?_⟩
  simp only [Ts, List.length_map]
  exact h.2

def FT (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def eff (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

def Red (n : ℕ) (G : List Gate) (j : ℕ) : Prop :=
  (∃ b : Bool, ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + j) false = b) ∨
  (∃ o, o < n + j ∧ ∀ x : Fin n → Bool,
    (W G (List.ofFn x)).getD (n + j) false = (W G (List.ofFn x)).getD o false)

theorem fin2 (n : ℕ) (h : (Fin n → Bool) → Bool) (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (T : Gate → Gate)
    (hTF : ∀ g ∈ G, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (T g).inputs.length ≤ 2)
    (hT : ∀ (x : Fin n → Bool) (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g →
      ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G (List.ofFn x)).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G (List.ofFn x)).getD i false) →
      (∀ i, i < n → ρ' i = (List.ofFn x).getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ))
    (ho : out = n + j → ∃ o, o < n + j ∧
      ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  have key : ∀ (x : Fin n → Bool) (m : ℕ),
      (W (del G j T) (List.ofFn x)).getD m false
        = (W G (List.ofFn x)).getD (up (n + j) m) false := by
    intro x
    exact sim G j T (List.ofFn x) n (by simp) hj (fun k g hk hg => hT x k g hk hg)
  have hlen := del_len G j T hj
  have hFT : FT (del G j T) := by
    intro g hg
    unfold del at hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hF g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      exact hTF g0 (List.mem_of_mem_drop hg0)
  have hlow : ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
      (W (del G j T) (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    intro x m hm
    rw [key x m, show up (n + j) m = m by simp only [up]; split_ifs <;> omega]
  by_cases hout : out = n + j
  · obtain ⟨o, hon, hox⟩ := ho hout
    exact ⟨del G j T, o, hFT, hlen, fun x => by rw [hlow x o hon]; exact hox x, hlow⟩
  · refine ⟨del G j T, sh (n + j) out, hFT, hlen, ?_, hlow⟩
    intro x
    rw [key x, ← hf x]
    congr 1
    simp only [up, sh]
    split_ifs <;> omega

theorem sdl (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y)
    (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (hR : Red n G j) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  rcases hR with ⟨b, hb⟩ | ⟨o, hoj, hoe⟩
  · have ho : out = n + j → ∃ o, o < n + j ∧
        ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x := by
      intro hout
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      rw [← hf x, ← hf y, hout, hb x, hb y]
    cases b with
    | false =>
      refine fin2 n h G out hF hf j hj (Ts (n + j) (n + G.length))
        (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ho
      intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      rw [h2, hb x]
      exact h4 _ (by omega)
    | true =>
      refine fin2 n h G out hF hf j hj (Tt (n + j))
        (fun g hg => Tt_fan _ g (hF g hg)) ?_ ho
      intro x k g _ hg ρ ρ' h1 h2 h5 h3 h4
      exact Tt_eval _ g (hF g (List.mem_of_getElem? hg)).1 ρ ρ' h1 (h2.trans (hb x))
  · refine fin2 n h G out hF hf j hj (Ts (n + j) o)
      (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ?_
    · intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      have e : sh (n + j) o = o := by
        simp only [sh]; split_ifs <;> omega
      have a1 := h1 o (by omega)
      rw [e] at a1
      rw [a1, h5 o hoj, h2]
      exact (hoe x).symm
    · intro hout
      exact ⟨o, hoj, fun x => by rw [← hoe x, ← hout]; exact hf x⟩

theorem iter (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y) :
    ∀ (k : ℕ) (S : Finset ℕ), S.card = k → ∀ (G : List Gate) (out : ℕ), FT G →
      (∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x) →
      (∀ j ∈ S, j < G.length ∧ Red n G j) →
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + k = G.length ∧
        ∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x := by
  intro k
  induction k with
  | zero =>
    intro S _ G out hF hf _
    exact ⟨G, out, hF, rfl, hf⟩
  | succ k ih =>
    intro S hS G out hF hf hR
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hj, hRj⟩ := hR (S.max' hne) (S.max'_mem hne)
    obtain ⟨G1, out1, hF1, hl1, hf1, hlow⟩ := sdl n h hnc G out hF hf (S.max' hne) hj hRj
    have hR1 : ∀ i ∈ S.erase (S.max' hne), i < G1.length ∧ Red n G1 i := by
      intro i hi
      have hlt : i < S.max' hne := Finset.lt_max'_of_mem_erase_max' S hne hi
      obtain ⟨_, hRi⟩ := hR i (Finset.mem_of_mem_erase hi)
      refine ⟨by omega, ?_⟩
      rcases hRi with ⟨b, hb⟩ | ⟨o, ho, hoe⟩
      · exact Or.inl ⟨b, fun x => by rw [hlow x _ (by omega)]; exact hb x⟩
      · exact Or.inr ⟨o, ho, fun x => by
          rw [hlow x _ (by omega), hlow x _ (by omega)]; exact hoe x⟩
    obtain ⟨G2, out2, hF2, hl2, hf2⟩ := ih (S.erase (S.max' hne))
      (by rw [Finset.card_erase_of_mem (S.max'_mem hne)]; omega) G1 out1 hF1 hf1 hR1
    exact ⟨G2, out2, hF2, by omega, hf2⟩

theorem gl0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g) :
    (∃ b : Bool, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = b) ∨
    (∃ w : ℕ, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = ρ w) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | false =>
        exact Or.inl ⟨false, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | true =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | or =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | true =>
        exact Or.inl ⟨true, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | false =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨!c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
  | mod m => simp at hop
  | maj => simp at hop

theorem gl (n : ℕ) (G : List Gate) (k : ℕ) (g : Gate) (hg : G[k]? = some g)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g)
    (hc : ∀ x : Fin n → Bool,
      (if q < n + k then (W G (List.ofFn x)).getD q false else false) = c) :
    Red n G k := by
  have key : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + k then (W G (List.ofFn x)).getD i false else false) := by
    intro x
    have e := W_spec G (List.ofFn x) k g hg
    rw [List.length_ofFn] at e
    exact e
  rcases gl0 g hop hlen q c hq with ⟨b, hb⟩ | ⟨w, hw⟩
  · exact Or.inl ⟨b, fun x => by
      rw [key x]
      exact hb (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)⟩
  · by_cases hwk : w < n + k
    · exact Or.inr ⟨w, hwk, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact if_pos hwk⟩
    · exact Or.inl ⟨false, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact if_neg hwk⟩

theorem gv0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hnor : g.op ≠ GateOp.or) (q : ℕ) (hq : q ∈ eff g) :
    (g.op = GateOp.and ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = true → ρ q = true) ∨
    (g.op = GateOp.not ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = !ρ q) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    refine Or.inl ⟨rfl, ?_⟩
    intro ρ he
    have hq' : q ∈ inputs := List.mem_of_mem_take hq
    simp only [GateOp.eval] at he
    exact List.all_eq_true.mp he (ρ q) (List.mem_map.mpr ⟨q, hq', rfl⟩)
  | or => exact absurd rfl hnor
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inr ⟨rfl, fun ρ => by simp [GateOp.eval]⟩
  | mod m => simp at hop
  | maj => simp at hop

theorem gl2 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (v p : ℕ) (hvp : v ≠ p) (hv : v ∈ eff g) (hp : p ∈ eff g) :
    (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v && ρ p)) ∨
    (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v || ρ p)) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
    · simp [eff, GateOp.eval] at hv hp
      left
      intro ρ
      rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
      · exact absurd rfl hvp
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.and_comm]
      · exact absurd rfl hvp
    · simp at hlen
  | or =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
    · simp [eff, GateOp.eval] at hv hp
      right
      intro ρ
      rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
      · exact absurd rfl hvp
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.or_comm]
      · exact absurd rfl hvp
    · simp at hlen
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
  | mod m => simp at hop
  | maj => simp at hop

theorem Ts_dead (p t : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (hne : p ∉ eff g) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) :
    (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    have e : eff ⟨GateOp.and, inputs⟩ = inputs := List.take_of_length_le hlen
    rw [e] at hne
    simp only [Ts, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hip : i ≠ p := fun h => hne (h ▸ hi)
    simp only [Function.comp, hip, if_false]
    exact h1 i hip
  | or =>
    have e : eff ⟨GateOp.or, inputs⟩ = inputs := List.take_of_length_le hlen
    rw [e] at hne
    simp only [Ts, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hip : i ≠ p := fun h => hne (h ▸ hi)
    simp only [Function.comp, hip, if_false]
    exact h1 i hip
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [Ts, GateOp.eval]
    · have ha : a ≠ p := by
        intro h
        apply hne
        simp [eff, GateOp.eval, h]
      simp [Ts, GateOp.eval, ha, h1 a ha]
  | mod m => simp at hop
  | maj => simp at hop

theorem pos_set (l : List Gate) (p : Gate → Bool) :
    ∃ S : Finset ℕ, S.card = (l.filter p).length ∧
      ∀ i ∈ S, ∃ g, l[i]? = some g ∧ p g = true := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨S, hS, hSp⟩ := ih
    have hlt : ∀ i ∈ S, i < l.length := by
      intro i hi
      obtain ⟨g, hg, _⟩ := hSp i hi
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hg
      cases hg
    by_cases hpa : p a = true
    · refine ⟨insert l.length S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun hm => by have := hlt _ hm; omega), hS]
        simp [List.filter_append, hpa]
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact ⟨a, by simp, hpa⟩
        · obtain ⟨g, hg, hpg⟩ := hSp i hi
          exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩
    · refine ⟨S, ?_, ?_⟩
      · rw [hS]; simp [List.filter_append, hpa]
      · intro i hi
        obtain ⟨g, hg, hpg⟩ := hSp i hi
        exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩

theorem eff_Rn (v B : ℕ) (g : Gate) :
    eff (Rn v B g) = (eff g).map fun i => if i = v then B else i := by
  simp [eff, Rn, List.map_take]


theorem main (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ) (hF : FanInTwo C)
    (hj : j < C.gates.length)
    (hjv : (eff (NestedCover.gateAt C j)).contains v.val = true)
    (hjor : (NestedCover.gateAt C j).op ≠ GateOp.or)
    (hcard : 3 ≤ (Finset.filter (fun k => k ≠ j ∧
      ((eff (NestedCover.gateAt C k)).contains v.val = true ∨
        j < k ∧ (eff (NestedCover.gateAt C k)).contains (n + j) = true))
        (Finset.range C.gates.length)).card)
    (hnc : ∃ x y : Fin n → Bool,
      circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false)) :
    ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s := by
  classical
  have hF0 : FT C.gates := hF
  have hf : ∀ x : Fin n → Bool,
      (W C.gates (List.ofFn x)).getD C.output false = circuitFun n C x := fun x => rfl
  obtain ⟨B, hB⟩ : ∃ B, B = n + C.gates.length := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = C.gates.map (Rn v.val B) := ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ o1, o1 = if C.output = v.val then B else C.output := ⟨_, rfl⟩
  have hlen1 : G1.length = C.gates.length := by rw [hG1, List.length_map]
  have hS : ∀ x : Fin n → Bool, ∀ m, m ≠ v.val →
      (W G1 (List.ofFn x)).getD m false
        = (W C.gates (List.ofFn (Function.update x v false))).getD m false := by
    intro x
    rw [hG1, hB]
    apply subst C.gates n v.val v.isLt (List.ofFn x) (List.ofFn (Function.update x v false))
      (by simp) (by simp)
    · intro i hi hiv
      rw [ofFn_getD x i hi, ofFn_getD (Function.update x v false) i hi,
        Function.update_apply, if_neg (fun h => hiv (congrArg Fin.val h))]
    · rw [ofFn_getD (Function.update x v false) v.val v.isLt, Function.update_apply, if_pos rfl]
  have hC1 : ∀ x : Fin n → Bool,
      (W G1 (List.ofFn x)).getD o1 false = circuitFun n C (Function.update x v false) := by
    intro x
    rw [← hf (Function.update x v false)]
    by_cases ho : C.output = v.val
    · rw [ho1, if_pos ho, ho, W_oob G1 (List.ofFn x) B (by rw [List.length_ofFn]; omega),
        W_inp C.gates (List.ofFn (Function.update x v false)) v.val
          (by rw [List.length_ofFn]; exact v.isLt),
        ofFn_getD (Function.update x v false) v.val v.isLt, Function.update_apply, if_pos rfl]
    · rw [ho1, if_neg ho]
      exact hS x C.output ho
  have hF1 : FT G1 := by
    intro g hg
    rw [hG1] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hF0 g0 hg0
    exact ⟨h0.1, by simp only [Rn, List.length_map]; exact h0.2⟩
  have hget1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → G1[k]? = some (Rn v.val B g) := by
    intro k g hg
    rw [hG1, List.getElem?_map, hg]; rfl
  have hklt : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k < C.gates.length := by
    intro k g hg
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hRn1 : ∀ g ∈ C.gates, (Rn v.val B g).op ∈
      ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (Rn v.val B g).inputs.length ≤ 2 := by
    intro g hg
    have h0 := hF0 g hg
    exact ⟨h0.1, by simp only [Rn, List.length_map]; exact h0.2⟩
  have hA : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → v.val ∈ eff g → Red n G1 k := by
    intro k g hg hv
    have hm := hRn1 g (List.mem_of_getElem? hg)
    have hk := hklt k g hg
    refine gl n G1 k (Rn v.val B g) (hget1 k g hg) hm.1 hm.2 B false ?_ ?_
    · rw [eff_Rn]
      exact List.mem_map.mpr ⟨v.val, hv, if_pos rfl⟩
    · intro x
      exact if_neg (by omega)
  have hgat : ∀ k, k < C.gates.length → C.gates[k]? = some (NestedCover.gateAt C k) := by
    intro k hk
    have e : NestedCover.gateAt C k = C.gates[k] := by
      unfold NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    rw [e]
    exact List.getElem?_eq_getElem hk
  -- gate j becomes a constant
  obtain ⟨g, hg⟩ : ∃ g, g = NestedCover.gateAt C j := ⟨_, rfl⟩
  have hgj : C.gates[j]? = some g := hg ▸ hgat j hj
  have hgC : g ∈ C.gates := List.mem_of_getElem? hgj
  have hgv : v.val ∈ eff g := by rw [hg]; simpa using hjv
  have hgor : g.op ≠ GateOp.or := hg ▸ hjor
  have hkey1 : ∀ x : Fin n → Bool, (W G1 (List.ofFn x)).getD (n + j) false =
      (Rn v.val B g).op.eval ((Rn v.val B g).inputs.map fun i =>
        if i < n + j then (W G1 (List.ofFn x)).getD i false else false) := by
    intro x
    have e := W_spec G1 (List.ofFn x) j _ (hget1 j g hgj)
    rw [List.length_ofFn] at e
    exact e
  have hBeff : B ∈ eff (Rn v.val B g) := by
    rw [eff_Rn]
    exact List.mem_map.mpr ⟨v.val, hgv, if_pos rfl⟩
  have hBj : ¬ B < n + j := by omega
  obtain ⟨c, hc⟩ : ∃ c : Bool, ∀ x : Fin n → Bool,
      (W G1 (List.ofFn x)).getD (n + j) false = c := by
    rcases gv0 (Rn v.val B g) (hRn1 g hgC).1 hgor B hBeff with ⟨_, hand⟩ | ⟨_, hnot⟩
    · refine ⟨false, fun x => ?_⟩
      rw [hkey1 x]
      apply Bool.eq_false_iff.mpr
      intro he
      have h2 := hand _ he
      rw [if_neg hBj] at h2
      cases h2
    · refine ⟨true, fun x => ?_⟩
      rw [hkey1 x, hnot, if_neg hBj]
      rfl
  have hRj : Red n G1 j := Or.inl ⟨c, hc⟩
  -- the set of eliminated gates
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = Finset.filter (fun k => k ≠ j ∧
      ((eff (NestedCover.gateAt C k)).contains v.val = true ∨
        j < k ∧ (eff (NestedCover.gateAt C k)).contains (n + j) = true))
        (Finset.range C.gates.length) := ⟨_, rfl⟩
  rw [← hSdef] at hcard
  have hjS : j ∉ S := by
    intro h
    rw [hSdef, Finset.mem_filter] at h
    exact h.2.1 rfl
  have hT : ∀ i ∈ insert j S, i < G1.length ∧ Red n G1 i := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨by omega, hRj⟩
    · rw [hSdef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hil, _, hcase⟩ := hi
      refine ⟨by omega, ?_⟩
      have hk := hgat i hil
      rcases hcase with hv | ⟨hji, hp⟩
      · exact hA i _ hk (by simpa using hv)
      · have hm := hRn1 _ (List.mem_of_getElem? hk)
        refine gl n G1 i _ (hget1 i _ hk) hm.1 hm.2 (n + j) c ?_ ?_
        · rw [eff_Rn]
          exact List.mem_map.mpr ⟨n + j, by simpa using hp, if_neg (by have := v.isLt; omega)⟩
        · intro x
          rw [if_pos (by omega)]
          exact hc x
  have hTc : 4 ≤ (insert j S).card := by
    rw [Finset.card_insert_of_notMem hjS]; omega
  obtain ⟨G', out', hF', hl', hf'⟩ :=
    iter n (fun x => circuitFun n C (Function.update x v false)) hnc (insert j S).card
      (insert j S) rfl G1 o1 hF1 hC1 hT
  refine ⟨G'.length, ?_, ⟨G', out'⟩, hF', le_refl _, hf'⟩
  change G'.length + 4 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_1972.Donor4113

theorem PEqualNP.Outside.L_meta_1972.Donor4113 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x6.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x6.inputs).contains x5;   have x6 : Fin x1 → ℕ → Finset ℕ := fun (x6 : Fin x1) (x7 : ℕ) => {x8 ∈ Finset.range x2.gates.length | x8 ≠ x7 ∧ (x5 (↑x6) (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) = Bool.true ∨ x7 < x8 ∧ x5 (x1 + x7) (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) = Bool.true)};   PEqualNP.MetaComplexity.FanInTwo x2 → x4 < x2.gates.length ∧ x5 (↑x3) (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x6 x3 x4).card → (∃ (x9 : Fin x1 → Bool) (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x9 x3 Bool.false) ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x10 x3 Bool.false)) → ∃ (x10 : ℕ), x10 + (4 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x11 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x11 x3 Bool.false)) x10 := by
  intro n C v j
  dsimp only
  intro hF hJ hnc
  obtain ⟨hj, hjv, hjor, hcard⟩ := hJ
  exact PEqualNP.Outside.L_meta_1972.Donor4113.main n C v j hF hj hjv hjor hcard hnc

-- The absorbing-wire elimination lemma is from jerry22717, PR 77, with the original credits below.
namespace PEqualNP.Outside.L_meta_1972.Donor4115
namespace Absorb193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire semantics and constant propagation below reuse the project’s
-- Shannon, Support and Elim helpers within the allowed dependency set.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]


def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)


def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]


def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)


theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj


def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def reader (n h : ℕ) (p : Gate × ℕ) : Bool :=
  decide (h < n + p.2) && (normGate p.1).inputs.contains h

-- Every counted reader sees the fixed false wire and emits no gate.
theorem savings (n m h : ℕ) (gs : List Gate) (j : ℕ) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, Ok g) (hh : h < acc.1.length)
    (fixed : acc.1.getD h (.inl false) = .inl false) :
    (elim m (gs.map normGate) acc).2.length + (gs.zipIdx j).countP (reader n h)
      ≤ acc.2.length + gs.length := by
  induction gs generalizing acc j with
  | nil => simp [elim]
  | cons g gs ih =>
    let a := elimStep m acc (normGate g)
    have tail := ih (j+1) a (fun g hg => ok g (by simp [hg]))
      (by simp [a, elimStep]; omega)
      (by change (acc.1 ++ [_]).getD h _ = _; rw [List.getD_append _ _ _ _ hh, fixed])
    change (elim m (gs.map normGate) a).2.length + _ ≤ _
    rw [List.zipIdx_cons, List.countP_cons, List.length_cons]
    let r := simplify (normGate g).op (m + acc.2.length)
      ((normGate g).inputs.map fun i => acc.1.getD i (.inl false))
    have ha : a.2.length = acc.2.length + r.1.toList.length := List.length_append
    by_cases hit : reader n h (g,j) = true
    · have mem : h ∈ (normGate g).inputs := by simpa [reader] using (Bool.and_eq_true_iff.mp hit).2
      have ng := normGate_nok g (ok g (by simp))
      have zero : r.1 = none := simplify_count _ _ _ ng.1.1
        (by simpa using ng.1.2) (fun e => by simpa using ng.2 e)
        ⟨false, List.mem_map.mpr ⟨h, mem, fixed⟩⟩
      simp [zero] at ha
      simp [hit]; omega
    · have := toList_length_le r.1
      simp [hit]; omega

def seed (m h : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => if i.val = h then .inl false else .inr i.val

theorem seed_inv (w : List Bool) (m h : ℕ) (hw : w.length = m)
    (hz : w.getD h false = false) : Inv m w w (seed m h, []) := by
  refine ⟨by simp [seed, hw], fun i => ?_⟩
  by_cases hi : i < m
  · by_cases e : i = h
    · subst i; simpa [seed, hi, Stat.Valid, Stat.val] using hz
    · simp [seed, hi, e, Stat.Valid, Stat.val, wiresFrom]
  · have : m ≤ i := by omega
    simpa [seed, hi, Stat.Valid, Stat.val] using (List.getD_eq_default w false (by omega : w.length ≤ i))

-- Reattach h to the residual output using a single final gate.
def finish (h : ℕ) : Stat → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [h]⟩
  | .inr j => ⟨.or, [h,j]⟩

theorem finish_ok (h : ℕ) (s : Stat) : Ok (finish h s) := by
  cases s with
  | inl b => cases b <;> simp [finish, Ok]
  | inr j => simp [finish, Ok]

theorem finish_eval (w : List Bool) (h : ℕ) (s : Stat) :
    (wiresFrom [finish h s] w).getD w.length false = (w.getD h false || s.val w) := by
  cases s with
  | inl b => cases b <;> simp [finish, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finish, wiresFrom, GateOp.eval, Stat.val]

end Absorb193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Absorb193

theorem absorbing : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ C.size + 1 := by
  intro n C h ok absorbs
  have form (g : Gate) : (GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs
      (g.inputs.take 1) (fun _ => g.inputs) g.inputs) = (normGate g).inputs := by
    cases g with | mk op ins => cases op <;> rfl
  simp_rw [form]
  change ∃ D, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
    D.size + C.gates.zipIdx.countP (reader n h) ≤ C.size + 1
  by_cases existsH : h < n + C.gates.length
  swap
  · refine ⟨C, ok, rfl, ?_⟩
    have z : C.gates.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬h < n + p.2 by omega]
    omega
  let pre := C.gates.take (h+1-n)
  let rest := C.gates.drop (h+1-n)
  have splitG : pre ++ rest = C.gates := List.take_append_drop ..
  let m := n + pre.length
  have hpLen : pre.length = min (h+1-n) C.gates.length := List.length_take ..
  have hm : h < m := by dsimp [m]; omega
  let init : List Stat × List Gate := (seed m h, [])
  let pass := elim m (rest.map normGate) init
  let s := pass.1.getD C.output (.inl false)
  let D : Circuit := ⟨(pre ++ pass.2) ++ [finish h s], m + pass.2.length⟩
  have preOk (g) (hg : g ∈ pre) : Ok g := ok g (splitG ▸ List.mem_append_left _ hg)
  have restOk (g) (hg : g ∈ rest) : Ok g := ok g (splitG ▸ List.mem_append_right _ hg)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ (pre ++ pass.2) ++ [finish h s] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hp | hr) | rfl)
    · exact preOk g hp
    · exact elim_ok m _ init (by simp [init]) g hr
    · exact finish_ok h s
  · funext x
    let y := List.ofFn x
    let w := wiresFrom pre y
    let v := wiresFrom pass.2 w
    have lw : w.length = m := by simp [w, y, length_wiresFrom, m]
    have lv : v.length = m + pass.2.length := by simp [v, length_wiresFrom, lw]
    have hh : h < w.length := lw ▸ hm
    have old : C.wires y = wiresFrom rest w := by rw [wires_eq, ← splitG, wiresFrom_append]
    have origH : (C.wires y).getD h false = w.getD h false := by rw [old, getD_wiresFrom _ _ _ hh]
    have out : circuitFun n D x = (w.getD h false || s.val v) := by
      change (wiresFrom ((pre ++ pass.2) ++ [finish h s]) y).getD (m + pass.2.length) false = _
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom [finish h s] v).getD _ false = _
      rw [← lv, finish_eval, getD_wiresFrom _ _ _ hh]
    rw [out]
    cases hc : w.getD h false with
    | true => simpa using (absorbs x (origH.trans hc)).symm
    | false =>
      have hi := inv_elim m w lw (rest.map normGate) w init
        (by intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
            exact (normGate_nok _ (restOk _ hg')).1)
        (seed_inv w m h lw hc)
      have eq := (hi.2 C.output).2
      rw [wiresFrom_norm, ← old] at eq
      simpa [s, v, pass, circuitFun, Circuit.eval, y] using eq
  · have zero : pre.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬ h < n + p.2 by omega]
    have save := savings n m h rest pre.length init restOk
      (by simpa [init, seed] using hm) (by simp [init, seed, hm])
    change pass.2.length + _ ≤ [].length + rest.length at save
    change ((pre ++ pass.2) ++ [finish h s]).length + _ ≤ C.gates.length + 1
    rw [← splitG, List.zipIdx_append, List.countP_append, zero]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
    omega
namespace Sole
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def reads (v : Nat) (g : Gate) := (pins g).contains v
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma read_only {v : Nat} {gs : List Gate} {a b : Gate}
    (le : (gs.filter (reads v)).length ≤ 1) (ha : a ∈ gs.filter (reads v))
    (hb : b ∈ gs) (read : v ∈ pins b) : b = a := by
  have both : b ∈ gs.filter (reads v) := List.mem_filter.mpr ⟨hb,List.contains_iff_mem.mpr read⟩
  generalize gs.filter (reads v) = ls at le ha both
  cases ls with
  | nil => simp at ha
  | cons c t =>
    have e : t = [] := by simpa using le
    subst t
    simpa using (List.mem_singleton.mp both).trans (List.mem_singleton.mp ha).symm

lemma raw {n} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    (List.ofFn x ++ tail).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append,i.isLt]

lemma same_pin {n} (x y : Fin n → Bool) (tail : List Bool) (i : Nat)
    (h : ∀ j : Fin n, i=j.val → x j=y j) :
    (List.ofFn x ++ tail).getD i false = (List.ofFn y ++ tail).getD i false := by
  by_cases b : i<n
  · let j : Fin n := ⟨i,b⟩
    exact (raw x tail j).trans ((h j rfl).trans (raw y tail j).symm)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,b]

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

lemma parallel_wires {n} (x y : Fin n → Bool) (gs : List Gate)
    (step : ∀ g ∈ gs, ∀ rest, atBank g (List.ofFn x ++ rest) = atBank g (List.ofFn y ++ rest))
    (t : List Bool) : ∃ suffix, (Circuit.mk gs 0).wires (List.ofFn x ++ t) = List.ofFn x ++ suffix ∧
      (Circuit.mk gs 0).wires (List.ofFn y ++ t) = List.ofFn y ++ suffix := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have eq := step g (by simp) t
    obtain ⟨s,hx,hy⟩ := ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) (t++[atBank g (List.ofFn x ++ t)])
    refine ⟨s,?_,?_⟩
    · change (Circuit.mk gs 0).wires ((List.ofFn x ++ t) ++ [atBank g _]) = _
      simpa only [List.append_assoc] using hx
    · change (Circuit.mk gs 0).wires ((List.ofFn y ++ t) ++ [atBank g _]) = _
      rw [←eq]
      simpa only [List.append_assoc] using hy

lemma lockstep {n} (C : Circuit) (fan : FanInTwo C) (g : Gate) (x y : Fin n → Bool)
    (out : n ≤ C.output)
    (reader : ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q = g)
    (agree : ∀ tail, atBank g (List.ofFn x ++ tail) = atBank g (List.ofFn y ++ tail)) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have step (q) (mem : q ∈ C.gates) (tail) :
      atBank q (List.ofFn x ++ tail)=atBank q (List.ofFn y ++ tail) := by
    by_cases eq : q=g
    · exact eq ▸ agree tail
    apply eval_from_pins _ _ _ (fan _ mem)
    intro i hi
    apply same_pin
    rintro j rfl
    by_contra different
    exact eq (reader j different q mem hi)
  obtain ⟨s,hx,hy⟩ := parallel_wires x y _ step []
  simp only [List.append_nil] at hx hy
  change ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD _ false =
    ((Circuit.mk C.gates 0).wires (List.ofFn y)).getD _ false
  rw [hx,hy]
  exact same_pin x y s C.output (fun j h => by have := j.isLt; omega)

section Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)}
def girthFive (G : SimpleGraph (Fin n)) := ∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length

lemma triangle (h : girthFive G) {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w)
    (wu : G.Adj w u) : False := by
  let p := Walk.cons uv (Walk.cons vw (Walk.cons wu Walk.nil))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have a := uv.ne
    have b := vw.ne
    have c := wu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
  have bound := h u p hp
  simp [p] at bound

lemma square (h : girthFive G) {u a w b : Fin n} (ua : G.Adj u a) (aw : G.Adj a w)
    (wb : G.Adj w b) (bu : G.Adj b u) (uw : u ≠ w) (ab : a ≠ b) : False := by
  let p := Walk.cons ua (Walk.cons aw (Walk.cons wb (Walk.cons bu Walk.nil)))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have h1 := ua.ne
    have h2 := aw.ne
    have h3 := wb.ne
    have h4 := bu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,h1,h2,h3,h4,uw,ab,
      Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm uw,Ne.symm ab]
  have bound := h u p hp
  simp [p] at bound

lemma private_neighbor (h : girthFive G) {u w a b : Fin n} (uw : u ≠ w)
    (ua : G.Adj u a) (ub : G.Adj u b) (ab : a ≠ b) :
    ∃ r, G.Adj u r ∧ r ≠ w ∧ ¬ G.Adj w r := by
  by_cases aw : a = w
  · subst w
    exact ⟨b,ub,ab.symm,fun e => triangle h ua e ub.symm⟩
  by_cases bw : b = w
  · subst w
    exact ⟨a,ua,aw,fun e => triangle h ub e ua.symm⟩
  by_cases wa : G.Adj w a
  · exact ⟨b,ub,bw,fun e => square h ua wa.symm e ub.symm uw ab⟩
  · exact ⟨a,ua,aw,wa⟩
end Geometry
open SimpleGraph
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))

lemma mark_true (S : Finset (Fin n)) :
    graphFun G A (mark S) = true ↔
      (∃ i ∈ A, i ∈ S) ∨ (∃ i j, G.Adj i j ∧ i ∈ S ∧ j ∈ S) := by
  simp [graphFun,mark]

lemma off_pair (a b : Fin n) (ao : a ∉ A) (bo : b ∉ A) (ab : ¬G.Adj a b) :
    graphFun G A (mark {a,b}) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  rcases (mark_true G A _).mp yes with ⟨i,hi,mem⟩|⟨i,j,adj,hi,hj⟩
  · rcases Finset.mem_insert.mp mem with rfl|e
    · exact ao hi
    · exact bo (Finset.mem_singleton.mp e ▸ hi)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;>
      first | exact adj.ne rfl | exact ab adj | exact ab adj.symm

lemma off_one (a : Fin n) (ao : a ∉ A) : graphFun G A (mark {a}) = false := by
  simpa using off_pair G A a a ao ao (G.loopless.irrefl a)

lemma on_edge {a b : Fin n} (ab : G.Adj a b) (S : Finset (Fin n)) (aS : a∈S) (bS : b∈S) :
    graphFun G A (mark S) = true :=
  (mark_true G A S).mpr (Or.inr ⟨a,b,ab,aS,bS⟩)

lemma inserts_differ (S : Finset (Fin n)) (u i : Fin n)
    (diff : mark S i ≠ mark (insert u S) i) : i = u := by
  by_contra ne
  exact diff (by simp [mark,ne])

lemma not_raw_output (C : Circuit) (out : circuitFun n C = graphFun G A)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ i j, G.Adj i j) :
    n ≤ C.output := by
  by_contra! small
  let k : Fin n := ⟨C.output,small⟩
  have projected (x : Fin n → Bool) : graphFun G A x = x k := by
    rw [←out]
    change ((Absorb193.wiresFrom C.gates (List.ofFn x)).getD k.val false) = _
    rw [Absorb193.getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  by_cases hk : k ∈ A
  · obtain ⟨a,b,adj⟩ := edge
    have ak : k ≠ a := fun e => apart a b adj (e ▸ hk)
    have bk : k ≠ b := fun e => apart b a adj.symm (e ▸ hk)
    have yes := on_edge G A adj {a,b} (by simp) (by simp)
    rw [projected] at yes
    simp [mark,ak,bk] at yes
  · have no := off_one G A k hk
    rw [projected] at no
    simp [mark] at no

lemma two_neighbors (u : Fin n) (degree : (G.neighborSet u).ncard = 3) :
    ∃ a b, G.Adj u a ∧ G.Adj u b ∧ a ≠ b := by
  have more : 1 < (G.neighborFinset u).card := by
    change 1 < (G.neighborSet u).toFinset.card
    rw [← Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp more
  exact ⟨a,b,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hb,ab⟩


lemma count_read {n} (i : Fin n) (gs : List Gate) (fan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (k : Nat) :
    (gs.zipIdx k).countP (Absorb193.reader n i.val) = (gs.filter (reads i.val)).length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,len⟩ := fan g (by simp)
    have same : Absorb193.reader n i.val (g,k) = reads i.val g := by
      have lt : i.val < n+k := by have := i.isLt; omega
      obtain ⟨o,l⟩ := g
      change o = .and ∨ o = .or ∨ o = .not at op
      change l.length ≤ 2 at len
      rcases op with rfl|rfl|rfl <;> simp [Absorb193.reader,Absorb193.normGate,reads,pins,GateOp.eval,lt,List.take_of_length_le len]
    rw [List.zipIdx_cons,List.countP_cons, same]
    have tail := ih (fun z hz => fan z (List.mem_cons_of_mem _ hz)) (k+1)
    rw [tail]
    by_cases on : reads i.val g = true <;> simp [on,List.filter_cons]

lemma absorbing_reads (C : Circuit) (minimal : IsMinimalCircuit n C)
    (correct : circuitFun n C = graphFun G A) (v : Fin n) (mem : v ∈ A) :
    (C.gates.filter (reads v.val)).length ≤ 1 := by
  have fixed (x : Fin n → Bool) (on : (C.wires (List.ofFn x)).getD v.val false = true) :
      circuitFun n C x = true := by
    change (Absorb193.wiresFrom C.gates (List.ofFn x)).getD v.val false = true at on
    rw [Absorb193.getD_wiresFrom _ _ _ (by simp)] at on
    have xv : x v = true := by simpa [List.getD_eq_getElem?_getD] using on
    rw [correct]
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inl ⟨v,mem,xv⟩
  obtain ⟨D,fan,eq,bound⟩ := absorbing n C v.val minimal.1 fixed
  have smaller := minimal.2 D fan eq
  have count : (C.gates.zipIdx.countP (Absorb193.reader n v.val)) =
      (C.gates.filter (reads v.val)).length := count_read v _ minimal.1 0
  have equal_reader (p : Gate × Nat) :
      (decide (v.val < n+p.2) && (GateOp.casesOn (motive := fun _ => List Nat) p.1.op
        p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains v.val)
        = Absorb193.reader n v.val p := by
    rcases p with ⟨⟨o,ins⟩,j⟩
    cases o <;> rfl
  simp_rw [equal_reader] at bound
  change D.size + C.gates.zipIdx.countP (Absorb193.reader n v.val) ≤ C.size + 1 at bound
  rw [count] at bound
  omega


lemma pair_eval (u v : Fin n) (g : Gate) (ord : g.inputs.Perm [u.val,v.val]) (join : Bool)
    (op : g.op = if join then .or else .and) (x : Fin n → Bool) (t : List Bool) :
    atBank g (List.ofFn x ++ t) = if join then x u || x v else x u && x v := by
  rcases List.perm_pair.mp ord with e|e <;> cases join <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] at op ⊢ <;>
    simp only [atBank,e,op,List.map_cons,List.map_nil,raw,GateOp.eval] <;>
    simp [Bool.and_comm,Bool.or_comm]

lemma main (C : Circuit) (u : Fin n) (uout : u ∉ A)
    (degree : (G.neighborSet u).ncard = 3)
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ i j, G.Adj i j)
    (small : IsMinimalCircuit n C) (correct : circuitFun n C = graphFun G A)
    (few : (C.gates.filter (reads u.val)).length ≤ 1) (g : Gate)
    (mem : g ∈ C.gates.filter (reads u.val)) (v : Fin n) (vu : v≠u)
    (ord : g.inputs.Perm [u.val,v.val]) : g.op ≠ .and ∧ g.op ≠ .or := by
  have out := not_raw_output G A C correct apart edge
  obtain ⟨a,b,ua,ub,ab⟩ := two_neighbors G u degree
  have short : girthFive G := fun i p hp => le_trans (by decide : 5 ≤ 7) (girth i p hp)
  obtain ⟨r,ur,rv,vr⟩ := private_neighbor short vu.symm ua ub ab
  have ur' := ur.ne
  have rout : r ∉ A := apart _ _ ur.symm
  have deny (x y : Fin n → Bool) (readers :
      ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q=g)
      (same : ∀ t, atBank g (List.ofFn x ++ t) = atBank g (List.ofFn y ++ t))
      (changeVal : graphFun G A x ≠ graphFun G A y) : False := by
    have eq := lockstep C small.1 g x y out readers same
    change circuitFun n C x = circuitFun n C y at eq
    rw [correct] at eq
    exact changeVal eq
  have only_u (S : Finset (Fin n)) (i : Fin n) (diff : mark S i ≠ mark (insert u S) i) :
      ∀ q ∈ C.gates, i.val ∈ pins q → q=g := by
    obtain rfl := inserts_differ S u i diff
    exact fun q h r => read_only few mem h r
  constructor
  · intro op
    refine deny (mark {r}) (mark (insert u {r})) (only_u _) ?_ ?_
    · intro t
      rw [pair_eval u v g ord false op, pair_eval u v g ord false op]
      simp [mark,rv.symm,vu]
    · rw [off_one G A r rout,on_edge G A ur _ (by simp) (by simp)]
      decide
  · intro op
    by_cases va : v∈A
    · have vg : v.val ∈ pins g := by
        rcases List.perm_pair.mp ord with e|e <;> simp [pins,op,e,GateOp.eval]
      have vm : g ∈ C.gates.filter (reads v.val) :=
        List.mem_filter.mpr ⟨(List.mem_filter.mp mem).1,List.contains_iff_mem.mpr vg⟩
      have vf := absorbing_reads G A C small correct v va
      refine deny (mark {u}) (mark {v}) ?_ ?_ ?_
      · intro i diff q h r
        by_cases iu : i=u
        · subst i; exact read_only few mem h r
        by_cases iv : i=v
        · subst i; exact read_only vf vm h r
        exact False.elim (diff (by simp [mark,iu,iv]))
      · intro t
        rw [pair_eval u v g ord true op,pair_eval u v g ord true op]
        simp [mark]
      · have on := (mark_true G A {v}).mpr (Or.inl ⟨v,va,by simp⟩)
        rw [off_one G A u uout,on]; decide
    · refine deny (mark {v,r}) (mark (insert u {v,r})) (only_u _) ?_ ?_
      · intro t
        rw [pair_eval u v g ord true op,pair_eval u v g ord true op]
        simp [mark]
      · rw [off_pair G A v r va rout vr,on_edge G A ur _ (by simp) (by simp)]
        decide

end Sole
end PEqualNP.Outside.L_meta_1972.Donor4115

theorem PEqualNP.Outside.L_meta_1972.Donor4115 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1),   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x8 : Fin x1) => List.filter (x7 ↑x8) x5.gates;   x6 ∉ x4 → (x2.neighborSet x6).ncard = (3 : ℕ) → (∀ (x11 : Fin x1) (x12 : x2.Walk x11 x11), x12.IsCycle → (7 : ℕ) ≤ x12.length) → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (x8 x6).length ≤ (1 : ℕ) → ∀ x17 ∈ x8 x6, ∀ (x19 : Fin x1), x19 ≠ x6 → x17.inputs.Perm [↑x6, ↑x19] → x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or := by
  intro n G dec A C u
  dsimp only
  exact PEqualNP.Outside.L_meta_1972.Donor4115.Sole.main G A C u

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count distinct gates exposed to one pinned input and the first forced constant.
-- A sole binary reader with two distinct raw inputs is excluded separately.
theorem PEqualNP.Outside.L_meta_1972.assemble
    (propagate : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ),
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let near (v : Fin n) (j : ℕ) :=
      (Finset.range C.gates.length).filter fun k =>
        k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
          j < k ∧ reads (n+j) (gateAt C k) = true)
    FanInTwo C → (j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card) →
    (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠
      circuitFun n C (Function.update y v false)) →
    ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    (noRaw : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (v : Fin n),
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let readers (v : Fin n) := C.gates.filter (reads v.val)
    v ∉ A → (G.neighborSet v).ncard = 3 →
    (∀ a (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) →
    (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
    IsMinimalCircuit n C → circuitFun n C = graphFun G A →
    (readers v).length ≤ 1 →
    ∀ g ∈ readers v, ∀ p : Fin n, p ≠ v →
      g.inputs.Perm [v.val,p.val] → g.op ≠ .and ∧ g.op ≠ .or)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := graphFun G A
    let reads (a : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
    let near (v : Fin n) (j : ℕ) :=
      (Finset.range C.gates.length).filter fun k =>
        k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
          j < k ∧ reads (n+j) (gateAt C k) = true)
    let readers (v : Fin n) := C.gates.filter (reads v.val)
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    7 ≤ G.egirth →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = f →
    (∀ v ∉ A, (readers v).length ≤ 3 ∧
      ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
    (∃ v ∉ A, (readers v).length ≤ 1 ∧ (∀ g ∈ readers v, ∀ p : Fin n, p ≠ v →
      g.inputs.Perm [v.val,p.val] → g.op ≠ .and ∧ g.op ≠ .or)) →
    (¬ (∃ v ∉ A, ∃ j : ℕ, j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card)) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A,
      let r := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      r.length ≤ 3 ∧ (r.length = 3 → ∀ g ∈ r, g.op = .or)) →
    (∃ v ∉ A, (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s := by
  classical
  intro n G A f C degree girth unmarked edge description fan computes minSize readBound few
  let reads (a : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains a
  let near (v : Fin n) (j : ℕ) :=
    (Finset.range C.gates.length).filter fun k =>
      k ≠ j ∧ (reads v.val (gateAt C k) = true ∨
        j < k ∧ reads (n+j) (gateAt C k) = true)
  have same : graphFun G A = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [description x]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases hit : ∃ v ∉ A, ∃ j : ℕ, j < C.gates.length ∧ reads v.val (gateAt C j) = true ∧
      (gateAt C j).op ≠ .or ∧ 3 ≤ (near v j).card
  · obtain ⟨v,vm,j,jlt,rin,nonOr,many⟩ := hit
    have degree' (z : Fin n) (hz : z ∉ A) : (G.neighborFinset z).card = 3 := by
      change G.degree z = 3
      rw [← G.ncard_neighborSet]
      exact degree z hz
    obtain ⟨a,ha⟩ := Finset.card_pos.mp
      (show 0 < (G.neighborFinset v).card by rw [degree' v vm]; decide)
    have va := (G.mem_neighborFinset v a).mp ha
    have am := unmarked a v va.symm
    have hmem : v ∈ G.neighborFinset a := (G.mem_neighborFinset a v).mpr va.symm
    have enough : 0 < ((G.neighborFinset a).erase v).card := by
      rw [Finset.card_erase_of_mem hmem,degree' a am]
      decide
    obtain ⟨b,hb⟩ := Finset.card_pos.mp enough
    obtain ⟨bv,hb'⟩ := Finset.mem_erase.mp hb
    have ab := (G.mem_neighborFinset a b).mp hb'
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a ∨ i = b)
    have x0 : f (Function.update x v false) = false := by
      have hx : Function.update x v false = x := Function.update_eq_self _ _
      rw [hx]
      apply Bool.eq_false_iff.mpr
      intro fail
      rw [description x] at fail
      simp [x] at fail
    have y1 : f (Function.update y v false) = true := by
      apply (description _).mpr
      right
      exact ⟨a,b,ab,by simp [Function.update_of_ne va.ne.symm,y],
        by simp [Function.update_of_ne bv,y]⟩
    obtain ⟨s,hs,D⟩ := propagate n C v j fan ⟨jlt,rin,nonOr,many⟩
      ⟨x,y,by rw [computes,x0,y1]; decide⟩
    exact ⟨v,vm,s,hs,by simpa only [computes] using D⟩
  · have least : IsMinimalCircuit n C := by
      refine ⟨fan,?_⟩
      intro D kind value
      apply minSize D.size
      exact ⟨D,kind,le_rfl,fun x => congrFun (value.trans computes) x⟩
    have wide : 7 ≤ G.egirth := by
      apply SimpleGraph.le_egirth.mpr
      intro v p hc
      exact_mod_cast girth v p hc
    obtain ⟨v,vm,unique⟩ := few
    have reasonable := noRaw n G A C v vm (degree v vm) girth unmarked edge least
      (computes.trans same.symm) unique
    have result := residual n G A C degree wide unmarked edge least (computes.trans same.symm)
      readBound ⟨v,vm,unique,reasonable⟩ hit
    rwa [same] at result
namespace PEqualNP.Outside.L_meta_1972

def Positive : Prop := (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17)

def Residual : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20

theorem residualOfPositive (pos : Positive) : Residual := by
  intro n G inst A C
  dsimp only
  intro deg girth iso edge minC ev rd lone rest
  refine pos n G A (graphFun G A) C deg ?_ iso edge ?_ minC.1 ev ?_ rd ?_
  · intro v p cyc
    exact_mod_cast (SimpleGraph.le_egirth.mp girth v p cyc)
  · intro x
    change (decide _ || decide _) = true ↔ _
    simp
  · rintro s ⟨D,fan,sz,works⟩
    exact (minC.2 D fan ((funext works).trans ev.symm)).trans sz
  · obtain ⟨v,away,l,_⟩ := lone
    exact ⟨v,away,l⟩

theorem neg_equiv : ¬ Positive ↔ ¬ Residual := by
  constructor
  · exact fun h r => h (assemble Donor4113 Donor4115 r)
  · exact fun h p => h (residualOfPositive p)
end PEqualNP.Outside.L_meta_1972
