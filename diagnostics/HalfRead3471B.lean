import PEqualNP.Defs

-- Normal form: reads go back, no degenerate gate, reads sorted.

namespace Sorted3471

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

lemma V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val_aux {n : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) :
    V gs x (n + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (n + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at n pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]


-- Wire renaming after the deletion of gate j.
def sg (n : ℕ) (j : ℕ) (u : ℕ) : ℕ := if n + j < u then u - 1 else u

lemma sg_le (n j u : ℕ) (h : u ≤ n + j) : sg n j u = u := by
  have h' : ¬ n + j < u := by omega
  simp [sg, h']

lemma sg_gt (n j u : ℕ) (h : n + j < u) : sg n j u = u - 1 := by
  simp [sg, h]

def sh (n j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg n j)⟩

def del (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) : List Gate :=
  ((gs.map f).eraseIdx j).map (sh n j)

lemma del_get (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg n j (n + i) = n + i' ∧ (del n f j gs)[i']? = some (sh n j (f g)) ∧
      ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h : i < j
  · refine ⟨i, sg_le n j _ (by omega), ?_, Or.inl ⟨rfl, h⟩⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_, Or.inr ⟨rfl, by omega⟩⟩
    · rw [sg_gt n j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del n f j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh n j (f g) ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

lemma del_back (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (i' : ℕ) (g' : Gate) (h : (del n f j gs)[i']? = some g') :
    ∀ u ∈ g'.inputs, u < n + i' := by
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv n f j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma del_val (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (x : List Bool) (hx : x.length = n)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (hfv : ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x))) :
    ∀ u, u ≠ n + j → V (del n f j gs) x (sg n j u) = V gs x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del n f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < n
    · rw [sg_le n j u (by omega)]
      exact V_in _ _ x u (by omega)
    · obtain ⟨i, rfl⟩ : ∃ i, u = n + i := ⟨u - n, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd, _⟩ := del_get n f j gs i gs[i] hg hij
        rw [hs, gate_val_aux _ x hx i' _ hd (del_back n f j gs hfb i' _ hd),
          gate_val_aux gs x hx i _ hg (hback i _ hg), ← hfv i _ hg]
        simp only [sh, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        exact ih w (hfb i _ hg w hw).1 (hfb i _ hg w hw).2
      · rw [V_out gs x _ (by omega)]
        apply V_out
        rw [hlen]
        unfold sg
        split_ifs <;> omega


def Mon (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i

lemma core (n : ℕ) (gs : List Gate) (out : ℕ) (j : ℕ) (hj : j < gs.length) (f : Gate → Gate)
    (out' : ℕ) (hout : out' ≠ n + j)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i)
    (hfm : ∀ g ∈ gs, (f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (f g).inputs.length ≤ 2)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (hfv : ∀ (x : List Bool), x.length = n → ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x)))
    (hov : ∀ (x : List Bool), x.length = n → V gs x out' = V gs x out) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ Back n gs' ∧ gs'.length < gs.length ∧
      ∀ (x : List Bool), x.length = n → V gs' x o = V gs x out := by
  refine ⟨del n f j gs, sg n j out', ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
    obtain ⟨i, g, hg, rfl, _⟩ := del_inv n f j gs i' g' hi'
    have h := hfm g (List.mem_of_getElem? hg)
    exact ⟨h.1, by simpa [sh] using h.2⟩
  · intro i' g' hi'
    exact del_back n f j gs hfb i' g' hi'
  · have hlen : (del n f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    omega
  · intro x hx
    rw [del_val n f j gs hj x hx hback hfb (hfv x hx) out' hout, hov x hx]

-- Case one: the gate copies wire w.
def f1 (n j w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun u => if u = n + j then w else u)⟩

-- Case two: the gate gj is a constant.
def f2 (n j : ℕ) (gj g : Gate) : Gate :=
  if g.op.eval [] = gj.op.eval [] then ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩
  else if n + j ∈ g.inputs then gj else g

lemma all_filter (W : ℕ → Bool) (a : ℕ) (h : W a = true) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).all id = (l.map W).all id := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro H b ⟨u, hu, rfl⟩
    by_cases hb : u = a
    · subst hb; simpa using h
    · exact H _ ⟨u, ⟨hu, hb⟩, rfl⟩
  · rintro H b ⟨u, ⟨hu, _⟩, rfl⟩
    exact H _ ⟨u, hu, rfl⟩

lemma any_filter (W : ℕ → Bool) (a : ℕ) (h : W a = false) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).any id = (l.map W).any id := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
    exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
  · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
    have hne : u ≠ a := by
      rintro rfl
      rw [h] at hb
      simp at hb
    exact ⟨_, ⟨u, ⟨hu, hne⟩, rfl⟩, hb⟩

lemma f2_val (n j : ℕ) (gj g : Gate) (W : ℕ → Bool)
    (hgj : gj.op = GateOp.and ∨ gj.op = GateOp.or) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : gj.inputs = []) (hW : W (n + j) = gj.op.eval []) :
    (f2 n j gj g).op.eval ((f2 n j gj g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases hgj with h1 | h1 <;> rcases hg with h2 | h2
  · have hc : W (n + j) = true := by rw [hW, h1]; rfl
    have e : f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact all_filter W _ hc _
  · have hc : W (n + j) = true := by rw [hW, h1]; rfl
    by_cases hm : n + j ∈ g.inputs
    · have e : f2 n j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, hc⟩
    · have e : f2 n j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (n + j) = false := by rw [hW, h1]; rfl
    by_cases hm : n + j ∈ g.inputs
    · have e : f2 n j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, by simp [hc]⟩
    · have e : f2 n j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (n + j) = false := by rw [hW, h1]; rfl
    have e : f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact any_filter W _ hc _

lemma f2_cases (n j : ℕ) (gj g : Gate) :
    f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ ∨
    f2 n j gj g = gj ∨ (f2 n j gj g = g ∧ n + j ∉ g.inputs) := by
  unfold f2
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rfl, h2⟩)

lemma shape (n : ℕ) (gs : List Gate) (j : ℕ) (g : Gate) (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hb : ∀ u ∈ g.inputs, u < n + j)
    (hdeg : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    g.inputs = [] ∨ ∃ w, w < n + j ∧
      ∀ (x : List Bool), x.length = n → V gs x (n + j) = V gs x w := by
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact Or.inl rfl
  · right
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · right
    rw [hin] at hdeg
    have hab : a = b := by simpa using hdeg
    subst hab
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · rw [hin] at hlen
    simp at hlen


-- The gate that replaces g when k wires exist.
def T (k : ℕ) (g : Gate) : Gate :=
  if g.op.eval [] = true ∧ g.inputs.any (fun u => decide (k ≤ u)) = true then ⟨GateOp.or, []⟩
  else ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩

def fix : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => T k g :: fix (k + 1) gs

lemma T_cases (k : ℕ) (g : Gate) :
    T k g = ⟨GateOp.or, []⟩ ∨ T k g = ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩ := by
  unfold T
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma T_mon (k : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (T k g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (T k g).inputs.length ≤ 2 := by
  rcases T_cases k g with e | e
  · rw [e]; simp
  · rw [e]; exact ⟨h.1, le_trans (List.length_filter_le _ _) h.2⟩

lemma T_back (k : ℕ) (g : Gate) : ∀ u ∈ (T k g).inputs, u < k := by
  intro u hu
  rcases T_cases k g with e | e
  · rw [e] at hu; simp at hu
  · rw [e] at hu
    simp only [List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2

lemma T_val (w : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hbad : ∀ u, w.length ≤ u → w.getD u false = false := fun u hu =>
    List.getD_eq_default _ _ hu
  rcases hop with h | h
  · by_cases hb : g.inputs.any (fun u => decide (w.length ≤ u)) = true
    · have e : T w.length g = ⟨GateOp.or, []⟩ := by simp [T, h, GateOp.eval, hb]
      rw [e, h]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      rw [List.any_eq_true] at hb
      obtain ⟨u, hu, hk⟩ := hb
      exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by rw [hbad u (by simpa using hk)]; simp⟩
    · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
        simp [T, hb]
      have hall : g.inputs.filter (fun u => decide (u < w.length)) = g.inputs := by
        rw [List.filter_eq_self]
        intro u hu
        by_contra hk
        exact hb (List.any_eq_true.mpr ⟨u, hu, by simpa using hk⟩)
      rw [e]
      simp only [hall]
  · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
      simp [T, h, GateOp.eval]
    rw [e]
    simp only [h, GateOp.eval]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
    · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
      have hlt : u < w.length := by
        by_contra hk
        rw [hbad u (by omega)] at hb
        simp at hb
      exact ⟨_, ⟨u, ⟨hu, hlt⟩, rfl⟩, hb⟩

lemma fix_wires : ∀ (gs : List Gate) (k : ℕ) (w : List Bool), w.length = k →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    wiresFrom (fix k gs) w = wiresFrom gs w := by
  intro gs
  induction gs with
  | nil => intro k w _ _; rfl
  | cons g gs ih =>
    intro k w hk hops
    subst hk
    have h1 : wiresFrom (fix w.length (g :: gs)) w = wiresFrom (fix (w.length + 1) gs)
        (w ++ [(T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)]) := rfl
    have h2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1, h2, T_val w g (hops g (by simp))]
    exact ih _ _ (by simp) (fun g' hg' => hops g' (by simp [hg']))

lemma fix_len : ∀ (gs : List Gate) (k : ℕ), (fix k gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [fix, ih]

lemma fix_mon : ∀ (gs : List Gate) (k : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ g' ∈ fix k gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro k _ g' hg'; simp [fix] at hg'
  | cons g gs ih =>
    intro k hm g' hg'
    simp only [fix, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact T_mon k g (hm g (by simp))
    · exact ih (k + 1) (fun g2 hg2 => hm g2 (by simp [hg2])) g' hg'

lemma fix_back : ∀ (gs : List Gate) (k j : ℕ) (g' : Gate), (fix k gs)[j]? = some g' →
    ∀ u ∈ g'.inputs, u < k + j := by
  intro gs
  induction gs with
  | nil => intro k j g' h; simp [fix] at h
  | cons g gs ih =>
    intro k j g' h u hu
    cases j with
    | zero =>
      simp [fix] at h
      subst h
      exact T_back k g u hu
    | succ j =>
      simp [fix] at h
      have := ih (k + 1) j g' h u hu
      omega


lemma step (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Mon gs) (hback : Back n gs)
    (x1 x0 : List Bool) (h1 : x1.length = n) (h0 : x0.length = n)
    (hne : V gs x1 out ≠ V gs x0 out)
    (hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ Back n gs' ∧ gs'.length < gs.length ∧
      ∀ (x : List Bool), x.length = n → V gs' x o = V gs x out := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmon g hg).1
  obtain ⟨gj, hmem, hdeg⟩ := hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hgj : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  rcases shape n gs j gs[j] hgj (hops _ hmem) (hmon _ hmem).2 (hback j _ hgj) hdeg with hin | ⟨w, hw, hv⟩
  · -- a constant gate
    have hc : ∀ (x : List Bool), x.length = n → V gs x (n + j) = gs[j].op.eval [] := by
      intro x hx
      rw [gate_val_aux gs x hx j _ hgj (hback j _ hgj), hin]
      rfl
    have hout : out ≠ n + j := by
      rintro rfl
      exact hne (by rw [hc x1 h1, hc x0 h0])
    refine core n gs out j hj (f2 n j gs[j]) out hout hback ?_ ?_ ?_ (fun _ _ => rfl)
    · intro g hg
      rcases f2_cases n j gs[j] g with e | e | ⟨e, _⟩
      · rw [e]
        exact ⟨(hmon g hg).1, le_trans (List.length_filter_le _ _) (hmon g hg).2⟩
      · rw [e]; exact hmon _ hmem
      · rw [e]; exact hmon g hg
    · intro i g hg u hu
      rcases f2_cases n j gs[j] g with e | e | ⟨e, hn⟩
      · rw [e] at hu
        simp only [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hback i g hg u hu.1, hu.2⟩
      · rw [e, hin] at hu
        simp at hu
      · rw [e] at hu
        refine ⟨hback i g hg u hu, ?_⟩
        rintro rfl
        exact hn hu
    · intro x hx i g hg
      exact f2_val n j gs[j] g (V gs x) (hops _ hmem) (hops g (List.mem_of_getElem? hg)) hin (hc x hx)
  · -- a copy of wire w
    refine core n gs out j hj (f1 n j w) (if out = n + j then w else out) ?_ hback ?_ ?_ ?_ ?_
    · split_ifs with h
      · omega
      · exact h
    · intro g hg
      exact ⟨(hmon g hg).1, by simpa [f1] using (hmon g hg).2⟩
    · intro i g hg u hu
      simp only [f1, List.mem_map] at hu
      obtain ⟨v, hv', rfl⟩ := hu
      have := hback i g hg v hv'
      split_ifs with h
      · omega
      · exact ⟨this, h⟩
    · intro x hx i g hg
      simp only [f1, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp]
      split_ifs with h
      · rw [h, hv x hx]
      · rfl
    · intro x hx
      split_ifs with h
      · rw [h, hv x hx]
      · rfl

-- Sorting the two reads of a gate.
def srt (g : Gate) : Gate :=
  ⟨g.op, [min (g.inputs.getD 0 0) (g.inputs.getD 1 0), max (g.inputs.getD 0 0) (g.inputs.getD 1 0)]⟩

lemma srt_val (g : Gate) (a b : ℕ) (hin : g.inputs = [a, b])
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (W : ℕ → Bool) :
    (srt g).op.eval ((srt g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases le_total a b with h | h <;> rcases hop with e | e <;>
    simp [srt, hin, e, GateOp.eval, h, Bool.and_comm, Bool.or_comm]

lemma map_wires (f : Gate → Gate) : ∀ (gs : List Gate) (w : List Bool),
    (∀ g ∈ gs, ∀ W : ℕ → Bool,
      (f g).op.eval ((f g).inputs.map W) = g.op.eval (g.inputs.map W)) →
    wiresFrom (gs.map f) w = wiresFrom gs w := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    have h1 : wiresFrom ((g :: gs).map f) w = wiresFrom (gs.map f)
        (w ++ [(f g).op.eval ((f g).inputs.map fun i => w.getD i false)]) := rfl
    have h2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1, h2, h g (by simp) (fun i => w.getD i false)]
    exact ih _ (fun g' hg' => h g' (by simp [hg']))

lemma two (g : Gate) (hlen : g.inputs.length ≤ 2)
    (hnd : ¬ (g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0)) :
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b := by
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rw [hin] at hnd; simp at hnd
  · rw [hin] at hnd; simp at hnd
  · rw [hin] at hnd
    exact ⟨a, b, rfl, fun h => hnd (Or.inr (by simpa using h))⟩
  · rw [hin] at hlen; simp at hlen

lemma base (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Mon gs) (hback : Back n gs)
    (hx : ∃ x1 x0 : List Bool, x1.length = n ∧ x0.length = n ∧ V gs x1 out ≠ V gs x0 out)
    (hnd : ¬ ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ gs'.length ≤ gs.length ∧
      (∀ x : List Bool, x.length = n → V gs' x o = V gs x out) ∧ o < n + gs'.length ∧
      ∀ (j : ℕ) (g' : Gate), gs'[j]? = some g' →
        ∃ a b, g'.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  obtain ⟨x1, x0, h1, h0, hne⟩ := hx
  have htwo : ∀ g ∈ gs, ∃ a b, g.inputs = [a, b] ∧ a ≠ b := fun g hg =>
    two g (hmon g hg).2 (fun h => hnd ⟨g, hg, h⟩)
  have hw : ∀ w : List Bool, wiresFrom (gs.map srt) w = wiresFrom gs w := by
    intro w
    apply map_wires
    intro g hg W
    obtain ⟨a, b, hin, _⟩ := htwo g hg
    exact srt_val g a b hin (by simpa using (hmon g hg).1) W
  have ho : out < n + gs.length := by
    by_contra h
    apply hne
    rw [V_out gs x1 out (by omega), V_out gs x0 out (by omega)]
  refine ⟨gs.map srt, out, ?_, by simp, fun x _ => ?_, by simpa using ho, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨(hmon g hg).1, by simp [srt]⟩
  · unfold V
    rw [hw]
  · intro j g' hj
    simp at hj
    obtain ⟨g, hg, rfl⟩ := hj
    obtain ⟨a, b, hin, hab⟩ := htwo g (List.mem_of_getElem? hg)
    have ha := hback j g hg a (by simp [hin])
    have hb := hback j g hg b (by simp [hin])
    refine ⟨min a b, max a b, by simp [srt, hin], ?_, ?_⟩
    · omega
    · omega

lemma ind (n : ℕ) : ∀ (m : ℕ) (gs : List Gate) (out : ℕ), gs.length ≤ m → Mon gs → Back n gs →
    (∃ x1 x0 : List Bool, x1.length = n ∧ x0.length = n ∧ V gs x1 out ≠ V gs x0 out) →
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ gs'.length ≤ gs.length ∧
      (∀ x : List Bool, x.length = n → V gs' x o = V gs x out) ∧ o < n + gs'.length ∧
      ∀ (j : ℕ) (g' : Gate), gs'[j]? = some g' →
        ∃ a b, g'.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  intro m
  induction m with
  | zero =>
    intro gs out hm hmon hback hx
    by_cases hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0
    · obtain ⟨x1, x0, h1, h0, hne⟩ := hx
      obtain ⟨gs2, o2, _, _, hl, _⟩ := step n gs out hmon hback x1 x0 h1 h0 hne hd
      omega
    · exact base n gs out hmon hback hx hd
  | succ m ih =>
    intro gs out hm hmon hback hx
    by_cases hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0
    · obtain ⟨x1, x0, h1, h0, hne⟩ := hx
      obtain ⟨gs2, o2, hm2, hb2, hl, hv⟩ := step n gs out hmon hback x1 x0 h1 h0 hne hd
      obtain ⟨gs3, o3, hm3, hl3, hv3, ho3, hf3⟩ := ih gs2 o2 (by omega) hm2 hb2
        ⟨x1, x0, h1, h0, by rw [hv x1 h1, hv x0 h0]; exact hne⟩
      exact ⟨gs3, o3, hm3, by omega, fun x hx' => by rw [hv3 x hx', hv x hx'], ho3, hf3⟩
    · exact base n gs out hmon hback hx hd

lemma top (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Monotone2 ⟨gs, out⟩) (x y : Fin n → Bool)
    (hxy : circuitFun n ⟨gs, out⟩ x ≠ circuitFun n ⟨gs, out⟩ y) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ Circuit.size ⟨gs, out⟩ ∧
      circuitFun n D = circuitFun n ⟨gs, out⟩ ∧ D.output < n + D.size ∧
      ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
        ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    simpa using (hmon g hg).1
  have hfw : ∀ w : List Bool, w.length = n → wiresFrom (fix n gs) w = wiresFrom gs w :=
    fun w hw => fix_wires gs n w hw hops
  have hne : V (fix n gs) (List.ofFn x) out ≠ V (fix n gs) (List.ofFn y) out := by
    unfold V
    rw [hfw _ (by simp), hfw _ (by simp)]
    exact hxy
  obtain ⟨gs', o, hm, hl, hv, ho, hf⟩ := ind n (fix n gs).length (fix n gs) out le_rfl
    (fix_mon gs n hmon) (fix_back gs n) ⟨List.ofFn x, List.ofFn y, by simp, by simp, hne⟩
  refine ⟨⟨gs', o⟩, hm, ?_, ?_, ho, hf⟩
  · have := fix_len gs n
    show gs'.length ≤ gs.length
    omega
  · funext z
    show V gs' (List.ofFn z) o = V gs (List.ofFn z) out
    rw [hv _ (by simp)]
    unfold V
    rw [hfw _ (by simp)]

end Sorted3471

theorem Sorted3471 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6 := by
  intro n C hmon hx
  obtain ⟨gs, out⟩ := C
  obtain ⟨x, y, hxy⟩ := hx
  exact Sorted3471.top n gs out hmon x y hxy
namespace PencilArithmetic3471

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

variable {G : SimpleGraph (Fin n)}

theorem point_contains_edge (hC : Monotone2 C) (he : GraphEval C G)
    {u v : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true :=
  acts_mono hC (point_mono (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)))
    C.output ((he u v).mpr edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in
    ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem live_reader {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    ∃ b, LNext n C a b := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b, hb, hpath⟩

end Circ2

section Forest

def ReachIn (A : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a = b
  | k+1, a, b => ∃ c, ReachIn A k a c ∧ A c b

theorem reachIn_of_rtg {A : ℕ → ℕ → Prop} {a b : ℕ} (h : ReflTransGen A a b) :
    ∃ k, ReachIn A k a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k+1, _, hk, hbc⟩

noncomputable def root (A : ℕ → ℕ → Prop) (v : ℕ) : ℕ := by
  classical exact Nat.find (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v)

theorem root_spec (A : ℕ → ℕ → Prop) (v : ℕ) : ReflTransGen A (root A v) v := by
  classical exact Nat.find_spec (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v)

theorem root_min (A : ℕ → ℕ → Prop) {v r : ℕ} (h : ReflTransGen A r v) : root A v ≤ r := by
  classical exact Nat.find_min' (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v) h

theorem root_eq {A : ℕ → ℕ → Prop} (hs : ∀ a b, A a b → A b a) {a b : ℕ}
    (h : ReflTransGen A a b) : root A a = root A b := by
  have hsym : ∀ {a b : ℕ}, ReflTransGen A a b → ReflTransGen A b a := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact (ReflTransGen.single (hs _ _ hbc)).trans ih
  apply le_antisymm
  · exact root_min A ((root_spec A b).trans (hsym h))
  · exact root_min A ((root_spec A a).trans h)

noncomputable def rdist (A : ℕ → ℕ → Prop) (v : ℕ) : ℕ := by
  classical exact Nat.find (reachIn_of_rtg (root_spec A v))

theorem rdist_spec (A : ℕ → ℕ → Prop) (v : ℕ) : ReachIn A (rdist A v) (root A v) v := by
  classical exact Nat.find_spec (reachIn_of_rtg (root_spec A v))

theorem rdist_min (A : ℕ → ℕ → Prop) {v k : ℕ} (h : ReachIn A k (root A v) v) :
    rdist A v ≤ k := by
  classical exact Nat.find_min' (reachIn_of_rtg (root_spec A v)) h

theorem rtg_of_reachIn {A : ℕ → ℕ → Prop} : ∀ {k a b : ℕ}, ReachIn A k a b → ReflTransGen A a b
  | 0, _, _, h => by
    change _ = _ at h
    subst h
    exact .refl
  | _+1, _, _, ⟨_, hc, hcb⟩ => (rtg_of_reachIn hc).tail hcb

theorem root_pred {A : ℕ → ℕ → Prop} (hs : ∀ a b, A a b → A b a) {v : ℕ} (hv : root A v ≠ v) :
    ∃ c, A c v ∧ rdist A c < rdist A v := by
  have hsp := rdist_spec A v
  rcases hk : rdist A v with _ | k
  · rw [hk] at hsp
    exact (hv hsp).elim
  · rw [hk] at hsp
    obtain ⟨c, hc, hcv⟩ := hsp
    have hr : root A c = root A v := root_eq hs (ReflTransGen.single hcv)
    refine ⟨c, hcv, ?_⟩
    have := rdist_min A (v := c) (k := k) (by rw [hr]; exact hc)
    omega

theorem forest_count (V : Finset ℕ) (F : Finset (ℕ × ℕ)) (A : ℕ → ℕ → Prop)
    (hs : ∀ a b, A a b → A b a) (hF : ∀ a b, A a b → (a, b) ∈ F ∨ (b, a) ∈ F) :
    V.card ≤ F.card + (V.image (root A)).card := by
  classical
  choose! pr hpr using fun v (hv : root A v ≠ v) => root_pred hs hv
  let φ : ℕ → ℕ × ℕ := fun v => if (pr v, v) ∈ F then (pr v, v) else (v, pr v)
  have hφ : ∀ v, root A v ≠ v → φ v ∈ F := by
    intro v hv
    dsimp only [φ]
    split_ifs with h
    · exact h
    · exact (hF _ _ (hpr v hv).1).resolve_left h
  have h1 : (V.filter (fun v => root A v ≠ v)).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn φ
    · intro v hv
      exact hφ v (Finset.mem_filter.1 hv).2
    · intro v hv w hw hvw
      have hv' := hpr v (Finset.mem_filter.1 hv).2
      have hw' := hpr w (Finset.mem_filter.1 hw).2
      dsimp only [φ] at hvw
      have a1 := hv'.2
      have a2 := hw'.2
      split_ifs at hvw <;> simp only [Prod.mk.injEq] at hvw
      all_goals first
        | exact hvw.2
        | exact hvw.1
        | (obtain ⟨e1, e2⟩ := hvw
           first
             | (rw [e1] at a1; rw [← e2] at a2; omega)
             | (rw [e2] at a1; rw [← e1] at a2; omega))
  have h2 : (V.filter (fun v => ¬ root A v ≠ v)).card ≤ (V.image (root A)).card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvV, hr⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_image.2 ⟨v, hvV, not_not.1 hr⟩
  have := Finset.card_filter_add_card_filter_not (s := V) (fun v => root A v ≠ v)
  omega

end Forest

section Regions

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

structure Good (n : ℕ) (C : Circuit) (G : SimpleGraph (Fin n)) (d : ℕ) : Prop where
  mono : Monotone2 C
  shape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < n + p
  eval : GraphEval C G
  two : 2 ≤ d
  deg : ∀ u : Fin n, ∃ S : Finset (Fin n), d ≤ S.card ∧ ∀ t ∈ S, G.Adj u t
  dist : ∀ u v : Fin n, u ≠ v → ∃ t, G.Adj u t ∧ ¬ G.Adj v t ∧ t ≠ v

theorem Good.nbr (H : Good n C G d) (u : Fin n) : ∃ t, G.Adj u t := by
  obtain ⟨S, hS, hA⟩ := H.deg u
  obtain ⟨t, ht⟩ : S.Nonempty := Finset.card_pos.1 (by have := H.two; omega)
  exact ⟨t, hA t ht⟩

theorem Good.two_nbrs (H : Good n C G d) (u : Fin n) :
    ∃ t t', t ≠ t' ∧ G.Adj u t ∧ G.Adj u t' := by
  obtain ⟨S, hS, hA⟩ := H.deg u
  obtain ⟨t, ht, t', ht', hne⟩ := Finset.one_lt_card.1 (by have := H.two; omega : 1 < S.card)
  exact ⟨t, t', hne, hA t ht, hA t' ht'⟩

theorem Good.live_in (H : Good n C G d) (u : Fin n) : Live n C u.val := by
  obtain ⟨t, ht⟩ := H.nbr u
  exact input_live H.eval ht

theorem gate_val (H : Good n C G d) {p : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[p]? = some g)
    (hi : g.inputs = [a, b]) (hb : b < n + p) (hab : a < b) (x : Fin n → Bool) :
    (g.op = GateOp.and ∧ val C x (n+p) = (val C x a && val C x b)) ∨
      (g.op = GateOp.or ∧ val C x (n+p) = (val C x a || val C x b)) := by
  have hop := (H.mono g (List.mem_of_getElem? hg)).1
  rw [val_gate C x hg, hi]
  have ea : operand C x (n+p) a = val C x a := by simp [operand, show a < n+p by omega]
  have eb : operand C x (n+p) b = val C x b := by simp [operand, hb]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h
  · left; simp [h, GateOp.eval, ea, eb]
  · right; simp [h, GateOp.eval, ea, eb]

theorem lnext_gate (H : Good n C G d) {m h : ℕ} (hm : LNext n C m h) :
    ∃ p g a b, C.gates[p]? = some g ∧ h = n + p ∧ g.inputs = [a, b] ∧ a < b ∧ b < n + p ∧
      (m = a ∨ m = b) := by
  obtain ⟨⟨_, p, g, hg, rfl, hmem⟩, _⟩ := hm
  obtain ⟨a, b, hi, hab, hb⟩ := H.shape p g hg
  refine ⟨p, g, a, b, hg, rfl, hi, hab, hb, ?_⟩
  rw [hi] at hmem
  simpa using hmem

theorem input_lnext {p : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[p]? = some g)
    (hi : g.inputs = [a, b]) (hb : b < n + p) (hab : a < b) (hl : Live n C (n+p)) :
    LNext n C a (n+p) ∧ LNext n C b (n+p) :=
  ⟨⟨⟨by omega, p, g, hg, rfl, by simp [hi]⟩, hl⟩, ⟨⟨hb, p, g, hg, rfl, by simp [hi]⟩, hl⟩⟩

def Single (C : Circuit) {n : ℕ} (u : Fin n) (w : ℕ) : Prop :=
  ∀ v : Fin n, val C (point {v}) w = true ↔ v = u

theorem single_input (u : Fin n) : Single C u u.val := by
  intro v
  rw [val_input]
  simp [point, eq_comm]

theorem single_unique {u u' : Fin n} {w : ℕ} (h : Single C u w) (h' : Single C u' w) :
    u = u' :=
  (h' u).1 ((h u).2 rfl)

theorem single_true {u : Fin n} {w : ℕ} (h : Single C u w) : val C (point {u}) w = true :=
  (h u).2 rfl

theorem out_not_single (H : Good n C G d) (u : Fin n) : ¬ Single C u C.output := by
  intro h
  have := single_true h
  rw [point_single_quiet H.eval] at this
  exact Bool.false_ne_true this

noncomputable def Preg (n : ℕ) (C : Circuit) (u : Fin n) : Finset ℕ :=
  open Classical in
  (living n C).filter (fun w => Trace n C (Single C u) u.val w ∧ Single C u w)

theorem mem_Preg {u : Fin n} {w : ℕ} : w ∈ Preg n C u ↔
    (w < n + C.gates.length ∧ Live n C w) ∧ Trace n C (Single C u) u.val w ∧ Single C u w := by
  classical
  unfold Preg; rw [Finset.mem_filter, mem_living]

noncomputable def Zreg (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (living n C).filter (fun w => ∀ v : Fin n, val C (point {v}) w = false)

theorem mem_Zreg {w : ℕ} : w ∈ Zreg n C ↔
    (w < n + C.gates.length ∧ Live n C w) ∧ ∀ v : Fin n, val C (point {v}) w = false := by
  classical
  unfold Zreg; rw [Finset.mem_filter, mem_living]

noncomputable def Dreg (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (living n C).filter
    (fun w => (∃ v : Fin n, val C (point {v}) w = true) ∧ ∀ u : Fin n, w ∉ Preg n C u)

theorem mem_Dreg {w : ℕ} : w ∈ Dreg n C ↔ (w < n + C.gates.length ∧ Live n C w) ∧
    (∃ v : Fin n, val C (point {v}) w = true) ∧ ∀ u : Fin n, w ∉ Preg n C u := by
  classical
  unfold Dreg; rw [Finset.mem_filter, mem_living]

noncomputable def Edges (n : ℕ) (C : Circuit) : Finset (ℕ × ℕ) :=
  open Classical in (living n C ×ˢ living n C).filter (fun e => LNext n C e.1 e.2)

theorem mem_Edges {e : ℕ × ℕ} : e ∈ Edges n C ↔ LNext n C e.1 e.2 := by
  classical
  unfold Edges
  rw [Finset.mem_filter, Finset.mem_product, mem_living, mem_living]
  constructor
  · exact fun h => h.2
  · intro h
    have h2 := next_in_range h.1
    exact ⟨⟨⟨by have := h.1.1; omega, live_before h.1 h.2⟩, h2, h.2⟩, h⟩

noncomputable def outE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R)

noncomputable def intE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R ∧ e.2 ∈ R)

noncomputable def extE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)

theorem mem_outE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ outE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R := by
  classical
  unfold outE; rw [Finset.mem_filter, mem_Edges]

theorem mem_intE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ intE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R ∧ e.2 ∈ R := by
  classical
  unfold intE; rw [Finset.mem_filter, mem_Edges]

theorem mem_extE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ extE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R ∧ e.2 ∉ R := by
  classical
  unfold extE; rw [Finset.mem_filter, mem_Edges]

theorem card_outE (R : Finset ℕ) :
    (outE n C R).card = (intE n C R).card + (extE n C R).card := by
  classical
  have h1 : (outE n C R).filter (fun e => e.2 ∈ R) = intE n C R := by
    ext e; simp only [Finset.mem_filter, mem_outE, mem_intE]; tauto
  have h2 : (outE n C R).filter (fun e => ¬ e.2 ∈ R) = extE n C R := by
    ext e; simp only [Finset.mem_filter, mem_outE, mem_extE]; tauto
  rw [← h1, ← h2, Finset.card_filter_add_card_filter_not]

theorem out_bound (R : Finset ℕ) (hR : ∀ w ∈ R, Live n C w) :
    R.card ≤ (outE n C R).card + 1 := by
  classical
  have hex : ∀ w ∈ R.erase C.output, ∃ b, LNext n C w b := fun w hw =>
    live_reader (hR w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw)
  choose! ρ hρ using hex
  have h1 : (R.erase C.output).card ≤ (outE n C R).card := by
    apply Finset.card_le_card_of_injOn (fun w => (w, ρ w))
    · intro w hw
      exact mem_outE.2 ⟨hρ w hw, Finset.mem_of_mem_erase hw⟩
    · intro w _ w' _ h
      exact congrArg Prod.fst h
  have h2 := Finset.pred_card_le_card_erase (s := R) (a := C.output)
  omega

theorem max_exit (R : Finset ℕ) (hne : R.Nonempty)
    (hR : ∀ w ∈ R, Live n C w ∧ w ≠ C.output) :
    ∃ b, LNext n C (R.max' hne) b ∧ b ∉ R := by
  obtain ⟨b, hb⟩ := live_reader (hR _ (R.max'_mem hne)).1 (hR _ (R.max'_mem hne)).2
  refine ⟨b, hb, fun hbR => ?_⟩
  have := R.le_max' b hbR
  have := hb.1.1
  omega

theorem Preg_single {u : Fin n} {w : ℕ} (h : w ∈ Preg n C u) : Single C u w :=
  (mem_Preg.1 h).2.2

theorem Preg_live {u : Fin n} {w : ℕ} (h : w ∈ Preg n C u) : Live n C w := (mem_Preg.1 h).1.2

theorem Preg_disj {u u' : Fin n} {w : ℕ} (h : w ∈ Preg n C u) (h' : w ∈ Preg n C u') :
    u = u' :=
  single_unique (Preg_single h) (Preg_single h')

theorem self_Preg (H : Good n C G d) (u : Fin n) : u.val ∈ Preg n C u :=
  mem_Preg.2 ⟨⟨by have := u.isLt; omega, H.live_in u⟩, .refl, single_input u⟩

theorem Preg_close {u : Fin n} {w h : ℕ} (hw : w ∈ Preg n C u) (hn : LNext n C w h)
    (hs : Single C u h) : h ∈ Preg n C u := by
  obtain ⟨_, ht, hsw⟩ := mem_Preg.1 hw
  exact mem_Preg.2 ⟨⟨next_in_range hn.1, hn.2⟩, ht.tail ⟨hsw, hn⟩, hs⟩

theorem trace_Preg {u : Fin n} {w : ℕ} (h : Trace n C (Single C u) u.val w) :
    Trace n C (· ∈ Preg n C u) u.val w := by
  induction h with
  | refl => exact .refl
  | tail hua hab ih =>
    refine ih.tail ⟨?_, hab.2⟩
    exact mem_Preg.2 ⟨⟨by have := next_in_range hab.2.1; have := hab.2.1.1; omega,
      live_before hab.2.1 hab.2.2⟩, hua, hab.1⟩

theorem Preg_parent {u : Fin n} {h : ℕ} (hh : h ∈ Preg n C u) (hne : h ≠ u.val) :
    ∃ a, a ∈ Preg n C u ∧ LNext n C a h := by
  obtain ⟨_, ht, _⟩ := mem_Preg.1 hh
  rcases ht.cases_tail with e | ⟨a, hua, hs, hn⟩
  · exact (hne e).elim
  · exact ⟨a, mem_Preg.2 ⟨⟨by have := next_in_range hn.1; have := hn.1.1; omega,
      live_before hn.1 hn.2⟩, hua, hs⟩, hn⟩

theorem int_bound (u : Fin n) : (Preg n C u).card ≤ (intE n C (Preg n C u)).card + 1 := by
  classical
  have hex : ∀ h ∈ (Preg n C u).erase u.val, ∃ a, a ∈ Preg n C u ∧ LNext n C a h :=
    fun h hh => Preg_parent (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh)
  choose! par hpar using hex
  have h1 : ((Preg n C u).erase u.val).card ≤ (intE n C (Preg n C u)).card := by
    apply Finset.card_le_card_of_injOn (fun h => (par h, h))
    · intro h hh
      exact mem_intE.2 ⟨(hpar h hh).2, (hpar h hh).1, Finset.mem_of_mem_erase hh⟩
    · intro h _ h' _ e
      exact congrArg Prod.snd e
  have h2 := Finset.pred_card_le_card_erase (s := Preg n C u) (a := u.val)
  omega

theorem ext_pos (H : Good n C G d) (u : Fin n) : 1 ≤ (extE n C (Preg n C u)).card := by
  have hne : (Preg n C u).Nonempty := ⟨_, self_Preg H u⟩
  obtain ⟨b, hb, hbR⟩ := max_exit (Preg n C u) hne (fun w hw =>
    ⟨Preg_live hw, fun e => out_not_single H u (e ▸ Preg_single hw)⟩)
  exact Finset.card_pos.2 ⟨((Preg n C u).max' hne, b),
    mem_extE.2 ⟨hb, (Preg n C u).max'_mem hne, hbR⟩⟩

theorem living_cover : (living n C).card ≤
    (∑ u : Fin n, (Preg n C u).card) + (Dreg n C).card + (Zreg n C).card := by
  classical
  have hsub : living n C ⊆ (Finset.univ.biUnion (Preg n C)) ∪ Dreg n C ∪ Zreg n C := by
    intro w hw
    have hw' := mem_living.1 hw
    by_cases hz : ∀ v : Fin n, val C (point {v}) w = false
    · exact Finset.mem_union_right _ (mem_Zreg.2 ⟨hw', hz⟩)
    · obtain ⟨v, hv⟩ := not_forall.1 hz
      by_cases hp : ∃ u, w ∈ Preg n C u
      · obtain ⟨u, hu⟩ := hp
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, hu⟩))
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_Dreg.2 ⟨hw', ⟨v, by simpa using hv⟩, not_exists.1 hp⟩))
  have h0 := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (Finset.univ.biUnion (Preg n C) ∪ Dreg n C) (Zreg n C)
  have h2 := Finset.card_union_le (Finset.univ.biUnion (Preg n C)) (Dreg n C)
  have h3 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n))) (t := Preg n C)
  omega

theorem edges_split :
    (∑ u : Fin n, (outE n C (Preg n C u)).card) + (outE n C (Dreg n C)).card +
      (outE n C (Zreg n C)).card ≤ (Edges n C).card := by
  classical
  let B := Finset.univ.biUnion fun u : Fin n => outE n C (Preg n C u)
  have hB : B.card = ∑ u : Fin n, (outE n C (Preg n C u)).card := by
    apply Finset.card_biUnion
    intro x _ y _ hxy
    change Disjoint (outE n C (Preg n C x)) (outE n C (Preg n C y))
    refine Finset.disjoint_left.2 fun e h1 h2 => hxy ?_
    exact Preg_disj (mem_outE.1 h1).2 (mem_outE.1 h2).2
  have d1 : Disjoint B (outE n C (Dreg n C)) := by
    refine Finset.disjoint_left.2 fun e h1 h2 => ?_
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h1
    exact (mem_Dreg.1 (mem_outE.1 h2).2).2.2 u (mem_outE.1 hu).2
  have d2 : Disjoint (B ∪ outE n C (Dreg n C)) (outE n C (Zreg n C)) := by
    refine Finset.disjoint_left.2 fun e h1 h2 => ?_
    have hz := (mem_Zreg.1 (mem_outE.1 h2).2).2
    rcases Finset.mem_union.1 h1 with h | h
    · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h
      have := single_true (Preg_single (mem_outE.1 hu).2)
      rw [hz u] at this
      exact Bool.false_ne_true this
    · obtain ⟨v, hv⟩ := (mem_Dreg.1 (mem_outE.1 h).2).2.1
      rw [hz v] at hv
      exact Bool.false_ne_true hv
  have hsub : B ∪ outE n C (Dreg n C) ∪ outE n C (Zreg n C) ⊆ Edges n C := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h'
        exact mem_Edges.2 (mem_outE.1 hu).1
      · exact mem_Edges.2 (mem_outE.1 h').1
    · exact mem_Edges.2 (mem_outE.1 h).1
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, hB] at this
  exact this

theorem edges_le (hC : Monotone2 C) :
    (Edges n C).card ≤ 2 * ((living n C).filter (fun j => ¬ j < n)).card := by
  classical
  let W := living n C
  have hcard : (Edges n C).card = ∑ j ∈ W, (W.filter fun i => LNext n C i j).card := by
    unfold Edges
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.card_filter]
  have H : (∑ j ∈ W, (W.filter fun i => LNext n C i j).card) ≤
      ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
    Finset.sum_le_sum fun j hj => incoming_bound hC hj
  have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2 * (W.filter (fun j => ¬ j < n)).card := by
    rw [Finset.sum_ite]
    simp [Nat.mul_comm]
  rw [hcard]
  exact H.trans_eq e

theorem living_eq (H : Good n C G d) :
    (living n C).card = n + ((living n C).filter (fun j => ¬ j < n)).card := by
  classical
  have hSub : Finset.range n ⊆ living n C := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    exact mem_living.2 ⟨by omega, H.live_in ⟨a, hi⟩⟩
  have h := Finset.card_sdiff_add_card_eq_card hSub
  have e : living n C \ Finset.range n = (living n C).filter (fun j => ¬ j < n) := by
    ext a; simp
  rw [e, Finset.card_range] at h
  omega

theorem gates_le : ((living n C).filter (fun j => ¬ j < n)).card ≤ C.gates.length := by
  rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
  apply Finset.card_le_card_of_injOn (fun a => a-n)
  · intro a ha
    have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
    have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
    apply Finset.mem_range.2
    change a-n < C.gates.length
    omega
  · intro a ha b hb hab
    have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
    have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
    change a-n=b-n at hab
    omega

end Regions

section Terminal

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

theorem terminal_unique (H : Good n C G d) {u : Fin n}
    (ht : (intE n C (Preg n C u)).card + (extE n C (Preg n C u)).card ≤ (Preg n C u).card)
    {w k k' : ℕ} (hw : w ∈ Preg n C u) (hk : LNext n C w k) (hk' : LNext n C w k') :
    k = k' := by
  classical
  by_contra hne
  have hex : ∀ w' ∈ Preg n C u, ∃ b, LNext n C w' b := fun w' hw' =>
    live_reader (Preg_live hw') (fun e => out_not_single H u (e ▸ Preg_single hw'))
  choose! ρ hρ using hex
  obtain ⟨k'', hk'', hne''⟩ : ∃ k'', LNext n C w k'' ∧ k'' ≠ ρ w := by
    by_cases h : k = ρ w
    · exact ⟨k', hk', fun e => hne (h.trans e.symm)⟩
    · exact ⟨k, hk, h⟩
  have hsub : insert (w, k'') ((Preg n C u).image fun w' => (w', ρ w')) ⊆
      outE n C (Preg n C u) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact mem_outE.2 ⟨hk'', hw⟩
    · obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 he
      exact mem_outE.2 ⟨hρ w' hw', hw'⟩
  have hnot : (w, k'') ∉ (Preg n C u).image fun w' => (w', ρ w') := by
    intro he
    obtain ⟨w', _, he'⟩ := Finset.mem_image.1 he
    have e1 : w' = w := congrArg Prod.fst he'
    have e2 : ρ w' = k'' := congrArg Prod.snd he'
    rw [e1] at e2
    exact hne'' e2.symm
  have hinj : ((Preg n C u).image fun w' => (w', ρ w')).card = (Preg n C u).card :=
    Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hinj, card_outE] at this
  omega

theorem dominator (H : Good n C G d) {u : Fin n} {P : ℕ → Prop} {g : ℕ}
    (path : Trace n C P u.val g)
    (uniq : ∀ a k k', a < g → P a → LNext n C a k → LNext n C a k' → k = k')
    (hg : Live n C g) {v : Fin n} (hvu : v ≠ u) : val C (point {v}) g = false := by
  classical
  rw [← Bool.not_eq_true]
  intro hv
  obtain ⟨t, hut, hvt, _⟩ := H.dist u v (Ne.symm hvu)
  have hx : val C (point ({t, v} : Finset (Fin n))) C.output = false :=
    point_pair_quiet H.eval (fun h => hvt h.symm)
  have hy : val C (point (insert u ({t, v} : Finset (Fin n)))) C.output = true :=
    point_contains_edge H.mono H.eval (u := u) (v := t) (by simp) (by simp) hut
  have hd := influence path uniq (x := point ({t, v} : Finset (Fin n)))
    (y := point (insert u ({t, v} : Finset (Fin n))))
    (fun i hi => (point_insert hi).symm) ReflTransGen.refl (by rw [hx, hy]; decide)
  have hgo := next_le hg
  rcases hd with h | h
  · exact absurd h.1 (by omega)
  · apply h.2
    have h1 : val C (point ({t, v} : Finset (Fin n))) g = true :=
      acts_mono H.mono (point_mono (by simp)) g hv
    have h2 : val C (point (insert u ({t, v} : Finset (Fin n)))) g = true :=
      acts_mono H.mono (point_mono (by simp)) g hv
    rw [h1, h2]

theorem terminal (H : Good n C G d) {u : Fin n}
    (ht : (intE n C (Preg n C u)).card + (extE n C (Preg n C u)).card ≤ (Preg n C u).card) :
    ∃ m a g, (∀ e ∈ extE n C (Preg n C u), e = (m, g)) ∧ Single C u m ∧ LNext n C m g ∧
      LNext n C a g ∧ a ≠ m ∧ (∀ x, LNext n C x g → x = m ∨ x = a) ∧ g ∈ Zreg n C ∧
      a ∈ Dreg n C ∧ (∀ t, G.Adj u t → val C (point {t}) a = true) := by
  classical
  have hint := int_bound (C := C) u
  have hext := ext_pos H u
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 (show (extE n C (Preg n C u)).card = 1 by omega)
  obtain ⟨m, g⟩ := e0
  have hall : ∀ e ∈ extE n C (Preg n C u), e = (m, g) := by
    intro e he
    rw [he0] at he
    exact Finset.mem_singleton.1 he
  have hmg : (m, g) ∈ extE n C (Preg n C u) := by
    rw [he0]; exact Finset.mem_singleton_self _
  have hmgL : LNext n C m g := (mem_extE.1 hmg).1
  have hmP : m ∈ Preg n C u := (mem_extE.1 hmg).2.1
  have hgP : g ∉ Preg n C u := (mem_extE.1 hmg).2.2
  have hsm : Single C u m := Preg_single hmP
  have hgl : Live n C g := hmgL.2
  have path : Trace n C (· ∈ Preg n C u) u.val g :=
    (trace_Preg (mem_Preg.1 hmP).2.1).tail ⟨hmP, hmgL⟩
  have uniq : ∀ a k k', a < g → a ∈ Preg n C u → LNext n C a k → LNext n C a k' → k = k' :=
    fun a k k' _ ha hk hk' => terminal_unique H ht ha hk hk'
  have hZ : ∀ v : Fin n, val C (point {v}) g = false := by
    have hother : ∀ v : Fin n, v ≠ u → val C (point {v}) g = false :=
      fun v hv => dominator H path uniq hgl hv
    intro v
    by_cases hv : v = u
    · subst hv
      rw [← Bool.not_eq_true]
      intro hu
      apply hgP
      refine Preg_close hmP hmgL fun w => ⟨fun hw => ?_, fun hw => hw ▸ hu⟩
      by_contra hne
      rw [hother w hne] at hw
      exact Bool.false_ne_true hw
    · exact hother v hv
  have hgZ : g ∈ Zreg n C := mem_Zreg.2 ⟨⟨next_in_range hmgL.1, hgl⟩, hZ⟩
  obtain ⟨p, gt, i1, i2, hgt, hgp, hi, h12, hi2, hm12⟩ := lnext_gate H hmgL
  subst hgp
  have hin : ∀ x, LNext n C x (n+p) → x = i1 ∨ x = i2 := by
    intro x hx
    obtain ⟨⟨_, p', g', hg', hpp, hxm⟩, _⟩ := hx
    have hp' : p' = p := by omega
    subst hp'
    rw [hgt] at hg'
    cases hg'
    rw [hi] at hxm
    simpa using hxm
  obtain ⟨hl1, hl2⟩ := input_lnext hgt hi hi2 h12 hgl
  obtain ⟨a, ham, ha12, hal, hma⟩ : ∃ a, a ≠ m ∧ (a = i1 ∨ a = i2) ∧ LNext n C a (n+p) ∧
      ∀ x, LNext n C x (n+p) → x = m ∨ x = a := by
    rcases hm12 with rfl | rfl
    · exact ⟨i2, by omega, Or.inr rfl, hl2, hin⟩
    · exact ⟨i1, by omega, Or.inl rfl, hl1, fun x hx => (hin x hx).symm⟩
  have hand : gt.op = GateOp.and := by
    rcases gate_val H hgt hi hi2 h12 (point {u}) with h | h
    · exact h.1
    · exfalso
      have hv := h.2
      rw [hZ u] at hv
      have hm' := single_true hsm
      rcases hm12 with rfl | rfl
      · rw [hm'] at hv; simp at hv
      · rw [hm'] at hv; simp at hv
  have hT : ∀ t : Fin n, G.Adj u t → val C (point {t}) a = true := by
    intro t hut
    have hx : val C (point {t}) C.output = false := point_single_quiet H.eval t
    have hy : val C (point (insert u ({t} : Finset (Fin n)))) C.output = true :=
      point_contains_edge H.mono H.eval (u := u) (v := t) (by simp) (by simp) hut
    have agrees : ∀ i, i ≠ u →
        point ({t} : Finset (Fin n)) i = point (insert u ({t} : Finset (Fin n))) i :=
      fun i hi => (point_insert hi).symm
    have hgo := next_le hgl
    have hdg : val C (point {t}) (n+p) ≠ val C (point (insert u ({t} : Finset (Fin n)))) (n+p) := by
      rcases influence path uniq agrees ReflTransGen.refl (by rw [hx, hy]; decide) with h | h
      · exact absurd h.1 (by omega)
      · exact h.2
    have hyg : val C (point (insert u ({t} : Finset (Fin n)))) (n+p) = true := by
      cases hxg : val C (point {t}) (n+p)
      · rw [hxg] at hdg
        simpa using hdg.symm
      · exact acts_mono H.mono (point_mono (by simp)) _ hxg
    have hya : val C (point (insert u ({t} : Finset (Fin n)))) a = true := by
      rcases gate_val H hgt hi hi2 h12 (point (insert u ({t} : Finset (Fin n)))) with h | h
      · rw [h.2, Bool.and_eq_true] at hyg
        rcases ha12 with rfl | rfl
        · exact hyg.1
        · exact hyg.2
      · exfalso
        have e := h.1.symm.trans hand
        cases e
    by_contra hxa
    have hda : val C (point {t}) a ≠ val C (point (insert u ({t} : Finset (Fin n)))) a := by
      rw [hya]; exact hxa
    rcases influence path uniq agrees (live_before hal.1 hal.2) hda with h | h
    · have := hall (a, n+p) (mem_extE.2 ⟨hal, h.2, hgP⟩)
      exact ham (congrArg Prod.fst this)
    · exact absurd h.1 (by have := hal.1.1; omega)
  have haD : a ∈ Dreg n C := by
    obtain ⟨t1, t2, h12', ht1, ht2⟩ := H.two_nbrs u
    refine mem_Dreg.2 ⟨⟨by have := next_in_range hal.1; have := hal.1.1; omega,
      live_before hal.1 hal.2⟩, ⟨t1, hT t1 ht1⟩, fun u' hu' => ?_⟩
    have hs := Preg_single hu'
    exact h12' (((hs t1).1 (hT t1 ht1)).trans ((hs t2).1 (hT t2 ht2)).symm)
  exact ⟨m, a, n+p, hall, hsm, hmgL, hal, ham, hma, hgZ, haD, hT⟩

end Terminal

section Count

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

def DAdj (n : ℕ) (C : Circuit) (x y : ℕ) : Prop :=
  x ∈ Dreg n C ∧ y ∈ Dreg n C ∧ (LNext n C x y ∨ LNext n C y x)

theorem DAdj_symm : ∀ x y, DAdj n C x y → DAdj n C y x :=
  fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩

noncomputable def Uset (n : ℕ) (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun u' => ∃ e ∈ Edges n C,
    e.1 ∈ Preg n C u' ∧ e.2 ∈ Dreg n C ∧ root (DAdj n C) e.2 = r)

theorem mem_Uset {r : ℕ} {u' : Fin n} : u' ∈ Uset n C r ↔ ∃ e ∈ Edges n C,
    e.1 ∈ Preg n C u' ∧ e.2 ∈ Dreg n C ∧ root (DAdj n C) e.2 = r := by
  classical
  unfold Uset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem T_sub_U (H : Good n C G d) : ∀ h, h ∈ Dreg n C → ∀ v : Fin n,
    val C (point {v}) h = true → v ∈ Uset n C (root (DAdj n C) h) := by
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro hD v hv
    obtain ⟨⟨hlt, hl⟩, _, hnP⟩ := mem_Dreg.1 hD
    have hge : n ≤ h := by
      by_contra hh
      have hh' : h < n := by omega
      exact hnP ⟨h, hh'⟩ (self_Preg H ⟨h, hh'⟩)
    obtain ⟨p, rfl⟩ : ∃ p, h = n + p := ⟨h - n, by omega⟩
    have hp : p < C.gates.length := by omega
    obtain ⟨gt, hgt⟩ : ∃ gt, C.gates[p]? = some gt := ⟨C.gates[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨i1, i2, hi, h12, hi2⟩ := H.shape p gt hgt
    obtain ⟨hl1, hl2⟩ := input_lnext hgt hi hi2 h12 hl
    have hc : ∃ c, LNext n C c (n+p) ∧ val C (point {v}) c = true := by
      rcases gate_val H hgt hi hi2 h12 (point {v}) with h' | h'
      · rw [h'.2, Bool.and_eq_true] at hv
        exact ⟨i1, hl1, hv.1⟩
      · rw [h'.2, Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact ⟨i1, hl1, hv⟩
        · exact ⟨i2, hl2, hv⟩
    obtain ⟨c, hcL, hcv⟩ := hc
    by_cases hcP : ∃ u', c ∈ Preg n C u'
    · obtain ⟨u', hu'⟩ := hcP
      have e : v = u' := (Preg_single hu' v).1 hcv
      subst e
      exact mem_Uset.2 ⟨(c, n+p), mem_Edges.2 hcL, hu', hD, rfl⟩
    · have hcr : c < n + C.gates.length := by
        have := next_in_range hcL.1; have := hcL.1.1; omega
      have hcD : c ∈ Dreg n C :=
        mem_Dreg.2 ⟨⟨hcr, live_before hcL.1 hcL.2⟩, ⟨v, hcv⟩, not_exists.1 hcP⟩
      have hr : root (DAdj n C) c = root (DAdj n C) (n+p) :=
        root_eq DAdj_symm (ReflTransGen.single ⟨hcD, hD, Or.inl hcL⟩)
      rw [← hr]
      exact ih c hcL.1.1 hcD v hcv

theorem exit_inj (H : Good n C G d) {u u' : Fin n} {m a m' g : ℕ} (hsm : Single C u m)
    (hT : ∀ t : Fin n, G.Adj u t → val C (point {t}) a = true)
    (hx : ∀ x, LNext n C x g → x = m ∨ x = a) (hsm' : Single C u' m') (hm' : LNext n C m' g) :
    u = u' := by
  rcases hx m' hm' with rfl | rfl
  · exact single_unique hsm hsm'
  · exfalso
    obtain ⟨t1, t2, h12, ht1, ht2⟩ := H.two_nbrs u
    exact h12 (((hsm' t1).1 (hT t1 ht1)).trans ((hsm' t2).1 (hT t2 ht2)).symm)

noncomputable def pc (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (Preg n C u).card
noncomputable def ic (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (intE n C (Preg n C u)).card
noncomputable def ec (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (extE n C (Preg n C u)).card

theorem final_arith (sg n d τ X NEc Elc Se : ℤ) (hmain : sg + 1 + τ ≥ X + n + NEc)
    (hS2 : Se + Elc * d ≤ d * X + Elc * 2) (hS3 : Elc ≤ X) (hent : d * τ ≤ Se)
    (hτ : τ ≤ NEc) (hcard : NEc + Elc = n) (hd : 0 ≤ d) :
    2 * n * (d + 1) ≤ (d + 2) * (sg + 1) := by
  have hk : 0 ≤ sg + 1 - (2 * n - (τ - X + Elc)) := by linarith
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 2) hk]

theorem main_count (H : Good n C G d) :
    2 * n * (d + 1) ≤ (d + 2) * (((living n C).filter (fun j => ¬ j < n)).card + 1) := by
  classical
  let D := Dreg n C
  let A := DAdj n C
  let NE := (Finset.univ : Finset (Fin n)).filter (fun u => ic n C u + ec n C u ≤ pc n C u)
  let El := (Finset.univ : Finset (Fin n)).filter (fun u => ¬ ic n C u + ec n C u ≤ pc n C u)
  have hNE : ∀ u, u ∈ NE ↔ ic n C u + ec n C u ≤ pc n C u := fun u =>
    ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  have hEl : ∀ u, u ∈ El ↔ ¬ ic n C u + ec n C u ≤ pc n C u := fun u =>
    ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  choose! m a g hterm using fun u (hu : u ∈ NE) => terminal H ((hNE u).1 hu)

  have hF : ∀ x y, A x y → (x, y) ∈ intE n C D ∨ (y, x) ∈ intE n C D := by
    rintro x y ⟨hx, hy, h | h⟩
    · exact Or.inl (mem_intE.2 ⟨h, hx, hy⟩)
    · exact Or.inr (mem_intE.2 ⟨h, hy, hx⟩)
  have hforest := forest_count D (intE n C D) A DAdj_symm hF
  let Rt := D.image (root A)
  let TC := NE.image (fun u => root A (a u))
  have hTC : TC ⊆ Rt := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨_, _, _, _, _, _, _, haD, _⟩ := hterm u hu
    exact Finset.mem_image.2 ⟨a u, haD, rfl⟩
  have hτ : TC.card ≤ NE.card := Finset.card_image_le
  have hRTC : (Rt \ TC).card + TC.card = Rt.card := Finset.card_sdiff_add_card_eq_card hTC
  have hZD : ∀ w, w ∈ Zreg n C → w ∉ D := by
    intro w hz hd
    obtain ⟨v, hv⟩ := (mem_Dreg.1 hd).2.1
    rw [(mem_Zreg.1 hz).2 v] at hv
    exact Bool.false_ne_true hv

  have hcomp : ∀ r ∈ Rt, ∃ e ∈ extE n C D, root A e.1 = r := by
    intro r hr
    let K := D.filter (fun w => root A w = r)
    have hKne : K.Nonempty := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hr
      exact ⟨w, Finset.mem_filter.2 ⟨hw, rfl⟩⟩
    have hK : ∀ w ∈ K, Live n C w ∧ w ≠ C.output := by
      intro w hw
      have hwD := (Finset.mem_filter.1 hw).1
      refine ⟨(mem_Dreg.1 hwD).1.2, fun e => ?_⟩
      obtain ⟨v, hv⟩ := (mem_Dreg.1 hwD).2.1
      rw [e, point_single_quiet H.eval] at hv
      exact Bool.false_ne_true hv
    obtain ⟨b, hb, hbK⟩ := max_exit K hKne hK
    have hmK := Finset.mem_filter.1 (K.max'_mem hKne)
    refine ⟨(K.max' hKne, b), mem_extE.2 ⟨hb, hmK.1, fun hbD => hbK ?_⟩, hmK.2⟩
    exact Finset.mem_filter.2 ⟨hbD,
      (root_eq DAdj_symm (ReflTransGen.single ⟨hmK.1, hbD, Or.inl hb⟩)).symm.trans hmK.2⟩
  choose! ex hex using hcomp
  have hX1 : (Rt \ TC).card ≤ ((extE n C D).filter (fun e => ¬ root A e.1 ∈ TC)).card := by
    apply Finset.card_le_card_of_injOn ex
    · intro r hr
      have hr' := Finset.mem_sdiff.1 hr
      obtain ⟨he, hroot⟩ := hex r hr'.1
      exact Finset.mem_filter.2 ⟨he, by rw [hroot]; exact hr'.2⟩
    · intro r hr r' hr' heq
      have h1 := (hex r (Finset.mem_sdiff.1 hr).1).2
      have h2 := (hex r' (Finset.mem_sdiff.1 hr').1).2
      exact h1.symm.trans ((congrArg (fun e => root A e.1) heq).trans h2)
  have hX2 : NE.card ≤ ((extE n C D).filter (fun e => root A e.1 ∈ TC)).card := by
    apply Finset.card_le_card_of_injOn (fun u => (a u, g u))
    · intro u hu
      obtain ⟨_, _, _, hag, _, _, hgZ, haD, _⟩ := hterm u hu
      exact Finset.mem_filter.2 ⟨mem_extE.2 ⟨hag, haD, hZD _ hgZ⟩,
        Finset.mem_image.2 ⟨u, hu, rfl⟩⟩
    · intro u hu u' hu' heq
      have hgg : g u = g u' := congrArg Prod.snd heq
      obtain ⟨_, hsm, _, _, _, hin, _, _, hT⟩ := hterm u hu
      obtain ⟨_, hsm', hmg', _, _, _, _, _, _⟩ := hterm u' hu'
      rw [← hgg] at hmg'
      exact exit_inj H hsm hT hin hsm' hmg'
  have hX : (Rt \ TC).card + NE.card ≤ (extE n C D).card := by
    have := Finset.card_filter_add_card_filter_not (s := extE n C D) (fun e => root A e.1 ∈ TC)
    omega

  have hTU := T_sub_U H
  have hU : ∀ c ∈ TC, d ≤ (Uset n C c).card := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨_, _, _, _, _, _, _, haD, hT⟩ := hterm u hu
    obtain ⟨S, hS, hSA⟩ := H.deg u
    exact hS.trans (Finset.card_le_card fun t ht => hTU (a u) haD t (hT t (hSA t ht)))
  let Ent := (Edges n C).filter (fun e => e.2 ∈ D ∧ root A e.2 ∈ TC ∧ ∃ u', e.1 ∈ Preg n C u')
  have hEnt1 : ∀ c ∈ TC, (Uset n C c).card ≤ (Ent.filter (fun e => root A e.2 = c)).card := by
    intro c hc
    have hpick : ∀ u' ∈ Uset n C c, ∃ e ∈ Edges n C,
        e.1 ∈ Preg n C u' ∧ e.2 ∈ D ∧ root A e.2 = c := fun u' hu' => mem_Uset.1 hu'
    choose! pk hpk using hpick
    apply Finset.card_le_card_of_injOn pk
    · intro u' hu'
      obtain ⟨h1, h2, h3, h4⟩ := hpk u' hu'
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨h1, h3, h4 ▸ hc, u', h2⟩, h4⟩
    · intro u' hu' u'' hu'' heq
      have h1 := (hpk u' hu').2.1
      have h2 := (hpk u'' hu'').2.1
      rw [heq] at h1
      exact Preg_disj h1 h2
  have hEnt2 : Ent.card = ∑ c ∈ TC, (Ent.filter (fun e => root A e.2 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => (Finset.mem_filter.1 he).2.2.1)
  have hEnt3 : Ent.card ≤ ∑ u ∈ El, ec n C u := by
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro e he
    obtain ⟨heE, heD, _, u', hu'⟩ := Finset.mem_filter.1 he
    have hx : e ∈ extE n C (Preg n C u') :=
      mem_extE.2 ⟨mem_Edges.1 heE, hu', fun h => (mem_Dreg.1 heD).2.2 u' h⟩
    refine Finset.mem_biUnion.2 ⟨u', (hEl u').2 fun hterm' => ?_, hx⟩
    obtain ⟨hall, _, _, _, _, _, hgZ, _, _⟩ := hterm u' ((hNE u').2 hterm')
    rw [hall e hx] at heD
    exact hZD _ hgZ heD
  have hentries : d * TC.card ≤ ∑ u ∈ El, ec n C u := by
    have h1 : d * TC.card ≤ ∑ c ∈ TC, (Uset n C c).card := by
      calc d * TC.card = TC.card • d := by rw [smul_eq_mul, mul_comm]
        _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ hU
    have h2 : ∑ c ∈ TC, (Uset n C c).card ≤ ∑ c ∈ TC, (Ent.filter (fun e => root A e.2 = c)).card :=
      Finset.sum_le_sum hEnt1
    exact h1.trans (h2.trans (hEnt2.symm.le.trans hEnt3))

  have f1 : ∑ u : Fin n, (outE n C (Preg n C u)).card + (outE n C D).card +
      (outE n C (Zreg n C)).card ≤ (Edges n C).card := edges_split
  have f1a : ∑ u : Fin n, (outE n C (Preg n C u)).card = ∑ u : Fin n, (ic n C u + ec n C u) :=
    Finset.sum_congr rfl (fun u _ => card_outE _)
  have f1b : (outE n C D).card = (intE n C D).card + (extE n C D).card := card_outE D
  have f2 : (living n C).card ≤ (∑ u : Fin n, pc n C u) + D.card + (Zreg n C).card :=
    living_cover
  have f3 : D.card ≤ (intE n C D).card + Rt.card := hforest
  have f5 : (Zreg n C).card ≤ (outE n C (Zreg n C)).card + 1 :=
    out_bound _ (fun w hw => (mem_Zreg.1 hw).1.2)
  have f6 : (Edges n C).card ≤ 2 * ((living n C).filter (fun j => ¬ j < n)).card :=
    edges_le H.mono
  have f6b : (living n C).card = n + ((living n C).filter (fun j => ¬ j < n)).card :=
    living_eq H
  have hcard : NE.card + El.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun u => ic n C u + ec n C u ≤ pc n C u)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hmain : ((((living n C).filter (fun j => ¬ j < n)).card : ℕ) : ℤ) + 1 +
      ((∑ u : Fin n, pc n C u : ℕ) : ℤ) + TC.card ≥
      ((∑ u : Fin n, (ic n C u + ec n C u) : ℕ) : ℤ) + n + NE.card := by
    omega

  have hz : ∀ u ∈ (Finset.univ : Finset (Fin n)), u ∉ El →
      ((ic n C u : ℤ) + ec n C u - pc n C u) = 0 := by
    intro u _ hu
    have h1 : ic n C u + ec n C u ≤ pc n C u := by
      by_contra h
      exact hu ((hEl u).2 h)
    have h2 : pc n C u ≤ ic n C u + 1 := int_bound u
    have h3 : 1 ≤ ec n C u := ext_pos H u
    omega
  have hS1 : ((∑ u : Fin n, (ic n C u + ec n C u) : ℕ) : ℤ) =
      ((∑ u : Fin n, pc n C u : ℕ) : ℤ) + ∑ u ∈ El, ((ic n C u : ℤ) + ec n C u - pc n C u) := by
    rw [Finset.sum_subset (Finset.subset_univ El) hz]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hper : ∀ u ∈ El, (ec n C u : ℤ) + d ≤ d * ((ic n C u : ℤ) + ec n C u - pc n C u) + 2 := by
    intro u hu
    have h1 := (hEl u).1 hu
    have h2 : pc n C u ≤ ic n C u + 1 := int_bound u
    have h3 : 2 ≤ d := H.two
    have h4 : (0:ℤ) ≤ ((d:ℤ) - 1) * ((ic n C u : ℤ) + ec n C u - pc n C u - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have hS2 := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul] at hS2
  have hS3 := Finset.card_nsmul_le_sum El (fun u => (ic n C u : ℤ) + ec n C u - pc n C u) 1
    (fun u hu => by have := (hEl u).1 hu; omega)
  rw [nsmul_eq_mul, mul_one] at hS3
  have hentZ : (d : ℤ) * TC.card ≤ ∑ u ∈ El, (ec n C u : ℤ) := by exact_mod_cast hentries
  have hτZ : (TC.card : ℤ) ≤ NE.card := by exact_mod_cast hτ
  have hcardZ : (NE.card : ℤ) + El.card = n := by exact_mod_cast hcard
  rw [hS1] at hmain
  set X := ∑ u ∈ El, ((ic n C u : ℤ) + ec n C u - pc n C u) with hX
  set sg := ((living n C).filter (fun j => ¬ j < n)).card with hsg
  have hfin : (2 * n * (d + 1) : ℤ) ≤ (d + 2) * (sg + 1) :=
    final_arith (sg : ℤ) n d TC.card X NE.card El.card (∑ u ∈ El, (ec n C u : ℤ))
      (by linarith) hS2 hS3 hentZ hτZ hcardZ (by positivity)
  exact_mod_cast hfin

end Count

section Plane

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
    (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)
  symm := ⟨by
    rintro u v ⟨p,l,h,hp,hl⟩
    exact ⟨p,l,h,hp.symm,hl.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨p,l,h,hp,hl⟩
    exact left_ne_right p l ((hp.elim id id).trans (hl.elim id id).symm)⟩

theorem adj_ll {N : ℕ} (I : Fin N → Fin N → Prop) (p r : Fin N) :
    ¬ (graph I).Adj (Fin.castAdd N p) (Fin.castAdd N r) := by
  rintro ⟨a,b,_,_,h⟩
  exact h.elim (fun he => left_ne_right p b he.symm) (fun he => left_ne_right r b he.symm)

theorem adj_rr {N : ℕ} (I : Fin N → Fin N → Prop) (l m : Fin N) :
    ¬ (graph I).Adj (Fin.natAdd N l) (Fin.natAdd N m) := by
  rintro ⟨a,b,_,h,_⟩
  exact h.elim (left_ne_right a l) (left_ne_right a m)

theorem adj_lr {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hp := Fin.castAdd_inj.mp (ha.resolve_right (left_ne_right a l))
    have hl := (Fin.natAdd_inj N).mp (hb.resolve_left (left_ne_right p b).symm)
    simpa [hp,hl] using hab
  · intro hi
    exact ⟨p,l,hi,Or.inl rfl,Or.inr rfl⟩

theorem adj_rl {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    (graph I).Adj (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l :=
  ((graph I).adj_comm _ _).trans (adj_lr I p l)

theorem no_square {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (uv : u ≠ v) (ab : a ≠ b)
    (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
    (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
  have rect {p r l m : Fin N} (pr : p ≠ r) (lm : l ≠ m)
      (pl : I p l) (rl : I r l) (pm : I p m) (rm : I r m) : False :=
    lm ((hu p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp_all only [adj_ll,adj_rr,adj_lr,adj_rl]
  all_goals first
    | exact rect (fun e => uv (congrArg (Fin.castAdd N) e)) (fun e => ab (congrArg (Fin.natAdd N) e)) ua va ub vb
    | exact rect (fun e => ab (congrArg (Fin.castAdd N) e)) (fun e => uv (congrArg (Fin.natAdd N) e)) ua ub va vb

theorem no_triangle {N : ℕ} (I : Fin N → Fin N → Prop) (x y z : Fin (N+N))
    (hxy : (graph I).Adj x y) (hyz : (graph I).Adj y z) (hxz : (graph I).Adj x z) : False := by
  induction x using Fin.addCases <;> induction y using Fin.addCases <;>
    induction z using Fin.addCases <;> simp_all only [adj_ll, adj_rr]

theorem plane_dist {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l)
    (two : ∀ u : Fin (N+N), ∃ a b, a ≠ b ∧ (graph I).Adj u a ∧ (graph I).Adj u b)
    (u v : Fin (N+N)) (huv : u ≠ v) :
    ∃ t, (graph I).Adj u t ∧ ¬ (graph I).Adj v t ∧ t ≠ v := by
  obtain ⟨a, b, hab, hua, hub⟩ := two u
  by_cases ha : ¬ (graph I).Adj v a ∧ a ≠ v
  · exact ⟨a, hua, ha.1, ha.2⟩
  by_cases hb : ¬ (graph I).Adj v b ∧ b ≠ v
  · exact ⟨b, hub, hb.1, hb.2⟩
  exfalso
  have ha' : (graph I).Adj v a ∨ a = v := by
    by_contra h
    exact ha ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
  have hb' : (graph I).Adj v b ∨ b = v := by
    by_contra h
    exact hb ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
  rcases ha' with ha' | hav <;> rcases hb' with hb' | hbv
  · exact no_square I hu u v a b huv hab hua hub ha' hb'
  · exact no_triangle I u v a (hbv ▸ hub) ha' hua
  · exact no_triangle I u v b (hav ▸ hua) hb' hub
  · exact hab (hav.trans hbv.symm)

theorem plane_good {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hshape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + p)
    (hInc : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hRej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) :
    Good (N + N) C (graph I) (q + 1) := by
  classical
  let G := graph I
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    rw [← Fintype.card_coe]
    refine (Fintype.card_congr (Equiv.subtypeEquivRight ?_)).trans (hline l)
    intro p; simp
  have rows := lines_through q N I hq hN cols hu
  have deg : ∀ u : Fin (N+N), ∃ S : Finset (Fin (N+N)), q + 1 ≤ S.card ∧
      ∀ t ∈ S, G.Adj u t := by
    intro u
    induction u using Fin.addCases with
    | left p =>
      refine ⟨(Finset.univ.filter (fun l => I p l)).map
        ⟨Fin.natAdd N, fun _ _ => (Fin.natAdd_inj N).mp⟩, ?_, ?_⟩
      · rw [Finset.card_map, rows p]
      · intro t ht
        obtain ⟨l, hl, rfl⟩ := Finset.mem_map.1 ht
        exact (adj_lr I p l).2 (Finset.mem_filter.1 hl).2
    | right l =>
      refine ⟨(Finset.univ.filter (fun p => I p l)).map
        ⟨Fin.castAdd N, fun _ _ => Fin.castAdd_inj.mp⟩, ?_, ?_⟩
      · rw [Finset.card_map, cols l]
      · intro t ht
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 ht
        exact (adj_rl I l p).2 (Finset.mem_filter.1 hp).2
  have two : ∀ u : Fin (N+N), ∃ a b, a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
    intro u
    obtain ⟨S, hS, hA⟩ := deg u
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    exact ⟨a, b, hab, hA a ha, hA b hb⟩
  have eval : GraphEval C G := by
    intro a b
    have hfn : point ({a, b} : Finset (Fin (N + N))) = fun z => decide (z = a ∨ z = b) := by
      funext z; simp [point]
    change circuitFun (N + N) C (point {a, b}) = true ↔ G.Adj a b
    rw [hfn]
    constructor
    · intro ht
      by_contra hnot
      have hcnt : Fintype.card { l : Fin N //
          decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } ≤ q := by
        have hle2 : (Finset.univ.filter
            (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card ≤ 2 := by
          have hsub : Finset.univ.filter
              (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b) ⊆
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)) ∪
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)) := by
            intro l hl
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
            exact hl
          have hc1 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp
              ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          have hc2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp
              ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
        have hceq : Fintype.card { l : Fin N //
            decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } =
            (Finset.univ.filter
              (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card := by
          rw [← Fintype.card_coe]
          apply Fintype.card_congr
          apply Equiv.subtypeEquivRight
          intro l; simp
        omega
      have hno : ¬ ∃ p l : Fin N, I p l ∧
          decide (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) = true ∧
          decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true := by
        rintro ⟨p, l, hpl, hp, hl⟩
        simp only [decide_eq_true_eq] at hp hl
        exact hnot ⟨p, l, hpl, hp, hl⟩
      have hf := hRej (fun z => decide (z = a ∨ z = b)) hcnt hno
      rw [hf] at ht
      exact Bool.false_ne_true ht
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hset : (fun z : Fin (N + N) => decide (z = a ∨ z = b)) =
          (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
        funext z
        have hne : Fin.castAdd N p ≠ Fin.natAdd N l := left_ne_right p l
        rcases hp with rfl | rfl <;> rcases hl with h2 | h2
        · exact (hne h2.symm).elim
        · subst h2; rfl
        · subst h2; simp [or_comm]
        · exact (hne h2.symm).elim
      rw [hset]
      exact hInc p l hpl
  exact ⟨hC, hshape, eval, by omega, deg, plane_dist I hu two⟩

theorem weighted_base (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hshape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + p)
    (hInc : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hRej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) :
    4*N*(q+2) ≤ (q+3)*(C.size+1) := by
  have H := plane_good q I C (by omega) hN hline hu hC hshape hInc hRej
  have hm := main_count H
  have hs := gates_le (n := N + N) (C := C)
  have h4 : 4 * N * (q + 2) ≤ (q + 3) * (C.size + 1) :=
    calc 4 * N * (q + 2) = 2 * (N + N) * (q + 1 + 1) := by ring
      _ ≤ (q + 1 + 2) * (((living (N + N) C).filter (fun j => ¬ j < N + N)).card + 1) := hm
      _ ≤ (q + 3) * (C.size + 1) := Nat.mul_le_mul (le_of_eq (by ring)) (Nat.add_le_add_right hs 1)
  exact h4

end Plane

end PencilArithmetic3471


namespace Order399
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.TopForm
theorem weighted (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 2 ≤ q) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    4*N*(q+2) ≤ (q+3)*(C.size+1) := by
  classical
  let I := fun p l : Fin N => p ∈ S l
  have deg (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa [I,Fintype.card_subtype] using col l
  have hit (p l : Fin N) (h : I p l) : circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true := by
    let x : Fin (N+N) → Bool := Fin.addCases (fun a => decide (a∈({p}:Finset (Fin N)))) (fun b => decide (b∈({l}:Finset (Fin N))))
    have raw : List.ofFn x = incidenceInput {p} {l} := List.ofFn_fin_append _ _
    have fn : x = (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · change x (Fin.castAdd N a) = _
        rw [show x (Fin.castAdd N a) = decide (a∈({p}:Finset (Fin N))) from Fin.addCases_left ..]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,PencilArithmetic3471.left_ne_right a l,or_false]
      · change x (Fin.natAdd N b) = _
        rw [show x (Fin.natAdd N b) = decide (b∈({l}:Finset (Fin N))) from Fin.addCases_right ..]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (PencilArithmetic3471.left_ne_right p b),false_or]
    rw [←fn]
    change C.eval (List.ofFn x)=true
    rw [raw]
    exact pos l p h
  have off (x : Fin (N+N) → Bool) (lim : Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q)
      (none : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) : circuitFun (N+N) C x=false := by
    let X := Finset.univ.filter (fun p => x (Fin.castAdd N p)=true)
    let Y := Finset.univ.filter (fun l => x (Fin.natAdd N l)=true)
    have eq : x = Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y)) := by
      funext i
      refine Fin.addCases (fun p => ?_) (fun l => ?_) i
      · rw [Fin.addCases_left]; simp [X]
      · rw [Fin.addCases_right]; simp [Y]
    have raw : List.ofFn x = incidenceInput X Y := by rw [eq]; exact List.ofFn_fin_append _ _
    change C.eval (List.ofFn x)=false
    rw [raw]
    apply sound X Y
    · simpa [Y,Fintype.card_subtype] using lim
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact none ⟨p,l,hp,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have npos : 0<N := by omega
  let l : Fin N := ⟨0,npos⟩
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (S l).card by rw [col]; omega)
  have on := hit p l hp
  have zero := off (fun _ => false) (by simp) (by simp)
  obtain ⟨D,dm,ds,de,-,shape⟩ := Sorted3471 (N+N) C mon ⟨(fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l)),(fun _ => false),by rw [on,zero]; decide⟩
  have w := PencilArithmetic3471.weighted_base q N I D hq ord deg uniq dm shape
    (by rw [de]; exact hit) (by rw [de]; exact off)
  exact w.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ ds))

theorem fourSquarePlusEleven (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 26 ≤ q) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    4*q^2+11 ≤ C.size := by
  have budget := weighted q N S C (by omega) ord col uniq ao pos sound
  rw [ord] at budget
  by_contra! lt
  have s : C.size+1 ≤ 4*q^2+11 := by omega
  have scaled := Nat.mul_le_mul_left (q+3) s
  nlinarith only [budget,scaled,hq]

theorem through399 (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hi : q ≤ 399) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    N*q ≤ 100*C.size := by
  have pay := fourSquarePlusEleven q N S C (by omega) ord col uniq ao pos sound
  have cub := Nat.mul_le_mul_left (q^2) hi
  rw [ord]
  nlinarith only [pay,cub,hi]

end Order399

namespace Half3471


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

private def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

private def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

private def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

private def Thin {N : ℕ} (z : Fin (N+N) → Bool) : Prop :=
  ∀ l l' : Fin N, z (Fin.natAdd N l) = true → z (Fin.natAdd N l') = true → l = l'

private lemma thin_pair {N : ℕ} (p l : Fin N) : Thin (pair p l) := by
  intro i j hi hj
  simp only [pair,decide_eq_true_eq] at hi hj
  exact Fin.natAdd_injective _ _ ((hi.resolve_left (Ne.symm (cast_ne_nat p i))).trans (hj.resolve_left (Ne.symm (cast_ne_nat p j))).symm)

private lemma thin_point {N : ℕ} (p : Fin N) : Thin (point p) := by
  intro i j hi
  exact ((cast_ne_nat p i) (of_decide_eq_true hi).symm).elim

private lemma thin_line {N : ℕ} (l : Fin N) : Thin (line l) := by
  intro i j hi hj
  simp [line] at hi hj
  exact hi.trans hj.symm

private lemma plane_support (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hq2 : 2 ≤ q) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  have hpair (p l : Fin N) (h : I p l) : circuitFun (N + N) C (pair p l) = true := by
    rw [hC _ (thin_pair p l), decide_eq_true_eq]
    exact ⟨p, l, h, by simp [pair], by simp [pair]⟩
  have hpoint (p : Fin N) : circuitFun (N + N) C (point p) = false := by
    rw [hC _ (thin_point p), decide_eq_false_iff_not]
    rintro ⟨_, l, _, _, h⟩
    exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline (l : Fin N) : circuitFun (N + N) C (line l) = false := by
    rw [hC _ (thin_line l), decide_eq_false_iff_not]
    rintro ⟨p, _, _, h, _⟩
    exact cast_ne_nat p l (of_decide_eq_true h)
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]


section ReadWitness


open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 2 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section Degrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

private def on (N : ℕ) (X Y : Set (Fin N)) (w : ℕ) : Prop :=
  (∃ p ∈ X, (p : ℕ) = w) ∨ ∃ l ∈ Y, N + (l : ℕ) = w

private lemma on_point {N : ℕ} (X Y : Set (Fin N)) (p : Fin N) :
    on N X Y p.val ↔ p ∈ X := by
  constructor
  · rintro (⟨q, hq, hv⟩ | ⟨l, _, hv⟩)
    · exact (Fin.ext hv : q = p) ▸ hq
    · omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

private lemma on_line {N : ℕ} (X Y : Set (Fin N)) (l : Fin N) :
    on N X Y (N + l.val) ↔ l ∈ Y := by
  constructor
  · rintro (⟨p, _, hv⟩ | ⟨l', hl', hv⟩)
    · omega
    · exact (Fin.ext (Nat.add_left_cancel hv) : l' = l) ▸ hl'
  · exact fun hl => Or.inr ⟨l, hl, rfl⟩

private noncomputable def bits {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) : Bool := by
  classical
  exact decide (on N X Y i.val)

private lemma bits_true {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) :
    bits X Y i = true ↔ on N X Y i.val := by
  classical
  simp [bits]

private def pcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (w < N)).length
private def lcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (N ≤ w)).length

private lemma sum_counts (N : ℕ) (t : List ℕ) : pcount N t + lcount N t = t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a < N
    · have hn : ¬ N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega
    · have hn : N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega

private def Hom (N : ℕ) (C : Circuit) (w a b : ℕ) (X Y : Set (Fin N)) : Prop :=
  ∃ t ∈ words (N + N) C w, pcount N t = a ∧ lcount N t = b ∧ ∀ j ∈ t, on N X Y j

private lemma hom_mono {N : ℕ} {C : Circuit} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (h : Hom N C w a b X Y) : Hom N C w a b X' Y' := by
  obtain ⟨t, ht, ha, hb, hxy⟩ := h
  exact ⟨t, ht, ha, hb, fun j hj => (hxy j hj).imp
    (fun ⟨p, hp, he⟩ => ⟨p, hx hp, he⟩) (fun ⟨l, hl, he⟩ => ⟨l, hy hl, he⟩)⟩

private lemma hom_pure_x {N : ℕ} {C : Circuit} {w a : ℕ} {X Y : Set (Fin N)} :
    Hom N C w a 0 X Y ↔ Hom N C w a 0 X ∅ := by
  refine ⟨?_, hom_mono (fun _ h => h) (Set.empty_subset _)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with hp | ⟨l, _, hl⟩
  · exact Or.inl hp
  · have hn : N ≤ j := by omega
    have hmem : j ∈ t.filter (fun w => decide (N ≤ w)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold lcount at hb
    rw [List.length_eq_zero_iff.mp hb] at hmem
    simp at hmem

private lemma hom_pure_y {N : ℕ} {C : Circuit} {w b : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 0 b X Y ↔ Hom N C w 0 b ∅ Y := by
  refine ⟨?_, hom_mono (Set.empty_subset _) (fun _ h => h)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, _, hp⟩ | hl
  · have hn : j < N := hp ▸ p.isLt
    have hmem : j ∈ t.filter (fun w => decide (w < N)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold pcount at ha
    rw [List.length_eq_zero_iff.mp ha] at hmem
    simp at hmem
  · exact Or.inr hl

private lemma hom_invalid {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ Hom N C w a b X Y := by
  simp [Hom, words_missing _ _ hw]

private lemma hom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) : 0 < a + b := by
  obtain ⟨t, ht, ha, hb, _⟩ := hh
  rw [← ha, ← hb, sum_counts]
  exact List.length_pos_iff.mpr (words_nonempty h ht)

private lemma hom_input {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)} (hw : w < N + N) :
    Hom N C w a b X Y ↔ on N X Y w ∧
      ((w < N ∧ a = 1 ∧ b = 0) ∨ (N ≤ w ∧ a = 0 ∧ b = 1)) := by
  unfold Hom
  rw [words_input C hw]
  by_cases h : w < N
  · have h' : ¬ N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]
  · have h' : N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]

private lemma hom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, Hom N C (operand C k i) a b X Y := by
  rw [Fin.exists_fin_two]
  unfold Hom
  rw [words_gate h k, ho]
  simp only [wordOp, Set.mem_union]
  exact ⟨fun ⟨t, hr, he⟩ => hr.imp (fun ht => ⟨t, ht, he⟩) (fun ht => ⟨t, ht, he⟩),
    fun h => h.elim (fun ⟨t, ht, he⟩ => ⟨t, Or.inl ht, he⟩) (fun ⟨t, ht, he⟩ => ⟨t, Or.inr ht, he⟩)⟩

private lemma hom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        Hom N C (operand C k 0) a₀ b₀ X Y ∧ Hom N C (operand C k 1) a₁ b₁ X Y := by
  unfold Hom
  rw [words_gate h k, ho]
  constructor
  · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, ha, hb, hxy⟩
    exact ⟨pcount N t, lcount N t, pcount N u, lcount N u, by simpa [pcount] using ha,
      by simpa [lcount] using hb, ⟨t, ht, rfl, rfl, fun j hj => hxy j (List.mem_append_left _ hj)⟩,
      ⟨u, hu, rfl, rfl, fun j hj => hxy j (List.mem_append_right _ hj)⟩⟩
  · rintro ⟨a₀, b₀, a₁, b₁, ha, hb, ⟨t, ht, rfl, rfl, hxy⟩, ⟨u, hu, rfl, rfl, hxy'⟩⟩
    exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, by simpa [pcount] using ha,
      by simpa [lcount] using hb, fun j hj => (List.mem_append.mp hj).elim (hxy j) (hxy' j)⟩

private lemma hom_and_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) (i : Fin 2)
    {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : Hom N C (operand C k i) a b X Y)
    (h₂ : Hom N C (operand C k (1 - i)) c d X Y) :
    Hom N C (outWire (N + N) k) (a + c) (b + d) X Y := by
  apply (hom_and h ho).mpr
  fin_cases i
  · exact ⟨a, b, c, d, rfl, rfl, h₁, h₂⟩
  · exact ⟨c, d, a, b, Nat.add_comm _ _, Nat.add_comm _ _, h₂, h₁⟩

private lemma hom_sound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) :
    circuitValue C (bits X Y) w = true := by
  obtain ⟨t, ht, _, _, hxy⟩ := hh
  apply (value_eq_terms h _ _).mpr
  refine ⟨t, ht, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨Fin.castAdd N p, rfl, (bits_true _ _ _).mpr ((on_point X Y p).mpr hp)⟩
  · exact ⟨Fin.natAdd N l, rfl, (bits_true _ _ _).mpr ((on_line X Y l).mpr hl)⟩

end Degrees


open Finset

section Charging


variable {A B W E : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]

private def fourFree : Prop :=
  ∀ ⦃c d : B⦄, c ≠ d → ∀ ⦃a b : A⦄, I a c → I a d → I b c → I b d → a = b

private noncomputable def single (f : Set A → Prop) : Finset A := by
  classical
  exact univ.filter (fun a => f {a})

private lemma mem_single (f : Set A → Prop) (a : A) : a ∈ single f ↔ f {a} := by
  classical
  simp [single]

private def clean (f : Set A → Prop) (c : B) : Prop :=
  ¬ f {a | ¬ I a c}

private lemma clean_single {f : Set A → Prop} (hm : Monotone f) {a : A} {c : B}
    (hc : clean I f c) (ha : a ∈ single f) : I a c := by
  by_contra hn
  exact hc (hm (Set.singleton_subset_iff.mpr hn) ((mem_single f a).mp ha))

private def almost (s : Finset A) (c : B) : Prop :=
  (s.filter fun a => ¬ I a c).card ≤ 1

private def approved (simple : Prop) (f : Set A → Prop) (c : B) : Prop :=
  (2 ≤ (single f).card ∧ clean I f c) ∨
    (simple ∧ 4 ≤ (single f).card ∧ almost I (single f) c)

private lemma almost_of_clean {f : Set A → Prop} (hm : Monotone f) {c : B}
    (hc : clean I f c) : almost I (single f) c := by
  classical
  have hzero : (single f).filter (fun a => ¬ I a c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact (Finset.mem_filter.mp ha).2 (clean_single I hm hc (Finset.mem_filter.mp ha).1)
  simp [almost, hzero]

private lemma almost_mono {s t : Finset A} (hst : s ⊆ t) {c : B}
    (h : almost I t c) : almost I s c :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hst)).trans h

private lemma almost_unique (hf : fourFree I) (s : Finset A) (hs : 4 ≤ s.card)
    {c d : B} (hc : almost I s c) (hd : almost I s d) : c = d := by
  classical
  by_contra hcd
  let good := s.filter (fun a => I a c ∧ I a d)
  have hgood : good.card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  let badC := s.filter (fun a => ¬ I a c)
  let badD := s.filter (fun a => ¬ I a d)
  have hcover : s ⊆ good ∪ (badC ∪ badD) := by
    intro a ha
    by_cases h1 : I a c <;> by_cases h2 : I a d <;> simp [good, badC, badD, ha, h1, h2]
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le good (badC ∪ badD))
  have hbad := Finset.card_union_le badC badD
  change badC.card ≤ 1 at hc
  change badD.card ≤ 1 at hd
  omega

private lemma exact_unique (hf : fourFree I) {f : Set A → Prop} (hm : Monotone f)
    (hs : 2 ≤ (single f).card) {c d : B} (hc : clean I f c) (hd : clean I f d) : c = d := by
  classical
  by_contra hcd
  have hcard : (single f).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (clean_single I hm hc ha) (clean_single I hm hd ha)
      (clean_single I hm hc hb) (clean_single I hm hd hb)
  omega

private lemma approved_unique (hf : fourFree I) {simple : Prop} {f : Set A → Prop}
    (hm : Monotone f) {c d : B} (hc : approved I simple f c) (hd : approved I simple f d) :
    c = d := by
  rcases hc with ⟨hs, hc⟩ | ⟨_, hs, hc⟩ <;> rcases hd with ⟨_, hd⟩ | ⟨_, hsd, hd⟩
  · exact exact_unique I hf hm hs hc hd
  · exact almost_unique I hf _ hsd (almost_of_clean I hm hc) hd
  · exact almost_unique I hf _ hs hc (almost_of_clean I hm hd)
  · exact almost_unique I hf _ hs hc hd

private lemma small_unapproved (simple : Prop) (f : Set A → Prop) (c : B)
    (simple_spec : simple → ∀ U, f U ↔ ∃ a ∈ single f, a ∈ U)
    (h : ¬ approved I simple f c)
    (ha : clean I f c ∨ simple ∧ almost I (single f) c) :
    ((single f).filter fun a => I a c).card ≤ 2 := by
  classical
  by_contra hbad
  have hs : 3 ≤ (single f).card := by
    have hcard := Finset.card_filter_le (single f) (fun a => I a c)
    omega
  rcases ha with hc | ⟨hsim, halm⟩
  · exact h (Or.inl ⟨by omega, hc⟩)
  by_cases h4 : 4 ≤ (single f).card
  · exact h (Or.inr ⟨hsim, h4, halm⟩)
  have hcard := Finset.card_filter_add_card_filter_not
    (s := single f) (p := fun a => I a c)
  have he : ((single f).filter fun a => ¬ I a c).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp he
  have hclean : clean I f c := by
    intro ht
    obtain ⟨a, ha, hni⟩ := (simple_spec hsim _).mp ht
    have hm' : a ∈ (single f).filter (fun a => ¬ I a c) := Finset.mem_filter.mpr ⟨ha, hni⟩
    simp [hempty] at hm'
  exact h (Or.inl ⟨by omega, hclean⟩)

private noncomputable def edgeCover (f : W → Set A → Prop) (simple : W → Prop) : Finset (A × B) := by
  classical
  exact univ.filter (fun p => I p.1 p.2 ∧ ∃ w, approved I (simple w) (f w) p.2 ∧
    p.1 ∈ single (f w))

private lemma cover_bound (hf : fourFree I) (f : W → Set A → Prop) (simple : W → Prop)
    (rank : W → ℕ) (arcs : Finset E) (src dst : E → W)
    (hm : ∀ w, Monotone (f w))
    (hs : ∀ w, simple w → ∀ U, f w U ↔ ∃ a ∈ single (f w), a ∈ U)
    (hr : ∀ w,
      (∀ c, ¬ approved I (simple w) (f w) c) ∨
      (∃ u v, rank u < rank w ∧ rank v < rank w ∧ ¬ simple w ∧
        ∀ U, f w U ↔ f u U ∧ f v U) ∨
      ((∀ e ∈ arcs, src e = w → rank (dst e) < rank w ∧ (simple w → simple (dst e))) ∧
        ∀ U, f w U ↔ ∃ e ∈ arcs, src e = w ∧ f (dst e) U)) :
    (edgeCover I f simple).card ≤ 2 * arcs.card := by
  classical
  let Pay (e : E) : Finset (A × B) := univ.filter fun p => I p.1 p.2 ∧
    approved I (simple (src e)) (f (src e)) p.2 ∧
    ¬ approved I (simple (dst e)) (f (dst e)) p.2 ∧
    (clean I (f (dst e)) p.2 ∨ simple (dst e) ∧ almost I (single (f (dst e))) p.2) ∧
    p.1 ∈ single (f (dst e))
  have pay_card (e : E) : (Pay e).card ≤ 2 := by
    by_cases hn : (Pay e).Nonempty
    · obtain ⟨p, hp⟩ := hn
      have hpv := (Finset.mem_filter.mp hp).2
      refine le_trans (Finset.card_le_card_of_injOn (t := (single (f (dst e))).filter (fun a => I a p.2)) Prod.fst ?_ ?_) ?_
      · intro q hq
        have hqv := (Finset.mem_filter.mp hq).2
        have he := approved_unique I hf (hm (src e)) hqv.2.1 hpv.2.1
        exact Finset.mem_filter.mpr ⟨hqv.2.2.2.2, he ▸ hqv.1⟩
      · intro q hq r hrr he
        exact Prod.ext he (approved_unique I hf (hm (src e))
          (Finset.mem_filter.mp hq).2.2.1 (Finset.mem_filter.mp hrr).2.2.1)
      · exact small_unapproved I _ _ _ (hs (dst e)) hpv.2.2.1 hpv.2.2.2.1
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have descend (w : W) (p : A × B) (hi : I p.1 p.2)
      (ha : approved I (simple w) (f w) p.2) (hsp : p.1 ∈ single (f w)) :
      ∃ e ∈ arcs, p ∈ Pay e := by
    induction ht : rank w using Nat.strong_induction_on generalizing w with
    | ind k ih =>
      rcases hr w with hl | ⟨u, v, hu, hv, hn, hmeet⟩ | ⟨hsub, hunion⟩
      · exact (hl _ ha).elim
      · have hw := (mem_single _ _).mp hsp
        obtain ⟨hpu, hpv⟩ := (hmeet _).mp hw
        obtain ⟨_, hc⟩ := ha.resolve_right (fun h => hn h.1)
        have hcu : clean I (f u) p.2 ∨ clean I (f v) p.2 := by
          by_cases hu : f u {a | ¬ I a p.2}
          · exact Or.inr (fun hv => hc ((hmeet _).mpr ⟨hu, hv⟩))
          · exact Or.inl hu
        have hSu : single (f w) ⊆ single (f u) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).1
        have hSv : single (f w) ⊆ single (f v) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).2
        have hs2 : 2 ≤ (single (f w)).card := (ha.resolve_right (fun h => hn h.1)).1
        rcases hcu with hcu | hcv
        · exact ih (rank u) (ht ▸ hu) u (Or.inl ⟨hs2.trans (Finset.card_le_card hSu), hcu⟩)
            ((mem_single _ _).mpr hpu) rfl
        · exact ih (rank v) (ht ▸ hv) v (Or.inl ⟨hs2.trans (Finset.card_le_card hSv), hcv⟩)
            ((mem_single _ _).mpr hpv) rfl
      · obtain ⟨e, he, hew, hep⟩ := (hunion _).mp ((mem_single _ _).mp hsp)
        have hsub' : single (f (dst e)) ⊆ single (f w) := by
          intro a ha'
          exact (mem_single _ _).mpr ((hunion _).mpr ⟨e, he, hew, (mem_single _ _).mp ha'⟩)
        have hnext : clean I (f (dst e)) p.2 ∨
            simple (dst e) ∧ almost I (single (f (dst e))) p.2 := by
          rcases ha with ⟨_, hc⟩ | ⟨hsw, _, hd⟩
          · exact Or.inl (fun hb => hc ((hunion _).mpr ⟨e, he, hew, hb⟩))
          · exact Or.inr ⟨(hsub e he hew).2 hsw, almost_mono I hsub' hd⟩
        by_cases hnext' : approved I (simple (dst e)) (f (dst e)) p.2
        · exact ih (rank (dst e)) (ht ▸ (hsub e he hew).1) _ hnext'
            ((mem_single _ _).mpr hep) rfl
        · refine ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_, hnext', hnext,
            (mem_single _ _).mpr hep⟩⟩
          simpa only [hew] using ha
  have hcover : edgeCover I f simple ⊆ arcs.biUnion Pay := by
    intro p hp
    obtain ⟨hi, w, ha, hsp⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr (descend w p hi ha hsp)
  calc
    _ ≤ (arcs.biUnion Pay).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ arcs, (Pay e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ arcs, 2 := Finset.sum_le_sum (fun e _ => pay_card e)
    _ = _ := by simp [Nat.mul_comm]

end Charging


section Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private lemma plane_four_free
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : fourFree I := by
  intro l l' hll p p' hp hpl' hp' hp'l'
  by_contra hpp
  obtain ⟨_, _, hunique⟩ := hu p p' hpp
  exact hll ((hunique l ⟨hp, hp'⟩).trans (hunique l' ⟨hpl', hp'l'⟩).symm)

private lemma pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  have small (T : Finset (Fin (N+N))) (hT : T ⊆ {Fin.castAdd N p, Fin.natAdd N l}) :
      Thin (setInput T) := by
    intro i j hi hj
    have eqv (k : Fin N) (hk : setInput T (Fin.natAdd N k) = true) : k = l := by
      have hv := hT (of_decide_eq_true hk)
      exact Fin.natAdd_injective _ _ (Finset.mem_singleton.mp ((Finset.mem_insert.mp hv).resolve_left (Ne.symm (cast_ne_nat p k))))
    exact (eqv i hi).trans (eqv j hj).symm
  constructor
  · rw [hC _ (small _ (fun _ h => h)), decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC _ (small _ hT'.subset), decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

private lemma setList_pair {p l : Fin N} (j : ℕ) :
    j ∈ setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔
      j = p.val ∨ j = N + l.val := by
  simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Fin.castAdd N p, Or.inl rfl, rfl⟩
    · exact ⟨Fin.natAdd N l, Or.inr rfl, rfl⟩

private lemma pair_counts {p l : Fin N} (t : List ℕ)
    (ht : ∀ a ∈ t, a = p.val ∨ a = N + l.val) :
    pcount N t = t.count p.val ∧ lcount N t = t.count (N + l.val) := by
  have hp : p.val < N := p.isLt
  have hne : p.val ≠ N + l.val := by omega
  have hl : ¬ N + l.val < N := by omega
  induction t with
  | nil => simp [pcount, lcount]
  | cons j t ih =>
    obtain ⟨h1, h2⟩ := ih (fun a ha => ht a (List.mem_cons_of_mem _ ha))
    change (t.filter _).length = _ at h1 h2
    rcases ht j (by simp) with rfl | rfl
    · have hpn : ¬ N ≤ p.val := by omega
      simp [pcount, lcount, hp, hpn, hne, Ne.symm hne, h1, h2, List.count_cons]
    · simp [pcount, lcount, hl, hne, Ne.symm hne, h1, h2, List.count_cons]

private lemma singleton_sound {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hC : ∀ z : Fin (N+N) → Bool, Thin z → circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {X Y : Set (Fin N)} {a b : ℕ} (hy : ∀ i ∈ Y, ∀ j ∈ Y, i = j)
    (hh : Hom N C C.output a b X Y) : ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  have hv := hom_sound h hh
  change circuitFun (N+N) C (bits X Y) = true at hv
  have ly (i : Fin N) (hi : bits X Y (Fin.natAdd N i) = true) : i ∈ Y :=
    (on_line X Y i).mp ((bits_true _ _ _).mp hi)
  rw [hC _ (fun i j hi hj => hy i (ly i hi) j (ly j hj)), decide_eq_true_eq] at hv
  obtain ⟨p,l,hi,hp,hl⟩ := hv
  exact ⟨p,(on_point X Y p).mp ((bits_true _ _ _).mp hp),l,ly l hl,hi⟩

private lemma plane_read_cover
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) (hr : readsAtMost C (N+N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ Hom N C C.output a b {p} {l} := by
  obtain ⟨t, ht, hs, hu⟩ := read_to_terms h _
    hr
  obtain ⟨hp, hl⟩ := pair_counts (p := p) (l := l) t
    (fun j hj => (setList_pair j).mp (hs j hj))
  have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := by
    refine ⟨t, ht, rfl, rfl, fun j hj => ?_⟩
    rcases (setList_pair j).mp (hs j hj) with rfl | rfl
    · exact (on_point _ _ p).mpr (by simp)
    · exact (on_line _ _ l).mpr (by simp)
  have hp1 : 1 ≤ pcount N t := by
    by_contra! hn
    have he : pcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨a, ha, _⟩ := singleton_sound I h hC (by simp) (hom_pure_y.mp hh)
    exact ha
  have hl1 : 1 ≤ lcount N t := by
    by_contra! hn
    have he : lcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨_, _, b, hb, _⟩ := singleton_sound I h hC (by simp) (hom_pure_x.mp hh)
    exact hb
  exact ⟨_, _, hp1, hp ▸ hu _ ((setList_pair _).mpr (Or.inl rfl)),
    hl1, hl ▸ hu _ ((setList_pair _).mpr (Or.inr rfl)), hh⟩

private noncomputable def allEdges : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

private lemma allEdges_card (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

end Plane


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

private abbrev Occ (C : Circuit) := Fin C.size × Fin 2
private def atWire (N : ℕ) {C : Circuit} (e : Occ C) : ℕ := outWire (N + N) e.1
private def fromWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 e.2
private def otherWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 (1 - e.2)
private def flip {C : Circuit} (e : Occ C) : Occ C := (e.1, 1 - e.2)

private lemma earlier_occ {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : fromWire e < atWire N e := earlier h e.1 e.2

private lemma earlier_other {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : otherWire e < atWire N e := earlier h e.1 (1 - e.2)

private lemma at_bound (N : ℕ) {C : Circuit} (e : Occ C) :
    atWire N e < N + N + C.size := Nat.add_lt_add_left e.1.isLt _

private lemma at_eq {C : Circuit} {N : ℕ} {e : Occ C} {k : Fin C.size}
    (hh : atWire N e = outWire (N + N) k) : e.1 = k := by
  apply Fin.ext
  exact Nat.add_left_cancel hh

private def andAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.and
private def orAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.or

private def orLink (N : ℕ) (C : Circuit) (w t : ℕ) : Prop :=
  ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ atWire N e = t

private def orPath (N : ℕ) (C : Circuit) := ReflTransGen (orLink N C)

private lemma orPath_head {N : ℕ} {C : Circuit} {w t : ℕ} :
    orPath N C w t ↔ w = t ∨
      ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ orPath N C (atWire N e) t := by
  unfold orPath
  rw [ReflTransGen.cases_head_iff]
  constructor
  · rintro (he | ⟨u, ⟨e, ho, hf, rfl⟩, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨e, ho, hf, ht⟩
  · rintro (he | ⟨e, ho, hf, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨_, ⟨e, ho, hf, rfl⟩, ht⟩

private lemma or_reaches {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : Hom N C w a b X Y) : Hom N C t a b X Y := by
  induction hp with
  | refl => exact hw
  | tail _ hy ih =>
    obtain ⟨e, ho, rfl, rfl⟩ := hy
    exact (hom_or h ho).mpr ⟨e.2, ih⟩

private def tag (s : Bool) {N : ℕ} (p : Fin N) : ℕ :=
  if s then N + p.val else p.val

private lemma tag_inj {s : Bool} {N : ℕ} {p q : Fin N} (h : tag s p = tag s q) : p = q := by
  cases s
  · exact Fin.ext h
  · exact Fin.ext (Nat.add_left_cancel h)

private def OHom (N : ℕ) (C : Circuit) (s : Bool) (w a b : ℕ) (X Y : Set (Fin N)) :=
  if s then Hom N C w b a Y X else Hom N C w a b X Y

private def oneSide (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) (X : Set (Fin N)) :=
  OHom N C s w a 0 X ∅

private lemma ohom_mono {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') :
    OHom N C s w a b X Y → OHom N C s w a b X' Y' := by
  cases s
  · exact hom_mono hx hy
  · exact hom_mono hy hx

private lemma ohom_pure {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w a 0 X Y ↔ oneSide N C s w a X := by
  cases s
  · exact hom_pure_x
  · exact hom_pure_y

private lemma ohom_void {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ OHom N C s w a b X Y := by
  cases s <;> exact hom_invalid hw

private lemma ohom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)} (hh : OHom N C s w a b X Y) : 0 < a + b := by
  cases s
  · exact hom_pos h hh
  · rw [Nat.add_comm]
    exact hom_pos h hh

private lemma ohom_input {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : w < N + N) :
    OHom N C s w a b X Y ↔
      (a = 1 ∧ b = 0 ∧ ∃ x ∈ X, tag s x = w) ∨ (a = 0 ∧ b = 1 ∧ ∃ y ∈ Y, tag (!s) y = w) := by
  cases s
  · simp only [OHom, Bool.false_eq_true, ite_false, Bool.not_false, tag, ite_true, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inl ⟨ha, hb, i, hi, he⟩
      · omega
      · omega
      · exact Or.inr ⟨ha, hb, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, ha, hb⟩⟩
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, ha, hb⟩⟩
  · simp only [OHom, ite_true, Bool.not_true, tag, Bool.false_eq_true, ite_false, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inr ⟨hb, ha, i, hi, he⟩
      · omega
      · omega
      · exact Or.inl ⟨hb, ha, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, hb, ha⟩⟩
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, hb, ha⟩⟩

private lemma ohom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, OHom N C s (operand C k i) a b X Y := by
  cases s <;> exact hom_or h ho

private lemma ohom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        OHom N C s (operand C k 0) a₀ b₀ X Y ∧ OHom N C s (operand C k 1) a₁ b₁ X Y := by
  cases s
  · exact hom_and h ho
  · exact (hom_and h ho).trans ⟨
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩,
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩⟩

private lemma ohom_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {e : Occ C} (ho : andAt e) {s : Bool} {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : OHom N C s (fromWire e) a b X Y) (h₂ : OHom N C s (otherWire e) c d X Y) :
    OHom N C s (atWire N e) (a + c) (b + d) X Y := by
  cases s <;> exact hom_and_add h ho e.2 h₁ h₂

private lemma one_mono (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) :
    Monotone (oneSide N C s w a) := fun _ _ h hx => ohom_mono h (fun _ he => he) hx

private lemma one_input {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X : Set (Fin N)}
    (hw : w < N + N) : oneSide N C s w a X ↔ a = 1 ∧ ∃ x ∈ X, tag s x = w := by
  unfold oneSide
  rw [ohom_input hw]
  simp

private lemma one_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a : ℕ} {X : Set (Fin N)} :
    oneSide N C s (outWire (N + N) k) a X ↔ ∃ i : Fin 2, oneSide N C s (operand C k i) a X :=
  ohom_or h ho

private lemma one_and_small {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a : ℕ} {X : Set (Fin N)}
    (ha : a ≤ 2) :
    oneSide N C s (outWire (N + N) k) a X ↔
      a = 2 ∧ oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X := by
  unfold oneSide
  rw [ohom_and h ho]
  constructor
  · rintro ⟨a₀, b₀, a₁, b₁, h₁, h₂, h₀, h₁'⟩
    have := ohom_pos h h₀
    have := ohom_pos h h₁'
    obtain rfl : a₀ = 1 := by omega
    obtain rfl : a₁ = 1 := by omega
    obtain rfl : b₀ = 0 := by omega
    obtain rfl : b₁ = 0 := by omega
    exact ⟨by omega, h₀, h₁'⟩
  · rintro ⟨rfl, hl, hr⟩
    exact ⟨1, 0, 1, 0, rfl, rfl, hl, hr⟩

section OneOccurrence


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private lemma no_approved_small {A B : Type*} [Fintype A] (I : A → B → Prop) [DecidableRel I]
    {f : Set A → Prop} {s : Prop} (hc : (single f).card ≤ 1) (l : B) :
    ¬ approved I s f l := by
  rintro (⟨h, _⟩ | ⟨_, h, _⟩) <;> omega

end OneOccurrence


section Shapes


open PEqualNP.CircuitLowerBounds Relation

private lemma ohom_pure_other {N : ℕ} {C : Circuit} {s : Bool}
    {w b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w 0 b X Y ↔ oneSide N C (!s) w b Y := by
  cases s
  · exact hom_pure_y
  · exact hom_pure_x

private lemma ohom_or_reach {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : OHom N C s w a b X Y) : OHom N C s t a b X Y := by
  cases s <;> exact or_reaches h hp hw

private lemma and_origin {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X Y : Set (Fin N)) (w : ℕ) :
    OHom N C s w a b X Y ↔ ∃ k : Fin C.size, (row C k).op = GateOp.and ∧
      orPath N C (outWire (N + N) k) w ∧ OHom N C s (outWire (N + N) k) a b X Y := by
  refine ⟨?_, fun ⟨_, _, hp, hh⟩ => ohom_or_reach h hp hh⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hh
    rcases wire_cases (N + N) C.size w with hi | ⟨k, rfl⟩ | hm
    · have hf := (ohom_input hi).mp hh
      rcases hf with hf | hf <;> omega
    · rcases op_kind h k with ho | ho
      · exact ⟨k, ho, .refl, hh⟩
      · obtain ⟨i, hsub⟩ := (ohom_or h ho).mp hh
        obtain ⟨k', ho', hp, ht⟩ := ih _ (earlier h k i) hsub
        exact ⟨k', ho', hp.tail ⟨(k, i), ho, rfl, rfl⟩, ht⟩
    · exact (ohom_void hm hh).elim

private lemma mixed11 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 1 1 X Y ↔ ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      oneSide N C false (fromWire e) 1 X ∧ oneSide N C true (otherWire e) 1 Y := by
  refine ⟨?_, ?_⟩
  · intro hw
    obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 1) (by decide : 0 < 1) X Y w).mp hw
    obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
    have hpos₁ := hom_pos h h₁
    have hpos₂ := hom_pos h h₂
    have hs : (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by omega
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨(k, 0), ho, hp, hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩
    · exact ⟨(k, 1), ho, hp, hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩
  · rintro ⟨e, ho, hp, h₁, h₂⟩
    exact or_reaches h hp (hom_and_add h ho e.2 (hom_pure_x.mpr h₁) (hom_pure_y.mpr h₂))

private lemma mixed21 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w : ℕ} {X Y : Set (Fin N)} (hw : OHom N C s w 2 1 X Y) :
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C s (fromWire e) 2 X ∧ oneSide N C (!s) (otherWire e) 1 Y) ∨
       (OHom N C s (fromWire e) 1 1 X Y ∧ oneSide N C s (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h s (by decide : 0 < 2) (by decide : 0 < 1) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (ohom_and h ho).mp hk
  have hpos₁ := ohom_pos h h₁
  have hpos₂ := ohom_pos h h₂
  have hs : (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 0) ∨
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 1) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨(k, 0), ho, hp, Or.inl ⟨ohom_pure.mp h₁, ohom_pure_other.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inl ⟨ohom_pure.mp h₂, ohom_pure_other.mp h₁⟩⟩
  · exact ⟨(k, 0), ho, hp, Or.inr ⟨h₁, ohom_pure.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inr ⟨h₂, ohom_pure.mp h₁⟩⟩

private lemma mixed22 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} (hw : Hom N C w 2 2 X Y) :
    (∃ k : Fin C.size, (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) w ∧
      Hom N C (operand C k 0) 1 1 X Y ∧ Hom N C (operand C k 1) 1 1 X Y) ∨
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C false (fromWire e) 2 X ∧ oneSide N C true (otherWire e) 2 Y) ∨
       (Hom N C (fromWire e) 2 1 X Y ∧ oneSide N C true (otherWire e) 1 Y) ∨
       (Hom N C (fromWire e) 1 2 X Y ∧ oneSide N C false (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 2) (by decide : 0 < 2) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
  have hpos₁ := hom_pos h h₁
  have hpos₂ := hom_pos h h₂
  have hs : (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 0) ∨
      (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
      (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 2) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨k, ho, hp, h₁, h₂⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inl ⟨hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inl ⟨hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inl ⟨h₁, hom_pure_y.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inl ⟨h₂, hom_pure_y.mp h₁⟩)⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inr ⟨h₁, hom_pure_x.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inr ⟨h₂, hom_pure_x.mp h₁⟩)⟩

private def backOne (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X : Set (Fin N)) : Prop :=
  ∃ e : Occ C, andAt e ∧ orPath N C w (fromWire e) ∧ orPath N C (atWire N e) C.output ∧
    oneSide N C s (otherWire e) 1 X

private lemma backOne_mono (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) :
    Monotone (backOne N C s w) :=
  fun _ _ hx ⟨e, ha, hp, ht, hh⟩ => ⟨e, ha, hp, ht, one_mono N C s _ _ hx hh⟩

private lemma backOne_head {N : ℕ} {C : Circuit} {s : Bool} {w : ℕ} {X : Set (Fin N)} :
    backOne N C s w X ↔ ∃ e : Occ C, fromWire e = w ∧
      ((orAt e ∧ backOne N C s (atWire N e) X) ∨
       (andAt e ∧ orPath N C (atWire N e) C.output ∧ oneSide N C s (otherWire e) 1 X)) := by
  constructor
  · rintro ⟨e, ha, hp, ht, hh⟩
    rcases orPath_head.mp hp with he | ⟨e', ho, he, hp'⟩
    · exact ⟨e, he.symm, Or.inr ⟨ha, ht, hh⟩⟩
    · exact ⟨e', he, Or.inl ⟨ho, e, ha, hp', ht, hh⟩⟩
  · rintro ⟨e, rfl, ⟨ho, e', ha, hp, ht, hh⟩ | ⟨ha, ht, hh⟩⟩
    · exact ⟨e', ha, orPath_head.mpr (Or.inr ⟨e, ho, rfl, hp⟩), ht, hh⟩
    · exact ⟨e, ha, .refl, ht, hh⟩

private lemma backOne_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {a b w : ℕ} {X Y : Set (Fin N)}
    (hb : backOne N C s w X) (hh : OHom N C s w a b X Y) :
    OHom N C s C.output (a + 1) b X Y := by
  obtain ⟨e, ho, hp, ht, hx⟩ := hb
  exact ohom_or_reach h ht (ohom_add h ho (ohom_or_reach h hp hh) (ohom_pure.mpr hx))

end Shapes


section PureNetwork


open Finset PEqualNP.CircuitLowerBounds

private lemma one_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    oneSide N C s w 1 X ↔ ∃ p ∈ single (oneSide N C s w 1), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => one_mono N C s w 1 (Set.singleton_subset_iff.mpr hx) hp⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases wire_cases (N + N) C.size w with hh | ⟨k, rfl⟩ | hm
    · obtain ⟨_, p, hp, hv⟩ := (one_input hh).mp hw
      exact ⟨p, (one_input hh).mpr ⟨rfl, p, by simp, hv⟩, hp⟩
    · rcases op_kind h k with ha | ho
      · have hbad := (one_and_small h ha (by decide)).mp hw
        omega
      · obtain ⟨i, hi⟩ := (one_or h ho).mp hw
        obtain ⟨p, hp, hx⟩ := ih _ (earlier h k i) hi
        exact ⟨p, (one_or h ho).mpr ⟨i, hp⟩, hx⟩
    · exact (ohom_void hm hw).elim

private lemma back_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    backOne N C s w X ↔ ∃ p ∈ single (backOne N C s w), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => backOne_mono N C s w (Set.singleton_subset_iff.mpr hx) hp⟩
  rintro ⟨e, ha, hp, ht, h1⟩
  obtain ⟨p, hm, hx⟩ := (one_linear h s (otherWire e) X).mp h1
  exact ⟨p, ⟨e, ha, hp, ht, (mem_single _ _).mp hm⟩, hx⟩

private abbrev PureNode (C : Circuit) := ((Fin 2 × ℕ) ⊕ ℕ) ⊕ Occ C
private abbrev PureArc (C : Circuit) := (Fin 2 × Occ C) ⊕ Occ C
private def pfwd {C : Circuit} (d : Fin 2) (w : ℕ) : PureNode C := .inl (.inl (d, w))
private def pbck {C : Circuit} (w : ℕ) : PureNode C := .inl (.inr w)
private def pjoin {C : Circuit} (e : Occ C) : PureNode C := .inr e

private def pureNode (N : ℕ) {C : Circuit} (s : Bool) : PureNode C → Set (Fin N) → Prop
  | .inl (.inl (d, w)) => oneSide N C s w (1 + d.val)
  | .inl (.inr w) => backOne N C s w
  | .inr e => fun X => oneSide N C s (fromWire e) 1 X ∧ backOne N C s (atWire N e) X

private def pureSimple {C : Circuit} : PureNode C → Prop
  | .inl (.inl (d, _)) => d = 0
  | .inl (.inr _) => True
  | .inr _ => False

private lemma pureNode_mono (N : ℕ) {C : Circuit} (s : Bool) (w : PureNode C) :
    Monotone (pureNode N s w) := by
  rcases w with (⟨d, w⟩ | w) | e
  · exact one_mono N C s w _
  · exact backOne_mono N C s w
  · exact fun X Y h hx => ⟨one_mono N C s _ _ h hx.1, backOne_mono N C s _ h hx.2⟩

private lemma pureNode_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : PureNode C) (hs : pureSimple w) (X : Set (Fin N)) :
    pureNode N s w X ↔ ∃ p ∈ single (pureNode N s w), p ∈ X := by
  rcases w with (⟨d, w⟩ | w) | e
  · obtain rfl : d = 0 := hs
    exact one_linear h s w X
  · exact back_linear h s w X
  · exact hs.elim

private def pureRank (N : ℕ) {C : Circuit} (w : PureNode C) : ℕ :=
  let m := N + N + C.size + 1
  match w with
  | .inl (.inl (_, w)) => w
  | .inl (.inr w) => m + (m - w)
  | .inr _ => 2 * m + 1

private def endAnd (N : ℕ) {C : Circuit} (e : Occ C) : Prop :=
  andAt e ∧ orPath N C (atWire N e) C.output

private noncomputable def pureArcs (N : ℕ) (C : Circuit) : Finset (PureArc C) := by
  classical
  exact univ.filter fun a => a.elim (fun e => orAt e.2) (fun e => orAt e ∨ endAnd N e)

private def pureSrc (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (atWire N e)
  | .inr e => pbck (fromWire e)

private noncomputable def pureDst (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (fromWire e)
  | .inr e => by
    classical
    exact if orAt e then pbck (atWire N e) else pfwd 0 (otherWire e)

private lemma pure_rule {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w : PureNode C) :
    (∀ c, ¬ approved J (pureSimple w) (pureNode N s w) c) ∨
    (∃ u v : PureNode C, pureRank N u < pureRank N w ∧ pureRank N v < pureRank N w ∧
      ¬ pureSimple w ∧ ∀ X, pureNode N s w X ↔ pureNode N s u X ∧ pureNode N s v X) ∨
    ((∀ e ∈ pureArcs N C, pureSrc N e = w → pureRank N (pureDst N e) < pureRank N w ∧
      (pureSimple w → pureSimple (pureDst N e))) ∧
      ∀ X, pureNode N s w X ↔
        ∃ e ∈ pureArcs N C, pureSrc N e = w ∧ pureNode N s (pureDst N e) X) := by
  classical
  rcases w with (⟨d, w⟩ | w) | e
  · rcases wire_cases (N + N) C.size w with hin | ⟨k, rfl⟩ | hmiss
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp hq
      obtain ⟨_, p', hp', hpt⟩ := (one_input hin).mp ((mem_single _ _).mp hp)
      obtain ⟨_, q', hq', hqt⟩ := (one_input hin).mp ((mem_single _ _).mp hq)
      obtain rfl : p' = p := hp'
      obtain rfl : q' = q := hq'
      exact tag_inj (hpt.trans hqt.symm)
    · rcases op_kind h k with ho | ho
      · fin_cases d
        · left
          apply no_approved_small
          apply Finset.card_le_one_iff.mpr
          intro p q hp _
          have hh := (one_and_small h ho (by decide)).mp ((mem_single _ _).mp hp)
          exact (by decide : (1 : ℕ) ≠ 2) hh.1 |>.elim
        · right; left
          exact ⟨pfwd 0 (operand C k 0), pfwd 0 (operand C k 1), earlier h k 0, earlier h k 1,
            by change (1 : Fin 2) ≠ 0; decide, fun X => by
              change oneSide N C s (outWire (N + N) k) 2 X ↔
                oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X
              simpa using (one_and_small h ho (by decide : (2 : ℕ) ≤ 2) (s := s) (X := X))⟩
      · right; right
        constructor
        · rintro (⟨i, e⟩ | e) _ he
          · change Sum.inl (Sum.inl (i, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at he
            obtain ⟨rfl, hw⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj he))
            exact ⟨by simpa [pureDst, pureRank, pfwd, hw] using earlier_occ h e, id⟩
          · simp [pureSrc, pbck] at he
        · intro X
          change oneSide N C s (outWire (N + N) k) (1 + d.val) X ↔ _
          rw [one_or h ho]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨.inl (d, (k, i)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, rfl, hi⟩
          · rintro ⟨(⟨j, e⟩ | e), _, hi, ht⟩
            · change Sum.inl (Sum.inl (j, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at hi
              obtain ⟨rfl, hh⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj hi))
              have heq := at_eq hh
              exact ⟨e.2, by simpa [pureNode, pureDst, pfwd, fromWire, heq] using ht⟩
            · simp [pureSrc, pbck] at hi
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp _
      have hh : oneSide N C s w (1 + d.val) {p} := (mem_single _ _).mp hp
      exact (ohom_void hmiss hh).elim
  · right; right
    constructor
    · rintro (⟨d, e⟩ | e) _ he
      · simp [pureSrc, pfwd] at he
      · have heq : fromWire e = w := by simpa [pureSrc, pbck] using he
        have hh := earlier_occ h e
        have hb := at_bound N e
        have hb' := earlier_other h e
        by_cases ho : orAt e
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pbck, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck]
          omega
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pfwd, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck, pfwd]
          omega
    · intro X
      change backOne N C s w X ↔ _
      rw [backOne_head]
      constructor
      · rintro ⟨e, he, ⟨ho, ht⟩ | ⟨ha, hp, ht⟩⟩
        · exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ho⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, ho, pbck] using ht⟩
        · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (ha.symm.trans ho)
          exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ha, hp⟩⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, hn, pfwd] using ht⟩
      · rintro ⟨(e | e), he, hp, ht⟩
        · obtain ⟨d, e⟩ := e
          simp [pureSrc, pfwd] at hp
        · have heq : fromWire e = w := by simpa [pureSrc, pbck] using hp
          by_cases ho : orAt e
          · exact ⟨e, heq, Or.inl ⟨ho, by simpa [pureNode, pureDst, ho, pbck] using ht⟩⟩
          · have hAnd : endAnd N e := ((Finset.mem_filter.mp he).2 : orAt e ∨ endAnd N e).resolve_left ho
            exact ⟨e, heq, Or.inr ⟨hAnd.1, hAnd.2, by simpa [pureNode, pureDst, ho, pfwd] using ht⟩⟩
  · right; left
    refine ⟨pfwd 0 (fromWire e), pbck (atWire N e), ?_, ?_, not_false, fun _ => Iff.rfl⟩
    · have := earlier_occ h e
      have := at_bound N e
      simp [pureRank, pfwd]
      omega
    · simp [pureRank, pbck]
      omega

end PureNetwork


section Rectangles


variable {A B R : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]
variable (f : R → Set A → Prop) (g : R → Set B → Prop)

private def mixHit (S : Set R) (X : Set A) (Y : Set B) : Prop :=
  ∃ r ∈ S, f r X ∧ g r Y

private def safe (U : Set A → Set B → Prop) : Prop :=
  ∀ X Y, U X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l

private def little (r : R) : Prop :=
  ((single (f r)).card ≤ 1 ∧ (single (g r)).card ≤ 3) ∨
    ((single (f r)).card ≤ 3 ∧ (single (g r)).card ≤ 1)

private def badL (S : Set R) (l : B) : Prop :=
  ∃ r ∈ S, single (g r) = {l} ∧ ¬ almost I (single (f r)) l

private def badP (S : Set R) (p : A) : Prop :=
  ∃ r ∈ S, single (f r) = {p} ∧ ¬ almost (fun l p => I p l) (single (g r)) p

private lemma swapped_free (hf : fourFree I) : fourFree (fun l p => I p l) := by
  intro p q hp a b hap haq hbp hbq
  by_contra hne
  exact hp (hf hne hap hbp haq hbq)

private lemma opposite_bad_adj (hf : fourFree I)
    (Sf : ∀ r X, f r X ↔ ∃ a ∈ single (f r), a ∈ X)
    (Sg : ∀ r Y, g r Y ↔ ∃ b ∈ single (g r), b ∈ Y)
    {U V : Set R} (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hl : badL I f g U l) (hp : badP I f g V p) : I p l := by
  classical
  obtain ⟨r, hr, hrl, hA⟩ := hl
  obtain ⟨s, hs, hsp, hB⟩ := hp
  let Ar := (single (f r)).filter (fun p' => ¬ I p' l)
  let Bs := (single (g s)).filter (fun l' => ¬ I p l')
  have hAr : 1 < Ar.card := Nat.lt_of_not_ge hA
  have hBs : 1 < Bs.card := Nat.lt_of_not_ge hB
  by_contra hpl
  have hfind : ∃ p' ∈ Ar, ∃ l' ∈ Bs, ¬ I p' l' := by
    by_contra! hall
    obtain ⟨p₁, p₂, ha₁, ha₂, hpp⟩ := Finset.one_lt_card_iff.mp hAr
    obtain ⟨l₁, l₂, hb₁, hb₂, hll⟩ := Finset.one_lt_card_iff.mp hBs
    exact hpp (hf hll (hall p₁ ha₁ l₁ hb₁) (hall p₁ ha₁ l₂ hb₂)
      (hall p₂ ha₂ l₁ hb₁) (hall p₂ ha₂ l₂ hb₂))
  obtain ⟨p', hpr, l', hls, hcross⟩ := hfind
  have hp' := Finset.mem_filter.mp hpr
  have hl' := Finset.mem_filter.mp hls
  have hr' : mixHit f g U ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨r, hr, (Sf _ _).mpr ⟨p', hp'.1, by simp⟩, (Sg _ _).mpr ⟨l, by simp [hrl], by simp⟩⟩
  have hs' : mixHit f g V ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨s, hs, (Sf _ _).mpr ⟨p, by simp [hsp], by simp⟩, (Sg _ _).mpr ⟨l', hl'.1, by simp⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hUV _ _ ⟨hr', hs'⟩
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hpl hab
    · obtain rfl : b = l' := hb
      exact hl'.2 hab
  · obtain rfl : a = p' := ha
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hp'.2 hab
    · obtain rfl : b = l' := hb
      exact hcross hab

private def pureGood (p : A) (l : B) : Prop :=
  (∃ r, p ∈ single (f r) ∧ approved I True (f r) l) ∨
    ∃ r, l ∈ single (g r) ∧ approved (fun l p => I p l) True (g r) p

private def smallGood (p : A) (l : B) : Prop :=
  ∃ r, little f g r ∧ p ∈ single (f r) ∧ l ∈ single (g r)

private lemma classify_same (p : A) (l : B) (r : R)
    (hp : p ∈ single (f r)) (hl : l ∈ single (g r))
    (hx : clean I (f r) l) (hy : clean (fun l p => I p l) (g r) p) :
    pureGood I f g p l ∨ smallGood f g p l := by
  by_cases h2 : 2 ≤ (single (f r)).card
  · exact Or.inl (Or.inl ⟨r, hp, Or.inl ⟨h2, hx⟩⟩)
  by_cases hg2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inr ⟨r, hl, Or.inl ⟨hg2, hy⟩⟩)
  exact Or.inr ⟨r, Or.inl ⟨by omega, by omega⟩, hp, hl⟩

private lemma singleton_of_small {T : Type*} [DecidableEq T] {s : Finset T}
    {a : T} (h : a ∈ s) (hc : s.card ≤ 1) : s = {a} := by
  ext b
  simp only [Finset.mem_singleton]
  exact ⟨fun hb => Finset.card_le_one_iff.mp hc hb h, fun e => e ▸ h⟩

private lemma classify_opposite {U V : Set R} {p : A} {l : B} {r s : R}
    (hr : r ∈ U) (hs : s ∈ V) (hpr : p ∈ single (f r)) (hlr : l ∈ single (g r))
    (hps : p ∈ single (f s)) (hls : l ∈ single (g s))
    (hY : clean (fun l p => I p l) (g r) p) (hX : clean I (f s) l) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨ (badL I f g U l ∧ badP I f g V p) := by
  classical
  by_cases hy2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inl (Or.inr ⟨r, hlr, Or.inl ⟨hy2, hY⟩⟩))
  by_cases hx2 : 2 ≤ (single (f s)).card
  · exact Or.inl (Or.inl (Or.inl ⟨s, hps, Or.inl ⟨hx2, hX⟩⟩))
  by_cases hRa : almost I (single (f r)) l
  · by_cases hR4 : 4 ≤ (single (f r)).card
    · exact Or.inl (Or.inl (Or.inl ⟨r, hpr, Or.inr ⟨trivial, hR4, hRa⟩⟩))
    · exact Or.inl (Or.inr ⟨r, Or.inr ⟨by omega, by omega⟩, hpr, hlr⟩)
  by_cases hSa : almost (fun l p => I p l) (single (g s)) p
  · by_cases hS4 : 4 ≤ (single (g s)).card
    · exact Or.inl (Or.inl (Or.inr ⟨s, hls, Or.inr ⟨trivial, hS4, hSa⟩⟩))
    · exact Or.inl (Or.inr ⟨s, Or.inl ⟨by omega, by omega⟩, hps, hls⟩)
  exact Or.inr ⟨⟨r, hr, singleton_of_small hlr (by omega), hRa⟩,
    ⟨s, hs, singleton_of_small hps (by omega), hSa⟩⟩

private lemma classify_product {U V : Set R}
    (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hU : mixHit f g U {p} {l}) (hV : mixHit f g V {p} {l}) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨
      (badL I f g U l ∧ badP I f g V p) ∨ (badL I f g V l ∧ badP I f g U p) := by
  classical
  obtain ⟨r, hr, hpr, hlr⟩ := hU
  obtain ⟨s, hs, hps, hls⟩ := hV
  let X := {a | ¬ I a l}
  let Y := {b | ¬ I p b}
  have hX : ¬ (mixHit f g U X {l} ∧ mixHit f g V X {l}) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : b = l := hb
    exact ha hi
  have hY : ¬ (mixHit f g U {p} Y ∧ mixHit f g V {p} Y) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : a = p := ha
    exact hb hi
  have hx : clean I (f r) l ∨ clean I (f s) l := by
    by_cases ha : f r X
    · exact Or.inr (fun hb => hX ⟨⟨r, hr, ha, hlr⟩, ⟨s, hs, hb, hls⟩⟩)
    · exact Or.inl ha
  have hy : clean (fun l p => I p l) (g r) p ∨ clean (fun l p => I p l) (g s) p := by
    by_cases ha : g r Y
    · exact Or.inr (fun hb => hY ⟨⟨r, hr, hpr, ha⟩, ⟨s, hs, hps, hb⟩⟩)
    · exact Or.inl ha
  have hpr' := (mem_single _ _).mpr hpr
  have hlr' := (mem_single _ _).mpr hlr
  have hps' := (mem_single _ _).mpr hps
  have hls' := (mem_single _ _).mpr hls
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (classify_same I f g p l r hpr' hlr' hx hy)
  · exact (classify_opposite I f g hs hr hps' hls' hpr' hlr' hy hx).imp id Or.inr
  · exact (classify_opposite I f g hr hs hpr' hlr' hps' hls' hy hx).imp id Or.inl
  · exact Or.inl (classify_same I f g p l s hps' hls' hx hy)

private lemma classify_direct
    (U : Set A → Prop) (V : Set B → Prop)
    (hUV : safe I (fun X Y => U X ∧ V Y))
    (p : A) (l : B) (hp : U {p}) (hl : V {l}) :
    (approved I False U l ∨ approved (fun l p => I p l) False V p) ∨
      ((single U).card ≤ 1 ∧ (single V).card ≤ 1) := by
  have hx : clean I U l := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hm, hl⟩
    obtain rfl : b = l := hb
    exact ha hi
  have hy : clean (fun l p => I p l) V p := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hp, hm⟩
    obtain rfl : a = p := ha
    exact hb hi
  by_cases ha : 2 ≤ (single U).card
  · exact Or.inl (Or.inl (Or.inl ⟨ha, hx⟩))
  by_cases hb : 2 ≤ (single V).card
  · exact Or.inl (Or.inr (Or.inl ⟨hb, hy⟩))
  exact Or.inr ⟨by omega, by omega⟩

end Rectangles


section MixedNetwork

open Finset Relation PEqualNP.CircuitLowerBounds

private abbrev Rect (C : Circuit) := Occ C ⊕ (Occ C × Fin 2)
private abbrev MixNode (C : Circuit) := (ℕ ⊕ ℕ) ⊕ Rect C

private def mfwd {C : Circuit} (w : ℕ) : MixNode C := .inl (.inl w)
private def mbck {C : Circuit} (w : ℕ) : MixNode C := .inl (.inr w)
private def mleaf {C : Circuit} (r : Rect C) : MixNode C := .inr r

private def rectPoint (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (fromWire e)
  | .inr (e, i) => if i = 0 then pfwd 0 (otherWire e) else pbck (atWire N e)

private def rectLine (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (otherWire e)
  | .inr (e, i) => if i = 0 then pbck (atWire N e) else pfwd 0 (otherWire e)

private def rpoint (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N false (rectPoint N r)

private def rline (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N true (rectLine N r)

private lemma rectPoint_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectPoint N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectPoint, pfwd, pbck, pureSimple]

private lemma rectLine_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectLine N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectLine, pfwd, pbck, pureSimple]

private def mixFamily (N : ℕ) {C : Circuit} : MixNode C → Set (Rect C)
  | .inl (.inl w) => {r | ∃ e : Occ C, r = .inl e ∧ andAt e ∧ orPath N C (atWire N e) w}
  | .inl (.inr w) => {r | ∃ e : Occ C, ∃ i : Fin 2, r = .inr (e, i) ∧ andAt e ∧
      orPath N C w (fromWire e)}
  | .inr r => {r}

private lemma mixFwd_spec {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mfwd (C := C) w)) X Y ↔ Hom N C w 1 1 X Y := by
  rw [mixed11 h]
  constructor
  · rintro ⟨_, ⟨e, rfl, he, hp⟩, hX, hY⟩
    exact ⟨e, he, hp, hX, hY⟩
  · rintro ⟨e, he, hp, hX, hY⟩
    exact ⟨.inl e, ⟨e, rfl, he, hp⟩, hX, hY⟩

private lemma mixBack_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)}
    (hb : mixHit (rpoint N) (rline N) (mixFamily N (mbck (C := C) w)) X Y)
    (hh : Hom N C w a b X Y) : Hom N C C.output (a + 1) (b + 1) X Y := by
  obtain ⟨_, ⟨e, i, rfl, he, hp⟩, hx, hy⟩ := hb
  fin_cases i
  · have hx' : oneSide N C false (otherWire e) 1 X := by
      simpa [rpoint, rectPoint, pureNode, pfwd] using hx
    have hy' : backOne N C true (atWire N e) Y := by
      simpa [rline, rectLine, pureNode, pbck] using hy
    have hj : Hom N C (atWire N e) (a + 1) b X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_x.mpr hx')
    exact backOne_apply (s := true) h hy' hj
  · have hx' : backOne N C false (atWire N e) X := by
      simpa [rpoint, rectPoint, pureNode, pbck] using hx
    have hy' : oneSide N C true (otherWire e) 1 Y := by
      simpa [rline, rectLine, pureNode, pfwd] using hy
    have hj : Hom N C (atWire N e) a (b + 1) X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_y.mpr hy')
    exact backOne_apply (s := false) h hx' hj

private lemma mixLeaf_spec (N : ℕ) {C : Circuit} (r : Rect C) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mleaf r)) X Y ↔ rpoint N r X ∧ rline N r Y := by
  simp [mixHit, mixFamily, mleaf]

private def mixRank (N : ℕ) {C : Circuit} : MixNode C → ℕ
  | .inl (.inl w) => w + 1
  | .inl (.inr w) => (N + N + C.size + 1 - w) + 1
  | .inr _ => 0

private def mixSrc (N : ℕ) {C : Circuit} : Rect C → MixNode C
  | .inl e => mfwd (atWire N e)
  | .inr (e, _) => mbck (fromWire e)

private noncomputable def mixDst (N : ℕ) {C : Circuit} (a : Rect C) : MixNode C := by
  classical
  exact match a with
  | .inl e => if orAt e then mfwd (fromWire e) else mleaf a
  | .inr (e, _) => if orAt e then mbck (atWire N e) else mleaf a

private lemma mixArc_rank {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (a : Rect C) : mixRank N (mixDst N a) < mixRank N (mixSrc N a) := by
  classical
  rcases a with e | ⟨e, i⟩
  · have := earlier_occ h e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mfwd, mleaf] <;> omega
  · have := earlier_occ h e
    have := at_bound N e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mbck, mleaf] <;> omega

private lemma mixFwd_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mfwd w) ↔
      ∃ a : Rect C, mixSrc N a = mfwd w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, rfl, he, hp⟩
    rcases hp.cases_tail with heq | ⟨_, hp', ⟨a, ha, hf, hw⟩⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inl e, by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inl a, by simp [mixSrc, hw], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, rfl, he, hf ▸ hp'⟩
  · rintro ⟨(a | a), hs, ht⟩
    · have hw : atWire N a = w := by simpa [mixSrc, mfwd] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, rfl, he, hp⟩ := ht
        exact ⟨e, rfl, he, hp.tail ⟨a, ha, rfl, hw⟩⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inl a := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, heq, hn, hw ▸ ReflTransGen.refl⟩
    · obtain ⟨a, i⟩ := a
      simp [mixSrc, mbck, mfwd] at hs

private lemma mixBack_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mbck w) ↔
      ∃ a : Rect C, mixSrc N a = mbck w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, i, rfl, he, hp⟩
    rcases orPath_head.mp hp with heq | ⟨a, ha, hf, ht⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inr (e, i), by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inr (a, 0), by simp [mixSrc, hf], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, i, rfl, he, ht⟩
  · rintro ⟨(a | ⟨a, i⟩), hs, ht⟩
    · simp [mixSrc, mfwd, mbck] at hs
    · have hw : fromWire a = w := by simpa [mixSrc, mbck] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, j, rfl, he, hp⟩ := ht
        exact ⟨e, j, rfl, he, orPath_head.mpr (Or.inr ⟨a, ha, hw, hp⟩)⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inr (a, i) := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, i, heq, hn, hw ▸ ReflTransGen.refl⟩

variable {N : ℕ} {C : Circuit}

private def centerLabel (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (r : Rect C) (v : Fin N) : Prop := by
  classical
  exact if s then single (rline N r) = {v} ∧ ¬ almost I (single (rpoint N r)) v
    else single (rpoint N r) = {v} ∧ ¬ almost (fun l p => I p l) (single (rline N r)) v

private def centerNode (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) : Prop :=
  ∃ r ∈ mixFamily N w, ∃ v ∈ X, centerLabel I s r v

private lemma center_mono (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) : Monotone (centerNode I s w) :=
  fun _ _ h ⟨r, hr, v, hv, hl⟩ => ⟨r, hr, v, h hv, hl⟩

private lemma center_member (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (v : Fin N) :
    v ∈ single (centerNode I s w) ↔ ∃ r ∈ mixFamily N w, centerLabel I s r v := by
  simp [centerNode, mem_single]

private lemma center_linear (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) :
    centerNode I s w X ↔ ∃ v ∈ single (centerNode I s w), v ∈ X := by
  simp only [center_member, centerNode]
  exact ⟨fun ⟨r, hr, v, hv, hl⟩ => ⟨v, ⟨r, hr, hl⟩, hv⟩,
    fun ⟨v, ⟨r, hr, hl⟩, hv⟩ => ⟨r, hr, v, hv, hl⟩⟩

private lemma center_rule (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (w : MixNode C) :
    (∀ c, ¬ approved J True (centerNode I s w) c) ∨
    (∃ u v : MixNode C, mixRank N u < mixRank N w ∧ mixRank N v < mixRank N w ∧
      ¬ True ∧ ∀ X, centerNode I s w X ↔ centerNode I s u X ∧ centerNode I s v X) ∨
    ((∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
      mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X) := by
  classical
  have go (w : MixNode C) (hw : ∀ r, r ∈ mixFamily N w ↔
      ∃ a : Rect C, mixSrc N a = w ∧ r ∈ mixFamily N (mixDst N a)) :
      (∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
        mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X := by
    refine ⟨fun a _ he => ⟨he ▸ mixArc_rank h a, id⟩, ?_⟩
    intro X
    constructor
    · rintro ⟨r, hr, v, hv, ht⟩
      obtain ⟨a, he, ha⟩ := (hw r).mp hr
      exact ⟨a, Finset.mem_univ _, he, r, ha, v, hv, ht⟩
    · rintro ⟨a, _, he, r, ha, v, hv, ht⟩
      exact ⟨r, (hw r).mpr ⟨a, he, ha⟩, v, hv, ht⟩
  rcases w with (w | w) | r
  · exact Or.inr (Or.inr (go (mfwd w) (mixFwd_next h w)))
  · exact Or.inr (Or.inr (go (mbck w) (mixBack_next h w)))
  · left
    apply no_approved_small
    apply Finset.card_le_one_iff.mpr
    intro p q hp hq
    obtain ⟨r', hr, hpl⟩ := (center_member I s _ _).mp hp
    obtain ⟨r'', ht, hql⟩ := (center_member I s _ _).mp hq
    have he' : r' = r := hr
    have he'' : r'' = r := ht
    subst r'
    subst r''
    cases s
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)

end MixedNetwork


section Products


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}

private abbrev MixProduct (C : Circuit) := Fin C.size ⊕ Occ C
private abbrev PureProduct (C : Circuit) := Fin 3 × Occ C

private def validMixed (N : ℕ) {C : Circuit} : MixProduct C → Prop
  | .inl k => (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) C.output
  | .inr e => andAt e

private def leftMix {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 0)
  | .inr e => mleaf (.inl e)

private def rightMix (N : ℕ) {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 1)
  | .inr e => mbck (atWire N e)

private def validPure (N : ℕ) {C : Circuit} (d : PureProduct C) : Prop :=
  andAt d.2 ∧ (d.1 = 0 → orPath N C (atWire N d.2) C.output)

private def purePoint {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 2 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private def pureLine {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 0 then pfwd 1 (otherWire d.2) else
    if d.1 = 1 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private lemma pjoin_spec (N : ℕ) {C : Circuit} (s : Bool) (e : Occ C) (X : Set (Fin N)) :
    pureNode N s (pjoin (flip e)) X ↔
      oneSide N C s (otherWire e) 1 X ∧ backOne N C s (atWire N e) X := Iff.rfl

private lemma mixed_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {t : MixProduct C}
    (ht : validMixed N t) {X Y : Set (Fin N)}
    (hl : mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y)
    (hr : mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y) :
    Hom N C C.output 2 2 X Y := by
  rcases t with k | e
  · have ha := (mixFwd_spec h _ _ _).mp hl
    have hb := (mixFwd_spec h _ _ _).mp hr
    exact or_reaches h ht.2 (hom_and_add h ht.1 0 ha hb)
  · have hs := (mixLeaf_spec N (.inl e) X Y).mp hl
    have hm := hom_and_add h ht e.2 (hom_pure_x.mpr hs.1) (hom_pure_y.mpr hs.2)
    exact mixBack_apply h hr hm

private lemma pure_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {d : PureProduct C}
    (hd : validPure N d) {X Y : Set (Fin N)}
    (hp : pureNode N false (purePoint d) X) (hl : pureNode N true (pureLine d) Y) :
    Hom N C C.output 2 2 X Y := by
  obtain ⟨t, e⟩ := d
  fin_cases t
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' : oneSide N C true (otherWire e) 2 Y := hl
    exact or_reaches h (hd.2 rfl) (hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'))
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' := (pjoin_spec N true e Y).mp hl
    have hh : Hom N C (atWire N e) 2 1 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'.1)
    exact backOne_apply (s := true) h hl'.2 hh
  · have hp' := (pjoin_spec N false e X).mp hp
    have hl' : oneSide N C true (fromWire e) 2 Y := hl
    have hh : Hom N C (atWire N e) 1 2 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_y.mpr hl') (hom_pure_x.mpr hp'.1)
    exact backOne_apply (s := false) h hp'.2 hh

private def mixedTerm (N : ℕ) {C : Circuit} (t : MixProduct C) (X Y : Set (Fin N)) : Prop :=
  mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y ∧
    mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y

private def pureTerm (N : ℕ) {C : Circuit} (d : PureProduct C) (X Y : Set (Fin N)) : Prop :=
  pureNode N false (purePoint d) X ∧ pureNode N true (pureLine d) Y

private lemma product_normal (h : PEqualNP.TopForm.IsAO2 (N + N) C) {X Y : Set (Fin N)}
    (hw : Hom N C C.output 2 2 X Y) :
    (∃ t : MixProduct C, validMixed N t ∧ mixedTerm N t X Y) ∨
    (∃ d : PureProduct C, validPure N d ∧ pureTerm N d X Y) := by
  rcases mixed22 h hw with ⟨k, ha, ht, h₁, h₂⟩ | ⟨e, ha, ht, (⟨hp, hl⟩ | ⟨hh, hl⟩ | ⟨hh, hp⟩)⟩
  · exact Or.inl ⟨.inl k, ⟨ha, ht⟩, (mixFwd_spec h _ _ _).mpr h₁, (mixFwd_spec h _ _ _).mpr h₂⟩
  · exact Or.inr ⟨(0, e), ⟨ha, fun _ => ht⟩, hp, hl⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := false) h hh
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      exact Or.inr ⟨(1, e'), ⟨he', fun hf => ((by decide : (1 : Fin 3) ≠ 0) hf).elim⟩,
        hy, (pjoin_spec N true e' Y).mpr ⟨hx, hb⟩⟩
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 0), ⟨e', 0, rfl, he', hpath⟩, hz, hb⟩⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := true) h hh
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      exact Or.inr ⟨(2, e'), ⟨he', fun hf => ((by decide : (2 : Fin 3) ≠ 0) hf).elim⟩,
        (pjoin_spec N false e' X).mpr ⟨hx, hb⟩, hy⟩
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 1), ⟨e', 1, rfl, he', hpath⟩, hb, hz⟩⟩

end Products


section Accounting


open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def exchange {N : ℕ} (S : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  S.map (Equiv.prodComm (Fin N) (Fin N)).toEmbedding

private lemma exchange_card {N : ℕ} (S : Finset (Fin N × Fin N)) :
    (exchange S).card = S.card := Finset.card_map _

private lemma exchange_mem {N : ℕ} {S : Finset (Fin N × Fin N)} {p l : Fin N}
    (h : (l, p) ∈ S) : (p, l) ∈ exchange S :=
  Finset.mem_map.mpr ⟨(l, p), h, rfl⟩

private lemma in_cover {A B W : Type*} [Fintype A] [Fintype B]
    (I : A → B → Prop) [DecidableRel I] {f : W → Set A → Prop} {s : W → Prop}
    {p : A} {l : B} (hi : I p l) (w : W) (ha : approved I (s w) (f w) l)
    (hp : p ∈ single (f w)) : (p, l) ∈ edgeCover I f s := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, w, ha, hp⟩

private noncomputable def singletonPay {N : ℕ} (f g : Set (Fin N) → Prop) :
    Finset (Fin N × Fin N) := by
  classical
  exact if (single f).card ≤ 1 ∧ (single g).card ≤ 1 then (single f) ×ˢ (single g) else ∅

private lemma singletonPay_mem {N : ℕ} {f g : Set (Fin N) → Prop} {p l : Fin N}
    (hp : p ∈ single f) (hl : l ∈ single g) (hs : (single f).card ≤ 1 ∧ (single g).card ≤ 1) :
    (p, l) ∈ singletonPay f g := by
  classical
  simp [singletonPay, hs, hp, hl]

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private noncomputable def rectPay (N : ℕ) {C : Circuit} (r : Rect C) : Finset (Fin N × Fin N) := by
  classical
  exact if little (rpoint N) (rline N) r then
    single (rpoint N r) ×ˢ single (rline N r) else ∅

private def centerPoint (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then leftMix t else rightMix N t

private def centerLine (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then rightMix N t else leftMix t

private noncomputable def mixedPay (t : MixProduct C × Bool) : Finset (Fin N × Fin N) :=
  singletonPay (centerNode I false (centerPoint N t.1 t.2)) (centerNode I true (centerLine N t.1 t.2))

private noncomputable def purePay (d : PureProduct C) : Finset (Fin N × Fin N) :=
  singletonPay (pureNode N false (purePoint d)) (pureNode N true (pureLine d))

private noncomputable def pureCover (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) :=
  edgeCover I (pureNode N (C := C) false) pureSimple ∪
  exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple)

private lemma covered_by_pure {p l : Fin N} (hi : I p l)
    (h : pureGood I (rpoint N (C := C)) (rline N) p l) : (p, l) ∈ pureCover N C I := by
  rcases h with ⟨r, hp, ha⟩ | ⟨r, hl, ha⟩
  · apply Finset.mem_union_left
    apply in_cover I hi (rectPoint N r) _ hp
    change approved I (pureSimple (rectPoint N r)) (rpoint N r) l
    simpa only [rectPoint_simple] using ha
  · apply Finset.mem_union_right
    apply exchange_mem
    apply in_cover (fun l p => I p l) hi (rectLine N r) _ hl
    change approved (fun l p => I p l) (pureSimple (rectLine N r)) (rline N r) p
    simpa only [rectLine_simple] using ha

private lemma pure_charges (d : PureProduct C) (hs : safe I (pureTerm N d))
    (p l : Fin N) (hi : I p l) (hTerm : pureTerm N d {p} {l}) :
    (p, l) ∈ pureCover N C I ∨ (p, l) ∈ purePay d := by
  have hp := (mem_single _ _).mpr hTerm.1
  have hl := (mem_single _ _).mpr hTerm.2
  rcases classify_direct I _ _ hs p l hTerm.1 hTerm.2 with (ha | ha) | ha
  · exact Or.inl (Finset.mem_union_left _ (in_cover I hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hp))
  · exact Or.inl (Finset.mem_union_right _ (exchange_mem
      (in_cover (fun l p => I p l) hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hl)))
  · exact Or.inr (singletonPay_mem hp hl ha)

private noncomputable def twiceEdges (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) := by
  classical
  exact univ.filter fun e => I e.1 e.2 ∧ Hom N C C.output 2 2 {e.1} {e.2}

end Accounting


section GateAccounting

open Finset PEqualNP.CircuitLowerBounds

private noncomputable def andRows (C : Circuit) : Finset (Fin C.size) := by
  classical
  exact univ.filter fun k => (row C k).op = GateOp.and

private noncomputable def orRows (C : Circuit) : Finset (Fin C.size) := by
  classical
  exact univ.filter fun k => (row C k).op = GateOp.or

private lemma orRows_mem {C : Circuit} (k : Fin C.size) :
    k ∈ orRows C ↔ (row C k).op = GateOp.or := by
  classical
  simp [orRows]

private lemma andRows_mem {C : Circuit} (k : Fin C.size) :
    k ∈ andRows C ↔ (row C k).op = GateOp.and := by
  classical
  simp [andRows]

private lemma gate_card_sum {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C) :
    (orRows C).card + (andRows C).card = C.size := by
  classical
  have heq : andRows C = univ.filter fun k => ¬ (row C k).op = GateOp.or := by
    ext k
    simp only [andRows_mem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha ho
      exact GateOp.noConfusion (ha.symm.trans ho)
    · exact (op_kind h k).resolve_right
  rw [heq, orRows, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

private lemma pure_bound_by_ops {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (hf : fourFree J) (s : Bool) :
    (edgeCover J (pureNode N (C := C) s) pureSimple).card ≤
      12 * (orRows C).card + 4 * (andRows C).card := by
  classical
  have hCover := cover_bound J hf (pureNode N (C := C) s) pureSimple (pureRank N)
    (pureArcs N C) (pureSrc N) (pureDst N) (pureNode_mono N s) (pureNode_linear h s) (pure_rule h J s)
  let O : Finset (Occ C) := (orRows C) ×ˢ univ
  let A : Finset (Occ C) := (andRows C) ×ˢ univ
  let S : Finset (PureArc C) := (univ ×ˢ O).disjSum (O ∪ A)
  have hsub : pureArcs N C ⊆ S := by
    intro e he
    have hp := (mem_filter.mp he).2
    rcases e with ⟨d, e⟩ | e
    · have he : e ∈ O := by simpa [O, orRows_mem, orAt] using hp
      exact mem_disjSum.mpr (Or.inl ⟨(d,e), mem_product.mpr ⟨mem_univ _, he⟩, rfl⟩)
    · refine mem_disjSum.mpr (Or.inr ⟨e, ?_, rfl⟩)
      rcases hp with hp | hp
      · exact mem_union_left _ (by simpa [O, orRows_mem, orAt] using hp)
      · exact mem_union_right _ (by simpa [A, andRows_mem, andAt] using hp.1)
  have hS : S.card ≤ 6 * (orRows C).card + 2 * (andRows C).card := by
    have hu := card_union_le O A
    have ho : O.card = 2 * (orRows C).card := by simp [O, Nat.mul_comm]
    have ha : A.card = 2 * (andRows C).card := by simp [A, Nat.mul_comm]
    simp only [S, card_disjSum, card_product, card_univ, Fintype.card_fin]
    omega
  have hA := (card_le_card hsub).trans hS
  omega

end GateAccounting


section CleanCenterAccounting

open Finset PEqualNP.CircuitLowerBounds

private noncomputable def cleanEdgeCover {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) : Finset (A × B) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧
    ∃ w, 2 ≤ (single (f w)).card ∧ clean J (f w) e.2 ∧ e.1 ∈ single (f w)

private noncomputable def cleanPay {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (u v : W) : Finset (A × B) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧ 2 ≤ (single (f u)).card ∧
    clean J (f u) e.2 ∧ (single (f v)).card ≤ 1 ∧ e.1 ∈ single (f v)

private lemma cleanEdgeCover_mem {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (e : A × B) :
    e ∈ cleanEdgeCover J f ↔ J e.1 e.2 ∧
      ∃ w, 2 ≤ (single (f w)).card ∧ clean J (f w) e.2 ∧ e.1 ∈ single (f w) := by
  classical
  simp [cleanEdgeCover]

private lemma cleanPay_mem {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (u v : W) (e : A × B) :
    e ∈ cleanPay J f u v ↔ J e.1 e.2 ∧ 2 ≤ (single (f u)).card ∧
      clean J (f u) e.2 ∧ (single (f v)).card ≤ 1 ∧ e.1 ∈ single (f v) := by
  classical
  simp [cleanPay]

private lemma cleanPay_card {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (hf : fourFree J)
    (f : W → Set A → Prop) (u v : W) (hm : Monotone (f u)) :
    (cleanPay J f u v).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨_, hsize, hac, hsmall, ham⟩ := (cleanPay_mem J f u v a).mp ha
  obtain ⟨_, _, hbc, _, hbm⟩ := (cleanPay_mem J f u v b).mp hb
  exact Prod.ext (Finset.card_le_one_iff.mp hsmall ham hbm)
    (exact_unique J hf hm hsize hac hbc)

private lemma center_descend {N : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (a b : Fin N) (hi : J a b)
    (w : MixNode C) (hbig : 2 ≤ (single (centerNode I s w)).card)
    (hclean : clean J (centerNode I s w) b) (hm : a ∈ single (centerNode I s w)) :
    ∃ r : Rect C, (a,b) ∈ cleanPay J (centerNode I s) (mixSrc N r) (mixDst N r) := by
  classical
  induction heq : mixRank N w using Nat.strong_induction_on generalizing w with
  | ind k ih =>
    rcases center_rule h I s J w with hno | ⟨_, _, _, _, bad, _⟩ | ⟨hdown, hor⟩
    · exact (hno b (Or.inl ⟨hbig,hclean⟩)).elim
    · exact (bad trivial).elim
    · obtain ⟨r, hr, hs, ht⟩ := (hor _).mp ((mem_single _ _).mp hm)
      have ht' := (mem_single _ _).mpr ht
      have hcd : clean J (centerNode I s (mixDst N r)) b := by
        intro bad
        exact hclean ((hor _).mpr ⟨r,hr,hs,bad⟩)
      by_cases hd : 2 ≤ (single (centerNode I s (mixDst N r))).card
      · exact ih _ (heq ▸ (hdown r hr hs).1) _ hd hcd ht' rfl
      · refine ⟨r, (cleanPay_mem _ _ _ _ _).mpr ⟨hi, ?_, ?_, by omega, ht'⟩⟩
        · simpa only [hs] using hbig
        · simpa only [hs] using hclean

private noncomputable def centerPayBoth {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) : Finset (Fin N × Fin N) :=
  cleanPay I (centerNode I false) (mixSrc N r) (mixDst N r) ∪
    exchange (cleanPay (fun l p => I p l) (centerNode I true) (mixSrc N r) (mixDst N r))

private lemma centerPayBoth_card {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (r : Rect C) :
    (centerPayBoth I r).card ≤ 2 := by
  have hp := cleanPay_card I hf (centerNode I false) (mixSrc N r) (mixDst N r)
    (center_mono I false _)
  have hl := cleanPay_card (fun l p => I p l) (swapped_free I hf)
    (centerNode I true) (mixSrc N r) (mixDst N r) (center_mono I true _)
  unfold centerPayBoth
  refine (Finset.card_union_le _ _).trans ?_
  rw [exchange_card]
  omega

private lemma center_labels_disjoint {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) (p l : Fin N)
    (hp : centerLabel I false r p) (hl : centerLabel I true r l) : False := by
  change single (rpoint N r) = {p} ∧ _ at hp
  change _ ∧ ¬ almost I (single (rpoint N r)) l at hl
  apply hl.2
  unfold almost
  exact (Finset.card_filter_le _ _).trans (by rw [hp.1, Finset.card_singleton])

private lemma centerPayBoth_leaf {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (r : Rect C)
    (hleaf : mixDst N r = mleaf r) : (centerPayBoth I r).card ≤ 1 := by
  classical
  let P := cleanPay I (centerNode I false) (mixSrc N r) (mixDst N r)
  let L := cleanPay (fun l p => I p l) (centerNode I true) (mixSrc N r) (mixDst N r)
  have hp := cleanPay_card I hf (centerNode I false) (mixSrc N r) (mixDst N r)
    (center_mono I false _)
  have hl := cleanPay_card (fun l p => I p l) (swapped_free I hf)
    (centerNode I true) (mixSrc N r) (mixDst N r) (center_mono I true _)
  have hdis : P.Nonempty → ¬ L.Nonempty := by
    rintro ⟨e, he⟩ ⟨f, hf'⟩
    have hep := ((cleanPay_mem _ _ _ _ _).mp he).2.2.2.2
    have hfl := ((cleanPay_mem _ _ _ _ _).mp hf').2.2.2.2
    rw [hleaf] at hep hfl
    obtain ⟨r₁, hr₁, hp'⟩ := (center_member I false (mleaf r) e.1).mp hep
    obtain ⟨r₂, hr₂, hl'⟩ := (center_member I true (mleaf r) f.1).mp hfl
    have eq₁ : r₁ = r := hr₁
    have eq₂ : r₂ = r := hr₂
    exact center_labels_disjoint I r e.1 f.1 (eq₁ ▸ hp') (eq₂ ▸ hl')
  change (P ∪ exchange L).card ≤ 1
  by_cases hP : P.Nonempty
  · have hz := Finset.not_nonempty_iff_eq_empty.mp (hdis hP)
    rw [hz, show exchange (∅ : Finset (Fin N × Fin N)) = ∅ by simp [exchange], Finset.union_empty]
    exact hp
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hP
    rw [hz, Finset.empty_union, exchange_card]
    exact hl

private noncomputable def centerSlotPay {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (e : Occ C) : Finset (Fin N × Fin N) := by
  classical
  exact centerPayBoth I (.inl e) ∪
    if orAt e then centerPayBoth I (.inr (e,0)) else
      centerPayBoth I (.inr (e,0)) ∪ centerPayBoth I (.inr (e,1))

private lemma every_center_slot {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) (p l : Fin N)
    (he : (p,l) ∈ centerPayBoth I r) : ∃ e : Occ C, (p,l) ∈ centerSlotPay I e := by
  classical
  rcases r with e | ⟨e,i⟩
  · exact ⟨e, Finset.mem_union_left _ he⟩
  · refine ⟨e, Finset.mem_union_right _ ?_⟩
    by_cases ho : orAt e
    · simp only [ho, ite_true]
      simpa [centerPayBoth, mixSrc, mixDst, ho] using he
    · simp only [ho, ite_false]
      fin_cases i
      · exact Finset.mem_union_left _ he
      · exact Finset.mem_union_right _ he

private lemma centerSlotPay_or {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (e : Occ C)
    (ho : orAt e) : (centerSlotPay I e).card ≤ 4 := by
  classical
  have h0 := centerPayBoth_card I hf (.inl e)
  have h1 := centerPayBoth_card I hf (.inr (e,0))
  rw [centerSlotPay, ite_eq_left ho]
  exact (Finset.card_union_le _ _).trans (by omega)

private lemma centerSlotPay_and {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (e : Occ C)
    (ha : andAt e) : (centerSlotPay I e).card ≤ 3 := by
  classical
  have ho : ¬ orAt e := fun ho => GateOp.noConfusion (ha.symm.trans ho)
  have h0 := centerPayBoth_leaf I hf (.inl e) (by simp [mixDst, ho])
  have h1 := centerPayBoth_leaf I hf (.inr (e,0)) (by simp [mixDst, ho])
  have h2 := centerPayBoth_leaf I hf (.inr (e,1)) (by simp [mixDst, ho])
  rw [centerSlotPay, ite_eq_right ho]
  have hU := Finset.card_union_le (centerPayBoth I (.inl e))
    (centerPayBoth I (.inr (e,0)) ∪ centerPayBoth I (.inr (e,1)))
  have hV := Finset.card_union_le (centerPayBoth I (.inr (e,0))) (centerPayBoth I (.inr (e,1)))
  omega

private lemma center_bound_by_ops {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hf : fourFree I) :
    (cleanEdgeCover I (centerNode I (C := C) false) ∪
      exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true))).card ≤
      8 * (orRows C).card + 6 * (andRows C).card := by
  classical
  let O : Finset (Occ C) := (orRows C) ×ˢ univ
  let A : Finset (Occ C) := (andRows C) ×ˢ univ
  have hcO : (O.biUnion (centerSlotPay I)).card ≤ 4 * O.card := by
    calc
      _ ≤ ∑ e ∈ O, (centerSlotPay I e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ O, 4 := Finset.sum_le_sum (fun e he =>
        centerSlotPay_or I hf e (by simpa [O, orAt, orRows_mem] using he))
      _ = _ := by simp [Nat.mul_comm]
  have hcA : (A.biUnion (centerSlotPay I)).card ≤ 3 * A.card := by
    calc
      _ ≤ ∑ e ∈ A, (centerSlotPay I e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ A, 3 := Finset.sum_le_sum (fun e he =>
        centerSlotPay_and I hf e (by simpa [A, andAt, andRows_mem] using he))
      _ = _ := by simp [Nat.mul_comm]
  have hsub :
      cleanEdgeCover I (centerNode I (C := C) false) ∪
        exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true)) ⊆
      O.biUnion (centerSlotPay I) ∪ A.biUnion (centerSlotPay I) := by
    rintro ⟨p,l⟩ hm
    have he : ∃ e : Occ C, (p,l) ∈ centerSlotPay I e := by
      rcases Finset.mem_union.mp hm with hp | hl
      · obtain ⟨hi, w, hb, hc, hm⟩ := (cleanEdgeCover_mem _ _ _).mp hp
        obtain ⟨r,hr⟩ := center_descend h I false I p l hi w hb hc hm
        exact every_center_slot I r p l (Finset.mem_union_left _ hr)
      · obtain ⟨⟨l',p'⟩, hpair, heq⟩ := Finset.mem_map.mp hl
        change (p',l') = (p,l) at heq
        cases heq
        obtain ⟨hi, w, hb, hc, hm⟩ := (cleanEdgeCover_mem _ _ _).mp hpair
        obtain ⟨r,hr⟩ := center_descend h I true (fun l p => I p l) l p hi w hb hc hm
        exact every_center_slot I r p l (Finset.mem_union_right _ (exchange_mem hr))
    obtain ⟨e, he⟩ := he
    rcases op_kind h e.1 with ha | ho
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e, by simp [A, andRows_mem, ha], he⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e, by simp [O, orRows_mem, ho], he⟩)
  have hA : A.card = 2 * (andRows C).card := by simp [A, Nat.mul_comm]
  have hO : O.card = 2 * (orRows C).card := by simp [O, Nat.mul_comm]
  have hsum := (Finset.card_le_card hsub).trans (Finset.card_union_le
    (O.biUnion (centerSlotPay I)) (A.biUnion (centerSlotPay I)))
  omega

end CleanCenterAccounting

section RefinedPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private theorem exchange_iff (S : Finset (Fin N × Fin N)) (p l : Fin N) :
    (p,l) ∈ exchange S ↔ (l,p) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩, ha, he⟩ := Finset.mem_map.mp h
    change (b,a) = (p,l) at he
    cases he
    exact ha
  · exact exchange_mem

private theorem columnPayment
    (F G : Finset (Fin N)) (S : Finset (Fin N × Fin N))
    (hF : F.card ≤ 3) (hG : G.card ≤ 1) (hsub : S ⊆ F ×ˢ G)
    (hinc : ∀ p l : Fin N, (p,l) ∈ S → I p l)
    (absorb : ∀ l ∈ G, (∀ p ∈ F, I p l) → 2 ≤ F.card → ∀ p ∈ F, (p,l) ∉ S) :
    S.card ≤ 2 := by
  classical
  by_contra! high
  have upper := Finset.card_le_card hsub
  rw [Finset.card_product] at upper
  have noZero : G.card ≠ 0 := by
    intro hz
    rw [hz, Nat.mul_zero] at upper
    omega
  have cardG : G.card = 1 := by omega
  have eq : S = F ×ˢ G := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_product, cardG, Nat.mul_one]
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp cardG
  have hGl : l ∈ G := by simp [hl]
  have hF3 : F.card = 3 := by simp [cardG] at upper; omega
  have all : ∀ p ∈ F, I p l := by
    intro p hp
    exact hinc p l (eq ▸ Finset.mem_product.mpr ⟨hp,hGl⟩)
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  exact absorb l hGl all (by omega) p hp (eq ▸ Finset.mem_product.mpr ⟨hp,hGl⟩)

private theorem badColumnPayment
    (F : Finset (Fin N)) (l : Fin N) (S : Finset (Fin N × Fin N))
    (hF : F.card ≤ 3) (hsub : S ⊆ F ×ˢ {l})
    (hinc : ∀ p l : Fin N, (p,l) ∈ S → I p l)
    (bad : ¬ almost I F l) : S.card ≤ 1 := by
  classical
  let hit := F.filter fun p => I p l
  let miss := F.filter fun p => ¬ I p l
  have ge : 2 ≤ miss.card := by
    change ¬ miss.card ≤ 1 at bad
    omega
  have bound : S ⊆ hit ×ˢ {l} := by
    intro e he
    have b := Finset.mem_product.mp (hsub he)
    have eq : e.2 = l := Finset.mem_singleton.mp b.2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨b.1, eq ▸ hinc e.1 e.2 he⟩,b.2⟩
  have both : hit ∪ miss = F := by
    ext p
    simp only [hit, miss, Finset.mem_union, Finset.mem_filter]
    by_cases h : I p l <;> simp [h]
  have sep : Disjoint hit miss := by
    rw [Finset.disjoint_left]
    intro p hp hnp
    exact (Finset.mem_filter.mp hnp).2 (Finset.mem_filter.mp hp).2
  have added := Finset.card_union_of_disjoint sep
  rw [both] at added
  have smaller := Finset.card_le_card bound
  simp only [Finset.card_product, Finset.card_singleton, Nat.mul_one] at smaller
  omega

private noncomputable def rectPayment (r : Rect C) : Finset (Fin N × Fin N) := by
  classical
  exact (rectPay N r).filter fun e => I e.1 e.2 ∧ e ∉ pureCover N C I

private theorem rectPayment_sub (r : Rect C) :
    rectPayment I r ⊆ single (rpoint N r) ×ˢ single (rline N r) := by
  classical
  intro e he
  have hr := (Finset.mem_filter.mp he).1
  by_cases h : little (rpoint N) (rline N) r
  · simpa [rectPay,h] using hr
  · simp [rectPay,h] at hr

private theorem rectPayment_inc (r : Rect C) {p l : Fin N} (h : (p,l) ∈ rectPayment I r) :
    I p l := (Finset.mem_filter.mp h).2.1

private theorem rectPayment_little (r : Rect C) (h : ¬ little (rpoint N) (rline N) r) :
    rectPayment I r = ∅ := by
  classical
  simp [rectPayment, rectPay, h]

private theorem swapPayment_sub (r : Rect C) :
    exchange (rectPayment I r) ⊆ single (rline N r) ×ˢ single (rpoint N r) := by
  intro ⟨l,p⟩ h
  have orig := (exchange_iff _ l p).mp h
  obtain ⟨hp,hl⟩ := Finset.mem_product.mp (rectPayment_sub I r orig)
  exact Finset.mem_product.mpr ⟨hl,hp⟩

private theorem rectPayment_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) (r : Rect C) :
    (rectPayment I r).card ≤ 2 := by
  classical
  by_cases h : little (rpoint N) (rline N) r
  · rcases h with ⟨hp,hl⟩ | ⟨hp,hl⟩
    · rw [← exchange_card (rectPayment I r)]
      refine columnPayment (fun l p => I p l) _ _ _ hl hp (swapPayment_sub I r)
        (fun l p he => rectPayment_inc I r ((exchange_iff _ l p).mp he)) ?_
      intro p _ all large l hl he
      have hc : clean (fun l p => I p l) (rline N r) p := by
        intro hn
        obtain ⟨k,hk,hnk⟩ := (pureNode_linear hAO true (rectLine N r) (rectLine_simple N r) _).mp hn
        exact hnk (all k hk)
      have used : (p,l) ∈ pureCover N C I :=
        covered_by_pure I (all l hl) (Or.inr ⟨r,hl,Or.inl ⟨large,hc⟩⟩)
      exact (Finset.mem_filter.mp ((exchange_iff _ l p).mp he)).2.2 used
    · refine columnPayment I _ _ _ hp hl (rectPayment_sub I r) (fun _ _ he => rectPayment_inc I r he) ?_
      intro l _ all large p hp he
      have hc : clean I (rpoint N r) l := by
        intro hn
        obtain ⟨k,hk,hnk⟩ := (pureNode_linear hAO false (rectPoint N r) (rectPoint_simple N r) _).mp hn
        exact hnk (all k hk)
      have used : (p,l) ∈ pureCover N C I :=
        covered_by_pure I (all p hp) (Or.inl ⟨r,hp,Or.inl ⟨large,hc⟩⟩)
      exact (Finset.mem_filter.mp he).2.2 used
  · simp [rectPayment_little I r h]

end RefinedPayments

section SharedRectPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private def rectLabel (e : Occ C) (rev : Bool) : Prop :=
  if rev then
    ∃ p : Fin N, single (rpoint N (.inl e)) = {p} ∧
      ¬ almost (fun l p => I p l) (single (rline N (.inl e))) p
  else
    ∃ l : Fin N, single (rline N (.inl e)) = {l} ∧
      ¬ almost I (single (rpoint N (.inl e))) l

private theorem rectLabel_separate (e : Occ C) :
    rectLabel I e true → rectLabel I e false → False := by
  classical
  intro a b
  obtain ⟨p,hp,_⟩ := a
  obtain ⟨l,_,hl⟩ := b
  apply hl
  unfold almost
  exact (Finset.card_filter_le _ _).trans (by simp [hp])

private noncomputable def mixedChoices (e : Occ C) : Finset Bool := by
  classical
  exact Finset.univ.filter fun rev => rectLabel I e rev

private theorem mixedChoices_card (e : Occ C) : (mixedChoices I e).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' : rectLabel I e a := (Finset.mem_filter.mp ha).2
  have hb' : rectLabel I e b := (Finset.mem_filter.mp hb).2
  cases a <;> cases b
  · rfl
  · exact (rectLabel_separate I e hb' ha').elim
  · exact (rectLabel_separate I e ha' hb').elim
  · rfl

private noncomputable def rectSupplement : Rect C → Finset (Fin N × Fin N)
  | .inl e => (mixedChoices I e).biUnion fun rev => mixedPay I (.inr e,rev)
  | .inr _ => ∅

private lemma mixedPay_le_one (t : MixProduct C × Bool) : (mixedPay I t).card ≤ 1 := by
  classical
  unfold mixedPay singletonPay
  split <;> simp_all only [Finset.card_empty, Finset.card_product]
  · exact (Nat.mul_le_mul ‹_ ∧ _›.1 ‹_ ∧ _›.2)
  · omega

private theorem rectSupplement_card (r : Rect C) : (rectSupplement I r).card ≤ 1 := by
  rcases r with e | e
  · calc
      _ ≤ ∑ rev ∈ mixedChoices I e, (mixedPay I (.inr e, rev)).card := Finset.card_biUnion_le
      _ ≤ ∑ _rev ∈ mixedChoices I e, 1 := Finset.sum_le_sum (fun rev _ => mixedPay_le_one I (.inr e,rev))
      _ ≤ 1 := by simpa only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one] using mixedChoices_card I e
  · simp [rectSupplement]

private theorem rectPayment_label (e : Occ C) (rev : Bool) (label : rectLabel I e rev) :
    (rectPayment I (.inl e)).card ≤ 1 := by
  classical
  let r : Rect C := .inl e
  change (rectPayment I r).card ≤ 1
  by_cases littleCase : little (rpoint N) (rline N) r
  · cases rev
    · obtain ⟨l, hl, bad⟩ := label
      change single (rline N r) = {l} at hl
      have big : 2 ≤ (single (rpoint N r)).card := by
        have h := Finset.card_filter_le (single (rpoint N r)) (fun p => ¬ I p l)
        change ¬ (Finset.filter (fun p => ¬ I p l) (single (rpoint N r))).card ≤ 1 at bad
        omega
      have h3 : (single (rpoint N r)).card ≤ 3 := by rcases littleCase with h | h <;> omega
      have hsub := rectPayment_sub I r
      rw [hl] at hsub
      exact badColumnPayment I _ l _ h3 hsub (fun _ _ h => rectPayment_inc I r h) bad
    · obtain ⟨p, hp, bad⟩ := label
      change single (rpoint N r) = {p} at hp
      have big : 2 ≤ (single (rline N r)).card := by
        have h := Finset.card_filter_le (single (rline N r)) (fun l => ¬ I p l)
        change ¬ (Finset.filter (fun l => ¬ I p l) (single (rline N r))).card ≤ 1 at bad
        omega
      have h3 : (single (rline N r)).card ≤ 3 := by rcases littleCase with h | h <;> omega
      rw [← exchange_card (rectPayment I r)]
      have hsub := swapPayment_sub I r
      rw [hp] at hsub
      exact badColumnPayment (fun l p => I p l) _ p _ h3 hsub
        (fun l p h => rectPayment_inc I r ((exchange_iff _ l p).mp h)) bad
  · rw [rectPayment_little I r littleCase]
    simp

private noncomputable def joinedRectPayment (r : Rect C) : Finset (Fin N × Fin N) :=
  rectPayment I r ∪ rectSupplement I r

private theorem joinedRectPayment_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) (r : Rect C) :
    (joinedRectPayment I r).card ≤ 2 := by
  classical
  rcases r with e | e
  · by_cases chosen : (mixedChoices I e).Nonempty
    · obtain ⟨rev,hrev⟩ := chosen
      have h1 := rectPayment_label I e rev (Finset.mem_filter.mp hrev).2
      have h2 := rectSupplement_card I (.inl e)
      have h3 := Finset.card_union_le (rectPayment I (.inl e)) (rectSupplement I (.inl e))
      unfold joinedRectPayment
      omega
    · have empty : mixedChoices I e = ∅ := Finset.not_nonempty_iff_eq_empty.mp chosen
      simpa [joinedRectPayment, rectSupplement, empty] using rectPayment_card I hAO (.inl e)
  · simpa [joinedRectPayment, rectSupplement] using rectPayment_card I hAO (.inr e)

end SharedRectPayments

section CoverByPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private def rectActive : Rect C → Prop
  | .inl e => andAt e
  | .inr (e,_) => andAt e

private theorem mixFamily_active (t : MixProduct C) (valid : validMixed N t) :
    (∀ r ∈ mixFamily N (leftMix t), rectActive r) ∧
      ∀ r ∈ mixFamily N (rightMix N t), rectActive r := by
  rcases t with j | e
  · constructor <;> intro r hr
    · obtain ⟨o,rfl,h,_⟩ := hr
      exact h
    · obtain ⟨o,rfl,h,_⟩ := hr
      exact h
  · constructor
    · intro r hr
      change r = Sum.inl e at hr
      subst r
      exact valid
    · intro r hr
      obtain ⟨o,b,rfl,h,_⟩ := hr
      exact h

private theorem classify_active (t : MixProduct C) (valid : validMixed N t)
    (safeTerm : safe I (mixedTerm N t)) (p l : Fin N) (hit : mixedTerm N t {p} {l}) :
    (pureGood I (rpoint N (C := C)) (rline N) p l ∨
      ∃ r : Rect C, rectActive r ∧ little (rpoint N) (rline N) r ∧
        p ∈ single (rpoint N r) ∧ l ∈ single (rline N r)) ∨
    (badL I (rpoint N) (rline N) (mixFamily N (leftMix t)) l ∧
      badP I (rpoint N) (rline N) (mixFamily N (rightMix N t)) p) ∨
    (badL I (rpoint N) (rline N) (mixFamily N (rightMix N t)) l ∧
      badP I (rpoint N) (rline N) (mixFamily N (leftMix t)) p) := by
  let T := {r : Rect C // rectActive r}
  let F (r : T) := rpoint N r.val
  let G (r : T) := rline N r.val
  let U : Set T := {r : T | r.val ∈ mixFamily N (leftMix t)}
  let V : Set T := {r : T | r.val ∈ mixFamily N (rightMix N t)}
  have active := mixFamily_active t valid
  have derive (W : Set (Rect C)) (X Y : Set (Fin N)) :
      mixHit F G {r : T | r.val ∈ W} X Y → mixHit (rpoint N) (rline N) W X Y := by
    rintro ⟨r, h, hp, hl⟩
    exact ⟨r.val,h,hp,hl⟩
  have cleanAll : safe I (fun X Y => mixHit F G U X Y ∧ mixHit F G V X Y) :=
    fun _ _ h => safeTerm _ _ ⟨derive _ _ _ h.1,derive _ _ _ h.2⟩
  have hitU : mixHit F G U {p} {l} := by
    obtain ⟨r,hr,hp,hl⟩ := hit.1
    exact ⟨⟨r,active.1 r hr⟩,hr,hp,hl⟩
  have hitV : mixHit F G V {p} {l} := by
    obtain ⟨r,hr,hp,hl⟩ := hit.2
    exact ⟨⟨r,active.2 r hr⟩,hr,hp,hl⟩
  have liftP (W : Set (Rect C)) :
      badP I F G {r : T | r.val ∈ W} p → badP I (rpoint N) (rline N) W p := by
    rintro ⟨r,hr,hp,hl⟩
    exact ⟨r.val,hr,hp,hl⟩
  have liftL (W : Set (Rect C)) :
      badL I F G {r : T | r.val ∈ W} l → badL I (rpoint N) (rline N) W l := by
    rintro ⟨r,hr,hp,hl⟩
    exact ⟨r.val,hr,hp,hl⟩
  rcases classify_product I F G cleanAll hitU hitV with ((pg | sg) | left | right)
  · rcases pg with ⟨r,hr,h⟩ | ⟨r,hr,h⟩
    · exact Or.inl (Or.inl (Or.inl ⟨r.val,hr,h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨r.val,hr,h⟩))
  · obtain ⟨r,hr,hp,hl⟩ := sg
    exact Or.inl (Or.inr ⟨r.val,r.prop,hr,hp,hl⟩)
  · exact Or.inr (Or.inl ⟨liftL _ left.1,liftP _ left.2⟩)
  · exact Or.inr (Or.inr ⟨liftL _ right.1,liftP _ right.2⟩)

private noncomputable def andOccs (C : Circuit) : Finset (Occ C) :=
  andRows C ×ˢ Finset.univ

private theorem andOccs_mem {e : Occ C} :
    e ∈ andOccs C ↔ andAt e := by
  simp [andOccs, andRows_mem, andAt]

private noncomputable def andRectangles (C : Circuit) : Finset (Rect C) :=
  (andOccs C).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
  (andOccs C ×ˢ (Finset.univ : Finset (Fin 2))).map ⟨Sum.inr, Sum.inr_injective⟩

private theorem andRectangles_mem {r : Rect C} : r ∈ andRectangles C ↔ rectActive r := by
  classical
  cases r <;> simp [andRectangles, rectActive, andOccs_mem]

private theorem andRectangles_card (C : Circuit) :
    (andRectangles C).card ≤ 6 * (andRows C).card := by
  simpa [andRectangles, andOccs, Finset.card_product] using
    Finset.card_union_le
      ((andOccs C).map (⟨Sum.inl, Sum.inl_injective⟩ : Occ C ↪ Rect C))
      ((andOccs C ×ˢ (Finset.univ : Finset (Fin 2))).map
        (⟨Sum.inr, Sum.inr_injective⟩ : Occ C × Fin 2 ↪ Rect C))
    |>.trans (by simp [andOccs, Finset.card_product]; omega)

private noncomputable def sharpCenter (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :
    Finset (Fin N × Fin N) :=
  cleanEdgeCover I (centerNode I (C := C) false) ∪
    exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true))

private theorem enters_clean_center (t : MixProduct C) (rev : Bool)
    (p l : Fin N)
    (hp : p ∈ single (centerNode I false (centerPoint N t rev)))
    (hl : l ∈ single (centerNode I true (centerLine N t rev)))
    (hcross : ∀ a ∈ single (centerNode I false (centerPoint N t rev)),
      ∀ b ∈ single (centerNode I true (centerLine N t rev)), I a b) :
    (p,l) ∈ sharpCenter I C ∨ (p,l) ∈ mixedPay I (t,rev) := by
  classical
  have hi := hcross p hp l hl
  by_cases hP : 2 ≤ (single (centerNode I false (centerPoint N t rev))).card
  · left
    apply Finset.mem_union_left
    refine (cleanEdgeCover_mem _ _ _).mpr ⟨hi, centerPoint N t rev, hP, ?_, hp⟩
    intro hc
    obtain ⟨a,ha,hn⟩ := (center_linear I false _ _).mp hc
    exact hn (hcross a ha l hl)
  by_cases hL : 2 ≤ (single (centerNode I true (centerLine N t rev))).card
  · left
    apply Finset.mem_union_right
    apply exchange_mem
    refine (cleanEdgeCover_mem _ _ _).mpr ⟨hi, centerLine N t rev, hL, ?_, hl⟩
    intro hc
    obtain ⟨b,hb,hn⟩ := (center_linear I true _ _).mp hc
    exact hn (hcross p hp b hb)
  · right
    have hp' : (single (centerNode I false (centerPoint N t rev))).card ≤ 1 := by omega
    have hl' : (single (centerNode I true (centerLine N t rev))).card ≤ 1 := by omega
    exact singletonPay_mem hp hl ⟨hp',hl'⟩

private noncomputable def smallAtRoot : Finset (Fin N × Fin N) :=
  (andRows C ×ˢ (Finset.univ : Finset Bool)).biUnion fun j => mixedPay I (.inl j.1,j.2)

private noncomputable def smallPure : Finset (Fin N × Fin N) :=
  ((Finset.univ : Finset (Fin 3)) ×ˢ andOccs C).biUnion fun d => purePay (N := N) d

private noncomputable def sharpRects : Finset (Fin N × Fin N) :=
  (andRectangles C).biUnion fun r => joinedRectPayment I r

private theorem payCardOn {S T : Type*} [DecidableEq T] (F : Finset S) (pay : S → Finset T) (b : ℕ)
    (hpay : ∀ s ∈ F, (pay s).card ≤ b) : (F.biUnion pay).card ≤ F.card * b := calc
  _ ≤ ∑ s ∈ F, (pay s).card := Finset.card_biUnion_le
  _ ≤ ∑ _s ∈ F, b := Finset.sum_le_sum hpay
  _ = _ := by simp

private theorem smallAtRoot_card :
    (smallAtRoot (C := C) I).card ≤ 2 * (andRows C).card := by
  have b := payCardOn (andRows C ×ˢ (Finset.univ : Finset Bool))
    (fun j => mixedPay I (.inl j.1,j.2)) 1 (fun j _ => mixedPay_le_one I (.inl j.1,j.2))
  simpa [smallAtRoot, Finset.card_product, Nat.mul_comm] using b

private theorem smallPure_card : (smallPure (N := N) (C := C)).card ≤ 6 * (andRows C).card := by
  classical
  have b := payCardOn ((Finset.univ : Finset (Fin 3)) ×ˢ andOccs C) (purePay (N := N)) 1 (by
    intro d _
    unfold purePay singletonPay
    split
    · rw [Finset.card_product]
      exact Nat.mul_le_mul ‹_ ∧ _›.1 ‹_ ∧ _›.2
    · simp)
  simp [smallPure, andOccs, Finset.card_product] at b ⊢
  omega

private theorem sharpRects_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) :
    (sharpRects (C := C) I).card ≤ 12 * (andRows C).card := by
  have a := andRectangles_card C
  have b := payCardOn (andRectangles C) (joinedRectPayment I) 2 (fun r _ => joinedRectPayment_card I hAO r)
  change (sharpRects (C := C) I).card ≤ _ at b
  omega

end CoverByPayments

section SharpCounting

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private theorem mixed_sharp_cover (hAO : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hf : fourFree I) (t : MixProduct C) (valid : validMixed N t)
    (safeTerm : safe I (mixedTerm N t)) (p l : Fin N) (hi : I p l)
    (hit : mixedTerm N t {p} {l}) :
    (p,l) ∈ pureCover N C I ∨ (p,l) ∈ sharpCenter I C ∨
      (p,l) ∈ sharpRects (C := C) I ∨ (p,l) ∈ smallAtRoot (C := C) I := by
  classical
  have sf (r : Rect C) (X : Set (Fin N)) := pureNode_linear hAO false (rectPoint N r) (rectPoint_simple N r) X
  have sg (r : Rect C) (Y : Set (Fin N)) := pureNode_linear hAO true (rectLine N r) (rectLine_simple N r) Y
  have coverBad (rev : Bool)
      (bp : badP I (rpoint N) (rline N) (mixFamily N (centerPoint N t rev)) p)
      (bl : badL I (rpoint N) (rline N) (mixFamily N (centerLine N t rev)) l) :
      (p,l) ∈ sharpCenter I C ∨ (p,l) ∈ sharpRects (C := C) I ∨ (p,l) ∈ smallAtRoot (C := C) I := by
    have hp : p ∈ single (centerNode I false (centerPoint N t rev)) :=
      (center_member I false _ _).mpr bp
    have hl : l ∈ single (centerNode I true (centerLine N t rev)) :=
      (center_member I true _ _).mpr bl
    have cross (a : Fin N) (ha : a ∈ single (centerNode I false (centerPoint N t rev)))
        (b : Fin N) (hb : b ∈ single (centerNode I true (centerLine N t rev))) : I a b := by
      have ap := (center_member I false _ _).mp ha
      have bl' := (center_member I true _ _).mp hb
      cases rev
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg safeTerm bl' ap
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg (fun X Y hs => safeTerm X Y hs.symm) bl' ap
    rcases enters_clean_center I t rev p l hp hl cross with h | paid
    · exact Or.inl h
    · rcases t with j | e
      · apply Or.inr; apply Or.inr
        exact Finset.mem_biUnion.mpr
          ⟨(j,rev), Finset.mem_product.mpr ⟨(andRows_mem j).mpr valid.1, Finset.mem_univ _⟩, paid⟩
      · have active : Sum.inl e ∈ andRectangles C := andRectangles_mem.mpr valid
        have label : rectLabel I e rev := by
          cases rev
          · obtain ⟨r, hr, h1, h2⟩ := bl
            change r = Sum.inl e at hr
            subst r
            exact ⟨l,h1,h2⟩
          · obtain ⟨r, hr, h1, h2⟩ := bp
            change r = Sum.inl e at hr
            subst r
            exact ⟨p,h1,h2⟩
        apply Or.inr; apply Or.inl
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl e,active,Finset.mem_union_right _ ?_⟩
        exact Finset.mem_biUnion.mpr
          ⟨rev,Finset.mem_filter.mpr ⟨Finset.mem_univ _,label⟩,paid⟩
  rcases classify_active I t valid safeTerm p l hit with ((h | h) | h | h)
  · exact Or.inl (covered_by_pure I hi h)
  · obtain ⟨r, act, littleCase, hp, hl⟩ := h
    by_cases used : (p,l) ∈ pureCover N C I
    · exact Or.inl used
    · refine Or.inr (Or.inr (Or.inl (Finset.mem_biUnion.mpr
        ⟨r,andRectangles_mem.mpr act,Finset.mem_union_left _ ?_⟩)))
      exact Finset.mem_filter.mpr ⟨by simp [rectPay,littleCase,hp,hl],hi,used⟩
  · exact Or.inr (coverBad false h.2 h.1)
  · exact Or.inr (coverBad true h.2 h.1)

private theorem twice_sharp_bound (hAO : PEqualNP.TopForm.IsAO2 (N + N) C) (hf : fourFree I)
    (hFun : ∀ {X Y : Set (Fin N)}, Hom N C C.output 2 2 X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l) :
    (twiceEdges N C I).card ≤ 32*C.size+2*(andRows C).card := by
  classical
  let U := pureCover N C I
  let V := sharpCenter I C
  let R := sharpRects (C := C) I
  let M := smallAtRoot (C := C) I
  let P := smallPure (N := N) (C := C)
  have fund : U.card ≤ 24 * (orRows C).card + 8 * (andRows C).card := by
    have full := Finset.card_union_le
      (edgeCover I (pureNode N (C := C) false) pureSimple)
      (exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple))
    rw [exchange_card] at full
    have h1 := pure_bound_by_ops hAO I hf false
    have h2 := pure_bound_by_ops hAO (fun l p => I p l) (swapped_free I hf) true
    change (pureCover N C I).card ≤ _
    unfold pureCover
    omega
  have cen : V.card ≤ 8 * (orRows C).card + 6 * (andRows C).card :=
    center_bound_by_ops I hAO hf
  have rectBound : R.card ≤ 12 * (andRows C).card := sharpRects_card I hAO
  have mix : M.card ≤ 2 * (andRows C).card := smallAtRoot_card I
  have one : P.card ≤ 6 * (andRows C).card := smallPure_card
  have all : twiceEdges N C I ⊆ U ∪ (V ∪ (R ∪ (M ∪ P))) := by
    rintro ⟨p,l⟩ he
    obtain ⟨hi, hh⟩ := (Finset.mem_filter.mp he).2
    rcases product_normal hAO hh with ⟨t,valid,hit⟩ | ⟨d,valid,hit⟩
    · have safeTerm : safe I (mixedTerm N t) := fun x y h =>
        hFun (mixed_sound hAO valid h.1 h.2)
      rcases mixed_sharp_cover I hAO hf t valid safeTerm p l hi hit with hu | hv | hr | hm
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hr))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_union_left _ hm)))
    · have safeTerm : safe I (pureTerm N d) := fun x y h =>
        hFun (pure_sound hAO valid h.1 h.2)
      rcases pure_charges I d safeTerm p l hi hit with hu | hp
      · exact Finset.mem_union_left _ hu
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨d,Finset.mem_product.mpr ⟨Finset.mem_univ _,andOccs_mem.mpr valid.1⟩,hp⟩
  have h0 := Finset.card_le_card all
  have h1 := Finset.card_union_le U (V ∪ (R ∪ (M ∪ P)))
  have h2 := Finset.card_union_le V (R ∪ (M ∪ P))
  have h3 := Finset.card_union_le R (M ∪ P)
  have h4 := Finset.card_union_le M P
  have count := gate_card_sum hAO
  omega

end SharpCounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


private def addGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], n + C.size⟩

private lemma addSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate n C op a b).size = C.size + 1 := by simp [Circuit.size, addGate]

private lemma addAO {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ} (ha : a < n+C.size) (hb : b < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (addGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact hop
  · intro j hj i hi
    change j < (C.gates ++ [_]).length at hj
    change i ∈ ((C.gates ++ [_]).getD j _).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h.2.1 j hj' i hi
    · simp only [List.length_append, List.length_singleton] at hj
      obtain rfl : j = C.gates.length := by omega
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.2.2 g hg
    · obtain rfl := List.mem_singleton.mp hg
      rfl

private lemma evalLast {α : Type} (d : α) (f : GateOp → List α → α) (xs : List α)
    {n : ℕ} (hx : xs.length = n) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    (evalFrom d f (addGate n C op a b).gates xs).getD i d =
    if i = n+C.size then f op [(evalFrom d f C.gates xs).getD a d,(evalFrom d f C.gates xs).getD b d]
    else (evalFrom d f C.gates xs).getD i d := by
  let w := evalFrom d f C.gates xs
  have hl : w.length = n+C.size := by simp [w,evalFrom_length,hx,Circuit.size]
  change (evalFrom d f (C.gates ++ [_]) xs).getD i d = _
  simp only [evalFrom,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
  change (w ++ [f op [w.getD a d,w.getD b d]]).getD i d = if i = n+C.size then _ else w.getD i d
  rcases lt_trichotomy i (n+C.size) with hi | rfl | hi
  · rw [if_neg hi.ne,List.getD_append _ _ _ _ (by omega)]
  · rw [if_pos rfl,List.getD_append_right _ _ _ _ (by omega)]
    simp [hl] <;> rfl
  · rw [if_neg hi.ne',List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private lemma wordLast (n : ℕ) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    words n (addGate n C op a b) i = if i = n+C.size then
      wordOp op [words n C a,words n C b] else words n C i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private lemma boolLast {n : ℕ} (C : Circuit) (z : Fin n → Bool) (op : GateOp) (a b i : ℕ) :
    circuitValue (addGate n C op a b) z i = if i = n+C.size then
      op.eval [circuitValue C z a,circuitValue C z b] else circuitValue C z i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private def paidAnd (g : Gate) : Bool := match g.op with | .and => true | _ => false
private lemma paidAnd_true (g : Gate) : paidAnd g=true ↔ g.op=GateOp.and := by
  rcases g with ⟨op,is⟩
  cases op <;> simp [paidAnd]
private lemma cardAnd (C : Circuit) : (andRows C).card = C.gates.countP paidAnd := by
  classical
  have h := List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) paidAnd
  have same : andRows C = Finset.univ.filter (fun i : Fin C.gates.length => paidAnd (C.gates.get i)=true) := by
    ext i
    rw [andRows_mem]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,paidAnd_true] <;> rfl
  rw [List.ofFn_get,←same] at h
  exact h.symm

private lemma paidAddAnd (n : ℕ) (C : Circuit) (a b : ℕ) :
    (addGate n C .and a b).gates.countP paidAnd = C.gates.countP paidAnd + 1 := by
  change (C.gates ++ [_]).countP paidAnd = _
  rw [List.countP_append]
  rfl

private lemma paidAddOr (n : ℕ) (C : Circuit) (a b : ℕ) :
    (addGate n C .or a b).gates.countP paidAnd = C.gates.countP paidAnd := by
  change (C.gates ++ [_]).countP paidAnd = _
  rw [List.countP_append]
  rfl

private lemma bank {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (ho : C.output < n+C.size) (k : ℕ) (hk : k ≤ n) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size+k ∧ D.gates.countP paidAnd = C.gates.countP paidAnd ∧ D.output < n+D.size ∧
      (∀ i < k, [i] ∈ words n D D.output) ∧
      words n D C.output = words n C C.output ∧
      ∀ z : Fin n → Bool, circuitValue D z C.output = circuitValue C z C.output := by
  induction k with
  | zero => exact ⟨C,h,by simp,rfl,ho,by simp,rfl,fun _ => rfl⟩
  | succ k ih =>
    obtain ⟨D,hd,hs,hands,hot,hall,hw,hv⟩ := ih (by omega)
    let E := addGate n D .or D.output k
    have hk' : k < n := by omega
    have hout : C.output ≠ n+D.size := by omega
    refine ⟨E,addAO hd (Or.inr rfl) hot (by omega),by simp [E,addSize,hs,Nat.add_assoc],
      by simpa [E,addGate,paidAnd,List.countP_append] using hands,?_,?_,?_,?_⟩
    · change n+D.size < n+E.size
      simp [E,addSize,Nat.add_assoc]
    · intro i hi
      change [i] ∈ words n E (n+D.size)
      unfold E
      rw [wordLast, if_pos rfl]
      by_cases hh : i = k
      · subst i
        exact Or.inr (by rw [words_input D hk']; rfl)
      · exact Or.inl (hall i (by omega))
    · simpa [E,wordLast,hout] using hw
    · intro z
      simpa [E,boolLast,hout] using hv z

private def augment (n : ℕ) (D : Circuit) (w r : ℕ) : Circuit :=
  addGate n (addGate n D .and w r) .or w (n+D.size)

private lemma augSize (n : ℕ) (D : Circuit) (w r : ℕ) :
    (augment n D w r).size = D.size+2 := by simp [augment,addSize,Nat.add_assoc]

private lemma augAO {n : ℕ} {D : Circuit} (h : PEqualNP.TopForm.IsAO2 n D)
    {w r : ℕ} (hw : w < n+D.size) (hr : r < n+D.size) :
    PEqualNP.TopForm.IsAO2 n (augment n D w r) :=
  addAO (addAO h (Or.inl rfl) hw hr) (Or.inr rfl)
    (by rw [addSize]; omega) (by rw [addSize]; omega)

private lemma augWords {n : ℕ} {D : Circuit} {w r : ℕ} (hw : w < n+D.size) :
    words n (augment n D w r) (augment n D w r).output =
      words n D w ∪ {t | ∃ u ∈ words n D w, ∃ v ∈ words n D r, t = u ++ v} := by
  change words n (addGate n (addGate n D .and w r) .or w (n+D.size))
    (n+(addGate n D .and w r).size) = _
  simp [wordLast,hw.ne,wordOp]

private lemma augValue {n : ℕ} {D : Circuit} {w r : ℕ} (hw : w < n+D.size) (z : Fin n → Bool) :
    circuitValue (augment n D w r) z (augment n D w r).output = circuitValue D z w := by
  change circuitValue (addGate n (addGate n D .and w r) .or w (n+D.size)) z
    (n+(addGate n D .and w r).size) = _
  simp [boolLast,hw.ne,GateOp.eval] <;> tauto

private lemma augOld {n : ℕ} {D : Circuit} {w r i : ℕ} (hi : i < n+D.size) :
    words n (augment n D w r) i = words n D i := by
  have hh : i ≠ n+(D.size+1) := by omega
  simp [augment,wordLast,hi.ne,addSize,hh]

open PEqualNP.GenericRejection

private def activeP {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => z (Fin.castAdd N p) = true

private def activeL {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun l => z (Fin.natAdd N l) = true

private lemma inputRep {N : ℕ} (z : Fin (N+N) → Bool) :
    incidenceInput (activeP z) (activeL z) = List.ofFn z := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [activeP]
  · intro l
    rw [Fin.append_right]
    simp [activeL]

private lemma thinCorrect {N q : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 1 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (z : Fin (N+N) → Bool) (hz : Thin z) :
    circuitFun (N+N) C z = decide (∃ p l : Fin N, p ∈ S l ∧
      z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  classical
  by_cases he : ∃ p l : Fin N, p ∈ S l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  · rw [decide_eq_true he]
    obtain ⟨p,l,hi,hp,hl⟩ := he
    have hinput : List.ofFn (pair p l) = incidenceInput ({p} : Finset (Fin N)) ({l} : Finset (Fin N)) := by
      unfold incidenceInput
      rw [← List.ofFn_fin_append]
      congr 1
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp only [pair,Fin.append_left,Finset.mem_singleton,cast_ne_nat i l,or_false,
          EmbeddingLike.apply_eq_iff_eq]
        simp
      · intro i
        simp only [pair,Fin.append_right,Finset.mem_singleton,Ne.symm (cast_ne_nat p i),false_or]
        simp
    have hv : circuitValue C (pair p l) C.output = true := by
      change C.eval (List.ofFn (pair p l)) = true
      rw [hinput]
      exact hr l p hi
    obtain ⟨t,ht,ha⟩ := (value_eq_terms h _ _).mp hv
    apply (value_eq_terms h _ _).mpr
    refine ⟨t,ht,?_⟩
    intro j hj
    obtain ⟨i,hi,hb⟩ := ha j hj
    refine ⟨i,hi,?_⟩
    rcases (of_decide_eq_true hb : i = Fin.castAdd N p ∨ i = Fin.natAdd N l) with rfl | rfl
    · exact hp
    · exact hl
  · rw [decide_eq_false he]
    change C.eval (List.ofFn z) = false
    rw [← inputRep z]
    apply hf
    · apply le_trans _ hq
      exact Finset.card_le_one_iff.mpr (fun {i} {j} hi hj =>
        hz i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hz
      exact he ⟨p,l,hp,(Finset.mem_filter.mp hz).2,(Finset.mem_filter.mp hl).2⟩

private lemma boundSound {N q : ℕ} {S : Fin N → Finset (Fin N)} {C D : Circuit}
    (hq : 2 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) D)
    (hv : ∀ z : Fin (N+N) → Bool, circuitValue D z D.output = circuitValue C z C.output)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    {X Y : Set (Fin N)} (hh : Hom N D D.output 2 2 X Y) :
    ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l := by
  classical
  obtain ⟨t,ht,ha,hb,hw⟩ := hh
  let L : Finset (Fin N) := Finset.univ.filter (fun l : Fin N => N+l.val ∈ t)
  have hsub : L.map ⟨fun l => N+l.val, fun _ _ he => Fin.ext (Nat.add_left_cancel he)⟩ ⊆
      (t.filter fun w => decide (N ≤ w)).toFinset := by
    intro w hw
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hw
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).2, by change decide (N ≤ N+l.val) = true; simp⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have hlen := List.toFinset_card_le (t.filter fun w => decide (N ≤ w))
  change (t.filter fun w => decide (N ≤ w)).length = 2 at hb
  have hly (l : Fin N) (hl : l ∈ L) : l ∈ Y :=
    (on_line X Y l).mp (hw _ (Finset.mem_filter.mp hl).2)
  have hh' : Hom N D D.output 2 2 X (↑L) := by
    refine ⟨t,ht,ha,hb,?_⟩
    intro j hj
    rcases hw j hj with hh | ⟨l,_,rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
  have hok := hom_sound h hh'
  rw [hv] at hok
  let z := bits X (↑L)
  have hp (p : Fin N) : p ∈ activeP z ↔ p ∈ X := by
    simp only [activeP,Finset.mem_filter,Finset.mem_univ,true_and,z,bits_true]
    exact on_point _ _ _
  have hl (l : Fin N) : l ∈ activeL z ↔ l ∈ L := by
    simp only [activeL,Finset.mem_filter,Finset.mem_univ,true_and,z,bits_true]
    exact on_line _ _ _
  have he : activeL z = L := Finset.ext hl
  by_contra hn
  have hfalse := hf (activeP z) (activeL z) (by rw [he]; omega) (by
    intro l hll
    apply Finset.disjoint_left.mpr
    intro p hpi hpp
    exact hn ⟨p,(hp p).mp hpp,l,hly l ((hl l).mp hll),hpi⟩)
  rw [inputRep] at hfalse
  change C.eval (List.ofFn z) = true at hok
  rw [hfalse] at hok
  contradiction

private lemma fillPoint {N : ℕ} {D : Circuit} {w r a b : ℕ} {p l : Fin N}
    (hw : w < N+N+D.size) (ha : 1 ≤ a) (ha' : a ≤ 2)
    (hr : [p.val] ∈ words (N+N) D r) (hh : Hom N D w a b {p} {l}) :
    Hom N (augment (N+N) D w r) (augment (N+N) D w r).output 2 b {p} {l} := by
  obtain ⟨t,ht,hp,hl,hs⟩ := hh
  by_cases he : a = 2
  · exact ⟨t, (augWords hw).symm ▸ Or.inl ht, hp.trans he,hl,hs⟩
  · refine ⟨t ++ [p.val], ?_, ?_, ?_, ?_⟩
    · rw [augWords hw]
      exact Or.inr ⟨t,ht,_,hr,rfl⟩
    · have he' : pcount N t = 1 := by omega
      simpa [pcount,p.isLt] using he'
    · have hnp : ¬ N ≤ p.val := by omega
      simpa [lcount,hnp] using hl
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hs j hj
      · rw [List.mem_singleton.mp hj]
        exact (on_point _ _ p).mpr rfl

private lemma fillLine {N : ℕ} {D : Circuit} {w r b : ℕ} {p l : Fin N}
    (hw : w < N+N+D.size) (hb : 1 ≤ b) (hb' : b ≤ 2)
    (hr : [N+l.val] ∈ words (N+N) D r) (hh : Hom N D w 2 b {p} {l}) :
    Hom N (augment (N+N) D w r) (augment (N+N) D w r).output 2 2 {p} {l} := by
  obtain ⟨t,ht,hp,hl,hs⟩ := hh
  by_cases he : b = 2
  · exact ⟨t, (augWords hw).symm ▸ Or.inl ht,hp,hl.trans he,hs⟩
  · refine ⟨t ++ [N+l.val], ?_, ?_, ?_, ?_⟩
    · rw [augWords hw]
      exact Or.inr ⟨t,ht,_,hr,rfl⟩
    · have hn : ¬ N+l.val < N := by omega
      simpa [pcount,hn] using hp
    · have he' : lcount N t = 1 := by omega
      simpa [lcount] using he'
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hs j hj
      · rw [List.mem_singleton.mp hj]
        exact (on_line _ _ l).mpr rfl

open PEqualNP.ReadK
def easy {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) :=
  Finset.univ.filter fun e : Fin N × Fin N => e.1∈S e.2 ∧
    readsAtMost C (N+N) (setList {Fin.castAdd N e.1,Fin.natAdd N e.2}) 2=true

theorem easy_budget (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (ho : C.output < N+N+C.size) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    (easy S C).card ≤ 34*C.size+64*N+132 := by
  classical
  let I : Fin N → Fin N → Prop := fun p l => p ∈ S l
  letI : DecidableRel I := fun p l => inferInstanceAs (Decidable (p ∈ S l))
  have hL (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q+1 := by
    simpa [I] using hc l
  have hthin := thinCorrect (by omega : 1 ≤ q) h hr hf
  have hbase := plane_support q N I C hN hL hu h hthin (by omega)
  obtain ⟨B,hB,hBs,hAndB,hBo,hterms,hwords,hval⟩ := bank h ho (N+N) (le_refl _)
  let E := augment (N+N) B C.output B.output
  let F := augment (N+N) E E.output B.output
  have hco : C.output < N+N+B.size := by omega
  have he : PEqualNP.TopForm.IsAO2 (N+N) E := augAO hB hco hBo
  have hes : E.size = B.size+2 := augSize _ _ _ _
  have heo : E.output < N+N+E.size := by
    change N+N+(addGate (N+N) B .and C.output B.output).size < _
    rw [addSize,hes]
    omega
  have hF : PEqualNP.TopForm.IsAO2 (N+N) F := augAO he heo (by omega)
  have hFs : F.size = E.size+2 := augSize _ _ _ _
  have hv (z : Fin (N+N) → Bool) : circuitValue F z F.output = circuitValue C z C.output :=
    (augValue heo z).trans ((augValue hco z).trans (hval z))
  have hcnt := twice_sharp_bound I hF (plane_four_free I hu)
    (fun hh => boundSound (by omega : 2 ≤ q) hF hv hf hh)
  have hsub : easy S C ⊆ twiceEdges N F I := by
    rintro ⟨p,l⟩ hi
    have hpl : I p l := (Finset.mem_filter.mp hi).2.1
    obtain ⟨a,b,ha,ha',hb,hb',hh⟩ := plane_read_cover I h hthin hpl (Finset.mem_filter.mp hi).2.2
    have hhB : Hom N B C.output a b {p} {l} := by
      unfold Hom at hh ⊢
      rw [hwords]
      exact hh
    have hE : Hom N E E.output 2 b {p} {l} :=
      fillPoint hco ha ha' (hterms p.val (by omega)) hhB
    have hw : [N+l.val] ∈ words (N+N) E B.output := by
      rw [show words (N+N) E B.output = words (N+N) B B.output from augOld hBo]
      exact hterms _ (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,fillLine heo hb hb' hw hE⟩
  have hc' := Finset.card_le_card hsub
  have fresh : F.gates.countP paidAnd = C.gates.countP paidAnd+2 := by
    simp only [F,E,augment,paidAddOr,paidAddAnd,hAndB] <;> omega
  have allowed : C.gates.countP paidAnd ≤ C.size := List.countP_le_length
  rw [cardAnd,fresh] at hcnt
  omega

theorem half_suffices (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card=q+1)
    (hu : ∀ p p' : Fin N, p≠p' → ∃! l, p∈S l ∧ p'∈S l)
    (ao : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output<N+N+C.size) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (half : N*(q+1) ≤ 2*(easy S C).card) : N*q ≤ 100*C.size := by
  have base := Order399.fourSquarePlusEleven q N S C (by omega) hN hc hu ao hr hf
  have bound := easy_budget q N S C hq hN hc hu ao ho hr hf
  have big : 127*N+264 ≤ 32*C.size := by
    rw [hN]
    have sq := Nat.mul_le_mul_left q hq
    nlinarith only [base,sq,hq]
  rw [Nat.mul_add,Nat.mul_one] at half
  omega

end Half3471
