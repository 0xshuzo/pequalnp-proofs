import Mathlib
import PEqualNP.Defs

namespace SignedFive19634

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

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

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

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

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)


theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · exact absurd hop (hm p g hg)
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun


/-! ## Family 1: a certified frontier search (Run states closed under the moves of `next`) -/

theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl


set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev U4 := Bool × Bool × Bool × Bool
abbrev UBank := Bool × Bool × Bool × Bool
def unot (a : U4) : U4 := (!a.1, !a.2.1, !a.2.2.1, !a.2.2.2)
def uand (a b : U4) : U4 := (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2 && b.2.2.2)
def uor (a b : U4) : U4 := (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2 || b.2.2.2)
def uempty : UBank := (true,true,true,true)
def ucons (a : U4) (r : UBank) : UBank :=
  let quiet := (a.1 == a.2.1) && (a.2.2.1 == a.2.2.2)
  let lo := !a.1 || a.2.1
  let lo' := !a.2.2.1 || a.2.2.2
  let ok := (lo || lo') && ((!a.2.1 || a.1) || (!a.2.2.2 || a.2.2.1))
  (quiet && r.1,(quiet && r.2.1) || (ok && r.1),lo && r.2.2.1,lo' && r.2.2.2)
def uvalid (r : UBank) : Bool :=
  (!r.1 || (r.2.1 && r.2.2.1 && r.2.2.2)) &&
  (!r.2.1 || (r.2.2.1 || r.2.2.2))
def ucost (r : UBank) : Nat := if r.2.1 then 2 else if r.2.2.1 || r.2.2.2 then 1 else 0
def ucalc : List U4 → UBank
  | [] => uempty
  | a :: r => ucons a (ucalc r)
def ukeep (k : Bool) (a : U4) (r : UBank) : UBank := if k then ucons a r else r
theorem ucalc_ok (xs : List U4) : uvalid (ucalc xs) = true := by
  have c : ∀ (a : U4) (r : UBank), uvalid r = true → uvalid (ucons a r) = true := by decide +kernel
  induction xs with
  | nil => rfl
  | cons a r ih => exact c _ _ ih
theorem ucalc_perm {xs ys : List U4} (p : xs.Perm ys) : ucalc xs = ucalc ys := by
  have c : ∀ (a b : U4) (r : UBank), ucons a (ucons b r) = ucons b (ucons a r) := by decide +kernel
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (ucons a) ih
  | swap a b r => exact c _ _ _
  | trans p q hp hq => exact hp.trans hq
theorem ucalc_keep (k : Bool) (a : U4) (r : List U4) : ucalc (kept k a r) = ukeep k a (ucalc r) := by
  cases k <;> rfl
theorem uoneCost : ∀ (a : U4) (r : UBank) (neg save : Bool), uvalid r = true →
    ucost (ucons a r) ≤ 1 + save.toNat + ucost (ucons (if neg then unot a else a) (ukeep save a r)) := by decide +kernel
theorem utwoCost : ∀ (a b : U4) (r : UBank) (op ka kb : Bool), uvalid r = true →
    ucost (ucons a (ucons b r)) ≤ ka.toNat + kb.toNat +
      ucost (ucons (if op then uand a b else uor a b) (ukeep ka a (ukeep kb b r))) := by decide +kernel
theorem len_keep4 (k : Bool) (a : U4) (r : List U4) : (kept k a r).length = r.length + k.toNat := by
  cases k <;> simp [kept]
theorem unate_run {t xs} (h : Run unot uand uor (true,false,true,false) t xs) :
    xs.length + ucost (ucalc xs) ≤ t + 1 := by
  induction h using Run.fold with
  | done => decide
  | perm hp _ ih => rwa [← hp.length_eq, ← ucalc_perm hp]
  | @one s a r neg save h ih =>
    have hc := uoneCost a (ucalc r) neg save (ucalc_ok r)
    simp only [List.length_cons, ucalc, ucalc_keep, len_keep4] at ih ⊢
    omega
  | @two s a b r op ka kb h ih =>
    have hc := utwoCost a b (ucalc r) op ka kb (ucalc_ok r)
    simp only [List.length_cons, ucalc, ucalc_keep, len_keep4] at ih ⊢
    omega
def probe (p n q m : Nat) (w : Nat) : U4 := (w.testBit p,w.testBit n,w.testBit q,w.testBit m)
theorem probe_run {M Y t xs} (h : NatRun M Y t xs) (p n q m : Nat)
    (hf : probe p n q m M = (true,true,true,true)) (hy : probe p n q m Y = (true,false,true,false)) :
    xs.length + ucost (ucalc (xs.map (probe p n q m))) ≤ t+1 := by
  have eqs : M.testBit p = true ∧ M.testBit n = true ∧ M.testBit q = true ∧ M.testBit m = true := by
    simpa [probe, Prod.mk.injEq] using hf
  have hi : ∀ a, probe p n q m (a ^^^ M) = unot (probe p n q m a) := by
    intro a
    simp [probe, unot, Nat.testBit_xor, eqs.1, eqs.2.1, eqs.2.2.1, eqs.2.2.2]
  have hm : ∀ a b, probe p n q m (a &&& b) = uand (probe p n q m a) (probe p n q m b) := by
    intros; simp [probe,uand,Nat.testBit_and]
  have hj : ∀ a b, probe p n q m (a ||| b) = uor (probe p n q m a) (probe p n q m b) := by
    intros; simp [probe,uor,Nat.testBit_or]
  have hh := Run.map (probe p n q m) hi hm hj h
  rw [hy] at hh
  simpa using unate_run hh

def ucheck (M Y t : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  if hint = 0 then true else
  let z := hint - 1
  let f := probe (z/32768) ((z/1024)%32) ((z/32)%32) (z%32)
  if f M = (true,true,true,true) ∧ f Y = (true,false,true,false) then
    Nat.ble (ws.length + ucost (ucalc (ws.map f))) (t+1)
  else true
theorem ucheck_sound {M Y t ws} (h : NatRun M Y t ws) (i : Nat) : ucheck M Y t ws i = true := by
  unfold ucheck
  split
  · rfl
  · dsimp only
    split
    · rename_i hh
      exact Nat.ble_eq.mpr (probe_run h _ _ _ _ hh.1 hh.2)
    · rfl
def urootHint (ws : List Nat) : Nat := (([([31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],407683),([31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],237667),([31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],133519),([31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],301753),([31,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],131407),([31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416],580273),([31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856],705079),([31,992,1015808,1082401,2164802,4329604,8659208,17318416,32505856],699799),([31,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],694519),([992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],655480)] : List (List Nat × Nat)).lookup (isort ws)).getD 0

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ucheck_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || !ucheck m y cap zs (urootHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK m y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, ucheck_sound hcap, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK m y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr


def code (k : ℕ) : ℕ := 2 ^ (k / 5) + 2 ^ (5 + k % 5)

def ohPts : List ℕ := List.ofFn fun k : Fin 25 => code k.val

theorem ofFn_code : ∀ k : Fin 25, List.ofFn (pt 10 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 5) (by have := k.isLt; omega) : Fin 5)
      (Fin.mk (k.val % 5) (by have := k.isLt; omega) : Fin 5) := by
  decide +kernel

theorem ohPts_length : ohPts.length = 25 := by simp [ohPts]

theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 25) : C.eval (List.ofFn (pt 10 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (5 * (k / 5) + k % 5) = M.testBit k
  rw [Nat.div_add_mod]

theorem enc_rep (M : ℕ) (hM : M < 2 ^ 25) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C) :
    encL (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) ohPts = M := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [encL_testBit]
  by_cases hj : j < 25
  · rw [List.getD_eq_getElem _ _ (by simp [ohPts_length, hj])]
    simp only [ohPts, List.getElem_map, List.getElem_ofFn]
    exact rep_val M C hrep j hj
  · rw [List.getD_eq_default _ _ (by simp [ohPts_length]; omega)]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc M < 2 ^ 25 := hM
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem signed_rep_lb (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ)
    (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 25) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 25) (h0' : zer < 25)
    (hxs : (List.ofFn fun (i : Fin 10) => (fun x : Fin 10 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 33554431 M PD PM = true) (hG : symOK 33554431 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK 33554431 M PD PM G T x h = true)
    (hi : XS.sublists.all (rootOK 33554431 M PD PM G T s) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  have hnc : ∃ a b : Fin 10 → Bool, (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 10 (code one), pt 10 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  have hl := lb_cert (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) ohPts 33554431 M XS PD PM G T s
    (s + 1) rfl (by rw [ohPts_length]; decide) (enc_rep M hM C hrep) hxs hnc hp hG hT hi s
    ⟨C, hfan, hsize, fun _ => rfl⟩
  omega


set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Y_ : Nat := 3315386
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,2874855),(2,4076308),(3,3458157),(4,1163217),(5,197135),(6,154848),(7,193431),(8,42028),(9,36849),(10,6687),(11,4328),(12,5523),(13,1838),(14,1648),(15,735),(16,136),(17,163),(18,54),(19,60),(20,25),(21,11),(22,2),(23,2)]
def PM_ : List (Nat × Nat) := [(0,3315386),(2,3315386),(6,3315386),(8,3315386),(11,3315386),(13,3315386),(14,3315386),(16,3315386),(18,3315386),(19,3315386),(22,3315386),(23,3315386),(24,3315386)]
def G_ : List (List Nat) := [[0,1,2,3,4,5,6,7,8,9,15,16,17,18,19,10,11,12,13,14,20,21,22,23,24]]

def hintWords : Array Nat := #[0,32867,32888,32899,32935,32999,34913,34945,34983,34985,35047,39073,39075,39139,39159,39209,39233,39319,44193,44195,44201,44215,44259,44265,44279,44329,44353,44355,44417,44419,44439,46425,46745,46777,56961,57007,57505,57575,57639,98339,98435,98441,98471,98473,98478,98487,98537,98638,98639,98711,100385,100481,100489,100505,100521,100583,100585,100590,100591,100745,100750,100751,100759,104609,104745,109889,109897,115177,122497,131107,131111,131129,131171,131247,131252,131255,131311,131316,131407,131417,131471,131479,131727,133153,133159,133217,133295,133300,133359,133364,133455,133460,133464,133465,133519,133524,133527,137903,154255,155311,163879,163881,163884,163887,163945,163960,165927,165932,170017,170019,170081,170113,170217,170231,170391,170679,170680,170681,172065,172067,172129,172131,172279,172439,175137,175511,178305,180791,187023,188079,189095,229411,229415,229507,231463,231468,231471,231831,235555,235619,235651,235703,236185,236206,236216,236217,237603,237667,237879,240675,242787,243747,243811,243832,243843,243863,244391,248931,248963,252583,295032,297207,301112,301176,301239,301241,301303,301377,301399,301400,301401,301443,301463,301561,301623,301710,301719,301720,301721,301740,301742,301743,301745,301751,301752,301753,303148,303153,303224,303287,303289,303351,303447,303491,303511,303671,303759,303767,303769,303788,303791,303793,303801,306233,306583,308345,309281,309304,309347,309368,309401,309911,309943,309944,318089,318095,318100,318121,318127,319119,319151,319156,327719,327724,327726,327727,333857,335969,338977,339351,342113,342145,350503,350895,351919,352551,393260,395561,399395,399491,401507,401539,404515,404600,404611,406563,406627,406648,406659,407587,407651,407672,407683,415788,415913,415977,416039,416041,416423,416428,559401,579633,579753,579817,579881,580270,580273,655416,655463,655479,655480,655512,655513,655543,655703,661673,661687,661751,661816,661817,661847,663959,666679,666921,666967,667031,668769,669825,670007,675127,678183,678185,678191,678584,679215,680231,690407,690423,690471,690583,694328,694329,694369,694393,694423,694425,694441,694447,694455,694497,694499,694505,694511,694519,694569,694583,694584,694585,694615,694657,694659,694679,694839,696551,696615,699425,699448,699489,699521,699555,699561,699575,699617,699619,699625,699639,699689,699727,699735,699777,699779,699785,699790,699791,699799,699959,701607,701671,701735,702007,702631,702759,702776,703127,704681,704695,704745,704759,704809,704855,704919,705015,705065,705079,707896,710823,710887,710951,710959,710964,711847,711911,711975,711983,712343,712871,712935,712999]

def digit (c : Char) : Nat :=
  let x := c.toNat
  if 65 ≤ x ∧ x ≤ 90 then x - 65 else
  if 97 ≤ x ∧ x ≤ 122 then x - 97 + 26 else
  if 48 ≤ x ∧ x ≤ 57 then x - 48 + 52 else
  if x = 45 then 62 else 63
def hdict : Array Nat := #[0,32867,32888,32899,32935,32999,34913,34945,34983,34985,35047,39073,39075,39139,39159,39209,39233,39319,44193,44195,44201,44215,44259,44265,44279,44329,44353,44355,44417,44419,44439,46425,46745,46777,56961,57007,57505,57575,57639,98339,98435,98441,98471,98473,98478,98487,98537,98638,98639,98711,100385,100481,100489,100505,100521,100583,100585,100590,100591,100745,100750,100751,100759,104609,104745,109889,109897,115177,122497,131107,131111,131129,131171,131247,131252,131255,131311,131316,131407,131417,131471,131479,131727,133153,133159,133217,133295,133300,133359,133364,133455,133460,133464,133465,133519,133524,133527,137903,154255,155311,163879,163881,163884,163887,163945,163960,165927,165932,170017,170019,170081,170113,170217,170231,170391,170679,170680,170681,172065,172067,172129,172131,172279,172439,175137,175511,178305,180791,187023,188079,189095,229411,229415,229507,231463,231468,231471,231831,235555,235619,235651,235703,236185,236206,236216,236217,237603,237667,237879,240675,242787,243747,243811,243832,243843,243863,244391,248931,248963,252583,295032,297207,301112,301176,301239,301241,301303,301377,301399,301400,301401,301443,301463,301561,301623,301710,301719,301720,301721,301740,301742,301743,301745,301751,301752,301753,303148,303153,303224,303287,303289,303351,303447,303491,303511,303671,303759,303767,303769,303788,303791,303793,303801,306233,306583,308345,309281,309304,309347,309368,309401,309911,309943,309944,318089,318095,318100,318121,318127,319119,319151,319156,327719,327724,327726,327727,333857,335969,338977,339351,342113,342145,350503,350895,351919,352551,393260,395561,399395,399491,401507,401539,404515,404600,404611,406563,406627,406648,406659,407587,407651,407672,407683,415788,415913,415977,416039,416041,416423,416428,559401,579633,579753,579817,579881,580270,580273,655416,655463,655479,655480,655512,655513,655543,655703,661673,661687,661751,661816,661817,661847,663959,666679,666921,666967,667031,668769,669825,670007,675127,678183,678185,678191,678584,679215,680231,690407,690423,690471,690583,694328,694329,694369,694393,694423,694425,694441,694447,694455,694497,694499,694505,694511,694519,694569,694583,694584,694585,694615,694657,694659,694679,694839,696551,696615,699425,699448,699489,699521,699555,699561,699575,699617,699619,699625,699639,699689,699727,699735,699777,699779,699785,699790,699791,699799,699959,701607,701671,701735,702007,702631,702759,702776,703127,704681,704695,704745,704759,704809,704855,704919,705015,705065,705079,707896,710823,710887,710951,710959,710964,711847,711911,711975,711983,712343,712871,712935,712999]
def hpairs : List Char → List (Nat × Nat)
  | a :: b :: c :: d :: rs => (64*digit a + digit b,hdict[64*digit c + digit d]?.getD 0) :: hpairs rs
  | _ => []
def hh (s : String) : List (Nat × Nat) := hpairs s.toList

def T_ : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [3,5412005,6291999] .lf) [3,5412517,6291487] .lf) [4,31,2164802,32268568] (.nd (.nd .lf [4,31,3213890,33317656] .lf) [4,31,4329604,7374369] .lf)) [4,31,4330116,7373857] (.nd (.nd (.nd .lf [4,31,5412005,6291968] .lf) [4,31,5412517,6291456] .lf) [4,512,5412005,6291487] (.nd .lf [4,543,4329604,7373857] .lf))) [4,543,5412005,6291456] (.nd (.nd (.nd (.nd .lf [4,1049119,2164802,33317656] .lf) [4,1082401,4329604,6291999] .lf) [4,1082401,4330116,6291487] (.nd .lf [4,1082431,2165730,4329604,9436424,33047056] .lf)) [4,1082913,4329604,6291487] (.nd (.nd (.nd .lf [5,31,512,4329604,7373857] .lf) [5,31,512,5412005,6291456] .lf) [5,31,992,10824010,23609872] (.nd .lf [5,31,1049088,2164802,33317656] .lf)))) [5,31,1082401,2164802,33317144] (.nd (.nd (.nd (.nd (.nd .lf [5,31,1082401,2165314,33317656] .lf) [5,31,1082401,2165730,4329604,9436424,33047056] .lf) [5,31,1082401,4329604,6291968] (.nd (.nd .lf [5,31,1082401,4330116,6291456] .lf) [5,31,1082913,2164802,33317656] .lf)) [5,31,1082913,4329604,6291456] (.nd (.nd (.nd .lf [5,31,1556463,2164802,8659208] .lf) [5,31,2164802,8659208,31997968] .lf) [5,31,3179553,4330116,32505856] (.nd .lf [5,31,3180065,4329604,32505856] .lf))) [5,31,3180065,4329604,33047056] (.nd (.nd (.nd (.nd .lf [5,31,3213890,8659208,33047056] .lf) [5,31,3247203,4330116,32539681] .lf) [5,31,3247203,4330468,32810281] (.nd .lf [5,31,3247203,5412517,32505856] .lf)) [5,31,3247203,6494918,32505856] (.nd (.nd (.nd .lf [5,31,3247715,4329604,32540193] .lf) [5,31,3247715,5412517,32505856] .lf) [5,31,3247715,6494406,32505856] (.nd .lf [5,31,3248099,4329604,33080881] .lf))))) [5,31,3248099,5412005,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,31,3248099,10824010,33047056] .lf) [5,31,4330116,25977624,32539681] .lf) [5,31,5412005,6495206,33047056] (.nd (.nd .lf [5,31,5412517,6494406,32505856] .lf) [5,31,5412517,6494918,32505856] .lf)) [5,31,8659208,21107332,32539681] (.nd (.nd (.nd .lf [5,31,9742313,10824010,33047056] .lf) [5,512,1082401,4329604,6291487] .lf) [5,543,1082401,2164802,33317656] (.nd .lf [5,543,1082401,4329604,6291456] .lf))) [5,543,3179553,4329604,32505856] (.nd (.nd (.nd (.nd .lf [5,543,3247203,4329604,32539681] .lf) [5,543,3247203,5412005,32505856] .lf) [5,543,3247203,6494406,32505856] (.nd .lf [5,543,4329604,25977624,32539681] .lf)) [5,543,5412005,6494406,32505856] (.nd (.nd (.nd .lf [5,992,1082431,2164802,4329604,9436424,33047056] .lf) [5,992,1082431,2164802,4329604,17825296,32776456] .lf) [5,992,5412005,6291487,17318416] (.nd .lf [5,992,6291487,10824010,17318416] .lf)))) [5,31744,1082431,2165730,4329604,9412872,33047056] (.nd (.nd (.nd (.nd (.nd .lf [5,1047552,1082431,2165730,4329604,8659208,33047056] .lf) [5,1049119,2164802,8659208,33047056] .lf) [5,1082401,2097183,4330116,32505856] (.nd .lf [5,1082401,2097695,4329604,32505856] .lf)) [5,1082401,2097695,4329604,33047056] (.nd (.nd (.nd .lf [5,1082401,2164802,32505887,32641668] .lf) [5,1082401,2164802,32506399,32641156] .lf) [5,1082401,2164831,4330116,32505887] (.nd .lf [5,1082401,2164831,4330468,32776479] .lf))) [5,1082401,2165343,4329604,32506399] (.nd (.nd (.nd (.nd .lf [5,1082401,2165730,4329631,9436424,17318416,32505856] .lf) [5,1082401,2165759,4329604,33047071] .lf) [5,1082401,3144770,4329631,8659944,17318416,32505856] (.nd .lf [5,1082431,2165730,4329604,9436424,17318416,32505856] .lf)) [5,1082431,3144770,4329604,8659944,17318416,32505856] (.nd (.nd (.nd .lf [5,1082913,2097183,4329604,32505856] .lf) [5,1082913,2164802,32505887,32641156] .lf) [5,1082913,2164831,4329604,32505887] (.nd .lf [5,4329604,8659208,16777759,32539681] .lf)))))) [6,31,512,1082401,2164802,33317656] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,512,1082401,4329604,6291456] .lf) [6,31,512,3179553,4329604,32505856] .lf) [6,31,512,3247203,4329604,32539681] (.nd (.nd .lf [6,31,512,3247203,5412005,32505856] .lf) [6,31,512,3247203,6494406,32505856] .lf)) [6,31,512,4329604,25977624,32539681] (.nd (.nd (.nd .lf [6,31,512,5412005,6494406,32505856] .lf) [6,31,992,1082401,2164802,4329604,9436424,33047056] .lf) [6,31,992,1082401,2164802,4329604,17825296,32776456] (.nd .lf [6,31,992,1082401,3144770,8659208,17318416,32641156] .lf))) [6,31,992,1555951,2164802,8659208] (.nd (.nd (.nd (.nd .lf [6,31,992,1826551,2164802,17318416] .lf) [6,31,992,2164802,8659208,23609872] .lf) [6,31,992,2164802,8659208,31998480] (.nd .lf [6,31,992,2164802,14950664,17318416] .lf)) [6,31,992,2164802,17318416,31727880] (.nd (.nd (.nd .lf [6,31,992,3179553,4329604,33047056] .lf) [6,31,992,3213378,8659208,33047056] .lf) [6,31,992,3213378,17318416,32776456] (.nd .lf [6,31,992,3247203,4329604,32810281] .lf)))) [6,31,992,3247203,4329604,33080881] (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,3247203,5412005,32776456] .lf) [6,31,992,3247203,5412005,33047056] .lf) [6,31,992,3247203,6494406,32776456] (.nd (.nd .lf [6,31,992,3247203,6494406,33047056] .lf) [6,31,992,3247203,8659208,33080881] .lf)) [6,31,992,3247203,9741609,33047056] (.nd (.nd (.nd .lf [6,31,992,3247203,10824010,33047056] .lf) [6,31,992,3247203,17318416,32810281] .lf) [6,31,992,3247203,18400817,32776456] (.nd .lf [6,31,992,3247203,19483218,32776456] .lf))) [6,31,992,4329604,7373857,17318416] (.nd (.nd (.nd (.nd .lf [6,31,992,4329604,9403358,17318416] .lf) [6,31,992,4329604,17318416,24151073] .lf) [6,31,992,4329604,25707024,32539681] (.nd .lf [6,31,992,4329604,25977624,32810281] .lf)) [6,31,992,4329604,25977624,33080881] (.nd (.nd (.nd .lf [6,31,992,5412005,6291456,17318416] .lf) [6,31,992,5412005,6494406,32776456] .lf) [6,31,992,5412005,6494406,33047056] (.nd .lf [6,31,992,6291456,10824010,17318416] .lf))))) [6,31,992,8659208,21648020,33080881] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,9741609,10824010,33047056] .lf) [6,31,992,12718212,17318416,32539681] .lf) [6,31,992,12988812,17318416,32810281] (.nd (.nd .lf [6,31,992,12988812,21648020,32539681] .lf) [6,31,992,12988812,25977624,32539681] .lf)) [6,31,992,18400817,19483218,32776456] (.nd (.nd (.nd .lf [6,31,992,21648020,25977624,32539681] .lf) [6,31,31744,1082401,2165730,4329604,9412872,33047056] .lf) [6,31,507375,1082401,2165730,4329604] (.nd .lf [6,31,507375,1083361,2164802,8659208] .lf))) [6,31,507887,1082401,2164802,8659208] (.nd (.nd (.nd (.nd .lf [6,31,777975,1082401,2164802,4330468] .lf) [6,31,1047552,1082401,2165730,4329604,8659208,33047056] .lf) [6,31,1047552,1082401,2165730,8659208,17318416,32641156] (.nd .lf [6,31,1048575,1082401,2164802,4330116] .lf)) [6,31,1048575,1082913,2164802,4329604] (.nd (.nd (.nd .lf [6,31,1049088,2164802,8659208,33047056] .lf) [6,31,1049568,2164802,8659208,33047056] .lf) [6,31,1082401,2097152,4330116,32505856] (.nd .lf [6,31,1082401,2097664,4329604,32505856] .lf)))) [6,31,1082401,2097664,4329604,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2098144,4329604,33047056] .lf) [6,31,1082401,2164802,4330116,32505856] .lf) [6,31,1082401,2164802,4330116,32505887] (.nd .lf [6,31,1082401,2164802,4330116,32539681] .lf)) [6,31,1082401,2164802,4330116,32776456] (.nd (.nd (.nd .lf [6,31,1082401,2164802,4330148,32505856] .lf) [6,31,1082401,2164802,4330180,32505856] .lf) [6,31,1082401,2164802,4330212,32505856] (.nd .lf [6,31,1082401,2164802,4330468,32506112] .lf))) [6,31,1082401,2164802,4330468,32776456] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2164802,4330468,32776479] .lf) [6,31,1082401,2164802,4330468,32810281] .lf) [6,31,1082401,2164802,5412517,32505856] (.nd .lf [6,31,1082401,2164802,5412837,32776456] .lf)) [6,31,1082401,2164802,6494918,32505856] (.nd (.nd (.nd .lf [6,31,1082401,2164802,6495206,32776456] .lf) [6,31,1082401,2164802,8659208,33046544] .lf) [6,31,1082401,2164802,12989420,32776456] (.nd .lf [6,31,1082401,2164802,16236527,32776456] .lf))))))) [6,31,1082401,2164802,17317904,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2164802,21107332,32505856] .lf) [6,31,1082401,2164802,25977112,32505856] .lf) [6,31,1082401,2164802,29223963,32776456] (.nd (.nd .lf [6,31,1082401,2164802,29224219,32505856] .lf) [6,31,1082401,2164802,29224315,32505856] .lf)) [6,31,1082401,2164802,32505856,32641668] (.nd (.nd (.nd .lf [6,31,1082401,2164802,32506368,32641156] .lf) [6,31,1082401,2164802,32642020,32776456] .lf) [6,31,1082401,2164802,32776456,32912364] (.nd .lf [6,31,1082401,2164831,4330116,32505856] .lf))) [6,31,1082401,2164831,4330468,32776456] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2165058,4330468,32505856] .lf) [6,31,1082401,2165314,4329604,32506368] .lf) [6,31,1082401,2165314,4329604,33047056] (.nd .lf [6,31,1082401,2165314,4330116,32505856] .lf)) [6,31,1082401,2165314,6494406,32505856] (.nd (.nd (.nd .lf [6,31,1082401,2165314,8659208,33047056] .lf) [6,31,1082401,2165314,17318416,32776456] .lf) [6,31,1082401,2165314,25977624,32505856] (.nd .lf [6,31,1082401,2165730,4329604,9436424,17318416,32505856] .lf)))) [6,31,1082401,2165730,4329604,32506368] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2165730,4329604,33047056] .lf) [6,31,1082401,2165730,4329604,33047071] .lf) [6,31,1082401,2165730,4329604,33080881] (.nd (.nd .lf [6,31,1082401,2165730,4330116,32505856] .lf) [6,31,1082401,2165730,5412005,33047056] .lf)) [6,31,1082401,2165730,10824010,33047056] (.nd (.nd (.nd .lf [6,31,1082401,2165730,21648020,33047056] .lf) [6,31,1082401,2165730,29224827,33047056] .lf) [6,31,1082401,2165730,32641156,33047056] (.nd .lf [6,31,1082401,2165730,33047056,33182356] .lf))) [6,31,1082401,2165759,4329604,33047056] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2194498,4330116,32505856] .lf) [6,31,1082401,3144770,4329604,8659944,17318416,32505856] .lf) [6,31,1082401,3247203,4330116,32505856] (.nd .lf [6,31,1082401,3247203,4330468,32776456] .lf)) [6,31,1082401,3248099,4329604,33047056] (.nd (.nd (.nd .lf [6,31,1082401,4329604,6495206,33047056] .lf) [6,31,1082401,4329604,31388701,33047056] .lf) [6,31,1082401,4330116,6494406,32505856] (.nd .lf [6,31,1082401,4330116,6494918,32505856] .lf))))) [6,31,1082401,4330116,25977624,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,4330116,31389629,32505856] .lf) [6,31,1082401,4330468,31389629,32776456] .lf) [6,31,1082401,6495206,10824010,32505856] (.nd (.nd .lf [6,31,1082401,6495206,21648020,32505856] .lf) [6,31,1082401,8659208,21107332,32505856] .lf)) [6,31,1082401,8659944,10824010,33047056] (.nd (.nd (.nd .lf [6,31,1082401,8659944,21648020,33047056] .lf) [6,31,1082401,10824010,12989420,32505856] .lf) [6,31,1082401,12989420,21648020,32505856] (.nd .lf [6,31,1082913,2097152,4329604,32505856] .lf))) [6,31,1082913,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [6,31,1082913,2164802,4329604,32505887] .lf) [6,31,1082913,2164802,4329604,32506368] .lf) [6,31,1082913,2164802,4329604,32539681] (.nd .lf [6,31,1082913,2164802,4329604,32540193] .lf)) [6,31,1082913,2164802,4329604,32776456] (.nd (.nd (.nd .lf [6,31,1082913,2164802,4329604,33047056] .lf) [6,31,1082913,2164802,4330116,32505856] .lf) [6,31,1082913,2164802,5412005,32505856] (.nd .lf [6,31,1082913,2164802,5412517,32505856] .lf)))) [6,31,1082913,2164802,6494406,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082913,2164802,8659208,33047056] .lf) [6,31,1082913,2164802,17318416,32776456] .lf) [6,31,1082913,2164802,25977624,32505856] (.nd .lf [6,31,1082913,2164802,29224827,32505856] .lf)) [6,31,1082913,2164802,32505856,32641156] (.nd (.nd (.nd .lf [6,31,1082913,2164831,4329604,32505856] .lf) [6,31,1082913,2165314,4329604,32505856] .lf) [6,31,1082913,2165730,4329604,32505856] (.nd .lf [6,31,1082913,2194498,4329604,32505856] .lf))) [6,31,1082913,3247203,4329604,32505856] (.nd (.nd (.nd (.nd .lf [6,31,1082913,3247715,4329604,32505856] .lf) [6,31,1082913,4329604,6494406,32505856] .lf) [6,31,1082913,4329604,25977624,32505856] (.nd .lf [6,31,1082913,4329604,31389629,32505856] .lf)) [6,31,1082977,2164802,4329604,32505856] (.nd (.nd (.nd .lf [6,31,1083041,2164802,4329604,32505856] .lf) [6,31,1083105,2164802,4329604,32505856] .lf) [6,31,1083361,2164802,4329604,33080881] (.nd .lf [6,31,1083361,2164802,4330468,32776456] .lf)))))) [6,31,1083361,2164802,5412005,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1083361,2164802,5412005,33047056] .lf) [6,31,1083361,2164802,8659208,33047056] .lf) [6,31,1083361,2164802,8659208,33047536] (.nd (.nd .lf [6,31,1083361,2164802,8659208,33080881] .lf) [6,31,1083361,2164802,8659208,33081329] .lf)) [6,31,1083361,2164802,8659208,33317656] (.nd (.nd (.nd .lf [6,31,1083361,2164802,10824010,33047056] .lf) [6,31,1083361,2164802,12988812,32776456] .lf) [6,31,1083361,2164802,17318896,32776456] (.nd .lf [6,31,1083361,2164802,18400817,32776456] .lf))) [6,31,1083361,2164802,24895223,33047056] (.nd (.nd (.nd (.nd .lf [6,31,1083361,2164802,25977624,32776456] .lf) [6,31,1083361,2164802,25977624,33047056] .lf) [6,31,1083361,2164802,32641156,32776456] (.nd .lf [6,31,1083361,2164802,32776456,33047056] .lf)) [6,31,1083361,2164802,33047056,33317656] (.nd (.nd (.nd .lf [6,31,1083361,2165058,4329604,32505856] .lf) [6,31,1083361,6494406,10824010,32505856] .lf) [6,31,1083361,6494406,12988812,32505856] (.nd .lf [6,31,1083361,8659208,10824010,33047056] .lf)))) [6,31,1083361,8659208,31389629,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1083361,10824010,12988812,32505856] .lf) [6,31,1083361,10824010,19483218,32505856] .lf) [6,31,1083361,10824010,25977624,32505856] (.nd (.nd .lf [6,31,1083361,19483218,25977624,32505856] .lf) [6,31,1083391,2164802,8659208,33047056] .lf)) [6,31,2164802,3247203,4330116,32505856] (.nd (.nd (.nd .lf [6,31,2164802,3247203,4330468,32776456] .lf) [6,31,2164802,3247715,4329604,32505856] .lf) [6,31,2164802,3248099,8659208,33047056] (.nd .lf [6,31,2164802,4329604,5412517,32505856] .lf))) [6,31,2164802,4329604,25977112,32505856] (.nd (.nd (.nd (.nd .lf [6,31,2164802,4329604,32471326,32505856] .lf) [6,31,2164802,4329604,32471518,32505856] .lf) [6,31,2164802,4330116,5412005,32505856] (.nd .lf [6,31,2164802,4330116,5412517,32505856] .lf)) [6,31,2164802,4330116,25977624,32505856] (.nd (.nd (.nd .lf [6,31,2164802,4330116,32472030,32505856] .lf) [6,31,2164802,4330468,5412005,32776456] .lf) [6,31,2164802,4330468,5412005,33047056] (.nd .lf [6,31,2164802,4330468,5412837,32776456] .lf))))) [6,31,2164802,4330468,25977624,32776456] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,2164802,4330468,25977624,33047056] .lf) [6,31,2164802,4330468,32472030,32776456] .lf) [6,31,2164802,8659208,9742313,33047056] (.nd (.nd .lf [6,31,2164802,8659208,32471070,33047056] .lf) [6,31,2164802,12989420,17318416,32776456] .lf)) [6,31,2165314,3247203,4329604,32505856] (.nd (.nd (.nd .lf [6,31,2165314,4329604,25977624,32505856] .lf) [6,31,2165730,4329604,5412005,33047056] .lf) [6,31,2165730,4329604,32472030,33047056] (.nd .lf [6,31,2165730,5412005,18400817,32505856] .lf))) [6,31,2165730,5412005,21648020,32505856] (.nd (.nd (.nd (.nd .lf [6,31,2165730,18400817,21648020,32505856] .lf) [6,31,3247203,4330468,8659208,32539681] .lf) [6,31,3247203,4330468,9741609,32505856] (.nd .lf [6,31,3247203,4330468,10824010,32505856] .lf)) [6,31,3248099,4329604,10824010,32505856] (.nd (.nd (.nd .lf [6,31,3248099,4329604,17318416,32539681] .lf) [6,31,3248099,4329604,18400817,32505856] .lf) [6,31,3248099,5412005,17318416,32505856] (.nd .lf [6,31,3248099,10824010,17318416,32505856] .lf)))) [6,31,4329604,8659208,16777728,32539681] (.nd (.nd (.nd (.nd (.nd .lf [6,31,4329604,8659720,17318416,32539681] .lf) [6,31,4329604,9742313,10824010,32505856] .lf) [6,31,4329604,9742313,18400817,32505856] (.nd .lf [6,31,4330116,8659208,17318416,32539681] .lf)) [6,31,4330468,8659208,21648020,32539681] (.nd (.nd (.nd .lf [6,31,4330468,9741609,10824010,32505856] .lf) [6,31,4330468,10824010,19483218,32505856] .lf) [6,31,4330468,10824010,25977624,32505856] (.nd .lf [6,31,4330468,19483218,25977624,32505856] .lf))) [6,31,5412005,6495206,17318416,32505856] (.nd (.nd (.nd (.nd .lf [6,31,5412005,8659944,18400817,32505856] .lf) [6,31,5412005,8659944,21648020,32505856] .lf) [6,31,5412005,9742313,17318416,32505856] (.nd .lf [6,31,5412005,12989420,17318416,32505856] .lf)) [6,31,6495206,10824010,17318416,32505856] (.nd (.nd (.nd .lf [6,31,8659944,18400817,21648020,32505856] .lf) [6,31,9742313,10824010,17318416,32505856] .lf) [6,31,10824010,12989420,17318416,32505856] (.nd .lf [6,287,1082401,2164802,4330468,32505856] .lf)))))))) [6,287,1083361,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,512,1082401,2097183,4329604,32505856] .lf) [6,512,1082401,2164802,32505887,32641156] .lf) [6,512,1082401,2164831,4329604,32505887] (.nd (.nd .lf [6,543,1048575,1082401,2164802,4329604] .lf) [6,543,1082401,2097152,4329604,32505856] .lf)) [6,543,1082401,2164802,4329604,32505856] (.nd (.nd (.nd .lf [6,543,1082401,2164802,4329604,32505887] .lf) [6,543,1082401,2164802,4329604,32506368] .lf) [6,543,1082401,2164802,4329604,32506399] (.nd .lf [6,543,1082401,2164802,4329604,32539681] .lf))) [6,543,1082401,2164802,4329604,32776456] (.nd (.nd (.nd (.nd .lf [6,543,1082401,2164802,4329604,33047056] .lf) [6,543,1082401,2164802,5412005,32505856] .lf) [6,543,1082401,2164802,6494406,32505856] (.nd .lf [6,543,1082401,2164802,8659208,33047056] .lf)) [6,543,1082401,2164802,17318416,32776456] (.nd (.nd (.nd .lf [6,543,1082401,2164802,25977624,32505856] .lf) [6,543,1082401,2164802,29224827,32505856] .lf) [6,543,1082401,2164802,32505856,32641156] (.nd .lf [6,543,1082401,2164831,4329604,32505856] .lf)))) [6,543,1082401,2165314,4329604,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,543,1082401,2165343,4329604,32505856] .lf) [6,543,1082401,2165730,4329604,32505856] .lf) [6,543,1082401,2194498,4329604,32505856] (.nd (.nd .lf [6,543,1082401,3247203,4329604,32505856] .lf) [6,543,1082401,4329604,6494406,32505856] .lf)) [6,543,1082401,4329604,25977624,32505856] (.nd (.nd (.nd .lf [6,543,1082401,4329604,31389629,32505856] .lf) [6,543,2164802,3247203,4329604,32505856] .lf) [6,543,2164802,4329604,5412005,32505856] (.nd .lf [6,543,2164802,4329604,25977624,32505856] .lf))) [6,543,2164802,4329604,32472030,32505856] (.nd (.nd (.nd (.nd .lf [6,543,4329604,8659208,17318416,32539681] .lf) [6,992,31744,1082431,2164802,4329604,9412872,33047056] .lf) [6,992,31744,1082431,2164802,4329604,17809936,32776456] (.nd .lf [6,992,1047552,1082431,2164802,4329604,8659208,33047056] .lf)) [6,992,1047552,1082431,2164802,4329604,17318416,32776456] (.nd (.nd (.nd .lf [6,992,1048607,2164802,8659208,33047056] .lf) [6,992,1048607,2164802,17318416,32776456] .lf) [6,992,1082401,2097183,4329604,33047056] (.nd .lf [6,992,1082401,2164802,4329631,8659208,17825296,32505856] .lf))))) [6,992,1082401,2164802,4329631,8682760,17809936,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,992,1082401,2164802,4329631,9436424,17318416,32505856] .lf) [6,992,1082401,2164831,4329604,32776479] .lf) [6,992,1082401,2164831,4329604,33047071] (.nd (.nd .lf [6,992,1082401,2194498,4329631,8659208,17809936,32505856] .lf) [6,992,1082401,2194498,4329631,9412872,17318416,32505856] .lf)) [6,992,1082401,3144770,4329631,8659208,17318416,32505856] (.nd (.nd (.nd .lf [6,992,1082401,4329604,6291487,17318416] .lf) [6,992,1082431,2164802,4329604,8659208,17825296,32505856] .lf) [6,992,1082431,2164802,4329604,8682760,17809936,32505856] (.nd .lf [6,992,1082431,2164802,4329604,9436424,17318416,32505856] .lf))) [6,992,1082431,2194498,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [6,992,1082431,2194498,4329604,9412872,17318416,32505856] .lf) [6,992,1082431,3144770,4329604,8659208,17318416,32505856] .lf) [6,992,2164802,6291487,8659208,17318416] (.nd .lf [6,992,4329604,8388639,17318416,32539681] .lf)) [6,992,4329604,8659231,17318431,32539681] (.nd (.nd (.nd .lf [6,1023,1082401,2164802,4329604,33047071] .lf) [6,1023,1082401,2164802,8659208,33047536] .lf) [6,1023,1082401,2164802,17318896,32776456] (.nd .lf [6,1023,4329604,8659208,17318431,32539681] .lf)))) [6,31744,1015808,1082431,2165730,4329604,8659208,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31744,1082401,2165730,4329631,9412872,17318416,32505856] .lf) [6,31744,1082401,3115074,4329631,8659944,17318416,32505856] .lf) [6,31744,1082431,2165730,4329604,9412872,17318416,32505856] (.nd .lf [6,31744,1082431,3115074,4329604,8659944,17318416,32505856] .lf)) [6,1047552,1082401,2164802,4329631,8659944,17318416,32505856] (.nd (.nd (.nd .lf [6,1047552,1082401,2165730,4329631,8659208,17318416,32505856] .lf) [6,1047552,1082431,2164802,4329604,8659944,17318416,32505856] .lf) [6,1047552,1082431,2165730,4329604,8659208,17318416,32505856] (.nd .lf [6,1047552,1083361,2164831,4329604,8659208] .lf))) [6,1047552,4329604,8659208,17318431,32539681] (.nd (.nd (.nd (.nd .lf [6,1047552,4329604,8659208,17318896,32573506] .lf) [6,1082401,2164802,4329604,16777759,32505856] .lf) [6,1082401,2164802,4329604,32505856,32506399] (.nd .lf [6,1082401,2164802,4329604,32505856,33553888] .lf)) [6,1082401,2164802,4329604,32505887,32506368] (.nd (.nd (.nd .lf [6,1082401,2164802,4330116,32505856,32505887] .lf) [6,1082401,2164802,4330116,32505856,33554400] .lf) [6,1082401,2164802,4330468,32776456,33554400] (.nd .lf [6,1082401,2164802,8659208,32505887,32642020] .lf)))))) [6,1082401,2164831,4330468,8659208,32505887] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,1082401,2164831,4330468,8659231,32505856] .lf) [6,1082401,2165730,4329604,33047056,33554400] .lf) [6,1082401,2165730,17318416,32505887,32641156] (.nd (.nd .lf [6,1082401,2165759,4329604,17318416,32505887] .lf) [6,1082401,2165759,4329604,17318431,32505856] .lf)) [6,1082401,4329604,8659208,16777759,32505856] (.nd (.nd (.nd .lf [6,1082401,4329604,8659967,17318431,32505856] .lf) [6,1082913,2164802,4329604,32505856,32505887] .lf) [6,1082913,2164802,4329604,32505856,33554400] (.nd .lf [6,1083361,2164802,8659208,32505887,32641156] .lf))) [6,1083361,2164802,8659208,33047056,33554400] (.nd (.nd (.nd (.nd .lf [6,1083361,2164831,4329604,8659208,32505887] .lf) [6,1083361,2164831,4329604,8659231,32505856] .lf) [6,2164802,4330495,8659208,17318416,32505887] (.nd .lf [6,4330468,8659208,17318416,32505887,32573506] .lf)) [7,31,256,1082401,2164802,4330468,32505856] (.nd (.nd (.nd .lf [7,31,256,1083361,2164802,4329604,32505856] .lf) [7,31,512,1048575,1082401,2164802,4329604] .lf) [7,31,512,1082401,2097152,4329604,32505856] (.nd .lf [7,31,512,1082401,2164802,4329604,32505856] .lf)))) [7,31,512,1082401,2164802,4329604,32505887] (.nd (.nd (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,4329604,32506368] .lf) [7,31,512,1082401,2164802,4329604,32539681] .lf) [7,31,512,1082401,2164802,4329604,32776456] (.nd (.nd .lf [7,31,512,1082401,2164802,4329604,33047056] .lf) [7,31,512,1082401,2164802,4330116,32505856] .lf)) [7,31,512,1082401,2164802,5412005,32505856] (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,6494406,32505856] .lf) [7,31,512,1082401,2164802,8659208,33047056] .lf) [7,31,512,1082401,2164802,17318416,32776456] (.nd .lf [7,31,512,1082401,2164802,25977624,32505856] .lf))) [7,31,512,1082401,2164802,29224827,32505856] (.nd (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,32505856,32641156] .lf) [7,31,512,1082401,2164831,4329604,32505856] .lf) [7,31,512,1082401,2165314,4329604,32505856] (.nd .lf [7,31,512,1082401,2165730,4329604,32505856] .lf)) [7,31,512,1082401,2194498,4329604,32505856] (.nd (.nd (.nd .lf [7,31,512,1082401,3247203,4329604,32505856] .lf) [7,31,512,1082401,4329604,6494406,32505856] .lf) [7,31,512,1082401,4329604,25977624,32505856] (.nd .lf [7,31,512,1082401,4329604,31389629,32505856] .lf))))) [7,31,512,1082913,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,512,2164802,3247203,4329604,32505856] .lf) [7,31,512,2164802,4329604,5412005,32505856] .lf) [7,31,512,2164802,4329604,25977624,32505856] (.nd (.nd .lf [7,31,512,2164802,4329604,32472030,32505856] .lf) [7,31,512,4329604,8659208,17318416,32539681] .lf)) [7,31,528,1082401,2164802,4329604,32505856] (.nd (.nd (.nd .lf [7,31,543,1082401,2164802,4329604,32505856] .lf) [7,31,544,1082401,2164802,4329604,32505856] .lf) [7,31,576,1082401,2164802,4329604,32505856] (.nd .lf [7,31,640,1082401,2164802,4329604,32505856] .lf))) [7,31,736,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,31744,1082401,2164802,4329604,9412872,33047056] .lf) [7,31,992,31744,1082401,2164802,4329604,17809936,32776456] .lf) [7,31,992,31744,1082401,3115074,8659208,17318416,32641156] (.nd .lf [7,31,992,507375,1082401,2164802,4329604] .lf)) [7,31,992,507375,1082401,2164802,8659208] (.nd (.nd (.nd .lf [7,31,992,777975,1082401,2164802,4329604] .lf) [7,31,992,777975,1082401,2164802,17318416] .lf) [7,31,992,1014750,4329604,8659208,17318416] (.nd .lf [7,31,992,1047552,1082401,2164802,4329604,8659208,33047056] .lf)))) [7,31,992,1047552,1082401,2164802,4329604,17318416,32776456] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1047552,1082401,2164802,8659208,17318416,32641156] .lf) [7,31,992,1048576,2164802,8659208,33047056] .lf) [7,31,992,1048576,2164802,17318416,32776456] (.nd .lf [7,31,992,1082401,2097152,4329604,33047056] .lf)) [7,31,992,1082401,2164802,4329604,8659208,17825296,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,8682760,17809936,32505856] .lf) [7,31,992,1082401,2164802,4329604,9436424] .lf) [7,31,992,1082401,2164802,4329604,9436424,17318416,32505856] (.nd .lf [7,31,992,1082401,2164802,4329604,17825296] .lf))) [7,31,992,1082401,2164802,4329604,32506112] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,32506368] .lf) [7,31,992,1082401,2164802,4329604,32776456] .lf) [7,31,992,1082401,2164802,4329604,32776479] (.nd .lf [7,31,992,1082401,2164802,4329604,32810281] .lf)) [7,31,992,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,33047071] .lf) [7,31,992,1082401,2164802,4329604,33080881] .lf) [7,31,992,1082401,2164802,4330116,32505856] (.nd .lf [7,31,992,1082401,2164802,4330468,32776456] .lf))))))) [7,31,992,1082401,2164802,5412005,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,5412005,33047056] .lf) [7,31,992,1082401,2164802,6494406,32776456] .lf) [7,31,992,1082401,2164802,6494406,33047056] (.nd (.nd .lf [7,31,992,1082401,2164802,8659208,33047056] .lf) [7,31,992,1082401,2164802,8659208,33047536] .lf)) [7,31,992,1082401,2164802,8659208,33080881] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,8659208,33317656] .lf) [7,31,992,1082401,2164802,9741609,33047056] .lf) [7,31,992,1082401,2164802,10824010,33047056] (.nd .lf [7,31,992,1082401,2164802,12988812,32776456] .lf))) [7,31,992,1082401,2164802,16236015,32776456] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,17318416,32776456] .lf) [7,31,992,1082401,2164802,17318416,32810281] .lf) [7,31,992,1082401,2164802,17318416,33317656] (.nd .lf [7,31,992,1082401,2164802,17318896,32776456] .lf)) [7,31,992,1082401,2164802,18400817,32776456] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,19483218,32776456] .lf) [7,31,992,1082401,2164802,21648020,33047056] .lf) [7,31,992,1082401,2164802,24895223,33047056] (.nd .lf [7,31,992,1082401,2164802,25977624,32776456] .lf)))) [7,31,992,1082401,2164802,25977624,33047056] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,29224827,32776456] .lf) [7,31,992,1082401,2164802,29224827,33047056] .lf) [7,31,992,1082401,2164802,32641156,32776456] (.nd (.nd .lf [7,31,992,1082401,2164802,32641156,33047056] .lf) [7,31,992,1082401,2164802,32776456,32911756] .lf)) [7,31,992,1082401,2164802,32776456,33047056] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,32776456,33317656] .lf) [7,31,992,1082401,2164802,33047056,33182356] .lf) [7,31,992,1082401,2164802,33047056,33317656] (.nd .lf [7,31,992,1082401,2164831,4329604,32776456] .lf))) [7,31,992,1082401,2164831,4329604,33047056] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2165058,4329604,32505856] .lf) [7,31,992,1082401,2165730,4329604,33047056] .lf) [7,31,992,1082401,2194498,4329604,8659208,17809936,32505856] (.nd .lf [7,31,992,1082401,2194498,4329604,9412872,17318416,32505856] .lf)) [7,31,992,1082401,3144770,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,3247203,4329604,32776456] .lf) [7,31,992,1082401,3247203,4329604,33047056] .lf) [7,31,992,1082401,3247203,8659208,33047056] (.nd .lf [7,31,992,1082401,3247203,17318416,32776456] .lf))))) [7,31,992,1082401,4329604,6291456,17318416] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,6494406,32776456] .lf) [7,31,992,1082401,4329604,6494406,33047056] .lf) [7,31,992,1082401,4329604,8659208,17825296] (.nd (.nd .lf [7,31,992,1082401,4329604,8682760,17809936] .lf) [7,31,992,1082401,4329604,9436424,17318416] .lf)) [7,31,992,1082401,4329604,9437183,17318416] (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,17318416,24117248] .lf) [7,31,992,1082401,4329604,25707024,32505856] .lf) [7,31,992,1082401,4329604,25977624,32776456] (.nd .lf [7,31,992,1082401,4329604,25977624,33047056] .lf))) [7,31,992,1082401,4329604,31389629,32776456] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,31389629,33047056] .lf) [7,31,992,1082401,6494406,10824010,32505856] .lf) [7,31,992,1082401,6494406,12988812,32505856] (.nd .lf [7,31,992,1082401,6494406,19483218,32505856] .lf)) [7,31,992,1082401,6494406,21648020,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,8659208,10824010,33047056] .lf) [7,31,992,1082401,8659208,21648020,33047056] .lf) [7,31,992,1082401,8659208,31389629,33047056] (.nd .lf [7,31,992,1082401,10824010,12988812,32505856] .lf)))) [7,31,992,1082401,10824010,19483218,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,10824010,25977624,32505856] .lf) [7,31,992,1082401,12718212,17318416,32505856] .lf) [7,31,992,1082401,12988812,17318416,32776456] (.nd .lf [7,31,992,1082401,12988812,21648020,32505856] .lf)) [7,31,992,1082401,12988812,25977624,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,17318416,19483218,32776456] .lf) [7,31,992,1082401,17318416,31389629,32776456] .lf) [7,31,992,1082401,19483218,21648020,32505856] (.nd .lf [7,31,992,1082401,19483218,25977624,32505856] .lf))) [7,31,992,1082401,21648020,25977624,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,1082431,2164802,8659208,33047056] .lf) [7,31,992,1082431,2164802,17318416,32776456] .lf) [7,31,992,1082913,2164802,4329604,32505856] (.nd .lf [7,31,992,1083361,2164802,4329604,32776456] .lf)) [7,31,992,1083361,2164802,8659208,33047056] (.nd (.nd (.nd .lf [7,31,992,1083361,2164802,17318416,32776456] .lf) [7,31,992,2096161,2164802,8659208,17318416] .lf) [7,31,992,2097151,2164802,8659208,17318416] (.nd .lf [7,31,992,2164802,3247203,4329604,32776456] .lf)))))) [7,31,992,2164802,3247203,4329604,33047056] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,3247203,8659208,33047056] .lf) [7,31,992,2164802,3247203,17318416,32776456] .lf) [7,31,992,2164802,4329604,5412005,32776456] (.nd (.nd .lf [7,31,992,2164802,4329604,5412005,33047056] .lf) [7,31,992,2164802,4329604,25977624,32776456] .lf)) [7,31,992,2164802,4329604,25977624,33047056] (.nd (.nd (.nd .lf [7,31,992,2164802,4329604,32472030,32776456] .lf) [7,31,992,2164802,4329604,32472030,33047056] .lf) [7,31,992,2164802,5412005,9741609,32505856] (.nd .lf [7,31,992,2164802,5412005,12988812,32505856] .lf))) [7,31,992,2164802,5412005,18400817,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,5412005,21648020,32505856] .lf) [7,31,992,2164802,6291456,8659208,17318416] .lf) [7,31,992,2164802,8659208,9741609,33047056] (.nd .lf [7,31,992,2164802,8659208,17318416,31457280] .lf)) [7,31,992,2164802,8659208,21512720,32505856] (.nd (.nd (.nd .lf [7,31,992,2164802,8659208,21648020,33047056] .lf) [7,31,992,2164802,8659208,32472030,33047056] .lf) [7,31,992,2164802,9741609,12988812,32505856] (.nd .lf [7,31,992,2164802,9741609,18400817,32505856] .lf)))) [7,31,992,2164802,9741609,25977624,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,12853512,17318416,32505856] .lf) [7,31,992,2164802,12988812,17318416,32776456] .lf) [7,31,992,2164802,12988812,21648020,32505856] (.nd (.nd .lf [7,31,992,2164802,12988812,25977624,32505856] .lf) [7,31,992,2164802,17318416,18400817,32776456] .lf)) [7,31,992,2164802,17318416,32472030,32776456] (.nd (.nd (.nd .lf [7,31,992,2164802,18400817,21648020,32505856] .lf) [7,31,992,2164802,18400817,25977624,32505856] .lf) [7,31,992,2164802,21648020,25977624,32505856] (.nd .lf [7,31,992,3179553,4329604,17318416,32505856] .lf))) [7,31,992,3213378,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,3247203,4329604,8659208,32539681] .lf) [7,31,992,3247203,4329604,9741609,32505856] .lf) [7,31,992,3247203,4329604,10824010,32505856] (.nd .lf [7,31,992,3247203,4329604,17318416,32539681] .lf)) [7,31,992,3247203,4329604,18400817,32505856] (.nd (.nd (.nd .lf [7,31,992,3247203,4329604,19483218,32505856] .lf) [7,31,992,3247203,5412005,8659208,32505856] .lf) [7,31,992,3247203,5412005,17318416,32505856] (.nd .lf [7,31,992,3247203,6494406,8659208,32505856] .lf))))) [7,31,992,3247203,6494406,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,3247203,8659208,17318416,32539681] .lf) [7,31,992,3247203,8659208,18400817,32505856] .lf) [7,31,992,3247203,8659208,19483218,32505856] (.nd (.nd .lf [7,31,992,3247203,9741609,17318416,32505856] .lf) [7,31,992,3247203,10824010,17318416,32505856] .lf)) [7,31,992,4329604,8388608,17318416,32539681] (.nd (.nd (.nd .lf [7,31,992,4329604,8659208,16236015,32539681] .lf) [7,31,992,4329604,8659208,17318416,32539681] .lf) [7,31,992,4329604,8659208,17318416,32810281] (.nd .lf [7,31,992,4329604,8659208,17318416,33080881] .lf))) [7,31,992,4329604,8659208,17318431,32539681] (.nd (.nd (.nd (.nd .lf [7,31,992,4329604,8659208,21648020,32539681] .lf) [7,31,992,4329604,8659208,25977624,32539681] .lf) [7,31,992,4329604,8659231,17318416,32539681] (.nd .lf [7,31,992,4329604,8659944,17318416,32539681] .lf)) [7,31,992,4329604,9741609,10824010,32505856] (.nd (.nd (.nd .lf [7,31,992,4329604,9741609,18400817,32505856] .lf) [7,31,992,4329604,9741609,25977624,32505856] .lf) [7,31,992,4329604,10824010,19483218,32505856] (.nd .lf [7,31,992,4329604,10824010,25977624,32505856] .lf)))) [7,31,992,4329604,12988812,17318416,32539681] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,4329604,17318416,24895223,32539681] .lf) [7,31,992,4329604,17318416,25977624,32539681] .lf) [7,31,992,4329604,18400817,19483218,32505856] (.nd .lf [7,31,992,4329604,18400817,25977624,32505856] .lf)) [7,31,992,4329604,19483218,25977624,32505856] (.nd (.nd (.nd .lf [7,31,992,5412005,6494406,8659208,32505856] .lf) [7,31,992,5412005,6494406,17318416,32505856] .lf) [7,31,992,5412005,8659208,18400817,32505856] (.nd .lf [7,31,992,5412005,8659208,21648020,32505856] .lf))) [7,31,992,5412005,9741609,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,5412005,12988812,17318416,32505856] .lf) [7,31,992,6494406,8659208,19483218,32505856] .lf) [7,31,992,6494406,8659208,21648020,32505856] (.nd .lf [7,31,992,6494406,10824010,17318416,32505856] .lf)) [7,31,992,6494406,12988812,17318416,32505856] (.nd (.nd (.nd .lf [7,31,992,8659208,12988812,17318416,32539681] .lf) [7,31,992,8659208,17318416,21648020,32539681] .lf) [7,31,992,8659208,17318416,29224827,32539681] (.nd .lf [7,31,992,8659208,18400817,19483218,32505856] .lf))))))))) [7,31,992,8659208,18400817,21648020,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,8659208,19483218,21648020,32505856] .lf) [7,31,992,9741609,10824010,17318416,32505856] .lf) [7,31,992,9741609,12988812,17318416,32505856] (.nd (.nd .lf [7,31,992,10824010,12988812,17318416,32505856] .lf) [7,31,1023,1082401,2164802,4329604,32776456] .lf)) [7,31,1023,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [7,31,1023,1082401,2164802,8659208,33047056] .lf) [7,31,1023,1082401,2164802,17318416,32776456] .lf) [7,31,1023,4329604,8659208,17318416,32539681] (.nd .lf [7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056] .lf))) [7,31,31744,1015808,1082401,2165730,8659208,17318416,32641156] (.nd (.nd (.nd (.nd .lf [7,31,31744,1082401,2164802,4330116,32505856] .lf) [7,31,31744,1082401,2164802,4330468,32776456] .lf) [7,31,31744,1082401,2165730,4329604,9412872,17318416,32505856] (.nd .lf [7,31,31744,1082401,2165730,4329604,33047056] .lf)) [7,31,31744,1082401,3115074,4329604,8659944,17318416,32505856] (.nd (.nd (.nd .lf [7,31,31744,1082913,2164802,4329604,32505856] .lf) [7,31,31744,1083361,2164802,8659208,33047056] .lf) [7,31,1047552,1082401,2164802,4329604,8659944,17318416,32505856] (.nd .lf [7,31,1047552,1082401,2164802,4329604,32776456] .lf)))) [7,31,1047552,1082401,2164802,17318416,32776456] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1047552,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [7,31,1047552,1082401,4329604,8659944,17318416] .lf) [7,31,1047552,1083361,2164802,4329604,8659208] (.nd (.nd .lf [7,31,1047552,1083361,2164802,8659208,17318416] .lf) [7,31,1047552,4329604,8659208,17318416,32539681] .lf)) [7,31,1048575,1082401,2164802,4330468,8659208] (.nd (.nd (.nd .lf [7,31,1048575,1082401,2165730,4329604,17318416] .lf) [7,31,1048575,1082401,4329604,8659944,17318416] .lf) [7,31,1048575,1083361,2164802,4329604,8659208] (.nd .lf [7,31,1048575,1083361,2164802,8659208,17318416] .lf))) [7,31,1048575,2164802,4330468,8659208,17318416] (.nd (.nd (.nd (.nd .lf [7,31,1049568,2164802,8659208,17318416,32505856] .lf) [7,31,1082401,1082913,2164802,4329604,32505856] .lf) [7,31,1082401,1083361,2164802,4329604,32776456] (.nd .lf [7,31,1082401,1083361,2164802,4329604,33047056] .lf)) [7,31,1082401,1083361,2164802,8659208,33047056] (.nd (.nd (.nd .lf [7,31,1082401,1083361,2164802,17318416,32776456] .lf) [7,31,1082401,2098144,4329604,17318416,32505856] .lf) [7,31,1082401,2164802,2165314,4329604,32505856] (.nd .lf [7,31,1082401,2164802,2165730,4329604,32776456] .lf))))) [7,31,1082401,2164802,2165730,4329604,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,2165730,8659208,33047056] .lf) [7,31,1082401,2164802,2165730,17318416,32776456] .lf) [7,31,1082401,2164802,4329604,4330116,32505856] (.nd (.nd .lf [7,31,1082401,2164802,4329604,4330468,32776456] .lf) [7,31,1082401,2164802,4329604,4330468,33047056] .lf)) [7,31,1082401,2164802,4329604,8659944,32776456] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4329604,9436424,32505856] .lf) [7,31,1082401,2164802,4329604,16777728,32505856] .lf) [7,31,1082401,2164802,4329604,32505856,32506368] (.nd .lf [7,31,1082401,2164802,4329604,32505856,33553695] .lf))) [7,31,1082401,2164802,4329604,32505856,33553919] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,4329604,32506848,32776456] .lf) [7,31,1082401,2164802,4329604,32776456,32777192] .lf) [7,31,1082401,2164802,4329604,32776456,33553439] (.nd .lf [7,31,1082401,2164802,4329604,33047056,33553439] .lf)) [7,31,1082401,2164802,4330116,8659208,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330116,17318416,32505856] .lf) [7,31,1082401,2164802,4330116,32505856] .lf) [7,31,1082401,2164802,4330468,8659208,32505856] (.nd .lf [7,31,1082401,2164802,4330468,8659208,32505887] .lf)))) [7,31,1082401,2164802,4330468,8659208,32539681] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330468,8659208,32776456] .lf) [7,31,1082401,2164802,4330468,8659231,32505856] .lf) [7,31,1082401,2164802,4330468,9741609,32505856] (.nd .lf [7,31,1082401,2164802,4330468,10824010,32505856] .lf)) [7,31,1082401,2164802,4330468,17318416,32776456] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330468,21648020,32505856] .lf) [7,31,1082401,2164802,4330468,24895223,32505856] .lf) [7,31,1082401,2164802,4330468,32505856,32776456] (.nd .lf [7,31,1082401,2164802,4330468,32776456] .lf))) [7,31,1082401,2164802,5412837,8659208,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,6495206,8659208,32505856] .lf) [7,31,1082401,2164802,8659208,8659944,33047056] .lf) [7,31,1082401,2164802,8659208,12989420,32505856] (.nd .lf [7,31,1082401,2164802,8659208,16236527,32505856] .lf)) [7,31,1082401,2164802,8659208,17317904,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2164802,8659208,29223963,32505856] .lf) [7,31,1082401,2164802,8659208,32505856,32642020] .lf) [7,31,1082401,2164802,8659208,33047056,33553439] (.nd .lf [7,31,1082401,2164802,8659720,17318416,32505856] .lf)))))) [7,31,1082401,2164802,8659944,17318416,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,17318416,32506848,32776456] .lf) [7,31,1082401,2164802,17318416,32776456,32777192] .lf) [7,31,1082401,2164802,17318416,32776456,33553439] (.nd (.nd .lf [7,31,1082401,2164831,4330468,8659208,32505856] .lf) [7,31,1082401,2165314,4329604,17318416,32505856] .lf)) [7,31,1082401,2165314,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,8659208,33047056] .lf) [7,31,1082401,2165730,4329604,10824010,32505856] .lf) [7,31,1082401,2165730,4329604,16236015,32505856] (.nd .lf [7,31,1082401,2165730,4329604,17318416,32505856] .lf))) [7,31,1082401,2165730,4329604,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,17318416,32539681] .lf) [7,31,1082401,2165730,4329604,17318416,33047056] .lf) [7,31,1082401,2165730,4329604,17318431,32505856] (.nd .lf [7,31,1082401,2165730,4329604,18400817,32505856] .lf)) [7,31,1082401,2165730,4329604,21648020,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,32505856,33047056] .lf) [7,31,1082401,2165730,4329604,33047056] .lf) [7,31,1082401,2165730,5412005,17318416,32505856] (.nd .lf [7,31,1082401,2165730,10824010,17318416,32505856] .lf)))) [7,31,1082401,2165730,17318416,21648020,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2165730,17318416,29224827,32505856] .lf) [7,31,1082401,2165730,17318416,32505856,32641156] .lf) [7,31,1082401,2165759,4329604,17318416,32505856] (.nd (.nd .lf [7,31,1082401,2194498,4329604,9412872,32505856] .lf) [7,31,1082401,3144770,4329604,8659208,32505856] .lf)) [7,31,1082401,3144770,4329604,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,3247203,4330468,8659208,32505856] .lf) [7,31,1082401,3248099,4329604,17318416,32505856] .lf) [7,31,1082401,4329604,6495206,17318416,32505856] (.nd .lf [7,31,1082401,4329604,8389600,17318416,32505856] .lf))) [7,31,1082401,4329604,8659208,16777728,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659720,17318416,32505856] .lf) [7,31,1082401,4329604,8659944,10824010,32505856] .lf) [7,31,1082401,4329604,8659944,16236015,32505856] (.nd .lf [7,31,1082401,4329604,8659944,17318416,32505856] .lf)) [7,31,1082401,4329604,8659944,17318416,32505887] (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659944,17318416,32506848] .lf) [7,31,1082401,4329604,8659944,17318416,32539681] .lf) [7,31,1082401,4329604,8659944,17318416,32776456] (.nd .lf [7,31,1082401,4329604,8659944,17318416,32777192] .lf))))) [7,31,1082401,4329604,8659944,17318416,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659944,17318431,32505856] .lf) [7,31,1082401,4329604,8659944,18400817,32505856] .lf) [7,31,1082401,4329604,8659944,21648020,32505856] (.nd (.nd .lf [7,31,1082401,4329604,8659967,17318416,32505856] .lf) [7,31,1082401,4329604,9436424,17318416,32505856] .lf)) [7,31,1082401,4329604,9742313,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,4329604,12989420,17318416,32505856] .lf) [7,31,1082401,4329604,17318416,24894487,32505856] .lf) [7,31,1082401,4329604,17318416,31388701,32505856] (.nd .lf [7,31,1082401,4330116,8659208,17318416,32505856] .lf))) [7,31,1082401,4330468,8659208,10824010,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,4330468,8659208,21648020,32505856] .lf) [7,31,1082401,4330468,8659208,31389629,32505856] .lf) [7,31,1082401,5412005,8659944,17318416,32505856] (.nd .lf [7,31,1082401,8659944,10824010,17318416,32505856] .lf)) [7,31,1082401,8659944,17318416,21648020,32505856] (.nd (.nd (.nd .lf [7,31,1082401,8659944,17318416,29224827,32505856] .lf) [7,31,1082913,2164802,4329604,8659208,32505856] .lf) [7,31,1082913,2164802,4329604,17318416,32505856] (.nd .lf [7,31,1082913,2164802,4329604,32505856] .lf)))) [7,31,1082913,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082913,4329604,8659208,17318416,32505856] .lf) [7,31,1083361,2164802,4329604,8659208,32505856] .lf) [7,31,1083361,2164802,4329604,8659208,32505887] (.nd .lf [7,31,1083361,2164802,4329604,8659208,32506848] .lf)) [7,31,1083361,2164802,4329604,8659208,32539681] (.nd (.nd (.nd .lf [7,31,1083361,2164802,4329604,8659208,32540641] .lf) [7,31,1083361,2164802,4329604,8659208,32776456] .lf) [7,31,1083361,2164802,4329604,8659208,33047056] (.nd .lf [7,31,1083361,2164802,4329604,8659231,32505856] .lf))) [7,31,1083361,2164802,4329604,10824010,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,4329604,12988812,32505856] .lf) [7,31,1083361,2164802,4329604,17318416,32539681] .lf) [7,31,1083361,2164802,4329604,18400817,32505856] (.nd .lf [7,31,1083361,2164802,4329604,24895223,32505856] .lf)) [7,31,1083361,2164802,4329604,32505856,32776456] (.nd (.nd (.nd .lf [7,31,1083361,2164802,4330468,8659208,32505856] .lf) [7,31,1083361,2164802,5412005,8659208,32505856] .lf) [7,31,1083361,2164802,5412005,17318416,32505856] (.nd .lf [7,31,1083361,2164802,5412837,8659208,32505856] .lf))))))) [7,31,1083361,2164802,6494406,8659208,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,12988812,32505856] .lf) [7,31,1083361,2164802,8659208,16236015,32505856] .lf) [7,31,1083361,2164802,8659208,17318416,32505856] (.nd (.nd .lf [7,31,1083361,2164802,8659208,17318416,32505887] .lf) [7,31,1083361,2164802,8659208,17318416,32506848] .lf)) [7,31,1083361,2164802,8659208,17318416,32539681] (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,17318416,32540641] .lf) [7,31,1083361,2164802,8659208,17318416,32776456] .lf) [7,31,1083361,2164802,8659208,17318416,33047056] (.nd .lf [7,31,1083361,2164802,8659208,17318896,32505856] .lf))) [7,31,1083361,2164802,8659208,18400817,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,18401265,32505856] .lf) [7,31,1083361,2164802,8659208,19483218,32505856] .lf) [7,31,1083361,2164802,8659208,25977624,32505856] (.nd .lf [7,31,1083361,2164802,8659208,29224827,32505856] .lf)) [7,31,1083361,2164802,8659208,32505856,32641156] (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,32505856,33047056] .lf) [7,31,1083361,2164802,8659208,33047056] .lf) [7,31,1083361,2164802,10824010,17318416,32505856] (.nd .lf [7,31,1083361,2164802,17318416,24895223,32505856] .lf)))) [7,31,1083361,2164802,17318416,25977624,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,17318416,32505856,32776456] .lf) [7,31,1083361,2164831,4329604,8659208,32505856] .lf) [7,31,1083361,4329604,6494406,8659208,32505856] (.nd (.nd .lf [7,31,1083361,4329604,8659208,10824010,32505856] .lf) [7,31,1083361,4329604,8659208,17318416,32539681] .lf)) [7,31,1083361,4329604,8659208,18400817,32505856] (.nd (.nd (.nd .lf [7,31,1083361,4329604,8659208,31389629,32505856] .lf) [7,31,1083361,5412005,8659208,17318416,32505856] .lf) [7,31,1083361,8659208,10824010,17318416,32505856] (.nd .lf [7,31,1083361,8659208,17318416,19483218,32505856] .lf))) [7,31,1083361,8659208,17318416,31389629,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083391,2164802,8659208,17318416,32505856] .lf) [7,31,2096161,2164802,8659208,17318416,32505856] .lf) [7,31,2164802,3247203,4330468,8659208,32505856] (.nd .lf [7,31,2164802,3248099,4329604,8659208,32505856] .lf)) [7,31,2164802,3248099,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4195296,8659208,17318416,32505856] .lf) [7,31,2164802,4329604,5412837,8659208,32505856] .lf) [7,31,2164802,4329604,8659208,9742313,32505856] (.nd .lf [7,31,2164802,4329604,8659208,16236527,32505856] .lf))))) [7,31,2164802,4329604,8659208,17317904,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,2164802,4329604,8659208,32471070,32505856] .lf) [7,31,2164802,4329604,8659720,17318416,32505856] .lf) [7,31,2164802,4329604,8659944,17318416,32776456] (.nd (.nd .lf [7,31,2164802,4330116,8659208,17318416,32505856] .lf) [7,31,2164802,4330468,5412005,8659208,32505856] .lf)) [7,31,2164802,4330468,5412005,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4330468,5412837,8659208,32505856] .lf) [7,31,2164802,4330468,8659208,9741609,32505856] .lf) [7,31,2164802,4330468,8659208,16236015,32505856] (.nd .lf [7,31,2164802,4330468,8659208,17318416,32505856] .lf))) [7,31,2164802,4330468,8659208,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,31,2164802,4330468,8659208,17318416,32776456] .lf) [7,31,2164802,4330468,8659208,17318416,33047056] .lf) [7,31,2164802,4330468,8659208,17318896,32505856] (.nd .lf [7,31,2164802,4330468,8659208,19483218,32505856] .lf)) [7,31,2164802,4330468,8659208,21648020,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4330468,8659208,21648372,32505856] .lf) [7,31,2164802,4330468,8659208,25977624,32505856] .lf) [7,31,2164802,4330468,8659208,32472030,32505856] (.nd .lf [7,31,2164802,4330468,10824010,17318416,32505856] .lf)))) [7,31,2164802,4330468,17318416,24895223,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,2164802,4330468,17318416,25977624,32505856] .lf) [7,31,2164802,4330495,8659208,17318416,32505856] .lf) [7,31,2164802,5241988,8659208,17318416,32505856] (.nd .lf [7,31,2164802,6495206,8659208,17318416,32505856] .lf)) [7,31,2164802,8659208,9742313,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,8659208,12989420,17318416,32505856] .lf) [7,31,2164802,8659208,17318416,29223963,32505856] .lf) [7,31,2164802,8659208,17318416,32471070,32505856] (.nd .lf [7,31,2165314,4329604,8659208,17318416,32505856] .lf))) [7,31,2165730,4329604,5412005,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,2165730,4329604,8659208,17318416,32539681] .lf) [7,31,2165730,4329604,10824010,17318416,32505856] .lf) [7,31,2165730,4329604,17318416,18400817,32505856] (.nd .lf [7,31,2165730,4329604,17318416,32472030,32505856] .lf)) [7,31,4329604,4330468,8659208,17318416,32539681] (.nd (.nd (.nd .lf [7,31,4329604,5412005,8659944,17318416,32505856] .lf) [7,31,4329604,8659208,8659944,17318416,32539681] .lf) [7,31,4329604,8659208,17318416,32506848,32539681] (.nd .lf [7,31,4329604,8659208,17318416,32539681,32540641] .lf)))))) [7,31,4329604,8659208,17318416,32539681,33553439] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,4329604,8659944,10824010,17318416,32505856] .lf) [7,31,4329604,8659944,17318416,18400817,32505856] .lf) [7,31,4329604,8659944,17318416,32472030,32505856] (.nd (.nd .lf [7,31,4329604,8659944,17318416,32505856,32539681] .lf) [7,31,4330468,5412005,8659208,17318416,32505856] .lf)) [7,31,4330468,8659208,10824010,17318416,32505856] (.nd (.nd (.nd .lf [7,31,4330468,8659208,17318416,19483218,32505856] .lf) [7,31,4330468,8659208,17318416,31389629,32505856] .lf) [7,31,4330468,8659208,17318416,32505856,32573506] (.nd .lf [7,287,992,1082401,2164802,4329604,32505856] .lf))) [7,512,543,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [7,512,1082401,2164802,4329604,32505856,32505887] .lf) [7,512,1082401,2164802,4329604,32505856,33554400] .lf) [7,543,992,1082401,2164802,4329604,32505856] (.nd .lf [7,543,31744,1082401,2164802,4329604,32505856] .lf)) [7,543,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [7,543,1082401,2164802,4329604,17318416,32505856] .lf) [7,543,1082401,2164802,4329604,32505856] .lf) [7,543,1082401,2164802,8659208,17318416,32505856] (.nd .lf [7,543,1082401,4329604,8659208,17318416,32505856] .lf)))) [7,543,2164802,4329604,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,992,1023,1082401,2164802,4329604,32776456] .lf) [7,992,1023,1082401,2164802,4329604,33047056] .lf) [7,992,1023,1082401,2164802,8659208,33047056] (.nd (.nd .lf [7,992,1023,1082401,2164802,17318416,32776456] .lf) [7,992,1023,4329604,8659208,17318416,32539681] .lf)) [7,992,31744,1015808,1082431,2164802,4329604,8659208,33047056] (.nd (.nd (.nd .lf [7,992,31744,1015808,1082431,2164802,4329604,17318416,32776456] .lf) [7,992,31744,1082401,2164802,4329631,8659208,17809936,32505856] .lf) [7,992,31744,1082401,2164802,4329631,9412872,17318416,32505856] (.nd .lf [7,992,31744,1082401,3115074,4329631,8659208,17318416,32505856] .lf))) [7,992,31744,1082431,2164802,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [7,992,31744,1082431,2164802,4329604,9412872,17318416,32505856] .lf) [7,992,31744,1082431,3115074,4329604,8659208,17318416,32505856] .lf) [7,992,1047552,1082401,2164802,4329631,8659208,17318416,32505856] (.nd .lf [7,992,1047552,1082401,2164802,8659208,32641156] .lf)) [7,992,1047552,1082401,2164802,17318416,32641156] (.nd (.nd (.nd .lf [7,992,1047552,1082401,2164831,4329604,8659208] .lf) [7,992,1047552,1082401,2164831,4329604,17318416] .lf) [7,992,1047552,1082431,2164802,4329604,8659208,17318416,32505856] (.nd .lf [7,992,1047552,2164802,4329631,8659208,17318416] .lf))))) [7,992,1047552,4329604,8659208,17318416,32573506] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,992,1048607,2164802,8659208,17318416,32505856] .lf) [7,992,1082401,2097183,4329604,17318416,32505856] .lf) [7,992,1082401,2164802,4329604,32776456,33554400] (.nd (.nd .lf [7,992,1082401,2164802,4329604,33047056,33554400] .lf) [7,992,1082401,2164802,8659208,32505887,32641156] .lf)) [7,992,1082401,2164802,8659208,33047056,33554400] (.nd (.nd (.nd .lf [7,992,1082401,2164802,17318416,32505887,32641156] .lf) [7,992,1082401,2164802,17318416,32776456,33554400] .lf) [7,992,1082401,2164831,4329604,8659208,32505887] (.nd .lf [7,992,1082401,2164831,4329604,8659231,32505856] .lf))) [7,992,1082401,2164831,4329604,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,992,1082401,2164831,4329604,17318431,32505856] .lf) [7,992,1082401,4329604,8388639,17318416,32505856] .lf) [7,992,1082401,4329604,8659231,17318431,32505856] (.nd .lf [7,992,2164802,4194335,8659208,17318416,32505856] .lf)) [7,992,2164802,4329631,8659208,17318416,32505887] (.nd (.nd (.nd .lf [7,992,4329604,8659208,17318416,32505887,32573506] .lf) [7,992,4329604,8659208,17318416,32539681,33554400] .lf) [7,1023,1082401,2164802,4329604,8659208,32505887] (.nd .lf [7,1023,1082401,2164802,4329604,8659208,32506848] .lf)))) [7,1023,1082401,2164802,4329604,17318416,32505887] (.nd (.nd (.nd (.nd (.nd .lf [7,1023,1082401,2164802,4329604,17318416,32506848] .lf) [7,1023,1082401,2164802,4329604,17318431,32505856] .lf) [7,1023,1082401,2164802,8659208,17318416,32505887] (.nd .lf [7,1023,1082401,2164802,8659208,17318416,32506848] .lf)) [7,1023,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd .lf [7,1023,1082401,4329604,8659208,17318416,32505887] .lf) [7,1023,1082401,4329604,8659208,17318416,32506848] .lf) [7,1023,1082401,4329604,8659208,17318431,32505856] (.nd .lf [7,1023,2164802,4329604,8659208,17318416,32505887] .lf))) [7,1023,2164802,4329604,8659208,17318416,32506848] (.nd (.nd (.nd (.nd .lf [7,1023,2164802,4329604,8659208,17318896,32505856] .lf) [7,31744,1015808,1082401,2164802,4329631,8659944,17318416,32505856] .lf) [7,31744,1015808,1082401,2165730,4329631,8659208,17318416,32505856] (.nd .lf [7,31744,1015808,1082431,2164802,4329604,8659944,17318416,32505856] .lf)) [7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31744,1015808,1083361,2164831,4329604,8659208] .lf) [7,31744,1015808,4329604,8659208,17318431,32539681] .lf) [7,31744,1015808,4329604,8659208,17318896,32573506] (.nd .lf [7,1047552,1082401,2164802,4329604,17318431,32505856] .lf)))))))) [7,1047552,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,1047552,1082401,4329604,8659208,17318431,32505856] .lf) [7,1047552,2164802,4329604,8659208,17318896,32505856] .lf) [7,1082401,2164802,4329604,8659208,32505887,32506848] (.nd (.nd .lf [7,1082401,2164802,4329604,17318416,32505887,32506848] .lf) [7,1082401,2164802,4330468,8659208,32505856,32505887] .lf)) [7,1082401,2164802,4330468,8659208,32505856,33554400] (.nd (.nd (.nd .lf [7,1082401,2164802,8659208,17318416,32505887,32506848] .lf) [7,1082401,2165730,4329604,17318416,32505856,32505887] .lf) [7,1082401,2165730,4329604,17318416,32505856,33554400] (.nd .lf [7,1082401,4329604,8659208,17318416,32505887,32506848] .lf))) [7,1082401,4329604,8659944,17318416,32505856,32505887] (.nd (.nd (.nd (.nd .lf [7,1082401,4329604,8659944,17318416,32505856,33554400] .lf) [7,1083361,2164802,4329604,8659208,32505856,32505887] .lf) [7,1083361,2164802,4329604,8659208,32505856,33554400] (.nd .lf [7,1083361,2164802,8659208,17318416,32505856,32505887] .lf)) [7,1083361,2164802,8659208,17318416,32505856,33554400] (.nd (.nd (.nd .lf [7,2164802,4329604,8659208,17318416,32505887,32506848] .lf) [7,2164802,4330468,8659208,17318416,32505856,32505887] .lf) [7,2164802,4330468,8659208,17318416,32505856,33554400] (.nd .lf [8,31,256,992,1082401,2164802,4329604,32505856] .lf)))) [8,31,512,992,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,512,31744,1082401,2164802,4329604,32505856] .lf) [8,31,512,1082401,2164802,4329604,8659208,32505856] .lf) [8,31,512,1082401,2164802,4329604,17318416,32505856] (.nd (.nd .lf [8,31,512,1082401,2164802,4329604,32505856] .lf) [8,31,512,1082401,2164802,8659208,17318416,32505856] .lf)) [8,31,512,1082401,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,31,512,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056] .lf) [8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456] (.nd .lf [8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156] .lf))) [8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,31744,1082401,2164802,4329604,9412872] .lf) [8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856] .lf) [8,31,992,31744,1082401,2164802,4329604,17809936] (.nd .lf [8,31,992,31744,1082401,2164802,4329604,32776456] .lf)) [8,31,992,31744,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [8,31,992,31744,1082401,2164802,8659208,33047056] .lf) [8,31,992,31744,1082401,2164802,17318416,32776456] .lf) [8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856] (.nd .lf [8,31,992,31744,1082401,4329604,8659208,17809936] .lf))))) [8,31,992,31744,1082401,4329604,9412872,17318416] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,31744,2065441,2164802,8659208,17318416] .lf) [8,31,992,31744,4329604,8659208,17318416,32539681] .lf) [8,31,992,1047552,1082401,2164802,4329604,8659208] (.nd (.nd .lf [8,31,992,1047552,1082401,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,992,1047552,1082401,2164802,4329604,17318416] .lf)) [8,31,992,1047552,1082401,2164802,8659208,17318416] (.nd (.nd (.nd .lf [8,31,992,1047552,1082401,4329604,8659208,17318416] .lf) [8,31,992,1047552,2164802,4329604,8659208,17318416] .lf) [8,31,992,1048575,1082401,2164802,4329604,8659208] (.nd .lf [8,31,992,1048575,1082401,2164802,4329604,17318416] .lf))) [8,31,992,1048575,1082401,2164802,8659208,17318416] (.nd (.nd (.nd (.nd .lf [8,31,992,1048575,1082401,4329604,8659208,17318416] .lf) [8,31,992,1048575,2164802,4329604,8659208,17318416] .lf) [8,31,992,1048576,2164802,8659208,17318416,32505856] (.nd .lf [8,31,992,1082401,2097152,4329604,17318416,32505856] .lf)) [8,31,992,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,8659208,32505887] .lf) [8,31,992,1082401,2164802,4329604,8659208,32506848] .lf) [8,31,992,1082401,2164802,4329604,8659208,32539681] (.nd .lf [8,31,992,1082401,2164802,4329604,8659208,32776456] .lf)))) [8,31,992,1082401,2164802,4329604,8659208,33047056] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,8659231,32505856] .lf) [8,31,992,1082401,2164802,4329604,8682760,32505856] .lf) [8,31,992,1082401,2164802,4329604,9741609,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,10824010,32505856] .lf)) [8,31,992,1082401,2164802,4329604,12988812,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,16236015,32505856] .lf) [8,31,992,1082401,2164802,4329604,17318416,32505856] .lf) [8,31,992,1082401,2164802,4329604,17318416,32505887] (.nd .lf [8,31,992,1082401,2164802,4329604,17318416,32506848] .lf))) [8,31,992,1082401,2164802,4329604,17318416,32539681] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,17318416,32776456] .lf) [8,31,992,1082401,2164802,4329604,17318416,33047056] .lf) [8,31,992,1082401,2164802,4329604,17318431,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,17333776,32505856] .lf)) [8,31,992,1082401,2164802,4329604,18400817,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,19483218,32505856] .lf) [8,31,992,1082401,2164802,4329604,21648020,32505856] .lf) [8,31,992,1082401,2164802,4329604,24895223,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,32505856,32776456] .lf)))))) [8,31,992,1082401,2164802,4329604,32505856,33047056] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,32776456] .lf) [8,31,992,1082401,2164802,4329604,33047056] .lf) [8,31,992,1082401,2164802,4330468,8659208,32505856] (.nd (.nd .lf [8,31,992,1082401,2164802,5412005,8659208,32505856] .lf) [8,31,992,1082401,2164802,5412005,17318416,32505856] .lf)) [8,31,992,1082401,2164802,6494406,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,6494406,17318416,32505856] .lf) [8,31,992,1082401,2164802,8659208,12988812,32505856] .lf) [8,31,992,1082401,2164802,8659208,16236015,32505856] (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,32505856] .lf))) [8,31,992,1082401,2164802,8659208,17318416,32505887] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,32506848] .lf) [8,31,992,1082401,2164802,8659208,17318416,32539681] .lf) [8,31,992,1082401,2164802,8659208,17318416,32776456] (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,33047056] .lf)) [8,31,992,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,18400817,32505856] .lf) [8,31,992,1082401,2164802,8659208,19483218,32505856] .lf) [8,31,992,1082401,2164802,8659208,25977624,32505856] (.nd .lf [8,31,992,1082401,2164802,8659208,29224827,32505856] .lf)))) [8,31,992,1082401,2164802,8659208,32505856,32641156] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,32505856,33047056] .lf) [8,31,992,1082401,2164802,8659208,33047056] .lf) [8,31,992,1082401,2164802,9741609,17318416,32505856] (.nd (.nd .lf [8,31,992,1082401,2164802,10824010,17318416,32505856] .lf) [8,31,992,1082401,2164802,17318416,21648020,32505856] .lf)) [8,31,992,1082401,2164802,17318416,24895223,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,17318416,25977624,32505856] .lf) [8,31,992,1082401,2164802,17318416,29224827,32505856] .lf) [8,31,992,1082401,2164802,17318416,32505856,32641156] (.nd .lf [8,31,992,1082401,2164802,17318416,32505856,32776456] .lf))) [8,31,992,1082401,2164802,17318416,32776456] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164831,4329604,8659208,32505856] .lf) [8,31,992,1082401,2164831,4329604,17318416,32505856] .lf) [8,31,992,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,992,1082401,2194498,4329604,8659208,32505856] .lf)) [8,31,992,1082401,2194498,4329604,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,3247203,4329604,8659208,32505856] .lf) [8,31,992,1082401,3247203,4329604,17318416,32505856] .lf) [8,31,992,1082401,3247203,8659208,17318416,32505856] (.nd .lf [8,31,992,1082401,4329604,6494406,8659208,32505856] .lf))))) [8,31,992,1082401,4329604,6494406,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8388608,17318416,32505856] .lf) [8,31,992,1082401,4329604,8659208,10824010,32505856] .lf) [8,31,992,1082401,4329604,8659208,16236015,32505856] (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,992,1082401,4329604,8659208,17318416,32505887] .lf)) [8,31,992,1082401,4329604,8659208,17318416,32506848] (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,17318416,32539681] .lf) [8,31,992,1082401,4329604,8659208,17318416,32776456] .lf) [8,31,992,1082401,4329604,8659208,17318416,33047056] (.nd .lf [8,31,992,1082401,4329604,8659208,17318431,32505856] .lf))) [8,31,992,1082401,4329604,8659208,17333776,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,18400817,32505856] .lf) [8,31,992,1082401,4329604,8659208,21648020,32505856] .lf) [8,31,992,1082401,4329604,8659208,25977624,32505856] (.nd .lf [8,31,992,1082401,4329604,8659208,31389629,32505856] .lf)) [8,31,992,1082401,4329604,8659231,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659944,17318416,32505856] .lf) [8,31,992,1082401,4329604,8682760,17318416,32505856] .lf) [8,31,992,1082401,4329604,9741609,17318416,32505856] (.nd .lf [8,31,992,1082401,4329604,12988812,17318416,32505856] .lf)))) [8,31,992,1082401,4329604,17318416,19483218,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,17318416,24895223,32505856] .lf) [8,31,992,1082401,4329604,17318416,25977624,32505856] .lf) [8,31,992,1082401,4329604,17318416,31389629,32505856] (.nd .lf [8,31,992,1082401,5412005,8659208,17318416,32505856] .lf)) [8,31,992,1082401,8659208,10824010,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,8659208,12988812,17318416,32505856] .lf) [8,31,992,1082401,8659208,17318416,19483218,32505856] .lf) [8,31,992,1082401,8659208,17318416,21648020,32505856] (.nd .lf [8,31,992,1082401,8659208,17318416,29224827,32505856] .lf))) [8,31,992,1082401,8659208,17318416,31389629,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,1082431,2164802,8659208,17318416,32505856] .lf) [8,31,992,1083361,2164802,4329604,8659208,32505856] .lf) [8,31,992,1083361,2164802,8659208,17318416,32505856] (.nd .lf [8,31,992,1113121,2164802,8659208,17318416,32505856] .lf)) [8,31,992,2164802,3247203,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,3247203,4329604,17318416,32505856] .lf) [8,31,992,2164802,3247203,8659208,17318416,32505856] .lf) [8,31,992,2164802,4194304,8659208,17318416,32505856] (.nd .lf [8,31,992,2164802,4329604,5412005,8659208,32505856] .lf))))))) [8,31,992,2164802,4329604,5412005,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,9741609,32505856] .lf) [8,31,992,2164802,4329604,8659208,16236015,32505856] .lf) [8,31,992,2164802,4329604,8659208,17318416,32505856] (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,17318416,32505887] .lf) [8,31,992,2164802,4329604,8659208,17318416,32506848] .lf)) [8,31,992,2164802,4329604,8659208,17318416,32539681] (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,17318416,32776456] .lf) [8,31,992,2164802,4329604,8659208,17318416,33047056] .lf) [8,31,992,2164802,4329604,8659208,17318896,32505856] (.nd .lf [8,31,992,2164802,4329604,8659208,19483218,32505856] .lf))) [8,31,992,2164802,4329604,8659208,21648020,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,25977624,32505856] .lf) [8,31,992,2164802,4329604,8659208,32472030,32505856] .lf) [8,31,992,2164802,4329604,10824010,17318416,32505856] (.nd .lf [8,31,992,2164802,4329604,12988812,17318416,32505856] .lf)) [8,31,992,2164802,4329604,17318416,18400817,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,17318416,24895223,32505856] .lf) [8,31,992,2164802,4329604,17318416,25977624,32505856] .lf) [8,31,992,2164802,4329604,17318416,32472030,32505856] (.nd .lf [8,31,992,2164802,4329631,8659208,17318416,32505856] .lf)))) [8,31,992,2164802,4330468,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4357252,8659208,17318416,32505856] .lf) [8,31,992,2164802,6494406,8659208,17318416,32505856] .lf) [8,31,992,2164802,8659208,9741609,17318416,32505856] (.nd (.nd .lf [8,31,992,2164802,8659208,12988812,17318416,32505856] .lf) [8,31,992,2164802,8659208,17318416,18400817,32505856] .lf)) [8,31,992,2164802,8659208,17318416,21648020,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,8659208,17318416,29224827,32505856] .lf) [8,31,992,2164802,8659208,17318416,32472030,32505856] .lf) [8,31,992,4329604,5412005,8659208,17318416,32505856] (.nd .lf [8,31,992,4329604,6494406,8659208,17318416,32505856] .lf))) [8,31,992,4329604,8659208,9741609,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,4329604,8659208,10824010,17318416,32505856] .lf) [8,31,992,4329604,8659208,17318416,18400817,32505856] .lf) [8,31,992,4329604,8659208,17318416,19483218,32505856] (.nd .lf [8,31,992,4329604,8659208,17318416,31389629,32505856] .lf)) [8,31,992,4329604,8659208,17318416,32472030,32505856] (.nd (.nd (.nd .lf [8,31,992,4329604,8659208,17318416,32505856,32539681] .lf) [8,31,992,4329604,8659208,17318416,32505856,32573506] .lf) [8,31,992,4329604,8659208,17318416,32539681] (.nd .lf [8,31,1023,1082401,2164802,4329604,8659208,32505856] .lf))))) [8,31,1023,1082401,2164802,4329604,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,1023,1082401,2164802,8659208,17318416,32505856] .lf) [8,31,1023,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,1023,2164802,4329604,8659208,17318416,32505856] (.nd (.nd .lf [8,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856] .lf) [8,31,31744,1015808,1082401,2164802,4329604,32776456] .lf)) [8,31,31744,1015808,1082401,2164802,17318416,32776456] (.nd (.nd (.nd .lf [8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,31744,1015808,1082401,4329604,8659944,17318416] .lf) [8,31,31744,1015808,1083361,2164802,4329604,8659208] (.nd .lf [8,31,31744,1015808,1083361,2164802,8659208,17318416] .lf))) [8,31,31744,1015808,4329604,8659208,17318416,32539681] (.nd (.nd (.nd (.nd .lf [8,31,31744,1082401,2164802,4329604,9412872,32505856] .lf) [8,31,31744,1082401,2164802,4330468,8659208,32505856] .lf) [8,31,31744,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,31744,1082401,3115074,4329604,8659208,32505856] .lf)) [8,31,31744,1082401,3115074,4329604,17318416,32505856] (.nd (.nd (.nd .lf [8,31,31744,1082401,4329604,8659944,17318416,32505856] .lf) [8,31,31744,1082401,4329604,9412872,17318416,32505856] .lf) [8,31,31744,1083361,2164802,4329604,8659208,32505856] (.nd .lf [8,31,31744,1083361,2164802,8659208,17318416,32505856] .lf)))) [8,31,31744,2065441,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,31744,2164802,4330468,8659208,17318416,32505856] .lf) [8,31,31744,2164802,5214340,8659208,17318416,32505856] .lf) [8,31,1047552,1082401,2164802,4329604,8659208,32505856] (.nd .lf [8,31,1047552,1082401,2164802,4329604,17318416,32505856] .lf)) [8,31,1047552,1082401,2164802,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,31,1047552,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,1047552,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,1083361,2164802,4329604,8659208,32505856] (.nd .lf [8,31,1082401,1083361,2164802,4329604,17318416,32505856] .lf))) [8,31,1082401,1083361,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,1082401,1083361,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,2164802,2165730,4329604,8659208,32505856] .lf) [8,31,1082401,2164802,2165730,4329604,17318416,32505856] (.nd .lf [8,31,1082401,2164802,2165730,8659208,17318416,32505856] .lf)) [8,31,1082401,2164802,4329604,4330468,8659208,32505856] (.nd (.nd (.nd .lf [8,31,1082401,2164802,4329604,4330468,17318416,32505856] .lf) [8,31,1082401,2164802,4329604,8659208,8659944,32505856] .lf) [8,31,1082401,2164802,4329604,8659208,32505856,32506848] (.nd .lf [8,31,1082401,2164802,4329604,8659208,32505856,33553439] .lf)))))) [8,31,1082401,2164802,4329604,8659944,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,1082401,2164802,4329604,17318416,32505856,32506848] .lf) [8,31,1082401,2164802,4329604,17318416,32505856,33553439] .lf) [8,31,1082401,2164802,4330468,8659208,17318416,32505856] (.nd (.nd .lf [8,31,1082401,2164802,4330468,8659208,32505856] .lf) [8,31,1082401,2164802,8659208,8659944,17318416,32505856] .lf)) [8,31,1082401,2164802,8659208,17318416,32505856,32506848] (.nd (.nd (.nd .lf [8,31,1082401,2164802,8659208,17318416,32505856,33553439] .lf) [8,31,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,1082401,4329604,4330468,8659208,17318416,32505856] .lf))) [8,31,1082401,4329604,8659208,8659944,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,1082401,4329604,8659208,17318416,32505856,32506848] .lf) [8,31,1082401,4329604,8659208,17318416,32505856,33553439] .lf) [8,31,1082401,4329604,8659944,17318416,32505856] (.nd .lf [8,31,1083361,2164802,4329604,8659208,17318416,32505856] .lf)) [8,31,1083361,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,1083361,2164802,8659208,17318416,32505856] .lf) [8,31,2164802,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,2164802,4329604,4330468,8659208,17318416,32505856] (.nd .lf [8,31,2164802,4329604,8659208,8659944,17318416,32505856] .lf)))) [8,31,2164802,4329604,8659208,17318416,32505856,32506848] (.nd (.nd (.nd (.nd (.nd .lf [8,31,2164802,4329604,8659208,17318416,32505856,33553439] .lf) [8,31,2164802,4330468,8659208,17318416,32505856] .lf) [8,992,1023,1082401,2164802,4329604,8659208,32505856] (.nd (.nd .lf [8,992,1023,1082401,2164802,4329604,17318416,32505856] .lf) [8,992,1023,1082401,2164802,8659208,17318416,32505856] .lf)) [8,992,1023,1082401,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,992,1023,2164802,4329604,8659208,17318416,32505856] .lf) [8,992,31744,1015808,1082401,2164802,4329631,8659208,17318416,32505856] .lf) [8,992,31744,1015808,1082401,2164802,8659208,32641156] (.nd .lf [8,992,31744,1015808,1082401,2164802,17318416,32641156] .lf))) [8,992,31744,1015808,1082401,2164831,4329604,8659208] (.nd (.nd (.nd (.nd .lf [8,992,31744,1015808,1082401,2164831,4329604,17318416] .lf) [8,992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856] .lf) [8,992,31744,1015808,2164802,4329631,8659208,17318416] (.nd .lf [8,992,31744,1015808,4329604,8659208,17318416,32573506] .lf)) [8,992,1047552,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,992,1047552,1082401,2164802,4329604,17318416,32505856] .lf) [8,992,1047552,1082401,2164802,8659208,17318416,32505856] .lf) [8,992,1047552,1082401,4329604,8659208,17318416,32505856] (.nd .lf [8,992,1047552,2164802,4329604,8659208,17318416,32505856] .lf))))) [8,992,1082401,2164802,4329604,8659208,32505856,32505887] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,992,1082401,2164802,4329604,8659208,32505856,33554400] .lf) [8,992,1082401,2164802,4329604,17318416,32505856,32505887] .lf) [8,992,1082401,2164802,4329604,17318416,32505856,33554400] (.nd (.nd .lf [8,992,1082401,2164802,8659208,17318416,32505856,32505887] .lf) [8,992,1082401,2164802,8659208,17318416,32505856,33554400] .lf)) [8,992,1082401,4329604,8659208,17318416,32505856,32505887] (.nd (.nd (.nd .lf [8,992,1082401,4329604,8659208,17318416,32505856,33554400] .lf) [8,992,2164802,4329604,8659208,17318416,32505856,32505887] .lf) [8,992,2164802,4329604,8659208,17318416,32505856,33554400] (.nd .lf [8,31744,1015808,1082401,2164802,4329604,17318431,32505856] .lf))) [8,31744,1015808,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd (.nd .lf [8,31744,1015808,1082401,4329604,8659208,17318431,32505856] .lf) [8,31744,1015808,2164802,4329604,8659208,17318896,32505856] .lf) [9,31,992,31744,1015808,1082401,2164802,4329604,8659208] (.nd .lf [9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856] .lf)) [9,31,992,31744,1015808,1082401,2164802,4329604,17318416] (.nd (.nd (.nd .lf [9,31,992,31744,1015808,1082401,2164802,8659208,17318416] .lf) [9,31,992,31744,1015808,1082401,4329604,8659208,17318416] .lf) [9,31,992,31744,1015808,2164802,4329604,8659208,17318416] (.nd .lf [9,31,992,31744,1082401,2164802,4329604,8659208,32505856] .lf)))) [9,31,992,31744,1082401,2164802,4329604,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [9,31,992,31744,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,992,31744,1082401,4329604,8659208,17318416,32505856] .lf) [9,31,992,31744,2164802,4329604,8659208,17318416,32505856] (.nd .lf [9,31,992,1082401,2164802,4329604,8659208,17318416,32505856] .lf)) [9,31,992,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [9,31,992,1082401,2164802,4329604,17318416,32505856] .lf) [9,31,992,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,992,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,31,992,2164802,4329604,8659208,17318416,32505856] .lf))) [9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd .lf [9,31,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,31744,1015808,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf)) [9,992,31744,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [9,992,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [9,992,31744,1015808,1082401,2164802,8659208,17318416,32505856] .lf) [9,992,31744,1015808,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,992,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf))))))))))
def P_ := stepOK 33554431 Y_ PD_ PM_ G_ T_
def b0 : List (List Nat × List (Nat × Nat)) := [([3,5412005,6291999],hh "AAALACALAEBsAGBs"),([3,5412517,6291487],hh "AAALACALAEBsAGBs"),([4,31,2164802,32268568],hh "AAArACArAEArAGArAIAEAKAE"),([4,31,3213890,33317656],hh "AAArACArAEArAGArAIAEAKAE"),([4,31,4329604,7374369],hh "AABsACBsAEBsAGBsAICKAKCK"),([4,31,4330116,7373857],hh "AABsACBsAEBsAGBsAICKAKCK"),([4,31,5412005,6291968],hh "AACkACCkAECkAGCkAIBsAKBsBJBsBKBs"),([4,31,5412517,6291456],hh "AAE0ACE0AEE0AGE0AIBsAKBsBJBsBKBs")]
theorem k0 : b0.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b1 : List (List Nat × List (Nat × Nat)) := [([4,512,5412005,6291487],hh "AAALACALAEALAGALAIBsAKBsA5ALA6ALBJBsBKBs"),([4,543,4329604,7373857],hh "AABsACBsAEBsAGBsAICKAKCK"),([4,543,5412005,6291456],hh "AAE0ACE0AEE0AGE0AIBsAKBsBJBsBKBs"),([4,1049119,2164802,33317656],hh "AAArACArAEArAGArAIAEAKAE"),([4,1082401,4329604,6291999],hh "AAALACALAEALAGALAICKAKCKA5ALA6AL"),([4,1082401,4330116,6291487],hh "AAALACALAEALAGALAICKAKCKA5ALA6AL"),([4,1082431,2165730,4329604,9436424,33047056],[]),([4,1082913,4329604,6291487],hh "AAALACALAEALAGALAICKAKCKA5ALA6AL")]
theorem k1 : b1.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b2 : List (List Nat × List (Nat × Nat)) := [([5,31,512,4329604,7373857],hh "AABsACBsAEBsAGBsAIBsAKBsAMCKAOCKA5BsA6BsBRBsBSBsBpCKBqCK"),([5,31,512,5412005,6291456],hh "AAE0ACE0AEE0AGE0AIE0AKE0AMBsAOBsA5E0A6E0BRE0BSE0BhBsBiBsBpBsBqBs"),([5,31,992,10824010,23609872],hh "AABOACBOAEBOAGBOAIBOAKBOAMAEAOAEA5BOA6BOBRBOBqAEBtBJ"),([5,31,1049088,2164802,33317656],hh "AAArACArAEArAGArAIArAKArAMAEAOAEA5ArA6ArBRArBSArBqAEBtAr"),([5,31,1082401,2164802,33317144],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMAKAOAKA6AuBRA4BSA4BqAKBtAr"),([5,31,1082401,2165314,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMAKAOAKA6AuBRA4BSA4BqAKBtAr"),([5,31,1082401,2165730,4329604,9436424,33047056],[]),([5,31,1082401,4329604,6291968],hh "AACmACCmAECmAGCmAICmAKCmAMCKAOCKBRCmBSCmBhCKBiCKBpCKBqCK")]
theorem k2 : b2.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b3 : List (List Nat × List (Nat × Nat)) := [([5,31,1082401,4330116,6291456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMCKAOCKBRE5BSE5BhCKBiCKBpCKBqCK"),([5,31,1082913,2164802,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMAKAOAKA6AuBRA4BSA4BqAKBtAr"),([5,31,1082913,4329604,6291456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMCKAOCKBRE5BSE5BhCKBiCKBpCKBqCK"),([5,31,1556463,2164802,8659208],hh "AAArACArAEArAGArAIArAKArAMAEAOAEBpArBuAEBxB-ByB-"),([5,31,2164802,8659208,31997968],hh "AABJACBJAEBJAGBJAIBJAKBJAMArAOArBRBJBSBJBxAEByAE"),([5,31,3179553,4330116,32505856],hh "AACKACCKAECKAGCKAIBsAKBsAMCKAOCKBRALBSALBhELBiCKBqCKBxBsB2CK"),([5,31,3180065,4329604,32505856],hh "AACKACCKAECKAGCKAIBsAKBsAMCKAOCKBRALBSALBhELBiCKBqCKBxBsB2CK"),([5,31,3180065,4329604,33047056],hh "AACKACCKAECKAGCKAIBsAKBsAMCKAOCKBRALBSALBiCKBqCKBxBYB2CK")]
theorem k3 : b3.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b4 : List (List Nat × List (Nat × Nat)) := [([5,31,3213890,8659208,33047056],hh "AABJACBJAEBJAGBJAIBJAKBJAMArAOArBRBJBSBJBxAEByAE"),([5,31,3247203,4330116,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMCTAOCTA6BsBRBsBSBsBtCKBxAL"),([5,31,3247203,4330468,32810281],hh "AABsACBsAEBsAGBsAIBsAKBsAMCaAOCaBSBsBxA4"),([5,31,3247203,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMBsAOBsA6E5BhEOBiBsBtBsBxAL"),([5,31,3247203,6494918,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMABAOABBhEOBiABBxEVB2AB"),([5,31,3247715,4329604,32540193],hh "AABsACBsAEBsAGBsAIBsAKBsAMCTAOCTA6BsBRBsBSBsBtCKBxAL"),([5,31,3247715,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMBsAOBsA6E5BhEOBiBsBtBsBxAL"),([5,31,3247715,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMABAOABBhEOBiABBxEVB2AB")]
theorem k4 : b4.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b5 : List (List Nat × List (Nat × Nat)) := [([5,31,3248099,4329604,33080881],hh "AABsACBsAEBsAGBsAIBsAKBsAMCLAOCLBRBsBtCKBxBe"),([5,31,3248099,5412005,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMBsAOBsA6CsBiBsBtBsBxBe"),([5,31,3248099,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMAEAOAEA6BQBtBJBxAL"),([5,31,4330116,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMCKAOCKBKBsBSBsByArB1Bs"),([5,31,5412005,6495206,33047056],hh "AACkACCkAECkAGCkAICkAKCkAMDTAODTBKCkBiDTB1BsB2Bt"),([5,31,5412517,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMF2AOF2BKE5BhEOBiF2B1BsB2B3"),([5,31,5412517,6494918,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMF2AOF2BKE5BhEOBiF2B1BsB2B3"),([5,31,8659208,21107332,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMCKAOCKA6BsBRBsBSBsBqCKBtBs")]
theorem k5 : b5.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b6 : List (List Nat × List (Nat × Nat)) := [([5,31,9742313,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMAIAOAIA6BQBqAIBtBJ"),([5,512,1082401,4329604,6291487],hh "AAALACALAEALAGALAIALAKALAMCKAOCKA5ALA6ALBJALBKALBRALBSALBhCKBiCK"),([5,543,1082401,2164802,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMAKAOAKA6AuBRA4BSA4BqAKBtAr"),([5,543,1082401,4329604,6291456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMCKAOCKBRE5BSE5BhCKBiCKBpCKBqCK"),([5,543,3179553,4329604,32505856],hh "AACKACCKAECKAGCKAIBsAKBsAMCKAOCKBRALBSALBhELBiCKBqCKBxBsB2CK"),([5,543,3247203,4329604,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMCTAOCTA6BsBRBsBSBsBtCKBxAL"),([5,543,3247203,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMBsAOBsA6E5BhEOBiBsBtBsBxAL"),([5,543,3247203,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMABAOABBhEOBiABBxEVB2AB")]
theorem k6 : b6.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b7 : List (List Nat × List (Nat × Nat)) := [([5,543,4329604,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMCKAOCKBKBsBRBsBSBsByArB1Bs"),([5,543,5412005,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AMF2AOF2BKE5BhEOBiF2B1BsB2B3"),([5,992,1082431,2164802,4329604,9436424,33047056],[]),([5,992,1082431,2164802,4329604,17825296,32776456],[]),([5,992,5412005,6291487,17318416],hh "AAAaACAaAEAaAGAaAIBsAKBsAMAaAOAaA5ASBJALBKBsBlALBmAaBpBOBqAaByBs"),([5,992,6291487,10824010,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMAEAOAEA5BOA6BOBJBOBiAEBlBJBxAaByAa"),([5,31744,1082431,2165730,4329604,9412872,33047056],[]),([5,1047552,1082431,2165730,4329604,8659208,33047056],[])]
theorem k7 : b7.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b8 : List (List Nat × List (Nat × Nat)) := [([5,1049119,2164802,8659208,33047056],hh "AABJACBJAEBJAGBJAIBJAKBJAMArAOArBRBJBSBJBxAEByAE"),([5,1082401,2097183,4330116,32505856],hh "AACKACCKAECKAGCKAIALAKALAMCKAOCKBJALBKALBiCKBqCKBxEpB2CK"),([5,1082401,2097695,4329604,32505856],hh "AACKACCKAECKAGCKAIALAKALAMCKAOCKBJALBKALBiCKBqCKBxEpB2CK"),([5,1082401,2097695,4329604,33047056],hh "AACKACCKAECKAGCKAIALAKALAMCKAOCKBJALBKALBiCKBqCKBxBYB2CK"),([5,1082401,2164802,32505887,32641668],hh "AACTACCTAECTAGCTAICTAKCTAMALAOALA5CTA6CTBVCLBqALBtCK"),([5,1082401,2164802,32506399,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMALAOALA5CTA6CTBVCLBqALBtCK"),([5,1082401,2164831,4330116,32505887],hh "AAAOACAOAEAOAGAOAIAOAKAOAMCSAOCSBJAOBKAOBRANBiCSBtCK"),([5,1082401,2164831,4330468,32776479],hh "AAAXACAXAEAXAGAXAIAXAKAXAMCXAOCXBJAUBKAXBiCX")]
theorem k8 : b8.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b9 : List (List Nat × List (Nat × Nat)) := [([5,1082401,2165343,4329604,32506399],hh "AAAOACAOAEAOAGAOAIAOAKAOAMCSAOCSBJAOBKAOBRANBiCSBtCK"),([5,1082401,2165730,4329631,9436424,17318416,32505856],[]),([5,1082401,2165759,4329604,33047071],hh "AAALACALAEALAGALAIALAKALAMCKAOCKBJALBKALBRALBtCK"),([5,1082401,3144770,4329631,8659944,17318416,32505856],[]),([5,1082431,2165730,4329604,9436424,17318416,32505856],[]),([5,1082431,3144770,4329604,8659944,17318416,32505856],[]),([5,1082913,2097183,4329604,32505856],hh "AACKACCKAECKAGCKAIALAKALAMCKAOCKBJALBKALBiCKBqCKBxEpB2CK"),([5,1082913,2164802,32505887,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMALAOALA5CTA6CTBVCLBqALBtCK")]
theorem k9 : b9.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b10 : List (List Nat × List (Nat × Nat)) := [([5,1082913,2164831,4329604,32505887],hh "AAAOACAOAEAOAGAOAIAOAKAOAMCSAOCSBJAOBKAOBRANBiCSBtCK"),([5,4329604,8659208,16777759,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMALAOALA5BsA6BsBRBsBqALBtBs"),([6,31,512,1082401,2164802,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQAKASAKA5A4A6A4BKAuBRA4BSA4BpA4BqA4BxA4ByA4CKAKCNA4CSAKCVAr"),([6,31,512,1082401,4329604,6291456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CBCKCCCKCJCKCKCKCRCKCSCK"),([6,31,512,3179553,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKA5CKA6CKBRCKBSCKBpBsBqBsBxALByALCBELCCCKCJCKCKCKCSCKCZBsCeCK"),([6,31,512,3247203,4329604,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCTASCTA5BsA6BsBKBsBRBsBSBsBpBsBqBsBxBsByBsCJCTCKCTCVCKCZAL"),([6,31,512,3247203,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQBsASBsA5E5A6E5BKE5BRE5BSE5BpE5BqE5CBEOCCBsCJBsCKBsCVBsCZAL"),([6,31,512,3247203,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQABASABA5E5A6E5BRE5BSE5BpE5BqE5CBEOCCABCJABCKABCZEVCeAB")]
theorem k10 : b10.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b11 : List (List Nat × List (Nat × Nat)) := [([6,31,512,4329604,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCKASCKA5BsA6BsBRBsBSBsBiBsBqBsBtBsBxBsByBsCJCKCKCKCaArCdBs"),([6,31,512,5412005,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQF2ASF2A5E5A6E5BRE5BSE5BiE5BpE5BqE5CBEOCCF2CJF2CKF2CdBsCeB3"),([6,31,992,1082401,2164802,4329604,9436424,33047056],[]),([6,31,992,1082401,2164802,4329604,17825296,32776456],[]),([6,31,992,1082401,3144770,8659208,17318416,32641156],[]),([6,31,992,1555951,2164802,8659208],hh "AAArACArAEArAGArAIArAKArAMArAOArAQAEASAEA5ArA6ArBRArBSArBpArCJAECRArCWAECZDnCaDn"),([6,31,992,1826551,2164802,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQAEASAEA5BOA6BOBVBOBpBOCKAECNBJCRBOCWAECZC5CaF5"),([6,31,992,2164802,8659208,23609872],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCZAECaAE")]
theorem k11 : b11.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b12 : List (List Nat × List (Nat × Nat)) := [([6,31,992,2164802,8659208,31998480],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCZAECaAE"),([6,31,992,2164802,14950664,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBRBOBpBOCKArCNBJCRArCSArCZAECaAE"),([6,31,992,2164802,17318416,31727880],hh "AAArACArAEArAGArAIArAKArAMArAOArAQBOASBOA5ArA6ArBRArBqArBtArBxArByArCJEyCZAECaAE"),([6,31,992,3179553,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCKASCKA5CsA6CsBRCsBpCmBxCsByCsCCCKCNCKCSCKCZBe"),([6,31,992,3213378,8659208,33047056],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCZAECaAE"),([6,31,992,3213378,17318416,32776456],hh "AAArACArAEArAGArAIArAKArAMArAOArAQBOASBOA5ArA6ArBRArBqArBtArBxArByArCJETCZAECaAE"),([6,31,992,3247203,4329604,32810281],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQD8ASD8A5BsA6BsBRBsBpBsBqBsBxBsByBsCJBxCZA4"),([6,31,992,3247203,4329604,33080881],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCTASCTA5BsA6BsBRBsBSBsBpBsBxBsByBsCNDiCVCsCZBe")]
theorem k12 : b12.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b13 : List (List Nat × List (Nat × Nat)) := [([6,31,992,3247203,5412005,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQBsASBsA5FQA6FQBKFQBRE6BpFPCCBsCJE5CZA4"),([6,31,992,3247203,5412005,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQBsASBsA5DCA6DCBKDCBRDCBSCsBpC_CCBsCNE5CVCoCZBe"),([6,31,992,3247203,6494406,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQADASADA5FQA6FQBRE6BpE5CCABCJE5CZA4"),([6,31,992,3247203,6494406,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQABASABA5DCA6DCBRDCBpC_CCABCNE5CZBe"),([6,31,992,3247203,8659208,33080881],hh "AABTACBTAEBTAGBTAIBTAKBTAMBTAOBTAQA4ASA4A5BTA6BTBRBTBpBTBxBTByBTCNBTCZAHCaAH"),([6,31,992,3247203,9741609,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAyASAyA5BeA6BeBRBeBpBeCKAyCNBYCZAGCaAG"),([6,31,992,3247203,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAEASAEA5BeA6BeBKBQBRBeBSBeBpBeCKAECNBYCVBOCZAa"),([6,31,992,3247203,17318416,32810281],hh "AAAyACAyAEAyAGAyAIAyAKAyAMAyAOAyAQBeASBeA5AyA6AyBRAyBqAyBtAyBxAyByAyCJBwCZAGCaAG")]
theorem k13 : b13.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b14 : List (List Nat × List (Nat × Nat)) := [([6,31,992,3247203,18400817,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBTASBTA5A4A6A4BRA4BtA4CJE3CZAHCaAH"),([6,31,992,3247203,19483218,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQAEASAEA5A4A6A4BKAuBRA4BtA4CJE3CZEb"),([6,31,992,4329604,7373857,17318416],hh "AABsACBsAEBsAGBsAIBsAKBsAMCKAOCKAQBsASBsA5BsA6BsBRBsBpBxCCBsCNBsCOBsCRBeCSBsCZBOCaDn"),([6,31,992,4329604,9403358,17318416],hh "AACqACCqAECqAGCqAICqAKCqAMCqAOCqAQAEASAEA5CqA6CqBRCqBtClCCAECNAECRBeCSAECZCK"),([6,31,992,4329604,17318416,24151073],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCqASCqA5BsA6BsBRBsBiBsBtBsBxBsByBsCJBxCaBO"),([6,31,992,4329604,25707024,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCpASCpA5BsA6BsBRBsBiBsBtBsBxBsByBsCJBxCaBO"),([6,31,992,4329604,25977624,32810281],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQArASArA5BsA6BsBRBsBtBsBxBsByBsCJBx"),([6,31,992,4329604,25977624,33080881],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBOASBOA5BsA6BsBRBsBqBsBtBsBxBsByBsCNDiCdBs")]
theorem k14 : b14.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b15 : List (List Nat × List (Nat × Nat)) := [([6,31,992,5412005,6291456,17318416],hh "AAFSACFSAEFSAGFSAIFSAKFSAMBsAOBsAQFSASFSA5FSA6FSBRFLBhBsBiBsBpE0BqBsCCFSCNE0COFSCRBOCSFSCZBsCaBs"),([6,31,992,5412005,6494406,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFcASFcA5FQA6FQBRFPBiFQBpE5CCFcCJE5"),([6,31,992,5412005,6494406,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQFhASFhA5DCA6DCBRC_BiDCBpC_BqCsCCFhCNE5CdBs"),([6,31,992,6291456,10824010,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQAEASAEA5BOA6BOBJBOBKBOBRBOBSBOBpBOCKAECNBJCRAECSAECZFSCaFS"),([6,31,992,8659208,21648020,33080881],hh "AABTACBTAEBTAGBTAIBTAKBTAMBTAOBTAQBFASBFA5BTA6BTBKBTBRBTBSBTBtBTBxBTByBTCNBTCSBFCVBT"),([6,31,992,9741609,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAJASAJA5BeA6BeBKBQBRBeBSBeBpBeCKAJCNBYCSAJCVBO"),([6,31,992,12718212,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCqASCqA5BsA6BsBRBsBiBsBtBsBxBsByBsCJBxCaBO"),([6,31,992,12988812,17318416,32810281],hh "AAAyACAyAEAyAGAyAIAyAKAyAMAyAOAyAQCqASCqA5AyA6AyBRAyBiAyBtAyBxAyByAyCJBwCaBO")]
theorem k15 : b15.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b16 : List (List Nat × List (Nat × Nat)) := [([6,31,992,12988812,21648020,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCTASCTA5BsA6BsBRBsBSBsBtBsCJBx"),([6,31,992,12988812,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQA4ASA4A5BsA6BsBRBsBtBsCJBxCaBO"),([6,31,992,18400817,19483218,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQAKASAKA5A4A6A4BKAuBVA4BtA4CJE3CSAK"),([6,31,992,21648020,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBcASBcA5BsA6BsBVBsBqBsBtBsCJBxCaAr"),([6,31,31744,1082401,2165730,4329604,9412872,33047056],[]),([6,31,507375,1082401,2165730,4329604],hh "AACLACCLAECLAGCLAICLAKCLAMCLAOCLAQBuASBuA6CLBRCLBiCKBqCKByCLCOBuCREACSEACZCK"),([6,31,507375,1083361,2164802,8659208],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQAIASAIBKArBRA2BSArBxA2CJA2COAICRArCZD8CaD8"),([6,31,507887,1082401,2164802,8659208],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQAKASAKBKAuBRA4BSArBxA4ByA4CJA4COAKCRArCSAKCZCaCaCa")]
theorem k16 : b16.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b17 : List (List Nat × List (Nat × Nat)) := [([6,31,777975,1082401,2164802,4330468],hh "AACaACCaAECaAGCaAICaAKCaAMCaAOCaAQFbASFbA6CYBRCaBiCXBxCaByCaCOFDCRFaCSFbCaAK"),([6,31,1047552,1082401,2165730,4329604,8659208,33047056],[]),([6,31,1047552,1082401,2165730,8659208,17318416,32641156],[]),([6,31,1048575,1082401,2164802,4330116],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4A6CTA9CTBRCTBiCSBqCKBxCTByCTCOB4CRCfCSCfCZCKCaAK"),([6,31,1048575,1082913,2164802,4329604],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4A6CTA9CTBRCTBiCSBqCKBxCTByCTCOB4CRCfCSCfCZCKCaAK"),([6,31,1049088,2164802,8659208,33047056],hh "AABJACBJAEBJAGBJAIBJAKBJAMBJAOBJAQArASArA5BJA6BJBRBJBSBJBpBJBqBJBxBJByBJCKArCNBJCZAECaAE"),([6,31,1049568,2164802,8659208,33047056],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCZAECaAE"),([6,31,1082401,2097152,4330116,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKBJCKBKCKBRCKBSCKBpALBqALBxBsByBsCBELCCCKCKCKCSCKCVCKCZBsCeCK")]
theorem k17 : b17.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b18 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2097664,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKBJCKBKCKBRCKBSCKBpALBqALBxBsByBsCBELCCCKCKCKCSCKCZBsCeCK"),([6,31,1082401,2097664,4329604,33047056],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKBJCKBKCKBRCKBSCKBpALBqALBxBsByBsCCCKCKCKCSCKCVCKCZBYCeCK"),([6,31,1082401,2098144,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCKASCKBJCsBKCsBSCsBpCsBqCsBxCmCCCKCKCKCVCKCZBe"),([6,31,1082401,2164802,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082401,2164802,4330116,32505887],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBJAOBKE5BRE5BSE5BhE2BpE5BqE5BxE5ByE5CCCTCFE5CKCTCVCL"),([6,31,1082401,2164802,4330116,32539681],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6EuBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCNE5CVCKCZAL"),([6,31,1082401,2164802,4330116,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCaASCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCYCKCaCVCKCZA4"),([6,31,1082401,2164802,4330148,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE0BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZDj")]
theorem k18 : b18.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b19 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,4330180,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCTASCTBKFPBRFPBSFPBpFPBqFPByE5CBEOCCCTCKCTCZE5"),([6,31,1082401,2164802,4330212,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCTASCTBKFPBRFPBSFPBpFLBqFPByE5CBEOCCCTCKCTCZE5"),([6,31,1082401,2164802,4330468,32506112],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCWASCWBKFOBRFOBSFOBpFKBqFOByE3CBEOCCCWCKCWCZE3"),([6,31,1082401,2164802,4330468,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCaASCaBKFOBRFOBSFOBpFKBqFOByE3CCCYCKCaCZA4"),([6,31,1082401,2164802,4330468,32776479],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCYASCYBJAXBKFOBRFOBSFOBhFNBpFKBqFOByE3CCCYCFFOCKCY"),([6,31,1082401,2164802,4330468,32810281],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCaASCaBKFOBRFOBSFOBqFOByE3CCCYCKCaCNFOCZA4"),([6,31,1082401,2164802,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6E5BKE5BRE5BSE5BqE5BtE5BxE5ByE5CBEOCCCTCKCTCNE0CVCKCZAL"),([6,31,1082401,2164802,5412837,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCaASCaA6FOBKFOBRFOBSFOBqFOBtFOByE3CCCYCKCaCNFKCZA4")]
theorem k19 : b19.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b20 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,6494918,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BpE5BqE5ByE5B1E5CBEOCCCTCKCTCZE5CeCT"),([6,31,1082401,2164802,6495206,32776456],hh "AAE3ACE3AEE3AGE3AIE3AKE3AME3AOE3AQCaASCaBRE3BSE3BpEyBqE3ByE3B1E3CCCYCKCaCZA4CeCW"),([6,31,1082401,2164802,8659208,33046544],hh "AABYACBYAEBYAGBYAIBYAKBYAMBYAOBYAQA4ASA4A6BMBRBYBSBYBpBYBqBYBxBYByBYCKA4CNBJCZAKCaAK"),([6,31,1082401,2164802,12989420,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQCaASCaBKA4BRA4BSA4BpA2BqA4ByA4CKCaCZA4"),([6,31,1082401,2164802,16236527,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQCaASCaA6AuBRA4BSA4BqA4BtA4ByA4B1A4CKCaCNArCZA4CeCa"),([6,31,1082401,2164802,17317904,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBYASBYA6AuBRA4BSA4BpA4BqA4BxA4ByA4CKBYCNArCZAKCaAK"),([6,31,1082401,2164802,21107332,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082401,2164802,25977112,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4A6E5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCA4CKA4CNE0CZAKCaAK")]
theorem k20 : b20.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b21 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,29223963,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQBYASBYBKFOBRFOBSFOBqFOBtFKByE3CCA6CKBYCZFD"),([6,31,1082401,2164802,29224219,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQA4ASA4BKFPBRFPBSFPBqFPBtFLByE5CBEOCCA4CKA4CZFu"),([6,31,1082401,2164802,29224315,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4BKE5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCA4CKA4CVAKCZB4"),([6,31,1082401,2164802,32505856,32641668],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4BKCSBRCTBSCTBhCTBiCTBqCTByCTB1CKCKALCSE5CVCKCaB4CdCT"),([6,31,1082401,2164802,32506368,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQC_ASC_BKCSBRCTBSCTBhCTBiCTBqCTByCTB1CKCKC_CSC_CVCK"),([6,31,1082401,2164802,32642020,32776456],hh "AAE3ACE3AEE3AGE3AIE3AKE3AME3AOE3AQCaASCaBKE3BRE3BSE3BqE3ByE3B1E3CCCYCKCaCZA4CeCW"),([6,31,1082401,2164802,32776456,32912364],hh "AACaACCaAECaAGCaAICaAKCaAMCaAOCaAQA4ASA4BKCXBRCaBSCaBqCaCKA4CSA4CVCVCaA4CdCa"),([6,31,1082401,2164831,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCSASCSA5E5BKE5BNE5BSE5BhE5BpE5BqE5BxE5CBCSCCCSCKCSCVCKCZB2")]
theorem k21 : b21.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b22 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164831,4330468,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCXASCXA5FOBKFOBNFOBSFOBhFOBpFKBqFOCBCXCCCXCKCXCZA4"),([6,31,1082401,2165058,4330468,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCWASCWBKFPBRFPBSFPBpFLBqFPByE5CBEOCCCWCKCWCZE5"),([6,31,1082401,2165314,4329604,32506368],hh "AACmACCmAECmAGCmAICmAKCmAMCmAOCmAQCTASCTBKCmBRCmBSCmBpCmBqCmBxCmByCmCBEOCCCTCKCTCVCKCZB4"),([6,31,1082401,2165314,4329604,33047056],hh "AACmACCmAECmAGCmAICmAKCmAMCmAOCmAQCTASCTBKCmBRCmBSCmBpCmBqCmBxCmByCmCCCTCKCTCVCKCZBY"),([6,31,1082401,2165314,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082401,2165314,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BpE5BqE5CBEOCCCTCKCTCZE5CeCT"),([6,31,1082401,2165314,8659208,33047056],hh "AABYACBYAEBYAGBYAIBYAKBYAMBYAOBYAQA4ASA4A6BMBRBYBSBYBpBYBqBYBxBYByBYCKA4CNBJCZAKCaAK"),([6,31,1082401,2165314,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBYASBYA6AuBRA4BSA4BpA4BqA4CKBYCNArCZAKCaAK")]
theorem k22 : b22.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b23 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2165314,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4A6E5BRE5BSE5BpE5BqE5CBEOCCA4CKA4CNE0CZAKCaAK"),([6,31,1082401,2165730,4329604,9436424,17318416,32505856],[]),([6,31,1082401,2165730,4329604,32506368],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBKCsBSCsBpCsBqCsBxCmCBEOCCCLCKCLCVCKCZBu"),([6,31,1082401,2165730,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBKCsBSCsBpCsBqCsBxCmCCCLCKCLCVCKCZBe"),([6,31,1082401,2165730,4329604,33047071],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBJARBKCsBSCsBhCrBpCsBqCsBxCmCCCLCFCsCKCLCVCL"),([6,31,1082401,2165730,4329604,33080881],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBKCsBRByBSCsBpCsBqCsBxCmCCCLCKCLCNCsCVCKCZBe"),([6,31,1082401,2165730,4330116,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQCLASCLBKFBBSFBBpFBBqFBBxE5CBEOCCCLCKCLCVCKCZBu"),([6,31,1082401,2165730,5412005,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLA6CsBKCsBRCsBSCsBqCsBtCsBxCmCCCLCKCLCNCoCVCKCZBe")]
theorem k23 : b23.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b24 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2165730,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA3ASA3A6BQBKBeBRBeBSBeBpBeBqBeCKA3CNBOCVBYCZAQ"),([6,31,1082401,2165730,21648020,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQCLASCLBKBeBSBeBpBeBqBeCKCLCVBYCZBe"),([6,31,1082401,2165730,29224827,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQA3ASA3BKCsBSCsBqCsBtCsB1CmCCA3CKA3CVAKCZBu"),([6,31,1082401,2165730,32641156,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBKCsBSCsBqCsCCCLCKCLCVCKCZBe"),([6,31,1082401,2165730,33047056,33182356],hh "AACLACCLAECLAGCLAICLAKCLAMCLAOCLAQBeASBeBKCKBSCLBqCLByCLB1CKCKBeCVDuCaBeCdCL"),([6,31,1082401,2165759,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCKASCKBKCsBNCsBSCsBpCsBqCsBxCmCBCKCCCKCKCKCVCKCZBe"),([6,31,1082401,2194498,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BpE5BqE5BxE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082401,3144770,4329604,8659944,17318416,32505856],[])]
theorem k24 : b24.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b25 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,3247203,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCKCTCVCKCZBs"),([6,31,1082401,3247203,4330468,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCaASCaBKFOBSFOBVFOBqFOByE3CCCYCJCaCKCaCZA4"),([6,31,1082401,3248099,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBKCsBSCsBVCsBpCsBqCsBxCmCCCLCJCLCKCLCVCKCZBe"),([6,31,1082401,4329604,6495206,33047056],hh "AACmACCmAECmAGCmAICmAKCmAMCmAOCmAQCKASCKBRCmBSCmBiCmBqCmByCmB1CmCCCKCKCKCdCKCeCK"),([6,31,1082401,4329604,31388701,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCLASCLBRCsBSCsBiCsBqCsByCmCCCLCKCLCRBeCdCK"),([6,31,1082401,4330116,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5ByE5CBEOCCCKCKCKCdCKCeCK"),([6,31,1082401,4330116,6494918,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5ByE5B1E5CBEOCCCKCKCKCdCKCeCK"),([6,31,1082401,4330116,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5ByE5CBEOCCCKCJCKCKCKCaDZCdE5")]
theorem k25 : b25.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b26 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,4330116,31389629,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BiE5BqE5BtE5ByE5B1E5CBEOCCCTCKCTCRB4CdCK"),([6,31,1082401,4330468,31389629,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCPASCPBRFKBSFOBiFOBqFOBtFOB1E3CCCPCKCPCRA4"),([6,31,1082401,6495206,10824010,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQAKASAKBRE0BSE5BpE5BqE5B2E5CBEOCCAKCKAKCWAK"),([6,31,1082401,6495206,21648020,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBSE5BpE5BqE5B2E5CBEOCCCKCKCKCWCK"),([6,31,1082401,8659208,21107332,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCKCJCKCKCKCSCKCVE5"),([6,31,1082401,8659944,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAKASAKA6BQBKBeBRBeBSBeBpBeBqBeCKAKCNBOCSAKCVBY"),([6,31,1082401,8659944,21648020,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQCKASCKBKBeBSBeBpBeBqBeCJCKCKCKCSCKCVBY"),([6,31,1082401,10824010,12989420,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCaASCaBRFPBSFPBpFLBqFPCBEOCCCaCKCa")]
theorem k26 : b26.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b27 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,12989420,21648020,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCLASCLBSFPBpFPBqFPCBEOCCCLCJCLCKCL"),([6,31,1082913,2097152,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKBJCKBKCKBRCKBSCKBpALBqALBxBsByBsCBELCCCKCKCKCSCKCVCKCZBsCeCK"),([6,31,1082913,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082913,2164802,4329604,32505887],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBJAOBKE5BRE5BSE5BhE2BpE5BqE5BxE5ByE5CCCTCFE5CKCTCVCL"),([6,31,1082913,2164802,4329604,32506368],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBCgCCCTCKCTCVCKCZB4"),([6,31,1082913,2164802,4329604,32539681],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6EuBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCVCKCZAL"),([6,31,1082913,2164802,4329604,32540193],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6EuBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCNE5CVCKCZAL"),([6,31,1082913,2164802,4329604,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCaASCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCYCKCaCVCKCZA4")]
theorem k27 : b27.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b28 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,2164802,4329604,33047056],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCVCKCZBY"),([6,31,1082913,2164802,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082913,2164802,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6E5BKE5BRE5BSE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZAL"),([6,31,1082913,2164802,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6E5BKE5BRE5BSE5BqE5BtE5BxE5ByE5CBEOCCCTCKCTCNE0CVCKCZAL"),([6,31,1082913,2164802,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BpE5BqE5ByE5B1E5CBEOCCCTCKCTCZE5CeCT"),([6,31,1082913,2164802,8659208,33047056],hh "AABYACBYAEBYAGBYAIBYAKBYAMBYAOBYAQA4ASA4A6BMBRBYBSBYBpBYBqBYBxBYByBYCKA4CNBJCZAKCaAK"),([6,31,1082913,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBYASBYA6AuBRA4BSA4BqA4BxA4ByA4CKBYCZAKCaAK"),([6,31,1082913,2164802,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4A6E5BRE5BSE5BqE5BxE5ByE5CBEOCCA4CKA4CZAKCaAK")]
theorem k28 : b28.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b29 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,2164802,29224827,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4BKE5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCA4CKA4CVAKCZB4"),([6,31,1082913,2164802,32505856,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4BKCSBRCTBSCTBhCTBiCTBqCTByCTB1CKCKALCSE5CVCKCaB4CdCT"),([6,31,1082913,2164831,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCSASCSA5E5BKE5BNE5BSE5BhE5BpE5BqE5BxE5CBCSCCCSCKCSCVCKCZB2"),([6,31,1082913,2165314,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082913,2165730,4329604,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQCLASCLBKFBBSFBBpFBBqFBBxE5CBEOCCCLCKCLCVCKCZBu"),([6,31,1082913,2194498,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BpE5BqE5BxE5CBEOCCCTCKCTCVCKCZB4"),([6,31,1082913,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCKCTCVCKCZBs"),([6,31,1082913,3247715,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCKCTCVCKCZBs")]
theorem k29 : b29.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b30 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,4329604,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5ByE5B1E5CBEOCCCKCKCKCdCKCeCK"),([6,31,1082913,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BqE5BxE5ByE5CBEOCCCKCJCKCKCKCaCKCdE5"),([6,31,1082913,4329604,31389629,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BiE5BqE5BtE5ByE5B1E5CBEOCCCTCKCTCRB4CdCK"),([6,31,1082977,2164802,4329604,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCTASCTBKFPBRE5BpFPBqFPBxFPByFPCBEOCCCTCKCTCZFt"),([6,31,1083041,2164802,4329604,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQDwASDwBKFBBRFBBSFBBpE5BqFBBxFBByFBCBEOCCDwCKDwCVDuCZB4"),([6,31,1083105,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQDwASDwBKFYBRFBBpFPBqFYBxFYByFYCBEOCCDwCKDwCZFt"),([6,31,1083361,2164802,4329604,33080881],hh "AAB7ACB7AEB7AGB7AIB7AKB7AMB7AOB7AQCTASCTBKB7BRB7BSByBpB6BxB7ByB7CCCTCNE5CVByCZBe"),([6,31,1083361,2164802,4330468,32776456],hh "AAFKACFKAEFKAGFKAIFKAKFKAMFKAOFKAQD8ASD8BKFKBRFKBpFKByFKCCD6")]
theorem k30 : b30.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b31 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,5412005,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQD8ASD8A6FQBKFQBRE6BxFQByFQCCD6"),([6,31,1083361,2164802,5412005,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQB5ASB5A6DCBKDCBRDCBSCsBxDCByDCCCB5CNE0CVCsCZBe"),([6,31,1083361,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2A6BQBRBeBpBeBxBeByBeCKA2CNBJCZAICaAI"),([6,31,1083361,2164802,8659208,33047536],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2A6BQBpBeBxBeByBeCKA2CNBOCaAI"),([6,31,1083361,2164802,8659208,33080881],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA4ASA4BRBeBpBeBxBeByBeCKA2CNBYCZAKCaAK"),([6,31,1083361,2164802,8659208,33081329],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2BpBeBxBeByBeCKA2CNBeCaAI"),([6,31,1083361,2164802,8659208,33317656],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAIASAIA6BQBRBeBiA9BpBeBuA8BxBeByBeCKAICNBJCaAICdBe"),([6,31,1083361,2164802,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2A6BQBKBeBRBeBSBeBpBeByBeB1BeCKA2CNBJCVBeCZAS")]
theorem k31 : b31.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b32 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,12988812,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQD8ASD8BKA4BRA4BpA4BxA4ByA4"),([6,31,1083361,2164802,17318896,32776456],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQBeASBeA6ArBRA2ByA2"),([6,31,1083361,2164802,18400817,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBeASBeBRA4BtA4BxA4ByA4CaAK"),([6,31,1083361,2164802,24895223,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQB5ASB5A6BQBRBeBtBeByBeB1BeCKB5CNBJCZBeCeB5"),([6,31,1083361,2164802,25977624,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQBeASBeA6FQBRE6BxFQByFQCCA9"),([6,31,1083361,2164802,25977624,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQA2ASA2A6DCBRDCBxDCByDCCCA2CNE0CZAI"),([6,31,1083361,2164802,32641156,32776456],hh "AAD8ACD8AED8AGD8AID8AKD8AMFtAOFtAQD8ASD8BKD5BRD8ByFKCCD6CSD8"),([6,31,1083361,2164802,32776456,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2A6BQBRBeByBeCNBJCSA2CZAI")]
theorem k32 : b32.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b33 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,33047056,33317656],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQAIASAIA6ArBRA2BiA2BtArBuA2ByA2CNAsCSASCaAICdA2"),([6,31,1083361,2165058,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQD2ASD2BKFYBRFBBpFPBqFYBxFYByFYCBEOCCD2CKD2CZFt"),([6,31,1083361,6494406,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQAJASAJBRE5BSFYBpFBCBEOCCAJCKAJCWAJ"),([6,31,1083361,6494406,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQCKASCKBRE5BpFPCBEOCCCKCKCKCWCK"),([6,31,1083361,8659208,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQAIASAIA6BQBKBeBRBeBSBeBpBeByBeB1BeCKAICNBJCSAICVBe"),([6,31,1083361,8659208,31389629,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBtASBtA6BQBRBeBtBeByBeB1BeCKBtCNBJCRBtCSBt"),([6,31,1083361,10824010,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQD8ASD8BRFBBpFPBqFYCBEOCCD8CKD8"),([6,31,1083361,10824010,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQBeASBeA6FYBRFBBqFYCBEOCCBeCKBe")]
theorem k33 : b33.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b34 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,10824010,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQBeASBeA6FYBRFBBqFYCBEOCCBeCKBeCaAI"),([6,31,1083361,19483218,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQA2ASA2A6FYCBEOCCA2CKA2CaAI"),([6,31,1083391,2164802,8659208,33047056],hh "AABQACBQAEBQAGBQAIBQAKBQAMBQAOBQAQArASArA6BQA9BQBRBQBpBQBxBQByBQCBArCNEzCZAECaAE"),([6,31,2164802,3247203,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCZB4"),([6,31,2164802,3247203,4330468,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQCaASCaBSFOBVFOBqE3BxFKByE3CCCYCJCaCZA4"),([6,31,2164802,3247715,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCZB4"),([6,31,2164802,3248099,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2BKBQBSBeBVBeBpBeBqBeBxBeCJA2CVBJCZAECaAE"),([6,31,2164802,4329604,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQB4ASB4A6E5BKE5BRE5BSE5BpE5BqE5ByE5B1E5CBEOCCB4CNBsCVB4")]
theorem k34 : b34.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b35 : List (List Nat × List (Nat × Nat)) := [([6,31,2164802,4329604,25977112,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCArCJArCVArCaAE"),([6,31,2164802,4329604,32471326,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQArASArA6FYBRFYBSFYBqFBByFPB1FYCBEOCCArCRArCeAr"),([6,31,2164802,4329604,32471518,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArA6E5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCArCNAECRArCeAr"),([6,31,2164802,4330116,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQB4ASB4A6E5BKE5BRE5BSE5BpE5BqE5ByE5CBEOCCB4CNBs"),([6,31,2164802,4330116,5412517,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQB4ASB4A6E5BKE5BRE5BSE5BpE5BqE5ByE5B1E5CBEOCCB4CNBsCVB4"),([6,31,2164802,4330116,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArBKE5BRE5BSE5BpE5BqE5ByE5CBEOCCArCJArCaDW"),([6,31,2164802,4330116,32472030,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArA6E5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCArCNAECRArCeAr"),([6,31,2164802,4330468,5412005,32776456],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQDnASDnA6FLBKFLBSE0BpFLBqFLByFKCCDm")]
theorem k35 : b35.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b36 : List (List Nat × List (Nat × Nat)) := [([6,31,2164802,4330468,5412005,33047056],hh "AAC9ACC9AEC9AGC9AIC9AKC9AMC9AOC9AQB4ASB4A6C9BKC9BRCkBSC9BpC9BqC9CCB4CNCkCVB4"),([6,31,2164802,4330468,5412837,32776456],hh "AAFKACFKAEFKAGFKAIFKAKFKAMFKAOFKAQDnASDnA6FKBKFKBSFKBqFKByFKB1FKCCDmCVB-"),([6,31,2164802,4330468,25977624,32776456],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQBOASBOBKFLBSE0BpFLBqFLByFKCCAwCJBO"),([6,31,2164802,4330468,25977624,33047056],hh "AAC9ACC9AEC9AGC9AIC9AKC9AMC9AOC9AQArASArBKC9BSC9BpC9BqC9CCArCJArCVAr"),([6,31,2164802,4330468,32472030,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQBOASBOA6FOBSE3BqFOBtFOByFKB1FOCCAwCRA4CeBO"),([6,31,2164802,8659208,9742313,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQArASArBRBeBSBeBiBQBqBeByBeB1BeCSAICaB-CdBJ"),([6,31,2164802,8659208,32471070,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA2ASA2BRBeBSBeBiBQBqBeByBeCRAICSAICdArCeA2"),([6,31,2164802,12989420,17318416,32776456],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQBOASBOBKArBSA2BpA2BqA2ByA2CJBOCaDE")]
theorem k36 : b36.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b37 : List (List Nat × List (Nat × Nat)) := [([6,31,2165314,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBpE5BqE5BxE5ByE5CBEOCCCTCJEWCZB4"),([6,31,2165314,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArBKE5BRE5BSE5BxE5ByE5CBEOCCArCJEWCVArCaAE"),([6,31,2165730,4329604,5412005,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQBuASBuA6CsBKCsBRCmBSCsBpCmByCsB1CsCCBuCNBsCVBu"),([6,31,2165730,4329604,32472030,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQAqASAqA6CsBRCmBtCsByCsB1CsCCAqCNAECRBeCeAq"),([6,31,2165730,5412005,18400817,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQCLASCLA6FBBRE5BiFBCBEOCCCLCaCL"),([6,31,2165730,5412005,21648020,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQCwASCwA6FBBRE5BiFBCBEOCCCw"),([6,31,2165730,18400817,21648020,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQBIASBIA6FBCBEOCCBICSBI"),([6,31,3247203,4330468,8659208,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCaASCaA6BsBSBsBiBsBpBsBqBsBxBsB2BsCRBxCZCaCaCa")]
theorem k37 : b37.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b38 : List (List Nat × List (Nat × Nat)) := [([6,31,3247203,4330468,9741609,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQBsASBsBSE5BxFPCBEOCCBsCRE5CZCaCaCa"),([6,31,3247203,4330468,10824010,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQAEASAEBRFLBSE5BxE5CBEOCCAECRE5CZCa"),([6,31,3248099,4329604,10824010,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQAEASAEBRE5BSFBBuFBBxFBByFBCBEOCCAECRAECZD8"),([6,31,3248099,4329604,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCLASCLA6BsBRBsBiBsBuBsBxBsByBsCRALCZCLCaCL"),([6,31,3248099,4329604,18400817,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQBsASBsBRE5BuFBBxFBByFBCBEOCCBsCRBsCZCLCaCL"),([6,31,3248099,5412005,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQBsASBsA6FBBiFBBuFBBxFBByFBCBEOCCBsCRALCZBsCaBs"),([6,31,3248099,10824010,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQBeASBeA6FBBqFBBxFBByFBCBEOCCBeCRBeCZAECaAE"),([6,31,4329604,8659208,16777728,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQClASClBKBsBRBsBSBsBhBsBiBsBpBsBqBsBxBsByBsCSClCVBs")]
theorem k38 : b38.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b39 : List (List Nat × List (Nat × Nat)) := [([6,31,4329604,8659720,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQC-ASC-BKBsBRBsBSBsBiBsBpBsBqBsCSC-CaBJ"),([6,31,4329604,9742313,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQAqASAqBRFYBSFPBpFYBqFYCBEOCCAqCJAqCSAq"),([6,31,4329604,9742313,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQBuASBuBSFPBpFYBqFYCBEOCCBuCSBuCaCB"),([6,31,4330116,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCKASCKBKBsBRBsBSBsBiBsBqBsBxBsByBsCSArCVBsCaBJCdBs"),([6,31,4330468,8659208,21648020,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCNASCNBKBsBRBsBSBsBiBsBtBsBxBsByBsCJBxCSCNCVBs"),([6,31,4330468,9741609,10824010,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQArASArBRFPBSFLBpE5CBEOCCArCJE5CSAr"),([6,31,4330468,10824010,19483218,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQBOASBOA6FLBRE0BqFLCBEOCCBO"),([6,31,4330468,10824010,25977624,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQBOASBOA6FLBRE0BqFLCBEOCCBOCRBOCaDX")]
theorem k39 : b39.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b40 : List (List Nat × List (Nat × Nat)) := [([6,31,4330468,19483218,25977624,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQArASArA6FLCBEOCCArCRArCaAE"),([6,31,5412005,6495206,17318416,32505856],hh "AAE0ACE0AEE0AGE0AIE0AKE0AME0AOE0AQDTASDTBKE0BiE0BpE0BqE0B2E0CBEOCCDTCWBtCZDTCaDT"),([6,31,5412005,8659944,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQC5ASC5BKFYBSFPBiFYCBEOCCC5CSC5CaDc"),([6,31,5412005,8659944,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQCwASCwBKFYBSFPBiFYCBEOCCCwCJCwCSCw"),([6,31,5412005,9742313,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQC5ASC5BKFYBiFYBpFYBqFYCBEOCCC5CSC5CaDc"),([6,31,5412005,12989420,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQC5ASC5BKFLBiFLBpFLBqFLCBEOCCC5CJCyCaDc"),([6,31,6495206,10824010,17318416,32505856],hh "AAE0ACE0AEE0AGE0AIE0AKE0AME0AOE0AQBOASBOA6E0BqE0BxE0ByE0CBEOCCBOCOBOCaDX"),([6,31,8659944,18400817,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQBFASBFA6FYCBEOCCBFCKBFCRBFCSBF")]
theorem k40 : b40.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b41 : List (List Nat × List (Nat × Nat)) := [([6,31,9742313,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQBeASBeA6FYBqFYBxFYByFYCBEOCCBeCKBeCZAICaAI"),([6,31,10824010,12989420,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQBOASBOBKFLBpFLBqFLByFLCBEOCCBOCJBOCaDX"),([6,287,1082401,2164802,4330468,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQCWASCWBKFPBRFPBSFPBpFLBqFPByE5CBEOCCCWCKCWCZE5"),([6,287,1083361,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQD2ASD2BKFYBRFBBpFPBqFYBxFYByFYCBEOCCD2CKD2CZFt"),([6,512,1082401,2097183,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMALAOALAQCKASCKA5CKA6CKBJCKBKCKBhALBiALBpALBqALCBCKCCCKCKCKCSCKCZEpCeCK"),([6,512,1082401,2164802,32505887,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQALASALA5CTA6CTBJCTBKCTBRCTBSCTBhCTBiCTB1CLCBALCCALCSALCVCK"),([6,512,1082401,2164831,4329604,32505887],hh "AAAOACAOAEAOAGAOAIAOAKAOAMAOAOAOAQCSASCSA5AOA6AOBJAOBKAOBhAOBiAOBpAOBqAOBxANCBCSCCCSCKCSCVCK"),([6,543,1048575,1082401,2164802,4329604],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4A6CTA9CTBRCTBiCSBqCKBxCTByCTCOB4CRCfCSCfCZCKCaAK")]
theorem k41 : b41.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b42 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2097152,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKBJCKBKCKBRCKBSCKBpALBqALBxBsByBsCBELCCCKCKCKCSCKCVCKCZBsCeCK"),([6,543,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,543,1082401,2164802,4329604,32505887],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBJAOBKE5BRE5BSE5BhE2BpE5BqE5BxE5ByE5CCCTCKCTCVCL"),([6,543,1082401,2164802,4329604,32506368],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCVCKCZCh"),([6,543,1082401,2164802,4329604,32506399],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBJAOBKE5BRE5BSE5BhE2BpE5BqE5BxE5ByE5CCCTCFE5CKCTCVCL"),([6,543,1082401,2164802,4329604,32539681],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6EuBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCNE5CVCKCZAL"),([6,543,1082401,2164802,4329604,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCaASCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCYCKCaCVCKCZA4"),([6,543,1082401,2164802,4329604,33047056],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCCTCKCTCVCKCZBY")]
theorem k42 : b42.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b43 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2164802,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTA6E5BKE5BRE5BSE5BqE5BtE5BxE5ByE5CBEOCCCTCKCTCNE0CVCKCZAL"),([6,543,1082401,2164802,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BpE5BqE5ByE5B1E5CBEOCCCTCKCTCZE5CeCT"),([6,543,1082401,2164802,8659208,33047056],hh "AABYACBYAEBYAGBYAIBYAKBYAMBYAOBYAQA4ASA4A6BMBRBYBSBYBpBYBqBYBxBYByBYCKA4CNBJCZAKCaAK"),([6,543,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBYASBYA6AuBRA4BSA4BpA4BqA4BxA4ByA4CKBYCNArCZAKCaAK"),([6,543,1082401,2164802,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4A6E5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCA4CKA4CNE0CZAKCaAK"),([6,543,1082401,2164802,29224827,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQA4ASA4BKE5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCA4CKA4CVAKCZB4"),([6,543,1082401,2164802,32505856,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4BKCSBRCTBSCTBhCTBiCTBqCTByCTB1CKCKALCSE5CVCKCaB4CdCT"),([6,543,1082401,2164831,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCSASCSA5E5BKE5BSE5BhE5BpE5BqE5BxE5CBCSCCCSCKCSCVCKCZB2")]
theorem k43 : b43.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b44 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2165314,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4"),([6,543,1082401,2165343,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCSASCSA5E5BKE5BNE5BSE5BhE5BpE5BqE5BxE5CBCSCCCSCKCSCVCKCZB2"),([6,543,1082401,2165730,4329604,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQCLASCLBKFBBSFBBpFBBqFBBxE5CBEOCCCLCKCLCVCKCZBu"),([6,543,1082401,2194498,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BpE5BqE5BxE5CBEOCCCTCKCTCVCKCZB4"),([6,543,1082401,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBKE5BSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCKCTCVCKCZBs"),([6,543,1082401,4329604,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5ByE5B1E5CBEOCCCKCKCKCdCKCeCK"),([6,543,1082401,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCKASCKBRE5BSE5BiE5BpE5BqE5BxE5ByE5CBEOCCCKCJCKCKCKCaCKCdE5"),([6,543,1082401,4329604,31389629,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBRE5BSE5BiE5BqE5BtE5ByE5B1E5CBEOCCCTCKCTCRB4CdCK")]
theorem k44 : b44.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b45 : List (List Nat × List (Nat × Nat)) := [([6,543,2164802,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTBSE5BVE5BpE5BqE5BxE5ByE5CBEOCCCTCJCTCZB4"),([6,543,2164802,4329604,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQB4ASB4A6E5BKE5BRE5BSE5BpE5BqE5ByE5B1E5CBEOCCB4CNBsCVB4"),([6,543,2164802,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCArCJArCVArCaAE"),([6,543,2164802,4329604,32472030,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQArASArA6E5BRE5BSE5BqE5BtE5ByE5B1E5CBEOCCArCNAECRArCeAr"),([6,543,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCKASCKBKBsBRBsBSBsBiBsBpBsBqBsBxBsByBsCSArCVBsCaBJCdBs"),([6,992,31744,1082431,2164802,4329604,9412872,33047056],[]),([6,992,31744,1082431,2164802,4329604,17809936,32776456],[]),([6,992,1047552,1082431,2164802,4329604,8659208,33047056],[])]
theorem k45 : b45.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b46 : List (List Nat × List (Nat × Nat)) := [([6,992,1047552,1082431,2164802,4329604,17318416,32776456],[]),([6,992,1048607,2164802,8659208,33047056],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOA6BOBJBOBhBOBxBOByBOCCArCFBJCZAECaAE"),([6,992,1048607,2164802,17318416,32776456],hh "AAArACArAEArAGArAIArAKArAMArAOArAQBOASBOA5ArA6ArBJArBiArBlArBxArByArCBEyCZAECaAE"),([6,992,1082401,2097183,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCKASCKA5CsBJCsBKCsBhCmBpCsBqCsCFCKCKCKCSCKCZBe"),([6,992,1082401,2164802,4329631,8659208,17825296,32505856],[]),([6,992,1082401,2164802,4329631,8682760,17809936,32505856],[]),([6,992,1082401,2164802,4329631,9436424,17318416,32505856],[]),([6,992,1082401,2164831,4329604,32776479],hh "AAAZACAZAEAZAGAZAIAZAKAZAMAZAOAZAQD5ASD5A5AZA6AUBJAPBhAYBiAXBpAZBqAZBxAZCBAOCKD5")]
theorem k46 : b46.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b47 : List (List Nat × List (Nat × Nat)) := [([6,992,1082401,2164831,4329604,33047071],hh "AAAeACAeAEAeAGAeAIAeAKAeAMAeAOAeAQCSASCSA5AeBJARBKAeBhAYBpAeBqAeBxAdCFAOCKCSCVCs"),([6,992,1082401,2194498,4329631,8659208,17809936,32505856],[]),([6,992,1082401,2194498,4329631,9412872,17318416,32505856],[]),([6,992,1082401,3144770,4329631,8659208,17318416,32505856],[]),([6,992,1082401,4329604,6291487,17318416],hh "AAAaACAaAEAaAGAaAIAaAKAaAMCKAOCKAQAaASAaA5ASBJAWBRAaBSAaBhALBiCKCFALCGAaCJBOCKAaCRBeCSAaCaCK"),([6,992,1082431,2164802,4329604,8659208,17825296,32505856],[]),([6,992,1082431,2164802,4329604,8682760,17809936,32505856],[]),([6,992,1082431,2164802,4329604,9436424,17318416,32505856],[])]
theorem k47 : b47.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b48 : List (List Nat × List (Nat × Nat)) := [([6,992,1082431,2194498,4329604,8659208,17809936,32505856],[]),([6,992,1082431,2194498,4329604,9412872,17318416,32505856],[]),([6,992,1082431,3144770,4329604,8659208,17318416,32505856],[]),([6,992,2164802,6291487,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArA5BOBJBOBKBOBhBOBpBOBqBOCCArCFBJCJArCKArCZAaCaAa"),([6,992,4329604,8388639,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCqASCqA5BsBJBsBKBsBlBsBpBsBqBsByBsCBBxCaBO"),([6,992,4329604,8659231,17318431,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQAfASAfA5BsBJBsBKBsBSBsBlBsBqBsCBBx"),([6,1023,1082401,2164802,4329604,33047071],hh "AAALACALAEALAGALAIALAKALAMALAOALAQCTASCTBJALBKALBRALBSALBhALBpALBqALBxALByALCFE5CVA_"),([6,1023,1082401,2164802,8659208,33047536],hh "AABUACBUAEBUAGBUAIBUAKBUAMBUAOBUAQA0ASA0A6BGBRBUBSBUBpBUBqBUBxBUByBUCNBG")]
theorem k48 : b48.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b49 : List (List Nat × List (Nat × Nat)) := [([6,1023,1082401,2164802,17318896,32776456],hh "AAA0ACA0AEA0AGA0AIA0AKA0AMA0AOA0AQBUASBUA6ApBRA0BSA0BpA0CKBUCNAp"),([6,1023,4329604,8659208,17318431,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQALASALA5BsBJBsBKBsBRBsBSBsBlBsBxBsCBBsCSALCVBs"),([6,31744,1015808,1082431,2165730,4329604,8659208,33047056],hh "CoAA"),([6,31744,1082401,2165730,4329631,9412872,17318416,32505856],[]),([6,31744,1082401,3115074,4329631,8659944,17318416,32505856],[]),([6,31744,1082431,2165730,4329604,9412872,17318416,32505856],[]),([6,31744,1082431,3115074,4329604,8659944,17318416,32505856],[]),([6,1047552,1082401,2164802,4329631,8659944,17318416,32505856],[])]
theorem k49 : b49.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b50 : List (List Nat × List (Nat × Nat)) := [([6,1047552,1082401,2165730,4329631,8659208,17318416,32505856],[]),([6,1047552,1082431,2164802,4329604,8659944,17318416,32505856],[]),([6,1047552,1082431,2165730,4329604,8659208,17318416,32505856],[]),([6,1047552,1083361,2164831,4329604,8659208],hh "AAD5ACD5AED5AGD5AID5AKD5AMAkAOAkAQD5ASD5A5D5BKDyBqAkBxCDCBBCCCD1CJArCOD1CSD5CZA4CaCT"),([6,1047552,4329604,8659208,17318431,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQALASALA5BsBJBsBKBsBRBsBSBsBiBsBlBsBxBsCBB9CSALCVBs"),([6,1047552,4329604,8659208,17318896,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQBGASBGA6ACBRACBSACBpACCKBGCNAC"),([6,1082401,2164802,4329604,16777759,32505856],hh "AAEvACEvAEEvAGEvAIEvAKEvAMEvAOEvAQALASALA5EvA6EvBJEvBKEvBREvBSEvBpEtCCALCNALCRALCZEO"),([6,1082401,2164802,4329604,32505856,32506399],hh "AAALACALAEALAGALAIALAKALAMALAOALAQEOASEOA5ALA6ALBJALBKALBRALBSALBqALBtALBxALByALCNA_CaEOCdAL")]
theorem k50 : b50.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b51 : List (List Nat × List (Nat × Nat)) := [([6,1082401,2164802,4329604,32505856,33553888],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQE5ASE5A5BkA6BkBJBkBKBkBRBkBSBkBiBkBtBkBxBkCNBlCaE5CdBk"),([6,1082401,2164802,4329604,32505887,32506368],hh "AAC8ACC8AEC8AGC8AIC8AKC8AMC8AOC8AQALASALA5C8A6C8BJC8BKC8BRC8BSC8BtCjCKALCNCiCRALCSAL"),([6,1082401,2164802,4330116,32505856,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQEOASEOA5ALA6ALBJALBKALBRALBSALBqALBtALBxALByALCNA_CaEOCdAL"),([6,1082401,2164802,4330116,32505856,33554400],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQE5ASE5A5BkA6BkBJBkBKBkBRBkBSBkBiBkBtBkBxBkCNBlCaE5CdBk"),([6,1082401,2164802,4330468,32776456,33554400],hh "AACHACCHAECHAGCHAICHAKCHAMCHAOCHAQFOASFOA5CHA6CHBJBrBKBmBSCGBiCHBxCHCNCICdCH"),([6,1082401,2164802,8659208,32505887,32642020],hh "AACZACCZAECZAGCZAICZAKCZAMCZAOCZAQAWASAWA5CZA6CZBJCZBKCZBRCZBSCZBxCYCKANCNCVCVCW"),([6,1082401,2164831,4330468,8659208,32505887],hh "AAAYACAYAEAYAGAYAIAYAKAYAMAYAOAYAQCXASCXBJAVBKAYBhAYBiAYBqAYBxAYB2AYCCCXCZCXCaCX"),([6,1082401,2164831,4330468,8659231,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQAXASAXA6FPBJFLBKFPBiFPCCAXCRE5CZCXCaCX")]
theorem k51 : b51.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b52 : List (List Nat × List (Nat × Nat)) := [([6,1082401,2165730,4329604,33047056,33554400],hh "AADeACDeAEDeAGDeAIDeAKDeAMDeAODeAQCsASCsA6BkBJDeBKDeBRCGBiDeBtBkBxDeCNDgCdDe"),([6,1082401,2165730,17318416,32505887,32641156],hh "AACLACCLAECLAGCLAICLAKCLAMCLAOCLAQAQASAQA6CLBJCLBKCLBWCLBxCLCRD8"),([6,1082401,2165759,4329604,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQCKASCKBJALBKALBRALBhALBiALBuALBxALByALCZCKCaCK"),([6,1082401,2165759,4329604,17318431,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQALASALA6FBBJFBBKFBBRE5BuFBCCALCRALCZCKCaCK"),([6,1082401,4329604,8659208,16777759,32505856],hh "AAEtACEtAEEtAGEtAIEtAKEtAMEtAOEtAQALASALA5EtA6EtBJEtBKEtBREtBSEtBxEtCBALCCALCSALCVEt"),([6,1082401,4329604,8659967,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQALASALA5FYA6FYBKFYBSFPCBALCCALCSALCaAj"),([6,1082913,2164802,4329604,32505856,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQEOASEOA5ALA6ALBJALBKALBRALBSALBqALBtALBxALByALCNA_CaEOCdAL"),([6,1082913,2164802,4329604,32505856,33554400],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQE5ASE5A5BkA6BkBJBkBKBkBRBkBSBkBiBkBtBkBxBkCNBlCaE5CdBk")]
theorem k52 : b52.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b53 : List (List Nat × List (Nat × Nat)) := [([6,1083361,2164802,8659208,32505887,32641156],hh "AAD7ACD7AED7AGD7AID7AKD7AMD7AOD7AQASASASA5D7BJD7BOD2BRD7BSD7BxD6CKASCRCT"),([6,1083361,2164802,8659208,33047056,33554400],hh "AABmACBmAEBmAGBmAIBmAKBmAMBmAOBmAQBeASBeA5BkBJBmBRBmBSBmBiBmBlBkBxBmByBmCFDs"),([6,1083361,2164831,4329604,8659208,32505887],hh "AAAeACAeAEAeAGAeAIAeAKAeAMAeAOAeAQD5ASD5BJAYBKAeBRAdBhAeBmAeBqAeBxAeByAeCCD5CZD5CaD5"),([6,1083361,2164831,4329604,8659231,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQAUASAUBJFPBKFYBRFYByFYCCAUCRAUCZD5CaD5"),([6,2164802,4330495,8659208,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQBOASBOA6ALBJALBKALBhALBiALBxALByALCaBS"),([6,4330468,8659208,17318416,32505887,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQATASATA5ACBKACBRACBSAC"),([7,31,256,1082401,2164802,4330468,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCWAWCWA5FPA6FPBRFPBSFPBiFPBpFPBqFPBxFPByFPCKFPCNFPCRFLCSFPCaE5CpEOCqCWCxCWCyCWC6CWDJE5"),([7,31,256,1083361,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD2AWD2A5FYA6FYBSFYBVFYBiFYBpFYBqFYBxFBCJFYCKFYCRFPCSFYCZFYCaFYCpEOCqD2CxD2CyD2C6D2DJFt")]
theorem k53 : b53.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b54 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1048575,1082401,2164802,4329604],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4A5CTA6CTBKCTBNCTBSCTBVCTBpCTBqCTBxCTCCCSCJCTCKCTCSCKCZCTCaCTCxB4CyB4C-B4DBCfDCCfDJCKDKAK"),([7,31,512,1082401,2097152,4329604,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMCKAOCKAQBsASBsAUCKAWCKA5CKA6CKBRCKBSCKBhCKBiCKBpCKBqCKBxCKByCKCJBsCKBsCRALCSALCZBsCaBsCpELCqCKCxCKCyCKC6CKDCCKDFCKDJBsDOCK"),([7,31,512,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC6CTDFCKDJB4"),([7,31,512,1082401,2164802,4329604,32505887],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BhAOBiE5BpE5BqE5BxE5ByE5CBE2CJE5CKE5CRE5CSE5CZE5CaE5CqCTCtE5CxCTCyCTC6CTDFCL"),([7,31,512,1082401,2164802,4329604,32506368],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCyCTC1E5C6CTDFCKDJB4"),([7,31,512,1082401,2164802,4329604,32539681],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BKEuBRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CqCTCxCTCyCTC6CTC9E5DFCKDJAL"),([7,31,512,1082401,2164802,4329604,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CqCYCxCaCyCaC6CaDFCKDJA4"),([7,31,512,1082401,2164802,4329604,33047056],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CqCTCyCTC1E5C6CTDFCKDJBY")]
theorem k54 : b54.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b55 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082401,2164802,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A-E5BRE5BSE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC1E5C6CTDFCKDJB4"),([7,31,512,1082401,2164802,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BKE5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CSE5CVE5CZE5CaE5CpEOCqCTCxCTCyCTC6CTC9E0DFCKDJAL"),([7,31,512,1082401,2164802,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CaE5CdE5CpEOCqCTCxCTCyCTC6CTDJE5DOCT"),([7,31,512,1082401,2164802,8659208,33047056],hh "AABYACBYAEBYAGBYAIBYAKBYAMBYAOBYAQBYASBYAUA4AWA4A5BYA6BYBKBMBRBYBSBYBpBYBqBYBxBYByBYCJBYCKBYCRBYCSBYCZBYCaBYCyA4C1BYC6A4C9BJDJAKDKAK"),([7,31,512,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBYAWBYA5A4A6A4BKAuBRA4BSA4BpA4BqA4BxA4ByA4CKA4CNA4CRA4CSA4CZA4CaA4CxBYCyBYC6BYC9ArDJAKDKAK"),([7,31,512,1082401,2164802,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUA4AWA4A5E5A6E5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqA4CxA4CyA4C6A4C9E0DJAKDKAK"),([7,31,512,1082401,2164802,29224827,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUA4AWA4A5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CKE5CNE5CSE5CVE5CaE5CdE5CpEOCqA4CxA4CyA4C6A4DFAKDJB4"),([7,31,512,1082401,2164802,32505856,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4A5CTA6CTBRCTBSCTBiCSBpCTBqCTBxCTByCTCBCTCCCTCJCTCKCTCSCTCaCTCdCKCxB4CyB4C6ALDCE5DFCKDKB4DNCT")]
theorem k55 : b55.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b56 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082401,2164831,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCSAWCSA5E5A6E5BJE5BRE5BSE5BiE5BlE5BpE5BqE5ByE5CBE5CJE5CKE5CRE5CSE5CZE5CpCSCqCSCxCSCyCSC6CSDFCKDJB2"),([7,31,512,1082401,2165314,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BqE5BtE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC6CTDFCKDJB4"),([7,31,512,1082401,2165730,4329604,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLA5FBA6FBBRFBBSFBBiFBBqFBBtFBByFBCJFBCKFBCRFBCSFBCZE5CpEOCqCLCxCLCyCLC6CLDFCKDJBu"),([7,31,512,1082401,2194498,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5ByE5CJE5CKE5CRE5CSE5CZE5CpEOCqCTCxCTCyCTC6CTDFCKDJB4"),([7,31,512,1082401,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5ByE5B1E5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC5CTC6CTDFCKDJBs"),([7,31,512,1082401,4329604,6494406,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CaE5CdE5CpEOCqCKCxCKCyCKC6CKDNCKDOCK"),([7,31,512,1082401,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqCKCxCKCyCKC5CKC6CKDKCKDNE5"),([7,31,512,1082401,4329604,31389629,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CKE5CNE5CSE5CVE5CaE5CdE5CpEOCqCTCxCTCyCTC6CTDBB4DNCK")]
theorem k56 : b56.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b57 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082913,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A-E5BRE5BSE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC1E5C6CTDFCKDJB4"),([7,31,512,2164802,3247203,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BpE5BqE5ByE5B1E5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC5CTDJB4"),([7,31,512,2164802,4329604,5412005,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUB4AWB4A5E5A6E5BKE5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CaE5CdE5CpEOCqB4CxB4CyB4C9BsDFB4"),([7,31,512,2164802,4329604,25977624,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUArAWArA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqArCxArCyArC5ArDFArDKAE"),([7,31,512,2164802,4329604,32472030,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUArAWArA5E5A6E5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CKE5CNE5CSE5CVE5CaE5CdE5CpEOCqArCxArCyArC9AEDBArDOAr"),([7,31,512,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCKAWCKA5BsA6BsBRBsBSBsBiBsBpBsBqBsBxBsByBsCCBsCKBsCNBsCRBsCSBsCZBsCaBsCxCKCyCKDCArDFBsDKBJDNBs"),([7,31,528,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC6CTDFCKDJB4"),([7,31,543,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A9E5BJE5BNE5BRE5BhE5BiE5BlE5BpE5BqE5BxE5ByE5CBE5CFE5CJE5CRE5CSE5CZE5CaE5CpCTCqCTCtE5CxCTCyCTC6CTDFCKDJB4")]
theorem k57 : b57.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b58 : List (List Nat × List (Nat × Nat)) := [([7,31,544,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC6CTDFCKDJDj"),([7,31,576,1082401,2164802,4329604,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCTAWCTA5FPA6FPBRFPBSFPBiFPBpE5BxFPByFPCJFPCKFPCRFPCSFPCZFPCaFPCpEOCqCTCxE8CyCTC6CTDJFv"),([7,31,640,1082401,2164802,4329604,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUDwAWDwA5FBA6FBBRFBBSFBBiFBBpFBBqFBBxFBByFBCJE5CKFBCRFBCSFBCZFBCaFBCpEOCqDwCxDwCyDwC6DwDFDuDJB4"),([7,31,736,1082401,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUDwAWDwA5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCpEOCqDwCxE5CyDwC6DwDJFv"),([7,31,992,31744,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,3115074,8659208,17318416,32641156],[]),([7,31,992,507375,1082401,2164802,4329604],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4A5CTA6CTBKCTBRCTBpCTBxCTCCCSCJCTCKCLCSCKCZCTCaCTCxCUC-B4DBEBDCEBDJCKDKAK")]
theorem k58 : b58.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b59 : List (List Nat × List (Nat × Nat)) := [([7,31,992,507375,1082401,2164802,8659208],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUAKAWAKA5A4A6A4BRA4BSA4BiAuBpA4BqA2BxA4ByArCJA4CZA4CaA4CxAKC5A4C-AKDBArDCAKDJD8DKD8"),([7,31,992,777975,1082401,2164802,4329604],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUFcAWFcA5D8A6D8BKD6BVD8BpD8BqD8BxD8CCD5CJD8CZD8CaD8CxFcCyFbC-FcDBFcDCFcDJCKDKAK"),([7,31,992,777975,1082401,2164802,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUAKAWAKA5BeA6BeBVBeBiBQBpBeBqBeBxBeByBOCJBeCZBeCaBeCyAKC1BYC5BeC-AKDBBODCAKDJC5DKF5"),([7,31,992,1014750,4329604,8659208,17318416],hh "AACqACCqAECqAGCqAICqAKCqAMCqAOCqAQCqASCqAUCKAWCKA5CqA6CqBVClBpCqCCCqCJCqCKCqCRCqCSCqCZCqCaCqCqCKC1CKC5CKDBBeDCD8DJCKDKCK"),([7,31,992,1047552,1082401,2164802,4329604,8659208,33047056],[]),([7,31,992,1047552,1082401,2164802,4329604,17318416,32776456],[]),([7,31,992,1047552,1082401,2164802,8659208,17318416,32641156],[]),([7,31,992,1048576,2164802,8659208,33047056],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArA5BOA6BOBJBOBKBOBRBOBSBOBpBOBxBOByBOCJBOCRBOCSBOCZBOCaBOCyArC1BJC6ArC9BODJAEDKAE")]
theorem k59 : b59.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b60 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1048576,2164802,17318416,32776456],hh "AAArACArAEArAGArAIArAKArAMArAOArAQArASArAUBOAWBOA5ArA6ArBJArBKArBRArBSArBpArBxArByArCKArCNArCRArCSArCZArCaArCxEyC6BOC9ArDJAEDKAE"),([7,31,992,1082401,2097152,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCsASCsAUCKAWCKA5CsA6CsBRCsBhCsBiCsBpCsBqCsBxCsByCsCJCmCRCsCSCsCZCsCaCsCqCKC1CKC6CKDCCKDFCsDJBe"),([7,31,992,1082401,2164802,4329604,8659208,17825296,32505856],[]),([7,31,992,1082401,2164802,4329604,8682760,17809936,32505856],[]),([7,31,992,1082401,2164802,4329604,9436424],hh "AAEBACEBAEEBAGEBAIEBAKEBAMEBAOEBAQEBASEBAUD4AWD4A5EBA6EBBREBBSD-BhD9BiEBBxEBByEBCBDtCKD_CREBCSEBCZEBCaEBCqD2CxDxC6D4DBD0"),([7,31,992,1082401,2164802,4329604,9436424,17318416,32505856],[]),([7,31,992,1082401,2164802,4329604,17825296],hh "AADHACDHAEDHAGDHAIDHAKDHAMDHAODHAQDHASDHAUCTAWCTA5DHA6DHBRDHBhC6BiDHBqCzBxDHByDHCBDHCRDHCSDHCZDHCaDHCqCTC6CTDBCz"),([7,31,992,1082401,2164802,4329604,32506112],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD2AWD2A5FQA6FQBRFQBSFKBiFQBpE6BxFQByFQCJFPCKFOCRFQCSFQCZFQCaFQCpEOCqD2CxE5C6D2DJFv")]
theorem k60 : b60.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b61 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,4329604,32506368],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBiDCBpDCBqCsBxDCByDCCJC_CRDCCSDCCZDCCaDCCpEOCqCTC1E5C6CTDFCsDJB4"),([7,31,992,1082401,2164802,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBRFQBSFKBiFQBpE6BxFQByFQCJFPCKFOCRFQCSFQCZFQCaFQCqD6CxE5C6D8DJA4"),([7,31,992,1082401,2164802,4329604,32776479],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD6AWD6A5FQA6FQBRFQBSFKBhAZBiFQBpE6BxFQByFQCBFQCJFPCKFOCRFQCSFQCZFQCaFQCqD6CtFQCxE5C6D6"),([7,31,992,1082401,2164802,4329604,32810281],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBRFQBiFQBpE6BxFQByFQCJFPCKFOCRFQCSFQCZFQCaFQCqD6CxE5C6D8C9FQDJA4"),([7,31,992,1082401,2164802,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBiDCBpDCBqCsBxDCByDCCJC_CRDCCSDCCZDCCaDCCqCTC1E5C6CTDFCsDJBe"),([7,31,992,1082401,2164802,4329604,33047071],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBhAeBiDCBpDCBqCsBxDCByDCCBDBCJC_CRDCCSDCCZDCCaDCCqCTCtDCC1E5C6CTDFCs"),([7,31,992,1082401,2164802,4329604,33080881],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBSB7BiDCBpDCBqCsBxDCByDCCJC_CRDCCSDCCZDCCaDCCqCTC1E5C6CTC9DCDFCsDJBe"),([7,31,992,1082401,2164802,4330116,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYA-E5BRFYBVE5BiFYBpFBBqFYBtFPBxFYByFYCJFPCNFBCRFYCSFYCZFYCaFYCpEOCqCTCxE5CyCTC1E5C6CTDFCKDJB4")]
theorem k61 : b61.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b62 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,4330468,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQFOASFOAUD8AWD8A5FOA6FOA-FOBRFOBSFKBVFOBiFOBpFOBtFOBxFOByFOCJFOCKFOCNFOCRFKCSFOCaFOCqD6CxD8C1FPC6D8DJA4"),([7,31,992,1082401,2164802,5412005,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBKFQBRFQBSFQBiFQBpE6BxFQByFQCJFPCKFOCSFQCVFQCZFQCaFQCqD6CxE5C6D8C9FQDJA4"),([7,31,992,1082401,2164802,5412005,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBKDCBRDCBSDCBiDCBpDCBqCsBxDCByDCCJC_CSDCCVDCCZDCCaDCCqCTC1E5C6CTC9DADFCsDJBe"),([7,31,992,1082401,2164802,6494406,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBRFQBSFKBpE6BxFQByFQCJE5CKFOCRFQCSFQCaFQCdFQCqD6CxE5C6D8DJA4"),([7,31,992,1082401,2164802,6494406,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBpDCBxDCByDCCJC_CRDCCSDCCaDCCdDCCqCTC1E5C6CTDJBe"),([7,31,992,1082401,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCJBeCRBeCSBeCZBeCaBeCyA4C1BYC6A4C9BODJAKDKAK"),([7,31,992,1082401,2164802,8659208,33047536],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBKBQBRBeBSBeBxBeByBeCJBeCRBeCSBeCZBeCaBeCyA4C1BeC6A4C9BODKAK"),([7,31,992,1082401,2164802,8659208,33080881],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBRBeBSBeBpBeBxBeByBeCJBeCRBeCSBeCZBeCaBeCyA4C1BYC6A4C9BeDJAKDKAK")]
theorem k62 : b62.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b63 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,8659208,33317656],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUAKAWAKA5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCCA9CJBeCOA8CRBeCSBeCZBeCaBeCyAKC1BYC6AKC9BODKAKDNBe"),([7,31,992,1082401,2164802,9741609,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBRBeBpBeBxBeByBeCJBeCSBeCVBeCZBeCaBeCyA4C1BYC6A4DJAKDKAK"),([7,31,992,1082401,2164802,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBKBQBRBeBSBeBiBeBpBeBqBeBxBeByBeCJBeCRBeCSBeCaBeCdBeCyA4C1BYC6A4C9BODFBeDJAa"),([7,31,992,1082401,2164802,12988812,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUD8AWD8A5A4A6A4BRA4BSA4BiA4BpA4BxA4ByA4CJA4CKA4CRA4CSA4CZA4CaA4CxE3C6D8DJA4"),([7,31,992,1082401,2164802,16236015,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUD8AWD8A5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CJA4CKA4CSA4CVA4CaA4CdA4CxE3C6D8C9ArDJA4DOD8"),([7,31,992,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CKA4CNA4CRA4CSA4CZA4CaA4CxE3C6BeC9ArDJAKDKAK"),([7,31,992,1082401,2164802,17318416,32810281],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BRA4BpA4BxA4ByA4CKA4CNA4CRA4CSA4CZA4CaA4CxE3C6BeC9A4DJAKDKAK"),([7,31,992,1082401,2164802,17318416,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUAKAWAKA5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CCA4CNA4COA4CRA4CSA4CZA4CaA4C1A5C6AKC9ArDKAKDNA4")]
theorem k63 : b63.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b64 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,17318896,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CKA4CNA4CRA2CSA4CaA4CxBeC6BeC9ArDJAK"),([7,31,992,1082401,2164802,18400817,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BRA4BSA4BpA4BxA4ByA4CKA4CNA4CSA4CVA4CZA4CaA4CxE3C6BeDJAKDKAK"),([7,31,992,1082401,2164802,19483218,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BKAuBRA4BSA2BiA4BpA4BxA4ByA4CKA4CNA4CRA4CSA4CaA4CdA4CxE3C6BeC9ArDJFQ"),([7,31,992,1082401,2164802,21648020,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUCTAWCTA5BeA6BeBRBeBiBeBpBeBqBeBxBeByBeCNBeCRBeCSBeCZBeCaBeCyCTC1BYC6CTDFBeDJBe"),([7,31,992,1082401,2164802,24895223,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUCTAWCTA5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCNBeCSBeCVBeCaBeCdBeCyCTC1BYC6CTC9BODJBeDOCT"),([7,31,992,1082401,2164802,25977624,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUBeAWBeA5FQA6FQBKFQBRFQBSFQBpE6BxFQByFQCKFOCNE5CRFQCSFQCZFQCaFQCqA9CxE5C6BeC9FQDJAK"),([7,31,992,1082401,2164802,25977624,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUA4AWA4A5DCA6DCBKDCBRDCBSDCBpDCBxDCByDCCNC_CRDCCSDCCZDCCaDCCqA4C1E5C6A4C9DADJAK"),([7,31,992,1082401,2164802,29224827,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUBeAWBeA5FQA6FQBRFQBSFKBiFQBpE6BxFQByFQCKFOCNFPCSFQCVFQCaFQCdFQCqA9CxE5C6BeDJFQ")]
theorem k64 : b64.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b65 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,29224827,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUA4AWA4A5DCA6DCBRDCBiDCBpDCBqCsBxDCByDCCNC_CSDCCVDCCaDCCdDCCqA4C1E5C6A4DFCsDJB4"),([7,31,992,1082401,2164802,32641156,32776456],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQFvASFvAUD8AWD8A5D8A6D8BRD8BSD8BiD5BpD8BxD8ByD8CJFvCKFuCSFvCaFQCqD6CxD8C6D8DCD8DJA4"),([7,31,992,1082401,2164802,32641156,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBiDCBpDCBqCsBxDCByDCCJC_CSDCCaDCCdCsCqCTC1CTC6CTDCCTDFCsDJBe"),([7,31,992,1082401,2164802,32776456,32911756],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUA4AWA4A5D8A6D8BRD8BSD8BiD5BpD8BxD8ByD8CJD8CSD8CaD8CxA4CyA4C6A4DCA4DKA4DND8"),([7,31,992,1082401,2164802,32776456,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCJBeCSBeCVBOCaBeCyA4C1BYC6A4C9BODCA4DJAKDKAK"),([7,31,992,1082401,2164802,32776456,33317656],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUAKAWAKA5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCCA9CJBeCOA8CSBeCVBOCaBeCyAKC1BYC6AKC9BODCFQDKAKDNBe"),([7,31,992,1082401,2164802,33047056,33182356],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUBeAWBeA5CTA6CTBRCTBiCSBpCTBqCLBxCTByCTCKCTCNCTCSCTCaCTCdCKC1DwC6BeDCBeDFCKDKBeDNCT"),([7,31,992,1082401,2164802,33047056,33317656],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUAKAWAKA5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CCA4CNA4COA4CSA4CVArCaA4C1A5C6AKC9ArDCAaDKAKDNA4")]
theorem k65 : b65.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b66 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164831,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD5AWD5A5FQA6FQBJFQBRFQBSFKBiFQBlFQBpE6ByFQCBFQCJFPCKFOCRFQCSFQCZFQCpD5CqD5CxE5C6D5DJA4"),([7,31,992,1082401,2164831,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCSAWCSA5DCA6DCBJDCBRDCBiDCBlDCBpDCBqCsByDCCBDCCJC_CRDCCSDCCZDCCpCSCqCSC1E5C6CSDFCsDJBe"),([7,31,992,1082401,2165058,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD2AWD2A5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCpEOCqD2CxE5CyD2C6D2DJFv"),([7,31,992,1082401,2165730,4329604,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCsASCsAUCLAWCLA5CsA6CsA-CsBRCsBVCsBiCsBpCsBqCsBtCsByCsCJCsCNCsCRCsCSCsCZCsCqCLCxCLC1FBC6CLDFCKDJBe"),([7,31,992,1082401,2194498,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,4329604,9412872,17318416,32505856],[]),([7,31,992,1082401,3144770,4329604,8659208,17318416,32505856],[]),([7,31,992,1082401,3247203,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBRFQBiFQBpE6ByFQB1FQCJFPCKFOCRFQCSFQCZFQCaFQCqD6CxE5C5D8C6D8DJA4")]
theorem k66 : b66.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b67 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,3247203,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBiDCBpDCBqCsByDCB1DCCJC_CRDCCSDCCZDCCaDCCqCTC1E5C5CTC6CTDFCsDJBe"),([7,31,992,1082401,3247203,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBRBeBpBeByBeB1BeCJBeCRBeCSBeCZBeCaBeCyA4C1BYC5A4C6A4DJAKDKAK"),([7,31,992,1082401,3247203,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BRA4BpA4ByA4B1A4CKA4CNA4CRA4CSA4CZA4CaA4CxE3C5BeC6BeDJAKDKAK"),([7,31,992,1082401,4329604,6291456,17318416],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQCKASCKAUFYAWFYA5FYA6FYBRFYBpFPBxFYByFYCBCKCCCKCJE5CKCKCRCKCSCKCqFYC1E5C2FYC5BOC6FYDBBeDCFYDJCKDKCK"),([7,31,992,1082401,4329604,6494406,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUFcAWFcA5FQA6FQBRFQBSFKBpFPBxFQByFQCCFQCJE5CRFQCSFQCaFQCdFQCqFcCxE5C6Fc"),([7,31,992,1082401,4329604,6494406,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCKAWCKA5DCA6DCBRDCBpC_BxDCByDCCCDCCJC_CKCsCRDCCSDCCaDCCdDCCqCKC1E5C6CKDNCK"),([7,31,992,1082401,4329604,8659208,17825296],hh "AACzACCzAECzAGCzAICzAKCzAMCzAOCzAQCzASCzAUCKAWCKA5CzA6CzBRCzBhCzBxCzByCzCCCzCJCzCKCzCRCzCSCzCZCzCaCzCqCKC6CKDJCKDKCK"),([7,31,992,1082401,4329604,8682760,17809936],hh "AAC2ACC2AEC2AGC2AIC2AKC2AMC2AOC2AQC2ASC2AUEDAWEDA5C2A6C2BRC2BhC2BxC2ByC2CCC2CJC2CKC2CSC2CqEDC6EDDJCKDKCK")]
theorem k67 : b67.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b68 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,4329604,9436424,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUEDAWEDA5C5A6C5BRC5BhC5BxC5ByC5CCC5CJC5CKC5CSC5CqEDC5BOC6EDDBBeDCEDDJCKDKCK"),([7,31,992,1082401,4329604,9437183,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUEDAWEDA5C5A6C5BRC5BpC5BxC5ByC5CCC5CFC5CKC5CNC5CSC5CVCyCqEDC1CfC5BOC6EDDBBeDCEDDJCK"),([7,31,992,1082401,4329604,17318416,24117248],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCpEQCqC5CxE5CyC5C5CyC6C5DKCK"),([7,31,992,1082401,4329604,25707024,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC4AWC4A5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCpEPCqC4CxE5CyC4C5CxC6C4DKCK"),([7,31,992,1082401,4329604,25977624,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUC0AWC0A5FQA6FQBRFQBpFPBxFQByFQCCFQCNE5CRFQCSFQCZFQCaFQCqC0CxE5C5CvC6C0"),([7,31,992,1082401,4329604,25977624,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCKAWCKA5DCA6DCBRDCBpC_BxDCByDCCCDCCKCsCNC_CRDCCSDCCZDCCaDCCqCKC1E5C5CKC6CKDNFY"),([7,31,992,1082401,4329604,31389629,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUC0AWC0A5FQA6FQBRFQBSFKBpFPBqFOBxFQByFQCCFQCNE6CSFQCVFQCaFQCdFQCqC0CxE5C6C0DBA4"),([7,31,992,1082401,4329604,31389629,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBpC_BxDCByDCCCDCCKCsCNDCCSDCCVDCCaDCCdDCCqCTC1E5C6CTDBBeDNCK")]
theorem k68 : b68.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b69 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,6494406,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAKAWAKA5FYA6FYBRFYBSFYBpE5BqFYBxFYByFYCJFBCRFYCSFYCpEOCqAKCxE5CyAKC6AKDGAK"),([7,31,992,1082401,6494406,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCKAWCKA5FYA6FYBRFYBSFYBpE5BxFYByFYCJFPCRFYCSFYCpEOCqCKCxE5CyCKC6CKDGCK"),([7,31,992,1082401,6494406,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAKAWAKA5FYA6FYBRFYBpE5BxFYByFYCNFPCRFYCSFYCpEOCqAKCxE5CyAKC6AKDGAK"),([7,31,992,1082401,6494406,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCKAWCKA5FYA6FYBRFYBpE5BqFYBxFYByFYCNFBCRFYCSFYCpEOCqCKCxE5CyCKC6CKDGCK"),([7,31,992,1082401,8659208,10824010,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUAKAWAKA5BeA6BeBKBQBRBeBSBeBiBeBpBeBqBeBxBeByBeCJBeCRBeCSBeCaBeCdBeCyAKC1BYC6AKC9BODCAKDFBe"),([7,31,992,1082401,8659208,21648020,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUCKAWCKA5BeA6BeBRBeBiBeBpBeBqBeBxBeByBeCNBeCRBeCSBeCZBeCaBeCyCKC1BYC5CKC6CKDCCKDFBe"),([7,31,992,1082401,8659208,31389629,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUCKAWCKA5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCNBeCSBeCVBeCaBeCdBeCyCKC1BYC6CKC9BODBCKDCCK"),([7,31,992,1082401,10824010,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A5FYA6FYBRFYBSFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCpEOCqD8CxE5CyD8C6D8")]
theorem k69 : b69.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b70 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,10824010,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCKFYCNFPCRFYCSFYCpEOCqBeCxE5CyBeC6BeC9FS"),([7,31,992,1082401,10824010,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCKFYCNE5CRFYCSFYCpEOCqBeCxE5CyBeC6BeC9FSDKAK"),([7,31,992,1082401,12718212,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCpEQCqC5CxE5CyC5C5CyC6C5DKCK"),([7,31,992,1082401,12988812,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUC5AWC5A5A4A6A4BRA4BpA4BxA4ByA4CCA4CNA4CRA4CSA4CZA4CaA4CxE3C5CyC6C5DKCK"),([7,31,992,1082401,12988812,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYBRFYBpFPBqFYBxFYByFYCNFBCRFYCSFYCpEOCqCTCxE5CyCTC5CTC6CT"),([7,31,992,1082401,12988812,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA4AWA4A5FYA6FYBRFYBpFPBxFYByFYCNE5CRFYCSFYCpEOCqA4CxE5CyA4C5A4C6A4DKCK"),([7,31,992,1082401,17318416,19483218,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUAKAWAKA5A4A6A4BKAuBRA4BSA2BiA4BtA4BxA4ByA4CNA4CRA4CSA4CaA4CdA4CxE3C6AKC9ArDCAK"),([7,31,992,1082401,17318416,31389629,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUCKAWCKA5A4A6A4BKAuBRA4BSA2BqA4BtA4BxA4ByA4CNA4CSA4CVA4CaA4CdA4CxE3C6CKC9ArDBCKDCCK")]
theorem k70 : b70.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b71 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,19483218,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYBRFYBqFYBtFPBxFYByFYCNFBCRFYCSFYCpEOCqCTCxE5CyCTC6CT"),([7,31,992,1082401,19483218,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA4AWA4A5FYA6FYBKFYBRFYBSFYBtFPBxFYByFYCNE5CRFYCSFYCpEOCqA4CxE5CyA4C6A4C9FSDKAK"),([7,31,992,1082401,21648020,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBRFYBtFBBxFYByFYCKFYCNE5CRFYCSFYCpEOCqBeCxE5CyBeC5BeC6BeDKCK"),([7,31,992,1082431,2164802,8659208,33047056],hh "AABQACBQAEBQAGBQAIBQAKBQAMBQAOBQAQBQASBQAUAuAWAuA5BQA6BQBKBQBNBQBRBQBSBQBhBQBpBQBxBQCBBQCJBQCRBQCZBQCaBQCpAuCyAuC1BMC9FRDJAFDKAF"),([7,31,992,1082431,2164802,17318416,32776456],hh "AAAuACAuAEAuAGAuAIAuAKAuAMAuAOAuAQAuASAuAUBQAWBQA5AuA6AuBKAuBNAuBRAuBSArBhAuBpAuBxAuCBAuCKAuCNAuCRAuCZAuCaAuCpBQCxE3C9FKDJAFDKAF"),([7,31,992,1082913,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYA-E5BRFYBVE5BiFYBpFBBqFYBtFPBxFYByFYCJFPCNFBCRFYCSFYCZFYCaFYCpEOCqCTCxE5CyCTC1E5C6CTDFCKDJB4"),([7,31,992,1083361,2164802,4329604,32776456],hh "AAFKACFKAEFKAGFKAIFKAKFKAMFKAOFKAQFKASFKAUD8AWD8A5FKA6FKBSFKBVFKBiFKBpFKBxFKCJFKCKFKCRFKCSFKCZFKCaFKCqD6C1FYDJA4"),([7,31,992,1083361,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA2AWA2A5BeA6BeA-BeBKBQBRBeBSBeBVBeBpBeBtBeBxBeCJBeCNBeCRBeCZBeCaBeCxA2CyA2C1BeC6A2C9BODJAIDKAI")]
theorem k71 : b71.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b72 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1083361,2164802,17318416,32776456],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQA2ASA2AUBeAWBeA5A2A6A2BKArBSA2BVA2BpA2BxA2CJA2CKA2CRA2CSA2CZA2CaA2C1A8C9AvDJAIDKAI"),([7,31,992,2096161,2164802,8659208,17318416],hh "AABaACBaAEBaAGBaAIBaAKBaAMBaAOBaAQBaASBaAUA4AWA4A5BaA6BaBKBOBRBWBSBaBhBaCJBaCRBaCZBaCaBaCyA4C5BODBC5DCA4DJAKDKAK"),([7,31,992,2097151,2164802,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArA5BOA6BOBKBOBNBOBSBOBVBOBpBOCJBOCRBOCWBOCZBOCaBOCyArC1BJC5BOC-ArDBC5DCArDJAEDKAE"),([7,31,992,2164802,3247203,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A5FQA6FQBRE6BpE6BqFKByFQB1FQCJFPCKFOCRFQCSFQCZFQCaFQCqD6CxE5C5D8DJA4"),([7,31,992,2164802,3247203,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA5DCA6DCBRDCBpDCByDCB1DCCJC_CRDCCSDCCZDCCaDCCqCTC1E5C5CTDJBe"),([7,31,992,2164802,3247203,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBRBeBiBQBpBeBqBeByBeB1BeCJBeCRBeCSBeCZBeCaBeCyA4C1BYC5A4DFBODJAEDKAE"),([7,31,992,2164802,3247203,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BRA4BiAuBpA4BqA2ByA4B1A4CKA4CNA4CRA4CSA4CZA4CaA4CxE3C5BeDFArDJAEDKAE"),([7,31,992,2164802,4329604,5412005,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUDnAWDnA5FQA6FQBKFQBRE6BiFQBpFPBqFQBxFQByFQCJFPCKFKCRFQCSFQCaFQCdFQCqDmCxE5DFFQ")]
theorem k72 : b72.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b73 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,4329604,5412005,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUB4AWB4A5DCA6DCBKDCBRDCBSCsBiDCBpC_BqDCBxDCByDCCJC_CRDCCSDCCaDCCdDCCqB4C1E5C9CsDFB4"),([7,31,992,2164802,4329604,25977624,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUBOAWBOA5FQA6FQBRE6BiFQBpFPBqFQBxFQByFQCKFKCNE5CRFQCSFQCZFQCaFQCqAwCxE5C5BODFFQ"),([7,31,992,2164802,4329604,25977624,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUArAWArA5DCA6DCBRDCBiDCBpC_BqDCBxDCByDCCNC_CRDCCSDCCZDCCaDCCqArC1E5C5ArDFAr"),([7,31,992,2164802,4329604,32472030,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUBOAWBOA5FQA6FQBKFQBRE6BpFPBqFOBxFQByFQCKFKCNFQCSFQCVFQCaFQCdFQCqAwCxE5DBA4DOBO"),([7,31,992,2164802,4329604,32472030,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUArAWArA5DCA6DCBKDCBRDCBSCsBpC_BxDCByDCCNDCCSDCCVDCCaDCCdDCCqArC1E5C9CsDBBeDOAr"),([7,31,992,2164802,5412005,9741609,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUEjAWEjA5FYA6FYBKFYBRFBBpFPBxFYByFYCCFYCJFYCRFYCSFYCpEOCqEjCxE5CyEjDKB4"),([7,31,992,2164802,5412005,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYBKFYBRFBBpFPBxFYByFYCCFYCJFPCRFYCSFYCpEOCqCTCxE5CyCT"),([7,31,992,2164802,5412005,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA5FYA6FYBKFYBRFBBSFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCpEOCqCTCxE5CyCTC9CKDKCT")]
theorem k73 : b73.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b74 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,5412005,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUDFAWDFA5FYA6FYBKFYBRFBBSFYBpFPBxFYByFYCCFYCNFBCRFYCSFYCpEOCqDFCxE5CyDFC9Cw"),([7,31,992,2164802,6291456,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArA5BOA6BOBRBOBhBOBiBOBpBOBqBOCJBOCRBOCSBOCZBOCaBOCyArC1BJC5ArC6ArDBArDCArDJFSDKFS"),([7,31,992,2164802,8659208,9741609,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUArAWArA5BeA6BeBRBeBpBeBxBeByBeCCBQCJBeCKBeCRBeCSBeCaBeCdBeCyArC1BYDCAKDKDnDNBO"),([7,31,992,2164802,8659208,17318416,31457280],hh "AAFSACFSAEFSAGFSAIFSAKFSAMFSAOFSAQFSASFSAUBOAWBOA5FSA6FSBRE-BpFSBxFSByFSCKFSCNE0CRFSCSFSCZFSCaFSCpBOCqBOCxE0CyBODBBODCBODJArDKAr"),([7,31,992,2164802,8659208,21512720,32505856],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArAUBOAWBOA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCRC3CSArCZAECaAECpEOCqBOCxE7CyBOC5BOC-BODCBODKAr"),([7,31,992,2164802,8659208,21648020,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUArAWArA5BeA6BeBRBeBpBeBxBeByBeCCBQCKBeCNBeCRBeCSBeCZBeCaBeCyArC1BYC5ArDCAEDNAr"),([7,31,992,2164802,8659208,32472030,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A5BeA6BeBRBeBpBeBxBeByBeCCBQCKBeCNBeCSBeCVBeCaBeCdBeCyA4C1BYDBAKDCAKDNArDOA4"),([7,31,992,2164802,9741609,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAoAWAoA5FYA6FYBKFYBRFBBpFYBxFYByFYCJFPCRFYCSFYCpEOCqAoCxE5CyAoDCAo")]
theorem k74 : b74.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b75 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,9741609,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBVAWBVA5FYA6FYBRFBBpFYBxFYByFYCNE5CRFYCSFYCpEOCqBVCxE5CyBVDCBVDKAz"),([7,31,992,2164802,9741609,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUArAWArA5FYA6FYBRFBBiFYBpFYBxFYByFYCNE5CRFYCSFYCpEOCqArCxE5CyArDCArDKEj"),([7,31,992,2164802,12853512,17318416,32505856],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArAUBOAWBOA5BOA6BOBRBOBpBOBxBOByBOCKArCNBJCRC5CSArCZAECaAECpENCqBOCxE9CyBOC5BOC-BODCBODKAr"),([7,31,992,2164802,12988812,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBOAWBOA5A4A6A4BRA4BiAuBpA4BqA2BxA4ByA4CKA4CNA4CRA4CSA4CZA4CaA4CxE3C5BODFBODKAE"),([7,31,992,2164802,12988812,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBIAWBIA5FYA6FYBRFBBpFPBxFYByFYCNFBCRFYCSFYCpEOCqBICxE5CyBIC5BI"),([7,31,992,2164802,12988812,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA4AWA4A5FYA6FYBRFBBiFYBpFPBxFYByFYCNE5CRFYCSFYCpEOCqA4CxE5CyA4C5A4DKAE"),([7,31,992,2164802,17318416,18400817,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBOAWBOA5A4A6A4BRA4BqA4BtA4BxA4ByA4CCAuCKA2CNA4CRA4CSA4CaA4CdA4CxE3DCAKDKB4DNAr"),([7,31,992,2164802,17318416,32472030,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BRA4BqA4BtA4BxA4ByA4CCAuCKA2CNA4CSA4CVA4CaA4CdA4CxE3DBAKDCAKDNBODOBe")]
theorem k75 : b75.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b76 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,18400817,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBIAWBIA5FYA6FYBKFYBRFBBSFYBtE5BxFYByFYCNFBCRFYCSFYCpEOCqBICxE5CyBIC9BFDCBI"),([7,31,992,2164802,18400817,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA4AWA4A5FYA6FYBRFBBiFYBtE5BxFYByFYCNE5CRFYCSFYCpEOCqA4CxE5CyA4DCA4DKAK"),([7,31,992,2164802,21648020,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUArAWArA5FYA6FYBRFBBiFYBtFBBxFYByFYCNE5CRFYCSFYCpEOCqArCxE5CyArC5ArDKDF"),([7,31,992,3179553,4329604,17318416,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMBsAOBsAQCKASCKAUCKAWCKA5CKA6CKBRCKBpBsBxAaByAaCCCKCNCKCOCKCRBOCSCKCZBeCaD8CpELCqCKCxCKCyCKC6CKDBBsDGCKDJCKDKCK"),([7,31,992,3213378,8659208,17318416,32505856],hh "AAEcACEcAEEcAGEcAIEcAKEcAMEcAOEcAQEcASEcAUBOAWBOA5EcA6EcBREYBpEcBxEcByEcCKEcCNEUCREcCSEcCZEcCaEcCpBOCqBOCxEUCyBODBBODCBODJArDKAr"),([7,31,992,3247203,4329604,8659208,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUD8AWD8A5BsA6BsBKBsBRBsBpBsBqBsBxBsByBsCCBsCJBsCOBsCRBsCSBsCZBsCaBsCxBxDBDoDJD8DKD8"),([7,31,992,3247203,4329604,9741609,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBsAWBsA5FYA6FYBRFBBpFPBqFYBxFYByFYCJFYCZFYCaFYCpEOCqBsCxE5CyBsDBBsDJD8DKD8"),([7,31,992,3247203,4329604,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAEAWAEA5FYA6FYBRFBBSFYBpFPBqFYBxFYByFYCJFBCZFYCaFYCpEOCqAECxE5CyAEDBAEDJD8")]
theorem k76 : b76.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b77 : List (List Nat × List (Nat × Nat)) := [([7,31,992,3247203,4329604,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCTAWCTA5BsA6BsBKBsBRBsBSBsBpBsBxBsByBsCCBsCNBsCOBsCRBsCSBsCZBsCaBsCxBxC9CKDBAaDJCTDKCT"),([7,31,992,3247203,4329604,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBsAWBsA5FYA6FYBRFBBSFYBpFPBxFYByFYCNE5CZFYCaFYCpEOCqBsCxE5CyBsDBBsDJCTDKCT"),([7,31,992,3247203,4329604,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAEAWAEA5FYA6FYBRFBBpFPBxFYByFYCNFPCZFYCaFYCpEOCqAECxE5CyAEDBAEDJCT"),([7,31,992,3247203,5412005,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBsAWBsA5FYA6FYBKFYBRFBBpFPCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqBsCxE5CyBsDBEiDJBsDKBs"),([7,31,992,3247203,5412005,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBsAWBsA5FYA6FYBKFYBRFBBSFYBpFPCCFYCNE5COFYCRFYCSFYCZFYCaFYCpEOCqBsCxE5CyBsC9BsDBAaDJBsDKBs"),([7,31,992,3247203,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUADAWADA5FYA6FYBRFBBpE5CCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqADCxE5CyADDBEdDGADDJADDKAD"),([7,31,992,3247203,6494406,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUABAWABA5FYA6FYBRFBBpE5CCFYCNE5COFYCRFYCSFYCZFYCaFYCpEOCqABCxE5CyABDBEdDGABDJABDKAB"),([7,31,992,3247203,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUBeAWBeA5BsA6BsBRBsBpBsBxBsByBsCKBsCNBsCRBsCSBsCZBsCaBsCxBxDBBeDCBeDJA4DKA4")]
theorem k77 : b77.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b78 : List (List Nat × List (Nat × Nat)) := [([7,31,992,3247203,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBTAWBTA5FYA6FYBRFBBpFYBxFYByFYCNE5CZFYCaFYCpEOCqBTCxE5CyBTDBBTDCBTDJA4DKA4"),([7,31,992,3247203,8659208,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAEAWAEA5FYA6FYBKFYBRFBBpFYBxFYByFYCNFPCZFYCaFYCpEOCqAECxE5CyAEDBAEDCAEDJA4"),([7,31,992,3247203,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBRFBBpFYCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBeCxE5CyBeDBBeDCBeDJAyDKAy"),([7,31,992,3247203,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBKFYBRFBBSFYBpFBCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBeCxE5CyBeC9BODBBeDJAEDKAE"),([7,31,992,4329604,8388608,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBhBsBiBsBpBsBqBsBxBsByBsCCBsCNBsCRBsCSBsCZBsCaBsCxBxDCCqDFBsDKBO"),([7,31,992,4329604,8659208,16236015,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUDrAWDrA5BsA6BsBRBsBiBsBpBsBqBsBxBsByBsCCBsCJBsCSBsCVBsCaBsCdBsCxBxDCDrDFBsDOCK"),([7,31,992,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBiBsBpBsBqBsBxBsByBsCCBsCNBsCRBsCSBsCZBsCaBsCxBxDCCqDFBsDKBO"),([7,31,992,4329604,8659208,17318416,32810281],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBpBsBxBsByBsCCBsCNBsCRBsCSBsCZBsCaBsCxBxDCCqDFBsDKBO")]
theorem k78 : b78.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b79 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,8659208,17318416,33080881],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUBOAWBOA5BsA6BsBRBsBiBsBpBsBqBsBxBsByBsCKBsCNBsCRBsCSBsCZBsCaBsC1DiDCBODFBsDKBODNBs"),([7,31,992,4329604,8659208,17318431,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBJBsBRBsBhBsBiBsBpBsBqBsBxBsByBsCCBsCFBsCNBsCSBsCZBsCaBsCpCnCxBxDCCqDFBs"),([7,31,992,4329604,8659208,21648020,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBSBsBiBsBpBsBqBsBxBsByBsCCBsCNBsCSBsCVBsCZBsCaBsCxBxC5CoDCCqDFBs"),([7,31,992,4329604,8659208,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBiBsBpBsBuBsBxBsByBsCCBsCNBsCRBsCSBsCaBsCdBsCxBxDBCpDCCqDKBO"),([7,31,992,4329604,8659231,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBJBsBRBsBiBsBlBsBpBsBqBsByBsCBBsCCBsCNBsCRBsCSBsCZBsCaBsCpCqCxBxDFByDKBO"),([7,31,992,4329604,8659944,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBiBsBqBsBtBsByBsCCBsCJBsCRBsCSBsCZBsC1DkDFDkDKBO"),([7,31,992,4329604,9741609,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUArAWArA5FYA6FYBRFPBSFYBpFYBqFYBxFYByFYCJFBCRFYCSFYCpEOCqArCxE5CyArC5ArDCAr"),([7,31,992,4329604,9741609,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB4AWB4A5FYA6FYBRFPBpFYBqFYBxFYByFYCNE5CRFYCSFYCpEOCqB4CxE5CyB4DCB4DKDq")]
theorem k79 : b79.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b80 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,9741609,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUArAWArA5FYA6FYBRFPBpFYBxFYByFYCNE5CRFYCSFYCpEOCqArCxE5CyArDBArDCArDKBs"),([7,31,992,4329604,10824010,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBKFYBRFPBSFYBpFBBxFYByFYCKFYCNFPCRFYCSFYCpEOCqBOCxE5CyBOC9BO"),([7,31,992,4329604,10824010,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBKFYBRFPBSFYBpFBBxFYByFYCKFYCNE5CRFYCSFYCpEOCqBOCxE5CyBOC9BODBBODKAE"),([7,31,992,4329604,12988812,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBiBsBpBsBqBsByBsB1BsCCBsCNBsCRBsCSBsCZBsCaBsCxBxC5CqDFBsDKBO"),([7,31,992,4329604,17318416,24895223,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBiBsBtBsBxBsByBsCCBsCKBsCNBsCSBsCVBsCaBsCdBsCxBxDCBODNCqDOCq"),([7,31,992,4329604,17318416,25977624,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCKAWCKA5BsA6BsBRBsBiBsBtBsBuBsBxBsByBsCCBsCKBsCNBsCRBsCSBsCaBsCdBsCxBxDBCKDCCKDKArDNBs"),([7,31,992,4329604,18400817,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBRFPBtE5BxFYByFYCKFYCNFPCRFYCSFYCpEOCqBOCxE5CyBOC5BODCBO"),([7,31,992,4329604,18400817,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBRFPBtE5BxFYByFYCKFYCNE5CRFYCSFYCpEOCqBOCxE5CyBODBBODCBODKBs")]
theorem k80 : b80.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b81 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,19483218,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUArAWArA5FYA6FYBKFYBRFPBSFYBtFPBxFYByFYCNE5CRFYCSFYCpEOCqArCxE5CyArC9ArDBArDKAE"),([7,31,992,5412005,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF5AWF5A5FYA6FYBRFPBiFYBpE5CCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqF5CxE5CyF5DGCKDJF0DKF5"),([7,31,992,5412005,6494406,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF2AWF2A5FYA6FYBRFPBiFYBpE5BqFYCCFYCNE5COFYCRFYCSFYCZFYCaFYCpEOCqF2CxE5CyF2DFBsDGB3DJF2DKF2"),([7,31,992,5412005,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFPBiFYBpFYBqFYBxFYByFYCCFYCNE5CZFYCaFYCpEOCqC5CxE5CyC5DCC5DFFYDKDp"),([7,31,992,5412005,8659208,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCwAWCwA5FYA6FYBRFPBiFYBpFYBqFYBxFYByFYCCFYCNFBCZFYCaFYCpEOCqCwCxE5CyCwC5CwDCCwDFFY"),([7,31,992,5412005,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFPBiFYBpFYBqFYCCFYCNE5CRFYCSFYCZFYCaFYCpEOCqC5CxE5CyC5DCC5DFFSDKEl"),([7,31,992,5412005,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFPBiFYBpFPBqFYCCFYCNE5CRFYCSFYCZFYCaFYCpEOCqC5CxE5CyC5C5CyDFC5DKBs"),([7,31,992,6494406,8659208,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAKAWAKA5FYA6FYBKFYBRE5BpFYBxFYByFYCNFPCZFYCaFYCpEOCqAKCxE5CyAKC-AKDCAK")]
theorem k81 : b81.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b82 : List (List Nat × List (Nat × Nat)) := [([7,31,992,6494406,8659208,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBFAWBFA5FYA6FYBRE5BpFYBxFYByFYCNFBCZFYCaFYCpEOCqBFCxE5CyBFC5EdC-BFDCBF"),([7,31,992,6494406,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBKFYBRE5BSFYBpFBCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBOCxE5CyBOC9BOC-BODKAJ"),([7,31,992,6494406,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBRE5BpFPCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBOCxE5CyBOC5EdC-BODKAn"),([7,31,992,8659208,12988812,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA5BsA6BsBRBsBpBsByBsB1BsCCBsCNBsCRBsCSBsCZBsCaBsCxBxC5CqC6CqDKBO"),([7,31,992,8659208,17318416,21648020,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCKAWCKA5BsA6BsBKBsBRBsBSBsBqBsBtBsBxBsByBsCNBsCRBsCSBsCaBsCdBsCxBxC6CKC9BsDBCKDCCK"),([7,31,992,8659208,17318416,29224827,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUAKAWAKA5BsA6BsBKBsBRBsBSBsBiBsBtBsBxBsByBsCNBsCSBsCVBsCaBsCdBsCxBxC6AKC9BsDCAK"),([7,31,992,8659208,18400817,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAKAWAKA5FYA6FYBRFYBiFYBtE5BxFYByFYCNFPCRFYCSFYCpEOCqAKCxE5CyAKC5AKC6AKDCAK"),([7,31,992,8659208,18400817,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBFAWBFA5FYA6FYBKFYBRFYBSFYBtE5BxFYByFYCNFBCRFYCSFYCpEOCqBFCxE5CyBFC6BFC9FYDBBFDCBF")]
theorem k82 : b82.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b83 : List (List Nat × List (Nat × Nat)) := [([7,31,992,8659208,19483218,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCwAWCwA5FYA6FYBRFYBtFPBxFYByFYCCFYCNFBCRFYCSFYCpEOCqCwCxE5CyCwC6CwDBCw"),([7,31,992,9741609,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA5FYA6FYBKFYBRFYBSFYBpFBCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBeCxE5CyBeC6BeC9FSDJAJDKAJ"),([7,31,992,9741609,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYA6FYBRFYBpFPCCFYCNE5CRFYCSFYCZFYCaFYCpEOCqC5CxE5CyC5C5CyC6C5DKAn"),([7,31,992,10824010,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA5FYA6FYBRFBBiFYBpFPBqFYCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBOCxE5CyBOC5BODFBODKAE"),([7,31,1023,1082401,2164802,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A6FQA9FQBRFQBiFQBpE6BxFQByFQCJFPCRFQCSFQCZFQCaFQCqD6CxE5C6D8DJA4"),([7,31,1023,1082401,2164802,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA6DCA9DCBRDCBiDCBpDCBqCsBxDCByDCCJC_CRDCCSDCCZDCCaDCCpCTCqCTC1E5C6CTDFCsDJBe"),([7,31,1023,1082401,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A6BeA9BeBKBQBRBeBSBQBpBeBxBeByBeCJBeCRBeCSBeCZBeCaBeCpA4C1E4C6A4C9BODJAKDKAK"),([7,31,1023,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA6A4A9A4BKAuBRA4BSArBpA4BxA4ByA4CBA4CNA4CRA4CSA4CZA4CaA4CxA4C6BeC9ArDJAKDKAK")]
theorem k83 : b83.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b84 : List (List Nat × List (Nat × Nat)) := [([7,31,1023,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA6BsA9BsBRBsBiBsBpBsBqBsBxBsByBsCBBsCCBsCNBsCRBsCSBsCZBsCaBsCxBsDCCqDFBsDKBO"),([7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],hh "DgAA"),([7,31,31744,1015808,1082401,2165730,8659208,17318416,32641156],[]),([7,31,31744,1082401,2164802,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A-E5BRE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxFYCyCTC1E5C6CTDFCKDJB4"),([7,31,31744,1082401,2164802,4330468,32776456],hh "AAFkACFkAEFkAGFkAIFkAKFkAMFkAOFkAQFkASFkAUCeAWCeA5FkA6FkA-FOBRFkBVFOBiFkBpFOBqFkBtFkBxFkByFkCJFkCNFOCRFiCSFkCaE3CqCdCxFVCyCeC1FOC6CeDJA4"),([7,31,31744,1082401,2165730,4329604,9412872,17318416,32505856],[]),([7,31,31744,1082401,2165730,4329604,33047056],hh "AACuACCuAECuAGCuAICuAKCuAMCuAOCuAQCuASCuAUCLAWCLA5CuA6CuA-CsBRCuBVCsBiCuBpCuBqCuBtCsByCuCJCsCNCuCRCuCSCuCZCmCqCLCxDMCyCLC1CsC6CLDFCKDJBe"),([7,31,31744,1082401,3115074,4329604,8659944,17318416,32505856],[])]
theorem k84 : b84.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b85 : List (List Nat × List (Nat × Nat)) := [([7,31,31744,1082913,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A-E5BRE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxFYCyCTC1E5C6CTDFCKDJB4"),([7,31,31744,1083361,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA2AWA2A5BeA6BeA-BeBKBQBRBeBSBaBVBeBpBeBtBeBxBeCJBeCNBeCRBeCZBeCaBeCxFXC1BfC6A2C9BKDJAIDKAI"),([7,31,1047552,1082401,2164802,4329604,8659944,17318416,32505856],[]),([7,31,1047552,1082401,2164802,4329604,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUD8AWD8A5E5A6E5BRE5BiE5BpE5BqE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CqD6CxFYCyD4C6D8DJA4"),([7,31,1047552,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA5A4A6A4BKAuBRA4BSA4BpA4BxA4ByA4CBA1CNA4CRA4CSA4CZA4CaA4CxFVC6BeC9ArDJAK"),([7,31,1047552,1082401,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1047552,1082401,4329604,8659944,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUCfAWCfA5C5A6C5BRC5BhC5BxC5ByC5CCC5CJC5CKC5CSC5CqCfCxCfCyCfC5BOC6CfDBBeDCCf"),([7,31,1047552,1083361,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQF3ASF3AUD8AWD8A5D8A6D8BRD8BhD8BiD5BqD0CBCFCSF3CZCKCaAKCqD6CxD8CyD4C5ArC-D2DBD8DCD8DJA4DKCT")]
theorem k85 : b85.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b86 : List (List Nat × List (Nat × Nat)) := [([7,31,1047552,1083361,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA2AWA2A5BeA6BeBKBQBRBeBSBaBhBeCJBeCRBeCZBeCaBeCxA2C6A2DBC5DCA2DJAIDKAI"),([7,31,1047552,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUClAWClA5BsA6BsBRBsBiBsBpBsBqBsBxBsByBsCBBsCCBsCKBsCNBsCRBsCSBsCZBsCaBsCxB9DCClDFBs"),([7,31,1048575,1082401,2164802,4330468,8659208],hh "AACaACCaAECaAGCaAICaAKCaAMCaAOCaAQF4ASF4AUCaAWCaA6CaA9CaBRCaBiCXBxCaByCaCOFuCRF3CSF4CaAKCqCYCxCaC2CaC5ArC6CaDBCaDCCaDJA4DOCW"),([7,31,1048575,1082401,2165730,4329604,17318416],hh "AACLACCLAECLAGCLAICLAKCLAMCLAOCLAQBuASBuAUCLAWCLA6CLA9CLBRCLBiCKByCLCOBuCRECCSECCZCKCqCLCxCLC2CLC5BOC6CLDGCLDJBeDKD8"),([7,31,1048575,1082401,4329604,8659944,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUDVAWDVA6C5A9C5BRC5BWCyBxC5ByC5CCC5CJC5CSC5CaC5CqDVCxDVC5BOC6DVDBBeDCDV"),([7,31,1048575,1083361,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQF3ASF3AUD8AWD8A6D8A9D8BRD8BiD5BxD8COFtCRF3CSF3CZCKCaAKCqD6CxD8C2D8C5ArC-D2DBD8DCD8DJA4DKCT"),([7,31,1048575,1083361,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA2AWA2A6BeA9BeBKBQBRBeBxBeCJBeCOBeCRBeCZBeCaBeCxBeC2A2C6A2DBC5DCA2DJAIDKAI"),([7,31,1048575,2164802,4330468,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArA6BOA9BOBWBOBiBOByBOCJBOCRBOCSBOCZBOCxBOC5C5C6ArDCArDJDTDKDT")]
theorem k86 : b86.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b87 : List (List Nat × List (Nat × Nat)) := [([7,31,1049568,2164802,8659208,17318416,32505856],hh "AAFSACFSAEFSAGFSAIFSAKFSAMFSAOFSAQFSASFSAUBOAWBOA5FSA6FSBRE-BpFSBxFSByFSCKFSCRFSCSFSCZFSCaFSCpBOCqBOCyBODBBODCBODJArDKAr"),([7,31,1082401,1082913,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA6E5A-E5BKE5BRE5BSE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CKE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxCTCyCTC1E5C5CTC6CTDFCKDJAL"),([7,31,1082401,1083361,2164802,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A6FQBKFQBSFQBVFQBiFQBpFQBqFQBxE6CJFQCKFQCRFPCSFOCZFQCaFQCqD6CyD8C1FKC5E5DJA4"),([7,31,1082401,1083361,2164802,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA6DCBKDCBSDCBVDCBiDCBpDCBqDCBxDCByCsCJDCCKDCCRC_CZDCCaDCCqCTCxCTCyCTC9E5DFCsDJBe"),([7,31,1082401,1083361,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A6BeA-BeBKBeBRBeBSBeBVBeBpBeBqBeBtBeBxBeCJBeCKBeCNBeCRBeCZBeCaBeCxA4CyA4C1BeC6A4C9BYDJAKDKAK"),([7,31,1082401,1083361,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA6A4BKA4BSA4BVA4BpA4BqA4BxA4CJA4CKA4CSA4CVA4CZA4CaA4CyBeC1A2C5E3DJAKDKAK"),([7,31,1082401,2098144,4329604,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCKAWCKBJFBBKFBBSFBBpFBBqFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCpELCqCKCyCKDBBsDJCKDKCK"),([7,31,1082401,2164802,2165314,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BiE5BpE5BqE5ByE5B1E5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCyCTC5CTDBE8DJB4")]
theorem k87 : b87.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b88 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,2165730,4329604,32776456],hh "AAE6ACE6AEE6AGE6AIE6AKE6AME6AOE6AQE6ASE6AUD8AWD8BKE6BRE6BSE6BiE6BpEyBqE6ByE6B1E6CJE6CKE6CRE6CSE6CZE5CaE3CqD6CyD8DBE5DJA4"),([7,31,1082401,2164802,2165730,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTBKDCBOCsBRDCBSDCBWCsBiDCBqDCBxCsByDCB1DCCJDCCKDCCRDCCSDCCVCsCZC_CqCTCyCTC5CTC9CsDFCTDJBe"),([7,31,1082401,2164802,2165730,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A6BQBKBeBRBeBSBeBiBeBpBeBqBeByBeB1BeCJBeCKBeCRBeCSBeCZBeCyA4C1BOC5A4DFBYDJAQDKAQ"),([7,31,1082401,2164802,2165730,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA6AuBKA4BRA4BSA4BiA4BpA2BqA4ByA4B1A4CJA4CKA4CRA4CSA4CaA4CdA4CyBeC1ArDBE3DJFDDKFD"),([7,31,1082401,2164802,4329604,4330116,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUB4AWB4BKE5BRE5BSE5BiE5BmE5BpE5BqE5BuE5BxE5ByE5B2E5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CdE5CpEOCqB4CyALC9BsDBB4DFCTDJB4"),([7,31,1082401,2164802,4329604,4330468,32776456],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFcAWFcBKFPBRFPBSFPBiFPBmFOBpFPBqFPBuFOBxFPByFPB2FOCCFPCJFKCKFPCSE5CZFOCaFPCdFPCqFcCyFcDBFcDFFODJE5"),([7,31,1082401,2164802,4329604,4330468,33047056],hh "AAC_ACC_AEC_AGC_AIC_AKC_AMC_AOC_AQC_ASC_AUCUAWCUBKC_BRC_BSC_BiC_BpC_BqC_BxC_ByC_CCC_CKC_CRCmCSC_CaC_CdC_CqCUCyCUC9CmDNCT"),([7,31,1082401,2164802,4329604,8659944,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8BKFQBRFQBSFQBpFQBqFQBxFQByFQCCFQCJFKCKFQCSE6CZFOCaFPCqD8CyD8DBFvDJE5")]
theorem k88 : b88.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b89 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4329604,9436424,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUDxAWDxBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CKE5CRE5CSE5CaE5CpEOCqDxCyDxDBFvDJFYDKED"),([7,31,1082401,2164802,4329604,16777728,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CBE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCTCyCTC9CKDBB4DJCT"),([7,31,1082401,2164802,4329604,32505856,32506368],hh "AACTACCTAECTAGCTAICTAKCTAMB4AOB4AQCTASCTAUCTAWCTBKCSBRCTBSCTBpALBqALBxCKByAKCBCTCCCTCKCTCSCTCVCKCZB4CaC_CpCTCqCTCyCTC6E8C9CKDBB4DCB4DKCTDNCT"),([7,31,1082401,2164802,4329604,32505856,33553695],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQDwASDwAUFYAWFYBKFYBRFYBSFYBpFYBqFYBxFYByFYCBEOCCDwCKDwCZFvCqFYCtFYCyFYC1FYC6FBDCFPDFFYDKFYDNDw"),([7,31,1082401,2164802,4329604,32505856,33553919],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQCTASCTAUE5AWE5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CBEOCCCTCKCTCVCKCZB4CqE5CtE5CyE5C1E5C6E5C9E5DCE5DFE5DKE5DNCT"),([7,31,1082401,2164802,4329604,32506848,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUD8AWD8BKE5BRE5BSE5BpE5BqE5BxE5ByE5CBE5CCE5CKE5CSE5CVE5CZE3CaE5CqD6CyD8DBA4DJE5DOD2"),([7,31,1082401,2164802,4329604,32776456,32777192],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQD8ASD8AUE5AWE5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CCD8CKD8CZFECqE5CyE5C6E5C9E5DBE3DCE5DKE5DND8"),([7,31,1082401,2164802,4329604,32776456,33553439],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQD8ASD8AUFQAWFQBKFQBRFQBSFQBpFQBqFQBxFQByFQCCD6CKD8CZA4CqFQCtFQCyFQC1FKC6E6DCFPDFFODKFY")]
theorem k89 : b89.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b90 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4329604,33047056,33553439],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQCTASCTAUDCAWDCBKDCBRDCBSDCBpDCBqDCBxDCByDCCCCTCKCTCVCsCZBeCqDCCtDCCyDCC6DCC9CsDCC_DOCT"),([7,31,1082401,2164802,4330116,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CJE5CKE5COE5CRE5CSE5CWE5CZE5CaE5CeE5CpEOCqCaCyCaC9CKDBB-DJCaDKCaDNE5"),([7,31,1082401,2164802,4330116,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CJE5CKE5COE5CRE5CSE5CWE5CaE5CeE5CpEOCqCTCyCTC9CKDBB4DJCTDKCTDNE5"),([7,31,1082401,2164802,4330116,32505856],hh "ABE5ADE5AFE5AHE5AJE5ALE5ANE5APE5ARCTATCTA7E5A_E5BLE5BPE5BTE5BXE5BjE5BnE5BrE5BvE5BzE5B3E5CDCTCHE5CLCTCPE5CTCTCXCTCbB4CfCT"),([7,31,1082401,2164802,4330468,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBpFLBqFPByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCpEOCqCaCyCaDBE5DJCaDKCa"),([7,31,1082401,2164802,4330468,8659208,32505887],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBJAYBKFPBRFPBSFPBhFNBpFLBqFPByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCqCaCtFPCyCaDJCYDKCa"),([7,31,1082401,2164802,4330468,8659208,32539681],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaA6FIBKFPBRFPBSFPBqFPByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCqCaCyCaC1FPDBE5DJCaDKCa"),([7,31,1082401,2164802,4330468,8659208,32776456],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBpFLBqFPByE5CCFPCGFOCJFPCKFPCOFOCRFPCSFPCWFOCZFPCaFOCeFPCqCaCyCaDBE5DJCaDKCaDNFP")]
theorem k90 : b90.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b91 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4330468,8659231,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCYAWCYA5FPBJFPBKFPBRFPBSFPBhFPBpFLBqFPByE5CCFPCFFPCKFPCRFPCSFPCeFPCpCYCqCYCyCYDBE5DJCYDKCY"),([7,31,1082401,2164802,4330468,9741609,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBqFPByE5CCFPCKFPCNFPCRFPCSFPCZFPCeFPCpEOCqCaCyCaDBE5DJCaDKCa"),([7,31,1082401,2164802,4330468,10824010,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBpFLBqFPBxFPByE5CCFPCJFPCKFPCSFPCVFPCZE5CeFPCpEOCqCaCyCaC9CaDBE5DJCa"),([7,31,1082401,2164802,4330468,17318416,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQFOASFOAUFbAWFbA6AuBKFOBRFOBSFOBiA4BpFKBqFOByE3CCFOCGFOCJFOCKFOCOFOCRFOCSFOCWFOCaFOCdA4CeFOCqDQCyFbC1ArDBA4DJFbDKFbDNFO"),([7,31,1082401,2164802,4330468,21648020,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBqFPBxFPByE5CCFPCJFPCKFPCRFPCSFPCdE5CeFPCpEOCqCaCyCaC9CaDBE5DJCa"),([7,31,1082401,2164802,4330468,24895223,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBpFLBqFPByE5CCFPCKFPCNFPCSFPCVFPCdFPCeFPCpEOCqCaCyCaDBE5DJFPDOCa"),([7,31,1082401,2164802,4330468,32505856,32776456],hh "AACaACCaAECaAGCaAICaAKCaAMFzAOFzAQCaASCaAUCaAWCaBKCXBRCaBSCaBpFyBqFzByAKCBCaCCCaCGFOCKCaCOFOCSFOCWCaCZFuCaFzCeFOCqCYCyCaC6CaDBA4DGCWDJCaDKCaDNCa"),([7,31,1082401,2164802,4330468,32776456],hh "ABFOADFOAFFOAHFOAJFOALFOANFOAPFOARCaATCaA7FOA_FOBLFOBPFOBTFOBXFOBjFOBnFOBrFOBvFOBzFOB3FOCDCaCHFOCLCaCPFOCTCaCXCaCbFbCfCa")]
theorem k91 : b91.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b92 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,5412837,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaA6FPBKFPBRFPBSFPBqFPBtFPByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCpEOCqCaCyCaC1FLDBE5DJCaDKCa"),([7,31,1082401,2164802,6495206,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaBRE5BSE5BpE0BqE5ByE5B1E5CCE5CJE5CKE5CRE5CSE5CZE5CeE5CpEOCqCaCyCaDBE5DGCaDJCaDKCa"),([7,31,1082401,2164802,8659208,8659944,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUAKAWAKA6BQBRBeBSBeBiBeBpBeBqBeBxBeByBeCCBeCJBeCKBeCSBeCaBeCdBeCyAKC1BODCAKDKCcDNBY"),([7,31,1082401,2164802,8659208,12989420,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBRFPBSFPBpFPBqFPBxFPByFPCJFLCKFPCSE5CaFPCdFPCpEOCqCaCyCaDBCaDCCaDJE5"),([7,31,1082401,2164802,8659208,16236527,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaA6E5BRE5BSE5BpE5BqE5BxE5ByE5CKE5CNE5CSE5CVE5CaE5CdE5CpEOCqCaCyCaC1E0DBCaDCCaDJE5DOCa"),([7,31,1082401,2164802,8659208,17317904,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBYAWBYA6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqBYCyBYC1E0DBBYDCBYDJA4DKA4"),([7,31,1082401,2164802,8659208,29223963,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUBYAWBYBKFPBRFPBSFPBiFPBpFPBqFPBxFPByFPCKFPCNFLCSE5CZFPCaFPCpEOCqBYCyBYDBBYDCBYDJFu"),([7,31,1082401,2164802,8659208,32505856,32642020],hh "AACaACCaAECaAGCaAICaAKCaAMCaAOCaAQCaASCaAUE5AWE5BKCXBRCaBSCaBiCYBpCaBqCaBxCaByCaCBCaCCCaCKCaCZCaCaCaCyE5C6E5C9CVDCE5DFCWDKE5DNCa")]
theorem k92 : b92.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b93 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,8659208,33047056,33553439],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQA4ASA4AUBeAWBeA6BQBRBeBSBeBpBeBqBeBxBeByBeCKA4CNBOCZAKCaAKCqBeCtBeCyBeC1BeC6BeDCBeDNA4DOA4"),([7,31,1082401,2164802,8659720,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBYAWBYA6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CpEOCqBYCyBYC1E0DBBYDCBYDJA4DKA4"),([7,31,1082401,2164802,8659944,17318416,32776456],hh "AAFOACFOAEFOAGFOAIFOAKFOAMFOAOFOAQFOASFOAUBeAWBeA6FOBRFOBSFOBiA4BpFKBqFOByE3CJFOCKFOCRFOCSFOCaFOCdA4CqBeCyBeC1FKDBE3DJAKDKAK"),([7,31,1082401,2164802,17318416,32506848,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA6AuBRA4BSA4BpA4BqA4BxA4ByA4CBA4CCA4CKA4CNAuCSA4CZA4CeA4CyBeC1ArDBAKDJE3"),([7,31,1082401,2164802,17318416,32776456,32777192],hh "AAE3ACE3AEE3AGE3AIE3AKE3AME3AOE3AQBeASBeAUE3AWE3A6E3BRE3BSE3BpE3BqE3BxE3ByE3CCBeCKBeCNEyCZAKCqA4CyE3C1E3C6E3DBE3DGA4DKE3DNBe"),([7,31,1082401,2164802,17318416,32776456,33553439],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQBeASBeAUA4AWA4A6AuBRA4BSA4BpA4BqA4BxA4ByA4CKBeCNArCZAKCaAKCqA4CtA4CyA4C1A2C6A4DFA4DGA4DKA7"),([7,31,1082401,2164831,4330468,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCXAWCXA5FPBKFPBNFPBSFPBhFPBpFLBqFPCBFPCCFPCJFPCKFPCRFPCSFPCZFPCeFPCpCXCqCXCyCXDBE5DJCXDKCX"),([7,31,1082401,2165314,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CWE5CZE5CaE5CpEOCqCTCyCTDBB4DJCTDKCT")]
theorem k93 : b93.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b94 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165314,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBYAWBYA6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CZE5CaE5CpEOCqBYCyBYC1E0DBBYDCBYDJA4DKA4"),([7,31,1082401,2165730,4329604,8659208,33047056],hh "AACsACCsAECsAGCsAICsAKCsAMCsAOCsAQCsASCsAUAQAWAQA6BRBKCsBSCsBiBgBpCsBqCsBxCmB2BeCCCsCGCsCJCsCKCsCOCsCRCsCSCsCWCsCZCsCaCsCeCsCqCMCyDnC9CKDBBeDJAQDKAQDNCs"),([7,31,1082401,2165730,4329604,10824010,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUD8AWD8BKFBBRFBBSFBBpFBBqFBBxE5ByFBCCFBCJFBCKFBCWFBCZFBCaFBCpEOCqD8CyD8DBDnDJD8"),([7,31,1082401,2165730,4329604,16236015,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBSFBBpFBBqFBBxE5CCFBCKFBCNFBCWFBCaFBCdFBCpEOCqCLCyCLDBBuDJFBDOCL"),([7,31,1082401,2165730,4329604,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBSFBBpFBBqFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCpEOCqCLCyCLDBBuDJCLDKCL"),([7,31,1082401,2165730,4329604,17318416,32505887],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBJARBKFBBSFBBhFABpFBBqFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCqCLCtFBCyCLDJCLDKCL"),([7,31,1082401,2165730,4329604,17318416,32539681],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLA6EuBKFBBRByBSFBBpFBBqFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCqCLCyCLC1FBDBAQDJCLDKCL"),([7,31,1082401,2165730,4329604,17318416,33047056],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBSFBBpFBBqFBBxE5CCFBCGCsCJFBCKFBCOCsCSCsCWFBCZFBCaFBCeCsCqCLCyCLC9CKDBBuDJCLDKCLDNFB")]
theorem k94 : b94.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b95 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165730,4329604,17318431,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLA5FBBJFBBKFBBSFBBhFBBpFBBqFBBxE5CCFBCFFBCKFBCWFBCaFBCpCLCqCLCyCLDBBuDJCLDKCL"),([7,31,1082401,2165730,4329604,18400817,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBRFBBSFBBpFBBqFBBxE5CCFBCKFBCNFBCWFBCZFBCaFBCpEOCqCLCyCLDBDnDJCLDKCL"),([7,31,1082401,2165730,4329604,21648020,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUD8AWD8BKFBBSFBBpFBBqFBBxE5ByFBCCFBCJFBCKFBCWFBCaFBCdFBCpEOCqD8CyD8DBBuDJD8"),([7,31,1082401,2165730,4329604,32505856,33047056],hh "AACLACCLAECLAGCLAICLAKCLAMBuAOBuAQCLASCLAUCLAWCLBKCKBSCLBpAQBqAQBxCKCBCLCCCLCGCsCKCLCOCsCSCLCWCsCZBuCaCsCeCLCqCLCyCLC9CKC-CLDBBeDCD8DJCLDKCLDNCL"),([7,31,1082401,2165730,4329604,33047056],hh "ABCsADCsAFCsAHCsAJCsALCsANCsAPCsARCLATCLA7CsA_CsBLCsBPCsBTCsBXCsBjCsBnCsBrCsBvCsBzCsB3CsCDCLCHCsCLCLCPCsCTCLCXCLCbBuCfCL"),([7,31,1082401,2165730,5412005,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLA6FBBKFBBRFBBSFBBqFBBtFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCpEOCqCLCyCLC1E-DBAQDJCLDKCL"),([7,31,1082401,2165730,10824010,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUBeAWBeA6FBBKFBBRFBBSFBBpFBBqFBCJFBCKFBCSFBCZFBCaFBCpEOCqBeCyBeC1E-DBBeDJA3DKA3"),([7,31,1082401,2165730,17318416,21648020,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBSFBBpFBBqFBByFBCJFBCKFBCaFBCdFBCpEOCqCLCyCLDBCLDCCLDJBe")]
theorem k95 : b95.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b96 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165730,17318416,29224827,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUA3AWA3BKFBBSFBBiFBBpFBBqFBB2FBCKFBCNFBCVE5CaFBCdFBCpEOCqA3CyA3DBA3DCA3DJBu"),([7,31,1082401,2165730,17318416,32505856,32641156],hh "AACLACCLAECLAGCLAICLAKCLAMCLAOCLAQCLASCLAUBuAWBuBKCKBSCLBiCLBpCLBqCLB2CLCBCLCCCLCKCLCSCLCZCLCaCLCyAQDBD8DCBeDKBuDNCL"),([7,31,1082401,2165759,4329604,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCKAWCKBKFBBNFBBSFBBpFBBqFBBxE5CBFBCCFBCJFBCKFBCWFBCZFBCaFBCpCKCqCKCyCKDBBsDJCKDKCK"),([7,31,1082401,2194498,4329604,9412872,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUDvAWDvBKE5BSE5BpE5BqE5BxE5CCE5CKE5CRE5CSE5CaE5CpEOCqDvCyDvDBFvDJFdDKEJ"),([7,31,1082401,3144770,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUDvAWDvBKE5BSE5BpE5BqE5BxE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqDvCyDvDBFvDJDvDKDv"),([7,31,1082401,3144770,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BSE5BpE5BqE5BxE5CBExCCE5CJE5CKE5CSE5CZE5CaE5CpEOCqCTCyCTDBFwDJFg"),([7,31,1082401,3247203,4330468,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBKFPBSFPBVFPBqFPByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCpEOCqCaCxCaCyCaDBE5DJCaDKCa"),([7,31,1082401,3248099,4329604,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBKFBBSFBBVFBBpFBBqFBBxE5CCFBCJFBCKFBCWFBCZFBCaFBCpEOCqCLCxCLCyCLDBBsDJCLDKCL")]
theorem k96 : b96.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b97 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,6495206,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKBRE5BSE5BiE5BqE5ByE5B1E5CCE5CJE5CKE5CRE5CSE5CeE5CpEOCqCKCyCKDGCKDJCKDKCK"),([7,31,1082401,4329604,8389600,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBhFYBiFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCpEQCqC5CxCyCyC5DCC5DKDc"),([7,31,1082401,4329604,8659208,16777728,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUC5AWC5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CBE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqC5CxCyCyC5DCC5DFE5"),([7,31,1082401,4329604,8659720,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUDKAWDKBRE5BSE5BiE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CpEOCqDKCxDGCyDKDCDKDKDc"),([7,31,1082401,4329604,8659944,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF5AWF5BRFYBSFYBiFYBpFYBqFYBxFYByFPCCFYCJFYCKFYCRFYCSFYCpEOCqF5CyF5C5FvDCF5"),([7,31,1082401,4329604,8659944,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF5AWF5BRFYBSFYBiFYBqFYByFPCCFYCKFYCNFYCSFYCVFYCpEOCqF5CxEnCyF5DCF5DODV"),([7,31,1082401,4329604,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCpEOCqC5CxCyCyC5DCC5DKDc"),([7,31,1082401,4329604,8659944,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BJFUBRFYBSFYBiFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCqC5CtFYCyC5DCC5DKDc")]
theorem k97 : b97.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b98 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,8659944,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYCCFYCJFYCKFYCRFYCSFYCpEMCqC5CyC5DCC5DFFYDKC1DNFY"),([7,31,1082401,4329604,8659944,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A6FFBRFYBSFYBiFYBqFYBtDkByFPCCFYCJFYCKFYCRFYCSFYCqC5CyC5C1FYDCC5DKDc"),([7,31,1082401,4329604,8659944,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCqC5CxCyCyC5DCC5DKDI"),([7,31,1082401,4329604,8659944,17318416,32777192],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYCCFYCJFYCKFYCRFYCSFYCqC5CyC5DCC5DFFYDKC1DNFY"),([7,31,1082401,4329604,8659944,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUDcAWDcBRFYBSFYBiFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCqDcCxDbCyDcDCC1DFE5DKDcDNFY"),([7,31,1082401,4329604,8659944,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A5FYBJFYBRFYBSFYBhFYBiFYBqFYByFPCCFYCFFYCKFYCSFYCpC5CqC5CxCyCyC5DCC5DKDc"),([7,31,1082401,4329604,8659944,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBpFYBqFYByFPCCFYCKFYCNFYCRFYCSFYCpEOCqC5CyC5DCC5DKDc"),([7,31,1082401,4329604,8659944,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYBxFYByFPCCFYCJFYCKFYCSFYCVFYCpEOCqC5CxCyCyC5C5C3DCC5")]
theorem k98 : b98.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b99 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,8659967,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBlFYBqFYByFPCBFYCCFYCJFYCKFYCRFYCSFYCpC5CqC5CxCyCyC5DCC5DKDc"),([7,31,1082401,4329604,9436424,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUC5AWC5BRE5BSE5BiE5BqE5ByE5CBExCCE5CJE5CKE5CRE5CSE5CaE5CpEOCqC5CxCyCyC5DCC5"),([7,31,1082401,4329604,9742313,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5BRFYBSFYBiFYBqFYBtFYByFPCCFYCJFYCKFYCRFYCSFYCpEOCqC5CyC5DCC5DKDc"),([7,31,1082401,4329604,12989420,17318416,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUC5AWC5BRFPBSFPBiFPBqFPByFPB1FPCCFPCJFPCKFPCRFPCSFPCpEOCqC5CxCyCyC5C5C5DKDc"),([7,31,1082401,4329604,17318416,24894487,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF1AWF1BRFYBSFYBiFYBpFYBqFYBxFYByFYCCFYCKFYCSFPCpEOCqF1CxEmCyF1DCF1DOC5"),([7,31,1082401,4329604,17318416,31388701,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUCLAWCLBRFBBSFBBiFBBpFBBqFBBxFBByFBCCFBCKFBCSE5CZFBCpEOCqCLCyCLC5BuDBCLDCCL"),([7,31,1082401,4330116,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKBRE5BSE5BiE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CSE5CZE5CaE5CpEOCqCKCxCKCyCKDCCKDFE5DKDaDNE5"),([7,31,1082401,4330468,8659208,10824010,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUF4AWF4BRFLBSFPBiFPBpFPBqFPBxFPByFPCCFPCJFPCKFPCRE5CaFPCdFPCpEOCqF4CyF4C5E5DCF4DFFP")]
theorem k99 : b99.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b100 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4330468,8659208,21648020,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCRAWCRBSFPBiFPBpFPBqFPBxFPByFPCCFPCJFPCKFPCVE5CZFPCaFPCpEOCqCRCxCOCyCRC5E5DCCRDFFP"),([7,31,1082401,4330468,8659208,31389629,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCRAWCRBRFLBSFPBiFPBpFPBqFPBxFPB2FPCCFPCKFPCNFPCVE5CaFPCdFPCpEOCqCRCyCRC5E5DBCQDCCR"),([7,31,1082401,5412005,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A6FYBSFYBVFYBiFYBpFYBqFYByFPCCFYCJFYCKFYCRFYCSFYCpEOCqC5CyC5C1FSDCC5DKDc"),([7,31,1082401,8659944,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBKFYBRFYBSFYBpFYBqFYCJFYCKFYCSFYCZFYCaFYCpEOCqBeCyBeC1FSC6BeDJAKDKAK"),([7,31,1082401,8659944,17318416,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCKAWCKBKFYBSFYBpFYBqFYByFYCJFYCKFYCaFYCdFYCpEOCqCKCxCKCyCKC6CKDBCKDCCK"),([7,31,1082401,8659944,17318416,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAKAWAKBKFYBSFYBiFYBpFYBqFYCKFYCNFYCVFPCaFYCdFYCpEOCqAKCxAKCyAKC6AKDCAK"),([7,31,1082913,2164802,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CJE5CKE5COE5CRE5CSE5CWE5CZE5CaE5CeE5CpEOCqCaCyCaC9CKDBB-DJCaDKCaDNE5"),([7,31,1082913,2164802,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CKE5COE5CRE5CSE5CWE5CZE5CaE5CeE5CpEOCqCTCyCTC9CKDBB4DJCTDKCTDNE5")]
theorem k100 : b100.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b101 : List (List Nat × List (Nat × Nat)) := [([7,31,1082913,2164802,4329604,32505856],hh "ABE5ADE5AFE5AHE5AJE5ALE5ANE5APE5ARCTATCTA7E5A_E5BLE5BPE5BTE5BXE5BjE5BnE5BrE5BvE5BzE5B3E5CDCTCHE5CLCTCPE5CTCTCXCTCbB4CfCT"),([7,31,1082913,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBYAWBYA6E5BRE5BSE5BpE5BqE5BxE5ByE5CKE5CRE5CSE5CZE5CaE5CpEOCqBYCyBYDBBYDCBYDJA4DKA4"),([7,31,1082913,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKBRE5BSE5BiE5BpE5BqE5BxE5ByE5CCE5CKE5CRE5CSE5CZE5CaE5CpEOCqCKCxCKCyCKDCCKDFE5DKCKDNE5"),([7,31,1083361,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFBBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqD8CyD8DBFtDJD8DKD8"),([7,31,1083361,2164802,4329604,8659208,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BJAeBKFYBRFBBhFUBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqD8CtFYCyD8DJD6DKD8"),([7,31,1083361,2164802,4329604,8659208,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpBpCqD8CyD8C9DyDBFtDKD8DNFY"),([7,31,1083361,2164802,4329604,8659208,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A6FIBKFYBRFBBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqD8CyD8DBFvDJD8DKD8"),([7,31,1083361,2164802,4329604,8659208,32540641],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A6FIBKFYBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqD8CyD8C1FYC9DyDBFtDKD8DNFY")]
theorem k101 : b101.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b102 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,4329604,8659208,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFBBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqD8CyD8DBFtDKD8DNFY"),([7,31,1083361,2164802,4329604,8659208,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFeAWFeA6BRBKFYBRFBBiBgBmFXBpFPBqFYBuBeBxFYByFYB2BeCCFYCJFYCOFYCRFYCSFYCZFYCaFYCdBeCqFeCyFeC1BJDBBeDFBeDJFeDKFe"),([7,31,1083361,2164802,4329604,8659231,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD6AWD6A5FYBJFYBKFYBRFBBhFYBpFPBqFYBxFYByFYCCFYCFFYCOFYCRFYCSFYCaFYCpD6CqD6CyD6DBFtDJD6DKD6"),([7,31,1083361,2164802,4329604,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFBBSFYBpFPBqFYBxFYByFYCCFYCJFBCOFYCSFYCVFYCZFYCaFYCpEOCqD8CyD8C9D8DBB-DJD8"),([7,31,1083361,2164802,4329604,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTBKFYBRFBBpFPBxFYByFYCCFYCJFPCOFYCRFYCSFYCaFYCdFYCpEOCqCTCyCTDBF3DJEZ"),([7,31,1083361,2164802,4329604,17318416,32539681],hh "AAB7ACB7AEB7AGB7AIB7AKB7AMB7AOB7AQB7ASB7AUCTAWCTA6B4BKB7BRB7BSByBpB6BxB7ByB7CCB7COB7CRB7CSB7CZB7CaB7CqCTC9ByDBASDJCTDKCT"),([7,31,1083361,2164802,4329604,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTBKFYBRFBBSFYBpFPBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYCpEOCqCTCyCTC9CKDBB-DJCTDKCT"),([7,31,1083361,2164802,4329604,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFBBpFPBqFYBxFYByFYCCFYCNFYCOFYCSFYCVFYCaFYCdFYCpEOCqD8CyD8DBFtDJFYDOD8")]
theorem k102 : b102.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b103 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,4329604,32505856,32776456],hh "AAD8ACD8AED8AGD8AID8AKD8AMFyAOFyAQD8ASD8AUD8AWD8BKD5BRD8BpFyBqFyBxCKByAKCBD8CCD8COFKCSFKCZFtCaFyCqD6C2EZC6D8DBA4DCEZDKD8DND8"),([7,31,1083361,2164802,4330468,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFYBpFLBqFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCeFYCpEOCqD8CyD8DBFtDJD8DKD8"),([7,31,1083361,2164802,5412005,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A6FYBKFYBRFBBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqD8CyD8DBFvDJD8DKD8"),([7,31,1083361,2164802,5412005,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB5AWB5A6FYBKFYBRFBBSFYBxFYByFYCCFYCOFYCRFYCSFYCZFYCaFYCpEOCqB5CyB5C9BtDBASDJB5DKB5"),([7,31,1083361,2164802,5412837,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A6FYBKFYBRFYBqFYBtFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCeFYCpEOCqD8CyD8C1FLDBFtDJD8DKD8"),([7,31,1083361,2164802,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BRFBBpE5BqFYByFYB1FYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqD8CyD8DBFYDGD8DJD8DKD8"),([7,31,1083361,2164802,8659208,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8BKFYBRFBBpFYBxFYByFYCJFPCKFYCRFYCSFYCaFYCdFYCpEOCqD8CyD8DBD8DCD8DJA4"),([7,31,1083361,2164802,8659208,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8A6FYBRFBBpFYBxFYByFYCKFYCSFYCVFYCaFYCdFYCpEOCqD8CyD8DBD8DCD8DJFYDOD8")]
theorem k103 : b103.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b104 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBRFBBpFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCpEOCqBeCyBeDBBeDCBeDJA2DKA2"),([7,31,1083361,2164802,8659208,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBJAeBRFBBpFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCqBeCtFYCyBeDCBeDKA2"),([7,31,1083361,2164802,8659208,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBpFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCpBpCqBeCyBeC1FSDCBeDJA2DKA2"),([7,31,1083361,2164802,8659208,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBRFBBpFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCqBeCyBeDBBeDCBeDJA4DKA4"),([7,31,1083361,2164802,8659208,17318416,32540641],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBpFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCqBeCyBeC1FYDCBeDJA2DKA2"),([7,31,1083361,2164802,8659208,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBRFBBiA-BpFYBuA8BxFYByFYCKFYCRFYCSFYCZFYCaFYCqBeCyBeDCBeDFFYDJAIDKAI"),([7,31,1083361,2164802,8659208,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA2AWA2A6FYBRFBBpFYBxFYByFYCCBgCGFXCKFYCOBeCRFYCSFYCWBeCZFYCaFYCeBeCqA2CyA2C1E0DBAIDCAIDJA2DKA2DNFY"),([7,31,1083361,2164802,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBRFYBpFYBxFYByFYCKFYCSFYCaFYCpEOCqBeCyBeDBBeDCBeDJA2DKA2")]
theorem k104 : b104.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b105 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeBRFBBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYCpEOCqBeCyBeDBBeDCBeDJA4DKA4"),([7,31,1083361,2164802,8659208,18401265,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeBRFYBpFYBxFYByFYCKFYCNFYCSFYCaFYCpEOCqBeCyBeDBBeDCBeDJA2DKA2"),([7,31,1083361,2164802,8659208,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBKFYBRFBBpFYBxFYByFYCKFYCSFYCVFYCZFYCaFYCpEOCqBeCyBeDBBeDCBeDJA2"),([7,31,1083361,2164802,8659208,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBRFBBiFYBpFYBuFYBxFYByFYCKFYCRFYCSFYCaFYCdFYCpEOCqBeCyBeDBBeDCBeDJAIDKAI"),([7,31,1083361,2164802,8659208,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeBKFYBRFBBiFYBpFYBuFYBxFYByFYCKFYCNFPCSFYCVFYCaFYCdFYCpEOCqBeCyBeDBBeDCBeDJFt"),([7,31,1083361,2164802,8659208,32505856,32641156],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUFtAWFtBKD5BRD8BiD6BpD8BuD2BxD8ByD8CBD8CCD8CKD8CSD8CZD8CaD8CyFtC6FYDBCTDCA4DKFtDND8"),([7,31,1083361,2164802,8659208,32505856,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA2AWA2A6BQBRBeBpBeBxBeByBeCBBeCCBeCGBeCKBeCOBeCSBeCWBeCZBeCaBeCeBeCyA2C1BJC6A2DBAIDCAIDJA2DKA2DNBe"),([7,31,1083361,2164802,8659208,33047056],hh "ABBeADBeAFBeAHBeAJBeALBeANBeAPBeARA2ATA2A7BeA_BeBLBeBPBeBTBeBXBeBjBeBnBeBrBeBvBeBzBeB3BeCDA2CHFXCLA2CPBeCTA2CXBeCbAICfBe")]
theorem k105 : b105.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b106 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBKFYBRFBBSFYBpFBByFYB1FYCKFYCRFYCSFYCZFYCaFYCpEOCqBeCyBeC9BeDBBeDJA2DKA2"),([7,31,1083361,2164802,17318416,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB5AWB5A6FYBRFBBqFYBxFYByFYCNFYCSFYCVFYCaFYCdFYCpEOCqB5CyB5DBB5DCB5DJFYDOB5"),([7,31,1083361,2164802,17318416,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUA2AWA2A6FYBRFBBiFYBuFYBxFYByFYCRFYCSFYCaFYCdFYCpEOCqA2CyA2DBA2DCA2DJAIDKAI"),([7,31,1083361,2164802,17318416,32505856,32776456],hh "AAA2ACA2AEA2AGA2AIA2AKA2AMA2AOA2AQA2ASA2AUBeAWBeA6ArBRA2BqA2BxA2ByA2CBA2CCA2COA2CSA2CZA2CaA2C6BeDBAIDCAIDKBeDNA2"),([7,31,1083361,2164831,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD5AWD5A5FYBKFYBNFYBhFYBpFPBqFYBxFYCBFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpD5CqD5CyD5DBFtDJD5DKD5"),([7,31,1083361,4329604,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF3AWF3BRFPBiFYBpE5ByFYB1FYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCpEOCqF3CyF3DGCKDJFyDKF3"),([7,31,1083361,4329604,8659208,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUF3AWF3BRFPBSFYBiFYBpFYBqFYBxFYByFYCCFYCJFBCRFYCSFYCaFYCdFYCpEOCqF3CyF3C5FtDCF3DFFY"),([7,31,1083361,4329604,8659208,17318416,32539681],hh "AAByACByAEByAGByAIByAKByAMByAOByAQByASByAUC5AWC5A6BsBRBxBiByBpByBqByBxByByByCCByCNBsCRByCSByCZByCaByCqC5CxBxDCC5DFByDKCK")]
theorem k106 : b106.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b107 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,4329604,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB1AWB1BRFPBiFYBpFYBqFYBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCpEOCqB1CyB1DCB1DFFYDKCK"),([7,31,1083361,4329604,8659208,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB1AWB1BRFPBSFYBiFYBpFYBuFYBxFYByFYCCFYCNFBCSFYCVFYCaFYCdFYCpEOCqB1CyB1C5BzDBB0DCB1"),([7,31,1083361,5412005,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A6FYBiFYBpFYBqFYBxFYByFYCCFYCRFYCSFYCZFYCaFYCpEOCqC5CyC5DCC5DFFYDKBt"),([7,31,1083361,8659208,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeA6FYBKFYBRFYBSFYBpFBByFYB1FYCKFYCRFYCSFYCZFYCaFYCpEOCqBeCyBeC6BeC9FYDJAIDKAI"),([7,31,1083361,8659208,17318416,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAIAWAIA6FYBRFYBiFYBxFYByFYCRFYCSFYCaFYCdFYCpEOCqAICyAIC5AIC6AIDCAI"),([7,31,1083361,8659208,17318416,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBtAWBtA6FYBRFYBqFYBxFYByFYCNFBCSFYCVFYCaFYCdFYCpEOCqBtCyBtC5BtC6BtDBBtDCBt"),([7,31,1083391,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBQAWBQA6FYA9FYBRFBBpFYBxFYByFYCBFYCRFYCSFYCZFYCaFYCpBQCqBQCyBQDBBQDCBQDJArDKAr"),([7,31,2096161,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBWAWBWA6E5BRE5BpE5BxE5ByE5CBExCRE5CSE5CZE5CaE5CpEOCqBWCyBWDBBWDCBWDJEg")]
theorem k107 : b107.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b108 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,3247203,4330468,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUCaAWCaBSFPBVFPBqE5BxFLByE5CCFPCJFPCKFPCRFPCSFPCZFPCeFPCpEOCqCaCxCaDBE5DJCaDKCa"),([7,31,2164802,3248099,4329604,8659208,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUD8AWD8BSFBBVFBBpFBBqFBBxE5ByFBCCFBCJFBCKFBCRFBCWFBCZFBCaFBCpEOCqD8CxD8DBB-DJD8DKD8"),([7,31,2164802,3248099,8659208,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUBeAWBeBKFBBSFBBVFBBpFBBqFBBxFBCJFBCKFBCSFBCZFBCaFBCpEOCqBeCxBeDBBeDCBeDJA2DKA2"),([7,31,2164802,4195296,8659208,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBJFLBKFLBSE0BpFLBqFLBxFLCJFLCKFLCSFLCZFLCaFLCpEOCqBOCxBODCBODKDX"),([7,31,2164802,4329604,5412837,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUB-AWB-A6FPBKFPBRFPBSFPBqE5ByFPB1FPCCFPCJFPCKFPCRFPCSFPCZFPCeFPCpEOCqB-C9B-DJB-DKB-"),([7,31,2164802,4329604,8659208,9742313,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUB-AWB-A6FYBRFYBSFYBpFYBqFYBxFYByFYCKFBCRFYCSFPCaFYCdFYCpEOCqB-C5B-DCB-DKCC"),([7,31,2164802,4329604,8659208,16236527,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUB-AWB-BKE5BRE5BSE5BpE5BqE5BxE5ByE5CKE5CNE5CSE5CVE5CaE5CdE5CpEOCqB-CxB-C9B-DCB-DOB-"),([7,31,2164802,4329604,8659208,17317904,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBJAWBJBKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqBJCxBJC9BJDCBJDKAr")]
theorem k108 : b108.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b109 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4329604,8659208,32471070,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBJAWBJA6FYBRFYBSFYBiFYBpFYBqFYBxFYByFYCKFBCSFPCVFYCZFYCaFYCpEOCqBJC5BJDBBJDCBJDOBJ"),([7,31,2164802,4329604,8659720,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBJAWBJBKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CpEOCqBJCxBJC9BJDCBJDKDb"),([7,31,2164802,4329604,8659944,17318416,32776456],hh "AAFKACFKAEFKAGFKAIFKAKFKAMFKAOFKAQFKASFKAUBOAWBOBKFKBRFKBSFKBiArBqEyBxFKByFKCJFKCKFKCRFKCSFKCaFKCqBOCxBOC9FKDKDE"),([7,31,2164802,4330116,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBJAWBJBKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CSE5CZE5CaE5CpEOCqBJCxBJDCBJDKDX"),([7,31,2164802,4330468,5412005,8659208,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUDnAWDnA6FLBKFLBSE0BpFLBqFLByFLCCFLCJFLCKFLCRFLCWFLCZFLCaFLCpEOCqDnDJDnDKDn"),([7,31,2164802,4330468,5412005,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUB4AWB4A6FLBKFLBRFLBSE0BpFLBqFLCCFLCJFLCKFLCWFLCZFLCaFLCpEOCqB4C1BsDJB4DKB4"),([7,31,2164802,4330468,5412837,8659208,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUDnAWDnA6FLBKFLBSFLBqFLByFLB1FLCCFLCJFLCKFLCRFLCWFLCZFLCeFLCpEOCqDnC9B-DJDnDKDn"),([7,31,2164802,4330468,8659208,9741609,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUDnAWDnA6FPBSE5BpFPBqFPBxFPCJFPCKFPCRFPCSFLCaFPCdFPCpEOCqDnC5E5DCDnDKAr")]
theorem k109 : b109.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b110 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4330468,8659208,16236015,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUDnAWDnBKFLBSE0BpFLBqFLBxFLCKFLCNFLCSFLCaFLCdFLCpEOCqDnCxDnDCDnDODn"),([7,31,2164802,4330468,8659208,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBKFLBSE0BpFLBqFLBxFLCJFLCKFLCSFLCZFLCaFLCpEOCqBOCxBODCBODKDX"),([7,31,2164802,4330468,8659208,17318416,32505887],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOA5AVBJFJBKFLBSE0BpFLBqFLBxFLCJFLCKFLCSFLCZFLCaFLCqBOCtFLDCBODKBS"),([7,31,2164802,4330468,8659208,17318416,32776456],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBKFLBSE0BiAtBpFLBqFLBxFLByFKCJFLCKFLCSFLCZFLCaFLCqBOCxBODCBODFFLDKDX"),([7,31,2164802,4330468,8659208,17318416,33047056],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUDXAWDXBKFLBSE0BpFLBqFLBxFLCCBLCJFLCKFLCZFLCaFLCqBSCxDXC9DXDCDXDKDXDNFL"),([7,31,2164802,4330468,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOBKFYBSFYBpFYBqFYBxFYCKFYCSFLCaFYCpEOCqBOCxBODCBODKCA"),([7,31,2164802,4330468,8659208,19483218,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOA6FLBKFLBSE0BpFLBqFLBxFLCKFLCNFLCSFLCZFLCaFLCpEOCqBODCBO"),([7,31,2164802,4330468,8659208,21648020,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUBOAWBOBSE5BpFPBqFPBxFPCJFPCKFPCSFLCVE5CZFPCaFPCpEOCqBOCxBOC5E5DCBO")]
theorem k110 : b110.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b111 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4330468,8659208,21648372,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBSFLBpFLBqFLBxFLCKFLCSFLCVFLCaFLCpEOCqBOCxBOC5BODCBO"),([7,31,2164802,4330468,8659208,25977624,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBKFLBSE0BiFLBpFLBqFLBxFLB2FLCJFLCKFLCSFLCaFLCdFLCpEOCqBOCxBODBBODCBODKDX"),([7,31,2164802,4330468,8659208,32472030,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUBOAWBOA6FPBSE5BiFPBpFPBqFPBxFPB2FPCKFPCNFPCSFLCVFPCaFPCdFPCpEOCqBOC5E5DBBODCBODOBO"),([7,31,2164802,4330468,10824010,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOA6FLBKFLBRFLBSE0BqFLBtFLBxE0CJFLCKFLCSFLCZFLCaFLCpEOCqBOC1BODKDX"),([7,31,2164802,4330468,17318416,24895223,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUB4AWB4BKFLBSE0BpFLBqFLByFLCKFLCNFLCVFLCaFLCdFLCpEOCqB4CxB4DCB4DOB4"),([7,31,2164802,4330468,17318416,25977624,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUArAWArBKFLBSE0BiFLBpFLBqFLB2FLCJFLCKFLCaFLCdFLCpEOCqArCxArDBArDCArDKDT"),([7,31,2164802,4330495,8659208,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBKFLBNFLBSE0BpFLBqFLBxFLCBFLCJFLCKFLCZFLCaFLCpBOCqBOCxBODCBODKDX"),([7,31,2164802,5241988,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBMAWBMBKE5BSE5BpE5BqE5BxE5CBExCJE5CKE5CZE5CaE5CpEOCqBMCxBMDCBM")]
theorem k111 : b111.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b112 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,6495206,8659208,17318416,32505856],hh "AAE0ACE0AEE0AGE0AIE0AKE0AME0AOE0AQE0ASE0AUBOAWBOBKE0BSE0BVE0BpE0BqE0BxE0CJE0CKE0CSE0CZE0CaE0CpEOCqBOC-BODCBODKDX"),([7,31,2164802,8659208,9742313,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeBRFYBSFYBiFYBqFBByFYB1FYCJFYCKFYCRFYCSFYCaFYCpEOCqBeC6BeDCBeDJArDKAr"),([7,31,2164802,8659208,12989420,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOBRFLBSFLBiFLBqE0ByFLB1FLCJFLCKFLCRFLCSFLCaFLCpEOCqBOCxBOC5BOC6BODKDX"),([7,31,2164802,8659208,17318416,29223963,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUEkAWEkBRFLBSFLBpFLBqFLBxFLByFLCCFLCKE0CSFLCdFLCpEOCqEkCxEkC6EkDCEk"),([7,31,2164802,8659208,17318416,32471070,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeBRFYBSFYBpFYBqFYBxFYByFYCCFYCKFBCSFYCdFYCpEOCqBeC5BeC6BeDBA2DCA2DOBe"),([7,31,2165314,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBJAWBJBKE5BRE5BSE5BpE5BqE5BxE5ByE5CRE5CSE5CZE5CaE5CpEOCqBJCxEXC9BJDCBJDKAr"),([7,31,2165730,4329604,5412005,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUBuAWBuA6FBBKFBBRE5BSFBBpE5ByFBB1FBCCFBCOFBCRFBCSFBCZFBCaFBCpEOCqBuC9BuDJBuDKBu"),([7,31,2165730,4329604,8659208,17318416,32539681],hh "AAByACByAEByAGByAIByAKByAMByAOByAQByASByAUCqAWCqA6BsBKByBRBxBiBuBpByBqByBxByByByCCBvCNBsCRByCSByCZByCaByCqBPCxBsDCCqDFBuDKBO")]
theorem k112 : b112.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b113 : List (List Nat × List (Nat × Nat)) := [([7,31,2165730,4329604,10824010,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUBOAWBOA6FBBKFBBRE5BSFBBxFBByFBCKFBCRFBCSFBCZFBCaFBCpEOCqBOC9BODKAq"),([7,31,2165730,4329604,17318416,18400817,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUBuAWBuA6FBBRE5BqFBBxFBByFBCRFBCSFBCaFBCdFBCpEOCqBuC5BuDCBuDKBO"),([7,31,2165730,4329604,17318416,32472030,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUAqAWAqA6FBBRE5BiFBBuFBBxFBByFBCNFBCSFBCVFBCaFBCdFBCpEOCqAqC5AqDBAqDCAqDOAq"),([7,31,4329604,4330468,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA6BsBKBsBSBsBVBsBiBsBpBsBqBsBxBsByBsCCBsCJBsCKBsCVBsCZBsCaBsC5BxDCCqDFBsDKBO"),([7,31,4329604,5412005,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5A6FYBSFYBVFYBiFYBpFYBqFPByFPCCFYCJFYCKFYCRFYCSFYCpEOCqC5C1C5C5CyDCC5DKDc"),([7,31,4329604,8659208,8659944,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqBKBsBRBsBSBsBiBsBqBsByBsB1BsCCBsCJBsCKBsCRBsCSBsCdBsC6CqC9BsDBBxDKBO"),([7,31,4329604,8659208,17318416,32506848,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUClAWClBKBsBRBsBSBsBiBsBpBsBqBsBxBsByBsCBBsCCBsCKBsCSBsCVBsCdBsCeBsC6ClC9BsDJBx"),([7,31,4329604,8659208,17318416,32539681,32540641],hh "AABxACBxAEBxAGBxAIBxAKBxAMBxAOBxAQClASClAUBxAWBxBKBxBRBxBSBxBiBxBpBxBqBxBxBxByBxCCDOCSClCVBxCqBsCyBxC6BxC9BxDFBxDGBsDKBxDNCl")]
theorem k113 : b113.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b114 : List (List Nat × List (Nat × Nat)) := [([7,31,4329604,8659208,17318416,32539681,33553439],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQCqASCqAUBsAWBsBKBsBRBsBSBsBiBsBpBsBqBsBxBsByBsCSCqCVBsCaBOCqBsCtBsCyBsC6BsC9BsDGBsDKB8"),([7,31,4329604,8659944,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOA6FYBKFYBRFYBSFPBpFYBqFYCJFYCKFYCSFYCZFYCaFYCpEOCqBOC1BOC6BODBBODKAE"),([7,31,4329604,8659944,17318416,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBsAWBsBKFYBSFPBpFYBqFYByFYCJFYCKFYCaFYCdFYCpEOCqBsC6BsDCBsDJBODKBO"),([7,31,4329604,8659944,17318416,32472030,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAEAWAEBKFYBSFPBiFYBpFYBqFYCKFYCNFYCVFYCaFYCdFYCpEOCqAEC6AEDCAEDJEdDOAE"),([7,31,4329604,8659944,17318416,32505856,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCyAWCyBKBsBSBsBiBsBpBsBqBsCBBsCCBsCKBsCWBsCaBsCyCyDCBODKCyDNBs"),([7,31,4330468,5412005,8659208,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUC5AWC5A6FLBiFLBpFLBqFLBxFLByFLCCFLCRFLCSFLCZFLCaFLCpEOCqC5C5CyDCC5DFFLDKBs"),([7,31,4330468,8659208,10824010,17318416,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBOAWBOA6FLBKFLBRFLBSFLBpE0ByFLB1FLCKFLCRFLCSFLCZFLCaFLCpEOCqBOC6BOC9FLDBBODKDX"),([7,31,4330468,8659208,17318416,19483218,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUAEAWAEA6FLBRFLBiFLBxFLByFLCRFLCSFLCaFLCdFLCpEOCqAEC6AEDCAEDJCy")]
theorem k114 : b114.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b115 : List (List Nat × List (Nat × Nat)) := [([7,31,4330468,8659208,17318416,31389629,32505856],hh "AAFLACFLAEFLAGFLAIFLAKFLAMFLAOFLAQFLASFLAUBsAWBsA6FLBRFLBqFLBxFLByFLCNE0CSFLCVFLCaFLCdFLCpEOCqBsC6BsDCBsDJBO"),([7,31,4330468,8659208,17318416,32505856,32573506],hh "AAAEACAEAEAEAGAEAIAEAKAEAMAEAOAEAQAEASAEAUBOAWBOA6AEBRAEBqAEBxAEByAECBAECCAECKAECSAECaAEC6BODCCyDKBODNAE"),([7,287,992,1082401,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD2AWD2BRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCpEOCqD2CxE5CyD2C6D2DJFv"),([7,512,543,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A9E5BJE5BKE5BNE5BhE5BiE5BlE5BqE5BxE5ByE5CBE5CCE5CFE5CRE5CSE5CZE5CaE5CpCTCqCTCtE5CxEOCyCTC6CTDFCKDJB4"),([7,512,1082401,2164802,4329604,32505856,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUEOAWEOA5ALA6ALBJALBKALBRALBSALBhALBiALBpALBqALBxALByALCBALCCALCSALCVALCZALCaALCpEOCqEOC9A_DKEODNAL"),([7,512,1082401,2164802,4329604,32505856,33554400],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUE5AWE5A5BkA6BkBJBkBKBkBRBkBSBkBhBkBiBkBpBkBqBkBxBkByBkCBBkCCBkCKBkCVBkCZBkCqE5CtBkC9BlDKE5DNBk"),([7,543,992,1082401,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTA6FYA-E5BRFYBVE5BiFYBpFBBqFYBtFPBxFYByFYCJFPCNFBCRFYCSFYCZFYCaFYCpEOCqCTCxE5CyCTC1E5C6CTDFCKDJB4"),([7,543,31744,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTA5E5A6E5A-E5BRE5BVE5BiE5BpE5BqE5BtE5BxE5ByE5CJE5CNE5CRE5CSE5CZE5CaE5CpEOCqCTCxFYCyCTC1E5C6CTDFCKDJB4")]
theorem k115 : b115.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b116 : List (List Nat × List (Nat × Nat)) := [([7,543,1082401,2164802,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCaAWCaBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CJE5CKE5COE5CRE5CSE5CWE5CZE5CaE5CeE5CpEOCqCaCyCaC9CKDBB-DJCaDKCaDNE5"),([7,543,1082401,2164802,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTBKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CGE5CJE5CKE5COE5CRE5CSE5CWE5CZE5CaE5CeE5CpEOCqCTCyCTC9CKDBB4DJCTDKCTDNE5"),([7,543,1082401,2164802,4329604,32505856],hh "ABE5ADE5AFE5AHE5AJE5ALE5ANE5APE5ARCTATCTA7E5A_E5BLE5BPE5BTE5BXE5BjE5BnE5BrE5BvE5BzE5B3E5CDCTCHE5CLCTCPE5CTCTCXCTCbB4CfCT"),([7,543,1082401,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBYAWBYA6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqBYCyBYC1E0DBBYDCBYDJA4DKA4"),([7,543,1082401,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCKAWCKBRE5BSE5BiE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqCKCxCKCyCKDCCKDFE5DKCKDNE5"),([7,543,2164802,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBJAWBJBKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpEOCqBJCxBJC9BJDCBJDKAr"),([7,992,1023,1082401,2164802,4329604,32776456],hh "AAFQACFQAEFQAGFQAIFQAKFQAMFQAOFQAQFQASFQAUD8AWD8A6FQA9FQBKFKBxFQByFQCCFOCRFQCSFQCZFQCaFQC6D8DJA4"),([7,992,1023,1082401,2164802,4329604,33047056],hh "AADCACDCAEDCAGDCAIDCAKDCAMDCAODCAQDCASDCAUCTAWCTA6DCA9DCBiCsBqCsBxDCByDCCRDCCSDCCZDCCaDCCpCTC6CTDFCsDJBe")]
theorem k116 : b116.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b117 : List (List Nat × List (Nat × Nat)) := [([7,992,1023,1082401,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUA4AWA4A6BeA9BeBKBeBSBQBxBeByBeCRBeCSBeCZBeCaBeCpA4CqA4C6A4C9BODJAKDKAK"),([7,992,1023,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUBeAWBeA6A4A9A4BKA2BSArBxA4ByA4CBA4CCA4CRA4CSA4CZA4CaA4C6BeC9ArDJAKDKAK"),([7,992,1023,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUCqAWCqA6BsA9BsBiBsBqBsBxBsByBsCBBsCRBsCSBsCZBsCaBsDCCqDFBsDKBO"),([7,992,31744,1015808,1082431,2164802,4329604,8659208,33047056],hh "DgAA"),([7,992,31744,1015808,1082431,2164802,4329604,17318416,32776456],hh "DgAA"),([7,992,31744,1082401,2164802,4329631,8659208,17809936,32505856],[]),([7,992,31744,1082401,2164802,4329631,9412872,17318416,32505856],hh "DgAA"),([7,992,31744,1082401,3115074,4329631,8659208,17318416,32505856],hh "CwAADgAA")]
theorem k117 : b117.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b118 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1082431,2164802,4329604,8659208,17809936,32505856],[]),([7,992,31744,1082431,2164802,4329604,9412872,17318416,32505856],hh "DgAA"),([7,992,31744,1082431,3115074,4329604,8659208,17318416,32505856],hh "CwAADgAA"),([7,992,1047552,1082401,2164802,4329631,8659208,17318416,32505856],[]),([7,992,1047552,1082401,2164802,8659208,32641156],hh "AAD7ACD7AED7AGD7AID7AKD7AMD7AOD7AQD7ASD7AUEqAWEqA5D7A6D7BKD7BqDzBxD7ByD7CGD2CKD3CRD7CSD7CZD7CaD7CqEoDCAKDJCT"),([7,992,1047552,1082401,2164802,17318416,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4A5CTA6CTBiCLBqCTBxCTByCTCBCTCGCTCKCTCRCTCSCTCZCTCaCTDCAKDFCKDJD8"),([7,992,1047552,1082401,2164831,4329604,8659208],hh "AAD5ACD5AED5AGD5AID5AKD5AMD5AOD5AQAmASAmAUD5AWD5A5D5A6D5BJD5BKD5BRD5BqDyCCAlCRAmCSAmCZCKCpBACuD1CxD5CyD1C5ArC6D5DCD5DJA4DKCT"),([7,992,1047552,1082401,2164831,4329604,17318416],hh "AACSACCSAECSAGCSAICSAKCSAMCSAOCSAQAiASAiAUCSAWCSA5CSA6CSBJCSBRCSBiCKBqCSCRAiCSAiCZCKCuCSCxCSCyCSC5BOC6CSDCCSDJBeDKD8")]
theorem k118 : b118.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b119 : List (List Nat × List (Nat × Nat)) := [([7,992,1047552,1082431,2164802,4329604,8659208,17318416,32505856],[]),([7,992,1047552,2164802,4329631,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArA5BOA6BOBiBOBqBOByBOCBBOCJBOCRBOCSBOCqArCxArC5C5C6ArDJBEDKBE"),([7,992,1047552,4329604,8659208,17318416,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQACASACAUBHAWBHA5ACA6ACBKACBSACBxACByACCBACCCACCRACCSACCZACCaACC6BHC9AC"),([7,992,1048607,2164802,8659208,17318416,32505856],hh "AAESACESAEESAGESAIESAKESAMESAOESAQESASESAUBOAWBOA5ESA6ESBJESBhESBxESByESCCESCFERCRESCSESCZESCaESCpE0CqBODBBODCBODJArDKAr"),([7,992,1082401,2097183,4329604,17318416,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMAaAOAaAQCKASCKAUCKAWCKA5CKBJCKBKCKBhAWBpAaBqAaCFCKCGCKCJBOCKCKCSCKCZBeCaD8CpCKCqCKCyCKC6CKDBErDGCKDJCKDKCK"),([7,992,1082401,2164802,4329604,32776456,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUFQAWFQA5BmA6DfBJDeBRDfBSDfBhCHBiDfBpDfBqDfBxDfByDfCBDfCKDfCZDfCqFQCtDfC9DhDNDf"),([7,992,1082401,2164802,4329604,33047056,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDCAWDCA5BmBJDeBKDfBRDfBSDfBhCHBpDfBqDfBxDfByDfCFBkCKDfCVDfCZDfCqDCCtDfC9DgDNDf"),([7,992,1082401,2164802,8659208,32505887,32641156],hh "AAD7ACD7AED7AGD7AID7AKD7AMD7AOD7AQD7ASD7AUAaAWAaA5D7A6D7BJD7BRD7BSD7BhD7BmD2BpD7BqD7BxD7ByD7CBD7CCD7CZD6CpAWCqAaC6AaDBCT")]
theorem k119 : b119.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b120 : List (List Nat × List (Nat × Nat)) := [([7,992,1082401,2164802,8659208,33047056,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUBeAWBeA5BmA6DfBJDeBRDfBSDfBhDfBpDfBqDfBxDfByDfCCDfCFBkCKDfCNDfCZDfCaDfCqBeCtDfC1Ds"),([7,992,1082401,2164802,17318416,32505887,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUAaAWAaA5CTBJCTBKCLBRCTBSCTBlCTBmCTBpCTBqCTBxCTByCTCBCTCCCTCVCLCZCTCpAWC6AaC9CKDBD8"),([7,992,1082401,2164802,17318416,32776456,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUA4AWA4A5BmA6DfBJDeBRDfBSDfBiDfBlBkBpDfBqDfBxDfByDfCBDfCKDfCNDfCZDfCaDfCqA4CtDfC1Ds"),([7,992,1082401,2164831,4329604,8659208,32505887],hh "AAAeACAeAEAeAGAeAIAeAKAeAMAeAOAeAQAeASAeAUD5AWD5A5AeA6AeBJARBhAYBiAeBpAeBqAeBxAdCBAeCGAeCJAeCKAeCSAeCZAeCaAeCpAOCqD5CyD5DJD5DKD5"),([7,992,1082401,2164831,4329604,8659231,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAZAWAZA5FYA6FYBJFBBSFYBhFPBiFYBpFYBqFYBxFYCBFYCKFYCaFYCpE5CqAZCyAZDBAZDJD5DKD5"),([7,992,1082401,2164831,4329604,17318416,32505887],hh "AAAeACAeAEAeAGAeAIAeAKAeAMAeAOAeAQAeASAeAUCSAWCSA5AeBJARBKAeBhAYBpAeBqAeBxAdCFAOCGAeCJAeCKAeCSAeCZAeCaAeCpAOCqCSCyCSC9CKDJCSDKCS"),([7,992,1082401,2164831,4329604,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCSAWCSA5FYBJFBBKFYBSFYBhFPBpFYBqFYBxFYCFE5CKFYCaFYCpE5CqCSCyCSDBB2DJCSDKCS"),([7,992,1082401,4329604,8388639,17318416,32505856],hh "AAFGACFGAEFGAGFGAIFGAKFGAMFGAOFGAQFGASFGAUC5AWC5A5FGBJFGBRFGBSFGBhFGBiFGCFEsCJFGCKFGCRFGCSFGCaFGCpE5CqC5CxCyCyC5DKBj")]
theorem k120 : b120.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b121 : List (List Nat × List (Nat × Nat)) := [([7,992,1082401,4329604,8659231,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUAhAWAhA5FYBJFPBRFYBSFYBhFYBiFYBqFYByFYCFE5CKFYCSFYCpE5CqAhCxAgCyAhDCAhDKAj"),([7,992,2164802,4194335,8659208,17318416,32505856],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQArASArAUBOAWBOA5BOBJBOBKBOBhBOBpBOBqBOCCArCFBJCJC5CKArCZAaCaAaCpE9CqBOCxEaC2BOC6BODCBODKBi"),([7,992,2164802,4329631,8659208,17318416,32505887],hh "AAFTACFTAEFTAGFTAIFTAKFTAMFTAOFTAQFTASFTAUBOAWBOA5E_BJFMBKFTBSAcBhFTBpFTBqFTCCFTCFE1CJFTCKFTCZFTCaFTCpE1CqBOC9BODCBODKBS"),([7,992,4329604,8659208,17318416,32505887,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQACASACAUAaAWAaA5ACA6ACBJACBRACBSACBiACBlACBpACBqACBxACByACCBACCCACCNACCpAQCyAaC1AC"),([7,992,4329604,8659208,17318416,32539681,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUBsAWBsA5CHBJDfBKDfBRDfBSDfBlBkBpDfBqDfBxDfByDfCBBmCSDfCVDfCaDfCqBsCtDfC9DfDFDf"),([7,1023,1082401,2164802,4329604,8659208,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUD8AWD8BJALBRALBSALBhALBpALBqALBxALByALCGALCJALCKALCRALCSALCZALCaALDJD6"),([7,1023,1082401,2164802,4329604,8659208,32506848],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUD8AWD8BRBkBSBkBpBkBqBkBxBkByBkCGBkCJBkCKBkCRBkCSBkCZBkCaBkC9BoDBCJDNBk"),([7,1023,1082401,2164802,4329604,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUCTAWCTBJALBKALBRALBSALBhALBpALBqALBxALByALCGALCJALCKALCRALCSALCZALCaALC9A_DJCTDKCT")]
theorem k121 : b121.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b122 : List (List Nat × List (Nat × Nat)) := [([7,1023,1082401,2164802,4329604,17318416,32506848],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUCTAWCTBKBkBRBkBSBkBpBkBqBkBxBkByBkCGBkCJBkCKBkCRBkCSBkCZBkCaBkC9BlDKCTDNBk"),([7,1023,1082401,2164802,4329604,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUALAWALA5FYBJFBBKFYBRFYBSFYBhFPBpFYBqFYBxFYByFYCFE5CGFYCRFYCpEvCqALCyALC9ALDBALDJCTDKCT"),([7,1023,1082401,2164802,8659208,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUBeAWBeA6ALBJALBRALBSALBpALBqALBxALByALCJALCKALCRALCSALCZALCaALC1AMDKA4"),([7,1023,1082401,2164802,8659208,17318416,32506848],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUBeAWBeA6BkBRBkBSBkBpBkBqBkBxBkByBkCJBkCKBkCRBkCSBkCZBkCaBkC1CEDJA4DKA4"),([7,1023,1082401,2164802,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBUAWBUA6FYBRFYBSFYBpFYBqFYBxFYByFYCJFYCpEOCqBUCyBUC1FSDBBUDCBUDJA0DKA0"),([7,1023,1082401,4329604,8659208,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUC5AWC5BJALBRALBSALBiALBpALBqALBxALByALCJALCKALCRALCSALCZALCaALDFALDKCK"),([7,1023,1082401,4329604,8659208,17318416,32506848],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUC5AWC5BRBkBSBkBiBkBpBkBqBkBxBkByBkCJBkCKBkCRBkCSBkCZBkCaBkDFBkDKBhDNBk"),([7,1023,1082401,4329604,8659208,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUALAWALA5FYBJFPBRFYBSFYBhFYBiFYBpFYBqFYBxFYByFYCFE5CZFYCpEtCqALCxALCyALDCALDFFYDKCK")]
theorem k122 : b122.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b123 : List (List Nat × List (Nat × Nat)) := [([7,1023,2164802,4329604,8659208,17318416,32505887],hh "AAALACALAEALAGALAIALAKALAMALAOALAQALASALAUBOAWBOA5ALBJALBKALBRALBSALBpALBqALBxALByALCJALCKALCRALCSALCZALCaALC9ALDKBS"),([7,1023,2164802,4329604,8659208,17318416,32506848],hh "AABkACBkAEBkAGBkAIBkAKBkAMBkAOBkAQBkASBkAUBOAWBOBKBkBRBkBSBkBpBkBqBkBxBkByBkCJBkCKBkCRBkCSBkCZBkCaBkC9BkDKAr"),([7,1023,2164802,4329604,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBGAWBGBKFYBRFYBSFYBpFYBqFYBxFYByFYCRFYCpEOCqBGCxBGC9BGDCBGDKAp"),([7,31744,1015808,1082401,2164802,4329631,8659944,17318416,32505856],hh "BgAA"),([7,31744,1015808,1082401,2165730,4329631,8659208,17318416,32505856],hh "CoAA"),([7,31744,1015808,1082431,2164802,4329604,8659944,17318416,32505856],hh "BgAA"),([7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856],hh "CoAA"),([7,31744,1015808,1083361,2164831,4329604,8659208],hh "AAD5ACD5AED5AGD5AID5AKD5AMD5AOD5AQAkASAkAUD5AWD5A5D5A6D5BJD5BRD5BiDyBqD5CSAkCZCDCpBCCqD1CxBDCyD5C5ArC-D1DCD5DJA4DKCT")]
theorem k123 : b123.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b124 : List (List Nat × List (Nat × Nat)) := [([7,31744,1015808,4329604,8659208,17318431,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUALAWALA5BsA6BsBJBsBRBsBhBsBiBsBpBsBqBsBxBsByBsCCBsCFBsCKBsCNBsCZBsCpB9CxB_DCALDFBs"),([7,31744,1015808,4329604,8659208,17318896,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQACASACAUBGAWBGA5ACA6ACBKACBSACBxACByACCRACC6BGC9AC"),([7,1047552,1082401,2164802,4329604,17318431,32505856],hh "AAEvACEvAEEvAGEvAIEvAKEvAMEvAOEvAQEvASEvAUALAWALA5EvBJEvBKEvBREvBSEvBhEvBpEvBqEvBxEvByEvCCEvCFEvCREtCpFYCqALCyALC9ALDBALDJEO"),([7,1047552,1082401,2164802,8659208,17318896,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUBUAWBUA6EOBREOBSEOBpEOBqEOBxEOByEOCJEOCpFYCqBUC1BGC6BUDBBUDJEw"),([7,1047552,1082401,4329604,8659208,17318431,32505856],hh "AAEtACEtAEEtAGEtAIEtAKEtAMEtAOEtAQEtASEtAUALAWALA5EtBJEtBREtBSEtBhEtBiEtBpEtBqEtBxEtByEtCCEtCFEtCZEtCpFYCqALCxALCyALDCALDFEt"),([7,1047552,2164802,4329604,8659208,17318896,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUBGAWBGBKEOBREOBSEOBpEOBqEOBxEOByEOCREOCpFYCqBGCxBGCyBGC6BGC9EO"),([7,1082401,2164802,4329604,8659208,32505887,32506848],hh "AADRACDRAEDRAGDRAIDRAKDRAMDRAODRAQDRASDRAUAYAWAYA5DRA6DRBJDRBKDRBRDRBSDRBhDRBiDRBpDRBqDRBxDRByDRCZDRCyAOC1DLC5AYC6AWDFDN"),([7,1082401,2164802,4329604,17318416,32505887,32506848],hh "AADRACDRAEDRAGDRAIDRAKDRAMDRAODRAQDRASDRAUAYAWAYA5DRA6DRBJDRBKDRBRDRBSDRBhDRBiDRBpDRBqDRBxDRByDRCNDRCZDRCyAOC1DPC6AWDFEO")]
theorem k124 : b124.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b125 : List (List Nat × List (Nat × Nat)) := [([7,1082401,2164802,4330468,8659208,32505856,32505887],hh "AAAWACAWAEAWAGAWAIAWAKAWAMAWAOAWAQAWASAWAUEOAWEOA5AWA6AWBJATBKASBSANBhAWBiAWBpAWBqAWBxAWB2AWCKAWCRAWCSAWCZAWDBEODKEODNAW"),([7,1082401,2164802,4330468,8659208,32505856,33554400],hh "AACHACCHAECHAGCHAICHAKCHAMCHAOCHAQCHASCHAUFPAWFPA5CHA6CHBJBrBKBmBSCGBhCHBiCHBpCHBqCHBxCHB2CHCCCHCRCHCZCHCaCHC1CIDFCHDKFPDNCH"),([7,1082401,2164802,8659208,17318416,32505887,32506848],hh "AADRACDRAEDRAGDRAIDRAKDRAMDRAODRAQDRASDRAUAYAWAYA5DRA6DRBJDRBKDRBRDRBSDRBhDRBiDRBpDRBqDRBxDRByDRCFDRCtDRCyAODBCb"),([7,1082401,2165730,4329604,17318416,32505856,32505887],hh "AAAQACAQAEAQAGAQAIAQAKAQAMAQAOAQAQAQASAQAUEOAWEOA6ALBJAQBKAQBRANBhAQBiAQBuAQBxAQByAQCKAQCRAQCSAQCZAQDBEODKEODNAQ"),([7,1082401,2165730,4329604,17318416,32505856,33554400],hh "AADeACDeAEDeAGDeAIDeAKDeAMDeAODeAQDeASDeAUFBAWFBA6BkBJDeBKDeBRCGBhDeBiDeBuDeBxDeByDeCCDeCRDeCZDeCaDeC1DgDFDeDKFBDNDe"),([7,1082401,4329604,8659208,17318416,32505887,32506848],hh "AADRACDRAEDRAGDRAIDRAKDRAMDRAODRAQDRASDRAUAYAWAYA5DRA6DRBJDRBKDRBRDRBSDRBhDRBiDRBpDRBqDRBxDRByDRCVDRCyAWC9DSDFEO"),([7,1082401,4329604,8659944,17318416,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUEOAWEOA5AaA6AaBKASBSAWBhAaBiAaBpAaBqAaCBAaCKAaDKEODNAa"),([7,1082401,4329604,8659944,17318416,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUFYAWFYA5DfA6DfBKBmBSCHBhDfBiDfBpDfBqDfCBDfCCDfCSDfCaDfC9DfDFDfDKFYDNDf")]
theorem k125 : b125.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b126 : List (List Nat × List (Nat × Nat)) := [([7,1083361,2164802,4329604,8659208,32505856,32505887],hh "AAASACASAEASAGASAIASAKASAMASAOASAQASASASAUEOAWEOA5ALBJASBKASBRASBSASBhASBmASBpASBqASBxASByASCKASCRASCSASCZASDBEODKEODNAS"),([7,1083361,2164802,4329604,8659208,32505856,33554400],hh "AABmACBmAEBmAGBmAIBmAKBmAMBmAOBmAQBmASBmAUFYAWFYA5BkBJBmBKBmBRBmBSBmBhBmBmBmBpBmBqBmBxBmByBmCCBmCRBmCZBmCaBmC1BnDFBmDKFYDNBm"),([7,1083361,2164802,8659208,17318416,32505856,32505887],hh "AAASACASAEASAGASAIASAKASAMASAOASAQASASASAUEOAWEOA5ALBJASBRASBSASBiASBpASBqASBxASByASCKASCRASCZASDKEODNAS"),([7,1083361,2164802,8659208,17318416,32505856,33554400],hh "AABmACBmAEBmAGBmAIBmAKBmAMBmAOBmAQBmASBmAUFYAWFYA5BkBJBmBRBmBSBmBiBmBpBmBqBmBxBmByBmCCBmCRBmCSBmCZBmCaBmCtDsDKFYDNBm"),([7,2164802,4329604,8659208,17318416,32505887,32506848],hh "AADRACDRAEDRAGDRAIDRAKDRAMDRAODRAQDRASDRAUAYAWAYA5DRA6DRBJDRBKDRBRDRBSDRBhDRBiDRBpDRBqDRBxDRByDRCNDRCqAOCyAWC1DR"),([7,2164802,4330468,8659208,17318416,32505856,32505887],hh "AAATACATAEATAGATAIATAKATAMATAOATAQATASATAUEOAWEOA6AMBJATBKATBRATBhATBiATBqATBxATByATCBATCCATCKATDKEODNAT"),([7,2164802,4330468,8659208,17318416,32505856,33554400],hh "AABrACBrAEBrAGBrAIBrAKBrAMBrAOBrAQBrASBrAUFLAWFLA6BqBJBrBKBrBRBrBhBrBiBrBqBrBxBrByBrCBBrCSBrCaBrC1DfDKFLDNBr"),([8,31,256,992,1082401,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD2AaD2A5FYA6FYBJFYBKFYBSFYBVFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCRFBCZFYCaFYCxFYCyFYC5FPC6FYDBFYDCFYDJFYDKFYDZEODaD2DhD2DiD2DpE5DqD2DyD2EBFv")]
theorem k126 : b126.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b127 : List (List Nat × List (Nat × Nat)) := [([8,31,512,992,1082401,2164802,4329604,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBJFYBKFYBOE5BSFYBVFYBWE5BpFYBqFYBxFYB1E5CCFYCJFYCKFYCRFBCSFYCVFPCZFYCaFYCxFYCyFYC5FPC9FBDBFYDCFYDJFYDKFYDZEODaCTDhCTDiCTDpE5DqCTDtE5DyCTD9CKEBB4"),([8,31,512,31744,1082401,2164802,4329604,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCTAaCTA5E5A6E5BJE5BKE5BOE5BRE5BSE5BWE5BpE5BqE5BxE5B1E5CCE5CJE5CKE5CRE5CSE5CVE5CZE5CaE5CxE5CyE5C5E5C9E5DBE5DCE5DJE5DKE5DZEODaCTDhCTDiCTDpFYDqCTDtE5DyCTD9CKEBB4"),([8,31,512,1082401,2164802,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCaAaCaA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CqE5CuE5CxE5CyE5C2E5C5E5C6E5C-E5DBE5DCE5DGE5DJE5DKE5DOE5DZEODaCaDhCaDiCaDqCaD1CKD5B-EBCaECCaEFE5"),([8,31,512,1082401,2164802,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCTAaCTA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CqE5CuE5CyE5C1E5C2E5C5E5C6E5C-E5DBE5DCE5DGE5DJE5DKE5DOE5DZEODaCTDhCTDiCTDqCTD1CKD5B4EBCTECCTEFE5"),([8,31,512,1082401,2164802,4329604,32505856],hh "ABE5ADE5AFE5AHE5AJE5ALE5ANE5APE5ARE5ATE5AVCTAXCTA7E5A_E5BLE5BPE5BTE5BXE5BjE5BnE5BrE5BvE5BzE5B3E5CDE5CHE5CLE5CPE5CTE5CXE5CbE5CfE5CrCTCvE5CzCTC3E5C7CTC_E5DDCTDHCTDLB4DPCT"),([8,31,512,1082401,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBYAaBYA5E5A6E5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CyE5C1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaBYDhBYDiBYDqBYDtE0D5BYD6BYEBA4ECA4"),([8,31,512,1082401,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCKAaCKA5E5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CqE5CyE5C1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaCKDhCKDiCKDpCKDqCKD6CKD9E5ECCKEFE5"),([8,31,512,2164802,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBJAaBJA5E5A6E5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CyE5C1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaBJDhBJDiBJDpBJD1BJD6BJECAr")]
theorem k127 : b127.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b128 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],hh "EgAA"),([8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],hh "EgAA"),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156],hh "C4AA"),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,9412872],hh "AAEIACEIAEEIAGEIAIEIAKEIAMEIAOEIAQEIASEIAUEIAWEIAYD8AaD8A5EIA6EIBJEIBKEIBREIBSEIBpEIBqEGBxEICBEFCCEICSEICZEICaEICpEECyEHDBEIDCEIDJEIDKEIDaD6DhD8DpD8DqD4DyD8D5D8"),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],hh "EgAA"),([8,31,992,31744,1082401,2164802,4329604,17809936],hh "AADJACDJAEDJAGDJAIDJAKDJAMDJAODJAQDJASDJAUDJAWDJAYCTAaCTA5DJA6DJBJDJBKDJBRDJBSDJBpDJBxDJCBC7CCDJCKC2CSDJCZDJCaDJCpDJDBDJDCDJDJDJDKDJDaCTDpCTDqCTDyCTD5C2"),([8,31,992,31744,1082401,2164802,4329604,32776456],hh "AAFmACFmAEFmAGFmAIFmAKFmAMFmAOFmAQFmASFmAUFmAWFmAYD8AaD8A5FmA6FmBJFmBKFmBOFQBRFmBSFmBWFQBpFmBqFiBxFmB1FQCCFmCJE6CRFQCSFmCVFmCZFmCaFmCxFlCyFkC5FmC9FQDBFmDCFmDJFmDKFmDaD6DhE5DpFYDqD4DtFQDyD8EBA4")]
theorem k128 : b128.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b129 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1082401,2164802,4329604,33047056],hh "AADDACDDAEDDAGDDAIDDAKDDAMDDAODDAQDDASDDAUDDAWDDAYCTAaCTA5DDA6DDBJDDBKDDBODCBRDDBSDDBWDCBpDDBxDDB1DCCCDDCJDDCKCuCRDDCSDDCVDCCZDDCaDDCxC_C5DCC9DDDBDDDCDDDJDDDKDDDaCTDlE5DpFYDqCTDtDCDyCTD9CuEBBe"),([8,31,992,31744,1082401,2164802,8659208,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA4AaA4A5BeA6BeBJBeBKBeBOBeBRBeBSBeBWBeBiBQBpBeBqBeBxBeByBaB1BeCJBeCRBeCVBeCZBeCaBeCxBeC5BeC9BeDBBeDCBeDJBeDKBeDiA4DlBZDpFXDtBfDyA4D1BOEBAKECAK"),([8,31,992,31744,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUA4AWA4AYBeAaBeA5A4A6A4BJA4BKA4BOA4BRA4BSA4BWA4BiAuBpA4BqA2BxA4ByA4B1A4CJA4CRA4CVA4CZA4CaA4CyA4C1A4C5A4C9A4DBA4DCA4DJA4DKA4DhE3DpFWDtA4DyBeD1ArEBAKECAK"),([8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],hh "DoAAEgAA"),([8,31,992,31744,1082401,4329604,8659208,17809936],hh "AAC2ACC2AEC2AGC2AIC2AKC2AMC2AOC2AQC2ASC2AUC2AWC2AYCKAaCKA5C2A6C2BJC2BKC2BRC2BSC2BpC2BxC2CBC2CZC2CaC2CqC2CxC2CyC2C5C2C6C2DBC2DCC2DJC2DKC2DaCKDpCKDqCKDyCKEBCKECCK"),([8,31,992,31744,1082401,4329604,9412872,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUC5AWC5AYEKAaEKA5C5A6C5BJC5BKC5BRC5BSC5BpC5BxC5CBC5CZC5CaC5CqC5CxC5CyC5C5C5C6C5DCC5DaEKDoAADpEKDqEKDxBODyEKD5BeD6EKEBCKECCK"),([8,31,992,31744,2065441,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA4AaA4A5BeA6BeBJBeBKBeBRBeBSBeBiBQBpBXBqBeBxBbByBaCBBeCxBeC5BeDBBeDJBeDKBeDiA4DpA4DxBOD5C5D6A4EBAKECAK"),([8,31,992,31744,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUBsAWBsAYCtAaCtA5BsA6BsBJBsBKBsBOBsBRBsBSBsBWBsBpBsBxBsB1BsCCBsCJBsCKBsCRBsCSBsCVBsCZBsCaBsCqBsC1BsC5BsC6BsC9BsDBBsDCBsDJBsDKBsDhBxDpDlDtBsD6CtD9BsECBO")]
theorem k129 : b129.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b130 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1047552,1082401,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUF5AWF5AYD8AaD8A5D8A6D8BJD8BKD8BRD8BSD8BpD8BqD8BxD8CBD8CCD5CSD0CZD8CaD8CpF5CyF4DBF5DCF5DJCKDKAKDaD6DhD8DmD2DpD8DqD4DxArDyD8D5D8D6D8EBA4ECCT"),([8,31,992,1047552,1082401,2164802,4329604,8659208,17318416,32505856],[]),([8,31,992,1047552,1082401,2164802,4329604,17318416],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4AYCTAaCTA5CTA6CTBJCTBKCTBRCTBSCTBpCTBxCTCBCTCCCSCKCLCSCTCZCTCaCTCpB4DBEDDCEDDJCKDKAKDaCTDmCTDpCTDqCTDxBODyCTD5C5D6CTEBBeECD8"),([8,31,992,1047552,1082401,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA4AaA4A5BeA6BeBJBeBKBeBRBeBSBeBiBQBpBeBqBeBxBeByBaCBBeCZBeCaBeCxBeC5BeDBBeDCBeDJBeDKBeDiA4DpA4DxBODyA4D5C5D6A4EBAKECAK"),([8,31,992,1047552,1082401,4329604,8659208,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUC5AWC5AYCKAaCKA5C5A6C5BJC5BKC5BRC5BSC5BpC5BxC5CBC5CZC5CaC5CqC5CxC5CyC5C5C5C6C5DBC5DCC5DJC5DKC5DaCKDpCKDqCKDxBODyCKD5BeD6D8EBCKECCK"),([8,31,992,1047552,2164802,4329604,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUBOAWBOAYArAaArA5BOA6BOBJBOBKBOBRBOBSBOBhBOCBBOCCBOCKBOCSBOCZBOCaBOCxBOC5BODBBODCBODJBODKBODiArDpArDxC5DyArD5BeD6ArEBAEECAE"),([8,31,992,1048575,1082401,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUF5AWF5AYD8AaD8A5D8A6D8BKD8BND8BSD8BVD8BpD8BqD8BxD8CCD5CJD8CZD8CaD8CxF5CyF4C-FvDBF5DCF5DJCKDKAKDaD6DhD8DmD2DpD8DuD8DxArDyD8D5D8D6D8EBA4ECCT"),([8,31,992,1048575,1082401,2164802,4329604,17318416],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUB4AWB4AYCTAaCTA5CTA6CTBKCTBNCTBSCTBVCTBpCTBxCTCCCSCJCTCKCLCSCKCZCTCaCTCxB4C-B4DBEDDCEDDJCKDKAKDaCTDlCTDmCTDpCTDuCTDxBODyCTD5C5D6CTEBBeECD8")]
theorem k130 : b130.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b131 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1048575,1082401,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA4AaA4A5BeA6BeBKBeBNBeBSBeBVBeBiBQBpBeBqBeBxBeByBOCJBeCZBeCaBeCxBeC5BeC-BeDBBeDCBeDJBeDKBeDiA4DlBYDpBeDuA4DxBODyA4D5C5D6A4EBAKECAK"),([8,31,992,1048575,1082401,4329604,8659208,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUC5AWC5AYCKAaCKA5C5A6C5BKC5BNC5BSC5BVC5BpC5BxC5B2CyCJC5CZC5CaC5CqC5CxC5CyC5C5C5C6C5DBC5DCC5DJC5DKC5DaCKDlCKDpCKDxBODyCKD5BeD6D8EBCKECCK"),([8,31,992,1048575,2164802,4329604,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUBOAWBOAYArAaArA5BOA6BOBKBOBNBOBSBOBVBOBpBOB2BOCCBOCJBOCKBOCSBOCZBOCaBOCxBOC5BODBBODCBODJBODKBODiArDlBJDpBODxC5DyArD5BeD6ArEBAEECAE"),([8,31,992,1048576,2164802,8659208,17318416,32505856],hh "AAFSACFSAEFSAGFSAIFSAKFSAMFSAOFSAQFSASFSAUFSAWFSAYBOAaBOA5FSA6FSBJFSBKFSBRFSBSFSBpE-BxFSByFSCJFSCRFSCSFSCZFSCaFSCyFSC1E0C5FSC6FSDBFSDCFSDJFSDKFSDZBODaBODhE0DiBODqBODtFSD5BOD6BOEBArECAr"),([8,31,992,1082401,2097152,4329604,17318416,32505856],hh "AACKACCKAECKAGCKAICKAKCKAMCKAOCKAQBsASBsAUCKAWCKAYCKAaCKA5CKA6CKBRCKBhCKBiCKBpCKBqCKBxCKByCKCJBsCRAaCSAaCZBsCaBsCqCKC1CKC2CKC5BOC6CKDBCKDCCKDJBeDKD8DZELDaCKDhCKDiCKDqCKDyCKD1CKD5BsD-CKEBCKECCK"),([8,31,992,1082401,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DqD8D5FvEBD8ECD8"),([8,31,992,1082401,2164802,4329604,8659208,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBhAeBiFYBpFBBxFYByFYCBFUCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDaD8DdFYDhE5DiD8DqD8EBD6ECD8"),([8,31,992,1082401,2164802,4329604,8659208,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBxFYByFYCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DiD8DlFYDqD8D1DyD5FuECD8EFFY")]
theorem k131 : b131.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b132 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,8659208,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBKFIBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDaD8DhE5DiD8DqD8DtFYD5FvEBD8ECD8"),([8,31,992,1082401,2164802,4329604,8659208,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCuFQCxFYCyFQC2FYC5FYC6FYC-FQDBFYDCFYDGFQDJFYDKFYDOFQDaD8DhE5DiD8DqD8D5FvEBD8ECD8EFFY"),([8,31,992,1082401,2164802,4329604,8659208,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAaAaAaA5FYA6FYBKBRBRFYBSFYBiFYBpFBBqCsBxFYByFYCCBgCGFXCJFPCKFYCOBeCRFYCSFYCWBeCZFYCaFYCeBeCqFYCuDCCxFYCyDCC2FYC5FYC6FYC-DCDBFYDCFYDGDCDJFYDKFYDNBeDODCDaEfDiFfDlE5DqDnDtBOD1CsD5BeD9BeEBAaECAaEFDC"),([8,31,992,1082401,2164802,4329604,8659231,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD6AaD6A5FYA6FYBJFYBRFYBSFYBhFYBiFYBpFBBxFYByFYCBFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCtFYCxFYC2FYC6FYDBFYDCFYDKFYDZD6DaD6DhE5DiD6DqD6D5FvEBD6ECD6"),([8,31,992,1082401,2164802,4329604,8682760,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYD4AaD4A5FrA6FrBRFrBSFrBiFrBpFCBxFrByFrCJFlCKFrCRFrCSFrCZFrCaFrCqFrCxFrC2FYC6FrDBFrDCFZDKFoDZEODaD4DhE5DiD4DqD4D5FvEBFYECED"),([8,31,992,1082401,2164802,4329604,9741609,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC6FYC9FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DqD8D5FvEBD8ECD8"),([8,31,992,1082401,2164802,4329604,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBpFBBqFYBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFBC2FYC5FYC6FYDCFYDFFYDJFYDKFYDZEODaD8DhE5DiD8DqD8D1D8D5DnEBD8"),([8,31,992,1082401,2164802,4329604,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYCxFPC2FYC5FYC6FYDBFYDCFYDKFYDNFYDZEODaCTDhE5DiCTDqCTD5F5EBCT")]
theorem k132 : b132.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b133 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYCxE5C2FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaCTDhE5DiCTDqCTD1CKD5B4EBFYEGCT"),([8,31,992,1082401,2164802,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDqCTD1CKD5B4EBCTECCT"),([8,31,992,1082401,2164802,4329604,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBhAeBiFYBpFBBqFYBxFYByFYCBFUCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDaCTDdFYDhE5DiCTDqCTD1CLEBCTECCT"),([8,31,992,1082401,2164802,4329604,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBqFYBxFYByFYCRFYCSFYCZFYCaFYCqFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDiCTDlFYDqCTD1CSECCTEFFY"),([8,31,992,1082401,2164802,4329604,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBKFHBRFYBSB7BiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDaCTDhE5DiCTDqCTDtFYD1CKD5AaEBCTECCT"),([8,31,992,1082401,2164802,4329604,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAaAaAaA5FYA6FYBKAxBRFYBSFKBiFYBpFBBqFYBxFYByFYCCA-CGFOCJFPCKFOCOA8CRFYCSFYCWA4CZFYCaFYCeA4CqFYCuFQCyFQC1E5C2FYC5FYC6FYC-FQDBFYDCFYDGFQDJFYDKFYDNA4DOFQDaEeDhE5DiCfDqB4DtArD1CKD5A4D9A4EBAaECAaEFFQ"),([8,31,992,1082401,2164802,4329604,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYCuDCCyDCC1E5C2FYC5FYC6FYC-DCDBFYDCFYDGDCDJFYDKFYDODCDaCTDiCTDlE5DqCTD1CKD5B4EBCTECCTEFFY"),([8,31,992,1082401,2164802,4329604,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBJFYBRFYBhFYBiFYBpFBBqFYBxFYByFYCBFYCJFPCRFYCSFYCZFYCaFYCqFYCtFYC1E5C2FYC6FYDBFYDCFYDKFYDZCTDaCTDhE5DiCTDqCTD1CKD5B4EBCTECCT")]
theorem k133 : b133.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b134 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,17333776,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYCTAaCTA5FrA6FrBRFrBiFrBpFCBqFrBxFrByFrCJFlCRFrCSFrCZFrCaFrCqFrC1E5C2FYC6FrDBFrDCFZDKFoDZEODaCTDhE5DiCTDqCTD1CKD5B4EBFYECED"),([8,31,992,1082401,2164802,4329604,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBSFYBiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC6FYC9FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDqCTD1CKD5DnEBCTECCT"),([8,31,992,1082401,2164802,4329604,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYC1FPC2FYC5FYC6FYDCFYDFFYDJFYDKFYDZEODaCTDhE5DiCTDqCTD5F5EBCT"),([8,31,992,1082401,2164802,4329604,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYC1FBC2FYC5FYC6FYDBFYDCFYDKFYDNFYDZEODaD8DhE5DiD8DqD8D1D8D5B4EBD8"),([8,31,992,1082401,2164802,4329604,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCRFYCSFYCZFYCaFYCqFYC1FYC2FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaD8DhE5DiD8DqD8D5FvEBFYEGD8"),([8,31,992,1082401,2164802,4329604,32505856,32776456],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQF0ASF0AUD8AWD8AYD8AaD8A5D8A6D8BRD8BSD8BiD5BpD8BxD8ByD8CJF0CKFzCRF0CSF0CZCKCaAKCpD8CqD8CuFQCxD8CyD8C2FQC6D8C-FQDCFQDGD8DJFvDKF0DOFQDaD6DhD8DmFYDqD8DyD8D5A4D6CTEBD8ECD8EFD8"),([8,31,992,1082401,2164802,4329604,32505856,33047056],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQB4ASB4AUCTAWCTAYCTAaCTA5CTA6CTBRCTBiCSBpCTBqCLBxCTByCTCJB4CRAaCSAaCZCKCaAKCpCTCqCTCuDCCxCTCyCTC2DCC6CTC-DCDCCTDFCKDGDCDJB4DKDCDOCTDaCTDlCTDmFYDqCTDyCTD1CKD5BeD6D8EBCTECCTEFCT"),([8,31,992,1082401,2164802,4329604,32776456],hh "ABFQADFQAFFQAHFQAJFQALFQANFQAPFQARFQATFQAVD8AXD8A7FQA_FQBLFQBPFQBTFQBXFQBjFQBnFQBrFQBvFQBzFQB3FQCDFQCHFQCLFQCPFQCTFQCXFQCbFQCfFQCrD8CvFQCzD8C3FYC7D8C_FQDDD8DHD8DLFcDPFQ")]
theorem k134 : b134.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b135 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,33047056],hh "ABDCADDCAFDCAHDCAJDCALDCANDCAPDCARDCATDCAVCTAXCTA7DCA_DCBLDCBPDCBTDCBXDCBjDCBnDCBrDCBvDCBzDCB3DCCDDCCHDCCLDCCPDCCTDCCXDCCbDCCfDCCrCTCvDCCzCTC3FYC7CTC_DCDDCTDHDCDLB4DPCT"),([8,31,992,1082401,2164802,4330468,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYA-FPBRFYBSFYBVFPBiFYBpFYBtFPBxFYByFYCJFPCKFYCNFYCRFYCSFYCaFYCqFYCxFYC1FPC2FYC5FYC6FYDBFYDCFYDJFYDOFYDZEODaD8DhD8DiD8DlFPDqD8D5FuEBD8ECD8"),([8,31,992,1082401,2164802,5412005,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBKFYBRFYBSFYBiFYBpFBBxFYByFYCJFPCKFYCSFYCVFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DqD8DtFSD5FvEBD8ECD8"),([8,31,992,1082401,2164802,5412005,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBKFYBRFYBSFYBiFYBpFBBqFYBxFYByFYCJFPCSFYCVFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDqCTDtFSD1CKD5AaEBCTECCT"),([8,31,992,1082401,2164802,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBpFBBxFYByFYCJE5CKFYCRFYCSFYCaFYCdFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DqD8D5FYD-D8EBD8ECD8"),([8,31,992,1082401,2164802,6494406,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBpFBBxFYByFYCJE5CRFYCSFYCaFYCdFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDqCTD5FYD-CTEBCTECCT"),([8,31,992,1082401,2164802,8659208,12988812,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCxFPCyFYC5FYC6FYDBFYDCFYDKFYDNFYDZEODaD8DhE5DiD8DqD8D5D8D6D8EBA4"),([8,31,992,1082401,2164802,8659208,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCxE5CyFYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaD8DhE5DiD8DqD8DtFSD5D8D6D8EBFYEGD8")]
theorem k135 : b135.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b136 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDqBeDtFSD5BeD6BeEBA4ECA4"),([8,31,992,1082401,2164802,8659208,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBhAeBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaBeDdFYDhE5DiBeDqBeDtFSD6BeECA4"),([8,31,992,1082401,2164802,8659208,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDiBeDlFYDqBeDtFSD6BeEBA4ECA4"),([8,31,992,1082401,2164802,8659208,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaBeDhE5DiBeDqBeDtFYD5BeD6BeEBA4ECA4"),([8,31,992,1082401,2164802,8659208,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCCA-CGFOCJFYCKFOCOA8CRFYCSFYCWA4CZFYCaFYCeA4CyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDNA4DaBeDhE5DiBeDqBeDtFSD5BeD6BeD9FYEBAKECAK"),([8,31,992,1082401,2164802,8659208,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYA4AaA4A5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCqBgCuFXCyFYC1E5C2BeC5FYC6FYC-BeDBFYDCFYDGBeDJFYDKFYDOBeDaA4DiA4DlE5DqA4DtFSD5AKD6AKEBA4ECA4EFFY"),([8,31,992,1082401,2164802,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBpFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1FYC5FYC6FYDCFYDKFYDZEODaBeDhBeDiBeDqBeDtFSD5BeD6BeEBA4ECA4"),([8,31,992,1082401,2164802,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C6FYC9FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDqBeD5BeD6BeEBA4ECA4")]
theorem k136 : b136.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b137 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,8659208,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBiFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1FPC5FYC6FYDCFYDFFYDJFYDKFYDZEODaBeDhE5DiBeDqBeDtFSD5BeD6BeEBA4"),([8,31,992,1082401,2164802,8659208,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaBeDhE5DiBeDqBeDtFSD5BeD6BeEBAKECAK"),([8,31,992,1082401,2164802,8659208,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFYBSFYBiFYBpFBBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCyFYC1FPC6FYC9FYDCFYDFFYDKFYDNFYDZEODaBeDhE5DiBeDqBeD5BeD6BeEBFv"),([8,31,992,1082401,2164802,8659208,32505856,32641156],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUD8AWD8AYFvAaFvA5D8A6D8BRD8BSD8BiD5BpD8BxD8ByD8CCD6CJD8COD2CRD8CSD8CZD8CaD8CpD8CqD8CxD8CyD8C6D8DCD8DJD8DKD8DhFvDiFuDqFvDyFYD5CTD6A4ECFvEFD8"),([8,31,992,1082401,2164802,8659208,32505856,33047056],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA4AaA4A5BeA6BeBKBQBRBeBSBeBpBeBxBeByBeCJBeCRBeCSBeCZBeCaBeCpBeCqBeCuBeCxBeCyBeC2BeC6BeC9BOC-BeDCBeDGBeDJBeDKBeDOBeDiA4DlBYDqA4DtBODyA4D5AKD6AKEBA4ECA4EFBe"),([8,31,992,1082401,2164802,8659208,33047056],hh "ABBeADBeAFBeAHBeAJBeALBeANBeAPBeARBeATBeAVA4AXA4A7BeA_BeBLBeBPBeBTBeBXBeBjBeBnBeBrBeBvBeBzBeB3BeCDBeCHBeCLBeCPBeCTBeCXBeCbBeCfBeCrA4CvFXCzA4C3BeC7A4C_BeDDA4DHBeDLAKDPBe"),([8,31,992,1082401,2164802,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFYBpFBBxFYByFYCJFYCSFYCVFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDqBeD5BeD6BeEBA4ECA4"),([8,31,992,1082401,2164802,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBiFYBpFBBqFYBxFYByFYCJFBCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDqBeDtFSD1BeD5BeEBA4ECA4")]
theorem k137 : b137.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b138 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,17318416,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FBC5FYC6FYDBFYDCFYDKFYDNFYDZEODaCTDhE5DiCTDqCTD1CKD5CTD6CTEBBe"),([8,31,992,1082401,2164802,17318416,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaCTDhE5DiCTDqCTDtFSD5CTD6CTEBFYEGCT"),([8,31,992,1082401,2164802,17318416,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYA4AaA4A5FYA6FYBKFYBRFYBSFYBpFBBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaA4DhE5DiA4DqA4DtFSD5A4D6A4EBAKECAK"),([8,31,992,1082401,2164802,17318416,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYA4AaA4A5FYA6FYBRFYBiFYBpFBBqFYBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYC1FPC6FYC9FYDCFYDFFYDKFYDNFYDZEODaA4DhE5DiA4DqA4D1AKD5A4D6A4EBB4"),([8,31,992,1082401,2164802,17318416,32505856,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUCTAWCTAYB4AaB4A5CTA6CTBRCTBiCSBpCTBqCLBxCTByCTCCCTCNCTCOCTCRCTCSCTCZCTCaCTCpCTCqCTCxCTCyCTC6CTDCCTDFCKDJCTDKCTDhB4DqAaDyFYD1CKD5D8D6BeECB4EFCT"),([8,31,992,1082401,2164802,17318416,32505856,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUA4AWA4AYBeAaBeA5A4A6A4BKAuBRA4BSA2BpA4BxA4ByA4CKA4CNA4CRA4CSA4CZA4CaA4CpA4CqA4CuA4CxA4CyA4C2A4C6A4C9ArC-A4DCA4DGA4DJA4DKA4DOA4DhBeDqBeDtArDyBeD5AKD6AKEBBeECBeEFA4"),([8,31,992,1082401,2164802,17318416,32776456],hh "ABA4ADA4AFA4AHA4AJA4ALA4ANA4APA4ARA4ATA4AVBeAXBeA7A4A_A4BLA4BPA4BTA4BXA4BjA4BnA4BrA4BvA4BzA4B3A4CDA4CHA4CLA4CPA4CTA4CXA4CbA4CfA4CrBeCvFOCzBeC3A8C7BeC_A4DDBeDHA4DLAKDPA4"),([8,31,992,1082401,2164831,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD5AaD5A5FYA6FYBJFYBRFYBSFYBiFYBlFYBpFBByFYCBFYCJFPCKFYCRFYCSFYCZFYCpFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZD5DaD5DhE5DiD5DqD5D5FvEBD5ECD5")]
theorem k138 : b138.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b139 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164831,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCSAaCSA5FYA6FYBJFYBRFYBiFYBlFYBpFBBqFYByFYCBFYCJFPCRFYCSFYCZFYCpFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZCSDaCSDhE5DiCSDqCSD1CKD5B2EBCSECCS"),([8,31,992,1082401,2165730,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCLAaCLA5FYA6FYA-FBBRFYBVFBBiFYBpFBBqFYBtFYByFYCJFYCNFBCRFYCSFYCZFYCqFYCxFYC1FBC2FYC5FYC6FYDBFYDGFYDJFYDKFYDZEODaCLDhCLDiCLDlFBDqCLD1CKD5BuEBCLECCL"),([8,31,992,1082401,2194498,4329604,8659208,32505856],hh "AAFZACFZAEFZAGFZAIFZAKFZAMFZAOFZAQFZASFZAUFZAWFZAYD0AaD0A5FZA6FZBRFZBSFZBiFZBpFCByFZCJFPCKFZCRFZCSFZCZFYCqFZCxFZC2FZC5FZC6FZDBFZDCFZDJFZDKFZDZEODaD0DhE5DiD0DqD0D5FvEBD0ECD0"),([8,31,992,1082401,2194498,4329604,17318416,32505856],hh "AAFZACFZAEFZAGFZAIFZAKFZAMFZAOFZAQFZASFZAUFZAWFZAYCTAaCTA5FZA6FZBRFZBiFZBpFCBqFZByFZCJFPCRFZCSFZCZFYCqFZC1E5C2FZC5FZC6FZDBFZDCFZDJFZDKFZDZEODaCTDhE5DiCTDqCTD1CKD5B4EBCTECCT"),([8,31,992,1082401,3247203,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFYBiFYBpFBByFYB1FYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DpD8DqD8D5FvEBD8ECD8"),([8,31,992,1082401,3247203,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBiFYBpFBBqFYByFYB1FYCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDpCTDqCTD1CKD5BsEBCTECCT"),([8,31,992,1082401,3247203,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFYBpFBByFYB1FYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDpBeDqBeD5BeD6BeEBA4ECA4"),([8,31,992,1082401,4329604,6494406,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYF5AaF5A5FYA6FYBRFYBSFYBpFPBxFYByFYCCFYCJE5CRFYCSFYCaFYCdFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaF5DhE5DiF5DqF5D-CKEBF0ECF5")]
theorem k139 : b139.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b140 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,6494406,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCKAaCKA5FYA6FYBRFYBpFPBxFYByFYCCFYCJE5CKFYCRFYCSFYCaFYCdFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCKDhE5DiCKDqCKD9CKD-CKEBCKECCK"),([8,31,992,1082401,4329604,8388608,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCBFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEQDaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,10824010,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYF5AaF5A5FYA6FYBRFYBSFYBpFPBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCxFBC5FYC6FYDBFYDCFYDKFYDNFYDZEODaF5DhE5DiF5DqF5DxFvD6F5D9FY"),([8,31,992,1082401,4329604,8659208,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYF5AaF5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCxE5C6FYC9FYDCFYDFFYDKFYDNFYDZEODaF5DhE5DiF5DpEnDqF5D6F5D9FYEGCK"),([8,31,992,1082401,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBhFUBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaC5DdFYDhE5DiC5DqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DiC5DlFYDqC5D6C5D9FYECC1EFFY"),([8,31,992,1082401,4329604,8659208,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBKFFBOByBRFYBSByBWDkBpFPBxFYByFYB1BsCCFYCJFYCKFYCRFYCSFYCVBsCZFYCaFYCqFYC1E5C5FYC6FYC9BsDBFYDCFYDJFYDKFYDaC5DhE5DiC5DpCqDqC5DtFYD6C5D9FYECCK")]
theorem k140 : b140.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b141 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,8659208,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCKAaCKA5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCyCsC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaCKDiC1DlE5DpCKDqCKD6CKD9FYECCKEFFY"),([8,31,992,1082401,4329604,8659208,17318431,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBJFYBRFYBhFYBpFPBxFYByFYCBFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCtFYC1E5C6FYDCFYDJFYDKFYDZC5DaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,17333776,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYC5AaC5A5FrA6FrBRFrBpFlBxFrByFrCCFrCJFrCKFrCRFrCSFrCZFrCaFrCqFrC1E5C6FrDCFoDJFrDKFrDZEODaC5DhE5DiC5DpCyDqC5D6C5D9FrECED"),([8,31,992,1082401,4329604,8659208,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBSFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C6FYC9FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659208,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1FBC5FYC6FYDCFYDFFYDJFYDKFYDZEODaC5DhE5DiC5DpCyDqC5DxC3D6C5D9FY"),([8,31,992,1082401,4329604,8659208,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaC5DhE5DiC5DpCyDqC5D5C4D6C5ECCK"),([8,31,992,1082401,4329604,8659208,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBSFYBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCqFYC1FBC6FYC9FYDCFYDFFYDKFYDNFYDZEODaC5DhE5DiC5DqC5DxC3D5C4D6C5")]
theorem k141 : b141.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b142 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,8659231,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBJFYBRFYBhFYBpFPBxFYByFYCCFYCFFYCJFYCKFYCSFYCaFYCpFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZC5DaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYA-FYBRFYBVFYBpFYBtFYBxFYByFYCCFYCJFYCKFYCNFYCSFYCaFYCqFYCxFYC1FYC5FYC6FYDBFYDCFYDJFYDZEODaC5DhC5DiC5DlFYDpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,8682760,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYC5AaC5A5FrA6FrBRFrBpFlBxFrByFrCCFrCJFrCKFrCSFrCaFoCqFrC1E5C5FrC6FrDBFrDCFrDJFrDKFrDZEODaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCSFYCVFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DqC5D6C5D9FYECCK"),([8,31,992,1082401,4329604,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCJFPCKFYCRFYCSFYCaFYCdFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DpCyDqC5DxC5D9C5ECCT"),([8,31,992,1082401,4329604,17318416,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1FPC5FYC6FYDBFYDCFYDKFYDNFYDZEODaC5DhE5DiC5DqC5DxC5D6CTEFC5"),([8,31,992,1082401,4329604,17318416,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaC5DhE5DiC5DpCyDqC5D6CKEFC5EGC5"),([8,31,992,1082401,4329604,17318416,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCKAaCKA5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYCqFYCyFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaCKDhE5DiCKDpCKDqCKD5CKD6CKECCKEFFY")]
theorem k142 : b142.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b143 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,17318416,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFYBpFPBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYCqFYCyFYC1FBC6FYC9FYDCFYDFFYDKFYDNFYDZEODaCTDhE5DiCTDqCTDxB4D5CTD6CTEFCK"),([8,31,992,1082401,5412005,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBKFYBRFYBSFYBpFPByFYB1FYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DqC5DtFSD6C5D9FYECCK"),([8,31,992,1082401,8659208,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBKFYBRFYBSFYBiFYBpFYBqFYBxFYByFYCJFBCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDqBeDtFSDyBeD1FYEBAKECAK"),([8,31,992,1082401,8659208,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFYBpFYBxFYByFYCJFPCRFYCSFYCaFYCdFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DpCyDqC5DxC5DyC5ECCK"),([8,31,992,1082401,8659208,17318416,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAKAaAKA5FYA6FYBKFYBRFYBSFYBpFYBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYC1FPC5FYC6FYDBFYDCFYDKFYDNFYDZEODaAKDhE5DiAKDqAKDtFSDxAKDyAKD6AK"),([8,31,992,1082401,8659208,17318416,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCKAaCKA5FYA6FYBRFYBiFYBpFYBqFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FBC5FYC6FYDBFYDCFYDKFYDNFYDZEODaCKDhE5DiCKDpCKDqCKDyCKD1FYD5CKD6CK"),([8,31,992,1082401,8659208,17318416,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAKAaAKA5FYA6FYBRFYBiFYBpFYBqFYBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYC1FPC6FYC9FYDCFYDFFYDKFYDNFYDZEODaAKDhE5DiAKDpAKDqAKDyAKD1FYD6AK"),([8,31,992,1082401,8659208,17318416,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCKAaCKA5FYA6FYBKFYBRFYBSFYBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FBC6FYC9FYDCFYDFFYDKFYDNFYDZEODaCKDhE5DiCKDqCKDtFSDxCKDyCKD5CKD6CK")]
theorem k143 : b143.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b144 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082431,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBQAaBQA5FYA6FYBKFYBNFYBRFYBSFYBhFYBpFBBxFYCBFYCJFYCRFYCZFYCaFYCpFYCyFYC1E5C5FYDBFYDCFYDJFYDKFYDZBQDaBQDhE5DiBQDqBQDtFSD5BQD6BQEBAuECAu"),([8,31,992,1083361,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYA-FYBRFYBSFYBVFYBiFYBpFYBtFYBxFYCJFYCKFYCNFYCRFYCSFYCZFYCaFYCqFYCxFYC1FYC2FYC5FYC-FYDBFYDCFYDJFYDKFYDZEODaD8DhD8DiD8DlFYDqD8D5FtEBD8ECD8"),([8,31,992,1083361,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYA-FYBKFYBRFYBSFYBVFYBpFYBtFYBxFYCJFYCNFYCRFYCZFYCaFYCxFYCyFYC1FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhBeDiBeDlFYDqBeDtFSD5BeD6BeEBA2ECA2"),([8,31,992,1113121,2164802,8659208,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYBaAaBaA5FrA6FrBKFrBRFrBSFrBpFCBxFZCJFrCRFrCZFrCaFrCyFrC1E5C5FrDBFrDCFrDJFrDKFrDZEODaBaDhE5DiBaDqBaDtFSD5BaD6BaEBA4ECA4"),([8,31,992,2164802,3247203,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A5FYA6FYBRFBBpFBBqFYByFYB1FYCJFPCKFYCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaD8DhE5DiD8DpD8D5DnEBD8ECD8"),([8,31,992,2164802,3247203,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA5FYA6FYBRFBBpFBByFYB1FYCJFPCRFYCSFYCZFYCaFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaCTDhE5DiCTDpCTD5B4EBCTECCT"),([8,31,992,2164802,3247203,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFBBiFYBpFBBqFYByFYB1FYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDpBeD1BOD5BeD6BeEBA4ECA4"),([8,31,992,2164802,4194304,8659208,17318416,32505856],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUArAWArAYBOAaBOA5BOA6BOBRBOBhBOBiBOBpBOBqBOBxBOByBOCJBOCRBOCSBOCZBOCaBOCyArC1BJC5C5C6ArDBArDCArDJAEDKAEDZEODaBODhE9DiBODpBODuBODyBOD1BOD6BOECAr")]
theorem k144 : b144.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b145 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,5412005,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYDnAaDnA5FYA6FYBKFYBRFBBiFYBpFPBqFYBxFYByFYCJFPCKFYCRFYCSFYCaFYCdFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaDnDhE5DiDnD1DnEBDnECDn"),([8,31,992,2164802,4329604,5412005,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYB4AaB4A5FYA6FYBKFYBRFBBSFYBiFYBpFPBqFYBxFYByFYCJFPCRFYCSFYCaFYCdFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaB4DhE5DiB4DtBsD1B4EBB4ECB4"),([8,31,992,2164802,4329604,8659208,9741609,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYDnAaDnA5FYA6FYBKFYBRFBBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCxFYCyFYC5FYC6FYDBFYDCFYDKFYDNFYDZEODaDnDhE5DiDnDxDnD6DnECAr"),([8,31,992,2164802,4329604,8659208,16236015,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYDnAaDnA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCxE5CyFYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaDnDhE5DiDnDpDnD1DnD6DnEGDn"),([8,31,992,2164802,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODpBOD1BOD6BOECAr"),([8,31,992,2164802,4329604,8659208,17318416,32505887],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBJAeBRFBBhFUBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaBODdFYDhE5DiBOD1BOD6BOECBS"),([8,31,992,2164802,4329604,8659208,17318416,32506848],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBiFYBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODiBODlFYD1BOD6BOECAr"),([8,31,992,2164802,4329604,8659208,17318416,32539681],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAaAaAaA5FYA6FYBKFFBOByBRFBBSByBWDkBiFYBpFPBqFYBxFYByFYB1BsCCFHCJFYCKB7CRFYCSFYCVBsCZFYCaFYCqFICyFYC1E5C5FYC6FYC9BsDBFYDCFYDJFYDKFYDaBPDhE5DiCfDpBsDtBsD1BdD6ArD9B4ECBOEFDn")]
theorem k145 : b145.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b146 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,8659208,17318416,32776456],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCCAxCJFYCKFKCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaBODhE5DiBODpBOD1BOD6BOD9FYECAE"),([8,31,992,2164802,4329604,8659208,17318416,33047056],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYArAaArA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCqBRCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDaBSDiArDlE5DpArD1ArD6AEECArEFFY"),([8,31,992,2164802,4329604,8659208,17318896,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFYBiFYBpFYBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1FYC6FYDBFYDCFYDKFYDZEODaBODhBODiBODpBOD1BOD6BOECAr"),([8,31,992,2164802,4329604,8659208,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBKFYBRFBBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1FPC6FYC9FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBOD1BOD6BO"),([8,31,992,2164802,4329604,8659208,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCyFYC1FBC5FYC6FYDCFYDFFYDJFYDKFYDZEODaBODhE5DiBODpBODxBOD6BO"),([8,31,992,2164802,4329604,8659208,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaBODhE5DiBODpBOD1BOD5BOD6BOECAE"),([8,31,992,2164802,4329604,8659208,32472030,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBKFYBRFBBpFPBqFYBxFYByFYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCyFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaBODhE5DiBODxBOD5BOD6BOEGBO"),([8,31,992,2164802,4329604,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBKFYBRFBBSFYBiFYBpFPBqFYBxFYByFYCJFBCSFYCVFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODtBOD1BOECAr")]
theorem k146 : b146.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b147 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBpFPBxFYByFYCJFPCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODpBODxBOECAr"),([8,31,992,2164802,4329604,17318416,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYB4AaB4A5FYA6FYBKFYBRFBBSFYBpFPBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaB4DhE5DiB4DtBsDxB4D6B4ECBO"),([8,31,992,2164802,4329604,17318416,24895223,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYB4AaB4A5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaB4DhE5DiB4DpB4D1B4D6B4EGB4"),([8,31,992,2164802,4329604,17318416,25977624,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYArAaArA5FYA6FYBRFBBiFYBpFPBqFYBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaArDhE5DiArDpArD1ArD5ArD6ArECAE"),([8,31,992,2164802,4329604,17318416,32472030,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYArAaArA5FYA6FYBKFYBRFBBSFYBpFPBxFYByFYCCFYCNE5COFYCRFYCSFYCZFYCaFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaArDhE5DiArDtAEDxArD5ArD6ArEGAr"),([8,31,992,2164802,4329631,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBJFYBRFBBiFYBlFYBpFPBqFYByFYCBFYCJFYCRFYCSFYCZFYCpFYCyFYC1E5C5FYC6FYDBFYDJFYDKFYDZBODaBODhE5DiBODpBOD1BOD6BOECAr"),([8,31,992,2164802,4330468,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYA-FLBRFYBVFLBiFYBpFLBqFYBtFYByFYCJFYCNFLCRFYCSFYCZFYCxFYCyFYC1FLC5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhBODiBODlFLDpBOD1BOD6BOECAr"),([8,31,992,2164802,4357252,8659208,17318416,32505856],hh "AAFnACFnAEFnAGFnAIFnAKFnAMFnAOFnAQFnASFnAUFnAWFnAYBOAaBOA5FnA6FnBRE-BiFnBpFlBqFnByFSCJFnCRFnCSFnCZFnCyFnC1E5C5FnC6FnDBFnDJFnDKFnDZEODaBODhE5DiBODpBOD1BOD6BOECAr")]
theorem k147 : b147.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b148 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,6494406,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBiFYBpE5BqFYByFYB1FYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBOD1BOD2BOD6BOECAr"),([8,31,992,2164802,8659208,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFBBpFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBeDhE5DiBeDyBeD6BeD9FSEBArECAr"),([8,31,992,2164802,8659208,12988812,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBpFYBxFYByFYCCFYCJFPCKFYCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODpBODxBODyBOD9BOECA4"),([8,31,992,2164802,8659208,17318416,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaBODhE5DiBODxBODyBOD6A4ECBOEFFS"),([8,31,992,2164802,8659208,17318416,21648020,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFBBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1FBC5FYC6FYDBFYDCFYDKFYDNFYDZEODaBeDhE5DiBeDpBeDyBeD5ArD6ArEFBO"),([8,31,992,2164802,8659208,17318416,29224827,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFBBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1FPC6FYC9FYDCFYDFFYDKFYDNFYDZEODaBODhE5DiBODpBODyBOD6ArEFBO"),([8,31,992,2164802,8659208,17318416,32472030,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA5FYA6FYBRFBBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYCqFYCyFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaBeDhE5DiBeDxBeDyBeD5A4D6A4EFBOEGBe"),([8,31,992,4329604,5412005,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBKFYBRFPBSFYBpFPByFYB1FYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DtC5DxCyD6C5D9FYECBs")]
theorem k148 : b148.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b149 : List (List Nat × List (Nat × Nat)) := [([8,31,992,4329604,6494406,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBRFPBpE5ByFYB1FYCJFYCRFYCSFYCZFYCaFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODxEdD2BOD6BOECAr"),([8,31,992,4329604,8659208,9741609,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A5FYA6FYBRFPBpFYBxFYByFYCJFYCRFYCSFYCaFYCdFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaC5DhE5DiC5DyC5D5CyD6C5ECBs"),([8,31,992,4329604,8659208,10824010,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA5FYA6FYBKFYBRFPBSFYBiFYBpFYBqFYBxFYByFYCJFBCRFYCSFYCaFYCdFYCyFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZEODaBODhE5DiBODtBODyBOD1FYD5BOECAE"),([8,31,992,4329604,8659208,17318416,18400817,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBsAaBsA5FYA6FYBRFPBiFYBpFYBqFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1E5C5FYC6FYDBFYDCFYDKFYDNFYDZEODaBsDhE5DiBsDyBsD1FYD6BsEBBOECBO"),([8,31,992,4329604,8659208,17318416,19483218,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAEAaAEA5FYA6FYBKFYBRFPBSFYBpFYBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYC1FPC5FYC6FYDBFYDCFYDKFYDNFYDZEODaAEDhE5DiAEDtAEDyAED6AEEBCy"),([8,31,992,4329604,8659208,17318416,31389629,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBsAaBsA5FYA6FYBKFYBRFPBSFYBpFYBxFYByFYCKFYCNE5CRFYCSFYCZFYCaFYC1FBC6FYC9FYDCFYDFFYDKFYDNFYDZEODaBsDhE5DiBsDtBsDyBsD6BsEBBO"),([8,31,992,4329604,8659208,17318416,32472030,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAEAaAEA5FYA6FYBRFPBiFYBpFYBqFYBxFYByFYCCFYCNE5CRFYCSFYCZFYCaFYC1FYC6FYC9FYDCFYDFFYDKFYDNFYDZEODaAEDhE5DiAEDyAED1FYD6AEEBEdEGAE"),([8,31,992,4329604,8659208,17318416,32505856,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUBsAWBsAYCyAaCyA5BsA6BsBRBsBiBsBpBsBqBsBxBsByBsCCBsCNBsCRBsCSBsCZBsCaBsCpBsCqBsCuBsCxBsCyBsC2BsC6BsC-BsDCBsDFBsDGBsDKBsDOBsDhCyDqCyDyCyD1BsD6BOEBCqECCyEFBs")]
theorem k149 : b149.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b150 : List (List Nat × List (Nat × Nat)) := [([8,31,992,4329604,8659208,17318416,32505856,32573506],hh "AAAEACAEAEAEAGAEAIAEAKAEAMAEAOAEAQAEASAEAUAEAWAEAYBOAaBOA5AEA6AEBKAEBRAEBSAEBpAEBxAEByAECKAECNAECRAECSAECZAECaAECpAECqAECxAECyAEC6AEC9AEDCAEDKAEDhBODqEdDtAEDyBOD6CyECBOEFAE"),([8,31,992,4329604,8659208,17318416,32539681],hh "ABBsADBsAFBsAHBsAJBsALBsANBsAPBsARBsATBsAVCqAXCqA7BsA_BsBLBsBPBsBTBsBXBsBjBsBnBsBrBsBvBsBzBsB3BsCDBsCHBsCLBsCPBsCTBsCXBsCbBsCfBsCrCqCvByCzCqC3DkC7CqC_BsDDCqDHBsDLCKDPBs"),([8,31,1023,1082401,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A6FYA9FYBRFYBiFYBpFBBxFYByFYCJFPCRFYCSFYCZFYCaFYCqFYCxFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZD8DaD8DhE5DiD8DqD8D5FvEBD8ECD8"),([8,31,1023,1082401,2164802,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA6FYA9FYBRFYBiFYBpFBBqFYBxFYByFYCJFPCRFYCSFYCZFYCaFYCpFYCqFYC1E5C2FYC5FYC6FYDBFYDCFYDJFYDKFYDZCTDaCTDhE5DiCTDqCTD1CKD5B4EBCTECCT"),([8,31,1023,1082401,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA6FYA9FYBKFYBRFYBSFYBpFBBxFYByFYCJFYCRFYCSFYCZFYCaFYCpFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZBeDaBeDhE5DiBeDqBeDtFSD5BeD6BeEBA4ECA4"),([8,31,1023,1082401,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A6FYA9FYBRFYBpFPBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCpFYCqFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZC5DaC5DhE5DiC5DpCyDqC5D6C5D9FYECCK"),([8,31,1023,2164802,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA6FYA9FYBRFBBiFYBpFPBqFYBxFYByFYCJFYCRFYCSFYCZFYCaFYCpFYC1E5C5FYC6FYDBFYDCFYDJFYDKFYDZBODaBODhE5DiBODpBOD1BOD6BOECAr"),([8,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856],hh "CIAA")]
theorem k150 : b150.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b151 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,1015808,1082401,2164802,4329604,32776456],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYD8AaD8A5E5A6E5BJE5BKE5BRE5BSE5BpE5BxE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CxE5C5E5DBE5DCE5DJE5DKE5DaD6DhFYDiD4DpFrDqD8DyD8EBA4"),([8,31,31744,1015808,1082401,2164802,17318416,32776456],hh "AAA4ACA4AEA4AGA4AIA4AKA4AMA4AOA4AQA4ASA4AUA4AWA4AYBeAaBeA5A4A6A4BJA4BKA4BRA4BSA4BiAuBpA4BqA4BxA4ByA4CJA4CRA4CZA4CaA4CpA1C1A4C9A4DBA4DCA4DJA4DKA4DhFVDpFqDyBeD1ArEBAK"),([8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856],hh "DgAA"),([8,31,31744,1015808,1082401,4329604,8659944,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUC5AWC5AYCfAaCfA5C5A6C5BJC5BKC5BRC5BSC5BpC5BxC5CBC5CZC5CaC5CqC5CxC5CyC5C5C5C6C5DCC5DaCfDhCfDiCfDpCfDqCfDxBODyCfD5BeD6Cf"),([8,31,31744,1015808,1083361,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUF3AWF3AYD8AaD8A5D8A6D8BJD8BKD8BRD8BSD8BpD8BxD8CBD8CCD5CKD0CSD8CpCFDCF3DJCKDKAKDaD6DhD8DiD4DpD8DqD8DxArD2D2D5D8D6D8EBA4ECCT"),([8,31,31744,1015808,1083361,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYA2AaA2A5BeA6BeBJBeBKBeBRBeBSBeBiBQBpBeBqBaBxBeByBeCBBeCxBeC5BeDBBeDJBeDKBeDhA2DpA2DyA2D5C5D6A2EBAIECAI"),([8,31,31744,1015808,4329604,8659208,17318416,32539681],hh "AABsACBsAEBsAGBsAIBsAKBsAMBsAOBsAQBsASBsAUBsAWBsAYClAaClA5BsA6BsBJBsBKBsBRBsBSBsBpBsBxBsCCBsCJBsCKBsCRBsCSBsCZBsCaBsCpBsCqBsCyBsC1BsC6BsC9BsDBBsDCBsDJBsDKBsDhB9DpB_D6ClD9Bs"),([8,31,31744,1082401,2164802,4329604,9412872,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYD8AaD8A5E5A6E5BRE5BiE5BpE5BqE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CqE5CxE5CyE5C6E5DBE5DCE5DKE5DZEODaD8DhFYDiD8DqD8D5FvEBFrECEK")]
theorem k151 : b151.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b152 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,1082401,2164802,4330468,8659208,32505856],hh "AAFlACFlAEFlAGFlAIFlAKFlAMFlAOFlAQFlASFlAUFlAWFlAYCeAaCeA5FlA6FlA-FPBRFlBVFPBiFlBpFPBqFlBtFlBxFlByFlCJFlCNFPCRFjCSFlCaE5CqFlCxFlCyFlC1FPC5FlC6FlDBFlDCFlDJFlDOFlDZEODaCeDhFYDiCeDlFPDqCeD5E5EBCeECCe"),([8,31,31744,1082401,2165730,4329604,17318416,32505856],hh "AAFCACFCAEFCAGFCAIFCAKFCAMFCAOFCAQFCASFCAUFCAWFCAYCLAaCLA5FCA6FCA-FBBRFCBVFBBiFCBpFCBqFCBtFBByFCCJFBCNFCCRFCCSFCCZE5CqFCCxFCCyFCC1FBC5FCC6FCDGFCDJFCDKFCDZEODaCLDhFYDiCLDlFBDqCLD5BuEBCLECCL"),([8,31,31744,1082401,3115074,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYD8AaD8A5E5A6E5BRE5BiE5BpE5BqE5ByE5CJE5CRE5CSE5CZE5CqE5CwAACxE5CyE5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaD8DhFYDiD8DqD8D5FvEBD8ECD8"),([8,31,31744,1082401,3115074,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCTAaCTA5E5A6E5BRE5BiE5BpE5BqE5ByE5CJE5CRE5CSE5CZE5CpExCqE5CyE5C1E5C5E5C6E5DCE5DJE5DKE5DZEODaCTDhFYDiCTDqCTD5FxEBFs"),([8,31,31744,1082401,4329604,8659944,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYC5AaC5A5FrA6FrA-FYBRFrBVFYBpFoBtFZBxFrByFrCCFrCJFrCKFrCNFYCSFrCaFlCqFrCxFrCyFrC1FYC5FrC6FrDBFrDCFrDZEODaC5DhFYDiC5DlFYDpCyDqC5D6C5ECDd"),([8,31,31744,1082401,4329604,9412872,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYC5AaC5A5E5A6E5BRE5BpE5BxE5ByE5CCE5CJE5CKE5CSE5CaE5CpExCqE5CyE5C1E5C5E5C6E5DBE5DCE5DKE5DZEODaC5DhFYDiC5DpCyDqC5D6C5"),([8,31,31744,1083361,2164802,4329604,8659208,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYD8AaD8A5FrA6FrA-FYBRFrBVFYBiFrBpFZBqFrBtFoBxFCCJFoCNFZCRFlCSFrCZFrCaFrCqFrCxFrCyFrC1FYC5FrC-FrDBFrDCFrDJFrDKFrDZEODaD8DhFYDiD8DlFYDqD8D5FtEBD8ECD8"),([8,31,31744,1083361,2164802,8659208,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYBeAaBeA5FrA6FrA-FYBKFrBRFrBSFrBVFYBpFZBtFoBxFCCJFrCNFYCRFrCZFrCaFrCxFrC1FYC6FrDBFrDCFrDJFrDKFrDZEODaBeDhFYDiBeDlFYDqBeD5BeD6BeEBA2ECA2")]
theorem k152 : b152.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b153 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,2065441,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBXAaBXA5E5A6E5BKE5BRE5BSE5BpE5BxE5CJE5CRE5CZE5CaE5CpExC1E5DBE5DCE5DJE5DKE5DZEODaBXDhFYDiBXDqBXD5BXD6BXEBEh"),([8,31,31744,2164802,4330468,8659208,17318416,32505856],hh "AAFjACFjAEFjAGFjAIFjAKFjAMFjAOFjAQFjASFjAUFjAWFjAYBOAaBOA5FjA6FjA-FLBRFLBVFjBiFjBpFjBqFjBtFLByE0CJFjCNFLCRFjCSFjCZFjCxFjC1FLC5FjC6FjDCFjDJFjDKFjDZEODaBODhFYDiBODlFLDpBOD6BOECDY"),([8,31,31744,2164802,5214340,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBNAaBNA5E5A6E5BRE5BiE5BpE5BqE5ByE5CJE5CRE5CSE5CZE5CpExC1E5C5E5C6E5DJE5DKE5DZEODaBNDhFYDiBNDpBND6BN"),([8,31,1047552,1082401,2164802,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYD8AaD8A5E5A6E5BRE5BiE5BpE5BqE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CqE5CxE5CyE5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaD8DhFYDiD8DqD8D5FvEBD8ECD8"),([8,31,1047552,1082401,2164802,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYCTAaCTA5E5A6E5BRE5BiE5BpE5BqE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CpExCqE5CyE5C1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaCTDhFYDiCTDqCTD1CKD5B4EBCT"),([8,31,1047552,1082401,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBeAaBeA5E5A6E5BKE5BRE5BSE5BpE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CpExC1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaBeDhFYDiBeDqBeDtE0D5BeD6BeEBA4"),([8,31,1047552,1082401,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYC5AaC5A5E5A6E5BRE5BpE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpExCqE5CyE5C1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaC5DhFYDiC5DpCyDqC5D6C5D9E5"),([8,31,1047552,2164802,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYBOAaBOA5E5A6E5BRE5BiE5BpE5BqE5BxE5ByE5CJE5CRE5CSE5CZE5CaE5CpExC1E5C5E5C6E5DBE5DCE5DJE5DKE5DZEODaBODhFYDiBODpBOD1E9D6BO")]
theorem k153 : b153.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b154 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,1083361,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A6FYA-FYBKFYBRFYBSFYBVFYBiFYBpFYBqFYBtFYBxFBCJFYCKFYCNFYCRFPCSFYCZFYCaFYCqFYCxFYCyFYC1FYC5FYC-FYDBFYDCFYDJFYDKFYDZEODaD8DhD8DiD8DlFYDpE5DqD8D5FvEBD8ECD8"),([8,31,1082401,1083361,2164802,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA6FYBKFYBSFYBVFYBiFYBpFYBqFYBxFBByFYCJFYCKFYCRFPCZFYCaFYCqFYCxFYCyFYC9E5C-FYDBFYDCFYDJFYDKFYDZEODaCTDhCTDiCTDpE5DqCTD1CKD5ASEBCTECCT"),([8,31,1082401,1083361,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA6FYA-FYBKFYBRFYBSFYBVFYBpFYBqFYBtFYBxFBCJFYCKFYCNFYCRFYCZFYCaFYCxFYCyFYC1FYC6FYC9E5DBFYDCFYDJFYDKFYDZEODaBeDhBeDiBeDlFYDpE5DqBeD5BeD6BeEBA4ECA4"),([8,31,1082401,1083361,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A6FYBKFYBSFYBVFYBpFYBqFYBxFPCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCxFYCyFYC9E5DBFYDCFYDJFYDKFYDZEODaC5DhC5DiC5DpE5DqC5D6C5D9FYECCK"),([8,31,1082401,2164802,2165730,4329604,8659208,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUFBAWFBAYD8AaD8BKFBBRFBBSFBBiFBBpFBBqFBByFBB1FBCJFBCKFBCRFBCSFBCZE5CaFBCqFBCxFBCyFBC5FBC6FBDBFBDGFBDJFBDKFBDZEODaD8DiD8DpD8DxE5D5DnEBD8ECD8"),([8,31,1082401,2164802,2165730,4329604,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUFBAWFBAYCTAaCTBKFBBOFBBRFBBSFBBWFBBiFBBqFBBxFBByFBB1FBCJFBCKFBCRFBCSFBCVFBCZE5CqFBCxFBCyFBC5FBC6FBC9FBDFE5DGFBDJFBDKFBDZEODaCTDiCTDpCTDtCLDxE5D5B4EBCTECCT"),([8,31,1082401,2164802,2165730,8659208,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUFBAWFBAYBeAaBeA6FBBKFBBRFBBSFBBiFBBpFBBqFBByFBB1FBCJFBCKFBCRFBCSFBCZFBCxFBCyFBC5FBC6FBDCFBDFE5DJFBDKFBDZEODaBeDiBeDlE-DpBeDxE5D5BeD6BeEBA4ECA4"),([8,31,1082401,2164802,4329604,4330468,8659208,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFPAWFPAYF5AaF5BKFPBRFPBSFPBiFPBmFPBpFPBqFPBuFPBxFPByFPB2FPCCFPCJFPCKFPCSE5CZFPCaFPCdFPCqFPCxFPCyFPC5FPC6FPDBFPDCFPDFFPDJFPDOFPDZEODaF5DiF5DxF5D1CaD5E5EBF0ECF5")]
theorem k154 : b154.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b155 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,2164802,4329604,4330468,17318416,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFPAWFPAYB4AaB4BKFPBRFPBSFPBiFPBpFPBqFPBxFPByFPCCFPCKFPCRFPCSE5CaFPCdFPCqFPCxFPCyFPC5FPC6FPDBFPDCFPDNE5DOFPDZEODaB4DiAWDtBsDxB4D5E5EBB4ECB4"),([8,31,1082401,2164802,4329604,8659208,8659944,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8BKFYBRFYBSFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCqFYCxFYCyFYC6FBDBFYDCFPDKFYDNFYDZEODaD8DiD8DxFvD5D8D6D8EBE5ECCf"),([8,31,1082401,2164802,4329604,8659208,32505856,32506848],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUD8AWD8AYE5AaE5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpD8CqD8CyD8DBFvDJD8DKD8DZBkDaE5DiE5DqE5DtE5DxE5DyE5D6E5D9E5ECE5EFD8"),([8,31,1082401,2164802,4329604,8659208,32505856,33553439],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUD8AWD8AYFYAaFYBKFYBRFYBSFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCpEOCqD8CyD8DBFvDJD8DKD8DaFYDdFYDiFYDlFYDqFBDyFPD1FYD5FYD6FYECFYEFD8"),([8,31,1082401,2164802,4329604,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYAaAaAaA6FYBKFYBOFYBRFYBSFYBWFYBiFYBpFYBqFYBxFYByFYB1FYCCFYCKFYCNFYCRFYCSFBCVFYCaFPCdFYCqFYCxFYCyFYC5FYC6FYC9FYDBFYDCFYDNE5DOFYDZEODaBEDhDGDiAaDpDKDtCKDxAaD5E5D6CfEBAaECAa"),([8,31,1082401,2164802,4329604,17318416,32505856,32506848],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUCTAWCTAYE5AaE5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpCTCqCTCyCTC9CKDBB4DJCTDZBkDaE5DiE5DqE5DtE5DyE5D9E5D-E5ECE5EFCT"),([8,31,1082401,2164802,4329604,17318416,32505856,33553439],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUCTAWCTAYFYAaFYBKFYBRFYBSFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCpEOCqCTCyCTC9CKDBB4DJCTDKCTDaFYDdFYDiFYDqFBDtFYDyFPD5FYD-E5ECFYEFCT"),([8,31,1082401,2164802,4330468,8659208,17318416,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFPAWFPAYAWAaAWA6FPA-FLBKFPBRFPBSFPBVFLBiFPBpFLBqFPBtFPByE5B1FPCCFPCJFPCKFPCNFLCRFPCSFPCZFPCeFPCqFPCuFPCxFPCyFPC1FLC2FPC5FPC6FPC-FPDCFPDFE5DGFPDJFPDKFPDOFPDZEODaBEDhDTDiAWDlFLDpDUDxE5D5FzD6AWEBF4ECAWEFFP")]
theorem k155 : b155.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b156 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,2164802,4330468,8659208,32505856],hh "ABFPADFPAFFPAHFPAJFPALFPANFPAPFPARFPATFPAVCaAXCaA7FPA_FPBLFPBPFPBTFPBXFPBjFPBnFPBrFPBvFPBzFPB3FPCDFPCHFPCLFPCPFPCTFPCXFPCbFPCfFPCrCaCvFPCzCaC3FPC7CaC_CaDDF4DHCaDLCaDPFP"),([8,31,1082401,2164802,8659208,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA6FYBRFYBSFYBiFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCSFBCaFYCdFYCxFYCyFYC5FYC6FYDBFYDCFYDKFYDNE5DZEODaBeDiBeDlFSDxBeDyBeD5E5D6BeEBAKECAK"),([8,31,1082401,2164802,8659208,17318416,32505856,32506848],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBeAWBeAYE5AaE5A6E5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpBeCqBeCyBeC1E0DBBeDCBeDJA4DZBkDaE5DiE5DlE5DqE5DyE5D5E5D-E5ECE5EFBe"),([8,31,1082401,2164802,8659208,17318416,32505856,33553439],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBeAWBeAYFYAaFYA6FYBRFYBSFYBpFYBqFYBxFYByFYCJFYCKFYCRFYCSFYCZFYCaFYCpEOCqBeCyBeC1FSDBBeDCBeDJA4DKA4DaFYDdFYDiFYDlFYDqFBDyFYD9FYD-E5ECFYEFBe"),([8,31,1082401,2165730,4329604,8659208,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUFBAWFBAYAQAaAQA6FBBKFBBSFBBVFBBiFBBpFBBqFBBxE5B2FBCCFBCGFBCJFBCKFBCOFBCRFBCSFBCWFBCZFBCaFBCeFBCqFBCxFBCyFBC9E5C-FBDBFBDCFBDJFBDKFBDNFBDZEODaBEDhCyDiAQDpE5DxAQD5AQD6AQD9FBEBAQECAQ"),([8,31,1082401,2165730,4329604,17318416,32505856],hh "ABFBADFBAFFBAHFBAJFBALFBANFBAPFBARFBATFBAVCLAXCLA7FBA_FBBLFBBPFBBTFBBXFBBjFBBnFBBrFBBvFBBzFBB3FBCDFBCHFBCLFBCPFBCTFBCXFBCbFBCfFBCrCLCvFBCzCLC3FBC7CLC_CLDDBuDHCLDLCLDPFB"),([8,31,1082401,4329604,4330468,8659208,17318416,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFPAWFPAYC5AaC5BKFPBRFPBSFPBiFPBqFPByFPB1FPCCFPCJFPCKFPCRFPCSFPCZFPCaFPCqFPCxFPCyFPC5FPC6FPDFE5DJFPDKFPDZEODaC5DhCyDiC5DpC5DxE5D6C5D9FPECBs"),([8,31,1082401,4329604,8659208,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5BRFYBSFYBiFYBmFYBpFYBqFYBuFYBxFYByFYB2FYCCFYCKFYCSFPCZFYCaFYCdFYCqFYCxFYCyFYC5FYC6FYDBFYDCFYDFFYDNE5DZEODaC5DhCyDiC5DxC5DyC5D1FYD5E5D6C5ECCK")]
theorem k156 : b156.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b157 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,4329604,8659208,17318416,32505856,32506848],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUC5AWC5AYE5AaE5BRE5BSE5BiE5BpE5BqE5BxE5ByE5CCE5CJE5CKE5CRE5CSE5CZE5CaE5CpC5CqC5CxCyCyC5DCC5DFE5DZBkDaE5DiE5DqE5DyE5D1E5D9E5D-E5ECE5EFC5"),([8,31,1082401,4329604,8659208,17318416,32505856,33553439],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUC5AWC5AYFYAaFYBRFYBSFYBiFYBpFYBqFYBxFYByFYCCFYCJFYCKFYCRFYCSFYCZFYCaFYCpEOCqC5CxCyCyC5DCC5DFFYDKCKDaFYDdFYDiFYDqFPDyFYD1FYD-E5ECFYEFC5"),([8,31,1082401,4329604,8659944,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVC5AXC5A7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrC5CvFYCzC5C3FYC7C5C_C5DDC5DHFYDLDVDPFY"),([8,31,1083361,2164802,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYASAaASA6FYBKFYBRFBBWFYBiFYBmFYBpFPBqFYBuFYBxFYByFYB2FYCCFYCJFYCOFYCRFYCSFYCZFYCaFYCdFYCqFYCuFYCyFYC1E5C2FYC5FYC6FYC-FYDBFYDCFYDFFYDGFYDJFYDKFYDOFYDZEODaBEDhE5DiCfDpASDxFtD1BeD5FyD6ASEBF3ECASEFFY"),([8,31,1083361,2164802,4329604,8659208,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVD8AXD8A7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrD8CvFYCzD8C3FYC7D8C_D8DDF3DHD8DLD8DPFY"),([8,31,1083361,2164802,8659208,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVBeAXBeA7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrBeCvFYCzBeC3FYC7BeC_BeDDBeDHFYDLA2DPFY"),([8,31,2164802,2165730,4329604,8659208,17318416,32505856],hh "AAFBACFBAEFBAGFBAIFBAKFBAMFBAOFBAQFBASFBAUFBAWFBAYBOAaBOA6FBBKFBBSFBBVFBBiFBBpFBBqFBBxE5ByFBCJFBCKFBCRFBCZFBCaFBCxFBCyFBC6FBC9E5DBFBDCFBDJFBDKFBDZEODaBODhBODpE5D1BOD6BOECAr"),([8,31,2164802,4329604,4330468,8659208,17318416,32505856],hh "AAFPACFPAEFPAGFPAIFPAKFPAMFPAOFPAQFPASFPAUFPAWFPAYBOAaBOBKFPBOFLBRFPBSFPBWFLBiFPBqE5BxFLByFPB1FPCJFPCKFPCRFPCSFPCVFLCZFPCxFPCyFPC5FPC6FPC9FLDCFPDFE5DJFPDKFPDZEODaBODhBODpBODtBODxE5D6BOECAr")]
theorem k157 : b157.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b158 : List (List Nat × List (Nat × Nat)) := [([8,31,2164802,4329604,8659208,8659944,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOBKFYBRFYBSFYBiFYBpFYBqFYBxFYByFYCCFYCKFBCRFYCSFPCaFYCdFYCxFYCyFYC5FYC6FYDBFYDCFYDKFYDNE5DZEODaBODhBODtBODxBODyBOD5E5D6BOECAE"),([8,31,2164802,4329604,8659208,17318416,32505856,32506848],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUBOAWBOAYE5AaE5BKE5BRE5BSE5BpE5BqE5BxE5ByE5CJE5CKE5CRE5CSE5CZE5CaE5CpBOCqBOCxBOC9E9DCBODZBkDaE5DiE5DqE5DtE5DyE5D-E5ECE5EFBO"),([8,31,2164802,4329604,8659208,17318416,32505856,33553439],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUBOAWBOAYFYAaFYBKFYBRFYBSFYBpFYBqFYBxFYByFYCJFYCKFYCRFYCSFYCZFYCaFYCpEOCqBOCxBOC9BODCBODKArDaFYDdFYDiFBDqFPDtFYDyFYD9FYD-E5ECFYEFBO"),([8,31,2164802,4330468,8659208,17318416,32505856],hh "ABFLADFLAFFLAHFLAJFLALFLANFLAPFLARFLATFLAVBOAXBOA7FLA_FLBLFLBPFLBTFLBXFLBjFLBnFLBrFLBvFLBzFLB3FLCDFLCHFLCLFLCPFLCTFLCXFLCbFLCfFLCrBOCvFLCzBOC3BOC7BOC_BODDBODHFLDLArDPFL"),([8,992,1023,1082401,2164802,4329604,8659208,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYD8AaD8A6FYA9FYBKFYBxFYByFYCCFYCRFYCSFYCZFYCaFYCuFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZD8DaD8DhEODiD8DqD8D5FvEBD8ECD8"),([8,992,1023,1082401,2164802,4329604,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYCTAaCTA6FYA9FYBiFYBqFYBxFYByFYCRFYCSFYCZFYCaFYCpFYCuFYC2FYC5FYC6FYDBFYDCFYDJFYDKFYDZCTDaCTDhEODiCTDqCTD1CKD5B4EBCTECCT"),([8,992,1023,1082401,2164802,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBeAaBeA6FYA9FYBKFYBSFYBxFYByFYCRFYCSFYCZFYCaFYCpFYCqFYC5FYC6FYDBFYDCFYDJFYDKFYDZBeDaBeDhEODiBeDqBeDtFSD5BeD6BeEBA4ECA4"),([8,992,1023,1082401,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYC5AaC5A6FYA9FYBxFYByFYCCFYCKFYCRFYCSFYCZFYCaFYCpFYC5FYC6FYDBFYDCFYDJFYDKFYDZC5DaC5DhEODiC5DpCyDqC5D6C5D9FYECCK")]
theorem k158 : b158.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b159 : List (List Nat × List (Nat × Nat)) := [([8,992,1023,2164802,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYBOAaBOA6FYA9FYBiFYBqFYBxFYByFYCRFYCSFYCZFYCaFYCpFYCqFYC5FYC6FYDBFYDCFYDJFYDKFYDZBODaBODhEODiBODpBOD1BOD6BOECAr"),([8,992,31744,1015808,1082401,2164802,4329631,8659208,17318416,32505856],hh "CIAADgAAEYAA"),([8,992,31744,1015808,1082401,2164802,8659208,32641156],hh "AAD7ACD7AED7AGD7AID7AKD7AMD7AOD7AQD7ASD7AUD7AWD7AYEqAaEqA5D7A6D7BJD7BKD7BRD7BSD7BiD7CKDzCSD7CZD7CaD7CuD2CyD3C6D7DBD7DCD7DJD7DKD7DaEoD6AKEBCT"),([8,992,31744,1015808,1082401,2164802,17318416,32641156],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUCTAWCTAYB4AaB4A5CTA6CTBJCTBKCTBRCTBSCTCCCLCKCTCSCTCZCTCaCTCpCTCuCTCyCTC6CTDBCTDCCTDJCTDKCTD6AKD9CKEBD8"),([8,992,31744,1015808,1082401,2164831,4329604,8659208],hh "AAD5ACD5AED5AGD5AID5AKD5AMD5AOD5AQD5ASD5AUAmAWAmAYD5AaD5A5D5A6D5BJD5BKD5BRD5BSD5BhD5BiD5BpD5BxD5CKDyCSD5CqAlDBAmDCAmDJCKDZBADeD1DhD5DiD1DpD5DqD5DxArDyD5D6D5EBA4ECCT"),([8,992,31744,1015808,1082401,2164831,4329604,17318416],hh "AACSACCSAECSAGCSAICSAKCSAMCSAOCSAQCSASCSAUAiAWAiAYCSAaCSA5CSA6CSBJCSBKCSBRCSBSCSBhCSBpCSBxCSCCCKCKCSCSCSDBAiDCAiDJCKDeCSDhCSDiCSDpCSDqCSDxBODyCSD6CSEBBeECD8"),([8,992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856],hh "CIAADgAAEYAA"),([8,992,31744,1015808,2164802,4329631,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUBOAWBOAYArAaArA5BOA6BOBJBOBKBOBRBOBSBOCCBOCKBOCSBOCaBOCpBOCxBOC5BODBBODCBODaArDhArDpArDxC5DyArEBBEECBE")]
theorem k159 : b159.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b160 : List (List Nat × List (Nat × Nat)) := [([8,992,31744,1015808,4329604,8659208,17318416,32573506],hh "AAACACACAEACAGACAIACAKACAMACAOACAQACASACAUACAWACAYBHAaBHA5ACA6ACBJACBKACBRACBSACBiACBqACByACCZACCaACCpACCqACDBACDCACDJACDKACDyBHD1AC"),([8,992,1047552,1082401,2164802,4329604,8659208,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYD8AaD8A5EOA6EOBKEOBqEOBxEOByEOCCEOCREOCSEOCZEOCaEOCuEOCyEOC5EOC6EODBEODCEODJEODKEODZE5DaD8DhFYDiD8DyD8D5FvD6F5EBD8"),([8,992,1047552,1082401,2164802,4329604,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYCTAaCTA5EOA6EOBiEOBqEOBxEOByEOCREOCSEOCZEOCaEOCpEOCuEOCyEOC5EOC6EODBEODCEODJEODKEODZE5DaCTDhFYDiCTDyCTD1ELD5B4D6B4EBCT"),([8,992,1047552,1082401,2164802,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYBeAaBeA5EOA6EOBKEOBSEOBxEOByEOCREOCSEOCZEOCaEOCpEOCqEOC5EOC6EODBEODCEODJEODKEODZE5DaBeDhFYDiBeDtBODyBeD5BeEBA4"),([8,992,1047552,1082401,4329604,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYC5AaC5A5EOA6EOBxEOByEOCCEOCKEOCREOCSEOCZEOCaEOCpEOCyEOC5EOC6EODBEODCEODJEODKEODZE5DaC5DhFYDiC5DpCyDyC5D9EQ"),([8,992,1047552,2164802,4329604,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYBOAaBOA5EOA6EOBiEOBqEOBxEOByEOCREOCSEOCZEOCaEOCpEOCqEOC5EOC6EODBEODCEODJEODKEODZE5DaBODhFYDiBODpBODqBODyBOD1EO"),([8,992,1082401,2164802,4329604,8659208,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUAaAWAaAYEOAaEOA5ASA6AaBJAQBRAaBSAaBhAWBiAaBpAaBqAaBxAaByAaCBAaCGAaCJAaCKAaCRAaCSAaCZAaCaAaCpAaCqAaC6AaDBAaDCAaDJAaDZALDaEOD5EOECEOEFAa"),([8,992,1082401,2164802,4329604,8659208,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDfAWDfAYFYAaFYA5BmA6DfBJDeBRDfBSDfBhCHBiDfBpDfBqDfBxDfByDfCBDfCGDfCJDfCKDfCRDfCSDfCZDfCaDfCpDfCqDfCyDfDBDfDJDfDKDfDaFYDdDfDtDhD9DfECFYEFDf")]
theorem k160 : b160.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b161 : List (List Nat × List (Nat × Nat)) := [([8,992,1082401,2164802,4329604,17318416,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUAaAWAaAYEOAaEOA5ASBJAQBKAaBRAaBSAaBhAWBpAaBqAaBxAaByAaCFALCGAaCJAaCKAaCRAaCSAaCZAaCaAaCpAaCqAaC6AaC9AaDBAaDCAaDJAaDZALDaEODtBBD5EOECEOEFAa"),([8,992,1082401,2164802,4329604,17318416,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDfAWDfAYFYAaFYA5BmBJDeBKDfBRDfBSDfBhCHBpDfBqDfBxDfByDfCFBkCGDfCJDfCKDfCRDfCSDfCZDfCaDfCpDfCqDfCyDfC9DfDBDfDJDfDKDfDaFYDdDfDtDgD9DfECFYEFDf"),([8,992,1082401,2164802,8659208,17318416,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUAaAWAaAYEOAaEOA5ASA6AaBJAQBRAaBSAaBhAaBpAaBqAaBxAaByAaCCAaCFALCJAaCKAaCRAaCSAaCZAaCaAaCpAaCqAaC1AaC6AaDBAaDJAaDZALDaEODlAbECEOEFAa"),([8,992,1082401,2164802,8659208,17318416,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDfAWDfAYFYAaFYA5BmA6DfBJDeBRDfBSDfBhDfBpDfBqDfBxDfByDfCCDfCFBkCJDfCKDfCRDfCSDfCZDfCaDfCpDfCqDfCyDfC1DfDBDfDCDfDJDfDKDfDaFYDdDfDlDsECFYEFDf"),([8,992,1082401,4329604,8659208,17318416,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUAaAWAaAYEOAaEOA5ASBJAWBRAaBSAaBhAaBiAaBpAaBqAaBxAaByAaCFALCJAaCKAaCRAaCSAaCZAaCaAaCpAaCqAaCxAaC6AaDFAaDZALDaEOD1AaECEOEFAa"),([8,992,1082401,4329604,8659208,17318416,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDfAWDfAYFYAaFYA5BmBJCHBRDfBSDfBhDfBiDfBpDfBqDfBxDfByDfCFBkCJDfCKDfCRDfCSDfCZDfCaDfCpDfCqDfCxDfCyDfDCDfDFDfDKDfDaFYDdDfD1DfD9DfECFYEFDf"),([8,992,2164802,4329604,8659208,17318416,32505856,32505887],hh "AAAaACAaAEAaAGAaAIAaAKAaAMAaAOAaAQAaASAaAUAaAWAaAYEOAaEOA5AQBJAWBKAaBRAaBSAaBhAaBpAaBqAaBxAaByAaCCAaCFALCJAaCKAaCRAaCSAaCZAaCaAaCpAaCqAaCxAaCyAaC6AaC9AaDZALDaEODtAaECEOEFAa"),([8,992,2164802,4329604,8659208,17318416,32505856,33554400],hh "AADfACDfAEDfAGDfAIDfAKDfAMDfAODfAQDfASDfAUDfAWDfAYFYAaFYA5DeBJCHBKDfBRDfBSDfBhDfBpDfBqDfBxDfByDfCCDfCFBkCJDfCKDfCRDfCSDfCZDfCaDfCpDfCqDfCxDfC9DfDCDfDKDfDaFYDdDfDtDfECFYEFDf")]
theorem k161 : b161.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b162 : List (List Nat × List (Nat × Nat)) := [([8,31744,1015808,1082401,2164802,4329604,17318431,32505856],hh "AAEvACEvAEEvAGEvAIEvAKEvAMEvAOEvAQEvASEvAUEvAWEvAYALAaALA5EvA6EvBJEvBREvBhEvBiEvBpEvBqEvBxEvByEvCBEvCJEvCREvCSEvCZEvCaEvCqEvCtEvCyEvC1EvDBEtDZFYDaALDhFrDiALDqALD1ALD5ALEBEO"),([8,31744,1015808,1082401,2164802,8659208,17318896,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYBUAaBUA5EOA6EOBKEOBSEOBxEOByEOCREOCSEOCZEOCaEOC5EODZFYDaBUDhFrDiBUDtBGDyBUD5BUEBEw"),([8,31744,1015808,1082401,4329604,8659208,17318431,32505856],hh "AAEtACEtAEEtAGEtAIEtAKEtAMEtAOEtAQEtASEtAUEtAWEtAYALAaALA5EtA6EtBJEtBREtBhEtBpEtBxEtByEtCBEtCCEtCJEtCKEtCREtCSEtCZEtCaEtCqEtCtEtCyEtC1EtDJEtDZFYDaALDhFrDiALDpALDqALD6ALD9Et"),([8,31744,1015808,2164802,4329604,8659208,17318896,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYBGAaBGA5EOA6EOBiEOBqEOBxEOByEOCREOCSEOCZEOCaEODBEODZFYDaBGDhFrDiBGDpBGDqBGDyBGD1EO"),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208],hh "AAD8ACD8AED8AGD8AID8AKD8AMD8AOD8AQD8ASD8AUD8AWD8AYF5AaF5AcD8AeD8A5D8A6D8BJD8BKD8BRD8BSD8BhD8BiD8BpD8BqD8BxD8ByD8CJD8CKD8CRD8CZD8CpD8CqD5C6D0DCD8DJD8DKD8DZF5DiF4D5F5D6F5EBCKECAKESD6EZD8EeD2EgAAEhD8EiD4EpD8EqD8ExArEyD8E5D8E6D8FBA4FCCT"),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],hh "C4AAEgAAFgAA"),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416],hh "AACTACCTAECTAGCTAICTAKCTAMCTAOCTAQCTASCTAUCTAWCTAYB4AaB4AcCTAeCTA5CTA6CTBJCTBKCTBRCTBSCTBhCTBiCTBpCTBqCTBxCTByCTCJCTCRCTCZCTCpCTCqCSCyCLC6CTDCCTDJCTDKCTDZB4D5EKD6EKEBCKECAKESCTEeCTEgAAEhCTEiCTEpCTEqCTExBOEyCTE5C5E6CTFBBeFCD8"),([9,31,992,31744,1015808,1082401,2164802,8659208,17318416],hh "AABeACBeAEBeAGBeAIBeAKBeAMBeAOBeAQBeASBeAUBeAWBeAYBeAaBeAcA4AeA4A5BeA6BeBJBeBKBeBRBeBSBeBhBeBiBeBpBeBqBeBxBeByBeCCBQCJBeCKBeCQAACRBeCSBaCZBeCaBeCpBeDJBeDKBeDhBeDpBeDxBeD5BeD6BeEBBeECBeEaA4EhA4EpA4ExBOEyA4E5C5E6A4FBAKFCAK")]
theorem k162 : b162.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b163 : List (List Nat × List (Nat × Nat)) := [([9,31,992,31744,1015808,1082401,4329604,8659208,17318416],hh "AAC5ACC5AEC5AGC5AIC5AKC5AMC5AOC5AQC5ASC5AUC5AWC5AYC5AaC5AcCKAeCKA5C5A6C5BJC5BKC5BRC5BSC5BhC5BiC5BpC5BqC5BxC5ByC5CJC5CRC5CZC5CpC5DJC5DKC5DaC5DhC5DiC5DoAADpC5DqC5DxC5DyC5D5C5D6C5EBC5ECC5ESCKEgAAEhCKEiCKEpCKEqCKExBOEyCKE5BeE6D8FBCKFCCK"),([9,31,992,31744,1015808,2164802,4329604,8659208,17318416],hh "AABOACBOAEBOAGBOAIBOAKBOAMBOAOBOAQBOASBOAUBOAWBOAYBOAaBOAcArAeArA5BOA6BOBJBOBKBOBRBOBSBOBhBOBiBOBpBOBqBOBxBOByBOCBBOCpBOCqBOCyBOC6BODCBODJBODKBODhBODpBODxBOD5BOD6BOEBBOECBOEaArEhArEpArExC5EyArE5BeE6ArFBAEFCAE"),([9,31,992,31744,1082401,2164802,4329604,8659208,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYFrAaFrAcD8AeD8A5FrA6FrBJFrBKFrBOFYBRFrBSFrBWFYBpFrBqFrBxFrB1FYCCFrCJFCCRFZCSFrCVFoCZFrCaFrCxFlCyFrC5FoC9FZDBFrDCFrDJFrDKFrDaFrDhFrDmFrDpFrDqFrDtFYDxFrDyFrD5FrD6FrEBFrECFrEREOESD8EZE5EaD8EhFYEiD8ElFYEqD8E5FvFBD8FCD8"),([9,31,992,31744,1082401,2164802,4329604,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYFrAaFrAcCTAeCTA5FrA6FrBJFrBKFrBOFYBRFrBSFrBWFYBpFrBxFrB1FYCCFrCJFCCKFrCRFZCSFrCVFoCZFrCaFrCxFlC5FoC9FZDBFrDCFrDJFrDKFrDaFrDlE5DmFrDpFrDqFrDtFYDxFrDyFrD5FrD6FrEBFrECFrEREOESCTEZE5EaCTEhFYEiCTElFYEqCTE1CKE5B4FBCTFCCT"),([9,31,992,31744,1082401,2164802,8659208,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYFrAaFrAcBeAeBeA5FrA6FrBJFrBKFrBOFYBRFrBSFrBWFYBiFrBpFrBqFrBxFrByFrB1FYCJFCCRFZCVFoCZFrCaFrCxFrC5FrC9FYDBFrDCFrDJFrDKFrDiFrDlE5DpFrDtFYDxFrDyFrD5FrD6FrEBFrECFrEREOESBeEZE5EaBeEhFYEiBeElFYEqBeEtFpE5BeE6BeFBA4FCA4"),([9,31,992,31744,1082401,4329604,8659208,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYFrAaFrAcC5AeC5A5FrA6FrBJFrBKFrBOFYBRFrBSFrBWFYBpFrBxFrB1FYCJFlCRFoCVFZCZFrCaFrCqFrCxFrCyFrC5FrC6FrC9FYDBFrDCFrDJFrDKFrDaFrDlE5DpFrDqFrDtFYDxFrDyFrD5FrD6FrEBFrECFrEREOESC5EZE5EaC5EhFYEiC5ElFYEpCyEqC5E6C5E9FrFCCK"),([9,31,992,31744,2164802,4329604,8659208,17318416,32505856],hh "AAFrACFrAEFrAGFrAIFrAKFrAMFrAOFrAQFrASFrAUFrAWFrAYFrAaFrAcBOAeBOA5FrA6FrBJFrBKFrBOFYBRFrBSFrBWFYBpFCBxFZB1FoCCFrCJFlCKFrCRFoCSFrCVFZCZFrCaFrCxFrC5FrC9FYDBFrDCFrDJFrDKFrDiFrDlE5DpFrDtFYDxFrDyFrD5FrD6FrEBFrECFrEREOESBOEZE5EaBOEhFYEiBOElFYEpBOE1BOE6BOFCAr"),([9,31,992,1082401,2164802,4329604,8659208,17318416,32505856],hh "AAFYACFYAEFYAGFYAIFYAKFYAMFYAOFYAQFYASFYAUFYAWFYAYFYAaFYAcAaAeAaA5FYA6FYBKFYBOFYBRFYBSFYBWFYBiFYBmFYBpFBBqFYBuFYBxFYByFYB1FYB2FYCCFYCGFYCJFPCKFYCOFYCRFYCSFYCVFYCWFYCZFYCaFYCdFYCeFYCqFYCuFYCxFYCyFYC2FYC5FYC6FYC9FYC-FYDBFYDCFYDFFYDGFYDJFYDKFYDNFYDOFYDaFYDeFYDiFYDlE5DmFYDpFYDqFYDtFYDuFYDxFYDyFYD1FYD2FYD5FYD6FYD9FYD-FYEBFYECFYEFFYEGFYEREOESBEEZE5EaCfEhAaEiAaElFYEpAaEtCKExAaE1BeE5AaE6AaE9FYFBAaFCAaFFFY")]
theorem k163 : b163.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b164 : List (List Nat × List (Nat × Nat)) := [([9,31,992,1082401,2164802,4329604,8659208,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVFYAXFYAZD8AbD8A7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrFYCvFYCzFYC3FYC7FYC_FYDDFYDHFYDLFYDPFYDbD8DfFYDjD8DnFYDrD8DvFYDzD8D3D8D7F5D_D8EDD8EHFY"),([9,31,992,1082401,2164802,4329604,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVFYAXFYAZCTAbCTA7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrFYCvFYCzFYC3FYC7FYC_FYDDFYDHFYDLFYDPFYDbCTDfFYDjCTDnFYDrCTDvFYDzCTD3CTD7B4D_CTEDCTEHFY"),([9,31,992,1082401,2164802,8659208,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVFYAXFYAZBeAbBeA7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrFYCvFYCzFYC3FYC7FYC_FYDDFYDHFYDLFYDPFYDbBeDfFYDjBeDnFYDrBeDvFYDzBeD3BeD7BeD_FYEDA4EHFY"),([9,31,992,1082401,4329604,8659208,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVFYAXFYAZC5AbC5A7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrFYCvFYCzFYC3FYC7FYC_FYDDFYDHFYDLFYDPFYDbC5DfFYDjC5DnFYDrC5DvFYDzC5D3C5D7C5D_FYEDCKEHFY"),([9,31,992,2164802,4329604,8659208,17318416,32505856],hh "ABFYADFYAFFYAHFYAJFYALFYANFYAPFYARFYATFYAVFYAXFYAZBOAbBOA7FYA_FYBLFYBPFYBTFYBXFYBjFYBnFYBrFYBvFYBzFYB3FYCDFYCHFYCLFYCPFYCTFYCXFYCbFYCfFYCrFYCvFYCzFYC3FYC7FYC_FYDDFYDHFYDLFYDPFYDbBODfFYDjBODnFYDrBODvBODzBOD3BOD7BOD_FYEDArEHFY"),([9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYE5AaE5AcD8AeD8A5E5A6E5BJE5BKE5BRE5BSE5BpE5BxE5CCE5CIAACJE5CKE5CRE5CSE5CZE5CaE5CxE5C5E5DBE5DCE5DJE5DKE5DaE5DgAADhE5DiE5DpE5DqE5DxE5DyE5D5E5D6E5EBE5ECE5EREOESD8EZFYEaD8EhFrEiD8EqD8E5FvFBD8FCD8"),([9,31,31744,1015808,1082401,2164802,4329604,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYE5AaE5AcCTAeCTA5E5A6E5BJE5BKE5BRE5BSE5BpE5BxE5CCE5CIAACJE5CKE5CRE5CSE5CZE5CaE5CxE5C5E5DBE5DCE5DJE5DKE5DZExDaE5DiE5DlE5DqE5DtE5DxE5DyE5D5E5D6E5EBE5ECE5EREOESCTEZFYEaCTEhFrEiCTEqCTE1CKE5B4FBCT"),([9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYE5AaE5AcBeAeBeA5E5A6E5BJE5BKE5BRE5BSE5BiE5BoAABpE5BqE5BxE5ByE5CJE5CRE5CZE5CaE5CxE5C5E5DBE5DCE5DJE5DKE5DZExDlE5DtE5DxE5DyE5D5E5D6E5EBE5ECE5EREOESBeEZFYEaBeEhFrEiBeEqBeEtE0E5BeE6BeFBA4")]
theorem k164 : b164.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b165 : List (List Nat × List (Nat × Nat)) := [([9,31,31744,1015808,1082401,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYE5AaE5AcC5AeC5A5E5A6E5BJE5BKE5BRE5BSE5BpE5BxE5CJE5CRE5CZE5CaE5CqE5CwAACxE5CyE5C5E5C6E5DBE5DCE5DJE5DKE5DZExDaE5DiE5DlE5DqE5DtE5DxE5DyE5D5E5D6E5EBE5ECE5EREOESC5EZFYEaC5EhFrEiC5EpCyEqC5E6C5E9E5"),([9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856],hh "AAE5ACE5AEE5AGE5AIE5AKE5AME5AOE5AQE5ASE5AUE5AWE5AYE5AaE5AcBOAeBOA5E5A6E5BJE5BKE5BRE5BSE5BpE5BxE5CCE5CIAACJE5CKE5CRE5CSE5CZE5CaE5CxE5C5E5DBE5DCE5DJE5DKE5DZExDlE5DtE5DxE5DyE5D5E5D6E5EBE5ECE5EREOESBOEZFYEaBOEhFrEiBOEpBOE1E9E6BO"),([9,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYEOAaEOAcD8AeD8A5EOA6EOBJEOBKEOBREOBSEOBiEOCKEOCSEOCZEOCaEOCqEODBEODCEODJEODKEODeEODiEODqEODxEODyEOD5EOD6EOEBEOECEOERE5ESD8EZFYEaD8EhFrEiD8EyD8E5FvE6F5FBD8"),([9,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYEOAaEOAcCTAeCTA5EOA6EOBJEOBKEOBREOBSEOCCEOCKEOCSEOCZEOCaEODBEODCEODJEODKEODZEODeEODiEODqEODxEODyEOD5EOD6EOEBEOECEOERE5ESCTEZFYEaCTEhFrEiCTEyCTE1ELE5B4E6B4FBCT"),([9,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYEOAaEOAcBeAeBeA5EOA6EOBJEOBKEOBREOBSEOBiEOBqEOByEOCZEOCaEODBEODCEODJEODKEODZEODaEODxEODyEOD5EOD6EOEBEOECEOERE5ESBeEZFYEaBeEhFrEiBeEtBOEyBeE5BeFBA4"),([9,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYEOAaEOAcC5AeC5A5EOA6EOBJEOBKEOBREOBSEOCZEOCaEOCqEOCyEOC6EODBEODCEODJEODKEODZEODiEODqEODxEODyEOD5EOD6EOEBEOECEOERE5ESC5EZFYEaC5EhFrEiC5EpCyEyC5E9EQ"),([9,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],hh "AAEOACEOAEEOAGEOAIEOAKEOAMEOAOEOAQEOASEOAUEOAWEOAYEOAaEOAcBOAeBOA5EOA6EOBJEOBKEOBREOBSEOCCEOCKEOCSEOCZEOCaEODBEODCEODJEODKEODZEODaEODxEODyEOD5EOD6EOEBEOECEOERE5ESBOEZFYEaBOEhFrEiBOEpBOEqBOEyBOE1EO")]
theorem k165 : b165.all (fun a => P_ a.1 a.2) = true := by decide +kernel
theorem rows_in_order : T_.toList = ((((((((b0 ++ b1) ++ (b2 ++ (b3 ++ b4))) ++ ((b5 ++ b6) ++ (b7 ++ (b8 ++ b9)))) ++ (((b10 ++ b11) ++ (b12 ++ (b13 ++ b14))) ++ ((b15 ++ b16) ++ (b17 ++ (b18 ++ b19))))) ++ ((((b20 ++ b21) ++ (b22 ++ (b23 ++ b24))) ++ ((b25 ++ b26) ++ (b27 ++ (b28 ++ b29)))) ++ (((b30 ++ b31) ++ (b32 ++ (b33 ++ b34))) ++ ((b35 ++ (b36 ++ b37)) ++ (b38 ++ (b39 ++ b40)))))) ++ (((((b41 ++ b42) ++ (b43 ++ (b44 ++ b45))) ++ ((b46 ++ b47) ++ (b48 ++ (b49 ++ b50)))) ++ (((b51 ++ b52) ++ (b53 ++ (b54 ++ b55))) ++ ((b56 ++ (b57 ++ b58)) ++ (b59 ++ (b60 ++ b61))))) ++ ((((b62 ++ b63) ++ (b64 ++ (b65 ++ b66))) ++ ((b67 ++ b68) ++ (b69 ++ (b70 ++ b71)))) ++ (((b72 ++ b73) ++ (b74 ++ (b75 ++ b76))) ++ ((b77 ++ (b78 ++ b79)) ++ (b80 ++ (b81 ++ b82))))))) ++ ((((((b83 ++ b84) ++ (b85 ++ (b86 ++ b87))) ++ ((b88 ++ b89) ++ (b90 ++ (b91 ++ b92)))) ++ (((b93 ++ b94) ++ (b95 ++ (b96 ++ b97))) ++ ((b98 ++ b99) ++ (b100 ++ (b101 ++ b102))))) ++ ((((b103 ++ b104) ++ (b105 ++ (b106 ++ b107))) ++ ((b108 ++ b109) ++ (b110 ++ (b111 ++ b112)))) ++ (((b113 ++ b114) ++ (b115 ++ (b116 ++ b117))) ++ ((b118 ++ (b119 ++ b120)) ++ (b121 ++ (b122 ++ b123)))))) ++ (((((b124 ++ b125) ++ (b126 ++ (b127 ++ b128))) ++ ((b129 ++ b130) ++ (b131 ++ (b132 ++ b133)))) ++ (((b134 ++ b135) ++ (b136 ++ (b137 ++ b138))) ++ ((b139 ++ (b140 ++ b141)) ++ (b142 ++ (b143 ++ b144))))) ++ ((((b145 ++ b146) ++ (b147 ++ (b148 ++ b149))) ++ ((b150 ++ b151) ++ (b152 ++ (b153 ++ b154)))) ++ (((b155 ++ b156) ++ (b157 ++ (b158 ++ b159))) ++ ((b160 ++ (b161 ++ b162)) ++ (b163 ++ (b164 ++ b165))))))))).map Prod.fst := by decide +kernel
theorem table_ok : ∀ x, T_.mem x = true → ∃ h, P_ x h = true := cover _ _ rows_in_order (all_app (all_app (all_app (all_app (all_app (all_app (all_app k0 k1) (all_app k2 (all_app k3 k4))) (all_app (all_app k5 k6) (all_app k7 (all_app k8 k9)))) (all_app (all_app (all_app k10 k11) (all_app k12 (all_app k13 k14))) (all_app (all_app k15 k16) (all_app k17 (all_app k18 k19))))) (all_app (all_app (all_app (all_app k20 k21) (all_app k22 (all_app k23 k24))) (all_app (all_app k25 k26) (all_app k27 (all_app k28 k29)))) (all_app (all_app (all_app k30 k31) (all_app k32 (all_app k33 k34))) (all_app (all_app k35 (all_app k36 k37)) (all_app k38 (all_app k39 k40)))))) (all_app (all_app (all_app (all_app (all_app k41 k42) (all_app k43 (all_app k44 k45))) (all_app (all_app k46 k47) (all_app k48 (all_app k49 k50)))) (all_app (all_app (all_app k51 k52) (all_app k53 (all_app k54 k55))) (all_app (all_app k56 (all_app k57 k58)) (all_app k59 (all_app k60 k61))))) (all_app (all_app (all_app (all_app k62 k63) (all_app k64 (all_app k65 k66))) (all_app (all_app k67 k68) (all_app k69 (all_app k70 k71)))) (all_app (all_app (all_app k72 k73) (all_app k74 (all_app k75 k76))) (all_app (all_app k77 (all_app k78 k79)) (all_app k80 (all_app k81 k82))))))) (all_app (all_app (all_app (all_app (all_app (all_app k83 k84) (all_app k85 (all_app k86 k87))) (all_app (all_app k88 k89) (all_app k90 (all_app k91 k92)))) (all_app (all_app (all_app k93 k94) (all_app k95 (all_app k96 k97))) (all_app (all_app k98 k99) (all_app k100 (all_app k101 k102))))) (all_app (all_app (all_app (all_app k103 k104) (all_app k105 (all_app k106 k107))) (all_app (all_app k108 k109) (all_app k110 (all_app k111 k112)))) (all_app (all_app (all_app k113 k114) (all_app k115 (all_app k116 k117))) (all_app (all_app k118 (all_app k119 k120)) (all_app k121 (all_app k122 k123)))))) (all_app (all_app (all_app (all_app (all_app k124 k125) (all_app k126 (all_app k127 k128))) (all_app (all_app k129 k130) (all_app k131 (all_app k132 k133)))) (all_app (all_app (all_app k134 k135) (all_app k136 (all_app k137 k138))) (all_app (all_app k139 (all_app k140 k141)) (all_app k142 (all_app k143 k144))))) (all_app (all_app (all_app (all_app k145 k146) (all_app k147 (all_app k148 k149))) (all_app (all_app k150 k151) (all_app k152 (all_app k153 k154)))) (all_app (all_app (all_app k155 k156) (all_app k157 (all_app k158 k159))) (all_app (all_app k160 (all_app k161 k162)) (all_app k163 (all_app k164 k165))))))))
theorem no_nine : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3315386 : ℕ).testBit (5 * u.val + v.val)) C :=
  signed_rep_lb 3315386 9 1 0 PD_ PM_ XS_ G_ T_ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) table_ok (by decide +kernel)

end SignedFive19634
