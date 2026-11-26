import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19071_refutation

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

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

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
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
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
    rw [hd, hc, hg] at hmem
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
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
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


/-! ## Family 2: a 4-by-4 bipartite graph, lower parts through the frontier certificate

A Monotone2 circuit representing `A` is a FanInTwo circuit on 8 inputs, so its function `f` has a
Run (L_meta_927); the Run's image on the 16 one-hot points (`ohPts`) is a `NatRun 65535 M`.
NOT moves are allowed in the search, so the certified bound also holds for AND/OR/NOT circuits. -/

def code (k : ℕ) : ℕ := 2 ^ (k / 4) + 2 ^ (4 + k % 4)

def ohPts : List ℕ := List.ofFn fun k : Fin 16 => code k.val

theorem ofFn_code : ∀ k : Fin 16, List.ofFn (pt 8 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 4) (by have := k.isLt; omega) : Fin 4)
      (Fin.mk (k.val % 4) (by have := k.isLt; omega) : Fin 4) := by
  decide +kernel

theorem ohPts_length : ohPts.length = 16 := by simp [ohPts]

theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 16) : C.eval (List.ofFn (pt 8 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (4 * (k / 4) + k % 4) = M.testBit k
  rw [Nat.div_add_mod]

theorem enc_rep (M : ℕ) (hM : M < 2 ^ 16) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C) :
    encL (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) ohPts = M := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [encL_testBit]
  by_cases hj : j < 16
  · rw [List.getD_eq_getElem _ _ (by simp [ohPts_length, hj])]
    simp only [ohPts, List.getElem_map, List.getElem_ofFn]
    exact rep_val M C hrep j hj
  · rw [List.getD_eq_default _ _ (by simp [ohPts_length]; omega)]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc M < 2 ^ 16 := hM
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem signed_rep_lb (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ)
    (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 16) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 16) (h0' : zer < 16)
    (hxs : (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 65535 M PD PM = true) (hG : symOK 65535 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK 65535 M PD PM G T x h = true)
    (hi : XS.sublists.all (rootOK M PD PM G T s) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  have hnc : ∃ a b : Fin 8 → Bool, (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 8 (code one), pt 8 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  have hl := lb_cert (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) ohPts 65535 M XS PD PM G T s
    (s + 1) rfl (by rw [ohPts_length]; decide) (enc_rep M hM C hrep) hxs hnc hp hG hT hi s
    ⟨C, hfan, hsize, fun _ => rfl⟩
  omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def L_ : List ℕ := [17,33,65,129,18,34,66,130,20,36,68,132,24,40,72,136]
def M_ : ℕ := 65535
def Y_ : ℕ := 858
def XS_ : List ℕ := [15,240,3840,61440,4369,8738,17476,34952]
def PD_ : List (ℕ × ℕ) := [(1,759),(2,908),(3,817),(4,879),(5,832),(6,855),(7,348),(8,89),(9,91),(10,26),(11,26),(12,10),(13,2),(14,2)]
def PM_ : List (ℕ × ℕ) := [(0,858),(2,858),(5,858),(7,858),(10,858),(11,858),(12,858),(13,858),(14,858),(15,858)]

def G_ : List (List ℕ) := [[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,14],[0,3,2,3,4,7,6,7,8,9,10,11,12,15,14,15],[5,4,7,6,1,0,3,2,9,8,11,10,5,12,15,14],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,7,14],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,11,14],[0,1,2,1,4,5,6,5,8,9,10,11,12,13,14,13],[5,4,7,6,1,0,3,2,9,4,11,10,13,12,15,14],[5,4,7,6,1,0,3,2,9,8,7,10,13,12,15,14],[2,1,2,3,6,5,6,7,8,9,10,11,14,13,14,15],[0,1,0,3,4,5,4,7,8,9,10,11,12,13,12,15],[0,1,2,1,4,5,6,7,8,9,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,8,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,1,10,11,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,14,13,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,5,12,13,14,15],[0,3,2,3,4,7,6,7,8,8,10,11,12,15,14,15],[0,3,2,3,4,5,6,7,8,8,10,11,12,15,14,15],[0,1,2,3,4,5,6,7,8,9,14,11,12,13,14,15],[0,1,2,1,4,5,6,7,8,9,14,13,12,13,14,13],[0,1,2,1,4,5,6,5,8,9,14,13,12,13,14,13],[0,3,2,3,4,7,6,7,8,9,10,11,12,10,14,15],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,10],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,11],[0,3,2,3,4,7,6,7,8,3,10,11,12,15,14,15],[0,3,2,3,4,7,6,7,8,9,10,11,12,10,10,10],[0,1,2,3,4,7,6,7,8,9,10,11,12,15,14,15],[0,1,2,1,4,5,6,15,8,9,10,13,12,13,14,13],[0,1,2,1,4,5,6,7,8,9,10,13,12,13,14,13],[0,1,2,1,4,5,6,5,8,9,10,11,12,13,14,10],[0,1,2,1,4,5,6,5,8,9,10,5,12,13,14,13],[0,1,2,1,4,5,6,5,8,9,10,5,12,13,14,15],[0,1,2,1,4,5,6,7,8,9,10,11,12,13,14,13],[0,1,2,1,4,5,6,5,8,9,10,5,12,13,14,7],[0,1,2,3,4,5,6,7,8,9,10,11,10,10,10,14],[0,1,2,1,4,5,6,5,8,9,10,13,11,10,10,10],[0,1,2,1,4,5,6,5,8,9,10,11,12,10,10,10],[0,1,2,3,4,5,6,7,8,9,10,11,11,11,15,11],[0,1,2,3,4,5,6,7,4,9,10,7,12,13,14,15],[0,1,2,3,4,5,6,7,8,9,10,11,5,5,5,13],[0,1,2,3,4,5,6,7,8,9,11,11,12,13,14,15],[0,1,2,3,4,5,6,7,4,9,10,5,12,13,14,15],[0,3,2,3,4,7,6,7,8,8,10,11,12,13,14,15],[2,3,0,3,6,7,4,7,6,6,5,10,14,15,12,15],[2,1,2,3,6,5,6,7,8,9,10,11,5,13,14,15],[2,1,2,3,6,5,6,7,8,9,10,11,5,5,5,13],[2,3,2,1,6,7,6,5,9,4,5,5,14,15,14,13],[2,1,2,3,6,5,6,7,8,9,10,11,5,5,5,15],[2,1,2,3,6,5,6,7,6,9,10,7,14,13,14,15],[2,3,2,1,6,7,6,5,4,9,5,5,14,15,14,13],[0,1,2,3,4,5,6,7,4,9,10,11,12,13,14,15],[0,1,2,1,4,5,6,5,4,9,10,5,12,13,14,13],[0,1,2,1,4,5,6,5,4,9,10,5,12,13,14,15],[2,1,0,1,6,5,4,5,6,6,10,7,14,13,12,13],[2,1,0,1,6,5,4,5,6,6,7,10,14,13,12,13],[0,1,2,3,4,5,6,7,8,9,10,11,7,15,7,7],[0,1,0,3,4,5,4,7,8,9,10,11,12,13,5,15],[0,1,0,3,4,5,4,7,8,9,10,11,5,5,5,13],[0,3,0,1,4,7,4,5,9,6,5,5,12,15,12,13],[0,1,0,3,4,5,4,7,8,9,10,11,5,5,5,15],[0,1,2,3,4,5,6,7,8,9,10,7,12,13,14,15],[2,6,10,6,1,5,9,5,3,4,11,7,15,11,11,11],[10,6,2,6,9,5,1,5,8,4,0,7,12,0,0,0],[5,4,7,6,1,0,3,2,9,8,11,10,13,0,11,14],[5,4,7,6,1,0,3,2,9,8,11,10,5,12,15,2],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,2],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,7,2],[5,4,7,6,1,0,3,2,9,8,11,10,13,12,11,2],[5,4,7,6,1,0,3,2,9,8,11,10,5,0,15,14],[5,4,7,6,1,0,3,2,9,8,11,10,13,0,15,14],[5,4,7,6,1,0,3,0,9,8,11,10,13,0,15,14],[5,3,7,6,1,0,3,2,9,8,11,10,13,0,7,14],[5,4,7,6,1,0,3,2,9,8,11,10,13,0,7,14],[5,4,7,6,1,0,3,2,9,3,11,10,13,0,11,14],[5,3,7,6,1,0,3,2,9,8,11,10,13,12,15,14],[5,4,7,6,1,0,3,2,9,3,11,10,13,12,15,14],[0,3,2,1,4,7,6,7,8,6,10,11,12,7,14,15],[10,1,0,3,9,5,4,7,8,4,12,12,11,13,12,15],[10,6,2,6,9,5,1,13,8,3,0,0,11,7,0,15],[10,6,2,6,9,5,1,13,8,4,0,0,11,7,0,15],[5,4,7,6,1,0,3,2,9,8,10,11,5,12,15,14],[2,1,0,3,6,5,4,7,8,4,12,12,10,13,12,15],[5,1,5,3,6,10,6,10,4,8,7,11,7,11,7,11],[0,1,2,1,4,5,6,5,8,9,10,5,12,13,14,10],[0,1,2,3,4,5,6,7,8,9,10,11,12,11,14,11],[0,1,2,1,4,5,6,5,8,9,10,5,12,10,10,10],[0,1,2,3,4,5,6,7,8,9,10,11,12,2,14,10],[0,1,2,1,4,5,6,5,4,9,10,5,7,15,7,15],[0,3,2,3,4,7,6,7,4,9,5,11,12,15,14,15],[2,1,2,3,6,5,6,7,6,9,10,11,14,13,14,15],[0,3,2,3,4,7,6,7,8,9,5,11,12,15,14,15],[0,1,2,1,4,5,6,5,8,9,10,5,7,15,7,15],[2,1,2,3,6,5,6,7,6,9,10,5,14,13,14,15],[2,1,0,3,9,5,4,7,8,4,12,12,2,13,12,15],[2,1,2,1,6,5,6,5,6,9,10,5,7,13,14,13],[10,6,10,6,1,5,1,5,8,4,11,7,11,7,11,7],[0,3,2,3,4,7,6,7,4,3,10,7,12,13,14,15],[11,9,11,9,6,14,6,14,3,1,5,13,5,13,5,13],[2,1,2,1,6,5,6,5,6,9,10,5,14,13,14,15],[2,3,2,3,6,7,6,7,6,4,5,7,10,11,10,11],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,7,7],[2,1,2,1,6,5,6,5,6,9,10,5,13,7,14,7],[0,1,2,3,4,5,6,7,8,9,10,11,12,5,5,15],[2,1,0,3,6,5,4,7,6,6,10,7,7,13,11,15],[0,1,2,3,4,5,6,7,8,9,10,11,5,5,14,15],[11,9,11,9,4,12,4,12,3,1,5,13,5,13,5,13],[0,1,0,1,4,5,4,5,8,6,10,5,12,7,11,7],[0,1,2,3,4,5,6,7,8,9,10,11,7,13,14,7],[0,1,0,1,4,5,4,5,8,6,10,5,11,7,11,7],[5,4,5,6,1,0,3,2,9,8,11,10,5,12,15,10],[0,3,2,3,4,5,9,7,8,8,11,11,12,15,11,15],[2,1,0,3,6,5,4,7,8,4,12,12,2,13,12,15],[5,4,7,6,1,0,3,2,6,8,11,10,7,12,15,11],[0,1,0,1,4,5,4,7,8,9,12,13,12,13,12,13],[0,1,2,1,4,5,6,7,8,9,10,11,12,10,10,10],[0,1,0,1,4,5,4,5,8,6,10,5,12,13,7,13],[0,1,0,1,4,5,4,5,8,6,10,5,12,13,11,15],[0,1,0,3,4,5,4,7,8,6,10,11,12,13,12,15],[10,6,10,6,4,5,4,5,8,1,0,5,11,7,11,7],[5,4,7,6,1,0,3,0,9,3,11,10,13,0,11,14],[0,1,2,3,4,5,6,7,8,9,10,11,0,0,0,14],[5,4,7,3,1,0,6,2,9,8,11,10,5,12,7,2],[5,4,5,1,1,0,3,2,9,8,11,10,5,12,15,2],[5,1,7,6,4,0,3,2,9,8,11,10,5,0,15,14],[5,1,7,6,4,0,3,0,9,8,11,10,5,0,15,14],[5,1,5,6,4,0,3,2,9,8,11,10,5,0,15,14],[10,6,2,6,9,5,1,7,8,1,0,0,11,13,0,15],[0,8,2,8,1,11,1,11,1,8,10,11,5,7,5,7],[5,4,5,6,1,0,3,2,6,8,10,11,5,0,15,2],[0,8,2,1,4,10,6,5,1,9,5,5,12,10,14,5]]



inductive CertTree where
  | leaf
  | node (left : CertTree) (key : List Nat) (hints : List (Nat × Nat)) (right : CertTree)
def CertTree.strip : CertTree → BT
  | .leaf => .lf
  | .node l k _ r => .nd l.strip k r.strip
def CertTree.check (p : List Nat → List (Nat × Nat) → Bool) : CertTree → Bool
  | .leaf => true
  | .node l k h r => l.check p && p k h && r.check p
theorem CertTree.local_ok {p t} (h : CertTree.check p t=true) :
    ∀k,t.strip.mem k=true → ∃a,p k a=true := by
  induction t with
  | leaf => intro k hm; simp [CertTree.strip,BT.mem] at hm
  | node l k a r il ir =>
    simp only [CertTree.check,Bool.and_eq_true] at h
    intro w hm
    simp only [CertTree.strip,BT.mem,Bool.or_eq_true] at hm
    rcases hm with eq|side
    · obtain rfl := leqL_eq _ _ eq
      exact ⟨a,h.1.2⟩
    · split at side
      · exact il h.1.1 _ side
      · exact ir h.2 _ side
def z := CertTree.leaf
def b (l : CertTree) (k : List Nat) (r : CertTree) := CertTree.node l k [] r
def bh := CertTree.node
theorem branch_ok {p l k h r} (hl : CertTree.check p l=true) (hk : p k h=true)
    (hr : CertTree.check p r=true) : CertTree.check p (.node l k h r)=true := by
  simp [CertTree.check,hl,hk,hr]

def B0 : CertTree := (b (b (b (b z [2,1551,64170] z) [3,15,1536,64170] (b z [3,15,4369,8954,20292] z)) [3,15,64716,65433] (b (b z [3,80,4383,8738,36744] z) [3,1551,21845,61440] z)) [3,1551,43690,61440] (bh (b (b z [3,4383,8946,20292,36744] z) [4,8,15,4369,8946,20292] z) [4,8,3840,4383,8946,17476] [(56,125),(96,125)] (b (b z [4,15,80,4369,8738,36744] z) [4,15,240,768,21845] z)))
def B1 : CertTree := (b (b (b (b z [4,15,240,4881,20292] z) [4,15,240,21845,64716] (bh z [4,15,240,62805,63078] [(96,126)] z)) [4,15,1536,21845,61440] (b (b z [4,15,1536,43690,61440] z) [4,15,1911,7953,17476] z)) [4,15,2288,4369,62532] (b (b (bh z [4,15,3840,4369,8954,17476] [(72,125),(128,76)] z) [4,15,3840,13107,64170] z) [4,15,3840,26214,64170] (b (b z [4,15,3840,35976,61986] z) [4,15,3840,39321,64170] z)))
def B2 : CertTree := (b (b (b (b z [4,15,3840,63897,64716] z) [4,15,4369,8946,20292,34952] (bh z [4,15,4369,8946,20292,43770] [(132,127)] z)) [4,15,4369,8959,20292] (b (b z [4,15,4369,20292,56589] z) [4,15,4369,64716,65416] z)) [4,15,4593,21845,63624] (b (b (b z [4,15,7953,17476,63631] z) [4,15,8738,61951,63624] z) [4,15,8738,64716,65416] (b (b z [4,15,8946,20292,61166] z) [4,15,13107,36744,61986] z)))
def B3 : CertTree := (b (b (b (b z [4,15,21845,35064,62532] z) [4,15,21845,39417,61440] z) [4,15,36744,61713,61986] (b (b z [4,80,3840,4383,8738,34952] z) [4,240,527,4369,62532] z)) [4,240,3003,4369,8751] (b (b (bh z [4,240,3840,4369,8746,17487] [(96,76)] z) [4,240,4369,8959,62532] z) [4,240,4369,26223,62532] (bh (b z [4,240,4369,56784,62532] z) [4,240,4369,62532,63087] [(80,126)] z)))
def B4 : CertTree := (bh (b (b (b z [4,240,4383,8738,20292,36744] z) [4,240,4383,8738,21845,36744] (b z [4,240,4383,8738,36744,62532] z)) [4,240,7953,34959,62532] (b (bh z [4,240,8738,62543,62805] [(80,126)] z) [4,240,8751,61166,62532] z)) [4,240,8751,62532,62805] [(80,126)] (b (b (b z [4,240,21845,26223,61440] z) [4,240,34952,62543,62805] z) [4,1551,4369,17476,61440] (b (bh z [4,1551,8738,34952,61440] [(104,23),(112,29)] z) [4,3840,4369,8738,17487,35064] z)))
def B5 : CertTree := (b (b (b (b z [4,3840,4369,8946,17487,34952] z) [4,3840,4369,8946,21855,34952] z) [4,3840,4383,8738,17487,35064] (bh (b z [4,3840,4383,8738,21845,35064] z) [4,3840,4383,8738,21855,35064] [(156,128)] z)) [4,3840,4383,8946,17476,34952] (b (b (b z [4,3840,4383,8946,17487,34952] z) [4,3840,4383,8946,20292,34952] z) [4,3840,4383,8946,21845] (b (b z [4,3840,4383,8946,21845,34952] z) [4,3840,4383,8946,21855,34952] z)))
def B6 : CertTree := (b (b (b (b z [4,3855,4369,8959,17476] z) [4,3855,8738,17487,63624] (b z [4,3855,12066,17476,63624] z)) [4,3855,17476,34952,65314] (b (b z [4,3855,17487,34952,61986] z) [4,4369,4383,8946,20292] z)) [4,4369,4383,8946,20292,34952] (b (b (b z [4,4369,4593,8751,62532] z) [4,4369,8738,17487,20292,35064] z) [4,4369,8946,17487,20292,34952] (b (b z [4,4369,8946,20292,65520] z) [4,4369,8959,17476,61680] z)))
def B7 : CertTree := (b (b (b (b z [4,4369,35064,61455,62532] z) [4,4383,8738,36744,61455] z) [4,4593,8751,21845,61440] (b (b z [4,7953,17476,63624,65520] z) [4,8738,36744,61455,61713] z)) [4,17476,35064,61455,61713] (bh (bh (b z [4,17487,21845,35064,61440] z) [5,8,15,240,4369,8738,20292] [(72,75)] z) [5,8,15,3840,4369,8946,17476] [(72,10),(176,76)] (bh (bh z [5,8,240,3840,4369,8738,17487] [(56,10),(136,76)] z) [5,8,240,3840,4383,8738,17476] [(56,77),(72,78),(128,78)] z)))
def B8 : CertTree := (b (b (bh (bh z [5,15,240,512,4369,20292] [(80,11)] z) [5,15,240,512,4369,62532] [(112,12)] (b z [5,15,240,768,4369,17476] z)) [5,15,240,1911,4369,17476] (b (bh z [5,15,240,2048,4369,62532] [(144,14)] z) [5,15,240,3003,4369,8738] z)) [5,15,240,3003,4369,34952] (b (b (bh z [5,15,240,3840,4369,8746,17476] [(96,78)] z) [5,15,240,3840,4881,17476] z) [5,15,240,3840,13107,21845] (b (b z [5,15,240,3840,21845,26214] z) [5,15,240,3840,21845,39321] z)))
def B9 : CertTree := (bh (bh (b (b z [5,15,240,4369,8738,17487,36744] z) [5,15,240,4369,8738,20292,34952] z) [5,15,240,4369,8738,20292,36744] [(104,79)] (b (b z [5,15,240,4369,8738,21845,36744] z) [5,15,240,4369,8738,36744,62532] z)) [5,15,240,4369,8738,45243] [(104,80)] (bh (bh (b z [5,15,240,4369,8751,20292] z) [5,15,240,4369,8751,62532] [(96,81)] z) [5,15,240,4369,8946,20292] [(104,16)] (b (b z [5,15,240,4369,8946,62532] z) [5,15,240,4369,13107,20292] z)))
def B10 : CertTree := (b (b (b (b z [5,15,240,4369,17476,63631] z) [5,15,240,4369,17476,63736] (b z [5,15,240,4369,17476,63743] z)) [5,15,240,4369,17476,64716] (b (b z [5,15,240,4369,20292,52428] z) [5,15,240,4369,20292,56797] z)) [5,15,240,4369,21845,63624] (bh (b (b z [5,15,240,4369,26214,62532] z) [5,15,240,4369,30583,62532] z) [5,15,240,4369,34952,64716] [(112,82)] (b (b z [5,15,240,4369,34959,62532] z) [5,15,240,4369,35064,62532] z)))
def B11 : CertTree := (b (b (b (b z [5,15,240,4369,48059,63624] z) [5,15,240,4369,52428,62532] z) [5,15,240,4369,56797,62532] (b (bh z [5,15,240,4369,61986,62532] [(96,81)] z) [5,15,240,4369,62532,63078] z)) [5,15,240,4369,62532,63624] (bh (bh (bh z [5,15,240,4369,62532,64716] [(112,83)] z) [5,15,240,4369,63624,64716] [(112,84)] z) [5,15,240,4383,8738,17476,36744] [(72,72)] (b (b z [5,15,240,7953,17476,63624] z) [5,15,240,7953,34952,62532] z)))
def B12 : CertTree := (b (b (b (b z [5,15,240,8738,13107,62532] z) [5,15,240,8738,20292,61166] (bh z [5,15,240,8738,21845,62532] [(72,85)] z)) [5,15,240,8738,61166,62532] (b (b z [5,15,240,8738,62532,62805] z) [5,15,240,13107,21845,61440] z)) [5,15,240,17476,61166,63624] (bh (b (bh z [5,15,240,17476,61713,61986] [(128,81)] z) [5,15,240,17476,61713,63624] z) [5,15,240,17476,63624,63897] [(112,84)] (b (b z [5,15,240,21845,26214,61440] z) [5,15,240,21845,34952,62532] z)))
def B13 : CertTree := (b (bh (b (b z [5,15,240,21845,52428,61440] z) [5,15,240,34952,61166,62532] z) [5,15,240,34952,62532,62805] [(112,83)] (b (b z [5,15,255,4369,8738,20292] z) [5,15,255,4369,8738,62532] z)) [5,15,255,4369,34952,62532] (bh (bh (bh z [5,15,256,3840,34952,61986] [(56,86),(136,86)] z) [5,15,256,8738,36744,61440] [(56,87),(80,87)] z) [5,15,1024,3840,34952,61986] [(56,39)] (bh (bh z [5,15,1536,4369,17476,61440] [(80,88)] z) [5,15,1536,8738,34952,61440] [(104,89),(144,90),(152,29)] z)))
def B14 : CertTree := (b (b (b (b z [5,15,1911,3840,4369,17476] z) [5,15,1911,3840,8738,17476] (bh z [5,15,2048,7953,17476,61440] [(56,91),(104,91),(136,91)] z)) [5,15,2288,4369,17476,61440] (b (b z [5,15,3549,3840,4369,17476] z) [5,15,3549,3840,4369,34952] z)) [5,15,3549,3840,17476,34952] (b (b (b z [5,15,3840,4369,8738,17487,35064] z) [5,15,3840,4369,8738,21845,35064] z) [5,15,3840,4369,8738,64170] (bh (b z [5,15,3840,4369,8738,65416] z) [5,15,3840,4369,8946,17487,34952] [(172,76)] z)))
def B15 : CertTree := (bh (b (b (bh z [5,15,3840,4369,8946,20292,34952] [(176,79)] z) [5,15,3840,4369,8946,21845] z) [5,15,3840,4369,8946,21845,34952] (b (b z [5,15,3840,4369,8946,48059] z) [5,15,3840,4369,8959,17476] z)) [5,15,3840,4369,13107,63624] [(80,93)] (b (b (b z [5,15,3840,4369,17476,30471] z) [5,15,3840,4369,17476,35071] z) [5,15,3840,4369,17476,56589] (b (bh z [5,15,3840,4369,17476,61999] [(56,94)] z) [5,15,3840,4369,17476,63631] z)))
def B16 : CertTree := (b (b (b (bh z [5,15,3840,4369,21845,35064] [(72,96)] z) [5,15,3840,4369,21845,61986] (b z [5,15,3840,4369,21845,63624] z)) [5,15,3840,4369,30583,61986] (b (b z [5,15,3840,4369,34952,64170] z) [5,15,3840,4369,35064,48059] z)) [5,15,3840,4369,36744,61986] (b (b (b z [5,15,3840,4369,39321,61986] z) [5,15,3840,4369,43690,61986] z) [5,15,3840,4369,43690,63624] (bh (b z [5,15,3840,4369,48059,61986] z) [5,15,3840,4369,48059,63624] [(80,97)] z)))
def B17 : CertTree := (bh (bh (bh (b z [5,15,3840,4369,61986,62532] z) [5,15,3840,4369,61986,63078] [(112,98)] z) [5,15,3840,4369,61986,64170] [(112,99)] (bh (bh z [5,15,3840,4369,62532,63624] [(80,100)] z) [5,15,3840,4369,63624,64170] [(112,101)] z)) [5,15,3840,4369,63624,64716] [(80,102)] (b (b (bh z [5,15,3840,4383,8738,17476,35064] [(72,70)] z) [5,15,3840,4383,8738,63624] z) [5,15,3840,4383,8946,17476,34952] (b (b z [5,15,3840,4383,34952,61986] z) [5,15,3840,4881,17476,61440] z)))
def B18 : CertTree := (b (bh (b (bh z [5,15,3840,7953,17476,63624] [(80,97)] z) [5,15,3840,8738,17476,64170] (b z [5,15,3840,8738,17487,63624] z)) [5,15,3840,8738,35976,61440] [(152,38)] (b (b z [5,15,3840,8738,39321,63624] z) [5,15,3840,8738,48059,63624] z)) [5,15,3840,8738,52428,63624] (b (b (bh z [5,15,3840,8738,61166,63624] [(108,29)] z) [5,15,3840,8738,61713,62532] z) [5,15,3840,8738,61713,63624] (bh (b z [5,15,3840,8738,62532,63624] z) [5,15,3840,8738,63624,63897] [(112,101)] z)))
def B19 : CertTree := (b (b (b (b z [5,15,3840,8946,17476,21845] z) [5,15,3840,8946,17476,61166] z) [5,15,3840,12066,17476,63624] (b (b z [5,15,3840,13107,21845,61440] z) [5,15,3840,13107,34952,61986] z)) [5,15,3840,13107,43690,61440] (b (b (bh z [5,15,3840,17476,21845,35064] [(72,104)] z) [5,15,3840,17476,21845,61986] z) [5,15,3840,17476,21845,63624] (b (b z [5,15,3840,17476,26214,63624] z) [5,15,3840,17476,30583,61986] z)))
def B20 : CertTree := (b (b (b (b z [5,15,3840,17476,34952,65314] z) [5,15,3840,17476,35064,61166] (b z [5,15,3840,17476,43690,61986] z)) [5,15,3840,17476,43690,63624] (b (b z [5,15,3840,17476,52428,61986] z) [5,15,3840,17476,56797,63624] z)) [5,15,3840,17476,61166,61986] (bh (b (b z [5,15,3840,17476,61166,63624] z) [5,15,3840,17476,61713,61986] z) [5,15,3840,17476,61713,63624] [(104,105)] (bh (bh z [5,15,3840,17476,61986,62259] [(112,98)] z) [5,15,3840,17476,61986,64170] [(112,106)] z)))
def B21 : CertTree := (bh (b (b (bh z [5,15,3840,17476,63624,64170] [(112,103)] z) [5,15,3840,17487,34952,61986] z) [5,15,3840,21845,26214,61440] (b (b z [5,15,3840,21845,39321,61440] z) [5,15,3840,21845,52428,61440] z)) [5,15,3840,26214,34952,61986] [(84,90)] (bh (b (b z [5,15,3840,26214,43690,61440] z) [5,15,3840,34952,48059,61986] z) [5,15,3840,34952,61166,61986] [(108,90)] (bh (b z [5,15,3840,34952,61713,61986] z) [5,15,3840,34952,61713,62532] [(104,107)] z)))
def B22 : CertTree := (b (b (bh (b z [5,15,3840,34952,61986,62532] z) [5,15,3840,34952,61986,63078] [(112,106),(140,90)] (b z [5,15,3840,39321,43690,61440] z)) [5,15,3840,43690,52428,61440] (b (b z [5,15,3855,4369,8738,63624] z) [5,15,3855,4369,8946,17476] z)) [5,15,3855,4369,17476,35064] (b (b (bh z [5,15,3855,4369,17476,61986] [(128,94)] z) [5,15,3855,4369,17476,63624] z) [5,15,3855,4369,34952,61986] (b (b z [5,15,3855,8738,17476,63624] z) [5,15,3855,17476,34952,61986] z)))
def B23 : CertTree := (b (b (b (b z [5,15,4080,7953,17476,34952] z) [5,15,4095,4369,8738,36744] z) [5,15,4095,4369,17476,35064] (b (b z [5,15,4095,7953,17476,34952] z) [5,15,4369,4593,8738,62532] z)) [5,15,4369,4593,17476,63624] (bh (b (b z [5,15,4369,4593,34952,62532] z) [5,15,4369,7953,17476,61986] z) [5,15,4369,7953,17476,63624] [(80,97)] (bh (bh z [5,15,4369,8738,8946,20292] [(112,16)] z) [5,15,4369,8738,8946,20292,34952] [(184,108)] z)))
def B24 : CertTree := (b (b (b (b z [5,15,4369,8738,20292,65280] z) [5,15,4369,8738,20292,65295] (bh z [5,15,4369,8738,28791,61440] [(104,89)] z)) [5,15,4369,8738,36744,61455] (b (b z [5,15,4369,8738,36744,61986] z) [5,15,4369,8738,36744,63624] z)) [5,15,4369,8738,36744,65280] (b (b (b z [5,15,4369,8738,36744,65416] z) [5,15,4369,8738,61440,65416] z) [5,15,4369,8738,61695,63624] (bh (b z [5,15,4369,8738,62532,65280] z) [5,15,4369,8738,62532,65295] [(72,94)] z)))
def B25 : CertTree := (bh (b (bh (b z [5,15,4369,8738,63624,65416] z) [5,15,4369,8946,17476,20292] [(96,109),(152,16)] z) [5,15,4369,8946,17476,20292,34952] (b (b z [5,15,4369,8946,17476,61680] z) [5,15,4369,8946,17476,61695] z)) [5,15,4369,8946,20292] [(0,16),(4,16),(8,16),(12,16),(14,80),(97,110)] (b (bh (b z [5,15,4369,8946,20292,34952] z) [5,15,4369,8946,20292,34952,61440] [(200,111)] z) [5,15,4369,8946,20292,61440] (b (bh z [5,15,4369,17476,20292,35064] [(72,112)] z) [5,15,4369,17476,30471,61440] z)))
def B26 : CertTree := (b (b (b (b z [5,15,4369,17476,35064,61680] z) [5,15,4369,17476,35064,62532] (b z [5,15,4369,17476,35064,63736] z)) [5,15,4369,17476,35071,61440] (b (b z [5,15,4369,17476,39417,61440] z) [5,15,4369,17476,61440,63736] z)) [5,15,4369,17476,61440,63743] (b (b (bh z [5,15,4369,17476,61680,61986] [(128,81)] z) [5,15,4369,17476,61680,63624] z) [5,15,4369,17476,61695,61986] (bh (b z [5,15,4369,17476,63624,63736] z) [5,15,4369,17476,63624,65280] [(136,105)] z)))
def B27 : CertTree := (bh (b (b (b z [5,15,4369,17476,63624,65416] z) [5,15,4369,21845,35064,61440] z) [5,15,4369,34952,35064,62532] (bh (b z [5,15,4369,34952,36744,61986] z) [5,15,4369,34952,61695,61986] [(104,54)] z)) [5,15,4369,34952,62532,65280] [(136,107)] (bh (b (b z [5,15,4369,34952,62532,65295] z) [5,15,4369,35064,48059,61440] z) [5,15,4369,35064,61440,62532] [(104,113)] (b (b z [5,15,4369,36744,56797,61440] z) [5,15,4369,36744,61440,61986] z)))
def B28 : CertTree := (bh (b (b (b z [5,15,4593,8738,21845,61440] z) [5,15,4593,21845,34952,61440] (b z [5,15,7953,8738,17476,63624] z)) [5,15,7953,13107,17476,61440] (b (bh z [5,15,7953,17476,30583,61440] [(108,88)] z) [5,15,7953,17476,34952,61455] z)) [5,15,7953,17476,34952,63624] [(104,114),(112,93),(152,97)] (bh (b (b z [5,15,7953,17476,34959,61440] z) [5,15,7953,17476,52428,61440] z) [5,15,7953,17476,61440,63624] [(104,105),(112,100),(152,97)] (bh (bh z [5,15,7953,17476,63624] [(0,97),(4,97),(6,115),(8,97),(10,97),(12,97),(113,102)] z) [5,15,7953,34952,48059,61440] [(144,97)] z)))
def B29 : CertTree := (bh (b (b (b z [5,15,8738,13107,36744,61440] z) [5,15,8738,17476,36744,63624] z) [5,15,8738,17476,61695,63624] (b (b z [5,15,8738,17476,63624,65280] z) [5,15,8738,17476,63624,65416] z)) [5,15,8738,34952,61440,61951] [(104,54)] (bh (bh (b z [5,15,8738,34952,62532,65280] z) [5,15,8738,36744,52428,61440] [(136,54)] z) [5,15,8738,36744,61166,61440] [(116,89)] (b (b z [5,15,8738,36744,61440,61713] z) [5,15,17476,21845,35064,61440] z)))
def B30 : CertTree := (b (b (bh (bh z [5,15,17476,34952,57582,61440] [(112,116),(144,115)] z) [5,15,17476,34952,61440,65297] [(96,117),(104,107),(112,105)] (b z [5,15,17476,34952,61695,61986] z)) [5,15,17476,35064,61166,61440] (b (bh z [5,15,17476,35064,61440,61713] [(104,113)] z) [5,240,255,4369,8738,20292] z)) [5,240,255,4369,8738,62532] (b (b (b z [5,240,255,4369,17476,63624] z) [5,240,255,4369,34952,62532] z) [5,240,527,4369,17476,61440] (b (b z [5,240,3840,4369,8738,17487,34952] z) [5,240,3840,4369,8738,21855,34952] z)))
def B31 : CertTree := (b (b (bh (b z [5,240,3840,4369,34959,62532] z) [5,240,3840,4383,8738,17476,34952] [(168,70),(176,72)] z) [5,240,3840,4383,8738,17487,34952] (b (b z [5,240,3840,4383,8738,20292,34952] z) [5,240,3840,4383,8738,21845] z)) [5,240,3840,4383,8738,21845,34952] (bh (b (bh z [5,240,3840,4383,8738,21855,34952] [(176,118)] z) [5,240,3840,4383,8738,34952,62532] z) [5,240,3840,4383,21845,34952] [(128,96)] (b (b z [5,240,3840,8738,17487,21845] z) [5,240,3840,8738,17487,34952,61713] z)))
def B32 : CertTree := (b (b (bh (b z [5,240,3840,17476,34959,61713] z) [5,240,3840,17487,21845,34952] [(128,104)] (bh z [5,240,3855,4369,8738,20292] [(96,92)] z)) [5,240,3855,4369,8751,17476] (b (b z [5,240,4095,4369,8751,17476] z) [5,240,4369,4383,8738,20292] z)) [5,240,4369,4383,8738,20292,34952] (b (bh (bh z [5,240,4369,8738,8751,62532] [(112,81)] z) [5,240,4369,8738,17487,20292] [(72,109)] z) [5,240,4369,8738,17487,20292,34952] (bh (b z [5,240,4369,8738,17487,62532] z) [5,240,4369,8738,20292,20303] [(72,110)] z)))
def B33 : CertTree := (b (b (b (bh z [5,240,4369,8738,61455,62532] [(112,81)] z) [5,240,4369,8738,62532,62543] z) [5,240,4369,8738,62532,65520] (bh (b z [5,240,4369,8751,17476,61680] z) [5,240,4369,8751,17476,62532] [(104,85),(152,81)] z)) [5,240,4369,8751,21845,61440] (bh (b (b z [5,240,4369,8751,34952,62532] z) [5,240,4369,8751,48059,61440] z) [5,240,4369,8751,61440,62532] [(104,81),(112,81),(152,81)] (b (bh z [5,240,4369,8751,62532] [(0,81),(2,94),(4,81),(8,81),(12,81)] z) [5,240,4369,8959,17476,61440] z)))
def B34 : CertTree := (b (b (b (b z [5,240,4369,17476,26223,61440] z) [5,240,4369,17476,56784,61440] (bh z [5,240,4369,17476,61440,61999] [(96,81),(104,81),(112,81)] z)) [5,240,4369,17476,63624,65520] (b (bh z [5,240,4369,17487,20292,34952] [(128,112)] z) [5,240,4369,17487,34952,62532] z)) [5,240,4369,34952,61455,62532] (b (b (b z [5,240,4369,34952,62532,62543] z) [5,240,4369,34952,62532,65520] z) [5,240,7953,17476,34959,61440] (b (bh z [5,240,8738,17476,61455,61713] [(104,81)] z) [5,240,8738,17487,21845,61440] z)))
def B35 : CertTree := (b (b (bh (b z [5,240,8751,17476,61166,61440] z) [5,240,8751,17476,61440,61713] [(104,81),(112,81)] z) [5,240,17476,34952,61455,61713] (b (bh z [5,240,17487,21845,34952,61440] [(152,119)] z) [5,255,3855,4369,8738,17476] z)) [5,255,3855,4369,17476,34952] (b (b (b z [5,255,4080,4369,8738,17476] z) [5,255,4080,4369,17476,34952] z) [5,255,4369,8738,17476,61455] (b (b z [5,255,4369,8738,17476,61680] z) [5,255,4369,17476,34952,61455] z)))
def B36 : CertTree := (b (bh (bh (b z [5,3840,3855,4369,8738,63624] z) [5,3840,3855,4369,8946,17476] [(128,92)] (b z [5,3840,3855,4369,17476,35064] z)) [5,3840,3855,4369,17476,61986] [(96,95)] (b (b z [5,3840,3855,4369,17476,63624] z) [5,3840,3855,4369,34952,61986] z)) [5,3840,3855,8738,17476,63624] (b (bh (b z [5,3840,3855,17476,34952,61986] z) [5,3840,4369,4383,8738,17476,35064] [(80,70)] z) [5,3840,4369,4383,8946,17476] (bh (b z [5,3840,4369,4383,8946,17476,34952] z) [5,3840,4369,4383,17476,35064] [(104,96)] z)))
def B37 : CertTree := (b (b (b (bh z [5,3840,4369,8738,17487,35064] [(146,120)] z) [5,3840,4369,8738,17487,35064,61440] z) [5,3840,4369,8738,61455,62532] (bh (b z [5,3840,4369,8738,63624,65520] z) [5,3840,4369,8946,17476,17487] [(96,109)] z)) [5,3840,4369,8946,17476,17487,34952] (b (bh (b z [5,3840,4369,8946,17476,65520] z) [5,3840,4369,8946,17487,34952] [(146,121),(158,76)] z) [5,3840,4369,8946,17487,34952,61440] (b (bh z [5,3840,4369,17476,17487,35064] [(72,112),(80,104)] z) [5,3840,4369,17476,35064,65520] z)))
def B38 : CertTree := (b (b (bh (b z [5,3840,4369,17476,63624,65520] z) [5,3840,4369,34952,61455,62532] [(56,107)] (b z [5,3840,4369,34952,61986,65520] z)) [5,3840,4383,8738,34952,61455] (b (bh z [5,3840,4383,8946,17476,34952] [(118,123),(130,122),(146,124)] z) [5,3840,4383,8946,17476,34952,61440] z)) [5,3840,8738,17476,61455,61713] (b (b (b z [5,3840,8738,17476,63624,65520] z) [5,3840,8738,17487,34952,61455] z) [5,3840,8738,34952,61455,61713] (bh (b z [5,3840,8738,34952,61455,62532] z) [5,3840,17476,34952,61455,61713] [(128,117)] z)))
def B39 : CertTree := (b (bh (b (b z [5,3855,4080,4369,8738,17476] z) [5,3855,4080,4369,17476,34952] z) [5,3855,4369,8738,17476,61455] [(144,94)] (bh (b z [5,3855,4369,8738,17476,65280] z) [5,3855,4369,8738,20292,61440] [(144,95)] z)) [5,3855,4369,8738,34952,61455] (b (bh (b z [5,3855,4369,8738,34952,65280] z) [5,3855,4369,8751,17476,61440] [(144,94)] z) [5,3855,4369,17476,34952,61455] (b (b z [5,3855,4369,17476,34952,65280] z) [5,3855,8738,17476,34952,61455] z)))
def B40 : CertTree := (b (bh (b (b z [5,3855,8738,17487,34952,61440] z) [5,3855,12066,17476,34952,61440] (b z [5,4369,4593,8751,17476,61440] z)) [5,4369,8738,17476,61455,61680] [(104,81)] (b (b z [5,4369,8738,17487,35064,61440] z) [5,4369,8738,34952,61455,65280] z)) [5,4369,8738,36744,61440,61455] (bh (bh (b z [5,4369,8738,36744,61440,65520] z) [5,4369,8751,17476,61440,61680] [(104,81)] z) [5,4369,8751,17476,61440,65295] [(112,94)] (b (b z [5,4369,17476,17487,35064,61440] z) [5,4369,17476,34952,61455,61680] z)))
def B41 : CertTree := (bh (b (b (b z [5,4369,17476,35064,61440,61455] z) [5,4369,17476,35064,61440,65520] z) [5,4593,8751,17476,34952,61440] (b (bh z [5,7953,17476,34952,61440,61455] [(96,117),(104,107)] z) [5,7953,17476,34952,61440,65520] z)) [6,8,15,240,3840,4369,8738,17476] [(72,10),(96,10)] (bh (bh (bh z [6,15,240,512,3840,4369,17476] [(72,11),(80,11)] z) [6,15,240,512,4369,17476,61440] [(112,12)] z) [6,15,240,2048,3840,4369,17476] [(72,13),(80,13),(184,13)] (bh (bh z [6,15,240,2048,4369,17476,61440] [(144,14),(184,14)] z) [6,15,240,3840,4369,8738,17476,34952] [(136,2),(224,3),(232,4)] z)))
def B42 : CertTree := (b (b (b (bh z [6,15,240,3840,4369,8738,20292] [(184,1)] z) [6,15,240,3840,4369,8738,20292,34952] (b z [6,15,240,3840,4369,8738,21845] z)) [6,15,240,3840,4369,8738,21845,34952] (b (bh z [6,15,240,3840,4369,8738,26214] [(152,15)] z) [6,15,240,3840,4369,8738,34952,62532] z)) [6,15,240,3840,4369,8738,48059] (bh (b (b z [6,15,240,3840,4369,8738,62532] z) [6,15,240,3840,4369,8751,17476] z) [6,15,240,3840,4369,8946,17476] [(136,16)] (b (b z [6,15,240,3840,4369,13107,17476] z) [6,15,240,3840,4369,17476,26214] z)))
def B43 : CertTree := (b (b (bh (b z [6,15,240,3840,4369,17476,34959] z) [6,15,240,3840,4369,17476,35064] [(176,18)] z) [6,15,240,3840,4369,17476,39321] (b (b z [6,15,240,3840,4369,17476,52428] z) [6,15,240,3840,4369,17476,56797] z)) [6,15,240,3840,4369,17476,61986] (b (b (b z [6,15,240,3840,4369,17476,63624] z) [6,15,240,3840,4369,21845,34952] z) [6,15,240,3840,4369,34952,48059] (b (bh z [6,15,240,3840,4369,34952,52428] [(144,19),(152,19)] z) [6,15,240,3840,4369,34952,62532] z)))
def B44 : CertTree := (b (b (bh (b z [6,15,240,3840,7953,17476,34952] z) [6,15,240,3840,8738,13107,17476] [(192,15)] (b z [6,15,240,3840,8738,17476,21845] z)) [6,15,240,3840,8738,17476,34952,61713] (b (b z [6,15,240,3840,8738,17476,61166] z) [6,15,240,3840,8738,17476,61713] z)) [6,15,240,3840,17476,21845,34952] (b (b (bh z [6,15,240,3840,17476,34952,39321] [(152,19)] z) [6,15,240,3840,17476,34952,61166] z) [6,15,240,3840,17476,34952,61713] (b (b z [6,15,240,3855,4369,8738,17476] z) [6,15,240,3855,4369,17476,34952] z)))
def B45 : CertTree := (b (b (b (b z [6,15,240,4080,4369,17476,34952] z) [6,15,240,4095,4369,8738,17476] z) [6,15,240,4095,4369,17476,34952] (b (bh z [6,15,240,4369,8738,17476,20292] [(200,1)] z) [6,15,240,4369,8738,17476,20292,34952] z)) [6,15,240,4369,8738,17476,61455] (bh (b (b z [6,15,240,4369,8738,17476,61680] z) [6,15,240,4369,8738,17476,61695] z) [6,15,240,4369,8738,17476,62532] [(200,20)] (bh (bh z [6,15,240,4369,8738,20292] [(0,1),(4,1),(8,1),(12,1),(16,1)] z) [6,15,240,4369,8738,20292,34952] [(106,21),(178,21),(194,21)] z)))
def B46 : CertTree := (bh (b (b (b z [6,15,240,4369,8738,20292,61440] z) [6,15,240,4369,8738,21845,61440] (bh z [6,15,240,4369,8738,26214,61440] [(112,23)] z)) [6,15,240,4369,8738,34952,62532] (bh (b z [6,15,240,4369,8738,48059,61440] z) [6,15,240,4369,8738,61440,62532] [(144,24),(200,20)] z)) [6,15,240,4369,8738,62532] [(0,20),(4,20),(8,20),(12,20),(16,20)] (b (b (bh z [6,15,240,4369,8751,17476,61440] [(96,25)] z) [6,15,240,4369,8946,17476,61440] z) [6,15,240,4369,13107,17476,61440] (b (b z [6,15,240,4369,17476,20292,34952] z) [6,15,240,4369,17476,26214,61440] z)))
def B47 : CertTree := (b (bh (b (bh z [6,15,240,4369,17476,34952,61455] [(136,26)] z) [6,15,240,4369,17476,34952,61680] z) [6,15,240,4369,17476,34952,61695] [(136,27)] (bh (bh z [6,15,240,4369,17476,34952,62532] [(192,28)] z) [6,15,240,4369,17476,34952,63624] [(136,29),(144,29),(152,29),(200,30)] z)) [6,15,240,4369,17476,34959,61440] (b (b (bh z [6,15,240,4369,17476,35064,61440] [(136,31)] z) [6,15,240,4369,17476,39321,61440] z) [6,15,240,4369,17476,52428,61440] (b (b z [6,15,240,4369,17476,56797,61440] z) [6,15,240,4369,17476,61440,61986] z)))
def B48 : CertTree := (b (bh (b (bh z [6,15,240,4369,17476,63624] [(0,30),(4,30),(8,30),(12,30),(16,30),(58,32),(113,33)] z) [6,15,240,4369,21845,34952,61440] (b z [6,15,240,4369,34952,48059,61440] z)) [6,15,240,4369,34952,52428,61440] [(112,34),(192,29)] (bh (bh z [6,15,240,4369,34952,61440,62532] [(144,35),(200,28)] z) [6,15,240,4369,34952,62532] [(0,28),(4,28),(8,28),(12,28),(16,28),(113,36)] z)) [6,15,240,7953,17476,34952,61440] (b (b (bh z [6,15,240,8738,13107,17476,61440] [(144,23)] z) [6,15,240,8738,17476,21845,61440] z) [6,15,240,8738,17476,61166,61440] (bh (bh z [6,15,240,8738,17476,61440,61713] [(152,24)] z) [6,15,240,17476,21845,34952,61440] [(200,33)] z)))
def B49 : CertTree := (bh (b (bh (b z [6,15,240,17476,34952,61166,61440] z) [6,15,240,17476,34952,61440,61713] [(144,35)] z) [6,15,255,3840,4369,8738,17476] (b (b z [6,15,255,3840,4369,17476,34952] z) [6,15,255,4369,8738,17476,61440] z)) [6,15,255,4369,17476,34952,61440] [(200,32)] (bh (bh (bh z [6,15,256,3840,8738,34952,61440] [(56,37),(104,37),(176,37),(200,38)] z) [6,15,512,3840,4369,17476,61440] [(56,11),(176,11)] z) [6,15,1024,3840,8738,34952,61440] [(56,39),(176,39),(200,38)] (b (bh z [6,15,2048,3840,4369,17476,61440] [(56,40),(136,40),(176,40)] z) [6,15,3840,4080,4369,8738,17476] z)))
def B50 : CertTree := (bh (b (b (b z [6,15,3840,4095,4369,8738,17476] z) [6,15,3840,4095,4369,8738,34952] (b z [6,15,3840,4095,4369,17476,34952] z)) [6,15,3840,4095,8738,17476,34952] (b (bh z [6,15,3840,4369,8738,8946,17476] [(152,16)] z) [6,15,3840,4369,8738,17476,61455] z)) [6,15,3840,4369,8738,17476,61986] [(112,15),(152,15),(192,41)] (b (b (b z [6,15,3840,4369,8738,17476,63624] z) [6,15,3840,4369,8738,17476,65280] z) [6,15,3840,4369,8738,17476,65295] (b (b z [6,15,3840,4369,8738,20292,61440] z) [6,15,3840,4369,8738,21845,61440] z)))
def B51 : CertTree := (bh (bh (b (b z [6,15,3840,4369,8738,30583,61440] z) [6,15,3840,4369,8738,34952,61455] z) [6,15,3840,4369,8738,34952,61986] [(192,43)] (b (bh z [6,15,3840,4369,8738,34952,63624] [(200,44)] z) [6,15,3840,4369,8738,34952,65280] z)) [6,15,3840,4369,8738,36744,61440] [(136,8)] (b (b (bh z [6,15,3840,4369,8738,39321,61440] [(112,45),(136,8)] z) [6,15,3840,4369,8738,43690,61440] z) [6,15,3840,4369,8738,48059,61440] (bh (b z [6,15,3840,4369,8738,61440,62532] z) [6,15,3840,4369,8738,61440,63624] [(152,46),(200,44)] z)))
def B52 : CertTree := (bh (b (bh (b z [6,15,3840,4369,8751,17476,61440] z) [6,15,3840,4369,8946,17476] [(0,16),(4,16),(8,16),(12,16),(16,16)] (b z [6,15,3840,4369,8946,17476,61440] z)) [6,15,3840,4369,13107,17476,61440] (b (bh z [6,15,3840,4369,13107,34952,61440] [(80,47),(136,48),(144,45)] z) [6,15,3840,4369,17476,26214,61440] z)) [6,15,3840,4369,17476,30583,61440] [(140,49)] (b (b (bh z [6,15,3840,4369,17476,34952,35064] [(136,19),(200,18)] z) [6,15,3840,4369,17476,34952,61455] z) [6,15,3840,4369,17476,34952,61986] (b (bh z [6,15,3840,4369,17476,34952,63624] [(136,50),(144,50),(152,50),(200,51)] z) [6,15,3840,4369,17476,34952,65280] z)))
def B53 : CertTree := (b (b (bh (b z [6,15,3840,4369,17476,34959,61440] z) [6,15,3840,4369,17476,35064] [(0,18),(4,18),(6,27),(8,18),(12,18),(16,18)] z) [6,15,3840,4369,17476,35064,61440] (b (b z [6,15,3840,4369,17476,39321,61440] z) [6,15,3840,4369,17476,52428,61440] z)) [6,15,3840,4369,17476,56797,61440] (bh (bh (bh z [6,15,3840,4369,17476,61440,61986] [(200,41)] z) [6,15,3840,4369,17476,61440,63624] [(200,51)] z) [6,15,3840,4369,17476,61986] [(0,41),(4,41),(8,41),(12,41),(16,41)] (b (bh z [6,15,3840,4369,17476,63624] [(0,51),(4,51),(6,30),(8,51),(12,51),(16,51)] z) [6,15,3840,4369,21845,34952,61440] z)))
def B54 : CertTree := (b (bh (bh (b z [6,15,3840,4369,34952,48059,61440] z) [6,15,3840,4369,34952,52428,61440] [(80,52),(104,50),(112,53),(192,50)] (b z [6,15,3840,4369,34952,56797,61440] z)) [6,15,3840,4369,34952,61440,61986] [(152,46),(200,43)] (bh (b z [6,15,3840,4369,34952,61440,62532] z) [6,15,3840,4369,34952,61986] [(0,43),(4,43),(8,43),(12,43),(16,43),(81,43),(113,54)] z)) [6,15,3840,4383,8738,34952,61440] (bh (bh (bh z [6,15,3840,7953,17476,34952,61440] [(80,5)] z) [6,15,3840,8738,13107,17476,61440] [(144,42),(184,15)] z) [6,15,3840,8738,13107,34952,61440] [(200,38)] (b (b z [6,15,3840,8738,17476,21845,61440] z) [6,15,3840,8738,17476,30583,61440] z)))
def B55 : CertTree := (b (b (bh (bh z [6,15,3840,8738,17476,34952,61986] [(184,55)] z) [6,15,3840,8738,17476,34952,63624] [(200,56)] z) [6,15,3840,8738,17476,34952,65280] (bh (b z [6,15,3840,8738,17476,43690,61440] z) [6,15,3840,8738,17476,52428,61440] [(112,57)] z)) [6,15,3840,8738,17476,61166,61440] (bh (bh (b z [6,15,3840,8738,17476,61440,61713] z) [6,15,3840,8738,17476,61440,63624] [(144,58),(200,56)] z) [6,15,3840,8738,17476,63624] [(0,56),(4,56),(8,56),(12,56),(16,56),(110,38),(114,38)] (bh (b z [6,15,3840,8738,17487,34952,61440] z) [6,15,3840,8738,26214,34952,61440] [(200,38)] z)))
def B56 : CertTree := (b (b (bh (b z [6,15,3840,8738,34952,48059,61440] z) [6,15,3840,8738,34952,52428,61440] [(184,54)] (bh z [6,15,3840,8738,34952,61166,61440] [(140,59)] z)) [6,15,3840,8738,34952,61440,61713] (b (b z [6,15,3840,8738,34952,61440,62532] z) [6,15,3840,12066,17476,34952,61440] z)) [6,15,3840,17476,21845,34952,61440] (b (bh (bh z [6,15,3840,17476,26214,34952,61440] [(144,57)] z) [6,15,3840,17476,34952,39321,61440] [(112,53),(136,5),(192,50)] z) [6,15,3840,17476,34952,43690,61440] (b (b z [6,15,3840,17476,34952,56797,61440] z) [6,15,3840,17476,34952,61166,61440] z)))
def B57 : CertTree := (b (b (bh (bh z [6,15,3840,17476,34952,61440,61986] [(152,58),(200,55)] z) [6,15,3840,17476,34952,61986] [(0,55),(4,55),(8,55),(12,55),(16,55),(113,54)] z) [6,15,3855,4369,8738,17476,61440] (b (b z [6,15,3855,4369,8738,34952,61440] z) [6,15,3855,4369,17476,34952,61440] z)) [6,15,3855,8738,17476,34952,61440] (b (b (b z [6,15,4369,4593,8738,17476,61440] z) [6,15,4369,4593,17476,34952,61440] z) [6,15,4369,7953,8738,17476,61440] (b (bh z [6,15,4369,7953,17476,34952,61440] [(80,5)] z) [6,15,4369,8738,17476,36744,61440] z)))
def B58 : CertTree := (bh (bh (bh (b z [6,15,4369,8738,17476,61440,61695] z) [6,15,4369,8738,17476,61440,65280] [(128,60)] (b z [6,15,4369,8738,17476,61440,65295] z)) [6,15,4369,8738,34952,36744,61440] [(152,8)] (b (b z [6,15,4369,8738,34952,61440,61695] z) [6,15,4369,8738,34952,61440,65280] z)) [6,15,4369,8738,36744,61440] [(0,8),(4,8),(8,8),(12,8),(16,8),(82,48),(106,8)] (bh (b (bh z [6,15,4369,17476,34952,35064,61440] [(152,31),(192,29)] z) [6,15,4369,17476,34952,61440,61680] z) [6,15,4369,17476,34952,61440,61695] [(152,30)] (b (b z [6,15,4369,17476,34952,61440,65280] z) [6,15,4369,17476,34952,61440,65295] z)))
def B59 : CertTree := (b (b (bh (b z [6,15,7953,8738,17476,34952,61440] z) [6,15,7953,17476,34952,61440] [(0,5),(4,5),(8,5),(12,5),(16,5),(105,5),(113,52)] z) [6,15,8738,17476,34952,36744,61440] (bh (b z [6,15,8738,17476,34952,61440,61695] z) [6,15,8738,17476,34952,61440,65280] [(128,61)] z)) [6,240,255,3840,4369,8738,17476] (b (b (b z [6,240,255,3840,4369,17476,34952] z) [6,240,255,4369,8738,17476,61440] z) [6,240,255,4369,17476,34952,61440] (b (b z [6,240,3840,3855,4369,8738,17476] z) [6,240,3840,3855,4369,17476,34952] z)))
def B60 : CertTree := (b (b (b (bh z [6,240,3840,4369,4383,8738,17476,34952] [(224,62)] z) [6,240,3840,4369,4383,17476,34952] (b z [6,240,3840,4369,8738,17476,17487] z)) [6,240,3840,4369,8738,17476,17487,34952] (bh (b z [6,240,3840,4369,8738,17476,65520] z) [6,240,3840,4369,8738,17487,34952] [(97,63),(98,64),(169,65),(170,64),(177,66),(194,64)] z)) [6,240,3840,4369,8738,17487,34952,61440] (b (b (b z [6,240,3840,4369,8751,17476,61440] z) [6,240,3840,4369,17476,17487,34952] z) [6,240,3840,4369,17476,34952,65520] (bh (b z [6,240,3840,4369,17476,34959,61440] z) [6,240,3840,4383,8738,17476,34952] [(97,67),(98,68),(134,69),(168,70),(169,71),(170,68),(176,72),(177,62),(178,68),(194,68)] z)))
def B61 : CertTree := (b (b (b (bh z [6,240,4369,8738,8751,17476,61440] [(112,25)] z) [6,240,4369,8738,17476,17487,61440] z) [6,240,4369,8738,17476,61440,61455] (b (b z [6,240,4369,8738,17476,61440,65520] z) [6,240,4369,8738,17487,34952,61440] z)) [6,240,4369,8751,17476,34952,61440] (b (b (bh z [6,240,4369,8751,17476,61440] [(0,25),(4,25),(8,25),(12,25),(16,25)] z) [6,240,4369,17476,17487,34952,61440] z) [6,240,4369,17476,34952,61440,61455] (b (b z [6,240,4369,17476,34952,61440,65520] z) [6,3840,3855,4369,8738,17476,61440] z)))
def B62 : CertTree := (b (b (b (b z [6,3840,3855,4369,17476,34952,61440] z) [6,3840,3855,8738,17476,34952,61440] (bh z [6,3840,4369,8738,17476,61440,61455] [(128,60)] z)) [6,3840,4369,8738,17476,61440,65520] (b (b z [6,3840,4369,8738,34952,61440,61455] z) [6,3840,4369,8738,34952,61440,65520] z)) [6,3840,4369,17476,34952,61440,61455] (b (bh (b z [6,3840,4369,17476,34952,61440,65520] z) [6,3840,8738,17476,34952,61440,61455] [(128,61)] z) [6,3840,8738,17476,34952,61440,65520] (bh (bh z [7,15,240,3840,4369,8738,17476] [(0,1),(4,1),(8,1),(12,1),(16,1),(20,1)] z) [7,15,240,3840,4369,8738,17476,34952] [(136,2),(137,2),(138,0),(182,0),(224,3),(225,3),(226,0),(232,4),(233,4),(234,0),(250,0)] z)))
def B63 : CertTree := (bh (b (bh (b z [7,15,240,3840,4369,8738,17476,61440] z) [7,15,240,3840,4369,17476,34952] [(0,5),(4,5),(8,5),(12,5),(16,5),(20,5),(185,5)] z) [7,15,240,3840,4369,17476,34952,61440] (bh (bh z [7,15,240,4369,8738,17476,34952,61440] [(80,6),(176,7),(256,4)] z) [7,15,240,4369,8738,17476,61440] [(0,1),(4,1),(8,1),(12,1),(16,1),(20,1)] z)) [7,15,240,4369,17476,34952,61440] [(0,5),(4,5),(8,5),(12,5),(16,5),(20,5)] (bh (bh (b z [7,15,3840,4369,8738,17476,34952,61440] z) [7,15,3840,4369,8738,17476,61440] [(0,1),(4,1),(8,1),(12,1),(16,1),(20,1)] z) [7,15,3840,4369,8738,34952,61440] [(0,8),(4,8),(8,8),(12,8),(16,8),(20,8),(81,8)] (bh (bh z [7,15,3840,4369,17476,34952,61440] [(0,5),(4,5),(8,5),(12,5),(16,5),(20,5),(137,5)] z) [7,15,3840,8738,17476,34952,61440] [(0,9),(4,9),(8,9),(12,9),(16,9),(20,9)] z)))
def allData : CertTree := (b (bh (b (b (b (b B0 [4,15,240,4369,8746,20292] B1) [4,15,3840,52428,64170] (b B2 [4,15,17476,63624,65433] B3)) [4,240,4383,8738,17487,36744] (b (b B4 [4,3840,4369,8738,21855,35064] B5) [4,3840,8946,17487,21845] (b B6 [4,4369,17487,35064,62532] B7))) [5,15,80,3840,4369,8738,34952] (b (b (b B8 [5,15,240,3840,21845,52428] B9) [5,15,240,4369,13107,62532] (b B10 [5,15,240,4369,39321,62532] B11)) [5,15,240,8738,13107,20292] (b (b B12 [5,15,240,21845,39321,61440] B13) [5,15,1911,3840,4369,8738] (bh B14 [5,15,3840,4369,8946,20292] [(56,92),(136,16)] B15)))) [5,15,3840,4369,20292,61986] [(56,95)] (b (b (b (b B16 [5,15,3840,4369,56797,63624] B17) [5,15,3840,7953,17476,35064] (bh B18 [5,15,3840,8738,63624,64716] [(112,103)] B19)) [5,15,3840,17476,34952,64170] (bh (b B20 [5,15,3840,17476,63624,63897] B21) [5,15,3840,34952,61986,62259] [(112,99)] (b B22 [5,15,4080,4369,17476,35064] B23))) [5,15,4369,8738,17476,20292,35064] (b (b (b B24 [5,15,4369,8738,63624,65280] B25) [5,15,4369,17476,35064,36856] (b B26 [5,15,4369,17476,63624,65295] B27)) [5,15,4383,8738,36744,61440] (bh (bh B28 [5,15,7953,34952,61440,62532] [(96,107),(104,107),(112,100)] B29) [5,15,17476,34952,36744,61986] [(80,54)] (b B30 [5,240,3840,4369,8751,62532] B31))))) [5,240,3840,8751,17476,61713] (bh (b (b (bh (b B32 [5,240,4369,8738,20292,65520] B33) [5,240,4369,17476,17487,63624] [(80,119)] (bh B34 [5,240,8751,17476,21845,61440] [(144,85)] B35)) [5,255,4369,17476,34952,61680] (b (b B36 [5,3840,4369,8738,17476,17487,35064] B37) [5,3840,4369,17476,61986,65520] (b B38 [5,3840,17476,34952,61986,65520] B39))) [5,3855,8738,17476,34952,65280] (b (b (bh B40 [5,4369,17476,34952,61455,65280] [(128,117)] B41) [6,15,240,3840,4369,8738,17487,34952] (bh B42 [6,15,240,3840,4369,17476,30583] [(188,17)] B43)) [6,15,240,3840,4383,8738,17476,34952] (bh (b B44 [6,15,240,4080,4369,8738,17476] B45) [6,15,240,4369,8738,20292,34952,61440] [(256,22)] (b B46 [6,15,240,4369,17476,30583,61440] B47)))) [6,15,240,4369,17476,61440,63624] [(200,30)] (bh (bh (b (bh B48 [6,15,240,17476,34952,39321,61440] [(112,34),(184,36),(192,29)] B49) [6,15,3840,4080,4369,17476,34952] (bh B50 [6,15,3840,4369,8738,26214,61440] [(112,42),(192,15)] B51)) [6,15,3840,4369,8738,63624] [(0,44),(4,44),(8,44),(12,44),(16,44),(81,44),(86,38),(113,38)] (b (b B52 [6,15,3840,4369,17476,34952,65295] B53) [6,15,3840,4369,34952,43690,61440] (b B54 [6,15,3840,8738,17476,34952,61455] B55))) [6,15,3840,8738,34952,39321,61440] [(184,54)] (b (b (b B56 [6,15,3840,17476,34952,61440,61713] B57) [6,15,4369,8738,17476,61440,61680] (bh B58 [6,15,4369,17476,35064,61440] [(0,31),(4,31),(8,31),(12,31),(16,31),(130,26)] B59)) [6,240,3840,4369,4383,8738,17476] (b (bh B60 [6,240,3840,4383,8738,17476,34952,61440] [(168,73),(176,74)] B61) [6,3840,3855,4369,8738,34952,61440] (bh B62 [7,15,240,3840,4369,8738,17476,34952,61440] [(136,0),(224,0),(232,0),(304,0),(320,0)] B63))))))
def T_cert : BT := allData.strip
theorem ok0 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B0=true := by decide +kernel
theorem ok1 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B1=true := by decide +kernel
theorem ok2 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B2=true := by decide +kernel
theorem ok3 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B3=true := by decide +kernel
theorem ok4 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B4=true := by decide +kernel
theorem ok5 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B5=true := by decide +kernel
theorem ok6 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B6=true := by decide +kernel
theorem ok7 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B7=true := by decide +kernel
theorem ok8 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B8=true := by decide +kernel
theorem ok9 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B9=true := by decide +kernel
theorem ok10 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B10=true := by decide +kernel
theorem ok11 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B11=true := by decide +kernel
theorem ok12 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B12=true := by decide +kernel
theorem ok13 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B13=true := by decide +kernel
theorem ok14 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B14=true := by decide +kernel
theorem ok15 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B15=true := by decide +kernel
theorem ok16 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B16=true := by decide +kernel
theorem ok17 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B17=true := by decide +kernel
theorem ok18 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B18=true := by decide +kernel
theorem ok19 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B19=true := by decide +kernel
theorem ok20 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B20=true := by decide +kernel
theorem ok21 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B21=true := by decide +kernel
theorem ok22 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B22=true := by decide +kernel
theorem ok23 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B23=true := by decide +kernel
theorem ok24 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B24=true := by decide +kernel
theorem ok25 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B25=true := by decide +kernel
theorem ok26 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B26=true := by decide +kernel
theorem ok27 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B27=true := by decide +kernel
theorem ok28 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B28=true := by decide +kernel
theorem ok29 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B29=true := by decide +kernel
theorem ok30 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B30=true := by decide +kernel
theorem ok31 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B31=true := by decide +kernel
theorem ok32 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B32=true := by decide +kernel
theorem ok33 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B33=true := by decide +kernel
theorem ok34 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B34=true := by decide +kernel
theorem ok35 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B35=true := by decide +kernel
theorem ok36 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B36=true := by decide +kernel
theorem ok37 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B37=true := by decide +kernel
theorem ok38 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B38=true := by decide +kernel
theorem ok39 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B39=true := by decide +kernel
theorem ok40 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B40=true := by decide +kernel
theorem ok41 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B41=true := by decide +kernel
theorem ok42 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B42=true := by decide +kernel
theorem ok43 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B43=true := by decide +kernel
theorem ok44 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B44=true := by decide +kernel
theorem ok45 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B45=true := by decide +kernel
theorem ok46 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B46=true := by decide +kernel
theorem ok47 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B47=true := by decide +kernel
theorem ok48 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B48=true := by decide +kernel
theorem ok49 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B49=true := by decide +kernel
theorem ok50 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B50=true := by decide +kernel
theorem ok51 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B51=true := by decide +kernel
theorem ok52 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B52=true := by decide +kernel
theorem ok53 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B53=true := by decide +kernel
theorem ok54 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B54=true := by decide +kernel
theorem ok55 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B55=true := by decide +kernel
theorem ok56 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B56=true := by decide +kernel
theorem ok57 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B57=true := by decide +kernel
theorem ok58 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B58=true := by decide +kernel
theorem ok59 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B59=true := by decide +kernel
theorem ok60 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B60=true := by decide +kernel
theorem ok61 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B61=true := by decide +kernel
theorem ok62 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B62=true := by decide +kernel
theorem ok63 : CertTree.check (stepOK M_ Y_ PD_ PM_ G_ T_cert) B63=true := by decide +kernel
theorem hT_cert : ∀k,T_cert.mem k=true → ∃h,stepOK M_ Y_ PD_ PM_ G_ T_cert k h=true := CertTree.local_ok (t:=allData) ((branch_ok (branch_ok (branch_ok (branch_ok (branch_ok (branch_ok ok0 (by decide +kernel) ok1) (by decide +kernel) (branch_ok ok2 (by decide +kernel) ok3)) (by decide +kernel) (branch_ok (branch_ok ok4 (by decide +kernel) ok5) (by decide +kernel) (branch_ok ok6 (by decide +kernel) ok7))) (by decide +kernel) (branch_ok (branch_ok (branch_ok ok8 (by decide +kernel) ok9) (by decide +kernel) (branch_ok ok10 (by decide +kernel) ok11)) (by decide +kernel) (branch_ok (branch_ok ok12 (by decide +kernel) ok13) (by decide +kernel) (branch_ok ok14 (by decide +kernel) ok15)))) (by decide +kernel) (branch_ok (branch_ok (branch_ok (branch_ok ok16 (by decide +kernel) ok17) (by decide +kernel) (branch_ok ok18 (by decide +kernel) ok19)) (by decide +kernel) (branch_ok (branch_ok ok20 (by decide +kernel) ok21) (by decide +kernel) (branch_ok ok22 (by decide +kernel) ok23))) (by decide +kernel) (branch_ok (branch_ok (branch_ok ok24 (by decide +kernel) ok25) (by decide +kernel) (branch_ok ok26 (by decide +kernel) ok27)) (by decide +kernel) (branch_ok (branch_ok ok28 (by decide +kernel) ok29) (by decide +kernel) (branch_ok ok30 (by decide +kernel) ok31))))) (by decide +kernel) (branch_ok (branch_ok (branch_ok (branch_ok (branch_ok ok32 (by decide +kernel) ok33) (by decide +kernel) (branch_ok ok34 (by decide +kernel) ok35)) (by decide +kernel) (branch_ok (branch_ok ok36 (by decide +kernel) ok37) (by decide +kernel) (branch_ok ok38 (by decide +kernel) ok39))) (by decide +kernel) (branch_ok (branch_ok (branch_ok ok40 (by decide +kernel) ok41) (by decide +kernel) (branch_ok ok42 (by decide +kernel) ok43)) (by decide +kernel) (branch_ok (branch_ok ok44 (by decide +kernel) ok45) (by decide +kernel) (branch_ok ok46 (by decide +kernel) ok47)))) (by decide +kernel) (branch_ok (branch_ok (branch_ok (branch_ok ok48 (by decide +kernel) ok49) (by decide +kernel) (branch_ok ok50 (by decide +kernel) ok51)) (by decide +kernel) (branch_ok (branch_ok ok52 (by decide +kernel) ok53) (by decide +kernel) (branch_ok ok54 (by decide +kernel) ok55))) (by decide +kernel) (branch_ok (branch_ok (branch_ok ok56 (by decide +kernel) ok57) (by decide +kernel) (branch_ok ok58 (by decide +kernel) ok59)) (by decide +kernel) (branch_ok (branch_ok ok60 (by decide +kernel) ok61) (by decide +kernel) (branch_ok ok62 (by decide +kernel) ok63)))))))
theorem no_seven :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 7 ∧ PEqualNP.Represents.Represents
        (fun u v : Fin 4 => (858 : ℕ).testBit (4 * u.val + v.val)) C :=
  signed_rep_lb 858 7 1 0 PD_ PM_ XS_ G_ T_cert (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel)
end PEqualNP.Outside.L_meta_19071_refutation

theorem PEqualNP.Outside.L_meta_19071_Negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (858 : ℕ).testBit (4 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19071_refutation.no_seven
