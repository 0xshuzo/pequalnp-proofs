import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19580_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



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


def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)


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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_ok (xs : List U4) : uvalid (ucalc xs) = true := by
  have c : ∀ (a : U4) (r : UBank), uvalid r = true → uvalid (ucons a r) = true := by decide +kernel
  induction xs with
  | nil => rfl
  | cons a r ih => exact c _ _ ih
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_perm {xs ys : List U4} (p : xs.Perm ys) : ucalc xs = ucalc ys := by
  have c : ∀ (a b : U4) (r : UBank), ucons a (ucons b r) = ucons b (ucons a r) := by decide +kernel
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (ucons a) ih
  | swap a b r => exact c _ _ _
  | trans p q hp hq => exact hp.trans hq
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_keep (k : Bool) (a : U4) (r : List U4) : ucalc (kept k a r) = ukeep k a (ucalc r) := by
  cases k <;> rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem uoneCost : ∀ (a : U4) (r : UBank) (neg save : Bool), uvalid r = true →
    ucost (ucons a r) ≤ 1 + save.toNat + ucost (ucons (if neg then unot a else a) (ukeep save a r)) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem utwoCost : ∀ (a b : U4) (r : UBank) (op ka kb : Bool), uvalid r = true →
    ucost (ucons a (ucons b r)) ≤ ka.toNat + kb.toNat +
      ucost (ucons (if op then uand a b else uor a b) (ukeep ka a (ukeep kb b r))) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem len_keep4 (k : Bool) (a : U4) (r : List U4) : (kept k a r).length = r.length + k.toNat := by
  cases k <;> simp [kept]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucheck_sound {M Y t ws} (h : NatRun M Y t ws) (i : Nat) : ucheck M Y t ws i = true := by
  unfold ucheck
  split
  · rfl
  · try dsimp only
    split
    · rename_i hh
      rw [Nat.ble_eq]
      exact probe_run h _ _ _ _ hh.1 hh.2
    · rfl
def urootHint (ws : List Nat) : Nat := (([([31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],511105),([31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],510049),([31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],100915),([31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],170017),([31,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],32935),([31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416],122497),([31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856],117217),([31,992,1015808,1082401,2164802,4329604,8659208,17318416,32505856],502195),([31,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],39073),([992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],163879)] : List (List Nat × Nat)).lookup (isort ws)).getD 0


def ugood (m y t : Nat) (ws : List Nat) (hs : List (Nat × Nat)) : Bool :=
  if ws.length = t then hs.all (fun x => x.1 != 1024 || ucheck m y t ws x.2) else true
theorem ugood_sound {m y t ws} (h : NatRun m y t ws) (hs : List (Nat × Nat)) :
    ugood m y t ws hs = true := by
  unfold ugood
  split
  · apply List.all_eq_true.mpr
    intro x _
    simp [ucheck_sound h]
  · rfl
def qvia (y : Nat) (pd pm : List (Nat × Nat)) (t : Nat) (ws : List Nat) : Bool :=
  Nat.ble ws.length (t+1) && (t != 0 || leqL ws [y]) &&
    (if ws.length = t+1 then monoOK pm ws else distOK pd ws)
theorem qvia_sound {m y pd pm t ws} (hp : prsOK m y pd pm = true) (h : NatRun m y t ws) :
    qvia y pd pm t ws = true := by
  have hv := via_sound hp h
  simp only [via, Bool.and_eq_true] at hv
  unfold qvia
  rw [hv.1.1.1, hv.1.1.2]
  simp only [Bool.true_and]
  split
  · rename_i hw
    simpa [hw] using hv.2
  · exact hv.1.2
def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => qvia y pD pM t ys && ugood m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
        (fun tag ys => qvia y pD pM t ys && ugood m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [qvia_sound hp hys, ugood_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !qvia y pD pM cap zs || !ucheck m y cap zs (urootHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
    have hd := qvia_sound hp hcap
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ofFn_code : ∀ k : Fin 25, List.ofFn (pt 10 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 5) (by have := k.isLt; omega) : Fin 5)
      (Fin.mk (k.val % 5) (by have := k.isLt; omega) : Fin 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ohPts_length : ohPts.length = 25 := by simp [ohPts]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 25) : C.eval (List.ofFn (pt 10 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (5 * (k / 5) + k % 5) = M.testBit k
  rw [Nat.div_add_mod]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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




def Y_ : Nat := 7594810
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,4854439),(2,7281652),(3,4038493),(4,1367305),(5,31779),(6,142518),(7,197884),(8,102617),(9,56011),(10,32706),(11,11590),(12,1028),(13,165),(14,757),(15,989),(16,329),(17,3),(18,38),(19,52),(20,29),(21,9),(22,3),(23,2)]
def PM_ : List (Nat × Nat) := [(0,7594810),(2,7594810),(6,7594810),(7,7594810),(10,7594810),(11,7594810),(12,7594810),(18,7594810),(19,7594810),(23,7594810),(24,7594810)]
def G_ : List (List Nat) := [[0,1,2,4,3,5,6,7,9,8,10,11,12,14,13,15,16,17,19,18,20,21,22,24,23],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,20,21,22,23,24,15,16,17,18,19],[0,1,2,4,3,5,6,7,9,8,10,11,12,14,13,20,21,22,24,23,15,16,17,19,18],[6,5,7,8,9,1,0,2,3,4,11,10,12,13,14,16,15,17,18,19,21,20,22,23,24],[6,5,7,9,8,1,0,2,4,3,11,10,12,14,13,16,15,17,19,18,21,20,22,24,23],[6,5,7,8,9,1,0,2,3,4,11,10,12,13,14,21,20,22,23,24,16,15,17,18,19],[6,5,7,9,8,1,0,2,4,3,11,10,12,14,13,21,20,22,24,23,16,15,17,19,18]]
def z0 : List Nat := [3,1082431,2165730,4357252,33547032]
def z1 : List Nat := [3,25977624,33521698]
def z2 : List Nat := [3,25977626,33521696]
def z3 : List Nat := [3,25977658,33521664]
def z4 : List Nat := [4,2,25977624,33521696]
def z5 : List Nat := [4,2,25977656,33521664]
def z6 : List Nat := [4,31,1082401,2165730,4357252,33547032]
def z7 : List Nat := [4,31,1082401,2194498,4330468,33547032]
def z8 : List Nat := [4,34,25977624,33521664]
def z9 : List Nat := [4,31744,1082431,2165730,4329604,33547032]
def z10 : List Nat := [4,31744,1083365,6494431]
def z11 : List Nat := [4,31744,3248127,4329669]
def z12 : List Nat := [4,31748,1083361,6494431]
def z13 : List Nat := [4,31773,1083361,6494406]
def z14 : List Nat := [4,31775,1083361,6494404]
def z15 : List Nat := [4,31775,1083363,6494406]
def z16 : List Nat := [4,31809,3248127,4329604]
def z17 : List Nat := [4,1015808,1082431,2165730,4357252,33317656]
def z18 : List Nat := [4,1015808,25977624,32505890]
def z19 : List Nat := [4,1015808,25977626,32505888]
def z20 : List Nat := [4,1015808,25977658,32505856]
def z21 : List Nat := [4,1015810,25977624,32505888]
def z22 : List Nat := [4,1082431,2165730,4357252,8659208,33538576]
def z23 : List Nat := [4,1082431,2165730,4357252,9412872,33047056]
def z24 : List Nat := [4,1082431,2165730,4357252,25977624,33521664]
def z25 : List Nat := [4,1083361,2168927,4357252]
def z26 : List Nat := [4,1083361,2194527,4331652]
def z27 : List Nat := [4,1085409,2194527,4329604]
def z28 : List Nat := [4,8659208,17318416,33521698]
def z29 : List Nat := [4,8659208,17318418,33521696]
def z30 : List Nat := [4,8659208,17318450,33521664]
def z31 : List Nat := [4,8659210,17318448,33521664]
def z32 : List Nat := [5,2,32,25977624,33521664]
def z33 : List Nat := [5,2,31775,1083361,6494406]
def z34 : List Nat := [5,2,1015808,25977624,32505888]
def z35 : List Nat := [5,2,1015808,25977656,32505856]
def z36 : List Nat := [5,2,8659208,17318416,33521696]
def z37 : List Nat := [5,2,8659208,17318448,33521664]
def z38 : List Nat := [5,4,31744,1083361,6494431]
def z39 : List Nat := [5,29,31744,1083361,6494406]
def z40 : List Nat := [5,31,992,1082401,2164802,4357252,33547032]
def z41 : List Nat := [5,31,992,1082401,2194498,4329604,33547032]
def z42 : List Nat := [5,31,31744,1082401,2164802,4330468,33547032]
def z43 : List Nat := [5,31,31744,1082401,2165730,4329604,33547032]
def z44 : List Nat := [5,31,31744,1083361,6494404]
def z45 : List Nat := [5,31,31744,1083363,6494406]
def z46 : List Nat := [5,31,31744,1083365,6494406]
def z47 : List Nat := [5,31,31744,2164930,5412837]
def z48 : List Nat := [5,31,31746,1083361,6494406]
def z49 : List Nat := [5,31,31748,1083361,6494406]
def z50 : List Nat := [5,31,31872,2164802,5412837]
def z51 : List Nat := [5,31,32704,2164802,5412005]
def z52 : List Nat := [5,31,32704,2164802,25977624]
def z53 : List Nat := [5,31,32736,2164802,5411973]
def z54 : List Nat := [5,31,32736,2164802,25977656]
def z55 : List Nat := [5,31,32736,2164834,5412005]
def z56 : List Nat := [5,31,1015808,1082401,2165730,4357252,33317656]
def z57 : List Nat := [5,31,1015808,1082401,2194498,4330468,33317656]
def z58 : List Nat := [5,31,1082401,2165730,4357252,8659208,33538576]
def z59 : List Nat := [5,31,1082401,2165730,4357252,9412872,33047056]
def z60 : List Nat := [5,31,1082401,2165730,4357252,25977624,33521664]
def z61 : List Nat := [5,31,1082401,2194498,4330468,8659208,33538576]
def z62 : List Nat := [5,31,1082401,2194498,4330468,9412872,33047056]
def z63 : List Nat := [5,31,1082401,2194498,4330468,25977624,33521664]
def z64 : List Nat := [5,31,1083361,2168898,4357252]
def z65 : List Nat := [5,31,1083361,2194498,4331652]
def z66 : List Nat := [5,31,1085409,2194498,4329604]
def z67 : List Nat := [5,31,1087457,2164802,4357252]
def z68 : List Nat := [5,31,1114081,2164802,4330628]
def z69 : List Nat := [5,31,1114081,2165826,4329604]
def z70 : List Nat := [5,31,2164802,5411973,33521664]
def z71 : List Nat := [5,31,2164802,5412005,33521696]
def z72 : List Nat := [5,31,2164802,25977624,33521696]
def z73 : List Nat := [5,31,2164802,25977656,33521664]
def z74 : List Nat := [5,31,2164834,5412005,33521664]
def z75 : List Nat := [5,34,1015808,25977624,32505856]
def z76 : List Nat := [5,34,8659208,17318416,33521664]
def z77 : List Nat := [5,63,32736,2164802,5412005]
def z78 : List Nat := [5,63,32736,2164802,25977624]
def z79 : List Nat := [5,65,31744,3248127,4329604]
def z80 : List Nat := [5,159,31744,2164802,5412837]
def z81 : List Nat := [5,1023,31775,3247203,5412005]
def z82 : List Nat := [5,1023,31775,3247203,6494406]
def z83 : List Nat := [5,1023,31775,5412005,6494406]
def z84 : List Nat := [5,1024,1114081,2164831,4329604]
def z85 : List Nat := [5,1055,1114081,2164802,4329604]
def z86 : List Nat := [5,4096,1083361,2164831,4357252]
def z87 : List Nat := [5,4127,1083361,2164802,4357252]
def z88 : List Nat := [5,31744,1015808,1082431,2165730,4329604,33317656]
def z89 : List Nat := [5,31744,1082401,2164959,4330468]
def z90 : List Nat := [5,31744,1082431,2165730,4329604,8659208,33538576]
def z91 : List Nat := [5,31744,1082431,2165730,4329604,9412872,33047056]
def z92 : List Nat := [5,31744,1082431,2165730,4329604,25977624,33521664]
def z93 : List Nat := [5,31744,1083361,2164831,4329604]
def z94 : List Nat := [5,31744,1083361,2164831,4329605]
def z95 : List Nat := [5,31744,1083361,2164831,4329669]
def z96 : List Nat := [5,31744,1083361,2164831,4330628]
def z97 : List Nat := [5,31744,1083361,2164831,29224827]
def z98 : List Nat := [5,31744,1083361,2164959,4329604]
def z99 : List Nat := [5,31744,1083361,2165855,4329604]
def z100 : List Nat := [5,31744,1083361,2168927,4329604]
def z101 : List Nat := [5,31744,1083361,4329604,31389600]
def z102 : List Nat := [5,31744,1083361,6494404,33554400]
def z103 : List Nat := [5,31744,1083361,6494406,33554402]
def z104 : List Nat := [5,31744,1083361,29224827,31389600]
def z105 : List Nat := [5,31744,4329604,25977631,33522721]
def z106 : List Nat := [5,31744,4329604,31389600,32471070]
def z107 : List Nat := [5,31745,1083361,2164831,4329604]
def z108 : List Nat := [5,31748,1083361,2164802,4329631]
def z109 : List Nat := [5,31748,1083361,2164831,4329604]
def z110 : List Nat := [5,31773,1083361,2164802,4329604]
def z111 : List Nat := [5,31773,1083361,4329604,31389629]
def z112 : List Nat := [5,31775,32736,3247203,5412005]
def z113 : List Nat := [5,31775,32736,5412005,6494406]
def z114 : List Nat := [5,31775,1083361,2164800,4329604]
def z115 : List Nat := [5,31775,1083361,2164802,4329606]
def z116 : List Nat := [5,31775,1083361,2164802,4331652]
def z117 : List Nat := [5,31775,1083361,4329604,31389631]
def z118 : List Nat := [5,31775,1083361,4357252,6494406]
def z119 : List Nat := [5,31775,1083363,2164802,4329604]
def z120 : List Nat := [5,31775,1085409,2164802,4329604]
def z121 : List Nat := [5,31809,1083361,2164831,4329604]
def z122 : List Nat := [5,1015808,1082431,2165730,4357252,8659208,33047056]
def z123 : List Nat := [5,1015808,1082431,2165730,4357252,25977624,32505856]
def z124 : List Nat := [5,1015808,8659208,17318416,32505890]
def z125 : List Nat := [5,1015808,8659208,17318418,32505888]
def z126 : List Nat := [5,1015808,8659208,17318450,32505856]
def z127 : List Nat := [5,1015808,8659210,17318448,32505856]
def z128 : List Nat := [5,1015810,8659208,17318416,32505888]
def z129 : List Nat := [5,1082431,2165730,4357252,8659208,17318416,33521664]
def z130 : List Nat := [5,1082431,2165730,25977624,33521664]
def z131 : List Nat := [5,1083361,2164831,4329604,33522687]
def z132 : List Nat := [5,1083361,2164831,29224827,33522687]
def z133 : List Nat := [5,1083361,4329604,31389600,33522687]
def z134 : List Nat := [6,0,31744,1083361,2164831,4329604]
def z135 : List Nat := [6,1,31744,1083361,2164831,4329604]
def z136 : List Nat := [6,2,31,31744,1083361,6494406]
def z137 : List Nat := [6,2,32,1015808,25977624,32505856]
def z138 : List Nat := [6,2,32,8659208,17318416,33521664]
def z139 : List Nat := [6,2,992,31775,1082401,6494406]
def z140 : List Nat := [6,2,992,31775,1082401,25977624]
def z141 : List Nat := [6,2,992,1082401,6494406,33521664]
def z142 : List Nat := [6,2,992,1082401,25977624,33521664]
def z143 : List Nat := [6,2,31744,1083361,2164831,4329604]
def z144 : List Nat := [6,2,31775,1083361,2164802,4329604]
def z145 : List Nat := [6,2,1015808,8659208,17318416,32505888]
def z146 : List Nat := [6,2,1015808,8659208,17318448,32505856]
def z147 : List Nat := [6,4,31,31744,1083361,6494406]
def z148 : List Nat := [6,4,992,31744,1082401,6494431]
def z149 : List Nat := [6,4,31744,1083361,2164802,4329631]
def z150 : List Nat := [6,4,31744,1083361,2164831,4329604]
def z151 : List Nat := [6,8,31744,1083361,2164831,4329604]
def z152 : List Nat := [6,29,992,31744,1082401,6494406]
def z153 : List Nat := [6,29,992,31744,1082401,25977624]
def z154 : List Nat := [6,29,31744,1083361,2164802,4329604]
def z155 : List Nat := [6,29,31744,1083361,4329604,31389629]
def z156 : List Nat := [6,31,992,31744,1082401,2164802,4329604,33547032]
def z157 : List Nat := [6,31,992,31744,1082401,6494404]
def z158 : List Nat := [6,31,992,31744,1082401,25977626]
def z159 : List Nat := [6,31,992,31744,1082403,6494406]
def z160 : List Nat := [6,31,992,31744,1082405,6494406]
def z161 : List Nat := [6,31,992,31744,1082405,25977624]
def z162 : List Nat := [6,31,992,31744,3247203,5412005]
def z163 : List Nat := [6,31,992,31744,3247203,27060025]
def z164 : List Nat := [6,31,992,31744,3247231,5412005]
def z165 : List Nat := [6,31,992,31744,5412005,6494406]
def z166 : List Nat := [6,31,992,31744,5412005,6494431]
def z167 : List Nat := [6,31,992,31744,5412005,27060025]
def z168 : List Nat := [6,31,992,31744,5412005,30307228]
def z169 : List Nat := [6,31,992,31744,27060025,28142426]
def z170 : List Nat := [6,31,992,31744,27060025,30307228]
def z171 : List Nat := [6,31,992,31746,1082401,6494406]
def z172 : List Nat := [6,31,992,31746,1082401,25977624]
def z173 : List Nat := [6,31,992,31748,1082401,6494406]
def z174 : List Nat := [6,31,992,31748,1082401,25977624]
def z175 : List Nat := [6,31,992,31775,3247203,5412005]
def z176 : List Nat := [6,31,992,31775,3247203,6494406]
def z177 : List Nat := [6,31,992,31775,5412005,6494406]
def z178 : List Nat := [6,31,992,1015808,1082401,2164802,4357252,33317656]
def z179 : List Nat := [6,31,992,1015808,1082401,2194498,4329604,33317656]
def z180 : List Nat := [6,31,992,1082401,2164802,4357252,8659208,33538576]
def z181 : List Nat := [6,31,992,1082401,2164802,4357252,9412872,33047056]
def z182 : List Nat := [6,31,992,1082401,2164802,4357252,25977624,33521664]
def z183 : List Nat := [6,31,992,1082401,2168898,4357252]
def z184 : List Nat := [6,31,992,1082401,2194498,4329604,8659208,33538576]
def z185 : List Nat := [6,31,992,1082401,2194498,4329604,9412872,33047056]
def z186 : List Nat := [6,31,992,1082401,2194498,4329604,25977624,33521664]
def z187 : List Nat := [6,31,992,1082401,2194498,4331652]
def z188 : List Nat := [6,31,992,1084449,2194498,4329604]
def z189 : List Nat := [6,31,992,1113121,2194498,25977624]
def z190 : List Nat := [6,31,992,1113121,4357252,25977624]
def z191 : List Nat := [6,31,992,3247203,5412005,33521664]
def z192 : List Nat := [6,31,992,3247203,5412005,33522687]
def z193 : List Nat := [6,31,992,5412005,6494406,33521664]
def z194 : List Nat := [6,31,992,5412005,6494406,33522687]
def z195 : List Nat := [6,31,994,31744,1082401,6494406]
def z196 : List Nat := [6,31,994,31744,1082401,25977624]
def z197 : List Nat := [6,31,996,31744,1082401,6494406]
def z198 : List Nat := [6,31,996,31744,1082401,25977624]
def z199 : List Nat := [6,31,1023,31744,3247203,5412005]
def z200 : List Nat := [6,31,1023,31744,3247203,6494406]
def z201 : List Nat := [6,31,1023,31744,5412005,6494406]
def z202 : List Nat := [6,31,1024,1114081,2164802,4329604]
def z203 : List Nat := [6,31,2048,1083361,2194498,4329604]
def z204 : List Nat := [6,31,3040,1082401,2194498,4329604]
def z205 : List Nat := [6,31,4096,1083361,2164802,4357252]
def z206 : List Nat := [6,31,5088,1082401,2164802,4357252]
def z207 : List Nat := [6,31,31744,32736,3247203,5412005]
def z208 : List Nat := [6,31,31744,32736,3247203,6494406]
def z209 : List Nat := [6,31,31744,32736,5412005,6494406]
def z210 : List Nat := [6,31,31744,1015808,1082401,2164802,4330468,33317656]
def z211 : List Nat := [6,31,31744,1015808,1082401,2165730,4329604,33317656]
def z212 : List Nat := [6,31,31744,1082401,2164802,4330468,8659208,33538576]
def z213 : List Nat := [6,31,31744,1082401,2164802,4330468,9412872,33047056]
def z214 : List Nat := [6,31,31744,1082401,2164802,4330468,25977624,33521664]
def z215 : List Nat := [6,31,31744,1082401,2164930,4330468]
def z216 : List Nat := [6,31,31744,1082401,2165730,4329604,8659208,33538576]
def z217 : List Nat := [6,31,31744,1082401,2165730,4329604,9412872,33047056]
def z218 : List Nat := [6,31,31744,1082401,2165730,4329604,25977624,33521664]
def z219 : List Nat := [6,31,31744,1082401,2165730,4329668]
def z220 : List Nat := [6,31,31744,1083361,2164800,4329604]
def z221 : List Nat := [6,31,31744,1083361,2164802,4329604]
def z222 : List Nat := [6,31,31744,1083361,2164802,4329605]
def z223 : List Nat := [6,31,31744,1083361,2164802,4329606]
def z224 : List Nat := [6,31,31744,1083361,2164802,4329668]
def z225 : List Nat := [6,31,31744,1083361,2164802,4330628]
def z226 : List Nat := [6,31,31744,1083361,2164802,4331652]
def z227 : List Nat := [6,31,31744,1083361,2164802,4395140]
def z228 : List Nat := [6,31,31744,1083361,2164802,6494406]
def z229 : List Nat := [6,31,31744,1083361,2164802,27060025]
def z230 : List Nat := [6,31,31744,1083361,2164802,29224827]
def z231 : List Nat := [6,31,31744,1083361,2164803,4329604]
def z232 : List Nat := [6,31,31744,1083361,2164806,4329604]
def z233 : List Nat := [6,31,31744,1083361,2164810,4329604]
def z234 : List Nat := [6,31,31744,1083361,2164831,4329604]
def z235 : List Nat := [6,31,31744,1083361,2164831,29224827]
def z236 : List Nat := [6,31,31744,1083361,2164930,4329604]
def z237 : List Nat := [6,31,31744,1083361,2165730,6494406]
def z238 : List Nat := [6,31,31744,1083361,2165826,4329604]
def z239 : List Nat := [6,31,31744,1083361,2168898,4329604]
def z240 : List Nat := [6,31,31744,1083361,2194498,6494406]
def z241 : List Nat := [6,31,31744,1083361,2295874,4329604]
def z242 : List Nat := [6,31,31744,1083361,3115074,6494406]
def z243 : List Nat := [6,31,31744,1083361,3247203,5412005]
def z244 : List Nat := [6,31,31744,1083361,3247203,6494406]
def z245 : List Nat := [6,31,31744,1083361,3248099,6494406]
def z246 : List Nat := [6,31,31744,1083361,4329604,6494406]
def z247 : List Nat := [6,31,31744,1083361,4329604,6494431]
def z248 : List Nat := [6,31,31744,1083361,4329604,27060025]
def z249 : List Nat := [6,31,31744,1083361,4329604,31389600]
def z250 : List Nat := [6,31,31744,1083361,4329604,31389629]
def z251 : List Nat := [6,31,31744,1083361,4329604,31389631]
def z252 : List Nat := [6,31,31744,1083361,4330468,6494406]
def z253 : List Nat := [6,31,31744,1083361,4357252,6494406]
def z254 : List Nat := [6,31,31744,1083361,5214340,6494406]
def z255 : List Nat := [6,31,31744,1083361,5412005,6494406]
def z256 : List Nat := [6,31,31744,1083361,5412837,6494406]
def z257 : List Nat := [6,31,31744,1083361,6494406,10824010]
def z258 : List Nat := [6,31,31744,1083361,6494406,12988812]
def z259 : List Nat := [6,31,31744,1083361,6494406,29224827]
def z260 : List Nat := [6,31,31744,1083361,6494406,31389629]
def z261 : List Nat := [6,31,31744,1083361,10824010,12988812]
def z262 : List Nat := [6,31,31744,1083361,29224827,31389629]
def z263 : List Nat := [6,31,31744,1083363,2164802,4329604]
def z264 : List Nat := [6,31,31744,1083365,2164802,4329604]
def z265 : List Nat := [6,31,31744,1085409,2164802,4329604]
def z266 : List Nat := [6,31,31744,1087457,2164802,4329604]
def z267 : List Nat := [6,31,31744,2164802,4329604,32471070]
def z268 : List Nat := [6,31,31744,2164802,5411973,33553439]
def z269 : List Nat := [6,31,31744,2164802,5412005,33522721]
def z270 : List Nat := [6,31,31744,2164802,5412005,33553471]
def z271 : List Nat := [6,31,31744,2164802,6494406,32471070]
def z272 : List Nat := [6,31,31744,2164802,25977624,33522721]
def z273 : List Nat := [6,31,31744,2164802,25977624,33553471]
def z274 : List Nat := [6,31,31744,2164802,29224827,32471070]
def z275 : List Nat := [6,31,31744,2164831,4329604,32471070]
def z276 : List Nat := [6,31,31744,3247203,4329604,33522721]
def z277 : List Nat := [6,31,31744,3247203,5412005,33521664]
def z278 : List Nat := [6,31,31744,3247203,5412005,33553439]
def z279 : List Nat := [6,31,31744,3247203,6494406,33521664]
def z280 : List Nat := [6,31,31744,3247203,6494406,33553439]
def z281 : List Nat := [6,31,31744,4329604,6494406,32471070]
def z282 : List Nat := [6,31,31744,4329604,25977624,33522721]
def z283 : List Nat := [6,31,31744,4329604,31389629,32471070]
def z284 : List Nat := [6,31,31744,5412005,6494406,33521664]
def z285 : List Nat := [6,31,31744,5412005,6494406,33553439]
def z286 : List Nat := [6,31,31745,1083361,2164802,4329604]
def z287 : List Nat := [6,31,31746,1083361,2164802,4329604]
def z288 : List Nat := [6,31,31748,1083361,2164802,4329604]
def z289 : List Nat := [6,31,31752,1083361,2164802,4329604]
def z290 : List Nat := [6,31,31775,1083361,2164802,4329604]
def z291 : List Nat := [6,31,31775,1083361,2164802,6494406]
def z292 : List Nat := [6,31,31775,1083361,2164802,29224827]
def z293 : List Nat := [6,31,31775,1083361,2164831,4329604]
def z294 : List Nat := [6,31,31775,1083361,4329604,6494406]
def z295 : List Nat := [6,31,31775,1083361,4329604,31389629]
def z296 : List Nat := [6,31,31775,2164802,4329604,32471070]
def z297 : List Nat := [6,31,31808,1082401,2165730,4329604]
def z298 : List Nat := [6,31,31808,1083361,2164802,4329604]
def z299 : List Nat := [6,31,31872,1082401,2164802,4330468]
def z300 : List Nat := [6,31,31872,1083361,2164802,4329604]
def z301 : List Nat := [6,31,32704,1082401,2164802,4329604]
def z302 : List Nat := [6,31,32704,2164802,4329604,32472030]
def z303 : List Nat := [6,31,32704,2164802,8659208,17318416]
def z304 : List Nat := [6,31,32736,1082369,2164802,4329604]
def z305 : List Nat := [6,31,32736,1082401,2164802,4329636]
def z306 : List Nat := [6,31,32736,1082401,2164802,4330628]
def z307 : List Nat := [6,31,32736,1082401,2164834,4329604]
def z308 : List Nat := [6,31,32736,1082401,2165730,6494406]
def z309 : List Nat := [6,31,32736,1082401,2165730,25977624]
def z310 : List Nat := [6,31,32736,1082401,2165826,4329604]
def z311 : List Nat := [6,31,32736,1082401,2194498,6494406]
def z312 : List Nat := [6,31,32736,1082401,2194498,25977624]
def z313 : List Nat := [6,31,32736,1082401,4330468,6494406]
def z314 : List Nat := [6,31,32736,1082401,4330468,25977624]
def z315 : List Nat := [6,31,32736,1082401,4357252,6494406]
def z316 : List Nat := [6,31,32736,1082401,4357252,25977624]
def z317 : List Nat := [6,31,32736,2164802,4329604,25977848]
def z318 : List Nat := [6,31,32736,2164802,4329604,32472062]
def z319 : List Nat := [6,31,32736,2164802,4357252,5412005]
def z320 : List Nat := [6,31,32736,2164802,4357252,25977624]
def z321 : List Nat := [6,31,32736,2164802,8659208,17318448]
def z322 : List Nat := [6,31,32736,2194498,3247203,4329604]
def z323 : List Nat := [6,31,32736,2194498,4329604,25977624]
def z324 : List Nat := [6,31,1015808,1082401,2165730,4357252,8659208,33047056]
def z325 : List Nat := [6,31,1015808,1082401,2165730,4357252,25977624,32505856]
def z326 : List Nat := [6,31,1015808,1082401,2194498,4330468,8659208,33047056]
def z327 : List Nat := [6,31,1015808,1082401,2194498,4330468,25977624,32505856]
def z328 : List Nat := [6,31,1015808,2164802,5411973,32505856]
def z329 : List Nat := [6,31,1015808,2164802,5412005,32505888]
def z330 : List Nat := [6,31,1015808,2164802,25977624,32505888]
def z331 : List Nat := [6,31,1015808,2164802,25977656,32505856]
def z332 : List Nat := [6,31,1015808,2164834,5412005,32505856]
def z333 : List Nat := [6,31,1082369,2164802,4329604,33521664]
def z334 : List Nat := [6,31,1082401,2164802,4329604,33521696]
def z335 : List Nat := [6,31,1082401,2164802,4329636,33521664]
def z336 : List Nat := [6,31,1082401,2164802,4330628,33521664]
def z337 : List Nat := [6,31,1082401,2164834,4329604,33521664]
def z338 : List Nat := [6,31,1082401,2165730,4357252,8659208,17318416,33521664]
def z339 : List Nat := [6,31,1082401,2165730,6494406,33521664]
def z340 : List Nat := [6,31,1082401,2165730,25977624,33521664]
def z341 : List Nat := [6,31,1082401,2165826,4329604,33521664]
def z342 : List Nat := [6,31,1082401,2194498,4330468,8659208,17318416,33521664]
def z343 : List Nat := [6,31,1082401,2194498,6494406,33521664]
def z344 : List Nat := [6,31,1082401,2194498,25977624,33521664]
def z345 : List Nat := [6,31,1082401,4330468,6494406,33521664]
def z346 : List Nat := [6,31,1082401,4330468,25977624,33521664]
def z347 : List Nat := [6,31,1082401,4357252,6494406,33521664]
def z348 : List Nat := [6,31,1082401,4357252,25977624,33521664]
def z349 : List Nat := [6,31,1083361,2164802,4329604,33522656]
def z350 : List Nat := [6,31,1083361,2164802,4329604,33522687]
def z351 : List Nat := [6,31,1083361,2164802,6494406,33522687]
def z352 : List Nat := [6,31,1083361,2164802,29224827,33522687]
def z353 : List Nat := [6,31,1083361,2164831,4329604,33522687]
def z354 : List Nat := [6,31,1083361,4329604,6494406,33522687]
def z355 : List Nat := [6,31,1083361,4329604,31389629,33522687]
def z356 : List Nat := [6,31,2164802,4329604,25977848,33521664]
def z357 : List Nat := [6,31,2164802,4329604,32471070,33522687]
def z358 : List Nat := [6,31,2164802,4329604,32472062,33521664]
def z359 : List Nat := [6,31,2164802,4357252,5412005,33521664]
def z360 : List Nat := [6,31,2164802,4357252,25977624,33521664]
def z361 : List Nat := [6,31,2164802,8659208,17318416,33521696]
def z362 : List Nat := [6,31,2164802,8659208,17318448,33521664]
def z363 : List Nat := [6,31,2194498,3247203,4329604,33521664]
def z364 : List Nat := [6,31,2194498,4329604,25977624,33521664]
def z365 : List Nat := [6,34,1015808,8659208,17318416,32505856]
def z366 : List Nat := [6,63,32736,1082401,2164802,4329604]
def z367 : List Nat := [6,63,32736,2164802,8659208,17318416]
def z368 : List Nat := [6,65,31744,1083361,2164831,4329604]
def z369 : List Nat := [6,95,31744,1083361,2164802,4329604]
def z370 : List Nat := [6,159,31744,1082401,2164802,4330468]
def z371 : List Nat := [6,159,31744,1083361,2164802,4329604]
def z372 : List Nat := [6,1023,31744,1082401,4329604,25977631]
def z373 : List Nat := [6,1023,31744,1082401,4330468,6494406]
def z374 : List Nat := [6,1023,31744,1082401,4330468,25977624]
def z375 : List Nat := [6,1023,31744,1083361,2164831,4329604]
def z376 : List Nat := [6,1023,31775,1082401,2164802,4329604]
def z377 : List Nat := [6,1023,31775,1082401,2164802,5412005]
def z378 : List Nat := [6,1023,31775,1082401,2164802,6494406]
def z379 : List Nat := [6,1023,31775,1082401,2164802,25977624]
def z380 : List Nat := [6,1023,31775,1082401,2164802,29224827]
def z381 : List Nat := [6,1023,31775,1082401,2164831,4329604]
def z382 : List Nat := [6,1023,31775,1082401,3247203,4329604]
def z383 : List Nat := [6,1023,31775,1082401,4329604,6494406]
def z384 : List Nat := [6,1023,31775,1082401,4329604,25977624]
def z385 : List Nat := [6,1023,31775,1082401,4329604,31389629]
def z386 : List Nat := [6,1023,31775,1083361,2164802,4329604]
def z387 : List Nat := [6,1023,31775,2164802,3247203,4329604]
def z388 : List Nat := [6,1023,31775,2164802,4329604,5412005]
def z389 : List Nat := [6,1023,31775,2164802,4329604,25977624]
def z390 : List Nat := [6,1023,31775,2164802,4329604,32472030]
def z391 : List Nat := [6,1023,1082401,2164802,4329604,33521695]
def z392 : List Nat := [6,1024,31744,1083361,2164831,4329604]
def z393 : List Nat := [6,1024,32736,1082401,2164831,4329604]
def z394 : List Nat := [6,1055,31744,1083361,2164802,4329604]
def z395 : List Nat := [6,1055,32736,1082401,2164802,4329604]
def z396 : List Nat := [6,1055,1082401,2164802,4329604,33521664]
def z397 : List Nat := [6,2016,31744,1082401,2164831,4329604]
def z398 : List Nat := [6,4096,31744,1083361,2164831,4329604]
def z399 : List Nat := [6,4127,31744,1083361,2164802,4329604]
def z400 : List Nat := [6,8192,31744,1083361,2164831,4329604]
def z401 : List Nat := [6,8223,31744,1083361,2164802,4329604]
def z402 : List Nat := [6,31744,31744,1083361,2164831,4329604]
def z403 : List Nat := [6,31744,31775,1083361,2164802,4329604]
def z404 : List Nat := [6,31744,31775,1083361,2164802,6494406]
def z405 : List Nat := [6,31744,31775,1083361,2164802,29224827]
def z406 : List Nat := [6,31744,31775,1083361,2164831,4329604]
def z407 : List Nat := [6,31744,31775,1083361,4329604,6494406]
def z408 : List Nat := [6,31744,31775,1083361,4329604,31389629]
def z409 : List Nat := [6,31744,31775,2164802,4329604,32471070]
def z410 : List Nat := [6,31744,32768,1083361,2164831,4329604]
def z411 : List Nat := [6,31744,33760,1082401,2164831,4329604]
def z412 : List Nat := [6,31744,131072,1083361,2164831,4329604]
def z413 : List Nat := [6,31744,262144,1083361,2164831,4329604]
def z414 : List Nat := [6,31744,1015808,1082431,2165730,4329604,8659208,33047056]
def z415 : List Nat := [6,31744,1015808,1082431,2165730,4329604,25977624,32505856]
def z416 : List Nat := [6,31744,1015808,1083361,2164831,4329604]
def z417 : List Nat := [6,31744,1015808,1083361,2164831,29224827]
def z418 : List Nat := [6,31744,1015808,1083361,4329604,31389600]
def z419 : List Nat := [6,31744,1015808,4329604,25977631,32539681]
def z420 : List Nat := [6,31744,1015839,1083361,2164831,4329604]
def z421 : List Nat := [6,31744,1047552,1083361,2164831,4329604]
def z422 : List Nat := [6,31744,1048575,1083361,2164831,4329604]
def z423 : List Nat := [6,31744,1082369,2164831,4329604,33553439]
def z424 : List Nat := [6,31744,1082401,1083361,2164831,4329604]
def z425 : List Nat := [6,31744,1082401,1083361,2164831,5412005]
def z426 : List Nat := [6,31744,1082401,1083361,2164831,29224827]
def z427 : List Nat := [6,31744,1082401,1083361,4329604,31389600]
def z428 : List Nat := [6,31744,1082401,1114081,2164831,4329604]
def z429 : List Nat := [6,31744,1082401,2164831,4329604,32471070]
def z430 : List Nat := [6,31744,1082401,2164831,4329604,33521695]
def z431 : List Nat := [6,31744,1082401,2164831,4329604,33553439]
def z432 : List Nat := [6,31744,1082401,2164831,4329604,33553471]
def z433 : List Nat := [6,31744,1082401,2164831,5412005,33553439]
def z434 : List Nat := [6,31744,1082401,2164831,29224827,33553439]
def z435 : List Nat := [6,31744,1082401,4329604,25977631,33521664]
def z436 : List Nat := [6,31744,1082401,4329604,31389600,33553439]
def z437 : List Nat := [6,31744,1082401,4330468,6494406,33521664]
def z438 : List Nat := [6,31744,1082401,4330468,25977624,33521664]
def z439 : List Nat := [6,31744,1082431,1083361,2164831,4329604]
def z440 : List Nat := [6,31744,1082431,2165730,4329604,8659208,17318416,33521664]
def z441 : List Nat := [6,31744,1083361,1083361,2164831,4329604]
def z442 : List Nat := [6,31744,1083361,1083391,2164831,4329604]
def z443 : List Nat := [6,31744,1083361,1113121,2164831,4329604]
def z444 : List Nat := [6,31744,1083361,1114081,2164831,4329604]
def z445 : List Nat := [6,31744,1083361,2065441,2164831,4329604]
def z446 : List Nat := [6,31744,1083361,2066401,2164831,4329604]
def z447 : List Nat := [6,31744,1083361,2164831,3247203,4329604]
def z448 : List Nat := [6,31744,1083361,2164831,3247231,4329604]
def z449 : List Nat := [6,31744,1083361,2164831,3248127,4329604]
def z450 : List Nat := [6,31744,1083361,2164831,4329604]
def z451 : List Nat := [6,31744,1083361,2164831,4329604,4329604]
def z452 : List Nat := [6,31744,1083361,2164831,4329604,4329631]
def z453 : List Nat := [6,31744,1083361,2164831,4329604,4357252]
def z454 : List Nat := [6,31744,1083361,2164831,4329604,5214340]
def z455 : List Nat := [6,31744,1083361,2164831,4329604,5412005]
def z456 : List Nat := [6,31744,1083361,2164831,4329604,5412837]
def z457 : List Nat := [6,31744,1083361,2164831,4329604,8659208]
def z458 : List Nat := [6,31744,1083361,2164831,4329604,8659231]
def z459 : List Nat := [6,31744,1083361,2164831,4329604,8682760]
def z460 : List Nat := [6,31744,1083361,2164831,4329604,9412872]
def z461 : List Nat := [6,31744,1083361,2164831,4329604,9741609]
def z462 : List Nat := [6,31744,1083361,2164831,4329604,9742313]
def z463 : List Nat := [6,31744,1083361,2164831,4329604,12988812]
def z464 : List Nat := [6,31744,1083361,2164831,4329604,16236015]
def z465 : List Nat := [6,31744,1083361,2164831,4329604,25977624]
def z466 : List Nat := [6,31744,1083361,2164831,4329604,29224827]
def z467 : List Nat := [6,31744,1083361,2164831,4329604,31389600]
def z468 : List Nat := [6,31744,1083361,2164831,4329604,31389629]
def z469 : List Nat := [6,31744,1083361,2164831,4329604,33521664]
def z470 : List Nat := [6,31744,1083361,2164831,4329604,33522687]
def z471 : List Nat := [6,31744,1083361,2164831,4329604,33553439]
def z472 : List Nat := [6,31744,1083361,2164831,8659208,12988812]
def z473 : List Nat := [6,31744,1083361,2164831,8659208,29224827]
def z474 : List Nat := [6,31744,1083361,2164831,29224827]
def z475 : List Nat := [6,31744,1083361,4329604,6494406,33554400]
def z476 : List Nat := [6,31744,1083361,4329604,8659208,31389600]
def z477 : List Nat := [6,31744,1083361,4329604,31389600]
def z478 : List Nat := [6,31744,1083361,4329604,31389629,33554400]
def z479 : List Nat := [6,31744,4329604,8659208,17318431,33522721]
def z480 : List Nat := [6,31775,32736,1082401,2164802,4329604]
def z481 : List Nat := [6,31775,32736,1082401,2164802,5412005]
def z482 : List Nat := [6,31775,32736,1082401,2164802,25977624]
def z483 : List Nat := [6,31775,32736,1082401,2164802,29224827]
def z484 : List Nat := [6,31775,32736,1082401,2164831,4329604]
def z485 : List Nat := [6,31775,32736,1082401,3247203,4329604]
def z486 : List Nat := [6,31775,32736,1082401,4329604,6494406]
def z487 : List Nat := [6,31775,32736,1082401,4329604,25977624]
def z488 : List Nat := [6,31775,32736,1082401,4329604,31389629]
def z489 : List Nat := [6,31775,1015839,1083361,2164802,4329604]
def z490 : List Nat := [6,31775,1047552,1083361,2164802,4329604]
def z491 : List Nat := [6,31775,1082401,1083391,2164802,4329604]
def z492 : List Nat := [6,31775,1082401,1114081,2164802,4329604]
def z493 : List Nat := [6,31775,1082401,2164802,4329604,33521695]
def z494 : List Nat := [6,31775,1082401,2164802,4329604,33553408]
def z495 : List Nat := [6,31775,1082431,1083361,2164802,4329604]
def z496 : List Nat := [6,31775,1083361,1083391,2164802,4329604]
def z497 : List Nat := [6,31775,1083361,1113121,2164802,4329604]
def z498 : List Nat := [6,31775,1083361,1114081,2164802,4329604]
def z499 : List Nat := [6,31775,1083361,2164802,4329604,4329631]
def z500 : List Nat := [6,31775,1083361,2164802,4329604,4357252]
def z501 : List Nat := [6,31775,1083361,2164802,4329604,8659231]
def z502 : List Nat := [6,31775,1083361,2164802,4329604,8682760]
def z503 : List Nat := [6,31775,1083361,2164802,4329604,33522687]
def z504 : List Nat := [6,31775,1083361,2164802,4329604,33554400]
def z505 : List Nat := [6,1015808,1047552,1083361,2164831,4329604]
def z506 : List Nat := [6,1015808,1082431,2165730,4357252,8659208,17318416,32505856]
def z507 : List Nat := [6,1015808,1082431,2165730,25977624,32505856]
def z508 : List Nat := [6,1015808,1083361,2164831,4329604,33522687]
def z509 : List Nat := [6,1015839,1047552,1083361,2164802,4329604]
def z510 : List Nat := [6,1082401,1083361,2164831,4329604,33522687]
def z511 : List Nat := [6,1082401,2164802,4329604,33521695,33522656]
def z512 : List Nat := [6,1082401,2164802,4329604,33521695,33553408]
def z513 : List Nat := [6,1082401,2164802,4329631,4330468,33521664]
def z514 : List Nat := [6,1082401,2164802,4329631,4357252,33521664]
def z515 : List Nat := [6,1082401,2164831,4329604,33522687,33553439]
def z516 : List Nat := [6,1082431,2165730,8659208,17318416,33521664]
def z517 : List Nat := [6,1083361,2164831,4329604,8659208,33522687]
def z518 : List Nat := [6,1083361,2164831,4329604,33522687]
def z519 : List Nat := [7,0,31,31744,1083361,2164802,4329604]
def z520 : List Nat := [7,1,31,31744,1083361,2164802,4329604]
def z521 : List Nat := [7,1,992,31744,1082401,2164831,4329604]
def z522 : List Nat := [7,1,992,31744,1082431,2164802,4329604]
def z523 : List Nat := [7,2,31,992,31744,1082401,6494406]
def z524 : List Nat := [7,2,31,992,31744,1082401,25977624]
def z525 : List Nat := [7,2,31,31744,1083361,2164802,4329604]
def z526 : List Nat := [7,2,32,1015808,8659208,17318416,32505856]
def z527 : List Nat := [7,2,992,31744,1082401,2164831,4329604]
def z528 : List Nat := [7,2,992,31775,1082401,2164802,4329604]
def z529 : List Nat := [7,2,992,31775,1082401,8659208,17318416]
def z530 : List Nat := [7,2,992,1015808,1082401,6494406,32505856]
def z531 : List Nat := [7,2,992,1015808,1082401,25977624,32505856]
def z532 : List Nat := [7,2,992,1082401,2164802,4329604,33521664]
def z533 : List Nat := [7,2,992,1082401,8659208,17318416,33521664]
def z534 : List Nat := [7,4,31,992,31744,1082401,6494406]
def z535 : List Nat := [7,4,31,992,31744,1082401,25977624]
def z536 : List Nat := [7,4,31,31744,1083361,2164802,4329604]
def z537 : List Nat := [7,4,992,31744,1082401,2164802,4329631]
def z538 : List Nat := [7,4,992,31744,1082401,2164831,4329604]
def z539 : List Nat := [7,8,31,31744,1083361,2164802,4329604]
def z540 : List Nat := [7,8,992,31744,1082401,2164831,4329604]
def z541 : List Nat := [7,29,992,31744,1082401,2164802,4329604]
def z542 : List Nat := [7,29,992,31744,1082401,4329604,31389629]
def z543 : List Nat := [7,29,992,31744,1082401,8659208,17318416]
def z544 : List Nat := [7,31,31,31744,1083361,2164802,4329604]
def z545 : List Nat := [7,31,992,1024,1113121,2164802,4329604]
def z546 : List Nat := [7,31,992,4096,1082401,2164802,4357252]
def z547 : List Nat := [7,31,992,31744,1015808,1082401,2164802,4329604,33317656]
def z548 : List Nat := [7,31,992,31744,1015808,3247203,5412005]
def z549 : List Nat := [7,31,992,31744,1015808,5412005,6494406]
def z550 : List Nat := [7,31,992,31744,1082369,2164802,4329604]
def z551 : List Nat := [7,31,992,31744,1082401,2164802,4329604]
def z552 : List Nat := [7,31,992,31744,1082401,2164802,4329604,8659208,33538576]
def z553 : List Nat := [7,31,992,31744,1082401,2164802,4329604,9412872,33047056]
def z554 : List Nat := [7,31,992,31744,1082401,2164802,4329604,25977624,33521664]
def z555 : List Nat := [7,31,992,31744,1082401,2164802,4329605]
def z556 : List Nat := [7,31,992,31744,1082401,2164802,4329606]
def z557 : List Nat := [7,31,992,31744,1082401,2164802,4330628]
def z558 : List Nat := [7,31,992,31744,1082401,2164802,4362372]
def z559 : List Nat := [7,31,992,31744,1082401,2164802,5412005]
def z560 : List Nat := [7,31,992,31744,1082401,2164802,7576807]
def z561 : List Nat := [7,31,992,31744,1082401,2164802,25977624]
def z562 : List Nat := [7,31,992,31744,1082401,2164802,27060025]
def z563 : List Nat := [7,31,992,31744,1082401,2164802,29224827]
def z564 : List Nat := [7,31,992,31744,1082401,2164803,4329604]
def z565 : List Nat := [7,31,992,31744,1082401,2164806,4329604]
def z566 : List Nat := [7,31,992,31744,1082401,2164810,4329604]
def z567 : List Nat := [7,31,992,31744,1082401,2164831,4329604]
def z568 : List Nat := [7,31,992,31744,1082401,2164831,5412005]
def z569 : List Nat := [7,31,992,31744,1082401,2164831,29224827]
def z570 : List Nat := [7,31,992,31744,1082401,2164834,4329604]
def z571 : List Nat := [7,31,992,31744,1082401,2164930,4329604]
def z572 : List Nat := [7,31,992,31744,1082401,2165730,6494406]
def z573 : List Nat := [7,31,992,31744,1082401,2165730,25977624]
def z574 : List Nat := [7,31,992,31744,1082401,2165826,4329604]
def z575 : List Nat := [7,31,992,31744,1082401,2168898,4329604]
def z576 : List Nat := [7,31,992,31744,1082401,2194498,6494406]
def z577 : List Nat := [7,31,992,31744,1082401,2194498,25977624]
def z578 : List Nat := [7,31,992,31744,1082401,2197570,4329604]
def z579 : List Nat := [7,31,992,31744,1082401,2295874,4329604]
def z580 : List Nat := [7,31,992,31744,1082401,3115074,6494406]
def z581 : List Nat := [7,31,992,31744,1082401,3115074,25977624]
def z582 : List Nat := [7,31,992,31744,1082401,3247203,4329604]
def z583 : List Nat := [7,31,992,31744,1082401,3247203,5412005]
def z584 : List Nat := [7,31,992,31744,1082401,3247203,6494406]
def z585 : List Nat := [7,31,992,31744,1082401,3247203,7576807]
def z586 : List Nat := [7,31,992,31744,1082401,3247203,25977624]
def z587 : List Nat := [7,31,992,31744,1082401,3247203,29224827]
def z588 : List Nat := [7,31,992,31744,1082401,3247231,4329604]
def z589 : List Nat := [7,31,992,31744,1082401,4329604,6494406]
def z590 : List Nat := [7,31,992,31744,1082401,4329604,6494431]
def z591 : List Nat := [7,31,992,31744,1082401,4329604,7576807]
def z592 : List Nat := [7,31,992,31744,1082401,4329604,25977624]
def z593 : List Nat := [7,31,992,31744,1082401,4329604,25977631]
def z594 : List Nat := [7,31,992,31744,1082401,4329604,27060025]
def z595 : List Nat := [7,31,992,31744,1082401,4329604,30307228]
def z596 : List Nat := [7,31,992,31744,1082401,4329604,31389600]
def z597 : List Nat := [7,31,992,31744,1082401,4329604,31389629]
def z598 : List Nat := [7,31,992,31744,1082401,4329604,31389631]
def z599 : List Nat := [7,31,992,31744,1082401,4330468,6494406]
def z600 : List Nat := [7,31,992,31744,1082401,4330468,25977624]
def z601 : List Nat := [7,31,992,31744,1082401,4357252,6494406]
def z602 : List Nat := [7,31,992,31744,1082401,4357252,25977624]
def z603 : List Nat := [7,31,992,31744,1082401,5214340,6494406]
def z604 : List Nat := [7,31,992,31744,1082401,5214340,25977624]
def z605 : List Nat := [7,31,992,31744,1082401,5412005,6494406]
def z606 : List Nat := [7,31,992,31744,1082401,5412005,7576807]
def z607 : List Nat := [7,31,992,31744,1082401,5412005,25977624]
def z608 : List Nat := [7,31,992,31744,1082401,5412005,31389629]
def z609 : List Nat := [7,31,992,31744,1082401,6494406,10824010]
def z610 : List Nat := [7,31,992,31744,1082401,6494406,12988812]
def z611 : List Nat := [7,31,992,31744,1082401,6494406,29224827]
def z612 : List Nat := [7,31,992,31744,1082401,6494406,31389629]
def z613 : List Nat := [7,31,992,31744,1082401,8659208,17318418]
def z614 : List Nat := [7,31,992,31744,1082401,10824010,12988812]
def z615 : List Nat := [7,31,992,31744,1082401,10824010,19483218]
def z616 : List Nat := [7,31,992,31744,1082401,10824010,25977624]
def z617 : List Nat := [7,31,992,31744,1082401,12988812,21648020]
def z618 : List Nat := [7,31,992,31744,1082401,12988812,25977624]
def z619 : List Nat := [7,31,992,31744,1082401,25977624,28142426]
def z620 : List Nat := [7,31,992,31744,1082401,25977624,29224827]
def z621 : List Nat := [7,31,992,31744,1082401,25977624,30307228]
def z622 : List Nat := [7,31,992,31744,1082401,25977624,31389629]
def z623 : List Nat := [7,31,992,31744,1082401,29224827,31389629]
def z624 : List Nat := [7,31,992,31744,1082405,8659208,17318416]
def z625 : List Nat := [7,31,992,31744,1083361,2164831,4329604]
def z626 : List Nat := [7,31,992,31744,1083361,4329604,6494406]
def z627 : List Nat := [7,31,992,31744,1083361,4329604,31389629]
def z628 : List Nat := [7,31,992,31744,1113121,3247203,4329604]
def z629 : List Nat := [7,31,992,31744,1113121,4329604,25977624]
def z630 : List Nat := [7,31,992,31744,2065441,3247203,4329604]
def z631 : List Nat := [7,31,992,31744,2065441,4329604,25977624]
def z632 : List Nat := [7,31,992,31744,3247203,4329604,5412005]
def z633 : List Nat := [7,31,992,31744,3247203,4329604,9741609]
def z634 : List Nat := [7,31,992,31744,3247203,4329604,31389629]
def z635 : List Nat := [7,31,992,31744,3247203,5412005]
def z636 : List Nat := [7,31,992,31744,3247203,5412005,8659208]
def z637 : List Nat := [7,31,992,31744,3247203,8659208,18400817]
def z638 : List Nat := [7,31,992,31744,4329604,5412005,6494406]
def z639 : List Nat := [7,31,992,31744,4329604,5412005,7576807]
def z640 : List Nat := [7,31,992,31744,4329604,5412005,25977624]
def z641 : List Nat := [7,31,992,31744,4329604,5412005,31389629]
def z642 : List Nat := [7,31,992,31744,4329604,9741609,10824010]
def z643 : List Nat := [7,31,992,31744,4329604,9741609,18400817]
def z644 : List Nat := [7,31,992,31744,4329604,9741609,25977624]
def z645 : List Nat := [7,31,992,31744,4329604,25977624,27060025]
def z646 : List Nat := [7,31,992,31744,4329604,25977624,31389629]
def z647 : List Nat := [7,31,992,31744,4329604,31389629,32472030]
def z648 : List Nat := [7,31,992,31744,5412005,6494406]
def z649 : List Nat := [7,31,992,31744,5412005,6494406,8659208]
def z650 : List Nat := [7,31,992,31744,5412005,8659208,18400817]
def z651 : List Nat := [7,31,992,31744,5412005,8659208,21648020]
def z652 : List Nat := [7,31,992,31744,8659208,18400817,19483218]
def z653 : List Nat := [7,31,992,31744,8659208,18400817,21648020]
def z654 : List Nat := [7,31,992,31745,1082401,2164802,4329604]
def z655 : List Nat := [7,31,992,31746,1082401,2164802,4329604]
def z656 : List Nat := [7,31,992,31746,1082401,8659208,17318416]
def z657 : List Nat := [7,31,992,31748,1082401,2164802,4329604]
def z658 : List Nat := [7,31,992,31748,1082401,8659208,17318416]
def z659 : List Nat := [7,31,992,31752,1082401,2164802,4329604]
def z660 : List Nat := [7,31,992,31775,1082401,2164802,4329604]
def z661 : List Nat := [7,31,992,31775,1082401,2164802,5412005]
def z662 : List Nat := [7,31,992,31775,1082401,2164802,6494406]
def z663 : List Nat := [7,31,992,31775,1082401,2164802,25977624]
def z664 : List Nat := [7,31,992,31775,1082401,2164802,29224827]
def z665 : List Nat := [7,31,992,31775,1082401,2164831,4329604]
def z666 : List Nat := [7,31,992,31775,1082401,3247203,4329604]
def z667 : List Nat := [7,31,992,31775,1082401,4329604,6494406]
def z668 : List Nat := [7,31,992,31775,1082401,4329604,25977624]
def z669 : List Nat := [7,31,992,31775,1082401,4329604,31389629]
def z670 : List Nat := [7,31,992,31775,1083361,2164802,4329604]
def z671 : List Nat := [7,31,992,31775,2164802,3247203,4329604]
def z672 : List Nat := [7,31,992,31775,2164802,4329604,5412005]
def z673 : List Nat := [7,31,992,31775,2164802,4329604,25977624]
def z674 : List Nat := [7,31,992,31775,2164802,4329604,32472030]
def z675 : List Nat := [7,31,992,32767,1082401,2164802,4329604]
def z676 : List Nat := [7,31,992,1015808,1082401,2164802,4357252,8659208,33047056]
def z677 : List Nat := [7,31,992,1015808,1082401,2164802,4357252,25977624,32505856]
def z678 : List Nat := [7,31,992,1015808,1082401,2194498,4329604,8659208,33047056]
def z679 : List Nat := [7,31,992,1015808,1082401,2194498,4329604,25977624,32505856]
def z680 : List Nat := [7,31,992,1015808,3247203,5412005,32505856]
def z681 : List Nat := [7,31,992,1015808,5412005,6494406,32505856]
def z682 : List Nat := [7,31,992,1082401,2164802,4329604,33521664]
def z683 : List Nat := [7,31,992,1082401,2164802,4329604,33521695]
def z684 : List Nat := [7,31,992,1082401,2164802,4329604,33522687]
def z685 : List Nat := [7,31,992,1082401,2164802,4357252,8659208,17318416,33521664]
def z686 : List Nat := [7,31,992,1082401,2164802,5412005,33521664]
def z687 : List Nat := [7,31,992,1082401,2164802,5412005,33522687]
def z688 : List Nat := [7,31,992,1082401,2164802,25977624,33521664]
def z689 : List Nat := [7,31,992,1082401,2164802,25977624,33522687]
def z690 : List Nat := [7,31,992,1082401,2164802,29224827,33521664]
def z691 : List Nat := [7,31,992,1082401,2164802,29224827,33522687]
def z692 : List Nat := [7,31,992,1082401,2164831,4329604,33521664]
def z693 : List Nat := [7,31,992,1082401,2164831,4329604,33522687]
def z694 : List Nat := [7,31,992,1082401,2194498,4329604,8659208,17318416,33521664]
def z695 : List Nat := [7,31,992,1082401,3247203,4329604,33521664]
def z696 : List Nat := [7,31,992,1082401,3247203,4329604,33522687]
def z697 : List Nat := [7,31,992,1082401,4329604,6494406,33521664]
def z698 : List Nat := [7,31,992,1082401,4329604,6494406,33522687]
def z699 : List Nat := [7,31,992,1082401,4329604,25977624,33521664]
def z700 : List Nat := [7,31,992,1082401,4329604,25977624,33522687]
def z701 : List Nat := [7,31,992,1082401,4329604,31389629,33521664]
def z702 : List Nat := [7,31,992,1082401,4329604,31389629,33522687]
def z703 : List Nat := [7,31,992,1113121,2194498,8659208,17318416]
def z704 : List Nat := [7,31,992,1113121,4357252,8659208,17318416]
def z705 : List Nat := [7,31,993,31744,1082401,2164802,4329604]
def z706 : List Nat := [7,31,994,31744,1082401,2164802,4329604]
def z707 : List Nat := [7,31,994,31744,1082401,8659208,17318416]
def z708 : List Nat := [7,31,996,31744,1082401,2164802,4329604]
def z709 : List Nat := [7,31,996,31744,1082401,8659208,17318416]
def z710 : List Nat := [7,31,1000,31744,1082401,2164802,4329604]
def z711 : List Nat := [7,31,1023,31744,1082401,2164802,4329604]
def z712 : List Nat := [7,31,1023,31744,1082401,2164802,5412005]
def z713 : List Nat := [7,31,1023,31744,1082401,2164802,6494406]
def z714 : List Nat := [7,31,1023,31744,1082401,2164802,25977624]
def z715 : List Nat := [7,31,1023,31744,1082401,2164802,29224827]
def z716 : List Nat := [7,31,1023,31744,1082401,2164831,4329604]
def z717 : List Nat := [7,31,1023,31744,1082401,3247203,4329604]
def z718 : List Nat := [7,31,1023,31744,1082401,4329604,6494406]
def z719 : List Nat := [7,31,1023,31744,1082401,4329604,25977624]
def z720 : List Nat := [7,31,1023,31744,1082401,4329604,31389629]
def z721 : List Nat := [7,31,1023,31744,1083361,2164802,4329604]
def z722 : List Nat := [7,31,1023,31744,2164802,3247203,4329604]
def z723 : List Nat := [7,31,1023,31744,2164802,4329604,5412005]
def z724 : List Nat := [7,31,1023,31744,2164802,4329604,25977624]
def z725 : List Nat := [7,31,1023,31744,2164802,4329604,32472030]
def z726 : List Nat := [7,31,1023,31775,1082401,2164802,4329604]
def z727 : List Nat := [7,31,1023,32736,1082401,2164802,4329604]
def z728 : List Nat := [7,31,1023,32767,1082401,2164802,4329604]
def z729 : List Nat := [7,31,1023,1082401,2164802,4329604,33521664]
def z730 : List Nat := [7,31,1023,1082401,2164802,4329604,33522687]
def z731 : List Nat := [7,31,1024,31744,1083361,2164802,4329604]
def z732 : List Nat := [7,31,1024,32736,1082401,2164802,4329604]
def z733 : List Nat := [7,31,1024,1082401,2164802,4329604,33521664]
def z734 : List Nat := [7,31,2016,31744,1082401,2164802,4329604]
def z735 : List Nat := [7,31,2048,31744,1083361,2164802,4329604]
def z736 : List Nat := [7,31,3040,31744,1082401,2164802,4329604]
def z737 : List Nat := [7,31,4096,31744,1083361,2164802,4329604]
def z738 : List Nat := [7,31,5088,31744,1082401,2164802,4329604]
def z739 : List Nat := [7,31,8192,31744,1083361,2164802,4329604]
def z740 : List Nat := [7,31,9184,31744,1082401,2164802,4329604]
def z741 : List Nat := [7,31,31744,31744,1083361,2164802,4329604]
def z742 : List Nat := [7,31,31744,31775,1083361,2164802,4329604]
def z743 : List Nat := [7,31,31744,32736,1082401,2164802,4329604]
def z744 : List Nat := [7,31,31744,32736,1082401,2164802,5412005]
def z745 : List Nat := [7,31,31744,32736,1082401,2164802,6494406]
def z746 : List Nat := [7,31,31744,32736,1082401,2164802,25977624]
def z747 : List Nat := [7,31,31744,32736,1082401,2164802,29224827]
def z748 : List Nat := [7,31,31744,32736,1082401,2164831,4329604]
def z749 : List Nat := [7,31,31744,32736,1082401,3247203,4329604]
def z750 : List Nat := [7,31,31744,32736,1082401,4329604,6494406]
def z751 : List Nat := [7,31,31744,32736,1082401,4329604,25977624]
def z752 : List Nat := [7,31,31744,32736,1082401,4329604,31389629]
def z753 : List Nat := [7,31,31744,32736,1083361,2164802,4329604]
def z754 : List Nat := [7,31,31744,32736,2164802,3247203,4329604]
def z755 : List Nat := [7,31,31744,32736,2164802,4329604,5412005]
def z756 : List Nat := [7,31,31744,32736,2164802,4329604,25977624]
def z757 : List Nat := [7,31,31744,32736,2164802,4329604,32472030]
def z758 : List Nat := [7,31,31744,32767,1082401,2164802,4329604]
def z759 : List Nat := [7,31,31744,32768,1083361,2164802,4329604]
def z760 : List Nat := [7,31,31744,33760,1082401,2164802,4329604]
def z761 : List Nat := [7,31,31744,65536,1083361,2164802,4329604]
def z762 : List Nat := [7,31,31744,131072,1083361,2164802,4329604]
def z763 : List Nat := [7,31,31744,262144,1083361,2164802,4329604]
def z764 : List Nat := [7,31,31744,1015808,1082401,2164802,4330468,8659208,33047056]
def z765 : List Nat := [7,31,31744,1015808,1082401,2164802,4330468,25977624,32505856]
def z766 : List Nat := [7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056]
def z767 : List Nat := [7,31,31744,1015808,1082401,2165730,4329604,25977624,32505856]
def z768 : List Nat := [7,31,31744,1015808,1083361,2164802,4329604]
def z769 : List Nat := [7,31,31744,1015808,1083361,2164802,6494406]
def z770 : List Nat := [7,31,31744,1015808,1083361,2164802,29224827]
def z771 : List Nat := [7,31,31744,1015808,1083361,2164831,4329604]
def z772 : List Nat := [7,31,31744,1015808,1083361,4329604,6494406]
def z773 : List Nat := [7,31,31744,1015808,1083361,4329604,31389629]
def z774 : List Nat := [7,31,31744,1015808,2164802,4329604,32471070]
def z775 : List Nat := [7,31,31744,1015808,2164802,5412005,32539681]
def z776 : List Nat := [7,31,31744,1015808,2164802,25977624,32539681]
def z777 : List Nat := [7,31,31744,1015808,3247203,4329604,32539681]
def z778 : List Nat := [7,31,31744,1015808,3247203,5412005,32505856]
def z779 : List Nat := [7,31,31744,1015808,3247203,6494406,32505856]
def z780 : List Nat := [7,31,31744,1015808,4329604,25977624,32539681]
def z781 : List Nat := [7,31,31744,1015808,5412005,6494406,32505856]
def z782 : List Nat := [7,31,31744,1015839,1083361,2164802,4329604]
def z783 : List Nat := [7,31,31744,1016800,1083361,2164802,4329604]
def z784 : List Nat := [7,31,31744,1047552,1083361,2164802,4329604]
def z785 : List Nat := [7,31,31744,1048575,1083361,2164802,4329604]
def z786 : List Nat := [7,31,31744,1082369,2164802,4329604,33553439]
def z787 : List Nat := [7,31,31744,1082401,1083361,2164802,4329604]
def z788 : List Nat := [7,31,31744,1082401,1083361,2164802,5412005]
def z789 : List Nat := [7,31,31744,1082401,1083361,2164802,6494406]
def z790 : List Nat := [7,31,31744,1082401,1083361,2164802,25977624]
def z791 : List Nat := [7,31,31744,1082401,1083361,2164802,29224827]
def z792 : List Nat := [7,31,31744,1082401,1083361,2164831,4329604]
def z793 : List Nat := [7,31,31744,1082401,1083361,3247203,4329604]
def z794 : List Nat := [7,31,31744,1082401,1083361,4329604,6494406]
def z795 : List Nat := [7,31,31744,1082401,1083361,4329604,25977624]
def z796 : List Nat := [7,31,31744,1082401,1083361,4329604,31389629]
def z797 : List Nat := [7,31,31744,1082401,1083391,2164802,4329604]
def z798 : List Nat := [7,31,31744,1082401,1114081,2164802,4329604]
def z799 : List Nat := [7,31,31744,1082401,2164802,4329604,32471070]
def z800 : List Nat := [7,31,31744,1082401,2164802,4329604,33521664]
def z801 : List Nat := [7,31,31744,1082401,2164802,4329604,33521695]
def z802 : List Nat := [7,31,31744,1082401,2164802,4329604,33522721]
def z803 : List Nat := [7,31,31744,1082401,2164802,4329604,33553408]
def z804 : List Nat := [7,31,31744,1082401,2164802,4329604,33553439]
def z805 : List Nat := [7,31,31744,1082401,2164802,4329604,33553471]
def z806 : List Nat := [7,31,31744,1082401,2164802,4330468,8659208,17318416,33521664]
def z807 : List Nat := [7,31,31744,1082401,2164802,5412005,33521664]
def z808 : List Nat := [7,31,31744,1082401,2164802,5412005,33553439]
def z809 : List Nat := [7,31,31744,1082401,2164802,6494406,33521664]
def z810 : List Nat := [7,31,31744,1082401,2164802,6494406,33553439]
def z811 : List Nat := [7,31,31744,1082401,2164802,25977624,33521664]
def z812 : List Nat := [7,31,31744,1082401,2164802,25977624,33553439]
def z813 : List Nat := [7,31,31744,1082401,2164802,29224827,33521664]
def z814 : List Nat := [7,31,31744,1082401,2164802,29224827,33553439]
def z815 : List Nat := [7,31,31744,1082401,2164831,4329604,33521664]
def z816 : List Nat := [7,31,31744,1082401,2164831,4329604,33553439]
def z817 : List Nat := [7,31,31744,1082401,2165730,4329604,8659208,17318416,33521664]
def z818 : List Nat := [7,31,31744,1082401,3247203,4329604,33521664]
def z819 : List Nat := [7,31,31744,1082401,3247203,4329604,33553439]
def z820 : List Nat := [7,31,31744,1082401,4329604,6494406,33521664]
def z821 : List Nat := [7,31,31744,1082401,4329604,6494406,33553439]
def z822 : List Nat := [7,31,31744,1082401,4329604,25977624,33521664]
def z823 : List Nat := [7,31,31744,1082401,4329604,25977624,33553439]
def z824 : List Nat := [7,31,31744,1082401,4329604,31389629,33521664]
def z825 : List Nat := [7,31,31744,1082401,4329604,31389629,33553439]
def z826 : List Nat := [7,31,31744,1082431,1083361,2164802,4329604]
def z827 : List Nat := [7,31,31744,1083361,1083361,2164802,4329604]
def z828 : List Nat := [7,31,31744,1083361,1083391,2164802,4329604]
def z829 : List Nat := [7,31,31744,1083361,1113121,2164802,4329604]
def z830 : List Nat := [7,31,31744,1083361,1114081,2164802,4329604]
def z831 : List Nat := [7,31,31744,1083361,2065441,2164802,4329604]
def z832 : List Nat := [7,31,31744,1083361,2066401,2164802,4329604]
def z833 : List Nat := [7,31,31744,1083361,2164802,2164802,4329604]
def z834 : List Nat := [7,31,31744,1083361,2164802,2164831,4329604]
def z835 : List Nat := [7,31,31744,1083361,2164802,2165730,4329604]
def z836 : List Nat := [7,31,31744,1083361,2164802,2194498,4329604]
def z837 : List Nat := [7,31,31744,1083361,2164802,3115074,4329604]
def z838 : List Nat := [7,31,31744,1083361,2164802,3247203,4329604]
def z839 : List Nat := [7,31,31744,1083361,2164802,3248099,4329604]
def z840 : List Nat := [7,31,31744,1083361,2164802,4329604]
def z841 : List Nat := [7,31,31744,1083361,2164802,4329604,4329604]
def z842 : List Nat := [7,31,31744,1083361,2164802,4329604,4329631]
def z843 : List Nat := [7,31,31744,1083361,2164802,4329604,4330468]
def z844 : List Nat := [7,31,31744,1083361,2164802,4329604,4357252]
def z845 : List Nat := [7,31,31744,1083361,2164802,4329604,5214340]
def z846 : List Nat := [7,31,31744,1083361,2164802,4329604,5412005]
def z847 : List Nat := [7,31,31744,1083361,2164802,4329604,5412837]
def z848 : List Nat := [7,31,31744,1083361,2164802,4329604,6494406]
def z849 : List Nat := [7,31,31744,1083361,2164802,4329604,8659208]
def z850 : List Nat := [7,31,31744,1083361,2164802,4329604,8659231]
def z851 : List Nat := [7,31,31744,1083361,2164802,4329604,8659944]
def z852 : List Nat := [7,31,31744,1083361,2164802,4329604,8682760]
def z853 : List Nat := [7,31,31744,1083361,2164802,4329604,9412872]
def z854 : List Nat := [7,31,31744,1083361,2164802,4329604,9741609]
def z855 : List Nat := [7,31,31744,1083361,2164802,4329604,9742313]
def z856 : List Nat := [7,31,31744,1083361,2164802,4329604,10824010]
def z857 : List Nat := [7,31,31744,1083361,2164802,4329604,12988812]
def z858 : List Nat := [7,31,31744,1083361,2164802,4329604,16236015]
def z859 : List Nat := [7,31,31744,1083361,2164802,4329604,25977624]
def z860 : List Nat := [7,31,31744,1083361,2164802,4329604,29224827]
def z861 : List Nat := [7,31,31744,1083361,2164802,4329604,31389629]
def z862 : List Nat := [7,31,31744,1083361,2164802,4329604,32471070]
def z863 : List Nat := [7,31,31744,1083361,2164802,4329604,32472030]
def z864 : List Nat := [7,31,31744,1083361,2164802,4329604,33521664]
def z865 : List Nat := [7,31,31744,1083361,2164802,4329604,33522687]
def z866 : List Nat := [7,31,31744,1083361,2164802,4329604,33553439]
def z867 : List Nat := [7,31,31744,1083361,2164802,4329604,33554400]
def z868 : List Nat := [7,31,31744,1083361,2164802,6494406]
def z869 : List Nat := [7,31,31744,1083361,2164802,6494406,8659208]
def z870 : List Nat := [7,31,31744,1083361,2164802,8659208,12988812]
def z871 : List Nat := [7,31,31744,1083361,2164802,8659208,18400817]
def z872 : List Nat := [7,31,31744,1083361,2164802,8659208,29224827]
def z873 : List Nat := [7,31,31744,1083361,2164802,29224827]
def z874 : List Nat := [7,31,31744,1083361,2164831,4329604]
def z875 : List Nat := [7,31,31744,1083361,2164831,4329604,8659208]
def z876 : List Nat := [7,31,31744,1083361,4329604,6494406]
def z877 : List Nat := [7,31,31744,1083361,4329604,6494406,8659208]
def z878 : List Nat := [7,31,31744,1083361,4329604,8659208,10824010]
def z879 : List Nat := [7,31,31744,1083361,4329604,8659208,18400817]
def z880 : List Nat := [7,31,31744,1083361,4329604,8659208,31389629]
def z881 : List Nat := [7,31,31744,1083361,4329604,31389629]
def z882 : List Nat := [7,31,31744,2065441,2164802,4329604,32539681]
def z883 : List Nat := [7,31,31744,2164802,3247203,4329604,33521664]
def z884 : List Nat := [7,31,31744,2164802,3247203,4329604,33553439]
def z885 : List Nat := [7,31,31744,2164802,4329604,5412005,33521664]
def z886 : List Nat := [7,31,31744,2164802,4329604,5412005,33553439]
def z887 : List Nat := [7,31,31744,2164802,4329604,8659208,32471070]
def z888 : List Nat := [7,31,31744,2164802,4329604,8659944,17318896]
def z889 : List Nat := [7,31,31744,2164802,4329604,25977624,33521664]
def z890 : List Nat := [7,31,31744,2164802,4329604,25977624,33553439]
def z891 : List Nat := [7,31,31744,2164802,4329604,32471070]
def z892 : List Nat := [7,31,31744,2164802,4329604,32472030,33521664]
def z893 : List Nat := [7,31,31744,2164802,4329604,32472030,33553439]
def z894 : List Nat := [7,31,31744,2164802,8659208,17318416,33522721]
def z895 : List Nat := [7,31,31744,2164802,8659208,17318416,33553471]
def z896 : List Nat := [7,31,31744,4329604,8659208,17318416,33522721]
def z897 : List Nat := [7,31,31775,32736,1082401,2164802,4329604]
def z898 : List Nat := [7,31,31775,32767,1082401,2164802,4329604]
def z899 : List Nat := [7,31,31775,1015808,1083361,2164802,4329604]
def z900 : List Nat := [7,31,31775,1082401,1083361,2164802,4329604]
def z901 : List Nat := [7,31,31775,1082401,2164802,4329604,33521664]
def z902 : List Nat := [7,31,31775,1082401,2164802,4329604,33553439]
def z903 : List Nat := [7,31,31775,1083361,2164802,4329604]
def z904 : List Nat := [7,31,31775,1083361,2164802,4329604,8659208]
def z905 : List Nat := [7,31,32736,1016800,1082401,2164802,4329604]
def z906 : List Nat := [7,31,32736,1047552,1082401,2164802,4329604]
def z907 : List Nat := [7,31,32736,1082401,2164802,2165730,4329604]
def z908 : List Nat := [7,31,32736,1082401,2164802,2194498,4329604]
def z909 : List Nat := [7,31,32736,1082401,2164802,4329604,4330468]
def z910 : List Nat := [7,31,32736,1082401,2164802,4329604,4357252]
def z911 : List Nat := [7,31,32736,1082401,2164802,4329604,8659944]
def z912 : List Nat := [7,31,32736,1082401,2164802,4329604,8682760]
def z913 : List Nat := [7,31,32736,1082401,2164802,4329604,33522687]
def z914 : List Nat := [7,31,32736,1082401,2164802,4329604,33553439]
def z915 : List Nat := [7,31,32736,1082401,2165730,8659208,17318416]
def z916 : List Nat := [7,31,32736,1082401,2194498,8659208,17318416]
def z917 : List Nat := [7,31,32736,1082401,4330468,8659208,17318416]
def z918 : List Nat := [7,31,32736,1082401,4357252,8659208,17318416]
def z919 : List Nat := [7,31,32736,2164802,4329604,8659208,17318896]
def z920 : List Nat := [7,31,32736,2164802,4357252,8659208,17318416]
def z921 : List Nat := [7,31,32736,2194498,4329604,8659208,17318416]
def z922 : List Nat := [7,31,1015808,1047552,1083361,2164802,4329604]
def z923 : List Nat := [7,31,1015808,1082369,2164802,4329604,32505856]
def z924 : List Nat := [7,31,1015808,1082401,2164802,4329604,32505888]
def z925 : List Nat := [7,31,1015808,1082401,2164802,4329636,32505856]
def z926 : List Nat := [7,31,1015808,1082401,2164802,4330628,32505856]
def z927 : List Nat := [7,31,1015808,1082401,2164834,4329604,32505856]
def z928 : List Nat := [7,31,1015808,1082401,2165730,4357252,8659208,17318416,32505856]
def z929 : List Nat := [7,31,1015808,1082401,2165730,6494406,32505856]
def z930 : List Nat := [7,31,1015808,1082401,2165730,25977624,32505856]
def z931 : List Nat := [7,31,1015808,1082401,2165826,4329604,32505856]
def z932 : List Nat := [7,31,1015808,1082401,2194498,4330468,8659208,17318416,32505856]
def z933 : List Nat := [7,31,1015808,1082401,2194498,6494406,32505856]
def z934 : List Nat := [7,31,1015808,1082401,2194498,25977624,32505856]
def z935 : List Nat := [7,31,1015808,1082401,4330468,6494406,32505856]
def z936 : List Nat := [7,31,1015808,1082401,4330468,25977624,32505856]
def z937 : List Nat := [7,31,1015808,1082401,4357252,6494406,32505856]
def z938 : List Nat := [7,31,1015808,1082401,4357252,25977624,32505856]
def z939 : List Nat := [7,31,1015808,1083361,2164802,4329604,32506848]
def z940 : List Nat := [7,31,1015808,1083361,2164802,4329604,33522687]
def z941 : List Nat := [7,31,1015808,2164802,4329604,25977848,32505856]
def z942 : List Nat := [7,31,1015808,2164802,4329604,32472062,32505856]
def z943 : List Nat := [7,31,1015808,2164802,4357252,5412005,32505856]
def z944 : List Nat := [7,31,1015808,2164802,4357252,25977624,32505856]
def z945 : List Nat := [7,31,1015808,2164802,8659208,17318416,32505888]
def z946 : List Nat := [7,31,1015808,2164802,8659208,17318448,32505856]
def z947 : List Nat := [7,31,1015808,2194498,3247203,4329604,32505856]
def z948 : List Nat := [7,31,1015808,2194498,4329604,25977624,32505856]
def z949 : List Nat := [7,31,1016800,1047552,1082401,2164802,4329604]
def z950 : List Nat := [7,31,1016800,1082401,2164802,4329604,32506848]
def z951 : List Nat := [7,31,1016800,1082401,2164802,4329604,33521664]
def z952 : List Nat := [7,31,1047552,1082401,2164802,4329604,32537600]
def z953 : List Nat := [7,31,1047552,1082401,2164802,4329604,33521664]
def z954 : List Nat := [7,31,1082401,1083361,2164802,4329604,33522687]
def z955 : List Nat := [7,31,1082401,2164802,2165730,4329604,33521664]
def z956 : List Nat := [7,31,1082401,2164802,2194498,4329604,33521664]
def z957 : List Nat := [7,31,1082401,2164802,4329604,4330468,33521664]
def z958 : List Nat := [7,31,1082401,2164802,4329604,4357252,33521664]
def z959 : List Nat := [7,31,1082401,2164802,4329604,8659944,33521664]
def z960 : List Nat := [7,31,1082401,2164802,4329604,8682760,33521664]
def z961 : List Nat := [7,31,1082401,2164802,4329604,33521664,33522656]
def z962 : List Nat := [7,31,1082401,2164802,4329604,33521664,33522687]
def z963 : List Nat := [7,31,1082401,2164802,4329604,33521664,33553408]
def z964 : List Nat := [7,31,1082401,2164802,4329604,33521664,33553439]
def z965 : List Nat := [7,31,1082401,2164802,4329604,33522687,33553439]
def z966 : List Nat := [7,31,1082401,2165730,8659208,17318416,33521664]
def z967 : List Nat := [7,31,1082401,2194498,8659208,17318416,33521664]
def z968 : List Nat := [7,31,1082401,4330468,8659208,17318416,33521664]
def z969 : List Nat := [7,31,1082401,4357252,8659208,17318416,33521664]
def z970 : List Nat := [7,31,1083361,2164802,4329604,8659208,33522687]
def z971 : List Nat := [7,31,1083361,2164802,4329604,33522687]
def z972 : List Nat := [7,31,2164802,4329604,8659208,17318896,33521664]
def z973 : List Nat := [7,31,2164802,4357252,8659208,17318416,33521664]
def z974 : List Nat := [7,31,2194498,4329604,8659208,17318416,33521664]
def z975 : List Nat := [7,1023,31744,31775,1082401,2164802,4329604]
def z976 : List Nat := [7,1023,31744,1015839,1082401,2164802,4329604]
def z977 : List Nat := [7,1023,31744,1082401,2164802,4329604,4329631]
def z978 : List Nat := [7,1023,31744,1082401,2164802,4329604,8659231]
def z979 : List Nat := [7,1023,31744,1082401,2164802,4329604,33553439]
def z980 : List Nat := [7,1023,31744,1082401,4329604,8659208,17318431]
def z981 : List Nat := [7,1023,31744,1082401,4330468,8659208,17318416]
def z982 : List Nat := [7,1023,31775,1015808,1082401,2164802,4329604]
def z983 : List Nat := [7,1023,31775,1082401,2164802,4329604]
def z984 : List Nat := [7,1023,31775,1082401,2164802,4329604,8659208]
def z985 : List Nat := [7,1023,31775,1082401,2164802,8659208,17318416]
def z986 : List Nat := [7,1023,31775,1082401,4329604,8659208,17318416]
def z987 : List Nat := [7,1023,31775,2164802,4329604,8659208,17318416]
def z988 : List Nat := [7,1023,1015808,1082401,2164802,4329604,32505887]
def z989 : List Nat := [7,1055,1015808,1082401,2164802,4329604,32505856]
def z990 : List Nat := [7,31744,31775,32736,1082401,2164802,4329604]
def z991 : List Nat := [7,31744,31775,32767,1082401,2164802,4329604]
def z992 : List Nat := [7,31744,31775,1015808,1083361,2164802,4329604]
def z993 : List Nat := [7,31744,31775,1082401,1083361,2164802,4329604]
def z994 : List Nat := [7,31744,31775,1082401,2164802,4329604,33521664]
def z995 : List Nat := [7,31744,31775,1082401,2164802,4329604,33553439]
def z996 : List Nat := [7,31744,31775,1083361,2164802,4329604]
def z997 : List Nat := [7,31744,31775,1083361,2164802,4329604,8659208]
def z998 : List Nat := [7,31744,1015808,1015839,1083361,2164802,4329604]
def z999 : List Nat := [7,31744,1015808,1082401,1083361,2164831,4329604]
def z1000 : List Nat := [7,31744,1015808,1082401,2164831,4329604,32505887]
def z1001 : List Nat := [7,31744,1015808,1082401,2164831,4329604,33553439]
def z1002 : List Nat := [7,31744,1015808,1082401,4329604,25977631,32505856]
def z1003 : List Nat := [7,31744,1015808,1082401,4330468,6494406,32505856]
def z1004 : List Nat := [7,31744,1015808,1082401,4330468,25977624,32505856]
def z1005 : List Nat := [7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856]
def z1006 : List Nat := [7,31744,1015808,1083361,2164831,4329604]
def z1007 : List Nat := [7,31744,1015808,1083361,2164831,4329604,8659208]
def z1008 : List Nat := [7,31744,1015808,1083361,2164831,4329604,32505856]
def z1009 : List Nat := [7,31744,1015808,4329604,8659208,17318431,32539681]
def z1010 : List Nat := [7,31744,1015839,1016800,1082401,2164802,4329604]
def z1011 : List Nat := [7,31744,1015839,1082401,2164802,4329604,32505887]
def z1012 : List Nat := [7,31744,1015839,1082401,2164802,4329604,33521664]
def z1013 : List Nat := [7,31744,1082401,1083361,2164802,2164831,4329604]
def z1014 : List Nat := [7,31744,1082401,1083361,2164802,4329604,33554400]
def z1015 : List Nat := [7,31744,1082401,1083361,2164831,4329604]
def z1016 : List Nat := [7,31744,1082401,1083361,2164831,4329604,8659208]
def z1017 : List Nat := [7,31744,1082401,2164802,4329604,4329631,33521664]
def z1018 : List Nat := [7,31744,1082401,2164802,4329604,8659231,33521664]
def z1019 : List Nat := [7,31744,1082401,2164802,4329604,33521664,33521695]
def z1020 : List Nat := [7,31744,1082401,2164802,4329604,33521664,33553439]
def z1021 : List Nat := [7,31744,1082401,2164802,4329604,33553439,33554400]
def z1022 : List Nat := [7,31744,1082401,2164831,4329604,8659208,33553439]
def z1023 : List Nat := [7,31744,1082401,2164831,4329604,33553439]
def z1024 : List Nat := [7,31744,1082401,4329604,8659208,17318431,33521664]
def z1025 : List Nat := [7,31744,1082401,4330468,8659208,17318416,33521664]
def z1026 : List Nat := [7,31744,1083361,2164831,4329604]
def z1027 : List Nat := [7,31744,1083361,2164831,4329604,8659208]
def z1028 : List Nat := [7,31744,1083361,2164831,4329604,8659208,17318416]
def z1029 : List Nat := [7,31775,32736,1015808,1082401,2164802,4329604]
def z1030 : List Nat := [7,31775,32736,1082401,2164802,4329604]
def z1031 : List Nat := [7,31775,32736,1082401,2164802,4329604,8659208]
def z1032 : List Nat := [7,31775,32736,1082401,2164802,8659208,17318416]
def z1033 : List Nat := [7,31775,32736,1082401,4329604,8659208,17318416]
def z1034 : List Nat := [7,31775,1015808,1082401,2164802,4329604,32505887]
def z1035 : List Nat := [7,31775,1015808,1082401,2164802,4329604,32537600]
def z1036 : List Nat := [7,1015808,1082401,2164802,4329604,32505887,32506848]
def z1037 : List Nat := [7,1015808,1082401,2164802,4329604,32505887,32537600]
def z1038 : List Nat := [7,1015808,1082401,2164802,4329631,4330468,32505856]
def z1039 : List Nat := [7,1015808,1082401,2164802,4329631,4357252,32505856]
def z1040 : List Nat := [7,1015808,1082431,2165730,8659208,17318416,32505856]
def z1041 : List Nat := [8,0,31,992,31744,1082401,2164802,4329604]
def z1042 : List Nat := [8,1,31,992,31744,1082401,2164802,4329604]
def z1043 : List Nat := [8,2,31,992,31744,1082401,2164802,4329604]
def z1044 : List Nat := [8,2,31,992,31744,1082401,8659208,17318416]
def z1045 : List Nat := [8,2,992,1015808,1082401,2164802,4329604,32505856]
def z1046 : List Nat := [8,2,992,1015808,1082401,8659208,17318416,32505856]
def z1047 : List Nat := [8,4,31,992,31744,1082401,2164802,4329604]
def z1048 : List Nat := [8,4,31,992,31744,1082401,8659208,17318416]
def z1049 : List Nat := [8,8,31,992,31744,1082401,2164802,4329604]
def z1050 : List Nat := [8,31,31,992,31744,1082401,2164802,4329604]
def z1051 : List Nat := [8,31,992,1023,31744,1082401,2164802,4329604]
def z1052 : List Nat := [8,31,992,1024,31744,1082401,2164802,4329604]
def z1053 : List Nat := [8,31,992,4096,31744,1082401,2164802,4329604]
def z1054 : List Nat := [8,31,992,8192,31744,1082401,2164802,4329604]
def z1055 : List Nat := [8,31,992,31744,31744,1082401,2164802,4329604]
def z1056 : List Nat := [8,31,992,31744,31775,1082401,2164802,4329604]
def z1057 : List Nat := [8,31,992,31744,32768,1082401,2164802,4329604]
def z1058 : List Nat := [8,31,992,31744,131072,1082401,2164802,4329604]
def z1059 : List Nat := [8,31,992,31744,262144,1082401,2164802,4329604]
def z1060 : List Nat := [8,31,992,31744,1015808,1082401,2164802,4329604]
def z1061 : List Nat := [8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056]
def z1062 : List Nat := [8,31,992,31744,1015808,1082401,2164802,4329604,25977624,32505856]
def z1063 : List Nat := [8,31,992,31744,1015808,1082401,2164802,5412005]
def z1064 : List Nat := [8,31,992,31744,1015808,1082401,2164802,25977624]
def z1065 : List Nat := [8,31,992,31744,1015808,1082401,2164802,29224827]
def z1066 : List Nat := [8,31,992,31744,1015808,1082401,2164831,4329604]
def z1067 : List Nat := [8,31,992,31744,1015808,1082401,3247203,4329604]
def z1068 : List Nat := [8,31,992,31744,1015808,1082401,4329604,6494406]
def z1069 : List Nat := [8,31,992,31744,1015808,1082401,4329604,25977624]
def z1070 : List Nat := [8,31,992,31744,1015808,1082401,4329604,31389629]
def z1071 : List Nat := [8,31,992,31744,1015839,1082401,2164802,4329604]
def z1072 : List Nat := [8,31,992,31744,1047552,1082401,2164802,4329604]
def z1073 : List Nat := [8,31,992,31744,1048575,1082401,2164802,4329604]
def z1074 : List Nat := [8,31,992,31744,1082401,1082401,2164802,4329604]
def z1075 : List Nat := [8,31,992,31744,1082401,1082431,2164802,4329604]
def z1076 : List Nat := [8,31,992,31744,1082401,1083361,2164802,4329604]
def z1077 : List Nat := [8,31,992,31744,1082401,1113121,2164802,4329604]
def z1078 : List Nat := [8,31,992,31744,1082401,2065441,2164802,4329604]
def z1079 : List Nat := [8,31,992,31744,1082401,2164802,3247203,4329604]
def z1080 : List Nat := [8,31,992,31744,1082401,2164802,4329604]
def z1081 : List Nat := [8,31,992,31744,1082401,2164802,4329604,4329604]
def z1082 : List Nat := [8,31,992,31744,1082401,2164802,4329604,4329631]
def z1083 : List Nat := [8,31,992,31744,1082401,2164802,4329604,4357252]
def z1084 : List Nat := [8,31,992,31744,1082401,2164802,4329604,5214340]
def z1085 : List Nat := [8,31,992,31744,1082401,2164802,4329604,5412005]
def z1086 : List Nat := [8,31,992,31744,1082401,2164802,4329604,8659208]
def z1087 : List Nat := [8,31,992,31744,1082401,2164802,4329604,8659208,17318416,33521664]
def z1088 : List Nat := [8,31,992,31744,1082401,2164802,4329604,8659231]
def z1089 : List Nat := [8,31,992,31744,1082401,2164802,4329604,8682760]
def z1090 : List Nat := [8,31,992,31744,1082401,2164802,4329604,9412872]
def z1091 : List Nat := [8,31,992,31744,1082401,2164802,4329604,9741609]
def z1092 : List Nat := [8,31,992,31744,1082401,2164802,4329604,12988812]
def z1093 : List Nat := [8,31,992,31744,1082401,2164802,4329604,16236015]
def z1094 : List Nat := [8,31,992,31744,1082401,2164802,4329604,25977624]
def z1095 : List Nat := [8,31,992,31744,1082401,2164802,4329604,29224827]
def z1096 : List Nat := [8,31,992,31744,1082401,2164802,4329604,31389629]
def z1097 : List Nat := [8,31,992,31744,1082401,2164802,4329604,33521664]
def z1098 : List Nat := [8,31,992,31744,1082401,2164802,4329604,33522687]
def z1099 : List Nat := [8,31,992,31744,1082401,2164802,4329604,33553439]
def z1100 : List Nat := [8,31,992,31744,1082401,2164802,5412005]
def z1101 : List Nat := [8,31,992,31744,1082401,2164802,5412005,8659208]
def z1102 : List Nat := [8,31,992,31744,1082401,2164802,8659208,12988812]
def z1103 : List Nat := [8,31,992,31744,1082401,2164802,8659208,16236015]
def z1104 : List Nat := [8,31,992,31744,1082401,2164802,8659208,17318416]
def z1105 : List Nat := [8,31,992,31744,1082401,2164802,8659208,18400817]
def z1106 : List Nat := [8,31,992,31744,1082401,2164802,8659208,25977624]
def z1107 : List Nat := [8,31,992,31744,1082401,2164802,8659208,29224827]
def z1108 : List Nat := [8,31,992,31744,1082401,2164802,25977624]
def z1109 : List Nat := [8,31,992,31744,1082401,2164802,29224827]
def z1110 : List Nat := [8,31,992,31744,1082401,2164831,4329604]
def z1111 : List Nat := [8,31,992,31744,1082401,2164831,4329604,8659208]
def z1112 : List Nat := [8,31,992,31744,1082401,2165730,8659208,17318416]
def z1113 : List Nat := [8,31,992,31744,1082401,2194498,8659208,17318416]
def z1114 : List Nat := [8,31,992,31744,1082401,3115074,8659208,17318416]
def z1115 : List Nat := [8,31,992,31744,1082401,3247203,4329604]
def z1116 : List Nat := [8,31,992,31744,1082401,3247203,4329604,8659208]
def z1117 : List Nat := [8,31,992,31744,1082401,3247203,8659208,17318416]
def z1118 : List Nat := [8,31,992,31744,1082401,4329604,6494406]
def z1119 : List Nat := [8,31,992,31744,1082401,4329604,6494406,8659208]
def z1120 : List Nat := [8,31,992,31744,1082401,4329604,8659208,10824010]
def z1121 : List Nat := [8,31,992,31744,1082401,4329604,8659208,16236015]
def z1122 : List Nat := [8,31,992,31744,1082401,4329604,8659208,17318416]
def z1123 : List Nat := [8,31,992,31744,1082401,4329604,8659208,17318431]
def z1124 : List Nat := [8,31,992,31744,1082401,4329604,8659208,18400817]
def z1125 : List Nat := [8,31,992,31744,1082401,4329604,8659208,21648020]
def z1126 : List Nat := [8,31,992,31744,1082401,4329604,8659208,25977624]
def z1127 : List Nat := [8,31,992,31744,1082401,4329604,8659208,31389629]
def z1128 : List Nat := [8,31,992,31744,1082401,4329604,25977624]
def z1129 : List Nat := [8,31,992,31744,1082401,4329604,31389629]
def z1130 : List Nat := [8,31,992,31744,1082401,4330468,8659208,17318416]
def z1131 : List Nat := [8,31,992,31744,1082401,4357252,8659208,17318416]
def z1132 : List Nat := [8,31,992,31744,1082401,5214340,8659208,17318416]
def z1133 : List Nat := [8,31,992,31744,1082401,5412005,8659208,17318416]
def z1134 : List Nat := [8,31,992,31744,1082401,8659208,10824010,17318416]
def z1135 : List Nat := [8,31,992,31744,1082401,8659208,12988812,17318416]
def z1136 : List Nat := [8,31,992,31744,1082401,8659208,17318416,29224827]
def z1137 : List Nat := [8,31,992,31744,1082401,8659208,17318416,31389629]
def z1138 : List Nat := [8,31,992,31744,1113121,4329604,8659208,17318416]
def z1139 : List Nat := [8,31,992,31744,2065441,4329604,8659208,17318416]
def z1140 : List Nat := [8,31,992,31744,4329604,5412005,8659208,17318416]
def z1141 : List Nat := [8,31,992,31744,4329604,8659208,9741609,17318416]
def z1142 : List Nat := [8,31,992,31744,4329604,8659208,17318416,31389629]
def z1143 : List Nat := [8,31,992,31775,1015808,1082401,2164802,4329604]
def z1144 : List Nat := [8,31,992,31775,1082401,2164802,4329604]
def z1145 : List Nat := [8,31,992,31775,1082401,2164802,4329604,8659208]
def z1146 : List Nat := [8,31,992,31775,1082401,2164802,8659208,17318416]
def z1147 : List Nat := [8,31,992,31775,1082401,4329604,8659208,17318416]
def z1148 : List Nat := [8,31,992,31775,2164802,4329604,8659208,17318416]
def z1149 : List Nat := [8,31,992,1015808,1047552,1082401,2164802,4329604]
def z1150 : List Nat := [8,31,992,1015808,1048575,1082401,2164802,4329604]
def z1151 : List Nat := [8,31,992,1015808,1082401,2164802,4329604,32505856]
def z1152 : List Nat := [8,31,992,1015808,1082401,2164802,4329604,32505887]
def z1153 : List Nat := [8,31,992,1015808,1082401,2164802,4329604,33521664]
def z1154 : List Nat := [8,31,992,1015808,1082401,2164802,4329604,33522687]
def z1155 : List Nat := [8,31,992,1015808,1082401,2164802,4357252,8659208,17318416,32505856]
def z1156 : List Nat := [8,31,992,1015808,1082401,2164802,5412005,32505856]
def z1157 : List Nat := [8,31,992,1015808,1082401,2164802,25977624,32505856]
def z1158 : List Nat := [8,31,992,1015808,1082401,2164802,29224827,32505856]
def z1159 : List Nat := [8,31,992,1015808,1082401,2164831,4329604,32505856]
def z1160 : List Nat := [8,31,992,1015808,1082401,2194498,4329604,8659208,17318416,32505856]
def z1161 : List Nat := [8,31,992,1015808,1082401,3247203,4329604,32505856]
def z1162 : List Nat := [8,31,992,1015808,1082401,4329604,6494406,32505856]
def z1163 : List Nat := [8,31,992,1015808,1082401,4329604,25977624,32505856]
def z1164 : List Nat := [8,31,992,1015808,1082401,4329604,31389629,32505856]
def z1165 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,33521664]
def z1166 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,33522687]
def z1167 : List Nat := [8,31,992,1082401,2164802,4329604,33521664]
def z1168 : List Nat := [8,31,992,1082401,2164802,4329604,33522687]
def z1169 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,33521664]
def z1170 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,33522687]
def z1171 : List Nat := [8,31,992,1082401,4329604,8659208,17318416,33521664]
def z1172 : List Nat := [8,31,992,1082401,4329604,8659208,17318416,33522687]
def z1173 : List Nat := [8,31,1023,31744,1015808,1082401,2164802,4329604]
def z1174 : List Nat := [8,31,1023,31744,1082401,2164802,4329604]
def z1175 : List Nat := [8,31,1023,31744,1082401,2164802,4329604,8659208]
def z1176 : List Nat := [8,31,1023,31744,1082401,2164802,8659208,17318416]
def z1177 : List Nat := [8,31,1023,31744,1082401,4329604,8659208,17318416]
def z1178 : List Nat := [8,31,1023,31744,2164802,4329604,8659208,17318416]
def z1179 : List Nat := [8,31,1023,1015808,1082401,2164802,4329604,32505856]
def z1180 : List Nat := [8,31,1024,1015808,1082401,2164802,4329604,32505856]
def z1181 : List Nat := [8,31,31744,32736,1015808,1082401,2164802,4329604]
def z1182 : List Nat := [8,31,31744,32736,1082401,2164802,4329604]
def z1183 : List Nat := [8,31,31744,32736,1082401,2164802,4329604,8659208]
def z1184 : List Nat := [8,31,31744,32736,1082401,2164802,8659208,17318416]
def z1185 : List Nat := [8,31,31744,32736,1082401,4329604,8659208,17318416]
def z1186 : List Nat := [8,31,31744,32736,2164802,4329604,8659208,17318416]
def z1187 : List Nat := [8,31,31744,1015808,1016800,1082401,2164802,4329604]
def z1188 : List Nat := [8,31,31744,1015808,1048575,1082401,2164802,4329604]
def z1189 : List Nat := [8,31,31744,1015808,1082401,1083361,2164802,4329604]
def z1190 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,32505856]
def z1191 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,32505887]
def z1192 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,32537600]
def z1193 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,32539681]
def z1194 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,33521664]
def z1195 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,33553439]
def z1196 : List Nat := [8,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856]
def z1197 : List Nat := [8,31,31744,1015808,1082401,2164802,5412005,32505856]
def z1198 : List Nat := [8,31,31744,1015808,1082401,2164802,6494406,32505856]
def z1199 : List Nat := [8,31,31744,1015808,1082401,2164802,25977624,32505856]
def z1200 : List Nat := [8,31,31744,1015808,1082401,2164802,29224827,32505856]
def z1201 : List Nat := [8,31,31744,1015808,1082401,2164831,4329604,32505856]
def z1202 : List Nat := [8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856]
def z1203 : List Nat := [8,31,31744,1015808,1082401,3247203,4329604,32505856]
def z1204 : List Nat := [8,31,31744,1015808,1082401,4329604,6494406,32505856]
def z1205 : List Nat := [8,31,31744,1015808,1082401,4329604,25977624,32505856]
def z1206 : List Nat := [8,31,31744,1015808,1082401,4329604,31389629,32505856]
def z1207 : List Nat := [8,31,31744,1015808,1083361,2164802,4329604]
def z1208 : List Nat := [8,31,31744,1015808,1083361,2164802,4329604,8659208]
def z1209 : List Nat := [8,31,31744,1015808,1083361,2164802,4329604,32505856]
def z1210 : List Nat := [8,31,31744,1015808,2164802,3247203,4329604,32505856]
def z1211 : List Nat := [8,31,31744,1015808,2164802,4329604,5412005,32505856]
def z1212 : List Nat := [8,31,31744,1015808,2164802,4329604,25977624,32505856]
def z1213 : List Nat := [8,31,31744,1015808,2164802,4329604,32472030,32505856]
def z1214 : List Nat := [8,31,31744,1015808,2164802,8659208,17318416,32539681]
def z1215 : List Nat := [8,31,31744,1015808,4329604,8659208,17318416,32539681]
def z1216 : List Nat := [8,31,31744,1082401,1083361,2164802,4329604]
def z1217 : List Nat := [8,31,31744,1082401,1083361,2164802,4329604,8659208]
def z1218 : List Nat := [8,31,31744,1082401,1083361,2164802,8659208,17318416]
def z1219 : List Nat := [8,31,31744,1082401,1083361,4329604,8659208,17318416]
def z1220 : List Nat := [8,31,31744,1082401,2164802,4329604,8659208,33521664]
def z1221 : List Nat := [8,31,31744,1082401,2164802,4329604,8659208,33553439]
def z1222 : List Nat := [8,31,31744,1082401,2164802,4329604,33521664]
def z1223 : List Nat := [8,31,31744,1082401,2164802,4329604,33553439]
def z1224 : List Nat := [8,31,31744,1082401,2164802,8659208,17318416,33521664]
def z1225 : List Nat := [8,31,31744,1082401,2164802,8659208,17318416,33553439]
def z1226 : List Nat := [8,31,31744,1082401,4329604,8659208,17318416,33521664]
def z1227 : List Nat := [8,31,31744,1082401,4329604,8659208,17318416,33553439]
def z1228 : List Nat := [8,31,31744,1083361,2164802,4329604]
def z1229 : List Nat := [8,31,31744,1083361,2164802,4329604,8659208]
def z1230 : List Nat := [8,31,31744,1083361,2164802,4329604,8659208,17318416]
def z1231 : List Nat := [8,31,31744,2164802,4329604,8659208,17318416,33521664]
def z1232 : List Nat := [8,31,31744,2164802,4329604,8659208,17318416,33553439]
def z1233 : List Nat := [8,31,31775,1015808,1082401,2164802,4329604,32505856]
def z1234 : List Nat := [8,31,1015808,1016800,1082401,2164802,4329604,32505856]
def z1235 : List Nat := [8,31,1015808,1047552,1082401,2164802,4329604,32505856]
def z1236 : List Nat := [8,31,1015808,1082401,2164802,2165730,4329604,32505856]
def z1237 : List Nat := [8,31,1015808,1082401,2164802,2194498,4329604,32505856]
def z1238 : List Nat := [8,31,1015808,1082401,2164802,4329604,4330468,32505856]
def z1239 : List Nat := [8,31,1015808,1082401,2164802,4329604,4357252,32505856]
def z1240 : List Nat := [8,31,1015808,1082401,2164802,4329604,8659944,32505856]
def z1241 : List Nat := [8,31,1015808,1082401,2164802,4329604,8682760,32505856]
def z1242 : List Nat := [8,31,1015808,1082401,2164802,4329604,32505856,33522687]
def z1243 : List Nat := [8,31,1015808,1082401,2164802,4329604,32505856,33553439]
def z1244 : List Nat := [8,31,1015808,1082401,2165730,8659208,17318416,32505856]
def z1245 : List Nat := [8,31,1015808,1082401,2194498,8659208,17318416,32505856]
def z1246 : List Nat := [8,31,1015808,1082401,4330468,8659208,17318416,32505856]
def z1247 : List Nat := [8,31,1015808,1082401,4357252,8659208,17318416,32505856]
def z1248 : List Nat := [8,31,1015808,2164802,4329604,8659208,17318896,32505856]
def z1249 : List Nat := [8,31,1015808,2164802,4357252,8659208,17318416,32505856]
def z1250 : List Nat := [8,31,1015808,2194498,4329604,8659208,17318416,32505856]
def z1251 : List Nat := [8,31744,31775,1015808,1082401,2164802,4329604,32505856]
def z1252 : List Nat := [8,31744,1015808,1015839,1082401,2164802,4329604,32505856]
def z1253 : List Nat := [8,31744,1015808,1082401,2164802,4329604,4329631,32505856]
def z1254 : List Nat := [8,31744,1015808,1082401,2164802,4329604,8659231,32505856]
def z1255 : List Nat := [8,31744,1015808,1082401,2164802,4329604,32505856,33553439]
def z1256 : List Nat := [8,31744,1015808,1082401,4329604,8659208,17318431,32505856]
def z1257 : List Nat := [8,31744,1015808,1082401,4330468,8659208,17318416,32505856]
def z1258 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604]
def z1259 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,8659208]
def z1260 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856]
def z1261 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,32505856]
def z1262 : List Nat := [9,31,992,31744,1015808,1082401,2164802,8659208,17318416]
def z1263 : List Nat := [9,31,992,31744,1015808,1082401,4329604,8659208,17318416]
def z1264 : List Nat := [9,31,992,31744,1082401,2164802,4329604]
def z1265 : List Nat := [9,31,992,31744,1082401,2164802,4329604,8659208]
def z1266 : List Nat := [9,31,992,31744,1082401,2164802,4329604,8659208,17318416]
def z1267 : List Nat := [9,31,992,31744,1082401,2164802,8659208,17318416]
def z1268 : List Nat := [9,31,992,31744,1082401,4329604,8659208,17318416]
def z1269 : List Nat := [9,31,992,1015808,1082401,2164802,4329604,8659208,32505856]
def z1270 : List Nat := [9,31,992,1015808,1082401,2164802,4329604,32505856]
def z1271 : List Nat := [9,31,992,1015808,1082401,2164802,8659208,17318416,32505856]
def z1272 : List Nat := [9,31,992,1015808,1082401,4329604,8659208,17318416,32505856]
def z1273 : List Nat := [9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856]
def z1274 : List Nat := [9,31,31744,1015808,1082401,2164802,4329604,32505856]
def z1275 : List Nat := [9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856]
def z1276 : List Nat := [9,31,31744,1015808,1082401,4329604,8659208,17318416,32505856]
def z1277 : List Nat := [9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def T_ : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z0 .lf) z1 .lf) z2 (.nd .lf z3 .lf)) z4 (.nd (.nd (.nd .lf z5 .lf) z6 .lf) z7 (.nd .lf z8 .lf))) z9 (.nd (.nd (.nd (.nd .lf z10 .lf) z11 .lf) z12 (.nd .lf z13 .lf)) z14 (.nd (.nd (.nd .lf z15 .lf) z16 .lf) z17 (.nd .lf z18 .lf)))) z19 (.nd (.nd (.nd (.nd (.nd .lf z20 .lf) z21 .lf) z22 (.nd .lf z23 .lf)) z24 (.nd (.nd (.nd .lf z25 .lf) z26 .lf) z27 (.nd .lf z28 .lf))) z29 (.nd (.nd (.nd (.nd .lf z30 .lf) z31 .lf) z32 (.nd .lf z33 .lf)) z34 (.nd (.nd (.nd .lf z35 .lf) z36 .lf) z37 (.nd .lf z38 .lf))))) z39 (.nd (.nd (.nd (.nd (.nd (.nd .lf z40 .lf) z41 .lf) z42 (.nd .lf z43 .lf)) z44 (.nd (.nd (.nd .lf z45 .lf) z46 .lf) z47 (.nd .lf z48 .lf))) z49 (.nd (.nd (.nd (.nd .lf z50 .lf) z51 .lf) z52 (.nd .lf z53 .lf)) z54 (.nd (.nd (.nd .lf z55 .lf) z56 .lf) z57 (.nd .lf z58 .lf)))) z59 (.nd (.nd (.nd (.nd (.nd .lf z60 .lf) z61 .lf) z62 (.nd .lf z63 .lf)) z64 (.nd (.nd (.nd .lf z65 .lf) z66 .lf) z67 (.nd .lf z68 .lf))) z69 (.nd (.nd (.nd (.nd .lf z70 .lf) z71 .lf) z72 (.nd .lf z73 .lf)) z74 (.nd (.nd (.nd .lf z75 .lf) z76 .lf) z77 (.nd .lf z78 .lf)))))) z79 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z80 .lf) z81 .lf) z82 (.nd .lf z83 .lf)) z84 (.nd (.nd (.nd .lf z85 .lf) z86 .lf) z87 (.nd .lf z88 .lf))) z89 (.nd (.nd (.nd (.nd .lf z90 .lf) z91 .lf) z92 (.nd .lf z93 .lf)) z94 (.nd (.nd (.nd .lf z95 .lf) z96 .lf) z97 (.nd .lf z98 .lf)))) z99 (.nd (.nd (.nd (.nd (.nd .lf z100 .lf) z101 .lf) z102 (.nd .lf z103 .lf)) z104 (.nd (.nd (.nd .lf z105 .lf) z106 .lf) z107 (.nd .lf z108 .lf))) z109 (.nd (.nd (.nd (.nd .lf z110 .lf) z111 .lf) z112 (.nd .lf z113 .lf)) z114 (.nd (.nd (.nd .lf z115 .lf) z116 .lf) z117 (.nd .lf z118 .lf))))) z119 (.nd (.nd (.nd (.nd (.nd (.nd .lf z120 .lf) z121 .lf) z122 (.nd .lf z123 .lf)) z124 (.nd (.nd (.nd .lf z125 .lf) z126 .lf) z127 (.nd .lf z128 .lf))) z129 (.nd (.nd (.nd (.nd .lf z130 .lf) z131 .lf) z132 (.nd .lf z133 .lf)) z134 (.nd (.nd (.nd .lf z135 .lf) z136 .lf) z137 (.nd .lf z138 .lf)))) z139 (.nd (.nd (.nd (.nd (.nd .lf z140 .lf) z141 .lf) z142 (.nd .lf z143 .lf)) z144 (.nd (.nd (.nd .lf z145 .lf) z146 .lf) z147 (.nd .lf z148 .lf))) z149 (.nd (.nd (.nd (.nd .lf z150 .lf) z151 .lf) z152 (.nd .lf z153 .lf)) z154 (.nd (.nd (.nd .lf z155 .lf) z156 .lf) z157 (.nd .lf z158 .lf))))))) z159 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z160 .lf) z161 .lf) z162 (.nd .lf z163 .lf)) z164 (.nd (.nd (.nd .lf z165 .lf) z166 .lf) z167 (.nd .lf z168 .lf))) z169 (.nd (.nd (.nd (.nd .lf z170 .lf) z171 .lf) z172 (.nd .lf z173 .lf)) z174 (.nd (.nd (.nd .lf z175 .lf) z176 .lf) z177 (.nd .lf z178 .lf)))) z179 (.nd (.nd (.nd (.nd (.nd .lf z180 .lf) z181 .lf) z182 (.nd .lf z183 .lf)) z184 (.nd (.nd (.nd .lf z185 .lf) z186 .lf) z187 (.nd .lf z188 .lf))) z189 (.nd (.nd (.nd (.nd .lf z190 .lf) z191 .lf) z192 (.nd .lf z193 .lf)) z194 (.nd (.nd (.nd .lf z195 .lf) z196 .lf) z197 (.nd .lf z198 .lf))))) z199 (.nd (.nd (.nd (.nd (.nd (.nd .lf z200 .lf) z201 .lf) z202 (.nd .lf z203 .lf)) z204 (.nd (.nd (.nd .lf z205 .lf) z206 .lf) z207 (.nd .lf z208 .lf))) z209 (.nd (.nd (.nd (.nd .lf z210 .lf) z211 .lf) z212 (.nd .lf z213 .lf)) z214 (.nd (.nd (.nd .lf z215 .lf) z216 .lf) z217 (.nd .lf z218 .lf)))) z219 (.nd (.nd (.nd (.nd (.nd .lf z220 .lf) z221 .lf) z222 (.nd .lf z223 .lf)) z224 (.nd (.nd (.nd .lf z225 .lf) z226 .lf) z227 (.nd .lf z228 .lf))) z229 (.nd (.nd (.nd (.nd .lf z230 .lf) z231 .lf) z232 (.nd .lf z233 .lf)) z234 (.nd (.nd (.nd .lf z235 .lf) z236 .lf) z237 (.nd .lf z238 .lf)))))) z239 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z240 .lf) z241 .lf) z242 (.nd .lf z243 .lf)) z244 (.nd (.nd (.nd .lf z245 .lf) z246 .lf) z247 (.nd .lf z248 .lf))) z249 (.nd (.nd (.nd (.nd .lf z250 .lf) z251 .lf) z252 (.nd .lf z253 .lf)) z254 (.nd (.nd (.nd .lf z255 .lf) z256 .lf) z257 (.nd .lf z258 .lf)))) z259 (.nd (.nd (.nd (.nd (.nd .lf z260 .lf) z261 .lf) z262 (.nd .lf z263 .lf)) z264 (.nd (.nd (.nd .lf z265 .lf) z266 .lf) z267 (.nd .lf z268 .lf))) z269 (.nd (.nd (.nd (.nd .lf z270 .lf) z271 .lf) z272 (.nd .lf z273 .lf)) z274 (.nd (.nd (.nd .lf z275 .lf) z276 .lf) z277 (.nd .lf z278 .lf))))) z279 (.nd (.nd (.nd (.nd (.nd (.nd .lf z280 .lf) z281 .lf) z282 (.nd .lf z283 .lf)) z284 (.nd (.nd (.nd .lf z285 .lf) z286 .lf) z287 (.nd .lf z288 .lf))) z289 (.nd (.nd (.nd (.nd .lf z290 .lf) z291 .lf) z292 (.nd .lf z293 .lf)) z294 (.nd (.nd (.nd .lf z295 .lf) z296 .lf) z297 (.nd .lf z298 .lf)))) z299 (.nd (.nd (.nd (.nd (.nd .lf z300 .lf) z301 .lf) z302 (.nd .lf z303 .lf)) z304 (.nd (.nd (.nd .lf z305 .lf) z306 .lf) z307 (.nd .lf z308 .lf))) z309 (.nd (.nd (.nd (.nd .lf z310 .lf) z311 .lf) z312 (.nd .lf z313 .lf)) z314 (.nd (.nd (.nd .lf z315 .lf) z316 .lf) z317 (.nd .lf z318 .lf)))))))) z319 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z320 .lf) z321 .lf) z322 (.nd .lf z323 .lf)) z324 (.nd (.nd (.nd .lf z325 .lf) z326 .lf) z327 (.nd .lf z328 .lf))) z329 (.nd (.nd (.nd (.nd .lf z330 .lf) z331 .lf) z332 (.nd .lf z333 .lf)) z334 (.nd (.nd (.nd .lf z335 .lf) z336 .lf) z337 (.nd .lf z338 .lf)))) z339 (.nd (.nd (.nd (.nd (.nd .lf z340 .lf) z341 .lf) z342 (.nd .lf z343 .lf)) z344 (.nd (.nd (.nd .lf z345 .lf) z346 .lf) z347 (.nd .lf z348 .lf))) z349 (.nd (.nd (.nd (.nd .lf z350 .lf) z351 .lf) z352 (.nd .lf z353 .lf)) z354 (.nd (.nd (.nd .lf z355 .lf) z356 .lf) z357 (.nd .lf z358 .lf))))) z359 (.nd (.nd (.nd (.nd (.nd (.nd .lf z360 .lf) z361 .lf) z362 (.nd .lf z363 .lf)) z364 (.nd (.nd (.nd .lf z365 .lf) z366 .lf) z367 (.nd .lf z368 .lf))) z369 (.nd (.nd (.nd (.nd .lf z370 .lf) z371 .lf) z372 (.nd .lf z373 .lf)) z374 (.nd (.nd (.nd .lf z375 .lf) z376 .lf) z377 (.nd .lf z378 .lf)))) z379 (.nd (.nd (.nd (.nd (.nd .lf z380 .lf) z381 .lf) z382 (.nd .lf z383 .lf)) z384 (.nd (.nd (.nd .lf z385 .lf) z386 .lf) z387 (.nd .lf z388 .lf))) z389 (.nd (.nd (.nd (.nd .lf z390 .lf) z391 .lf) z392 (.nd .lf z393 .lf)) z394 (.nd (.nd (.nd .lf z395 .lf) z396 .lf) z397 (.nd .lf z398 .lf)))))) z399 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z400 .lf) z401 .lf) z402 (.nd .lf z403 .lf)) z404 (.nd (.nd (.nd .lf z405 .lf) z406 .lf) z407 (.nd .lf z408 .lf))) z409 (.nd (.nd (.nd (.nd .lf z410 .lf) z411 .lf) z412 (.nd .lf z413 .lf)) z414 (.nd (.nd (.nd .lf z415 .lf) z416 .lf) z417 (.nd .lf z418 .lf)))) z419 (.nd (.nd (.nd (.nd (.nd .lf z420 .lf) z421 .lf) z422 (.nd .lf z423 .lf)) z424 (.nd (.nd (.nd .lf z425 .lf) z426 .lf) z427 (.nd .lf z428 .lf))) z429 (.nd (.nd (.nd (.nd .lf z430 .lf) z431 .lf) z432 (.nd .lf z433 .lf)) z434 (.nd (.nd (.nd .lf z435 .lf) z436 .lf) z437 (.nd .lf z438 .lf))))) z439 (.nd (.nd (.nd (.nd (.nd (.nd .lf z440 .lf) z441 .lf) z442 (.nd .lf z443 .lf)) z444 (.nd (.nd (.nd .lf z445 .lf) z446 .lf) z447 (.nd .lf z448 .lf))) z449 (.nd (.nd (.nd (.nd .lf z450 .lf) z451 .lf) z452 (.nd .lf z453 .lf)) z454 (.nd (.nd (.nd .lf z455 .lf) z456 .lf) z457 (.nd .lf z458 .lf)))) z459 (.nd (.nd (.nd (.nd (.nd .lf z460 .lf) z461 .lf) z462 (.nd .lf z463 .lf)) z464 (.nd (.nd (.nd .lf z465 .lf) z466 .lf) z467 (.nd .lf z468 .lf))) z469 (.nd (.nd (.nd (.nd .lf z470 .lf) z471 .lf) z472 (.nd .lf z473 .lf)) z474 (.nd (.nd (.nd .lf z475 .lf) z476 .lf) z477 (.nd .lf z478 .lf))))))) z479 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z480 .lf) z481 .lf) z482 (.nd .lf z483 .lf)) z484 (.nd (.nd (.nd .lf z485 .lf) z486 .lf) z487 (.nd .lf z488 .lf))) z489 (.nd (.nd (.nd (.nd .lf z490 .lf) z491 .lf) z492 (.nd .lf z493 .lf)) z494 (.nd (.nd (.nd .lf z495 .lf) z496 .lf) z497 (.nd .lf z498 .lf)))) z499 (.nd (.nd (.nd (.nd (.nd .lf z500 .lf) z501 .lf) z502 (.nd .lf z503 .lf)) z504 (.nd (.nd (.nd .lf z505 .lf) z506 .lf) z507 (.nd .lf z508 .lf))) z509 (.nd (.nd (.nd (.nd .lf z510 .lf) z511 .lf) z512 (.nd .lf z513 .lf)) z514 (.nd (.nd (.nd .lf z515 .lf) z516 .lf) z517 (.nd .lf z518 .lf))))) z519 (.nd (.nd (.nd (.nd (.nd (.nd .lf z520 .lf) z521 .lf) z522 (.nd .lf z523 .lf)) z524 (.nd (.nd (.nd .lf z525 .lf) z526 .lf) z527 (.nd .lf z528 .lf))) z529 (.nd (.nd (.nd (.nd .lf z530 .lf) z531 .lf) z532 (.nd .lf z533 .lf)) z534 (.nd (.nd (.nd .lf z535 .lf) z536 .lf) z537 (.nd .lf z538 .lf)))) z539 (.nd (.nd (.nd (.nd (.nd .lf z540 .lf) z541 .lf) z542 (.nd .lf z543 .lf)) z544 (.nd (.nd (.nd .lf z545 .lf) z546 .lf) z547 (.nd .lf z548 .lf))) z549 (.nd (.nd (.nd (.nd .lf z550 .lf) z551 .lf) z552 (.nd .lf z553 .lf)) z554 (.nd (.nd (.nd .lf z555 .lf) z556 .lf) z557 (.nd .lf z558 .lf)))))) z559 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z560 .lf) z561 .lf) z562 (.nd .lf z563 .lf)) z564 (.nd (.nd (.nd .lf z565 .lf) z566 .lf) z567 (.nd .lf z568 .lf))) z569 (.nd (.nd (.nd (.nd .lf z570 .lf) z571 .lf) z572 (.nd .lf z573 .lf)) z574 (.nd (.nd (.nd .lf z575 .lf) z576 .lf) z577 (.nd .lf z578 .lf)))) z579 (.nd (.nd (.nd (.nd (.nd .lf z580 .lf) z581 .lf) z582 (.nd .lf z583 .lf)) z584 (.nd (.nd (.nd .lf z585 .lf) z586 .lf) z587 (.nd .lf z588 .lf))) z589 (.nd (.nd (.nd (.nd .lf z590 .lf) z591 .lf) z592 (.nd .lf z593 .lf)) z594 (.nd (.nd (.nd .lf z595 .lf) z596 .lf) z597 (.nd .lf z598 .lf))))) z599 (.nd (.nd (.nd (.nd (.nd (.nd .lf z600 .lf) z601 .lf) z602 (.nd .lf z603 .lf)) z604 (.nd (.nd (.nd .lf z605 .lf) z606 .lf) z607 (.nd .lf z608 .lf))) z609 (.nd (.nd (.nd (.nd .lf z610 .lf) z611 .lf) z612 (.nd .lf z613 .lf)) z614 (.nd (.nd (.nd .lf z615 .lf) z616 .lf) z617 (.nd .lf z618 .lf)))) z619 (.nd (.nd (.nd (.nd (.nd .lf z620 .lf) z621 .lf) z622 (.nd .lf z623 .lf)) z624 (.nd (.nd (.nd .lf z625 .lf) z626 .lf) z627 (.nd .lf z628 .lf))) z629 (.nd (.nd (.nd (.nd .lf z630 .lf) z631 .lf) z632 (.nd .lf z633 .lf)) z634 (.nd (.nd (.nd .lf z635 .lf) z636 .lf) z637 (.nd .lf z638 .lf))))))))) z639 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z640 .lf) z641 .lf) z642 (.nd .lf z643 .lf)) z644 (.nd (.nd (.nd .lf z645 .lf) z646 .lf) z647 (.nd .lf z648 .lf))) z649 (.nd (.nd (.nd (.nd .lf z650 .lf) z651 .lf) z652 (.nd .lf z653 .lf)) z654 (.nd (.nd (.nd .lf z655 .lf) z656 .lf) z657 (.nd .lf z658 .lf)))) z659 (.nd (.nd (.nd (.nd (.nd .lf z660 .lf) z661 .lf) z662 (.nd .lf z663 .lf)) z664 (.nd (.nd (.nd .lf z665 .lf) z666 .lf) z667 (.nd .lf z668 .lf))) z669 (.nd (.nd (.nd (.nd .lf z670 .lf) z671 .lf) z672 (.nd .lf z673 .lf)) z674 (.nd (.nd (.nd .lf z675 .lf) z676 .lf) z677 (.nd .lf z678 .lf))))) z679 (.nd (.nd (.nd (.nd (.nd (.nd .lf z680 .lf) z681 .lf) z682 (.nd .lf z683 .lf)) z684 (.nd (.nd (.nd .lf z685 .lf) z686 .lf) z687 (.nd .lf z688 .lf))) z689 (.nd (.nd (.nd (.nd .lf z690 .lf) z691 .lf) z692 (.nd .lf z693 .lf)) z694 (.nd (.nd (.nd .lf z695 .lf) z696 .lf) z697 (.nd .lf z698 .lf)))) z699 (.nd (.nd (.nd (.nd (.nd .lf z700 .lf) z701 .lf) z702 (.nd .lf z703 .lf)) z704 (.nd (.nd (.nd .lf z705 .lf) z706 .lf) z707 (.nd .lf z708 .lf))) z709 (.nd (.nd (.nd (.nd .lf z710 .lf) z711 .lf) z712 (.nd .lf z713 .lf)) z714 (.nd (.nd (.nd .lf z715 .lf) z716 .lf) z717 (.nd .lf z718 .lf)))))) z719 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z720 .lf) z721 .lf) z722 (.nd .lf z723 .lf)) z724 (.nd (.nd (.nd .lf z725 .lf) z726 .lf) z727 (.nd .lf z728 .lf))) z729 (.nd (.nd (.nd (.nd .lf z730 .lf) z731 .lf) z732 (.nd .lf z733 .lf)) z734 (.nd (.nd (.nd .lf z735 .lf) z736 .lf) z737 (.nd .lf z738 .lf)))) z739 (.nd (.nd (.nd (.nd (.nd .lf z740 .lf) z741 .lf) z742 (.nd .lf z743 .lf)) z744 (.nd (.nd (.nd .lf z745 .lf) z746 .lf) z747 (.nd .lf z748 .lf))) z749 (.nd (.nd (.nd (.nd .lf z750 .lf) z751 .lf) z752 (.nd .lf z753 .lf)) z754 (.nd (.nd (.nd .lf z755 .lf) z756 .lf) z757 (.nd .lf z758 .lf))))) z759 (.nd (.nd (.nd (.nd (.nd (.nd .lf z760 .lf) z761 .lf) z762 (.nd .lf z763 .lf)) z764 (.nd (.nd (.nd .lf z765 .lf) z766 .lf) z767 (.nd .lf z768 .lf))) z769 (.nd (.nd (.nd (.nd .lf z770 .lf) z771 .lf) z772 (.nd .lf z773 .lf)) z774 (.nd (.nd (.nd .lf z775 .lf) z776 .lf) z777 (.nd .lf z778 .lf)))) z779 (.nd (.nd (.nd (.nd (.nd .lf z780 .lf) z781 .lf) z782 (.nd .lf z783 .lf)) z784 (.nd (.nd (.nd .lf z785 .lf) z786 .lf) z787 (.nd .lf z788 .lf))) z789 (.nd (.nd (.nd (.nd .lf z790 .lf) z791 .lf) z792 (.nd .lf z793 .lf)) z794 (.nd (.nd (.nd .lf z795 .lf) z796 .lf) z797 (.nd .lf z798 .lf))))))) z799 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z800 .lf) z801 .lf) z802 (.nd .lf z803 .lf)) z804 (.nd (.nd (.nd .lf z805 .lf) z806 .lf) z807 (.nd .lf z808 .lf))) z809 (.nd (.nd (.nd (.nd .lf z810 .lf) z811 .lf) z812 (.nd .lf z813 .lf)) z814 (.nd (.nd (.nd .lf z815 .lf) z816 .lf) z817 (.nd .lf z818 .lf)))) z819 (.nd (.nd (.nd (.nd (.nd .lf z820 .lf) z821 .lf) z822 (.nd .lf z823 .lf)) z824 (.nd (.nd (.nd .lf z825 .lf) z826 .lf) z827 (.nd .lf z828 .lf))) z829 (.nd (.nd (.nd (.nd .lf z830 .lf) z831 .lf) z832 (.nd .lf z833 .lf)) z834 (.nd (.nd (.nd .lf z835 .lf) z836 .lf) z837 (.nd .lf z838 .lf))))) z839 (.nd (.nd (.nd (.nd (.nd (.nd .lf z840 .lf) z841 .lf) z842 (.nd .lf z843 .lf)) z844 (.nd (.nd (.nd .lf z845 .lf) z846 .lf) z847 (.nd .lf z848 .lf))) z849 (.nd (.nd (.nd (.nd .lf z850 .lf) z851 .lf) z852 (.nd .lf z853 .lf)) z854 (.nd (.nd (.nd .lf z855 .lf) z856 .lf) z857 (.nd .lf z858 .lf)))) z859 (.nd (.nd (.nd (.nd (.nd .lf z860 .lf) z861 .lf) z862 (.nd .lf z863 .lf)) z864 (.nd (.nd (.nd .lf z865 .lf) z866 .lf) z867 (.nd .lf z868 .lf))) z869 (.nd (.nd (.nd (.nd .lf z870 .lf) z871 .lf) z872 (.nd .lf z873 .lf)) z874 (.nd (.nd (.nd .lf z875 .lf) z876 .lf) z877 (.nd .lf z878 .lf)))))) z879 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z880 .lf) z881 .lf) z882 (.nd .lf z883 .lf)) z884 (.nd (.nd (.nd .lf z885 .lf) z886 .lf) z887 (.nd .lf z888 .lf))) z889 (.nd (.nd (.nd (.nd .lf z890 .lf) z891 .lf) z892 (.nd .lf z893 .lf)) z894 (.nd (.nd (.nd .lf z895 .lf) z896 .lf) z897 (.nd .lf z898 .lf)))) z899 (.nd (.nd (.nd (.nd (.nd .lf z900 .lf) z901 .lf) z902 (.nd .lf z903 .lf)) z904 (.nd (.nd (.nd .lf z905 .lf) z906 .lf) z907 (.nd .lf z908 .lf))) z909 (.nd (.nd (.nd (.nd .lf z910 .lf) z911 .lf) z912 (.nd .lf z913 .lf)) z914 (.nd (.nd (.nd .lf z915 .lf) z916 .lf) z917 (.nd .lf z918 .lf))))) z919 (.nd (.nd (.nd (.nd (.nd (.nd .lf z920 .lf) z921 .lf) z922 (.nd .lf z923 .lf)) z924 (.nd (.nd (.nd .lf z925 .lf) z926 .lf) z927 (.nd .lf z928 .lf))) z929 (.nd (.nd (.nd (.nd .lf z930 .lf) z931 .lf) z932 (.nd .lf z933 .lf)) z934 (.nd (.nd (.nd .lf z935 .lf) z936 .lf) z937 (.nd .lf z938 .lf)))) z939 (.nd (.nd (.nd (.nd (.nd .lf z940 .lf) z941 .lf) z942 (.nd .lf z943 .lf)) z944 (.nd (.nd (.nd .lf z945 .lf) z946 .lf) z947 (.nd .lf z948 .lf))) z949 (.nd (.nd (.nd (.nd .lf z950 .lf) z951 .lf) z952 (.nd .lf z953 .lf)) z954 (.nd (.nd (.nd .lf z955 .lf) z956 .lf) z957 (.nd .lf z958 .lf)))))))) z959 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z960 .lf) z961 .lf) z962 (.nd .lf z963 .lf)) z964 (.nd (.nd (.nd .lf z965 .lf) z966 .lf) z967 (.nd .lf z968 .lf))) z969 (.nd (.nd (.nd (.nd .lf z970 .lf) z971 .lf) z972 (.nd .lf z973 .lf)) z974 (.nd (.nd (.nd .lf z975 .lf) z976 .lf) z977 (.nd .lf z978 .lf)))) z979 (.nd (.nd (.nd (.nd (.nd .lf z980 .lf) z981 .lf) z982 (.nd .lf z983 .lf)) z984 (.nd (.nd (.nd .lf z985 .lf) z986 .lf) z987 (.nd .lf z988 .lf))) z989 (.nd (.nd (.nd (.nd .lf z990 .lf) z991 .lf) z992 (.nd .lf z993 .lf)) z994 (.nd (.nd (.nd .lf z995 .lf) z996 .lf) z997 (.nd .lf z998 .lf))))) z999 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1000 .lf) z1001 .lf) z1002 (.nd .lf z1003 .lf)) z1004 (.nd (.nd (.nd .lf z1005 .lf) z1006 .lf) z1007 (.nd .lf z1008 .lf))) z1009 (.nd (.nd (.nd (.nd .lf z1010 .lf) z1011 .lf) z1012 (.nd .lf z1013 .lf)) z1014 (.nd (.nd (.nd .lf z1015 .lf) z1016 .lf) z1017 (.nd .lf z1018 .lf)))) z1019 (.nd (.nd (.nd (.nd (.nd .lf z1020 .lf) z1021 .lf) z1022 (.nd .lf z1023 .lf)) z1024 (.nd (.nd (.nd .lf z1025 .lf) z1026 .lf) z1027 (.nd .lf z1028 .lf))) z1029 (.nd (.nd (.nd (.nd .lf z1030 .lf) z1031 .lf) z1032 (.nd .lf z1033 .lf)) z1034 (.nd (.nd (.nd .lf z1035 .lf) z1036 .lf) z1037 (.nd .lf z1038 .lf)))))) z1039 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1040 .lf) z1041 .lf) z1042 (.nd .lf z1043 .lf)) z1044 (.nd (.nd (.nd .lf z1045 .lf) z1046 .lf) z1047 (.nd .lf z1048 .lf))) z1049 (.nd (.nd (.nd (.nd .lf z1050 .lf) z1051 .lf) z1052 (.nd .lf z1053 .lf)) z1054 (.nd (.nd (.nd .lf z1055 .lf) z1056 .lf) z1057 (.nd .lf z1058 .lf)))) z1059 (.nd (.nd (.nd (.nd (.nd .lf z1060 .lf) z1061 .lf) z1062 (.nd .lf z1063 .lf)) z1064 (.nd (.nd (.nd .lf z1065 .lf) z1066 .lf) z1067 (.nd .lf z1068 .lf))) z1069 (.nd (.nd (.nd (.nd .lf z1070 .lf) z1071 .lf) z1072 (.nd .lf z1073 .lf)) z1074 (.nd (.nd (.nd .lf z1075 .lf) z1076 .lf) z1077 (.nd .lf z1078 .lf))))) z1079 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1080 .lf) z1081 .lf) z1082 (.nd .lf z1083 .lf)) z1084 (.nd (.nd (.nd .lf z1085 .lf) z1086 .lf) z1087 (.nd .lf z1088 .lf))) z1089 (.nd (.nd (.nd (.nd .lf z1090 .lf) z1091 .lf) z1092 (.nd .lf z1093 .lf)) z1094 (.nd (.nd (.nd .lf z1095 .lf) z1096 .lf) z1097 (.nd .lf z1098 .lf)))) z1099 (.nd (.nd (.nd (.nd (.nd .lf z1100 .lf) z1101 .lf) z1102 (.nd .lf z1103 .lf)) z1104 (.nd (.nd (.nd .lf z1105 .lf) z1106 .lf) z1107 (.nd .lf z1108 .lf))) z1109 (.nd (.nd (.nd (.nd .lf z1110 .lf) z1111 .lf) z1112 (.nd .lf z1113 .lf)) z1114 (.nd (.nd (.nd .lf z1115 .lf) z1116 .lf) z1117 (.nd .lf z1118 .lf))))))) z1119 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1120 .lf) z1121 .lf) z1122 (.nd .lf z1123 .lf)) z1124 (.nd (.nd (.nd .lf z1125 .lf) z1126 .lf) z1127 (.nd .lf z1128 .lf))) z1129 (.nd (.nd (.nd (.nd .lf z1130 .lf) z1131 .lf) z1132 (.nd .lf z1133 .lf)) z1134 (.nd (.nd (.nd .lf z1135 .lf) z1136 .lf) z1137 (.nd .lf z1138 .lf)))) z1139 (.nd (.nd (.nd (.nd (.nd .lf z1140 .lf) z1141 .lf) z1142 (.nd .lf z1143 .lf)) z1144 (.nd (.nd (.nd .lf z1145 .lf) z1146 .lf) z1147 (.nd .lf z1148 .lf))) z1149 (.nd (.nd (.nd (.nd .lf z1150 .lf) z1151 .lf) z1152 (.nd .lf z1153 .lf)) z1154 (.nd (.nd (.nd .lf z1155 .lf) z1156 .lf) z1157 (.nd .lf z1158 .lf))))) z1159 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1160 .lf) z1161 .lf) z1162 (.nd .lf z1163 .lf)) z1164 (.nd (.nd (.nd .lf z1165 .lf) z1166 .lf) z1167 (.nd .lf z1168 .lf))) z1169 (.nd (.nd (.nd (.nd .lf z1170 .lf) z1171 .lf) z1172 (.nd .lf z1173 .lf)) z1174 (.nd (.nd (.nd .lf z1175 .lf) z1176 .lf) z1177 (.nd .lf z1178 .lf)))) z1179 (.nd (.nd (.nd (.nd (.nd .lf z1180 .lf) z1181 .lf) z1182 (.nd .lf z1183 .lf)) z1184 (.nd (.nd (.nd .lf z1185 .lf) z1186 .lf) z1187 (.nd .lf z1188 .lf))) z1189 (.nd (.nd (.nd (.nd .lf z1190 .lf) z1191 .lf) z1192 (.nd .lf z1193 .lf)) z1194 (.nd (.nd (.nd .lf z1195 .lf) z1196 .lf) z1197 (.nd .lf z1198 .lf)))))) z1199 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1200 .lf) z1201 .lf) z1202 (.nd .lf z1203 .lf)) z1204 (.nd (.nd (.nd .lf z1205 .lf) z1206 .lf) z1207 (.nd .lf z1208 .lf))) z1209 (.nd (.nd (.nd (.nd .lf z1210 .lf) z1211 .lf) z1212 (.nd .lf z1213 .lf)) z1214 (.nd (.nd (.nd .lf z1215 .lf) z1216 .lf) z1217 (.nd .lf z1218 .lf)))) z1219 (.nd (.nd (.nd (.nd (.nd .lf z1220 .lf) z1221 .lf) z1222 (.nd .lf z1223 .lf)) z1224 (.nd (.nd (.nd .lf z1225 .lf) z1226 .lf) z1227 (.nd .lf z1228 .lf))) z1229 (.nd (.nd (.nd (.nd .lf z1230 .lf) z1231 .lf) z1232 (.nd .lf z1233 .lf)) z1234 (.nd (.nd (.nd .lf z1235 .lf) z1236 .lf) z1237 (.nd .lf z1238 .lf))))) z1239 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1240 .lf) z1241 .lf) z1242 (.nd .lf z1243 .lf)) z1244 (.nd (.nd (.nd .lf z1245 .lf) z1246 .lf) z1247 (.nd .lf z1248 .lf))) z1249 (.nd (.nd (.nd (.nd .lf z1250 .lf) z1251 .lf) z1252 (.nd .lf z1253 .lf)) z1254 (.nd (.nd (.nd .lf z1255 .lf) z1256 .lf) z1257 (.nd .lf z1258 .lf)))) z1259 (.nd (.nd (.nd (.nd (.nd .lf z1260 .lf) z1261 .lf) z1262 (.nd .lf z1263 .lf)) z1264 (.nd (.nd (.nd .lf z1265 .lf) z1266 .lf) z1267 (.nd .lf z1268 .lf))) z1269 (.nd (.nd (.nd (.nd .lf z1270 .lf) z1271 .lf) z1272 (.nd .lf z1273 .lf)) z1274 (.nd (.nd .lf z1275 .lf) z1276 (.nd .lf z1277 .lf))))))))))
def P_ := stepOK 33554431 Y_ PD_ PM_ G_ T_
def b0 : List (List Nat × List (Nat × Nat)) := [(z0,[]),(z1,[(1024,32883),(1024,98355)]),(z2,[(1024,32947),(1024,163891)]),(z3,[(1024,33267),(1024,491571)]),(z4,[(1024,98483),(1024,163955)]),(z5,[(72,3),(1024,98803),(1024,491635)]),(z6,[]),(z7,[]),(z8,[(1024,98803),(1024,491635)]),(z9,[]),(z10,[(1024,51361),(1024,163891)]),(z11,[(1024,51627),(1024,436275)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : b0.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b1 : List (List Nat × List (Nat × Nat)) := [(z12,[(1024,51361),(1024,163891)]),(z13,[(1024,51299),(1024,100403)]),(z14,[(1024,51361),(1024,163891)]),(z15,[(1024,32867),(1024,34913)]),(z16,[(1024,51617),(1024,426035)]),(z17,[]),(z18,[(1024,98360),(1024,32888)]),(z19,[(1024,32952),(1024,163896)]),(z20,[(1024,33267),(1024,491571)]),(z21,[(1024,98355),(1024,32883)]),(z22,[]),(z23,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1 : b1.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b2 : List (List Nat × List (Nat × Nat)) := [(z24,[]),(z25,[(1024,51361),(1024,163891)]),(z26,[(1024,51361),(1024,163891)]),(z27,[(1024,51361),(1024,163891)]),(z28,[(1024,32883),(1024,98355)]),(z29,[(1024,163892),(1024,32948)]),(z30,[(1024,491572),(1024,33268)]),(z31,[(1024,491571),(1024,33267)]),(z32,[(72,3),(96,3),(1024,98803),(1024,491635)]),(z33,[(1024,116897),(1024,163955)]),(z34,[(1024,98488),(1024,163960)]),(z35,[(56,5),(96,3),(1024,98803),(1024,491635)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2 : b2.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b3 : List (List Nat × List (Nat × Nat)) := [(z36,[(56,0),(1024,98483),(1024,131252)]),(z37,[(96,3),(1024,98803),(1024,131572)]),(z38,[(1024,51361),(1024,163891)]),(z39,[(1024,51299),(1024,100403)]),(z40,[(72,3)]),(z41,[]),(z42,[]),(z43,[]),(z44,[(1024,182305),(1024,32947)]),(z45,[(1024,32867),(1024,34913)]),(z46,[(1024,182307),(1024,34995)]),(z47,[(72,3),(1024,182369),(1024,98483)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k3 : b3.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b4 : List (List Nat × List (Nat × Nat)) := [(z48,[(1024,34987),(1024,44193)]),(z49,[(1024,182369),(1024,98483)]),(z50,[(72,3),(1024,182369),(1024,98483)]),(z51,[(72,3),(1024,182369),(1024,116897)]),(z52,[(1024,98483),(1024,116897)]),(z53,[(72,3),(1024,182760),(1024,117217)]),(z54,[(1024,98803),(1024,117217)]),(z55,[(72,3),(1024,170081),(1024,98471)]),(z56,[]),(z57,[]),(z58,[]),(z59,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4 : b4.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b5 : List (List Nat × List (Nat × Nat)) := [(z60,[]),(z61,[]),(z62,[]),(z63,[]),(z64,[(1024,182369),(1024,98483)]),(z65,[(1024,182369),(1024,98483)]),(z66,[(1024,182369),(1024,98483)]),(z67,[(72,3),(1024,182369),(1024,98483)]),(z68,[(72,3),(1024,182369),(1024,98483)]),(z69,[(72,3),(1024,182369),(1024,98483)]),(z70,[(1024,498867),(1024,510049)]),(z71,[(1024,171283),(1024,182369)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5 : b5.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b6 : List (List Nat × List (Nat × Nat)) := [(z72,[(1024,98483),(1024,171283)]),(z73,[(1024,98803),(1024,498867)]),(z74,[(1024,171271),(1024,170081)]),(z75,[(56,1),(1024,98803),(1024,491635)]),(z76,[(56,0),(1024,98803),(1024,131572)]),(z77,[(72,3),(1024,164328),(1024,117217)]),(z78,[(1024,117217),(1024,98803)]),(z79,[(1024,51627),(1024,436275)]),(z80,[(72,3),(1024,182369),(1024,98483)]),(z81,[(1024,39073),(1024,44551)]),(z82,[(1024,32867),(1024,34913)]),(z83,[(1024,39073),(1024,44551)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6 : b6.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b7 : List (List Nat × List (Nat × Nat)) := [(z84,[(72,3),(96,3),(1024,182305),(1024,32947)]),(z85,[(72,3),(1024,182369),(1024,98483)]),(z86,[(56,3),(1024,444451),(1024,35251)]),(z87,[(1024,182369),(1024,98483)]),(z88,[]),(z89,[(104,3),(1024,51459),(1024,264243)]),(z90,[]),(z91,[]),(z92,[]),(z93,[(1024,51361),(1024,163891)]),(z94,[(1024,51367),(1024,170035)]),(z95,[(1024,444460),(1024,44467)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7 : b7.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b8 : List (List Nat × List (Nat × Nat)) := [(z96,[(56,3),(1024,51361),(1024,163891)]),(z97,[(1024,35379),(1024,51361)]),(z98,[(104,3),(1024,51361),(1024,163891)]),(z99,[(56,3),(1024,51361),(1024,163891)]),(z100,[(1024,51361),(1024,163891)]),(z101,[(1024,163891),(1024,51361)]),(z102,[(1024,163891),(1024,51361)]),(z103,[(1024,34931),(1024,51299)]),(z104,[(1024,35379),(1024,163891)]),(z105,[(1024,39073),(1024,170017)]),(z106,[(1024,32947),(1024,163891)]),(z107,[(1024,51367),(1024,170035)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8 : b8.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b9 : List (List Nat × List (Nat × Nat)) := [(z108,[(1024,182369),(1024,98483)]),(z109,[(1024,182305),(1024,32947)]),(z110,[(1024,116780),(1024,44147)]),(z111,[(1024,109619),(1024,51308)]),(z112,[(1024,116907),(1024,170017)]),(z113,[(1024,116907),(1024,174195)]),(z114,[(1024,51361),(1024,163891)]),(z115,[(1024,34924),(1024,44131)]),(z116,[(1024,182369),(1024,98483)]),(z117,[(1024,44563),(1024,51361)]),(z118,[(1024,116897),(1024,163955)]),(z119,[(1024,39073),(1024,32876)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k9 : b9.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b10 : List (List Nat × List (Nat × Nat)) := [(z120,[(1024,182316),(1024,44211)]),(z121,[(1024,444460),(1024,44467)]),(z122,[]),(z123,[(128,1)]),(z124,[(1024,32888),(1024,98360)]),(z125,[(1024,32953),(1024,98488)]),(z126,[(1024,33268),(1024,98803)]),(z127,[(1024,33267),(1024,131572)]),(z128,[(1024,32883),(1024,98355)]),(z129,[(192,0)]),(z130,[(1024,98867),(1024,491955)]),(z131,[(1024,44467),(1024,51361)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10 : b10.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b11 : List (List Nat × List (Nat × Nat)) := [(z132,[(1024,35379),(1024,44467)]),(z133,[(1024,44467),(1024,163891)]),(z134,[(1024,51361),(1024,182305)]),(z135,[(1024,51367),(1024,182311)]),(z136,[(1024,542819),(1024,100883)]),(z137,[(72,5),(80,1),(96,3),(128,3),(1024,98803),(1024,491635)]),(z138,[(72,4),(80,0),(96,3),(128,3),(1024,98803),(1024,131572)]),(z139,[(56,3),(96,3),(1024,117217),(1024,281095)]),(z140,[(56,3),(128,3),(1024,281095),(1024,100883)]),(z141,[(72,3),(128,3),(1024,510049),(1024,491635)]),(z142,[(96,3),(128,3),(1024,100883),(1024,491635)]),(z143,[(1024,116897),(1024,182369)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k11 : b11.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b12 : List (List Nat × List (Nat × Nat)) := [(z144,[(1024,116897),(1024,163955)]),(z145,[(72,0),(1024,98488),(1024,131257)]),(z146,[(56,5),(128,3),(1024,98803),(1024,131572)]),(z147,[(1024,182369),(1024,116897)]),(z148,[(56,3),(72,3),(96,3),(1024,51463),(1024,268339)]),(z149,[(72,3),(1024,116897),(1024,182369)]),(z150,[(72,3),(1024,182305),(1024,51361)]),(z151,[(1024,51361),(1024,182305)]),(z152,[(72,3),(1024,51299),(1024,116771)]),(z153,[(72,3),(1024,100403),(1024,116771)]),(z154,[(1024,182311),(1024,39091)]),(z155,[(1024,170035),(1024,51367)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12 : b12.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b13 : List (List Nat × List (Nat × Nat)) := [(z156,[(96,3),(112,3),(168,3)]),(z157,[(72,3),(1024,51681),(1024,281095)]),(z158,[(72,3),(1024,35347),(1024,51681)]),(z159,[(72,3),(1024,32867),(1024,34913)]),(z160,[(128,3),(1024,444907),(1024,117217)]),(z161,[(1024,268819),(1024,117217)]),(z162,[(1024,170017),(1024,32935)]),(z163,[(1024,34913),(1024,98339)]),(z164,[(1024,170248),(1024,32935)]),(z165,[(1024,509987),(1024,35315)]),(z166,[(1024,510379),(1024,33267)]),(z167,[(1024,171539),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13 : b13.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b14 : List (List Nat × List (Nat × Nat)) := [(z168,[(1024,170017),(1024,32935)]),(z169,[(1024,35315),(1024,117217)]),(z170,[(1024,98339),(1024,34913)]),(z171,[(1024,35307),(1024,44513)]),(z172,[(1024,100883),(1024,35307)]),(z173,[(128,3),(1024,117217),(1024,281095)]),(z174,[(1024,268819),(1024,117217)]),(z175,[(1024,171271),(1024,170017)]),(z176,[(1024,510379),(1024,32867)]),(z177,[(1024,542888),(1024,171539)]),(z178,[(96,3)]),(z179,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14 : b14.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b15 : List (List Nat × List (Nat × Nat)) := [(z180,[(72,3)]),(z181,[(72,3)]),(z182,[(72,3)]),(z183,[(96,3),(1024,444515),(1024,100787)]),(z184,[]),(z185,[]),(z186,[]),(z187,[(96,3),(1024,444679),(1024,117217)]),(z188,[(96,3),(1024,444679),(1024,117217)]),(z189,[(1024,35307),(1024,100915)]),(z190,[(1024,170017),(1024,117217)]),(z191,[(1024,543148),(1024,170017)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15 : b15.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b16 : List (List Nat × List (Nat × Nat)) := [(z192,[(1024,170017),(1024,32935)]),(z193,[(1024,509987),(1024,502195)]),(z194,[(1024,502195),(1024,117217)]),(z195,[(72,3),(1024,39393),(1024,35335)]),(z196,[(72,3),(1024,35335),(1024,39393)]),(z197,[(128,3),(1024,444907),(1024,117217)]),(z198,[(1024,268819),(1024,117217)]),(z199,[(1024,170017),(1024,32935)]),(z200,[(1024,32867),(1024,34913)]),(z201,[(1024,509987),(1024,35315)]),(z202,[(1024,182369),(1024,98483)]),(z203,[(96,3),(1024,182369),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16 : b16.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b17 : List (List Nat × List (Nat × Nat)) := [(z204,[(96,3),(1024,444679),(1024,117217)]),(z205,[(1024,444515),(1024,100787)]),(z206,[(96,3),(1024,444515),(1024,100787)]),(z207,[(1024,170017),(1024,32935)]),(z208,[(56,3),(1024,34913),(1024,32867)]),(z209,[(1024,509987),(1024,35315)]),(z210,[]),(z211,[]),(z212,[]),(z213,[]),(z214,[]),(z215,[(1024,280675),(1024,116995)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17 : b17.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b18 : List (List Nat × List (Nat × Nat)) := [(z216,[]),(z217,[]),(z218,[]),(z219,[(1024,444684),(1024,117217)]),(z220,[(1024,182305),(1024,32947)]),(z221,[(1024,182369),(1024,98483)]),(z222,[(1024,182699),(1024,117283)]),(z223,[(1024,182369),(1024,34983)]),(z224,[(96,3),(1024,182369),(1024,116897)]),(z225,[(1024,182369),(1024,116897)]),(z226,[(96,3),(1024,182369),(1024,98483)]),(z227,[(1024,182369),(1024,98483)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k18 : b18.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b19 : List (List Nat × List (Nat × Nat)) := [(z228,[(1024,575587),(1024,100915)]),(z229,[(1024,100915),(1024,116897)]),(z230,[(1024,100915),(1024,116897)]),(z231,[(1024,182305),(1024,117283)]),(z232,[(1024,182369),(1024,98483)]),(z233,[(1024,182401),(1024,131251)]),(z234,[(1024,182699),(1024,444587)]),(z235,[(1024,171571),(1024,182305)]),(z236,[(1024,182369),(1024,116897)]),(z237,[(1024,575587),(1024,100915)]),(z238,[(1024,182369),(1024,116897)]),(z239,[(1024,182369),(1024,98483)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k19 : b19.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b20 : List (List Nat × List (Nat × Nat)) := [(z240,[(1024,575587),(1024,100915)]),(z241,[(1024,182369),(1024,98483)]),(z242,[(1024,510471),(1024,98488)]),(z243,[(1024,170083),(1024,100519)]),(z244,[(1024,575587),(1024,100915)]),(z245,[(1024,575587),(1024,100915)]),(z246,[(1024,542887),(1024,116897)]),(z247,[(1024,542887),(1024,170515)]),(z248,[(1024,116897),(1024,170515)]),(z249,[(1024,170515),(1024,182305)]),(z250,[(1024,170515),(1024,116897)]),(z251,[(1024,170515),(1024,51361)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k20 : b20.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b21 : List (List Nat × List (Nat × Nat)) := [(z252,[(1024,543148),(1024,117217)]),(z253,[(1024,542887),(1024,116897)]),(z254,[(1024,510472),(1024,98488)]),(z255,[(1024,542983),(1024,116897)]),(z256,[(1024,543148),(1024,116897)]),(z257,[(1024,281095),(1024,116897)]),(z258,[(1024,281128),(1024,116897)]),(z259,[(1024,182369),(1024,98483)]),(z260,[(1024,182369),(1024,98483)]),(z261,[(1024,100519),(1024,116897)]),(z262,[(1024,182369),(1024,98483)]),(z263,[(1024,182369),(1024,32935)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21 : b21.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b22 : List (List Nat × List (Nat × Nat)) := [(z264,[(96,3),(128,3),(1024,182369),(1024,98483)]),(z265,[(96,3),(1024,182369),(1024,98483)]),(z266,[(96,3),(1024,182369),(1024,98483)]),(z267,[(72,3),(1024,98483),(1024,116897)]),(z268,[(72,3),(1024,498867),(1024,117217)]),(z269,[(1024,171283),(1024,39073)]),(z270,[(72,3),(1024,171283),(1024,116897)]),(z271,[(1024,98483),(1024,116897)]),(z272,[(1024,171283),(1024,39073)]),(z273,[(1024,171283),(1024,98483)]),(z274,[(72,3),(1024,98483),(1024,100915)]),(z275,[(72,3),(1024,436403),(1024,444587)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22 : b22.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b23 : List (List Nat × List (Nat × Nat)) := [(z276,[(1024,170017),(1024,32935)]),(z277,[(1024,170017),(1024,32935)]),(z278,[(1024,170017),(1024,32935)]),(z279,[(1024,32867),(1024,34913)]),(z280,[(1024,32867),(1024,34913)]),(z281,[(1024,98483),(1024,116897)]),(z282,[(1024,170017),(1024,39073)]),(z283,[(1024,98483),(1024,116897)]),(z284,[(1024,509987),(1024,35315)]),(z285,[(1024,509987),(1024,35315)]),(z286,[(1024,182699),(1024,117283)]),(z287,[(1024,182369),(1024,44193)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k23 : b23.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b24 : List (List Nat × List (Nat × Nat)) := [(z288,[(1024,182369),(1024,98483)]),(z289,[(1024,182401),(1024,131251)]),(z290,[(1024,444587),(1024,174515)]),(z291,[(1024,444587),(1024,174515)]),(z292,[(1024,171571),(1024,182369)]),(z293,[(1024,444587),(1024,174515)]),(z294,[(1024,444587),(1024,174515)]),(z295,[(1024,444587),(1024,170515)]),(z296,[(1024,436403),(1024,182369)]),(z297,[(1024,444679),(1024,117217)]),(z298,[(96,3),(1024,182369),(1024,116897)]),(z299,[(96,3),(1024,280675),(1024,116995)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24 : b24.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b25 : List (List Nat × List (Nat × Nat)) := [(z300,[(96,3),(1024,182369),(1024,116897)]),(z301,[(96,3),(1024,182369),(1024,116897)]),(z302,[(72,3),(1024,98483),(1024,116897)]),(z303,[(1024,116897),(1024,98483)]),(z304,[(96,3),(1024,182763),(1024,117217)]),(z305,[(96,3),(1024,171105),(1024,117217)]),(z306,[(96,3),(1024,117217),(1024,281095)]),(z307,[(96,3),(1024,170081),(1024,117217)]),(z308,[(1024,117217),(1024,444907)]),(z309,[(1024,444935),(1024,100915)]),(z310,[(96,3),(1024,575587),(1024,117217)]),(z311,[(1024,34987),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k25 : b25.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b26 : List (List Nat × List (Nat × Nat)) := [(z312,[(1024,281095),(1024,34987)]),(z313,[(1024,174115),(1024,117217)]),(z314,[(1024,174115),(1024,34987)]),(z315,[(1024,281095),(1024,117217)]),(z316,[(1024,281095),(1024,117217)]),(z317,[(1024,98803),(1024,32935)]),(z318,[(72,3),(1024,98803),(1024,117217)]),(z319,[(72,3),(1024,281095),(1024,117217)]),(z320,[(1024,281095),(1024,32935)]),(z321,[(1024,117217),(1024,98803)]),(z322,[(1024,32935),(1024,117217)]),(z323,[(1024,281095),(1024,32935)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26 : b26.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b27 : List (List Nat × List (Nat × Nat)) := [(z324,[]),(z325,[(176,1)]),(z326,[]),(z327,[(176,1)]),(z328,[(1024,542887),(1024,498867)]),(z329,[(1024,542983),(1024,171288)]),(z330,[(1024,98488),(1024,171288)]),(z331,[(1024,98803),(1024,498867)]),(z332,[(1024,171271),(1024,170081)]),(z333,[(1024,501939),(1024,510049)]),(z334,[(1024,174355),(1024,182369)]),(z335,[(1024,502035),(1024,171105)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k27 : b27.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b28 : List (List Nat × List (Nat × Nat)) := [(z336,[(1024,530707),(1024,39073)]),(z337,[(1024,174343),(1024,170081)]),(z338,[(248,0)]),(z339,[(1024,575751),(1024,502195)]),(z340,[(1024,100915),(1024,502195)]),(z341,[(1024,530707),(1024,39073)]),(z342,[(248,0)]),(z343,[(1024,34987),(1024,39073)]),(z344,[(1024,34987),(1024,39073)]),(z345,[(1024,542983),(1024,174115)]),(z346,[(1024,174115),(1024,170017)]),(z347,[(1024,542983),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k28 : b28.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b29 : List (List Nat × List (Nat × Nat)) := [(z348,[(1024,39073),(1024,170017)]),(z349,[(1024,174515),(1024,182369)]),(z350,[(1024,174515),(1024,116897)]),(z351,[(1024,116897),(1024,163955)]),(z352,[(1024,100915),(1024,116897)]),(z353,[(1024,174515),(1024,182305)]),(z354,[(1024,174515),(1024,116897)]),(z355,[(1024,116897),(1024,163955)]),(z356,[(1024,98803),(1024,32935)]),(z357,[(56,3),(1024,98483),(1024,116897)]),(z358,[(1024,174579),(1024,501939)]),(z359,[(1024,510049),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k29 : b29.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b30 : List (List Nat × List (Nat × Nat)) := [(z360,[(1024,32935),(1024,39073)]),(z361,[(1024,171283),(1024,98483)]),(z362,[(1024,498868),(1024,98803)]),(z363,[(1024,32935),(1024,39073)]),(z364,[(1024,32935),(1024,39073)]),(z365,[(56,1),(72,0),(1024,98803),(1024,131572)]),(z366,[(96,3),(1024,164331),(1024,117217)]),(z367,[(1024,117217),(1024,98803)]),(z368,[(1024,444460),(1024,51628)]),(z369,[(1024,182311),(1024,116897)]),(z370,[(1024,280675),(1024,116995)]),(z371,[(1024,182369),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k30 : b30.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b31 : List (List Nat × List (Nat × Nat)) := [(z372,[(1024,39073),(1024,51719)]),(z373,[(1024,117217),(1024,163875)]),(z374,[(1024,163875),(1024,34977)]),(z375,[(1024,444907),(1024,509985)]),(z376,[(1024,39073),(1024,44551)]),(z377,[(1024,44551),(1024,39073)]),(z378,[(1024,281128),(1024,39073)]),(z379,[(1024,281128),(1024,39073)]),(z380,[(1024,39073),(1024,44551)]),(z381,[(1024,39403),(1024,44551)]),(z382,[(1024,39073),(1024,44551)]),(z383,[(1024,39073),(1024,44551)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k31 : b31.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b32 : List (List Nat × List (Nat × Nat)) := [(z384,[(1024,39073),(1024,44551)]),(z385,[(1024,39073),(1024,44551)]),(z386,[(1024,444907),(1024,164275)]),(z387,[(1024,39073),(1024,32935)]),(z388,[(1024,44551),(1024,39073)]),(z389,[(1024,39073),(1024,32935)]),(z390,[(1024,39073),(1024,44551)]),(z391,[(1024,39073),(1024,117217)]),(z392,[(1024,51361),(1024,182305)]),(z393,[(96,3),(128,3),(1024,51463),(1024,280615)]),(z394,[(1024,182369),(1024,116897)]),(z395,[(96,3),(1024,281095),(1024,116907)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k32 : b32.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b33 : List (List Nat × List (Nat × Nat)) := [(z396,[(1024,530707),(1024,39073)]),(z397,[(1024,51463),(1024,268339)]),(z398,[(72,3),(1024,51361),(1024,182305)]),(z399,[(1024,182369),(1024,98483)]),(z400,[(1024,51361),(1024,182305)]),(z401,[(1024,182369),(1024,98483)]),(z402,[(1024,51361),(1024,182305)]),(z403,[(1024,116897),(1024,163955)]),(z404,[(1024,116897),(1024,163955)]),(z405,[(1024,100915),(1024,116897)]),(z406,[(1024,542887),(1024,182305)]),(z407,[(1024,116897),(1024,163955)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k33 : b33.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b34 : List (List Nat × List (Nat × Nat)) := [(z408,[(1024,116897),(1024,163955)]),(z409,[(1024,98483),(1024,116897)]),(z410,[(1024,51361),(1024,182305)]),(z411,[(1024,51463),(1024,268339)]),(z412,[(1024,51361),(1024,182305)]),(z413,[(1024,52385),(1024,183329)]),(z414,[]),(z415,[(176,1)]),(z416,[(1024,56481),(1024,187425)]),(z417,[(1024,35544),(1024,56481)]),(z418,[(1024,163896),(1024,187425)]),(z419,[(1024,39073),(1024,170017)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k34 : b34.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b35 : List (List Nat × List (Nat × Nat)) := [(z420,[(1024,51681),(1024,187425)]),(z421,[(1024,56481),(1024,187425)]),(z422,[(1024,51361),(1024,182305)]),(z423,[(104,3),(1024,39091),(1024,51367)]),(z424,[(1024,51463),(1024,280615)]),(z425,[(1024,280615),(1024,39187)]),(z426,[(1024,35379),(1024,51361)]),(z427,[(1024,268339),(1024,280615)]),(z428,[(1024,280615),(1024,39187)]),(z429,[(1024,39187),(1024,51361)]),(z430,[(1024,39187),(1024,51463)]),(z431,[(1024,39187),(1024,51463)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k35 : b35.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b36 : List (List Nat × List (Nat × Nat)) := [(z432,[(104,3),(1024,39187),(1024,51361)]),(z433,[(136,3),(1024,575523),(1024,35379)]),(z434,[(1024,35379),(1024,39187)]),(z435,[(1024,39073),(1024,170017)]),(z436,[(1024,39187),(1024,268339)]),(z437,[(1024,542979),(1024,163875)]),(z438,[(1024,163875),(1024,165921)]),(z439,[(1024,281095),(1024,444587)]),(z440,[(248,0)]),(z441,[(1024,51628),(1024,444460)]),(z442,[(1024,444940),(1024,542881)]),(z443,[(1024,280615),(1024,51361)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k36 : b36.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b37 : List (List Nat × List (Nat × Nat)) := [(z444,[(1024,51747),(1024,575523)]),(z445,[(1024,56583),(1024,182311)]),(z446,[(1024,56748),(1024,182785)]),(z447,[(1024,117283),(1024,280609)]),(z448,[(1024,281128),(1024,444460)]),(z449,[(1024,444973),(1024,575523)]),(z450,[(6,3),(1024,51361),(1024,182699),(1024,444460)]),(z451,[(1024,51361),(1024,182305)]),(z452,[(1024,444587),(1024,182305)]),(z453,[(1024,51361),(1024,182305)]),(z454,[(1024,56481),(1024,187425)]),(z455,[(1024,280615),(1024,51361)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k37 : b37.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b38 : List (List Nat × List (Nat × Nat)) := [(z456,[(108,3),(1024,51628),(1024,444460)]),(z457,[(1024,52385),(1024,183329)]),(z458,[(1024,51457),(1024,183329)]),(z459,[(1024,52385),(1024,183329)]),(z460,[(1024,57505),(1024,188449)]),(z461,[(1024,52519),(1024,182311)]),(z462,[(1024,52684),(1024,182369)]),(z463,[(1024,52385),(1024,183329)]),(z464,[(1024,51361),(1024,182305)]),(z465,[(1024,116897),(1024,280609)]),(z466,[(1024,51361),(1024,182305)]),(z467,[(1024,182699),(1024,444460)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k38 : b38.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b39 : List (List Nat × List (Nat × Nat)) := [(z468,[(1024,116897),(1024,182311)]),(z469,[(1024,509985),(1024,542881)]),(z470,[(1024,51361),(1024,182305)]),(z471,[(1024,51628),(1024,444460)]),(z472,[(1024,52385),(1024,100915)]),(z473,[(1024,35380),(1024,52385)]),(z474,[(6,3),(1024,35379),(1024,182305)]),(z475,[(1024,542887),(1024,163955)]),(z476,[(1024,163892),(1024,183329)]),(z477,[(1024,163891),(1024,444587)]),(z478,[(1024,182369),(1024,98483)]),(z479,[(1024,170017),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k39 : b39.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b40 : List (List Nat × List (Nat × Nat)) := [(z480,[(1024,116907),(1024,174195)]),(z481,[(1024,280620),(1024,44307)]),(z482,[(1024,116907),(1024,100915)]),(z483,[(1024,100915),(1024,116907)]),(z484,[(1024,281095),(1024,44307)]),(z485,[(1024,116907),(1024,170017)]),(z486,[(1024,116907),(1024,174195)]),(z487,[(1024,116907),(1024,170017)]),(z488,[(1024,116907),(1024,174195)]),(z489,[(1024,449707),(1024,174195)]),(z490,[(1024,122017),(1024,163960)]),(z491,[(1024,39436),(1024,44551)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k40 : b40.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b41 : List (List Nat × List (Nat × Nat)) := [(z492,[(1024,117283),(1024,163955)]),(z493,[(1024,44307),(1024,116907)]),(z494,[(1024,39073),(1024,163879)]),(z495,[(1024,444940),(1024,164275)]),(z496,[(1024,444940),(1024,164275)]),(z497,[(1024,117283),(1024,163955)]),(z498,[(1024,117283),(1024,163955)]),(z499,[(1024,444587),(1024,174515)]),(z500,[(1024,116897),(1024,163955)]),(z501,[(1024,280673),(1024,98484)]),(z502,[(1024,150689),(1024,163955)]),(z503,[(1024,182369),(1024,98483)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k41 : b41.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b42 : List (List Nat × List (Nat × Nat)) := [(z504,[(1024,182699),(1024,98483)]),(z505,[(1024,56481),(1024,163896)]),(z506,[(128,2),(168,1),(248,0)]),(z507,[(1024,98867),(1024,491955)]),(z508,[(1024,44472),(1024,56481)]),(z509,[(1024,122017),(1024,163960)]),(z510,[(1024,44467),(1024,51361)]),(z511,[(1024,44307),(1024,174195)]),(z512,[(1024,39073),(1024,163879)]),(z513,[(1024,44291),(1024,174179)]),(z514,[(1024,39073),(1024,510049)]),(z515,[(1024,51463),(1024,39187)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k42 : b42.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b43 : List (List Nat × List (Nat × Nat)) := [(z516,[(1024,491955),(1024,98867)]),(z517,[(1024,44500),(1024,52385)]),(z518,[(2,3),(1024,44467),(1024,182305)]),(z519,[(1024,182369),(1024,116897)]),(z520,[(1024,444587),(1024,117283)]),(z521,[(56,3),(72,3),(96,3),(128,3),(168,3),(1024,444460),(1024,51463)]),(z522,[(72,3),(168,3),(1024,444523),(1024,117163)]),(z523,[(1024,117217),(1024,281095)]),(z524,[(1024,281095),(1024,100883)]),(z525,[(1024,116897),(1024,182369)]),(z526,[(72,5),(80,1),(96,4),(104,0),(128,3),(168,3),(1024,98803),(1024,131572)]),(z527,[(128,3),(1024,116999),(1024,280679)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k43 : b43.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b44 : List (List Nat × List (Nat × Nat)) := [(z528,[(56,3),(96,3),(168,3),(1024,117217),(1024,281095)]),(z529,[(56,3),(128,4),(168,3),(1024,281095),(1024,100883)]),(z530,[(72,5),(96,3),(168,3),(1024,510049),(1024,491635)]),(z531,[(72,5),(128,3),(168,3),(1024,100883),(1024,491635)]),(z532,[(72,3),(128,3),(168,3),(1024,510049),(1024,491635)]),(z533,[(96,4),(128,3),(168,3),(1024,100883),(1024,133652)]),(z534,[(1024,444907),(1024,117217)]),(z535,[(1024,268819),(1024,117217)]),(z536,[(1024,182369),(1024,116897)]),(z537,[(56,3),(72,3),(96,3),(1024,117000),(1024,280680)]),(z538,[(56,3),(72,3),(96,3),(128,3),(168,3),(1024,444460),(1024,51463)]),(z539,[(1024,182401),(1024,149665)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k44 : b44.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b45 : List (List Nat × List (Nat × Nat)) := [(z540,[(128,3),(1024,51463),(1024,280615)]),(z541,[(72,3),(128,3),(1024,51463),(1024,117217)]),(z542,[(72,3),(1024,268339),(1024,51463)]),(z543,[(72,3),(1024,280615),(1024,100403)]),(z544,[(1024,182699),(1024,444587)]),(z545,[(72,3),(128,3),(144,3),(184,3),(1024,444513),(1024,117153)]),(z546,[(72,3),(112,3),(128,3),(1024,444515),(1024,100787)]),(z547,[(128,3),(144,3),(216,3)]),(z548,[(1024,170017),(1024,122497)]),(z549,[(1024,678947),(1024,122497)]),(z550,[(128,3),(192,3),(1024,182791),(1024,117217)]),(z551,[(128,3),(1024,444907),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k45 : b45.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b46 : List (List Nat × List (Nat × Nat)) := [(z552,[(96,3),(112,3),(168,3)]),(z553,[(96,3),(112,3),(168,3)]),(z554,[(96,3),(112,3),(168,3)]),(z555,[(96,3),(128,3),(1024,444907),(1024,117283)]),(z556,[(72,3),(1024,35079),(1024,117217)]),(z557,[(112,3),(128,3),(1024,444940),(1024,117217)]),(z558,[(128,3),(1024,444940),(1024,117283)]),(z559,[(128,3),(1024,575587),(1024,117217)]),(z560,[(1024,575587),(1024,100915)]),(z561,[(1024,100915),(1024,117217)]),(z562,[(1024,100915),(1024,117217)]),(z563,[(128,3),(1024,100915),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k46 : b46.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b47 : List (List Nat × List (Nat × Nat)) := [(z564,[(128,3),(1024,444907),(1024,117283)]),(z565,[(128,3),(1024,444907),(1024,117217)]),(z566,[(128,3),(1024,444907),(1024,149985)]),(z567,[(128,3),(1024,444907),(1024,281095)]),(z568,[(96,3),(128,3),(1024,281095),(1024,444907)]),(z569,[(128,3),(1024,269875),(1024,281095)]),(z570,[(128,3),(192,3),(1024,281095),(1024,117217)]),(z571,[(128,3),(192,3),(1024,444907),(1024,117217)]),(z572,[(152,3),(1024,117217),(1024,444907)]),(z573,[(1024,117217),(1024,100915)]),(z574,[(112,3),(128,3),(1024,575587),(1024,117217)]),(z575,[(128,3),(1024,444907),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k47 : b47.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b48 : List (List Nat × List (Nat × Nat)) := [(z576,[(1024,575587),(1024,117217)]),(z577,[(1024,100915),(1024,117217)]),(z578,[(1024,444940),(1024,117283)]),(z579,[(1024,444907),(1024,117217)]),(z580,[(1024,744547),(1024,122497)]),(z581,[(1024,100883),(1024,122497)]),(z582,[(1024,542983),(1024,117217)]),(z583,[(1024,444940),(1024,117217)]),(z584,[(152,3),(1024,575587),(1024,117217)]),(z585,[(1024,575587),(1024,100915)]),(z586,[(1024,100915),(1024,117217)]),(z587,[(1024,100915),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k48 : b48.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b49 : List (List Nat × List (Nat × Nat)) := [(z588,[(1024,542983),(1024,170017)]),(z589,[(1024,542983),(1024,117217)]),(z590,[(1024,542983),(1024,268819)]),(z591,[(1024,542983),(1024,117217)]),(z592,[(1024,268819),(1024,117217)]),(z593,[(72,3),(1024,268819),(1024,170017)]),(z594,[(1024,268819),(1024,117217)]),(z595,[(1024,268819),(1024,117217)]),(z596,[(1024,268819),(1024,281095)]),(z597,[(1024,268819),(1024,117217)]),(z598,[(72,3),(1024,268819),(1024,51681)]),(z599,[(152,3),(1024,543148),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k49 : b49.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b50 : List (List Nat × List (Nat × Nat)) := [(z600,[(1024,117217),(1024,170017)]),(z601,[(72,3),(1024,542983),(1024,117217)]),(z602,[(72,3),(1024,117217),(1024,170017)]),(z603,[(1024,711943),(1024,122371)]),(z604,[(1024,268819),(1024,122371)]),(z605,[(1024,542983),(1024,117217)]),(z606,[(1024,542983),(1024,117217)]),(z607,[(1024,268819),(1024,117217)]),(z608,[(1024,268819),(1024,117217)]),(z609,[(1024,444940),(1024,117217)]),(z610,[(1024,444973),(1024,117217)]),(z611,[(1024,444907),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k50 : b50.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b51 : List (List Nat × List (Nat × Nat)) := [(z612,[(1024,444907),(1024,117217)]),(z613,[(72,3),(1024,281095),(1024,35348)]),(z614,[(1024,100647),(1024,117217)]),(z615,[(1024,100647),(1024,117217)]),(z616,[(1024,268819),(1024,117217)]),(z617,[(1024,268419),(1024,117217)]),(z618,[(1024,100915),(1024,117217)]),(z619,[(1024,268819),(1024,117217)]),(z620,[(1024,268819),(1024,117217)]),(z621,[(1024,100915),(1024,117217)]),(z622,[(1024,100915),(1024,117217)]),(z623,[(1024,100915),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k51 : b51.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b52 : List (List Nat × List (Nat × Nat)) := [(z624,[(1024,268819),(1024,117217)]),(z625,[(128,3),(1024,444907),(1024,509985)]),(z626,[(152,3),(1024,117217),(1024,444907)]),(z627,[(1024,117217),(1024,170515)]),(z628,[(72,3),(1024,170017),(1024,117217)]),(z629,[(72,3),(1024,170017),(1024,117217)]),(z630,[(1024,170017),(1024,122337)]),(z631,[(1024,170017),(1024,122337)]),(z632,[(1024,170017),(1024,117217)]),(z633,[(1024,170017),(1024,117217)]),(z634,[(1024,444907),(1024,117217)]),(z635,[(2,3),(18,3),(57,3),(73,3),(82,3),(1024,117283),(1024,170248),(1024,171271)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k52 : b52.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b53 : List (List Nat × List (Nat × Nat)) := [(z636,[(1024,170017),(1024,117217)]),(z637,[(1024,34945),(1024,100915)]),(z638,[(1024,444907),(1024,117217)]),(z639,[(1024,170017),(1024,32935)]),(z640,[(1024,170017),(1024,117217)]),(z641,[(1024,268819),(1024,117217)]),(z642,[(1024,98599),(1024,117217)]),(z643,[(1024,268417),(1024,117217)]),(z644,[(1024,98803),(1024,117217)]),(z645,[(1024,98803),(1024,117217)]),(z646,[(1024,98803),(1024,117217)]),(z647,[(1024,575587),(1024,98803)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k53 : b53.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b54 : List (List Nat × List (Nat × Nat)) := [(z648,[(2,3),(14,3),(57,3),(73,3),(82,3),(106,3),(1024,117217),(1024,281095),(1024,444907)]),(z649,[(1024,511011),(1024,117217)]),(z650,[(1024,171540),(1024,117217)]),(z651,[(1024,170017),(1024,117217)]),(z652,[(1024,35316),(1024,100915)]),(z653,[(1024,131107),(1024,117217)]),(z654,[(96,3),(128,3),(1024,575587),(1024,117283)]),(z655,[(1024,44513),(1024,281095)]),(z656,[(1024,281095),(1024,35307)]),(z657,[(128,3),(168,3),(1024,444907),(1024,117217)]),(z658,[(1024,268819),(1024,117217)]),(z659,[(1024,575619),(1024,149985)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k54 : b54.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b55 : List (List Nat × List (Nat × Nat)) := [(z660,[(1024,444907),(1024,281095)]),(z661,[(96,3),(1024,281095),(1024,444907)]),(z662,[(1024,444907),(1024,281095)]),(z663,[(96,3),(1024,281095),(1024,100915)]),(z664,[(1024,269875),(1024,281095)]),(z665,[(1024,542983),(1024,268819)]),(z666,[(1024,281095),(1024,170017)]),(z667,[(1024,444907),(1024,281095)]),(z668,[(168,3),(1024,444907),(1024,170017)]),(z669,[(168,3),(1024,268819),(1024,281095)]),(z670,[(1024,444907),(1024,510049)]),(z671,[(1024,444907),(1024,32935)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k55 : b55.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b56 : List (List Nat × List (Nat × Nat)) := [(z672,[(128,3),(1024,281095),(1024,444907)]),(z673,[(128,3),(1024,281095),(1024,32935)]),(z674,[(1024,436723),(1024,281095)]),(z675,[(1024,444907),(1024,502195)]),(z676,[(96,3)]),(z677,[(96,3),(232,1)]),(z678,[]),(z679,[(232,1)]),(z680,[(1024,543148),(1024,170017)]),(z681,[(1024,509987),(1024,502195)]),(z682,[(1024,502195),(1024,510049)]),(z683,[(96,3),(1024,502195),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k56 : b56.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b57 : List (List Nat × List (Nat × Nat)) := [(z684,[(96,3),(1024,502195),(1024,117217)]),(z685,[(72,3),(312,0)]),(z686,[(72,3),(84,3),(1024,542983),(1024,502195)]),(z687,[(96,3),(1024,535987),(1024,117217)]),(z688,[(72,3),(84,3),(1024,100915),(1024,502195)]),(z689,[(1024,569779),(1024,100915)]),(z690,[(1024,438835),(1024,502195)]),(z691,[(96,3),(1024,100915),(1024,117217)]),(z692,[(168,3),(1024,542983),(1024,502195)]),(z693,[(96,3),(168,3),(1024,502195),(1024,281095)]),(z694,[(312,0)]),(z695,[(1024,543148),(1024,170017)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k57 : b57.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b58 : List (List Nat × List (Nat × Nat)) := [(z696,[(1024,535987),(1024,117217)]),(z697,[(1024,542983),(1024,502195)]),(z698,[(1024,502195),(1024,117217)]),(z699,[(128,3),(1024,170017),(1024,268819)]),(z700,[(1024,535987),(1024,117217)]),(z701,[(128,3),(1024,437779),(1024,502195)]),(z702,[(1024,268819),(1024,117217)]),(z703,[(1024,35307),(1024,100915)]),(z704,[(1024,170017),(1024,117217)]),(z705,[(128,3),(1024,444907),(1024,116897)]),(z706,[(72,3),(1024,444907),(1024,39393)]),(z707,[(72,3),(1024,35335),(1024,39393)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k58 : b58.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b59 : List (List Nat × List (Nat × Nat)) := [(z708,[(128,3),(168,3),(1024,444907),(1024,117217)]),(z709,[(1024,268819),(1024,117217)]),(z710,[(1024,444907),(1024,149985)]),(z711,[(1024,281095),(1024,39073)]),(z712,[(1024,281095),(1024,39073)]),(z713,[(1024,281128),(1024,39073)]),(z714,[(1024,281128),(1024,39073)]),(z715,[(1024,269875),(1024,39073)]),(z716,[(1024,542983),(1024,268819)]),(z717,[(1024,39073),(1024,170017)]),(z718,[(1024,281095),(1024,39073)]),(z719,[(1024,281095),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k59 : b59.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b60 : List (List Nat × List (Nat × Nat)) := [(z720,[(1024,268819),(1024,39073)]),(z721,[(1024,444907),(1024,510049)]),(z722,[(1024,32935),(1024,39073)]),(z723,[(128,3),(1024,281095),(1024,39073)]),(z724,[(128,3),(1024,32935),(1024,39073)]),(z725,[(1024,436723),(1024,39073)]),(z726,[(1024,575752),(1024,281095)]),(z727,[(56,3),(128,3),(1024,444907),(1024,510049)]),(z728,[(1024,444907),(1024,39073)]),(z729,[(1024,39073),(1024,502195)]),(z730,[(1024,281095),(1024,39073)]),(z731,[(1024,575587),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k60 : b60.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b61 : List (List Nat × List (Nat × Nat)) := [(z732,[(1024,575587),(1024,117217)]),(z733,[(1024,530707),(1024,39073)]),(z734,[(1024,575587),(1024,117217)]),(z735,[(56,3),(72,3),(128,3),(1024,182369),(1024,116897)]),(z736,[(72,3),(128,3),(1024,575587),(1024,117217)]),(z737,[(1024,182369),(1024,116897)]),(z738,[(128,3),(1024,575587),(1024,117217)]),(z739,[(1024,182369),(1024,116897)]),(z740,[(128,3),(1024,575587),(1024,117217)]),(z741,[(1024,182369),(1024,116897)]),(z742,[(1024,182791),(1024,542887)]),(z743,[(128,3),(1024,281095),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k61 : b61.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b62 : List (List Nat × List (Nat × Nat)) := [(z744,[(128,3),(1024,281095),(1024,117217)]),(z745,[(56,3),(1024,117217),(1024,281095)]),(z746,[(1024,281095),(1024,100915)]),(z747,[(128,3),(1024,100915),(1024,117217)]),(z748,[(128,3),(1024,281095),(1024,509985)]),(z749,[(1024,281095),(1024,117217)]),(z750,[(1024,281095),(1024,117217)]),(z751,[(1024,281095),(1024,117217)]),(z752,[(1024,268819),(1024,117217)]),(z753,[(56,3),(128,3),(1024,510049),(1024,117217)]),(z754,[(56,3),(1024,281095),(1024,32935)]),(z755,[(56,3),(96,3),(1024,281095),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k62 : b62.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b63 : List (List Nat × List (Nat × Nat)) := [(z756,[(56,3),(1024,281095),(1024,32935)]),(z757,[(56,3),(96,3),(1024,98803),(1024,117217)]),(z758,[(1024,281095),(1024,39073)]),(z759,[(1024,182369),(1024,116897)]),(z760,[(1024,444940),(1024,117283)]),(z761,[(72,3),(128,3),(1024,182369),(1024,116897)]),(z762,[(1024,182369),(1024,116897)]),(z763,[(1024,183393),(1024,117921)]),(z764,[]),(z765,[(232,1)]),(z766,[]),(z767,[(232,1)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k63 : b63.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b64 : List (List Nat × List (Nat × Nat)) := [(z768,[(1024,187489),(1024,122017)]),(z769,[(1024,744547),(1024,122017)]),(z770,[(1024,101080),(1024,122017)]),(z771,[(1024,187819),(1024,449707)]),(z772,[(1024,711847),(1024,122017)]),(z773,[(1024,170680),(1024,122017)]),(z774,[(96,3),(1024,98488),(1024,122017)]),(z775,[(1024,171288),(1024,39073)]),(z776,[(1024,171288),(1024,39073)]),(z777,[(1024,170017),(1024,39073)]),(z778,[(1024,170017),(1024,32935)]),(z779,[(1024,32867),(1024,34913)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k64 : b64.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b65 : List (List Nat × List (Nat × Nat)) := [(z780,[(1024,170017),(1024,39073)]),(z781,[(1024,509987),(1024,35315)]),(z782,[(1024,187819),(1024,117217)]),(z783,[(128,3),(1024,182791),(1024,122497)]),(z784,[(1024,187489),(1024,122017)]),(z785,[(1024,182369),(1024,116897)]),(z786,[(1024,530611),(1024,117217)]),(z787,[(1024,281095),(1024,116897)]),(z788,[(1024,281095),(1024,116897)]),(z789,[(1024,575587),(1024,116897)]),(z790,[(1024,281095),(1024,100915)]),(z791,[(1024,100915),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k65 : b65.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b66 : List (List Nat × List (Nat × Nat)) := [(z792,[(1024,281095),(1024,444587)]),(z793,[(1024,281095),(1024,116897)]),(z794,[(1024,542983),(1024,116897)]),(z795,[(1024,281095),(1024,116897)]),(z796,[(1024,268819),(1024,116897)]),(z797,[(1024,281095),(1024,39073)]),(z798,[(1024,281095),(1024,116897)]),(z799,[(1024,530707),(1024,116897)]),(z800,[(1024,530707),(1024,39073)]),(z801,[(1024,530707),(1024,117217)]),(z802,[(1024,530707),(1024,39073)]),(z803,[(1024,444907),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k66 : b66.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b67 : List (List Nat × List (Nat × Nat)) := [(z804,[(1024,530707),(1024,117217)]),(z805,[(1024,530707),(1024,116897)]),(z806,[(312,0)]),(z807,[(1024,575587),(1024,39073)]),(z808,[(1024,530707),(1024,117217)]),(z809,[(1024,510049),(1024,39073)]),(z810,[(1024,564499),(1024,117217)]),(z811,[(1024,39073),(1024,100915)]),(z812,[(1024,564499),(1024,100915)]),(z813,[(1024,269875),(1024,39073)]),(z814,[(1024,100915),(1024,117217)]),(z815,[(1024,542983),(1024,509985)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k67 : b67.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b68 : List (List Nat × List (Nat × Nat)) := [(z816,[(1024,444907),(1024,509985)]),(z817,[(312,0)]),(z818,[(1024,542983),(1024,39073)]),(z819,[(1024,530707),(1024,117217)]),(z820,[(1024,542983),(1024,39073)]),(z821,[(1024,530707),(1024,117217)]),(z822,[(1024,39073),(1024,170017)]),(z823,[(1024,530707),(1024,117217)]),(z824,[(1024,268819),(1024,39073)]),(z825,[(1024,268819),(1024,117217)]),(z826,[(1024,281095),(1024,444587)]),(z827,[(1024,444940),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k68 : b68.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b69 : List (List Nat × List (Nat × Nat)) := [(z828,[(1024,444940),(1024,542887)]),(z829,[(1024,281095),(1024,116897)]),(z830,[(1024,575587),(1024,116897)]),(z831,[(1024,286375),(1024,122017)]),(z832,[(1024,182791),(1024,122017)]),(z833,[(96,3),(1024,116897),(1024,182369)]),(z834,[(96,3),(128,3),(1024,182699),(1024,444587)]),(z835,[(96,3),(1024,117217),(1024,444907)]),(z836,[(96,3),(128,3),(1024,116897),(1024,182369)]),(z837,[(96,3),(1024,187489),(1024,122017)]),(z838,[(1024,281128),(1024,116897)]),(z839,[(96,3),(1024,444973),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k69 : b69.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b70 : List (List Nat × List (Nat × Nat)) := [(z840,[(2,3),(97,3),(1024,116897),(1024,182699),(1024,444587)]),(z841,[(1024,182369),(1024,116897)]),(z842,[(1024,182699),(1024,444587)]),(z843,[(96,3),(1024,444907),(1024,117217)]),(z844,[(1024,182369),(1024,116897)]),(z845,[(1024,187489),(1024,122017)]),(z846,[(1024,281095),(1024,116897)]),(z847,[(148,3),(1024,444940),(1024,116897)]),(z848,[(96,3),(1024,116897),(1024,182369)]),(z849,[(1024,183425),(1024,116897)]),(z850,[(1024,183755),(1024,116993)]),(z851,[(96,3),(1024,511105),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k70 : b70.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b71 : List (List Nat × List (Nat × Nat)) := [(z852,[(1024,183425),(1024,116897)]),(z853,[(1024,188545),(1024,116897)]),(z854,[(1024,182369),(1024,116897)]),(z855,[(1024,182369),(1024,116897)]),(z856,[(96,3),(1024,183425),(1024,116897)]),(z857,[(1024,183425),(1024,116897)]),(z858,[(1024,182369),(1024,116897)]),(z859,[(1024,281095),(1024,116897)]),(z860,[(1024,182369),(1024,116897)]),(z861,[(1024,116897),(1024,182369)]),(z862,[(96,3),(1024,444940),(1024,116897)]),(z863,[(96,3),(1024,281095),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k71 : b71.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b72 : List (List Nat × List (Nat × Nat)) := [(z864,[(1024,510049),(1024,542887)]),(z865,[(1024,182369),(1024,116897)]),(z866,[(1024,510049),(1024,117217)]),(z867,[(96,3),(1024,182699),(1024,444587)]),(z868,[(2,3),(97,3),(1024,116897),(1024,182699),(1024,444587)]),(z869,[(1024,576643),(1024,116897)]),(z870,[(1024,183425),(1024,100915)]),(z871,[(1024,116897),(1024,100915)]),(z872,[(1024,133684),(1024,116897)]),(z873,[(2,3),(97,3),(1024,100915),(1024,182369)]),(z874,[(2,3),(97,3),(1024,182699),(1024,444940),(1024,542887)]),(z875,[(1024,183755),(1024,444587)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k72 : b72.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b73 : List (List Nat × List (Nat × Nat)) := [(z876,[(1024,116897),(1024,182699),(1024,444587)]),(z877,[(1024,543911),(1024,116897)]),(z878,[(1024,183425),(1024,116897)]),(z879,[(1024,150689),(1024,170516)]),(z880,[(1024,170516),(1024,116897)]),(z881,[(1024,170515),(1024,116897)]),(z882,[(1024,182552),(1024,39073)]),(z883,[(1024,32935),(1024,39073)]),(z884,[(1024,564499),(1024,32935)]),(z885,[(96,3),(1024,510049),(1024,39073)]),(z886,[(72,3),(1024,510049),(1024,117217)]),(z887,[(72,3),(1024,131252),(1024,116897)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k73 : b73.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b74 : List (List Nat × List (Nat × Nat)) := [(z888,[(1024,98803),(1024,32935)]),(z889,[(96,3),(1024,32935),(1024,39073)]),(z890,[(1024,98803),(1024,32935)]),(z891,[(2,3),(72,3),(73,3),(1024,98483),(1024,444940)]),(z892,[(1024,98803),(1024,39073)]),(z893,[(72,3),(1024,98803),(1024,117217)]),(z894,[(1024,171283),(1024,39073)]),(z895,[(1024,171283),(1024,98483)]),(z896,[(96,0),(1024,170017),(1024,39073)]),(z897,[(1024,281095),(1024,510049)]),(z898,[(1024,281095),(1024,510049)]),(z899,[(1024,449707),(1024,187489)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k74 : b74.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b75 : List (List Nat × List (Nat × Nat)) := [(z900,[(1024,542983),(1024,281095)]),(z901,[(1024,530707),(1024,510049)]),(z902,[(1024,444907),(1024,502195)]),(z903,[(1024,182699),(1024,444940),(1024,542887)]),(z904,[(1024,478379),(1024,183425)]),(z905,[(128,3),(1024,450187),(1024,122497)]),(z906,[(128,3),(1024,286375),(1024,122497)]),(z907,[(96,3),(128,3),(1024,117217),(1024,444907)]),(z908,[(96,3),(128,3),(1024,281128),(1024,117217)]),(z909,[(96,3),(1024,444907),(1024,117217)]),(z910,[(96,3),(1024,281095),(1024,117217)]),(z911,[(96,3),(1024,478699),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k75 : b75.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b76 : List (List Nat × List (Nat × Nat)) := [(z912,[(96,3),(1024,314887),(1024,117217)]),(z913,[(96,3),(1024,575587),(1024,117217)]),(z914,[(96,3),(1024,575587),(1024,117217)]),(z915,[(1024,444935),(1024,100915)]),(z916,[(1024,281095),(1024,34987)]),(z917,[(1024,174115),(1024,34987)]),(z918,[(1024,281095),(1024,117217)]),(z919,[(1024,131572),(1024,32935)]),(z920,[(1024,281095),(1024,32935)]),(z921,[(1024,281095),(1024,32935)]),(z922,[(1024,187489),(1024,98488)]),(z923,[(1024,542887),(1024,501939)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k76 : b76.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b77 : List (List Nat × List (Nat × Nat)) := [(z924,[(1024,542983),(1024,174360)]),(z925,[(1024,542983),(1024,171105)]),(z926,[(1024,530707),(1024,39073)]),(z927,[(1024,174343),(1024,170081)]),(z928,[(176,2),(224,1),(312,0)]),(z929,[(1024,575751),(1024,502195)]),(z930,[(1024,100915),(1024,502195)]),(z931,[(1024,530707),(1024,39073)]),(z932,[(176,2),(224,1),(312,0)]),(z933,[(1024,34987),(1024,39073)]),(z934,[(1024,34987),(1024,39073)]),(z935,[(1024,542983),(1024,174115)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k77 : b77.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b78 : List (List Nat × List (Nat × Nat)) := [(z936,[(1024,174115),(1024,170017)]),(z937,[(1024,542983),(1024,39073)]),(z938,[(1024,39073),(1024,170017)]),(z939,[(1024,187489),(1024,174520)]),(z940,[(1024,174520),(1024,122017)]),(z941,[(1024,98803),(1024,32935)]),(z942,[(1024,174579),(1024,501939)]),(z943,[(1024,510049),(1024,39073)]),(z944,[(1024,32935),(1024,39073)]),(z945,[(1024,98488),(1024,131257)]),(z946,[(1024,98803),(1024,131572)]),(z947,[(1024,32935),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k78 : b78.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b79 : List (List Nat × List (Nat × Nat)) := [(z948,[(1024,32935),(1024,39073)]),(z949,[(128,3),(1024,286131),(1024,122497)]),(z950,[(1024,281016),(1024,286131)]),(z951,[(1024,530707),(1024,510049)]),(z952,[(1024,444696),(1024,39073)]),(z953,[(1024,502195),(1024,39073)]),(z954,[(1024,281095),(1024,116897)]),(z955,[(1024,510049),(1024,502195)]),(z956,[(1024,39073),(1024,510049)]),(z957,[(1024,502195),(1024,510049)]),(z958,[(1024,39073),(1024,510049)]),(z959,[(1024,502035),(1024,511105)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k79 : b79.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b80 : List (List Nat × List (Nat × Nat)) := [(z960,[(1024,530707),(1024,39073)]),(z961,[(1024,530707),(1024,510049)]),(z962,[(1024,530707),(1024,39073)]),(z963,[(1024,502195),(1024,39073)]),(z964,[(1024,502195),(1024,510049)]),(z965,[(1024,117217),(1024,502195)]),(z966,[(1024,502195),(1024,100915)]),(z967,[(1024,34987),(1024,39073)]),(z968,[(1024,174115),(1024,170017)]),(z969,[(1024,39073),(1024,170017)]),(z970,[(1024,174548),(1024,116897)]),(z971,[(2,3),(73,3),(1024,116897),(1024,174515)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k80 : b80.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b81 : List (List Nat × List (Nat × Nat)) := [(z972,[(1024,131572),(1024,32935)]),(z973,[(1024,39073),(1024,32935)]),(z974,[(1024,32935),(1024,39073)]),(z975,[(1024,39073),(1024,281095)]),(z976,[(1024,39073),(1024,117217)]),(z977,[(144,3),(1024,39073),(1024,281095)]),(z978,[(1024,39073),(1024,117255)]),(z979,[(1024,444907),(1024,39073)]),(z980,[(1024,39073),(1024,52743)]),(z981,[(1024,163875),(1024,34977)]),(z982,[(1024,39073),(1024,44711)]),(z983,[(6,3),(1024,39436),(1024,542983)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k81 : b81.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b82 : List (List Nat × List (Nat × Nat)) := [(z984,[(1024,39073),(1024,44551)]),(z985,[(1024,281128),(1024,39073)]),(z986,[(1024,39073),(1024,44551)]),(z987,[(1024,39073),(1024,32935)]),(z988,[(1024,39073),(1024,122497)]),(z989,[(1024,530707),(1024,39073)]),(z990,[(1024,575587),(1024,117217)]),(z991,[(1024,39073),(1024,163879)]),(z992,[(1024,122017),(1024,187489)]),(z993,[(1024,117283),(1024,281095)]),(z994,[(1024,39073),(1024,510049)]),(z995,[(1024,117217),(1024,491635)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k82 : b82.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b83 : List (List Nat × List (Nat × Nat)) := [(z996,[(6,3),(101,3),(105,3),(1024,116897),(1024,182791),(1024,542887)]),(z997,[(1024,150689),(1024,183425)]),(z998,[(1024,187489),(1024,98488)]),(z999,[(1024,56583),(1024,285735)]),(z1000,[(1024,56583),(1024,39192)]),(z1001,[(1024,39192),(1024,56583)]),(z1002,[(80,1),(1024,39073),(1024,170017)]),(z1003,[(1024,542979),(1024,163875)]),(z1004,[(1024,163875),(1024,165921)]),(z1005,[(176,2),(224,1),(312,0)]),(z1006,[(6,1),(10,3),(105,3),(109,3),(1024,56481),(1024,187819),(1024,449580)]),(z1007,[(1024,57505),(1024,188449)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k83 : b83.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b84 : List (List Nat × List (Nat × Nat)) := [(z1008,[(1024,509985),(1024,542881)]),(z1009,[(1024,39073),(1024,170017)]),(z1010,[(1024,122131),(1024,285811)]),(z1011,[(1024,117016),(1024,122131)]),(z1012,[(1024,39073),(1024,491635)]),(z1013,[(80,3),(1024,575587),(1024,116897)]),(z1014,[(80,3),(1024,281095),(1024,163955)]),(z1015,[(6,3),(1024,51463),(1024,281128),(1024,444460)]),(z1016,[(1024,52519),(1024,280615)]),(z1017,[(104,3),(1024,39073),(1024,510049)]),(z1018,[(1024,39073),(1024,511073)]),(z1019,[(1024,39073),(1024,491635)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k84 : b84.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b85 : List (List Nat × List (Nat × Nat)) := [(z1020,[(1024,39073),(1024,491635)]),(z1021,[(1024,444907),(1024,491635)]),(z1022,[(1024,39220),(1024,52519)]),(z1023,[(6,3),(18,3),(105,3),(1024,39187),(1024,444460)]),(z1024,[(1024,39073),(1024,170017)]),(z1025,[(1024,163875),(1024,165921)]),(z1026,[(6,3),(7,3),(9,3),(75,3),(79,3),(111,3),(115,3)]),(z1027,[(6,3),(18,0),(142,3),(146,3),(1024,52385),(1024,183755),(1024,444460)]),(z1028,[(1024,116897),(1024,280609)]),(z1029,[(1024,122027),(1024,285740)]),(z1030,[(2,3),(10,3),(97,3),(113,3),(145,3),(154,3),(1024,117217),(1024,280620),(1024,510049)]),(z1031,[(1024,150699),(1024,280620)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k85 : b85.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b86 : List (List Nat × List (Nat × Nat)) := [(z1032,[(1024,116907),(1024,100915)]),(z1033,[(1024,116907),(1024,170017)]),(z1034,[(1024,44312),(1024,122027)]),(z1035,[(1024,39073),(1024,510049)]),(z1036,[(1024,44312),(1024,174200)]),(z1037,[(1024,39073),(1024,510049)]),(z1038,[(1024,44291),(1024,174179)]),(z1039,[(1024,39073),(1024,510049)]),(z1040,[(1024,98867),(1024,131636)]),(z1041,[(176,3),(1024,444907),(1024,117217)]),(z1042,[(1024,444907),(1024,117283)]),(z1043,[(128,3),(1024,117217),(1024,281095)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k86 : b86.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b87 : List (List Nat × List (Nat × Nat)) := [(z1044,[(168,0),(1024,281095),(1024,100883)]),(z1045,[(72,5),(96,3),(168,3),(216,3),(1024,510049),(1024,491635)]),(z1046,[(72,5),(128,4),(168,3),(216,3),(1024,100883),(1024,133652)]),(z1047,[(128,3),(1024,444907),(1024,117217)]),(z1048,[(1024,268819),(1024,117217)]),(z1049,[(1024,444907),(1024,149985)]),(z1050,[(1024,444907),(1024,281095)]),(z1051,[(72,3),(96,3),(168,3),(1024,444907),(1024,510049)]),(z1052,[(72,3),(168,3),(1024,575587),(1024,117217)]),(z1053,[(72,3),(144,3),(168,3),(1024,444907),(1024,117217)]),(z1054,[(72,3),(168,3),(1024,575587),(1024,117217)]),(z1055,[(72,3),(168,3),(1024,575587),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k87 : b87.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b88 : List (List Nat × List (Nat × Nat)) := [(z1056,[(96,3),(168,3),(1024,575752),(1024,281095)]),(z1057,[(168,3),(1024,444940),(1024,117283)]),(z1058,[(152,3),(168,3),(1024,444907),(1024,117217)]),(z1059,[(168,3),(1024,445931),(1024,118241)]),(z1060,[(168,3),(1024,450187),(1024,122497)]),(z1061,[(128,3),(144,3),(216,3)]),(z1062,[(128,3),(144,3),(216,3),(296,1)]),(z1063,[(152,3),(168,3),(1024,744547),(1024,122497)]),(z1064,[(152,3),(1024,101080),(1024,122497)]),(z1065,[(168,3),(1024,101080),(1024,122497)]),(z1066,[(96,3),(100,3),(168,3),(1024,450187),(1024,286375)]),(z1067,[(1024,711943),(1024,122497)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k88 : b88.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b89 : List (List Nat × List (Nat × Nat)) := [(z1068,[(1024,711943),(1024,122497)]),(z1069,[(1024,268984),(1024,122497)]),(z1070,[(1024,268984),(1024,122497)]),(z1071,[(72,3),(168,3),(1024,450187),(1024,117217)]),(z1072,[(72,3),(168,3),(1024,444907),(1024,122497)]),(z1073,[(168,3),(1024,444907),(1024,117217)]),(z1074,[(168,3),(1024,444940),(1024,117217)]),(z1075,[(72,3),(168,3),(240,3),(1024,281095),(1024,444907)]),(z1076,[(108,3),(152,3),(168,3),(1024,444940),(1024,117217)]),(z1077,[(72,3),(168,3),(240,3),(1024,575587),(1024,117217)]),(z1078,[(168,3),(240,3),(1024,450220),(1024,122337)]),(z1079,[(128,3),(192,3),(240,3),(1024,444973),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k89 : b89.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b90 : List (List Nat × List (Nat × Nat)) := [(z1080,[(2,3),(14,3),(57,3),(73,3),(82,3),(106,3),(128,3),(129,3),(153,3),(193,3),(202,3),(1024,117217),(1024,281095),(1024,444907)]),(z1081,[(128,3),(192,3),(1024,444907),(1024,117217)]),(z1082,[(72,3),(128,3),(192,3),(1024,444907),(1024,281095)]),(z1083,[(72,3),(128,3),(192,3),(1024,117217),(1024,281095)]),(z1084,[(128,3),(192,3),(1024,450187),(1024,122403)]),(z1085,[(128,3),(240,3),(1024,444940),(1024,117217)]),(z1086,[(128,3),(1024,478699),(1024,117217)]),(z1087,[(96,3),(112,3),(168,3),(384,0)]),(z1088,[(72,3),(128,3),(1024,478699),(1024,281095)]),(z1089,[(72,3),(128,3),(1024,576643),(1024,117217)]),(z1090,[(128,3),(1024,483979),(1024,117377)]),(z1091,[(128,3),(192,3),(1024,444907),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k90 : b90.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b91 : List (List Nat × List (Nat × Nat)) := [(z1092,[(128,3),(192,3),(1024,444973),(1024,117217)]),(z1093,[(128,3),(1024,444907),(1024,117217)]),(z1094,[(128,3),(1024,444907),(1024,117217)]),(z1095,[(128,3),(192,3),(1024,444907),(1024,117217)]),(z1096,[(128,3),(1024,444907),(1024,117217)]),(z1097,[(128,3),(1024,575587),(1024,510049)]),(z1098,[(72,3),(128,3),(1024,575587),(1024,117217)]),(z1099,[(128,3),(1024,444907),(1024,117217)]),(z1100,[(2,3),(14,3),(22,3),(57,3),(73,3),(82,3),(98,3),(110,3),(114,3),(128,3),(129,3),(153,3),(1024,117283),(1024,281095),(1024,444907)]),(z1101,[(128,3),(240,3),(1024,576643),(1024,117217)]),(z1102,[(128,3),(192,3),(1024,100915),(1024,117217)]),(z1103,[(1024,576643),(1024,100915)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k91 : b91.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b92 : List (List Nat × List (Nat × Nat)) := [(z1104,[(1024,100915),(1024,117217)]),(z1105,[(192,3),(1024,100915),(1024,117217)]),(z1106,[(192,3),(1024,133684),(1024,117217)]),(z1107,[(128,3),(1024,133684),(1024,117217)]),(z1108,[(2,3),(14,3),(57,3),(73,3),(82,3),(98,3),(110,3),(114,3),(129,3),(153,3),(193,3),(202,3),(1024,100915),(1024,281095),(1024,117217)]),(z1109,[(2,3),(14,3),(57,3),(73,3),(82,3),(106,3),(128,3),(129,3),(153,3),(1024,100915),(1024,281095)]),(z1110,[(2,3),(14,3),(57,3),(61,3),(73,3),(77,3),(82,3),(97,3),(128,3),(129,3),(169,3),(193,3),(1024,281095),(1024,444907),(1024,509985)]),(z1111,[(128,3),(216,3),(1024,478699),(1024,281095)]),(z1112,[(1024,117217),(1024,100915)]),(z1113,[(1024,100915),(1024,117217)]),(z1114,[(1024,100883),(1024,122497)]),(z1115,[(2,3),(14,3),(57,3),(73,3),(82,3),(1024,170017),(1024,542983)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k92 : b92.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b93 : List (List Nat × List (Nat × Nat)) := [(z1116,[(1024,170017),(1024,117217)]),(z1117,[(192,0),(1024,100915),(1024,117217)]),(z1118,[(2,3),(14,3),(57,3),(73,3),(82,3),(193,3),(1024,117217),(1024,281095),(1024,444907)]),(z1119,[(1024,544039),(1024,117217)]),(z1120,[(1024,268819),(1024,117217)]),(z1121,[(1024,544039),(1024,117217)]),(z1122,[(1024,268819),(1024,117217)]),(z1123,[(72,3),(168,3),(1024,301588),(1024,170017)]),(z1124,[(1024,151009),(1024,268819)]),(z1125,[(1024,576643),(1024,117217)]),(z1126,[(1024,151009),(1024,170017)]),(z1127,[(1024,301588),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k93 : b93.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b94 : List (List Nat × List (Nat × Nat)) := [(z1128,[(2,3),(14,3),(57,3),(73,3),(82,3),(1024,117217),(1024,268819),(1024,170017)]),(z1129,[(2,3),(57,3),(73,3),(82,3),(1024,268819),(1024,117217)]),(z1130,[(1024,117217),(1024,170017)]),(z1131,[(72,3),(1024,281095),(1024,117217)]),(z1132,[(1024,268819),(1024,122371)]),(z1133,[(192,0),(1024,268819),(1024,117217)]),(z1134,[(152,0),(1024,268819),(1024,117217)]),(z1135,[(152,0),(1024,100915),(1024,117217)]),(z1136,[(1024,268819),(1024,117217)]),(z1137,[(1024,100915),(1024,117217)]),(z1138,[(72,3),(1024,170017),(1024,117217)]),(z1139,[(1024,170017),(1024,122337)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k94 : b94.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b95 : List (List Nat × List (Nat × Nat)) := [(z1140,[(192,0),(1024,170017),(1024,117217)]),(z1141,[(152,0),(1024,98803),(1024,117217)]),(z1142,[(1024,170017),(1024,98803)]),(z1143,[(96,3),(1024,450187),(1024,286375)]),(z1144,[(2,3),(10,3),(57,3),(97,3),(169,3),(1024,281095),(1024,444907),(1024,510049)]),(z1145,[(216,3),(1024,478699),(1024,281095)]),(z1146,[(96,3),(1024,281095),(1024,100915)]),(z1147,[(168,4),(216,3),(1024,444907),(1024,170017)]),(z1148,[(128,3),(1024,444907),(1024,32935)]),(z1149,[(72,3),(168,3),(1024,450187),(1024,122497)]),(z1150,[(1024,450187),(1024,502195)]),(z1151,[(1024,502195),(1024,510049)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k95 : b95.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b96 : List (List Nat × List (Nat × Nat)) := [(z1152,[(72,3),(128,3),(1024,122497),(1024,502195)]),(z1153,[(72,3),(1024,666040),(1024,510049)]),(z1154,[(128,3),(1024,666040),(1024,122497)]),(z1155,[(96,3),(232,2),(288,1),(384,0)]),(z1156,[(96,3),(108,3),(1024,542983),(1024,502195)]),(z1157,[(96,3),(108,3),(1024,100915),(1024,502195)]),(z1158,[(1024,438835),(1024,502195)]),(z1159,[(72,5),(216,3),(1024,542983),(1024,502195)]),(z1160,[(232,2),(288,1),(384,0)]),(z1161,[(1024,543148),(1024,170017)]),(z1162,[(1024,542983),(1024,502195)]),(z1163,[(168,3),(1024,170017),(1024,268819)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k96 : b96.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b97 : List (List Nat × List (Nat × Nat)) := [(z1164,[(168,3),(1024,437779),(1024,502195)]),(z1165,[(168,3),(1024,502228),(1024,511105)]),(z1166,[(96,3),(1024,502228),(1024,117217)]),(z1167,[(2,3),(10,3),(57,3),(73,3),(82,3),(85,3),(113,3),(129,3),(145,3),(154,3),(169,3),(178,3),(1024,502195),(1024,542983),(1024,510049)]),(z1168,[(2,3),(10,3),(57,3),(82,3),(96,3),(97,3),(113,3),(145,3),(154,3),(1024,502195),(1024,117217)]),(z1169,[(72,3),(84,3),(1024,502195),(1024,100915)]),(z1170,[(1024,569779),(1024,100915)]),(z1171,[(128,4),(168,3),(1024,502195),(1024,170017)]),(z1172,[(1024,535987),(1024,117217)]),(z1173,[(1024,39073),(1024,286375)]),(z1174,[(2,3),(1024,39073),(1024,281095)]),(z1175,[(1024,314887),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k97 : b97.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b98 : List (List Nat × List (Nat × Nat)) := [(z1176,[(1024,281128),(1024,39073)]),(z1177,[(168,0),(1024,281095),(1024,39073)]),(z1178,[(128,3),(1024,39073),(1024,32935)]),(z1179,[(72,1),(1024,39073),(1024,502195)]),(z1180,[(1024,530707),(1024,39073)]),(z1181,[(168,3),(1024,286375),(1024,122497)]),(z1182,[(2,3),(73,3),(128,3),(129,3),(1024,117217),(1024,281095),(1024,510049)]),(z1183,[(128,3),(1024,314887),(1024,117217)]),(z1184,[(1024,281095),(1024,100915)]),(z1185,[(1024,281095),(1024,117217)]),(z1186,[(56,3),(1024,281095),(1024,32935)]),(z1187,[(168,3),(1024,450187),(1024,122497)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k98 : b98.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b99 : List (List Nat × List (Nat × Nat)) := [(z1188,[(1024,286375),(1024,39073)]),(z1189,[(1024,286375),(1024,122017)]),(z1190,[(1024,530707),(1024,39073)]),(z1191,[(1024,122497),(1024,510049)]),(z1192,[(1024,450187),(1024,39073)]),(z1193,[(1024,694552),(1024,39073)]),(z1194,[(1024,39073),(1024,510049)]),(z1195,[(1024,694552),(1024,122497)]),(z1196,[(232,2),(288,1),(384,0)]),(z1197,[(112,1),(1024,575587),(1024,39073)]),(z1198,[(1024,575587),(1024,39073)]),(z1199,[(112,1),(1024,100915),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k99 : b99.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b100 : List (List Nat × List (Nat × Nat)) := [(z1200,[(1024,269875),(1024,39073)]),(z1201,[(72,1),(1024,542983),(1024,509985)]),(z1202,[(232,2),(288,1),(384,0)]),(z1203,[(112,1),(1024,542983),(1024,39073)]),(z1204,[(1024,542983),(1024,39073)]),(z1205,[(112,1),(1024,39073),(1024,170017)]),(z1206,[(1024,268819),(1024,39073)]),(z1207,[(2,3),(10,1),(129,3),(1024,122017),(1024,187819),(1024,449707)]),(z1208,[(1024,188545),(1024,122017)]),(z1209,[(1024,510049),(1024,542887)]),(z1210,[(1024,32935),(1024,39073)]),(z1211,[(128,3),(1024,510049),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k100 : b100.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b101 : List (List Nat × List (Nat × Nat)) := [(z1212,[(128,3),(1024,32935),(1024,39073)]),(z1213,[(1024,98803),(1024,39073)]),(z1214,[(1024,171288),(1024,39073)]),(z1215,[(128,0),(1024,170017),(1024,39073)]),(z1216,[(1024,116897),(1024,281095),(1024,444587)]),(z1217,[(1024,314887),(1024,116897)]),(z1218,[(184,0),(1024,281095),(1024,100915)]),(z1219,[(184,0),(1024,281095),(1024,116897)]),(z1220,[(1024,530740),(1024,39073)]),(z1221,[(1024,530740),(1024,117217)]),(z1222,[(2,3),(1024,39073),(1024,510379),(1024,530707)]),(z1223,[(97,3),(1024,530707),(1024,117217)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k101 : b101.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b102 : List (List Nat × List (Nat × Nat)) := [(z1224,[(1024,39073),(1024,100915)]),(z1225,[(1024,564499),(1024,100915)]),(z1226,[(128,0),(1024,39073),(1024,170017)]),(z1227,[(1024,530707),(1024,117217)]),(z1228,[(2,3),(97,3),(119,3),(151,3)]),(z1229,[(2,3),(22,0),(97,3),(190,3),(1024,150689),(1024,183755),(1024,444587)]),(z1230,[(1024,281095),(1024,116897)]),(z1231,[(96,3),(1024,39073),(1024,32935)]),(z1232,[(1024,117217),(1024,32935)]),(z1233,[(72,1),(1024,530707),(1024,510049)]),(z1234,[(56,1),(1024,530707),(1024,510049)]),(z1235,[(56,1),(1024,502195),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k102 : b102.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b103 : List (List Nat × List (Nat × Nat)) := [(z1236,[(1024,510049),(1024,502195)]),(z1237,[(1024,39073),(1024,510049)]),(z1238,[(1024,502195),(1024,510049)]),(z1239,[(1024,542983),(1024,39073)]),(z1240,[(1024,502035),(1024,511105)]),(z1241,[(1024,530707),(1024,39073)]),(z1242,[(1024,530707),(1024,39073)]),(z1243,[(1024,502195),(1024,510049)]),(z1244,[(1024,100915),(1024,133684)]),(z1245,[(1024,34987),(1024,39073)]),(z1246,[(1024,174115),(1024,170017)]),(z1247,[(1024,39073),(1024,170017)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k103 : b103.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b104 : List (List Nat × List (Nat × Nat)) := [(z1248,[(1024,131572),(1024,32935)]),(z1249,[(1024,32935),(1024,39073)]),(z1250,[(1024,32935),(1024,39073)]),(z1251,[(72,1),(1024,39073),(1024,510049)]),(z1252,[(56,1),(1024,491635),(1024,39073)]),(z1253,[(144,3),(1024,39073),(1024,510049)]),(z1254,[(1024,39073),(1024,511073)]),(z1255,[(1024,39073),(1024,491635)]),(z1256,[(80,1),(1024,39073),(1024,170017)]),(z1257,[(1024,163875),(1024,165921)]),(z1258,[(2,3),(14,1),(18,3),(57,3),(73,3),(82,3),(97,3),(106,3),(138,3),(168,3),(169,3),(193,3),(197,3),(201,3),(249,3),(258,3),(1024,122497),(1024,286375),(1024,450187)]),(z1259,[(168,3),(1024,483979),(1024,122497)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k104 : b104.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b105 : List (List Nat × List (Nat × Nat)) := [(z1260,[(128,3),(144,3),(216,3),(296,2),(360,1),(464,0)]),(z1261,[(168,3),(1024,575587),(1024,510049)]),(z1262,[(152,3),(1024,101080),(1024,122497)]),(z1263,[(1024,268984),(1024,122497)]),(z1264,[(2,3),(3,3),(5,3),(14,3),(15,3),(17,3),(57,3),(73,3),(82,3),(83,3),(106,3),(111,3),(128,3),(129,3),(131,3),(139,3),(143,3),(147,3),(151,3),(153,3),(179,3),(183,3),(193,3),(202,3),(203,3)]),(z1265,[(2,3),(14,3),(26,0),(57,3),(73,3),(82,3),(106,3),(128,3),(129,3),(153,3),(193,3),(202,3),(226,3),(230,3),(241,3),(250,3),(1024,151009),(1024,281095),(1024,444907)]),(z1266,[(128,3),(1024,444907),(1024,117217)]),(z1267,[(2,3),(14,3),(22,0),(57,3),(73,3),(82,3),(98,3),(110,3),(114,3),(129,3),(153,3),(193,3),(194,0),(202,4),(241,4),(249,0),(250,3),(257,0),(1024,100915),(1024,133684),(1024,117217)]),(z1268,[(2,3),(14,3),(22,0),(57,3),(73,3),(82,3),(170,0),(194,0),(202,0),(241,0),(249,0),(257,0),(1024,170017),(1024,117283),(1024,268819)]),(z1269,[(216,3),(1024,502228),(1024,511105)]),(z1270,[(2,3),(10,1),(14,3),(57,3),(73,3),(74,1),(82,5),(97,3),(106,3),(109,3),(153,3),(169,3),(193,3),(202,3),(217,5),(225,1),(226,3),(233,1),(1024,502195),(1024,542983),(1024,510049)]),(z1271,[(96,3),(108,3),(1024,100915),(1024,133684)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k105 : b105.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b106 : List (List Nat × List (Nat × Nat)) := [(z1272,[(168,4),(216,3),(1024,170017),(1024,268819)]),(z1273,[(1024,530740),(1024,39073)]),(z1274,[(2,3),(10,1),(74,1),(82,1),(113,1),(217,1),(225,1),(233,1),(1024,39073),(1024,510379),(1024,530707)]),(z1275,[(112,1),(1024,39073),(1024,100915)]),(z1276,[(112,1),(168,0),(1024,39073),(1024,170017)]),(z1277,[(128,3),(1024,32935),(1024,39073)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k106 : b106.all (fun a => P_ a.1 a.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_in_order : T_.toList = (((((((b0 ++ (b1 ++ b2)) ++ (b3 ++ (b4 ++ b5))) ++ ((b6 ++ (b7 ++ b8)) ++ ((b9 ++ b10) ++ (b11 ++ b12)))) ++ (((b13 ++ (b14 ++ b15)) ++ (b16 ++ (b17 ++ b18))) ++ ((b19 ++ (b20 ++ b21)) ++ ((b22 ++ b23) ++ (b24 ++ b25))))) ++ ((((b26 ++ (b27 ++ b28)) ++ (b29 ++ (b30 ++ b31))) ++ ((b32 ++ (b33 ++ b34)) ++ ((b35 ++ b36) ++ (b37 ++ b38)))) ++ (((b39 ++ (b40 ++ b41)) ++ ((b42 ++ b43) ++ (b44 ++ b45))) ++ ((b46 ++ (b47 ++ b48)) ++ ((b49 ++ b50) ++ (b51 ++ b52)))))) ++ (((((b53 ++ (b54 ++ b55)) ++ (b56 ++ (b57 ++ b58))) ++ ((b59 ++ (b60 ++ b61)) ++ ((b62 ++ b63) ++ (b64 ++ b65)))) ++ (((b66 ++ (b67 ++ b68)) ++ ((b69 ++ b70) ++ (b71 ++ b72))) ++ ((b73 ++ (b74 ++ b75)) ++ ((b76 ++ b77) ++ (b78 ++ b79))))) ++ ((((b80 ++ (b81 ++ b82)) ++ (b83 ++ (b84 ++ b85))) ++ ((b86 ++ (b87 ++ b88)) ++ ((b89 ++ b90) ++ (b91 ++ b92)))) ++ (((b93 ++ (b94 ++ b95)) ++ ((b96 ++ b97) ++ (b98 ++ b99))) ++ ((b100 ++ (b101 ++ b102)) ++ ((b103 ++ b104) ++ (b105 ++ b106)))))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem table_ok : ∀ x, T_.mem x = true → ∃ h, P_ x h = true := cover _ _ rows_in_order (all_app (all_app (all_app (all_app (all_app (all_app k0 (all_app k1 k2)) (all_app k3 (all_app k4 k5))) (all_app (all_app k6 (all_app k7 k8)) (all_app (all_app k9 k10) (all_app k11 k12)))) (all_app (all_app (all_app k13 (all_app k14 k15)) (all_app k16 (all_app k17 k18))) (all_app (all_app k19 (all_app k20 k21)) (all_app (all_app k22 k23) (all_app k24 k25))))) (all_app (all_app (all_app (all_app k26 (all_app k27 k28)) (all_app k29 (all_app k30 k31))) (all_app (all_app k32 (all_app k33 k34)) (all_app (all_app k35 k36) (all_app k37 k38)))) (all_app (all_app (all_app k39 (all_app k40 k41)) (all_app (all_app k42 k43) (all_app k44 k45))) (all_app (all_app k46 (all_app k47 k48)) (all_app (all_app k49 k50) (all_app k51 k52)))))) (all_app (all_app (all_app (all_app (all_app k53 (all_app k54 k55)) (all_app k56 (all_app k57 k58))) (all_app (all_app k59 (all_app k60 k61)) (all_app (all_app k62 k63) (all_app k64 k65)))) (all_app (all_app (all_app k66 (all_app k67 k68)) (all_app (all_app k69 k70) (all_app k71 k72))) (all_app (all_app k73 (all_app k74 k75)) (all_app (all_app k76 k77) (all_app k78 k79))))) (all_app (all_app (all_app (all_app k80 (all_app k81 k82)) (all_app k83 (all_app k84 k85))) (all_app (all_app k86 (all_app k87 k88)) (all_app (all_app k89 k90) (all_app k91 k92)))) (all_app (all_app (all_app k93 (all_app k94 k95)) (all_app (all_app k96 k97) (all_app k98 k99))) (all_app (all_app k100 (all_app k101 k102)) (all_app (all_app k103 k104) (all_app k105 k106)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C) :=
  signed_rep_lb 7594810 9 1 0 PD_ PM_ XS_ G_ T_ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) table_ok (by decide +kernel)
end PEqualNP.Outside.L_meta_19580_aux

theorem PEqualNP.Outside.L_meta_19580 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19580_aux.result
