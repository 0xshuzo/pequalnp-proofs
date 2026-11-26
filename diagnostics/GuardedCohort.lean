import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19634_aux

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
def urootHint (ws : List Nat) : Nat := (([([31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],407683),([31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],237667),([31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],133519),([31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],301753),([31,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],131407),([31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416],580273),([31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856],705079),([31,992,1015808,1082401,2164802,4329604,8659208,17318416,32505856],699799),([31,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],694519),([992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],655480)] : List (List Nat × Nat)).lookup (isort ws)).getD 0

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

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
        (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ucheck_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || !ucheck m y cap zs (urootHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

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



def Y_ : Nat := 3315386
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,2874855),(2,4076308),(3,3458157),(4,1163217),(5,197135),(6,154848),(7,193431),(8,42028),(9,36849),(10,6687),(11,4328),(12,5523),(13,1838),(14,1648),(15,735),(16,136),(17,163),(18,54),(19,60),(20,25),(21,11),(22,2),(23,2)]
def PM_ : List (Nat × Nat) := [(0,3315386),(2,3315386),(6,3315386),(8,3315386),(11,3315386),(13,3315386),(14,3315386),(16,3315386),(18,3315386),(19,3315386),(22,3315386),(23,3315386),(24,3315386)]
def G_ : List (List Nat) := [[0,1,2,3,4,5,6,7,8,9,15,16,17,18,19,10,11,12,13,14,20,21,22,23,24]]

def hintWords : Array Nat := #[0,32867,32888,32899,32935,32999,34913,34945,34983,34985,35047,39073,39075,39139,39159,39209,39233,39319,44193,44195,44201,44215,44259,44265,44279,44329,44353,44355,44417,44419,44439,46425,46745,46777,56961,57007,57505,57575,57639,98339,98435,98441,98471,98473,98478,98487,98537,98638,98639,98711,100385,100481,100489,100505,100521,100583,100585,100590,100591,100745,100750,100751,100759,104609,104745,109889,109897,115177,122497,131107,131111,131129,131171,131247,131252,131255,131311,131316,131407,131417,131471,131479,131727,133153,133159,133217,133295,133300,133359,133364,133455,133460,133464,133465,133519,133524,133527,137903,154255,155311,163879,163881,163884,163887,163945,163960,165927,165932,170017,170019,170081,170113,170217,170231,170391,170679,170680,170681,172065,172067,172129,172131,172279,172439,175137,175511,178305,180791,187023,188079,189095,229411,229415,229507,231463,231468,231471,231831,235555,235619,235651,235703,236185,236206,236216,236217,237603,237667,237879,240675,242787,243747,243811,243832,243843,243863,244391,248931,248963,252583,295032,297207,301112,301176,301239,301241,301303,301377,301399,301400,301401,301443,301463,301561,301623,301710,301719,301720,301721,301740,301742,301743,301745,301751,301752,301753,303148,303153,303224,303287,303289,303351,303447,303491,303511,303671,303759,303767,303769,303788,303791,303793,303801,306233,306583,308345,309281,309304,309347,309368,309401,309911,309943,309944,318089,318095,318100,318121,318127,319119,319151,319156,327719,327724,327726,327727,333857,335969,338977,339351,342113,342145,350503,350895,351919,352551,393260,395561,399395,399491,401507,401539,404515,404600,404611,406563,406627,406648,406659,407587,407651,407672,407683,415788,415913,415977,416039,416041,416423,416428,559401,579633,579753,579817,579881,580270,580273,655416,655463,655479,655480,655512,655513,655543,655703,661673,661687,661751,661816,661817,661847,663959,666679,666921,666967,667031,668769,669825,670007,675127,678183,678185,678191,678584,679215,680231,690407,690423,690471,690583,694328,694329,694369,694393,694423,694425,694441,694447,694455,694497,694499,694505,694511,694519,694569,694583,694584,694585,694615,694657,694659,694679,694839,696551,696615,699425,699448,699489,699521,699555,699561,699575,699617,699619,699625,699639,699689,699727,699735,699777,699779,699785,699790,699791,699799,699959,701607,701671,701735,702007,702631,702759,702776,703127,704681,704695,704745,704759,704809,704855,704919,705015,705065,705079,707896,710823,710887,710951,710959,710964,711847,711911,711975,711983,712343,712871,712935,712999]

def hdict : Array Nat := #[0,32867,32888,32899,32935,32999,34913,34945,34983,34985,35047,39073,39075,39139,39159,39209,39233,39319,44193,44195,44201,44215,44259,44265,44279,44329,44353,44355,44417,44419,44439,46425,46745,46777,56961,57007,57505,57575,57639,98339,98435,98441,98471,98473,98478,98487,98537,98638,98639,98711,100385,100481,100489,100505,100521,100583,100585,100590,100591,100745,100750,100751,100759,104609,104745,109889,109897,115177,122497,131107,131111,131129,131171,131247,131252,131255,131311,131316,131407,131417,131471,131479,131727,133153,133159,133217,133295,133300,133359,133364,133455,133460,133464,133465,133519,133524,133527,137903,154255,155311,163879,163881,163884,163887,163945,163960,165927,165932,170017,170019,170081,170113,170217,170231,170391,170679,170680,170681,172065,172067,172129,172131,172279,172439,175137,175511,178305,180791,187023,188079,189095,229411,229415,229507,231463,231468,231471,231831,235555,235619,235651,235703,236185,236206,236216,236217,237603,237667,237879,240675,242787,243747,243811,243832,243843,243863,244391,248931,248963,252583,295032,297207,301112,301176,301239,301241,301303,301377,301399,301400,301401,301443,301463,301561,301623,301710,301719,301720,301721,301740,301742,301743,301745,301751,301752,301753,303148,303153,303224,303287,303289,303351,303447,303491,303511,303671,303759,303767,303769,303788,303791,303793,303801,306233,306583,308345,309281,309304,309347,309368,309401,309911,309943,309944,318089,318095,318100,318121,318127,319119,319151,319156,327719,327724,327726,327727,333857,335969,338977,339351,342113,342145,350503,350895,351919,352551,393260,395561,399395,399491,401507,401539,404515,404600,404611,406563,406627,406648,406659,407587,407651,407672,407683,415788,415913,415977,416039,416041,416423,416428,559401,579633,579753,579817,579881,580270,580273,655416,655463,655479,655480,655512,655513,655543,655703,661673,661687,661751,661816,661817,661847,663959,666679,666921,666967,667031,668769,669825,670007,675127,678183,678185,678191,678584,679215,680231,690407,690423,690471,690583,694328,694329,694369,694393,694423,694425,694441,694447,694455,694497,694499,694505,694511,694519,694569,694583,694584,694585,694615,694657,694659,694679,694839,696551,696615,699425,699448,699489,699521,699555,699561,699575,699617,699619,699625,699639,699689,699727,699735,699777,699779,699785,699790,699791,699799,699959,701607,701671,701735,702007,702631,702759,702776,703127,704681,704695,704745,704759,704809,704855,704919,705015,705065,705079,707896,710823,710887,710951,710959,710964,711847,711911,711975,711983,712343,712871,712935,712999]
def hintLimb : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,w => if w = 1 then [] else
    (w%512,hdict[(w/512)%512]?.getD 0) :: hintLimb n (w/262144)
def hh (limbs : List Nat) : List (Nat × Nat) := limbs.flatMap (hintLimb 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def T_ : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [3,5412005,6291999] .lf) [3,5412517,6291487] .lf) [4,31,2164802,32268568] (.nd (.nd .lf [4,31,3213890,33317656] .lf) [4,31,4329604,7374369] .lf)) [4,31,4330116,7373857] (.nd (.nd (.nd .lf [4,31,5412005,6291968] .lf) [4,31,5412517,6291456] .lf) [4,512,5412005,6291487] (.nd .lf [4,543,4329604,7373857] .lf))) [4,543,5412005,6291456] (.nd (.nd (.nd (.nd .lf [4,1049119,2164802,33317656] .lf) [4,1082401,4329604,6291999] .lf) [4,1082401,4330116,6291487] (.nd .lf [4,1082431,2165730,4329604,9436424,33047056] .lf)) [4,1082913,4329604,6291487] (.nd (.nd (.nd .lf [5,31,512,4329604,7373857] .lf) [5,31,512,5412005,6291456] .lf) [5,31,992,10824010,23609872] (.nd .lf [5,31,1049088,2164802,33317656] .lf)))) [5,31,1082401,2164802,33317144] (.nd (.nd (.nd (.nd (.nd .lf [5,31,1082401,2165314,33317656] .lf) [5,31,1082401,2165730,4329604,9436424,33047056] .lf) [5,31,1082401,4329604,6291968] (.nd (.nd .lf [5,31,1082401,4330116,6291456] .lf) [5,31,1082913,2164802,33317656] .lf)) [5,31,1082913,4329604,6291456] (.nd (.nd (.nd .lf [5,31,1556463,2164802,8659208] .lf) [5,31,2164802,8659208,31997968] .lf) [5,31,3179553,4330116,32505856] (.nd .lf [5,31,3180065,4329604,32505856] .lf))) [5,31,3180065,4329604,33047056] (.nd (.nd (.nd (.nd .lf [5,31,3213890,8659208,33047056] .lf) [5,31,3247203,4330116,32539681] .lf) [5,31,3247203,4330468,32810281] (.nd .lf [5,31,3247203,5412517,32505856] .lf)) [5,31,3247203,6494918,32505856] (.nd (.nd (.nd .lf [5,31,3247715,4329604,32540193] .lf) [5,31,3247715,5412517,32505856] .lf) [5,31,3247715,6494406,32505856] (.nd .lf [5,31,3248099,4329604,33080881] .lf))))) [5,31,3248099,5412005,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,31,3248099,10824010,33047056] .lf) [5,31,4330116,25977624,32539681] .lf) [5,31,5412005,6495206,33047056] (.nd (.nd .lf [5,31,5412517,6494406,32505856] .lf) [5,31,5412517,6494918,32505856] .lf)) [5,31,8659208,21107332,32539681] (.nd (.nd (.nd .lf [5,31,9742313,10824010,33047056] .lf) [5,512,1082401,4329604,6291487] .lf) [5,543,1082401,2164802,33317656] (.nd .lf [5,543,1082401,4329604,6291456] .lf))) [5,543,3179553,4329604,32505856] (.nd (.nd (.nd (.nd .lf [5,543,3247203,4329604,32539681] .lf) [5,543,3247203,5412005,32505856] .lf) [5,543,3247203,6494406,32505856] (.nd .lf [5,543,4329604,25977624,32539681] .lf)) [5,543,5412005,6494406,32505856] (.nd (.nd (.nd .lf [5,992,1082431,2164802,4329604,9436424,33047056] .lf) [5,992,1082431,2164802,4329604,17825296,32776456] .lf) [5,992,5412005,6291487,17318416] (.nd .lf [5,992,6291487,10824010,17318416] .lf)))) [5,31744,1082431,2165730,4329604,9412872,33047056] (.nd (.nd (.nd (.nd (.nd .lf [5,1047552,1082431,2165730,4329604,8659208,33047056] .lf) [5,1049119,2164802,8659208,33047056] .lf) [5,1082401,2097183,4330116,32505856] (.nd .lf [5,1082401,2097695,4329604,32505856] .lf)) [5,1082401,2097695,4329604,33047056] (.nd (.nd (.nd .lf [5,1082401,2164802,32505887,32641668] .lf) [5,1082401,2164802,32506399,32641156] .lf) [5,1082401,2164831,4330116,32505887] (.nd .lf [5,1082401,2164831,4330468,32776479] .lf))) [5,1082401,2165343,4329604,32506399] (.nd (.nd (.nd (.nd .lf [5,1082401,2165730,4329631,9436424,17318416,32505856] .lf) [5,1082401,2165759,4329604,33047071] .lf) [5,1082401,3144770,4329631,8659944,17318416,32505856] (.nd .lf [5,1082431,2165730,4329604,9436424,17318416,32505856] .lf)) [5,1082431,3144770,4329604,8659944,17318416,32505856] (.nd (.nd (.nd .lf [5,1082913,2097183,4329604,32505856] .lf) [5,1082913,2164802,32505887,32641156] .lf) [5,1082913,2164831,4329604,32505887] (.nd .lf [5,4329604,8659208,16777759,32539681] .lf)))))) [6,31,512,1082401,2164802,33317656] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,512,1082401,4329604,6291456] .lf) [6,31,512,3179553,4329604,32505856] .lf) [6,31,512,3247203,4329604,32539681] (.nd (.nd .lf [6,31,512,3247203,5412005,32505856] .lf) [6,31,512,3247203,6494406,32505856] .lf)) [6,31,512,4329604,25977624,32539681] (.nd (.nd (.nd .lf [6,31,512,5412005,6494406,32505856] .lf) [6,31,992,1082401,2164802,4329604,9436424,33047056] .lf) [6,31,992,1082401,2164802,4329604,17825296,32776456] (.nd .lf [6,31,992,1082401,3144770,8659208,17318416,32641156] .lf))) [6,31,992,1555951,2164802,8659208] (.nd (.nd (.nd (.nd .lf [6,31,992,1826551,2164802,17318416] .lf) [6,31,992,2164802,8659208,23609872] .lf) [6,31,992,2164802,8659208,31998480] (.nd .lf [6,31,992,2164802,14950664,17318416] .lf)) [6,31,992,2164802,17318416,31727880] (.nd (.nd (.nd .lf [6,31,992,3179553,4329604,33047056] .lf) [6,31,992,3213378,8659208,33047056] .lf) [6,31,992,3213378,17318416,32776456] (.nd .lf [6,31,992,3247203,4329604,32810281] .lf)))) [6,31,992,3247203,4329604,33080881] (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,3247203,5412005,32776456] .lf) [6,31,992,3247203,5412005,33047056] .lf) [6,31,992,3247203,6494406,32776456] (.nd (.nd .lf [6,31,992,3247203,6494406,33047056] .lf) [6,31,992,3247203,8659208,33080881] .lf)) [6,31,992,3247203,9741609,33047056] (.nd (.nd (.nd .lf [6,31,992,3247203,10824010,33047056] .lf) [6,31,992,3247203,17318416,32810281] .lf) [6,31,992,3247203,18400817,32776456] (.nd .lf [6,31,992,3247203,19483218,32776456] .lf))) [6,31,992,4329604,7373857,17318416] (.nd (.nd (.nd (.nd .lf [6,31,992,4329604,9403358,17318416] .lf) [6,31,992,4329604,17318416,24151073] .lf) [6,31,992,4329604,25707024,32539681] (.nd .lf [6,31,992,4329604,25977624,32810281] .lf)) [6,31,992,4329604,25977624,33080881] (.nd (.nd (.nd .lf [6,31,992,5412005,6291456,17318416] .lf) [6,31,992,5412005,6494406,32776456] .lf) [6,31,992,5412005,6494406,33047056] (.nd .lf [6,31,992,6291456,10824010,17318416] .lf))))) [6,31,992,8659208,21648020,33080881] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,9741609,10824010,33047056] .lf) [6,31,992,12718212,17318416,32539681] .lf) [6,31,992,12988812,17318416,32810281] (.nd (.nd .lf [6,31,992,12988812,21648020,32539681] .lf) [6,31,992,12988812,25977624,32539681] .lf)) [6,31,992,18400817,19483218,32776456] (.nd (.nd (.nd .lf [6,31,992,21648020,25977624,32539681] .lf) [6,31,31744,1082401,2165730,4329604,9412872,33047056] .lf) [6,31,507375,1082401,2165730,4329604] (.nd .lf [6,31,507375,1083361,2164802,8659208] .lf))) [6,31,507887,1082401,2164802,8659208] (.nd (.nd (.nd (.nd .lf [6,31,777975,1082401,2164802,4330468] .lf) [6,31,1047552,1082401,2165730,4329604,8659208,33047056] .lf) [6,31,1047552,1082401,2165730,8659208,17318416,32641156] (.nd .lf [6,31,1048575,1082401,2164802,4330116] .lf)) [6,31,1048575,1082913,2164802,4329604] (.nd (.nd (.nd .lf [6,31,1049088,2164802,8659208,33047056] .lf) [6,31,1049568,2164802,8659208,33047056] .lf) [6,31,1082401,2097152,4330116,32505856] (.nd .lf [6,31,1082401,2097664,4329604,32505856] .lf)))) [6,31,1082401,2097664,4329604,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2098144,4329604,33047056] .lf) [6,31,1082401,2164802,4330116,32505856] .lf) [6,31,1082401,2164802,4330116,32505887] (.nd .lf [6,31,1082401,2164802,4330116,32539681] .lf)) [6,31,1082401,2164802,4330116,32776456] (.nd (.nd (.nd .lf [6,31,1082401,2164802,4330148,32505856] .lf) [6,31,1082401,2164802,4330180,32505856] .lf) [6,31,1082401,2164802,4330212,32505856] (.nd .lf [6,31,1082401,2164802,4330468,32506112] .lf))) [6,31,1082401,2164802,4330468,32776456] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2164802,4330468,32776479] .lf) [6,31,1082401,2164802,4330468,32810281] .lf) [6,31,1082401,2164802,5412517,32505856] (.nd .lf [6,31,1082401,2164802,5412837,32776456] .lf)) [6,31,1082401,2164802,6494918,32505856] (.nd (.nd (.nd .lf [6,31,1082401,2164802,6495206,32776456] .lf) [6,31,1082401,2164802,8659208,33046544] .lf) [6,31,1082401,2164802,12989420,32776456] (.nd .lf [6,31,1082401,2164802,16236527,32776456] .lf))))))) [6,31,1082401,2164802,17317904,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2164802,21107332,32505856] .lf) [6,31,1082401,2164802,25977112,32505856] .lf) [6,31,1082401,2164802,29223963,32776456] (.nd (.nd .lf [6,31,1082401,2164802,29224219,32505856] .lf) [6,31,1082401,2164802,29224315,32505856] .lf)) [6,31,1082401,2164802,32505856,32641668] (.nd (.nd (.nd .lf [6,31,1082401,2164802,32506368,32641156] .lf) [6,31,1082401,2164802,32642020,32776456] .lf) [6,31,1082401,2164802,32776456,32912364] (.nd .lf [6,31,1082401,2164831,4330116,32505856] .lf))) [6,31,1082401,2164831,4330468,32776456] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2165058,4330468,32505856] .lf) [6,31,1082401,2165314,4329604,32506368] .lf) [6,31,1082401,2165314,4329604,33047056] (.nd .lf [6,31,1082401,2165314,4330116,32505856] .lf)) [6,31,1082401,2165314,6494406,32505856] (.nd (.nd (.nd .lf [6,31,1082401,2165314,8659208,33047056] .lf) [6,31,1082401,2165314,17318416,32776456] .lf) [6,31,1082401,2165314,25977624,32505856] (.nd .lf [6,31,1082401,2165730,4329604,9436424,17318416,32505856] .lf)))) [6,31,1082401,2165730,4329604,32506368] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,2165730,4329604,33047056] .lf) [6,31,1082401,2165730,4329604,33047071] .lf) [6,31,1082401,2165730,4329604,33080881] (.nd (.nd .lf [6,31,1082401,2165730,4330116,32505856] .lf) [6,31,1082401,2165730,5412005,33047056] .lf)) [6,31,1082401,2165730,10824010,33047056] (.nd (.nd (.nd .lf [6,31,1082401,2165730,21648020,33047056] .lf) [6,31,1082401,2165730,29224827,33047056] .lf) [6,31,1082401,2165730,32641156,33047056] (.nd .lf [6,31,1082401,2165730,33047056,33182356] .lf))) [6,31,1082401,2165759,4329604,33047056] (.nd (.nd (.nd (.nd .lf [6,31,1082401,2194498,4330116,32505856] .lf) [6,31,1082401,3144770,4329604,8659944,17318416,32505856] .lf) [6,31,1082401,3247203,4330116,32505856] (.nd .lf [6,31,1082401,3247203,4330468,32776456] .lf)) [6,31,1082401,3248099,4329604,33047056] (.nd (.nd (.nd .lf [6,31,1082401,4329604,6495206,33047056] .lf) [6,31,1082401,4329604,31388701,33047056] .lf) [6,31,1082401,4330116,6494406,32505856] (.nd .lf [6,31,1082401,4330116,6494918,32505856] .lf))))) [6,31,1082401,4330116,25977624,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082401,4330116,31389629,32505856] .lf) [6,31,1082401,4330468,31389629,32776456] .lf) [6,31,1082401,6495206,10824010,32505856] (.nd (.nd .lf [6,31,1082401,6495206,21648020,32505856] .lf) [6,31,1082401,8659208,21107332,32505856] .lf)) [6,31,1082401,8659944,10824010,33047056] (.nd (.nd (.nd .lf [6,31,1082401,8659944,21648020,33047056] .lf) [6,31,1082401,10824010,12989420,32505856] .lf) [6,31,1082401,12989420,21648020,32505856] (.nd .lf [6,31,1082913,2097152,4329604,32505856] .lf))) [6,31,1082913,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [6,31,1082913,2164802,4329604,32505887] .lf) [6,31,1082913,2164802,4329604,32506368] .lf) [6,31,1082913,2164802,4329604,32539681] (.nd .lf [6,31,1082913,2164802,4329604,32540193] .lf)) [6,31,1082913,2164802,4329604,32776456] (.nd (.nd (.nd .lf [6,31,1082913,2164802,4329604,33047056] .lf) [6,31,1082913,2164802,4330116,32505856] .lf) [6,31,1082913,2164802,5412005,32505856] (.nd .lf [6,31,1082913,2164802,5412517,32505856] .lf)))) [6,31,1082913,2164802,6494406,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1082913,2164802,8659208,33047056] .lf) [6,31,1082913,2164802,17318416,32776456] .lf) [6,31,1082913,2164802,25977624,32505856] (.nd .lf [6,31,1082913,2164802,29224827,32505856] .lf)) [6,31,1082913,2164802,32505856,32641156] (.nd (.nd (.nd .lf [6,31,1082913,2164831,4329604,32505856] .lf) [6,31,1082913,2165314,4329604,32505856] .lf) [6,31,1082913,2165730,4329604,32505856] (.nd .lf [6,31,1082913,2194498,4329604,32505856] .lf))) [6,31,1082913,3247203,4329604,32505856] (.nd (.nd (.nd (.nd .lf [6,31,1082913,3247715,4329604,32505856] .lf) [6,31,1082913,4329604,6494406,32505856] .lf) [6,31,1082913,4329604,25977624,32505856] (.nd .lf [6,31,1082913,4329604,31389629,32505856] .lf)) [6,31,1082977,2164802,4329604,32505856] (.nd (.nd (.nd .lf [6,31,1083041,2164802,4329604,32505856] .lf) [6,31,1083105,2164802,4329604,32505856] .lf) [6,31,1083361,2164802,4329604,33080881] (.nd .lf [6,31,1083361,2164802,4330468,32776456] .lf)))))) [6,31,1083361,2164802,5412005,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,1083361,2164802,5412005,33047056] .lf) [6,31,1083361,2164802,8659208,33047056] .lf) [6,31,1083361,2164802,8659208,33047536] (.nd (.nd .lf [6,31,1083361,2164802,8659208,33080881] .lf) [6,31,1083361,2164802,8659208,33081329] .lf)) [6,31,1083361,2164802,8659208,33317656] (.nd (.nd (.nd .lf [6,31,1083361,2164802,10824010,33047056] .lf) [6,31,1083361,2164802,12988812,32776456] .lf) [6,31,1083361,2164802,17318896,32776456] (.nd .lf [6,31,1083361,2164802,18400817,32776456] .lf))) [6,31,1083361,2164802,24895223,33047056] (.nd (.nd (.nd (.nd .lf [6,31,1083361,2164802,25977624,32776456] .lf) [6,31,1083361,2164802,25977624,33047056] .lf) [6,31,1083361,2164802,32641156,32776456] (.nd .lf [6,31,1083361,2164802,32776456,33047056] .lf)) [6,31,1083361,2164802,33047056,33317656] (.nd (.nd (.nd .lf [6,31,1083361,2165058,4329604,32505856] .lf) [6,31,1083361,6494406,10824010,32505856] .lf) [6,31,1083361,6494406,12988812,32505856] (.nd .lf [6,31,1083361,8659208,10824010,33047056] .lf)))) [6,31,1083361,8659208,31389629,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1083361,10824010,12988812,32505856] .lf) [6,31,1083361,10824010,19483218,32505856] .lf) [6,31,1083361,10824010,25977624,32505856] (.nd (.nd .lf [6,31,1083361,19483218,25977624,32505856] .lf) [6,31,1083391,2164802,8659208,33047056] .lf)) [6,31,2164802,3247203,4330116,32505856] (.nd (.nd (.nd .lf [6,31,2164802,3247203,4330468,32776456] .lf) [6,31,2164802,3247715,4329604,32505856] .lf) [6,31,2164802,3248099,8659208,33047056] (.nd .lf [6,31,2164802,4329604,5412517,32505856] .lf))) [6,31,2164802,4329604,25977112,32505856] (.nd (.nd (.nd (.nd .lf [6,31,2164802,4329604,32471326,32505856] .lf) [6,31,2164802,4329604,32471518,32505856] .lf) [6,31,2164802,4330116,5412005,32505856] (.nd .lf [6,31,2164802,4330116,5412517,32505856] .lf)) [6,31,2164802,4330116,25977624,32505856] (.nd (.nd (.nd .lf [6,31,2164802,4330116,32472030,32505856] .lf) [6,31,2164802,4330468,5412005,32776456] .lf) [6,31,2164802,4330468,5412005,33047056] (.nd .lf [6,31,2164802,4330468,5412837,32776456] .lf))))) [6,31,2164802,4330468,25977624,32776456] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,2164802,4330468,25977624,33047056] .lf) [6,31,2164802,4330468,32472030,32776456] .lf) [6,31,2164802,8659208,9742313,33047056] (.nd (.nd .lf [6,31,2164802,8659208,32471070,33047056] .lf) [6,31,2164802,12989420,17318416,32776456] .lf)) [6,31,2165314,3247203,4329604,32505856] (.nd (.nd (.nd .lf [6,31,2165314,4329604,25977624,32505856] .lf) [6,31,2165730,4329604,5412005,33047056] .lf) [6,31,2165730,4329604,32472030,33047056] (.nd .lf [6,31,2165730,5412005,18400817,32505856] .lf))) [6,31,2165730,5412005,21648020,32505856] (.nd (.nd (.nd (.nd .lf [6,31,2165730,18400817,21648020,32505856] .lf) [6,31,3247203,4330468,8659208,32539681] .lf) [6,31,3247203,4330468,9741609,32505856] (.nd .lf [6,31,3247203,4330468,10824010,32505856] .lf)) [6,31,3248099,4329604,10824010,32505856] (.nd (.nd (.nd .lf [6,31,3248099,4329604,17318416,32539681] .lf) [6,31,3248099,4329604,18400817,32505856] .lf) [6,31,3248099,5412005,17318416,32505856] (.nd .lf [6,31,3248099,10824010,17318416,32505856] .lf)))) [6,31,4329604,8659208,16777728,32539681] (.nd (.nd (.nd (.nd (.nd .lf [6,31,4329604,8659720,17318416,32539681] .lf) [6,31,4329604,9742313,10824010,32505856] .lf) [6,31,4329604,9742313,18400817,32505856] (.nd .lf [6,31,4330116,8659208,17318416,32539681] .lf)) [6,31,4330468,8659208,21648020,32539681] (.nd (.nd (.nd .lf [6,31,4330468,9741609,10824010,32505856] .lf) [6,31,4330468,10824010,19483218,32505856] .lf) [6,31,4330468,10824010,25977624,32505856] (.nd .lf [6,31,4330468,19483218,25977624,32505856] .lf))) [6,31,5412005,6495206,17318416,32505856] (.nd (.nd (.nd (.nd .lf [6,31,5412005,8659944,18400817,32505856] .lf) [6,31,5412005,8659944,21648020,32505856] .lf) [6,31,5412005,9742313,17318416,32505856] (.nd .lf [6,31,5412005,12989420,17318416,32505856] .lf)) [6,31,6495206,10824010,17318416,32505856] (.nd (.nd (.nd .lf [6,31,8659944,18400817,21648020,32505856] .lf) [6,31,9742313,10824010,17318416,32505856] .lf) [6,31,10824010,12989420,17318416,32505856] (.nd .lf [6,287,1082401,2164802,4330468,32505856] .lf)))))))) [6,287,1083361,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,512,1082401,2097183,4329604,32505856] .lf) [6,512,1082401,2164802,32505887,32641156] .lf) [6,512,1082401,2164831,4329604,32505887] (.nd (.nd .lf [6,543,1048575,1082401,2164802,4329604] .lf) [6,543,1082401,2097152,4329604,32505856] .lf)) [6,543,1082401,2164802,4329604,32505856] (.nd (.nd (.nd .lf [6,543,1082401,2164802,4329604,32505887] .lf) [6,543,1082401,2164802,4329604,32506368] .lf) [6,543,1082401,2164802,4329604,32506399] (.nd .lf [6,543,1082401,2164802,4329604,32539681] .lf))) [6,543,1082401,2164802,4329604,32776456] (.nd (.nd (.nd (.nd .lf [6,543,1082401,2164802,4329604,33047056] .lf) [6,543,1082401,2164802,5412005,32505856] .lf) [6,543,1082401,2164802,6494406,32505856] (.nd .lf [6,543,1082401,2164802,8659208,33047056] .lf)) [6,543,1082401,2164802,17318416,32776456] (.nd (.nd (.nd .lf [6,543,1082401,2164802,25977624,32505856] .lf) [6,543,1082401,2164802,29224827,32505856] .lf) [6,543,1082401,2164802,32505856,32641156] (.nd .lf [6,543,1082401,2164831,4329604,32505856] .lf)))) [6,543,1082401,2165314,4329604,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,543,1082401,2165343,4329604,32505856] .lf) [6,543,1082401,2165730,4329604,32505856] .lf) [6,543,1082401,2194498,4329604,32505856] (.nd (.nd .lf [6,543,1082401,3247203,4329604,32505856] .lf) [6,543,1082401,4329604,6494406,32505856] .lf)) [6,543,1082401,4329604,25977624,32505856] (.nd (.nd (.nd .lf [6,543,1082401,4329604,31389629,32505856] .lf) [6,543,2164802,3247203,4329604,32505856] .lf) [6,543,2164802,4329604,5412005,32505856] (.nd .lf [6,543,2164802,4329604,25977624,32505856] .lf))) [6,543,2164802,4329604,32472030,32505856] (.nd (.nd (.nd (.nd .lf [6,543,4329604,8659208,17318416,32539681] .lf) [6,992,31744,1082431,2164802,4329604,9412872,33047056] .lf) [6,992,31744,1082431,2164802,4329604,17809936,32776456] (.nd .lf [6,992,1047552,1082431,2164802,4329604,8659208,33047056] .lf)) [6,992,1047552,1082431,2164802,4329604,17318416,32776456] (.nd (.nd (.nd .lf [6,992,1048607,2164802,8659208,33047056] .lf) [6,992,1048607,2164802,17318416,32776456] .lf) [6,992,1082401,2097183,4329604,33047056] (.nd .lf [6,992,1082401,2164802,4329631,8659208,17825296,32505856] .lf))))) [6,992,1082401,2164802,4329631,8682760,17809936,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,992,1082401,2164802,4329631,9436424,17318416,32505856] .lf) [6,992,1082401,2164831,4329604,32776479] .lf) [6,992,1082401,2164831,4329604,33047071] (.nd (.nd .lf [6,992,1082401,2194498,4329631,8659208,17809936,32505856] .lf) [6,992,1082401,2194498,4329631,9412872,17318416,32505856] .lf)) [6,992,1082401,3144770,4329631,8659208,17318416,32505856] (.nd (.nd (.nd .lf [6,992,1082401,4329604,6291487,17318416] .lf) [6,992,1082431,2164802,4329604,8659208,17825296,32505856] .lf) [6,992,1082431,2164802,4329604,8682760,17809936,32505856] (.nd .lf [6,992,1082431,2164802,4329604,9436424,17318416,32505856] .lf))) [6,992,1082431,2194498,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [6,992,1082431,2194498,4329604,9412872,17318416,32505856] .lf) [6,992,1082431,3144770,4329604,8659208,17318416,32505856] .lf) [6,992,2164802,6291487,8659208,17318416] (.nd .lf [6,992,4329604,8388639,17318416,32539681] .lf)) [6,992,4329604,8659231,17318431,32539681] (.nd (.nd (.nd .lf [6,1023,1082401,2164802,4329604,33047071] .lf) [6,1023,1082401,2164802,8659208,33047536] .lf) [6,1023,1082401,2164802,17318896,32776456] (.nd .lf [6,1023,4329604,8659208,17318431,32539681] .lf)))) [6,31744,1015808,1082431,2165730,4329604,8659208,33047056] (.nd (.nd (.nd (.nd (.nd .lf [6,31744,1082401,2165730,4329631,9412872,17318416,32505856] .lf) [6,31744,1082401,3115074,4329631,8659944,17318416,32505856] .lf) [6,31744,1082431,2165730,4329604,9412872,17318416,32505856] (.nd .lf [6,31744,1082431,3115074,4329604,8659944,17318416,32505856] .lf)) [6,1047552,1082401,2164802,4329631,8659944,17318416,32505856] (.nd (.nd (.nd .lf [6,1047552,1082401,2165730,4329631,8659208,17318416,32505856] .lf) [6,1047552,1082431,2164802,4329604,8659944,17318416,32505856] .lf) [6,1047552,1082431,2165730,4329604,8659208,17318416,32505856] (.nd .lf [6,1047552,1083361,2164831,4329604,8659208] .lf))) [6,1047552,4329604,8659208,17318431,32539681] (.nd (.nd (.nd (.nd .lf [6,1047552,4329604,8659208,17318896,32573506] .lf) [6,1082401,2164802,4329604,16777759,32505856] .lf) [6,1082401,2164802,4329604,32505856,32506399] (.nd .lf [6,1082401,2164802,4329604,32505856,33553888] .lf)) [6,1082401,2164802,4329604,32505887,32506368] (.nd (.nd (.nd .lf [6,1082401,2164802,4330116,32505856,32505887] .lf) [6,1082401,2164802,4330116,32505856,33554400] .lf) [6,1082401,2164802,4330468,32776456,33554400] (.nd .lf [6,1082401,2164802,8659208,32505887,32642020] .lf)))))) [6,1082401,2164831,4330468,8659208,32505887] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,1082401,2164831,4330468,8659231,32505856] .lf) [6,1082401,2165730,4329604,33047056,33554400] .lf) [6,1082401,2165730,17318416,32505887,32641156] (.nd (.nd .lf [6,1082401,2165759,4329604,17318416,32505887] .lf) [6,1082401,2165759,4329604,17318431,32505856] .lf)) [6,1082401,4329604,8659208,16777759,32505856] (.nd (.nd (.nd .lf [6,1082401,4329604,8659967,17318431,32505856] .lf) [6,1082913,2164802,4329604,32505856,32505887] .lf) [6,1082913,2164802,4329604,32505856,33554400] (.nd .lf [6,1083361,2164802,8659208,32505887,32641156] .lf))) [6,1083361,2164802,8659208,33047056,33554400] (.nd (.nd (.nd (.nd .lf [6,1083361,2164831,4329604,8659208,32505887] .lf) [6,1083361,2164831,4329604,8659231,32505856] .lf) [6,2164802,4330495,8659208,17318416,32505887] (.nd .lf [6,4330468,8659208,17318416,32505887,32573506] .lf)) [7,31,256,1082401,2164802,4330468,32505856] (.nd (.nd (.nd .lf [7,31,256,1083361,2164802,4329604,32505856] .lf) [7,31,512,1048575,1082401,2164802,4329604] .lf) [7,31,512,1082401,2097152,4329604,32505856] (.nd .lf [7,31,512,1082401,2164802,4329604,32505856] .lf)))) [7,31,512,1082401,2164802,4329604,32505887] (.nd (.nd (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,4329604,32506368] .lf) [7,31,512,1082401,2164802,4329604,32539681] .lf) [7,31,512,1082401,2164802,4329604,32776456] (.nd (.nd .lf [7,31,512,1082401,2164802,4329604,33047056] .lf) [7,31,512,1082401,2164802,4330116,32505856] .lf)) [7,31,512,1082401,2164802,5412005,32505856] (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,6494406,32505856] .lf) [7,31,512,1082401,2164802,8659208,33047056] .lf) [7,31,512,1082401,2164802,17318416,32776456] (.nd .lf [7,31,512,1082401,2164802,25977624,32505856] .lf))) [7,31,512,1082401,2164802,29224827,32505856] (.nd (.nd (.nd (.nd .lf [7,31,512,1082401,2164802,32505856,32641156] .lf) [7,31,512,1082401,2164831,4329604,32505856] .lf) [7,31,512,1082401,2165314,4329604,32505856] (.nd .lf [7,31,512,1082401,2165730,4329604,32505856] .lf)) [7,31,512,1082401,2194498,4329604,32505856] (.nd (.nd (.nd .lf [7,31,512,1082401,3247203,4329604,32505856] .lf) [7,31,512,1082401,4329604,6494406,32505856] .lf) [7,31,512,1082401,4329604,25977624,32505856] (.nd .lf [7,31,512,1082401,4329604,31389629,32505856] .lf))))) [7,31,512,1082913,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,512,2164802,3247203,4329604,32505856] .lf) [7,31,512,2164802,4329604,5412005,32505856] .lf) [7,31,512,2164802,4329604,25977624,32505856] (.nd (.nd .lf [7,31,512,2164802,4329604,32472030,32505856] .lf) [7,31,512,4329604,8659208,17318416,32539681] .lf)) [7,31,528,1082401,2164802,4329604,32505856] (.nd (.nd (.nd .lf [7,31,543,1082401,2164802,4329604,32505856] .lf) [7,31,544,1082401,2164802,4329604,32505856] .lf) [7,31,576,1082401,2164802,4329604,32505856] (.nd .lf [7,31,640,1082401,2164802,4329604,32505856] .lf))) [7,31,736,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,31744,1082401,2164802,4329604,9412872,33047056] .lf) [7,31,992,31744,1082401,2164802,4329604,17809936,32776456] .lf) [7,31,992,31744,1082401,3115074,8659208,17318416,32641156] (.nd .lf [7,31,992,507375,1082401,2164802,4329604] .lf)) [7,31,992,507375,1082401,2164802,8659208] (.nd (.nd (.nd .lf [7,31,992,777975,1082401,2164802,4329604] .lf) [7,31,992,777975,1082401,2164802,17318416] .lf) [7,31,992,1014750,4329604,8659208,17318416] (.nd .lf [7,31,992,1047552,1082401,2164802,4329604,8659208,33047056] .lf)))) [7,31,992,1047552,1082401,2164802,4329604,17318416,32776456] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1047552,1082401,2164802,8659208,17318416,32641156] .lf) [7,31,992,1048576,2164802,8659208,33047056] .lf) [7,31,992,1048576,2164802,17318416,32776456] (.nd .lf [7,31,992,1082401,2097152,4329604,33047056] .lf)) [7,31,992,1082401,2164802,4329604,8659208,17825296,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,8682760,17809936,32505856] .lf) [7,31,992,1082401,2164802,4329604,9436424] .lf) [7,31,992,1082401,2164802,4329604,9436424,17318416,32505856] (.nd .lf [7,31,992,1082401,2164802,4329604,17825296] .lf))) [7,31,992,1082401,2164802,4329604,32506112] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,32506368] .lf) [7,31,992,1082401,2164802,4329604,32776456] .lf) [7,31,992,1082401,2164802,4329604,32776479] (.nd .lf [7,31,992,1082401,2164802,4329604,32810281] .lf)) [7,31,992,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,33047071] .lf) [7,31,992,1082401,2164802,4329604,33080881] .lf) [7,31,992,1082401,2164802,4330116,32505856] (.nd .lf [7,31,992,1082401,2164802,4330468,32776456] .lf))))))) [7,31,992,1082401,2164802,5412005,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,5412005,33047056] .lf) [7,31,992,1082401,2164802,6494406,32776456] .lf) [7,31,992,1082401,2164802,6494406,33047056] (.nd (.nd .lf [7,31,992,1082401,2164802,8659208,33047056] .lf) [7,31,992,1082401,2164802,8659208,33047536] .lf)) [7,31,992,1082401,2164802,8659208,33080881] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,8659208,33317656] .lf) [7,31,992,1082401,2164802,9741609,33047056] .lf) [7,31,992,1082401,2164802,10824010,33047056] (.nd .lf [7,31,992,1082401,2164802,12988812,32776456] .lf))) [7,31,992,1082401,2164802,16236015,32776456] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,17318416,32776456] .lf) [7,31,992,1082401,2164802,17318416,32810281] .lf) [7,31,992,1082401,2164802,17318416,33317656] (.nd .lf [7,31,992,1082401,2164802,17318896,32776456] .lf)) [7,31,992,1082401,2164802,18400817,32776456] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,19483218,32776456] .lf) [7,31,992,1082401,2164802,21648020,33047056] .lf) [7,31,992,1082401,2164802,24895223,33047056] (.nd .lf [7,31,992,1082401,2164802,25977624,32776456] .lf)))) [7,31,992,1082401,2164802,25977624,33047056] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,29224827,32776456] .lf) [7,31,992,1082401,2164802,29224827,33047056] .lf) [7,31,992,1082401,2164802,32641156,32776456] (.nd (.nd .lf [7,31,992,1082401,2164802,32641156,33047056] .lf) [7,31,992,1082401,2164802,32776456,32911756] .lf)) [7,31,992,1082401,2164802,32776456,33047056] (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,32776456,33317656] .lf) [7,31,992,1082401,2164802,33047056,33182356] .lf) [7,31,992,1082401,2164802,33047056,33317656] (.nd .lf [7,31,992,1082401,2164831,4329604,32776456] .lf))) [7,31,992,1082401,2164831,4329604,33047056] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2165058,4329604,32505856] .lf) [7,31,992,1082401,2165730,4329604,33047056] .lf) [7,31,992,1082401,2194498,4329604,8659208,17809936,32505856] (.nd .lf [7,31,992,1082401,2194498,4329604,9412872,17318416,32505856] .lf)) [7,31,992,1082401,3144770,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,3247203,4329604,32776456] .lf) [7,31,992,1082401,3247203,4329604,33047056] .lf) [7,31,992,1082401,3247203,8659208,33047056] (.nd .lf [7,31,992,1082401,3247203,17318416,32776456] .lf))))) [7,31,992,1082401,4329604,6291456,17318416] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,6494406,32776456] .lf) [7,31,992,1082401,4329604,6494406,33047056] .lf) [7,31,992,1082401,4329604,8659208,17825296] (.nd (.nd .lf [7,31,992,1082401,4329604,8682760,17809936] .lf) [7,31,992,1082401,4329604,9436424,17318416] .lf)) [7,31,992,1082401,4329604,9437183,17318416] (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,17318416,24117248] .lf) [7,31,992,1082401,4329604,25707024,32505856] .lf) [7,31,992,1082401,4329604,25977624,32776456] (.nd .lf [7,31,992,1082401,4329604,25977624,33047056] .lf))) [7,31,992,1082401,4329604,31389629,32776456] (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,4329604,31389629,33047056] .lf) [7,31,992,1082401,6494406,10824010,32505856] .lf) [7,31,992,1082401,6494406,12988812,32505856] (.nd .lf [7,31,992,1082401,6494406,19483218,32505856] .lf)) [7,31,992,1082401,6494406,21648020,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,8659208,10824010,33047056] .lf) [7,31,992,1082401,8659208,21648020,33047056] .lf) [7,31,992,1082401,8659208,31389629,33047056] (.nd .lf [7,31,992,1082401,10824010,12988812,32505856] .lf)))) [7,31,992,1082401,10824010,19483218,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,10824010,25977624,32505856] .lf) [7,31,992,1082401,12718212,17318416,32505856] .lf) [7,31,992,1082401,12988812,17318416,32776456] (.nd .lf [7,31,992,1082401,12988812,21648020,32505856] .lf)) [7,31,992,1082401,12988812,25977624,32505856] (.nd (.nd (.nd .lf [7,31,992,1082401,17318416,19483218,32776456] .lf) [7,31,992,1082401,17318416,31389629,32776456] .lf) [7,31,992,1082401,19483218,21648020,32505856] (.nd .lf [7,31,992,1082401,19483218,25977624,32505856] .lf))) [7,31,992,1082401,21648020,25977624,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,1082431,2164802,8659208,33047056] .lf) [7,31,992,1082431,2164802,17318416,32776456] .lf) [7,31,992,1082913,2164802,4329604,32505856] (.nd .lf [7,31,992,1083361,2164802,4329604,32776456] .lf)) [7,31,992,1083361,2164802,8659208,33047056] (.nd (.nd (.nd .lf [7,31,992,1083361,2164802,17318416,32776456] .lf) [7,31,992,2096161,2164802,8659208,17318416] .lf) [7,31,992,2097151,2164802,8659208,17318416] (.nd .lf [7,31,992,2164802,3247203,4329604,32776456] .lf)))))) [7,31,992,2164802,3247203,4329604,33047056] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,3247203,8659208,33047056] .lf) [7,31,992,2164802,3247203,17318416,32776456] .lf) [7,31,992,2164802,4329604,5412005,32776456] (.nd (.nd .lf [7,31,992,2164802,4329604,5412005,33047056] .lf) [7,31,992,2164802,4329604,25977624,32776456] .lf)) [7,31,992,2164802,4329604,25977624,33047056] (.nd (.nd (.nd .lf [7,31,992,2164802,4329604,32472030,32776456] .lf) [7,31,992,2164802,4329604,32472030,33047056] .lf) [7,31,992,2164802,5412005,9741609,32505856] (.nd .lf [7,31,992,2164802,5412005,12988812,32505856] .lf))) [7,31,992,2164802,5412005,18400817,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,5412005,21648020,32505856] .lf) [7,31,992,2164802,6291456,8659208,17318416] .lf) [7,31,992,2164802,8659208,9741609,33047056] (.nd .lf [7,31,992,2164802,8659208,17318416,31457280] .lf)) [7,31,992,2164802,8659208,21512720,32505856] (.nd (.nd (.nd .lf [7,31,992,2164802,8659208,21648020,33047056] .lf) [7,31,992,2164802,8659208,32472030,33047056] .lf) [7,31,992,2164802,9741609,12988812,32505856] (.nd .lf [7,31,992,2164802,9741609,18400817,32505856] .lf)))) [7,31,992,2164802,9741609,25977624,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,12853512,17318416,32505856] .lf) [7,31,992,2164802,12988812,17318416,32776456] .lf) [7,31,992,2164802,12988812,21648020,32505856] (.nd (.nd .lf [7,31,992,2164802,12988812,25977624,32505856] .lf) [7,31,992,2164802,17318416,18400817,32776456] .lf)) [7,31,992,2164802,17318416,32472030,32776456] (.nd (.nd (.nd .lf [7,31,992,2164802,18400817,21648020,32505856] .lf) [7,31,992,2164802,18400817,25977624,32505856] .lf) [7,31,992,2164802,21648020,25977624,32505856] (.nd .lf [7,31,992,3179553,4329604,17318416,32505856] .lf))) [7,31,992,3213378,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,3247203,4329604,8659208,32539681] .lf) [7,31,992,3247203,4329604,9741609,32505856] .lf) [7,31,992,3247203,4329604,10824010,32505856] (.nd .lf [7,31,992,3247203,4329604,17318416,32539681] .lf)) [7,31,992,3247203,4329604,18400817,32505856] (.nd (.nd (.nd .lf [7,31,992,3247203,4329604,19483218,32505856] .lf) [7,31,992,3247203,5412005,8659208,32505856] .lf) [7,31,992,3247203,5412005,17318416,32505856] (.nd .lf [7,31,992,3247203,6494406,8659208,32505856] .lf))))) [7,31,992,3247203,6494406,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,3247203,8659208,17318416,32539681] .lf) [7,31,992,3247203,8659208,18400817,32505856] .lf) [7,31,992,3247203,8659208,19483218,32505856] (.nd (.nd .lf [7,31,992,3247203,9741609,17318416,32505856] .lf) [7,31,992,3247203,10824010,17318416,32505856] .lf)) [7,31,992,4329604,8388608,17318416,32539681] (.nd (.nd (.nd .lf [7,31,992,4329604,8659208,16236015,32539681] .lf) [7,31,992,4329604,8659208,17318416,32539681] .lf) [7,31,992,4329604,8659208,17318416,32810281] (.nd .lf [7,31,992,4329604,8659208,17318416,33080881] .lf))) [7,31,992,4329604,8659208,17318431,32539681] (.nd (.nd (.nd (.nd .lf [7,31,992,4329604,8659208,21648020,32539681] .lf) [7,31,992,4329604,8659208,25977624,32539681] .lf) [7,31,992,4329604,8659231,17318416,32539681] (.nd .lf [7,31,992,4329604,8659944,17318416,32539681] .lf)) [7,31,992,4329604,9741609,10824010,32505856] (.nd (.nd (.nd .lf [7,31,992,4329604,9741609,18400817,32505856] .lf) [7,31,992,4329604,9741609,25977624,32505856] .lf) [7,31,992,4329604,10824010,19483218,32505856] (.nd .lf [7,31,992,4329604,10824010,25977624,32505856] .lf)))) [7,31,992,4329604,12988812,17318416,32539681] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,4329604,17318416,24895223,32539681] .lf) [7,31,992,4329604,17318416,25977624,32539681] .lf) [7,31,992,4329604,18400817,19483218,32505856] (.nd .lf [7,31,992,4329604,18400817,25977624,32505856] .lf)) [7,31,992,4329604,19483218,25977624,32505856] (.nd (.nd (.nd .lf [7,31,992,5412005,6494406,8659208,32505856] .lf) [7,31,992,5412005,6494406,17318416,32505856] .lf) [7,31,992,5412005,8659208,18400817,32505856] (.nd .lf [7,31,992,5412005,8659208,21648020,32505856] .lf))) [7,31,992,5412005,9741609,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,5412005,12988812,17318416,32505856] .lf) [7,31,992,6494406,8659208,19483218,32505856] .lf) [7,31,992,6494406,8659208,21648020,32505856] (.nd .lf [7,31,992,6494406,10824010,17318416,32505856] .lf)) [7,31,992,6494406,12988812,17318416,32505856] (.nd (.nd (.nd .lf [7,31,992,8659208,12988812,17318416,32539681] .lf) [7,31,992,8659208,17318416,21648020,32539681] .lf) [7,31,992,8659208,17318416,29224827,32539681] (.nd .lf [7,31,992,8659208,18400817,19483218,32505856] .lf))))))))) [7,31,992,8659208,18400817,21648020,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,8659208,19483218,21648020,32505856] .lf) [7,31,992,9741609,10824010,17318416,32505856] .lf) [7,31,992,9741609,12988812,17318416,32505856] (.nd (.nd .lf [7,31,992,10824010,12988812,17318416,32505856] .lf) [7,31,1023,1082401,2164802,4329604,32776456] .lf)) [7,31,1023,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [7,31,1023,1082401,2164802,8659208,33047056] .lf) [7,31,1023,1082401,2164802,17318416,32776456] .lf) [7,31,1023,4329604,8659208,17318416,32539681] (.nd .lf [7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056] .lf))) [7,31,31744,1015808,1082401,2165730,8659208,17318416,32641156] (.nd (.nd (.nd (.nd .lf [7,31,31744,1082401,2164802,4330116,32505856] .lf) [7,31,31744,1082401,2164802,4330468,32776456] .lf) [7,31,31744,1082401,2165730,4329604,9412872,17318416,32505856] (.nd .lf [7,31,31744,1082401,2165730,4329604,33047056] .lf)) [7,31,31744,1082401,3115074,4329604,8659944,17318416,32505856] (.nd (.nd (.nd .lf [7,31,31744,1082913,2164802,4329604,32505856] .lf) [7,31,31744,1083361,2164802,8659208,33047056] .lf) [7,31,1047552,1082401,2164802,4329604,8659944,17318416,32505856] (.nd .lf [7,31,1047552,1082401,2164802,4329604,32776456] .lf)))) [7,31,1047552,1082401,2164802,17318416,32776456] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1047552,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [7,31,1047552,1082401,4329604,8659944,17318416] .lf) [7,31,1047552,1083361,2164802,4329604,8659208] (.nd (.nd .lf [7,31,1047552,1083361,2164802,8659208,17318416] .lf) [7,31,1047552,4329604,8659208,17318416,32539681] .lf)) [7,31,1048575,1082401,2164802,4330468,8659208] (.nd (.nd (.nd .lf [7,31,1048575,1082401,2165730,4329604,17318416] .lf) [7,31,1048575,1082401,4329604,8659944,17318416] .lf) [7,31,1048575,1083361,2164802,4329604,8659208] (.nd .lf [7,31,1048575,1083361,2164802,8659208,17318416] .lf))) [7,31,1048575,2164802,4330468,8659208,17318416] (.nd (.nd (.nd (.nd .lf [7,31,1049568,2164802,8659208,17318416,32505856] .lf) [7,31,1082401,1082913,2164802,4329604,32505856] .lf) [7,31,1082401,1083361,2164802,4329604,32776456] (.nd .lf [7,31,1082401,1083361,2164802,4329604,33047056] .lf)) [7,31,1082401,1083361,2164802,8659208,33047056] (.nd (.nd (.nd .lf [7,31,1082401,1083361,2164802,17318416,32776456] .lf) [7,31,1082401,2098144,4329604,17318416,32505856] .lf) [7,31,1082401,2164802,2165314,4329604,32505856] (.nd .lf [7,31,1082401,2164802,2165730,4329604,32776456] .lf))))) [7,31,1082401,2164802,2165730,4329604,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,2165730,8659208,33047056] .lf) [7,31,1082401,2164802,2165730,17318416,32776456] .lf) [7,31,1082401,2164802,4329604,4330116,32505856] (.nd (.nd .lf [7,31,1082401,2164802,4329604,4330468,32776456] .lf) [7,31,1082401,2164802,4329604,4330468,33047056] .lf)) [7,31,1082401,2164802,4329604,8659944,32776456] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4329604,9436424,32505856] .lf) [7,31,1082401,2164802,4329604,16777728,32505856] .lf) [7,31,1082401,2164802,4329604,32505856,32506368] (.nd .lf [7,31,1082401,2164802,4329604,32505856,33553695] .lf))) [7,31,1082401,2164802,4329604,32505856,33553919] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,4329604,32506848,32776456] .lf) [7,31,1082401,2164802,4329604,32776456,32777192] .lf) [7,31,1082401,2164802,4329604,32776456,33553439] (.nd .lf [7,31,1082401,2164802,4329604,33047056,33553439] .lf)) [7,31,1082401,2164802,4330116,8659208,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330116,17318416,32505856] .lf) [7,31,1082401,2164802,4330116,32505856] .lf) [7,31,1082401,2164802,4330468,8659208,32505856] (.nd .lf [7,31,1082401,2164802,4330468,8659208,32505887] .lf)))) [7,31,1082401,2164802,4330468,8659208,32539681] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330468,8659208,32776456] .lf) [7,31,1082401,2164802,4330468,8659231,32505856] .lf) [7,31,1082401,2164802,4330468,9741609,32505856] (.nd .lf [7,31,1082401,2164802,4330468,10824010,32505856] .lf)) [7,31,1082401,2164802,4330468,17318416,32776456] (.nd (.nd (.nd .lf [7,31,1082401,2164802,4330468,21648020,32505856] .lf) [7,31,1082401,2164802,4330468,24895223,32505856] .lf) [7,31,1082401,2164802,4330468,32505856,32776456] (.nd .lf [7,31,1082401,2164802,4330468,32776456] .lf))) [7,31,1082401,2164802,5412837,8659208,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,6495206,8659208,32505856] .lf) [7,31,1082401,2164802,8659208,8659944,33047056] .lf) [7,31,1082401,2164802,8659208,12989420,32505856] (.nd .lf [7,31,1082401,2164802,8659208,16236527,32505856] .lf)) [7,31,1082401,2164802,8659208,17317904,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2164802,8659208,29223963,32505856] .lf) [7,31,1082401,2164802,8659208,32505856,32642020] .lf) [7,31,1082401,2164802,8659208,33047056,33553439] (.nd .lf [7,31,1082401,2164802,8659720,17318416,32505856] .lf)))))) [7,31,1082401,2164802,8659944,17318416,32776456] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2164802,17318416,32506848,32776456] .lf) [7,31,1082401,2164802,17318416,32776456,32777192] .lf) [7,31,1082401,2164802,17318416,32776456,33553439] (.nd (.nd .lf [7,31,1082401,2164831,4330468,8659208,32505856] .lf) [7,31,1082401,2165314,4329604,17318416,32505856] .lf)) [7,31,1082401,2165314,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,8659208,33047056] .lf) [7,31,1082401,2165730,4329604,10824010,32505856] .lf) [7,31,1082401,2165730,4329604,16236015,32505856] (.nd .lf [7,31,1082401,2165730,4329604,17318416,32505856] .lf))) [7,31,1082401,2165730,4329604,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,17318416,32539681] .lf) [7,31,1082401,2165730,4329604,17318416,33047056] .lf) [7,31,1082401,2165730,4329604,17318431,32505856] (.nd .lf [7,31,1082401,2165730,4329604,18400817,32505856] .lf)) [7,31,1082401,2165730,4329604,21648020,32505856] (.nd (.nd (.nd .lf [7,31,1082401,2165730,4329604,32505856,33047056] .lf) [7,31,1082401,2165730,4329604,33047056] .lf) [7,31,1082401,2165730,5412005,17318416,32505856] (.nd .lf [7,31,1082401,2165730,10824010,17318416,32505856] .lf)))) [7,31,1082401,2165730,17318416,21648020,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,2165730,17318416,29224827,32505856] .lf) [7,31,1082401,2165730,17318416,32505856,32641156] .lf) [7,31,1082401,2165759,4329604,17318416,32505856] (.nd (.nd .lf [7,31,1082401,2194498,4329604,9412872,32505856] .lf) [7,31,1082401,3144770,4329604,8659208,32505856] .lf)) [7,31,1082401,3144770,4329604,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,3247203,4330468,8659208,32505856] .lf) [7,31,1082401,3248099,4329604,17318416,32505856] .lf) [7,31,1082401,4329604,6495206,17318416,32505856] (.nd .lf [7,31,1082401,4329604,8389600,17318416,32505856] .lf))) [7,31,1082401,4329604,8659208,16777728,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659720,17318416,32505856] .lf) [7,31,1082401,4329604,8659944,10824010,32505856] .lf) [7,31,1082401,4329604,8659944,16236015,32505856] (.nd .lf [7,31,1082401,4329604,8659944,17318416,32505856] .lf)) [7,31,1082401,4329604,8659944,17318416,32505887] (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659944,17318416,32506848] .lf) [7,31,1082401,4329604,8659944,17318416,32539681] .lf) [7,31,1082401,4329604,8659944,17318416,32776456] (.nd .lf [7,31,1082401,4329604,8659944,17318416,32777192] .lf))))) [7,31,1082401,4329604,8659944,17318416,33047056] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082401,4329604,8659944,17318431,32505856] .lf) [7,31,1082401,4329604,8659944,18400817,32505856] .lf) [7,31,1082401,4329604,8659944,21648020,32505856] (.nd (.nd .lf [7,31,1082401,4329604,8659967,17318416,32505856] .lf) [7,31,1082401,4329604,9436424,17318416,32505856] .lf)) [7,31,1082401,4329604,9742313,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1082401,4329604,12989420,17318416,32505856] .lf) [7,31,1082401,4329604,17318416,24894487,32505856] .lf) [7,31,1082401,4329604,17318416,31388701,32505856] (.nd .lf [7,31,1082401,4330116,8659208,17318416,32505856] .lf))) [7,31,1082401,4330468,8659208,10824010,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1082401,4330468,8659208,21648020,32505856] .lf) [7,31,1082401,4330468,8659208,31389629,32505856] .lf) [7,31,1082401,5412005,8659944,17318416,32505856] (.nd .lf [7,31,1082401,8659944,10824010,17318416,32505856] .lf)) [7,31,1082401,8659944,17318416,21648020,32505856] (.nd (.nd (.nd .lf [7,31,1082401,8659944,17318416,29224827,32505856] .lf) [7,31,1082913,2164802,4329604,8659208,32505856] .lf) [7,31,1082913,2164802,4329604,17318416,32505856] (.nd .lf [7,31,1082913,2164802,4329604,32505856] .lf)))) [7,31,1082913,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1082913,4329604,8659208,17318416,32505856] .lf) [7,31,1083361,2164802,4329604,8659208,32505856] .lf) [7,31,1083361,2164802,4329604,8659208,32505887] (.nd .lf [7,31,1083361,2164802,4329604,8659208,32506848] .lf)) [7,31,1083361,2164802,4329604,8659208,32539681] (.nd (.nd (.nd .lf [7,31,1083361,2164802,4329604,8659208,32540641] .lf) [7,31,1083361,2164802,4329604,8659208,32776456] .lf) [7,31,1083361,2164802,4329604,8659208,33047056] (.nd .lf [7,31,1083361,2164802,4329604,8659231,32505856] .lf))) [7,31,1083361,2164802,4329604,10824010,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,4329604,12988812,32505856] .lf) [7,31,1083361,2164802,4329604,17318416,32539681] .lf) [7,31,1083361,2164802,4329604,18400817,32505856] (.nd .lf [7,31,1083361,2164802,4329604,24895223,32505856] .lf)) [7,31,1083361,2164802,4329604,32505856,32776456] (.nd (.nd (.nd .lf [7,31,1083361,2164802,4330468,8659208,32505856] .lf) [7,31,1083361,2164802,5412005,8659208,32505856] .lf) [7,31,1083361,2164802,5412005,17318416,32505856] (.nd .lf [7,31,1083361,2164802,5412837,8659208,32505856] .lf))))))) [7,31,1083361,2164802,6494406,8659208,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,12988812,32505856] .lf) [7,31,1083361,2164802,8659208,16236015,32505856] .lf) [7,31,1083361,2164802,8659208,17318416,32505856] (.nd (.nd .lf [7,31,1083361,2164802,8659208,17318416,32505887] .lf) [7,31,1083361,2164802,8659208,17318416,32506848] .lf)) [7,31,1083361,2164802,8659208,17318416,32539681] (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,17318416,32540641] .lf) [7,31,1083361,2164802,8659208,17318416,32776456] .lf) [7,31,1083361,2164802,8659208,17318416,33047056] (.nd .lf [7,31,1083361,2164802,8659208,17318896,32505856] .lf))) [7,31,1083361,2164802,8659208,18400817,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,18401265,32505856] .lf) [7,31,1083361,2164802,8659208,19483218,32505856] .lf) [7,31,1083361,2164802,8659208,25977624,32505856] (.nd .lf [7,31,1083361,2164802,8659208,29224827,32505856] .lf)) [7,31,1083361,2164802,8659208,32505856,32641156] (.nd (.nd (.nd .lf [7,31,1083361,2164802,8659208,32505856,33047056] .lf) [7,31,1083361,2164802,8659208,33047056] .lf) [7,31,1083361,2164802,10824010,17318416,32505856] (.nd .lf [7,31,1083361,2164802,17318416,24895223,32505856] .lf)))) [7,31,1083361,2164802,17318416,25977624,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,1083361,2164802,17318416,32505856,32776456] .lf) [7,31,1083361,2164831,4329604,8659208,32505856] .lf) [7,31,1083361,4329604,6494406,8659208,32505856] (.nd (.nd .lf [7,31,1083361,4329604,8659208,10824010,32505856] .lf) [7,31,1083361,4329604,8659208,17318416,32539681] .lf)) [7,31,1083361,4329604,8659208,18400817,32505856] (.nd (.nd (.nd .lf [7,31,1083361,4329604,8659208,31389629,32505856] .lf) [7,31,1083361,5412005,8659208,17318416,32505856] .lf) [7,31,1083361,8659208,10824010,17318416,32505856] (.nd .lf [7,31,1083361,8659208,17318416,19483218,32505856] .lf))) [7,31,1083361,8659208,17318416,31389629,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1083391,2164802,8659208,17318416,32505856] .lf) [7,31,2096161,2164802,8659208,17318416,32505856] .lf) [7,31,2164802,3247203,4330468,8659208,32505856] (.nd .lf [7,31,2164802,3248099,4329604,8659208,32505856] .lf)) [7,31,2164802,3248099,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4195296,8659208,17318416,32505856] .lf) [7,31,2164802,4329604,5412837,8659208,32505856] .lf) [7,31,2164802,4329604,8659208,9742313,32505856] (.nd .lf [7,31,2164802,4329604,8659208,16236527,32505856] .lf))))) [7,31,2164802,4329604,8659208,17317904,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,2164802,4329604,8659208,32471070,32505856] .lf) [7,31,2164802,4329604,8659720,17318416,32505856] .lf) [7,31,2164802,4329604,8659944,17318416,32776456] (.nd (.nd .lf [7,31,2164802,4330116,8659208,17318416,32505856] .lf) [7,31,2164802,4330468,5412005,8659208,32505856] .lf)) [7,31,2164802,4330468,5412005,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4330468,5412837,8659208,32505856] .lf) [7,31,2164802,4330468,8659208,9741609,32505856] .lf) [7,31,2164802,4330468,8659208,16236015,32505856] (.nd .lf [7,31,2164802,4330468,8659208,17318416,32505856] .lf))) [7,31,2164802,4330468,8659208,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,31,2164802,4330468,8659208,17318416,32776456] .lf) [7,31,2164802,4330468,8659208,17318416,33047056] .lf) [7,31,2164802,4330468,8659208,17318896,32505856] (.nd .lf [7,31,2164802,4330468,8659208,19483218,32505856] .lf)) [7,31,2164802,4330468,8659208,21648020,32505856] (.nd (.nd (.nd .lf [7,31,2164802,4330468,8659208,21648372,32505856] .lf) [7,31,2164802,4330468,8659208,25977624,32505856] .lf) [7,31,2164802,4330468,8659208,32472030,32505856] (.nd .lf [7,31,2164802,4330468,10824010,17318416,32505856] .lf)))) [7,31,2164802,4330468,17318416,24895223,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,31,2164802,4330468,17318416,25977624,32505856] .lf) [7,31,2164802,4330495,8659208,17318416,32505856] .lf) [7,31,2164802,5241988,8659208,17318416,32505856] (.nd .lf [7,31,2164802,6495206,8659208,17318416,32505856] .lf)) [7,31,2164802,8659208,9742313,17318416,32505856] (.nd (.nd (.nd .lf [7,31,2164802,8659208,12989420,17318416,32505856] .lf) [7,31,2164802,8659208,17318416,29223963,32505856] .lf) [7,31,2164802,8659208,17318416,32471070,32505856] (.nd .lf [7,31,2165314,4329604,8659208,17318416,32505856] .lf))) [7,31,2165730,4329604,5412005,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,2165730,4329604,8659208,17318416,32539681] .lf) [7,31,2165730,4329604,10824010,17318416,32505856] .lf) [7,31,2165730,4329604,17318416,18400817,32505856] (.nd .lf [7,31,2165730,4329604,17318416,32472030,32505856] .lf)) [7,31,4329604,4330468,8659208,17318416,32539681] (.nd (.nd (.nd .lf [7,31,4329604,5412005,8659944,17318416,32505856] .lf) [7,31,4329604,8659208,8659944,17318416,32539681] .lf) [7,31,4329604,8659208,17318416,32506848,32539681] (.nd .lf [7,31,4329604,8659208,17318416,32539681,32540641] .lf)))))) [7,31,4329604,8659208,17318416,32539681,33553439] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,4329604,8659944,10824010,17318416,32505856] .lf) [7,31,4329604,8659944,17318416,18400817,32505856] .lf) [7,31,4329604,8659944,17318416,32472030,32505856] (.nd (.nd .lf [7,31,4329604,8659944,17318416,32505856,32539681] .lf) [7,31,4330468,5412005,8659208,17318416,32505856] .lf)) [7,31,4330468,8659208,10824010,17318416,32505856] (.nd (.nd (.nd .lf [7,31,4330468,8659208,17318416,19483218,32505856] .lf) [7,31,4330468,8659208,17318416,31389629,32505856] .lf) [7,31,4330468,8659208,17318416,32505856,32573506] (.nd .lf [7,287,992,1082401,2164802,4329604,32505856] .lf))) [7,512,543,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [7,512,1082401,2164802,4329604,32505856,32505887] .lf) [7,512,1082401,2164802,4329604,32505856,33554400] .lf) [7,543,992,1082401,2164802,4329604,32505856] (.nd .lf [7,543,31744,1082401,2164802,4329604,32505856] .lf)) [7,543,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [7,543,1082401,2164802,4329604,17318416,32505856] .lf) [7,543,1082401,2164802,4329604,32505856] .lf) [7,543,1082401,2164802,8659208,17318416,32505856] (.nd .lf [7,543,1082401,4329604,8659208,17318416,32505856] .lf)))) [7,543,2164802,4329604,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,992,1023,1082401,2164802,4329604,32776456] .lf) [7,992,1023,1082401,2164802,4329604,33047056] .lf) [7,992,1023,1082401,2164802,8659208,33047056] (.nd (.nd .lf [7,992,1023,1082401,2164802,17318416,32776456] .lf) [7,992,1023,4329604,8659208,17318416,32539681] .lf)) [7,992,31744,1015808,1082431,2164802,4329604,8659208,33047056] (.nd (.nd (.nd .lf [7,992,31744,1015808,1082431,2164802,4329604,17318416,32776456] .lf) [7,992,31744,1082401,2164802,4329631,8659208,17809936,32505856] .lf) [7,992,31744,1082401,2164802,4329631,9412872,17318416,32505856] (.nd .lf [7,992,31744,1082401,3115074,4329631,8659208,17318416,32505856] .lf))) [7,992,31744,1082431,2164802,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [7,992,31744,1082431,2164802,4329604,9412872,17318416,32505856] .lf) [7,992,31744,1082431,3115074,4329604,8659208,17318416,32505856] .lf) [7,992,1047552,1082401,2164802,4329631,8659208,17318416,32505856] (.nd .lf [7,992,1047552,1082401,2164802,8659208,32641156] .lf)) [7,992,1047552,1082401,2164802,17318416,32641156] (.nd (.nd (.nd .lf [7,992,1047552,1082401,2164831,4329604,8659208] .lf) [7,992,1047552,1082401,2164831,4329604,17318416] .lf) [7,992,1047552,1082431,2164802,4329604,8659208,17318416,32505856] (.nd .lf [7,992,1047552,2164802,4329631,8659208,17318416] .lf))))) [7,992,1047552,4329604,8659208,17318416,32573506] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,992,1048607,2164802,8659208,17318416,32505856] .lf) [7,992,1082401,2097183,4329604,17318416,32505856] .lf) [7,992,1082401,2164802,4329604,32776456,33554400] (.nd (.nd .lf [7,992,1082401,2164802,4329604,33047056,33554400] .lf) [7,992,1082401,2164802,8659208,32505887,32641156] .lf)) [7,992,1082401,2164802,8659208,33047056,33554400] (.nd (.nd (.nd .lf [7,992,1082401,2164802,17318416,32505887,32641156] .lf) [7,992,1082401,2164802,17318416,32776456,33554400] .lf) [7,992,1082401,2164831,4329604,8659208,32505887] (.nd .lf [7,992,1082401,2164831,4329604,8659231,32505856] .lf))) [7,992,1082401,2164831,4329604,17318416,32505887] (.nd (.nd (.nd (.nd .lf [7,992,1082401,2164831,4329604,17318431,32505856] .lf) [7,992,1082401,4329604,8388639,17318416,32505856] .lf) [7,992,1082401,4329604,8659231,17318431,32505856] (.nd .lf [7,992,2164802,4194335,8659208,17318416,32505856] .lf)) [7,992,2164802,4329631,8659208,17318416,32505887] (.nd (.nd (.nd .lf [7,992,4329604,8659208,17318416,32505887,32573506] .lf) [7,992,4329604,8659208,17318416,32539681,33554400] .lf) [7,1023,1082401,2164802,4329604,8659208,32505887] (.nd .lf [7,1023,1082401,2164802,4329604,8659208,32506848] .lf)))) [7,1023,1082401,2164802,4329604,17318416,32505887] (.nd (.nd (.nd (.nd (.nd .lf [7,1023,1082401,2164802,4329604,17318416,32506848] .lf) [7,1023,1082401,2164802,4329604,17318431,32505856] .lf) [7,1023,1082401,2164802,8659208,17318416,32505887] (.nd .lf [7,1023,1082401,2164802,8659208,17318416,32506848] .lf)) [7,1023,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd .lf [7,1023,1082401,4329604,8659208,17318416,32505887] .lf) [7,1023,1082401,4329604,8659208,17318416,32506848] .lf) [7,1023,1082401,4329604,8659208,17318431,32505856] (.nd .lf [7,1023,2164802,4329604,8659208,17318416,32505887] .lf))) [7,1023,2164802,4329604,8659208,17318416,32506848] (.nd (.nd (.nd (.nd .lf [7,1023,2164802,4329604,8659208,17318896,32505856] .lf) [7,31744,1015808,1082401,2164802,4329631,8659944,17318416,32505856] .lf) [7,31744,1015808,1082401,2165730,4329631,8659208,17318416,32505856] (.nd .lf [7,31744,1015808,1082431,2164802,4329604,8659944,17318416,32505856] .lf)) [7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31744,1015808,1083361,2164831,4329604,8659208] .lf) [7,31744,1015808,4329604,8659208,17318431,32539681] .lf) [7,31744,1015808,4329604,8659208,17318896,32573506] (.nd .lf [7,1047552,1082401,2164802,4329604,17318431,32505856] .lf)))))))) [7,1047552,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,1047552,1082401,4329604,8659208,17318431,32505856] .lf) [7,1047552,2164802,4329604,8659208,17318896,32505856] .lf) [7,1082401,2164802,4329604,8659208,32505887,32506848] (.nd (.nd .lf [7,1082401,2164802,4329604,17318416,32505887,32506848] .lf) [7,1082401,2164802,4330468,8659208,32505856,32505887] .lf)) [7,1082401,2164802,4330468,8659208,32505856,33554400] (.nd (.nd (.nd .lf [7,1082401,2164802,8659208,17318416,32505887,32506848] .lf) [7,1082401,2165730,4329604,17318416,32505856,32505887] .lf) [7,1082401,2165730,4329604,17318416,32505856,33554400] (.nd .lf [7,1082401,4329604,8659208,17318416,32505887,32506848] .lf))) [7,1082401,4329604,8659944,17318416,32505856,32505887] (.nd (.nd (.nd (.nd .lf [7,1082401,4329604,8659944,17318416,32505856,33554400] .lf) [7,1083361,2164802,4329604,8659208,32505856,32505887] .lf) [7,1083361,2164802,4329604,8659208,32505856,33554400] (.nd .lf [7,1083361,2164802,8659208,17318416,32505856,32505887] .lf)) [7,1083361,2164802,8659208,17318416,32505856,33554400] (.nd (.nd (.nd .lf [7,2164802,4329604,8659208,17318416,32505887,32506848] .lf) [7,2164802,4330468,8659208,17318416,32505856,32505887] .lf) [7,2164802,4330468,8659208,17318416,32505856,33554400] (.nd .lf [8,31,256,992,1082401,2164802,4329604,32505856] .lf)))) [8,31,512,992,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,512,31744,1082401,2164802,4329604,32505856] .lf) [8,31,512,1082401,2164802,4329604,8659208,32505856] .lf) [8,31,512,1082401,2164802,4329604,17318416,32505856] (.nd (.nd .lf [8,31,512,1082401,2164802,4329604,32505856] .lf) [8,31,512,1082401,2164802,8659208,17318416,32505856] .lf)) [8,31,512,1082401,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,31,512,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056] .lf) [8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456] (.nd .lf [8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156] .lf))) [8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,31744,1082401,2164802,4329604,9412872] .lf) [8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856] .lf) [8,31,992,31744,1082401,2164802,4329604,17809936] (.nd .lf [8,31,992,31744,1082401,2164802,4329604,32776456] .lf)) [8,31,992,31744,1082401,2164802,4329604,33047056] (.nd (.nd (.nd .lf [8,31,992,31744,1082401,2164802,8659208,33047056] .lf) [8,31,992,31744,1082401,2164802,17318416,32776456] .lf) [8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856] (.nd .lf [8,31,992,31744,1082401,4329604,8659208,17809936] .lf))))) [8,31,992,31744,1082401,4329604,9412872,17318416] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,31744,2065441,2164802,8659208,17318416] .lf) [8,31,992,31744,4329604,8659208,17318416,32539681] .lf) [8,31,992,1047552,1082401,2164802,4329604,8659208] (.nd (.nd .lf [8,31,992,1047552,1082401,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,992,1047552,1082401,2164802,4329604,17318416] .lf)) [8,31,992,1047552,1082401,2164802,8659208,17318416] (.nd (.nd (.nd .lf [8,31,992,1047552,1082401,4329604,8659208,17318416] .lf) [8,31,992,1047552,2164802,4329604,8659208,17318416] .lf) [8,31,992,1048575,1082401,2164802,4329604,8659208] (.nd .lf [8,31,992,1048575,1082401,2164802,4329604,17318416] .lf))) [8,31,992,1048575,1082401,2164802,8659208,17318416] (.nd (.nd (.nd (.nd .lf [8,31,992,1048575,1082401,4329604,8659208,17318416] .lf) [8,31,992,1048575,2164802,4329604,8659208,17318416] .lf) [8,31,992,1048576,2164802,8659208,17318416,32505856] (.nd .lf [8,31,992,1082401,2097152,4329604,17318416,32505856] .lf)) [8,31,992,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,8659208,32505887] .lf) [8,31,992,1082401,2164802,4329604,8659208,32506848] .lf) [8,31,992,1082401,2164802,4329604,8659208,32539681] (.nd .lf [8,31,992,1082401,2164802,4329604,8659208,32776456] .lf)))) [8,31,992,1082401,2164802,4329604,8659208,33047056] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,8659231,32505856] .lf) [8,31,992,1082401,2164802,4329604,8682760,32505856] .lf) [8,31,992,1082401,2164802,4329604,9741609,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,10824010,32505856] .lf)) [8,31,992,1082401,2164802,4329604,12988812,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,16236015,32505856] .lf) [8,31,992,1082401,2164802,4329604,17318416,32505856] .lf) [8,31,992,1082401,2164802,4329604,17318416,32505887] (.nd .lf [8,31,992,1082401,2164802,4329604,17318416,32506848] .lf))) [8,31,992,1082401,2164802,4329604,17318416,32539681] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,17318416,32776456] .lf) [8,31,992,1082401,2164802,4329604,17318416,33047056] .lf) [8,31,992,1082401,2164802,4329604,17318431,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,17333776,32505856] .lf)) [8,31,992,1082401,2164802,4329604,18400817,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,19483218,32505856] .lf) [8,31,992,1082401,2164802,4329604,21648020,32505856] .lf) [8,31,992,1082401,2164802,4329604,24895223,32505856] (.nd .lf [8,31,992,1082401,2164802,4329604,32505856,32776456] .lf)))))) [8,31,992,1082401,2164802,4329604,32505856,33047056] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,4329604,32776456] .lf) [8,31,992,1082401,2164802,4329604,33047056] .lf) [8,31,992,1082401,2164802,4330468,8659208,32505856] (.nd (.nd .lf [8,31,992,1082401,2164802,5412005,8659208,32505856] .lf) [8,31,992,1082401,2164802,5412005,17318416,32505856] .lf)) [8,31,992,1082401,2164802,6494406,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,6494406,17318416,32505856] .lf) [8,31,992,1082401,2164802,8659208,12988812,32505856] .lf) [8,31,992,1082401,2164802,8659208,16236015,32505856] (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,32505856] .lf))) [8,31,992,1082401,2164802,8659208,17318416,32505887] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,32506848] .lf) [8,31,992,1082401,2164802,8659208,17318416,32539681] .lf) [8,31,992,1082401,2164802,8659208,17318416,32776456] (.nd .lf [8,31,992,1082401,2164802,8659208,17318416,33047056] .lf)) [8,31,992,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,18400817,32505856] .lf) [8,31,992,1082401,2164802,8659208,19483218,32505856] .lf) [8,31,992,1082401,2164802,8659208,25977624,32505856] (.nd .lf [8,31,992,1082401,2164802,8659208,29224827,32505856] .lf)))) [8,31,992,1082401,2164802,8659208,32505856,32641156] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,8659208,32505856,33047056] .lf) [8,31,992,1082401,2164802,8659208,33047056] .lf) [8,31,992,1082401,2164802,9741609,17318416,32505856] (.nd (.nd .lf [8,31,992,1082401,2164802,10824010,17318416,32505856] .lf) [8,31,992,1082401,2164802,17318416,21648020,32505856] .lf)) [8,31,992,1082401,2164802,17318416,24895223,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,2164802,17318416,25977624,32505856] .lf) [8,31,992,1082401,2164802,17318416,29224827,32505856] .lf) [8,31,992,1082401,2164802,17318416,32505856,32641156] (.nd .lf [8,31,992,1082401,2164802,17318416,32505856,32776456] .lf))) [8,31,992,1082401,2164802,17318416,32776456] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,2164831,4329604,8659208,32505856] .lf) [8,31,992,1082401,2164831,4329604,17318416,32505856] .lf) [8,31,992,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,992,1082401,2194498,4329604,8659208,32505856] .lf)) [8,31,992,1082401,2194498,4329604,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,3247203,4329604,8659208,32505856] .lf) [8,31,992,1082401,3247203,4329604,17318416,32505856] .lf) [8,31,992,1082401,3247203,8659208,17318416,32505856] (.nd .lf [8,31,992,1082401,4329604,6494406,8659208,32505856] .lf))))) [8,31,992,1082401,4329604,6494406,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8388608,17318416,32505856] .lf) [8,31,992,1082401,4329604,8659208,10824010,32505856] .lf) [8,31,992,1082401,4329604,8659208,16236015,32505856] (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,992,1082401,4329604,8659208,17318416,32505887] .lf)) [8,31,992,1082401,4329604,8659208,17318416,32506848] (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,17318416,32539681] .lf) [8,31,992,1082401,4329604,8659208,17318416,32776456] .lf) [8,31,992,1082401,4329604,8659208,17318416,33047056] (.nd .lf [8,31,992,1082401,4329604,8659208,17318431,32505856] .lf))) [8,31,992,1082401,4329604,8659208,17333776,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659208,18400817,32505856] .lf) [8,31,992,1082401,4329604,8659208,21648020,32505856] .lf) [8,31,992,1082401,4329604,8659208,25977624,32505856] (.nd .lf [8,31,992,1082401,4329604,8659208,31389629,32505856] .lf)) [8,31,992,1082401,4329604,8659231,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,8659944,17318416,32505856] .lf) [8,31,992,1082401,4329604,8682760,17318416,32505856] .lf) [8,31,992,1082401,4329604,9741609,17318416,32505856] (.nd .lf [8,31,992,1082401,4329604,12988812,17318416,32505856] .lf)))) [8,31,992,1082401,4329604,17318416,19483218,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,1082401,4329604,17318416,24895223,32505856] .lf) [8,31,992,1082401,4329604,17318416,25977624,32505856] .lf) [8,31,992,1082401,4329604,17318416,31389629,32505856] (.nd .lf [8,31,992,1082401,5412005,8659208,17318416,32505856] .lf)) [8,31,992,1082401,8659208,10824010,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,1082401,8659208,12988812,17318416,32505856] .lf) [8,31,992,1082401,8659208,17318416,19483218,32505856] .lf) [8,31,992,1082401,8659208,17318416,21648020,32505856] (.nd .lf [8,31,992,1082401,8659208,17318416,29224827,32505856] .lf))) [8,31,992,1082401,8659208,17318416,31389629,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,1082431,2164802,8659208,17318416,32505856] .lf) [8,31,992,1083361,2164802,4329604,8659208,32505856] .lf) [8,31,992,1083361,2164802,8659208,17318416,32505856] (.nd .lf [8,31,992,1113121,2164802,8659208,17318416,32505856] .lf)) [8,31,992,2164802,3247203,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,3247203,4329604,17318416,32505856] .lf) [8,31,992,2164802,3247203,8659208,17318416,32505856] .lf) [8,31,992,2164802,4194304,8659208,17318416,32505856] (.nd .lf [8,31,992,2164802,4329604,5412005,8659208,32505856] .lf))))))) [8,31,992,2164802,4329604,5412005,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,9741609,32505856] .lf) [8,31,992,2164802,4329604,8659208,16236015,32505856] .lf) [8,31,992,2164802,4329604,8659208,17318416,32505856] (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,17318416,32505887] .lf) [8,31,992,2164802,4329604,8659208,17318416,32506848] .lf)) [8,31,992,2164802,4329604,8659208,17318416,32539681] (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,17318416,32776456] .lf) [8,31,992,2164802,4329604,8659208,17318416,33047056] .lf) [8,31,992,2164802,4329604,8659208,17318896,32505856] (.nd .lf [8,31,992,2164802,4329604,8659208,19483218,32505856] .lf))) [8,31,992,2164802,4329604,8659208,21648020,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,8659208,25977624,32505856] .lf) [8,31,992,2164802,4329604,8659208,32472030,32505856] .lf) [8,31,992,2164802,4329604,10824010,17318416,32505856] (.nd .lf [8,31,992,2164802,4329604,12988812,17318416,32505856] .lf)) [8,31,992,2164802,4329604,17318416,18400817,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,4329604,17318416,24895223,32505856] .lf) [8,31,992,2164802,4329604,17318416,25977624,32505856] .lf) [8,31,992,2164802,4329604,17318416,32472030,32505856] (.nd .lf [8,31,992,2164802,4329631,8659208,17318416,32505856] .lf)))) [8,31,992,2164802,4330468,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,2164802,4357252,8659208,17318416,32505856] .lf) [8,31,992,2164802,6494406,8659208,17318416,32505856] .lf) [8,31,992,2164802,8659208,9741609,17318416,32505856] (.nd (.nd .lf [8,31,992,2164802,8659208,12988812,17318416,32505856] .lf) [8,31,992,2164802,8659208,17318416,18400817,32505856] .lf)) [8,31,992,2164802,8659208,17318416,21648020,32505856] (.nd (.nd (.nd .lf [8,31,992,2164802,8659208,17318416,29224827,32505856] .lf) [8,31,992,2164802,8659208,17318416,32472030,32505856] .lf) [8,31,992,4329604,5412005,8659208,17318416,32505856] (.nd .lf [8,31,992,4329604,6494406,8659208,17318416,32505856] .lf))) [8,31,992,4329604,8659208,9741609,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,992,4329604,8659208,10824010,17318416,32505856] .lf) [8,31,992,4329604,8659208,17318416,18400817,32505856] .lf) [8,31,992,4329604,8659208,17318416,19483218,32505856] (.nd .lf [8,31,992,4329604,8659208,17318416,31389629,32505856] .lf)) [8,31,992,4329604,8659208,17318416,32472030,32505856] (.nd (.nd (.nd .lf [8,31,992,4329604,8659208,17318416,32505856,32539681] .lf) [8,31,992,4329604,8659208,17318416,32505856,32573506] .lf) [8,31,992,4329604,8659208,17318416,32539681] (.nd .lf [8,31,1023,1082401,2164802,4329604,8659208,32505856] .lf))))) [8,31,1023,1082401,2164802,4329604,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,1023,1082401,2164802,8659208,17318416,32505856] .lf) [8,31,1023,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,1023,2164802,4329604,8659208,17318416,32505856] (.nd (.nd .lf [8,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856] .lf) [8,31,31744,1015808,1082401,2164802,4329604,32776456] .lf)) [8,31,31744,1015808,1082401,2164802,17318416,32776456] (.nd (.nd (.nd .lf [8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,31744,1015808,1082401,4329604,8659944,17318416] .lf) [8,31,31744,1015808,1083361,2164802,4329604,8659208] (.nd .lf [8,31,31744,1015808,1083361,2164802,8659208,17318416] .lf))) [8,31,31744,1015808,4329604,8659208,17318416,32539681] (.nd (.nd (.nd (.nd .lf [8,31,31744,1082401,2164802,4329604,9412872,32505856] .lf) [8,31,31744,1082401,2164802,4330468,8659208,32505856] .lf) [8,31,31744,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,31744,1082401,3115074,4329604,8659208,32505856] .lf)) [8,31,31744,1082401,3115074,4329604,17318416,32505856] (.nd (.nd (.nd .lf [8,31,31744,1082401,4329604,8659944,17318416,32505856] .lf) [8,31,31744,1082401,4329604,9412872,17318416,32505856] .lf) [8,31,31744,1083361,2164802,4329604,8659208,32505856] (.nd .lf [8,31,31744,1083361,2164802,8659208,17318416,32505856] .lf)))) [8,31,31744,2065441,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [8,31,31744,2164802,4330468,8659208,17318416,32505856] .lf) [8,31,31744,2164802,5214340,8659208,17318416,32505856] .lf) [8,31,1047552,1082401,2164802,4329604,8659208,32505856] (.nd .lf [8,31,1047552,1082401,2164802,4329604,17318416,32505856] .lf)) [8,31,1047552,1082401,2164802,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,31,1047552,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,1047552,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,1083361,2164802,4329604,8659208,32505856] (.nd .lf [8,31,1082401,1083361,2164802,4329604,17318416,32505856] .lf))) [8,31,1082401,1083361,2164802,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,1082401,1083361,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,2164802,2165730,4329604,8659208,32505856] .lf) [8,31,1082401,2164802,2165730,4329604,17318416,32505856] (.nd .lf [8,31,1082401,2164802,2165730,8659208,17318416,32505856] .lf)) [8,31,1082401,2164802,4329604,4330468,8659208,32505856] (.nd (.nd (.nd .lf [8,31,1082401,2164802,4329604,4330468,17318416,32505856] .lf) [8,31,1082401,2164802,4329604,8659208,8659944,32505856] .lf) [8,31,1082401,2164802,4329604,8659208,32505856,32506848] (.nd .lf [8,31,1082401,2164802,4329604,8659208,32505856,33553439] .lf)))))) [8,31,1082401,2164802,4329604,8659944,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,31,1082401,2164802,4329604,17318416,32505856,32506848] .lf) [8,31,1082401,2164802,4329604,17318416,32505856,33553439] .lf) [8,31,1082401,2164802,4330468,8659208,17318416,32505856] (.nd (.nd .lf [8,31,1082401,2164802,4330468,8659208,32505856] .lf) [8,31,1082401,2164802,8659208,8659944,17318416,32505856] .lf)) [8,31,1082401,2164802,8659208,17318416,32505856,32506848] (.nd (.nd (.nd .lf [8,31,1082401,2164802,8659208,17318416,32505856,33553439] .lf) [8,31,1082401,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,1082401,2165730,4329604,17318416,32505856] (.nd .lf [8,31,1082401,4329604,4330468,8659208,17318416,32505856] .lf))) [8,31,1082401,4329604,8659208,8659944,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,1082401,4329604,8659208,17318416,32505856,32506848] .lf) [8,31,1082401,4329604,8659208,17318416,32505856,33553439] .lf) [8,31,1082401,4329604,8659944,17318416,32505856] (.nd .lf [8,31,1083361,2164802,4329604,8659208,17318416,32505856] .lf)) [8,31,1083361,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,31,1083361,2164802,8659208,17318416,32505856] .lf) [8,31,2164802,2165730,4329604,8659208,17318416,32505856] .lf) [8,31,2164802,4329604,4330468,8659208,17318416,32505856] (.nd .lf [8,31,2164802,4329604,8659208,8659944,17318416,32505856] .lf)))) [8,31,2164802,4329604,8659208,17318416,32505856,32506848] (.nd (.nd (.nd (.nd (.nd .lf [8,31,2164802,4329604,8659208,17318416,32505856,33553439] .lf) [8,31,2164802,4330468,8659208,17318416,32505856] .lf) [8,992,1023,1082401,2164802,4329604,8659208,32505856] (.nd (.nd .lf [8,992,1023,1082401,2164802,4329604,17318416,32505856] .lf) [8,992,1023,1082401,2164802,8659208,17318416,32505856] .lf)) [8,992,1023,1082401,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,992,1023,2164802,4329604,8659208,17318416,32505856] .lf) [8,992,31744,1015808,1082401,2164802,4329631,8659208,17318416,32505856] .lf) [8,992,31744,1015808,1082401,2164802,8659208,32641156] (.nd .lf [8,992,31744,1015808,1082401,2164802,17318416,32641156] .lf))) [8,992,31744,1015808,1082401,2164831,4329604,8659208] (.nd (.nd (.nd (.nd .lf [8,992,31744,1015808,1082401,2164831,4329604,17318416] .lf) [8,992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856] .lf) [8,992,31744,1015808,2164802,4329631,8659208,17318416] (.nd .lf [8,992,31744,1015808,4329604,8659208,17318416,32573506] .lf)) [8,992,1047552,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [8,992,1047552,1082401,2164802,4329604,17318416,32505856] .lf) [8,992,1047552,1082401,2164802,8659208,17318416,32505856] .lf) [8,992,1047552,1082401,4329604,8659208,17318416,32505856] (.nd .lf [8,992,1047552,2164802,4329604,8659208,17318416,32505856] .lf))))) [8,992,1082401,2164802,4329604,8659208,32505856,32505887] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,992,1082401,2164802,4329604,8659208,32505856,33554400] .lf) [8,992,1082401,2164802,4329604,17318416,32505856,32505887] .lf) [8,992,1082401,2164802,4329604,17318416,32505856,33554400] (.nd (.nd .lf [8,992,1082401,2164802,8659208,17318416,32505856,32505887] .lf) [8,992,1082401,2164802,8659208,17318416,32505856,33554400] .lf)) [8,992,1082401,4329604,8659208,17318416,32505856,32505887] (.nd (.nd (.nd .lf [8,992,1082401,4329604,8659208,17318416,32505856,33554400] .lf) [8,992,2164802,4329604,8659208,17318416,32505856,32505887] .lf) [8,992,2164802,4329604,8659208,17318416,32505856,33554400] (.nd .lf [8,31744,1015808,1082401,2164802,4329604,17318431,32505856] .lf))) [8,31744,1015808,1082401,2164802,8659208,17318896,32505856] (.nd (.nd (.nd (.nd .lf [8,31744,1015808,1082401,4329604,8659208,17318431,32505856] .lf) [8,31744,1015808,2164802,4329604,8659208,17318896,32505856] .lf) [9,31,992,31744,1015808,1082401,2164802,4329604,8659208] (.nd .lf [9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856] .lf)) [9,31,992,31744,1015808,1082401,2164802,4329604,17318416] (.nd (.nd (.nd .lf [9,31,992,31744,1015808,1082401,2164802,8659208,17318416] .lf) [9,31,992,31744,1015808,1082401,4329604,8659208,17318416] .lf) [9,31,992,31744,1015808,2164802,4329604,8659208,17318416] (.nd .lf [9,31,992,31744,1082401,2164802,4329604,8659208,32505856] .lf)))) [9,31,992,31744,1082401,2164802,4329604,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [9,31,992,31744,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,992,31744,1082401,4329604,8659208,17318416,32505856] .lf) [9,31,992,31744,2164802,4329604,8659208,17318416,32505856] (.nd .lf [9,31,992,1082401,2164802,4329604,8659208,17318416,32505856] .lf)) [9,31,992,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [9,31,992,1082401,2164802,4329604,17318416,32505856] .lf) [9,31,992,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,992,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,31,992,2164802,4329604,8659208,17318416,32505856] .lf))) [9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd .lf [9,31,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856] .lf) [9,31,31744,1015808,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf)) [9,992,31744,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd .lf [9,992,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [9,992,31744,1015808,1082401,2164802,8659208,17318416,32505856] .lf) [9,992,31744,1015808,1082401,4329604,8659208,17318416,32505856] (.nd .lf [9,992,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf))))))))))
def P_ := stepOK 33554431 Y_ PD_ PM_ G_ T_
def b0 : List (List Nat × List (Nat × Nat)) := [([3,5412005,6291999],hh [0x136018d804058081600]),([3,5412517,6291487],hh [0x136018d804058081600]),([4,31,2164802,32268568],hh [0x1158185604158085600,0x1020280808]),([4,31,3213890,33317656],hh [0x1158185604158085600,0x1020280808]),([4,31,4329604,7374369],hh [0x136018d80436008d800,0x1450291408]),([4,31,4330116,7373857],hh [0x136018d80436008d800,0x1450291408]),([4,31,5412005,6291968],hh [0x1520194804520094800,0x136128d84936028d808]),([4,31,5412517,6291456],hh [0x19a01a68049a00a6800,0x136128d84936028d808])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : b0.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b1 : List (List Nat × List (Nat × Nat)) := [([4,512,5412005,6291487],hh [0x1058181604058081600,0x1058e8163936028d808,0x136128d849]),([4,543,4329604,7373857],hh [0x136018d80436008d800,0x1450291408]),([4,543,5412005,6291456],hh [0x19a01a68049a00a6800,0x136128d84936028d808]),([4,1049119,2164802,33317656],hh [0x1158185604158085600,0x1020280808]),([4,1082401,4329604,6291999],hh [0x1058181604058081600,0x1058e81639450291408]),([4,1082401,4330116,6291487],hh [0x1058181604058081600,0x1058e81639450291408]),([4,1082431,2165730,4329604,9436424,33047056],[]),([4,1082913,4329604,6291487],hh [0x1058181604058081600,0x1058e81639450291408])]
def b2 : List (List Nat × List (Nat × Nat)) := [([5,31,512,4329604,7373857],hh [0x136018d80436008d800,0x145039140c36028d808,0x136148d851360e8d839,0x1451a91469]),([5,31,512,5412005,6291456],hh [0x19a01a68049a00a6800,0x136038d80c9a02a6808,0x19a14a68519a0ea6839,0x1361a8d86936188d861]),([5,31,992,10824010,23609872],hh [0x1270189c04270089c00,0x102038080c270289c08,0x1021a89c51270e89c39,0x4926d]),([5,31,1049088,2164802,33317656],hh [0x1158185604158085600,0x102038080c158285608,0x1159485651158e85639,0x1159b4086a]),([5,31,1082401,2164802,33317144],hh [0x11c01870041c0087000,0x105038140c1c0287008,0x1051a870521c1445c3a,0x4566d]),([5,31,1082401,2165314,33317656],hh [0x11c01870041c0087000,0x105038140c1c0287008,0x1051a870521c1445c3a,0x4566d]),([5,31,1082401,2165730,4329604,9436424,33047056],[]),([5,31,1082401,4329604,6291968],hh [0x1530194c04530094c00,0x145039140c530294c08,0x1451891461531494c51,0x1451a91469])]
def b3 : List (List Nat × List (Nat × Nat)) := [([5,31,1082401,4330116,6291456],hh [0x19c81a72049c80a7200,0x145039140c9c82a7208,0x14518914619c94a7251,0x1451a91469]),([5,31,1082913,2164802,33317656],hh [0x11c01870041c0087000,0x105038140c1c0287008,0x1051a870521c1445c3a,0x4566d]),([5,31,1082913,4329604,6291456],hh [0x19c81a72049c80a7200,0x145039140c9c82a7208,0x14518914619c94a7251,0x1451a91469]),([5,31,1556463,2164802,8659208],hh [0x1158185604158085600,0x102038080c158285608,0x13f1c8fc71021b85669]),([5,31,2164802,8659208,31997968],hh [0x1248189204248089200,0x115838560c248289208,0x1021c80871249489251]),([5,31,3179553,4330116,32505856],hh [0x1450191404450091400,0x145039140c36028d808,0x14518a1661059481651,0x51476361c5146a]),([5,31,3180065,4329604,32505856],hh [0x1450191404450091400,0x145039140c36028d808,0x14518a1661059481651,0x51476361c5146a]),([5,31,3180065,4329604,33047056],hh [0x1450191404450091400,0x145039140c36028d808,0x1451a91462059481651,0x1451d8b071])]
def b4 : List (List Nat × List (Nat × Nat)) := [([5,31,3213890,8659208,33047056],hh [0x1248189204248089200,0x115838560c248289208,0x1021c80871249489251]),([5,31,3247203,4330116,32539681],hh [0x136018d80436008d800,0x149839260c36028d808,0x1451b4d85236144d83a,0x41671]),([5,31,3247203,4330468,32810281],hh [0x136018d80436008d800,0x14d039340c36028d808,0x11c1c4d852]),([5,31,3247203,5412517,32505856],hh [0x19c81a72049c80a7200,0x136038d80c9c82a7208,0x1361b4d86287186723a,0x41671]),([5,31,3247203,6494918,32505856],hh [0x19c81a72049c80a7200,0x100838020c9c82a7208,0x1009da2a710098a1c61]),([5,31,3247715,4329604,32540193],hh [0x136018d80436008d800,0x149839260c36028d808,0x1451b4d85236144d83a,0x41671]),([5,31,3247715,5412517,32505856],hh [0x19c81a72049c80a7200,0x136038d80c9c82a7208,0x1361b4d86287186723a,0x41671]),([5,31,3247715,6494406,32505856],hh [0x19c81a72049c80a7200,0x100838020c9c82a7208,0x1009da2a710098a1c61])]
def b5 : List (List Nat × List (Nat × Nat)) := [([5,31,3248099,4329604,33080881],hh [0x136018d80436008d800,0x145839160c36028d808,0x4bc71451b4d851]),([5,31,3248099,5412005,33047056],hh [0x1560195804560095800,0x136038d80c560295808,0x12f1c4d86d36189583a]),([5,31,3248099,10824010,33047056],hh [0x12f018bc042f008bc00,0x102038080c2f028bc08,0x41671249b4a03a]),([5,31,4330116,25977624,32539681],hh [0x136018d80436008d800,0x145039140c36028d808,0x1361d4567236148d84a]),([5,31,5412005,6495206,33047056],hh [0x1520194804520094800,0x169839a60c520294808,0x1369d8d87569989484a]),([5,31,5412517,6494406,32505856],hh [0x19c81a72049c80a7200,0x1bb03aec0c9c82a7208,0x1361d6ec6287186724a,0x4ee76]),([5,31,5412517,6494918,32505856],hh [0x19c81a72049c80a7200,0x1bb03aec0c9c82a7208,0x1361d6ec6287186724a,0x4ee76]),([5,31,8659208,21107332,32539681],hh [0x136018d80436008d800,0x145039140c36028d808,0x1451a8d85236144d83a,0x4d86d])]
def b6 : List (List Nat × List (Nat × Nat)) := [([5,31,9742313,10824010,33047056],hh [0x12f018bc042f008bc00,0x104038100c2f028bc08,0x4926d041a8a03a]),([5,512,1082401,4329604,6291487],hh [0x1058181604058081600,0x145039140c058281608,0x1059281649058e81639,0x1451891461059481651]),([5,543,1082401,2164802,33317656],hh [0x11c01870041c0087000,0x105038140c1c0287008,0x1051a870521c1445c3a,0x4566d]),([5,543,1082401,4329604,6291456],hh [0x19c81a72049c80a7200,0x145039140c9c82a7208,0x14518914619c94a7251,0x1451a91469]),([5,543,3179553,4329604,32505856],hh [0x1450191404450091400,0x145039140c36028d808,0x14518a1661059481651,0x51476361c5146a]),([5,543,3247203,4329604,32539681],hh [0x136018d80436008d800,0x149839260c36028d808,0x1451b4d85236144d83a,0x41671]),([5,543,3247203,5412005,32505856],hh [0x19c81a72049c80a7200,0x136038d80c9c82a7208,0x1361b4d86287186723a,0x41671]),([5,543,3247203,6494406,32505856],hh [0x19c81a72049c80a7200,0x100838020c9c82a7208,0x1009da2a710098a1c61])]
def b7 : List (List Nat × List (Nat × Nat)) := [([5,543,4329604,25977624,32539681],hh [0x136018d80436008d800,0x145039140c36028d808,0x1159c8d85236144d84a,0x4d875]),([5,543,5412005,6494406,32505856],hh [0x19c81a72049c80a7200,0x1bb03aec0c9c82a7208,0x1361d6ec6287186724a,0x4ee76]),([5,992,1082431,2164802,4329604,9436424,33047056],[]),([5,992,1082431,2164802,4329604,17825296,32776456],[]),([5,992,5412005,6291487,17318416],hh [0x10d01834040d0083400,0x10d038340c36028d808,0x105994d84a059242439,0x1361c8346a271a43466]),([5,992,6291487,10824010,17318416],hh [0x1270189c04270089c00,0x102038080c270289c08,0x1021889c49270e89c39,0x434720d1c49265]),([5,31744,1082431,2165730,4329604,9412872,33047056],[]),([5,1047552,1082431,2165730,4329604,8659208,33047056],[])]
def b8 : List (List Nat × List (Nat × Nat)) := [([5,1049119,2164802,8659208,33047056],hh [0x1248189204248089200,0x115838560c248289208,0x1021c80871249489251]),([5,1082401,2097183,4330116,32505856],hh [0x1450191404450091400,0x145039140c058281608,0x1451a91462059281649,0x1451da5271]),([5,1082401,2097695,4329604,32505856],hh [0x1450191404450091400,0x145039140c058281608,0x1451a91462059281649,0x1451da5271]),([5,1082401,2097695,4329604,33047056],hh [0x1450191404450091400,0x145039140c058281608,0x1451a91462059281649,0x1451d8b071]),([5,1082401,2164802,32505887,32641668],hh [0x1498192604498092600,0x105838160c498292608,0x1059a91655498e92639,0x5146d]),([5,1082401,2164802,32506399,32641156],hh [0x1498192604498092600,0x105838160c498292608,0x1059a91655498e92639,0x5146d]),([5,1082401,2164831,4330116,32505887],hh [0x1070181c04070081c00,0x149039240c070281c08,0x1491881a51071281c49,0x5146d]),([5,1082401,2164831,4330468,32776479],hh [0x10b8182e040b8082e00,0x14b8392e0c0b8282e08,0x52e620b9282849])]
def b9 : List (List Nat × List (Nat × Nat)) := [([5,1082401,2165343,4329604,32506399],hh [0x1070181c04070081c00,0x149039240c070281c08,0x1491881a51071281c49,0x5146d]),([5,1082401,2165730,4329631,9436424,17318416,32505856],[]),([5,1082401,2165759,4329604,33047071],hh [0x1058181604058081600,0x145039140c058281608,0x1451b41651059281649]),([5,1082401,3144770,4329631,8659944,17318416,32505856],[]),([5,1082431,2165730,4329604,9436424,17318416,32505856],[]),([5,1082431,3144770,4329604,8659944,17318416,32505856],[]),([5,1082913,2097183,4329604,32505856],hh [0x1450191404450091400,0x145039140c058281608,0x1451a91462059281649,0x1451da5271]),([5,1082913,2164802,32505887,32641156],hh [0x1498192604498092600,0x105838160c498292608,0x1059a91655498e92639,0x5146d])]
def b10 : List (List Nat × List (Nat × Nat)) := [([5,1082913,2164831,4329604,32505887],hh [0x1070181c04070081c00,0x149039240c070281c08,0x1491881a51071281c49,0x5146d]),([5,4329604,8659208,16777759,32539681],hh [0x136018d80436008d800,0x105838160c36028d808,0x1059a8d851360e8d839,0x4d86d]),([6,31,512,1082401,2164802,33317656],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c0e87039050481410,0x11c1a470521c1445c4a,0x10522870721c1c4706a,0x4569505248708d]),([6,31,512,1082401,4329604,6291456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c8ea7239450491410,0x19c9aa72699c94a7251,0x14520914819c9ca7271,0x1452491491452291489]),([6,31,512,3179553,4329604,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1450e91439450491410,0x1361a8d869451491451,0x14520a1681059c81671,0x1362651492452291489,0x5149e]),([6,31,512,3247203,4329604,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839498492610,0x1361a4d85236144d84a,0x149a24d872361c4d86a,0x4169945255268a]),([6,31,512,3247203,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c8ea723936048d810,0x19c9a672529c946724a,0x136224d88287206726a,0x4169936254d88a]),([6,31,512,3247203,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c8ea7239008480210,0x19c9aa72699c94a7251,0x100a28028900a0a1c81,0x100a7a2a99])]
def b11 : List (List Nat × List (Nat × Nat)) := [([6,31,512,4329604,25977624,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839450491410,0x1361a8d86236148d851,0x145224d872361c4d86d,0x4d89d15a69148a]),([6,31,512,5412005,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c8ea7239bb04aec10,0x19c9a672629c94a7251,0x1bb226ec8287206726a,0x4ee9e36276ec8a]),([6,31,992,1082401,2164802,4329604,9436424,33047056],[]),([6,31,992,1082401,2164802,4329604,17825296,32776456],[]),([6,31,992,1082401,3144770,8659208,17318416,32641156],[]),([6,31,992,1555951,2164802,8659208],hh [0x1158185604158085600,0x115838560c158285608,0x1158e85639020480810,0x1022245669159485651,0x173a69ce99022585691]),([6,31,992,1826551,2164802,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39020480810,0x124a34088a271a49c55,0x1bca697299022589c91]),([6,31,992,2164802,8659208,23609872],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x1271c89c71271a49c51,0x102268089924a34568a])]
def b12 : List (List Nat × List (Nat × Nat)) := [([6,31,992,2164802,8659208,31998480],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x1271c89c71271a49c51,0x102268089924a34568a]),([6,31,992,2164802,14950664,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x124a34568a271a49c51,0x102268089915a485691]),([6,31,992,2164802,17318416,31727880],hh [0x1158185604158085600,0x115838560c158285608,0x1158e85639270489c10,0x1159c4566d159a85651,0x1022680899992245672]),([6,31,992,3179553,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1560e95839450491410,0x1561c95871531a55851,0x12f2651492452351482]),([6,31,992,3213378,8659208,33047056],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x1271c89c71271a49c51,0x102268089924a34568a]),([6,31,992,3213378,17318416,32776456],hh [0x1158185604158085600,0x115838560c158285608,0x1158e85639270489c10,0x1159c4566d159a85651,0x102268089989a245672]),([6,31,992,3247203,4329604,32810281],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d8397e049f810,0x1361c4d86a361a4d851,0x4709938a24d872]),([6,31,992,3247203,4329604,33080881],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839498492610,0x1361c4d86936148d851,0x12f265589571234d872])]
def b13 : List (List Nat × List (Nat × Nat)) := [([6,31,992,3247203,5412005,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1a80eaa03936048d810,0x13620a9e699d146a04a,0x11c2667289]),([6,31,992,3247203,5412005,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1610e9843936048d810,0x15f9a5585261145844a,0x12f26550959ca34d882]),([6,31,992,3247203,6494406,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1a80eaa039018480610,0x19ca2402829c9a67451,0x47099]),([6,31,992,3247203,6494406,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1610e98439008480210,0x19ca3402825f9a58451,0x4bc99]),([6,31,992,3247203,8659208,33080881],hh [0x129818a60429808a600,0x129838a60c29828a608,0x1298e8a6391c0487010,0x1299c8a671299a4a651,0x40e9a03a64a68d]),([6,31,992,3247203,9741609,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f0e8bc39190486410,0x12c234648a2f1a4bc51,0x1032680c99]),([6,31,992,3247203,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f0e8bc39020480810,0x12f1a4bc522f144a04a,0x10d2649c952c234088a]),([6,31,992,3247203,17318416,32810281],hh [0x1190186404190086400,0x119038640c190286408,0x1190e864392f048bc10,0x1191c4646d191a86451,0x1032680c99382246472])]
def b14 : List (List Nat × List (Nat × Nat)) := [([6,31,992,3247203,18400817,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c0e8703929848a610,0x103a666e891c1b47051,0x40e9a]),([6,31,992,3247203,19483218,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c0e87039020480810,0x19ba24706d1c1445c4a,0x63699]),([6,31,992,4329604,7373857,17318416],hh [0x136018d80436008d800,0x145039140c36028d808,0x1360e8d83936048d810,0x136234d882389a4d851,0x127264d8922f244d88e,0x5ce9a]),([6,31,992,4329604,9403358,17318416],hh [0x1550195404550095400,0x155039540c550295408,0x1550e95439020480810,0x1022340882529b55451,0x5149902248bc91]),([6,31,992,4329604,17318416,24151073],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839550495410,0x1361c4d86d36188d851,0x49c9a38a24d872]),([6,31,992,4329604,25707024,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839548495210,0x1361c4d86d36188d851,0x49c9a38a24d872]),([6,31,992,4329604,25977624,32810281],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839158485610,0x1361c8d871361b4d851,0x4e289]),([6,31,992,4329604,25977624,33080881],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839270489c10,0x1361c4d86d361a8d851,0x4d89d71234d872])]
def b15 : List (List Nat × List (Nat × Nat)) := [([6,31,992,5412005,6291456,17318416],hh [0x1a901aa404a900aa400,0x136038d80ca902aa408,0x1a90eaa439a904aa410,0x19a1a4d862361869651,0x1a923a688da9208d86a,0x136268d899a92489c91]),([6,31,992,5412005,6494406,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1a80eaa039ae04ab810,0x1ae20a7269a818a9e51,0x67289]),([6,31,992,5412005,6494406,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1610e98439b084ac210,0x1561a97e69611897e51,0x4d89d9ca36c282]),([6,31,992,6291456,10824010,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39020480810,0x1271489c51271289c49,0x102244928d022289c69,0x6a49aa92640892]),([6,31,992,8659208,21648020,33080881],hh [0x129818a60429808a600,0x129838a60c29828a608,0x1298e8a639228488a10,0x1299b4a65229944a64a,0x122a48a68d299c8a671,0x4a695]),([6,31,992,9741609,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f0e8bc39048481210,0x12f1a4bc522f144a04a,0x12725412922c234128a]),([6,31,992,12718212,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839550495410,0x1361c4d86d36188d851,0x49c9a38a24d872]),([6,31,992,12988812,17318416,32810281],hh [0x1190186404190086400,0x119038640c190286408,0x1190e86439550495410,0x1191c4646d191886451,0x49c9a382246472])]
def b16 : List (List Nat × List (Nat × Nat)) := [([6,31,992,12988812,21648020,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d839498492610,0x138a24d86d36148d851]),([6,31,992,12988812,25977624,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d8391c0487010,0x127268e289361b4d851]),([6,31,992,18400817,19483218,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c0e87039050481410,0x19ba24706d1c1545c4a,0x41492]),([6,31,992,21648020,25977624,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1360e8d8392e048b810,0x138a24d86d361a8d855,0x4569a]),([6,31,31744,1082401,2165730,4329604,9412872,33047056],[]),([6,31,507375,1082401,2165730,4329604],hh [0x1458191604458091600,0x145839160c458291608,0x145945163a37048dc10,0x1372391672451a91462,0x514998024a0091]),([6,31,507375,1083361,2164802,8659208],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x11b144564a040481010,0x1042386c891b1c45652,0x5f89a7e2645691]),([6,31,507887,1082401,2164802,8659208],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c4a050481410,0x11c22470721c1c45652,0x14d264149215a44148e,0x5349a])]
def b17 : List (List Nat × List (Nat × Nat)) := [([6,31,777975,1082401,2164802,4330468],hh [0x14d01934044d0093400,0x14d039340c4d0293408,0x14d145303aad84ab610,0x1a1a3934724d1c52e62,0x4149aada4ab491]),([6,31,1047552,1082401,2165730,4329604,8659208,33047056],[]),([6,31,1047552,1082401,2165730,8659208,17318416,32641156],[]),([6,31,1048575,1082401,2164802,4330116],hh [0x1498192604498092600,0x149839260c498292608,0x1498f5263a3c048f010,0x1499c5146a491892651,0x14fa493e913c2392672,0x1052691499]),([6,31,1048575,1082913,2164802,4329604],hh [0x1498192604498092600,0x149839260c498292608,0x1498f5263a3c048f010,0x1499c5146a491892651,0x14fa493e913c2392672,0x1052691499]),([6,31,1049088,2164802,8659208,33047056],hh [0x1248189204248089200,0x124838920c248289208,0x1248e89239158485610,0x1249a89269249489251,0x124a34568a249c89271,0x1022680899]),([6,31,1049568,2164802,8659208,33047056],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x1271c89c71271a49c51,0x102268089924a34568a]),([6,31,1082401,2097152,4330116,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1451291449450491410,0x1059a81669451491451,0x14520a1681361c8d871,0x136265149545249148a,0x5149e])]
def b18 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2097664,4329604,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1451291449450491410,0x1059a81669451491451,0x14520a1681361c8d871,0x145278d89945249148a]),([6,31,1082401,2097664,4329604,33047056],hh [0x1450191404450091400,0x136038d80c450291408,0x1451291449450491410,0x1059a81669451491451,0x1452291482361c8d871,0x145278b099452551492]),([6,31,1082401,2098144,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1561295849450491410,0x1531c5586a561a55852,0x12f2651495452291482]),([6,31,1082401,2164802,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,31,1082401,2164802,4330116,32505887],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9281c49498492610,0x19c9a66c619c94a7251,0x149a0a72729c9c6726a,0x5169549a2a7285]),([6,31,1082401,2164802,4330116,32539681],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a5c3a498492610,0x19c9aa72699c94a7251,0x149a2926829c9ca7271,0x4169945256728d]),([6,31,1082401,2164802,4330116,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a4d0493410,0x19c9c6726a9c9a67252,0x145255348a4c20a7272,0x47099]),([6,31,1082401,2164802,4330148,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9a1a67252,0x149a292682872067272,0x171a651495])]
def b19 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,4330180,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79469e4a498492610,0x19c9ca9e6aa79a69e52,0x19ca65268a49a0a1c81]),([6,31,1082401,2164802,4330212,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79469e4a498492610,0x19c9ca9e6aa59a69e52,0x19ca65268a49a0a1c81]),([6,31,1082401,2164802,4330468,32506112],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71469c4a4b0492c10,0x19b9ca9c6aa51a69c52,0x19ba652c8a4b20a1c81]),([6,31,1082401,2164802,4330468,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71469c4a4d0493410,0x19b9ca9c6aa51a69c52,0x470994d2293082]),([6,31,1082401,2164802,4330468,32776479],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71282e494c0493010,0x1a51a69a61a714a9c51,0x1a721530829b9ca9c6a,0x5308a]),([6,31,1082401,2164802,4330468,32810281],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71469c4a4d0493410,0x14c20a6e72a71aa9c52,0x47099a7235348a]),([6,31,1082401,2164802,5412517,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a498492610,0x19c9b6726a9c94a7251,0x149a0a1c819c9ca7271,0x105a6514959a235268a]),([6,31,1082401,2164802,5412837,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a712a9c3a4d0493410,0x1a71b69c6aa714a9c51,0x1a5235348a4c20a6e72,0x47099])]
def b20 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,6494918,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9d672729c9aa7269,0x19ca65268a49a0a1c81,0x5269e]),([6,31,1082401,2164802,6495206,32776456],hh [0x19b81a6e049b80a6e00,0x19b83a6e0c9b82a6e08,0x19b94a6e514d0493410,0x19b9d66e729b9aa6469,0x14b27870994d2293082]),([6,31,1082401,2164802,8659208,33046544],hh [0x12c018b0042c008b000,0x12c038b00c2c028b008,0x12c144983a1c0487010,0x12c1c4b06a2c1a4b052,0x105264928d1c228b072,0x4149a]),([6,31,1082401,2164802,12989420,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c144704a4d0493410,0x11c1c8706a1b1a47052,0x11c265348a]),([6,31,1082401,2164802,16236527,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c3a4d0493410,0x11c1c8706d1c1a87052,0x11c264568d4d2287075,0x5349e]),([6,31,1082401,2164802,17317904,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c3a2c048b010,0x11c1c4706a1c1a47052,0x105264568d2c2287072,0x4149a]),([6,31,1082401,2164802,21107332,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,31,1082401,2164802,25977112,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a1c0487010,0x19c9c6726a9c9a67252,0x11c2287082872067272,0x4149a05266688d])]
def b21 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,29223963,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71469c4a2c048b010,0x19b9ca946da71aa9c52,0x686992c2287482]),([6,31,1082401,2164802,29224219,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79469e4a1c0487010,0x19c9ca966da79aa9e52,0x1b7264708a1c20a1c81]),([6,31,1082401,2164802,29224315,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a1c0487010,0x19c9ca726d9c9aa7252,0x11c2287082872067275,0x13c2641495]),([6,31,1082401,2164802,32505856,32641668],hh [0x1498192604498092600,0x149839260c498292608,0x149945244a3c048f010,0x1499a92662499852652,0x19ca48168a451d52672,0x5269d3c2691495]),([6,31,1082401,2164802,32506368,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x149945244a5f8497e10,0x1499a92662499852652,0x15fa497e8a451d52672,0x51495]),([6,31,1082401,2164802,32642020,32776456],hh [0x19b81a6e049b80a6e00,0x19b83a6e0c9b82a6e08,0x19b9466e4a4d0493410,0x19b9d66e729b9aa6e52,0x14b27870994d2293082]),([6,31,1082401,2164802,32776456,32912364],hh [0x14d01934044d0093400,0x14d039340c4d0293408,0x14d1452e4a1c0487010,0x11c248708a4d1a93452,0x5349d1c2692a95]),([6,31,1082401,2164831,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a7239490492410,0x19c9a672619c94a724d,0x14920924819c9c6726a,0x4ec9945255248a])]
def b22 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164831,4330468,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a712a9c394b8492e10,0x1a51a69c61a714a9c4d,0x14ba292e824ba069c6a,0x47099]),([6,31,1082401,2165058,4330468,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79469e4a4b0492c10,0x19c9ca9e6aa59a69e52,0x19ca652c8a4b20a1c81]),([6,31,1082401,2165314,4329604,32506368],hh [0x1530194c04530094c00,0x1530394c0c530294c08,0x1531454c4a498492610,0x1531c54c6a531a54c52,0x149a292682872054c72,0x13c2651495]),([6,31,1082401,2165314,4329604,33047056],hh [0x1530194c04530094c00,0x1530394c0c530294c08,0x1531454c4a498492610,0x1531c54c6a531a54c52,0x145255268a49a094c72,0x4b099]),([6,31,1082401,2165314,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x145255268a49a0a1c81,0x4f099]),([6,31,1082401,2165314,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x149a0a1c819c9aa7269,0x5269e9ca65268a]),([6,31,1082401,2165314,8659208,33047056],hh [0x12c018b0042c008b000,0x12c038b00c2c028b008,0x12c144983a1c0487010,0x12c1c4b06a2c1a4b052,0x105264928d1c228b072,0x4149a]),([6,31,1082401,2165314,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c3a2c048b010,0x12c228706a1c1a47052,0x4149a05264568d])]
def b23 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2165314,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a1c0487010,0x187206726a9c9a67252,0x105266688d1c2287082,0x4149a]),([6,31,1082401,2165730,4329604,9436424,17318416,32505856],[]),([6,31,1082401,2165730,4329604,32506368],hh [0x1560195804560095800,0x156039580c560295808,0x156149584a458491610,0x1872054c71561a95869,0x137265149545a291682]),([6,31,1082401,2165730,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156149584a458491610,0x145a094c71561a95869,0x4bc9945255168a]),([6,31,1082401,2165730,4329604,33047071],hh [0x1560195804560095800,0x156039580c560295808,0x1561282249458491610,0x1561a95869559855852,0x145a29588545a094c71,0x51695]),([6,31,1082401,2165730,4329604,33080881],hh [0x1560195804560095800,0x156039580c560295808,0x139145584a458491610,0x1531c5586a561a55852,0x145255588d45a291682,0x4bc99]),([6,31,1082401,2165730,4330116,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a094a824a458491610,0x1872067271a09aa8269,0x137265149545a291682]),([6,31,1082401,2165730,5412005,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156129583a458491610,0x1561b5586a561495851,0x154235168a45a094c71,0x12f2651495])]
def b24 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2165730,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f128a03a1b8486e10,0x12f1a8bc692f148bc51,0x108264b095272346e8a]),([6,31,1082401,2165730,21648020,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f148bc4a458491610,0x12c255168a2f1a8bc69,0x4bc99]),([6,31,1082401,2165730,29224827,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156149584a1b8486e10,0x11ba094c75561b5586a,0x4dc99052546e8a]),([6,31,1082401,2165730,32641156,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156149584a458491610,0x145255168a45a09586a,0x4bc99]),([6,31,1082401,2165730,33047056,33182356],hh [0x1458191604458091600,0x145839160c458291608,0x145949144a2f048bc10,0x12f2291475459c9166a,0x5169d2f269dc95]),([6,31,1082401,2165759,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156135584a450491410,0x1531c5586a561a55852,0x145255148a452091481,0x4bc99]),([6,31,1082401,2194498,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x18720672719c9aa7269,0x13c265149549a292682]),([6,31,1082401,3144770,4329604,8659944,17318416,32505856],[])]
def b25 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,3247203,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x19c9c6726a9c9a67255,0x149a252682872067272,0x4d89945255268a]),([6,31,1082401,3247203,4330468,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a714a9c4a4d0493410,0x14c20a6e72a71aa9c55,0x470994d2293489]),([6,31,1082401,3248099,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156149584a458491610,0x1531c5586a561a55855,0x145255168a45a251682,0x4bc99]),([6,31,1082401,4329604,6495206,33047056],hh [0x1530194c04530094c00,0x1530394c0c530294c08,0x1531494c51450491410,0x1531d54c72531a94c62,0x145279149d452291482]),([6,31,1082401,4329604,31388701,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1561495851458491610,0x145a094c72561a95862,0x5149d2f245168a]),([6,31,1082401,4330116,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca726a9c9a67262,0x145275148a4520a1c81,0x5149e]),([6,31,1082401,4330116,6494918,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca726a9c9a67262,0x1452291482872067275,0x145279149d]),([6,31,1082401,4330116,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca726a9c9a67262,0x14522914894520a1c81,0x19ca75b29a])]
def b26 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,4330116,31389629,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9ca726d9c9aa7262,0x149a292682872067275,0x145274f091]),([6,31,1082401,4330468,31389629,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a714a9451478491e10,0x19b9d69c6da71aa9c62,0x4709147a291e82]),([6,31,1082401,6495206,10824010,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a6851050481410,0x18720672769c9aa7269,0x41496052281482]),([6,31,1082401,6495206,21648020,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9a67252450491410,0x14520a1c819c9da726a,0x145259148a]),([6,31,1082401,8659208,21107332,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a450491410,0x19c9c6726a9c9a67252,0x1452251482872067272,0x6729545249148a]),([6,31,1082401,8659944,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f128a03a050481410,0x12f1a8bc692f148bc51,0x12c254149227234148a]),([6,31,1082401,8659944,21648020,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f148bc4a450491410,0x14522914892f1a8bc69,0x12c2551492]),([6,31,1082401,10824010,12989420,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a794a9e514d0493410,0x14d20a1c81a79aa9669,0x5348a])]
def b27 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,12989420,21648020,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79a69e52458491610,0x145a251682872069e6a,0x5168a]),([6,31,1082913,2097152,4329604,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1451291449450491410,0x1059a81669451491451,0x14520a1681361c8d871,0x136265149545249148a,0x5149e]),([6,31,1082913,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,31,1082913,2164802,4329604,32505887],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9281c49498492610,0x19c9a66c619c94a7251,0x149a0a72729c9c6726a,0x5169549a2a7285]),([6,31,1082913,2164802,4329604,32506368],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682502067272,0x13c2651495]),([6,31,1082913,2164802,4329604,32539681],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a5c3a498492610,0x19c9aa72699c94a7251,0x149a2926829c9ca7271,0x105a651495]),([6,31,1082913,2164802,4329604,32540193],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a5c3a498492610,0x19c9aa72699c94a7251,0x149a2926829c9ca7271,0x4169945256728d]),([6,31,1082913,2164802,4329604,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a4d0493410,0x19c9c6726a9c9a67252,0x145255348a4c20a7272,0x47099])]
def b28 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,2164802,4329604,33047056],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x145255268a49a0a7272,0x4b099]),([6,31,1082913,2164802,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,31,1082913,2164802,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a498492610,0x19c9c6726a9c94a7251,0x149a292682872067272,0x105a651495]),([6,31,1082913,2164802,5412517,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a498492610,0x19c9b6726a9c94a7251,0x149a0a1c819c9ca7271,0x105a6514959a235268a]),([6,31,1082913,2164802,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9d672729c9aa7269,0x19ca65268a49a0a1c81,0x5269e]),([6,31,1082913,2164802,8659208,33047056],hh [0x12c018b0042c008b000,0x12c038b00c2c028b008,0x12c144983a1c0487010,0x12c1c4b06a2c1a4b052,0x105264928d1c228b072,0x4149a]),([6,31,1082913,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c3a2c048b010,0x11c1c870711c1a87052,0x4149a05264b08a]),([6,31,1082913,2164802,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a1c0487010,0x19c9ca72719c9aa7252,0x105264708a1c20a1c81,0x4149a])]
def b29 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,2164802,29224827,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a1c0487010,0x19c9ca726d9c9aa7252,0x11c2287082872067275,0x13c2641495]),([6,31,1082913,2164802,32505856,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x149945244a3c048f010,0x1499a92662499852652,0x19ca48168a451d52672,0x5269d3c2691495]),([6,31,1082913,2164831,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a7239490492410,0x19c9a672619c94a724d,0x14920924819c9c6726a,0x4ec9945255248a]),([6,31,1082913,2165314,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x19c9ca72719c9aa7269,0x145255268a49a0a1c81,0x4f099]),([6,31,1082913,2165730,4329604,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a094a824a458491610,0x1872067271a09aa8269,0x137265149545a291682]),([6,31,1082913,2194498,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x18720672719c9aa7269,0x13c265149549a292682]),([6,31,1082913,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x19c9ca72719c9aa7269,0x149a29268949a0a1c81,0x1362651495]),([6,31,1082913,3247715,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x19c9c6726a9c9a67255,0x149a252682872067272,0x4d89945255268a])]
def b30 : List (List Nat × List (Nat × Nat)) := [([6,31,1082913,4329604,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca726a9c9a67262,0x1452291482872067275,0x145279149d]),([6,31,1082913,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca72719c9aa7262,0x14522914894520a1c81,0x19ca75149a]),([6,31,1082913,4329604,31389629,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9ca726d9c9aa7262,0x149a292682872067275,0x145274f091]),([6,31,1082977,2164802,4329604,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x19c9469e4a498492610,0x1a79ca9e71a79aa9e69,0x1b6a65268a49a0a1c81]),([6,31,1083041,2164802,4329604,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a0946824a78049e010,0x1a09c6826a9c9a68252,0x178229e082872068272,0x13c265dc95]),([6,31,1083105,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a0946b04a78049e010,0x1ac1cab071ac1aa9e69,0x1b6a65e08a7820a1c81]),([6,31,1083361,2164802,4329604,33080881],hh [0x13d818f6043d808f600,0x13d838f60c3d828f608,0x13d944f64a498492610,0x13d9c8f6713d1a4e452,0x12f264e4959ca352682]),([6,31,1083361,2164802,4330468,32776456],hh [0x1a501a9404a500a9400,0x1a503a940ca502a9408,0x1a5146944a7e049f810,0x5f482a51ca9469])]
def b31 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,5412005,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1a812aa03a7e049f810,0x17d20aa072a81c67451]),([6,31,1083361,2164802,5412005,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x161129843a3c848f210,0x1611c98471561498451,0x12f26558959a234f282]),([6,31,1083361,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f144a03a1b0486c10,0x11b228bc722f1c4bc69,0x4109a04264928d]),([6,31,1083361,2164802,8659208,33047536],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f1a4a03a1b0486c10,0x1272346c8a2f1c8bc71,0x4109a]),([6,31,1083361,2164802,8659208,33080881],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f1a4bc511c0487010,0x12c2346c8a2f1c8bc71,0x1052681499]),([6,31,1083361,2164802,8659208,33081329],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f1c4bc691b0486c10,0x104268bc8d1b228bc72]),([6,31,1083361,2164802,8659208,33317656],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f144a03a040481010,0x12f1c4786e2f1a47a62,0x104268928d04228bc72,0x4bc9d]),([6,31,1083361,2164802,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f128a03a1b0486c10,0x12f1c8bc692f148bc51,0x12f254928d1b228bc75,0x42499])]
def b32 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,12988812,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c144704a7e049f810,0x470721c1c47069]),([6,31,1083361,2164802,17318896,32776456],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x11b144563a2f048bc10,0x46c72]),([6,31,1083361,2164802,18400817,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1b470512f048bc10,0x4149a1c1c87071]),([6,31,1083361,2164802,24895223,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f144a03a3c848f210,0x13ca28bc752f1c8bc6d,0x4f29e2f264928d]),([6,31,1083361,2164802,25977624,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x19d146a03a2f048bc10,0x47a82a81caa071]),([6,31,1083361,2164802,25977624,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x161145843a1b0486c10,0x19a2346c82611c98471,0x41099]),([6,31,1083361,2164802,32641156,32776456],hh [0x17e019f8047e009f800,0x1b683ada0c7e029f808,0x17e145f24a7e049f810,0x5f8927d20a9472]),([6,31,1083361,2164802,32776456,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f144a03a1b0486c10,0x1042646c9224a34bc72])]
def b33 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,2164802,33047056,33317656],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x11b144563a040481010,0x11b1c86c6e159b46c62,0x11b274109a09248588d]),([6,31,1083361,2165058,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a0946b04a7b049ec10,0x1ac1cab071ac1aa9e69,0x1b6a65ec8a7b20a1c81]),([6,31,1083361,6494406,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac14a7251048481210,0x104a281282872068269,0x41296]),([6,31,1083361,6494406,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a79a67251450491410,0x145259148a4520a1c81]),([6,31,1083361,8659208,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f128a03a040481010,0x12f1c8bc692f148bc51,0x104248928d04228bc75,0x4bc95]),([6,31,1083361,8659208,31389629,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f144a03a36848da10,0x136a28bc752f1c8bc6d,0x4da9236a44928d]),([6,31,1083361,10824010,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a79a682517e049f810,0x17e229f88287206b06a]),([6,31,1083361,10824010,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a0946b03a2f048bc10,0x12f228bc8287206b06a])]
def b34 : List (List Nat × List (Nat × Nat)) := [([6,31,1083361,10824010,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a0946b03a2f048bc10,0x12f228bc8287206b06a,0x4109a]),([6,31,1083361,19483218,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x187206b03a1b0486c10,0x4109a1b2286c82]),([6,31,1083391,2164802,8659208,33047056],hh [0x128018a00428008a000,0x128038a00c28028a008,0x1280f4a03a158485610,0x1281c8a071281a4a051,0x102268089999a345681]),([6,31,2164802,3247203,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9567252498492610,0x19c9ca72719c9aa7269,0x13c265268949a0a1c81]),([6,31,2164802,3247203,4330468,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1a71569c524d0493410,0x14c20a6e72a51c66e6a,0x11c2653489]),([6,31,2164802,3247715,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9567252498492610,0x19c9ca72719c9aa7269,0x13c265268949a0a1c81]),([6,31,2164802,3248099,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f148a04a1b0486c10,0x12f1c4bc6a2f1a4bc55,0x102268089924a546c89]),([6,31,2164802,4329604,5412517,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a3c048f010,0x19c9aa72699c94a7251,0x13c20a1c819c9d67272,0x13c254d88d])]
def b35 : List (List Nat × List (Nat × Nat)) := [([6,31,2164802,4329604,25977112,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a158485610,0x19c9c6726a9c9a67252,0x115a245682872067272,0x1022685695]),([6,31,2164802,4329604,32471326,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac146b03a158485610,0x1ac1d69e72a09aab052,0x115a78569115a0a1c81]),([6,31,2164802,4329604,32471518,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a158485610,0x19c9ca726d9c9aa7252,0x1022345682872067275,0x115a785691]),([6,31,2164802,4330116,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a3c048f010,0x19c9aa72699c94a7251,0x136234f082872067272]),([6,31,2164802,4330116,5412517,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a3c048f010,0x19c9aa72699c94a7251,0x13c20a1c819c9d67272,0x13c254d88d]),([6,31,2164802,4330116,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a158485610,0x19c9ca726a9c9a67252,0x16b268568915a0a1c81]),([6,31,2164802,4330116,32472030,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a158485610,0x19c9ca726d9c9aa7252,0x1022345682872067275,0x115a785691]),([6,31,2164802,4330468,5412005,32776456],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1a592a963a73849ce10,0x1a51ca966aa59a66852,0x5cc82])]
def b36 : List (List Nat × List (Nat × Nat)) := [([6,31,2164802,4330468,5412005,33047056],hh [0x15e8197a045e8097a00,0x15e8397a0c5e8297a08,0x15e9297a3a3c048f010,0x15e9a97a695e9494851,0x4f09552234f082]),([6,31,2164802,4330468,5412837,32776456],hh [0x1a501a9404a500a9400,0x1a503a940ca502a9408,0x1a512a943a73849ce10,0x1a51d69472a51aa9452,0x13f255cc82]),([6,31,2164802,4330468,25977624,32776456],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x19a14a964a270489c10,0x11820a9472a59aa9669,0x49c89]),([6,31,2164802,4330468,25977624,33047056],hh [0x15e8197a045e8097a00,0x15e8397a0c5e8297a08,0x15e9497a4a158485610,0x115a2456825e9a97a69,0x45695]),([6,31,2164802,4330468,32472030,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x19b94a9c3a270489c10,0x1a71d69472a71b69c6a,0x49c9e1c2446082]),([6,31,2164802,8659208,9742313,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f148bc51158485610,0x12f1d4bc722f1a8a062,0x4929d3f2681092]),([6,31,2164802,8659208,32471070,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f148bc511b0486c10,0x104244bc722f1a8a062,0x46c9e15a741092]),([6,31,2164802,12989420,17318416,32776456],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x11b148564a270489c10,0x1272246c721b1a86c69,0x5889a])]
def b37 : List (List Nat × List (Nat × Nat)) := [([6,31,2165314,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9aa7269498492610,0x149a0a1c819c9ca7271,0x13c2662c89]),([6,31,2165314,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a158485610,0x18720672729c9c67252,0x10226856958b2245682]),([6,31,2165730,4329604,5412005,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x156129583a37048dc10,0x1561c94c69561494c51,0x137254d88d372095875]),([6,31,2165730,4329604,32472030,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x153145583a150485410,0x1152095875561c9586d,0x4549e2f244088d]),([6,31,2165730,5412005,18400817,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x19c946823a458491610,0x145a691682872068262]),([6,31,2165730,5412005,21648020,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x19c946823a580496010,0x56082872068262]),([6,31,2165730,18400817,21648020,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x187206823a240489010,0x1242489082]),([6,31,3247203,4330468,8659208,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136148d83a4d0493410,0x1361c4d86a361a4d862,0x14d269349938a44d876])]
def b38 : List (List Nat × List (Nat × Nat)) := [([6,31,3247203,4330468,9741609,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79c6725236048d810,0x14d26672913620a1c81,0x5349a]),([6,31,3247203,4330468,10824010,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x19c94a9651020480810,0x19ca440882872067271,0x53499]),([6,31,3248099,4329604,10824010,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a094a7251020480810,0x1872068272a09c6826e,0x5f899022440882]),([6,31,3248099,4329604,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d83a458491610,0x1361c8d871361b8d862,0x5169a45a641691]),([6,31,3248099,4329604,18400817,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a09ba725136048d810,0x13620a1c81a09ca8271,0x5169a45a64d891]),([6,31,3248099,5412005,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a098a823a36048d810,0x1872068272a09c6826e,0x136268d89905a44d882]),([6,31,3248099,10824010,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a09aa823a2f048bc10,0x12f20a1c81a09ca8271,0x4089a02264bc91]),([6,31,4329604,8659208,16777728,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d84a528494a10,0x1361a4d86236184d852,0x152a48d872361c4d86a,0x4d895])]
def b39 : List (List Nat × List (Nat × Nat)) := [([6,31,4329604,8659720,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d84a5f0497c10,0x1361a8d86936188d852,0x124a697c92]),([6,31,4329604,9742313,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a794ab051150485410,0x11520a1c81ac1aab069,0x1152485489]),([6,31,4329604,9742313,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac1a69e5237048dc10,0x137248dc8287206b06a,0x5029a]),([6,31,4330116,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d84a450491410,0x1361c4d86a36188d852,0x124a68d89515a48d872,0x4d89d]),([6,31,4330468,8659208,21648020,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d84a468491a10,0x1361c4d86d36188d852,0x1362551a9238a24d872]),([6,31,4330468,9741609,10824010,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a594a9e51158485610,0x19ca245682872067269,0x45692]),([6,31,4330468,10824010,19483218,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x19a146963a270489c10,0x49c8287206966a]),([6,31,4330468,10824010,25977624,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x19a146963a270489c10,0x1272449c8287206966a,0x5ae9a])]
def b40 : List (List Nat × List (Nat × Nat)) := [([6,31,4330468,19483218,25977624,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x187206963a158485610,0x4089a15a445682]),([6,31,5412005,6495206,17318416,32505856],hh [0x19a01a68049a00a6800,0x19a03a680c9a02a6808,0x19a18a684a69849a610,0x18720668769a1aa6869,0x169a69a69936a59a682]),([6,31,5412005,8659944,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a794ab04a5c8497210,0x15ca49728287206b062,0x5b89a]),([6,31,5412005,8659944,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a794ab04a580496010,0x158225608287206b062,0x56092]),([6,31,5412005,9742313,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac18ab04a5c8497210,0x15ca0a1c81ac1aab069,0x16e2697292]),([6,31,5412005,12989420,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1a598a964a5c8497210,0x15ca0a1c81a59aa9669,0x16e2696489]),([6,31,6495206,10824010,17318416,32505856],hh [0x19a01a68049a00a6800,0x19a03a680c9a02a6808,0x19a1aa683a270489c10,0x12720a1c819a1ca6871,0x16ba689c8e]),([6,31,8659944,18400817,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x187206b03a228488a10,0x122a488a9122a288a82])]
def b41 : List (List Nat × List (Nat × Nat)) := [([6,31,9742313,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac1aab03a2f048bc10,0x12f20a1c81ac1cab071,0x4109a04264bc8a]),([6,31,10824010,12989420,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1a59a6964a270489c10,0x12720a1c81a59ca966a,0x16ba689c89]),([6,287,1082401,2164802,4330468,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a79469e4a4b0492c10,0x19c9ca9e6aa59a69e52,0x19ca652c8a4b20a1c81]),([6,287,1083361,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1a0946b04a7b049ec10,0x1ac1cab071ac1aa9e69,0x1b6a65ec8a7b20a1c81]),([6,512,1082401,2097183,4329604,32505856],hh [0x1450191404450091400,0x105838160c450291408,0x1450e91439450491410,0x1059881661451291449,0x1452091481059a81669,0x14527a529945249148a]),([6,512,1082401,2164802,32505887,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x1498e92639058481610,0x1499492651499292649,0x105a051675499892661,0x5149505a481682]),([6,512,1082401,2164831,4329604,32505887],hh [0x1070181c04070081c00,0x1070381c0c070281c08,0x1070e81c39490492410,0x1071881c61071281c49,0x1492041a71071a81c69,0x51495492292482]),([6,543,1048575,1082401,2164802,4329604],hh [0x1498192604498092600,0x149839260c498292608,0x1498f5263a3c048f010,0x1499c5146a491892651,0x14fa493e913c2392672,0x1052691499])]
def b42 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2097152,4329604,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1451291449450491410,0x1059a81669451491451,0x14520a1681361c8d871,0x136265149545249148a,0x5149e]),([6,543,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,543,1082401,2164802,4329604,32505887],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9281c49498492610,0x19c9a66c619c94a7251,0x149a0a72729c9c6726a,0x145a55268a]),([6,543,1082401,2164802,4329604,32506368],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x145255268a49a0a7272,0x54299]),([6,543,1082401,2164802,4329604,32506399],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9281c49498492610,0x19c9a66c619c94a7251,0x149a0a72729c9c6726a,0x5169549a2a7285]),([6,543,1082401,2164802,4329604,32539681],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a5c3a498492610,0x19c9aa72699c94a7251,0x149a2926829c9ca7271,0x4169945256728d]),([6,543,1082401,2164802,4329604,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a4d0493410,0x19c9c6726a9c9a67252,0x145255348a4c20a7272,0x47099]),([6,543,1082401,2164802,4329604,33047056],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x145255268a49a0a7272,0x4b099])]
def b43 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2164802,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a498492610,0x19c9b6726a9c94a7251,0x149a0a1c819c9ca7271,0x105a6514959a235268a]),([6,543,1082401,2164802,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9d672729c9aa7269,0x19ca65268a49a0a1c81,0x5269e]),([6,543,1082401,2164802,8659208,33047056],hh [0x12c018b0042c008b000,0x12c038b00c2c028b008,0x12c144983a1c0487010,0x12c1c4b06a2c1a4b052,0x105264928d1c228b072,0x4149a]),([6,543,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c1445c3a2c048b010,0x11c1c4706a1c1a47052,0x105264568d2c2287072,0x4149a]),([6,543,1082401,2164802,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a1c0487010,0x19c9c6726a9c9a67252,0x11c2287082872067272,0x4149a05266688d]),([6,543,1082401,2164802,29224827,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a1c0487010,0x19c9ca726d9c9aa7252,0x11c2287082872067275,0x13c2641495]),([6,543,1082401,2164802,32505856,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x149945244a3c048f010,0x1499a92662499852652,0x19ca48168a451d52672,0x5269d3c2691495]),([6,543,1082401,2164831,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a7239490492410,0x19c9aa72699c9867252,0x1492292482492067271,0x13b2651495])]
def b44 : List (List Nat × List (Nat × Nat)) := [([6,543,1082401,2165314,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a498492610,0x19c9c6726a9c9a67252,0x149a292682872067272,0x13c2651495]),([6,543,1082401,2165343,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a7239490492410,0x19c9a672619c94a724d,0x14920924819c9c6726a,0x4ec9945255248a]),([6,543,1082401,2165730,4329604,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a094a824a458491610,0x1872067271a09aa8269,0x137265149545a291682]),([6,543,1082401,2194498,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x18720672719c9aa7269,0x13c265149549a292682]),([6,543,1082401,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a724a498492610,0x19c9c6726a9c9a67255,0x149a252682872067272,0x4d89945255268a]),([6,543,1082401,4329604,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9ca726a9c9a67262,0x1452291482872067275,0x145279149d]),([6,543,1082401,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251450491410,0x19c9c6726a9c9a67262,0x1452251482872067272,0x6729d45269148a]),([6,543,1082401,4329604,31389629,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c94a7251498492610,0x19c9ca726d9c9aa7262,0x149a292682872067275,0x145274f091])]
def b45 : List (List Nat × List (Nat × Nat)) := [([6,543,2164802,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c9567252498492610,0x19c9ca72719c9aa7269,0x13c265268949a0a1c81]),([6,543,2164802,4329604,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c92a723a3c048f010,0x19c9aa72699c94a7251,0x13c20a1c819c9d67272,0x13c254d88d]),([6,543,2164802,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946724a158485610,0x19c9c6726a9c9a67252,0x115a245682872067272,0x1022685695]),([6,543,2164802,4329604,32472030,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c946723a158485610,0x19c9ca726d9c9aa7252,0x1022345682872067275,0x115a785691]),([6,543,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136144d84a450491410,0x1361a8d86936188d852,0x1362545692361c8d871,0x136274929a]),([6,992,31744,1082431,2164802,4329604,9412872,33047056],[]),([6,992,31744,1082431,2164802,4329604,17809936,32776456],[]),([6,992,1047552,1082431,2164802,4329604,8659208,33047056],[])]
def b46 : List (List Nat × List (Nat × Nat)) := [([6,992,1047552,1082431,2164802,4329604,17318416,32776456],[]),([6,992,1048607,2164802,8659208,33047056],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270e89c39158485610,0x1271c89c71271849c49,0x102268089924a145682]),([6,992,1048607,2164802,17318416,32776456],hh [0x1158185604158085600,0x115838560c158285608,0x1158e85639270489c10,0x1159c45665159885649,0x1022680899992045672]),([6,992,1082401,2097183,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1561255839450491410,0x1561a9586953185584a,0x12f2651492452291485]),([6,992,1082401,2164802,4329631,8659208,17825296,32505856],[]),([6,992,1082401,2164802,4329631,8682760,17809936,32505856],[]),([6,992,1082401,2164802,4329631,9436424,17318416,32505856],[]),([6,992,1082401,2164831,4329604,32776479],hh [0x10c81832040c8083200,0x10c838320c0c8283208,0x10a0e832397c849f210,0x10c9a42e620c1841e49,0x17ca281c810c9c4326a])]
def b47 : List (List Nat × List (Nat × Nat)) := [([6,992,1082401,2164831,4329604,33047071],hh [0x10f0183c040f0083c00,0x10f0383c0c0f0283c08,0x1089243c39490492410,0x10f1a83c690c1843c4a,0x156255248a072143a71]),([6,992,1082401,2194498,4329631,8659208,17809936,32505856],[]),([6,992,1082401,2194498,4329631,9412872,17318416,32505856],[]),([6,992,1082401,3144770,4329631,8659208,17318416,32505856],[]),([6,992,1082401,4329604,6291487,17318416],hh [0x10d01834040d0083400,0x145039140c0d0283408,0x10b12424390d0483410,0x14518816610d1483451,0x10d2289c890d2181685,0x5149a0d248bc91]),([6,992,1082431,2164802,4329604,8659208,17825296,32505856],[]),([6,992,1082431,2164802,4329604,8682760,17809936,32505856],[]),([6,992,1082431,2164802,4329604,9436424,17318416,32505856],[])]
def b48 : List (List Nat × List (Nat × Nat)) := [([6,992,1082431,2194498,4329604,8659208,17809936,32505856],[]),([6,992,1082431,2194498,4329604,9412872,17318416,32505856],[]),([6,992,1082431,3144770,4329604,8659208,17318416,32505856],[]),([6,992,2164802,6291487,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1271249c39158485610,0x1271a89c69271849c4a,0x115a28568924a145682,0x10d2683499]),([6,992,4329604,8388639,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136124d839550495410,0x1361a8d86936194d84a,0x49c9a38a04d872]),([6,992,4329604,8659231,17318431,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136124d8390f8483e10,0x1361a8d86536148d84a,0x4e281]),([6,1023,1082401,2164802,4329604,33047071],hh [0x1058181604058081600,0x105838160c058281608,0x1059281649498492610,0x1059a41661059481651,0x19ca141672059c4166a,0x47e95]),([6,1023,1082401,2164802,8659208,33047536],hh [0x12a018a8042a008a800,0x12a038a80c2a028a808,0x12a1448c3a1a0486810,0x12a1c4a86a2a1a4a852,0x123234a872])]
def b49 : List (List Nat × List (Nat × Nat)) := [([6,1023,1082401,2164802,17318896,32776456],hh [0x11a01868041a0086800,0x11a038680c1a0286808,0x11a144523a2a048a810,0x114a34a88a1a1a46852]),([6,1023,4329604,8659208,17318431,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136124d839058481610,0x136194d85236144d84a,0x136254169236204d871]),([6,31744,1015808,1082431,2165730,4329604,8659208,33047056],hh [0x400a8]),([6,31744,1082401,2165730,4329631,9412872,17318416,32505856],[]),([6,31744,1082401,3115074,4329631,8659944,17318416,32505856],[]),([6,31744,1082431,2165730,4329604,9412872,17318416,32505856],[]),([6,31744,1082431,3115074,4329604,8659944,17318416,32505856],[]),([6,1047552,1082401,2164802,4329631,8659944,17318416,32505856],[])]
def b50 : List (List Nat × List (Nat × Nat)) := [([6,1047552,1082401,2165730,4329631,8659208,17318416,32505856],[]),([6,1047552,1082431,2164802,4329604,8659944,17318416,32505856],[]),([6,1047552,1082431,2165730,4329604,8659208,17318416,32505856],[]),([6,1047552,1083361,2164831,4329604,8659208],hh [0x17c819f2047c809f200,0x112038480c7c829f208,0x179129f2397c849f210,0x17aa088481419c4486a,0x11c265f2927aa385689,0x5269a]),([6,1047552,4329604,8659208,17318431,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136124d839058481610,0x136188d85236144d84a,0x105a48fa81361c4d865,0x4d895]),([6,1047552,4329604,8659208,17318896,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x101144043a230488c10,0x1012348c8a011a40452]),([6,1082401,2164802,4329604,16777759,32505856],hh [0x19781a5e049780a5e00,0x19783a5e0c9782a5e08,0x1978ea5e39058481610,0x19794a5e519792a5e49,0x105a44168d05a0a5a69,0x61c99]),([6,1082401,2164802,4329604,32505856,32506399],hh [0x1058181604058081600,0x105838160c058281608,0x1058e816398704a1c10,0x1059481651059281649,0x1059c81671059b4166a,0x4169d872687e8d])]
def b51 : List (List Nat × List (Nat × Nat)) := [([6,1082401,2164802,4329604,32505856,33553888],hh [0x132018c80432008c800,0x132038c80c32028c808,0x1320e8c8399c84a7210,0x132148c85132128c849,0x132a34c871321b4c862,0x132276729a]),([6,1082401,2164802,4329604,32505887,32506368],hh [0x15e01978045e0097800,0x15e039780c5e0297808,0x15e0e97839058481610,0x15e14978515e1297849,0x105a45448d05a29466d,0x41692]),([6,1082401,2164802,4330116,32505856,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x1058e816398704a1c10,0x1059481651059281649,0x1059c81671059b4166a,0x4169d872687e8d]),([6,1082401,2164802,4330116,32505856,33554400],hh [0x132018c80432008c800,0x132038c80c32028c808,0x1320e8c8399c84a7210,0x132148c85132128c849,0x132a34c871321b4c862,0x132276729a]),([6,1082401,2164802,4330468,32776456,33554400],hh [0x1438190e04438090e00,0x1438390e0c438290e08,0x1438e90e39a704a9c10,0x1439890c5233128d649,0x50e9d442350e71]),([6,1082401,2164802,8659208,32505887,32642020],hh [0x14c81932044c8093200,0x14c839320c4c8293208,0x14c8e932390b0482c10,0x14c94932514c9293249,0x14b2552a8d06a293071]),([6,1082401,2164831,4330468,8659208,32505887],hh [0x10c01830040c0083000,0x10c038300c0c0283008,0x10c1282a494b8492e10,0x10c1c4306a0c1883061,0x14ba692e994ba083076]),([6,1082401,2164831,4330468,8659231,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a59269e3a0b8482e10,0x19ca442e82a798a9e4a,0x14ba692e99])]
def b52 : List (List Nat × List (Nat × Nat)) := [([6,1082401,2165730,4329604,33047056,33554400],hh [0x16f019bc046f009bc00,0x16f039bc0c6f029bc08,0x16f124c83a560495810,0x1321b5bc6243145bc4a,0x5bc9d70235bc71]),([6,1082401,2165730,17318416,32505887,32641156],hh [0x1458191604458091600,0x145839160c458291608,0x145925163a080482010,0x17e245167145959164a]),([6,1082401,2165759,4329604,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x1059281649450491410,0x1059b81662059841651,0x1452691499059c81671]),([6,1082401,2165759,4329604,17318431,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a0926823a058481610,0x105a0a826e9c946824a,0x5149a452641691]),([6,1082401,4329604,8659208,16777759,32505856],hh [0x19681a5a049680a5a00,0x19683a5a0c9682a5a08,0x1968ea5a39058481610,0x19694a5a519692a5a49,0x105a48168205a065a71,0x65a95]),([6,1082401,4329604,8659967,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac0eab039058481610,0x105a081681a794ab04a,0x111a681692]),([6,1082913,2164802,4329604,32505856,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x1058e816398704a1c10,0x1059481651059281649,0x1059c81671059b4166a,0x4169d872687e8d]),([6,1082913,2164802,4329604,32505856,33554400],hh [0x132018c80432008c800,0x132038c80c32028c808,0x1320e8c8399c84a7210,0x132148c85132128c849,0x132a34c871321b4c862,0x132276729a])]
def b53 : List (List Nat × List (Nat × Nat)) := [([6,1083361,2164802,8659208,32505887,32641156],hh [0x17d819f6047d809f600,0x17d839f60c7d829f608,0x17d925f639090482410,0x17d1c5f6527d945ec4e,0x149a44248a]),([6,1083361,2164802,8659208,33047056,33554400],hh [0x133018cc0433008cc00,0x133038cc0c33028cc08,0x133124c8392f048bc10,0x132194cc6233148cc51,0x5d885331c8cc71]),([6,1083361,2164831,4329604,8659208,32505887],hh [0x10f0183c040f0083c00,0x10f0383c0c0f0283c08,0x10f12830497c849f210,0x10f1a83c660f1843a51,0x17ca65f2820f1c83c71,0x5f29a]),([6,1083361,2164831,4329604,8659231,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac12a9e490a0482810,0x10a2442882ac1cab051,0x17ca69f299]),([6,2164802,4330495,8659208,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x105924163a270489c10,0x1059c4166205984164a,0x1292681672]),([6,4330468,8659208,17318416,32505887,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x1011280439098482610,0x1011480451]),([7,31,256,1082401,2164802,4330468,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14b0592c14a784a9e10,0x1a794a9e51a78ea9e39,0x1a79c69e6aa79a69e62,0x1a5a469e8da7a2a9e72,0x14b2aa1ca99ca6a9e92,0x19cb252cba4b2c92cb1]),([7,31,256,1083361,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17b059ec14ac04ab010,0x1ac156b052ac0eab039,0x1a09c6b06aac1a6b062,0x1ac24a9e91ac22ab089,0x17b2aa1ca9ac26ab099,0x1b6b25ecba7b2c9ecb1])]
def b54 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1048575,1082401,2164802,4329604],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x149935264a498e92639,0x1499a92669499552652,0x149a292689492092671,0x13c2c5269a49a651492,0x14fb093ec13c2f8f0b2,0x10532914c9]),([7,31,512,1082401,2097152,4329604,32505856],hh [0x1450191404450091400,0x145039140c450291408,0x145059141436048d810,0x1451491451450e91439,0x1451a91469451891461,0x136228d889451c91471,0x136268d89905a481691,0x1452c914b1452aa16a9,0x13632514c54530914ba,0x514ce]),([7,31,512,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x1872a6729a9ca667292,0x149ae926b249ac526aa,0x13c32514c5]),([7,31,512,1082401,2164802,4329604,32505887],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9aa72699c9881c61,0x19ca266c819c9ca7271,0x19ca6672929ca46728a,0x149ac672ad49aaa729a,0x516c549ae926b2]),([7,31,512,1082401,2164802,4329604,32506368],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x1872a6729a9ca667292,0x149aea72b549ac926aa,0x13c32514c5]),([7,31,512,1082401,2164802,4329604,32539681],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9465c4a9c8ea7239,0x19c9aa72699c98a7252,0x19ca2a72899c9ca7271,0x19ca6a72999ca4a7291,0x149ae926b249ac526aa,0x416c94531672bd]),([7,31,512,1082401,2164802,4329604,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x14c2aa729a9ca667292,0x14531534ba4d2c934b1,0x470c9]),([7,31,512,1082401,2164802,4329604,33047056],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x149aaa729a9ca667292,0x14531526ba9cad526b2,0x4b0c9])]
def b55 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082401,2164802,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946723e9c8ea7239,0x19c9a672629c9567252,0x19c9ca72719c9b6726a,0x19ca46728d9ca2a7289,0x1872a6729a9ca667292,0x19cad526b249ac526aa,0x4f0c94531526ba]),([7,31,512,1082401,2164802,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946724a9c8ea7239,0x19c9aa72699c98a7252,0x19ca2a72899c9ca7271,0x19ca6a72999ca567292,0x149ac926b149aaa1ca9,0x105b2514c59a2f526ba]),([7,31,512,1082401,2164802,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9ca72719c9aa7269,0x19ca4a72919ca2a7289,0x149aaa1ca99ca76729a,0x19cb2526ba49ac926b1,0x526ce]),([7,31,512,1082401,2164802,8659208,33047056],hh [0x12c018b0042c008b000,0x12c038b00c2c028b008,0x11c05870142c048b010,0x12c144984a2c0e8b039,0x12c1c4b06a2c1a4b052,0x12c244b08a2c224b072,0x11c2c8b09a2c264b092,0x10532492bd1c2e8b0b5,0x414ca]),([7,31,512,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12c058b0141c0487010,0x11c1445c4a1c0e87039,0x11c1c4706a1c1a47052,0x11c244708d1c2287072,0x12c2c4709a1c2647092,0x10532456bd2c2e8b0b2,0x414ca]),([7,31,512,1082401,2164802,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x11c05870149c84a7210,0x19c946724a9c8ea7239,0x19c9c6726a9c9a67252,0x19ca46728d9ca2a7272,0x1872a6729a9ca667292,0x11c2e870b21c2c470aa,0x414ca0532668bd]),([7,31,512,1082401,2164802,29224827,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x11c05870149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca4a728d9ca2a7272,0x1872a6729d9ca6a7295,0x11c2e870b21c2c470aa,0x13c32414c5]),([7,31,512,1082401,2164802,32505856,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x1499492651498e92639,0x1499c5266a499a52462,0x149a25268249a052672,0x145275269a49a49268a,0x19cb0816ba3c2c8f0b1,0x526cd3c32914c5])]
def b56 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082401,2164831,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14905924149c84a7210,0x19c94672499c8ea7239,0x19c9a672659c98a7252,0x19ca2672819c9ca726a,0x19ca6672929ca46728a,0x1492c924b1492a924a9,0x4ecc94531524ba]),([7,31,512,1082401,2165314,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726d9c9aa7262,0x19ca46728a9ca267272,0x1872a6729a9ca667292,0x149ae926b249ac526aa,0x13c32514c5]),([7,31,512,1082401,2165730,4329604,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a094a8251a08ea8239,0x1a09ca826da09aa8262,0x1a0a4a8291a0a2a8289,0x145ac516aa872a67299,0x13732514c545ae916b2]),([7,31,512,1082401,2194498,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9ca726a9c9a67262,0x19ca4a72919ca2a7289,0x149ac526aa872a67299,0x13c32514c549ae926b2]),([7,31,512,1082401,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9ca726a9c9a67262,0x19ca46728a9ca267275,0x1872a6729a9ca667292,0x149ae526b249ac526aa,0x4d8c94531526ba]),([7,31,512,1082401,4329604,6494406,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c94a72519c8ea7239,0x19c9ca72719c9aa7269,0x19ca46728a9ca267282,0x1872a6729d9ca6a7292,0x1452e914b2452c514aa,0x14533914cd]),([7,31,512,1082401,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c94a72519c8ea7239,0x19c9ca72719c9aa7269,0x19ca46728d9ca2a7282,0x1872a6729a9ca667292,0x1452e514b2452c514aa,0x672cd4532914ba]),([7,31,512,1082401,4329604,31389629,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9ca72719c9aa7269,0x19ca4a728d9ca2a7282,0x1872a6729d9ca6a7295,0x149ae926b249ac526aa,0x145334f0c1])]
def b57 : List (List Nat × List (Nat × Nat)) := [([7,31,512,1082913,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946723e9c8ea7239,0x19c9a672629c9567252,0x19c9ca72719c9b6726a,0x19ca46728d9ca2a7289,0x1872a6729a9ca667292,0x19cad526b249ac526aa,0x4f0c94531526ba]),([7,31,512,2164802,3247203,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9d672729c9aa7269,0x19ca4a72919ca2a7289,0x149aaa1ca99ca6a7299,0x13c32526b949ac926b1]),([7,31,512,2164802,4329604,5412005,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x13c058f0149c84a7210,0x19c946724a9c8ea7239,0x19c9aa72699c98a7252,0x19ca2a72899c9ca7271,0x19ca76729a9ca4a7291,0x13c2c8f0b13c2aa1ca9,0x13c314d8bd]),([7,31,512,2164802,4329604,25977624,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x11585856149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728d9ca2a7272,0x1872a6729a9ca667292,0x115ae456b215ac456aa,0x10232856c5]),([7,31,512,2164802,4329604,32472030,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x11585856149c84a7210,0x19c946724a9c8ea7239,0x19c9c6726a9c9a67252,0x19ca4a728d9ca2a7272,0x1872a6729d9ca6a7295,0x1022f456b215ac456aa,0x115b3856c1]),([7,31,512,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x145059141436048d810,0x136148d851360e8d839,0x1361c4d86a361a4d862,0x136234d88a36208d872,0x136268d89936248d891,0x13631456c2452c914b1,0x13633492ca]),([7,31,528,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x1872a6729a9ca667292,0x149ae926b249ac526aa,0x13c32514c5]),([7,31,543,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c926723d9c8ea7239,0x19c98a72619c946724d,0x19c9c6726a9c9a67265,0x19ca2672859ca067272,0x19ca6a72999ca4a7291,0x149ac672ad49aa926a9,0x13c32514c549ae926b2])]
def b58 : List (List Nat × List (Nat × Nat)) := [([7,31,544,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c94a72519c8ea7239,0x19c9c6726a9c9a67262,0x19ca46728a9ca267272,0x1872a6729a9ca667292,0x149ae926b249ac526aa,0x171b2514c5]),([7,31,576,1082401,2164802,4329604,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1498592614a784a9e10,0x1a794a9e51a78ea9e39,0x1a79ca9e719c9a69e62,0x1a7a4a9e91a7a2a9e89,0x149aaa1ca9a7a6a9e99,0x1b7b2526ba49aca78b1]),([7,31,640,1082401,2164802,4329604,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x178059e014a084a8210,0x1a094a8251a08ea8239,0x1a09c6826aa09a68262,0x1a0a46828a9ca268272,0x1872a6829aa0a668292,0x1782e9e0b2782c5e0aa,0x13c325dcc5]),([7,31,736,1082401,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x178059e014ac04ab010,0x1ac14ab051ac0eab039,0x1ac1cab071a09a6b062,0x1ac24ab091ac22a9e89,0x1782aa1ca9ac26ab099,0x1b7b25e0ba782ca72b1]),([7,31,992,31744,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,3115074,8659208,17318416,32641156],[]),([7,31,992,507375,1082401,2164802,4329604],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x149945264a498e92639,0x149a252482499c52669,0x149a69269945249168a,0x180b0a02c13c2f928b1,0x10532914c9])]
def b59 : List (List Nat × List (Nat × Nat)) := [([7,31,992,507375,1082401,2164802,8659208],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x10505814141c0487010,0x11c14870511c0e87039,0x11c1c46c6a1c1a45c62,0x11c26870991c2245672,0x115b0414be1c2e414b1,0x5f8ca7e32414c2]),([7,31,992,777975,1082401,2164802,4329604],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x1ae05ab8147e049f810,0x17e155f44a7e0e9f839,0x17ca09f8717e1a9f869,0x1ae2c5f89a7e265f889,0x1ae30ab8c1ae2fab6b2,0x10532914c9]),([7,31,992,777975,1082401,2164802,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x10505814142f048bc10,0x128188bc552f0e8bc39,0x1271c8bc712f1a8bc69,0x1052c8bc9a2f264bc89,0x12730414be2f2e4b0b5,0x6f2ca5cb2414c2]),([7,31,992,1014750,4329604,8659208,17318416],hh [0x1550195404550095400,0x155039540c550295408,0x1450591414550495410,0x1551a54a55550e95439,0x155245548a552255482,0x1452a9549a552655492,0x17e308bcc1452e514b5,0x14532914c9]),([7,31,992,1047552,1082401,2164802,4329604,8659208,33047056],[]),([7,31,992,1047552,1082401,2164802,4329604,17318416,32776456],[]),([7,31,992,1047552,1082401,2164802,8659208,17318416,32641156],[]),([7,31,992,1048576,2164802,8659208,33047056],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1271289c49270e89c39,0x1271c49c69271489c51,0x1272489c91272249c72,0x124ad456b2272689c99,0x10232808c9272f456ba])]
def b60 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1048576,2164802,17318416,32776456],hh [0x1158185604158085600,0x115838560c158285608,0x1270589c14158485610,0x1159285649158e85639,0x1159c45669159485651,0x115a44568d15a285672,0x1992c4569a15a645692,0x10232808c915af49cba]),([7,31,992,1082401,2097152,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1450591414560495810,0x1561855851560e95839,0x1561c5586a561a55862,0x1562495891532255872,0x1452d514aa562695899,0x12f32558c54530914ba]),([7,31,992,1082401,2164802,4329604,8659208,17825296,32505856],[]),([7,31,992,1082401,2164802,4329604,8682760,17809936,32505856],[]),([7,31,992,1082401,2164802,4329604,9436424],hh [0x18081a02048080a0200,0x18083a020c8082a0208,0x17c059f0148084a0210,0x17f14a0251808ea0239,0x1809ca027180989fa61,0x180a4a02917fa29da81,0x178ac5ecaa80a6a0299,0x17a305f0ba]),([7,31,992,1082401,2164802,4329604,9436424,17318416,32505856],[]),([7,31,992,1082401,2164802,4329604,17825296],hh [0x1638198e04638098e00,0x1638398e0c638298e08,0x1498592614638498e10,0x15d1858e51638e98e39,0x1639c98e71599a98e62,0x163a658e9263a458e81,0x159b0526ba49aa98e9a]),([7,31,992,1082401,2164802,4329604,32506112],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17b059ec14a804aa010,0x1a514aa051a80eaa039,0x1a81caa0719d1a6a062,0x1a824aa091a722a9e89,0x17b2aa1ca9a826aa099,0x6dec97b2ea72b1])]
def b61 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,4329604,32506368],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611898451610e98439,0x1611c98471561a98469,0x1612658492612457e89,0x19cad526aa872a5849a,0x4f0c95631526ba]),([7,31,992,1082401,2164802,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a514aa051a80eaa039,0x1a81caa0719d1a6a062,0x1a824aa091a722a9e89,0x19cac5f4aaa826aa099,0x11c325f8ba]),([7,31,992,1082401,2164802,4329604,32776479],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17d059f414a804aa010,0x1a514aa051a80eaa039,0x1a81c67469a81883261,0x1a722a9e89a8206a072,0x1a826aa099a824aa091,0x17d2ea72b1a82b5f4aa]),([7,31,992,1082401,2164802,4329604,32810281],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a818aa051a80eaa039,0x1a7a26a072a81c67469,0x1a8266a092a82469c8a,0x17e2ea72b17d2aaa09a,0x11c326a0bd]),([7,31,992,1082401,2164802,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611898451610e98439,0x1611c98471561a98469,0x1612658492612457e89,0x149aea72b549aa9849a,0x12f32558c5]),([7,31,992,1082401,2164802,4329604,33047071],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x10f1858451610e98439,0x1611c5586a611a58462,0x1612457e8960a058472,0x149aa9849a612658492,0x15631526ba9cad584ad]),([7,31,992,1082401,2164802,4329604,33080881],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x13d9498451610e98439,0x1611c5586a611a58462,0x16124984915fa258472,0x19cad526aa612698499,0x12f32558c5612f526ba]),([7,31,992,1082401,2164802,4330116,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1ac146723eac0eab039,0x1ac1aa8269ac18a7255,0x1a7a26b072ac1c69e6d,0x1ac266b092ac246828d,0x19cac526aa872a6b09a,0x14531526ba9cad526b2,0x4f0c9])]
def b62 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,4330468,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x17e059f814a704a9c10,0x1a71469c3ea70ea9c39,0x1a71a69c62a71569452,0x1a72269c72a71c69c6d,0x1a724a9491a72369c8a,0x1a7ad5f8b17d2aa9c9a,0x11c325f8ba]),([7,31,992,1082401,2164802,5412005,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a8146a04aa80eaa039,0x1a81c67469a818aa052,0x1a824a9c8aa7a26a072,0x17d2aaa09aa8266a095,0x11c326a0bd7e2ea72b1]),([7,31,992,1082401,2164802,5412005,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x161145844a610e98439,0x1561a98469611898452,0x1612497e89611c98471,0x149aa9849a612658495,0x15631580bd49aea72b5,0x4bcc9]),([7,31,992,1082401,2164802,6494406,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a514aa051a80eaa039,0x19ca26a072a81c67469,0x1a826aa092a82469c8a,0x17e2ea72b17d2aaa09d,0x470c9]),([7,31,992,1082401,2164802,6494406,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611a58451610e98439,0x1612457e89611c98471,0x149aa9849d612698492,0x4bcc949aea72b5]),([7,31,992,1082401,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f264bc922f244bc89,0x11c2e8b0b51c2c8bc9a,0x414ca053249cbd]),([7,31,992,1082401,2164802,8659208,33047536],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144a04a2f0e8bc39,0x12f224bc722f1c4bc52,0x12f268bc992f248bc91,0x1272f470ba2f2d470b2,0x414ca]),([7,31,992,1082401,2164802,8659208,33080881],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f148bc512f0e8bc39,0x12f224bc722f1c4bc69,0x12f268bc992f248bc91,0x12f2f470ba2c2d470b2,0x10532814c9])]
def b63 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,8659208,33317656],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x10505814142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f244788e2f2247a82,0x1052c8bc9a2f264bc92,0x1053289cbd052e8b0b5,0x4bccd]),([7,31,992,1082401,2164802,9741609,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f1a4bc512f0e8bc39,0x12f248bc892f1c8bc71,0x11c2c8bc9a2f264bc95,0x10532814c91c2e8b0b5]),([7,31,992,1082401,2164802,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144a04a2f0e8bc39,0x12f1a8bc692f188bc52,0x12f244bc892f1c8bc71,0x11c2c8bc9d2f268bc92,0x12f3149cbd1c2e8b0b5,0x434c9]),([7,31,992,1082401,2164802,12988812,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x17e059f8141c0487010,0x11c14870511c0e87039,0x11c1c870711c1a47062,0x11c24870911c2287089,0x17e2ea6eb11c2687099,0x470c9]),([7,31,992,1082401,2164802,16236015,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x17e059f8141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a46c52,0x11c25470921c2287089,0x17e2ea6eb11c274709a,0x5f8ce1c32456bd]),([7,31,992,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a46c52,0x11c24870911c234708a,0x12f2ea6eb11c2687099,0x414ca0532456bd]),([7,31,992,1082401,2164802,17318416,32810281],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1a470511c0e87039,0x11c234708a1c1c87071,0x11c26870991c2487091,0x10532470bd2f2ea6eb1,0x414ca]),([7,31,992,1082401,2164802,17318416,33317656],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x10505814141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a46c52,0x11c244708e1c2347082,0x11cad4709a1c2647092,0x11c33414ca15af414ba])]
def b64 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,17318896,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a46c52,0x11c2486c911c234708a,0x115af4bcba2f2c4709a,0x414c9]),([7,31,992,1082401,2164802,18400817,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c14870511c0e87039,0x11c22870721c1c47069,0x11c26470951c248708d,0x105324bcba9bac4709a,0x414ca]),([7,31,992,1082401,2164802,19483218,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1445c4a1c0e87039,0x11c1c470691c1886c52,0x11c244708d1c2287072,0x19bac4709d1c2687092,0x6a0c915af4bcba]),([7,31,992,1082401,2164802,21648020,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x14985926142f048bc10,0x12f188bc512f0e8bc39,0x12f1c8bc712f1a8bc69,0x12f264bc922f244bc8d,0x149ae8b0b549ac8bc9a,0x12f324bcc5]),([7,31,992,1082401,2164802,24895223,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x14985926142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f268bc952f248bc8d,0x149ae8b0b549ac8bc9d,0x526ce2f3249cbd]),([7,31,992,1082401,2164802,25977624,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x12f058bc14a804aa010,0x1a8146a04aa80eaa039,0x1a81caa0719d1a6a052,0x1a824aa0919ca369c8a,0x19cac47aaaa826aa099,0x414c9a82f4bcba]),([7,31,992,1082401,2164802,25977624,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x11c0587014610498410,0x161145844a610e98439,0x1611c98471611a58452,0x1612658492612457e8d,0x11c2ea72b51c2a9849a,0x10532580bd]),([7,31,992,1082401,2164802,29224827,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x12f058bc14a804aa010,0x1a514aa051a80eaa039,0x1a81caa0719d1a6a062,0x1a8256a092a7a369c8a,0x19cac47aaaa8276a09a,0x1a8324bcba])]
def b65 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164802,29224827,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x11c0587014610498410,0x1611898451610e98439,0x1611c98471561a98469,0x1612698495612497e8d,0x11c2ea72b51c2a9849d,0x13c32558c5]),([7,31,992,1082401,2164802,32641156,32776456],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f814b784ade10,0x17e149f8517e0e9f839,0x17e1c9f8717e1a5f262,0x1a826ade92b722ade89,0x17e309f8ba7e2c5f4aa,0x470c9]),([7,31,992,1082401,2164802,32641156,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611898451610e98439,0x1611c98471561a98469,0x156275849a612497e89,0x149b0926ba49ad526aa,0x12f32558c5]),([7,31,992,1082401,2164802,32776456,32911756],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x11c05870147e049f810,0x17e149f8517e0e9f839,0x17e1c9f8717e1a5f262,0x11c2c5f89a7e249f889,0x11c32870c21c2e870b2,0x5f8cd]),([7,31,992,1082401,2164802,32776456,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f2689c952f248bc89,0x1272f470ba2c2d470b2,0x414ca0532470c2]),([7,31,992,1082401,2164802,32776456,33317656],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x10505814142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f248788e2f2247a82,0x12c2d414b22f2689c95,0x10532aa0c2272f414ba,0x4bccd]),([7,31,992,1082401,2164802,33047056,33182356],hh [0x1498192604498092600,0x149839260c498292608,0x12f058bc14498492610,0x1491892651498e92639,0x1499c92671459a92669,0x149a69269249a35268a,0x12f308bcba782d5149d,0x526cd2f32914c5]),([7,31,992,1082401,2164802,33047056,33317656],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x10505814141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a46c52,0x11c248708e1c2347082,0x1052e872b51c2685695,0x11c33414ca0d30856bd])]
def b66 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,2164831,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17c859f214a804aa010,0x1a8146a049a80eaa039,0x19d1a6a065a818a9452,0x1a722a9e89a8206a072,0x17caa6a099a824aa091,0x11c325f2ba9cac5f2aa]),([7,31,992,1082401,2164831,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1490592414610498410,0x1611458449610e98439,0x1561a98469611958462,0x1612457e89612058472,0x1492a924a9612658492,0x12f32558c5492ea72b5]),([7,31,992,1082401,2165058,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17b059ec14ac04ab010,0x1ac14ab051ac0eab039,0x1ac1cab071a09a6b062,0x1ac24ab091ac22a9e89,0x17b2aa1ca9ac26ab099,0x1b7b25ecba7b2ca72b1]),([7,31,992,1082401,2165730,4329604,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1458591614560495810,0x156145583e560e95839,0x1561a95869561895855,0x1562355889561c9586d,0x145aa95899562495891,0x14531516baa0ad516b1,0x4bcc9]),([7,31,992,1082401,2194498,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,4329604,9412872,17318416,32505856],[]),([7,31,992,1082401,3144770,4329604,8659208,17318416,32505856],[]),([7,31,992,1082401,3247203,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a818aa051a80eaa039,0x1a7a26a075a81ca7469,0x1a8266a092a82469c8a,0x17e2e672b17d2aaa09a,0x11c325f8ba])]
def b67 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,3247203,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611898451610e98439,0x1611d58472561a98469,0x1612658492612457e89,0x149ae672b549aa9849a,0x4bcc95631526ba]),([7,31,992,1082401,3247203,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f1a4bc512f0e8bc39,0x12f244bc892f1d4bc72,0x11c2c8bc9a2f264bc92,0x10532470ba1c2e4b0b5,0x414ca]),([7,31,992,1082401,3247203,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1a470511c0e87039,0x11c234708a1c1d47072,0x11c26870991c2487091,0x105324bcba2f2e66eb1,0x414ca]),([7,31,992,1082401,4329604,6291456,17318416],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014450491410,0x1a79a6b051ac0eab039,0x1452091481ac1cab071,0x14524914914522a7289,0x1272e6b0b69cad6b0aa,0x145326b0c22f306b0ba,0x514ca]),([7,31,992,1082401,4329604,6494406,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1ae05ab814a804aa010,0x1a514aa051a80eaa039,0x1a820aa072a81c69e69,0x1a826aa092a82467289,0x1ae2ea72b1ae2aaa09d]),([7,31,992,1082401,4329604,6494406,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1450591414610498410,0x15f9a58451610e98439,0x15fa258482611c98471,0x161269849261245588a,0x1452ea72b5452a9849d,0x514cd]),([7,31,992,1082401,4329604,8659208,17825296],hh [0x1598196604598096600,0x159839660c598296608,0x1450591414598496610,0x1599856651598e96639,0x159a256682599c96671,0x159a65669259a45668a,0x14532514ba452a9669a,0x514ca]),([7,31,992,1082401,4329604,8682760,17809936],hh [0x15b0196c045b0096c00,0x15b0396c0c5b0296c08,0x18185a06145b0496c10,0x15b1856c515b0e96c39,0x15b2256c825b1c96c71,0x181aea06aa5b2496c8a,0x14532914c9])]
def b68 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,4329604,9436424,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x18185a06145c8497210,0x15c98572515c8e97239,0x15ca2572825c9c97271,0x1272e606aa5ca49728a,0x14532606c22f30606ba,0x514ca]),([7,31,992,1082401,4329604,9437183,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x18185a06145c8497210,0x15c9a572515c8e97239,0x15ca1572825c9c97271,0x15925572925ca35728a,0x181ae89cb94fad606aa,0x514c981b08bcc1]),([7,31,992,1082401,4329604,17318416,24117248],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1a79a6b051ac0eab039,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x15caca72b15caaa20a9,0x514ca5cae964b9]),([7,31,992,1082401,4329604,25707024,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c0597014ac04ab010,0x1a79a6b051ac0eab039,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x15c2ca72b15c2aa1ea9,0x514ca5c2e962b9]),([7,31,992,1082401,4329604,25977624,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x15a0596814a804aa010,0x1a79a6a051a80eaa039,0x19ca36a082a81caa071,0x1a826aa099a824aa091,0x15a2e95eb99cac568aa]),([7,31,992,1082401,4329604,25977624,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1450591414610498410,0x15f9a58451610e98439,0x1562298482611c98471,0x1612658492612457e8d,0x1452e672b5452a9849a,0x1ac33514ba]),([7,31,992,1082401,4329604,31389629,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x15a0596814a804aa010,0x1a514aa051a80eaa039,0x1a81caa071a71aa9e69,0x1a8256a0929d236a082,0x19cac568aaa8276a09a,0x11c30568ba]),([7,31,992,1082401,4329604,31389629,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x15f9a58451610e98439,0x1562298482611c98471,0x161269849561249848d,0x149aea72b549aa9849d,0x145334bcc1])]
def b69 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,6494406,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1050581414ac04ab010,0x1ac14ab051ac0eab039,0x1ac1cab071ac1aa7269,0x1872a6b092ac2468289,0x1052e814b29cac414aa,0x414c6]),([7,31,992,1082401,6494406,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1450591414ac04ab010,0x1ac14ab051ac0eab039,0x1a7a26b072ac1c67269,0x1452aa1ca9ac24ab091,0x14531914ba452ca72b1]),([7,31,992,1082401,6494406,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1050581414ac04ab010,0x19c9a6b051ac0eab039,0x1ac2469e8dac1cab071,0x19cac414aa872a6b092,0x414c6052e814b2]),([7,31,992,1082401,6494406,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1450591414ac04ab010,0x19c9a6b051ac0eab039,0x1a0a36b072ac1c6b06a,0x1452aa1ca9ac24ab091,0x14531914ba452ca72b1]),([7,31,992,1082401,8659208,10824010,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x10505814142f048bc10,0x12f144a04a2f0e8bc39,0x12f1a8bc692f188bc52,0x12f244bc892f1c8bc71,0x1052c8bc9d2f268bc92,0x1053089cbd052e8b0b5,0x4bcc5]),([7,31,992,1082401,8659208,21648020,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x14505914142f048bc10,0x12f188bc512f0e8bc39,0x12f1c8bc712f1a8bc69,0x12f264bc922f244bc8d,0x1452e4b0b5452c8bc9a,0x4bcc54530914ba]),([7,31,992,1082401,8659208,31389629,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x14505914142f048bc10,0x12f144a04a2f0e8bc39,0x12f1c8bc712f1a4bc52,0x12f268bc952f248bc8d,0x1452e8b0b5452c8bc9d,0x514c2453049cbd]),([7,31,992,1082401,10824010,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac14ab051ac0eab039,0x1a7a26b072ac1c68269,0x1872a6b092ac246b08a,0x17e2e9f8b29cac5f8aa])]
def b70 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,10824010,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac146b04aac0eab039,0x1ac1cab071a09a6b052,0x1ac24ab091a7a36b08a,0x12f2ca72b12f2aa1ca9,0x1a92f4bcba]),([7,31,992,1082401,10824010,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac146b04aac0eab039,0x1ac1cab071a09a6b052,0x1ac24ab0919ca36b08a,0x12f2ca72b12f2aa1ca9,0x414caa92f4bcba]),([7,31,992,1082401,12718212,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1a79a6b051ac0eab039,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x15caca72b15caaa20a9,0x514ca5cae964b9]),([7,31,992,1082401,12988812,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x15c85972141c0487010,0x11c1a470511c0e87039,0x11c23470821c1c87071,0x11c26870991c2487091,0x14532972ba592e66eb1]),([7,31,992,1082401,12988812,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1a79a6b051ac0eab039,0x1a0a36b072ac1c6b06a,0x149aaa1ca9ac24ab091,0x149ae926b949aca72b1]),([7,31,992,1082401,12988812,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11c0587014ac04ab010,0x1a79a6b051ac0eab039,0x1ac246728dac1cab071,0x19cac470aa872a6b092,0x14532870ba1c2e470b2]),([7,31,992,1082401,17318416,19483218,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x10505814141c0487010,0x11c1445c4a1c0e87039,0x11c1c4706d1c1886c52,0x11c24870911c2347072,0x1052ea6eb11c274709a,0x10530856bd]),([7,31,992,1082401,17318416,31389629,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x14505914141c0487010,0x11c1445c4a1c0e87039,0x11c1c4706d1c1a86c52,0x11c25470921c2347072,0x1452ea6eb11c274709a,0x514c24530456bd])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k70 : b70.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b71 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1082401,19483218,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1ac1aab051ac0eab039,0x1a0a36b072ac1c69e6d,0x149aaa1ca9ac24ab091,0x526ba49aca72b1]),([7,31,992,1082401,19483218,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11c0587014ac04ab010,0x1ac146b04aac0eab039,0x1ac1cab071a79b6b052,0x1872a6b092ac246728d,0x11c2e870b29cac470aa,0x10532aa4bd]),([7,31,992,1082401,21648020,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1a09b6b051ac0eab039,0x19ca36b08aac1cab071,0x12f2aa1ca9ac24ab091,0x12f2e8bcb92f2ca72b1,0x514ca]),([7,31,992,1082431,2164802,8659208,33047056],hh [0x128018a00428008a000,0x128038a00c28028a008,0x1170585c1428048a010,0x128134a04a280e8a039,0x1281a4a06128148a051,0x128244a08928204a071,0x1172c85ca928268a099,0x102b280ac9a8af498b5]),([7,31,992,1082431,2164802,17318416,32776456],hh [0x1170185c04170085c00,0x1170385c0c170285c08,0x128058a014170485c10,0x1171345c4a170e85c39,0x1171a45c61159485c51,0x1172345c8a172045c71,0x1282a45c9a172645c91,0x102b280ac9a52f66eb1]),([7,31,992,1082913,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1ac146723eac0eab039,0x1ac1aa8269ac18a7255,0x1a7a26b072ac1c69e6d,0x1ac266b092ac246828d,0x19cac526aa872a6b09a,0x14531526ba9cad526b2,0x4f0c9]),([7,31,992,1083361,2164802,4329604,32776456],hh [0x1a501a9404a500a9400,0x1a503a940ca502a9408,0x17e059f814a504a9410,0x1a51569452a50ea9439,0x1a52269471a51a69462,0x1a52669492a5246948a,0x11c326b0b57d2aa949a]),([7,31,992,1083361,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11b0586c142f048bc10,0x128128bc3e2f0e8bc39,0x12f1a4bc552f148bc51,0x12f234bc892f1c4bc6d,0x11b2c4bc9a2f264bc91,0x1272f46cba2f2d46cb2,0x10432810c9])]
def b72 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1083361,2164802,17318416,32776456],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x12f058bc141b0486c10,0x11b148564a1b0e86c39,0x11b2246c711b1a46c55,0x11b2646c921b2446c8a,0x1043245ebd1e2d46c9a,0x410ca]),([7,31,992,2096161,2164802,8659208,17318416],hh [0x12d018b4042d008b400,0x12d038b40c2d028b408,0x11c05870142d048b410,0x12b1449c4a2d0e8b439,0x12d244b4892d184b452,0x1272e470b22d268b499,0x10532814c91c30972c1]),([7,31,992,2097151,2164802,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1271349c4a270e89c39,0x1272249c69271549c52,0x1272689c99272589c91,0x115af89cb924ad456b2,0x10232808c915b0972c1]),([7,31,992,2164802,3247203,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x19d1a67451a80eaa039,0x1a7a26a075a81ca946a,0x1a8266a092a82469c8a,0x17e2e672b17d2aaa09a,0x470c9]),([7,31,992,2164802,3247203,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611a58451610e98439,0x1612457e89611d58472,0x149aa9849a612658492,0x4bcc949ae672b5]),([7,31,992,2164802,3247203,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x128188bc512f0e8bc39,0x12f1d4bc722f1a8bc69,0x12f264bc922f244bc89,0x11c2e4b0b51c2c8bc9a,0x408ca023249cc5]),([7,31,992,2164802,3247203,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11718870511c0e87039,0x11c1d470721b1a87069,0x11c24870911c234708a,0x12f2e66eb11c2687099,0x408ca0232456c5]),([7,31,992,2164802,4329604,5412005,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x173859ce14a804aa010,0x19d146a04aa80eaa039,0x1a81c6a06aa79a6a062,0x1a8246948aa7a26a072,0x1732aaa09da826aa092,0x1a831672b1])]
def b73 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,4329604,5412005,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x13c058f014610498410,0x161145844a610e98439,0x1611a97e69611895852,0x1612457e89611c98471,0x13c2a9849d612698492,0x4f0c5562f672b5]),([7,31,992,2164802,4329604,25977624,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1270589c14a804aa010,0x1a818a7451a80eaa039,0x1a81caa071a81aa9e69,0x1a824aa0919ca36948a,0x19cac460aaa826aa099,0x1a83149cb9]),([7,31,992,2164802,4329604,25977624,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1158585614610498410,0x1611898451610e98439,0x1611c98471611a97e69,0x1612658492612457e8d,0x115ae672b515aa9849a,0x456c5]),([7,31,992,2164802,4329604,32472030,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1270589c14a804aa010,0x19d146a04aa80eaa039,0x1a81caa071a71aa9e69,0x1a8256a092a8236948a,0x19cac460aaa8276a09a,0x12733870c1]),([7,31,992,2164802,4329604,32472030,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1158585614610498410,0x161145844a610e98439,0x1611c984715f9a55852,0x161269849561249848d,0x1562f672b515aa9849d,0x115b38bcc1]),([7,31,992,2164802,5412005,9741609,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x19185a4614ac04ab010,0x1a0946b04aac0eab039,0x1ac20ab072ac1c69e69,0x1872a6b092ac246b089,0x13c32a46b29cac646aa]),([7,31,992,2164802,5412005,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1a0946b04aac0eab039,0x1ac20ab072ac1c69e69,0x1872a6b092ac2469e89,0x526b29cac526aa]),([7,31,992,2164802,5412005,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1a0946b04aac0eab039,0x1ac1cab071a79a6b052,0x1ac24ab0919ca36b082,0x149aca72b149aaa1ca9,0x149b2914bd])]
def b74 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,5412005,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1628598a14ac04ab010,0x1a0946b04aac0eab039,0x1ac1cab071a79a6b052,0x1ac24ab091a0a36b082,0x162aca72b162aaa1ca9,0x560bd]),([7,31,992,2164802,6291456,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1271849c51270e89c39,0x1272249c6a271a49c62,0x1272689c99272489c91,0x115ae856b924ad456b2,0x1a932aa4c915b0856c1]),([7,31,992,2164802,8659208,9741609,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11585856142f048bc10,0x12f1a4bc512f0e8bc39,0x12f224a0822f1c8bc71,0x12f268bc922f244bc8a,0x105308b0b515ac8bc9d,0x127335ceca]),([7,31,992,2164802,8659208,17318416,31457280],hh [0x1a901aa404a900aa400,0x1a903aa40ca902aa408,0x1270589c14a904aa410,0x1a91a67c51a90eaa439,0x19a236a48aa91caa471,0x1a926aa499a924aa491,0x1272ca68b1272a89ca9,0x115b2856c9273089cc1]),([7,31,992,2164802,8659208,21512720,32505856],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14158485610,0x1271a49c51270e89c39,0x124a34568a271c89c71,0x102268089915a496e91,0x1272ca76b1272aa1ca9,0x115b289cc2272f89cb9]),([7,31,992,2164802,8659208,21648020,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11585856142f048bc10,0x12f1a4bc512f0e8bc39,0x12f228a0822f1c8bc71,0x12f264bc922f244bc8d,0x115ae4b0b515ac8bc9a,0x115b3408c2]),([7,31,992,2164802,8659208,32472030,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f1a4bc512f0e8bc39,0x12f228a0822f1c8bc71,0x12f268bc952f248bc8d,0x105304b0b51c2c8bc9d,0x470ce15b3414c2]),([7,31,992,2164802,9741609,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1140585014ac04ab010,0x1a0946b04aac0eab039,0x1a7a26b072ac1c6b069,0x1142aa1ca9ac24ab091,0x450c2142ca72b1])]
def b75 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,9741609,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12a858aa14ac04ab010,0x1ac1a68251ac0eab039,0x1ac246728dac1cab071,0x19cac4aaaa872a6b092,0x466ca2ab08aab2]),([7,31,992,2164802,9741609,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1158585614ac04ab010,0x1ac18a8251ac0eab039,0x19ca36b072ac1c6b069,0x115aaa1ca9ac24ab091,0x191b2856c215aca72b1]),([7,31,992,2164802,12853512,17318416,32505856],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14158485610,0x1271a49c51270e89c39,0x124a34568a271c89c71,0x102268089915a497291,0x1272ca7ab1272aa1aa9,0x115b289cc2272f89cb9]),([7,31,992,2164802,12988812,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x1270589c141c0487010,0x11718870511c0e87039,0x11c1c870711b1a87069,0x11c24870911c234708a,0x1272e66eb11c2687099,0x1023289cc5]),([7,31,992,2164802,12988812,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1240589014ac04ab010,0x1a79a68251ac0eab039,0x1ac246828dac1cab071,0x19cac490aa872a6b092,0x1242e490b2]),([7,31,992,2164802,12988812,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11c0587014ac04ab010,0x1ac18a8251ac0eab039,0x19ca36b072ac1c69e69,0x11c2aa1ca9ac24ab091,0x10232870b91c2ca72b1]),([7,31,992,2164802,17318416,18400817,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x1270589c141c0487010,0x11c1a870511c0e87039,0x11720870721c1c4706d,0x11c24870911c2346c8a,0x10530a6eb11c274709a,0x115b34f0ca]),([7,31,992,2164802,17318416,32472030,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1a870511c0e87039,0x11720870721c1c4706d,0x11c25470921c2346c8a,0x1053066eb11c274709a,0x4bcce2733414c2])]
def b76 : List (List Nat × List (Nat × Nat)) := [([7,31,992,2164802,18400817,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1240589014ac04ab010,0x1a0946b04aac0eab039,0x1ac1cab0719c9b6b052,0x1872a6b092ac246828d,0x122af490b29cac490aa,0x490c2]),([7,31,992,2164802,18400817,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11c0587014ac04ab010,0x1ac18a8251ac0eab039,0x19ca36b072ac1c6726d,0x11c2aa1ca9ac24ab091,0x10532870c21c2ca72b1]),([7,31,992,2164802,21648020,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1158585614ac04ab010,0x1ac18a8251ac0eab039,0x19ca36b072ac1c6826d,0x115aaa1ca9ac24ab091,0x162b2856b915aca72b1]),([7,31,992,3179553,4329604,17318416,32505856],hh [0x1450191404450091400,0x136038d80c450291408,0x1450591414450491410,0x1361a51451450e91439,0x14523514820d1c83471,0x12f265149227245148e,0x1452c514aa85aa5f89a,0x145318d8c1452e914b2,0x14532914c9]),([7,31,992,3213378,8659208,17318416,32505856],hh [0x18e01a38048e00a3800,0x18e03a380c8e02a3808,0x1270589c148e04a3810,0x18e1a630518e0ea3839,0x18a236388a8e1ca3871,0x18e26a38998e24a3891,0x1272ca28b1272a89ca9,0x115b2856c9273089cc1]),([7,31,992,3247203,4329604,8659208,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x17e059f81436048d810,0x136144d84a360e8d839,0x1361c8d871361a8d869,0x136244d88e36224d882,0x138ac4d89a36264d892,0x5f8ca7e325d0c1]),([7,31,992,3247203,4329604,9741609,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136058d814ac04ab010,0x1a79a68251ac0eab039,0x1ac226b072ac1c6b06a,0x1362aa1ca9ac26ab099,0x17e324d8c1362ca72b1,0x5f8ca]),([7,31,992,3247203,4329604,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1020580814ac04ab010,0x1ac14a8251ac0eab039,0x1ac1cab071ac1aa9e69,0x1872a6b09aac2668289,0x10230408b29cac408aa,0x5f8c9])]
def b77 : List (List Nat × List (Nat × Nat)) := [([7,31,992,3247203,4329604,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x149859261436048d810,0x136144d84a360e8d839,0x1361c8d871361a4d852,0x136244d88e36234d882,0x138ac4d89a36264d892,0x149b2926c90d30514bd]),([7,31,992,3247203,4329604,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136058d814ac04ab010,0x1ac14a8251ac0eab039,0x19ca36b072ac1c69e69,0x1362aa1ca9ac26ab099,0x149b24d8c1362ca72b1,0x526ca]),([7,31,992,3247203,4329604,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1020580814ac04ab010,0x1a79a68251ac0eab039,0x1ac2669e8dac1cab071,0x19cac408aa872a6b09a,0x526c90230408b2]),([7,31,992,3247203,5412005,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136058d814ac04ab010,0x1a0946b04aac0eab039,0x1ac23ab089ac20a9e69,0x1ac26ab099ac24ab091,0x1362ca72b1362aa1ca9,0x4d8ca3632644c1]),([7,31,992,3247203,5412005,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136058d814ac04ab010,0x1a0946b04aac0eab039,0x19ca36b082a79a6b052,0x1ac266b092ac246b08e,0x19cac4d8aa872a6b09a,0x13632434c1362f4d8b2,0x4d8ca]),([7,31,992,3247203,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1018580614ac04ab010,0x19c9a68251ac0eab039,0x1ac246b08eac226b082,0x1872a6b09aac266b092,0x18eb0406b29cac406aa,0x406ca01b2406c6]),([7,31,992,3247203,6494406,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1008580214ac04ab010,0x19c9a68251ac0eab039,0x1ac246b08e9ca36b082,0x1872a6b09aac266b092,0x18eb0402b29cac402aa,0x402ca00b2402c6]),([7,31,992,3247203,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x12f058bc1436048d810,0x1361a4d851360e8d839,0x136234d88a361c8d871,0x136268d89936248d891,0x11c324bcc22f304e2b1,0x470ca])]
def b78 : List (List Nat × List (Nat × Nat)) := [([7,31,992,3247203,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x129858a614ac04ab010,0x1ac1a68251ac0eab039,0x1ac266728dac1cab071,0x19cac4a6aa872a6b09a,0x11c324a6c229b04a6b2,0x470ca]),([7,31,992,3247203,8659208,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1020580814ac04ab010,0x1a0946b04aac0eab039,0x1a7a36b072ac1c6b069,0x1022aa1ca9ac26ab099,0x10230808c1022ca72b1,0x470c9]),([7,31,992,3247203,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a68251ac0eab039,0x1ac24ab0919ca36b08a,0x12f2aa1ca9ac26ab099,0x12f308bcc12f2ca72b1,0x11932864c9]),([7,31,992,3247203,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1a0946b04aac0eab039,0x19ca36b08aa09a6b052,0x1ac26ab099ac24ab091,0x12f2ca72b12f2aa1ca9,0x10232808c92f3049cbd]),([7,31,992,4329604,8388608,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136184d851360e8d839,0x1361c4d86a361a4d862,0x136244d88d36208d872,0x138ac4d89a36264d892,0x49cca3631554c2]),([7,31,992,4329604,8659208,16236015,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x175859d61436048d810,0x136188d851360e8d839,0x1361c8d871361a8d869,0x136254d89236224d882,0x175b08e2b136274d89a,0x145338d8c5]),([7,31,992,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360e8d839,0x1361c8d871361a8d869,0x136248d89136234d882,0x155308e2b136268d899,0x127328d8c5]),([7,31,992,4329604,8659208,17318416,32810281],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x1361a4d851360e8d839,0x136234d882361c8d871,0x136268d89936248d891,0x127328d8c555308e2b1])]
def b79 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,8659208,17318416,33080881],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1270589c1436048d810,0x136188d851360e8d839,0x1361c8d871361a8d869,0x136248d89136234d88a,0x127309c4b536268d899,0x4d8cd27328d8c5]),([7,31,992,4329604,8659208,17318431,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136144d849360e8d839,0x1361a8d86936188d861,0x136214d882361c8d871,0x136268d89936248d88d,0x13631554c238ac54ea9]),([7,31,992,4329604,8659208,21648020,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136148d851360e8d839,0x1361c4d86a361a4d862,0x136248d88d36208d872,0x138ac4d89a36264d895,0x4d8c55530950b9]),([7,31,992,4329604,8659208,25977624,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360e8d839,0x1361c8d871361b8d869,0x136248d89136234d882,0x154b04e2b136274d89a,0x12732954c2]),([7,31,992,4329604,8659231,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136144d849360e8d839,0x1361a8d86936194d862,0x136234d88236204d872,0x136268d89936248d891,0x127328e4c538ac554a9]),([7,31,992,4329604,8659944,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360e8d839,0x136208d872361b4d86a,0x136264d89236244d889,0x49cca72315c8b5]),([7,31,992,4329604,9741609,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1158585614ac04ab010,0x1ac14a9e51ac0eab039,0x1ac1cab071ac1aab069,0x1872a6b092ac2468289,0x115ae456b29cac456aa,0x456c2]),([7,31,992,4329604,9741609,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13c058f014ac04ab010,0x1ac1a69e51ac0eab039,0x19ca36b072ac1c6b06a,0x13c2aa1ca9ac24ab091,0x175328f0c23c2ca72b1])]
def b80 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,9741609,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1158585614ac04ab010,0x1ac1a69e51ac0eab039,0x1ac246728dac1cab071,0x19cac456aa872a6b092,0x13632856c215b0456b2]),([7,31,992,4329604,10824010,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1a7946b04aac0eab039,0x1ac1cab071a09a6b052,0x1ac24ab091a7a36b08a,0x1272ca72b1272aa1ca9,0x49cbd]),([7,31,992,4329604,10824010,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1a7946b04aac0eab039,0x1ac1cab071a09a6b052,0x1ac24ab0919ca36b08a,0x1272ca72b1272aa1ca9,0x408ca273049cbd]),([7,31,992,4329604,12988812,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360e8d839,0x1361d4d872361a8d869,0x136248d89136234d882,0x1552e4e2b136268d899,0x127328d8c5]),([7,31,992,4329604,17318416,24895223,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360e8d839,0x136208d872361c4d86d,0x136254d89236234d88a,0x127308e2b136274d89a,0x15533954cd]),([7,31,992,4329604,17318416,25977624,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x145059141436048d810,0x136188d851360e8d839,0x1361c8d871361b8d86d,0x136244d88d36228d882,0x138ac4d89d36268d892,0x13633456ca4530914c1]),([7,31,992,4329604,18400817,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x19c9b69e51ac0eab039,0x1a7a36b08aac1cab071,0x1272aa1ca9ac24ab091,0x1273089cb9272ca72b1]),([7,31,992,4329604,18400817,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x19c9b69e51ac0eab039,0x19ca36b08aac1cab071,0x1272aa1ca9ac24ab091,0x1273089cc1272ca72b1,0x4d8ca])]
def b81 : List (List Nat × List (Nat × Nat)) := [([7,31,992,4329604,19483218,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1158585614ac04ab010,0x1a7946b04aac0eab039,0x1ac1cab071a79b6b052,0x1872a6b092ac246728d,0x115af456b29cac456aa,0x10232856c1]),([7,31,992,5412005,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bc85af214ac04ab010,0x1ac18a9e51ac0eab039,0x1ac23ab089ac20a7269,0x1ac26ab099ac24ab091,0x1bcaca72b1bcaaa1ca9,0x6f2caba32514c6]),([7,31,992,5412005,6494406,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bb05aec14ac04ab010,0x1ac18a9e51ac0eab039,0x19ca36b082ac1aa7269,0x1ac266b092ac246b08e,0x19cac6ecaa872a6b09a,0x1bb324eec636316ecb2,0x6ecca]),([7,31,992,5412005,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18a9e51ac0eab039,0x1ac1cab071ac1aab069,0x1ac26ab0999ca36b082,0x15caca72b15caaa1ca9,0x5d2caac31572c2]),([7,31,992,5412005,8659208,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1580596014ac04ab010,0x1ac18a9e51ac0eab039,0x1ac1cab071ac1aab069,0x1ac26ab099a0a36b082,0x1582ca72b1582aa1ca9,0x6b0c55830960b9]),([7,31,992,5412005,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18a9e51ac0eab039,0x19ca36b082ac1aab069,0x1ac26ab099ac24ab091,0x15caca72b15caaa1ca9,0x64acaa931572c2]),([7,31,992,5412005,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18a9e51ac0eab039,0x19ca36b082ac1aa9e69,0x1ac26ab099ac24ab091,0x15caca72b15caaa1ca9,0x4d8ca5cb1564b9]),([7,31,992,6494406,8659208,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1050581414ac04ab010,0x19c946b04aac0eab039,0x1a7a36b072ac1c6b069,0x1052aa1ca9ac26ab099,0x10530814be052ca72b1])]
def b82 : List (List Nat × List (Nat × Nat)) := [([7,31,992,6494406,8659208,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1228588a14ac04ab010,0x1ac1a67251ac0eab039,0x1ac266828dac1cab071,0x19cac48aaa872a6b09a,0x122b088abe8eae48ab2]),([7,31,992,6494406,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x19c946b04aac0eab039,0x19ca36b08aa09a6b052,0x1ac26ab099ac24ab091,0x1272ca72b1272aa1ca9,0x412ca272f89cbd]),([7,31,992,6494406,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1a79a67251ac0eab039,0x1ac24ab0919ca36b08a,0x1272aa1ca9ac26ab099,0x1272fa3ab9272ca72b1,0x44eca]),([7,31,992,8659208,12988812,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x1361a4d851360e8d839,0x136234d882361d4d872,0x136268d89936248d891,0x12732954ba552e4e2b1]),([7,31,992,8659208,17318416,21648020,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x145059141436048d810,0x136144d84a360e8d839,0x1361c4d86d361a8d852,0x136248d89136234d872,0x1452e8e2b136274d89a,0x514c245304d8bd]),([7,31,992,8659208,17318416,29224827,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x105058141436048d810,0x136144d84a360e8d839,0x1361c4d86d36188d852,0x136254d89236234d872,0x1052e8e2b136274d89a,0x105308d8bd]),([7,31,992,8659208,18400817,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1050581414ac04ab010,0x1ac18ab051ac0eab039,0x1a7a36b072ac1c6726d,0x1052aa1ca9ac24ab091,0x1052e814b9052ca72b1,0x414c2]),([7,31,992,8659208,18400817,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1228588a14ac04ab010,0x1ac146b04aac0eab039,0x1ac1cab0719c9b6b052,0x1872a6b092ac246828d,0x122ae88ab29cac48aaa,0x48ac222b06b0bd])]
def b83 : List (List Nat × List (Nat × Nat)) := [([7,31,992,8659208,19483218,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1580596014ac04ab010,0x1a79b6b051ac0eab039,0x1a0a36b082ac1cab071,0x1582aa1ca9ac24ab091,0x15830560ba582ca72b1]),([7,31,992,9741609,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac146b04aac0eab039,0x19ca36b08aa09a6b052,0x1ac26ab099ac24ab091,0x12f2ca72b12f2aa1ca9,0x104b2812c9a92f4bcba]),([7,31,992,9741609,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1a79a6b051ac0eab039,0x1ac24ab0919ca36b082,0x15caaa1ca9ac26ab099,0x15cae964b95caca72b1,0x44eca]),([7,31,992,10824010,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1ac18a8251ac0eab039,0x19ca36b08aac1aa9e69,0x1ac26ab099ac24ab091,0x1272ca72b1272aa1ca9,0x408ca273149cb9]),([7,31,1023,1082401,2164802,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a818aa051a80f6a03a,0x1a7a26a072a81c67469,0x1a826aa099a824aa091,0x11c325f8ba9cac5f4aa]),([7,31,1023,1082401,2164802,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1611898451610f5843a,0x1611c98471561a98469,0x1612658492612457e89,0x19cad526aa49aa5849a,0x4bcc95631526ba]),([7,31,1023,1082401,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144a04a2f0f4bc3a,0x12f1c8bc712f1a4a052,0x12f264bc922f244bc89,0x11c2ea70b51c2a4bc9a,0x414ca053249cbd]),([7,31,1023,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1445c4a1c0f4703a,0x11c1c870711c1a45652,0x11c24870911c2347081,0x12f2e870b11c2687099,0x414ca0532456bd])]
def b84 : List (List Nat × List (Nat × Nat)) := [([7,31,1023,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d851360f4d83a,0x1361c8d871361a8d869,0x136244d88d36208d881,0x1362c4d89a36264d892,0x49cca3631554c2]),([7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],hh [0x400e0]),([7,31,31744,1015808,1082401,2165730,8659208,17318416,32641156],[]),([7,31,31744,1082401,2164802,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946723e9c8ea7239,0x19c9aa72699c98a7255,0x19ca2672729c9c6726d,0x19ca6672929ca46728d,0x1ac2c526aa872a6729a,0x14531526ba9cad526b2,0x4f0c9]),([7,31,31744,1082401,2164802,4330468,32776456],hh [0x1b201ac804b200ac800,0x1b203ac80cb202ac808,0x14f0593c14b204ac810,0x1b21469c3eb20eac839,0x1b21aa9c69b218a9c55,0x1b2226c872b21c6c86d,0x19ba6ac892b12469c8d,0x1a72d53cb2aaac53aaa,0x11c3253cba]),([7,31,31744,1082401,2165730,4329604,9412872,17318416,32505856],[]),([7,31,31744,1082401,2165730,4329604,33047056],hh [0x1570195c04570095c00,0x1570395c0c570295c08,0x1458591614570495c10,0x157145583e570e95c39,0x1571a95c69571895855,0x1572355889571c9586d,0x145aa94c99572495c91,0x145ae958b545ac998b1,0x12f32514c5]),([7,31,31744,1082401,3115074,4329604,8659944,17318416,32505856],[])]
def b85 : List (List Nat × List (Nat × Nat)) := [([7,31,31744,1082913,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946723e9c8ea7239,0x19c9aa72699c98a7255,0x19ca2672729c9c6726d,0x19ca6672929ca46728d,0x1ac2c526aa872a6729a,0x14531526ba9cad526b2,0x4f0c9]),([7,31,31744,1083361,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11b0586c142f048bc10,0x128128bc3e2f0e8bc39,0x12f1a4bc552d148bc51,0x12f234bc892f1c4bc6d,0x1abac4bc9a2f264bc91,0x10432494bd1b2e8beb5,0x410ca]),([7,31,1047552,1082401,2164802,4329604,8659944,17318416,32505856],[]),([7,31,1047552,1082401,2164802,4329604,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x17e059f8149c84a7210,0x19c98a72519c8ea7239,0x19c9ca72719c9aa7269,0x19ca6672929ca467289,0x17c2cab0b17d2aa729a,0x11c325f8ba]),([7,31,1047552,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1445c4a1c0e87039,0x11c1c870711c1a47052,0x11c24870911c2346a81,0x12f2eaaab11c2687099,0x10532456bd]),([7,31,1047552,1082401,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1047552,1082401,4329604,8659944,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x14f8593e145c8497210,0x15c98572515c8e97239,0x15ca2572825c9c97271,0x14fac53eaa5ca49728a,0x12f3053eba272e53eb2,0x53ec2]),([7,31,1047552,1083361,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f814bb84aee10,0x17e185f8517e0e9f839,0x1bba490a817a1a9f262,0x17e2c5f4aa052691499,0x17e305ecbe15ae5f0b2,0x526ca1c325f8c2])]
def b86 : List (List Nat × List (Nat × Nat)) := [([7,31,1047552,1083361,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11b0586c142f048bc10,0x12f144a04a2f0e8bc39,0x12f244bc892f184b452,0x11b2e86cb12f268bc99,0x10432810c91b30972c1]),([7,31,1047552,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1528594a1436048d810,0x136188d851360e8d839,0x1361c8d871361a8d869,0x136234d88a36208d881,0x136268d89936248d891,0x4d8c552b08fab1]),([7,31,1048575,1082401,2164802,4330468,8659208],hh [0x14d01934044d0093400,0x14d039340c4d0293408,0x14d0593414bc04af010,0x14b98934514d0f5343a,0x1bba46dc8e4d1c93471,0x14d2c530aa0526af092,0x14d30534ba15ae534b6,0x52cce1c32534c2]),([7,31,1048575,1082401,2165730,4329604,17318416],hh [0x1458191604458091600,0x145839160c458291608,0x145859161437048dc10,0x1451891651458f5163a,0x18124a0491372391672,0x145ad916b145aa91499,0x12f32516c645ae89cb9,0x5f8ca]),([7,31,1048575,1082401,4329604,8659944,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x16a859aa145c8497210,0x15915972515c8f5723a,0x15ca2572825c9c97271,0x16aac5aaaa5ca697292,0x16ab08bcc16aae89cb9]),([7,31,1048575,1083361,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f814bb84aee10,0x17c989f8517e0f5f83a,0x1bba4aee91b6a39f871,0x17e2c5f4aa052691499,0x17e305ecbe15ae5f8b6,0x526ca1c325f8c2]),([7,31,1048575,1083361,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11b0586c142f048bc10,0x12f144a04a2f0f4bc3a,0x12f244bc8e2f224bc71,0x11b2d8bcb12f268bc99,0x1043246cc25cb046cba,0x410ca]),([7,31,1048575,2164802,4330468,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1271889c56270f49c3a,0x1272489c91272249c72,0x115ae972b9272c49c99,0x5a6ca69b2456c2])]
def b87 : List (List Nat × List (Nat × Nat)) := [([7,31,1049568,2164802,8659208,17318416,32505856],hh [0x1a901aa404a900aa400,0x1a903aa40ca902aa408,0x1270589c14a904aa410,0x1a91a67c51a90eaa439,0x1a9246a48aa91caa471,0x1272a6a49aa9266a492,0x1273089cc1272c89caa,0x115b2856c9]),([7,31,1082401,1082913,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946724a9c8fa723a,0x19c9a672629c9567252,0x19c9ca72719c9b6726a,0x19ca46728d9ca2a7289,0x1872a6729a9ca667292,0x19cad526b249ac526aa,0x105b2514c549ae926b9]),([7,31,1082401,1083361,2164802,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a8156a052a812aa03a,0x19d1c6a06aa81a6a062,0x1a724a9e91a822aa089,0x17e2c9f4aaa826aa099,0x470c99cae694b5]),([7,31,1082401,1083361,2164802,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x161155845261129843a,0x1611c5846a611a58462,0x15fa45848a612255872,0x149ac526aa612698499,0x12f32558c59caf526b2]),([7,31,1082401,1083361,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f144bc4a2f0f8bc3a,0x12f1a8bc692f154bc52,0x12f228bc892f1c4bc6d,0x12f268bc992f244bc8d,0x11c2e8bcb51c2c870b1,0x414ca05324b0bd]),([7,31,1082401,1083361,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c15470521c128703a,0x11c22470711c1a87069,0x11c26470951c248708a,0x19bae46cb52f2c8709a,0x10532814c9]),([7,31,1082401,2098144,4329604,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1450591414a084a8210,0x1a09a68252a092a8249,0x1a0a2682829c9c6826a,0x1a0a6a8299a0a5a828a,0x13630514b2452aa16a9,0x14532914c9]),([7,31,1082401,2164802,2165314,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c98a72529c946724a,0x19c9d672729c9aa7269,0x19ca4a72919ca2a7289,0x149aaa1ca99ca6a7299,0x13c32678c149ae526b2])]
def b88 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,2165730,4329604,32776456],hh [0x19d01a74049d00a7400,0x19d03a740c9d02a7408,0x17e059f8149d04a7410,0x19d18a74529d146744a,0x19d1d674729d1aa6469,0x19d24a74919d22a7489,0x17e2c9f4aa9ba6a7299,0x11c32672c1]),([7,31,1082401,2164802,2165730,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x161149845156139844a,0x1561c5846a611895856,0x1612298489611d58472,0x15fa655895612498491,0x1562f526b949ac926aa,0x12f32526c5]),([7,31,1082401,2164802,2165730,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x12f148bc512f128a03a,0x12f1c8bc6a2f1a4bc62,0x12f244bc8a2f224bc75,0x1272d470b22f264bc92,0x10832820c92c31470b9]),([7,31,1082401,2164802,2165730,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c14870511c1285c3a,0x11c1c8706a1b1a47062,0x11c244708a1c2247075,0x12f2c8709d1c2687092,0x1a1b2a86c99bb0456b5]),([7,31,1082401,2164802,4329604,4330116,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x13c058f0149c84a7210,0x19c98a72529c946724a,0x19c9ba726a9c9a67266,0x19ca0a72769c9ca7271,0x19ca4a72919ca2a7289,0x1872a6729d9ca6a7299,0x13c304d8bd05ac8f0aa,0x13c32526c5]),([7,31,1082401,2164802,4329604,4330468,32776456],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1ae05ab814a784a9e10,0x1a798a9e52a79469e4a,0x1a71ba9e6aa79a69c66,0x1a7a0a9c76a79ca9e71,0x1a72667292a7a2a9489,0x1ae2cab8aaa7a769e9a,0x672c9a7316b8c1]),([7,31,1082401,2164802,4329604,4330468,33047056],hh [0x15f8197e045f8097e00,0x15f8397e0c5f8297e08,0x14a05928145f8497e10,0x15f9897e525f9457e4a,0x15f9c97e715f9a97e69,0x15fa494c915fa297e82,0x14a2c928aa5fa757e9a,0x149b354cbd]),([7,31,1082401,2164802,4329604,8659944,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a81a6a052a8146a04a,0x1a820aa072a81c6a06a,0x1a72667492a822a9489,0x1b7b05f8b27e2aa9e9a,0x672c9])]
def b89 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4329604,9436424,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x178859e2149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca6a72929ca46728a,0x1b7b05e2b278aaa1ca9,0x181b2ab0c9]),([7,31,1082401,2164802,4329604,16777728,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9a672529c946724a,0x19ca0672729c9c6726a,0x19ca46728a9ca267282,0x1872a6729a9ca667292,0x13c30514bd49ac926aa,0x526c9]),([7,31,1082401,2164802,4329604,32505856,32506368],hh [0x1498192604498092600,0x13c038f00c498292608,0x1498592614498492610,0x1059a5265249945244a,0x149a041472451c4166a,0x145255269249a292682,0x149aa926a95fa68f099,0x13c30514bd9e2e926b2,0x526cd49b28f0c2]),([7,31,1082401,2164802,4329604,32505856,33553695],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab01478049e010,0x1ac1a6b052ac146b04a,0x187206b072ac1c6b06a,0x1ac2aade9978229e082,0x1a0aeab0b5ac2cab0ad,0x178336b0caac3169ec2]),([7,31,1082401,2164802,4329604,32505856,33553919],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a7214498492610,0x19c9a672529c946724a,0x18720672729c9c6726a,0x13c265149549a292682,0x19cad672b29cab672aa,0x19cb1672c29caf672ba,0x149b3672ca]),([7,31,1082401,2164802,4329604,32506848,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x17e059f8149c84a7210,0x19c9a672529c946724a,0x19ca0672729c9c6726a,0x19ca5672929ca2a7282,0x17e2c9f4aa9ca6a6e99,0x5ecce9cb2470c1]),([7,31,1082401,2164802,4329604,32776456,32777192],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72147e049f810,0x19c9a672529c946724a,0x17e20a72729c9c6726a,0x19caca72aaa2265f88a,0x19cb0a6ec19caf672ba,0x17e33672ca]),([7,31,1082401,2164802,4329604,32776456,33553439],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x1a805aa0147e049f810,0x1a81a6a052a8146a04a,0x17d20aa072a81c6a06a,0x1a82b6a0aa1c265f88a,0x1a7b0a74baa52d6a0b2,0x1ac32a9cc5])]
def b90 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4329604,33047056,33553439],hh [0x1610198404610098400,0x161039840c610298408,0x1610598414498492610,0x1611a5845261145844a,0x149a098472611c5846a,0x1612a8bc9956255268a,0x1562f584ba612c984ad,0x149b397ec2]),([7,31,1082401,2164802,4330116,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca3a728a9ca267286,0x19ca6672969ca4a7291,0x14d2aa1ca99ca7a729a,0x14d324fcc1452f534b2,0x19cb3534ca]),([7,31,1082401,2164802,4330116,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca3a728a9ca267286,0x19ca6a72969ca4a7291,0x149ac926aa872a6729e,0x149b2926c93c30514bd,0x672cd]),([7,31,1082401,2164802,4330116,32505856],hh [0x19c81e72059c80e7201,0x19c83e720d9c82e7209,0x19c8fe723b4984d2611,0x19c95e72539c93e724b,0x19c9be726b9c99e7263,0x19ca1d26839c9de7273,0x149a5d26939ca3d268b,0x149a7cf09b]),([7,31,1082401,2164802,4330468,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a59a69e52a79469e4a,0x1a7a269e829c9ca9e6a,0x1a7a669e92a7a469e8a,0x14d2c934aa872a69e9e,0x534ca4d32672c1]),([7,31,1082401,2164802,4330468,8659208,32505887],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a794a9e51a79283049,0x19c9ca9e6aa59a69a61,0x1a7a469e8aa7a269e82,0x14d2aa9e9ea7a669e92,0x14d32930c94d2ca9ead]),([7,31,1082401,2164802,4330468,8659208,32539681],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a794a9e51a792a903a,0x1a7a269e829c9ca9e6a,0x1a7a669e92a7a469e8a,0x1a7ad534b24d2aa9e9e,0x534ca4d32672c1]),([7,31,1082401,2164802,4330468,8659208,32776456],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a59a69e52a79469e4a,0x1a721a9e829c9ca9e6a,0x1a7a469c8ea7a2a9e89,0x1a726a9e99a725a9e92,0x19cb0534b24d2aa9e9e,0x69ecd4d32934c9])]
def b91 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,4330468,8659231,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14c0593014a784a9e10,0x1a79469e4aa79269e39,0x1a79aa9669a79869e52,0x1a7a2a9e85a7a0a7272,0x14c2a69e9ea7a4a9e91,0x14c32672c14c2c930aa,0x530ca]),([7,31,1082401,2164802,4330468,9741609,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a79aa9e52a79469e4a,0x1a7a369e8aa7a0a7272,0x1a7a7a9e99a7a4a9e91,0x19cb0534b24d2aa1ca9,0x14d32934c9]),([7,31,1082401,2164802,4330468,10824010,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a59a69e52a79469e4a,0x1a7a0a7272a79c69e6a,0x1a7a569e92a7a2a9e89,0x14d2aa1ca9a7a7a7299,0x14d32672c14d2f534b2]),([7,31,1082401,2164802,4330468,17318416,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x1ad85ab614a704a9c10,0x1a714a9c51a71285c3a,0x19b9ca9c6aa51a47062,0x1a722a9c89a721a9c82,0x1a725a9c92a72469c8e,0x1682aa9c9e1c2769c9a,0x1adb2470c115ad6b6b2,0x1a7336b6ca]),([7,31,1082401,2164802,4330468,21648020,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a79aa9e52a79469e4a,0x1a7a269e829c9ca9e71,0x19ca769e92a7a469e8a,0x14d2c934aa872a69e9e,0x534c99cb0534bd]),([7,31,1082401,2164802,4330468,24895223,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a59a69e52a79469e4a,0x1a7a2a9e829c9ca9e6a,0x1a7a769e95a7a4a9e8d,0x14d2c934aa872a69e9e,0x534cea7b2672c1]),([7,31,1082401,2164802,4330468,32505856,32776456],hh [0x14d01934044d0093400,0x1b983ae60c4d0293408,0x14d05934144d0493410,0x1b91a534524d1452e4a,0x14d2093481051cae66a,0x1a724a9c8e4d22a9c86,0x1a727ae69ab72653496,0x11c30534ba4d2c930aa,0x14d33534ca4d3252cc6]),([7,31,1082401,2164802,4330468,32776456],hh [0x1a701e9c05a700e9c01,0x1a703e9c0da702e9c09,0x1a70fe9c3b4d04d3411,0x1a715e9c53a713e9c4b,0x1a71be9c6ba719e9c63,0x1a721d3483a71de9c73,0x14d25d3493a723d348b,0x14d27eb69b])]
def b92 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,5412837,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a794a9e51a792a9e3a,0x1a7a0a7272a79b69e6a,0x1a7a4a9e91a7a2a9e89,0x14d2aa1ca9a7a7a9e99,0x14d32672c1a5ad534b2,0x534ca]),([7,31,1082401,2164802,6495206,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c9aa68699c94a7251,0x19ca2672829c9d67272,0x19ca6672929ca46728a,0x14d2c934aa872a6729e,0x14d32934c94d31a72c1]),([7,31,1082401,2164802,8659208,8659944,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x10505814142f048bc10,0x12f188bc522f144a03a,0x12f1c8bc712f1a8bc69,0x12f248bc8a2f224bc82,0x1272d414b22f274bc9a,0x4b0cd4e32814c2]),([7,31,1082401,2164802,8659208,12989420,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a79a69e52a79469e4a,0x1a5a269e72a79c69e6a,0x1a7a769e9a9ca4a9e8a,0x14d30534b24d2aa1ca9,0x19cb2534c2]),([7,31,1082401,2164802,8659208,16236527,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c9a672529c946723a,0x19ca2a72729c9c6726a,0x19ca6a72959ca4a728d,0x14d2c934aa872a6729d,0x19cb2534c24d30668b5,0x534ce]),([7,31,1082401,2164802,8659208,17317904,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12c058b0149c84a7210,0x19c9a672529c946723a,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x12c2c8b0aa872a6729a,0x11c324b0c22c30668b5,0x470ca]),([7,31,1082401,2164802,8659208,29223963,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x12c058b014a784a9e10,0x1a798a9e52a79469e4a,0x1a79ca9e71a79aa9e69,0x1a7a667292a5a369e8a,0x12c2c8b0aa872a69e9a,0x6dcc92c308b0c1]),([7,31,1082401,2164802,8659208,32505856,32642020],hh [0x14d01934044d0093400,0x14d039340c4d0293408,0x19c85a72144d0493410,0x14c18934524d1452e4a,0x14d1c934714d1a93469,0x14d265348a4d2093481,0x14aaf672ba9cac9349a,0x14d33672ca4b31672c2])]
def b93 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2164802,8659208,33047056,33553439],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc141c0487010,0x12f1a4bc522f144a03a,0x11c228bc722f1c4bc6a,0x12f2a8149a052649c8d,0x12f2e8bcb52f2c8bcad,0x470ce1c334bcc2]),([7,31,1082401,2164802,8659720,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12c058b0149c84a7210,0x19c9a672529c946723a,0x19ca2672729c9c6726a,0x1872a672929ca46728a,0x12c30668b52c2c8b0aa,0x470ca1c324b0c2]),([7,31,1082401,2164802,8659944,17318416,32776456],hh [0x1a701a9c04a700a9c00,0x1a703a9c0ca702a9c08,0x12f058bc14a704a9c10,0x11c18a9c52a71469c3a,0x1a72266e72a71aa9469,0x1a726a9c92a72469c8a,0x1a52d4bcb22f2a8709d,0x414ca053266ec1]),([7,31,1082401,2164802,17318416,32506848,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x11c1a470521c1445c3a,0x11c20470721c1c4706a,0x11c2485c8d1c2287082,0x115ad4bcb21c2787099,0x19bb2414c1]),([7,31,1082401,2164802,17318416,32776456,32777192],hh [0x19b81a6e049b80a6e00,0x19b83a6e0c9b82a6e08,0x19b85a6e142f048bc10,0x19b9a66e529b9466e3a,0x12f20a6e729b9c66e6a,0x11c2a8149999234bc8a,0x19bb066eba9bad66eb2,0x4bccd9bb2870c6]),([7,31,1082401,2164802,17318416,32776456,33553439],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c05870142f048bc10,0x11c1a470521c1445c3a,0x12f22870721c1c4706a,0x11c2a8149a05264568d,0x11c2e86cb51c2c870ad,0x476ca1c31870c5]),([7,31,1082401,2164831,4330468,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14b8592e14a784a9e10,0x1a794a9e4da792a9e39,0x1a7a069e6aa59a69e61,0x1a7a469e8aa7a269e82,0x14baa69e9ea7a669e92,0x14bb2672c14bac92eaa,0x52eca]),([7,31,1082401,2165314,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca6672969ca2a7289,0x149ac926aa872a6729a,0x526ca49b24f0c1])]
def b94 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165314,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12c058b0149c84a7210,0x19c9a672529c946723a,0x19ca2672729c9c6726a,0x1872a6729a9ca66728a,0x12c30668b52c2c8b0aa,0x470ca1c324b0c2]),([7,31,1082401,2165730,4329604,8659208,33047056],hh [0x1560195804560095800,0x156039580c560295808,0x1080582014560495810,0x130189585256128a23a,0x12f1d94c71561a95869,0x1562295889562195882,0x156259589256245588e,0x1462a9589e562695899,0x108324bcc1452f5ceb2,0x15633420ca]),([7,31,1082401,2165730,4329604,10824010,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x17e059f814a084a8210,0x1a09a68252a0946824a,0x1a0a0a82729c9c6826a,0x1a0a668296a0a2a8289,0x17e2c9f8aa872a6829a,0x17e325cec1]),([7,31,1082401,2165730,4329604,16236015,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09aa8269a094a824a,0x1a0a36828aa0a0a7271,0x1872a6829da0a6a8296,0x1a0b24dcc145ac916aa,0x516ce]),([7,31,1082401,2165730,4329604,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09aa8269a094a824a,0x1a0a2a8289a0a0a7271,0x1872a6829aa0a668296,0x145b24dcc145ac916aa,0x516ca]),([7,31,1082401,2165730,4329604,17318416,32505887],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a01868252a09282249,0x1a0a0a7271a09aa8269,0x1a0a668296a0a2a8289,0x145aca82ad45aaa829a,0x145b2916c9]),([7,31,1082401,2165730,4329604,17318416,32539681],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a0948e451a092a5c3a,0x1a0a0a7271a09aa8269,0x1a0a668296a0a2a8289,0x1a0ad516b245aaa829a,0x516ca45b2420c1]),([7,31,1082401,2165730,4329604,17318416,33047056],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09aa8269a094a824a,0x1a0a255886a0a0a7271,0x1a0a5958925623a828a,0x145aa9589ea0a6a8299,0x145b24dcc1452f516b2,0x1a0b3516ca])]
def b95 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165730,4329604,17318431,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a094a824aa09268239,0x19c9c6826aa09a68261,0x1a0a5a828aa0a168282,0x145ac916aa45aa6829a,0x516ca45b24dcc1]),([7,31,1082401,2165730,4329604,18400817,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09a68252a0946824a,0x1a0a2a82829c9c6826a,0x1a0a6a8299a0a5a828d,0x173b0516b245aaa1ca9,0x145b2916c9]),([7,31,1082401,2165730,4329604,21648020,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x17e059f814a084a8210,0x1a09aa8269a094a824a,0x1a0a268282a09ca7271,0x1a0a76829aa0a5a828a,0x137305f8b27e2aa1ca9,0x5f8c9]),([7,31,1082401,2165730,4329604,32505856,33047056],hh [0x1458191604458091600,0x137038dc0c458291608,0x1458591614458491610,0x1081a8206945949144a,0x156219168245a051471,0x156259169256239168a,0x145aa9169e56268dc99,0x12f30516be452f516b2,0x145b3516ca45b25f8c2]),([7,31,1082401,2165730,4329604,33047056],hh [0x15601d58055600d5801,0x15603d580d5602d5809,0x1560fd583b4584d1611,0x15615d58535613d584b,0x1561bd586b5619d5863,0x15621d1683561dd5873,0x145a5d16935623d168b,0x145a7cdc9b]),([7,31,1082401,2165730,5412005,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a094a8251a092a823a,0x1a0a0a7271a09b6826a,0x1a0a668296a0a2a8289,0x145ac916aa872a6829a,0x145b2916c9083067cb5]),([7,31,1082401,2165730,10824010,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x12f058bc14a084a8210,0x1a094a8251a092a823a,0x1a0a2a8289a09aa8269,0x1872a6829aa0a668292,0x12f3067cb52f2c8bcaa,0x11bb286ec9]),([7,31,1082401,2165730,17318416,21648020,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09aa8269a094a824a,0x1a0a6a828aa0a268272,0x145ac916aa872a6829d,0x4bcc945b0916c1])]
def b96 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,2165730,17318416,29224827,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x11b8586e14a084a8210,0x1a09a68262a094a824a,0x1a0a36828aa09da826a,0x1872a6829da0a6a7295,0x11bb086ec11bac86eaa,0x4dcc9]),([7,31,1082401,2165730,17318416,32505856,32641156],hh [0x1458191604458091600,0x145839160c458291608,0x137058dc14458491610,0x1459a5166245949144a,0x145a091681459d9166a,0x145a69169945a49168a,0x137328bcc27e30420b2,0x516cd]),([7,31,1082401,2165759,4329604,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1450591414a084a8210,0x1a09a68252a0936824a,0x1a0a0a82819c9c6826a,0x1a0a668296a0a2a8289,0x1452c914aa452a6829a,0x514ca45324d8c1]),([7,31,1082401,2194498,4329604,9412872,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x177859de149c84a7210,0x19c9aa72699c94a724a,0x19ca46728a9ca0a7271,0x177aaa1ca99ca6a7292,0x184b2abac9b7b05deb2]),([7,31,1082401,3144770,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x177859de149c84a7210,0x19c9aa72699c94a724a,0x19ca2a72899ca0a7271,0x19ca6a72999ca4a7291,0x1b7b05deb277aaa1ca9,0x177b29dec9]),([7,31,1082401,3144770,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9aa72699c94a724a,0x19ca26728298a067271,0x19ca6a72999ca4a728a,0x1b830526b249aaa1ca9,0x6c0c9]),([7,31,1082401,3247203,4330468,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a79aa9e55a794a9e4a,0x1a7a2a9e89a7a0a7272,0x1a7a7a9e99a7a4a9e91,0x14d2c934b14d2aa1ca9,0x534ca4d32672c1]),([7,31,1082401,3248099,4329604,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09a68255a094a824a,0x1a0a2682829c9c6826a,0x1a0a6a8299a0a5a828a,0x145ac916b145aaa1ca9,0x516ca45b24d8c1])]
def b97 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,6495206,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c9aa72629c94a7251,0x19ca2672829c9d67272,0x19ca7a72929ca46728a,0x14531914b2452aa1ca9,0x14532914c9]),([7,31,1082401,4329604,8389600,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18ab061ac14ab051,0x1ac226b082a79cab06a,0x1882a6b092ac246b08a,0x15cb0972b2592c572aa,0x5b8ca]),([7,31,1082401,4329604,8659208,16777728,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x15c85972149c84a7210,0x19c9a672629c94a7251,0x19ca0672729c9c6726a,0x19ca46728a9ca267282,0x1872a6729a9ca667292,0x15cb0972b2592c572aa,0x672c5]),([7,31,1082401,4329604,8659720,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x16505994149c84a7210,0x19c9a672629c94a7251,0x19ca0a72729c9c6726a,0x19ca4a72919ca2a7289,0x1652c98cb1652aa1ca9,0x16e32994c2]),([7,31,1082401,4329604,8659944,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bc85af214ac04ab010,0x1ac1a6b062ac14ab051,0x1ac20a9e72ac1c6b06a,0x1ac24ab091ac22ab089,0x1b7ae6f2b2bcaaa1ca9,0x6f2c2]),([7,31,1082401,4329604,8659944,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bc85af214ac04ab010,0x1ac1aab062ac14ab051,0x1ac236b08aac20a9e72,0x1bcaaa1ca9ac256b092,0x16ab3af2c2bcaca4eb1]),([7,31,1082401,4329604,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac22ab089ac20a9e72,0x15caaa1ca9ac24ab091,0x16e32972c25cac964b1]),([7,31,1082401,4329604,8659944,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18ab052ac146a849,0x1ac226b082a79cab06a,0x15caaab092ac246b08a,0x16e32972c25cacab0ad])]
def b98 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,8659944,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac246b08aac226b082,0x15cac972aa862a6b092,0x1ac3356acaac31572c2]),([7,31,1082401,4329604,8659944,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18ab052ac1468a3a,0x1ac20a9e72721b6b06a,0x1ac24ab091ac22ab089,0x15cb0ab0b55cac972aa,0x5b8ca]),([7,31,1082401,4329604,8659944,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac22ab089ac20a9e72,0x1592c572aaac24ab091,0x590ca5cb0972b2]),([7,31,1082401,4329604,8659944,17318416,32777192],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac246b08aac226b082,0x15cb0972b25caaab092,0x6b0cd5ab2ab0c5]),([7,31,1082401,4329604,8659944,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x16e059b814ac04ab010,0x1ac1aab062ac14ab051,0x1ac22ab089ac20a9e72,0x16dac5b8aaac24ab091,0x16e32a72c55ab09b8b2,0x6b0cd]),([7,31,1082401,4329604,8659944,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac14ab051ac126b039,0x1a79cab06aac18ab061,0x1ac24ab08aac216b082,0x15cac964b15caa972a9,0x16e32972c2]),([7,31,1082401,4329604,8659944,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1a6b062ac14ab051,0x1ac22ab082a79cab06a,0x1872a6b092ac246b08d,0x16e32972c25cac972aa]),([7,31,1082401,4329604,8659944,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac226b082a79cab071,0x1872a6b095ac24ab08a,0x15bae572b2592c572aa,0x572c2])]
def b99 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4329604,8659967,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac196b062ac14ab051,0x1ac20ab081a79cab06a,0x1ac24ab091ac22ab089,0x15cac964b15caa972a9,0x16e32972c2]),([7,31,1082401,4329604,9436424,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x15c85972149c84a7210,0x19c9aa72629c94a7251,0x19ca26728298a067272,0x19ca6a72929ca46728a,0x15cac964b15caaa1ca9,0x572c2]),([7,31,1082401,4329604,9742313,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab062ac14ab051,0x1ac226b082a79cab06d,0x1872a6b092ac246b08a,0x16e32972c25cac972aa]),([7,31,1082401,4329604,12989420,17318416,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x15c8597214a784a9e10,0x1a79aa9e62a794a9e51,0x1a7a269e82a79d69e72,0x1872a69e92a7a469e8a,0x15cae572b2592c572aa,0x5b8ca]),([7,31,1082401,4329604,17318416,24894487,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ba85aea14ac04ab010,0x1ac1a6b062ac14ab051,0x1ac20ab072ac1c6b06a,0x1baaaa1ca9a7a4ab08a,0x15cb3aeac2baaca4cb1]),([7,31,1082401,4329604,17318416,31388701,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1458591614a084a8210,0x1a09a68262a094a8251,0x1a0a0a8272a09c6826a,0x1872a682999ca4a828a,0x145b04dcb945ac916aa,0x516c2]),([7,31,1082401,4330116,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c9a672629c94a7251,0x19ca0a72729c9c6726a,0x19ca6672929ca2a7289,0x1452c514aa872a6729a,0x16d32a72c54530914b2,0x672cd]),([7,31,1082401,4330468,8659208,10824010,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1bc05af014a784a9e10,0x1a79a69e62a794a9651,0x1a7a0a9e72a79c69e6a,0x1a7a6a7291a7a2a9e89,0x1bc2caf0aa872a69e9d,0x69ec5bc30a72b9])]
def b100 : List (List Nat × List (Nat × Nat)) := [([7,31,1082401,4330468,8659208,21648020,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1488592214a784a9e10,0x1a79aa9e69a798a9e52,0x1a7a269e82a79ca9e71,0x1a7a6a9e999ca569e8a,0x148ac91cb148aaa1ca9,0x69ec548b0a72b9]),([7,31,1082401,4330468,8659208,31389629,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1488592214a784a9e10,0x1a79a69e62a794a9651,0x1a7a0a9e76a79c69e6a,0x1a7a6a7295a7a369e8a,0x148ac922aa872a69e9d,0x522c24830672b9]),([7,31,1082401,5412005,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18ab055ac14ab03a,0x1ac20a9e72ac1aab069,0x1ac24ab091ac22ab089,0x1a92d572b25caaa1ca9,0x16e32972c2]),([7,31,1082401,8659944,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac14ab051ac12ab03a,0x1ac22ab089ac1aab069,0x1872a6b09aac266b092,0x12f2eaa4b52f2c8bcaa,0x10532814c9]),([7,31,1082401,8659944,17318416,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1450591414ac04ab010,0x1ac1aab069ac14ab04a,0x1ac26ab08aac226b072,0x1452c514aa872a6b09d,0x14530914c1452e914b2]),([7,31,1082401,8659944,17318416,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1050581414ac04ab010,0x1ac1a6b062ac14ab04a,0x1a7a56b08dac22ab06a,0x1052aa1ca9ac276b09a,0x10530814ba052c814b1]),([7,31,1082913,2164802,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca3a728a9ca267286,0x19ca6672969ca4a7291,0x14d2aa1ca99ca7a729a,0x14d324fcc1452f534b2,0x19cb3534ca]),([7,31,1082913,2164802,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca46728e9ca2a7286,0x19ca6a72999ca5a7292,0x149ac926aa872a6729e,0x149b2926c93c30514bd,0x672cd])]
def b101 : List (List Nat × List (Nat × Nat)) := [([7,31,1082913,2164802,4329604,32505856],hh [0x19c81e72059c80e7201,0x19c83e720d9c82e7209,0x19c8fe723b4984d2611,0x19c95e72539c93e724b,0x19c9be726b9c99e7263,0x19ca1d26839c9de7273,0x149a5d26939ca3d268b,0x149a7cf09b]),([7,31,1082913,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12c058b0149c84a7210,0x19c9a672529c946723a,0x19ca2a72729c9c6726a,0x19ca6a72999ca4a7291,0x12c304b0b22c2aa1ca9,0x470ca1c324b0c2]),([7,31,1082913,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c9a672629c94a7251,0x19ca0a72729c9c6726a,0x19ca6672929ca46728a,0x1452c514aa872a6729a,0x14532a72c54530914b2,0x672cd]),([7,31,1083361,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aa9e69a0946b04a,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x17e2c9f8aa872a6b09a,0x5f8ca7e326dac1]),([7,31,1083361,2164802,4329604,8659208,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1aa1868251ac1283c49,0x1ac1cab071ac1aa9e69,0x1ac246b08eac226b082,0x17e2aab09aac266b092,0x17e329f4c97e2cab0ad]),([7,31,1083361,2164802,4329604,8659208,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1cab071ac1aab04a,0x1ac246b08eac226b082,0x134aa6b09aac266b092,0x1b6b05e4bd7e2c9f8aa,0x1ac335f8ca]),([7,31,1083361,2164802,4329604,8659208,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1a79a68251ac12a903a,0x1ac20ab072ac1c6b06a,0x1ac24ab091ac23ab089,0x17e2c9f8aaac26ab099,0x5f8ca7e326dec1]),([7,31,1083361,2164802,4329604,8659208,32540641],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1c6b06aac12a903a,0x1ac23ab089ac20ab072,0x1ac26ab099ac24ab091,0x1792f6b0b57e2c9f8aa,0x6b0cd7e32adac1])]
def b102 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,4329604,8659208,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aa9e69a0946b04a,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1b6b05f8b27e2aab09a,0x1ac335f8ca]),([7,31,1083361,2164802,4329604,8659208,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1af05abc14ac04ab010,0x13018a8251ac128a23a,0x12f1bab06aa79a6ae66,0x1ac208bc76ac1cab071,0x1ac24ab091ac23ab089,0x1af2a8bc9dac26ab099,0x12f314bcc124ad6bcb2,0x1af32abcc9]),([7,31,1083361,2164802,4329604,8659231,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17d059f414ac04ab010,0x1a0946b04aac126b039,0x1ac1c6b06aa79a6b061,0x1ac23ab085ac20ab072,0x17d2a6b09aac24ab091,0x17d326dac17d2c9f4aa,0x5f4ca]),([7,31,1083361,2164802,4329604,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1a79a6b052a0946b04a,0x1ac20ab072ac1c6b06a,0x1ac256b092ac23a8289,0x17e2aa1ca9ac26ab099,0x17e324fcc17e2f5f8b2]),([7,31,1083361,2164802,4329604,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1ac1c69e69a0946b04a,0x1ac23a9e89ac20ab072,0x1ac276b09aac24ab091,0x1bbb0526b249aaa1ca9,0x632c9]),([7,31,1083361,2164802,4329604,17318416,32539681],hh [0x13d818f6043d808f600,0x13d838f60c3d828f608,0x14985926143d848f610,0x139148f6513d928f03a,0x13da08f6723d9c4f469,0x13da64f6923da44f68e,0x109304e4bd49aa8f69a,0x149b2926c9]),([7,31,1083361,2164802,4329604,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1a79a6b052a0946b04a,0x19ca36b082ac1cab071,0x1ac266b092ac246b08e,0x149ac926aa872a6b09a,0x149b2926c93f30514bd]),([7,31,1083361,2164802,4329604,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aa9e69a0946b04a,0x1ac236b082ac1cab071,0x1ac26ab095ac24ab08e,0x17e2c9f8aa872a6b09d,0x5f8ceac326dac1])]
def b103 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,4329604,32505856,32776456],hh [0x17e019f8047e009f800,0x1b903ae40c7e029f808,0x17e059f8147e049f810,0x1b91aae4697e145f24a,0x17e209f881051c91471,0x1b926ada99a524a948e,0x11c305f8ba8cad9f4aa,0x5f8cd7e32a32c2]),([7,31,1083361,2164802,4330468,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aa9669ac146b04a,0x1ac23ab089ac20ab072,0x1ac27ab099ac24ab091,0x1b6b05f8b27e2aa1ca9,0x17e329f8c9]),([7,31,1083361,2164802,5412005,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aa8251ac12ab03a,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x17e2c9f8aa872a6b09a,0x5f8ca7e326dec1]),([7,31,1083361,2164802,5412005,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13c858f214ac04ab010,0x1ac14a8251ac12ab03a,0x1ac23ab082ac1cab071,0x1ac26ab099ac24ab091,0x136af4f2b23caaa1ca9,0x4f2ca3cb2424c1]),([7,31,1083361,2164802,5412837,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1aab051ac12ab03a,0x1ac226b082ac1cab06d,0x1ac266b092ac246b08e,0x17e2c9f8aa872a6b09e,0x17e329f8c9b6b0696b5]),([7,31,1083361,2164802,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1cab06a9c9a68251,0x1ac23ab089ac20ab075,0x1ac26ab099ac24ab091,0x1ac305f8b27e2aa1ca9,0x5f8ca7e325f8c6]),([7,31,1083361,2164802,8659208,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1c6b069a0946b04a,0x1ac246b08aa7a26b072,0x1872a6b09dac26ab092,0x17e309f8c17e2c9f8aa,0x470c9]),([7,31,1083361,2164802,8659208,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac1c6b069a0946b03a,0x1ac256b092ac22ab072,0x17e2aa1ca9ac276b09a,0x1ac325f8c27e305f8b2,0x5f8ce])]
def b104 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1c6b069a0946b03a,0x1ac24ab091ac22ab072,0x12f2aa1ca9ac26ab099,0x11b324bcc22f304bcb2,0x46cca]),([7,31,1083361,2164802,8659208,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a682510f126b03a,0x1ac246b08aac1cab071,0x12f2aab09aac266b092,0x11b328bcc22f2cab0ad]),([7,31,1083361,2164802,8659208,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1cab071ac1a6b03a,0x1ac266b092ac246b08a,0x12f2c8bcaa34aa6b09a,0x11b3286cc92f30aa4b5]),([7,31,1083361,2164802,8659208,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1c6b069a0946b03a,0x1ac24ab091ac22ab072,0x12f2c8bcaaac26ab099,0x11c32870c92f308bcc1]),([7,31,1083361,2164802,8659208,17318416,32540641],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1cab071ac1a6b03a,0x1ac266b092ac246b08a,0x1ac2d4bcb22f2aab09a,0x46cca1b324bcc2]),([7,31,1083361,2164802,8659208,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a47c62a0946b03a,0x1ac22ab072ac1c4786e,0x1ac26ab099ac24ab091,0x1ac314bcc22f2c8bcaa,0x10432810c9]),([7,31,1083361,2164802,8659208,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11b0586c14ac04ab010,0x1ac1c6b069a0946b03a,0x1ac22aae863020ab072,0x12f25ab092ac244bc8e,0x11b2a8bc9eac26ab099,0x10430810c19a2d46cb2,0x6b0cd1b3286cc9]),([7,31,1083361,2164802,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1c6b069ac146b03a,0x1ac26ab092ac22ab072,0x12f304bcb22f2aa1ca9,0x46cca1b324bcc2])]
def b105 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1cab071ac1a68251,0x1ac24ab0919ca36b08a,0x12f2aa1ca9ac26ab099,0x11c324bcc22f304bcb2,0x470ca]),([7,31,1083361,2164802,8659208,18401265,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1cab071ac1a6b051,0x1ac26ab092ac236b08a,0x12f304bcb22f2aa1ca9,0x46cca1b324bcc2]),([7,31,1083361,2164802,8659208,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a68251ac12ab03a,0x1ac24ab08aac1cab071,0x1872a6b09aac266b095,0x12f308bcc12f2c8bcaa,0x46cc9]),([7,31,1083361,2164802,8659208,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a6b062a0946b03a,0x1ac22ab072ac1c6b06e,0x1ac276b09aac24ab091,0x12f304bcb22f2aa1ca9,0x410ca04324bcc2]),([7,31,1083361,2164802,8659208,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1a6b062a0946b04a,0x1ac22ab072ac1c6b06e,0x1ac26ab095ac24a9e8d,0x12f2c8bcaa872a6b09d,0x6dac92f308bcc1]),([7,31,1083361,2164802,8659208,32505856,32641156],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x1b685ada147e049f810,0x17e1a5f4627e145f24a,0x17e205f8727e1c5ec6e,0x17e265f8927e229f882,0x149b06b0bab6ac9f89a,0x5f8cdb6b2870c2]),([7,31,1083361,2164802,8659208,32505856,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11b0586c142f048bc10,0x12f1c4bc692f144a03a,0x12f218bc822f204bc72,0x12f258bc922f238bc8a,0x11b2c8bc9e2f268bc99,0x10430810c11b2e892b5,0x4bccd1b3286cc9]),([7,31,1083361,2164802,8659208,33047056],hh [0x12f01cbc052f00cbc01,0x12f03cbc0d2f02cbc09,0x12f0fcbc3b1b04c6c11,0x12f15cbc532f13cbc4b,0x12f1bcbc6b2f19cbc63,0x1aba1c6c832f1dcbc73,0x12f25c6c932f23c6c8b,0x12f27c109b])]
def b106 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,2164802,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac14a8251ac12ab03a,0x1ac22ab075ac1ca8269,0x1ac26ab099ac24ab091,0x12f2f4bcb22f2aa1ca9,0x46cca1b324bcc1]),([7,31,1083361,2164802,17318416,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13c858f214ac04ab010,0x1ac1c6b06aa0946b03a,0x1ac256b092ac236b072,0x13caaa1ca9ac276b09a,0x1ac324f2c23cb04f2b2,0x4f2ce]),([7,31,1083361,2164802,17318416,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x11b0586c14ac04ab010,0x1ac1bab062a0946b03a,0x1ac24ab091ac1cab071,0x11b2aa1ca9ac276b09a,0x1043246cc21b3046cb2,0x410ca]),([7,31,1083361,2164802,17318416,32505856,32776456],hh [0x11b0186c041b0086c00,0x11b0386c0c1b0286c08,0x12f058bc141b0486c10,0x11b1c46c6a1b144563a,0x11b2386c821b2046c72,0x12f2e86c9a1b2646c92,0x11b334bcca0430810c1]),([7,31,1083361,2164831,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17c859f214ac04ab010,0x1ac186b04dac12ab039,0x1ac206b071ac1aa9e69,0x1ac246b08eac226b082,0x17caa6b09aac266b092,0x17cb26dac17cac9f2aa,0x5f2ca]),([7,31,1083361,4329604,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bb85aee14ac04ab010,0x1ac1ca7269ac18a9e51,0x1ac23ab089ac20ab075,0x1ac26ab099ac24ab091,0x14531aeeb2bbaaa1ca9,0x1bbb2ae4c9]),([7,31,1083361,4329604,8659208,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1bb85aee14ac04ab010,0x1ac1a6b062ac14a9e51,0x1ac20ab072ac1c6b06a,0x1ac26ab092ac2468289,0x1bbacaeeaa872a6b09d,0x6b0c5bbb0adab9]),([7,31,1083361,4329604,8659208,17318416,32539681],hh [0x139018e40439008e400,0x139038e40c39028e408,0x15c859721439048e410,0x1391a4e46238944d83a,0x139208e472391c4e46a,0x139264e49239244d88d,0x15cb08e2b15caa8e49a,0x145328e4c5])]
def b107 : List (List Nat × List (Nat × Nat)) := [([7,31,1083361,4329604,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13a858ea14ac04ab010,0x1ac1aab069ac18a9e51,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x13ab08eab23aaaa1ca9,0x14532ab0c5]),([7,31,1083361,4329604,8659208,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13a858ea14ac04ab010,0x1ac1a6b062ac14a9e51,0x1ac20ab072ac1c6b06e,0x1ac26ab095ac24a828d,0x13aac8eaaa872a6b09d,0x4eac23a304e6b9]),([7,31,1083361,5412005,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac1aab069ac18ab03a,0x1ac246b082ac1cab071,0x1872a6b09aac266b092,0x1ac31572c25cac972aa,0x4daca]),([7,31,1083361,8659208,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac14ab051ac12ab03a,0x1ac22ab075ac1ca8269,0x1ac26ab099ac24ab091,0x12f2e8bcb22f2aa1ca9,0x410ca04326b0bd]),([7,31,1083361,8659208,17318416,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1040581014ac04ab010,0x1ac1c6b062ac146b03a,0x1ac26ab092ac246b072,0x1042c810aa872a6b09d,0x410c2042e810b9]),([7,31,1083361,8659208,17318416,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136858da14ac04ab010,0x1ac1c6b06aac146b03a,0x1ac256b092a0a36b072,0x136aaa1ca9ac276b09a,0x136b04daba36ae4dab2,0x4dac2]),([7,31,1083391,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x128058a014ac04ab010,0x1ac1a68251ac0f6b03a,0x1ac246b081ac1cab071,0x1282a6b09aac266b092,0x128308a0c1282c8a0aa,0x115b2856c9]),([7,31,2096161,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12b058ac149c84a7210,0x19c9c672699c946723a,0x19ca4a729198a067272,0x12b2aa1ca99ca6a7299,0x190324acc22b304acb2])]
def b108 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,3247203,4330468,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x14d0593414a784a9e10,0x1a59c6726aa79569e52,0x1a7a2a9e89a7a0a7272,0x1a7a7a9e99a7a4a9e91,0x19cb0534b14d2aa1ca9,0x14d32934c9]),([7,31,2164802,3248099,4329604,8659208,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x17e059f814a084a8210,0x1a09aa8269a09568252,0x1a0a268282a09ca7271,0x1a0a668296a0a46828a,0x17e2c5f8aa872a6829a,0x5f8ca7e324fcc1]),([7,31,2164802,3248099,8659208,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x12f058bc14a084a8210,0x1a09a68255a094a824a,0x1a0a2a8289a09c6826a,0x1872a6829aa0a668292,0x12f308bcc12f2c4bcaa,0x11b3286cc9]),([7,31,2164802,4195296,8659208,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59a66852a592a9649,0x1a5a2a9689a59c6966a,0x1872a6969aa5a669692,0x16bb289cc2272c49caa]),([7,31,2164802,4329604,5412837,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x13f058fc14a784a9e10,0x1a794a9e51a792a9e3a,0x1a7a0a9e75a79ca726a,0x1a7a4a9e91a7a2a9e89,0x13f2aa1ca9a7a7a9e99,0x4fcca3f324fcbd]),([7,31,2164802,4329604,8659208,9742313,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x13f058fc14ac04ab010,0x1ac1a6b052ac146b03a,0x1a0a2ab072ac1c6b06a,0x1ac276b09aa7a4ab091,0x13f308fcb93f2aa1ca9,0x504ca]),([7,31,2164802,4329604,8659208,16236527,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x13f058fc149c84a7210,0x19c9a672529c946724a,0x19ca2a72729c9c6726a,0x19ca6a72959ca4a728d,0x13f2c4fcaa872a6729d,0x4fcce3f308fcbd]),([7,31,2164802,4329604,8659208,17317904,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12485892149c84a7210,0x19c9a672529c946724a,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x124ac492aa872a6729a,0x456ca24b0892bd])]
def b109 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4329604,8659208,32471070,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1248589214ac04ab010,0x1ac18ab052ac146b03a,0x1ac1cab071ac1aab069,0x1ac266b095a7a4a828a,0x124ae492aa872a6b09a,0x492ce24b0892c1]),([7,31,2164802,4329604,8659720,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12485892149c84a7210,0x19c9a672529c946724a,0x19ca2672729c9c6726a,0x1872a672929ca46728a,0x124b0892bd24ac492aa,0x5b6ca]),([7,31,2164802,4329604,8659944,17318416,32776456],hh [0x1a501a9404a500a9400,0x1a503a940ca502a9408,0x1270589c14a504a9410,0x11598a9452a5146944a,0x1a52269472a51c6646a,0x1a526a9492a5246948a,0x16232a94bd272c49caa]),([7,31,2164802,4330116,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12485892149c84a7210,0x19c9a672529c946724a,0x19ca2672729c9c6726a,0x19ca6a72999ca4a728a,0x124b0892b124aaa1ca9,0x5aeca]),([7,31,2164802,4330468,5412005,8659208,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x173859ce14a584a9610,0x1a59a66852a592a963a,0x1a5a269682a59ca966a,0x1a5a669696a5a46968a,0x173b25ceaa872a6969a,0x5ceca]),([7,31,2164802,4330468,5412005,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x13c058f014a584a9610,0x19a14a9651a592a963a,0x1a5a269682a59aa9669,0x1a5a6a9699a5a5a968a,0x13c324d8b53c2aa1ca9,0x4f0ca]),([7,31,2164802,4330468,5412837,8659208,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x173859ce14a584a9610,0x1a59aa9652a592a963a,0x1a5a269682a59d69672,0x1a5a669696a5a46968a,0x13f2f5ceaa872a6969e,0x173b29cec9]),([7,31,2164802,4330468,8659208,9741609,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x173859ce14a784a9e10,0x1a79aa9e699c94a9e3a,0x1a7a469e8aa7a269e71,0x1872a69e9da7a6a9692,0x115b29cec29cae5ceaa])]
def b110 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4330468,8659208,16236015,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x173859ce14a584a9610,0x1a59aa96699a14a964a,0x1a5a4a968da5a2a9671,0x173aaa1ca9a5a76969a,0x5cece73b09ceb1]),([7,31,2164802,4330468,8659208,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59aa96699a14a964a,0x1a5a4a968aa5a269671,0x1272aa1ca9a5a6a9699,0x5aeca273089cb1]),([7,31,2164802,4330468,8659208,17318416,32505887],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x19a14a964aa49242a39,0x1a5a269671a59aa9669,0x1a5a6a9699a5a4a968a,0x1293289cc2a5ab49caa]),([7,31,2164802,4330468,8659208,17318416,32776456],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59a45a629a14a964a,0x1a5a269472a59c6966a,0x1a5a6a9699a5a4a968a,0x1a5b149cc2272c49caa,0x5aeca]),([7,31,2164802,4330468,8659208,17318416,33047056],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x16b859ae14a584a9610,0x1a59aa96699a14a964a,0x1a5a2a968925a0a9671,0x16bac4a4aaa5a6a9699,0x1a5b35aeca6bb09aebd]),([7,31,2164802,4330468,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1ac1aab069ac14ab04a,0x1ac26a9692ac22ab071,0x1273089cb1272aa1ca9,0x500ca]),([7,31,2164802,4330468,8659208,19483218,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59a66852a592a963a,0x1a5a36968aa59c6966a,0x1872a6969aa5a669692,0x1273089caa]),([7,31,2164802,4330468,8659208,21648020,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1270589c14a784a9e10,0x1a79c69e6aa79a67252,0x19ca569692a7a2a9e89,0x1272aa1ca9a7a6a9e99,0x49cc29cae49cb1])]
def b111 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,4330468,8659208,21648372,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59c6966aa59a69652,0x1a5a6a9695a5a4a968a,0x1272e49cb1272aa1ca9,0x49cc2]),([7,31,2164802,4330468,8659208,25977624,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59a696629a14a964a,0x1a5a269676a59c6966a,0x1a5a76969aa5a4a968a,0x1273049cb1272aa1ca9,0x16bb289cc2]),([7,31,2164802,4330468,8659208,32472030,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1270589c14a784a9e10,0x1a79a69e629c94a9e3a,0x1a7a2a9e76a79c69e6a,0x1a7a6a9e95a5a4a9e8d,0x19cae49caa872a69e9d,0x49cce273089cc1]),([7,31,2164802,4330468,10824010,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x19a14a9651a592a963a,0x1a5a266871a59b6966a,0x1a5a6a9699a5a4a968a,0x16bb289cb5272aa1ca9]),([7,31,2164802,4330468,17318416,24895223,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x13c058f014a584a9610,0x1a59aa96699a14a964a,0x1a5a56968da5a2a9672,0x13c2aa1ca9a5a76969a,0x4f0ce3c308f0b1]),([7,31,2164802,4330468,17318416,25977624,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1158585614a584a9610,0x1a59a696629a14a964a,0x1a5a2a9689a59da966a,0x115aaa1ca9a5a76969a,0x169b2856c215b0456b1]),([7,31,2164802,4330495,8659208,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a59a66852a5936964a,0x1a5a269681a59c6966a,0x1272a6969aa5a66968a,0x16bb289cc2272c49caa]),([7,31,2164802,5241988,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12605898149c84a7210,0x19c9aa72699c94a724a,0x19ca2a728998a067271,0x1262aa1ca99ca6a7299,0x12630898b1])]
def b112 : List (List Nat × List (Nat × Nat)) := [([7,31,2164802,6495206,8659208,17318416,32505856],hh [0x19a01a68049a00a6800,0x19a03a680c9a02a6808,0x1270589c149a04a6810,0x19a1a668559a14a684a,0x19a22a68899a1c6686a,0x1872a6689a9a2666892,0x16bb289cc2272f89caa]),([7,31,2164802,8659208,9742313,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1a09aab062ac14ab051,0x1ac22ab089ac1d6b072,0x1872a6b09aac24ab091,0x115b24bcc22f2e8bcaa,0x456ca]),([7,31,2164802,8659208,12989420,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x19a1aa9662a594a9651,0x1a5a2a9689a59d69672,0x1872a6969aa5a4a9691,0x1272e89cb9272c49caa,0x5aeca]),([7,31,2164802,8659208,17318416,29223963,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x19205a4814a584a9610,0x1a59aa9669a594a9651,0x19a22a9682a59ca9671,0x1922aa1ca9a5a769692,0x648c2922ea48b1]),([7,31,2164802,8659208,17318416,32471070,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac1aab069ac14ab051,0x1a0a2ab082ac1cab071,0x12f2aa1ca9ac276b092,0x11b3086cc12f2e8bcb9,0x4bcce]),([7,31,2165314,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12485892149c84a7210,0x19c9a672529c946724a,0x19ca4672729c9c6726a,0x1872a6729a9ca667292,0x124b0892bd8bac492aa,0x456ca]),([7,31,2165730,4329604,5412005,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x137058dc14a084a8210,0x1a094a7251a092a823a,0x1a0a0a8275a09ca7269,0x1a0a668292a0a46828e,0x1372f4dcaa872a6829a,0x137328dcc9]),([7,31,2165730,4329604,8659208,17318416,32539681],hh [0x139018e40439008e400,0x139038e40c39028e408,0x155059541439048e410,0x137188e25139128d83a,0x1391c8e471391a8e469,0x139248e49136234de82,0x1362c49eaa39268e499,0x49cca3731554c2])]
def b113 : List (List Nat × List (Nat × Nat)) := [([7,31,2165730,4329604,10824010,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1270589c14a084a8210,0x1a094a7251a092a823a,0x1a0a46828aa09ca8271,0x1872a6829aa0a668292,0x454ca272f49caa]),([7,31,2165730,4329604,17318416,18400817,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x137058dc14a084a8210,0x1a09c6826a9c946823a,0x1a0a6a8292a0a468272,0x1372e4dcaa872a6829d,0x127328dcc2]),([7,31,2165730,4329604,17318416,32472030,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1150585414a084a8210,0x1a09ba82629c946823a,0x1a0a4a828da09ca8271,0x1872a6829da0a6a8295,0x11530854c1152e454aa,0x454ce]),([7,31,4329604,4330468,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136154d85236128d83a,0x1361c4d86a361a4d862,0x136228d88936208d872,0x138ae4d89a36264d895,0x49cca3631554c2]),([7,31,4329604,5412005,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac18ab055ac14ab03a,0x1ac20a9e72a79aab069,0x1ac24ab091ac22ab089,0x1592e572b55caaa1ca9,0x16e32972c2]),([7,31,4329604,8659208,8659944,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x136188d85236144d84a,0x136208d875361c8d86a,0x136248d89136228d889,0x138b04d8bd552e8d89d,0x49cca]),([7,31,4329604,8659208,17318416,32506848,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x1528594a1436048d810,0x136188d85236144d84a,0x1361c8d871361a8d869,0x136248d88a36208d881,0x152ae8d89e36274d895,0x138b24d8bd]),([7,31,4329604,8659208,17318416,32539681,32540641],hh [0x138818e20438808e200,0x138838e20c38828e208,0x138858e214528494a10,0x138988e25238944e24a,0x1389c8e271389a8e269,0x1362a8e29552a499c82,0x138b14e2bd38ae8e2b2,0x54acd38b28d8c6])]
def b114 : List (List Nat × List (Nat × Nat)) := [([7,31,4329604,8659208,17318416,32539681,33553439],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136058d814550495410,0x136188d85236144d84a,0x1361c8d871361a8d869,0x1362a89c9a362555492,0x1362f4d8ba362c8d8ad,0x13e328d8c6]),([7,31,4329604,8659944,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1a794ab051ac12ab03a,0x1ac22ab089ac1aab069,0x1872a6b09aac266b092,0x1273049cba272d49caa,0x408ca]),([7,31,4329604,8659944,17318416,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x136058d814ac04ab010,0x1ac1aab069a794ab04a,0x1ac26ab08aac226b072,0x1362e8d8aa872a6b09d,0x49cca27324d8c2]),([7,31,4329604,8659944,17318416,32472030,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1020580814ac04ab010,0x1ac1a6b062a794ab04a,0x1ac256b08dac22ab06a,0x1022aa1ca9ac276b09a,0x10233a3ac90230808ba]),([7,31,4329604,8659944,17318416,32505856,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x159059641436048d810,0x1361a4d86236148d84a,0x136228d88236204d86a,0x12730964b236268d896,0x13633564ca]),([7,31,4330468,5412005,8659208,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x15c8597214a584a9610,0x1a59aa9669a598a963a,0x1a5a469682a59ca9671,0x1872a6969aa5a669692,0x1a5b1572c2592e572aa,0x4d8ca]),([7,31,4330468,8659208,10824010,17318416,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1270589c14a584a9610,0x1a594a9651a592a963a,0x1a5a2a9675a59ca6869,0x1a5a6a9699a5a4a9691,0x1a5af49cba272aa1ca9,0x16bb289cc1]),([7,31,4330468,8659208,17318416,19483218,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x1020580814a584a9610,0x1a59c69662a5946963a,0x1a5a6a9692a5a469672,0x1022e808aa872a6969d,0x15932408c2])]
def b115 : List (List Nat × List (Nat × Nat)) := [([7,31,4330468,8659208,17318416,31389629,32505856],hh [0x1a581a9604a580a9600,0x1a583a960ca582a9608,0x136058d814a584a9610,0x1a59c6966aa5946963a,0x1a5a5696929a2369672,0x1362aa1ca9a5a76969a,0x49cc936308d8ba]),([7,31,4330468,8659208,17318416,32505856,32573506],hh [0x1020180804020080800,0x102038080c020280808,0x1270589c14020480810,0x1021c4086a02144083a,0x1022280882022040872,0x1593089cba022680892,0x1023349cca]),([7,287,992,1082401,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17b059ec14ac04ab010,0x1a09a6b062ac14ab051,0x1ac22a9e89ac1cab071,0x1ac26ab099ac24ab091,0x17b2ca72b17b2aa1ca9,0x1b7b25ecba]),([7,512,543,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c926723d9c8ea7239,0x19c98a72619c936724a,0x19c9ca72719c9aa7265,0x19ca4672859ca0a7281,0x149aa6729a9ca667292,0x149aca1cb19cab526aa,0x4f0c94531526ba]),([7,512,1082401,2164802,4329604,32505856,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x18705a1c14058481610,0x1059281649058e81639,0x1059881661059481651,0x1059c81671059a81669,0x105a54169205a081681,0x1872aa1ca905a681699,0x416cd873287ebd]),([7,512,1082401,2164802,4329604,32505856,33554400],hh [0x132018c80432008c800,0x132038c80c32028c808,0x19c85a721432048c810,0x132128c849320e8c839,0x132188c86132148c851,0x1321c8c871321a8c869,0x132254c88a32208c881,0x132af4c8ad9caa8c899,0x13233672ca]),([7,543,992,1082401,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x19c956b0519c8fab03a,0x1a79b6b06aa09a6b062,0x1a0a369e89ac1cab071,0x1ac26ab099ac24ab091,0x149aca72b149aaa1ca9,0x13c32514c549aea72b5]),([7,543,31744,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946723e9c8ea7239,0x19c9aa72699c98a7255,0x19ca2672729c9c6726d,0x19ca6672929ca46728d,0x1ac2c526aa872a6729a,0x14531526ba9cad526b2,0x4f0c9])]
def b116 : List (List Nat × List (Nat × Nat)) := [([7,543,1082401,2164802,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14d05934149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca3a728a9ca267286,0x19ca6672969ca4a7291,0x14d2aa1ca99ca7a729a,0x14d324fcc1452f534b2,0x19cb3534ca]),([7,543,1082401,2164802,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c9a672529c946724a,0x19ca0a72729c9c6726a,0x19ca3a728a9ca267286,0x19ca6672969ca4a7291,0x149aaa1ca99ca7a729a,0x149b24f0c1452f526b2,0x19cb3526ca]),([7,543,1082401,2164802,4329604,32505856],hh [0x19c81e72059c80e7201,0x19c83e720d9c82e7209,0x19c8fe723b4984d2611,0x19c95e72539c93e724b,0x19c9be726b9c99e7263,0x19ca1d26839c9de7273,0x149a5d26939ca3d268b,0x149a7cf09b]),([7,543,1082401,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12c058b0149c84a7210,0x19c9a672529c946723a,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x12c2c8b0aa872a6729a,0x11c324b0c22c30668b5,0x470ca]),([7,543,1082401,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14505914149c84a7210,0x19c9a672629c94a7251,0x19ca0a72729c9c6726a,0x19ca4a72919ca2a7289,0x1452aa1ca99ca6a7299,0x19cb1514c2452c914b1,0x19cb3514ca]),([7,543,2164802,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12485892149c84a7210,0x19c9a672529c946724a,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x124ac492aa872a6729a,0x456ca24b0892bd]),([7,992,1023,1082401,2164802,4329604,32776456],hh [0x1a801aa004a800aa000,0x1a803aa00ca802aa008,0x17e059f814a804aa010,0x1a81c6944aa80f6a03a,0x1a824aa091a720aa072,0x11c325f8baa826aa099]),([7,992,1023,1082401,2164802,4329604,33047056],hh [0x1610198404610098400,0x161039840c610298408,0x1498592614610498410,0x1561a95862610f5843a,0x1612498491611c98471,0x149ae926a9612698499,0x12f32558c5])]
def b117 : List (List Nat × List (Nat × Nat)) := [([7,992,1023,1082401,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x11c05870142f048bc10,0x128148bc4a2f0f4bc3a,0x12f248bc912f1c8bc71,0x11c2a870a92f268bc99,0x10532814c9272f470ba]),([7,992,1023,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x12f058bc141c0487010,0x1159486c4a1c0f4703a,0x11c20870811c1c87071,0x11c26870991c2487091,0x10532814c915af4bcba]),([7,992,1023,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x155059541436048d810,0x1361a8d862360f4d83a,0x136244d881361c8d871,0x155308d89a36264d892,0x127328d8c5]),([7,992,31744,1015808,1082431,2164802,4329604,8659208,33047056],hh [0x400e0]),([7,992,31744,1015808,1082431,2164802,4329604,17318416,32776456],hh [0x400e0]),([7,992,31744,1082401,2164802,4329631,8659208,17809936,32505856],[]),([7,992,31744,1082401,2164802,4329631,9412872,17318416,32505856],hh [0x400e0]),([7,992,31744,1082401,3115074,4329631,8659208,17318416,32505856],hh [0x10038000b0])]
def b118 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1082431,2164802,4329604,8659208,17809936,32505856],[]),([7,992,31744,1082431,2164802,4329604,9412872,17318416,32505856],hh [0x400e0]),([7,992,31744,1082431,3115074,4329604,8659208,17318416,32505856],hh [0x10038000b0]),([7,992,1047552,1082401,2164802,4329631,8659208,17318416,32505856],[]),([7,992,1047552,1082401,2164802,8659208,32641156],hh [0x17d819f6047d809f600,0x17d839f60c7d829f608,0x19505a54147d849f610,0x1799a9f64a7d8e9f639,0x17ba29ec867d9c9f671,0x17da69f6997da49f691,0x526c90530a50aa]),([7,992,1047552,1082401,2164802,17318416,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x1499a91662498e92639,0x149a192681499c92671,0x149a65269249a45268a,0x17e32514c505309269a]),([7,992,1047552,1082401,2164831,4329604,8659208],hh [0x17c819f2047c809f200,0x17c839f20c7c829f208,0x17c859f214130484c10,0x17c929f2497c8e9f239,0x1132444a82791a9f251,0x17aab880a9452644c92,0x17cae856b97aac9f2b1,0x526ca1c325f2c2]),([7,992,1047552,1082401,2164831,4329604,17318416],hh [0x1490192404490092400,0x149039240c490292408,0x1490592414110484410,0x1491452449490e92439,0x1112484491491a91462,0x1492c924b1492b91499,0x12f32524c2492e89cb9,0x5f8ca])]
def b119 : List (List Nat × List (Nat × Nat)) := [([7,992,1047552,1082431,2164802,4329604,8659208,17318416,32505856],[]),([7,992,1047552,2164802,4329631,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1271a89c62270e89c39,0x1272449c89272049c72,0x15cae456b115aa89c92,0x488ca2232456ba]),([7,992,1047552,4329604,8659208,17318416,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x1238588e14010480410,0x101148044a010e80439,0x1012080481011c80471,0x1012680499012480491,0x1012f48eba]),([7,992,1048607,2164802,8659208,17318416,32505856],hh [0x18901a24048900a2400,0x18903a240c8902a2408,0x1270589c148904a2410,0x1891862449890ea2439,0x188a162482891ca2471,0x18926a24998924a2491,0x1273089cc1272aa68a9,0x115b2856c9]),([7,992,1082401,2097183,4329604,17318416,32505856],hh [0x1450191404450091400,0x10d038340c450291408,0x1450591414450491410,0x10b185144a451251439,0x14521914850d1a83469,0x12f2651492452289c89,0x1452c914aa452a5f89a,0x14532514c695b0514ba,0x514ca]),([7,992,1082401,2164802,4329604,32776456,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x1a805aa0146f849be10,0x16f945bc496f8e8cc39,0x16f9a5be6243985be52,0x16fa05be726f9c5be6a,0x16fab6a0aa6fa65be8a,0x16fb35c2bd]),([7,992,1082401,2164802,4329604,33047056,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16105984146f849be10,0x16f945be4a6f124cc39,0x16f9a9be6943985be52,0x16fa28c8856f9c9be71,0x16fab584aa6fa65be95,0x16fb35c0bd]),([7,992,1082401,2164802,8659208,32505887,32641156],hh [0x17d819f6047d809f600,0x17d839f60c7d829f608,0x10d05834147d849f610,0x17d945f6497d8e9f639,0x17d9a5ec667d985f652,0x17da05f6727d9c5f66a,0x10d2a82ca97d265f682,0x149b0434ba])]
def b120 : List (List Nat × List (Nat × Nat)) := [([7,992,1082401,2164802,8659208,33047056,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x12f058bc146f849be10,0x16f945bc496f8e8cc39,0x16f9a9be696f985be52,0x132215be826f9c9be71,0x16fa69be996fa35be8a,0x5d8b56fab4bcaa]),([7,992,1082401,2164802,17318416,32505887,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x10d0583414498492610,0x149945164a499252639,0x1499a52666499952652,0x149a052672499c5266a,0x10b2a5269945a552682,0x5f8c1452f434ba]),([7,992,1082401,2164802,17318416,32776456,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x11c05870146f849be10,0x16f945bc496f8e8cc39,0x16f9a4c8656f989be52,0x16fa05be726f9c5be6a,0x16fa69be996fa35be8a,0x5d8b56fab470aa]),([7,992,1082401,2164831,4329604,8659208,32505887],hh [0x10f0183c040f0083c00,0x10f0383c0c0f0283c08,0x17c859f2140f0483c10,0x10c18422490f0e83c39,0x10e9c43c6a0f1a43c62,0x10f2283c890f2183c81,0x1072a43c9a0f2643c92,0x17cb29f2c97cac9f2aa]),([7,992,1082401,2164831,4329604,8659231,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x10c8583214ac04ab010,0x1ac14a8249ac0eab039,0x1ac1aab069ac18a9e61,0x1ac26ab08aac206b071,0x10cb0432b20caaa72a9,0x17cb29f2c9]),([7,992,1082401,2164831,4329604,17318416,32505887],hh [0x10f0183c040f0083c00,0x10f0383c0c0f0283c08,0x14905924140f0483c10,0x10c1843c4a089243c39,0x1072143a710f1a83c69,0x10f2483c8a0f2243c86,0x1492a81ca90f2683c99,0x14932924c9452f524b2]),([7,992,1082401,2164831,4329604,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1490592414ac04ab010,0x1ac14ab04aa0926b039,0x1ac1c6b06aac1a69e61,0x19caa6b09aac22a7285,0x149324ecc1492c924aa,0x524ca]),([7,992,1082401,4329604,8388639,17318416,32505856],hh [0x1a301a8c04a300a8c00,0x1a303a8c0ca302a8c08,0x15c8597214a304a8c10,0x1a314a8c51a31268c39,0x1a32265885a318a8c61,0x1a326a8c92a32468c8a,0x15cac964b15caaa72a9,0x4c6ca])]
def b121 : List (List Nat × List (Nat × Nat)) := [([7,992,1082401,4329604,8659231,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1108584214ac04ab010,0x1ac14ab051a7926b039,0x1ac1cab06aac18ab061,0x19caa6b092ac22a7285,0x110b0842b2102c442aa,0x446ca]),([7,992,2164802,4194335,8659208,17318416,32505856],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14158485610,0x1271849c4a271249c39,0x124a145682271a89c69,0x10d268349915a297289,0x1272da34b1272aa7aa9,0x4c4ca273089cba]),([7,992,2164802,4329631,8659208,17318416,32505887],hh [0x1a981aa604a980aa600,0x1a983aa60ca982aa608,0x1270589c14a984aa610,0x10e14aa64aa61267e39,0x1a9a0aa66aa99a6a661,0x1a9a66a68aa9a266a85,0x1272f49caa9aaa6a69a,0x1293289cc2]),([7,992,4329604,8659208,17318416,32505887,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x10d0583414010480410,0x1011440449010e80439,0x1011a40465011880452,0x1012040472011c4046a,0x10d2c820a9012340482,0x404b5]),([7,992,4329604,8659208,17318416,32539681,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x136058d8146f849be10,0x16f945be4a6f9250e39,0x16f9a9be6932195be52,0x16fa48cc816f9c9be71,0x16fab4d8aa6fa69be95,0x16fb15bebd]),([7,1023,1082401,2164802,4329604,8659208,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x17e059f814058481610,0x1059841652059441649,0x1059c81671059a81669,0x105a44168a05a241686,0x17d324169a05a641692]),([7,1023,1082401,2164802,4329604,8659208,32506848],hh [0x132018c80432008c800,0x132038c80c32028c808,0x17e059f81432048c810,0x1321a8c86932148c851,0x132224c886321c8c871,0x132264c89232244c88a,0x13233512c1342f4c89a]),([7,1023,1082401,2164802,4329604,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x1498592614058481610,0x1059481651059281649,0x1059c4166a059a41661,0x105a28168905a181672,0x105a68169905a481691,0x526ca49b247ebd])]
def b122 : List (List Nat × List (Nat × Nat)) := [([7,1023,1082401,2164802,4329604,17318416,32506848],hh [0x132018c80432008c800,0x132038c80c32028c808,0x149859261432048c810,0x1321a4c85232144c84a,0x132218c872321c4c86a,0x132248c89132228c889,0x149b28cabd32268c899,0x4c8cd]),([7,1023,1082401,2164802,4329604,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1058581614ac04ab010,0x1ac146b04aa0926b039,0x1ac1aab069a7986b052,0x1ac21a7285ac1cab071,0x105ac816aa97aa6b091,0x149b2926c905b0416bd]),([7,1023,1082401,2164802,8659208,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x12f058bc14058481610,0x105948165105924163a,0x1059c81671059a81669,0x105a48169105a281689,0x11c32818b505a681699]),([7,1023,1082401,2164802,8659208,17318416,32506848],hh [0x132018c80432008c800,0x132038c80c32028c808,0x12f058bc1432048c810,0x1321a4c85232144c83a,0x132224c872321c4c86a,0x132264c89232244c88a,0x11c32870c9422d4c89a]),([7,1023,1082401,2164802,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12a058a814ac04ab010,0x1ac1a6b052ac146b03a,0x1ac226b072ac1c6b06a,0x1a92d4a8b22a2aa1ca9,0x11a32868c92a308a8c1]),([7,1023,1082401,4329604,8659208,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x15c8597214058481610,0x1059881652059441649,0x1059c81671059a81669,0x105a48169105a281689,0x14532816c505a681699]),([7,1023,1082401,4329604,8659208,17318416,32506848],hh [0x132018c80432008c800,0x132038c80c32028c808,0x15c859721432048c810,0x1321a4c86232148c851,0x132224c872321c4c86a,0x132264c89232244c88a,0x132334c2ca32314c89a]),([7,1023,1082401,4329604,8659208,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1058581614ac04ab010,0x1ac14ab051a7926b039,0x1ac1aab069ac18ab061,0x1ac2667285ac1cab071,0x105ac816b105aaa5aa9,0x514caac31416c2])]
def b123 : List (List Nat × List (Nat × Nat)) := [([7,1023,2164802,4329604,8659208,17318416,32505887],hh [0x1058181604058081600,0x105838160c058281608,0x1270589c14058481610,0x105944164a059241639,0x1059c4166a059a41652,0x105a44168a05a241672,0x105af4169a05a641692,0x4a4ca]),([7,1023,2164802,4329604,8659208,17318416,32506848],hh [0x132018c80432008c800,0x132038c80c32028c808,0x1270589c1432048c810,0x1321a4c85232144c84a,0x132224c872321c4c86a,0x132264c89232244c88a,0x456ca322f4c89a]),([7,1023,2164802,4329604,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1230588c14ac04ab010,0x1ac1a6b052ac146b04a,0x1ac246b072ac1c6b06a,0x1232f48cb1232aa1ca9,0x114b288cc2]),([7,31744,1015808,1082401,2164802,4329631,8659944,17318416,32505856],hh [0x40060]),([7,31744,1015808,1082401,2165730,4329631,8659208,17318416,32505856],hh [0x400a8]),([7,31744,1015808,1082431,2164802,4329604,8659944,17318416,32505856],hh [0x40060]),([7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856],hh [0x400a8]),([7,31744,1015808,1083361,2164831,4329604,8659208],hh [0x17c819f2047c809f200,0x17c839f20c7c829f208,0x17c859f214120484810,0x17c945f2497c8e9f239,0x141a6448927c9a9e462,0x17cac886b17aaa884a9,0x11c325f2c27aaf856b9,0x526ca])]
def b124 : List (List Nat × List (Nat × Nat)) := [([7,31744,1015808,4329604,8659208,17318431,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x105858161436048d810,0x136144d849360e8d839,0x1361a8d86936188d861,0x136214d882361c8d871,0x13eaa4d89936234d88a,0x4d8c505b08feb1]),([7,31744,1015808,4329604,8659208,17318896,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x1230588c14010480410,0x101148044a010e80439,0x1232e80491011c80471,0x404bd]),([7,1047552,1082401,2164802,4329604,17318431,32505856],hh [0x19781a5e049780a5e00,0x19783a5e0c9782a5e08,0x10585816149784a5e10,0x1979465e4a979265e39,0x1979aa5e69979865e52,0x197a165e82979ca5e71,0x105ac816aaac2a65a91,0x61cc905b0416bd]),([7,1047552,1082401,2164802,8659208,17318896,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x12a058a8148704a1c10,0x1871a61c52871461c3a,0x1872261c72871c61c6a,0x12a2e88cb52a2aab0a9,0x198324a8c1]),([7,1047552,1082401,4329604,8659208,17318431,32505856],hh [0x19681a5a049680a5a00,0x19683a5a0c9682a5a08,0x10585816149684a5a10,0x19694a5a51969265a39,0x1969aa5a699698a5a61,0x196a165a82969ca5a71,0x105ac416aaac2a65a99,0x65ac505b0816b2]),([7,1047552,2164802,4329604,8659208,17318896,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x1230588c148704a1c10,0x1871a61c52871461c4a,0x1872461c72871c61c6a,0x1232c88cb1232aab0a9,0x1872f48cba]),([7,1082401,2164802,4329604,8659208,32505887,32506848],hh [0x168819a20468809a200,0x168839a20c68829a208,0x10c058301468849a210,0x168929a249688e9a239,0x168989a26168949a251,0x1689c9a271689a9a269,0x10c2e596b5072c9a299,0x166b142cba]),([7,1082401,2164802,4329604,17318416,32505887,32506848],hh [0x168819a20468809a200,0x168839a20c68829a208,0x10c058301468849a210,0x168929a249688e9a239,0x168989a26168949a251,0x1689c9a271689a9a269,0x167ad41cb268a65a28d,0x1873142cba])]
def b125 : List (List Nat × List (Nat × Nat)) := [([7,1082401,2164802,4330468,8659208,32505856,32505887],hh [0x10b0182c040b0082c00,0x10b0382c0c0b0282c08,0x18705a1c140b0482c10,0x10912826490b0e82c39,0x10b1a42c620b1841a52,0x10b2282c760b1c42c6a,0x1873042c990b2482c91,0x10b3361cca]),([7,1082401,2164802,4330468,8659208,32505856,33554400],hh [0x1438190e04438090e00,0x1438390e0c438290e08,0x1a785a9e14438490e10,0x133128d649438e90e39,0x1439a50e62439850c52,0x143a090e76439c50e6a,0x1442d50e9a43a650e91,0x50ecda7b290ec5]),([7,1082401,2164802,8659208,17318416,32505887,32506848],hh [0x168819a20468809a200,0x168839a20c68829a208,0x10c058301468849a210,0x168929a249688e9a239,0x168989a26168949a251,0x1689c9a271689a9a269,0x14db041cb268ab5a285]),([7,1082401,2165730,4329604,17318416,32505856,32505887],hh [0x1080182004080082000,0x108038200c080282008,0x18705a1c14080482010,0x106944204a08124163a,0x1081c4206e081882061,0x1082482091082282072,0x1083361cca873042099]),([7,1082401,2165730,4329604,17318416,32505856,33554400],hh [0x16f019bc046f009bc00,0x16f039bc0c6f029bc08,0x1a085a82146f049bc10,0x143145bc4a6f124c83a,0x16f1c5bc6e6f189bc61,0x16f265bc916f209bc72,0x1a0b29bcc5702d5bc9a,0x5bccd]),([7,1082401,4329604,8659208,17318416,32505887,32506848],hh [0x168819a20468809a200,0x168839a20c68829a208,0x10c058301468849a210,0x168929a249688e9a239,0x168989a26168949a251,0x1689c9a271689a9a269,0x187315a4bd0b2c9a295]),([7,1082401,4329604,8659944,17318416,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x18705a1c140d0483410,0x10b148244a0d0e83439,0x10d1a834690d1883461,0x10d3361cca0d2283481]),([7,1082401,4329604,8659944,17318416,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x1ac05ab0146f849be10,0x143948cc4a6f8e9be39,0x16f9a9be696f989be61,0x16fa69be926fa09be81,0x16fb36b0ca6fb15bebd])]
def b126 : List (List Nat × List (Nat × Nat)) := [([7,1083361,2164802,4329604,8659208,32505856,32505887],hh [0x1090182404090082400,0x109038240c090282408,0x18705a1c14090482410,0x109144244a091241639,0x1091a42466091842452,0x1092282472091c4246a,0x1873042499092482491,0x1093361cca]),([7,1083361,2164802,4329604,8659208,32505856,33554400],hh [0x133018cc0433008cc00,0x133038cc0c33028cc08,0x1ac05ab01433048cc10,0x133144cc4a33124c839,0x1331a4cc6633184cc52,0x133208cc72331c4cc6a,0x133ad4cc9a33264cc91,0x4cccdac328ccc5]),([7,1083361,2164802,8659208,17318416,32505856,32505887],hh [0x1090182404090082400,0x109038240c090282408,0x18705a1c14090482410,0x1091482451091241639,0x1091c4246a091a42462,0x1092642491092282472,0x1093361cca]),([7,1083361,2164802,8659208,17318416,32505856,33554400],hh [0x133018cc0433008cc00,0x133038cc0c33028cc08,0x1ac05ab01433048cc10,0x133148cc5133124c839,0x1331c4cc6a331a4cc62,0x133248cc9133208cc72,0x1ac329d8ad33268cc99,0x4cccd]),([7,2164802,4329604,8659208,17318416,32505887,32506848],hh [0x168819a20468809a200,0x168839a20c68829a208,0x10c058301468849a210,0x168929a249688e9a239,0x168989a26168949a251,0x1689c9a271689a9a269,0x168ad42cb2072a9a28d]),([7,2164802,4330468,8659208,17318416,32505856,32505887],hh [0x1098182604098082600,0x109838260c098282608,0x18705a1c14098482610,0x109944264a09924183a,0x1099c4266a099882661,0x109a28268209a042672,0x109b361cca]),([7,2164802,4330468,8659208,17318416,32505856,33554400],hh [0x135818d60435808d600,0x135838d60c35828d608,0x1a585a961435848d610,0x135944d64a35924d43a,0x1359c4d66a35988d661,0x135a68d69235a04d672,0x4d6cda5b29beb5]),([8,31,256,992,1082401,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397b069ec18,0x1ac156b052ac12ab049,0x1ac1cab071ac1aab069,0x1a0a46b08aac226b082,0x1ac2cab0b1ac26ab099,0x1ac30ab0c1ac2ea9eb9,0x17b36a1cd9ac32ab0c9,0x17b3aa72e97b389ece1,0x1b7c05ecf2])]
def b127 : List (List Nat × List (Nat × Nat)) := [([8,31,512,992,1082401,2164802,4329604,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac14a724eac12ab049,0x1ac1aab0699c95ab055,0x1ac226b0829c9d6b071,0x1a7a56b092a0a46b08a,0x1ac2cab0b1ac26ab099,0x1ac30ab0c1a0af69eb9,0x149b6a1cd9ac32ab0c9,0x149baa72e949b8926e1,0x13c40514fd49bca72ed]),([8,31,512,31744,1082401,2164802,4329604,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239498692618,0x19c946724e9c92a7249,0x19c9aa72699c95a7252,0x19ca2672829c9d67271,0x19ca5672929ca46728a,0x19caca72b19ca6a7299,0x19cb0a72c19caf672b9,0x149b6a1cd99cb2a72c9,0x149baab0e949b8926e1,0x13c40514fd49bca72ed]),([8,31,512,1082401,2164802,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72394d0693418,0x19c9a672629c94a7251,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x19cac672ae9caaa729a,0x19caea72b99cada72b2,0x19cb1a72c29cb0672be,0x18736672ce9cb2a72c9,0x14d3a934e24d38534da,0x14d40935013f3e514f5,0x67305]),([8,31,512,1082401,2164802,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239498692618,0x19c9a672629c94a7251,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x19caca72ae9caaa729a,0x19caea72b99cada72b5,0x19cb1a72c29cb0672be,0x18736672ce9cb2a72c9,0x149ba926e249b8526da,0x149c0927013c3e514f5,0x67305]),([8,31,512,1082401,2164802,4329604,32505856],hh [0x19c81e72059c80e7201,0x19c83e720d9c82e7209,0x14985d26159c84e7211,0x19c93e724b9c8fe723b,0x19c99e72639c95e7253,0x19c9de72739c9be726b,0x19ca3e728b9ca1e7283,0x19ca7e729b9ca5e7293,0x19cadd26b39cabd26ab,0x149b1d26c39cafd26bb,0x149b3cf0cb]),([8,31,512,1082401,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72392c068b018,0x19c9a672529c946724a,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x19cae672b59caca729a,0x19cb2672c29cb0672ba,0x12c384b0da8736672ca,0x12c3e668ed2c3a8b0e2,0x471021c404b0fa]),([8,31,512,1082401,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239450691418,0x19c9aa72699c94a7251,0x19ca2672829c9ca7271,0x19ca6672929ca46728a,0x19cad672b29caaa729a,0x19cb0a72c19caea72b9,0x14536a1cd99cb2a72c9,0x1453a914e94538914e1,0x19cc1515029cbf514fa]),([8,31,512,2164802,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239248689218,0x19c9a672629c94a7251,0x19ca2672729c9c6726a,0x19ca6672929ca46728a,0x19cae672b59caca729a,0x19cb2672c29cb0672ba,0x124b8492da8736672ca,0x124be892f524ba492e2,0x45702])]
def b128 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],hh [0x40120]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],hh [0x40120]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156],hh [0x400b8]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,9412872],hh [0x18401a10048400a1000,0x18403a100c8402a1008,0x18405a10148404a1010,0x1840ea10397e069f818,0x18414a10518412a1049,0x182a061071831aa1069,0x18426a10998424a1082,0x18430a10c183aca08a9,0x17e385f4da8432a10c9,0x17e3e5f8f27c3a9f8e9]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],hh [0x40120]),([8,31,992,31744,1082401,2164802,4329604,17809936],hh [0x1648199204648099200,0x164839920c648299208,0x1648599214648499210,0x1648e99239498692618,0x1649499251649299249,0x164a097681649c59269,0x164a69929964a496c8a,0x164b2592c264b0592a9,0x149ba926e949b6992ca,0x15b3e526f2]),([8,31,992,31744,1082401,2164802,4329604,32776456],hh [0x1b301acc04b300acc00,0x1b303acc0cb302acc08,0x1b305acc14b304acc10,0x1b30eacc397e069f818,0x1b3146a04eb312acc49,0x1b11aacc69a815acc52,0x19d226cc82a81d6cc71,0x1b3266cc95b324aa091,0x1b32e6c8b2b2ac6cc9a,0x1b3326ccc2b3306a0bd,0x1ac3a672e17d36accca,0x11c405f8f2a83b5f0ea])]
def b129 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1082401,2164802,4329604,33047056],hh [0x1618198604618098600,0x161839860c618298608,0x1618598614618498610,0x1618e98639498692618,0x161945844e619298649,0x1619c58669611598652,0x157229868961a098475,0x161a65849561a498691,0x161af584b95fac5869a,0x161b2986c961b0986c1,0x149baab0e99cb9526da,0x12f4055cfd49bc984ed]),([8,31,992,31744,1082401,2164802,8659208,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391c0687018,0x12f144bc4e2f128bc49,0x12f1a4a0622f158bc52,0x12f1d4b4722f1c4bc6a,0x12f264bc952f244bc89,0x12f2f4bcb92f2c4bc9a,0x12f328bcc92f308bcc1,0x12fbb6aee92cb9470e2,0x1054081501273d470f2]),([8,31,992,31744,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c05870141c0487010,0x11c0e870392f068bc18,0x11c144704e1c1287049,0x11c1a45c621c1587052,0x11c1d470721c1c46c6a,0x11c26470951c2447089,0x11c2e470b51c2c8709a,0x11c32470c21c30470bd,0x11c3b6ace99bb8470ca,0x105408150115bd4bcf2]),([8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],hh [0x10048000e8]),([8,31,992,31744,1082401,4329604,8659208,17809936],hh [0x15b0196c045b0096c00,0x15b0396c0c5b0296c08,0x15b0596c145b0496c10,0x15b0e96c39450691418,0x15b1496c515b1296c49,0x15b2656c815b1c56c69,0x15b2c96cb15b2a96c9a,0x15b3096cc15b2e96cb9,0x1453a514da5b3296cc9,0x1454091501453c914ea]),([8,31,992,31744,1082401,4329604,9412872,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x15c85972145c8497210,0x15c8e972398506a1418,0x15c94972515c9297249,0x15ca6572815c9c57269,0x15cac972b15caa9729a,0x18536972c25cae972b9,0x1273c614ea853a400e8,0x14540614fa2f3e614f2,0x51502]),([8,31,992,31744,2065441,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391c0687018,0x12f148bc512f128bc49,0x12d9c4bc6a2b9a4a062,0x12f2e4bcb12f204b472,0x11c388bcca2f324bcc1,0x11c3e972f9273c470e9,0x1054081501]),([8,31,992,31744,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136058d81436048d810,0x1360e8d839568695a18,0x136144d84e36128d849,0x1361c4d86936158d852,0x136228d88936208d875,0x136264d89536248d891,0x1362e4d8b5362a8d89a,0x136308d8c1362f4d8ba,0x172ba4e2e136328d8c9,0x127408d8fd56be8d8ed])]
def b130 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1047552,1082401,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x1bc85af2147e049f810,0x17e0e9f8397e069f818,0x17e149f8517e129f849,0x17e205f8717e1a9f869,0x17e269f8997a249f282,0x1bcb0af2c1bc2caf2a9,0x17e385f4da0532914c9,0x115bc5f0ea7e3a5ece6,0x11c405f8fa7e3e5f8f2,0x52702]),([8,31,992,1047552,1082401,2164802,4329604,8659208,17318416,32505856],[]),([8,31,992,1047552,1082401,2164802,4329604,17318416],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x1498e92639498692618,0x1499492651499292649,0x1492092681499c52669,0x149a69269949a49168a,0x14532606c281b04f0a9,0x149ba526e649b6814ca,0x15cbe526f2273c526ea,0x5f9022f40526fa]),([8,31,992,1047552,1082401,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391c0687018,0x12f148bc512f128bc49,0x12f1c4bc6a2f1a4a062,0x12f268bc992f204b472,0x12f308bcc12f2e4bcb1,0x11c3a470e22f328bcc9,0x11c3e972f91c3c89cf1,0x1054081501]),([8,31,992,1047552,1082401,4329604,8659208,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x15c85972145c8497210,0x15c8e97239450691418,0x15c94972515c9297249,0x15ca6572815c9c57269,0x15cac972b15caa9729a,0x15cb0972c15cae972b9,0x1453a514da5cb2972c9,0x12f3e514f2273c514ea,0x5150245405f8fa]),([8,31,992,1047552,2164802,4329604,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14270489c10,0x1270e89c39158685618,0x1271489c51271289c49,0x1272289c82272049c61,0x1272c49c9a272649c92,0x1273249cc2273049cb9,0x15cbc456e915b889cca,0x10240456fa2f3e456f2,0x40902]),([8,31,992,1048575,1082401,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x1bc85af2147e049f810,0x17e0e9f8397e069f818,0x17e155f8527e135f84a,0x17ca09f8717e1a9f869,0x1bcac5f89a7e265f889,0x1bcb0af2c1b7afaf0b2,0x17e385f4da0532914c9,0x115bc5f8ee7e3a5ece6,0x11c405f8fa7e3e5f8f2,0x52702]),([8,31,992,1048575,1082401,2164802,4329604,17318416],hh [0x1498192604498092600,0x149839260c498292608,0x13c058f014498492610,0x1498e92639498692618,0x149955265249935264a,0x149a252482499c52669,0x149a69269945249168a,0x181b0a06c13c2f8f0b1,0x149b9526da0532914c9,0x1273c526ee49ba526e6,0x12f40526fa5cbe526f2,0x5f902])]
def b131 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1048575,1082401,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391c0687018,0x12f154bc522f134bc4a,0x12f1c4bc6a2f1a4a062,0x12f268bc992f2249c72,0x12f304bcbe2f2e4bcb1,0x11c388bcca2f324bcc2,0x1273c470ee2f3a4b0e5,0x10540470fa5cbe470f2,0x41502]),([8,31,992,1048575,1082401,4329604,8659208,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x15c85972145c8497210,0x15c8e97239450691418,0x15c95572525c935724a,0x15ca2564765c9c57269,0x15cac572aa5ca697299,0x15cb0572ba5cae572b2,0x14536972ca5cb2572c2,0x1453c89cf1453a514e5,0x14540915017e3e8bcf9]),([8,31,992,1048575,2164802,4329604,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14270489c10,0x1270e89c39158685618,0x1271549c52271349c4a,0x1272249c82271d89c69,0x1272689c99272489c8a,0x1273089cc1272e49cb1,0x124b9456e2273289cc9,0x12f3e456f25cbc49ce9,0x409020240456fa]),([8,31,992,1048576,2164802,8659208,17318416,32505856],hh [0x1a901aa404a900aa400,0x1a903aa40ca902aa408,0x1a905aa414a904aa410,0x1a90eaa439270689c18,0x1a914aa451a912aa449,0x1a9226a472a91c67c69,0x1a926aa499a924aa491,0x1a92eaa4b99a2d6a4b2,0x1a932aa4c9a930aa4c1,0x12738a68e1273689cd9,0x1273e89cf9a93b49cea,0x115c085701]),([8,31,992,1082401,2097152,4329604,17318416,32505856],hh [0x1450191404450091400,0x145039140c450291408,0x145059141436048d810,0x1450e91439450691418,0x1451a51462451851451,0x1362251472451c5146a,0x136268d8990d2483491,0x1272e514b6452d514aa,0x12f32514c24530514ba,0x14538514da85b65f8ca,0x1453d514f2453a914e2,0x1454091501453f8d8f9]),([8,31,992,1082401,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b062ac14ab051,0x1ac22a9e89ac1cab071,0x1ac26ab099ac24ab091,0x1ac2e6b0b6ac2c6b0aa,0x1ac326b0c2ac306b0ba,0x19cb85f8da87366b0ca,0x17e406def97e3a9f8e2,0x5f902]),([8,31,992,1082401,2164802,4329604,8659208,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1883c61ac14ab051,0x1aa206b072ac1c68269,0x1ac24ab091ac22a9e89,0x1ac2c6b0aaac26ab099,0x1ac306b0baac2e6b0b6,0x17e36ab0caac326b0c2,0x17e3a9f8e29cb86b0dd,0x17e409f501]),([8,31,992,1082401,2164802,4329604,8659208,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1c6b062ac14ab051,0x1ac24ab091ac22ab072,0x1ac2c6b0aaac26ab099,0x1ac306b0baac2e6b0b6,0x187366b0caac326b0c2,0x17e3aab0e57e389f8da,0x1ac415f902b73e5e4f5])]
def b132 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,8659208,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac18ab052ac146904a,0x1a7a26b072ac1c68269,0x1ac266b092ac246b08a,0x1ac2dab0b1ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x19cb85f8daac32ab0c9,0x1b7be6b0ed7e3a9f8e2,0x17e409f901]),([8,31,992,1082401,2164802,4329604,8659208,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b062ac14ab051,0x1ac22a9e89ac1cab071,0x1ac26ab099ac24ab091,0x1a82cab0b1a82bab0aa,0x1a82fab0baac2e6b0b6,0x1ac326a0c6ac30ab0c1,0x19cb85f8daa833ab0ca,0x17e406def97e3a9f8e2,0x1ac415f902]),([8,31,992,1082401,2164802,4329604,8659208,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0390d0683418,0x1ac18ab052ac144a24a,0x1ac1cab071561aa8269,0x1ac22a9e89aba18c082,0x12f25ab092ac244bc8e,0x1ac2a8bc9eac26ab099,0x1ac2d984b2ac2c584ae,0x1ac30584beac2eab0b9,0x1ac32ab0c96131ab0c2,0x1afb8a3eda61338bccd,0x1563d49ced73baa72e5,0x10d40835012f3f4bcf9,0x58505]),([8,31,992,1082401,2164802,4329604,8659231,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397d069f418,0x1ac186b052ac146b049,0x1ac1cab071a09a6b062,0x1ac246b08aa7a26b081,0x1ac2aab09aac266b092,0x1ac2eab0b6ac2c6b0ad,0x17d366b0caac30ab0c1,0x17d3a9f4e29cb85f4da,0x5f5027d406def9]),([8,31,992,1082401,2164802,4329604,8682760,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6397c069f018,0x1a11a6d662b594ad651,0x1b5a2aca89b59cad671,0x1b5a6ad699b5a4ad691,0x1b5aeab0b6b5ac6d6aa,0x187366d0caacb0ad6c1,0x17c3a9f0e29cb85f0da,0x60702ac406def9]),([8,31,992,1082401,2164802,4329604,9741609,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1c68269ac18ab051,0x1ac246b08aa7a26b072,0x1ac2aab09aac266b092,0x1ac2f6b0baac2dab0b1,0x1ac32ab0c9ac30ab0c1,0x17e38a72e17e36a1cd9,0x17e409f901b7be5f8ea]),([8,31,992,1082401,2164802,4329604,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b062ac14ab051,0x1a7a26b072ac1c6b06a,0x1ac266b092ac246b08a,0x1ac2da82b1ac2aab09a,0x1ac316b0c2ac2eab0b9,0x17e36a1cd9ac32ab0c9,0x17e3d5f8ea7e38a72e1,0x17e405cef9]),([8,31,992,1082401,2164802,4329604,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1a09a6b062ac14ab051,0x1ac2469e89ac1cab071,0x1ac2aab09aac266b092,0x1ac2eab0b9ac2da9eb1,0x1ac336b0caac30ab0c1,0x149b8a72e149b6a1cd9,0x52701bcbe526ea])]
def b133 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1aa8269ac18ab051,0x1ac2469e89ac1cab071,0x1ac2aab09aac266b092,0x1ac2f6b0baac2da72b1,0x1ac336b0caac316b0c2,0x149b8a72e149b6a1cd9,0x1ac404f0f9453d526ea,0x52706]),([8,31,992,1082401,2164802,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1aa8269ac18ab051,0x1ac2469e89ac1cab071,0x1ac2aab09aac266b092,0x1ac2eab0b9ac2da72b5,0x1ac32ab0c9ac30ab0c1,0x149b8a72e149b6a1cd9,0x149c04f0f9453d526ea,0x52702]),([8,31,992,1082401,2164802,4329604,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1a09a6b0620f186b051,0x1aa206b072ac1c6b06a,0x1ac266b092ac2469e89,0x1ac2da72b5ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x1ac37526daac32ab0c9,0x145bd526ea49b8a72e1,0x149c092701]),([8,31,992,1082401,2164802,4329604,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1c6b06aac18ab051,0x1ac266b092ac246b072,0x1ac2e6b0b6ac2aab09a,0x1ac326b0c2ac306b0ba,0x149b8926da87366b0ca,0x149c0924f549baab0e5,0x6b105]),([8,31,992,1082401,2164802,4329604,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac188f652ac1468e4a,0x1ac1cab071ac1aa8269,0x1ac266b092ac2469e89,0x1ac2da72b5ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x19cb8526daac32ab0c9,0x1453d6b0ed49ba926e2,0x5270249c0434f9]),([8,31,992,1082401,2164802,4329604,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0390d0683418,0x1ac18a9452ac144624a,0x1ac1cab071ac1aa8269,0x1a722a9e89a72187c82,0x11c25ab092ac244788e,0x1ac2a8709eac26ab099,0x1ac2da72b5a82caa0ae,0x1ac306a0beac2eab0b9,0x1ac32ab0c9a831ab0c2,0x19cb863cdaa833870cd,0x1453d456ed3c3a93ee2,0x10d40835011c3f470f9,0x6a105]),([8,31,992,1082401,2164802,4329604,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1aa8269ac18ab051,0x1ac2469e89ac1cab071,0x1ac2aab09aac266b092,0x1ac2da72b5612c984ae,0x1ac30584beac2eab0b9,0x1ac32ab0c96131ab0c2,0x19cb9526e249b6984ce,0x149c04f0f9453d526ea,0x1ac4152702]),([8,31,992,1082401,2164802,4329604,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac18ab061ac146b049,0x1ac1cab071ac1aa8269,0x1ac24ab091a7a26b081,0x1ac2b6b0aaac26ab099,0x1ac306b0baac2da72b5,0x149b6926d9ac32ab0c2,0x1453d526ea49b8a72e1,0x5270249c04f0f9])]
def b134 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,17333776,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead639498692618,0x1b59aa8469b598ad651,0x1b5a46ca89b59cad671,0x1b5aaad69ab5a66d692,0x1b5b06d6baac2da72b5,0x149b6a1cd9b432ab2c2,0x1453d526ea49b8a72e1,0x60702ac404f0f9]),([8,31,992,1082401,2164802,4329604,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1a09a6b062ac14ab051,0x1a7a26b072ac1c6b06a,0x1ac26ab099ac24ab091,0x1ac2eab0b69cad6b0aa,0x1ac326b0c2ac306b0bd,0x19cb8526da87366b0ca,0x173be514f549ba926e2,0x149c092701]),([8,31,992,1082401,2164802,4329604,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1c68269ac18ab051,0x1ac24ab091a7a26b072,0x1a7ad6b0aaac26ab099,0x1ac30ab0baac2e6b0b6,0x187366b0caac326b0c5,0x149ba926e29cb8526da,0x149c06f2f9]),([8,31,992,1082401,2164802,4329604,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1aa8269ac18ab051,0x1ac22a9e89ac1cab071,0x1ac26ab099ac24ab091,0x1ac2e6b0b6a0ad6b0aa,0x1ac32ab0c2ac306b0ba,0x19cb85f8da87366b0cd,0x13c3e5f8f57e3a9f8e2,0x5f901]),([8,31,992,1082401,2164802,4329604,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b062ac14ab051,0x1ac22a9e89ac1cab071,0x1ac26ab099ac24ab091,0x1ac2eab0b6ac2d6b0aa,0x1ac32ab0c5ac30ab0bd,0x19cb85f8da87366b0cd,0x1ac406def97e3a9f8e2,0x5f906]),([8,31,992,1082401,2164802,4329604,32505856,32776456],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f814ba04ae810,0x17e0e9f8397e069f818,0x17e1a5f2627e149f851,0x1b9a2ae8897e1c9f871,0x1052691499ba24ae891,0x17e2c6a0ae7e2a9f8a9,0x1a82f9f8baa82d9f8b2,0x1ba32adec97e31aa0c2,0x1ac399f8e17d36aa0ce,0x149be870f97e3c9f8ea,0x5f9057e409f901]),([8,31,992,1082401,2164802,4329604,32505856,33047056],hh [0x1498192604498092600,0x149839260c498292608,0x14985926143c048f010,0x1498e92639498692618,0x1459a92669491892651,0x10d244f089499c92671,0x149aa4149a452643492,0x149ac926b1612b926aa,0x149b0984be49ae984b6,0x161328f0c96131914c5,0x1ac39926e549b6926ce,0x12f3e514f549bc926ea,0x149c15270249c05f8fa]),([8,31,992,1082401,2164802,4329604,32776456],hh [0x1a801ea005a800ea001,0x1a803ea00da802ea009,0x17e05df815a804ea011,0x1a813ea04ba80fea03b,0x1a819ea063a815ea053,0x1a81dea073a81bea06b,0x1a823ea08ba821ea083,0x1a827ea09ba825ea093,0x1ac2ddf8b3a82bdf8ab,0x17e31df8c3a82fdf8bb,0x1a833eb8cb])]
def b135 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,4329604,33047056],hh [0x16101d84056100d8401,0x16103d840d6102d8409,0x14985d26156104d8411,0x16113d844b610fd843b,0x16119d84636115d8453,0x1611dd8473611bd846b,0x16123d848b6121d8483,0x16127d849b6125d8493,0x1ac2dd26b3612bd26ab,0x16131d26c3612fd26bb,0x149b3cf0cb]),([8,31,992,1082401,2164802,4330468,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a7956b052ac1469e3e,0x1ac1c69e6dac1a6b062,0x1ac236b08aa7a26b072,0x1ac2aab09aac24ab091,0x1ac2e6b0b6a7ad6b0b1,0x1ac326b0c2ac306b0ba,0x17e385f8da87366b0ce,0x1b73e5f8eaa7b95f8e2,0x17e409f901]),([8,31,992,1082401,2164802,5412005,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac18ab052ac146b04a,0x1a7a26b072ac1c68269,0x1ac266b095ac24ab08a,0x1ac2dab0b1ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x17e36a1cd9ac32ab0c9,0x1a93b5f8ea7e38a72e1,0x5f9027e406def9]),([8,31,992,1082401,2164802,5412005,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac18ab052ac146b04a,0x1ac1cab071ac1aa8269,0x1ac266b095ac24a9e89,0x1ac2da72b5ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x149b6a1cd9ac32ab0c9,0x1a93b526ea49b8a72e1,0x149c0927010d3e514f5]),([8,31,992,1082401,2164802,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1c68269ac14ab051,0x1ac246b08a9ca26b072,0x1ac2aab09dac26ab092,0x1ac2eab0b9ac2dab0b1,0x1ac32ab0c9ac30ab0c1,0x17e38a72e17e36a1cd9,0x17e405f8feac3e5f8ea,0x5f902]),([8,31,992,1082401,2164802,6494406,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1cab071a09a6b051,0x1ac26ab092ac2467289,0x1ac2da72b5ac2aab09d,0x1ac30ab0c1ac2eab0b9,0x149b6a1cd9ac32ab0c9,0x1ac3e526ea49b8a72e1,0x5270249c0526fe]),([8,31,992,1082401,2164802,8659208,12988812,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b062ac14ab051,0x1ac246b089ac1cab071,0x1a7ac6b09aac266b092,0x1ac306b0baac2e6b0b2,0x187366b0cdac32ab0c2,0x17e3a9f8e29cb85f8da,0x471017e3e9f8f9]),([8,31,992,1082401,2164802,8659208,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1a09a6b052ac146b04a,0x1ac246b089ac1cab071,0x19cac6b09aac266b092,0x1ac30ab0bdac2eab0b2,0x187366b0cdac32ab0c5,0x17e3a9f8e29cb85f8da,0x1ac405f8fa7e3e6a4ed,0x5f906])]
def b136 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1a09a6b052ac146b04a,0x1ac246b089ac1cab071,0x1ac2cab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x12f3a8bce29cb84bcda,0x11c404bcfa2f3e6a4ed,0x47102]),([8,31,992,1082401,2164802,8659208,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x10f186b052ac146b04a,0x1ac226b072ac1c68269,0x1ac26ab099ac24ab091,0x1ac2eab0b99cad6b0b2,0x1ac32ab0c9ac30ab0c1,0x12f38a72e1ac374bcda,0x11c408bcfaa93b4bcea]),([8,31,992,1082401,2164802,8659208,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1c6b052ac146b04a,0x1ac24ab091ac226b072,0x1ac2e6b0b2ac26ab099,0x1ac326b0c2ac306b0ba,0x12f388bcda87366b0ca,0x12f3eaa4ed2f3aab0e5,0x11c4087101]),([8,31,992,1082401,2164802,8659208,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1a09a6b052ac146b04a,0x1ac246b089ac1cab071,0x1ac2cab09aac266b092,0x1ac306b0baac2e672b5,0x12f36ab0caac326b0c2,0x1ac3b4bcea2f38a72e1,0x11c40871012f3e8bcf9]),([8,31,992,1082401,2164802,8659208,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1a09a6b052ac146b04a,0x1a72187c82ac1cab071,0x1ac244788ea722ab089,0x1ac26ab0991c25ab092,0x1ac2e672b5ac2c8709e,0x1ac326b0c2ac306b0ba,0x19cb84bcda1c336b0ca,0x12f3e6a4ed2f3a8bce2,0x1054081501ac3f4bcfa]),([8,31,992,1082401,2164802,8659208,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0391c0687018,0x1a09a6b052ac146b04a,0x1ac246b089ac1cab071,0x1302aab09aac266b092,0x12f2da72b5ac2caaeae,0x1ac304bcbeac2eab0b9,0x1ac32ab0c92f31ab0c2,0x19cb9470e21c368bcce,0x1053e814f9a93b470ea,0x6b1051c4087101]),([8,31,992,1082401,2164802,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1a6b052ac146b04a,0x1ac246b089ac1cab071,0x1ac2cab09aac266b092,0x1ac30ab0baac2e6b0b5,0x12f384bcda87366b0ca,0x12f3e6a4ed2f3a8bce2,0x471021c404bcfa]),([8,31,992,1082401,2164802,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1c68269ac14ab051,0x1ac24ab091ac226b072,0x19cad6b0b2ac26ab099,0x1ac30ab0c1ac2f6b0ba,0x12f36a1cd9ac32ab0c9,0x12f3e4bcea2f38a72e1,0x471021c404bcfa])]
def b137 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,8659208,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac18ab052ac146b04a,0x1ac226b072ac1c68269,0x1ac26ab099ac24ab091,0x1ac2eab0b9a7ad6b0b2,0x1ac32ab0c9ac316b0c2,0x12f38a72e12f36a1cd9,0x12f3e8bcf9a93b4bcea,0x47101]),([8,31,992,1082401,2164802,8659208,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1a09a6b052ac146b04a,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2e672b5ac2cab09a,0x1ac32ab0c2ac306b0ba,0x19cb84bcda87366b0cd,0x12f3e6a4ed2f3a8bce2,0x4150205404bcfa]),([8,31,992,1082401,2164802,8659208,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1a09a6b062ac14ab051,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2ea9eb5ac2cab09a,0x1ac32ab0c5ac30ab0bd,0x19cb84bcda87366b0cd,0x12f3e8bcf92f3a8bce2,0x6df01]),([8,31,992,1082401,2164802,8659208,32505856,32641156],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f8147e049f810,0x17e0e9f839b786ade18,0x17e1a5f2627e149f851,0x17e225f4827e1c9f871,0x17e265f8927e245ec8e,0x17e2c5f8aa7e2a5f89a,0x17e325f8c27e2e9f8b2,0x1b7baadce2b7b85f8ca,0x1b7c0870fa49be6b0f2,0x5f905]),([8,31,992,1082401,2164802,8659208,32505856,33047056],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391c0687018,0x12f1a4bc522f144a04a,0x12f244bc892f1c8bc71,0x12f2a4bc9a2f264bc92,0x12f2c8bcb12f2b8bcaa,0x12f2f89cbd2f2e8bcb6,0x12f328bcc92f318bcc2,0x11c3a8b0e51c388bcce,0x1053e814f91c3c89ced,0x4bd051c4087101]),([8,31,992,1082401,2164802,8659208,33047056],hh [0x12f01cbc052f00cbc01,0x12f03cbc0d2f02cbc09,0x11c05c70152f04cbc11,0x12f13cbc4b2f0fcbc3b,0x12f19cbc632f15cbc53,0x12f1dcbc732f1bcbc6b,0x12f23cbc8b2f21cbc83,0x12f27cbc9b2f25cbc93,0x12f2dc70b3ababc70ab,0x12f31c70c32f2fc70bb,0x12f33c14cb]),([8,31,992,1082401,2164802,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1cab071a09a6b051,0x1ac266b095ac24ab089,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x19cb84bcda87366b0ca,0x12f3e8bcf92f3a8bce2,0x11c4087101]),([8,31,992,1082401,2164802,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac18ab052ac146b04a,0x1ac1cab071ac1aa8269,0x1ac26ab092ac2468289,0x1ac2e672b5ac2cab09d,0x1ac326b0c2ac306b0ba,0x19cb84bcda87366b0ca,0x12f3d6a4ed2f3a8bce2,0x471021c404bcf9])]
def b138 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164802,17318416,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1aa8269ac18ab051,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e682b5,0x187366b0cdac32ab0c2,0x149ba926e29cb8526da,0x12f40526fa49be514f5]),([8,31,992,1082401,2164802,17318416,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1a09a6b052ac146b04a,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2eab0b5,0x187366b0cdac32ab0c5,0x149ba926e29cb8526da,0x1ac40526fa49be6a4ed,0x52706]),([8,31,992,1082401,2164802,17318416,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0391c0687018,0x1a09a6b052ac146b04a,0x19ca36b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2eab0b99cad6b09a,0x1ac336b0caac30ab0c1,0x11c38a72e11c36a1cd9,0x11c3e870f9a93b470ea,0x1054081501]),([8,31,992,1082401,2164802,17318416,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0391c0687018,0x1ac1aa8269ac18ab051,0x19ca36b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2f6b0baa7ad6b09a,0x1ac336b0caac316b0c2,0x11c38a72e11c36a1cd9,0x11c3e870f9053d470ea,0x4f101]),([8,31,992,1082401,2164802,17318416,32505856,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x1498592614498492610,0x1498e926393c068f018,0x1459a92669491892651,0x149a352682499c92671,0x149a65269249a45268e,0x149ac526aa49aa5269a,0x14531526c249ae926b2,0x10d3a8f0e149b2926c9,0x12f3e9f8f9453d6b0f2,0x149c14f102]),([8,31,992,1082401,2164802,17318416,32505856,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c05870141c0487010,0x11c0e870392f068bc18,0x11c1a46c521c1445c4a,0x11c234708a1c1c87071,0x11c26870991c2487091,0x11c2c470ae1c2a870a9,0x115af470ba1c2d870b2,0x11c32470c61c30870be,0x12f3a8bce11c33870ca,0x1053e814f92f3c856ed,0x471052f408bd01]),([8,31,992,1082401,2164802,17318416,32776456],hh [0x11c01c70051c00c7001,0x11c03c700d1c02c7009,0x12f05cbc151c04c7011,0x11c13c704b1c0fc703b,0x11c19c70631c15c7053,0x11c1dc70731c1bc706b,0x11c23c708b1c21c7083,0x11c27c709b1c25c7093,0x11e2dcbcb3a72bcbcab,0x11c31cbcc31c2fcbcbb,0x11c33c14cb]),([8,31,992,1082401,2164831,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397c869f218,0x1ac18ab052ac146b049,0x1ac206b072a09a6b065,0x1ac24ab091ac22a9e89,0x1ac2c6b0aaac2a6b099,0x1ac306b0baac2e6b0b6,0x17cb66b0caac326b0c2,0x17cba9f2e29cb85f2da,0x5f3027cc06def9])]
def b139 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,2164831,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039490692418,0x1ac196b062ac146b049,0x1ac206b072ac1aa8269,0x1ac266b092ac2469e89,0x1ac2da72b5ac2aab0a9,0x1ac30ab0c1ac2eab0b9,0x14936924d9ac32ab0c9,0x1453d524ea4938a72e1,0x5250249404ecf9]),([8,31,992,1082401,2165730,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039458691618,0x1ac18a8255ac146823e,0x1ac1cab06dac1aa8269,0x1ac24ab091a0a36b089,0x1a0ad6b0b1ac2aab099,0x1ac306b0baac2e6b0b6,0x187366b0caac326b0c6,0x1a0b9516e245b8516da,0x145c04dcf9453d516ea,0x51702]),([8,31,992,1082401,2194498,4329604,8659208,32505856],hh [0x1ac81ab204ac80ab200,0x1ac83ab20cac82ab208,0x1ac85ab214ac84ab210,0x1ac8eab2397a069e818,0x1a11a6b262ac94ab251,0x1aca46b28aa7a26b272,0x1acac6b2aaac266b292,0x1acb06b2baacae6b2b6,0x187366b2caacb26b2c2,0x17a3a9e8e29cb85e8da,0x5e9027a406def9]),([8,31,992,1082401,2194498,4329604,17318416,32505856],hh [0x1ac81ab204ac80ab200,0x1ac83ab20cac82ab208,0x1ac85ab214ac84ab210,0x1ac8eab239498692618,0x1ac9aa8469ac98ab251,0x1aca4ab291a7a26b272,0x1acada72b5acaaab099,0x1acb0ab2c1acaeab2b9,0x149b6a1cd9acb2ab2c9,0x1453d526ea49b8a72e1,0x5270249c04f0f9]),([8,31,992,1082401,3247203,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1ca8269ac18ab051,0x1ac246b08aa7a26b075,0x1ac2aab09aac266b092,0x1ac2eab0b9ac2dab0b1,0x1ac32ab0c9ac30ab0c1,0x17e38a72e17e36a1cd9,0x17e406def97e3a9f8e9,0x5f902]),([8,31,992,1082401,3247203,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1aa8269ac18ab051,0x1ac2469e89ac1d6b072,0x1ac2aab09aac266b092,0x1ac2eab0b9ac2da72b5,0x1ac32ab0c9ac30ab0c1,0x149b8a72e149b6a1cd9,0x1363e514f549ba926e9,0x149c092701]),([8,31,992,1082401,3247203,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1d6b072a09a6b051,0x1ac266b092ac246b089,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x19cb84bcda87366b0ca,0x12f3e4bcea2f3a4bce2,0x471021c404bcfa]),([8,31,992,1082401,4329604,6494406,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039bc86af218,0x1ac1c69e69ac14ab051,0x1ac2467289ac20ab072,0x1ac2aab09dac26ab092,0x1ac2eab0b9ac2dab0b1,0x1ac32ab0c9ac30ab0c1,0x1bcb8a72e1bcb6a1cd9,0x1bcc0ae901453faf2ea])]
def b140 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,6494406,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039450691418,0x1ac1cab071a79a6b051,0x1ac246b08a9ca26b082,0x1ac2aab09dac26ab092,0x1ac2eab0b9ac2da72b5,0x1ac32ab0c9ac30ab0c1,0x14538a72e14536a1cd9,0x14540514fe453f514ea,0x51502]),([8,31,992,1082401,4329604,8388608,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac22ab089ac20ab081,0x1ac26ab099ac24ab091,0x1ac2eab0b99cad6b0aa,0x1ac32ab0c9ac30ab0c1,0x15cb8a72e15cb6a20d9,0x1ac3f572fa5cba964e9,0x51502]),([8,31,992,1082401,4329604,8659208,10824010,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039bc86af218,0x1ac1aa9e69ac14ab051,0x1ac226b082ac1cab071,0x1ac266b092ac246b08a,0x1ac2e682b1ac2aab09a,0x1ac32ab0c2ac306b0ba,0x19cb86f2da87366b0cd,0x1bcbeadef1bcbaaf2e2,0x6b0fd]),([8,31,992,1082401,4329604,8659208,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039bc86af218,0x1ac1cab071a79a6b051,0x1ac246b08aac226b082,0x1ac2aab09aac266b092,0x1ac30ab0bdac2ea72b1,0x187366b0cdac32ab0c5,0x193ba6f2e29cb86f2da,0x14541ab0fdbcbeaf2ea]),([8,31,992,1082401,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac246b08aac226b082,0x1ac2aab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x1593a572e29cb8572da,0x14540ab0fd5cbe972ea]),([8,31,992,1082401,4329604,8659208,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1c69e69aa186b051,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1ac2eab0b99cad6b0aa,0x1ac32ab0c9ac30ab0c1,0x15cb8a72e1ac37572da,0x14540ab0fd5cbe972ea]),([8,31,992,1082401,4329604,8659208,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac20ab072ac1c6b051,0x1ac24ab091ac22ab089,0x1ac2e6b0aaac26ab099,0x1ac326b0c2ac306b0ba,0x15cb8972da87366b0ca,0x1ac3f572fa5cbaab0e5,0x1ac4156b02]),([8,31,992,1082401,4329604,8659208,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x13914ab0513913a8a4a,0x1ac1cab071a79a5c856,0x1ac22ab089ac208d875,0x1ac264d895ac24ab091,0x1ac2e672b5ac2aab09a,0x1ac30ab0c1362f6b0ba,0x19cb8572daac32ab0c9,0x1ac3b572ea553a572e2,0x51502ac3f572fa])]
def b141 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,8659208,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac246b08aac226b082,0x1ac2aab09aac266b092,0x1ac306b0baac2e672b5,0x15cb6ab0caac326b0c2,0x15cba964e95cb8a72e1,0x51502ac3f572fa]),([8,31,992,1082401,4329604,8659208,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039450691418,0x1ac1cab071a79a6b051,0x1ac246b08aac226b082,0x1ac2aab09aac266b092,0x1ac2eab0b99cad558b2,0x1ac32ab0c9ac30ab0c1,0x1453a672e55ab8914da,0x14540ab0fd453e914ea,0x6b105]),([8,31,992,1082401,4329604,8659208,17318431,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1a79a6b061ac146b049,0x1ac20ab081ac1cab071,0x1ac24ab091ac22ab089,0x1ac2b6b0aaac26ab099,0x1ac326b0c2ac2ea72b5,0x19cb8572da5cb66b0ca,0x15cbe972ea593a572e2,0x14540ab0fd]),([8,31,992,1082401,4329604,8659208,17333776,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6395c8697218,0x1b59cad671b29a6d651,0x1b5a46d68ab5a26d682,0x1b5aaad69ab5a66d692,0x1b5b26d0c2b5aea72b5,0x19cb8572da87366d6ca,0x15cbe972ea593a572e2,0x181c0ad6fd]),([8,31,992,1082401,4329604,8659208,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1c69e69ac14ab051,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1ac2f6b0ba9cad6b0aa,0x1ac32ab0c9ac30ab0c1,0x15cb8a72e15cb6a1cd9,0x14540ab0fd5cbe972ea]),([8,31,992,1082401,4329604,8659208,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1c6b06aa79a6b051,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1ac2eab0b9a0ad6b0aa,0x1ac32ab0c9ac316b0c2,0x15cb8a72e15cb6a1cd9,0x15cbe96ef15cba964e9,0x6b0fd]),([8,31,992,1082401,4329604,8659208,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac246b08eac226b082,0x1ac2aab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0cdac32ab0c2,0x1593a572e29cb8572da,0x14540972fa5c3e572ea]),([8,31,992,1082401,4329604,8659208,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1aa9e69ac14ab051,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2ea82b5ac2aab09a,0x1ac32ab0c5ac30ab0bd,0x19cb8572da87366b0cd,0x15c3e56ef15cba972e2,0x572fa])]
def b142 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,8659231,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1a79a6b061ac146b049,0x1ac216b082ac1cab071,0x1ac26ab092ac22ab089,0x1ac2e672b5ac2aab0a9,0x1ac326b0c2ac306b0ba,0x19cb8572da5cb66b0ca,0x15cbe972ea593a572e2,0x14540ab0fd]),([8,31,992,1082401,4329604,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1a6b055ac146b03e,0x1ac20ab072ac1c6b06d,0x1ac24ab08dac22ab089,0x1ac2d6b0b1ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x15cb8572da87366b0c9,0x15cba964e9ac39572e2,0x51502ac3f572fa]),([8,31,992,1082401,4329604,8682760,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6395c8697218,0x1b59cad671b29a6d651,0x1b5a4ad68ab5a26d682,0x1b5ae672b5b5aaad09a,0x1b5b26d6c2b5b06d6ba,0x19cb8572da87366d6ca,0x15cbe972ea593a572e2,0x14540ab0fd]),([8,31,992,1082401,4329604,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac24ab08aac226b082,0x1ac2aab09aac266b095,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x15cba972e29cb8572da,0x51502ac3f572fa]),([8,31,992,1082401,4329604,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac246b08aa7a26b082,0x1ac2aab09dac26ab092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x1593a572e29cb8572da,0x149c0972fd5cbc572ea]),([8,31,992,1082401,4329604,17318416,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac24ab0919ca36b082,0x1ac2cab0aaac26ab099,0x1ac306b0baac2e69eb5,0x187366b0cdac32ab0c2,0x15cba972e29cb8572da,0x5730549be972f1]),([8,31,992,1082401,4329604,17318416,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071a79a6b051,0x1ac24ab0919ca36b082,0x1ac2cab0aaac26ab099,0x1ac30ab0bdac2eab0b5,0x187366b0cdac32ab0c5,0x1593a572e29cb8572da,0x15cc197305453e972ea]),([8,31,992,1082401,4329604,17318416,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039450691418,0x1ac1cab071a79a6b051,0x1ac246b08e9ca36b082,0x1ac2aab09aac266b092,0x1ac2eab0b99cad6b0b2,0x1ac336b0caac30ab0c1,0x14538a72e14536a1cd9,0x1453e914f9453a914e9,0x1ac4151502])]
def b143 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082401,4329604,17318416,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1cab071a79a6b051,0x1ac246b08e9ca36b082,0x1ac2aab09aac266b092,0x1ac2f6b0baa0ad6b0b2,0x1ac336b0caac316b0c2,0x149b8a72e149b6a1cd9,0x149be926f93c3c526ea,0x51505]),([8,31,992,1082401,5412005,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1a79a6b052ac146b04a,0x1ac226b082ac1d6b072,0x1ac266b092ac246b08a,0x1ac2e672b5ac2aab09a,0x1ac326b0c2ac306b0ba,0x19cb8572da87366b0ca,0x15cbeaa4ed5cba972e2,0x14540ab0fd]),([8,31,992,1082401,8659208,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac18ab052ac146b04a,0x1ac1cab071ac1aab069,0x1ac26ab092ac2468289,0x1ac2e672b5ac2cab09d,0x1ac326b0c2ac306b0ba,0x19cb84bcda87366b0ca,0x12f3caa4ed2f3a8bce2,0x4150205406b0f5]),([8,31,992,1082401,8659208,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071ac1a6b051,0x1ac26ab092ac2469e89,0x1ac2e672b5ac2aab09d,0x1ac326b0c2ac306b0ba,0x19cb8572da87366b0ca,0x15cbc572ea593a572e2,0x14540972f2]),([8,31,992,1082401,8659208,17318416,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039050681418,0x1ac1a6b052ac146b04a,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e69eb5,0x187366b0cdac32ab0c2,0x1053a814e29cb8414da,0x1053e814f2053c6a4ed]),([8,31,992,1082401,8659208,17318416,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039450691418,0x1ac1aab069ac18ab051,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e682b5,0x187366b0cdac32ab0c2,0x1453a514e29cb8514da,0x1453e6b0f5453c914ea,0x514fa]),([8,31,992,1082401,8659208,17318416,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039050681418,0x1ac1aab069ac18ab051,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2ea9eb5,0x187366b0cdac32ab0c5,0x1053a414e29cb8414da,0x1053eab0f5053c814ea]),([8,31,992,1082401,8659208,17318416,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039450691418,0x1ac1a6b052ac146b04a,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2ea82b5,0x187366b0cdac32ab0c5,0x1453a914e29cb8514da,0x1453e514f2453c6a4ed,0x514fa])]
def b144 : List (List Nat × List (Nat × Nat)) := [([8,31,992,1082431,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03928068a018,0x1ac14ab051ac136b04a,0x1ac206b071a09a6b061,0x1ac26ab099ac246b089,0x1ac2e672b5ac2cab0a9,0x1ac32ab0c9ac30ab0c1,0x12838a72e128368a0d9,0x1283e8a0f9a93b4a0ea,0x1174085d01]),([8,31,992,1083361,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac156b052ac146b03e,0x1ac1c6b06dac1a6b062,0x1ac246b08dac22ab089,0x1ac2aab09aac266b092,0x1ac2e6b0b6ac2d6b0b1,0x1ac326b0c2ac306b0be,0x17e385f8da87366b0ca,0x1b6be5f8eaac395f8e2,0x17e409f901]),([8,31,992,1083361,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac14ab051ac12ab03e,0x1ac1c6b06dac1a6b055,0x1ac266b091ac236b089,0x1ac2d6b0b2ac2c6b09a,0x1ac30ab0c1ac2eab0b9,0x12f36a1cd9ac32ab0c9,0x12f3aab0e52f388bce1,0x11b404bcfa2f3e6a4ed,0x46d02]),([8,31,992,1113121,2164802,8659208,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6392d068b418,0x1a11a6d652b5946d64a,0x1b5a66d691b5a26b271,0x1b5ae672b5b5acad69a,0x1b5b2ad6c9b5b0ad6c1,0x12d38a72e12d36a1cd9,0x12d3e8b4f9a93b4b4ea,0x11c4087101]),([8,31,992,2164802,3247203,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0397e069f818,0x1ac1cab06aa09a68251,0x1ac246b08aa7a26b075,0x1ac2aab09aac266b092,0x1ac2eab0b9ac2dab0b1,0x1ac32ab0c9ac30ab0c1,0x17e38a72e17e36a1cd9,0x17e409f90173be5f8e9]),([8,31,992,2164802,3247203,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039498692618,0x1ac1d6b072a09a68251,0x1ac266b092ac2469e89,0x1ac2da72b5ac2aab09a,0x1ac30ab0c1ac2eab0b9,0x149b6a1cd9ac32ab0c9,0x13c3e526e949b8a72e1,0x149c092701]),([8,31,992,2164802,3247203,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1aa8269ac18a8251,0x1ac246b089ac1d6b072,0x1ac2cab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x12f3a4bce29cb84bcda,0x11c404bcfa2f3e49cf5,0x47102]),([8,31,992,2164802,4194304,8659208,17318416,32505856],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1158585614270489c10,0x1270e89c39270689c18,0x1271a49c62271849c51,0x1272249c72271c49c6a,0x1272689c99272489c91,0x115ae972b924ad456b2,0x10232808c915b0856c1,0x12738a7ae12736a1cd9,0x1273d49cf2273b89ce9,0x115c089cfa])]
def b145 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,5412005,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03973869ce18,0x1a79a6b062a0946b04a,0x1a7a26b072ac1c6b06a,0x1ac26ab092ac246b08a,0x1ac2dab0b1ac2aab09d,0x1ac30ab0c1ac2eab0b9,0x173b6a1cd9ac32ab0c9,0x173c05cef573b8a72e1,0x5cf02]),([8,31,992,2164802,4329604,5412005,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0393c068f018,0x1ac18ab052a0946b04a,0x1ac1cab071ac1aa9e69,0x1ac26ab092ac2469e89,0x1ac2da72b5ac2aab09d,0x1ac30ab0c1ac2eab0b9,0x13c36a1cd9ac32ab0c9,0x13c3d4d8ed3c38a72e1,0x13c408f101]),([8,31,992,2164802,4329604,8659208,9741609,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03973869ce18,0x1ac1aa9e69a0946b04a,0x1ac246b089ac1cab071,0x1ac2c6b09aac266b092,0x1ac306b0baac2e6b0b2,0x187366b0cdac32ab0c2,0x173bc5cee29cb85ceda,0x115c09cefa]),([8,31,992,2164802,4329604,8659208,16236015,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03973869ce18,0x1ac1aa9e69ac18a8251,0x1ac246b089ac1cab071,0x19cac6b09aac266b092,0x1ac30ab0bdac2eab0b2,0x187366b0cdac32ab0c5,0x173ba5cee29cb85ceda,0x5cf0673be9cef5]),([8,31,992,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aa9e69ac18a8251,0x1ac246b089ac1cab071,0x1ac2cab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x1273a49ce29cb849cda,0x45702273e89cf5]),([8,31,992,2164802,4329604,8659208,17318416,32505887],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac18aa861a09443c49,0x1ac1cab071ac1aa9e69,0x1ac266b092ac246b089,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x19cb86b0dd2736ab0ca,0x1294089cfa273d49ce2]),([8,31,992,2164802,4329604,8659208,17318416,32506848],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1cab071ac1aab062,0x1ac266b092ac246b089,0x1ac2eab0b9ac2cab09a,0x1ac32ab0c9ac30ab0c1,0x1ac3949ce22736a1cd9,0x45702273e89cf5]),([8,31,992,2164802,4329604,8659208,17318416,32539681],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0390d0683418,0x13914a82513913a8a4a,0x1ac1aa9e69ac189c856,0x1a3a08d875ac1cab071,0x1ac24ab0913da2ab089,0x1a42aab09aac264d895,0x1ac2eab0b99cad6b0b2,0x1ac326b0c2ac304d8bd,0x14fb8a72e127b6ab0ca,0x115be8baf5363b4d8e9,0x5cf0527408f0fd])]
def b146 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,8659208,17318416,32776456],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aa9e69ac18a8251,0x1ac2246282ac1cab071,0x1ac266b092ac246948a,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x12738a72e12736ab0ca,0x1ac3f49cfa273d49ce9,0x40902]),([8,31,992,2164802,4329604,8659208,17318416,33047056],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039158685618,0x1ac1aa9e69ac18a8251,0x1ac246b089ac1cab071,0x128aaab09aac266b092,0x1ac2eab0b99cad6b0b2,0x1ac32ab0c9ac30ab0c1,0x115ba672e515b88a4da,0x1ac4145702023e856f5]),([8,31,992,2164802,4329604,8659208,17318896,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aab069ac18ab051,0x1ac246b089ac1cab071,0x1ac2cab09aac266b092,0x1ac30ab0c1ac2eab0b5,0x1273849cda87366b0ca,0x1273e89cf5273a49ce2,0x45702]),([8,31,992,2164802,4329604,8659208,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1a79a6b062a0946b04a,0x1ac226b072ac1c6b06a,0x1ac26ab099ac24ab091,0x1ac2f6b0baa7ad6b0b2,0x1ac32ab0c9ac30ab0c1,0x12738a72e12736a1cd9,0x1273e89cf5]),([8,31,992,2164802,4329604,8659208,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1c6b06aa79a68251,0x1ac24ab091ac226b072,0x1a0ad6b0b2ac26ab099,0x1ac316b0c2ac2eab0b9,0x12736a1cd9ac32ab0c9,0x1273c49ce92738a72e1,0x49cfa]),([8,31,992,2164802,4329604,8659208,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aa9e69ac18a8251,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2e672b5ac2cab09a,0x1ac32ab0c2ac306b0ba,0x19cb849cda87366b0cd,0x1273e49cf5273a49ce2,0x1024089cfa]),([8,31,992,2164802,4329604,8659208,32472030,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aa9e69a0946b04a,0x1ac226b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2eab0b5ac2cab09a,0x1ac32ab0c5ac30ab0bd,0x19cb849cda87366b0cd,0x1273e89cf9273c49ce2,0x49d06]),([8,31,992,2164802,4329604,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac18ab052a0946b04a,0x1ac1cab071ac1aa9e69,0x1ac266b095ac24a8289,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x19cb849cda87366b0ca,0x115c089cf5273b49ce2])]
def b147 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,4329604,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1cab071a79a68251,0x1ac26ab092ac2469e89,0x1ac2e672b5ac2cab09d,0x1ac326b0c2ac306b0ba,0x19cb849cda87366b0ca,0x115c089cf1273a49ce2]),([8,31,992,2164802,4329604,17318416,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0393c068f018,0x1a79a6b052a0946b04a,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e672b5,0x187366b0cdac32ab0c2,0x1363b4f0e29cb84f0da,0x49d023c3e8f0f1]),([8,31,992,2164802,4329604,17318416,24895223,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0393c068f018,0x1ac1aa9e69ac18a8251,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2eab0b5,0x187366b0cdac32ab0c5,0x13c3a4f0e29cb84f0da,0x4f1063c3e8f0f5]),([8,31,992,2164802,4329604,17318416,25977624,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039158685618,0x1ac1aa9e69ac18a8251,0x19ca36b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2eab0b99cad6b09a,0x1ac336b0caac30ab0c1,0x115b8a72e115b6a1cd9,0x115be856f915bd456e9,0x40902]),([8,31,992,2164802,4329604,17318416,32472030,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039158685618,0x1a79a6b052a0946b04a,0x19ca36b082ac1cab071,0x1ac266b092ac246b08e,0x1ac2f6b0baac2d6b09a,0x1ac336b0caac316b0c2,0x115b8a72e115b6a1cd9,0x115be856f915bc408ed,0x45706]),([8,31,992,2164802,4329631,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac196b062a0946b049,0x1ac206b072ac1aa9e69,0x1ac266b092ac246b089,0x1ac2e672b5ac2cab0a9,0x1ac32ab0c9ac306b0ba,0x12738a72e1273689cd9,0x115c089cfa273d49ce9]),([8,31,992,2164802,4330468,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac18a9655ac146963e,0x1ac1cab06dac1aa9669,0x1ac24ab091a5a36b089,0x1a5ad6b0b2ac2c6b099,0x1ac30ab0c1ac2eab0b9,0x12736a1cd9ac32ab0c9,0x1273a696e5273889ce1,0x45702273e89cf5]),([8,31,992,2164802,4357252,8659208,17318416,32505856],hh [0x1b381ace04b380ace00,0x1b383ace0cb382ace08,0x1b385ace14b384ace10,0x1b38eace39270689c18,0x1b39aaca69b398a7c51,0x1b3a4ace91b3a26a472,0x1b3ae672b5b3acace99,0x1b3b2acec9b3b06ceba,0x12738a72e12736a1cd9,0x115c089cfa273d49ce9])]
def b148 : List (List Nat × List (Nat × Nat)) := [([8,31,992,2164802,6494406,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1aa7269ac18a8251,0x1ac246b089ac1d6b072,0x1ac2cab09aac266b092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x1273d49ce29cb849cda,0x45702273e89cf6]),([8,31,992,2164802,8659208,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1cab071ac1a68251,0x1ac246b08aac226b082,0x1ac2cab09dac26ab092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x12f3c8bce29cb84bcda,0x115c085701a93f4bcfa]),([8,31,992,2164802,8659208,12988812,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1cab071ac1a68251,0x1ac246b08aa7a26b082,0x1ac2cab09dac26ab092,0x1ac306b0baac2e672b5,0x187366b0caac326b0c2,0x1273a49ce29cb849cda,0x11c4089cfd273c89cf1]),([8,31,992,2164802,8659208,17318416,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1cab071ac1a68251,0x1ac24ab0919ca36b08a,0x1ac2cab0aaac26ab099,0x1ac306b0baac2e672b5,0x187366b0cdac32ab0c2,0x1273c49ce29cb849cda,0x1a94149d021c3e89cf2]),([8,31,992,2164802,8659208,17318416,21648020,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1cab071ac1a68251,0x1ac24ab0919ca36b08a,0x1ac2cab0aaac26ab099,0x1ac306b0baac2e682b5,0x187366b0cdac32ab0c2,0x12f3a4bce29cb84bcda,0x12741456fa15be4bcf2]),([8,31,992,2164802,8659208,17318416,29224827,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1cab071ac1a68251,0x1ac24ab0919ca36b08a,0x1ac2cab0aaac26ab099,0x1ac30ab0bdac2ea9eb5,0x187366b0cdac32ab0c5,0x1273a49ce29cb849cda,0x49d0515be89cf2]),([8,31,992,2164802,8659208,17318416,32472030,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0392f068bc18,0x1ac1cab071ac1a68251,0x1ac24ab0919ca36b08a,0x1ac2cab0aaac26ab099,0x1ac30ab0bdac2eab0b5,0x187366b0cdac32ab0c5,0x12f3c4bce29cb84bcda,0x12741470fa1c3e4bcf2,0x4bd06]),([8,31,992,4329604,5412005,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1a79a6b052a7946b04a,0x1ac226b082ac1d6b072,0x1ac266b092ac246b08a,0x1ac2e672b5ac2aab09a,0x1ac326b0c2ac306b0ba,0x19cb8572da87366b0ca,0x15cbe964f15cbb572e2,0x13640ab0fd])]
def b149 : List (List Nat × List (Nat × Nat)) := [([8,31,992,4329604,6494406,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac1d6b0729c9a69e51,0x1ac266b092ac246b089,0x1ac2e672b5ac2cab09a,0x1ac326b0c2ac306b0ba,0x19cb849cda87366b0ca,0x1273e89cf68ebc49ce2,0x45702]),([8,31,992,4329604,8659208,9741609,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab0395c8697218,0x1ac1cab071ac1a69e51,0x1ac26ab092ac246b089,0x1ac2e672b5ac2aab09d,0x1ac326b0c2ac306b0ba,0x19cb8572da87366b0ca,0x15cbe964f95cbc972e2,0x4d902]),([8,31,992,4329604,8659208,10824010,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039270689c18,0x1ac18ab052a7946b04a,0x1ac1cab071ac1aab069,0x1ac26ab092ac2468289,0x1ac2e672b5ac2cab09d,0x1ac326b0c2ac306b0ba,0x19cb849cda87366b0ca,0x1ac3d49cf2273b49ce2,0x1024089cf9]),([8,31,992,4329604,8659208,17318416,18400817,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03936068d818,0x1ac1aab069ac18a9e51,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e672b5,0x187366b0cdac32ab0c2,0x1363c8d8e29cb84d8da,0x1274089d01363eab0f5]),([8,31,992,4329604,8659208,17318416,19483218,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039020680818,0x1ac1a6b052a7946b04a,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e69eb5,0x187366b0cdac32ab0c2,0x1023b408e29cb8408da,0x56501023e808f2]),([8,31,992,4329604,8659208,17318416,31389629,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab03936068d818,0x1ac1a6b052a7946b04a,0x19ca36b08aac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2ea82b5,0x187366b0cdac32ab0c5,0x1363b4d8e29cb84d8da,0x49d01363e8d8f2]),([8,31,992,4329604,8659208,17318416,32472030,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0eab039020680818,0x1ac1aab069ac18a9e51,0x19ca36b082ac1cab071,0x1ac26ab099ac24ab091,0x1ac30ab0bdac2eab0b5,0x187366b0cdac32ab0c5,0x1023c808e29cb8408da,0x10241a3b01023eab0f5]),([8,31,992,4329604,8659208,17318416,32505856,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136058d81436048d810,0x1360e8d839590696418,0x1361a8d86936188d851,0x136234d882361c8d871,0x136268d89936248d891,0x1362c4d8ae362a8d8a9,0x1362f8d8ba362d8d8b2,0x136328d8c636314d8c2,0x1593c964ea59384d8ce,0x1594095501273e8d8f5,0x4d905])]
def b150 : List (List Nat × List (Nat × Nat)) := [([8,31,992,4329604,8659208,17318416,32505856,32573506],hh [0x1020180804020080800,0x102038080c020280808,0x1020580814020480810,0x1020e80839270689c18,0x1021a4085202144084a,0x102234088a021c80871,0x1022680899022480891,0x1022c808b1022a808a9,0x10232808c2022f408ba,0x1273c808ed8eba89ce1,0x409052740964fa]),([8,31,992,4329604,8659208,17318416,32539681],hh [0x13601cd8053600cd801,0x13603cd80d3602cd809,0x15505d54153604cd811,0x13613cd84b360fcd83b,0x13619cd8633615cd853,0x1361dcd873361bcd86b,0x13623cd88b3621cd883,0x13627cd89b3625cd893,0x1722dd54b3392bd54ab,0x13631d54c3362fd54bb,0x13633d14cb]),([8,31,1023,1082401,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a7e069f818,0x1ac1c68269ac18ab051,0x1ac24ab091a7a26b072,0x1ac2c6b0aaac26ab099,0x1ac306b0baac2e6b0b6,0x17e366b0caac326b0c2,0x17e3a9f8e29cb85f8da,0x5f9027e406def9]),([8,31,1023,1082401,2164802,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a498692618,0x1ac1aa8269ac18ab051,0x1ac2469e89ac1cab071,0x1ac2a6b09aac266b092,0x1ac2e6b0b69cad6b0aa,0x1ac326b0c2ac306b0ba,0x19cb8526da49b66b0ca,0x13c3e514f549ba926e2,0x149c092701]),([8,31,1023,1082401,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a2f068bc18,0x1a09a6b052ac146b04a,0x1ac246b089ac1cab071,0x1ac2a6b09aac266b092,0x1ac306b0baac2e672b5,0x12f366b0caac326b0c2,0x12f3a8bce29cb84bcda,0x11c404bcfa2f3e6a4ed,0x47102]),([8,31,1023,1082401,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a5c8697218,0x1ac1cab071a79a6b051,0x1ac246b08aac226b082,0x1ac2a6b09aac266b092,0x1ac2eab0b99cad6b0aa,0x1ac32ab0c9ac30ab0c1,0x15cb8a72e15cb6972d9,0x1ac3f572fa5cba964e9,0x51502]),([8,31,1023,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a270689c18,0x1ac1aa9e69ac18a8251,0x1ac246b089ac1cab071,0x1ac2a6b09aac266b092,0x1ac306b0baac2e672b5,0x127366b0caac326b0c2,0x1273a49ce29cb849cda,0x45702273e89cf5]),([8,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856],hh [0x40088])]
def b151 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,1015808,1082401,2164802,4329604,32776456],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72397e069f818,0x19c94a72519c92a7249,0x19ca2672829c9c67269,0x19ca6672929ca46728a,0x19cb0672b99cac6729a,0x17d36a72ca9cb2672c2,0x17e3aad6e97c38ab0e1,0x11c405f8f2]),([8,31,31744,1015808,1082401,2164802,17318416,32776456],hh [0x11c01870041c0087000,0x11c038700c1c0287008,0x11c05870141c0487010,0x11c0e870392f068bc18,0x11c14870511c1287049,0x11c1c4706a1c1a45c62,0x11c26470911c2247072,0x11c2f470b51aaa4709a,0x11c32870c91c30870c1,0x115bd4bcf2b53a6aae1,0x41501]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856],hh [0x400e0]),([8,31,31744,1015808,1082401,4329604,8659944,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x15c85972145c8497210,0x15c8e972394f8693e18,0x15c94972515c9297249,0x15ca6572815c9c57269,0x15cac972b15caa9729a,0x14fb6972c25cae972b9,0x14fba93ee94fb893ee1,0x14fbe8bcf94fbc89cf1]),([8,31,31744,1015808,1083361,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x1bb85aee147e049f810,0x17e0e9f8397e069f818,0x17e149f8517e129f849,0x17ca09f8817e1c5f869,0x1bbb090aa97e249e88a,0x17e385f4da0532914c9,0x115bc5f8ea7e3a5f0e2,0x11c405f8fa7e3e5ecf6,0x52702]),([8,31,31744,1015808,1083361,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x12f0e8bc391b0686c18,0x12f148bc512f128bc49,0x12f1c4b46a2f1a4a062,0x12f2e4bcb12f204bc72,0x11b384bcca2f324bcc1,0x11b3e972f91b3c86ce9,0x1044081101]),([8,31,31744,1015808,4329604,8659208,17318416,32539681],hh [0x136018d80436008d800,0x136038d80c36028d808,0x136058d81436048d810,0x1360e8d839528694a18,0x136148d85136128d849,0x136224d882361c4d869,0x136264d89236244d88a,0x1362c8d8aa362a4d89a,0x136304d8bd362e8d8b5,0x13eb84d8ca36324d8c2,0x4d8fd52be8fee9]),([8,31,31744,1082401,2164802,4329604,9412872,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72397e069f818,0x19c9aa72699c98a7251,0x19ca4672899c9ca7271,0x19caaa729a9ca667292,0x19cb0672ba9caca72b1,0x17e36a1cd99cb2a72c2,0x1b7be5f8ea7e38ab0e1,0x18540ad701])]
def b152 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,1082401,2164802,4330468,8659208,32505856],hh [0x1b281aca04b280aca00,0x1b283aca0cb282aca08,0x1b285aca14b284aca10,0x1b28eaca394f0693c18,0x1b298a9e55b29469e3e,0x1b29c6ca6db29aa9e69,0x1b1a469e8db2a26ca72,0x1b2ac6caaa9ca6aca92,0x1b2aeacab9a7ad6cab2,0x1b2b3acac9b2b0acac1,0x14f38ab0e14f36a1cd9,0x14f40672f94f3aa9ee5,0x53d02]),([8,31,31744,1082401,2165730,4329604,17318416,32505856],hh [0x1a101a8404a100a8400,0x1a103a840ca102a8408,0x1a105a8414a104a8410,0x1a10ea8439458691618,0x1a118a8255a1146823e,0x1a11ca826da11aa8469,0x1a124a8491a12368289,0x1a12ca84b1a12aa7299,0x1a131a84baa12e682b5,0x145b6a1cd9a132a84c9,0x145baa82e545b8ab0e1,0x5170245c04dcf9]),([8,31,31744,1082401,3115074,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72397e069f818,0x19c9aa72699c98a7251,0x19ca4a72919ca267272,0x19cac400b09caaa7299,0x19cb0672ba9cae672b2,0x18736672ca9cb2672c2,0x17e3a9f8e2ac385f8da,0x5f9027e406def9]),([8,31,31744,1082401,3115074,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239498692618,0x19c9aa72699c98a7251,0x19ca4a72919ca267272,0x19caca72aa98aa67299,0x19cb0a72ba9cae672b5,0x149b6a1cd99cb2a72c9,0x1b8be526ea49b8ab0e1,0x6d901]),([8,31,31744,1082401,4329604,8659944,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6395c8697218,0x1b41a6b055b5946b03e,0x1b5a0ad672b59c6b26d,0x1b5a4ab08db5a2ad689,0x1b5acad6b1b5aaaca9a,0x1b5b06d6bab5ae6b0b5,0x1ac38572da87366d6c2,0x15cba964e9ac39572e2,0x16ec0972fa]),([8,31,31744,1082401,4329604,9412872,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72395c8697218,0x19c9ca72719c9a67251,0x19ca4a728a9ca267282,0x19caca72aa98aa6729a,0x19cb0672ba9cae672b5,0x15cb6a1cd99cb2a72c2,0x15cba964e95cb8ab0e1,0x572fa]),([8,31,31744,1083361,2164802,4329604,8659208,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6397e069f818,0x1b598ab055b5946b03e,0x1a11c6d06db59aab269,0x1b5a4aca91aca36d089,0x1b5ac6d6aab5a6ad699,0x1b5afad6b9ac2d6d6b2,0x1b5b2ad6c9b5b0ad6c1,0x17e38ab0e17e36a1cd9,0x17e406daf97e3aab0e5,0x5f902]),([8,31,31744,1083361,2164802,8659208,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1b58ead6392f068bc18,0x1b594ad651b592ab03e,0x1a11c6d06dac9a6b055,0x1b5a66d691ac236d689,0x1b5aeab0b5b5ac6d69a,0x1b5b2ad6c9b5b0ad6c1,0x12f38ab0e12f36a1cd9,0x12f3e8bcf92f3aab0e5,0x11b4086d01])]
def b153 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,2065441,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72392b868ae18,0x19c9a672529c946724a,0x19ca6672919ca267271,0x19cb0672b598aa6729a,0x18736672ca9cb2672c2,0x12bba8aee2ac384aeda,0x643012bbe8aef9]),([8,31,31744,2164802,4330468,8659208,17318416,32505856],hh [0x1b181ac604b180ac600,0x1b183ac60cb182ac608,0x1b185ac614b184ac610,0x1b18eac639270689c18,0x1b198ac655a5946963e,0x19a1ca966db19aac669,0x1b1a4ac691a5a36c689,0x1b1ae696b5b1ac6c699,0x1b1b2ac6c9b1b0ac6ba,0x12738ab0e12736a1cd9,0x16c4089cfa273a696e5]),([8,31,31744,2164802,5214340,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239268689a18,0x19c9aa72699c98a7251,0x19ca4a72919ca267272,0x19cae672b598aa67299,0x18736672ca9cb2672ba,0x126ba49ae2ac3849ada,0x49afa]),([8,31,1047552,1082401,2164802,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72397e069f818,0x19c9aa72699c98a7251,0x19ca4672899c9ca7271,0x19caaa729a9ca667292,0x19caea72b99caca72b1,0x19cb2a72c99cb0a72c1,0x17e38ab0e17e36a1cd9,0x17e409f901b7be5f8ea]),([8,31,1047552,1082401,2164802,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239498692618,0x19c9aa72699c98a7251,0x19ca4672899c9ca7271,0x198aa6729a9ca667292,0x19cae672b59caca72aa,0x19cb2672c29cb0672ba,0x1ac38526da8736672ca,0x13c3e514f549ba926e2,0x52701]),([8,31,1047552,1082401,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72392f068bc18,0x19c9a672529c946724a,0x19ca4672899c9ca7271,0x198aa6729a9ca667292,0x19cb0672ba9cae672b5,0x18736672ca9cb2672c2,0x12f3a8bce2ac384bcda,0x11c404bcfa2f3e668ed]),([8,31,1047552,1082401,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea72395c8697218,0x19c9ca72719c9a67251,0x19ca46728a9ca267282,0x198aa6729a9ca667292,0x19cae672b59caca72aa,0x19cb2672c29cb0672ba,0x1ac38572da8736672ca,0x15cbe972ea593a572e2,0x672fd]),([8,31,1047552,2164802,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x19c8ea7239270689c18,0x19c9aa72699c98a7251,0x19ca4672899c9ca7271,0x198aa6729a9ca667292,0x19cb0672ba9cae672b5,0x18736672ca9cb2672c2,0x1273a49ce2ac3849cda,0x1273ea7af5])]
def b154 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,1083361,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0fab03a7e069f818,0x1ac156b052ac146b04a,0x1ac1b6b06aac1a6b062,0x1ac236b08aac2268271,0x1ac26ab099ac24a9e91,0x1ac2d6b0b2ac2c6b0aa,0x1ac30ab0c1ac2fab0b9,0x17e36a1cd9ac32ab0c9,0x19cba6b0e57e389f8e1,0x17e409f901b7be5f8ea]),([8,31,1082401,1083361,2164802,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac12ab03a498692618,0x1ac1a6b062ac156b052,0x1ac226b072a09c6b06a,0x1ac26ab099a7a46b08a,0x19caf6b0b2ac2c6b0aa,0x1ac326b0c2ac306b0be,0x149b8526da87366b0ca,0x1453d526ea9cba526e2,0x5270249c0424f9]),([8,31,1082401,1083361,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0fab03a2f068bc18,0x1ac156b052ac146b04a,0x1a09c6b06dac1aab069,0x1ac246b08dac22ab089,0x1ac2cab0b1ac26ab099,0x1ac30672bdac2eab0b5,0x187366b0caac326b0c2,0x1ac394bce22f384bcda,0x12f3e8bcf92f3aa72e9,0x11c4087101]),([8,31,1082401,1083361,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac12ab03a5c8697218,0x1ac1aab069ac156b052,0x1ac22ab089ac20a9e71,0x1ac26ab099ac24ab091,0x19caf6b0b2ac2c6b0aa,0x1ac32ab0c9ac30ab0c1,0x15cb8972e15cb6a1cd9,0x1ac3f572fa5cbaa72e9,0x51502]),([8,31,1082401,2164802,2165730,4329604,8659208,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a085a8214a084a8210,0x1a0946824a7e069f818,0x1a09aa8269a098a8252,0x1a0a2a8289a09d68272,0x1a0a6a7299a0a4a8291,0x1a0ae682b2a0ac682aa,0x1a0b2682c6a0b0682ba,0x17e389f8da8736682ca,0x17e405cef99cbc5f8e9,0x5f902]),([8,31,1082401,2164802,2165730,4329604,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a085a8214a084a8210,0x1a093a824a498692618,0x1a098a8256a094a8251,0x1a09d68272a09c6826a,0x1a0a4a8291a0a2a8289,0x1a0ac682aa9ca668295,0x1a0af682baa0ae682b2,0x1a0b2a82c9a0b1a72c5,0x149ba526e249b6a1cd9,0x149c04f0f99cbc516ed,0x52702]),([8,31,1082401,2164802,2165730,8659208,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a085a8214a084a8210,0x1a092a823a2f068bc18,0x1a09a68262a094a8251,0x1a0a268275a09ca826a,0x1a0a668292a0a46828a,0x1a0aea82b9a0aca82b1,0x1a0b2a82c99cb1682c2,0x19f394bce22f36a1cd9,0x12f3e8bcf99cbc4bce9,0x11c4087101]),([8,31,1082401,2164802,4329604,4330468,8659208,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a785a9e14a784a9e10,0x1a79469e4abc86af218,0x1a79a69e66a798a9e52,0x1a79ca9e71a79ba9e6a,0x1a7a2a9e89a7a0a9e76,0x1a7a769e9aa7a667292,0x1a7ae69eb2a7ac69eaa,0x1a7b169ec2a7b069eba,0x1bcb6a1cd9a7b3a9ec9,0x19cbe534f5bcbc6f2e2,0x1bcc0ae901])]
def b155 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,2164802,4329604,4330468,17318416,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a785a9e14a784a9e10,0x1a79469e4a3c068f018,0x1a79aa9e69a798a9e52,0x1a7a2a9e82a79ca9e71,0x1a7a769e9a9ca4a9e91,0x1a7ae69eb2a7ac69eaa,0x19cb369ec2a7b069eba,0x10b388f0da873669ece,0x13c40672f93c3c4d8ed,0x4f102]),([8,31,1082401,2164802,4329604,8659208,8659944,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac146b04a7e069f818,0x1ac1c6b06aac1a6b052,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1a0aeab0b2ac2c6b0aa,0x1ac336b0caa7b0ab0c1,0x1b7bc5f8e27e36a1cd9,0x14fc0a73017e3e9f8f9]),([8,31,1082401,2164802,4329604,8659208,32505856,32506848],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x17e059f8149c84a7210,0x19c946724a9c86a7218,0x19c9c6726a9c9a67252,0x19ca2a72899ca0a7272,0x19ca6a72999ca4a7291,0x1b7b05f8b27e2a9f8a9,0x19cb68c8d97e329f8c9,0x19cbc672ed9cbaa72e2,0x19cc0a72fd9cbea72f2,0x5f905]),([8,31,1082401,2164802,4329604,8659208,32505856,33553439],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x17e059f814ac04ab010,0x1ac146b04aac06ab018,0x1ac1c6b06aac1a6b052,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1b7b05f8b27e2aa1ca9,0x1ac376b0da7e329f8c9,0x1a7bca82eaac396b0e2,0x1ac40ab0faac3e6b0f5,0x5f905]),([8,31,1082401,2164802,4329604,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac12ab03a0d0683418,0x1ac15ab052ac146b04e,0x1ac1c6b06aac1a6b062,0x1ac22ab082ac1d6b072,0x1ac2568292ac246b08d,0x1ac2c6b0aaac2769e9a,0x1ac2f6b0baac2e6b0b2,0x1ac33a72cdac30ab0c1,0x10d3898ce12236a1cd9,0x19cbe434f1453b594e9,0x435020d4053efa]),([8,31,1082401,2164802,4329604,17318416,32505856,32506848],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x14985926149c84a7210,0x19c946724a9c86a7218,0x19c9c6726a9c9a67252,0x19ca2a72899ca0a7272,0x19ca6a72999ca4a7291,0x1452f526b249aa926a9,0x19cb68c8d949b24f0c1,0x19cbca72ed9cbaa72e2,0x149c1673029cbfa72fd]),([8,31,1082401,2164802,4329604,17318416,32505856,33553439],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1498592614ac04ab010,0x1ac146b04aac06ab018,0x1ac1c6b06aac1a6b052,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x1452f526b249aaa1ca9,0x1ac36926ca49b24f0c1,0x1ac3b682eaac38ab0dd,0x1ac40a72feac3e69ef2,0x52705]),([8,31,1082401,2164802,4330468,8659208,17318416,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a785a9e14a784a9e10,0x1a58fa9e3a0b0682c18,0x1a59569e52a79469e4a,0x1a79b69e6aa59a69e62,0x1a7a269e82a79d67272,0x1a7a4a9e91a5a369e8a,0x1a7aba9eaaa7a7a9e99,0x1a7ada96b5a7aca9eb1,0x1a7b0a9ebea7aea9eb9,0x1a7b2a9ec9a7b1a72c5,0x169b8488da873669ece,0x19cbc5a8e9a5b942ce2,0x10b40af1010b3eae6f9,0x69f05])]
def b156 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,2164802,4330468,8659208,32505856],hh [0x1a781e9e05a780e9e01,0x1a783e9e0da782e9e09,0x14d05d3415a784e9e11,0x1a793e9e4ba78fe9e3b,0x1a799e9e63a795e9e53,0x1a79de9e73a79be9e6b,0x1a7a3e9e8ba7a1e9e83,0x1a7a7e9e9ba7a5e9e93,0x1a7add34b3a7abd34ab,0x14d31ef0c34d2fd34bb,0x1a7b3d34cb]),([8,31,1082401,2164802,8659208,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac146b03a2f068bc18,0x1ac1aab069ac18ab052,0x1ac226b082ac1cab071,0x1ac276b09aa0a4ab08a,0x1ac2eab0b9ac2cab0b1,0x19cb36b0caac30ab0c1,0x1a9394bce22f36a1cd9,0x12f3ea72f92f3c8bcf1,0x1054081501]),([8,31,1082401,2164802,8659208,17318416,32505856,32506848],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x12f058bc149c84a7210,0x19c946723a9c86a7218,0x19c9c6726a9c9a67252,0x19ca46728a9ca267272,0x12f2a6729a9ca667292,0x12f30668b52f2c8bcaa,0x19cb68c8d91c324bcc2,0x19cbca72ea9cb9672e2,0x12f41673029cbfa72f9]),([8,31,1082401,2164802,8659208,17318416,32505856,33553439],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x12f058bc14ac04ab010,0x1ac146b03aac06ab018,0x1ac1c6b06aac1a6b052,0x1ac246b08aac226b072,0x1872a6b09aac266b092,0x12f306a4b52f2c8bcaa,0x1ac36870ca1c324bcc2,0x1a0baab0e5ac38ab0dd,0x1ac40a72feac3f6b0f2,0x4bd05]),([8,31,1082401,2165730,4329604,8659208,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a085a8214a084a8210,0x1a092a823a080682018,0x1a09a68262a09568252,0x1a0a0a82769c9c6826a,0x1a0a3a828aa0a268286,0x1a0a668296a0a4a8291,0x1a0ac682aaa0a7a829a,0x1a0b0682be9caf682b2,0x1a0b3682caa0b2682c2,0x10838964e12236a1cd9,0x1083e820f9083c672e9,0x421020840682fd]),([8,31,1082401,2165730,4329604,17318416,32505856],hh [0x1a081e8205a080e8201,0x1a083e820da082e8209,0x14585d1615a084e8211,0x1a093e824ba08fe823b,0x1a099e8263a095e8253,0x1a09de8273a09be826b,0x1a0a3e828ba0a1e8283,0x1a0a7e829ba0a5e8293,0x1a0add16b3a0abd16ab,0x145b1cdcc345afd16bb,0x1a0b3d16cb]),([8,31,1082401,4329604,4330468,8659208,17318416,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a785a9e14a784a9e10,0x1a79469e4a5c8697218,0x1a79ca9e6aa798a9e52,0x1a7a2a9e89a7a0a9e75,0x1a7a6a9e99a7a4a9e91,0x1a7ae69eb2a7ac69eaa,0x1a7b2a9ec99cb169eba,0x15cb8964e15cb6a1cd9,0x1a7bf572fa9cbc572e9,0x4d902]),([8,31,1082401,4329604,8659208,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac14ab0515c8697218,0x1ac1aab069ac19ab062,0x1ac1dab072ac1c6b06e,0x1ac2669e92ac22ab082,0x1ac2c6b0aaac276b09a,0x1ac306b0baac2e6b0b2,0x18736672cdac316b0c2,0x15cbc572e25938572da,0x15cbea72f9ac3d572f2,0x51502])]
def b157 : List (List Nat × List (Nat × Nat)) := [([8,31,1082401,4329604,8659208,17318416,32505856,32506848],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x15c85972149c84a7210,0x19c94a72519c86a7218,0x19c9c6726a9c9a67262,0x19ca2a72899ca0a7272,0x19ca6a72999ca4a7291,0x15cac964b15caa972a9,0x19cb68c8d99cb1572c2,0x19cbd672f29cbaa72e2,0x15cc1673029cbfa72fd]),([8,31,1082401,4329604,8659208,17318416,32505856,33553439],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x15c8597214ac04ab010,0x1ac14ab051ac06ab018,0x1ac1c6b06aac1a6b062,0x1ac22ab089ac20ab072,0x1ac26ab099ac24ab091,0x15cac964b15caaa1ca9,0x1ac36914caac31572c2,0x1ac3ca9eeaac38ab0dd,0x15cc16b1029cbfab0f5]),([8,31,1082401,4329604,8659944,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x15c85d7215ac04eb011,0x1ac13eb04bac0feb03b,0x1ac19eb063ac15eb053,0x1ac1deb073ac1beb06b,0x1ac23eb08bac21eb083,0x1ac27eb09bac25eb093,0x1ac2dd72b3ac2bd72ab,0x1ac31d72c35cafd72bb,0x1ac33daacb]),([8,31,1083361,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac12ab03a090682418,0x1ac19ab062ac15a8251,0x1ac1c6b06eac1aa9e69,0x1ac226b082ac1dab072,0x1ac266b092ac246b08e,0x1ac2bab0aaac276b09a,0x1ac2e6b0b69cad6b0b2,0x1ac30ab0c1ac2fab0ba,0x1ac32ab0c9ac31ab0c5,0x19cb8488da87366b0ce,0x12f3d6daf1093a53ee2,0x10940aef01093eae4f9,0x6b105]),([8,31,1083361,2164802,4329604,8659208,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x17e05df815ac04eb011,0x1ac13eb04bac0feb03b,0x1ac19eb063ac15eb053,0x1ac1deb073ac1beb06b,0x1ac23eb08bac21eb083,0x1ac27eb09bac25eb093,0x1ac2ddf8b3ac2bdf8ab,0x17e31eeec37e2fdf8bb,0x1ac33df8cb]),([8,31,1083361,2164802,8659208,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x12f05cbc15ac04eb011,0x1ac13eb04bac0feb03b,0x1ac19eb063ac15eb053,0x1ac1deb073ac1beb06b,0x1ac23eb08bac21eb083,0x1ac27eb09bac25eb093,0x1ac2dcbcb3ac2bcbcab,0x1ac31cbcc32f2fcbcbb,0x1ac33c6ccb]),([8,31,2164802,2165730,4329604,8659208,17318416,32505856],hh [0x1a081a8204a080a8200,0x1a083a820ca082a8208,0x1a085a8214a084a8210,0x1a092a823a270689c18,0x1a09a68262a09568252,0x1a0a2682729c9c6826a,0x1a0a6a8299a0a46828a,0x19caf682baa0aca82b1,0x1a0b2a82c9a0b0a82c1,0x19cba49ce12736a1cd9,0x45702273e89cf5]),([8,31,2164802,4329604,4330468,8659208,17318416,32505856],hh [0x1a781a9e04a780a9e00,0x1a783a9e0ca782a9e08,0x1a785a9e14a784a9e10,0x1a593a9e4a270689c18,0x1a798a9656a794a9e51,0x1a79d69e72a59c6726a,0x1a7a4a9e91a7a2a9e89,0x1a7aca9eb1a7a669695,0x1a7b0a96bda7aea9eb9,0x1873669ecaa7b2672c5,0x1273b49ce9273849cda,0x45702273ea72f1])]
def b158 : List (List Nat × List (Nat × Nat)) := [([8,31,2164802,4329604,8659208,8659944,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac146b04a270689c18,0x1ac1aab069ac18ab052,0x1a0a2ab082ac1cab071,0x1ac276b09aa7a4ab091,0x1ac2eab0b9ac2cab0b1,0x19cb36b0caac30ab0c1,0x1273b49ce12736a1cd9,0x1273ea72f9273c89cf1,0x40902]),([8,31,2164802,4329604,8659208,17318416,32505856,32506848],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x1270589c149c84a7210,0x19c946724a9c86a7218,0x19c9c6726a9c9a67252,0x19ca46728a9ca267272,0x1272a6729a9ca667292,0x12730a7abd272c49caa,0x19cbaa72e29cb68c8d9,0x19cc0a72fe9cbca72ed,0x49d05]),([8,31,2164802,4329604,8659208,17318416,32505856,33553439],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1270589c14ac04ab010,0x1ac146b04aac06ab018,0x1ac1c6b06aac1a6b052,0x1ac246b08aac226b072,0x1872a6b09aac266b092,0x1273089cbd272c49caa,0x1a0b8ab0ddac36856ca,0x1ac3f6b0f2ac3b69eea,0x49d05ac40a72fe]),([8,31,2164802,4330468,8659208,17318416,32505856],hh [0x1a581e9605a580e9601,0x1a583e960da582e9609,0x12705c9c15a584e9611,0x1a593e964ba58fe963b,0x1a599e9663a595e9653,0x1a59de9673a59be966b,0x1a5a3e968ba5a1e9683,0x1a5a7e969ba5a5e9693,0x1272dc9cb3a5abc9cab,0x1a5b1c9cc3272fc9cbb,0x1a5b3c56cb]),([8,992,1023,1082401,2164802,4329604,8659208,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a7e069f818,0x1ac20ab072ac1c6b04a,0x1ac26ab099ac24ab091,0x1ac2eab0b9ac2dab0ae,0x1ac32ab0c9ac30ab0c1,0x17e38a1ce17e369f8d9,0x17e409f901b7be5f8ea]),([8,992,1023,1082401,2164802,4329604,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a498692618,0x1ac1cab071ac1aab062,0x1ac26ab099ac24ab091,0x1ac2e6b0b6ac2bab0a9,0x1ac326b0c2ac306b0ba,0x18738526da49b66b0ca,0x13c3e514f549ba926e2,0x149c092701]),([8,992,1023,1082401,2164802,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a2f068bc18,0x1ac1cab071ac14ab04a,0x1ac26ab099ac24ab091,0x1ac2eab0b9ac2aab0a9,0x1ac32ab0c9ac30ab0c1,0x12f38a1ce12f368bcd9,0x12f3e8bcf9a93b4bcea,0x11c4087101]),([8,992,1023,1082401,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a5c8697218,0x1ac22ab082ac1cab071,0x1ac26ab099ac24ab091,0x1ac306b0baac2e6b0a9,0x15cb66b0caac326b0c2,0x1593a572e28738572da,0x14540ab0fd5cbe972ea])]
def b159 : List (List Nat × List (Nat × Nat)) := [([8,992,1023,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x1ac0f6b03a270689c18,0x1ac1cab071ac1aab062,0x1ac26ab099ac24ab091,0x1ac2eab0b9ac2aab0a9,0x1ac32ab0c9ac30ab0c1,0x12738a1ce1273689cd9,0x115c089cfa273d49ce9]),([8,992,31744,1015808,1082401,2164802,4329631,8659208,17318416,32505856],hh [0x40118003800088]),([8,992,31744,1015808,1082401,2164802,8659208,32641156],hh [0x17d819f6047d809f600,0x17d839f60c7d829f608,0x17d859f6147d849f610,0x17d8e9f6399506a5418,0x17d949f6517d929f649,0x17da65f69279a29f662,0x17dae9eeb27b2b9f69a,0x17db29f6c97db09f6c1,0x52701053ea50da]),([8,992,31744,1015808,1082401,2164802,17318416,32641156],hh [0x1498192604498092600,0x149839260c498292608,0x1498592614498492610,0x1498e926393c068f018,0x1499492651499292649,0x149a65269249a291682,0x149ac926ae49aa5269a,0x149b2526c249b0526ba,0x17e40514fd053e926ca]),([8,992,31744,1015808,1082401,2164831,4329604,8659208],hh [0x17c819f2047c809f200,0x17c839f20c7c829f208,0x1130584c147c849f210,0x17c8e9f2397c869f218,0x17c949f2517c929f249,0x17c9c5f2697c989f261,0x1133044aaa7ca49e48a,0x17ab7880d9453244cc2,0x17cba9f2e97ab89f2e1,0x11c405f2fa7cbc856f1,0x52702]),([8,992,31744,1015808,1082401,2164831,4329604,17318416],hh [0x1490192404490092400,0x149039240c490292408,0x1110584414490492410,0x1490e92439490692418,0x1491492451491292449,0x1452092471491a52461,0x11130844c149249248a,0x14938924e14937914c9,0x1493c89cf1493a924e9,0x5f9022f40524fa]),([8,992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856],hh [0x40118003800088]),([8,992,31744,1015808,2164802,4329631,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14270489c10,0x1270e89c39158685618,0x1271489c51271289c49,0x1272689c92272289c82,0x1273049cb9272c49ca9,0x115ba456e115b689cc2,0x122408890115bc972f1])]
def b160 : List (List Nat × List (Nat × Nat)) := [([8,992,31744,1015808,4329604,8659208,17318416,32573506],hh [0x1010180404010080400,0x101038040c010280408,0x1010580414010480410,0x1010e80439238688e18,0x1011480451011280449,0x1012640472011a80462,0x10130404aa012a4049a,0x123bc804ca0132404c2,0x404f5]),([8,992,1047552,1082401,2164802,4329604,8659208,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c397e069f818,0x1871ca1c71871aa1c4a,0x1872661c92872461c82,0x1872e61cb2872ba1c9a,0x1873261cc2873061cba,0x1ac385f8da9cb661cca,0x1bcbeadef97e3c9f8e2,0x5f901]),([8,992,1047552,1082401,2164802,4329604,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c39498692618,0x1871ca1c71871aa1c62,0x18726a1c998724a1c91,0x1872e61cb2872ba1ca9,0x1873261cc2873061cba,0x1ac38526da9cb661cca,0x13c3e616f549bc926e2,0x149c04f0fa]),([8,992,1047552,1082401,2164802,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c392f068bc18,0x1871ca1c718714a1c4a,0x18726a1c998724a1c91,0x1872ea1cb9872aa1ca9,0x18732a1cc98730a1cc1,0x12f38ab0e12f36a72d9,0x11c404bcf92f3c89ced]),([8,992,1047552,1082401,4329604,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c395c8697218,0x18722a1c82871ca1c71,0x18726a1c998724a1c91,0x1872ea1cb9872ca1ca9,0x18732a1cc98730a1cc1,0x15cb8ab0e15cb6a72d9,0x620fd5cbc964e9]),([8,992,1047552,2164802,4329604,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c39270689c18,0x1871ca1c71871aa1c62,0x18726a1c998724a1c91,0x1872ea1cb9872aa1ca9,0x18732a1cc98730a1cc1,0x12738ab0e12736a72d9,0x1873d49cf2273a89ce9]),([8,992,1082401,2164802,4329604,8659208,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x10d05834140d0483410,0x10d0e824398706a1c18,0x10b18434520d1442049,0x10d1c4346a0d1a43462,0x10d22434860d2043472,0x10d26434920d244348a,0x10d2e834aa0d2a4349a,0x105b6434c90d30834c1,0x10d4161d02873e61cda]),([8,992,1082401,2164802,4329604,8659208,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16f859be146f849be10,0x16f8e8cc39ac06ab018,0x143985be526f945bc49,0x16f9c5be6a6f9a5be62,0x16fa25be866fa05be72,0x16fa65be926fa45be8a,0x16fac9beaa6faa5be9a,0x1ac369beca6fb25bec1,0x1ac409befd70bb5bedd,0x5bf05])]
def b161 : List (List Nat × List (Nat × Nat)) := [([8,992,1082401,2164802,4329604,17318416,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x10d05834140d0483410,0x10812424398706a1c18,0x10b18434520d144344a,0x10d1c834710d1a83469,0x10d22834890d2181685,0x10d26834990d2483491,0x10d2f434ba0d2a834a9,0x105b6434c90d30834c1,0x18740a1cf920bb61cda,0x43505]),([8,992,1082401,2164802,4329604,17318416,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16f859be146f849be10,0x16f124cc39ac06ab018,0x143985be526f945be4a,0x16f9c9be716f9a9be69,0x16fa29be896fa18c885,0x16fa69be996fa49be91,0x16faf5beb26faa9bea9,0x1ac369beca6fb25bec1,0x1ac409befd703b5bedd,0x5bf05]),([8,992,1082401,2164802,8659208,17318416,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x10d05834140d0483410,0x10d0e824398706a1c18,0x10d18434520d1442049,0x10d1c834710d1a83469,0x10d228348905a143482,0x10d26834990d2483491,0x10d2e834b50d2a834a9,0x18736816d90d32434c1,0x435058740836e5]),([8,992,1082401,2164802,8659208,17318416,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16f859be146f849be10,0x16f8e8cc39ac06ab018,0x16f985be526f945bc49,0x16f9c9be716f9a9be69,0x16fa29be8932215be82,0x16fa69be996fa49be91,0x16fad5beb26faa9bea9,0x16fb29bec96fb09bec1,0x1ac409d8e56fb76b0da,0x5bf05]),([8,992,1082401,4329604,8659208,17318416,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x10d05834140d0483410,0x10b12424398706a1c18,0x10d18834610d1483451,0x10d1c834710d1a83469,0x10d244348a0d2241685,0x10d2a4349a0d2643492,0x10d31434ba0d2c434aa,0x18740834f58736816d9,0x43505]),([8,992,1082401,4329604,8659208,17318416,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16f859be146f849be10,0x143924cc39ac06ab018,0x16f989be616f949be51,0x16f9c9be716f9a9be69,0x16fa45be8a6fa24c885,0x16faa5be9a6fa65be92,0x16fb09beb26fac5beaa,0x16fb76b0da6fb29bec5,0x16fc16b1026fbf5bef5]),([8,992,2164802,4329604,8659208,17318416,32505856,32505887],hh [0x10d01834040d0083400,0x10d038340c0d0283408,0x10d05834140d0483410,0x10b12420398706a1c18,0x10d18434520d144344a,0x10d1c834710d1a83469,0x10d228348905a143482,0x10d26834990d2483491,0x10d2c834b10d2a834a9,0x18736816d90d2f434ba,0x435058740834ed]),([8,992,2164802,4329604,8659208,17318416,32505856,33554400],hh [0x16f819be046f809be00,0x16f839be0c6f829be08,0x16f859be146f849be10,0x143925bc39ac06ab018,0x16f985be526f945be4a,0x16f9c9be716f9a9be69,0x16fa29be8932215be82,0x16fa69be996fa49be91,0x16faf5beb16faa9bea9,0x16fb76b0da6fb29bec2,0x5bf05ac409beed])]
def b162 : List (List Nat × List (Nat × Nat)) := [([8,31744,1015808,1082401,2164802,4329604,17318431,32505856],hh [0x19781a5e049780a5e00,0x19783a5e0c9782a5e08,0x19785a5e149784a5e10,0x1978ea5e39058681618,0x19798a5e61979465e49,0x1979ca5e71979aa5e69,0x197a4a5e9197a265e81,0x197ab65eaa97a6a5e99,0x1ac3665ac197ad65eb2,0x105ba816e2b5b8416da,0x61d0105be416f5]),([8,31744,1015808,1082401,2164802,8659208,17318896,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c392a068a818,0x1871ca1c718714a1c4a,0x18726a1c998724a1c91,0x1b5b84a8daac3661cb9,0x12a3e4a8f2233b4a8e2,0x66101]),([8,31744,1015808,1082401,4329604,8659208,17318431,32505856],hh [0x19681a5a049680a5a00,0x19683a5a0c9682a5a08,0x19685a5a149684a5a10,0x1968ea5a39058681618,0x1969a65a61969465a49,0x196a0a5a81969ca5a71,0x196a4a5a9196a2a5a89,0x196ab65aaa96a6a5a99,0x1ac3665ac996ad65ab2,0x105ba416e2b5b8416da,0x65afd05be816ea]),([8,31744,1015808,2164802,4329604,8659208,17318896,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1870ea1c39230688c18,0x1871ca1c71871aa1c62,0x18726a1c998724a1c91,0x1b5b848cdaac3661cc1,0x1233c88cea233a48ce2,0x61cf5]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208],hh [0x17e019f8047e009f800,0x17e039f80c7e029f808,0x17e059f8147e049f810,0x17e079f81cbc86af218,0x17e129f8497e0e9f839,0x17e189f8617e149f851,0x17e1c9f8717e1a9f869,0x17e265f8917e229f889,0x17e309e8ba7caa9f8a9,0x1bc38af2d97e329f8c9,0x1054091501bcbeaf2f9,0x100481ed1e7e465f512,0x17e4a9f9297c489f921,0x17e4e9f9397e4c85731,0x149d087141]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],hh [0x401600048000b8]),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416],hh [0x1498192604498092600,0x149839260c498292608,0x1498592614498492610,0x149879261c3c068f018,0x1499292649498e92639,0x1499892661499492651,0x1499c92671499a92669,0x149aa5269949a452689,0x149b0926ba45ac924aa,0x1853e4f0d949b2926c9,0x149c4815024540614fa,0x149c89272100481271e,0x149cc89d3149ca92729,0x17e508bd4149ce97339]),([9,31,992,31744,1015808,1082401,2164802,8659208,17318416],hh [0x12f018bc042f008bc00,0x12f038bc0c2f028bc08,0x12f058bc142f048bc10,0x11c078701c2f068bc18,0x12f128bc492f0e8bc39,0x12f188bc612f148bc51,0x12f1c8bc712f1a8bc69,0x100240bc8a2f224a082,0x12f268bc992d248bc91,0x12f384bcca2f324bca9,0x12f3e8bcf92f3c4bce9,0x11c484711a2f408bd01,0x15cce47132274c47129,0x4154205504713a])]
def b163 : List (List Nat × List (Nat × Nat)) := [([9,31,992,31744,1015808,1082401,4329604,8659208,17318416],hh [0x15c81972045c8097200,0x15c839720c5c8297208,0x15c85972145c8497210,0x145079141c5c8697218,0x15c92972495c8e97239,0x15c98972615c9497251,0x15c9c972715c9a97269,0x15caa572995ca457289,0x15cb8572da5cb2972c9,0x15cba972e9003a172e2,0x15cbe972f95cbc972f1,0x10048115125cc097301,0x1454a91529454891521,0x17e4e8bd39454c89d31,0x1455091541]),([9,31,992,31744,1015808,2164802,4329604,8659208,17318416],hh [0x1270189c04270089c00,0x1270389c0c270289c08,0x1270589c14270489c10,0x115878561c270689c18,0x1271289c49270e89c39,0x1271889c61271489c51,0x1271c89c71271a89c69,0x1272c89caa272a49c81,0x1273289cc9273089cba,0x1273e49cf1273a49ce1,0x115c689d02274049cfa,0x115cc9733115ca45721,0x102508094115ce8bd39]),([9,31,992,31744,1082401,2164802,4329604,8659208,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x17e079f81cb586ad618,0x1b592ad649b58ead639,0x1ac15ad652b5946b04e,0x1ac1d6d671b59aad669,0x1b5a4ab291a1226d682,0x1b2ac6d69ab5a66d095,0x1b5b06b2bdb42e6d6b2,0x1b5b6ad6cab5b26d6c2,0x1b5baad6e9b5b9ad6e1,0x1b5be6d6f2b5bc6b0ed,0x187446d702b5c06d6fa,0x1ac485f91a9cc65f912,0x1b7ce5f92aac495f922,0x17e509f941]),([9,31,992,31744,1082401,2164802,4329604,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x149879261cb586ad618,0x1b592ad649b58ead639,0x1ac15ad652b5946b04e,0x1b5a0ab075b59c6d669,0x1b5a4ab291b5a2a8489,0x1b2ac6d69ab5a66d095,0x1b5b0ad6c1acaf6d0b9,0x19cb96d6dab5b2ad6c9,0x1ac3b6d6eab5ba6d6e6,0x1b5bead6f9b5bcad6f1,0x149c4a1d11b5c0ad701,0x149c8ab12149c6a7319,0x13c4e5153549caab125,0x149d092741]),([9,31,992,31744,1082401,2164802,8659208,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x12f078bc1cb586ad618,0x1b592ad649b58ead639,0x1ac15ad652b5946b04e,0x1b59c6d66ab59a6d662,0x1aca468489ac1d6d672,0x1b5ac6d69ab5a66d095,0x1b5b0ad6c1ac2f6d6b9,0x19cb96d6e2b5b2ad6c9,0x1b5bcad6f1ac3b6d6e9,0x1b5c0ad701b5bead6f9,0x12f46a73192f44a1d11,0x12f4aab1252f48ab121,0x11c504bd3a2f4e6d32d,0x47142]),([9,31,992,31744,1082401,4329604,8659208,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x15c879721cb586ad618,0x1b592ad649b58ead639,0x1ac15ad652b5946b04e,0x1b2a26b075b59c6d669,0x1b5a6ad699aca56d091,0x1b5ae6d6b2b5ac6d6aa,0x1b5b0ad6c1ac2f6d6ba,0x19cb96d6dab5b2ad6c9,0x1b5bc6b0edb5baad6e9,0x1b5c06d6fab5be6d6f2,0x19cc65731287446d702,0x1ac4957322ac485731a,0x1b5cf5733a5cca96529,0x51542]),([9,31,992,31744,2164802,4329604,8659208,17318416,32505856],hh [0x1b581ad604b580ad600,0x1b583ad60cb582ad608,0x1b585ad614b584ad610,0x1270789c1cb586ad618,0x1b592ad649b58ead639,0x1ac15ad652b5946b04e,0x1b5a0ad075ac9c68469,0x1b5a4ad091b5a2aca89,0x1b5ac6d69ab5a66b295,0x1b5b0ad6c1ac2f6d6b9,0x19cb96d6e2b5b2ad6c9,0x1b5bcad6f1ac3b6d6e9,0x1b5c0ad701b5bead6f9,0x12746a73192744a1d11,0x1274a6b1252748ab121,0x45742274e89d35]),([9,31,992,1082401,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01ab004ac00ab000,0x1ac03ab00cac02ab008,0x1ac05ab014ac04ab010,0x10d078341cac06ab018,0x1ac13ab04aac0eab039,0x1ac18ab056ac14ab051,0x1ac1bab06aa09a6b066,0x1ac1dab075ac1cab071,0x1ac22a9e89ac21ab082,0x1ac256b092ac246b08e,0x1ac276b09aac266b096,0x1ac2c6b0aeac2aab09e,0x1ac2eab0b9ac2dab0b2,0x1ac30ab0c1ac2fab0bd,0x1ac32ab0c9ac31ab0c5,0x1ac37ab0daac33ab0cd,0x1ac3a6b0e69cb96b0e2,0x1ac3c6b0eeac3b6b0ea,0x1ac3e6b0f6ac3d6b0f2,0x1ac406b0feac3f6b0fa,0x187446b106ac416b102,0x10d4853f1a9cc648912,0x1454b43529ac4943522,0x10d4e835392f4d43531,0x1ac51435420d506b13d])]
def b164 : List (List Nat × List (Nat × Nat)) := [([9,31,992,1082401,2164802,4329604,8659208,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x1ac05eb015ac04eb011,0x1ac0feb03b7e06df819,0x1ac15eb053ac13eb04b,0x1ac1beb06bac19eb063,0x1ac21eb083ac1deb073,0x1ac25eb093ac23eb08b,0x1ac2beb0abac27eb09b,0x1ac2feb0bbac2deb0b3,0x1ac33eb0cbac31eb0c3,0x1ac39df8e3ac37df8db,0x17e3ddf8f3ac3bdf8eb,0x1ac41df9037e3fef2fb]),([9,31,992,1082401,2164802,4329604,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x1ac05eb015ac04eb011,0x1ac0feb03b4986d2619,0x1ac15eb053ac13eb04b,0x1ac1beb06bac19eb063,0x1ac21eb083ac1deb073,0x1ac25eb093ac23eb08b,0x1ac2beb0abac27eb09b,0x1ac2feb0bbac2deb0b3,0x1ac33eb0cbac31eb0c3,0x1ac39d26e3ac37d26db,0x149bdd26f3ac3bd26eb,0x1ac41d270349bfcf0fb]),([9,31,992,1082401,2164802,8659208,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x1ac05eb015ac04eb011,0x1ac0feb03b2f06cbc19,0x1ac15eb053ac13eb04b,0x1ac1beb06bac19eb063,0x1ac21eb083ac1deb073,0x1ac25eb093ac23eb08b,0x1ac2beb0abac27eb09b,0x1ac2feb0bbac2deb0b3,0x1ac33eb0cbac31eb0c3,0x1ac39cbce3ac37cbcdb,0x12f3dcbcf3ac3bcbceb,0x1ac41c7103ac3fcbcfb]),([9,31,992,1082401,4329604,8659208,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x1ac05eb015ac04eb011,0x1ac0feb03b5c86d7219,0x1ac15eb053ac13eb04b,0x1ac1beb06bac19eb063,0x1ac21eb083ac1deb073,0x1ac25eb093ac23eb08b,0x1ac2beb0abac27eb09b,0x1ac2feb0bbac2deb0b3,0x1ac33eb0cbac31eb0c3,0x1ac39d72e3ac37d72db,0x15cbdd72f3ac3bd72eb,0x1ac41d1503ac3fd72fb]),([9,31,992,2164802,4329604,8659208,17318416,32505856],hh [0x1ac01eb005ac00eb001,0x1ac03eb00dac02eb009,0x1ac05eb015ac04eb011,0x1ac0feb03b2706c9c19,0x1ac15eb053ac13eb04b,0x1ac1beb06bac19eb063,0x1ac21eb083ac1deb073,0x1ac25eb093ac23eb08b,0x1ac2beb0abac27eb09b,0x1ac2feb0bbac2deb0b3,0x1ac33eb0cbac31eb0c3,0x1ac39c9ce3ac37c9cdb,0x1273dc9cf3273bc9ceb,0x1ac41c5703ac3fc9cfb]),([9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x17e079f81c9c86a7218,0x19c92a72499c8ea7239,0x19c9c672699c94a7251,0x19ca2a7289002227282,0x19ca6a72999ca4a7291,0x19cb0a72c19cae672b1,0x10038272da9cb2a72c9,0x19cbaa72e99cb8a72e1,0x19cbea72f99cbca72f1,0x17e44a1d119cc0a7301,0x17e48ad7217e46ab119,0x17e509f941b7ce5f92a]),([9,31,31744,1015808,1082401,2164802,4329604,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x149879261c9c86a7218,0x19c92a72499c8ea7239,0x19c9c672699c94a7251,0x19ca2a7289002227282,0x19ca6a72999ca4a7291,0x19cb0a72c19cae672b1,0x19cb6a62d99cb2a72c9,0x19cbb672ea9cb9672e2,0x19cbea72f99cbca72f1,0x149c4a1d119cc0a7301,0x149c8ad72149c6ab119,0x149d04f139454d5272a]),([9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x12f078bc1c9c86a7218,0x19c92a72499c8ea7239,0x1001a272629c94a7251,0x19c9ca72719c9aa7269,0x19ca6a72999ca467289,0x19cb0a72c19cae672b1,0x19cb9662d99cb2a72c9,0x19cbe672f29cbc672ed,0x18744673029cc0672fa,0x1b5c84bd1aac464bd12,0x12f4e6692d2f4a8bd22,0x11c504bd3a])]
def b165 : List (List Nat × List (Nat × Nat)) := [([9,31,31744,1015808,1082401,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x15c879721c9c86a7218,0x19c92a72499c8ea7239,0x19c9c672699c94a7251,0x19ca6a72999ca467289,0x19caca72b1002c272aa,0x19cb0a72c19caea72b9,0x19cb6a62d99cb2a72c9,0x19cbb672ea9cb9672e2,0x19cbea72f99cbca72f1,0x15cc4a1d119cc0a7301,0x15cc8ad7215cc6ab119,0x19ccf5733a5cca96529]),([9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856],hh [0x19c81a72049c80a7200,0x19c83a720c9c82a7208,0x19c85a72149c84a7210,0x1270789c1c9c86a7218,0x19c92a72499c8ea7239,0x19c9c672699c94a7251,0x19ca2a7289002227282,0x19ca6a72999ca4a7291,0x19cb0a72c19cae672b1,0x19cb9662d99cb2a72c9,0x19cbe672f29cbc672ed,0x18744673029cc0672fa,0x1b5c849d1aac4649d12,0x1274ea7b35274a49d22]),([9,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x17e079f81c8706a1c18,0x18712a1c49870ea1c39,0x18722a1c628714a1c51,0x1872aa1c9a872661c92,0x18732a1cc98730a1cc1,0x1873c61cea8738a1cde,0x1874061cfa873e61cf2,0x1ac465f9129cc461d02,0x17e4c9f922b5c85f91a,0x5f941bcceadf39]),([9,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x149879261c8706a1c18,0x18712a1c49870ea1c39,0x18722a1c828714a1c51,0x1873061c9a872661c92,0x1873661cca873261cc2,0x1873c61cea8738a1cde,0x1874061cfa873e61cf2,0x1ac46527129cc461d02,0x149cc92722b5c85271a,0x149d04f13a3c4e61735]),([9,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x12f078bc1c8706a1c18,0x18712a1c49870ea1c39,0x1871aa1c628714a1c51,0x1873061c9a872661c72,0x1873661cca873261cc2,0x1873e61cf2873c61cda,0x19cc461d02874061cfa,0x1b5c84bd1aac464bd12,0x12f4e4bd32274b4bd22,0x47141]),([9,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x15c879721c8706a1c18,0x18712a1c49870ea1c39,0x18726a1c998714a1c51,0x1873061cba872ca1caa,0x1873661cca873261cc2,0x1873ca1cf1873aa1ce2,0x18740a1d01873ea1cf9,0x15cc6ab1195cc4a7311,0x15ccc965295cc8ad721,0x6213d]),([9,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],hh [0x18701a1c048700a1c00,0x18703a1c0c8702a1c08,0x18705a1c148704a1c10,0x1270789c1c8706a1c18,0x18712a1c49870ea1c39,0x18722a1c828714a1c51,0x1873061c9a872661c92,0x1873661cca873261cc2,0x1873e61cf2873c61cda,0x19cc461d02874061cfa,0x1b5c849d1aac4649d12,0x1274c89d2a274a49d22,0x61d35])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k165 : b165.all (fun a => P_ a.1 a.2) = true := by decide +kernel
end PEqualNP.Outside.L_meta_19634_aux

theorem PEqualNP.Outside.L_meta_19634 : True := True.intro
