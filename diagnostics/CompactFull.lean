import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19528_aux

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
def urootHint (ws : List Nat) : Nat := (([] : List (List Nat × Nat)).lookup (isort ws)).getD 0


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




def quadPi (i : Nat) : List Nat :=
  let z := i-1
  [z/32768,(z/1024)%32,(z/32)%32,z%32]
def xPass (S : BT) (M Y t : Nat) (ws : List Nat) (i : Nat) : Bool :=
  if i = 0 then true else
  if actL (quadPi i) M = 15 ∧ actL (quadPi i) Y = 5 then
    !(S.mem (t :: isort (ws.map (actL (quadPi i)))))
  else true
theorem xPass_sound {M Y t ws} (S : BT)
    (hs : ∀ t es, NatRun 15 5 t es → S.mem (t :: isort es) = false)
    (h : NatRun M Y t ws) (i : Nat) : xPass S M Y t ws i = true := by
  unfold xPass
  split
  · rfl
  · split
    · rename_i hc
      have hi : ∀ a, actL (quadPi i) (a ^^^ M) = actL (quadPi i) a ^^^ 15 := by
        intro a
        rw [actL_xor, hc.1]
      have hx := Run.map (actL (quadPi i)) (inv' := (· ^^^ 15))
        (meet' := (· &&& ·)) (join' := (· ||| ·)) hi (actL_and (quadPi i)) (actL_or (quadPi i)) h
      rw [hc.2] at hx
      simp [hs _ _ hx]
    · rfl
def xGood (S : BT) (M Y t : Nat) (ws : List Nat) (hin : List (Nat × Nat)) : Bool :=
  if t ≤ ws.length+1 then hin.all (fun x => x.1 != 1025 || xPass S M Y t ws x.2) else true
theorem xGood_sound {M Y t ws} (S : BT)
    (hs : ∀ t es, NatRun 15 5 t es → S.mem (t :: isort es) = false)
    (h : NatRun M Y t ws) (hin : List (Nat × Nat)) : xGood S M Y t ws hin = true := by
  unfold xGood
  split
  · apply List.all_eq_true.mpr
    intro x _
    simp [xPass_sound S hs h]
  · rfl
def spd : List (Nat × Nat) := [(1,7),(3,1)]
def spm : List (Nat × Nat) := [(1,5),(3,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sT : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [2,3,6] .lf) [2,3,9] .lf) [2,6,12] (.nd .lf [2,9,12] .lf)) [3,0,3,6] (.nd (.nd .lf [3,0,3,9] .lf) [3,0,6,12] (.nd .lf [3,0,9,12] .lf))) [3,3,3,6] (.nd (.nd (.nd (.nd .lf [3,3,3,9] .lf) [3,3,6] .lf) [3,3,6,6] (.nd .lf [3,3,6,15] .lf)) [3,3,9] (.nd (.nd .lf [3,3,9,9] .lf) [3,3,9,15] (.nd .lf [3,6,6,12] .lf)))) [3,6,12] (.nd (.nd (.nd (.nd (.nd .lf [3,6,12,12] .lf) [3,6,12,15] .lf) [3,9,9,12] (.nd .lf [3,9,12] .lf)) [3,9,12,12] (.nd (.nd .lf [3,9,12,15] .lf) [4,0,0,3,6] (.nd .lf [4,0,0,3,9] .lf))) [4,0,0,6,12] (.nd (.nd (.nd .lf [4,0,0,9,12] .lf) [4,0,3,3,6] (.nd .lf [4,0,3,3,9] .lf)) [4,0,3,6] (.nd (.nd .lf [4,0,3,6,6] .lf) [4,0,3,6,15] (.nd .lf [4,0,3,9] .lf))))) [4,0,3,9,9] (.nd (.nd (.nd (.nd (.nd (.nd .lf [4,0,3,9,15] .lf) [4,0,6,6,12] .lf) [4,0,6,12] (.nd .lf [4,0,6,12,12] .lf)) [4,0,6,12,15] (.nd (.nd .lf [4,0,9,9,12] .lf) [4,0,9,12] (.nd .lf [4,0,9,12,12] .lf))) [4,0,9,12,15] (.nd (.nd (.nd .lf [4,3,3,6,15] .lf) [4,3,3,9,15] (.nd .lf [4,3,6,6,15] .lf)) [4,3,6,15] (.nd (.nd .lf [4,3,6,15,15] .lf) [4,3,9,9,15] (.nd .lf [4,3,9,15] .lf)))) [4,3,9,15,15] (.nd (.nd (.nd (.nd (.nd .lf [4,6,6,12,15] .lf) [4,6,12,12,15] .lf) [4,6,12,15] (.nd .lf [4,6,12,15,15] .lf)) [4,9,9,12,15] (.nd (.nd .lf [4,9,12,12,15] .lf) [4,9,12,15] (.nd .lf [4,9,12,15,15] .lf))) [5,0,0,0,3,6] (.nd (.nd (.nd .lf [5,0,0,0,3,9] .lf) [5,0,0,0,6,12] (.nd .lf [5,0,0,0,9,12] .lf)) [5,0,0,3,3,6] (.nd (.nd .lf [5,0,0,3,3,9] .lf) [5,0,0,3,6] (.nd .lf [5,0,0,3,6,6] .lf)))))) [5,0,0,3,6,15] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,0,0,3,9] .lf) [5,0,0,3,9,9] .lf) [5,0,0,3,9,15] (.nd .lf [5,0,0,6,6,12] .lf)) [5,0,0,6,12] (.nd (.nd .lf [5,0,0,6,12,12] .lf) [5,0,0,6,12,15] (.nd .lf [5,0,0,9,9,12] .lf))) [5,0,0,9,12] (.nd (.nd (.nd (.nd .lf [5,0,0,9,12,12] .lf) [5,0,0,9,12,15] .lf) [5,0,3,3,6,15] (.nd .lf [5,0,3,3,9,15] .lf)) [5,0,3,6,6,15] (.nd (.nd .lf [5,0,3,6,15] .lf) [5,0,3,6,15,15] (.nd .lf [5,0,3,9,9,15] .lf)))) [5,0,3,9,15] (.nd (.nd (.nd (.nd (.nd .lf [5,0,3,9,15,15] .lf) [5,0,6,6,12,15] .lf) [5,0,6,12,12,15] (.nd .lf [5,0,6,12,15] .lf)) [5,0,6,12,15,15] (.nd (.nd .lf [5,0,9,9,12,15] .lf) [5,0,9,12,12,15] (.nd .lf [5,0,9,12,15] .lf))) [5,0,9,12,15,15] (.nd (.nd (.nd .lf [5,3,3,6,15,15] .lf) [5,3,3,9,15,15] (.nd .lf [5,3,6,6,15,15] .lf)) [5,3,6,15,15] (.nd (.nd .lf [5,3,6,15,15,15] .lf) [5,3,9,9,15,15] (.nd .lf [5,3,9,15,15] .lf))))) [5,3,9,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,6,6,12,15,15] .lf) [5,6,12,12,15,15] .lf) [5,6,12,15,15] (.nd .lf [5,6,12,15,15,15] .lf)) [5,9,9,12,15,15] (.nd (.nd .lf [5,9,12,12,15,15] .lf) [5,9,12,15,15] (.nd .lf [5,9,12,15,15,15] .lf))) [6,0,0,0,0,3,6] (.nd (.nd (.nd .lf [6,0,0,0,0,3,9] .lf) [6,0,0,0,0,6,12] (.nd .lf [6,0,0,0,0,9,12] .lf)) [6,0,0,0,3,3,6] (.nd (.nd .lf [6,0,0,0,3,3,9] .lf) [6,0,0,0,3,6] (.nd .lf [6,0,0,0,3,6,6] .lf)))) [6,0,0,0,3,6,15] (.nd (.nd (.nd (.nd (.nd .lf [6,0,0,0,3,9] .lf) [6,0,0,0,3,9,9] .lf) [6,0,0,0,3,9,15] (.nd .lf [6,0,0,0,6,6,12] .lf)) [6,0,0,0,6,12] (.nd (.nd .lf [6,0,0,0,6,12,12] .lf) [6,0,0,0,6,12,15] (.nd .lf [6,0,0,0,9,9,12] .lf))) [6,0,0,0,9,12] (.nd (.nd (.nd .lf [6,0,0,0,9,12,12] .lf) [6,0,0,0,9,12,15] (.nd .lf [6,0,0,3,3,6,15] .lf)) [6,0,0,3,3,9,15] (.nd (.nd .lf [6,0,0,3,6,6,15] .lf) [6,0,0,3,6,15] (.nd .lf [6,0,0,3,6,15,15] .lf))))))) [6,0,0,3,9,9,15] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,0,0,3,9,15] .lf) [6,0,0,3,9,15,15] .lf) [6,0,0,6,6,12,15] (.nd .lf [6,0,0,6,12,12,15] .lf)) [6,0,0,6,12,15] (.nd (.nd .lf [6,0,0,6,12,15,15] .lf) [6,0,0,9,9,12,15] (.nd .lf [6,0,0,9,12,12,15] .lf))) [6,0,0,9,12,15] (.nd (.nd (.nd (.nd .lf [6,0,0,9,12,15,15] .lf) [6,0,3,3,6,15,15] .lf) [6,0,3,3,9,15,15] (.nd .lf [6,0,3,6,6,15,15] .lf)) [6,0,3,6,15,15] (.nd (.nd .lf [6,0,3,6,15,15,15] .lf) [6,0,3,9,9,15,15] (.nd .lf [6,0,3,9,15,15] .lf)))) [6,0,3,9,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [6,0,6,6,12,15,15] .lf) [6,0,6,12,12,15,15] .lf) [6,0,6,12,15,15] (.nd .lf [6,0,6,12,15,15,15] .lf)) [6,0,9,9,12,15,15] (.nd (.nd .lf [6,0,9,12,12,15,15] .lf) [6,0,9,12,15,15] (.nd .lf [6,0,9,12,15,15,15] .lf))) [6,3,3,6,15,15,15] (.nd (.nd (.nd .lf [6,3,3,9,15,15,15] .lf) [6,3,6,6,15,15,15] (.nd .lf [6,3,6,15,15,15] .lf)) [6,3,6,15,15,15,15] (.nd (.nd .lf [6,3,9,9,15,15,15] .lf) [6,3,9,15,15,15] (.nd .lf [6,3,9,15,15,15,15] .lf))))) [6,6,6,12,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,6,12,12,15,15,15] .lf) [6,6,12,15,15,15] .lf) [6,6,12,15,15,15,15] (.nd .lf [6,9,9,12,15,15,15] .lf)) [6,9,12,12,15,15,15] (.nd (.nd .lf [6,9,12,15,15,15] .lf) [6,9,12,15,15,15,15] (.nd .lf [7,0,0,0,0,0,3,6] .lf))) [7,0,0,0,0,0,3,9] (.nd (.nd (.nd .lf [7,0,0,0,0,0,6,12] .lf) [7,0,0,0,0,0,9,12] (.nd .lf [7,0,0,0,0,3,3,6] .lf)) [7,0,0,0,0,3,3,9] (.nd (.nd .lf [7,0,0,0,0,3,6] .lf) [7,0,0,0,0,3,6,6] (.nd .lf [7,0,0,0,0,3,6,15] .lf)))) [7,0,0,0,0,3,9] (.nd (.nd (.nd (.nd (.nd .lf [7,0,0,0,0,3,9,9] .lf) [7,0,0,0,0,3,9,15] .lf) [7,0,0,0,0,6,6,12] (.nd .lf [7,0,0,0,0,6,12] .lf)) [7,0,0,0,0,6,12,12] (.nd (.nd .lf [7,0,0,0,0,6,12,15] .lf) [7,0,0,0,0,9,9,12] (.nd .lf [7,0,0,0,0,9,12] .lf))) [7,0,0,0,0,9,12,12] (.nd (.nd (.nd .lf [7,0,0,0,0,9,12,15] .lf) [7,0,0,0,3,3,6,15] (.nd .lf [7,0,0,0,3,3,9,15] .lf)) [7,0,0,0,3,6,6,15] (.nd (.nd .lf [7,0,0,0,3,6,15] .lf) [7,0,0,0,3,6,15,15] (.nd .lf [7,0,0,0,3,9,9,15] .lf)))))) [7,0,0,0,3,9,15] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,0,0,0,3,9,15,15] .lf) [7,0,0,0,6,6,12,15] .lf) [7,0,0,0,6,12,12,15] (.nd .lf [7,0,0,0,6,12,15] .lf)) [7,0,0,0,6,12,15,15] (.nd (.nd .lf [7,0,0,0,9,9,12,15] .lf) [7,0,0,0,9,12,12,15] (.nd .lf [7,0,0,0,9,12,15] .lf))) [7,0,0,0,9,12,15,15] (.nd (.nd (.nd .lf [7,0,0,3,3,6,15,15] .lf) [7,0,0,3,3,9,15,15] (.nd .lf [7,0,0,3,6,6,15,15] .lf)) [7,0,0,3,6,15,15] (.nd (.nd .lf [7,0,0,3,6,15,15,15] .lf) [7,0,0,3,9,9,15,15] (.nd .lf [7,0,0,3,9,15,15] .lf)))) [7,0,0,3,9,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [7,0,0,6,6,12,15,15] .lf) [7,0,0,6,12,12,15,15] .lf) [7,0,0,6,12,15,15] (.nd .lf [7,0,0,6,12,15,15,15] .lf)) [7,0,0,9,9,12,15,15] (.nd (.nd .lf [7,0,0,9,12,12,15,15] .lf) [7,0,0,9,12,15,15] (.nd .lf [7,0,0,9,12,15,15,15] .lf))) [7,0,3,3,6,15,15,15] (.nd (.nd (.nd .lf [7,0,3,3,9,15,15,15] .lf) [7,0,3,6,6,15,15,15] (.nd .lf [7,0,3,6,15,15,15] .lf)) [7,0,3,6,15,15,15,15] (.nd (.nd .lf [7,0,3,9,9,15,15,15] .lf) [7,0,3,9,15,15,15] (.nd .lf [7,0,3,9,15,15,15,15] .lf))))) [7,0,6,6,12,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,0,6,12,12,15,15,15] .lf) [7,0,6,12,15,15,15] .lf) [7,0,6,12,15,15,15,15] (.nd .lf [7,0,9,9,12,15,15,15] .lf)) [7,0,9,12,12,15,15,15] (.nd (.nd .lf [7,0,9,12,15,15,15] .lf) [7,0,9,12,15,15,15,15] (.nd .lf [7,3,3,6,15,15,15,15] .lf))) [7,3,3,9,15,15,15,15] (.nd (.nd (.nd .lf [7,3,6,6,15,15,15,15] .lf) [7,3,6,15,15,15,15] (.nd .lf [7,3,6,15,15,15,15,15] .lf)) [7,3,9,9,15,15,15,15] (.nd (.nd .lf [7,3,9,15,15,15,15] .lf) [7,3,9,15,15,15,15,15] (.nd .lf [7,6,6,12,15,15,15,15] .lf)))) [7,6,12,12,15,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [7,6,12,15,15,15,15] .lf) [7,6,12,15,15,15,15,15] .lf) [7,9,9,12,15,15,15,15] (.nd .lf [7,9,12,12,15,15,15,15] .lf)) [7,9,12,15,15,15,15] (.nd (.nd .lf [7,9,12,15,15,15,15,15] .lf) [8,0,0,0,0,0,0,3,6] (.nd .lf [8,0,0,0,0,0,0,3,9] .lf))) [8,0,0,0,0,0,0,6,12] (.nd (.nd (.nd .lf [8,0,0,0,0,0,0,9,12] .lf) [8,0,0,0,0,0,3,3,6] (.nd .lf [8,0,0,0,0,0,3,3,9] .lf)) [8,0,0,0,0,0,3,6] (.nd (.nd .lf [8,0,0,0,0,0,3,6,6] .lf) [8,0,0,0,0,0,3,6,15] (.nd .lf [8,0,0,0,0,0,3,9] .lf)))))))) [8,0,0,0,0,0,3,9,9] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,0,0,0,0,0,3,9,15] .lf) [8,0,0,0,0,0,6,6,12] .lf) [8,0,0,0,0,0,6,12] (.nd .lf [8,0,0,0,0,0,6,12,12] .lf)) [8,0,0,0,0,0,6,12,15] (.nd (.nd .lf [8,0,0,0,0,0,9,9,12] .lf) [8,0,0,0,0,0,9,12] (.nd .lf [8,0,0,0,0,0,9,12,12] .lf))) [8,0,0,0,0,0,9,12,15] (.nd (.nd (.nd (.nd .lf [8,0,0,0,0,3,3,6,15] .lf) [8,0,0,0,0,3,3,9,15] .lf) [8,0,0,0,0,3,6,6,15] (.nd .lf [8,0,0,0,0,3,6,15] .lf)) [8,0,0,0,0,3,6,15,15] (.nd (.nd .lf [8,0,0,0,0,3,9,9,15] .lf) [8,0,0,0,0,3,9,15] (.nd .lf [8,0,0,0,0,3,9,15,15] .lf)))) [8,0,0,0,0,6,6,12,15] (.nd (.nd (.nd (.nd (.nd .lf [8,0,0,0,0,6,12,12,15] .lf) [8,0,0,0,0,6,12,15] .lf) [8,0,0,0,0,6,12,15,15] (.nd .lf [8,0,0,0,0,9,9,12,15] .lf)) [8,0,0,0,0,9,12,12,15] (.nd (.nd .lf [8,0,0,0,0,9,12,15] .lf) [8,0,0,0,0,9,12,15,15] (.nd .lf [8,0,0,0,3,3,6,15,15] .lf))) [8,0,0,0,3,3,9,15,15] (.nd (.nd (.nd .lf [8,0,0,0,3,6,6,15,15] .lf) [8,0,0,0,3,6,15,15] (.nd .lf [8,0,0,0,3,6,15,15,15] .lf)) [8,0,0,0,3,9,9,15,15] (.nd (.nd .lf [8,0,0,0,3,9,15,15] .lf) [8,0,0,0,3,9,15,15,15] (.nd .lf [8,0,0,0,6,6,12,15,15] .lf))))) [8,0,0,0,6,12,12,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,0,0,0,6,12,15,15] .lf) [8,0,0,0,6,12,15,15,15] .lf) [8,0,0,0,9,9,12,15,15] (.nd .lf [8,0,0,0,9,12,12,15,15] .lf)) [8,0,0,0,9,12,15,15] (.nd (.nd .lf [8,0,0,0,9,12,15,15,15] .lf) [8,0,0,3,3,6,15,15,15] (.nd .lf [8,0,0,3,3,9,15,15,15] .lf))) [8,0,0,3,6,6,15,15,15] (.nd (.nd (.nd .lf [8,0,0,3,6,15,15,15] .lf) [8,0,0,3,6,15,15,15,15] (.nd .lf [8,0,0,3,9,9,15,15,15] .lf)) [8,0,0,3,9,15,15,15] (.nd (.nd .lf [8,0,0,3,9,15,15,15,15] .lf) [8,0,0,6,6,12,15,15,15] (.nd .lf [8,0,0,6,12,12,15,15,15] .lf)))) [8,0,0,6,12,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [8,0,0,6,12,15,15,15,15] .lf) [8,0,0,9,9,12,15,15,15] .lf) [8,0,0,9,12,12,15,15,15] (.nd .lf [8,0,0,9,12,15,15,15] .lf)) [8,0,0,9,12,15,15,15,15] (.nd (.nd .lf [8,0,3,3,6,15,15,15,15] .lf) [8,0,3,3,9,15,15,15,15] (.nd .lf [8,0,3,6,6,15,15,15,15] .lf))) [8,0,3,6,15,15,15,15] (.nd (.nd (.nd .lf [8,0,3,6,15,15,15,15,15] .lf) [8,0,3,9,9,15,15,15,15] (.nd .lf [8,0,3,9,15,15,15,15] .lf)) [8,0,3,9,15,15,15,15,15] (.nd (.nd .lf [8,0,6,6,12,15,15,15,15] .lf) [8,0,6,12,12,15,15,15,15] (.nd .lf [8,0,6,12,15,15,15,15] .lf)))))) [8,0,6,12,15,15,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [8,0,9,9,12,15,15,15,15] .lf) [8,0,9,12,12,15,15,15,15] .lf) [8,0,9,12,15,15,15,15] (.nd .lf [8,0,9,12,15,15,15,15,15] .lf)) [8,3,3,6,15,15,15,15,15] (.nd (.nd .lf [8,3,3,9,15,15,15,15,15] .lf) [8,3,6,6,15,15,15,15,15] (.nd .lf [8,3,6,15,15,15,15,15] .lf))) [8,3,6,15,15,15,15,15,15] (.nd (.nd (.nd .lf [8,3,9,9,15,15,15,15,15] .lf) [8,3,9,15,15,15,15,15] (.nd .lf [8,3,9,15,15,15,15,15,15] .lf)) [8,6,6,12,15,15,15,15,15] (.nd (.nd .lf [8,6,12,12,15,15,15,15,15] .lf) [8,6,12,15,15,15,15,15] (.nd .lf [8,6,12,15,15,15,15,15,15] .lf)))) [8,9,9,12,15,15,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [8,9,12,12,15,15,15,15,15] .lf) [8,9,12,15,15,15,15,15] .lf) [8,9,12,15,15,15,15,15,15] (.nd .lf [9,0,0,0,0,0,0,0,3,6] .lf)) [9,0,0,0,0,0,0,0,3,9] (.nd (.nd .lf [9,0,0,0,0,0,0,0,6,12] .lf) [9,0,0,0,0,0,0,0,9,12] (.nd .lf [9,0,0,0,0,0,0,3,3,6] .lf))) [9,0,0,0,0,0,0,3,3,9] (.nd (.nd (.nd .lf [9,0,0,0,0,0,0,3,6] .lf) [9,0,0,0,0,0,0,3,6,6] (.nd .lf [9,0,0,0,0,0,0,3,6,15] .lf)) [9,0,0,0,0,0,0,3,9] (.nd (.nd .lf [9,0,0,0,0,0,0,3,9,9] .lf) [9,0,0,0,0,0,0,3,9,15] (.nd .lf [9,0,0,0,0,0,0,6,6,12] .lf))))) [9,0,0,0,0,0,0,6,12] (.nd (.nd (.nd (.nd (.nd (.nd .lf [9,0,0,0,0,0,0,6,12,12] .lf) [9,0,0,0,0,0,0,6,12,15] .lf) [9,0,0,0,0,0,0,9,9,12] (.nd .lf [9,0,0,0,0,0,0,9,12] .lf)) [9,0,0,0,0,0,0,9,12,12] (.nd (.nd .lf [9,0,0,0,0,0,0,9,12,15] .lf) [9,0,0,0,0,0,3,3,6,15] (.nd .lf [9,0,0,0,0,0,3,3,9,15] .lf))) [9,0,0,0,0,0,3,6,6,15] (.nd (.nd (.nd .lf [9,0,0,0,0,0,3,6,15] .lf) [9,0,0,0,0,0,3,6,15,15] (.nd .lf [9,0,0,0,0,0,3,9,9,15] .lf)) [9,0,0,0,0,0,3,9,15] (.nd (.nd .lf [9,0,0,0,0,0,3,9,15,15] .lf) [9,0,0,0,0,0,6,6,12,15] (.nd .lf [9,0,0,0,0,0,6,12,12,15] .lf)))) [9,0,0,0,0,0,6,12,15] (.nd (.nd (.nd (.nd (.nd .lf [9,0,0,0,0,0,6,12,15,15] .lf) [9,0,0,0,0,0,9,9,12,15] .lf) [9,0,0,0,0,0,9,12,12,15] (.nd .lf [9,0,0,0,0,0,9,12,15] .lf)) [9,0,0,0,0,0,9,12,15,15] (.nd (.nd .lf [9,0,0,0,0,3,3,6,15,15] .lf) [9,0,0,0,0,3,3,9,15,15] (.nd .lf [9,0,0,0,0,3,6,6,15,15] .lf))) [9,0,0,0,0,3,6,15,15] (.nd (.nd (.nd .lf [9,0,0,0,0,3,6,15,15,15] .lf) [9,0,0,0,0,3,9,9,15,15] (.nd .lf [9,0,0,0,0,3,9,15,15] .lf)) [9,0,0,0,0,3,9,15,15,15] (.nd (.nd .lf [9,0,0,0,0,6,6,12,15,15] .lf) [9,0,0,0,0,6,12,12,15,15] (.nd .lf [9,0,0,0,0,6,12,15,15] .lf))))))) [9,0,0,0,0,6,12,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [9,0,0,0,0,9,9,12,15,15] .lf) [9,0,0,0,0,9,12,12,15,15] .lf) [9,0,0,0,0,9,12,15,15] (.nd .lf [9,0,0,0,0,9,12,15,15,15] .lf)) [9,0,0,0,3,3,6,15,15,15] (.nd (.nd .lf [9,0,0,0,3,3,9,15,15,15] .lf) [9,0,0,0,3,6,6,15,15,15] (.nd .lf [9,0,0,0,3,6,15,15,15] .lf))) [9,0,0,0,3,6,15,15,15,15] (.nd (.nd (.nd (.nd .lf [9,0,0,0,3,9,9,15,15,15] .lf) [9,0,0,0,3,9,15,15,15] .lf) [9,0,0,0,3,9,15,15,15,15] (.nd .lf [9,0,0,0,6,6,12,15,15,15] .lf)) [9,0,0,0,6,12,12,15,15,15] (.nd (.nd .lf [9,0,0,0,6,12,15,15,15] .lf) [9,0,0,0,6,12,15,15,15,15] (.nd .lf [9,0,0,0,9,9,12,15,15,15] .lf)))) [9,0,0,0,9,12,12,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [9,0,0,0,9,12,15,15,15] .lf) [9,0,0,0,9,12,15,15,15,15] .lf) [9,0,0,3,3,6,15,15,15,15] (.nd .lf [9,0,0,3,3,9,15,15,15,15] .lf)) [9,0,0,3,6,6,15,15,15,15] (.nd (.nd .lf [9,0,0,3,6,15,15,15,15] .lf) [9,0,0,3,6,15,15,15,15,15] (.nd .lf [9,0,0,3,9,9,15,15,15,15] .lf))) [9,0,0,3,9,15,15,15,15] (.nd (.nd (.nd .lf [9,0,0,3,9,15,15,15,15,15] .lf) [9,0,0,6,6,12,15,15,15,15] (.nd .lf [9,0,0,6,12,12,15,15,15,15] .lf)) [9,0,0,6,12,15,15,15,15] (.nd (.nd .lf [9,0,0,6,12,15,15,15,15,15] .lf) [9,0,0,9,9,12,15,15,15,15] (.nd .lf [9,0,0,9,12,12,15,15,15,15] .lf))))) [9,0,0,9,12,15,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [9,0,0,9,12,15,15,15,15,15] .lf) [9,0,3,3,6,15,15,15,15,15] .lf) [9,0,3,3,9,15,15,15,15,15] (.nd .lf [9,0,3,6,6,15,15,15,15,15] .lf)) [9,0,3,6,15,15,15,15,15] (.nd (.nd .lf [9,0,3,6,15,15,15,15,15,15] .lf) [9,0,3,9,9,15,15,15,15,15] (.nd .lf [9,0,3,9,15,15,15,15,15] .lf))) [9,0,3,9,15,15,15,15,15,15] (.nd (.nd (.nd .lf [9,0,6,6,12,15,15,15,15,15] .lf) [9,0,6,12,12,15,15,15,15,15] (.nd .lf [9,0,6,12,15,15,15,15,15] .lf)) [9,0,6,12,15,15,15,15,15,15] (.nd (.nd .lf [9,0,9,9,12,15,15,15,15,15] .lf) [9,0,9,12,12,15,15,15,15,15] (.nd .lf [9,0,9,12,15,15,15,15,15] .lf)))) [9,0,9,12,15,15,15,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [9,3,3,6,15,15,15,15,15,15] .lf) [9,3,3,9,15,15,15,15,15,15] .lf) [9,3,6,6,15,15,15,15,15,15] (.nd .lf [9,3,6,15,15,15,15,15,15] .lf)) [9,3,6,15,15,15,15,15,15,15] (.nd (.nd .lf [9,3,9,9,15,15,15,15,15,15] .lf) [9,3,9,15,15,15,15,15,15] (.nd .lf [9,3,9,15,15,15,15,15,15,15] .lf))) [9,6,6,12,15,15,15,15,15,15] (.nd (.nd (.nd .lf [9,6,12,12,15,15,15,15,15,15] .lf) [9,6,12,15,15,15,15,15,15] (.nd .lf [9,6,12,15,15,15,15,15,15,15] .lf)) [9,9,9,12,15,15,15,15,15,15] (.nd (.nd .lf [9,9,12,12,15,15,15,15,15,15] .lf) [9,9,12,15,15,15,15,15,15] (.nd .lf [9,9,12,15,15,15,15,15,15,15] .lf)))))) [10,0,0,0,0,0,0,0,0,3,6] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [10,0,0,0,0,0,0,0,0,3,9] .lf) [10,0,0,0,0,0,0,0,0,6,12] .lf) [10,0,0,0,0,0,0,0,0,9,12] (.nd .lf [10,0,0,0,0,0,0,0,3,6] .lf)) [10,0,0,0,0,0,0,0,3,6,15] (.nd (.nd .lf [10,0,0,0,0,0,0,0,3,9] .lf) [10,0,0,0,0,0,0,0,3,9,15] (.nd .lf [10,0,0,0,0,0,0,0,6,12] .lf))) [10,0,0,0,0,0,0,0,6,12,15] (.nd (.nd (.nd .lf [10,0,0,0,0,0,0,0,9,12] .lf) [10,0,0,0,0,0,0,0,9,12,15] (.nd .lf [10,0,0,0,0,0,0,3,6,15] .lf)) [10,0,0,0,0,0,0,3,6,15,15] (.nd (.nd .lf [10,0,0,0,0,0,0,3,9,15] .lf) [10,0,0,0,0,0,0,3,9,15,15] (.nd .lf [10,0,0,0,0,0,0,6,12,15] .lf)))) [10,0,0,0,0,0,0,6,12,15,15] (.nd (.nd (.nd (.nd (.nd .lf [10,0,0,0,0,0,0,9,12,15] .lf) [10,0,0,0,0,0,0,9,12,15,15] .lf) [10,0,0,0,0,0,3,6,15,15] (.nd .lf [10,0,0,0,0,0,3,6,15,15,15] .lf)) [10,0,0,0,0,0,3,9,15,15] (.nd (.nd .lf [10,0,0,0,0,0,3,9,15,15,15] .lf) [10,0,0,0,0,0,6,12,15,15] (.nd .lf [10,0,0,0,0,0,6,12,15,15,15] .lf))) [10,0,0,0,0,0,9,12,15,15] (.nd (.nd (.nd .lf [10,0,0,0,0,0,9,12,15,15,15] .lf) [10,0,0,0,0,3,6,15,15,15] (.nd .lf [10,0,0,0,0,3,6,15,15,15,15] .lf)) [10,0,0,0,0,3,9,15,15,15] (.nd (.nd .lf [10,0,0,0,0,3,9,15,15,15,15] .lf) [10,0,0,0,0,6,12,15,15,15] (.nd .lf [10,0,0,0,0,6,12,15,15,15,15] .lf))))) [10,0,0,0,0,9,12,15,15,15] (.nd (.nd (.nd (.nd (.nd (.nd .lf [10,0,0,0,0,9,12,15,15,15,15] .lf) [10,0,0,0,3,6,15,15,15,15] .lf) [10,0,0,0,3,6,15,15,15,15,15] (.nd .lf [10,0,0,0,3,9,15,15,15,15] .lf)) [10,0,0,0,3,9,15,15,15,15,15] (.nd (.nd .lf [10,0,0,0,6,12,15,15,15,15] .lf) [10,0,0,0,6,12,15,15,15,15,15] (.nd .lf [10,0,0,0,9,12,15,15,15,15] .lf))) [10,0,0,0,9,12,15,15,15,15,15] (.nd (.nd (.nd .lf [10,0,0,3,6,15,15,15,15,15] .lf) [10,0,0,3,6,15,15,15,15,15,15] (.nd .lf [10,0,0,3,9,15,15,15,15,15] .lf)) [10,0,0,3,9,15,15,15,15,15,15] (.nd (.nd .lf [10,0,0,6,12,15,15,15,15,15] .lf) [10,0,0,6,12,15,15,15,15,15,15] (.nd .lf [10,0,0,9,12,15,15,15,15,15] .lf)))) [10,0,0,9,12,15,15,15,15,15,15] (.nd (.nd (.nd (.nd (.nd .lf [10,0,3,6,15,15,15,15,15,15] .lf) [10,0,3,6,15,15,15,15,15,15,15] .lf) [10,0,3,9,15,15,15,15,15,15] (.nd .lf [10,0,3,9,15,15,15,15,15,15,15] .lf)) [10,0,6,12,15,15,15,15,15,15] (.nd (.nd .lf [10,0,6,12,15,15,15,15,15,15,15] .lf) [10,0,9,12,15,15,15,15,15,15] (.nd .lf [10,0,9,12,15,15,15,15,15,15,15] .lf))) [10,3,6,15,15,15,15,15,15,15] (.nd (.nd (.nd .lf [10,3,6,15,15,15,15,15,15,15,15] .lf) [10,3,9,15,15,15,15,15,15,15] (.nd .lf [10,3,9,15,15,15,15,15,15,15,15] .lf)) [10,6,12,15,15,15,15,15,15,15] (.nd (.nd .lf [10,6,12,15,15,15,15,15,15,15,15] .lf) [10,9,12,15,15,15,15,15,15,15] (.nd .lf [10,9,12,15,15,15,15,15,15,15,15] .lf)))))))))
def sP := stepOK 15 5 spd spm [] sT
def sb0 : List (List Nat × List (Nat × Nat)) := [([2,3,6],[]),([2,3,9],[]),([2,6,12],[]),([2,9,12],[]),([3,0,3,6],[]),([3,0,3,9],[]),([3,0,6,12],[]),([3,0,9,12],[]),([3,3,3,6],[]),([3,3,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc0 : sb0.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb1 : List (List Nat × List (Nat × Nat)) := [([3,3,6],[]),([3,3,6,6],[]),([3,3,6,15],[]),([3,3,9],[]),([3,3,9,9],[]),([3,3,9,15],[]),([3,6,6,12],[]),([3,6,12],[]),([3,6,12,12],[]),([3,6,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc1 : sb1.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb2 : List (List Nat × List (Nat × Nat)) := [([3,9,9,12],[]),([3,9,12],[]),([3,9,12,12],[]),([3,9,12,15],[]),([4,0,0,3,6],[]),([4,0,0,3,9],[]),([4,0,0,6,12],[]),([4,0,0,9,12],[]),([4,0,3,3,6],[]),([4,0,3,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc2 : sb2.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb3 : List (List Nat × List (Nat × Nat)) := [([4,0,3,6],[]),([4,0,3,6,6],[]),([4,0,3,6,15],[]),([4,0,3,9],[]),([4,0,3,9,9],[]),([4,0,3,9,15],[]),([4,0,6,6,12],[]),([4,0,6,12],[]),([4,0,6,12,12],[]),([4,0,6,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc3 : sb3.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb4 : List (List Nat × List (Nat × Nat)) := [([4,0,9,9,12],[]),([4,0,9,12],[]),([4,0,9,12,12],[]),([4,0,9,12,15],[]),([4,3,3,6,15],[]),([4,3,3,9,15],[]),([4,3,6,6,15],[]),([4,3,6,15],[]),([4,3,6,15,15],[]),([4,3,9,9,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc4 : sb4.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb5 : List (List Nat × List (Nat × Nat)) := [([4,3,9,15],[]),([4,3,9,15,15],[]),([4,6,6,12,15],[]),([4,6,12,12,15],[]),([4,6,12,15],[]),([4,6,12,15,15],[]),([4,9,9,12,15],[]),([4,9,12,12,15],[]),([4,9,12,15],[]),([4,9,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc5 : sb5.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb6 : List (List Nat × List (Nat × Nat)) := [([5,0,0,0,3,6],[]),([5,0,0,0,3,9],[]),([5,0,0,0,6,12],[]),([5,0,0,0,9,12],[]),([5,0,0,3,3,6],[]),([5,0,0,3,3,9],[]),([5,0,0,3,6],[]),([5,0,0,3,6,6],[]),([5,0,0,3,6,15],[]),([5,0,0,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc6 : sb6.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb7 : List (List Nat × List (Nat × Nat)) := [([5,0,0,3,9,9],[]),([5,0,0,3,9,15],[]),([5,0,0,6,6,12],[]),([5,0,0,6,12],[]),([5,0,0,6,12,12],[]),([5,0,0,6,12,15],[]),([5,0,0,9,9,12],[]),([5,0,0,9,12],[]),([5,0,0,9,12,12],[]),([5,0,0,9,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc7 : sb7.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb8 : List (List Nat × List (Nat × Nat)) := [([5,0,3,3,6,15],[]),([5,0,3,3,9,15],[]),([5,0,3,6,6,15],[]),([5,0,3,6,15],[]),([5,0,3,6,15,15],[]),([5,0,3,9,9,15],[]),([5,0,3,9,15],[]),([5,0,3,9,15,15],[]),([5,0,6,6,12,15],[]),([5,0,6,12,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc8 : sb8.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb9 : List (List Nat × List (Nat × Nat)) := [([5,0,6,12,15],[]),([5,0,6,12,15,15],[]),([5,0,9,9,12,15],[]),([5,0,9,12,12,15],[]),([5,0,9,12,15],[]),([5,0,9,12,15,15],[]),([5,3,3,6,15,15],[]),([5,3,3,9,15,15],[]),([5,3,6,6,15,15],[]),([5,3,6,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc9 : sb9.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb10 : List (List Nat × List (Nat × Nat)) := [([5,3,6,15,15,15],[]),([5,3,9,9,15,15],[]),([5,3,9,15,15],[]),([5,3,9,15,15,15],[]),([5,6,6,12,15,15],[]),([5,6,12,12,15,15],[]),([5,6,12,15,15],[]),([5,6,12,15,15,15],[]),([5,9,9,12,15,15],[]),([5,9,12,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc10 : sb10.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb11 : List (List Nat × List (Nat × Nat)) := [([5,9,12,15,15],[]),([5,9,12,15,15,15],[]),([6,0,0,0,0,3,6],[]),([6,0,0,0,0,3,9],[]),([6,0,0,0,0,6,12],[]),([6,0,0,0,0,9,12],[]),([6,0,0,0,3,3,6],[]),([6,0,0,0,3,3,9],[]),([6,0,0,0,3,6],[]),([6,0,0,0,3,6,6],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc11 : sb11.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb12 : List (List Nat × List (Nat × Nat)) := [([6,0,0,0,3,6,15],[]),([6,0,0,0,3,9],[]),([6,0,0,0,3,9,9],[]),([6,0,0,0,3,9,15],[]),([6,0,0,0,6,6,12],[]),([6,0,0,0,6,12],[]),([6,0,0,0,6,12,12],[]),([6,0,0,0,6,12,15],[]),([6,0,0,0,9,9,12],[]),([6,0,0,0,9,12],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc12 : sb12.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb13 : List (List Nat × List (Nat × Nat)) := [([6,0,0,0,9,12,12],[]),([6,0,0,0,9,12,15],[]),([6,0,0,3,3,6,15],[]),([6,0,0,3,3,9,15],[]),([6,0,0,3,6,6,15],[]),([6,0,0,3,6,15],[]),([6,0,0,3,6,15,15],[]),([6,0,0,3,9,9,15],[]),([6,0,0,3,9,15],[]),([6,0,0,3,9,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc13 : sb13.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb14 : List (List Nat × List (Nat × Nat)) := [([6,0,0,6,6,12,15],[]),([6,0,0,6,12,12,15],[]),([6,0,0,6,12,15],[]),([6,0,0,6,12,15,15],[]),([6,0,0,9,9,12,15],[]),([6,0,0,9,12,12,15],[]),([6,0,0,9,12,15],[]),([6,0,0,9,12,15,15],[]),([6,0,3,3,6,15,15],[]),([6,0,3,3,9,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc14 : sb14.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb15 : List (List Nat × List (Nat × Nat)) := [([6,0,3,6,6,15,15],[]),([6,0,3,6,15,15],[]),([6,0,3,6,15,15,15],[]),([6,0,3,9,9,15,15],[]),([6,0,3,9,15,15],[]),([6,0,3,9,15,15,15],[]),([6,0,6,6,12,15,15],[]),([6,0,6,12,12,15,15],[]),([6,0,6,12,15,15],[]),([6,0,6,12,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc15 : sb15.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb16 : List (List Nat × List (Nat × Nat)) := [([6,0,9,9,12,15,15],[]),([6,0,9,12,12,15,15],[]),([6,0,9,12,15,15],[]),([6,0,9,12,15,15,15],[]),([6,3,3,6,15,15,15],[]),([6,3,3,9,15,15,15],[]),([6,3,6,6,15,15,15],[]),([6,3,6,15,15,15],[]),([6,3,6,15,15,15,15],[]),([6,3,9,9,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc16 : sb16.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb17 : List (List Nat × List (Nat × Nat)) := [([6,3,9,15,15,15],[]),([6,3,9,15,15,15,15],[]),([6,6,6,12,15,15,15],[]),([6,6,12,12,15,15,15],[]),([6,6,12,15,15,15],[]),([6,6,12,15,15,15,15],[]),([6,9,9,12,15,15,15],[]),([6,9,12,12,15,15,15],[]),([6,9,12,15,15,15],[]),([6,9,12,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc17 : sb17.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb18 : List (List Nat × List (Nat × Nat)) := [([7,0,0,0,0,0,3,6],[]),([7,0,0,0,0,0,3,9],[]),([7,0,0,0,0,0,6,12],[]),([7,0,0,0,0,0,9,12],[]),([7,0,0,0,0,3,3,6],[]),([7,0,0,0,0,3,3,9],[]),([7,0,0,0,0,3,6],[]),([7,0,0,0,0,3,6,6],[]),([7,0,0,0,0,3,6,15],[]),([7,0,0,0,0,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc18 : sb18.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb19 : List (List Nat × List (Nat × Nat)) := [([7,0,0,0,0,3,9,9],[]),([7,0,0,0,0,3,9,15],[]),([7,0,0,0,0,6,6,12],[]),([7,0,0,0,0,6,12],[]),([7,0,0,0,0,6,12,12],[]),([7,0,0,0,0,6,12,15],[]),([7,0,0,0,0,9,9,12],[]),([7,0,0,0,0,9,12],[]),([7,0,0,0,0,9,12,12],[]),([7,0,0,0,0,9,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc19 : sb19.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb20 : List (List Nat × List (Nat × Nat)) := [([7,0,0,0,3,3,6,15],[]),([7,0,0,0,3,3,9,15],[]),([7,0,0,0,3,6,6,15],[]),([7,0,0,0,3,6,15],[]),([7,0,0,0,3,6,15,15],[]),([7,0,0,0,3,9,9,15],[]),([7,0,0,0,3,9,15],[]),([7,0,0,0,3,9,15,15],[]),([7,0,0,0,6,6,12,15],[]),([7,0,0,0,6,12,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc20 : sb20.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb21 : List (List Nat × List (Nat × Nat)) := [([7,0,0,0,6,12,15],[]),([7,0,0,0,6,12,15,15],[]),([7,0,0,0,9,9,12,15],[]),([7,0,0,0,9,12,12,15],[]),([7,0,0,0,9,12,15],[]),([7,0,0,0,9,12,15,15],[]),([7,0,0,3,3,6,15,15],[]),([7,0,0,3,3,9,15,15],[]),([7,0,0,3,6,6,15,15],[]),([7,0,0,3,6,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc21 : sb21.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb22 : List (List Nat × List (Nat × Nat)) := [([7,0,0,3,6,15,15,15],[]),([7,0,0,3,9,9,15,15],[]),([7,0,0,3,9,15,15],[]),([7,0,0,3,9,15,15,15],[]),([7,0,0,6,6,12,15,15],[]),([7,0,0,6,12,12,15,15],[]),([7,0,0,6,12,15,15],[]),([7,0,0,6,12,15,15,15],[]),([7,0,0,9,9,12,15,15],[]),([7,0,0,9,12,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc22 : sb22.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb23 : List (List Nat × List (Nat × Nat)) := [([7,0,0,9,12,15,15],[]),([7,0,0,9,12,15,15,15],[]),([7,0,3,3,6,15,15,15],[]),([7,0,3,3,9,15,15,15],[]),([7,0,3,6,6,15,15,15],[]),([7,0,3,6,15,15,15],[]),([7,0,3,6,15,15,15,15],[]),([7,0,3,9,9,15,15,15],[]),([7,0,3,9,15,15,15],[]),([7,0,3,9,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc23 : sb23.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb24 : List (List Nat × List (Nat × Nat)) := [([7,0,6,6,12,15,15,15],[]),([7,0,6,12,12,15,15,15],[]),([7,0,6,12,15,15,15],[]),([7,0,6,12,15,15,15,15],[]),([7,0,9,9,12,15,15,15],[]),([7,0,9,12,12,15,15,15],[]),([7,0,9,12,15,15,15],[]),([7,0,9,12,15,15,15,15],[]),([7,3,3,6,15,15,15,15],[]),([7,3,3,9,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc24 : sb24.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb25 : List (List Nat × List (Nat × Nat)) := [([7,3,6,6,15,15,15,15],[]),([7,3,6,15,15,15,15],[]),([7,3,6,15,15,15,15,15],[]),([7,3,9,9,15,15,15,15],[]),([7,3,9,15,15,15,15],[]),([7,3,9,15,15,15,15,15],[]),([7,6,6,12,15,15,15,15],[]),([7,6,12,12,15,15,15,15],[]),([7,6,12,15,15,15,15],[]),([7,6,12,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc25 : sb25.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb26 : List (List Nat × List (Nat × Nat)) := [([7,9,9,12,15,15,15,15],[]),([7,9,12,12,15,15,15,15],[]),([7,9,12,15,15,15,15],[]),([7,9,12,15,15,15,15,15],[]),([8,0,0,0,0,0,0,3,6],[]),([8,0,0,0,0,0,0,3,9],[]),([8,0,0,0,0,0,0,6,12],[]),([8,0,0,0,0,0,0,9,12],[]),([8,0,0,0,0,0,3,3,6],[]),([8,0,0,0,0,0,3,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc26 : sb26.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb27 : List (List Nat × List (Nat × Nat)) := [([8,0,0,0,0,0,3,6],[]),([8,0,0,0,0,0,3,6,6],[]),([8,0,0,0,0,0,3,6,15],[]),([8,0,0,0,0,0,3,9],[]),([8,0,0,0,0,0,3,9,9],[]),([8,0,0,0,0,0,3,9,15],[]),([8,0,0,0,0,0,6,6,12],[]),([8,0,0,0,0,0,6,12],[]),([8,0,0,0,0,0,6,12,12],[]),([8,0,0,0,0,0,6,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc27 : sb27.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb28 : List (List Nat × List (Nat × Nat)) := [([8,0,0,0,0,0,9,9,12],[]),([8,0,0,0,0,0,9,12],[]),([8,0,0,0,0,0,9,12,12],[]),([8,0,0,0,0,0,9,12,15],[]),([8,0,0,0,0,3,3,6,15],[]),([8,0,0,0,0,3,3,9,15],[]),([8,0,0,0,0,3,6,6,15],[]),([8,0,0,0,0,3,6,15],[]),([8,0,0,0,0,3,6,15,15],[]),([8,0,0,0,0,3,9,9,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc28 : sb28.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb29 : List (List Nat × List (Nat × Nat)) := [([8,0,0,0,0,3,9,15],[]),([8,0,0,0,0,3,9,15,15],[]),([8,0,0,0,0,6,6,12,15],[]),([8,0,0,0,0,6,12,12,15],[]),([8,0,0,0,0,6,12,15],[]),([8,0,0,0,0,6,12,15,15],[]),([8,0,0,0,0,9,9,12,15],[]),([8,0,0,0,0,9,12,12,15],[]),([8,0,0,0,0,9,12,15],[]),([8,0,0,0,0,9,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc29 : sb29.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb30 : List (List Nat × List (Nat × Nat)) := [([8,0,0,0,3,3,6,15,15],[]),([8,0,0,0,3,3,9,15,15],[]),([8,0,0,0,3,6,6,15,15],[]),([8,0,0,0,3,6,15,15],[]),([8,0,0,0,3,6,15,15,15],[]),([8,0,0,0,3,9,9,15,15],[]),([8,0,0,0,3,9,15,15],[]),([8,0,0,0,3,9,15,15,15],[]),([8,0,0,0,6,6,12,15,15],[]),([8,0,0,0,6,12,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc30 : sb30.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb31 : List (List Nat × List (Nat × Nat)) := [([8,0,0,0,6,12,15,15],[]),([8,0,0,0,6,12,15,15,15],[]),([8,0,0,0,9,9,12,15,15],[]),([8,0,0,0,9,12,12,15,15],[]),([8,0,0,0,9,12,15,15],[]),([8,0,0,0,9,12,15,15,15],[]),([8,0,0,3,3,6,15,15,15],[]),([8,0,0,3,3,9,15,15,15],[]),([8,0,0,3,6,6,15,15,15],[]),([8,0,0,3,6,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc31 : sb31.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb32 : List (List Nat × List (Nat × Nat)) := [([8,0,0,3,6,15,15,15,15],[]),([8,0,0,3,9,9,15,15,15],[]),([8,0,0,3,9,15,15,15],[]),([8,0,0,3,9,15,15,15,15],[]),([8,0,0,6,6,12,15,15,15],[]),([8,0,0,6,12,12,15,15,15],[]),([8,0,0,6,12,15,15,15],[]),([8,0,0,6,12,15,15,15,15],[]),([8,0,0,9,9,12,15,15,15],[]),([8,0,0,9,12,12,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc32 : sb32.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb33 : List (List Nat × List (Nat × Nat)) := [([8,0,0,9,12,15,15,15],[]),([8,0,0,9,12,15,15,15,15],[]),([8,0,3,3,6,15,15,15,15],[]),([8,0,3,3,9,15,15,15,15],[]),([8,0,3,6,6,15,15,15,15],[]),([8,0,3,6,15,15,15,15],[]),([8,0,3,6,15,15,15,15,15],[]),([8,0,3,9,9,15,15,15,15],[]),([8,0,3,9,15,15,15,15],[]),([8,0,3,9,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc33 : sb33.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb34 : List (List Nat × List (Nat × Nat)) := [([8,0,6,6,12,15,15,15,15],[]),([8,0,6,12,12,15,15,15,15],[]),([8,0,6,12,15,15,15,15],[]),([8,0,6,12,15,15,15,15,15],[]),([8,0,9,9,12,15,15,15,15],[]),([8,0,9,12,12,15,15,15,15],[]),([8,0,9,12,15,15,15,15],[]),([8,0,9,12,15,15,15,15,15],[]),([8,3,3,6,15,15,15,15,15],[]),([8,3,3,9,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc34 : sb34.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb35 : List (List Nat × List (Nat × Nat)) := [([8,3,6,6,15,15,15,15,15],[]),([8,3,6,15,15,15,15,15],[]),([8,3,6,15,15,15,15,15,15],[]),([8,3,9,9,15,15,15,15,15],[]),([8,3,9,15,15,15,15,15],[]),([8,3,9,15,15,15,15,15,15],[]),([8,6,6,12,15,15,15,15,15],[]),([8,6,12,12,15,15,15,15,15],[]),([8,6,12,15,15,15,15,15],[]),([8,6,12,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc35 : sb35.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb36 : List (List Nat × List (Nat × Nat)) := [([8,9,9,12,15,15,15,15,15],[]),([8,9,12,12,15,15,15,15,15],[]),([8,9,12,15,15,15,15,15],[]),([8,9,12,15,15,15,15,15,15],[]),([9,0,0,0,0,0,0,0,3,6],[]),([9,0,0,0,0,0,0,0,3,9],[]),([9,0,0,0,0,0,0,0,6,12],[]),([9,0,0,0,0,0,0,0,9,12],[]),([9,0,0,0,0,0,0,3,3,6],[]),([9,0,0,0,0,0,0,3,3,9],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc36 : sb36.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb37 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,0,0,0,3,6],[]),([9,0,0,0,0,0,0,3,6,6],[]),([9,0,0,0,0,0,0,3,6,15],[]),([9,0,0,0,0,0,0,3,9],[]),([9,0,0,0,0,0,0,3,9,9],[]),([9,0,0,0,0,0,0,3,9,15],[]),([9,0,0,0,0,0,0,6,6,12],[]),([9,0,0,0,0,0,0,6,12],[]),([9,0,0,0,0,0,0,6,12,12],[]),([9,0,0,0,0,0,0,6,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc37 : sb37.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb38 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,0,0,0,9,9,12],[]),([9,0,0,0,0,0,0,9,12],[]),([9,0,0,0,0,0,0,9,12,12],[]),([9,0,0,0,0,0,0,9,12,15],[]),([9,0,0,0,0,0,3,3,6,15],[]),([9,0,0,0,0,0,3,3,9,15],[]),([9,0,0,0,0,0,3,6,6,15],[]),([9,0,0,0,0,0,3,6,15],[]),([9,0,0,0,0,0,3,6,15,15],[]),([9,0,0,0,0,0,3,9,9,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc38 : sb38.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb39 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,0,0,3,9,15],[]),([9,0,0,0,0,0,3,9,15,15],[]),([9,0,0,0,0,0,6,6,12,15],[]),([9,0,0,0,0,0,6,12,12,15],[]),([9,0,0,0,0,0,6,12,15],[]),([9,0,0,0,0,0,6,12,15,15],[]),([9,0,0,0,0,0,9,9,12,15],[]),([9,0,0,0,0,0,9,12,12,15],[]),([9,0,0,0,0,0,9,12,15],[]),([9,0,0,0,0,0,9,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc39 : sb39.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb40 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,0,3,3,6,15,15],[]),([9,0,0,0,0,3,3,9,15,15],[]),([9,0,0,0,0,3,6,6,15,15],[]),([9,0,0,0,0,3,6,15,15],[]),([9,0,0,0,0,3,6,15,15,15],[]),([9,0,0,0,0,3,9,9,15,15],[]),([9,0,0,0,0,3,9,15,15],[]),([9,0,0,0,0,3,9,15,15,15],[]),([9,0,0,0,0,6,6,12,15,15],[]),([9,0,0,0,0,6,12,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc40 : sb40.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb41 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,0,6,12,15,15],[]),([9,0,0,0,0,6,12,15,15,15],[]),([9,0,0,0,0,9,9,12,15,15],[]),([9,0,0,0,0,9,12,12,15,15],[]),([9,0,0,0,0,9,12,15,15],[]),([9,0,0,0,0,9,12,15,15,15],[]),([9,0,0,0,3,3,6,15,15,15],[]),([9,0,0,0,3,3,9,15,15,15],[]),([9,0,0,0,3,6,6,15,15,15],[]),([9,0,0,0,3,6,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc41 : sb41.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb42 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,3,6,15,15,15,15],[]),([9,0,0,0,3,9,9,15,15,15],[]),([9,0,0,0,3,9,15,15,15],[]),([9,0,0,0,3,9,15,15,15,15],[]),([9,0,0,0,6,6,12,15,15,15],[]),([9,0,0,0,6,12,12,15,15,15],[]),([9,0,0,0,6,12,15,15,15],[]),([9,0,0,0,6,12,15,15,15,15],[]),([9,0,0,0,9,9,12,15,15,15],[]),([9,0,0,0,9,12,12,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc42 : sb42.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb43 : List (List Nat × List (Nat × Nat)) := [([9,0,0,0,9,12,15,15,15],[]),([9,0,0,0,9,12,15,15,15,15],[]),([9,0,0,3,3,6,15,15,15,15],[]),([9,0,0,3,3,9,15,15,15,15],[]),([9,0,0,3,6,6,15,15,15,15],[]),([9,0,0,3,6,15,15,15,15],[]),([9,0,0,3,6,15,15,15,15,15],[]),([9,0,0,3,9,9,15,15,15,15],[]),([9,0,0,3,9,15,15,15,15],[]),([9,0,0,3,9,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc43 : sb43.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb44 : List (List Nat × List (Nat × Nat)) := [([9,0,0,6,6,12,15,15,15,15],[]),([9,0,0,6,12,12,15,15,15,15],[]),([9,0,0,6,12,15,15,15,15],[]),([9,0,0,6,12,15,15,15,15,15],[]),([9,0,0,9,9,12,15,15,15,15],[]),([9,0,0,9,12,12,15,15,15,15],[]),([9,0,0,9,12,15,15,15,15],[]),([9,0,0,9,12,15,15,15,15,15],[]),([9,0,3,3,6,15,15,15,15,15],[]),([9,0,3,3,9,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc44 : sb44.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb45 : List (List Nat × List (Nat × Nat)) := [([9,0,3,6,6,15,15,15,15,15],[]),([9,0,3,6,15,15,15,15,15],[]),([9,0,3,6,15,15,15,15,15,15],[]),([9,0,3,9,9,15,15,15,15,15],[]),([9,0,3,9,15,15,15,15,15],[]),([9,0,3,9,15,15,15,15,15,15],[]),([9,0,6,6,12,15,15,15,15,15],[]),([9,0,6,12,12,15,15,15,15,15],[]),([9,0,6,12,15,15,15,15,15],[]),([9,0,6,12,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc45 : sb45.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb46 : List (List Nat × List (Nat × Nat)) := [([9,0,9,9,12,15,15,15,15,15],[]),([9,0,9,12,12,15,15,15,15,15],[]),([9,0,9,12,15,15,15,15,15],[]),([9,0,9,12,15,15,15,15,15,15],[]),([9,3,3,6,15,15,15,15,15,15],[]),([9,3,3,9,15,15,15,15,15,15],[]),([9,3,6,6,15,15,15,15,15,15],[]),([9,3,6,15,15,15,15,15,15],[]),([9,3,6,15,15,15,15,15,15,15],[]),([9,3,9,9,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc46 : sb46.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb47 : List (List Nat × List (Nat × Nat)) := [([9,3,9,15,15,15,15,15,15],[]),([9,3,9,15,15,15,15,15,15,15],[]),([9,6,6,12,15,15,15,15,15,15],[]),([9,6,12,12,15,15,15,15,15,15],[]),([9,6,12,15,15,15,15,15,15],[]),([9,6,12,15,15,15,15,15,15,15],[]),([9,9,9,12,15,15,15,15,15,15],[]),([9,9,12,12,15,15,15,15,15,15],[]),([9,9,12,15,15,15,15,15,15],[]),([9,9,12,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc47 : sb47.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb48 : List (List Nat × List (Nat × Nat)) := [([10,0,0,0,0,0,0,0,0,3,6],[]),([10,0,0,0,0,0,0,0,0,3,9],[]),([10,0,0,0,0,0,0,0,0,6,12],[]),([10,0,0,0,0,0,0,0,0,9,12],[]),([10,0,0,0,0,0,0,0,3,6],[]),([10,0,0,0,0,0,0,0,3,6,15],[]),([10,0,0,0,0,0,0,0,3,9],[]),([10,0,0,0,0,0,0,0,3,9,15],[]),([10,0,0,0,0,0,0,0,6,12],[]),([10,0,0,0,0,0,0,0,6,12,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc48 : sb48.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb49 : List (List Nat × List (Nat × Nat)) := [([10,0,0,0,0,0,0,0,9,12],[]),([10,0,0,0,0,0,0,0,9,12,15],[]),([10,0,0,0,0,0,0,3,6,15],[]),([10,0,0,0,0,0,0,3,6,15,15],[]),([10,0,0,0,0,0,0,3,9,15],[]),([10,0,0,0,0,0,0,3,9,15,15],[]),([10,0,0,0,0,0,0,6,12,15],[]),([10,0,0,0,0,0,0,6,12,15,15],[]),([10,0,0,0,0,0,0,9,12,15],[]),([10,0,0,0,0,0,0,9,12,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc49 : sb49.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb50 : List (List Nat × List (Nat × Nat)) := [([10,0,0,0,0,0,3,6,15,15],[]),([10,0,0,0,0,0,3,6,15,15,15],[]),([10,0,0,0,0,0,3,9,15,15],[]),([10,0,0,0,0,0,3,9,15,15,15],[]),([10,0,0,0,0,0,6,12,15,15],[]),([10,0,0,0,0,0,6,12,15,15,15],[]),([10,0,0,0,0,0,9,12,15,15],[]),([10,0,0,0,0,0,9,12,15,15,15],[]),([10,0,0,0,0,3,6,15,15,15],[]),([10,0,0,0,0,3,6,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc50 : sb50.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb51 : List (List Nat × List (Nat × Nat)) := [([10,0,0,0,0,3,9,15,15,15],[]),([10,0,0,0,0,3,9,15,15,15,15],[]),([10,0,0,0,0,6,12,15,15,15],[]),([10,0,0,0,0,6,12,15,15,15,15],[]),([10,0,0,0,0,9,12,15,15,15],[]),([10,0,0,0,0,9,12,15,15,15,15],[]),([10,0,0,0,3,6,15,15,15,15],[]),([10,0,0,0,3,6,15,15,15,15,15],[]),([10,0,0,0,3,9,15,15,15,15],[]),([10,0,0,0,3,9,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc51 : sb51.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb52 : List (List Nat × List (Nat × Nat)) := [([10,0,0,0,6,12,15,15,15,15],[]),([10,0,0,0,6,12,15,15,15,15,15],[]),([10,0,0,0,9,12,15,15,15,15],[]),([10,0,0,0,9,12,15,15,15,15,15],[]),([10,0,0,3,6,15,15,15,15,15],[]),([10,0,0,3,6,15,15,15,15,15,15],[]),([10,0,0,3,9,15,15,15,15,15],[]),([10,0,0,3,9,15,15,15,15,15,15],[]),([10,0,0,6,12,15,15,15,15,15],[]),([10,0,0,6,12,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc52 : sb52.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb53 : List (List Nat × List (Nat × Nat)) := [([10,0,0,9,12,15,15,15,15,15],[]),([10,0,0,9,12,15,15,15,15,15,15],[]),([10,0,3,6,15,15,15,15,15,15],[]),([10,0,3,6,15,15,15,15,15,15,15],[]),([10,0,3,9,15,15,15,15,15,15],[]),([10,0,3,9,15,15,15,15,15,15,15],[]),([10,0,6,12,15,15,15,15,15,15],[]),([10,0,6,12,15,15,15,15,15,15,15],[]),([10,0,9,12,15,15,15,15,15,15],[]),([10,0,9,12,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc53 : sb53.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
def sb54 : List (List Nat × List (Nat × Nat)) := [([10,3,6,15,15,15,15,15,15,15],[]),([10,3,6,15,15,15,15,15,15,15,15],[]),([10,3,9,15,15,15,15,15,15,15],[]),([10,3,9,15,15,15,15,15,15,15,15],[]),([10,6,12,15,15,15,15,15,15,15],[]),([10,6,12,15,15,15,15,15,15,15,15],[]),([10,9,12,15,15,15,15,15,15,15],[]),([10,9,12,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc54 : sb54.all (fun kh => sP kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem srows : sT.toList = ((((((sb0 ++ (sb1 ++ sb2)) ++ (sb3 ++ (sb4 ++ sb5))) ++ ((sb6 ++ (sb7 ++ sb8)) ++ ((sb9 ++ sb10) ++ (sb11 ++ sb12)))) ++ (((sb13 ++ (sb14 ++ sb15)) ++ ((sb16 ++ sb17) ++ (sb18 ++ sb19))) ++ ((sb20 ++ (sb21 ++ sb22)) ++ ((sb23 ++ sb24) ++ (sb25 ++ sb26))))) ++ ((((sb27 ++ (sb28 ++ sb29)) ++ ((sb30 ++ sb31) ++ (sb32 ++ sb33))) ++ ((sb34 ++ (sb35 ++ sb36)) ++ ((sb37 ++ sb38) ++ (sb39 ++ sb40)))) ++ (((sb41 ++ (sb42 ++ sb43)) ++ ((sb44 ++ sb45) ++ (sb46 ++ sb47))) ++ ((sb48 ++ (sb49 ++ sb50)) ++ ((sb51 ++ sb52) ++ (sb53 ++ sb54))))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sgood : ∀ x, sT.mem x = true → ∃ h, sP x h = true := cover _ _ srows (all_app (all_app (all_app (all_app (all_app sc0 (all_app sc1 sc2)) (all_app sc3 (all_app sc4 sc5))) (all_app (all_app sc6 (all_app sc7 sc8)) (all_app (all_app sc9 sc10) (all_app sc11 sc12)))) (all_app (all_app (all_app sc13 (all_app sc14 sc15)) (all_app (all_app sc16 sc17) (all_app sc18 sc19))) (all_app (all_app sc20 (all_app sc21 sc22)) (all_app (all_app sc23 sc24) (all_app sc25 sc26))))) (all_app (all_app (all_app (all_app sc27 (all_app sc28 sc29)) (all_app (all_app sc30 sc31) (all_app sc32 sc33))) (all_app (all_app sc34 (all_app sc35 sc36)) (all_app (all_app sc37 sc38) (all_app sc39 sc40)))) (all_app (all_app (all_app sc41 (all_app sc42 sc43)) (all_app (all_app sc44 sc45) (all_app sc46 sc47))) (all_app (all_app sc48 (all_app sc49 sc50)) (all_app (all_app sc51 sc52) (all_app sc53 sc54))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallClosed : ∀ t ws, NatRun 15 5 t ws → sT.mem (t :: isort ws) = false := closure_sound sT (pD := spd) (pM := spm) (G := []) (by decide +kernel) (by decide +kernel) sgood
def bigUHint (ws : List Nat) : Nat := (([] : List (List Nat × Nat)).lookup (isort ws)).getD 0
def bigXHint (ws : List Nat) : Nat := (([] : List (List Nat × Nat)).lookup (isort ws)).getD 0
def bigStep (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => qvia y pD pM t ys && ugood m y t ys h && xGood sT m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bigClosure {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, bigStep m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [bigStep] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [bigStep, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => qvia y pD pM t ys && ugood m y t ys h && xGood sT m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [qvia_sound hp hys, ugood_sound hys, xGood_sound sT smallClosed hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def bigRoot (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !qvia y pD pM cap zs || !ucheck m y cap zs (bigUHint zs) || !xPass sT m y cap zs (bigXHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bigCore {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, bigStep m y pD pM G T x h = true)
    (hi : xs.sublists.all (bigRoot m y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := qvia_sound hp hcap
    have hc := bigClosure T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [bigClosure T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold bigRoot at hmem
    rw [hd, ucheck_sound hcap, xPass_sound sT smallClosed hcap, hc, hg] at hmem
    simp at hmem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bigLB {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, bigStep m y pD pM G T x h = true)
    (hi : xs.sublists.all (bigRoot m y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact bigCore hp hG hT hi (by omega) hsub' hr


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bigSigned (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ)
    (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 25) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 25) (h0' : zer < 25)
    (hxs : (List.ofFn fun (i : Fin 10) => (fun x : Fin 10 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 33554431 M PD PM = true) (hG : symOK 33554431 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, bigStep 33554431 M PD PM G T x h = true)
    (hi : XS.sublists.all (bigRoot 33554431 M PD PM G T s) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  have hnc : ∃ a b : Fin 10 → Bool, (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 10 (code one), pt 10 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  have hl := bigLB (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) ohPts 33554431 M XS PD PM G T s
    (s + 1) rfl (by rw [ohPts_length]; decide) (enc_rep M hM C hrep) hxs hnc hp hG hT hi s
    ⟨C, hfan, hsize, fun _ => rfl⟩
  omega



def Y_ : Nat := 3195660
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,2663050),(2,3994575),(3,3595117),(4,1298236),(5,83220),(7,41610),(8,62415),(9,56173),(10,20284),(11,1300),(13,650),(14,975),(15,877),(16,316),(17,20),(19,10),(20,15),(21,13),(22,4)]
def PM_ : List (Nat × Nat) := [(0,3195660),(1,3195660),(4,3195660),(5,3195660),(6,3195660),(7,3195660),(10,3195660),(11,3195660),(12,3195660),(13,3195660),(16,3195660),(17,3195660),(18,3195660),(19,3195660),(22,3195660),(23,3195660),(24,3195660)]
def G_ : List (List Nat) := [[24,19,14,9,4,23,18,13,8,3,22,17,12,7,2,21,16,11,6,1,20,15,10,5,0]]

abbrev Hints := List (Nat × Nat)
abbrev Row := List Nat × Hints
def localTree (a : Array Row) : Nat → Nat → Nat → BT
  | 0, _, _ => .lf
  | f+1, i, n =>
    if n = 0 then .lf else
    let h := n / 2
    let k := (a[i+h]?.getD ([],[])).1
    .nd (localTree a f i h) k (localTree a f (i+h+1) (n-h-1))
def blockTree (rs : List Row) : BT := localTree rs.toArray 9 0 rs.length
def Covered (p : List Nat → Hints → Bool) (T : BT) : Prop :=
  ∀ x, T.mem x = true → ∃ h, p x h = true
theorem coveredNode {p : List Nat → Hints → Bool} {l r : BT} {k : List Nat} {h : Hints}
    (hl : Covered p l) (hr : Covered p r) (hk : p k h = true) : Covered p (.nd l k r) := by
  intro x hx
  simp only [BT.mem, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · rw [leqL_eq x k hx]
    exact ⟨h, hk⟩
  · split at hx
    · exact hl x hx
    · exact hr x hx
theorem coveredBlock {p : List Nat → Hints → Bool} (rs : List Row)
    (hk : (blockTree rs).toList = rs.map Prod.fst)
    (hv : rs.all (fun kh => p kh.1 kh.2) = true) : Covered p (blockTree rs) :=
  cover _ _ hk hv


def b0 : List Row := [([4,12,1083361,2194498,9412872,33047056],[]),([4,31,49664,3248099,4329604,32776456],[]),([4,31,1083361,2194498,9412876,33047056],[]),([4,31,1083361,3162624,4329604,9412872],[]),([4,31,3180513,4357252,17318416,33530120],[]),([4,31,3196897,4329604,8659208,33538576],[]),([4,31,3196897,4329604,9412872,33047056],[]),([4,31,3248099,4357252,17351184,32776456],[]),([4,992,3178496,4329604,8682760,17318431],[]),([4,992,3178496,4357252,8659208,17318431],[]),([4,31744,1083361,2097164,17809936,32776456],[]),([4,31744,1083361,2164831,17809936,32776460],[]),([5,4,31,1083361,2194498,9412872,33047056],[]),([5,4,31744,1083361,2164831,17809936,32776456],[]),([5,12,992,1082401,2194498,9412872,33047056],[]),([5,12,31744,1083361,2164802,9412872,33047056],[]),([5,12,31744,1083361,2164802,17809936,32776456],[]),([5,12,1015808,1083361,2194498,8659208,33047056],[]),([5,12,1015808,1113121,2165730,8659208,33047056],[]),([5,12,1083361,2194498,9412872,17318416,32505856],[]),([5,31,992,1082401,2194498,9412876,33047056],[]),([5,31,992,3178496,4329604,8682760,17318416],[]),([5,31,992,3178496,4357252,8659208,17318416],[]),([5,31,992,3179553,4357252,17318416,33530120],[]),([5,31,992,3179553,8682760,17318416,33525892],[]),([5,31,992,3195937,4329604,8659208,33538576],[]),([5,31,992,3195937,4329604,9412872,33047056],[]),([5,31,992,3195937,5214340,8659208,33047056],[]),([5,31,992,3210273,4329604,8659208,33538576],[]),([5,31,992,3247203,4357252,17318416,32809224],[(80,0)]),([5,31,992,3247203,4357252,17351184,32776456],[]),([5,31,992,3247203,8682760,17318416,32673924],[])]
def b1 : List Row := [([5,31,992,3275875,4329604,8659208,33079824],[]),([5,31,996,1082401,2194498,9412872,33047056],[]),([5,31,31744,1083361,2164802,9412876,33047056],[]),([5,31,31744,1083361,2164802,17809936,32776460],[]),([5,31,31744,3180513,4329604,8659208,33538576],[]),([5,31,31744,3180513,4329604,9412872,33047056],[]),([5,31,31744,3180513,4329604,17318416,33530120],[]),([5,31,31744,3180513,4329604,17809936,32776456],[]),([5,31,31744,3248099,4329604,8659208,33079824],[]),([5,31,31744,3248099,4329604,8691976,33047056],[]),([5,31,31744,3248099,4329604,17351184,32776456],[]),([5,31,31748,1083361,2164802,9412872,33047056],[]),([5,31,31748,1083361,2164802,17809936,32776456],[]),([5,31,32768,3248099,4357252,17318416,32776456],[(176,0)]),([5,31,49664,1083361,2164802,4329604,32776456],[(96,0)]),([5,31,49664,3248099,4329604,8659208,32505856],[]),([5,31,1015808,1083361,2194498,8659212,33047056],[]),([5,31,1015808,1083361,3162624,4329604,8659208],[]),([5,31,1015808,1113121,2165730,8659212,33047056],[]),([5,31,1015808,3180513,4357252,17318416,32776456],[]),([5,31,1015808,3196897,4329604,8659208,33047056],[]),([5,31,1015812,1083361,2194498,8659208,33047056],[]),([5,31,1015812,1113121,2165730,8659208,33047056],[]),([5,31,1081344,2165730,4357252,17318416,32776456],[]),([5,31,1082401,2098144,4357252,17318416,33530120],[]),([5,31,1082401,2114528,4329604,8659208,33538576],[]),([5,31,1082401,2114528,4329604,9412872,33047056],[]),([5,31,1082401,2114528,5214340,8659208,33047056],[]),([5,31,1082401,2165730,4357252,17318416,32809224],[(80,0)]),([5,31,1082401,2165730,4357252,17351184,32776456],[]),([5,31,1082401,2182114,5214340,8659208,33047056],[]),([5,31,1082401,2182114,5214340,17318416,32776456],[(56,0)])]
def t0 : BT := .nd (blockTree b0) [5,31,992,3247203,8682760,17351184,32641156] (blockTree b1)
def b2 : List Row := [([5,31,1083361,2113536,4329604,8659208,33538576],[]),([5,31,1083361,2113536,4329604,9412872,33047056],[]),([5,31,1083361,2128896,4329604,8659208,33538576],[]),([5,31,1083361,2128896,4329604,9412872,33047056],[]),([5,31,1083361,2164802,4357252,17351184,32776456],[]),([5,31,1083361,2181186,4329604,9412872,33047056],[]),([5,31,1083361,2194498,4329604,8659208,33079824],[]),([5,31,1083361,2194498,4329604,8691976,33047056],[]),([5,31,1083361,2194498,4329604,9412872,33047056],[]),([5,31,1083361,2194498,4329604,33047056,33530120],[]),([5,31,1083361,2194498,4330468,9412872,33047056],[]),([5,31,1083361,2194498,4357252,9412872,33047056],[]),([5,31,1083361,2194498,5214340,9412872,33047056],[]),([5,31,1083361,2194498,9412872,12988812,33047056],[]),([5,31,1083361,2194498,9412872,13611404,33047056],[]),([5,31,1083361,2194498,9412872,17318416,32505860],[]),([5,31,1083361,2194498,9412872,32641156,33047056],[]),([5,31,1083361,2194498,17318416,32641156,33530120],[]),([5,31,1083361,2195426,4329604,9412872,33047056],[]),([5,31,1083361,3275875,4329604,9412872,33047056],[]),([5,31,1083361,3275875,5214340,8659208,33047056],[]),([5,31,1083361,3276771,4329604,9412872,33047056],[]),([5,31,1097728,2165730,4329604,8659208,33047056],[]),([5,31,1098785,2165730,5214340,8659208,33047056],[]),([5,31,1099745,2164802,4329604,9412872,33047056],[]),([5,31,1099745,2164802,4329604,17809936,32776456],[(72,0)]),([5,31,1113121,2098144,4329604,8659208,33538576],[]),([5,31,1113121,2165730,4329604,8659208,33079824],[]),([5,31,1113121,3248099,5214340,8659208,33047056],[]),([5,31,1114081,3248099,4329604,9412872,33047056],[]),([5,31,1114081,3248099,4329604,17809936,32776456],[]),([5,31,3248099,4357252,8659208,17351184,32505856],[])]
def b3 : List Row := [([5,992,31744,1082401,2097164,17809936,32776456],[]),([5,992,31744,1082401,2164831,17809936,32776460],[]),([5,992,31744,3178496,4329604,8659208,17318431],[(96,0)]),([5,992,32768,3145728,4329604,8682760,17318431],[]),([5,992,32768,3145728,4357252,8659208,17318431],[]),([5,992,1081344,2097152,4329604,8682760,17318431],[]),([5,992,1082401,3115074,8675596,17318431,32505856],[]),([5,992,1082401,3115074,8682764,17318431,32505856],[]),([5,992,1082431,2194498,4329604,33047056,33530120],[]),([5,992,1082431,2194498,5214340,32776456,33047056],[]),([5,992,1082431,2194498,8659208,33047056,33525892],[]),([5,992,1082431,2194498,9412872,32641156,33047056],[]),([5,992,1082431,3275875,4329604,9412872,33047056],[]),([5,992,1098785,2164831,4329604,17809936,32776456],[(56,0)]),([5,992,1098785,2164831,8659208,17809936,32641156],[]),([5,992,1113121,2164831,4329604,32776456,33538576],[]),([5,992,1113121,2164831,8659208,32641156,33538576],[]),([5,992,1113121,2164831,8659212,17809936,32505856],[]),([5,992,1113121,2164831,17809936,32641156,32776456],[]),([5,992,1113121,3247231,4329604,17809936,32776456],[]),([5,992,3179553,4329604,8682760,17318431,33521664],[]),([5,992,3179553,4357252,8659208,17318431,33521664],[]),([5,992,3247203,4329604,8682760,17318431,32538624],[]),([5,992,3247203,4357252,8691976,17318431,32505856],[]),([5,992,3247203,4362372,8682760,17318431,32505856],[]),([5,996,1082401,3115074,8682760,17318431,32505856],[]),([5,17376,1082401,2164831,4329604,17809936,32776456],[(56,0)]),([5,31744,1082431,2165730,5214340,32776456,33047056],[]),([5,31744,1083361,2097183,4329604,17809936,32776456],[]),([5,31744,1083361,2164831,4329604,17809936,32776456],[]),([5,31744,1083361,2164831,4329604,32776456,33538576],[])]
def t1 : BT := .nd (blockTree b2) [5,31,3275875,4330468,8659208,17351184,32505856] (blockTree b3)
def t2 : BT := .nd t0 [5,31,1082401,2195426,4330468,9412872,33047056] t1
def b4 : List Row := [([5,31744,1083361,2164831,17809936,32641156,32776456],[]),([5,31744,1083361,2164831,17809936,32776456,32911756],[]),([5,31744,3247203,4330468,8691976,17318431,32505856],[]),([6,4,31,992,1082401,2194498,9412872,33047056],[]),([6,4,31,31744,1083361,2164802,9412872,33047056],[]),([6,4,31,31744,1083361,2164802,17809936,32776456],[]),([6,4,31,1015808,1083361,2194498,8659208,33047056],[]),([6,4,31,1015808,1113121,2165730,8659208,33047056],[]),([6,4,31,1083361,2194498,9412872,17318416,32505856],[(128,0)]),([6,4,992,31744,1082401,2164831,17809936,32776456],[]),([6,4,992,1082401,3115074,8682760,17318431,32505856],[]),([6,4,992,1082431,2194498,9412872,17318416,32505856],[(128,0),(216,0)]),([6,4,992,1113121,2164831,8659208,17809936,32505856],[(216,0)]),([6,4,31744,1015808,1082431,2165730,17318416,32776456],[(72,0),(216,0)]),([6,4,31744,1015808,1083361,2164831,17318416,32776456],[(216,0)]),([6,4,31744,1083361,2164831,8659208,17809936,32505856],[(128,0),(216,0)]),([6,12,992,31744,1082401,2164802,9412872,33047056],[]),([6,12,992,31744,1082401,2164802,17809936,32776456],[]),([6,12,992,1015808,1082401,2194498,8659208,33047056],[]),([6,12,992,1015808,1113121,2164802,8659208,33047056],[]),([6,12,992,1082401,2194498,9412872,17318416,32505856],[]),([6,12,992,1082401,3115074,8682760,17318416,32505856],[]),([6,12,992,1113121,2164802,8659208,17809936,32505856],[]),([6,12,31744,1015808,1082401,2165730,8659208,33047056],[]),([6,12,31744,1015808,1082401,2165730,17318416,32776456],[]),([6,12,31744,1015808,1083361,2164802,8659208,33047056],[]),([6,12,31744,1015808,1083361,2164802,17318416,32776456],[]),([6,12,31744,1083361,2164802,8659208,17809936,32505856],[]),([6,12,31744,1083361,2164802,9412872,17318416,32505856],[]),([6,12,1015808,1083361,2194498,8659208,17318416,32505856],[]),([6,12,1015808,1113121,2165730,8659208,17318416,32505856],[]),([6,31,992,31744,1082401,2164802,9412876,33047056],[])]
def b5 : List Row := [([6,31,992,31744,3178496,4329604,8659208,17318416],[(136,0)]),([6,31,992,31744,3179553,4329604,8659208,33538576],[]),([6,31,992,31744,3179553,4329604,9412872,33047056],[]),([6,31,992,31744,3179553,4329604,17318416,33530120],[(96,0)]),([6,31,992,31744,3179553,4329604,17809936,32776456],[]),([6,31,992,31744,3179553,5214340,8659208,33047056],[]),([6,31,992,31744,3179553,5214340,17318416,32776456],[(96,0)]),([6,31,992,31744,3179553,8659208,17318416,33525892],[(96,0)]),([6,31,992,31744,3179553,8659208,17809936,32641156],[]),([6,31,992,31744,3179553,9412872,17318416,32641156],[(96,0)]),([6,31,992,31744,3247203,4329604,8659208,33079824],[]),([6,31,992,31744,3247203,4329604,8691976,33047056],[]),([6,31,992,31744,3247203,4329604,17318416,32809224],[(96,0),(104,0)]),([6,31,992,31744,3247203,4329604,17351184,32776456],[]),([6,31,992,31744,3247203,4362372,8659208,33047056],[]),([6,31,992,31744,3247203,4362372,17318416,32776456],[(96,0)]),([6,31,992,31744,3247203,8659208,17318416,32673924],[(96,0)]),([6,31,992,31744,3247203,8659208,17351184,32641156],[]),([6,31,992,31744,3247203,8691976,17318416,32641156],[(96,0)]),([6,31,992,31748,1082401,2164802,9412872,33047056],[]),([6,31,992,31748,1082401,2164802,17809936,32776456],[]),([6,31,992,32768,3145728,4329604,8682760,17318416],[]),([6,31,992,32768,3145728,4357252,8659208,17318416],[]),([6,31,992,32768,3247203,4357252,17318416,32776456],[]),([6,31,992,32768,3247203,8682760,17318416,32641156],[]),([6,31,992,32768,3275875,4329604,8659208,33047056],[]),([6,31,992,1015808,1082401,2194498,8659212,33047056],[]),([6,31,992,1015808,1113121,2164802,8659212,33047056],[]),([6,31,992,1015808,3179553,4357252,17318416,32776456],[]),([6,31,992,1015808,3179553,8682760,17318416,32641156],[]),([6,31,992,1015808,3195937,4329604,8659208,33047056],[])]
def t3 : BT := .nd (blockTree b4) [6,31,992,31744,1082401,2164802,17809936,32776460] (blockTree b5)
def b6 : List Row := [([6,31,992,1015812,1082401,2194498,8659208,33047056],[]),([6,31,992,1015812,1113121,2164802,8659208,33047056],[]),([6,31,992,1081344,2097152,4329604,8682760,17318416],[]),([6,31,992,1081344,2164802,4357252,17318416,32776456],[]),([6,31,992,1081344,2164802,8682760,17318416,32641156],[]),([6,31,992,1081344,2194498,4329604,8659208,33047056],[]),([6,31,992,1082401,2097152,4357252,17318416,33530120],[(80,0),(96,0)]),([6,31,992,1082401,2097152,8682760,17318416,33525892],[(96,0)]),([6,31,992,1082401,2113536,4329604,8659208,33538576],[]),([6,31,992,1082401,2113536,4329604,9412872,33047056],[]),([6,31,992,1082401,2113536,5214340,8659208,33047056],[]),([6,31,992,1082401,2128896,4329604,8659208,33538576],[]),([6,31,992,1082401,2128896,4329604,9412872,33047056],[]),([6,31,992,1082401,2128896,5214340,8659208,33047056],[]),([6,31,992,1082401,2164802,4357252,17318416,32809224],[(80,0)]),([6,31,992,1082401,2164802,4357252,17351184,32776456],[]),([6,31,992,1082401,2164802,8682760,17318416,32673924],[]),([6,31,992,1082401,2164802,8682760,17351184,32641156],[]),([6,31,992,1082401,2181186,4329604,9412872,33047056],[]),([6,31,992,1082401,2181186,5214340,8659208,33047056],[]),([6,31,992,1082401,2181186,5214340,17318416,32776456],[(72,0)]),([6,31,992,1082401,2181186,9412872,17318416,32641156],[(72,0)]),([6,31,992,1082401,2194498,4329604,8659208,33079824],[]),([6,31,992,1082401,2194498,4329604,8691976,33047056],[]),([6,31,992,1082401,2194498,4329604,9412872,33047056],[]),([6,31,992,1082401,2194498,4329604,33047056,33530120],[]),([6,31,992,1082401,2194498,4330468,9412872,33047056],[]),([6,31,992,1082401,2194498,4357252,9412872,33047056],[]),([6,31,992,1082401,2194498,4362372,8659208,33047056],[]),([6,31,992,1082401,2194498,5214340,8659208,33047056],[]),([6,31,992,1082401,2194498,5214340,8682760,33047056],[]),([6,31,992,1082401,2194498,5214340,9412872,33047056],[])]
def b7 : List Row := [([6,31,992,1082401,2194498,8659208,13611404,33047056],[]),([6,31,992,1082401,2194498,8659208,33047056,33525892],[]),([6,31,992,1082401,2194498,9412872,12988812,33047056],[]),([6,31,992,1082401,2194498,9412872,13611404,33047056],[]),([6,31,992,1082401,2194498,9412872,17318416,32505860],[(72,0)]),([6,31,992,1082401,2194498,9412872,32641156,33047056],[]),([6,31,992,1082401,2194498,9412876,17318416,32505856],[(72,0),(80,0)]),([6,31,992,1082401,2194498,17318416,32641156,33530120],[(72,0)]),([6,31,992,1082401,2194498,17318416,32776456,33525892],[(72,0)]),([6,31,992,1082401,2195426,4329604,9412872,33047056],[]),([6,31,992,1082401,2195426,5214340,8659208,33047056],[]),([6,31,992,1082401,2197570,4357252,17318416,32776456],[]),([6,31,992,1082401,2197570,8682760,17318416,32641156],[]),([6,31,992,1082401,3115074,8682760,17318416,32505860],[]),([6,31,992,1082401,3115074,8682764,17318416,32505856],[]),([6,31,992,1082401,3145728,4357252,9412872,17318416],[(80,0)]),([6,31,992,1082401,3145728,5214340,8682760,17318416],[]),([6,31,992,1082401,3275875,4329604,9412872,33047056],[]),([6,31,992,1082401,3275875,5214340,8659208,33047056],[(72,0)]),([6,31,992,1083361,2194498,4329604,9412872,33047056],[]),([6,31,992,1097728,2164802,4329604,8659208,33047056],[]),([6,31,992,1098785,2164802,4329604,9412872,33047056],[]),([6,31,992,1098785,2164802,4329604,17809936,32776456],[]),([6,31,992,1098785,2164802,5214340,8659208,33047056],[]),([6,31,992,1098785,2164802,5214340,17318416,32776456],[(104,0)]),([6,31,992,1098785,2164802,8659208,17809936,32641156],[]),([6,31,992,1098785,2164802,9412872,17318416,32641156],[]),([6,31,992,1113121,2097152,4329604,8659208,33538576],[]),([6,31,992,1113121,2164802,4329604,8659208,33079824],[]),([6,31,992,1113121,2164802,4329604,32776456,33538576],[]),([6,31,992,1113121,2164802,5214340,9412872,33047056],[])]
def t4 : BT := .nd (blockTree b6) [6,31,992,1082401,2194498,5214340,32776456,33047056] (blockTree b7)
def t5 : BT := .nd t3 [6,31,992,1015808,3210273,4329604,8659208,33047056] t4
def t6 : BT := .nd t2 [5,31744,1083361,2164831,12988812,17809936,32776456] t5
def b8 : List Row := [([6,31,992,1113121,2164802,8659208,32641156,33538576],[]),([6,31,992,1113121,2164802,8659212,17809936,32505856],[]),([6,31,992,1113121,2164802,17809936,32641156,32776456],[]),([6,31,992,1113121,3145728,4329604,8659208,17809936],[]),([6,31,992,1113121,3247203,4329604,9412872,33047056],[]),([6,31,992,1113121,3247203,4329604,17809936,32776456],[]),([6,31,992,1113121,3247203,5214340,8659208,33047056],[]),([6,31,992,1113121,3247203,5214340,17318416,32776456],[(104,0)]),([6,31,992,1113121,3247203,8659208,17809936,32641156],[(96,0)]),([6,31,992,1113121,3247203,9412872,17318416,32641156],[]),([6,31,992,3179553,4329604,8682760,17318416,33521664],[]),([6,31,992,3179553,4357252,8659208,17318416,33521664],[(80,0)]),([6,31,992,3179553,4357252,9412872,17318416,32505856],[(80,0)]),([6,31,992,3179553,5214340,8682760,17318416,32505856],[]),([6,31,992,3210273,4329604,8659208,17809936,32505856],[]),([6,31,992,3247203,4329604,8682760,17318416,32538624],[]),([6,31,992,3247203,4329604,8682760,17351184,32505856],[]),([6,31,992,3247203,4357252,8659208,17351184,32505856],[]),([6,31,992,3247203,4357252,8691976,17318416,32505856],[(80,0)]),([6,31,992,3247203,4362372,8682760,17318416,32505856],[]),([6,31,992,3275875,4329604,8659208,17351184,32505856],[]),([6,31,996,31744,1082401,2164802,9412872,33047056],[]),([6,31,996,31744,1082401,2164802,17809936,32776456],[]),([6,31,996,1015808,1082401,2194498,8659208,33047056],[]),([6,31,996,1015808,1113121,2164802,8659208,33047056],[]),([6,31,996,1082401,2194498,9412872,17318416,32505856],[]),([6,31,996,1082401,3115074,8682760,17318416,32505856],[]),([6,31,996,1113121,2164802,8659208,17809936,32505856],[]),([6,31,17376,1082401,2164802,4329604,9412872,33047056],[]),([6,31,17376,1082401,2164802,4329604,17809936,32776456],[]),([6,31,17376,1082401,2164802,5214340,8659208,33047056],[]),([6,31,17376,1082401,2164802,5214340,17318416,32776456],[(72,0)])]
def b9 : List Row := [([6,31,17376,1082401,2164802,9412872,17318416,32641156],[(72,0)]),([6,31,31744,32768,3248099,4329604,8659208,33047056],[]),([6,31,31744,32768,3248099,4329604,17318416,32776456],[(232,0)]),([6,31,31744,1015808,1082401,2165730,8659212,33047056],[]),([6,31,31744,1015808,1082401,2165730,17318416,32776460],[(96,0)]),([6,31,31744,1015808,1083361,2164802,8659212,33047056],[]),([6,31,31744,1015808,1083361,2164802,17318416,32776460],[(128,0)]),([6,31,31744,1015808,3180513,4329604,8659208,33047056],[]),([6,31,31744,1015808,3180513,4329604,17318416,32776456],[]),([6,31,31744,1015812,1082401,2165730,8659208,33047056],[]),([6,31,31744,1015812,1082401,2165730,17318416,32776456],[(96,0)]),([6,31,31744,1015812,1083361,2164802,8659208,33047056],[]),([6,31,31744,1015812,1083361,2164802,17318416,32776456],[]),([6,31,31744,1081344,2165730,4329604,8659208,33047056],[]),([6,31,31744,1081344,2165730,4329604,17318416,32776456],[]),([6,31,31744,1082401,2098144,4329604,8659208,33538576],[]),([6,31,31744,1082401,2098144,4329604,9412872,33047056],[]),([6,31,31744,1082401,2098144,4329604,17318416,33530120],[(72,0)]),([6,31,31744,1082401,2098144,4329604,17809936,32776456],[]),([6,31,31744,1082401,2098144,5214340,8659208,33047056],[]),([6,31,31744,1082401,2098144,5214340,17318416,32776456],[(72,0)]),([6,31,31744,1082401,2165730,4329604,8659208,33079824],[]),([6,31,31744,1082401,2165730,4329604,8691976,33047056],[]),([6,31,31744,1082401,2165730,4329604,17318416,32809224],[(72,0),(112,0)]),([6,31,31744,1082401,2165730,4329604,17351184,32776456],[]),([6,31,31744,1082401,2165730,4330468,9412872,33047056],[]),([6,31,31744,1082401,2165730,4330468,17809936,32776456],[]),([6,31,31744,1082401,2165730,4362372,8659208,33047056],[]),([6,31,31744,1082401,2165730,4362372,17318416,32776456],[(72,0)]),([6,31,31744,1082401,2165730,5214340,8659208,33047056],[]),([6,31,31744,1082401,2165730,5214340,17318416,32776456],[(72,0)]),([6,31,31744,1082401,2165730,5214340,32776456,33047056],[])]
def t7 : BT := .nd (blockTree b8) [6,31,17376,1082401,2164802,8659208,17809936,32641156] (blockTree b9)
def b10 : List Row := [([6,31,31744,1082401,2165730,8659208,33047056,33525892],[(72,0)]),([6,31,31744,1082401,2165730,9412872,12988812,33047056],[]),([6,31,31744,1082401,2165730,13611404,17318416,32776456],[(72,0)]),([6,31,31744,1082401,2165730,17318416,32776456,33525892],[(72,0)]),([6,31,31744,1082401,2165730,17318416,32776456,33534348],[(72,0)]),([6,31,31744,1082401,2165730,17318416,32911756,33530120],[(72,0)]),([6,31,31744,1082401,3248099,5214340,8659208,33047056],[(72,0)]),([6,31,31744,1082401,3248099,5214340,17318416,32776456],[(72,0),(80,0)]),([6,31,31744,1082431,2165730,5214340,17318416,32776456],[(72,0)]),([6,31,31744,1083361,2097152,4329604,8659208,33538576],[]),([6,31,31744,1083361,2097152,4329604,9412872,33047056],[]),([6,31,31744,1083361,2097152,4329604,17809936,32776456],[]),([6,31,31744,1083361,2164802,4329604,8659208,33079824],[]),([6,31,31744,1083361,2164802,4329604,8691976,33047056],[]),([6,31,31744,1083361,2164802,4329604,9412872,33047056],[]),([6,31,31744,1083361,2164802,4329604,17351184,32776456],[(96,0)]),([6,31,31744,1083361,2164802,4329604,17809936,32776456],[]),([6,31,31744,1083361,2164802,4329604,32776456,33538576],[]),([6,31,31744,1083361,2164802,4329604,33047056,33530120],[]),([6,31,31744,1083361,2164802,4330468,9412872,33047056],[]),([6,31,31744,1083361,2164802,4330468,17809936,32776456],[]),([6,31,31744,1083361,2164802,4357252,9412872,33047056],[]),([6,31,31744,1083361,2164802,4357252,17809936,32776456],[]),([6,31,31744,1083361,2164802,5214340,9412872,33047056],[]),([6,31,31744,1083361,2164802,5214340,17809936,32776456],[]),([6,31,31744,1083361,2164802,8659208,17809936,32505860],[(96,0)]),([6,31,31744,1083361,2164802,8659208,32641156,33538576],[(96,0)]),([6,31,31744,1083361,2164802,8659212,17809936,32505856],[(96,0)]),([6,31,31744,1083361,2164802,9412872,12988812,33047056],[]),([6,31,31744,1083361,2164802,9412872,13611404,33047056],[]),([6,31,31744,1083361,2164802,9412872,17318416,32505860],[]),([6,31,31744,1083361,2164802,9412872,32641156,33047056],[])]
def b11 : List Row := [([6,31,31744,1083361,2164802,12988812,17809936,32776456],[]),([6,31,31744,1083361,2164802,17318416,32641156,33530120],[]),([6,31,31744,1083361,2164802,17318416,32911756,33530120],[(96,0)]),([6,31,31744,1083361,2164802,17809936,32641156,32776456],[]),([6,31,31744,1083361,2164802,17809936,32776456,32911756],[]),([6,31,31744,1083361,2164831,4329604,17809936,32776456],[]),([6,31,31744,1083361,2165730,4329604,9412872,33047056],[]),([6,31,31744,1083361,2165730,4329604,17809936,32776456],[]),([6,31,31744,1083361,2194498,4329604,9412872,33047056],[]),([6,31,31744,1083361,3145728,4329604,8659208,17809936],[]),([6,31,31744,1083361,3247203,4329604,9412872,33047056],[]),([6,31,31744,1083361,3247203,4329604,17809936,32776456],[(96,0)]),([6,31,31744,1083361,3247203,5214340,8659208,33047056],[]),([6,31,31744,1083361,3247203,5214340,17318416,32776456],[]),([6,31,31744,1083361,3247203,8659208,17809936,32641156],[(96,0)]),([6,31,31744,1083361,3247203,9412872,17318416,32641156],[]),([6,31,31744,1083361,3248099,4329604,9412872,33047056],[]),([6,31,31744,1083361,3248099,4329604,17809936,32776456],[]),([6,31,31744,3180513,4329604,8659208,17809936,32505856],[]),([6,31,31744,3247203,4330468,8659208,17351184,32505856],[]),([6,31,31744,3247203,4330468,8691976,17318416,32505856],[]),([6,31,31744,3248099,4329604,8659208,17351184,32505856],[]),([6,31,31748,1015808,1082401,2165730,8659208,33047056],[]),([6,31,31748,1015808,1082401,2165730,17318416,32776456],[]),([6,31,31748,1015808,1083361,2164802,8659208,33047056],[]),([6,31,31748,1015808,1083361,2164802,17318416,32776456],[]),([6,31,31748,1083361,2164802,8659208,17809936,32505856],[]),([6,31,31748,1083361,2164802,9412872,17318416,32505856],[]),([6,31,32736,1082401,2164802,4330468,9412872,33047056],[]),([6,31,32736,1082401,2164802,4330468,17809936,32776456],[]),([6,31,32736,1082401,2165730,4329604,9412872,33047056],[])]
def t8 : BT := .nd (blockTree b10) [6,31,31744,1083361,2164802,9412876,17318416,32505856] (blockTree b11)
def t9 : BT := .nd t7 [6,31,31744,1082401,2165730,8659208,13611404,33047056] t8
def b12 : List Row := [([6,31,32736,1082401,2165730,5214340,8659208,33047056],[]),([6,31,32736,1082401,2165730,5214340,17318416,32776456],[(72,0),(180,0)]),([6,31,32736,1083361,2164802,4329604,9412872,33047056],[]),([6,31,32736,1083361,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,32768,1082401,2165730,4357252,17318416,32776456],[]),([6,31,32768,1083361,2164802,4357252,17318416,32776456],[(224,0)]),([6,31,32768,1083361,2194498,4329604,8659208,33047056],[]),([6,31,32768,1113121,2165730,4329604,8659208,33047056],[]),([6,31,49664,1083361,2164802,4329604,8659208,32505856],[(96,0)]),([6,31,1015808,1082401,2098144,4357252,17318416,32776456],[]),([6,31,1015808,1082401,2114528,4329604,8659208,33047056],[]),([6,31,1015808,1082401,2165730,4357252,17318416,32776456],[]),([6,31,1015808,1082401,2165730,4358116,17318416,32776456],[]),([6,31,1015808,1082401,2165730,13008268,17318416,32776456],[]),([6,31,1015808,1082401,2182114,4329604,8659208,33047056],[]),([6,31,1015808,1082401,2195426,4330468,8659208,33047056],[]),([6,31,1015808,1082401,3248099,4357252,17318416,32776456],[]),([6,31,1015808,1082431,2165730,4357252,17318416,32776456],[]),([6,31,1015808,1083361,2113536,4329604,8659208,33047056],[]),([6,31,1015808,1083361,2128896,4329604,8659208,33047056],[]),([6,31,1015808,1083361,2164802,4357252,17318416,32776456],[]),([6,31,1015808,1083361,2164802,4358116,17318416,32776456],[]),([6,31,1015808,1083361,2164831,4357252,17318416,32776456],[]),([6,31,1015808,1083361,2165730,4357252,17318416,32776456],[]),([6,31,1015808,1083361,2181186,4329604,8659208,33047056],[]),([6,31,1015808,1083361,2194498,4329604,8659208,33047056],[]),([6,31,1015808,1083361,2194498,4329604,9412872,33047056],[]),([6,31,1015808,1083361,2194498,4329604,32776456,33047056],[]),([6,31,1015808,1083361,2194498,4330468,8659208,33047056],[]),([6,31,1015808,1083361,2194498,4357252,8659208,33047056],[]),([6,31,1015808,1083361,2194498,5214340,8659208,33047056],[]),([6,31,1015808,1083361,2194498,8659208,12988812,33047056],[])]
def b13 : List Row := [([6,31,1015808,1083361,2194498,17318416,32641156,32776456],[]),([6,31,1015808,1083361,2195426,4329604,8659208,33047056],[]),([6,31,1015808,1083361,3247203,4357252,17318416,32776456],[]),([6,31,1015808,1083361,3248099,4357252,17318416,32776456],[]),([6,31,1015808,1083361,3275875,4329604,8659208,33047056],[]),([6,31,1015808,1083361,3276771,4329604,8659208,33047056],[]),([6,31,1015808,1098785,2165730,4329604,8659208,33047056],[]),([6,31,1015808,1099745,2164802,4329604,8659208,33047056],[]),([6,31,1015808,1113121,2098144,4329604,8659208,33047056],[]),([6,31,1015808,1113121,2165730,4329604,8659208,33047056],[]),([6,31,1015808,1113121,2165730,4329604,32776456,33047056],[]),([6,31,1015808,1113121,2165730,4330468,8659208,33047056],[]),([6,31,1015808,1113121,2165730,4357252,8659208,33047056],[]),([6,31,1015808,1113121,2165730,5214340,8659208,33047056],[]),([6,31,1015808,1113121,2165730,8659208,12988812,33047056],[]),([6,31,1015808,1113121,2165730,8659208,32641156,33047056],[]),([6,31,1015808,1113121,2165730,17318416,32641156,32776456],[]),([6,31,1015808,1113121,3248099,4329604,8659208,33047056],[]),([6,31,1015808,1114081,2164802,4330468,8659208,33047056],[]),([6,31,1015808,1114081,2165730,4329604,8659208,33047056],[]),([6,31,1015808,1114081,3248099,4329604,8659208,33047056],[]),([6,31,1082401,1083361,2194498,4329604,9412872,33047056],[(56,0)]),([6,31,1082401,1083361,2194498,5214340,8659208,33047056],[(56,0)]),([6,31,1082401,1113121,2165730,5214340,8659208,33047056],[(56,0)]),([6,31,1082401,1113121,2165730,5214340,17318416,32776456],[(56,0),(104,0)]),([6,31,1082401,2098144,4357252,9412872,17318416,32505856],[(80,0)]),([6,31,1082401,2098144,5214340,8682760,17318416,32505856],[]),([6,31,1082401,2165730,2194498,5214340,8659208,33047056],[]),([6,31,1082401,2165730,2194498,5214340,17318416,32776456],[(56,0)]),([6,31,1082401,2165730,2195426,5214340,8659208,33047056],[]),([6,31,1082401,2165730,2195426,5214340,17318416,32776456],[(56,0),(196,0)])]
def t10 : BT := .nd (blockTree b12) [6,31,1015808,1083361,2194498,8659208,32641156,33047056] (blockTree b13)
def b14 : List Row := [([6,31,1082401,2165730,4357252,5214340,17318416,32776456],[(56,0)]),([6,31,1082401,2165730,4357252,8659208,17351184,32505856],[]),([6,31,1082401,2165730,4357252,8659208,17809936,33047056],[]),([6,31,1082401,2165730,4357252,9412872,17318416,32776456],[]),([6,31,1082401,2165730,4357252,17318416,17809936,32776456],[]),([6,31,1082401,2165730,4357252,17318416,32776456,33521664],[]),([6,31,1082401,2165730,4357252,17318416,32776456,33530120],[]),([6,31,1082401,2165730,4358116,9412872,17318416,32505856],[]),([6,31,1082401,2165730,5214340,8682760,17318416,32776456],[(56,0)]),([6,31,1082401,2165730,8682760,13611404,17318416,32505856],[(56,0)]),([6,31,1082401,2194498,4330468,8659208,17351184,32505856],[]),([6,31,1082401,2194498,4330468,8659208,17809936,33047056],[]),([6,31,1083361,1113121,2164802,4329604,9412872,33047056],[]),([6,31,1083361,1113121,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,1083361,1113121,2164802,5214340,8659208,33047056],[]),([6,31,1083361,1113121,2164802,8659208,17809936,32641156],[(96,0)]),([6,31,1083361,1114081,2164802,4329604,9412872,33047056],[]),([6,31,1083361,1114081,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,1083361,2128896,4329604,8659208,17809936,32505856],[]),([6,31,1083361,2164802,2194498,4329604,9412872,33047056],[]),([6,31,1083361,2164802,4357252,8659208,17351184,32505856],[]),([6,31,1083361,2164802,4357252,8659208,17809936,33047056],[]),([6,31,1083361,2194498,4329604,8659208,9412872,33047056],[]),([6,31,1083361,2194498,4329604,8659208,17351184,32505856],[]),([6,31,1083361,2194498,4329604,8659208,17809936,33047056],[]),([6,31,1083361,2194498,4329604,8659208,33047056,33521664],[]),([6,31,1083361,2194498,4329604,8659208,33047056,33538576],[]),([6,31,1083361,2194498,4329604,9412872,32505856,33047056],[]),([6,31,1083361,2194498,4329604,9412872,33047056],[]),([6,31,1083361,2194498,4357252,8659208,17809936,32505856],[]),([6,31,1083361,2194498,9412872,33047056],[(1024,300101),(1024,279617)]),([6,31,1099745,2164802,4329604,8659208,17809936,32505856],[(72,0)])]
def b15 : List Row := [([6,31,1113121,2164802,4330468,8659208,17351184,32505856],[]),([6,31,1113121,2164802,4330468,8659208,17809936,33047056],[]),([6,31,1113121,2165730,4329604,8659208,17351184,32505856],[]),([6,31,1113121,2165730,4329604,8659208,17809936,33047056],[]),([6,31,1113121,2165730,4329604,8659208,33047056,33521664],[]),([6,31,1113121,2165730,4329604,8659208,33047056,33538576],[]),([6,31,1113121,2165730,4330468,8659208,17809936,32505856],[]),([6,31,1114081,2164802,4330468,8659208,17809936,32505856],[]),([6,31,1114081,2165730,4329604,8659208,17809936,32505856],[]),([6,31,1114081,3248099,4329604,8659208,17809936,32505856],[]),([6,992,16388,1082401,3115074,8659208,17318431,32505856],[(56,0)]),([6,992,31744,32768,3145728,4329604,8659208,17318431],[(128,0)]),([6,992,31744,1082401,2097183,4329604,17809936,32776456],[]),([6,992,31744,1082401,2097183,8659208,17809936,32641156],[]),([6,992,31744,1082401,2164831,4329604,17351184,32776456],[(72,0)]),([6,992,31744,1082401,2164831,4329604,17809936,32776456],[]),([6,992,31744,1082401,2164831,4329604,32776456,33538576],[]),([6,992,31744,1082401,2164831,5214340,17318431,32776456],[]),([6,992,31744,1082401,2164831,8659208,17351184,32641156],[]),([6,992,31744,1082401,2164831,8659208,17809936,32505860],[(72,0),(80,0)]),([6,992,31744,1082401,2164831,8659208,17809936,32641156],[]),([6,992,31744,1082401,2164831,8659208,17809936,32911756],[]),([6,992,31744,1082401,2164831,8659208,32641156,33538576],[(72,0)]),([6,992,31744,1082401,2164831,8659212,17809936,32505856],[(72,0)]),([6,992,31744,1082401,2164831,9412872,17318431,32641156],[]),([6,992,31744,1082401,2164831,12988812,17809936,32776456],[]),([6,992,31744,1082401,2164831,17809936,32641156,32776456],[]),([6,992,31744,1082401,2164831,17809936,32776456,32911756],[]),([6,992,31744,1082401,3115074,8659212,17318431,32505856],[]),([6,992,31744,1082401,3247231,4329604,17809936,32776456],[(72,0)]),([6,992,31744,1082401,3247231,8659208,17809936,32641156],[(72,0),(80,0)])]
def t11 : BT := .nd (blockTree b14) [6,31,1113121,2098144,4329604,8659208,17809936,32505856] (blockTree b15)
def t12 : BT := .nd t10 [6,31,1082401,2165730,3115074,4357252,17318416,32776456] t11
def t13 : BT := .nd t9 [6,31,32736,1082401,2165730,4329604,17809936,32776456] t12
def t14 : BT := .nd t6 [6,31,992,1113121,2164802,8659208,17809936,32505860] t13
def b16 : List Row := [([6,992,31744,1082431,2164802,5214340,17318431,32776456],[]),([6,992,31744,1082431,2164802,5214340,17809936,32776456],[]),([6,992,31744,1082431,2164802,5214340,32776456,33047056],[]),([6,992,31744,1082431,2164802,8659208,33047056,33525892],[(96,0)]),([6,992,31744,1082431,2164802,9412872,17318431,32641156],[]),([6,992,31744,1082431,2164802,9412872,17809936,32641156],[]),([6,992,31744,1082431,2164802,9412872,32641156,33047056],[]),([6,992,31744,1082431,3247203,4329604,9412872,33047056],[]),([6,992,31744,1082431,3247203,4329604,17809936,32776456],[]),([6,992,31744,1082431,3247203,5214340,8659208,33047056],[(96,0),(104,0)]),([6,992,31744,1082431,3247203,8659208,17809936,32641156],[]),([6,992,31744,1083361,2164831,4329604,17809936,32776456],[(56,0)]),([6,992,31744,3179553,4329604,8659208,17318431,33521664],[(96,0)]),([6,992,31744,3247203,4329604,8691976,17318431,32505856],[]),([6,992,31744,3247203,4362372,8659208,17318431,32505856],[]),([6,992,31748,1082401,3115074,8659208,17318431,32505856],[]),([6,992,32736,1082401,2164831,4329604,17809936,32776456],[(72,0)]),([6,992,32736,1082401,2164831,8659208,17809936,32641156],[]),([6,992,32768,3247203,4329604,8682760,17318431,32505856],[]),([6,992,32768,3247203,4357252,8659208,17318431,32505856],[(224,0)]),([6,992,1014750,4329604,8682760,17318431],[(1024,83425),(1024,67063)]),([6,992,1014750,4357252,8659208,17318431],[(1024,77281),(1024,67051)]),([6,992,1015808,1082401,2164802,8675596,17318431,32505856],[]),([6,992,1015808,1082401,2164802,8682764,17318431,32505856],[]),([6,992,1015808,1082401,2164802,13008268,17318431,32776456],[]),([6,992,1015808,1082401,2164831,4357252,17318431,32776456],[]),([6,992,1015808,1082401,2164831,8682760,17318431,32641156],[]),([6,992,1015808,1082401,3145728,4329604,8682760,17318431],[]),([6,992,1015808,1082401,3145728,4357252,8659208,17318431],[]),([6,992,1015808,1082431,2164802,4357252,17318431,32776456],[]),([6,992,1015808,1082431,2164802,8682760,17318431,32641156],[]),([6,992,1015808,1082431,2194498,4329604,32776456,33047056],[])]
def b17 : List Row := [([6,992,1015808,1113121,2164831,4329604,32776456,33047056],[]),([6,992,1015808,1113121,2164831,8659208,32641156,33047056],[]),([6,992,1015808,3179553,4329604,8682760,17318431,32505856],[]),([6,992,1015808,3179553,4357252,8659208,17318431,32505856],[]),([6,992,1081344,2164802,4329604,8682760,17318431,32505856],[]),([6,992,1082401,1082431,2194498,4329604,9412872,33047056],[(56,0)]),([6,992,1082401,1082431,2194498,5214340,8659208,33047056],[(56,0),(104,0)]),([6,992,1082401,1113121,2164831,4329604,17809936,32776456],[(56,0)]),([6,992,1082401,1113121,2164831,8659208,17809936,32641156],[(56,0),(104,0)]),([6,992,1082401,2097152,4329604,8682760,17318431,33521664],[(72,0)]),([6,992,1082401,2164802,4329604,8682760,17318431,32538624],[]),([6,992,1082401,2164802,4357252,8691976,17318431,32505856],[]),([6,992,1082401,2164802,4357252,9412872,17318431,32776456],[]),([6,992,1082401,2164802,4362372,8682760,17318431,32505856],[]),([6,992,1082401,2164802,5214340,8682760,17318431,32641156],[]),([6,992,1082401,2164802,9412872,13008268,17318431,32505856],[]),([6,992,1082401,2164831,4357252,9412872,17318431,32505856],[]),([6,992,1082401,2164831,5214340,8682760,17318431,32505856],[]),([6,992,1082401,2197570,4329604,8682760,17318431,32505856],[]),([6,992,1082401,2197570,4357252,8659208,17318431,32505856],[]),([6,992,1082401,3112960,4329604,8682760,17318431,32505856],[]),([6,992,1082401,3115074,4329604,8675592,17318431,32505856],[(96,0)]),([6,992,1082401,3115074,4329604,8682760,17318431,32505856],[]),([6,992,1082401,3115074,4330468,8682760,17318431,32505856],[]),([6,992,1082401,3115074,4357252,8659208,17318431,32505856],[]),([6,992,1082401,3115074,4357252,8682760,17318431,32505856],[]),([6,992,1082401,3115074,4358116,8659208,17318431,32505856],[]),([6,992,1082401,3115074,8682760,12988812,17318431,32505856],[]),([6,992,1082401,3115074,8682760,13008268,17318431,32505856],[]),([6,992,1082431,1113121,2164802,4329604,9412872,33047056],[]),([6,992,1082431,1113121,2164802,4329604,17809936,32776456],[]),([6,992,1082431,2164802,4357252,9412872,17318431,32505856],[])]
def t15 : BT := .nd (blockTree b16) [6,992,1015808,1082431,2194498,8659208,32641156,33047056] (blockTree b17)
def b18 : List Row := [([6,992,1082431,2194498,4329604,9412872,32505856,33047056],[]),([6,992,1113121,2164831,4329604,17809936,32505856,32776456],[]),([6,992,3179553,4329604,8682760,17318431],[(1024,110049),(1024,99819)]),([6,992,3179553,4357252,8659208,17318431],[(1024,77281),(1024,67051)]),([6,992,4329604,8682760,16236000,32539681],[(1024,491602),(1024,67063)]),([6,992,4329604,8682760,17318431,32538624],[(1024,83449),(1024,66039)]),([6,992,4329604,8682760,17318431,32539681],[(1024,83425),(1024,67063)]),([6,992,4329604,8682760,17383967],[(1024,66034),(1024,98795),(1024,83425),(1025,88761),(1025,268984)]),([6,992,4329604,8748296,17318431],[(1024,66034),(1024,98795),(1024,83425),(1025,88761),(1025,268984)]),([6,992,4329604,13008268,17318431,32539681],[(1024,99819),(1024,78305),(1025,89785)]),([6,992,4329604,17318431,24871671,32539681],[(1024,83425),(1024,67063)]),([6,992,4330468,8682760,17318431,32539681],[(1024,67063),(1024,83425),(1025,285368)]),([6,992,4357252,8659208,16236000,32539681],[(1024,491596),(1024,67051)]),([6,992,4357252,8659208,17318431,32539681],[(1024,77281),(1024,67051)]),([6,992,4357252,8659208,17383967],[(1024,66027),(1024,98803),(1024,76257),(1025,122553),(1025,301753)]),([6,992,4357252,8682760,17318431,32539681],[(1024,83425),(1024,67063)]),([6,992,4357252,8724744,17318431],[(1024,66027),(1024,98801),(1024,76257),(1025,122553),(1025,301753)]),([6,992,4357252,12988812,17318431,32539681],[(1024,78305),(1024,99832)]),([6,992,4357252,13008268,17318431,32539681],[(1024,99832),(1024,77281),(1025,483001)]),([6,992,4357252,17318431,24895223,32539681],[(1024,77281),(1024,67051)]),([6,992,4358116,8659208,17318431,32539681],[(1024,67051),(1024,77281),(1025,285368)]),([6,992,4395140,8682760,17318431],[(1024,66033),(1024,98795),(1024,82401),(1025,88761),(1025,268984)]),([6,992,4422788,8659208,17318431],[(1024,66027),(1024,98803),(1024,76257),(1025,122553),(1025,301753)]),([6,992,8659208,17318431,29197179,32539681],[(1024,77281),(1024,99832)]),([6,992,8682760,12988812,17318431,32539681],[(1024,67063),(1024,83425)]),([6,992,8682760,13008268,17318431,32539681],[(1024,67063),(1024,83425),(1025,267960)]),([6,992,8682760,17318431,29224827,32539681],[(1024,83425),(1024,99819)]),([6,996,1015808,1082401,2164802,8682760,17318431,32505856],[]),([6,31744,1015808,1082431,2165730,4329604,32776456,33047056],[]),([6,31744,1015808,1083361,2164831,4329604,17809936,32776456],[]),([6,31744,1015808,1083361,2164831,4329604,32776456,33047056],[]),([6,31744,1082401,1083361,2164831,4329604,17809936,32776456],[(56,0),(104,0)])]
def b19 : List Row := [([6,31744,1082401,2164802,4330468,9412872,17318431,32776456],[]),([6,31744,1083361,2164831,4329604,17809936,32776456],[(57,0),(133,0)]),([6,31744,4330468,8682760,17318431,32539681],[(1024,67046),(1024,72161),(1025,483001)]),([6,31744,4330468,8724744,17318431],[(1024,66022),(1024,98801),(1024,71137),(1025,122553),(1025,318137)]),([6,31744,4330468,17318431,24895223,32539681],[(1024,72161),(1024,67046)]),([6,1015808,1082401,2164802,4330468,8682760,17318431,32776456],[]),([6,1015808,1082401,2165730,4330468,8682760,17318431,32505856],[]),([7,4,31,992,31744,1082401,2164802,9412872,33047056],[]),([7,4,31,992,31744,1082401,2164802,17809936,32776456],[]),([7,4,31,992,1015808,1082401,2194498,8659208,33047056],[]),([7,4,31,992,1015808,1113121,2164802,8659208,33047056],[]),([7,4,31,992,1082401,2194498,9412872,17318416,32505856],[]),([7,4,31,992,1082401,3115074,8682760,17318416,32505856],[]),([7,4,31,992,1113121,2164802,8659208,17809936,32505856],[]),([7,4,31,31744,1015808,1082401,2165730,8659208,33047056],[]),([7,4,31,31744,1015808,1082401,2165730,17318416,32776456],[]),([7,4,31,31744,1015808,1083361,2164802,8659208,33047056],[]),([7,4,31,31744,1015808,1083361,2164802,17318416,32776456],[]),([7,4,31,31744,1083361,2164802,8659208,17809936,32505856],[]),([7,4,31,31744,1083361,2164802,9412872,17318416,32505856],[]),([7,4,31,1015808,1083361,2194498,8659208,17318416,32505856],[(72,0),(168,0),(272,0)]),([7,4,31,1015808,1113121,2165730,8659208,17318416,32505856],[(72,0),(168,0),(272,0)]),([7,4,992,31744,1015808,1082401,2164831,17318416,32776456],[(272,0)]),([7,4,992,31744,1015808,1082431,2164802,17318416,32776456],[(96,0),(272,0)]),([7,4,992,31744,1082401,2164831,8659208,17809936,32505856],[]),([7,4,992,31744,1082401,3115074,8659208,17318431,32505856],[(56,0)]),([7,4,992,31744,1082431,2164802,9412872,17318416,32505856],[(168,0),(272,0)]),([7,4,992,1015808,1082401,2164802,8682760,17318431,32505856],[]),([7,4,992,1015808,1082431,2194498,8659208,17318416,32505856],[(72,0),(168,0),(272,0)]),([7,4,992,1015808,1113121,2164831,8659208,17318416,32505856],[(168,0),(272,0)]),([7,4,31744,1015808,1082431,2165730,8659208,17318416,32505856],[(72,0),(168,0),(272,0)])]
def t16 : BT := .nd (blockTree b18) [6,31744,1082401,2164802,4330468,8691976,17318431,32505856] (blockTree b19)
def t17 : BT := .nd t15 [6,992,1082431,2164802,5214340,8682760,17318431,32505856] t16
def b20 : List Row := [([7,12,992,31744,1015808,1082401,2164802,8659208,33047056],[]),([7,12,992,31744,1015808,1082401,2164802,17318416,32776456],[]),([7,12,992,31744,1082401,2164802,8659208,17809936,32505856],[]),([7,12,992,31744,1082401,2164802,9412872,17318416,32505856],[]),([7,12,992,31744,1082401,3115074,8659208,17318416,32505856],[]),([7,12,992,1015808,1082401,2164802,8682760,17318416,32505856],[]),([7,12,992,1015808,1082401,2194498,8659208,17318416,32505856],[]),([7,12,992,1015808,1113121,2164802,8659208,17318416,32505856],[]),([7,12,31744,1015808,1082401,2165730,8659208,17318416,32505856],[]),([7,12,31744,1015808,1083361,2164802,8659208,17318416,32505856],[]),([7,31,287,1082401,3115074,17318416,32505856],[(1024,496948),(1024,302149),(1025,98968),(1025,266702)]),([7,31,992,31744,32768,3145728,4329604,8659208,17318416],[(176,0)]),([7,31,992,31744,32768,3247203,4329604,8659208,33047056],[]),([7,31,992,31744,32768,3247203,4329604,17318416,32776456],[(128,0)]),([7,31,992,31744,32768,3247203,8659208,17318416,32641156],[(128,0)]),([7,31,992,31744,1015808,1082401,2164802,8659212,33047056],[]),([7,31,992,31744,1015808,1082401,2164802,17318416,32776460],[(128,0),(168,0)]),([7,31,992,31744,1015808,3179553,4329604,8659208,33047056],[]),([7,31,992,31744,1015808,3179553,4329604,17318416,32776456],[(128,0)]),([7,31,992,31744,1015808,3179553,8659208,17318416,32641156],[(128,0)]),([7,31,992,31744,1015812,1082401,2164802,8659208,33047056],[]),([7,31,992,31744,1015812,1082401,2164802,17318416,32776456],[(128,0)]),([7,31,992,31744,1081344,2164802,4329604,8659208,33047056],[]),([7,31,992,31744,1081344,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,992,31744,1081344,2164802,8659208,17318416,32641156],[(128,0)]),([7,31,992,31744,1082401,2097152,4329604,8659208,33538576],[]),([7,31,992,31744,1082401,2097152,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2097152,4329604,17318416,33530120],[(96,0),(104,0),(128,0)]),([7,31,992,31744,1082401,2097152,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,2097152,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2097152,5214340,17318416,32776456],[(96,0),(128,0)]),([7,31,992,31744,1082401,2097152,8659208,17318416,33525892],[(96,0),(128,0)])]
def b21 : List Row := [([7,31,992,31744,1082401,2097152,9412872,17318416,32641156],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,4329604,8659208,33079824],[]),([7,31,992,31744,1082401,2164802,4329604,8691976,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,17318416,32809224],[(96,0),(104,0),(128,0)]),([7,31,992,31744,1082401,2164802,4329604,17351184,32776456],[]),([7,31,992,31744,1082401,2164802,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,4329604,32776456,33538576],[]),([7,31,992,31744,1082401,2164802,4329604,33047056,33530120],[]),([7,31,992,31744,1082401,2164802,4330468,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4330468,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,4357252,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4357252,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,4362372,8659208,33047056],[]),([7,31,992,31744,1082401,2164802,4362372,17318416,32776456],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,8682760,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,17318416,32776456],[(96,0)]),([7,31,992,31744,1082401,2164802,5214340,17318431,32776456],[]),([7,31,992,31744,1082401,2164802,5214340,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,5214340,32776456,33047056],[]),([7,31,992,31744,1082401,2164802,8659208,13611404,33047056],[]),([7,31,992,31744,1082401,2164802,8659208,17318416,32673924],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,8659208,17351184,32641156],[]),([7,31,992,31744,1082401,2164802,8659208,17809936,32505860],[]),([7,31,992,31744,1082401,2164802,8659208,17809936,32641156],[]),([7,31,992,31744,1082401,2164802,8659208,17809936,32911756],[]),([7,31,992,31744,1082401,2164802,8659208,32641156,33538576],[]),([7,31,992,31744,1082401,2164802,8659208,33047056,33525892],[]),([7,31,992,31744,1082401,2164802,8659212,17809936,32505856],[])]
def t18 : BT := .nd (blockTree b20) [7,31,992,31744,1082401,2097152,8659208,17809936,32641156] (blockTree b21)
def b22 : List Row := [([7,31,992,31744,1082401,2164802,8691976,17318416,32641156],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,9412872,12988812,33047056],[]),([7,31,992,31744,1082401,2164802,9412872,13611404,33047056],[]),([7,31,992,31744,1082401,2164802,9412872,17318416,32505860],[(96,0)]),([7,31,992,31744,1082401,2164802,9412872,17318416,32641156],[(96,0)]),([7,31,992,31744,1082401,2164802,9412872,17318416,32911756],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,9412872,17318431,32641156],[]),([7,31,992,31744,1082401,2164802,9412872,17809936,32641156],[]),([7,31,992,31744,1082401,2164802,9412872,32641156,33047056],[]),([7,31,992,31744,1082401,2164802,9412876,17318416,32505856],[(96,0)]),([7,31,992,31744,1082401,2164802,12988812,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,13611404,17318416,32776456],[(96,0)]),([7,31,992,31744,1082401,2164802,17318416,32641156,33530120],[(96,0)]),([7,31,992,31744,1082401,2164802,17318416,32776456,33525892],[(96,0)]),([7,31,992,31744,1082401,2164802,17318416,32776456,33534348],[(96,0)]),([7,31,992,31744,1082401,2164802,17318416,32911756,33530120],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,17809936,32641156,32776456],[]),([7,31,992,31744,1082401,2164802,17809936,32776456,32911756],[]),([7,31,992,31744,1082401,2164831,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,2164831,5214340,17318416,32776456],[(96,0)]),([7,31,992,31744,1082401,2164831,8659208,17809936,32641156],[]),([7,31,992,31744,1082401,2164831,9412872,17318416,32641156],[(96,0)]),([7,31,992,31744,1082401,2165730,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2165730,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,2165730,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2165730,5214340,17318416,32776456],[(96,0)]),([7,31,992,31744,1082401,2194498,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2194498,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2197570,4329604,8659208,33047056],[]),([7,31,992,31744,1082401,2197570,4329604,17318416,32776456],[]),([7,31,992,31744,1082401,2197570,8659208,17318416,32641156],[]),([7,31,992,31744,1082401,3115074,4329604,32776456,33047056],[])]
def b23 : List Row := [([7,31,992,31744,1082401,3115074,8659208,32641156,33047056],[]),([7,31,992,31744,1082401,3115074,8659212,17318416,32505856],[]),([7,31,992,31744,1082401,3115074,17318416,32641156,32776456],[]),([7,31,992,31744,1082401,3145728,4329604,8659208,17809936],[]),([7,31,992,31744,1082401,3145728,4329604,9412872,17318416],[(96,0),(104,0)]),([7,31,992,31744,1082401,3145728,5214340,8659208,17318416],[(96,0)]),([7,31,992,31744,1082401,3247203,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,3247203,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,3247203,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,3247203,5214340,17318416,32776456],[(96,0)]),([7,31,992,31744,1082401,3247203,8659208,17809936,32641156],[]),([7,31,992,31744,1082401,3247203,9412872,17318416,32641156],[(96,0)]),([7,31,992,31744,1082431,2164802,5214340,17318416,32776456],[(96,0),(128,0)]),([7,31,992,31744,1082431,2164802,9412872,17318416,32641156],[(96,0),(128,0)]),([7,31,992,31744,1083361,2164802,4329604,9412872,33047056],[]),([7,31,992,31744,1083361,2164802,4329604,17809936,32776456],[]),([7,31,992,31744,3179553,4329604,8659208,17318416,33521664],[(96,0),(104,0),(112,0),(136,0)]),([7,31,992,31744,3179553,4329604,8659208,17809936,32505856],[]),([7,31,992,31744,3179553,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([7,31,992,31744,3179553,5214340,8659208,17318416,32505856],[(96,0)]),([7,31,992,31744,3247203,4329604,8659208,17351184,32505856],[]),([7,31,992,31744,3247203,4329604,8691976,17318416,32505856],[(96,0),(104,0)]),([7,31,992,31744,3247203,4362372,8659208,17318416,32505856],[(96,0)]),([7,31,992,31744,12988812,25977624,32539681],[(1024,269817),(1024,67022)]),([7,31,992,31748,1015808,1082401,2164802,8659208,33047056],[]),([7,31,992,31748,1015808,1082401,2164802,17318416,32776456],[]),([7,31,992,31748,1082401,2164802,8659208,17809936,32505856],[]),([7,31,992,31748,1082401,2164802,9412872,17318416,32505856],[]),([7,31,992,31748,1082401,3115074,8659208,17318416,32505856],[]),([7,31,992,32736,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,32736,1082401,2164802,4329604,17809936,32776456],[])]
def t19 : BT := .nd (blockTree b22) [7,31,992,31744,1082401,3115074,8659208,17318416,32505860] (blockTree b23)
def t20 : BT := .nd t18 [7,31,992,31744,1082401,2164802,8682760,17809936,32641156] t19
def t21 : BT := .nd t17 [7,4,31744,1015808,1083361,2164831,8659208,17318416,32505856] t20
def b24 : List Row := [([7,31,992,32736,1082401,2164802,5214340,17318416,32776456],[(96,0),(236,0)]),([7,31,992,32736,1082401,2164802,8659208,17809936,32641156],[]),([7,31,992,32736,1082401,2164802,9412872,17318416,32641156],[(96,0),(236,0)]),([7,31,992,32768,1082401,2164802,4357252,17318416,32776456],[]),([7,31,992,32768,1082401,2164802,8682760,17318416,32641156],[]),([7,31,992,32768,1082401,2194498,4329604,8659208,33047056],[]),([7,31,992,32768,1113121,2164802,4329604,8659208,33047056],[]),([7,31,992,32768,3247203,4329604,8682760,17318416,32505856],[]),([7,31,992,32768,3247203,4357252,8659208,17318416,32505856],[(104,0),(288,0)]),([7,31,992,1014750,4329604,8682760,17318416],[(1024,99819),(1024,67063)]),([7,31,992,1014750,4357252,8659208,17318416],[(1024,67051),(1024,77281)]),([7,31,992,1015808,1082401,2097152,4357252,17318416,32776456],[(104,0),(128,0)]),([7,31,992,1015808,1082401,2097152,8682760,17318416,32641156],[(128,0)]),([7,31,992,1015808,1082401,2113536,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,2128896,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,2164802,4345988,17318416,32776456],[(96,0),(104,0),(128,0),(136,0)]),([7,31,992,1015808,1082401,2164802,4357252,8682760,33047056],[]),([7,31,992,1015808,1082401,2164802,4357252,17318416,32776456],[]),([7,31,992,1015808,1082401,2164802,4357252,17318431,32776456],[]),([7,31,992,1015808,1082401,2164802,4358116,17318416,32776456],[]),([7,31,992,1015808,1082401,2164802,8675592,17318416,32641156],[(96,0),(128,0)]),([7,31,992,1015808,1082401,2164802,8682760,17318416,32505860],[]),([7,31,992,1015808,1082401,2164802,8682760,17318416,32641156],[]),([7,31,992,1015808,1082401,2164802,8682760,17318416,32911756],[(96,0),(128,0)]),([7,31,992,1015808,1082401,2164802,8682760,17318431,32641156],[]),([7,31,992,1015808,1082401,2164802,8682764,17318416,32505856],[]),([7,31,992,1015808,1082401,2164802,13008268,17318416,32776456],[(104,0)]),([7,31,992,1015808,1082401,2164831,4357252,17318416,32776456],[(96,0)]),([7,31,992,1015808,1082401,2164831,8682760,17318416,32641156],[(96,0)]),([7,31,992,1015808,1082401,2165730,4357252,17318416,32776456],[]),([7,31,992,1015808,1082401,2181186,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,2181186,4329604,17318416,32776456],[(96,0),(104,0),(136,0)])]
def b25 : List Row := [([7,31,992,1015808,1082401,2194498,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,2194498,4329604,8682760,33047056],[]),([7,31,992,1015808,1082401,2194498,4329604,9412872,33047056],[]),([7,31,992,1015808,1082401,2194498,4329604,32776456,33047056],[]),([7,31,992,1015808,1082401,2194498,4330468,8659208,33047056],[]),([7,31,992,1015808,1082401,2194498,4357252,8659208,33047056],[]),([7,31,992,1015808,1082401,2194498,5214340,8659208,33047056],[]),([7,31,992,1015808,1082401,2194498,8659208,12988812,33047056],[]),([7,31,992,1015808,1082401,2194498,8659208,17318416,32505860],[(96,0),(104,0)]),([7,31,992,1015808,1082401,2194498,8659208,32641156,33047056],[]),([7,31,992,1015808,1082401,2194498,8659212,17318416,32505856],[(96,0),(104,0)]),([7,31,992,1015808,1082401,2194498,17318416,32641156,32776456],[(96,0)]),([7,31,992,1015808,1082401,2195426,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,3145728,4329604,8682760,17318416],[]),([7,31,992,1015808,1082401,3145728,4357252,8659208,17318416],[(104,0)]),([7,31,992,1015808,1082401,3247203,4357252,17318416,32776456],[]),([7,31,992,1015808,1082401,3247203,8682760,17318416,32641156],[]),([7,31,992,1015808,1082401,3275875,4329604,8659208,33047056],[(96,0)]),([7,31,992,1015808,1082431,2164802,4357252,17318416,32776456],[(128,0)]),([7,31,992,1015808,1082431,2164802,8682760,17318416,32641156],[(128,0)]),([7,31,992,1015808,1083361,2164802,4357252,17318416,32776456],[]),([7,31,992,1015808,1083361,2194498,4329604,8659208,33047056],[]),([7,31,992,1015808,1098785,2164802,4329604,8659208,33047056],[]),([7,31,992,1015808,1098785,2164802,4329604,17318416,32776456],[(104,0),(128,0),(136,0)]),([7,31,992,1015808,1098785,2164802,8659208,17318416,32641156],[(128,0)]),([7,31,992,1015808,1113121,2097152,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,2164802,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,2164802,4329604,8682760,33047056],[]),([7,31,992,1015808,1113121,2164802,4329604,9412872,33047056],[]),([7,31,992,1015808,1113121,2164802,4329604,32776456,33047056],[]),([7,31,992,1015808,1113121,2164802,4330468,8659208,33047056],[])]
def t22 : BT := .nd (blockTree b24) [7,31,992,1015808,1082401,2181186,8659208,17318416,32641156] (blockTree b25)
def b26 : List Row := [([7,31,992,1015808,1113121,2164802,5214340,8659208,33047056],[]),([7,31,992,1015808,1113121,2164802,8659208,12988812,33047056],[]),([7,31,992,1015808,1113121,2164802,8659208,32641156,33047056],[]),([7,31,992,1015808,1113121,2164802,8659212,17318416,32505856],[(128,0),(136,0)]),([7,31,992,1015808,1113121,2164802,17318416,32641156,32776456],[(128,0)]),([7,31,992,1015808,1113121,2165730,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,2194498,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,3247203,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,3247203,4329604,17318416,32776456],[(128,0),(136,0)]),([7,31,992,1015808,1113121,3247203,8659208,17318416,32641156],[(128,0)]),([7,31,992,1015808,1113121,3275875,4329604,8659208,33047056],[]),([7,31,992,1015808,1114081,2164802,4329604,8659208,33047056],[]),([7,31,992,1015808,3179553,4329604,8682760,17318416,32505856],[]),([7,31,992,1015808,3179553,4357252,8659208,17318416,32505856],[(104,0)]),([7,31,992,1015812,1082401,2164802,8682760,17318416,32505856],[]),([7,31,992,1015812,1082401,2194498,8659208,17318416,32505856],[(96,0),(104,0)]),([7,31,992,1081344,2164802,4329604,8682760,17318416,32505856],[]),([7,31,992,1082401,1113121,2164802,4329604,9412872,33047056],[]),([7,31,992,1082401,1113121,2164802,4329604,17809936,32776456],[]),([7,31,992,1082401,1113121,2164802,5214340,8659208,33047056],[(72,0)]),([7,31,992,1082401,1113121,2164802,5214340,17318416,32776456],[(72,0),(80,0)]),([7,31,992,1082401,1113121,2164802,8659208,17809936,32641156],[(72,0)]),([7,31,992,1082401,1113121,2164802,9412872,17318416,32641156],[(72,0),(80,0)]),([7,31,992,1082401,2097152,4329604,8682760,17318416,33521664],[(96,0),(104,0)]),([7,31,992,1082401,2097152,4357252,9412872,17318416,32505856],[(80,0),(96,0)]),([7,31,992,1082401,2097152,5214340,8682760,17318416,32505856],[(96,0)]),([7,31,992,1082401,2128896,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2128896,4329604,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2128896,5214340,8659208,17318416,32505856],[(72,0)]),([7,31,992,1082401,2164802,2194498,4329604,9412872,33047056],[]),([7,31,992,1082401,2164802,2194498,5214340,8659208,33047056],[]),([7,31,992,1082401,2164802,2194498,5214340,17318416,32776456],[(72,0)])]
def b27 : List Row := [([7,31,992,1082401,2164802,3115074,4357252,17318416,32776456],[]),([7,31,992,1082401,2164802,3115074,8682760,17318416,32641156],[]),([7,31,992,1082401,2164802,4329604,8682760,17318416,32538624],[]),([7,31,992,1082401,2164802,4329604,8682760,17351184,32505856],[]),([7,31,992,1082401,2164802,4329604,8682760,17809936,33047056],[]),([7,31,992,1082401,2164802,4345988,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2164802,4357252,5214340,17318416,32776456],[(72,0),(96,0)]),([7,31,992,1082401,2164802,4357252,8659208,17351184,32505856],[]),([7,31,992,1082401,2164802,4357252,8659208,17809936,33047056],[]),([7,31,992,1082401,2164802,4357252,8682760,17809936,32505856],[]),([7,31,992,1082401,2164802,4357252,8691976,17318416,32505856],[(80,0),(104,0)]),([7,31,992,1082401,2164802,4357252,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,2164802,4357252,9412872,17318416,32641156],[(72,0)]),([7,31,992,1082401,2164802,4357252,9412872,17318416,32776456],[(80,0)]),([7,31,992,1082401,2164802,4357252,9412872,17318416,33047056],[(80,0)]),([7,31,992,1082401,2164802,4357252,9412872,17318431,32505856],[]),([7,31,992,1082401,2164802,4357252,17318416,17809936,32776456],[(80,0)]),([7,31,992,1082401,2164802,4357252,17318416,32505856,33530120],[(80,0)]),([7,31,992,1082401,2164802,4357252,17318416,32776456,33521664],[(80,0)]),([7,31,992,1082401,2164802,4357252,17318416,32776456,33530120],[(80,0)]),([7,31,992,1082401,2164802,4358116,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,2164802,4362372,8682760,17318416,32505856],[]),([7,31,992,1082401,2164802,5214340,8675592,17318416,32505856],[(72,0),(104,0)]),([7,31,992,1082401,2164802,5214340,8682760,17318416,32505856],[]),([7,31,992,1082401,2164802,5214340,8682760,17318416,32641156],[]),([7,31,992,1082401,2164802,5214340,8682760,17318416,32776456],[(72,0)]),([7,31,992,1082401,2164802,5214340,8682760,17318416,33047056],[]),([7,31,992,1082401,2164802,5214340,8682760,17318431,32505856],[]),([7,31,992,1082401,2164802,8682760,9412872,17318416,32641156],[(72,0),(96,0)]),([7,31,992,1082401,2164802,8682760,13611404,17318416,32505856],[(72,0)]),([7,31,992,1082401,2164802,8682760,17318416,17809936,32641156],[])]
def t23 : BT := .nd (blockTree b26) [7,31,992,1082401,2164802,2194498,9412872,17318416,32641156] (blockTree b27)
def t24 : BT := .nd t22 [7,31,992,1015808,1113121,2164802,4357252,8659208,33047056] t23
def b28 : List Row := [([7,31,992,1082401,2164802,8682760,17318416,32641156,33521664],[]),([7,31,992,1082401,2164802,8682760,17318416,32641156,33525892],[]),([7,31,992,1082401,2164802,9412872,13008268,17318416,32505856],[(80,0),(104,0)]),([7,31,992,1082401,2164831,4357252,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2164831,5214340,8682760,17318416,32505856],[(72,0)]),([7,31,992,1082401,2165730,4357252,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,2165730,5214340,8682760,17318416,32505856],[]),([7,31,992,1082401,2181186,4329604,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2194498,3115074,4329604,8659208,33047056],[]),([7,31,992,1082401,2194498,3115074,4329604,17318416,32776456],[]),([7,31,992,1082401,2194498,3115074,8659208,17318416,32641156],[]),([7,31,992,1082401,2194498,4329604,5214340,8659208,33047056],[]),([7,31,992,1082401,2194498,4329604,8659208,9412872,33047056],[]),([7,31,992,1082401,2194498,4329604,8659208,17351184,32505856],[]),([7,31,992,1082401,2194498,4329604,8659208,17809936,33047056],[]),([7,31,992,1082401,2194498,4329604,8659208,33047056,33521664],[(72,0)]),([7,31,992,1082401,2194498,4329604,8659208,33047056,33538576],[]),([7,31,992,1082401,2194498,4329604,8682760,17809936,32505856],[]),([7,31,992,1082401,2194498,4329604,8691976,17318416,32505856],[(72,0),(80,0),(136,0)]),([7,31,992,1082401,2194498,4329604,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2194498,4329604,9412872,17318416,33047056],[(80,0)]),([7,31,992,1082401,2194498,4329604,9412872,32505856,33047056],[]),([7,31,992,1082401,2194498,4329604,9412872,33047056],[]),([7,31,992,1082401,2194498,4329604,17318416,32505856,33530120],[(72,0),(80,0)]),([7,31,992,1082401,2194498,4329604,17318416,32776456,33521664],[(72,0),(80,0)]),([7,31,992,1082401,2194498,4330468,9412872,17318416,32505856],[(80,0),(104,0)]),([7,31,992,1082401,2194498,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,4357252,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,2194498,5214340,8659208,17318416,32505856],[(72,0)]),([7,31,992,1082401,2194498,5214340,8659208,17318416,33047056],[]),([7,31,992,1082401,2194498,5214340,8659208,32505856,33047056],[(72,0)]),([7,31,992,1082401,2194498,5214340,8659208,33047056],[])]
def b29 : List Row := [([7,31,992,1082401,2194498,5214340,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2194498,5214340,17318416,32505856,32776456],[(72,0)]),([7,31,992,1082401,2194498,5214340,33047056],[(1024,470117),(1024,482402)]),([7,31,992,1082401,2194498,8659208,13611404,17318416,32505856],[(72,0)]),([7,31,992,1082401,2194498,8659208,17318416,32505856,33525892],[(72,0)]),([7,31,992,1082401,2194498,8659208,17318416,32641156,33521664],[(72,0),(80,0)]),([7,31,992,1082401,2194498,8659231,33047056],[(1024,302149),(1024,281062),(1025,266536)]),([7,31,992,1082401,2194498,9412872,12988812,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2194498,9412872,13611404,17318416,32505856],[(72,0),(80,0)]),([7,31,992,1082401,2194498,9412872,17318416,32505856,32641156],[(72,0),(80,0)]),([7,31,992,1082401,2194498,9412872,33047056],[(1024,302149),(1024,481346)]),([7,31,992,1082401,2195426,4329604,9412872,17318416,32505856],[(72,0),(80,0),(136,0)]),([7,31,992,1082401,2197570,4329604,8682760,17318416,32505856],[]),([7,31,992,1082401,2197570,4357252,8659208,17318416,32505856],[]),([7,31,992,1082401,3112960,4329604,8682760,17318416,32505856],[]),([7,31,992,1082401,3115074,4329604,8675592,17318416,32505856],[(136,0)]),([7,31,992,1082401,3115074,4329604,8682760,17318416,32505856],[]),([7,31,992,1082401,3115074,4329604,8682760,17318431,32505856],[]),([7,31,992,1082401,3115074,4330468,8682760,17318416,32505856],[]),([7,31,992,1082401,3115074,4357252,8659208,17318416,32505856],[]),([7,31,992,1082401,3115074,4357252,8659208,17318431,32505856],[]),([7,31,992,1082401,3115074,4357252,8682760,17318416,32505856],[]),([7,31,992,1082401,3115074,4357252,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,3115074,4357252,17318416,32505856,32776456],[]),([7,31,992,1082401,3115074,4358116,8659208,17318416,32505856],[]),([7,31,992,1082401,3115074,5214340,8682760,17318416,32505856],[]),([7,31,992,1082401,3115074,8682760,12988812,17318416,32505856],[]),([7,31,992,1082401,3115074,8682760,13008268,17318416,32505856],[]),([7,31,992,1082401,3115074,8682760,17318416,32505856,32641156],[]),([7,31,992,1082401,3247203,4357252,9412872,17318416,32505856],[(80,0)]),([7,31,992,1082401,3247203,5214340,8682760,17318416,32505856],[])]
def t25 : BT := .nd (blockTree b28) [7,31,992,1082401,2194498,5214340,8682760,17318416,32505856] (blockTree b29)
def b30 : List Row := [([7,31,992,1082401,4357252,25977624,32776456],[(1024,102862),(1024,67051),(1025,99001)]),([7,31,992,1082401,8682760,21648020,32641156],[(1024,99819),(1024,69928),(1025,66233)]),([7,31,992,1082401,13008268,17318416,32641156],[(1024,99819),(1024,78305),(1025,66232),(1025,89785)]),([7,31,992,1082401,13008268,17318416,32776456],[(1024,67051),(1024,77281),(1025,99000),(1025,122553)]),([7,31,992,1082431,2164802,4357252,9412872,17318416,32505856],[(96,0)]),([7,31,992,1082431,2164802,5214340,8682760,17318416,32505856],[(96,0)]),([7,31,992,1082431,2194498,4329604,9412872,17318416,32505856],[(72,0)]),([7,31,992,1083361,2164802,4357252,9412872,17318416,32505856],[(80,0),(104,0),(136,0)]),([7,31,992,1083361,2194498,4329604,9412872,17318416,32505856],[(80,0),(104,0),(136,0)]),([7,31,992,1098785,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,1098785,2164802,4329604,9412872,17318416,32505856],[(80,0)]),([7,31,992,1113121,2097152,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,17351184,32505856],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,17809936,33047056],[]),([7,31,992,1113121,2164802,4329604,8659208,32505856,33538576],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,33047056,33521664],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,33047056,33538576],[]),([7,31,992,1113121,2164802,4329604,8682760,17809936,32505856],[]),([7,31,992,1113121,2164802,4329604,9412872,17809936,32505856],[]),([7,31,992,1113121,2164802,4329604,17318416,32776456,33521664],[(96,0),(104,0)]),([7,31,992,1113121,2164802,4329604,17809936,32505856,32776456],[]),([7,31,992,1113121,2164802,4330468,8659208,17809936,32505856],[]),([7,31,992,1113121,2164802,4357252,8659208,17809936,32505856],[]),([7,31,992,1113121,2164802,5214340,8659208,17809936,32505856],[]),([7,31,992,1113121,2164802,5214340,9412872,17318416,32505856],[]),([7,31,992,1113121,2164802,8659208,12988812,17809936,32505856],[(96,0)]),([7,31,992,1113121,2164802,8659208,17809936,32505856,32641156],[(96,0)]),([7,31,992,1113121,2164831,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,1113121,2165730,4329604,8659208,17809936,32505856],[]),([7,31,992,1113121,2194498,4329604,8659208,17809936,32505856],[]),([7,31,992,1113121,3115074,4329604,8659208,17809936,32505856],[])]
def b31 : List Row := [([7,31,992,1113121,3247203,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,1113121,3247203,4329604,9412872,17318416,32505856],[]),([7,31,992,1113121,3275875,4329604,8659208,17809936,32505856],[]),([7,31,992,1114081,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,992,3179553,4329604,8682760,17318416],[(1024,99819),(1024,83425)]),([7,31,992,3179553,4357252,8659208,17318416],[(1024,281062),(1024,67051)]),([7,31,992,3247203,4357252,17318416,32539681],[(1024,515170),(1024,78305)]),([7,31,992,3247203,8682760,17318416,32539681],[(1024,269803),(1024,83425)]),([7,31,992,4329604,8682760,16236015,32539681],[(1024,516391),(1024,67063)]),([7,31,992,4329604,8682760,17318416,32538624],[(1024,66039),(1024,98808)]),([7,31,992,4329604,8682760,17318416,32539681],[(1024,99819),(1024,67063)]),([7,31,992,4329604,8682760,17318431,32539681],[(1024,301561),(1024,67063),(1025,88761)]),([7,31,992,4329604,8682760,17383952],[(1024,66034),(1024,98795),(1024,83425),(1025,67255),(1025,268984)]),([7,31,992,4329604,8682760,21648020,32539681],[(1024,99819),(1024,69928),(1025,66233)]),([7,31,992,4329604,8748296,17318416],[(1024,66034),(1024,98795),(1024,83425),(1025,67255),(1025,268984)]),([7,31,992,4329604,13008268,17318416,32539681],[(1024,99819),(1024,78305),(1025,66232)]),([7,31,992,4329604,17318416,24871671,32539681],[(1024,501858),(1024,67063)]),([7,31,992,4330468,8682760,17318416,32539681],[(1024,67063),(1024,83425),(1025,285368)]),([7,31,992,4357252,8659208,16236015,32539681],[(1024,516391),(1024,67051)]),([7,31,992,4357252,8659208,17318416,32539681],[(1024,67051),(1024,77281)]),([7,31,992,4357252,8659208,17318431,32539681],[(1024,301561),(1024,67051),(1025,88761)]),([7,31,992,4357252,8659208,17383952],[(1024,66027),(1024,98803),(1024,76257),(1025,67255),(1025,268984)]),([7,31,992,4357252,8659208,25977624,32539681],[(1024,301561),(1024,67051),(1025,99001)]),([7,31,992,4357252,8682760,17318416,32539681],[(1024,99832),(1024,67063)]),([7,31,992,4357252,8724744,17318416],[(1024,66027),(1024,98801),(1024,76257),(1025,67255),(1025,268984)]),([7,31,992,4357252,12988812,17318416,32539681],[(1024,99832),(1024,78305)]),([7,31,992,4357252,13008268,17318416,32539681],[(1024,99832),(1024,77281),(1025,66232)]),([7,31,992,4357252,17318416,24895223,32539681],[(1024,515170),(1024,67051)]),([7,31,992,4357252,17318416,25977624,32539681],[(1024,99832),(1024,67051),(1025,300729)]),([7,31,992,4358116,8659208,17318416,32539681],[(1024,67051),(1024,77281),(1025,285368)]),([7,31,992,4395140,8682760,17318416],[(1024,66033),(1024,98795),(1024,82401),(1025,67255),(1025,268984)])]
def t26 : BT := .nd (blockTree b30) [7,31,992,1113121,3115074,4329604,9412872,17318416,32505856] (blockTree b31)
def t27 : BT := .nd t25 [7,31,992,1082401,3275875,4329604,9412872,17318416,32505856] t26
def t28 : BT := .nd t24 [7,31,992,1082401,2164802,8682760,17318416,32505856,33525892] t27
def t29 : BT := .nd t21 [7,31,992,32736,1082401,2164802,5214340,8659208,33047056] t28
def t30 : BT := .nd t14 [6,992,31744,1082431,2164802,4329604,33047056,33530120] t29
def b32 : List Row := [([7,31,992,8659208,17318416,29197179,32539681],[(1024,501826),(1024,77281)]),([7,31,992,8682760,12988812,17318416,32539681],[(1024,67063),(1024,83425)]),([7,31,992,8682760,13008268,17318416,32539681],[(1024,67063),(1024,83425),(1025,99000)]),([7,31,992,8682760,17318416,21648020,32539681],[(1024,67063),(1024,83425),(1025,300729)]),([7,31,992,8682760,17318416,29224827,32539681],[(1024,99819),(1024,83425)]),([7,31,996,31744,1015808,1082401,2164802,8659208,33047056],[]),([7,31,996,31744,1015808,1082401,2164802,17318416,32776456],[]),([7,31,996,31744,1082401,2164802,8659208,17809936,32505856],[]),([7,31,996,31744,1082401,2164802,9412872,17318416,32505856],[]),([7,31,996,1015808,1082401,2164802,8682760,17318416,32505856],[]),([7,31,1023,4329604,8682760,17318416,32539681],[(1024,273894),(1024,67063),(1025,71351)]),([7,31,17376,1015808,1082401,2164802,4329604,8659208,33047056],[]),([7,31,17376,1015808,1082401,2164802,4329604,17318416,32776456],[(96,0),(104,0),(128,0),(136,0)]),([7,31,17376,1082401,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,17376,1082401,2164802,4329604,9412872,17318416,32505856],[(72,0),(80,0)]),([7,31,31744,32768,1082401,2165730,4329604,8659208,33047056],[]),([7,31,31744,32768,1082401,2165730,4329604,17318416,32776456],[(96,0)]),([7,31,31744,32768,1083361,2164802,4329604,8659208,33047056],[]),([7,31,31744,32768,1083361,2164802,4329604,17318416,32776456],[(128,0),(288,0)]),([7,31,31744,1015808,1082401,2098144,4329604,8659208,33047056],[]),([7,31,31744,1015808,1082401,2098144,4329604,17318416,32776456],[(96,0)]),([7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,4329604,17318416,32776456],[(96,0)]),([7,31,31744,1015808,1082401,2165730,4329604,32776456,33047056],[]),([7,31,31744,1015808,1082401,2165730,4330468,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,4330468,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,4357252,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,4357252,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,5214340,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,5214340,17318416,32776456],[(96,0)]),([7,31,31744,1015808,1082401,2165730,8659208,12988812,33047056],[]),([7,31,31744,1015808,1082401,2165730,8659208,32641156,33047056],[(96,0)])]
def b33 : List Row := [([7,31,31744,1015808,1082401,2165730,17318416,32641156,32776456],[(96,0)]),([7,31,31744,1015808,1082401,2165730,17318416,32776456,32911756],[(96,0)]),([7,31,31744,1015808,1082401,3248099,4329604,8659208,33047056],[(96,0)]),([7,31,31744,1015808,1082401,3248099,4329604,17318416,32776456],[(96,0),(104,0)]),([7,31,31744,1015808,1082431,2165730,4329604,17318416,32776456],[(96,0)]),([7,31,31744,1015808,1083361,2097152,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4329604,9412872,33047056],[]),([7,31,31744,1015808,1083361,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,17809936,32776456],[]),([7,31,31744,1015808,1083361,2164802,4329604,32776456,33047056],[]),([7,31,31744,1015808,1083361,2164802,4330468,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4330468,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,4357252,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4357252,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,5214340,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,5214340,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,8659208,12988812,33047056],[]),([7,31,31744,1015808,1083361,2164802,8659208,32641156,33047056],[(128,0)]),([7,31,31744,1015808,1083361,2164802,12988812,17318416,32776456],[(128,0),(176,0)]),([7,31,31744,1015808,1083361,2164802,17318416,32641156,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,17318416,32776456,32911756],[(128,0)]),([7,31,31744,1015808,1083361,2164831,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2165730,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2165730,4329604,17318416,32776456],[]),([7,31,31744,1015808,1083361,2194498,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,3247203,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,3247203,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,3248099,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,3248099,4329604,17318416,32776456],[(104,0)]),([7,31,31744,1015808,1113121,2165730,4329604,8659208,33047056],[]),([7,31,31744,1082401,1083361,2164802,4329604,9412872,33047056],[(72,0)])]
def t31 : BT := .nd (blockTree b32) [7,31,31744,1015808,1082401,2165730,12988812,17318416,32776456] (blockTree b33)
def b34 : List Row := [([7,31,31744,1082401,1083361,2164802,5214340,8659208,33047056],[(72,0)]),([7,31,31744,1082401,1083361,2164802,5214340,17318416,32776456],[(72,0),(80,0)]),([7,31,31744,1082401,1083361,2164802,8659208,17809936,32641156],[(72,0),(128,0)]),([7,31,31744,1082401,1083361,2164802,9412872,17318416,32641156],[(72,0),(80,0)]),([7,31,31744,1082401,2098144,4329604,8659208,17809936,32505856],[]),([7,31,31744,1082401,2098144,4329604,9412872,17318416,32505856],[(72,0),(112,0)]),([7,31,31744,1082401,2164802,2165730,5214340,8659208,33047056],[]),([7,31,31744,1082401,2164802,2165730,5214340,17318416,32776456],[(72,0)]),([7,31,31744,1082401,2164802,4330468,8659208,17351184,32505856],[]),([7,31,31744,1082401,2164802,4330468,8659208,17809936,33047056],[]),([7,31,31744,1082401,2164802,4330468,8691976,17318416,32505856],[(104,0)]),([7,31,31744,1082401,2164802,4330468,9412872,17318416,32776456],[]),([7,31,31744,1082401,2165730,3115074,4329604,8659208,33047056],[]),([7,31,31744,1082401,2165730,3115074,4329604,17318416,32776456],[]),([7,31,31744,1082401,2165730,4329604,5214340,8659208,33047056],[]),([7,31,31744,1082401,2165730,4329604,5214340,17318416,32776456],[(72,0)]),([7,31,31744,1082401,2165730,4329604,8659208,9412872,33047056],[]),([7,31,31744,1082401,2165730,4329604,8659208,17351184,32505856],[]),([7,31,31744,1082401,2165730,4329604,8659208,17809936,33047056],[]),([7,31,31744,1082401,2165730,4329604,8659208,33047056,33521664],[(72,0)]),([7,31,31744,1082401,2165730,4329604,8659208,33047056,33538576],[]),([7,31,31744,1082401,2165730,4329604,9412872,17318416,32776456],[(72,0)]),([7,31,31744,1082401,2165730,4329604,17318416,17809936,32776456],[]),([7,31,31744,1082401,2165730,4329604,17318416,32776456,33521664],[(72,0),(80,0)]),([7,31,31744,1082401,2165730,4329604,17318416,32776456,33530120],[(72,0)]),([7,31,31744,1082401,2165730,4330468,8659208,17809936,32505856],[]),([7,31,31744,1082401,2165730,4330468,9412872,17318416,32505856],[(104,0)]),([7,31,31744,1082401,2165730,5214340,8659208,32505856,33047056],[(72,0)]),([7,31,31744,1082401,2165730,5214340,8659208,33047056],[(73,0),(229,0)]),([7,31,31744,1082401,2165730,5214340,17318416,32505856,32776456],[(72,0)]),([7,31,31744,1082401,2165730,5214340,17318416,32776456],[(72,0),(73,0),(181,0)]),([7,31,31744,1082401,2165730,9412872,12988812,17318416,32505856],[(72,0),(176,0)])]
def b35 : List Row := [([7,31,31744,1083361,2097152,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,9412872,33047056],[]),([7,31,31744,1083361,2164802,4329604,8659208,17351184,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,33047056],[]),([7,31,31744,1083361,2164802,4329604,8659208,32505856,33538576],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,33047056,33521664],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,33047056,33538576],[]),([7,31,31744,1083361,2164802,4329604,9412872,17809936,32505856],[]),([7,31,31744,1083361,2164802,4329604,9412872,32505856,33047056],[]),([7,31,31744,1083361,2164802,4329604,9412872,33047056],[(229,0)]),([7,31,31744,1083361,2164802,4329604,17809936,32505856,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,17809936,32776456],[(97,0),(181,0)]),([7,31,31744,1083361,2164802,4330468,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,4330468,9412872,17318416,32505856],[(104,0),(136,0)]),([7,31,31744,1083361,2164802,4357252,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,4357252,9412872,17318416,32505856],[(104,0),(136,0)]),([7,31,31744,1083361,2164802,5214340,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,5214340,9412872,17318416,32505856],[(104,0)]),([7,31,31744,1083361,2164802,8659208,12988812,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2164802,8659208,17809936,32505856,32641156],[(96,0)]),([7,31,31744,1083361,2164802,9412872,12988812,17318416,32505856],[(96,0),(104,0),(176,0)]),([7,31,31744,1083361,2164802,9412872,13611404,17318416,32505856],[(104,0)]),([7,31,31744,1083361,2164802,9412872,17318416,32505856,32641156],[(104,0)]),([7,31,31744,1083361,2164802,9412872,33047056],[(1024,300101),(1024,279617)]),([7,31,31744,1083361,2164802,17809936,32776456],[(1024,300101),(1024,284737)]),([7,31,31744,1083361,2164831,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2165730,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,2194498,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,3115074,4329604,8659208,17809936,32505856],[])]
def t32 : BT := .nd (blockTree b34) [7,31,31744,1082401,3115074,4330468,8659208,17318431,32505856] (blockTree b35)
def t33 : BT := .nd t31 [7,31,31744,1082401,1083361,2164802,4329604,17809936,32776456] t32
def b36 : List Row := [([7,31,31744,1083361,3248099,4329604,8659208,17809936,32505856],[]),([7,31,31744,4330468,8659208,16236015,32539681],[(1024,516391),(1024,67046)]),([7,31,31744,4330468,8659208,17318431,32539681],[(128,0),(1024,301561),(1024,67046),(1025,88761)]),([7,31,31744,4330468,8659208,17383952],[(128,0),(1024,66022),(1024,98803),(1024,71137),(1025,67255),(1025,470713)]),([7,31,31744,4330468,8659208,25977624,32539681],[(1024,301561),(1024,67046),(1025,99001)]),([7,31,31744,4330468,8682760,17318416,32539681],[(1024,67046),(1024,72161),(1025,483001)]),([7,31,31744,4330468,8724744,17318416],[(1024,66022),(1024,98801),(1024,71137),(1025,67255),(1025,470713)]),([7,31,31744,4330468,17318416,24895223,32539681],[(1024,515170),(1024,67046)]),([7,31,32736,1015808,1082401,2164802,4330468,8659208,33047056],[]),([7,31,32736,1015808,1082401,2164802,4330468,17318416,32776456],[]),([7,31,32736,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,32736,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,32736,1082401,2164802,4330468,8659208,17809936,32505856],[]),([7,31,32736,1082401,2164802,4330468,9412872,17318416,32505856],[(104,0)]),([7,31,32736,1082401,2165730,4329604,8659208,17809936,32505856],[]),([7,31,32736,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,1015808,1082401,1083361,2164802,4357252,17318416,32776456],[]),([7,31,1015808,1082401,1083361,2194498,4329604,8659208,33047056],[(72,0)]),([7,31,1015808,1082401,1113121,2165730,4329604,8659208,33047056],[(72,0)]),([7,31,1015808,1082401,2164802,2165730,4357252,17318416,32776456],[]),([7,31,1015808,1082401,2164802,4330468,8682760,17318416,32776456],[]),([7,31,1015808,1082401,2165730,2194498,4329604,8659208,33047056],[]),([7,31,1015808,1082401,2165730,2195426,4329604,8659208,33047056],[]),([7,31,1015808,1082401,2165730,4330468,8682760,17318416,32505856],[]),([7,31,1015808,1082401,2165730,4357252,17318416,32505856,32776456],[]),([7,31,1015808,1082401,2165730,4357252,17318416,32776456],[]),([7,31,1015808,1083361,1113121,2164802,4329604,8659208,33047056],[]),([7,31,1015808,1083361,1114081,2164802,4329604,8659208,33047056],[]),([7,31,1015808,1083361,2164802,2194498,4329604,8659208,33047056],[(96,0)]),([7,31,1015808,1083361,2164802,4357252,17318416,32776456],[(177,0),(225,0),(245,0)]),([7,31,1015808,1083361,2194498,4329604,8659208,32505856,33047056],[]),([7,31,1015808,1083361,2194498,4329604,8659208,33047056],[(1024,295032),(1024,300101)])]
def b37 : List Row := [([7,31,1015808,1113121,2164802,2165730,4329604,8659208,33047056],[(96,0)]),([7,31,1015808,1113121,2165730,4329604,8659208,32505856,33047056],[]),([7,31,1015808,1113121,2165730,4329604,8659208,33047056],[(1024,296056),(1024,301125)]),([7,31,1015808,1113121,2165730,8659208,33047056],[(1024,301125),(1024,317506)]),([7,31,1082401,2165730,4357252,17318416,32776456],[(1024,314854),(1024,78305)]),([7,31,1082401,2165730,5214340,17318416,32776456],[(56,0),(1024,666073),(1024,78277)]),([7,31,1082401,3115074,4329631,17318896,32505856],[(1024,275525),(1024,501826)]),([7,31,1082401,3115074,17318672,32505856],[(1024,72965),(1024,269381),(1024,496706),(1025,102862),(1025,98968),(1025,469492)]),([7,31,1082401,4330468,8682760,17318416,32641156],[(1024,99819),(1024,73185),(1025,66231),(1025,88761)]),([7,31,1083361,1113121,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,1083361,1114081,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,992,16388,1015808,1082401,2164802,8659208,17318431,32505856],[(56,0)]),([7,992,31744,32768,3247203,4329604,8659208,17318431,32505856],[(128,0),(288,0)]),([7,992,31744,1014750,4329604,8659208,17318431],[(96,0),(1024,83425),(1024,67063)]),([7,992,31744,1015808,1082401,2164802,8659212,17318431,32505856],[]),([7,992,31744,1015808,1082401,2164802,12988812,17318431,32776456],[]),([7,992,31744,1015808,1082401,2164831,4329604,17318431,32776456],[]),([7,992,31744,1015808,1082401,2164831,4329604,17809936,32776456],[]),([7,992,31744,1015808,1082401,2164831,4329604,32776456,33047056],[]),([7,992,31744,1015808,1082401,2164831,8659208,17318431,32641156],[]),([7,992,31744,1015808,1082401,2164831,8659208,17809936,32641156],[]),([7,992,31744,1015808,1082401,2164831,8659208,32641156,33047056],[(96,0)]),([7,992,31744,1015808,1082401,3145728,4329604,8659208,17318431],[(168,0)]),([7,992,31744,1015808,1082431,2164802,4329604,17318431,32776456],[]),([7,992,31744,1015808,1082431,2164802,4329604,17809936,32776456],[]),([7,992,31744,1015808,1082431,2164802,4329604,32776456,33047056],[]),([7,992,31744,1015808,1082431,2164802,8659208,17318431,32641156],[]),([7,992,31744,1015808,1082431,2164802,8659208,17809936,32641156],[]),([7,992,31744,1015808,1082431,2164802,8659208,32641156,33047056],[(128,0)]),([7,992,31744,1015808,1082431,3247203,4329604,8659208,33047056],[(128,0),(136,0)]),([7,992,31744,1015808,3179553,4329604,8659208,17318431,32505856],[(128,0)])]
def t34 : BT := .nd (blockTree b36) [7,31,1015808,1083361,2194498,8659208,33047056] (blockTree b37)
def b38 : List Row := [([7,992,31744,1082401,1082431,2164802,4329604,17809936,32776456],[(72,0)]),([7,992,31744,1082401,1082431,2164802,5214340,8659208,33047056],[(72,0),(80,0),(128,0)]),([7,992,31744,1082401,1082431,2164802,8659208,17809936,32641156],[(72,0),(80,0)]),([7,992,31744,1082401,2097183,4329604,8659208,17809936,32505856],[(72,0),(80,0)]),([7,992,31744,1082401,2164802,2164831,4329604,17809936,32776456],[(72,0)]),([7,992,31744,1082401,2164802,2164831,8659208,17809936,32641156],[]),([7,992,31744,1082401,2164802,4329604,8691976,17318431,32505856],[]),([7,992,31744,1082401,2164802,4329604,9412872,17318431,32776456],[]),([7,992,31744,1082401,2164802,4362372,8659208,17318431,32505856],[]),([7,992,31744,1082401,2164802,5214340,8659208,17318431,32641156],[]),([7,992,31744,1082401,2164802,9412872,12988812,17318431,32505856],[]),([7,992,31744,1082401,2164831,3115074,4329604,8659208,33047056],[]),([7,992,31744,1082401,2164831,4329604,8659208,17809936,32505856],[(72,0),(80,0)]),([7,992,31744,1082401,2164831,4329604,8659208,17809936,32641156],[]),([7,992,31744,1082401,2164831,4329604,8659208,17809936,32776456],[(72,0)]),([7,992,31744,1082401,2164831,4329604,8659208,32505856,33538576],[(72,0),(80,0)]),([7,992,31744,1082401,2164831,4329604,8659208,33047056,33521664],[(72,0),(80,0)]),([7,992,31744,1082401,2164831,4329604,9412872,17318431,32505856],[]),([7,992,31744,1082401,2164831,4329604,17809936,32505856,32776456],[(72,0)]),([7,992,31744,1082401,2164831,4329604,17809936,32776456],[(181,0)]),([7,992,31744,1082401,2164831,5214340,8659208,17318431,32505856],[]),([7,992,31744,1082401,2164831,8659208,12988812,17809936,32505856],[(72,0),(80,0)]),([7,992,31744,1082401,2164831,8659208,17809936,32505856,32641156],[(72,0),(80,0)]),([7,992,31744,1082401,2164831,8659208,17809936,32641156],[(73,0),(181,0)]),([7,992,31744,1082401,2197570,4329604,8659208,17318431,32505856],[(128,0)]),([7,992,31744,1082401,3115074,4329604,8659208,17318431,32505856],[(128,0)]),([7,992,31744,1082401,3115074,4329604,8682760,17318431,32505856],[]),([7,992,31744,1082401,3115074,4330468,8659208,17318431,32505856],[(56,0),(128,0)]),([7,992,31744,1082401,3115074,4357252,8659208,17318431,32505856],[]),([7,992,31744,1082401,3115074,8659208,12988812,17318431,32505856],[(176,0)]),([7,992,31744,1082431,2164802,4329604,9412872,17318431,32505856],[]),([7,992,31744,1082431,2164802,4329604,9412872,17809936,32505856],[])]
def b39 : List Row := [([7,992,31744,1082431,2164802,5214340,8659208,17318431,32505856],[]),([7,992,31744,1082431,2164802,5214340,8659208,17809936,32505856],[]),([7,992,31744,1082431,2164802,5214340,8659208,32505856,33047056],[(96,0),(104,0)]),([7,992,31744,1082431,2164802,5214340,32776456],[(1024,83238),(1024,65832)]),([7,992,31744,1082431,2164802,9412872,32641156],[(1024,65832),(1024,88358)]),([7,992,31744,3179553,4329604,8659208,17318431],[(96,0),(1024,117217),(1024,281062)]),([7,992,31744,4329604,8659208,16236000,32539681],[(72,0),(1024,491602),(1024,67063)]),([7,992,31744,4329604,8659208,17318431,32539681],[(72,0),(1024,83425),(1024,67063)]),([7,992,31744,4329604,8659208,17383967],[(72,0),(1024,66034),(1024,98803),(1024,83425),(1025,88761),(1025,122553)]),([7,992,31744,4329604,8682760,17318431,32539681],[(1024,83425),(1024,67063),(1025,483001)]),([7,992,31744,4329604,8724744,17318431],[(1024,66034),(1024,98801),(1024,83425),(1025,88761),(1025,122553)]),([7,992,31744,4329604,12988812,17318431,32539681],[(1024,83425),(1024,99832),(1025,89785)]),([7,992,31744,4329604,17318431,24895223,32539681],[(1024,83425),(1024,67063)]),([7,992,31744,4330468,8659208,17318431,32539681],[(56,0),(72,0),(1024,83425),(1024,67063),(1025,285368)]),([7,992,31744,4357252,8659208,17318431,32539681],[(56,0),(72,0),(1024,83425),(1024,67063),(1025,481977)]),([7,992,31744,4395140,8659208,17318431],[(72,0),(1024,66033),(1024,98803),(1024,82401),(1025,88761),(1025,122553)]),([7,992,31744,8659208,12988812,17318431,32539681],[(104,0),(1024,67063),(1024,83425),(1025,122553)]),([7,992,31744,8659208,17318431,29224827,32539681],[(1024,83425),(1024,99832)]),([7,992,31748,1015808,1082401,2164802,8659208,17318431,32505856],[]),([7,992,32768,1082401,2164802,4329604,8682760,17318431,32505856],[]),([7,992,32768,1082401,2164802,4357252,8659208,17318431,32505856],[(280,0)]),([7,992,32768,4329604,8682760,17318431,32505856],[(1024,83609),(1024,66199)]),([7,992,32768,4357252,8659208,17318431,32505856],[(176,0),(1024,76441),(1024,66199)]),([7,992,65536,4329604,8682760,17318431],[(56,0),(1024,66034),(1024,98795),(1024,83425),(1025,88761),(1025,268984)]),([7,992,65536,4357252,8659208,17318431],[(56,0),(1024,66027),(1024,98803),(1024,76257),(1025,122553),(1025,268984),(1025,301753)]),([7,992,1015808,1082401,2097152,4329604,8682760,17318431,32505856],[(96,0)]),([7,992,1015808,1082401,2164802,4329604,8675592,17318431,32505856],[(128,0)]),([7,992,1015808,1082401,2164802,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8682760,17318431,32641156],[]),([7,992,1015808,1082401,2164802,4329604,8682760,17318431,32776456],[]),([7,992,1015808,1082401,2164802,4329604,8682760,17318431,33047056],[])]
def t35 : BT := .nd (blockTree b38) [7,992,31744,1082431,2164802,4329604,9412872,32505856,33047056] (blockTree b39)
def t36 : BT := .nd t34 [7,992,31744,1082401,1082431,2164802,4329604,9412872,33047056] t35
def t37 : BT := .nd t33 [7,31,31744,1083361,3247203,4329604,8659208,17809936,32505856] t36
def b40 : List Row := [([7,992,1015808,1082401,2164802,4357252,8659208,17318431,32505856],[]),([7,992,1015808,1082401,2164802,4357252,8659208,17318431,32641156],[]),([7,992,1015808,1082401,2164802,4357252,8659208,17318431,32776456],[]),([7,992,1015808,1082401,2164802,4357252,8659208,17318431,33047056],[(72,0),(96,0)]),([7,992,1015808,1082401,2164802,4357252,8682760,17318431,32505856],[]),([7,992,1015808,1082401,2164802,4358116,8659208,17318431,32505856],[(72,0),(96,0)]),([7,992,1015808,1082401,2164802,8682760,12988812,17318431,32505856],[]),([7,992,1015808,1082401,2164802,8682760,13008268,17318431,32505856],[]),([7,992,1015808,1082401,2164831,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1082401,2164831,4357252,8659208,17318431,32505856],[]),([7,992,1015808,1082401,2165730,4329604,8682760,17318431,32505856],[(72,0)]),([7,992,1015808,1082401,2165730,4357252,8659208,17318431,32505856],[(72,0),(128,0)]),([7,992,1015808,1082401,2194498,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1082401,2194498,4329631,33047056],[(1024,470085),(1024,318536)]),([7,992,1015808,1082401,2194498,4357252,8659208,17318431,32505856],[]),([7,992,1015808,1082401,2194498,8659231,33047056],[(1024,470085),(1024,481346)]),([7,992,1015808,1082401,3115074,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1082401,3115074,4357252,8659208,17318431,32505856],[]),([7,992,1015808,1082401,3247203,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1082401,3247203,4357252,8659208,17318431,32505856],[]),([7,992,1015808,1082401,4329604,8659231,17333776,32573506],[]),([7,992,1015808,1082401,4329631,8659208,17333776,32573506],[]),([7,992,1015808,1082431,2164802,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1083361,2164802,4329604,8682760,17318431,32505856],[(96,0),(128,0)]),([7,992,1015808,1113121,2164802,4329604,8682760,17318431,32505856],[]),([7,992,1015808,1113121,2164802,4329631,33047056],[(1024,469061),(1024,318536)]),([7,992,1015808,1113121,2164802,8659231,33047056],[(1024,469061),(1024,481345)]),([7,992,1015808,2164802,4329604,8659231,17333776,32539681],[(1024,508001)]),([7,992,1015808,2164802,4329631,8659208,17333776,32539681],[(1024,507969)]),([7,992,1015808,4329604,8682760,17318431,32539681],[(1024,110209),(1024,67223)]),([7,992,1015808,4329604,8682760,17318431,32573506],[(1024,109044),(1024,66034),(1025,88761)]),([7,992,1015808,4357252,8659208,17318431,32539681],[(1024,77441),(1024,67211)])]
def b41 : List Row := [([7,992,1048575,1082401,4329604,8682760,17318431],[(1024,83425),(1024,67255)]),([7,992,1048575,1082401,4357252,8659208,17318431],[(1024,77281),(1024,67051)]),([7,992,1082401,2097152,4329604,8682760,17318431],[(1024,110049),(1024,99819)]),([7,992,1082401,2164802,3115074,4329604,8682760,17318431,32505856],[]),([7,992,1082401,2164802,4329604,5214340,8682760,17318431,32505856],[]),([7,992,1082401,2164802,4329604,8682760,9412872,17318431,32505856],[(96,0)]),([7,992,1082401,2164802,4329604,8682760,17318431,17809936,32505856],[]),([7,992,1082401,2164802,4329604,8682760,17318431,32505856,33521664],[]),([7,992,1082401,3115074,4329604,8682760,17318431,32505856],[(1024,70295),(1024,83425)]),([7,992,1082401,3115074,4357252,8659208,17318431,32505856],[(153,0),(1024,70283),(1024,66199),(1024,69896)]),([7,992,1082401,4329604,8682760,16236000,32505856],[(1024,491602),(1024,67255)]),([7,992,1082401,4329604,8682760,17318431,32505856],[(1024,83425),(1024,67255)]),([7,992,1082401,4329604,8682760,17318431,32539681],[(1024,83641),(1024,67255)]),([7,992,1082401,4329604,13008268,17318431,32505856],[(1024,99819),(1024,78305),(1025,66034),(1025,89785)]),([7,992,1082401,4329604,17318431,24871671,32505856],[(1024,501858),(1024,67255)]),([7,992,1082401,4330468,8682760,17318431,32505856],[(1024,67255),(1024,83425),(1025,269803),(1025,285368)]),([7,992,1082401,4357252,8659208,16236000,32505856],[(1024,491596),(1024,67051)]),([7,992,1082401,4357252,8659208,17318431,32505856],[(1024,77281),(1024,67051)]),([7,992,1082401,4357252,8659208,17318431,32539681],[(1024,77497),(1024,67051)]),([7,992,1082401,4357252,8682760,17318431,32505856],[(1024,83425),(1024,67255)]),([7,992,1082401,4357252,12988812,17318431,32505856],[(1024,78305),(1024,100024)]),([7,992,1082401,4357252,13008268,17318431,32505856],[(1024,100024),(1024,77281),(1025,459250),(1025,483001)]),([7,992,1082401,4357252,17318431,24895223,32505856],[(1024,711778),(1024,67051)]),([7,992,1082401,4358116,8659208,17318431,32505856],[(1024,67051),(1024,77281),(1025,285368),(1025,295403)]),([7,992,1082401,8659208,17318431,29197179,32505856],[(1024,501826),(1024,77281)]),([7,992,1082401,8682760,12988812,17318431,32505856],[(1024,67255),(1024,83425)]),([7,992,1082401,8682760,13008268,17318431,32505856],[(1024,67255),(1024,83425),(1025,267763),(1025,483001)]),([7,992,1082401,8682760,17318431,29224827,32505856],[(1024,710722),(1024,83425)]),([7,992,1082431,2164802,5214340,32776456],[(1024,65997),(1024,98766),(1024,78118),(1025,470713),(1025,469492)]),([7,992,1082431,2164802,9412872,32641156],[(1024,65997),(1024,98766),(1024,78118),(1025,469492),(1025,470713)]),([7,992,1113121,2164802,4329631,17809936,32505856],[(1024,313416),(1024,469061)]),([7,992,1113121,2164802,8659231,17809936,32505856],[(1024,469061),(1024,476225)])]
def t38 : BT := .nd (blockTree b40) [7,992,1015808,4357252,8659208,17318431,32573506] (blockTree b41)
def b42 : List Row := [([7,992,2065441,2164802,4329604,8682760,17318431],[(1024,88545),(1024,70130),(1025,88761)]),([7,992,2164802,4329604,8682760,17318431,32539681],[(1024,83425),(1024,70135)]),([7,992,4329604,8682760,17318431,32472030,32505856],[(1024,83641),(1024,67255)]),([7,992,4329604,8682760,17318431,32505856,32539681],[(1024,83425),(1024,67223)]),([7,992,4329604,8682760,17318431,32539681],[(2,0),(57,0),(1024,67063),(1024,99819),(1024,83425),(1025,88761),(1025,267960),(1025,268984)]),([7,992,4357252,8659208,17318431,32539681],[(2,0),(57,0),(81,0),(1024,67051),(1024,99832),(1024,77281),(1025,122553),(1025,268984),(1025,481977)]),([7,31744,1082401,3115074,4329631,17318896,32505856],[(1024,472133),(1024,507969)]),([7,31744,1082401,4330468,8682760,17318431,32505856],[(1024,67046),(1024,72161),(1025,459246),(1025,483001)]),([7,31744,1082401,4330468,17318431,24895223,32505856],[(1024,711778),(1024,67046)]),([8,4,31,992,31744,1015808,1082401,2164802,8659208,33047056],[]),([8,4,31,992,31744,1015808,1082401,2164802,17318416,32776456],[]),([8,4,31,992,31744,1082401,2164802,8659208,17809936,32505856],[]),([8,4,31,992,31744,1082401,2164802,9412872,17318416,32505856],[]),([8,4,31,992,31744,1082401,3115074,8659208,17318416,32505856],[(72,0)]),([8,4,31,992,1015808,1082401,2164802,8682760,17318416,32505856],[]),([8,4,31,992,1015808,1082401,2194498,8659208,17318416,32505856],[(72,0)]),([8,4,31,992,1015808,1113121,2164802,8659208,17318416,32505856],[(72,0),(96,0),(336,0)]),([8,4,31,31744,1015808,1082401,2165730,8659208,17318416,32505856],[(72,0),(96,0),(216,0),(336,0)]),([8,4,31,31744,1015808,1083361,2164802,8659208,17318416,32505856],[(72,0),(96,0),(216,0),(336,0)]),([8,4,992,31744,1015808,1082401,2164802,8659208,17318431,32505856],[(56,0)]),([8,4,992,31744,1015808,1082401,2164831,8659208,17318416,32505856],[(216,0),(336,0)]),([8,4,992,31744,1015808,1082431,2164802,8659208,17318416,32505856],[(96,0),(216,0),(336,0)]),([8,12,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,31,256,1082401,3115074,17318416,32505856],[(56,0),(137,0),(1024,72997),(1024,302149),(1024,496706),(1025,102862),(1025,98968),(1025,469492)]),([8,31,287,1015808,1082401,2164802,17318416,32505856],[(1024,660793),(1024,302149),(1025,98803),(1025,98968),(1025,266702)]),([8,31,992,31744,32768,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,32768,1082401,2164802,4329604,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,32768,1082401,2164802,8659208,17318416,32641156],[(128,0),(168,0)]),([8,31,992,31744,32768,3247203,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(176,0),(360,0)]),([8,31,992,31744,1014750,4329604,8659208,17318416],[(136,0),(1024,83425),(1024,67063)]),([8,31,992,31744,1015808,1082401,2097152,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2097152,4329604,17318416,32776456],[(128,0),(136,0),(168,0)])]
def b43 : List Row := [([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,8682760,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,9412872,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318431,32776456],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,17809936,32776456],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,32776456,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4330468,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4330468,17318416,32776456],[]),([8,31,992,31744,1015808,1082401,2164802,4357252,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4357252,17318416,32776456],[]),([8,31,992,31744,1015808,1082401,2164802,5214340,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,5214340,17318416,32776456],[(128,0)]),([8,31,992,31744,1015808,1082401,2164802,8659208,12988812,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32505860],[(128,0),(136,0),(144,0),(168,0),(176,0)]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416,32911756],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318431,32641156],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,17809936,32641156],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,32641156,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,8659212,17318416,32505856],[(128,0),(136,0),(168,0),(176,0)]),([8,31,992,31744,1015808,1082401,2164802,8682760,17318416,32641156],[]),([8,31,992,31744,1015808,1082401,2164802,9412872,17318416,32641156],[(128,0)]),([8,31,992,31744,1015808,1082401,2164802,12988812,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,17318416,32641156,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,17318416,32776456,32911756],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164831,4329604,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164831,8659208,17318416,32641156],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2165730,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2165730,4329604,17318416,32776456],[(80,0),(128,0)]),([8,31,992,31744,1015808,1082401,2194498,4329604,8659208,33047056],[])]
def t39 : BT := .nd (blockTree b42) [8,31,992,31744,1015808,1082401,2097152,8659208,17318416,32641156] (blockTree b43)
def t40 : BT := .nd t38 [7,992,2065441,2164802,4329604,8659231,17333776,32505856] t39
def b44 : List Row := [([8,31,992,31744,1015808,1082401,3247203,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,3247203,4329604,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,3247203,8659208,17318416,32641156],[(128,0),(136,0),(168,0)]),([8,31,992,31744,1015808,1082431,2164802,4329604,17318416,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082431,2164802,8659208,17318416,32641156],[(128,0),(168,0)]),([8,31,992,31744,1015808,1083361,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1083361,2164802,4329604,17318416,32776456],[(80,0),(168,0)]),([8,31,992,31744,1015808,1113121,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,3179553,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(176,0)]),([8,31,992,31744,1015812,1082401,2164802,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(176,0)]),([8,31,992,31744,1082401,2097152,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2097152,4329604,9412872,17318416,32505856],[(96,0),(104,0),(128,0)]),([8,31,992,31744,1082401,2097152,5214340,8659208,17318416,32505856],[(96,0),(128,0),(136,0)]),([8,31,992,31744,1082401,2164802,3115074,4329604,8659208,33047056],[]),([8,31,992,31744,1082401,2164802,3115074,4329604,17318416,32776456],[(128,0)]),([8,31,992,31744,1082401,2164802,3115074,8659208,17318416,32641156],[(128,0),(136,0)]),([8,31,992,31744,1082401,2164802,4329604,5214340,8659208,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,5214340,17318416,32776456],[(96,0),(128,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,9412872,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,17351184,32505856],[(128,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32641156],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32776456],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,32505856,33538576],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,33047056,33521664],[(96,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,33047056,33538576],[]),([8,31,992,31744,1082401,2164802,4329604,8682760,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,8691976,17318416,32505856],[(96,0),(104,0),(128,0),(136,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32641156],[(96,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32776456],[(96,0),(104,0),(128,0)])]
def b45 : List Row := [([8,31,992,31744,1082401,2164802,4329604,9412872,17318431,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,9412872,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,9412872,32505856,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,9412872,33047056],[(293,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,17809936,32776456],[(104,0),(128,0),(236,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32505856,33530120],[(96,0),(104,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32776456,33521664],[(96,0),(104,0),(128,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32776456,33530120],[(96,0),(104,0),(128,0)]),([8,31,992,31744,1082401,2164802,4329604,17809936,32505856,32776456],[]),([8,31,992,31744,1082401,2164802,4329604,17809936,32776456],[(237,0)]),([8,31,992,31744,1082401,2164802,4330468,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4330468,9412872,17318416,32505856],[]),([8,31,992,31744,1082401,2164802,4357252,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4357252,9412872,17318416,32505856],[]),([8,31,992,31744,1082401,2164802,4362372,8659208,17318416,32505856],[(96,0),(128,0),(136,0),(144,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,17318416,32505856],[(96,0),(136,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,17318416,32641156],[(96,0),(128,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,17318416,32776456],[(96,0),(136,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,17318416,33047056],[(136,0),(292,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,17318431,32505856],[]),([8,31,992,31744,1082401,2164802,5214340,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,5214340,8659208,32505856,33047056],[]),([8,31,992,31744,1082401,2164802,5214340,8659208,33047056],[(293,0)]),([8,31,992,31744,1082401,2164802,5214340,8682760,17318416,32505856],[]),([8,31,992,31744,1082401,2164802,5214340,9412872,17318416,32505856],[(96,0)]),([8,31,992,31744,1082401,2164802,5214340,17318416,32505856,32776456],[(96,0)]),([8,31,992,31744,1082401,2164802,5214340,17318416,32776456],[(96,0),(97,0),(237,0),(1024,69928),(1024,83397)]),([8,31,992,31744,1082401,2164802,5214340,32776456],[(1024,102862),(1024,69928)]),([8,31,992,31744,1082401,2164802,5214340,33047056],[(1024,472165),(1024,509025)]),([8,31,992,31744,1082401,2164802,8659208,9412872,17318416,32641156],[(96,0),(128,0)]),([8,31,992,31744,1082401,2164802,8659208,12988812,17809936,32505856],[])]
def t41 : BT := .nd (blockTree b44) [8,31,992,31744,1082401,2164802,4329604,9412872,17318416,33047056] (blockTree b45)
def b46 : List Row := [([8,31,992,31744,1082401,2164802,8659208,17318416,17809936,32641156],[(128,0),(236,0)]),([8,31,992,31744,1082401,2164802,8659208,17318416,32505856,33525892],[(96,0),(136,0)]),([8,31,992,31744,1082401,2164802,8659208,17318416,32641156,33521664],[(96,0),(104,0),(112,0),(128,0),(136,0)]),([8,31,992,31744,1082401,2164802,8659208,17318416,32641156,33525892],[(96,0),(128,0)]),([8,31,992,31744,1082401,2164802,8659208,17809936,32505856,32641156],[]),([8,31,992,31744,1082401,2164802,8659208,17809936,32641156],[(237,0)]),([8,31,992,31744,1082401,2164802,8659231,17809936],[(1024,302149),(1024,286342),(1025,266536)]),([8,31,992,31744,1082401,2164802,8659231,33047056],[(1024,302149),(1024,281062),(1025,99603),(1025,266536)]),([8,31,992,31744,1082401,2164802,9412872,12988812,17318416,32505856],[(96,0),(128,0)]),([8,31,992,31744,1082401,2164802,9412872,13611404,17318416,32505856],[(96,0)]),([8,31,992,31744,1082401,2164802,9412872,17318416,32505856,32641156],[(96,0)]),([8,31,992,31744,1082401,2164802,9412872,17318416,32641156],[(96,0),(97,0),(237,0),(1024,69928),(1024,88517)]),([8,31,992,31744,1082401,2164802,9412872,32641156],[(1024,69928),(1024,102862)]),([8,31,992,31744,1082401,2164802,9412872,33047056],[(1024,302149),(1024,508993)]),([8,31,992,31744,1082401,2164802,17809936,32641156],[(1024,472165),(1024,510049)]),([8,31,992,31744,1082401,2164802,17809936,32776456],[(1024,302149),(1024,508993)]),([8,31,992,31744,1082401,2164831,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164831,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([8,31,992,31744,1082401,2164831,5214340,8659208,17318416,32505856],[(96,0)]),([8,31,992,31744,1082401,2165730,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2165730,4329604,9412872,17318416,32505856],[(80,0),(96,0),(104,0)]),([8,31,992,31744,1082401,2165730,5214340,8659208,17318416,32505856],[(80,0),(96,0),(136,0),(144,0)]),([8,31,992,31744,1082401,2194498,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2194498,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([8,31,992,31744,1082401,2194498,5214340,8659208,17318416,32505856],[(96,0)]),([8,31,992,31744,1082401,2197570,4329604,8659208,17318416,32505856],[(176,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],[(176,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,17318431,32505856],[]),([8,31,992,31744,1082401,3115074,4329604,8659208,17809936,32505856],[(96,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,32505856,33047056],[]),([8,31,992,31744,1082401,3115074,4329604,8682760,17318416,32505856],[]),([8,31,992,31744,1082401,3115074,4329604,9412872,17318416,32505856],[(96,0),(104,0)])]
def b47 : List Row := [([8,31,992,31744,1082401,3115074,4330468,8659208,17318416,32505856],[(80,0),(176,0)]),([8,31,992,31744,1082401,3115074,4357252,8659208,17318416,32505856],[]),([8,31,992,31744,1082401,3115074,5214340,8659208,17318416,32505856],[(96,0),(104,0),(112,0)]),([8,31,992,31744,1082401,3115074,8659208,12988812,17318416,32505856],[(232,0)]),([8,31,992,31744,1082401,3115074,8659208,17318416,32505856,32641156],[]),([8,31,992,31744,1082401,3247203,4329604,8659208,17809936,32505856],[(96,0),(128,0)]),([8,31,992,31744,1082401,3247203,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([8,31,992,31744,1082401,3247203,4329604,32776456],[(1024,706855),(1024,69928),(1025,66034),(1025,99001)]),([8,31,992,31744,1082401,3247203,4329604,33047056],[(1024,707682),(1024,83425),(1025,66034),(1025,300729)]),([8,31,992,31744,1082401,3247203,5214340,8659208,17318416,32505856],[(96,0),(104,0),(112,0),(136,0),(144,0)]),([8,31,992,31744,1082401,3247203,8659208,32641156],[(1024,705831),(1024,69928),(1025,66233),(1025,98803)]),([8,31,992,31744,1082401,3247203,8659208,33047056],[(1024,707650),(1024,83425),(1025,98803),(1025,300729)]),([8,31,992,31744,1082401,3247203,17318416,32641156],[(1024,705634),(1024,83425),(1025,66232),(1025,300532)]),([8,31,992,31744,1082401,3247203,17318416,32776456],[(1024,706626),(1024,83425),(1025,99000),(1025,300532)]),([8,31,992,31744,1082401,4329604,25977624,32776456],[(1024,102862),(1024,67255),(1025,99001),(1025,285369)]),([8,31,992,31744,1082401,4329604,25977624,33047056],[(1024,100020),(1024,67255),(1025,300729),(1025,318137),(1025,481977)]),([8,31,992,31744,1082401,8659208,21648020,32641156],[(1024,301746),(1024,69928),(1025,66233)]),([8,31,992,31744,1082401,8659208,21648020,33047056],[(1024,67252),(1024,83425),(1025,300729),(1025,483001)]),([8,31,992,31744,1082401,12988812,17318416,32641156],[(1024,100018),(1024,83425),(1025,66232),(1025,89785)]),([8,31,992,31744,1082401,12988812,17318416,32776456],[(1024,67251),(1024,83425),(1025,99000),(1025,122553)]),([8,31,992,31744,1082401,12988812,25977624,32505856],[(1024,270009),(1024,67022)]),([8,31,992,31744,1082431,2164802,4329604,9412872,17318416,32505856],[(96,0),(128,0)]),([8,31,992,31744,1082431,2164802,5214340,8659208,17318416,32505856],[(96,0),(128,0),(136,0),(144,0)]),([8,31,992,31744,1083361,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,31744,1083361,2164802,4329604,9412872,17318416,32505856],[(80,0),(104,0),(136,0)]),([8,31,992,31744,1113121,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,31744,3115074,4329604,8659208,17318416,32539681],[(1024,70295),(1024,73345),(1024,78465),(1024,112257),(1024,507969),(1024,508001),(1024,508166),(1024,508198),(1024,508363)]),([8,31,992,31744,3179553,4329604,8659208,17318416],[(136,0),(1024,281062),(1024,83425)]),([8,31,992,31744,3247203,4329604,8659208,32539681],[(1024,478699),(1024,69928),(1025,66233),(1025,99001)]),([8,31,992,31744,3247203,4329604,17318416,32539681],[(1024,515170),(1024,83425),(1025,66232),(1025,300729)]),([8,31,992,31744,3247203,8659208,17318416,32539681],[(1024,514114),(1024,83425),(1025,99000),(1025,300729)])]
def t42 : BT := .nd (blockTree b46) [8,31,992,31744,1082401,3115074,4329604,17318416,32505856,32776456] (blockTree b47)
def t43 : BT := .nd t41 [8,31,992,31744,1082401,2164802,8659208,13611404,17318416,32505856] t42
def t44 : BT := .nd t40 [8,31,992,31744,1015808,1082401,3145728,4329604,8659208,17318416] t43
def t45 : BT := .nd t37 [7,992,1015808,1082401,2164802,4330468,8682760,17318431,32505856] t44
def b48 : List Row := [([8,31,992,31744,4329604,8659208,17318416,32539681],[(104,0),(1024,83425),(1024,67063)]),([8,31,992,31744,4329604,8659208,17318431,32539681],[(1024,301561),(1024,67063),(1025,88761)]),([8,31,992,31744,4329604,8659208,17383952],[(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,31744,4329604,8659208,21648020,32539681],[(1024,301561),(1024,69928),(1025,66233),(1025,268584)]),([8,31,992,31744,4329604,8659208,25977624,32539681],[(1024,301561),(1024,67063),(1025,99001)]),([8,31,992,31744,4329604,8682760,17318416,32539681],[(1024,99832),(1024,67063),(1025,483001)]),([8,31,992,31744,4329604,8724744,17318416],[(1024,66034),(1024,98801),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,31744,4329604,12988812,17318416,32539681],[(1024,99832),(1024,83425),(1025,66232),(1025,268584)]),([8,31,992,31744,4329604,17318416,24895223,32539681],[(1024,515170),(1024,67063)]),([8,31,992,31744,4329604,17318416,25977624,32539681],[(104,0),(1024,99832),(1024,67063),(1025,66661),(1025,300729)]),([8,31,992,31744,4330468,8659208,17318416,32539681],[(80,0),(104,0),(1024,67063),(1024,83425),(1025,285368)]),([8,31,992,31744,4357252,8659208,17318416,32539681],[(80,0),(104,0),(1024,99832),(1024,67063),(1025,481977)]),([8,31,992,31744,4395140,8659208,17318416],[(104,0),(1024,66033),(1024,98803),(1024,82401),(1025,67255),(1025,268984)]),([8,31,992,31744,8659208,12988812,17318416,32539681],[(144,0),(1024,67063),(1024,83425),(1025,99000)]),([8,31,992,31744,8659208,17318416,21648020,32539681],[(1024,67063),(1024,83425),(1025,66661),(1025,300729)]),([8,31,992,31744,8659208,17318416,29224827,32539681],[(1024,514114),(1024,83425)]),([8,31,992,31748,1015808,1082401,2164802,8659208,17318416,32505856],[(136,0),(176,0)]),([8,31,992,32736,1015808,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,32736,1015808,1082401,2164802,4329604,17318416,32776456],[(128,0),(136,0),(168,0),(176,0),(292,0)]),([8,31,992,32736,1015808,1082401,2164802,8659208,17318416,32641156],[(128,0),(168,0),(292,0)]),([8,31,992,32736,1082401,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,32736,1082401,2164802,4329604,9412872,17318416,32505856],[(96,0),(104,0),(136,0),(292,0)]),([8,31,992,32736,1082401,2164802,5214340,8659208,17318416,32505856],[(96,0),(136,0),(144,0),(292,0)]),([8,31,992,32768,1082401,2164802,4329604,8682760,17318416,32505856],[]),([8,31,992,32768,1082401,2164802,4357252,8659208,17318416,32505856],[(104,0),(136,0),(352,0)]),([8,31,992,32768,4329604,8682760,17318416,32505856],[(1024,66199),(1024,98968)]),([8,31,992,32768,4357252,8659208,17318416,32505856],[(232,0),(1024,98968),(1024,66199)]),([8,31,992,65536,4329604,8682760,17318416],[(72,0),(80,0),(1024,66034),(1024,98795),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,65536,4357252,8659208,17318416],[(72,0),(80,0),(1024,66027),(1024,98803),(1024,76257),(1025,67255),(1025,268984)]),([8,31,992,1015808,1082401,1113121,2164802,4329604,8659208,33047056],[(96,0)]),([8,31,992,1015808,1082401,1113121,2164802,4329604,17318416,32776456],[(96,0),(104,0),(168,0),(176,0)]),([8,31,992,1015808,1082401,1113121,2164802,8659208,17318416,32641156],[(96,0),(104,0),(168,0)])]
def b49 : List Row := [([8,31,992,1015808,1082401,2164802,2194498,4329604,8659208,33047056],[(128,0)]),([8,31,992,1015808,1082401,2164802,2194498,4329604,17318416,32776456],[(96,0),(104,0),(128,0),(136,0)]),([8,31,992,1015808,1082401,2164802,2194498,8659208,17318416,32641156],[(96,0),(128,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4329604,4357252,17318416,32776456],[(96,0),(104,0),(128,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4329604,8675592,17318416,32505856],[(96,0),(104,0),(128,0),(136,0),(176,0)]),([8,31,992,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,4329604,8682760,17318416,32641156],[]),([8,31,992,1015808,1082401,2164802,4329604,8682760,17318416,32776456],[(96,0),(104,0),(128,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4329604,8682760,17318416,33047056],[]),([8,31,992,1015808,1082401,2164802,4329604,8682760,17318431,32505856],[]),([8,31,992,1015808,1082401,2164802,4330468,8682760,17318416,32505856],[(104,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17318416,32505856],[(104,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17318416,32641156],[(96,0),(128,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17318416,32776456],[(104,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17318416,33047056],[(104,0),(136,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17318431,32505856],[(96,0)]),([8,31,992,1015808,1082401,2164802,4357252,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,4357252,9412872,17318416,32505856],[(104,0)]),([8,31,992,1015808,1082401,2164802,4357252,17318416,32505856,32776456],[(104,0)]),([8,31,992,1015808,1082401,2164802,4357252,17318416,32776456],[]),([8,31,992,1015808,1082401,2164802,4358116,8659208,17318416,32505856],[(104,0),(136,0)]),([8,31,992,1015808,1082401,2164802,5214340,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,8659208,8682760,17318416,32641156],[(96,0),(128,0)]),([8,31,992,1015808,1082401,2164802,8682760,12988812,17318416,32505856],[(96,0),(104,0),(128,0),(136,0)]),([8,31,992,1015808,1082401,2164802,8682760,13008268,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,8682760,17318416,32505856,32641156],[]),([8,31,992,1015808,1082401,2164802,8682760,17318416,32641156],[(1024,88357)]),([8,31,992,1015808,1082401,2164831,4329604,8682760,17318416,32505856],[(96,0)]),([8,31,992,1015808,1082401,2164831,4357252,8659208,17318416,32505856],[(96,0),(104,0)]),([8,31,992,1015808,1082401,2165730,4329604,8682760,17318416,32505856],[(104,0)]),([8,31,992,1015808,1082401,2165730,4357252,8659208,17318416,32505856],[(104,0),(136,0),(176,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,32505856,33047056],[(96,0)])]
def t46 : BT := .nd (blockTree b48) [8,31,992,1015808,1082401,2097152,4329604,8682760,17318416,32505856] (blockTree b49)
def b50 : List Row := [([8,31,992,1015808,1082401,2194498,4329604,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,2194498,4329604,9412872,17318416,32505856],[(96,0),(104,0)]),([8,31,992,1015808,1082401,2194498,4329604,17318416,32505856,32776456],[(96,0),(104,0)]),([8,31,992,1015808,1082401,2194498,4329604,33047056],[(1024,470117),(1024,482402)]),([8,31,992,1015808,1082401,2194498,4330468,8659208,17318416,32505856],[(104,0),(136,0),(176,0)]),([8,31,992,1015808,1082401,2194498,4357252,8659208,17318416,32505856],[(104,0)]),([8,31,992,1015808,1082401,2194498,5214340,8659208,17318416,32505856],[(96,0),(104,0)]),([8,31,992,1015808,1082401,2194498,8659208,17318416,32505856,32641156],[(96,0),(104,0)]),([8,31,992,1015808,1082401,2194498,8659208,33047056],[(1024,470085),(1024,481346)]),([8,31,992,1015808,1082401,3115074,4329604,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,3115074,4357252,8659208,17318416,32505856],[(104,0)]),([8,31,992,1015808,1082401,3247203,4329604,8682760,17318416,32505856],[]),([8,31,992,1015808,1082401,3247203,4357252,8659208,17318416,32505856],[(104,0),(136,0)]),([8,31,992,1015808,1082401,4329604,8659208,17333776,32573506],[(1024,83397),(1024,117189)]),([8,31,992,1015808,1082431,2164802,4329604,8682760,17318416,32505856],[(128,0)]),([8,31,992,1015808,1083361,2164802,4329604,8682760,17318416,32505856],[(136,0),(176,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,32505856,33047056],[(128,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,33047056],[(129,0),(1024,319560),(1024,469112)]),([8,31,992,1015808,1113121,2164802,4329604,8682760,17318416,32505856],[]),([8,31,992,1015808,1113121,2164802,4329604,9412872,17318416,32505856],[]),([8,31,992,1015808,1113121,2164802,4329604,17318416,32505856,32776456],[(128,0),(136,0)]),([8,31,992,1015808,1113121,2164802,4329604,33047056],[(1024,469093),(1024,482401)]),([8,31,992,1015808,1113121,2164802,8659208,33047056],[(1024,469061),(1024,481345)]),([8,31,992,1015808,2164802,4329604,8659208,17333776,32539681],[(1024,508363)]),([8,31,992,1015808,4329604,8682760,17318416,32539681],[(1024,99979),(1024,67223)]),([8,31,992,1015808,4329604,8682760,17318416,32573506],[(1024,98803),(1024,66034),(1025,67255)]),([8,31,992,1015808,4357252,8659208,17318416,32539681],[(1024,67211),(1024,77441)]),([8,31,992,1015808,4357252,8659208,17318416,32573506],[(1024,66034),(1024,76418),(1025,67255)]),([8,31,992,1048575,1082401,4329604,8682760,17318416],[(1024,99819),(1024,67255)]),([8,31,992,1048575,1082401,4357252,8659208,17318416],[(1024,67051),(1024,77281)]),([8,31,992,1082401,1113121,2164802,4329604,8659208,17809936,32505856],[(72,0),(128,0)])]
def b51 : List Row := [([8,31,992,1082401,2097152,4329604,8682760,17318416],[(1024,99819),(1024,83425)]),([8,31,992,1082401,2164802,2194498,4329604,9412872,17318416,32505856],[(72,0),(80,0)]),([8,31,992,1082401,2164802,3115074,4329604,8682760,17318416,32505856],[]),([8,31,992,1082401,2164802,4329604,4357252,9412872,17318416,32505856],[(72,0),(80,0)]),([8,31,992,1082401,2164802,4329604,5214340,8682760,17318416,32505856],[]),([8,31,992,1082401,2164802,4329604,8682760,9412872,17318416,32505856],[(72,0),(80,0),(96,0),(104,0),(136,0)]),([8,31,992,1082401,2164802,4329604,8682760,17318416,17809936,32505856],[]),([8,31,992,1082401,2164802,4329604,8682760,17318416,32505856,33521664],[]),([8,31,992,1082401,2164802,4357252,9412872,17318416],[(1024,483979),(1024,78465)]),([8,31,992,1082401,2164802,4357252,9412872,17318416,32505856],[(80,0),(81,0),(1024,67211),(1024,78498)]),([8,31,992,1082401,2164802,4357252,17318416,32539681],[(1024,78305),(1024,281062)]),([8,31,992,1082401,2164802,4357252,17318416,32776456],[(1024,281062),(1024,78305)]),([8,31,992,1082401,2164802,5214340,8682760,17318416],[(1024,483979),(1024,83585)]),([8,31,992,1082401,2164802,5214340,8682760,17318416,32505856],[(1024,83237),(1024,82561),(1024,83618)]),([8,31,992,1082401,2164802,5214340,17318416,32776456],[(72,0),(1024,666073),(1024,78277)]),([8,31,992,1082401,2164802,5214340,32776456],[(1024,70093),(1024,102862),(1024,78277),(1025,470713),(1025,70100)]),([8,31,992,1082401,2164802,8682760,17318416,32539681],[(1024,269803),(1024,83425)]),([8,31,992,1082401,2164802,8682760,17318416,32641156],[(1024,478699),(1024,83425)]),([8,31,992,1082401,2164802,9412872,17318416,32641156],[(72,0),(1024,502228),(1024,78277)]),([8,31,992,1082401,2164802,9412872,32641156],[(1024,70093),(1024,102862),(1024,78277),(1025,102868),(1025,469657)]),([8,31,992,1082401,2194498,4329604,8659208,33047056],[(1024,314854),(1024,83425)]),([8,31,992,1082401,2194498,4329604,9412872,17318416,32505856],[(72,0),(73,0),(80,0),(81,0)]),([8,31,992,1082401,2194498,4329604,33047056],[(1024,470117),(1024,83425),(1024,281062),(1025,98803),(1025,66034),(1025,267763),(1025,300697)]),([8,31,992,1082401,2194498,5214340,8659208,17318416,32505856],[(72,0),(73,0),(74,0),(81,0),(106,0),(114,0),(1024,72997),(1024,509190)]),([8,31,992,1082401,2194498,5214340,17318416,32505856],[(1024,711778),(1024,470117)]),([8,31,992,1082401,2194498,8659208,33047056],[(1024,83425),(1024,281062),(1024,302149),(1025,66034),(1025,98803),(1025,69928),(1025,300697)]),([8,31,992,1082401,2194498,8659231,17318416,32505856],[(1024,302149),(1024,281062),(1025,266536)]),([8,31,992,1082401,2194498,9412872,17318416,32505856],[(80,0),(1024,508993),(1024,302149)]),([8,31,992,1082401,3115074,4329604,8682760,17318416,32505856],[(217,0),(1024,111909),(1024,112257),(1024,66199)]),([8,31,992,1082401,3115074,4329631,17318416,32505856],[(1024,472133),(1024,501826)]),([8,31,992,1082401,3115074,4357252,8659208,17318416,32505856],[(81,0),(201,0),(217,0),(1024,78465),(1024,66199),(1024,72997),(1024,508166)])]
def t47 : BT := .nd (blockTree b50) [8,31,992,1082401,1113121,2164802,4329604,9412872,17318416,32505856] (blockTree b51)
def t48 : BT := .nd t46 [8,31,992,1015808,1082401,2194498,4329604,8659208,33047056] t47
def b52 : List Row := [([8,31,992,1082401,3115074,8659231,17318416,32505856],[(1024,302149),(1024,501826),(1025,102862),(1025,266536)]),([8,31,992,1082401,3115074,8682760,17318416,32505856],[(1024,710722),(1024,302149),(1025,102862)]),([8,31,992,1082401,3247203,4357252,17318416,32505856],[(1024,711778),(1024,78305),(1025,300532)]),([8,31,992,1082401,3247203,8682760,17318416,32505856],[(1024,710722),(1024,83425),(1025,300532)]),([8,31,992,1082401,4329604,8682760,16236015,32505856],[(1024,712999),(1024,67255)]),([8,31,992,1082401,4329604,8682760,17318416,32505856],[(1024,99819),(1024,67255)]),([8,31,992,1082401,4329604,8682760,17318416,32539681],[(1024,100024),(1024,67255)]),([8,31,992,1082401,4329604,8682760,17318416,32641156],[(1024,99819),(1024,83425),(1025,66231),(1025,88761)]),([8,31,992,1082401,4329604,8682760,17318416,32776456],[(1024,478699),(1024,67255),(1025,99000),(1025,122553),(1025,285368)]),([8,31,992,1082401,4329604,8682760,17318431,32505856],[(1024,301753),(1024,67255),(1025,88761),(1025,102891)]),([8,31,992,1082401,4329604,8682760,21648020,32505856],[(1024,99819),(1024,69928),(1025,66034)]),([8,31,992,1082401,4329604,13008268,17318416,32505856],[(1024,99819),(1024,78305),(1025,66034)]),([8,31,992,1082401,4329604,17318416,24871671,32505856],[(1024,501858),(1024,67255)]),([8,31,992,1082401,4330468,8682760,17318416,32505856],[(1024,67255),(1024,83425),(1025,269803),(1025,285368)]),([8,31,992,1082401,4357252,8659208,16236015,32505856],[(1024,712999),(1024,67051)]),([8,31,992,1082401,4357252,8659208,17318416,32505856],[(1024,67051),(1024,77281)]),([8,31,992,1082401,4357252,8659208,17318416,32539681],[(1024,67255),(1024,77281)]),([8,31,992,1082401,4357252,8659208,17318416,32641156],[(1024,100024),(1024,78305),(1025,66231),(1025,88761)]),([8,31,992,1082401,4357252,8659208,17318416,32776456],[(1024,67051),(1024,77281),(1025,99000),(1025,122553)]),([8,31,992,1082401,4357252,8659208,17318431,32505856],[(1024,301753),(1024,67051),(1025,70123),(1025,88761)]),([8,31,992,1082401,4357252,8659208,25977624,32505856],[(1024,301753),(1024,67051),(1025,98803)]),([8,31,992,1082401,4357252,8682760,17318416,32505856],[(1024,100024),(1024,67255)]),([8,31,992,1082401,4357252,9412872,17318416],[(1024,67244),(1024,100017),(1024,77441),(1025,268984),(1025,67255)]),([8,31,992,1082401,4357252,9412872,17318416,32505856],[(80,0),(1024,100024),(1024,67255)]),([8,31,992,1082401,4357252,12988812,17318416,32505856],[(1024,100024),(1024,78305)]),([8,31,992,1082401,4357252,13008268,17318416,32505856],[(1024,100024),(1024,77281),(1025,66034),(1025,483001)]),([8,31,992,1082401,4357252,17318416,24895223,32505856],[(1024,711778),(1024,67051)]),([8,31,992,1082401,4357252,17318416,25977624,32505856],[(1024,100024),(1024,67051),(1025,300532),(1025,481977)]),([8,31,992,1082401,4358116,8659208,17318416,32505856],[(80,0),(1024,67051),(1024,77281),(1025,285368)]),([8,31,992,1082401,5214340,8682760,17318416],[(1024,67249),(1024,99979),(1024,82561),(1025,67255),(1025,268984)]),([8,31,992,1082401,5214340,8682760,17318416,32505856],[(1024,100024),(1024,67255)]),([8,31,992,1082401,8659208,17318416,29197179,32505856],[(1024,501826),(1024,77281)])]
def b53 : List Row := [([8,31,992,1082401,8682760,13008268,17318416,32505856],[(1024,67255),(1024,83425),(1025,98803),(1025,483001)]),([8,31,992,1082401,8682760,17318416,21648020,32505856],[(1024,67255),(1024,83425),(1025,300532),(1025,483001)]),([8,31,992,1082401,8682760,17318416,29224827,32505856],[(1024,710722),(1024,83425)]),([8,31,992,1113121,2164802,4329604,8659208,17809936,32505856],[(96,0),(97,0),(1024,314440),(1024,469107)]),([8,31,992,1113121,2164802,4329604,17809936,32505856],[(1024,477446),(1024,469093)]),([8,31,992,1113121,2164802,8659208,17809936,32505856],[(1024,469061),(1024,476225)]),([8,31,992,1113121,4329604,8659208,17809936,32505856],[(1024,67255),(1024,100024)]),([8,31,992,1113121,4329604,8682760,17318416,32505856],[(104,0),(1024,99819),(1024,67255),(1025,459246),(1025,483001)]),([8,31,992,2065441,2164802,4329604,8659208,17333776,32505856],[(128,0),(1024,67021)]),([8,31,992,2065441,2164802,4329604,8682760,17318416],[(1024,483819),(1024,88545),(1025,67255)]),([8,31,992,2164802,4329604,8682760,17318416,32539681],[(1024,478699),(1024,83425)]),([8,31,992,4329604,8682760,17318416,32472030,32505856],[(1024,100024),(1024,67255)]),([8,31,992,4329604,8682760,17318416,32505856,32539681],[(1024,99819),(1024,67223)]),([8,31,992,4329604,8682760,17318416,32539681],[(2,0),(6,0),(57,0),(81,0),(129,0),(1024,67063),(1024,99819),(1024,83425),(1025,483001),(1025,66231),(1025,67255),(1025,268984)]),([8,31,992,4357252,8659208,17318416,32539681],[(2,0),(6,0),(57,0),(58,0),(81,0),(113,0),(129,0),(1024,67051),(1024,99832),(1024,77281),(1025,481977),(1025,67255),(1025,99000),(1025,268984)]),([8,31,1023,1015808,1082401,2164802,17318416,32641156],[(1024,72997),(1024,472165),(1025,98803)]),([8,31,1023,1082401,2164802,5214340,17318416,32505856],[(1024,72997),(1024,472165),(1025,98968)]),([8,31,1023,1082401,3115074,4329604,17318416,32505856],[(1024,72997),(1024,472165),(1025,98968)]),([8,31,1023,1082401,4329604,8682760,17318416,32505856],[(1024,273894),(1024,67255),(1025,67255),(1025,103915)]),([8,31,31744,1015808,1082401,1083361,2164802,4329604,8659208,33047056],[(96,0)]),([8,31,31744,1015808,1082401,1083361,2164802,4329604,17318416,32776456],[(96,0),(104,0),(168,0)]),([8,31,31744,1015808,1082401,2164802,2165730,4329604,8659208,33047056],[(128,0)]),([8,31,31744,1015808,1082401,2164802,2165730,4329604,17318416,32776456],[(96,0),(128,0),(136,0)]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[(96,0),(128,0),(272,0)]),([8,31,31744,1015808,1082401,2164802,8659944,32641156],[(1024,102862),(1024,69896)]),([8,31,31744,1015808,1082401,2164802,17318896,32641156],[(1024,472165),(1024,88325)]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,32505856,33047056],[(96,0)]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],[(97,0),(285,0),(1024,301125),(1024,296056)]),([8,31,31744,1015808,1082401,2165730,4329604,17318416,32505856,32776456],[(96,0),(104,0)]),([8,31,31744,1015808,1082401,2165730,4329604,17318416,32776456],[(96,0),(97,0),(105,0),(137,0),(177,0),(229,0),(1024,284738)]),([8,31,31744,1015808,1082401,2165730,8659208,33047056],[(1024,301125),(1024,317506)])]
def t49 : BT := .nd (blockTree b52) [8,31,992,1082401,8682760,12988812,17318416,32505856] (blockTree b53)
def b54 : List Row := [([8,31,31744,1015808,1082401,4329604,8659208,17318896,32573506],[(128,0),(1024,83237),(1024,111909)]),([8,31,31744,1015808,1082401,4329604,8659944,17318416,32573506],[(1024,69896),(1024,78498),(1024,83618)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,32505856,33047056],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,33047056],[(129,0),(285,0),(1024,295032),(1024,300101)]),([8,31,31744,1015808,1083361,2164802,4329604,17318416,32776456],[(105,0),(128,0),(129,0),(137,0),(177,0),(229,0),(233,0),(289,0),(309,0),(1024,112069)]),([8,31,31744,1015808,1083361,2164802,8659208,33047056],[(1024,300101),(1024,317505)]),([8,31,31744,1015808,1083361,2164802,17318416,32776456],[(1024,284737),(1024,300101)]),([8,31,31744,1015808,2164802,4329604,8659208,17318896,32539681],[(128,0),(1024,111909),(1024,508198)]),([8,31,31744,1015808,2164802,4329604,8659944,17318416,32539681],[(1024,69896),(1024,78465),(1024,508166)]),([8,31,31744,1082401,1083361,2164802,4329604,8659208,17809936,32505856],[(72,0),(128,0)]),([8,31,31744,1082401,2164802,5214340,8659944,32505856],[(1024,102862),(1024,69896)]),([8,31,31744,1082401,2164802,5214340,17318896,32505856],[(1024,472165),(1024,83205)]),([8,31,31744,1082401,2165730,4329604,8659208,33047056],[(1024,281062),(1024,83425)]),([8,31,31744,1082401,2165730,4329604,17318416,32776456],[(1024,281062),(1024,83425)]),([8,31,31744,1082401,2165730,8659208,33047056],[(1024,83425),(1024,280642),(1024,301125),(1025,66034),(1025,98803),(1025,70093),(1025,99603),(1025,469657)]),([8,31,31744,1082401,2165730,17318416,32776456],[(1024,83425),(1024,280642),(1024,301125),(1025,66034),(1025,98968),(1025,70093),(1025,300532)]),([8,31,31744,1082401,3115074,4329604,8659944,32505856],[(1024,102862),(1024,69896)]),([8,31,31744,1082401,3115074,4329604,17318896,32505856],[(1024,472165),(1024,508001)]),([8,31,31744,1082401,3115074,8659231,17318416,32505856],[(1024,496915),(1024,302149),(1025,266536)]),([8,31,31744,1082401,4330468,8659208,16236015,32505856],[(1024,712999),(1024,67046)]),([8,31,31744,1082401,4330468,8659208,17318431,32505856],[(168,0),(1024,301753),(1024,67046),(1025,70118),(1025,88761)]),([8,31,31744,1082401,4330468,8659208,25977624,32505856],[(1024,301753),(1024,67046),(1025,98803),(1025,285369)]),([8,31,31744,1082401,4330468,8682760,17318416,32505856],[(80,0),(1024,67046),(1024,72161),(1025,483001)]),([8,31,31744,1082401,4330468,17318416,24895223,32505856],[(1024,711778),(1024,67046)]),([8,31,31744,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0),(97,0),(229,0),(1024,295027),(1024,300101)]),([8,31,31744,1083361,2164802,8659208,17809936,32505856],[(1024,312385),(1024,300101)]),([8,31,31744,1083361,2164802,9412872,17318416,32505856],[(104,0),(1024,279617),(1024,300101)]),([8,31,31744,1083361,4329604,8659208,17809936,32505856],[(1024,67255),(1024,100024)]),([8,31,31744,2065441,2164802,4329604,8659208,17318896,32505856],[(128,0),(1024,66856),(1024,111909)]),([8,31,1015808,1082401,2164802,4329631,17318896,32505856],[(1024,275525),(1024,502036),(1025,98803),(1025,98968)]),([8,31,1015808,1082401,2164802,4357252,8659944,17318416,32505856],[(1024,69896),(1024,78305),(1024,78465),(1024,78498),(1024,508166)])]
def b55 : List Row := [([8,31,1015808,1082401,2164802,8659208,17333776,32641156],[(72,0),(96,0),(1024,660760),(1024,72997)]),([8,31,1015808,1082401,2164802,17318416,17318896,32641156],[(1024,510049),(1024,78117),(1025,102862)]),([8,31,1015808,1082401,2164802,17318672,32505856],[(1024,72965),(1024,269381),(1024,496916),(1025,102862),(1025,98803),(1025,98968),(1025,469492),(1025,470713)]),([8,31,1015808,1082401,2164802,17318896,32641156],[(1024,111877),(1024,275557),(1024,502036),(1025,102862),(1025,98803),(1025,98968)]),([8,31,1015808,1082401,2165730,17318416,32776456],[(1024,78277),(1024,268761),(1024,275522),(1025,70093),(1025,66034),(1025,98968),(1025,469492),(1025,470713)]),([8,31,1015808,1082401,2194498,8659231,17318416,32505856],[(1024,660760),(1024,302149),(1025,266536)]),([8,31,1015808,1083361,2164802,17318416,32776456],[(1024,78277),(1024,267737),(1024,275521),(1025,70093),(1025,66034),(1025,98968),(1025,469492),(1025,470713)]),([8,31,1082401,2164802,5214340,8659208,17318896,32505856],[(56,0),(1024,502056),(1024,78117)]),([8,31,1082401,2164802,5214340,8659208,17333776,32505856],[(56,0),(1024,496915),(1024,72997)]),([8,31,1082401,2164802,5214340,17318896,32505856],[(1024,111877),(1024,275557),(1024,502024),(1025,102862),(1025,98803),(1025,98968)]),([8,31,1082401,2194498,5214340,17318416,32505856],[(1024,72997),(1024,464997),(1024,496904),(1025,267763),(1025,276152)]),([8,31,1082401,3115074,4329604,8659208,17318896,32505856],[(1024,502055),(1024,78117)]),([8,31,1082401,3115074,4329604,8659208,17333776,32505856],[(128,0),(1024,496915),(1024,72997)]),([8,31,1082401,3115074,4329604,17318896,32505856],[(1024,111877),(1024,275557),(1024,501858),(1025,102862),(1025,98968)]),([8,31,1082401,3115074,4357252,17318416,32505856],[(1024,72997),(1024,466021),(1024,496738),(1025,267763),(1025,267928),(1025,281272)]),([8,992,31744,32768,1082401,2164802,4329604,8659208,17318431,32505856],[(168,0),(352,0)]),([8,992,31744,32768,4329604,8659208,17318431,32505856],[(96,0),(232,0),(1024,83609),(1024,66199)]),([8,992,31744,65536,4329604,8659208,17318431],[(72,0),(80,0),(96,0),(1024,66034),(1024,98803),(1024,83425),(1025,88761),(1025,268984)]),([8,992,31744,1015808,1082401,1082431,2164802,4329604,8659208,33047056],[(96,0),(104,0),(168,0),(176,0)]),([8,992,31744,1015808,1082401,2164802,2164831,4329604,8659208,33047056],[(96,0),(104,0),(128,0),(136,0)]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32505856],[(168,0)]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32641156],[(168,0)]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32776456],[(168,0)]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,33047056],[(96,0),(104,0),(128,0),(136,0),(168,0)]),([8,992,31744,1015808,1082401,2164802,4329604,8682760,17318431,32505856],[]),([8,992,31744,1015808,1082401,2164802,4329631,33047056],[(1024,472133),(1024,318536)]),([8,992,31744,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[(56,0),(96,0),(128,0),(168,0)]),([8,992,31744,1015808,1082401,2164802,4357252,8659208,17318431,32505856],[(104,0)]),([8,992,31744,1015808,1082401,2164802,8659208,12988812,17318431,32505856],[(224,0)]),([8,992,31744,1015808,1082401,2164802,8659231,33047056],[(1024,471109),(1024,481358)]),([8,992,31744,1015808,1082401,2164831,4329604,8659208,17318431,32505856],[(168,0)])]
def t50 : BT := .nd (blockTree b54) [8,31,1015808,1082401,2164802,8659208,17318896,32641156] (blockTree b55)
def t51 : BT := .nd t49 [8,31,31744,1015808,1082401,2165730,17318416,32776456] t50
def t52 : BT := .nd t48 [8,31,992,1082401,3115074,4357252,17318416,32505856] t51
def b56 : List Row := [([8,992,31744,1015808,1082401,2164831,4329604,8659208,32505856,33047056],[(96,0),(104,0)]),([8,992,31744,1015808,1082401,2164831,4329604,32776456],[(1024,99790),(1024,66856)]),([8,992,31744,1015808,1082401,2164831,8659208,32641156],[(1024,66856),(1024,88359)]),([8,992,31744,1015808,1082401,2165730,4329604,8659208,17318431,32505856],[(56,0),(96,0),(168,0)]),([8,992,31744,1015808,1082401,2194498,4329604,8659208,17318431,32505856],[(104,0),(168,0)]),([8,992,31744,1015808,1082401,3115074,4329604,8659208,17318431,32505856],[(168,0)]),([8,992,31744,1015808,1082401,3247203,4329604,8659208,17318431,32505856],[(168,0)]),([8,992,31744,1015808,1082431,2164802,4329604,32776456],[(1024,122150),(1024,65832)]),([8,992,31744,1015808,1082431,2164802,8659208,32641156],[(1024,88358),(1024,65832)]),([8,992,31744,1015808,4329604,8659208,17318431,32539681],[(96,0),(1024,301697),(1024,67223)]),([8,992,31744,1015808,4329604,8659208,17318431,32573506],[(96,0),(1024,300532),(1024,66034),(1025,88761)]),([8,992,31744,1048575,1082401,4329604,8659208,17318431],[(128,0),(1024,83425),(1024,67255)]),([8,992,31744,1082401,2164802,4329631,17809936,32505856],[(1024,472133),(1024,313416)]),([8,992,31744,1082401,2164802,8659231,17809936,32505856],[(1024,471109),(1024,476238)]),([8,992,31744,1082401,2164831,4329604,8659208,17809936,32505856],[(58,0),(72,0),(73,0),(74,0),(80,0),(81,0),(82,0),(114,0),(229,0)]),([8,992,31744,1082401,2164831,4329604,32776456],[(1024,99790),(1024,66856),(1024,83239),(1025,469492),(1025,66034),(1025,267929),(1025,300532)]),([8,992,31744,1082401,2164831,8659208,32641156],[(1024,99790),(1024,66856),(1024,83239),(1025,469492),(1025,98803),(1025,300532),(1025,656057)]),([8,992,31744,1082401,3115074,4329604,8659208,17318431,32505856],[(58,0),(128,0),(129,0),(137,0),(177,0),(229,0),(1024,70295),(1024,69896),(1024,83425)]),([8,992,31744,1082401,4329604,8659208,16236000,32505856],[(96,0),(1024,491602),(1024,67255)]),([8,992,31744,1082401,4329604,8659208,17318431,32505856],[(96,0),(1024,83425),(1024,67255)]),([8,992,31744,1082401,4329604,8659208,17318431,32539681],[(96,0),(1024,83641),(1024,67255)]),([8,992,31744,1082401,4329604,8659208,17318431,33047056],[(1024,83425),(1024,67255),(1025,300729),(1025,318137),(1025,481977),(1025,483001)]),([8,992,31744,1082401,4329604,8682760,17318431,32505856],[(1024,83425),(1024,67255),(1025,459246),(1025,483001)]),([8,992,31744,1082401,4329604,12988812,17318431,32505856],[(1024,83425),(1024,100024),(1025,66034),(1025,89785)]),([8,992,31744,1082401,4329604,17318431,24895223,32505856],[(1024,711778),(1024,67255)]),([8,992,31744,1082401,4330468,8659208,17318431,32505856],[(56,0),(96,0),(1024,83425),(1024,67255),(1025,285368),(1025,295400)]),([8,992,31744,1082401,4357252,8659208,17318431,32505856],[(56,0),(96,0),(1024,83425),(1024,67255),(1025,459245),(1025,481977)]),([8,992,31744,1082401,8659208,12988812,17318431,32505856],[(136,0),(1024,67255),(1024,83425),(1025,98803),(1025,122553)]),([8,992,31744,1082401,8659208,17318431,29224827,32505856],[(1024,710722),(1024,83425)]),([8,992,31744,1082431,2164802,4329604,9412872,32505856],[(1024,117030),(1024,65832)]),([8,992,31744,1082431,2164802,5214340,8659208,32505856],[(1024,83238),(1024,65832)]),([8,992,31744,4329604,8659208,17318431,32539681],[(2,0),(6,0),(57,0),(58,0),(72,0),(73,0),(81,0),(105,0),(1024,67063),(1024,99832),(1024,83425),(1025,88761),(1025,122553),(1025,268984),(1025,470713)])]
def b57 : List Row := [([8,992,1015808,1082401,2164802,4329604,8682760,17318431],[(1024,112257),(1024,103051),(1025,88761)]),([8,992,1015808,1082401,2164802,4329604,8682760,17318431,32505856],[(1024,70130),(1024,70295),(1024,70327),(1024,88705)]),([8,992,1015808,1082401,2164802,4329631,8659208,17333776,32505856],[(80,0),(1024,507969)]),([8,992,1015808,1082401,2164802,4357252,8659208,17318431],[(80,0),(1024,78465),(1024,70283),(1025,122553)]),([8,992,1015808,1082401,2164802,4357252,8659208,17318431,32505856],[(74,0),(105,0),(177,0),(201,0),(281,0),(301,0),(1024,70123),(1024,70283),(1024,70316),(1024,66199),(1024,69896)]),([8,992,1015808,1082401,2164831,4329604,32776456],[(1024,67021),(1024,99790),(1024,78119),(1025,469657),(1025,77261)]),([8,992,1015808,1082401,2164831,8659208,32641156],[(1024,67021),(1024,99790),(1024,78119),(1025,110030),(1025,469492)]),([8,992,1015808,1082401,2194498,4329604,33047056],[(1024,299080),(1024,459863),(1024,462925),(1025,98803),(1025,112313)]),([8,992,1015808,1082401,2194498,8659208,33047056],[(72,0),(1024,299080),(1024,459845),(1024,462914),(1025,66034),(1025,73017),(1025,98803)]),([8,992,1015808,1082401,4329604,8682760,17318431],[(1024,67255),(1024,99979),(1024,88705),(1025,88761),(1025,268984)]),([8,992,1015808,1082401,4329604,8682760,17318431,32505856],[(1024,110265),(1024,67255)]),([8,992,1015808,1082401,4357252,8659208,17318431],[(1024,67244),(1024,100024),(1024,77441),(1025,122553),(1025,268984),(1025,301753)]),([8,992,1015808,1082401,4357252,8659208,17318431,32505856],[(1024,77497),(1024,67255)]),([8,992,1015808,1082431,2164802,4329604,32776456],[(1024,65997),(1024,98766),(1024,78118),(1025,470713),(1025,76237)]),([8,992,1015808,1082431,2164802,8659208,32641156],[(1024,65997),(1024,98766),(1024,78118),(1025,109006),(1025,470713)]),([8,992,1015808,1113121,2164802,4329604,33047056],[(1024,299080),(1024,458839),(1024,462925),(1025,100025),(1025,112115)]),([8,992,1015808,2164802,4329604,8682760,17318431],[(1024,66199),(1024,98803),(1024,88564),(1025,88729),(1025,267928),(1025,88761)]),([8,992,1015808,2164802,4329604,8682760,17318431,32505856],[(1024,109044),(1024,66034),(1025,83444)]),([8,992,1015808,2164802,4357252,8659208,17318431],[(1024,66187),(1024,98803),(1024,76276),(1025,122521),(1025,300697),(1025,267928),(1025,122553)]),([8,992,1082401,2164802,4329604,8682760,17318431,32505856],[(1024,112097),(1024,102891)]),([8,992,1082401,4329604,8682760,17318431,32505856],[(2,0),(73,0),(1024,67255),(1024,99819),(1024,83425),(1025,88761),(1025,66034),(1025,267763),(1025,268779),(1025,268984),(1025,300532),(1025,483001)]),([8,992,1082401,4357252,8659208,17318431,32505856],[(2,0),(6,0),(73,0),(113,0),(177,0),(1024,100024),(1024,67051),(1024,77281),(1025,122553),(1025,98803),(1025,268984),(1025,295399),(1025,300532),(1025,459250),(1025,481977)]),([8,992,1082431,2164802,4329604,9412872,32505856],[(1024,65997),(1024,98766),(1024,78118),(1025,469492),(1025,470713)]),([8,992,1113121,2164802,4329604,17809936,32505856],[(1024,299080),(1024,458834),(1024,462925),(1025,112116),(1025,100024)]),([8,992,2164802,4329604,8682760,17318431,32505856],[(1024,66034),(1024,98795),(1024,83425),(1025,83444),(1025,267763),(1025,88729)]),([8,31744,1015808,1082401,2164802,4329631,17318896,32505856],[(1024,472133),(1024,510017)]),([8,31744,1082401,3115074,4329604,8659944,32505856],[(1024,69736),(1024,102862),(1024,462925),(1025,69928),(1025,66034)]),([9,4,31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],[(72,0)]),([9,31,256,1015808,1082401,2164802,17318416,32505856],[(56,0),(177,0),(1024,72997),(1024,302149),(1024,496948),(1025,102862),(1025,98803),(1025,98968),(1025,469492),(1025,470713)]),([9,31,992,31744,32768,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(168,0),(176,0),(184,0),(224,0),(432,0)]),([9,31,992,31744,32768,4329604,8659208,17318416,32505856],[(136,0),(296,0),(1024,66199),(1024,98968)])]
def t53 : BT := .nd (blockTree b56) [8,992,1015808,1082401,2164802,4329604,8659231,17333776,32505856] (blockTree b57)
def b58 : List Row := [([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(168,0),(176,0),(184,0),(224,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32641156],[(128,0),(168,0),(224,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32776456],[(128,0),(136,0),(168,0),(176,0),(224,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,33047056],[(136,0),(144,0),(176,0),(184,0),(224,0),(356,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32505856],[(128,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856,33047056],[(128,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],[(357,0),(1024,314854),(1024,319560),(1024,483438)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[]),([9,31,992,31744,1015808,1082401,2164802,4329604,9412872,17318416,32505856],[(128,0),(136,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856,32776456],[(128,0),(136,0),(168,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],[(128,0),(129,0),(168,0),(169,0),(293,0),(1024,69928),(1024,122309),(1024,117217)]),([9,31,992,31744,1015808,1082401,2164802,4329604,32776456],[(1024,69928),(1024,102862)]),([9,31,992,31744,1015808,1082401,2164802,4329604,33047056],[(1024,472165),(1024,510049)]),([9,31,992,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[(80,0),(136,0),(144,0),(176,0),(224,0)]),([9,31,992,31744,1015808,1082401,2164802,4357252,8659208,17318416,32505856],[(136,0),(144,0),(176,0)]),([9,31,992,31744,1015808,1082401,2164802,5214340,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(176,0)]),([9,31,992,31744,1015808,1082401,2164802,8659208,12988812,17318416,32505856],[(128,0),(136,0),(144,0),(168,0),(176,0),(184,0),(288,0)]),([9,31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856,32641156],[(128,0),(136,0),(144,0),(168,0),(176,0)]),([9,31,992,31744,1015808,1082401,2164802,8659208,17318416,32641156],[(128,0),(129,0),(137,0),(168,0),(169,0),(177,0),(293,0),(1024,677985),(1024,678182),(1024,678347),(1024,678150)]),([9,31,992,31744,1015808,1082401,2164802,8659208,32641156],[(1024,69928),(1024,102862)]),([9,31,992,31744,1015808,1082401,2164802,8659208,33047056],[(1024,302149),(1024,508993)]),([9,31,992,31744,1015808,1082401,2164802,8659231,17318416],[(1024,320134),(1024,302149),(1025,98808),(1025,102872),(1025,266536)]),([9,31,992,31744,1015808,1082401,2164802,17318416,32641156],[(1024,472165),(1024,510049)]),([9,31,992,31744,1015808,1082401,2164802,17318416,32776456],[(1024,710722),(1024,302149)]),([9,31,992,31744,1015808,1082401,2164831,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(168,0),(224,0)]),([9,31,992,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[(80,0),(128,0),(136,0),(144,0),(176,0),(184,0),(224,0)]),([9,31,992,31744,1015808,1082401,2194498,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(184,0),(224,0)]),([9,31,992,31744,1015808,1082401,3115074,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(224,0)]),([9,31,992,31744,1015808,1082401,3247203,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(168,0),(176,0),(184,0),(224,0)]),([9,31,992,31744,1015808,1082401,4329604,8659208,17318416,32573506],[(168,0),(216,0),(1024,83618),(1024,70327),(1024,73378),(1024,78498),(1024,112290),(1024,117410),(1024,315047)]),([9,31,992,31744,1015808,2164802,4329604,8659208,17318416,32539681],[(168,0),(216,0),(1024,67063),(1024,70295),(1024,73345),(1024,78465),(1024,112257)])]
def b59 : List Row := [([9,31,992,31744,1015808,4329604,8659208,17318416,32573506],[(136,0),(1024,98803),(1024,66034),(1025,67255)]),([9,31,992,31744,1048575,1082401,4329604,8659208,17318416],[(176,0),(1024,83425),(1024,67255)]),([9,31,992,31744,1082401,2164802,4329604,8659208,17809936],[(1024,88705),(1024,286342)]),([9,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[(97,0),(129,0),(293,0),(1024,314440),(1024,315014),(1024,478318),(1024,315047)]),([9,31,992,31744,1082401,2164802,4329604,8659208,32539681],[(1024,102862),(1024,69928),(1025,66201),(1025,98969),(1025,656057)]),([9,31,992,31744,1082401,2164802,4329604,8659208,33047056],[(1024,478699),(1024,83425)]),([9,31,992,31744,1082401,2164802,4329604,9412872],[(1024,320134),(1024,69928),(1024,88705),(1025,470713),(1025,300697)]),([9,31,992,31744,1082401,2164802,4329604,9412872,17318416],[(1024,483979),(1024,88705)]),([9,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],[(96,0),(97,0),(104,0),(105,0),(293,0),(1024,117189),(1024,117377),(1024,69928),(1024,117410)]),([9,31,992,31744,1082401,2164802,4329604,9412872,32505856],[(1024,69928),(1024,102862)]),([9,31,992,31744,1082401,2164802,4329604,17318416,32539681],[(1024,711778),(1024,83425),(1025,66200),(1025,300697),(1025,666296)]),([9,31,992,31744,1082401,2164802,4329604,17318416,32776456],[(128,0),(1024,281062),(1024,83425)]),([9,31,992,31744,1082401,2164802,4329604,17809936],[(1024,122497),(1024,286342),(1024,472165),(1025,100024),(1025,267928)]),([9,31,992,31744,1082401,2164802,4329604,17809936,32505856],[(1024,711943),(1024,472165)]),([9,31,992,31744,1082401,2164802,4329604,32776456],[(1024,83425),(1024,102862),(1024,69928),(1025,469492),(1025,300532),(1025,66034),(1025,98969)]),([9,31,992,31744,1082401,2164802,4329604,33047056],[(1024,117217),(1024,281062),(1024,472165),(1025,98803),(1025,267763),(1025,66034),(1025,300697)]),([9,31,992,31744,1082401,2164802,5214340,8659208],[(1024,102862),(1024,69928),(1024,83585),(1025,301753),(1025,469657)]),([9,31,992,31744,1082401,2164802,5214340,8659208,17318416],[(1024,483979),(1024,83585)]),([9,31,992,31744,1082401,2164802,5214340,8659208,17318416,32505856],[(96,0),(97,0),(105,0),(113,0),(136,0),(137,0),(145,0),(233,0),(293,0),(1024,83237),(1024,83397),(1024,83585),(1024,69907),(1024,69928),(1024,83618),(1024,509190)]),([9,31,992,31744,1082401,2164802,5214340,8659208,32505856],[(1024,102862),(1024,69928)]),([9,31,992,31744,1082401,2164802,5214340,17318416],[(1024,472165),(1024,83585),(1024,286342),(1025,268984),(1025,98968)]),([9,31,992,31744,1082401,2164802,5214340,17318416,32505856],[(1024,711778),(1024,472165)]),([9,31,992,31744,1082401,2164802,8659208,17318416,32539681],[(1024,314854),(1024,83425),(1025,98968),(1025,300697),(1025,661175),(1025,666295)]),([9,31,992,31744,1082401,2164802,8659208,17318416,32641156],[(128,0),(1024,83425),(1024,281062)]),([9,31,992,31744,1082401,2164802,8659208,17809936],[(1024,88705),(1024,286342),(1024,302149),(1025,67255),(1025,66199),(1025,69928),(1025,70093),(1025,98968)]),([9,31,992,31744,1082401,2164802,8659208,17809936,32505856],[(1024,302149),(1024,508993)]),([9,31,992,31744,1082401,2164802,8659208,32641156],[(1024,83425),(1024,102862),(1024,69928),(1025,300532),(1025,469492),(1025,66201),(1025,98803)]),([9,31,992,31744,1082401,2164802,8659208,33047056],[(1024,83425),(1024,281062),(1024,302149),(1025,66034),(1025,98803),(1025,69928),(1025,70093),(1025,300697)]),([9,31,992,31744,1082401,2164802,8659231,17318416,32505856],[(1024,314854),(1024,302149),(1025,98968),(1025,99603),(1025,102867),(1025,266536)]),([9,31,992,31744,1082401,2164802,9412872,17318416],[(1024,88705),(1024,270001),(1024,280198),(1025,67255),(1025,66199),(1025,69928),(1025,70093),(1025,98808)]),([9,31,992,31744,1082401,2164802,9412872,17318416,32505856],[(1024,508993),(1024,302149)])]
def t54 : BT := .nd (blockTree b58) [9,31,992,31744,1015808,4329604,8659208,17318416,32539681] (blockTree b59)
def t55 : BT := .nd t53 [9,31,992,31744,65536,4329604,8659208,17318416] t54
def b60 : List Row := [([9,31,992,31744,1082401,2164802,17318416,32776456],[(1024,83425),(1024,281062),(1024,302149),(1025,66034),(1025,98968),(1025,69928),(1025,70093),(1025,300532)]),([9,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],[(82,0),(97,0),(105,0),(113,0),(176,0),(177,0),(185,0),(233,0),(273,0),(293,0),(1024,507969),(1024,508001),(1024,508198),(1024,508166),(1024,508363),(1024,66199),(1024,83425),(1024,462958)]),([9,31,992,31744,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,102862)]),([9,31,992,31744,1082401,3115074,4329604,17318416,32505856],[(168,0),(1024,508001),(1024,472165),(1025,267763)]),([9,31,992,31744,1082401,3115074,8659208,17318416,32505856],[(168,0),(1024,507969),(1024,302149),(1025,102696)]),([9,31,992,31744,1082401,3247203,4329604,8659208,32505856],[(1024,712999),(1024,69928),(1025,66034),(1025,98803)]),([9,31,992,31744,1082401,3247203,4329604,17318416,32505856],[(1024,711778),(1024,83425),(1025,66034),(1025,300532)]),([9,31,992,31744,1082401,3247203,8659208,17318416,32505856],[(1024,710722),(1024,83425),(1025,98803),(1025,300532)]),([9,31,992,31744,1082401,4329604,8659208,16236015,32505856],[(1024,712999),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32505856],[(136,0),(1024,83425),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32539681],[(136,0),(1024,100024),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32641156],[(136,0),(1024,281062),(1024,83425),(1025,66231),(1025,88761)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32776456],[(1024,281062),(1024,67255),(1025,99000),(1025,122553),(1025,285368)]),([9,31,992,31744,1082401,4329604,8659208,17318416,33047056],[(1024,478699),(1024,67255),(1025,300729),(1025,318137),(1025,481977),(1025,483001)]),([9,31,992,31744,1082401,4329604,8659208,17318431,32505856],[(96,0),(1024,301753),(1024,67255),(1025,88761)]),([9,31,992,31744,1082401,4329604,8659208,17809936],[(1024,67255),(1024,100024),(1024,88705),(1025,301753),(1025,67255)]),([9,31,992,31744,1082401,4329604,8659208,17809936,32505856],[(1024,67255),(1024,100024)]),([9,31,992,31744,1082401,4329604,8659208,21648020,32505856],[(1024,301753),(1024,69928),(1025,66034),(1025,268584)]),([9,31,992,31744,1082401,4329604,8659208,25977624,32505856],[(1024,102862),(1024,67255),(1025,98803)]),([9,31,992,31744,1082401,4329604,8682760,17318416,32505856],[(1024,100024),(1024,67255),(1025,483001)]),([9,31,992,31744,1082401,4329604,9412872,17318416],[(1024,67255),(1024,100017),(1024,88705),(1025,100024),(1025,301753)]),([9,31,992,31744,1082401,4329604,9412872,17318416,32505856],[(96,0),(104,0),(1024,67255),(1024,100024)]),([9,31,992,31744,1082401,4329604,12988812,17318416,32505856],[(1024,100024),(1024,83425),(1025,66034),(1025,268584)]),([9,31,992,31744,1082401,4329604,17318416,24895223,32505856],[(1024,711778),(1024,67255)]),([9,31,992,31744,1082401,4329604,17318416,25977624,32505856],[(136,0),(1024,100024),(1024,67255),(1025,66661),(1025,300532)]),([9,31,992,31744,1082401,4330468,8659208,17318416,32505856],[(80,0),(104,0),(136,0),(1024,67255),(1024,83425),(1025,285368)]),([9,31,992,31744,1082401,4357252,8659208,17318416,32505856],[(80,0),(112,0),(136,0),(1024,100024),(1024,67255),(1025,481977)]),([9,31,992,31744,1082401,5214340,8659208,17318416],[(1024,67249),(1024,100024),(1024,82561),(1025,67255),(1025,268984)]),([9,31,992,31744,1082401,5214340,8659208,17318416,32505856],[(96,0),(1024,67255),(1024,100024)]),([9,31,992,31744,1082401,8659208,12988812,17318416,32505856],[(184,0),(1024,67255),(1024,83425),(1025,98803)]),([9,31,992,31744,1082401,8659208,17318416,21648020,32505856],[(1024,67255),(1024,83425),(1025,66661),(1025,300532)]),([9,31,992,31744,1082401,8659208,17318416,29224827,32505856],[(1024,710722),(1024,83425)])]
def b61 : List Row := [([9,31,992,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[(1024,65997),(1024,67021),(1024,83397),(1024,88517),(1024,117189),(1024,122309),(1024,508363)]),([9,31,992,1015808,1082401,2164802,4329604,8682760,17318416],[(1024,483979),(1024,88705),(1025,67255)]),([9,31,992,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[(273,0),(1024,112097),(1024,112257),(1024,111909),(1024,112290),(1024,66199)]),([9,31,992,1015808,1082401,2164802,4329604,17318416,32776456],[(96,0),(104,0),(128,0),(136,0),(1024,502228),(1024,78277)]),([9,31,992,1015808,1082401,2164802,4329604,32776456],[(1024,70093),(1024,102862),(1024,78277),(1025,469657),(1025,70093)]),([9,31,992,1015808,1082401,2164802,4329631,17318416,32505856],[(1024,510017),(1024,472133),(1025,98803),(1025,98968)]),([9,31,992,1015808,1082401,2164802,4357252,8659208,17318416],[(112,0),(1024,320134),(1024,78465),(1025,67255)]),([9,31,992,1015808,1082401,2164802,4357252,8659208,17318416,32505856],[(98,0),(104,0),(105,0),(106,0),(136,0),(137,0),(145,0),(233,0),(257,0),(273,0),(289,0),(353,0),(373,0),(1024,72997),(1024,78305),(1024,78465),(1024,78498),(1024,66199)]),([9,31,992,1015808,1082401,2164802,4357252,17318416],[(1024,471141),(1024,78465),(1024,286342),(1025,98968),(1025,268984)]),([9,31,992,1015808,1082401,2164802,4357252,17318416,32505856],[(1024,711778),(1024,471141)]),([9,31,992,1015808,1082401,2164802,8659208,17318416,32641156],[(96,0),(128,0),(1024,502228),(1024,78277),(1025,102862)]),([9,31,992,1015808,1082401,2164802,8659208,32641156],[(1024,70093),(1024,102862),(1024,78277),(1025,102862),(1025,469492)]),([9,31,992,1015808,1082401,2164802,8659231,17318416,32505856],[(1024,508993),(1024,302149),(1025,98574),(1025,98803),(1025,98968),(1025,99598),(1025,102862),(1025,266536)]),([9,31,992,1015808,1082401,2164802,8682760,17318416],[(1024,88705),(1024,269963),(1024,275078),(1025,66199),(1025,67255),(1025,66034),(1025,69928),(1025,102872)]),([9,31,992,1015808,1082401,2164802,8682760,17318416,32505856],[(1024,302149),(1024,508993),(1025,102862)]),([9,31,992,1015808,1082401,2164802,17318416,32641156],[(1024,112069),(1024,472165),(1024,502228),(1025,102862),(1025,98803),(1025,98968),(1025,469492),(1025,470713)]),([9,31,992,1015808,1082401,2164802,17318416,32776456],[(1024,78277),(1024,269785),(1024,302149),(1025,70093),(1025,66034),(1025,69928),(1025,98968),(1025,269785),(1025,469492),(1025,470713)]),([9,31,992,1015808,1082401,2194498,4329604,17318416,32505856],[(168,0),(1024,679009),(1024,470117),(1025,267763)]),([9,31,992,1015808,1082401,2194498,8659208,17318416,32505856],[(104,0),(168,0),(1024,677953),(1024,302149),(1025,102696)]),([9,31,992,1015808,1082401,4329604,8682760,17318416],[(1024,67255),(1024,99979),(1024,88705),(1025,67255),(1025,268984)]),([9,31,992,1015808,1082401,4329604,8682760,17318416,32505856],[(1024,67255),(1024,100024)]),([9,31,992,1015808,1082401,4357252,8659208,17318416],[(1024,67244),(1024,100024),(1024,77441),(1025,268984),(1025,67255)]),([9,31,992,1015808,1082401,4357252,8659208,17318416,32505856],[(104,0),(1024,100024),(1024,67255)]),([9,31,992,1015808,1113121,2164802,4329604,17318416,32505856],[(168,0),(1024,711778),(1024,469093),(1025,268984)]),([9,31,992,1015808,2164802,4329604,8682760,17318416],[(1024,66199),(1024,98803),(1024,88705),(1025,66199),(1025,267928),(1025,67255)]),([9,31,992,1015808,2164802,4329604,8682760,17318416,32505856],[(1024,66034),(1024,98803),(1025,67058)]),([9,31,992,1015808,2164802,4357252,8659208,17318416],[(1024,66187),(1024,98803),(1024,76417),(1025,267928),(1025,66199),(1025,67255)]),([9,31,992,1082401,2164802,4329604,8682760,17318416,32505856],[(1024,478699),(1024,83425)]),([9,31,992,1082401,2164802,4329604,9412872,17318416,32505856],[(72,0),(80,0),(1024,502228),(1024,78277)]),([9,31,992,1082401,2164802,4329604,9412872,32505856],[(1024,70093),(1024,102862),(1024,78277),(1025,469492),(1025,70093)]),([9,31,992,1082401,2164802,4357252,17318416,32505856],[(1024,471141),(1024,78305),(1024,281062),(1025,98803),(1025,267763),(1025,98968),(1025,300532)])]
def t56 : BT := .nd (blockTree b60) [9,31,992,31744,4329604,8659208,17318416,32539681] (blockTree b61)
def b62 : List Row := [([9,31,992,1082401,2164802,5214340,17318416,32505856],[(177,0),(1024,112069),(1024,472165),(1024,502024),(1025,102862),(1025,98803),(1025,98968),(1025,469492),(1025,470713)]),([9,31,992,1082401,2164802,8682760,17318416,32505856],[(1024,83425),(1024,269803),(1024,274918),(1025,66034),(1025,66199),(1025,69928),(1025,102867),(1025,300532)]),([9,31,992,1082401,2164802,9412872,17318416,32505856],[(80,0),(1024,78277),(1024,269780),(1024,302149),(1025,70093),(1025,66199),(1025,69928),(1025,98803),(1025,269780),(1025,469492),(1025,470713)]),([9,31,992,1082401,2194498,4329604,17318416,32505856],[(1024,117217),(1024,281062),(1024,470117),(1025,98803),(1025,98968),(1025,66034),(1025,267763),(1025,300532),(1025,666296)]),([9,31,992,1082401,2194498,8659208,17318416,32505856],[(1024,83425),(1024,281062),(1024,302149),(1025,66034),(1025,66199),(1025,98803),(1025,69928),(1025,300532),(1025,666295)]),([9,31,992,1082401,3115074,4329604,8659208,32505856],[(1024,70093),(1024,102862),(1024,78277),(1025,70093),(1025,469492)]),([9,31,992,1082401,3115074,4329604,17318416,32505856],[(177,0),(1024,112069),(1024,472165),(1024,501858),(1025,102862),(1025,70093),(1025,98968),(1025,469492)]),([9,31,992,1082401,3115074,8659208,17318416,32505856],[(177,0),(1024,78277),(1024,302149),(1024,501826),(1025,70093),(1025,66199),(1025,69928),(1025,102862),(1025,469492)]),([9,31,992,1082401,4329604,8682760,17318416,32505856],[(2,0),(6,0),(57,0),(105,0),(169,0),(1024,67255),(1024,99819),(1024,83425),(1025,66034),(1025,67255),(1025,98803),(1025,99819),(1025,268779),(1025,268984),(1025,300532),(1025,483001)]),([9,31,992,1082401,4329604,9412872,17318416,32505856],[(72,0),(80,0),(1024,470713),(1024,67255),(1024,78277),(1025,470713),(1025,67255),(1025,70093),(1025,268756),(1025,268984),(1025,469492),(1025,502456)]),([9,31,992,1082401,4357252,8659208,17318416,32505856],[(2,0),(6,0),(10,0),(57,0),(58,0),(82,0),(105,0),(153,0),(169,0),(233,0),(1024,77281),(1024,100024),(1024,67051),(1025,66034),(1025,67051),(1025,67255),(1025,98803),(1025,268984),(1025,300532),(1025,481977)]),([9,31,992,2164802,4329604,8682760,17318416,32505856],[(1024,66034),(1024,98795),(1024,83425),(1025,66034),(1025,267763),(1025,66199)]),([9,31,1023,1015808,1082401,2164802,4329604,17318416,32505856],[(1024,72997),(1024,472165),(1025,98803),(1025,98968)]),([9,31,31744,1015808,1082401,2164802,4329604,8659208,17318896,32505856],[(168,0),(1024,65832),(1024,66856),(1024,78085),(1024,83237),(1024,88357),(1024,111909),(1024,508198)]),([9,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856],[(112,0),(1024,496915),(1024,69896),(1024,491602),(1024,502035),(1024,508166),(1024,509190),(1024,678150),(1024,699672)]),([9,31,31744,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,102862),(1024,69896)]),([9,31,31744,1015808,1082401,2164802,4329604,17318896,32505856],[(1024,472165),(1024,510049)]),([9,31,31744,1015808,1082401,2164802,8659208,32641156],[(96,0),(128,0),(1024,102862),(1024,69912),(1024,72997),(1025,69945),(1025,300532),(1025,70105)]),([9,31,31744,1015808,1082401,2164802,8659231,17318416,32505856],[(104,0),(1024,660760),(1024,302149),(1025,266536)]),([9,31,31744,1015808,1082401,2164802,17318416,32641156],[(1024,72997),(1024,472165),(1024,496915),(1025,267763),(1025,268984)]),([9,31,31744,1082401,2164802,5214340,8659208,32505856],[(72,0),(1024,102862),(1024,69907),(1024,72997),(1025,69940),(1025,300697),(1025,70100)]),([9,31,31744,1082401,2164802,5214340,17318416,32505856],[(1024,72997),(1024,472165),(1024,496904),(1025,267763),(1025,268984)]),([9,31,31744,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,72997),(1024,102862),(1025,69928),(1025,70093),(1025,300532)]),([9,31,31744,1082401,3115074,4329604,17318416,32505856],[(1024,72997),(1024,472165),(1024,496738),(1025,267763),(1025,267928),(1025,281272)]),([9,31,1015808,1082401,2164802,4329604,8659208,17318896,32505856],[(72,0),(96,0),(1024,78117),(1024,502068)]),([9,31,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[(72,0),(96,0),(168,0),(1024,660760),(1024,72997)]),([9,31,1015808,1082401,2164802,4329604,17318896,32505856],[(1024,111877),(1024,275557),(1024,502036),(1025,102862),(1025,98803),(1025,98968)]),([9,31,1015808,1082401,2164802,4357252,17318416,32505856],[(1024,72997),(1024,466021),(1024,496915),(1025,267763),(1025,268984)]),([9,992,31744,1015808,1082401,2164802,4329604,8659208,17318431],[(112,0),(168,0),(1024,88705),(1024,286342),(1025,88761)]),([9,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32505856],[(58,0),(98,0),(106,0),(145,0),(168,0),(169,0),(177,0),(185,0),(225,0),(233,0),(285,0),(353,0),(373,0),(1024,70130),(1024,70295),(1024,70327),(1024,69896),(1024,88705)]),([9,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],[(96,0),(104,0),(128,0),(136,0),(1024,491602),(1024,299080)]),([9,992,31744,1015808,1082401,2164802,4329604,33047056],[(1024,299080),(1024,462925),(1024,472151),(1025,98803),(1025,100025)])]
def b63 : List Row := [([9,992,31744,1015808,1082401,2164831,4329604,8659208,32505856],[(1024,680230),(1024,66856)]),([9,992,31744,1015808,1082401,4329604,8659208,17318431],[(128,0),(1024,67255),(1024,100024),(1024,88705),(1025,88761),(1025,268984)]),([9,992,31744,1015808,1082401,4329604,8659208,17318431,32505856],[(128,0),(1024,301753),(1024,67255)]),([9,992,31744,1015808,2164802,4329604,8659208,17318431],[(128,0),(1024,66199),(1024,98803),(1024,88564),(1025,88729),(1025,267928),(1025,88761)]),([9,992,31744,1082401,2164802,4329604,17809936,32505856],[(1024,299080),(1024,462925),(1024,472146),(1025,98804),(1025,100024)]),([9,992,31744,1082401,2164802,8659208,17809936,32505856],[(72,0),(80,0),(1024,299080),(1024,462925),(1024,302149),(1025,66199),(1025,73012),(1025,98804)]),([9,992,31744,1082401,2164831,4329604,8659208,32505856],[(1024,99790),(1024,66856),(1024,83239),(1025,469492),(1025,300532),(1025,66034),(1025,98803),(1025,300697),(1025,656057)]),([9,992,31744,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,102862),(1024,299080),(1025,69928),(1025,102862)]),([9,992,31744,1082401,4329604,8659208,17318431,32505856],[(2,0),(6,0),(10,0),(57,0),(58,0),(96,0),(97,0),(105,0),(137,0),(233,0),(1024,67255),(1024,100024),(1024,83425),(1025,88761),(1025,66034),(1025,98803),(1025,122553),(1025,268984),(1025,295399),(1025,300532),(1025,459244),(1025,470713)]),([9,31744,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,69736),(1024,102862),(1024,462925),(1025,69928),(1025,299470)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208],[(1024,102862),(1024,69928),(1024,88705),(1025,300697),(1025,470713)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416],[(152,0),(224,0),(1024,286342),(1024,88705),(1025,67255)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(82,0),(128,0),(129,0),(130,0),(136,0),(137,0),(138,0),(144,0),(145,0),(146,0),(152,0),(168,0),(169,0),(176,0),(177,0),(184,0),(185,0),(193,0),(216,0),(224,0),(225,0),(233,0),(241,0),(272,0),(289,0),(297,0),(337,0),(357,0),(361,0),(433,0),(453,0),(1024,66034),(1024,67255),(1024,69928),(1024,299080),(1024,302149),(1024,472165),(1024,491635),(1024,496915),(1024,66199),(1024,78277),(1024,88705)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[(128,0),(1024,69928),(1024,102862)]),([10,31,992,31744,1015808,1082401,2164802,4329604,17318416],[(1024,472165),(1024,88705),(1024,286342),(1025,267928),(1025,100024)]),([10,31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],[(216,0),(1024,472165),(1024,510049),(1025,267763)]),([10,31,992,31744,1015808,1082401,2164802,8659208,17318416],[(1024,88705),(1024,286342),(1024,302149),(1025,66199),(1025,67255),(1025,66034),(1025,69928),(1025,70093),(1025,98968)]),([10,31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],[(136,0),(144,0),(176,0),(216,0),(1024,508993),(1024,302149),(1025,102696)]),([10,31,992,31744,1015808,1082401,4329604,8659208,17318416],[(176,0),(1024,67255),(1024,100024),(1024,88705),(1025,67255),(1025,268984)]),([10,31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],[(128,0),(136,0),(144,0),(176,0),(1024,67255),(1024,100024)]),([10,31,992,31744,1015808,2164802,4329604,8659208,17318416],[(176,0),(1024,66199),(1024,98803),(1024,88705),(1025,66199),(1025,267928),(1025,67255)]),([10,31,992,31744,1082401,2164802,4329604,8659208,32505856],[(1024,83425),(1024,102862),(1024,69928),(1025,300532),(1025,469492),(1025,66034),(1025,98803),(1025,300697)]),([10,31,992,31744,1082401,2164802,4329604,17318416,32505856],[(1024,472165),(1024,83425),(1024,281062),(1025,267763),(1025,98803),(1025,66034),(1025,98968),(1025,300532)]),([10,31,992,31744,1082401,2164802,8659208,17318416,32505856],[(136,0),(1024,83425),(1024,281062),(1024,302149),(1025,66034),(1025,66199),(1025,98803),(1025,69928),(1025,70093),(1025,300532)]),([10,31,992,31744,1082401,4329604,8659208,17318416,32505856],[(2,0),(6,0),(10,0),(14,0),(57,0),(58,0),(73,0),(74,0),(81,0),(82,0),(98,0),(106,0),(114,0),(136,0),(137,0),(145,0),(185,0),(217,0),(297,0),(1024,67255),(1024,100024),(1024,83425),(1025,66034),(1025,67255),(1025,98803),(1025,268984),(1025,300532),(1025,470713)]),([10,31,992,1015808,1082401,2164802,4329604,8659208,32505856],[(96,0),(128,0),(1024,70093),(1024,102862),(1024,78277),(1025,70093),(1025,469492)]),([10,31,992,1015808,1082401,2164802,4329604,17318416,32505856],[(225,0),(1024,112069),(1024,472165),(1024,502228),(1025,102862),(1025,70093),(1025,98803),(1025,98968),(1025,469492),(1025,470713)]),([10,31,992,1015808,1082401,2164802,8659208,17318416,32505856],[(104,0),(136,0),(225,0),(1024,78277),(1024,302149),(1024,502228),(1025,70093),(1025,66034),(1025,66199),(1025,69928),(1025,102862),(1025,469492),(1025,470713)]),([10,31,31744,1015808,1082401,2164802,4329604,8659208,32505856],[(96,0),(128,0),(1024,69928),(1024,72997),(1024,102862),(1025,69928),(1025,70093),(1025,300532)]),([10,31,31744,1015808,1082401,2164802,4329604,17318416,32505856],[(104,0),(136,0),(1024,72997),(1024,472165),(1024,496915),(1025,267763),(1025,268984)]),([10,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[(1024,69928),(1024,102862),(1024,299080),(1025,69928),(1025,102862)])]
def t57 : BT := .nd (blockTree b62) [9,992,31744,1015808,1082401,2164802,8659208,33047056] (blockTree b63)
def t58 : BT := .nd t56 [9,31,992,1082401,2164802,5214340,8659208,32505856] t57
def t59 : BT := .nd t55 [9,31,992,31744,1082401,2164802,17318416,32641156] t58
def t60 : BT := .nd t52 [8,992,31744,1015808,1082401,2164831,4329604,8659208,17809936,32505856] t59
def t61 : BT := .nd t45 [8,31,992,31744,4329604,8659208,16236015,32539681] t60
def t62 : BT := .nd t30 [7,31,992,4422788,8659208,17318416] t61
def mT : BT := t62
def mP := bigStep 33554431 Y_ PD_ PM_ G_ mT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb0 : Covered mP (blockTree b0) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb1 : Covered mP (blockTree b1) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb2 : Covered mP (blockTree b2) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb3 : Covered mP (blockTree b3) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb4 : Covered mP (blockTree b4) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb5 : Covered mP (blockTree b5) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb6 : Covered mP (blockTree b6) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb7 : Covered mP (blockTree b7) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb8 : Covered mP (blockTree b8) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb9 : Covered mP (blockTree b9) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb10 : Covered mP (blockTree b10) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb11 : Covered mP (blockTree b11) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb12 : Covered mP (blockTree b12) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb13 : Covered mP (blockTree b13) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb14 : Covered mP (blockTree b14) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb15 : Covered mP (blockTree b15) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb16 : Covered mP (blockTree b16) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb17 : Covered mP (blockTree b17) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb18 : Covered mP (blockTree b18) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb19 : Covered mP (blockTree b19) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb20 : Covered mP (blockTree b20) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb21 : Covered mP (blockTree b21) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb22 : Covered mP (blockTree b22) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb23 : Covered mP (blockTree b23) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb24 : Covered mP (blockTree b24) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb25 : Covered mP (blockTree b25) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb26 : Covered mP (blockTree b26) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb27 : Covered mP (blockTree b27) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb28 : Covered mP (blockTree b28) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb29 : Covered mP (blockTree b29) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb30 : Covered mP (blockTree b30) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb31 : Covered mP (blockTree b31) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb32 : Covered mP (blockTree b32) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb33 : Covered mP (blockTree b33) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb34 : Covered mP (blockTree b34) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb35 : Covered mP (blockTree b35) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb36 : Covered mP (blockTree b36) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb37 : Covered mP (blockTree b37) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb38 : Covered mP (blockTree b38) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb39 : Covered mP (blockTree b39) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb40 : Covered mP (blockTree b40) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb41 : Covered mP (blockTree b41) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb42 : Covered mP (blockTree b42) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb43 : Covered mP (blockTree b43) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb44 : Covered mP (blockTree b44) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb45 : Covered mP (blockTree b45) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb46 : Covered mP (blockTree b46) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb47 : Covered mP (blockTree b47) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb48 : Covered mP (blockTree b48) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb49 : Covered mP (blockTree b49) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb50 : Covered mP (blockTree b50) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb51 : Covered mP (blockTree b51) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb52 : Covered mP (blockTree b52) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb53 : Covered mP (blockTree b53) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb54 : Covered mP (blockTree b54) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb55 : Covered mP (blockTree b55) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb56 : Covered mP (blockTree b56) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb57 : Covered mP (blockTree b57) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb58 : Covered mP (blockTree b58) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb59 : Covered mP (blockTree b59) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb60 : Covered mP (blockTree b60) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb61 : Covered mP (blockTree b61) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb62 : Covered mP (blockTree b62) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb63 : Covered mP (blockTree b63) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct0 : Covered mP t0 := coveredNode cb0 cb1 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct1 : Covered mP t1 := coveredNode cb2 cb3 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct2 : Covered mP t2 := coveredNode ct0 ct1 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct3 : Covered mP t3 := coveredNode cb4 cb5 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct4 : Covered mP t4 := coveredNode cb6 cb7 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct5 : Covered mP t5 := coveredNode ct3 ct4 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct6 : Covered mP t6 := coveredNode ct2 ct5 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct7 : Covered mP t7 := coveredNode cb8 cb9 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct8 : Covered mP t8 := coveredNode cb10 cb11 (h := [(104,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct9 : Covered mP t9 := coveredNode ct7 ct8 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct10 : Covered mP t10 := coveredNode cb12 cb13 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct11 : Covered mP t11 := coveredNode cb14 cb15 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct12 : Covered mP t12 := coveredNode ct10 ct11 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct13 : Covered mP t13 := coveredNode ct9 ct12 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct14 : Covered mP t14 := coveredNode ct6 ct13 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct15 : Covered mP t15 := coveredNode cb16 cb17 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct16 : Covered mP t16 := coveredNode cb18 cb19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct17 : Covered mP t17 := coveredNode ct15 ct16 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct18 : Covered mP t18 := coveredNode cb20 cb21 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct19 : Covered mP t19 := coveredNode cb22 cb23 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct20 : Covered mP t20 := coveredNode ct18 ct19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct21 : Covered mP t21 := coveredNode ct17 ct20 (h := [(168,0),(272,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct22 : Covered mP t22 := coveredNode cb24 cb25 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct23 : Covered mP t23 := coveredNode cb26 cb27 (h := [(72,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct24 : Covered mP t24 := coveredNode ct22 ct23 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct25 : Covered mP t25 := coveredNode cb28 cb29 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct26 : Covered mP t26 := coveredNode cb30 cb31 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct27 : Covered mP t27 := coveredNode ct25 ct26 (h := [(72,0),(80,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct28 : Covered mP t28 := coveredNode ct24 ct27 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct29 : Covered mP t29 := coveredNode ct21 ct28 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct30 : Covered mP t30 := coveredNode ct14 ct29 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct31 : Covered mP t31 := coveredNode cb32 cb33 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct32 : Covered mP t32 := coveredNode cb34 cb35 (h := [(216,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct33 : Covered mP t33 := coveredNode ct31 ct32 (h := [(72,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct34 : Covered mP t34 := coveredNode cb36 cb37 (h := [(1024,317505),(1024,300101)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct35 : Covered mP t35 := coveredNode cb38 cb39 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct36 : Covered mP t36 := coveredNode ct34 ct35 (h := [(72,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct37 : Covered mP t37 := coveredNode ct33 ct36 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct38 : Covered mP t38 := coveredNode cb40 cb41 (h := [(1024,76276),(1024,66034),(1025,122553)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct39 : Covered mP t39 := coveredNode cb42 cb43 (h := [(128,0),(168,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct40 : Covered mP t40 := coveredNode ct38 ct39 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct41 : Covered mP t41 := coveredNode cb44 cb45 (h := [(104,0),(292,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct42 : Covered mP t42 := coveredNode cb46 cb47 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct43 : Covered mP t43 := coveredNode ct41 ct42 (h := [(96,0),(136,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct44 : Covered mP t44 := coveredNode ct40 ct43 (h := [(128,0),(136,0),(144,0),(224,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct45 : Covered mP t45 := coveredNode ct37 ct44 (h := [(72,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct46 : Covered mP t46 := coveredNode cb48 cb49 (h := [(128,0),(136,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct47 : Covered mP t47 := coveredNode cb50 cb51 (h := [(72,0),(80,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct48 : Covered mP t48 := coveredNode ct46 ct47 (h := [(97,0),(1024,314854),(1024,319560),(1024,470136)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct49 : Covered mP t49 := coveredNode cb52 cb53 (h := [(1024,67255),(1024,83425)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct50 : Covered mP t50 := coveredNode cb54 cb55 (h := [(72,0),(96,0),(1024,665896),(1024,78117)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct51 : Covered mP t51 := coveredNode ct49 ct50 (h := [(1024,677953),(1024,284738)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct52 : Covered mP t52 := coveredNode ct48 ct51 (h := [(1024,711778),(1024,471141)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct53 : Covered mP t53 := coveredNode cb56 cb57 (h := [(1024,508001)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct54 : Covered mP t54 := coveredNode cb58 cb59 (h := [(136,0),(1024,67223),(1024,99992)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct55 : Covered mP t55 := coveredNode ct53 ct54 (h := [(96,0),(104,0),(112,0),(136,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct56 : Covered mP t56 := coveredNode cb60 cb61 (h := [(2,0),(6,0),(10,0),(57,0),(58,0),(73,0),(74,0),(81,0),(82,0),(104,0),(105,0),(113,0),(145,0),(169,0),(1024,67063),(1024,99832),(1024,83425),(1025,66231),(1025,67255),(1025,99000),(1025,268984),(1025,300729),(1025,470713)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct57 : Covered mP t57 := coveredNode cb62 cb63 (h := [(96,0),(104,0),(128,0),(1024,299080),(1024,462925),(1024,302149),(1025,66034),(1025,67257),(1025,98803)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct58 : Covered mP t58 := coveredNode ct56 ct57 (h := [(72,0),(1024,70093),(1024,102862),(1024,78277),(1025,102862),(1025,469492)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct59 : Covered mP t59 := coveredNode ct55 ct58 (h := [(1024,472165),(1024,83425),(1024,281062),(1025,267763),(1025,66200),(1025,98803),(1025,300532)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct60 : Covered mP t60 := coveredNode ct52 ct59 (h := [(96,0),(104,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct61 : Covered mP t61 := coveredNode ct45 ct60 (h := [(1024,516391),(1024,67063)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct62 : Covered mP t62 := coveredNode ct30 ct61 (h := [(1024,66027),(1024,98803),(1024,76257),(1025,67255),(1025,268984)]) (by decide +kernel)
theorem mgood : Covered mP mT := ct62
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)) C) :=
  bigSigned 3195660 10 2 0 PD_ PM_ XS_ G_ mT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) mgood (by decide +kernel)
end PEqualNP.Outside.L_meta_19528_aux

theorem PEqualNP.Outside.L_meta_19528 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19528_aux.result
