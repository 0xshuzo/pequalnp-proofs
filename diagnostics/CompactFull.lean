import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19527_aux

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



def Y_ : Nat := 3187468
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,2683530),(2,3967951),(3,3585901),(4,1288508),(5,75284),(6,24960),(7,49738),(8,37807),(9,47965),(10,12068),(11,9496),(12,6),(13,649),(14,974),(15,877),(16,316),(17,20),(19,10),(20,15),(21,13),(22,4)]
def PM_ : List (Nat × Nat) := [(0,3187468),(1,3187468),(4,3187468),(5,3187468),(6,3187468),(7,3187468),(10,3187468),(11,3187468),(12,3187468),(14,3187468),(16,3187468),(17,3187468),(18,3187468),(19,3187468),(22,3187468),(23,3187468),(24,3187468)]
def G_ : List (List Nat) := [[5,6,9,8,7,0,1,4,3,2,10,11,14,13,12,15,16,19,18,17,20,21,24,23,22]]

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


def b0 : List Row := [([3,31,3276771,4329604,32809736],[]),([3,1082431,2195426,5214340,32776968],[]),([3,1113151,2165730,17318416,32809228],[]),([4,4,1083361,2194527,17809936,32776456],[(128,0)]),([4,12,1083361,2194498,17809936,32776456],[]),([4,31,31744,3248099,4329604,32809736],[]),([4,31,33280,3276771,4329604,32776456],[]),([4,31,1082112,2194498,4329604,32776456],[]),([4,31,1082401,2195426,5214340,32776968],[]),([4,31,1083361,2194498,4329604,32809736],[]),([4,31,1083361,2194498,17809936,32776460],[(72,0)]),([4,31,1083361,2194498,32911756,33547032],[]),([4,31,1113121,2097920,4329604,33530120],[]),([4,31,1114081,2164802,4329604,32809736],[(72,0)]),([4,31,1114081,3146240,4329604,9412872],[]),([4,31,3180513,4357252,8659208,33538576],[]),([4,31,3188705,4329604,17318416,33530120],[]),([4,31,3188705,4329604,17809936,32776456],[]),([4,31,3248099,4357252,8659208,32539136],[]),([4,31,3248099,4357252,8659208,33079824],[]),([4,31,3248099,4357252,8691976,33047056],[]),([4,31,3248099,4357252,8692488,32505856],[]),([4,31,3276771,4329604,8659208,32539136],[]),([4,31,3276771,4329604,8692488,32505856],[]),([4,31744,1081356,2165730,17318416,32776456],[])]
def b1 : List Row := [([4,31744,1082431,2097920,5214340,32776456],[]),([4,31744,1082431,2165730,5214340,32776968],[]),([4,31744,1082431,2165730,17318416,32809228],[]),([4,31744,1082431,2165730,33317656,33534348],[]),([4,31744,3178496,4330468,8659208,17318431],[]),([4,31775,1083361,2164802,9412876,33047056],[]),([4,31775,1083361,2164802,17809936,32776460],[(72,0)]),([4,32772,1113151,2165730,17318416,32776456],[]),([4,1015808,1082431,2195426,4329604,32776968],[]),([4,1015808,1113151,2165730,17318416,32776460],[]),([4,1015812,1113151,2165730,17318416,32776456],[]),([4,1082431,2106336,4329604,17318416,33530120],[]),([4,1082431,2106336,5214340,17318416,32776456],[]),([4,1082431,2173922,5214340,17318416,32776456],[]),([4,1082431,2195426,5214340,8659208,32506368],[]),([4,1082431,2195426,5214340,8659720,32505856],[]),([4,1090623,2165730,5214340,17318416,32776456],[]),([4,1113151,2165730,8659208,17318416,32538628],[]),([4,1113151,2165730,8691980,17318416,32505856],[]),([4,3210273,4330468,8659208,17318431,33521664],[]),([4,3275875,4330468,8659208,17318431,32538624],[]),([4,3275875,4330468,8691976,17318431,32505856],[]),([5,4,31,1083361,2194498,17809936,32776456],[]),([5,4,992,1082401,2194527,17809936,32776456],[(168,0)])]
def t0 : BT := .nd (blockTree b0) [4,31744,1082431,2097920,4329604,33530120] (blockTree b1)
def b2 : List Row := [([5,4,31775,1083361,2164802,9412872,33047056],[]),([5,4,31775,1083361,2164802,17809936,32776456],[]),([5,4,1015808,1083361,2194527,17318416,32776456],[(168,0)]),([5,4,1015808,1113151,2165730,17318416,32776456],[]),([5,4,1083361,2194527,8659208,17809936,32505856],[(96,0),(168,0)]),([5,12,992,1082401,2194498,17809936,32776456],[]),([5,12,31744,1083361,2164802,9412872,33047056],[]),([5,12,31744,1083361,2164802,17809936,32776456],[]),([5,12,1015808,1083361,2194498,17318416,32776456],[]),([5,12,1015808,1113121,2165730,17318416,32776456],[]),([5,12,1083361,2194498,8659208,17809936,32505856],[]),([5,31,992,1082401,2194498,5214340,32776968],[(72,0)]),([5,31,992,1082401,2194498,32911756,33547032],[]),([5,31,992,3178496,4329604,8659208,17333776],[]),([5,31,992,3179553,4357252,8659208,33538576],[]),([5,31,992,3187745,4329604,17318416,33530120],[(72,0)]),([5,31,992,3187745,4329604,17809936,32776456],[]),([5,31,992,3210273,4329604,17318416,33530120],[]),([5,31,992,3247203,4357252,8659208,33079824],[]),([5,31,992,3247203,4357252,8691976,33047056],[]),([5,31,992,3275875,4329604,17318416,32809224],[]),([5,31,996,1082401,2194498,17809936,32776456],[]),([5,31,31744,33280,3248099,4329604,32776456],[]),([5,31,31744,1082112,2164802,4329604,32776456],[(96,0)]),([5,31,31744,1082401,2097920,4329604,33530120],[])]
def b3 : List Row := [([5,31,31744,1082401,2165730,5214340,32776968],[]),([5,31,31744,1082401,2165730,13611404,33317656],[]),([5,31,31744,1082401,2165730,33317656,33534348],[]),([5,31,31744,1083361,2164802,4329604,32809736],[(96,0)]),([5,31,31744,1083361,2164802,9412876,33047056],[]),([5,31,31744,1083361,2164802,17809936,32776460],[(96,0)]),([5,31,31744,1083361,2164802,32911756,33547032],[(96,0)]),([5,31,31744,1083361,3146240,4329604,9412872],[]),([5,31,31744,3178496,4330468,8659208,17318416],[]),([5,31,31744,3180513,4329604,8659208,33538576],[]),([5,31,31744,3180513,4329604,9412872,33047056],[]),([5,31,31744,3180513,4329604,17318416,33530120],[]),([5,31,31744,3180513,4329604,17809936,32776456],[]),([5,31,31744,3248099,4329604,8659208,32539136],[]),([5,31,31744,3248099,4329604,8659208,33079824],[]),([5,31,31744,3248099,4329604,8691976,33047056],[]),([5,31,31744,3248099,4329604,8692488,32505856],[]),([5,31,31744,3248099,4329604,17318416,32809224],[]),([5,31,31744,3248099,4329604,17351184,32776456],[]),([5,31,31748,1083361,2164802,9412872,33047056],[]),([5,31,31748,1083361,2164802,17809936,32776456],[]),([5,31,32736,1082401,2164802,5214340,32776968],[(72,0)]),([5,31,32736,1082401,2164802,9413384,32641156],[(72,0)]),([5,31,32768,3248099,4357252,8659208,33047056],[])]
def t1 : BT := .nd (blockTree b2) [5,31,31744,1082401,2097920,5214340,32776456] (blockTree b3)
def t2 : BT := .nd t0 [5,4,31744,1083361,2164831,17809936,32776456] t1
def b4 : List Row := [([5,31,33280,1114081,2164802,4329604,32776456],[(96,0)]),([5,31,33280,3248099,4357252,8659208,32505856],[]),([5,31,33280,3276771,4329604,8659208,32505856],[]),([5,31,1015808,1082401,2195426,4329604,32776968],[]),([5,31,1015808,1083361,2194498,4329604,32776968],[]),([5,31,1015808,1083361,2194498,17318416,32776460],[(96,0)]),([5,31,1015808,1083361,2194498,32911756,33317656],[]),([5,31,1015808,1083361,3146240,4357252,8659208],[]),([5,31,1015808,1113121,2097920,4329604,32776456],[]),([5,31,1015808,1113121,2165730,4329604,32776968],[]),([5,31,1015808,1113121,2165730,17318416,32776460],[]),([5,31,1015808,1113121,2165730,32911756,33317656],[]),([5,31,1015808,1114081,2164802,4329604,32776968],[(96,0)]),([5,31,1015808,1114081,3146240,4329604,8659208],[]),([5,31,1015808,3180513,4357252,8659208,33047056],[]),([5,31,1015808,3188705,4329604,17318416,32776456],[]),([5,31,1015812,1083361,2194498,17318416,32776456],[]),([5,31,1015812,1113121,2165730,17318416,32776456],[]),([5,31,1016320,1083361,2194498,4329604,32776456],[]),([5,31,1016320,1114081,2164802,4329604,32776456],[(96,0)]),([5,31,1081344,2165730,4357252,8659208,33047056],[]),([5,31,1082401,2098144,4357252,8659208,33538576],[]),([5,31,1082401,2106336,4329604,17318416,33530120],[]),([5,31,1082401,2106336,4329604,17809936,32776456],[]),([5,31,1082401,2106336,5214340,17318416,32776456],[])]
def b5 : List Row := [([5,31,1082401,2165730,4357252,8691976,33047056],[]),([5,31,1082401,2165730,4357252,9412872,33317656],[]),([5,31,1082401,2173922,5214340,8659208,33047056],[]),([5,31,1082401,2173922,5214340,17318416,32776456],[]),([5,31,1082401,2195426,4330468,17809936,32776456],[]),([5,31,1082401,2195426,5214340,8659208,32506368],[]),([5,31,1082401,2195426,5214340,8659720,32505856],[]),([5,31,1082401,3115074,4358116,8659720,32505856],[]),([5,31,1083361,2097152,4357252,8659208,33538576],[]),([5,31,1083361,2105344,4329604,17318416,33530120],[(72,0)]),([5,31,1083361,2105344,4329604,17809936,32776456],[(72,0)]),([5,31,1083361,2128896,4329604,17318416,33530120],[]),([5,31,1083361,2128896,4329604,17809936,32776456],[]),([5,31,1083361,2164802,4357252,8659208,32539136],[]),([5,31,1083361,2164802,4357252,8659208,33079824],[]),([5,31,1083361,2164802,4357252,8691976,33047056],[]),([5,31,1083361,2164802,4357252,8692488,32505856],[]),([5,31,1083361,2164802,4357252,9412872,33317656],[]),([5,31,1083361,2164802,4357252,26207000,32776456],[]),([5,31,1083361,2172994,4329604,17809936,32776456],[(72,0)]),([5,31,1083361,2194498,4329604,8659208,32539136],[]),([5,31,1083361,2194498,4329604,8692488,32505856],[]),([5,31,1083361,2194498,4329604,17318416,32809224],[]),([5,31,1083361,2194498,4329604,17351184,32776456],[])]
def t3 : BT := .nd (blockTree b4) [5,31,1082401,2165730,4357252,8659208,33079824] (blockTree b5)
def b6 : List Row := [([5,31,1083361,2194498,4329604,26207000,32776456],[]),([5,31,1083361,2194498,4329604,32776456,33538576],[]),([5,31,1083361,2194498,4329604,32776456,33547032],[]),([5,31,1083361,2194498,4329604,33317656,33530120],[]),([5,31,1083361,2194498,4330468,17809936,32776456],[]),([5,31,1083361,2194498,4357252,17809936,32776456],[]),([5,31,1083361,2194498,5214340,17809936,32776456],[]),([5,31,1083361,2194498,8659208,17809936,32505860],[(72,0)]),([5,31,1083361,2194498,8659208,32641156,33538576],[]),([5,31,1083361,2194498,8659212,17809936,32505856],[(72,0)]),([5,31,1083361,2194498,12988812,17809936,32776456],[]),([5,31,1083361,2194498,12988812,26207000,32505856],[]),([5,31,1083361,2194498,17318416,32911756,33530120],[]),([5,31,1083361,2194498,17809936,32641156,32776456],[]),([5,31,1083361,2194498,17809936,32776456,32911756],[]),([5,31,1083361,2194527,4329604,17809936,32776456],[]),([5,31,1083361,2195426,4329604,17809936,32776456],[]),([5,31,1083361,3145728,4357252,8659208,17809936],[]),([5,31,1083361,3275875,4329604,17809936,32776456],[]),([5,31,1083361,3275875,5214340,17318416,32776456],[]),([5,31,1083361,3276771,4329604,17809936,32776456],[]),([5,31,1089536,2165730,4329604,17318416,32776456],[]),([5,31,1090593,2165730,5214340,8659208,33047056],[]),([5,31,1090593,2165730,5214340,17318416,32776456],[])]
def b7 : List Row := [([5,31,1091553,2164802,4329604,17809936,32776456],[(72,0)]),([5,31,1113121,2098144,4329604,17318416,33530120],[]),([5,31,1113121,2165730,4329604,17318416,32809224],[]),([5,31,1113121,2165730,4329604,33317656,33530120],[]),([5,31,1113121,2165730,17318416,32911756,33530120],[]),([5,31,1113121,3248099,5214340,8659208,33047056],[]),([5,31,1113121,3248099,5214340,17318416,32776456],[]),([5,31,1114081,2164802,4329604,8659208,32539136],[(72,0)]),([5,31,1114081,2164802,4329604,8692488,32505856],[(72,0)]),([5,31,1114081,2164802,4329604,9412872,32506368],[]),([5,31,1114081,2164802,4329604,9413384,32505856],[]),([5,31,1114081,3248099,4329604,9412872,33047056],[]),([5,31,1114081,3248099,4329604,17809936,32776456],[]),([5,31,3180513,4357252,8659208,17318416,33521664],[]),([5,31,3180513,4357252,8659208,17809936,32505856],[]),([5,31,3210273,4330468,8659208,17318416,33521664],[]),([5,31,3248099,4357252,8659208,17318416,32538624],[]),([5,31,3248099,4357252,8659208,17351184,32505856],[]),([5,31,3248099,4357252,8691976,17318416,32505856],[]),([5,31,3275875,4330468,8659208,17318416,32538624],[]),([5,31,3275875,4330468,8691976,17318416,32505856],[]),([5,543,32736,1082401,2164802,5214340,32776456],[]),([5,543,32736,1082401,2164802,9412872,32641156],[]),([5,543,1082401,3115074,4358116,8659208,32505856],[])]
def t4 : BT := .nd (blockTree b6) [5,31,1091553,2164802,4329604,9412872,33047056] (blockTree b7)
def t5 : BT := .nd t3 [5,31,1083361,2194498,4329604,17809936,32776456] t4
def t6 : BT := .nd t2 [5,31,33280,1083361,2194498,4329604,32776456] t5
def b8 : List Row := [([5,8223,1082401,2165730,5214340,8659208,33047056],[]),([5,8223,1082401,2165730,5214340,17318416,32776456],[]),([5,8223,1083361,2164802,4329604,9412872,33047056],[]),([5,8223,1083361,2164802,4329604,17809936,32776456],[(72,0)]),([5,31744,32768,3145728,4330468,8659208,17318431],[]),([5,31744,32772,1082431,2165730,17318416,32776456],[]),([5,31744,1015808,1082431,2097920,4329604,32776456],[]),([5,31744,1015808,1082431,2165730,4329604,32776968],[]),([5,31744,1015808,1082431,2165730,17318416,32776460],[]),([5,31744,1015808,1082431,2165730,32911756,33317656],[]),([5,31744,1015812,1082431,2165730,17318416,32776456],[]),([5,31744,1081344,2097152,4330468,8659208,17318431],[]),([5,31744,1082431,2098144,4329604,17318416,33530120],[]),([5,31744,1082431,2098144,5214340,17318416,32776456],[]),([5,31744,1082431,2165730,4329604,17318416,32809224],[]),([5,31744,1082431,2165730,4329604,33317656,33530120],[]),([5,31744,1082431,2165730,4362372,17318416,32776456],[]),([5,31744,1082431,2165730,5214340,8659208,32506368],[]),([5,31744,1082431,2165730,5214340,8659720,32505856],[]),([5,31744,1082431,2165730,5214340,17318416,32776456],[]),([5,31744,1082431,2165730,5214340,25977624,32776456],[]),([5,31744,1082431,2165730,5214340,32776456,33047056],[]),([5,31744,1082431,2165730,5214340,32776456,33317656],[]),([5,31744,1082431,2165730,8659208,17318416,32538628],[]),([5,31744,1082431,2165730,8659208,33047056,33525892],[])]
def b9 : List Row := [([5,31744,1082431,2165730,13611404,17318416,32776456],[]),([5,31744,1082431,2165730,13611404,25977624,32505856],[]),([5,31744,1082431,2165730,17318416,32776456,33525892],[]),([5,31744,1082431,2165730,17318416,32776456,33534348],[]),([5,31744,1082431,2165730,17318416,32911756,33530120],[]),([5,31744,1082431,3248099,5214340,8659208,33047056],[]),([5,31744,1082431,3248099,5214340,17318416,32776456],[]),([5,31744,3179553,4330468,8659208,17318431,33521664],[]),([5,31744,3247203,4330468,8659208,17318431,32538624],[]),([5,31744,3247203,4330468,8691976,17318431,32505856],[]),([5,31775,1015808,1082401,2165730,8659212,33047056],[]),([5,31775,1015808,1082401,2165730,17318416,32776460],[]),([5,31775,1015808,1083361,2164802,8659212,33047056],[]),([5,31775,1015808,1083361,2164802,17318416,32776460],[(96,0)]),([5,31775,1015812,1082401,2165730,8659208,33047056],[]),([5,31775,1015812,1082401,2165730,17318416,32776456],[]),([5,31775,1015812,1083361,2164802,8659208,33047056],[]),([5,31775,1015812,1083361,2164802,17318416,32776456],[]),([5,31775,1082431,2165730,5214340,17318416,32776456],[]),([5,31775,1083361,2164802,8659208,17809936,32505860],[(72,0)]),([5,31775,1083361,2164802,8659212,17809936,32505856],[(72,0)]),([5,31775,1083361,2164802,9412872,17318416,32505860],[]),([5,31775,1083361,2164802,9412876,17318416,32505856],[]),([5,31775,1083361,2164831,4329604,17809936,32776456],[])]
def t7 : BT := .nd (blockTree b8) [5,31744,1082431,2165730,8691980,17318416,32505856] (blockTree b9)
def b10 : List Row := [([5,32772,1113151,2165730,8659208,17318416,32505856],[]),([5,1015808,1082431,2106336,4329604,17318416,32776456],[]),([5,1015808,1082431,2173922,4329604,17318416,32776456],[]),([5,1015808,1082431,2195426,4329604,8659208,32506368],[]),([5,1015808,1082431,2195426,4329604,8659720,32505856],[]),([5,1015808,1090623,2165730,4329604,17318416,32776456],[]),([5,1015808,1113121,3145728,4330468,8659208,17318431],[]),([5,1015808,1113151,2165730,8659208,17318416,32505860],[]),([5,1015808,1113151,2165730,8659212,17318416,32505856],[]),([5,1015808,3210273,4330468,8659208,17318431,32505856],[]),([5,1015812,1113151,2165730,8659208,17318416,32505856],[]),([5,1081344,2194498,4330468,8659208,17318431,32505856],[]),([5,1082401,2128896,4330468,8659208,17318431,33521664],[]),([5,1082401,2194498,4330468,8659208,17318431,32538624],[]),([5,1082401,2194498,4330468,8691976,17318431,32505856],[]),([5,1082401,2194498,4330468,9412872,17318431,32776456],[]),([5,1082401,3115074,4330468,8659208,17326623,32505856],[]),([5,1082401,3115074,8659724,32505856],[(1024,491603),(1024,655448)]),([5,1082431,1083361,2194498,4329604,17809936,32776456],[]),([5,1082431,1113121,2165730,5214340,8659208,33047056],[]),([5,1082431,1113121,2165730,5214340,17318416,32776456],[]),([5,1082431,1113151,2165730,5214340,17318416,32776456],[]),([5,1082431,2098144,4329604,8659208,17333776,33521664],[]),([5,1082431,2098144,5214340,8659208,17333776,32505856],[])]
def b11 : List Row := [([5,1082431,2165730,2195426,5214340,17318416,32776456],[(140,0)]),([5,1082431,2165730,5214340,8659208,17326608,32505856],[]),([5,1082431,2173922,5214340,8659208,17318416,32505856],[]),([5,1090593,3115074,4330468,8659208,17318431,32505856],[]),([5,1090623,2165730,5214340,8659208,17318416,32505856],[]),([5,1113121,2097152,4330468,8659208,17318431,33521664],[]),([5,1113121,2097183,4330468,8659208,17318416,33521664],[]),([5,1113121,2164802,4330468,8659208,17318431,32538624],[]),([5,1113121,2164802,4330468,8691976,17318431,32505856],[]),([5,1113121,2164802,4330468,9412872,17318431,32776456],[]),([5,1113121,3112960,4330468,8659208,17318431,32505856],[]),([6,4,31,992,1082401,2194498,17809936,32776456],[(216,0)]),([6,4,31,31744,1083361,2164802,9412872,33047056],[]),([6,4,31,31744,1083361,2164802,17809936,32776456],[]),([6,4,31,1015808,1083361,2194498,17318416,32776456],[]),([6,4,31,1015808,1113121,2165730,17318416,32776456],[]),([6,4,31,1083361,2194498,8659208,17809936,32505856],[]),([6,4,992,31744,1082401,2164831,17809936,32776456],[(216,0)]),([6,4,992,31775,1082401,2164802,9412872,33047056],[(56,0),(168,0)]),([6,4,992,31775,1082401,2164802,17809936,32776456],[(56,0),(216,0)]),([6,4,992,1015808,1082401,2194527,17318416,32776456],[(216,0)]),([6,4,992,1015808,1082431,2194498,17318416,32776456],[(72,0),(216,0)]),([6,4,992,1015808,1113121,2164831,17318416,32776456],[(216,0)]),([6,4,992,1015808,1113151,2164802,17318416,32776456],[(72,0),(216,0)])]
def t8 : BT := .nd (blockTree b10) [5,1082431,2165730,2194498,5214340,17318416,32776456] (blockTree b11)
def t9 : BT := .nd t7 [5,32768,3275875,4330468,8659208,17318431,32505856] t8
def b12 : List Row := [([6,4,992,1082401,3115074,8659208,17333791,32505856],[(56,0),(128,0)]),([6,4,992,1113151,2164802,9412872,17318416,32505856],[(128,0),(216,0)]),([6,4,31744,1015808,1082431,2165730,17318416,32776456],[]),([6,4,31744,1015808,1083361,2164831,17318416,32776456],[(216,0)]),([6,4,31744,1083361,2164831,8659208,17809936,32505856],[(128,0),(216,0)]),([6,4,31775,1015808,1082401,2165730,8659208,33047056],[]),([6,4,31775,1015808,1082401,2165730,17318416,32776456],[]),([6,4,31775,1015808,1083361,2164802,8659208,33047056],[]),([6,4,31775,1015808,1083361,2164802,17318416,32776456],[]),([6,4,31775,1083361,2164802,8659208,17809936,32505856],[]),([6,4,31775,1083361,2164802,9412872,17318416,32505856],[]),([6,4,1015808,1083361,2194527,8659208,17318416,32505856],[(128,0),(216,0)]),([6,4,1015808,1113151,2165730,8659208,17318416,32505856],[]),([6,4,1082401,3115074,8659720,32505856],[(1024,491635),(1024,655480)]),([6,12,992,31744,1082401,2164802,9412872,33047056],[]),([6,12,992,31744,1082401,2164802,17809936,32776456],[]),([6,12,992,1015808,1082401,2194498,17318416,32776456],[]),([6,12,992,1015808,1113121,2164802,17318416,32776456],[]),([6,12,992,1082401,2194498,8659208,17809936,32505856],[]),([6,12,992,1082401,3115074,8659208,17333776,32505856],[]),([6,12,992,1113121,2164802,9412872,17318416,32505856],[]),([6,12,31744,1015808,1082401,2165730,8659208,33047056],[]),([6,12,31744,1015808,1082401,2165730,17318416,32776456],[]),([6,12,31744,1015808,1083361,2164802,8659208,33047056],[]),([6,12,31744,1015808,1083361,2164802,17318416,32776456],[])]
def b13 : List Row := [([6,12,31744,1083361,2164802,9412872,17318416,32505856],[]),([6,12,1015808,1083361,2194498,8659208,17318416,32505856],[]),([6,12,1015808,1113121,2165730,8659208,17318416,32505856],[]),([6,31,992,31744,1082401,2164802,5214340,32776968],[(96,0)]),([6,31,992,31744,1082401,2164802,9412876,33047056],[(72,0)]),([6,31,992,31744,1082401,2164802,13611404,33317656],[]),([6,31,992,31744,1082401,2164802,32911756,33547032],[(128,0)]),([6,31,992,31744,3178496,4329604,8659208,17318416],[(144,0),(216,0)]),([6,31,992,31744,3179553,4329604,8659208,33538576],[]),([6,31,992,31744,3179553,4329604,9412872,33047056],[]),([6,31,992,31744,3179553,4329604,17318416,33530120],[(96,0)]),([6,31,992,31744,3179553,4329604,17809936,32776456],[]),([6,31,992,31744,3179553,5214340,8659208,33047056],[]),([6,31,992,31744,3247203,4329604,8659208,33079824],[]),([6,31,992,31744,3247203,4329604,8691976,33047056],[]),([6,31,992,31744,3247203,4329604,17318416,32809224],[(96,0)]),([6,31,992,31744,3247203,4329604,17351184,32776456],[]),([6,31,992,31744,3247203,4362372,8659208,33047056],[]),([6,31,992,31748,1082401,2164802,9412872,33047056],[]),([6,31,992,31748,1082401,2164802,17809936,32776456],[]),([6,31,992,32768,3145728,4329604,8659208,17333776],[]),([6,31,992,32768,3247203,4357252,8659208,33047056],[]),([6,31,992,32768,3275875,4329604,17318416,32776456],[]),([6,31,992,1015808,1082401,2194498,4329604,32776968],[(96,0)])]
def t10 : BT := .nd (blockTree b12) [6,12,31744,1083361,2164802,8659208,17809936,32505856] (blockTree b13)
def b14 : List Row := [([6,31,992,1015808,1113121,2164802,4329604,32776968],[(128,0)]),([6,31,992,1015808,1113121,2164802,32911756,33317656],[(128,0)]),([6,31,992,1015808,3179553,4357252,8659208,33047056],[]),([6,31,992,1015808,3187745,4329604,17318416,32776456],[(96,0),(144,0)]),([6,31,992,1015808,3210273,4329604,17318416,32776456],[]),([6,31,992,1015812,1082401,2194498,17318416,32776456],[(96,0)]),([6,31,992,1015812,1113121,2164802,17318416,32776456],[(96,0)]),([6,31,992,1081344,2097152,4329604,8659208,17333776],[]),([6,31,992,1081344,2164802,4357252,8659208,33047056],[]),([6,31,992,1081344,2194498,4329604,17318416,32776456],[]),([6,31,992,1082401,2097152,4357252,8659208,33538576],[]),([6,31,992,1082401,2105344,4329604,17318416,33530120],[(72,0),(96,0)]),([6,31,992,1082401,2105344,4329604,17809936,32776456],[(96,0)]),([6,31,992,1082401,2128896,4329604,17318416,33530120],[(72,0)]),([6,31,992,1082401,2128896,4329604,17809936,32776456],[]),([6,31,992,1082401,2164802,4357252,8659208,33079824],[]),([6,31,992,1082401,2164802,4357252,8691976,33047056],[]),([6,31,992,1082401,2164802,4357252,9412872,33317656],[]),([6,31,992,1082401,2164802,4357252,26207000,32776456],[]),([6,31,992,1082401,2172994,4329604,17809936,32776456],[(96,0)]),([6,31,992,1082401,2172994,5214340,8659208,33047056],[]),([6,31,992,1082401,2194498,4329604,17318416,32809224],[(72,0)]),([6,31,992,1082401,2194498,4329604,17351184,32776456],[]),([6,31,992,1082401,2194498,4329604,17809936,32776456],[])]
def b15 : List Row := [([6,31,992,1082401,2194498,4329604,32776456,33538576],[]),([6,31,992,1082401,2194498,4329604,32776456,33547032],[]),([6,31,992,1082401,2194498,4329604,33317656,33530120],[(72,0),(248,0)]),([6,31,992,1082401,2194498,4330468,17809936,32776456],[]),([6,31,992,1082401,2194498,4357252,17809936,32776456],[]),([6,31,992,1082401,2194498,5214340,8659208,32506368],[(72,0)]),([6,31,992,1082401,2194498,5214340,8659720,32505856],[(72,0)]),([6,31,992,1082401,2194498,5214340,17809936,32776456],[(72,0)]),([6,31,992,1082401,2194498,5214340,25977624,32776456],[(72,0),(180,0)]),([6,31,992,1082401,2194498,5214340,32776456,33047056],[(72,0)]),([6,31,992,1082401,2194498,5214340,32776456,33317656],[(72,0),(200,0),(228,0)]),([6,31,992,1082401,2194498,8659208,32641156,33538576],[]),([6,31,992,1082401,2194498,12988812,26207000,32505856],[]),([6,31,992,1082401,2194527,4329604,17809936,32776456],[]),([6,31,992,1082401,2194527,5214340,17318416,32776456],[(72,0),(168,0)]),([6,31,992,1082401,2197570,4357252,8659208,33047056],[]),([6,31,992,1082401,3115074,4357252,8659208,32506368],[]),([6,31,992,1082401,3115074,4357252,8659720,32505856],[]),([6,31,992,1082401,3145728,4357252,8659208,17809936],[]),([6,31,992,1082401,3275875,4329604,17809936,32776456],[(72,0)]),([6,31,992,1082431,2194498,5214340,17318416,32776456],[(72,0),(96,0),(168,0)]),([6,31,992,1089536,2164802,4329604,17318416,32776456],[(96,0)]),([6,31,992,1090593,2164802,4329604,9412872,33047056],[]),([6,31,992,1090593,2164802,4329604,17809936,32776456],[(96,0)])]
def t11 : BT := .nd (blockTree b14) [6,31,992,1082401,2194498,4329604,26207000,32776456] (blockTree b15)
def t12 : BT := .nd t10 [6,31,992,1015808,1082401,2194498,32911756,33317656] t11
def t13 : BT := .nd t9 [6,4,992,1082401,2194527,8659208,17809936,32505856] t12
def t14 : BT := .nd t6 [5,8192,1082431,2165730,5214340,17318416,32776456] t13
def b16 : List Row := [([6,31,992,1113121,2097152,4329604,17318416,33530120],[(96,0)]),([6,31,992,1113121,2164802,4329604,9412872,32506368],[]),([6,31,992,1113121,2164802,4329604,9413384,32505856],[]),([6,31,992,1113121,2164802,4329604,17318416,32809224],[(96,0)]),([6,31,992,1113121,2164802,4329604,33047056,33530120],[]),([6,31,992,1113121,2164802,4329604,33317656,33530120],[(96,0)]),([6,31,992,1113121,2164802,5214340,17809936,32776456],[]),([6,31,992,1113121,2164802,9412872,32641156,33047056],[]),([6,31,992,1113121,2164802,13611404,26207000,32505856],[]),([6,31,992,1113121,3145728,4329604,9412872,17318416],[]),([6,31,992,1113121,3247203,4329604,9412872,33047056],[]),([6,31,992,1113121,3247203,4329604,17809936,32776456],[(96,0)]),([6,31,992,1113121,3247203,5214340,8659208,33047056],[]),([6,31,992,3179553,4329604,8659208,17333776,33521664],[(72,0),(240,0)]),([6,31,992,3179553,4357252,8659208,17809936,32505856],[]),([6,31,992,3210273,4329604,8659208,17318416,33521664],[(168,0)]),([6,31,992,3210273,4329604,9412872,17318416,32505856],[]),([6,31,992,3247203,4329604,8659208,17333776,32538624],[(72,0),(240,0)]),([6,31,992,3247203,4329604,8691976,17333776,32505856],[(72,0),(240,0)]),([6,31,992,3247203,4357252,8659208,17351184,32505856],[]),([6,31,992,3275875,4329604,8659208,17318416,32538624],[(168,0)]),([6,31,992,3275875,4329604,8691976,17318416,32505856],[(168,0)]),([6,31,996,31744,1082401,2164802,9412872,33047056],[(72,0)]),([6,31,996,31744,1082401,2164802,17809936,32776456],[(72,0)]),([6,31,996,1015808,1082401,2194498,17318416,32776456],[])]
def b17 : List Row := [([6,31,996,1082401,2194498,8659208,17809936,32505856],[]),([6,31,996,1082401,3115074,8659208,17333776,32505856],[(168,0)]),([6,31,996,1113121,2164802,9412872,17318416,32505856],[]),([6,31,8192,1082401,2165730,5214340,8659208,33047056],[]),([6,31,8192,1082401,2165730,5214340,17318416,32776456],[]),([6,31,8192,1083361,2164802,4329604,9412872,33047056],[]),([6,31,8192,1083361,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,9184,1082401,2164802,4329604,9412872,33047056],[]),([6,31,9184,1082401,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,9184,1082401,2164802,5214340,8659208,33047056],[]),([6,31,9184,1082401,2164802,5214340,17318416,32776456],[(72,0)]),([6,31,9184,1082401,2164802,8659208,17809936,32641156],[(96,0)]),([6,31,9184,1082401,2164802,9412872,17318416,32641156],[(72,0)]),([6,31,31744,32768,3145728,4330468,8659208,17318416],[]),([6,31,31744,32768,3248099,4329604,8659208,33047056],[]),([6,31,31744,32768,3248099,4329604,17318416,32776456],[]),([6,31,31744,33280,1083361,2164802,4329604,32776456],[(128,0)]),([6,31,31744,33280,3248099,4329604,8659208,32505856],[]),([6,31,31744,1015808,1082401,2097920,4329604,32776456],[]),([6,31,31744,1015808,1082401,2165730,4329604,32776968],[]),([6,31,31744,1015808,1082401,2165730,8659212,33047056],[]),([6,31,31744,1015808,1082401,2165730,12988812,33317656],[]),([6,31,31744,1015808,1082401,2165730,17318416,32776460],[]),([6,31,31744,1015808,1082401,2165730,32911756,33317656],[])]
def t15 : BT := .nd (blockTree b16) [6,31,996,1015808,1113121,2164802,17318416,32776456] (blockTree b17)
def b18 : List Row := [([6,31,31744,1015808,1083361,2164802,8659212,33047056],[]),([6,31,31744,1015808,1083361,2164802,12988812,33317656],[]),([6,31,31744,1015808,1083361,2164802,17318416,32776460],[(128,0)]),([6,31,31744,1015808,1083361,2164802,32911756,33317656],[(128,0)]),([6,31,31744,1015808,1083361,3146240,4329604,8659208],[]),([6,31,31744,1015808,3180513,4329604,8659208,33047056],[]),([6,31,31744,1015808,3180513,4329604,17318416,32776456],[]),([6,31,31744,1015812,1082401,2165730,8659208,33047056],[]),([6,31,31744,1015812,1082401,2165730,17318416,32776456],[]),([6,31,31744,1015812,1083361,2164802,8659208,33047056],[]),([6,31,31744,1015812,1083361,2164802,17318416,32776456],[]),([6,31,31744,1016320,1083361,2164802,4329604,32776456],[(128,0)]),([6,31,31744,1081344,2097152,4330468,8659208,17318416],[]),([6,31,31744,1081344,2165730,4329604,8659208,33047056],[]),([6,31,31744,1081344,2165730,4329604,17318416,32776456],[]),([6,31,31744,1082401,2098144,4329604,8659208,33538576],[]),([6,31,31744,1082401,2098144,4329604,9412872,33047056],[]),([6,31,31744,1082401,2098144,4329604,17318416,33530120],[]),([6,31,31744,1082401,2098144,4329604,17809936,32776456],[]),([6,31,31744,1082401,2098144,5214340,8659208,33047056],[]),([6,31,31744,1082401,2098144,5214340,17318416,32776456],[]),([6,31,31744,1082401,2165730,4329604,8659208,33079824],[]),([6,31,31744,1082401,2165730,4329604,8691976,33047056],[]),([6,31,31744,1082401,2165730,4329604,9412872,33317656],[]),([6,31,31744,1082401,2165730,4329604,17318416,32809224],[])]
def b19 : List Row := [([6,31,31744,1082401,2165730,4329604,33317656,33530120],[]),([6,31,31744,1082401,2165730,4330468,9412872,33047056],[]),([6,31,31744,1082401,2165730,4330468,17809936,32776456],[]),([6,31,31744,1082401,2165730,4362372,8659208,33047056],[]),([6,31,31744,1082401,2165730,4362372,17318416,32776456],[]),([6,31,31744,1082401,2165730,5214340,8659208,32506368],[]),([6,31,31744,1082401,2165730,5214340,8659208,33047056],[]),([6,31,31744,1082401,2165730,5214340,8659208,33317656],[]),([6,31,31744,1082401,2165730,5214340,8659720,32505856],[]),([6,31,31744,1082401,2165730,5214340,17318416,32776456],[]),([6,31,31744,1082401,2165730,5214340,25977624,32776456],[]),([6,31,31744,1082401,2165730,5214340,32776456,33047056],[]),([6,31,31744,1082401,2165730,5214340,32776456,33317656],[]),([6,31,31744,1082401,2165730,8659208,13611404,33047056],[]),([6,31,31744,1082401,2165730,8659208,33047056,33525892],[]),([6,31,31744,1082401,2165730,9412872,12988812,33047056],[]),([6,31,31744,1082401,2165730,13611404,17318416,32776456],[]),([6,31,31744,1082401,2165730,13611404,25977624,32505856],[]),([6,31,31744,1082401,2165730,17318416,32776456,33525892],[]),([6,31,31744,1082401,2165730,17318416,32776456,33534348],[]),([6,31,31744,1082401,2165730,17318416,32911756,33530120],[]),([6,31,31744,1082401,3115074,4330468,8659720,32505856],[]),([6,31,31744,1082401,3248099,5214340,8659208,33047056],[]),([6,31,31744,1082401,3248099,5214340,17318416,32776456],[])]
def t16 : BT := .nd (blockTree b18) [6,31,31744,1082401,2165730,4329604,17351184,32776456] (blockTree b19)
def t17 : BT := .nd t15 [6,31,31744,1015808,1083361,2164802,4329604,32776968] t16
def b20 : List Row := [([6,31,31744,1083361,2097152,4329604,8659208,33538576],[]),([6,31,31744,1083361,2097152,4329604,9412872,33047056],[]),([6,31,31744,1083361,2097152,4329604,17318416,33530120],[(96,0)]),([6,31,31744,1083361,2097152,4329604,17809936,32776456],[(96,0)]),([6,31,31744,1083361,2164802,4329604,8659208,32539136],[(96,0)]),([6,31,31744,1083361,2164802,4329604,8659208,33079824],[]),([6,31,31744,1083361,2164802,4329604,8691976,33047056],[]),([6,31,31744,1083361,2164802,4329604,8692488,32505856],[(96,0)]),([6,31,31744,1083361,2164802,4329604,9412872,32506368],[]),([6,31,31744,1083361,2164802,4329604,9412872,33047056],[]),([6,31,31744,1083361,2164802,4329604,9412872,33317656],[]),([6,31,31744,1083361,2164802,4329604,9413384,32505856],[]),([6,31,31744,1083361,2164802,4329604,17318416,32809224],[(96,0)]),([6,31,31744,1083361,2164802,4329604,17351184,32776456],[(96,0)]),([6,31,31744,1083361,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,31744,1083361,2164802,4329604,26207000,32776456],[(96,0)]),([6,31,31744,1083361,2164802,4329604,32776456,33538576],[(96,0)]),([6,31,31744,1083361,2164802,4329604,32776456,33547032],[(96,0)]),([6,31,31744,1083361,2164802,4329604,33047056,33530120],[]),([6,31,31744,1083361,2164802,4329604,33317656,33530120],[(96,0)]),([6,31,31744,1083361,2164802,4330468,9412872,33047056],[]),([6,31,31744,1083361,2164802,4330468,17809936,32776456],[]),([6,31,31744,1083361,2164802,4357252,9412872,33047056],[]),([6,31,31744,1083361,2164802,4357252,17809936,32776456],[]),([6,31,31744,1083361,2164802,5214340,9412872,33047056],[])]
def b21 : List Row := [([6,31,31744,1083361,2164802,8659208,17809936,32505860],[(96,0)]),([6,31,31744,1083361,2164802,8659208,32641156,33538576],[(96,0)]),([6,31,31744,1083361,2164802,8659212,17809936,32505856],[(96,0)]),([6,31,31744,1083361,2164802,9412872,12988812,33047056],[]),([6,31,31744,1083361,2164802,9412872,13611404,33047056],[]),([6,31,31744,1083361,2164802,9412872,17318416,32505860],[]),([6,31,31744,1083361,2164802,9412872,32641156,33047056],[]),([6,31,31744,1083361,2164802,9412876,17318416,32505856],[]),([6,31,31744,1083361,2164802,12988812,17809936,32776456],[(96,0)]),([6,31,31744,1083361,2164802,12988812,26207000,32505856],[(96,0)]),([6,31,31744,1083361,2164802,13611404,26207000,32505856],[]),([6,31,31744,1083361,2164802,17318416,32641156,33530120],[]),([6,31,31744,1083361,2164802,17318416,32911756,33530120],[(96,0)]),([6,31,31744,1083361,2164802,17809936,32641156,32776456],[(96,0)]),([6,31,31744,1083361,2164802,17809936,32776456,32911756],[(96,0)]),([6,31,31744,1083361,2164831,4329604,17809936,32776456],[(96,0)]),([6,31,31744,1083361,2165730,4329604,9412872,33047056],[]),([6,31,31744,1083361,2165730,4329604,17809936,32776456],[]),([6,31,31744,1083361,2194498,4329604,17809936,32776456],[]),([6,31,31744,1083361,3145728,4329604,8659208,17809936],[]),([6,31,31744,1083361,3145728,4329604,9412872,17318416],[]),([6,31,31744,1083361,3247203,4329604,9412872,33047056],[]),([6,31,31744,1083361,3247203,4329604,17809936,32776456],[(96,0)]),([6,31,31744,1083361,3247203,5214340,8659208,33047056],[])]
def t18 : BT := .nd (blockTree b20) [6,31,31744,1083361,2164802,5214340,17809936,32776456] (blockTree b21)
def b22 : List Row := [([6,31,31744,1083361,3247203,8659208,17809936,32641156],[(96,0)]),([6,31,31744,1083361,3247203,9412872,17318416,32641156],[]),([6,31,31744,1083361,3248099,4329604,9412872,33047056],[]),([6,31,31744,1083361,3248099,4329604,17809936,32776456],[]),([6,31,31744,3179553,4330468,8659208,17318416,33521664],[]),([6,31,31744,3180513,4329604,8659208,17318416,33521664],[]),([6,31,31744,3180513,4329604,8659208,17809936,32505856],[]),([6,31,31744,3180513,4329604,9412872,17318416,32505856],[]),([6,31,31744,3247203,4330468,8659208,17318416,32538624],[]),([6,31,31744,3247203,4330468,8659208,17351184,32505856],[]),([6,31,31744,3247203,4330468,8691976,17318416,32505856],[]),([6,31,31744,3248099,4329604,8659208,17318416,32538624],[]),([6,31,31744,3248099,4329604,8659208,17351184,32505856],[]),([6,31,31744,3248099,4329604,8691976,17318416,32505856],[]),([6,31,31748,1015808,1082401,2165730,8659208,33047056],[]),([6,31,31748,1015808,1082401,2165730,17318416,32776456],[]),([6,31,31748,1015808,1083361,2164802,8659208,33047056],[]),([6,31,31748,1015808,1083361,2164802,17318416,32776456],[]),([6,31,31748,1083361,2164802,8659208,17809936,32505856],[]),([6,31,31748,1083361,2164802,9412872,17318416,32505856],[]),([6,31,31775,1082401,2165730,5214340,8659208,33047056],[]),([6,31,31775,1082401,2165730,5214340,17318416,32776456],[]),([6,31,31775,1083361,2164802,4329604,9412872,33047056],[]),([6,31,31775,1083361,2164802,4329604,17809936,32776456],[])]
def b23 : List Row := [([6,31,32736,1015808,1082401,2164802,8659720,32641156],[(96,0),(128,0)]),([6,31,32736,1016320,1082401,2164802,4329604,32776456],[(96,0),(128,0)]),([6,31,32736,1016320,1082401,2164802,8659208,32641156],[(96,0),(128,0)]),([6,31,32736,1082401,2164802,4329604,9412872,32506368],[(72,0)]),([6,31,32736,1082401,2164802,4329604,9413384,32505856],[(72,0)]),([6,31,32736,1082401,2164802,4330468,9412872,33047056],[]),([6,31,32736,1082401,2164802,4330468,17809936,32776456],[]),([6,31,32736,1082401,2164802,5214340,8659208,32506368],[(72,0)]),([6,31,32736,1082401,2164802,5214340,8659720,32505856],[(72,0)]),([6,31,32736,1082401,2165730,4329604,9412872,33047056],[]),([6,31,32736,1082401,2165730,4329604,17809936,32776456],[]),([6,31,32736,1082401,2165730,5214340,8659208,33047056],[]),([6,31,32736,1082401,2165730,5214340,17318416,32776456],[(72,0)]),([6,31,32736,1082401,3115074,4329604,8659208,32506368],[]),([6,31,32736,1082401,3115074,4329604,8659720,32505856],[]),([6,31,32736,1083361,2164802,4329604,9412872,33047056],[]),([6,31,32736,1083361,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,32768,1082401,2165730,4357252,8659208,33047056],[]),([6,31,32768,1083361,2164802,4357252,8659208,33047056],[]),([6,31,32768,1083361,2194498,4329604,17318416,32776456],[]),([6,31,32768,1113121,2165730,4329604,17318416,32776456],[]),([6,31,32768,3248099,4357252,8659208,17318416,32505856],[]),([6,31,32768,3275875,4330468,8659208,17318416,32505856],[]),([6,31,33280,1083361,2164802,4357252,8659208,32505856],[])]
def t19 : BT := .nd (blockTree b22) [6,31,32736,1015808,1082401,2164802,4329604,32776968] (blockTree b23)
def t20 : BT := .nd t18 [6,31,31744,1083361,3247203,5214340,17318416,32776456] t19
def t21 : BT := .nd t17 [6,31,31744,1082431,2165730,5214340,17318416,32776456] t20
def b24 : List Row := [([6,31,33280,1114081,2164802,4329604,8659208,32505856],[(96,0)]),([6,31,1015808,1082401,2098144,4357252,8659208,33047056],[]),([6,31,1015808,1082401,2106336,4329604,17318416,32776456],[]),([6,31,1015808,1082401,2164802,4358116,8659720,32505856],[]),([6,31,1015808,1082401,2165730,4337796,8659208,33047056],[]),([6,31,1015808,1082401,2165730,4357252,8659208,32506368],[]),([6,31,1015808,1082401,2165730,4357252,8659208,33047056],[]),([6,31,1015808,1082401,2165730,4357252,8659208,33317656],[]),([6,31,1015808,1082401,2165730,4357252,8659720,32505856],[]),([6,31,1015808,1082401,2165730,4357252,25977624,32776456],[]),([6,31,1015808,1082401,2165730,4358116,8659208,33047056],[]),([6,31,1015808,1082401,2173922,4329604,8659208,33047056],[]),([6,31,1015808,1082401,2173922,4329604,17318416,32776456],[]),([6,31,1015808,1082401,2194498,4330468,8659720,32505856],[]),([6,31,1015808,1082401,2194498,4330468,25977624,32776456],[]),([6,31,1015808,1082401,2195426,4329604,8659208,32506368],[]),([6,31,1015808,1082401,2195426,4329604,8659720,32505856],[]),([6,31,1015808,1082401,2195426,4330468,17318416,32776456],[]),([6,31,1015808,1082401,3248099,4357252,8659208,33047056],[]),([6,31,1015808,1083361,2097152,4357252,8659208,33047056],[]),([6,31,1015808,1083361,2105344,4329604,17318416,32776456],[(96,0)]),([6,31,1015808,1083361,2128896,4329604,17318416,32776456],[]),([6,31,1015808,1083361,2164802,4337796,8659208,33047056],[]),([6,31,1015808,1083361,2164802,4357252,8659208,32506368],[]),([6,31,1015808,1083361,2164802,4357252,8659208,33047056],[])]
def b25 : List Row := [([6,31,1015808,1083361,2164802,4357252,8659720,32505856],[]),([6,31,1015808,1083361,2164802,4357252,25977624,32776456],[]),([6,31,1015808,1083361,2164802,4358116,8659208,33047056],[]),([6,31,1015808,1083361,2165730,4357252,8659208,33047056],[]),([6,31,1015808,1083361,2172994,4329604,8659208,33047056],[]),([6,31,1015808,1083361,2172994,4329604,17318416,32776456],[(96,0)]),([6,31,1015808,1083361,2194498,4329604,8659208,32506368],[]),([6,31,1015808,1083361,2194498,4329604,8659720,32505856],[]),([6,31,1015808,1083361,2194498,4329604,17318416,32776456],[]),([6,31,1015808,1083361,2194498,4329604,17809936,32776456],[]),([6,31,1015808,1083361,2194498,4329604,25977624,32776456],[]),([6,31,1015808,1083361,2194498,4329604,32776456,33047056],[]),([6,31,1015808,1083361,2194498,4329604,32776456,33317656],[]),([6,31,1015808,1083361,2194498,4330468,17318416,32776456],[]),([6,31,1015808,1083361,2194498,4357252,17318416,32776456],[]),([6,31,1015808,1083361,2194498,5214340,17318416,32776456],[]),([6,31,1015808,1083361,2194498,8659208,17318416,32505860],[(96,0)]),([6,31,1015808,1083361,2194498,8659208,32641156,33047056],[]),([6,31,1015808,1083361,2194498,8659212,17318416,32505856],[(96,0)]),([6,31,1015808,1083361,2194498,12988812,17318416,32776456],[]),([6,31,1015808,1083361,2194498,12988812,25977624,32505856],[]),([6,31,1015808,1083361,2194498,17318416,32641156,32776456],[]),([6,31,1015808,1083361,2194498,17318416,32776456,32911756],[]),([6,31,1015808,1083361,2194527,4329604,17318416,32776456],[])]
def t22 : BT := .nd (blockTree b24) [6,31,1015808,1083361,2164802,4357252,8659208,33317656] (blockTree b25)
def b26 : List Row := [([6,31,1015808,1083361,3145728,4357252,8659208,17318416],[]),([6,31,1015808,1083361,3247203,4357252,8659208,33047056],[]),([6,31,1015808,1083361,3248099,4357252,8659208,33047056],[]),([6,31,1015808,1083361,3275875,4329604,17318416,32776456],[]),([6,31,1015808,1083361,3276771,4329604,17318416,32776456],[]),([6,31,1015808,1090593,2165730,4329604,8659208,33047056],[]),([6,31,1015808,1090593,2165730,4329604,17318416,32776456],[]),([6,31,1015808,1091553,2164802,4329604,8659208,33047056],[]),([6,31,1015808,1091553,2164802,4329604,17318416,32776456],[(96,0)]),([6,31,1015808,1113121,2098144,4329604,17318416,32776456],[]),([6,31,1015808,1113121,2164802,4330468,8659720,32505856],[]),([6,31,1015808,1113121,2164802,4330468,25977624,32776456],[]),([6,31,1015808,1113121,2165730,4329604,8659208,32506368],[]),([6,31,1015808,1113121,2165730,4329604,8659720,32505856],[]),([6,31,1015808,1113121,2165730,4329604,17318416,32776456],[]),([6,31,1015808,1113121,2165730,4329604,25977624,32776456],[]),([6,31,1015808,1113121,2165730,4329604,32776456,33047056],[]),([6,31,1015808,1113121,2165730,4329604,32776456,33317656],[]),([6,31,1015808,1113121,2165730,4330468,17318416,32776456],[]),([6,31,1015808,1113121,2165730,4357252,17318416,32776456],[]),([6,31,1015808,1113121,2165730,5214340,17318416,32776456],[]),([6,31,1015808,1113121,2165730,8659208,17318416,32505860],[]),([6,31,1015808,1113121,2165730,8659208,32641156,33047056],[]),([6,31,1015808,1113121,2165730,8659212,17318416,32505856],[])]
def b27 : List Row := [([6,31,1015808,1113121,2165730,12988812,25977624,32505856],[]),([6,31,1015808,1113121,2165730,17318416,32641156,32776456],[]),([6,31,1015808,1113121,2165730,17318416,32776456,32911756],[]),([6,31,1015808,1113121,3145728,4330468,8659208,17318416],[]),([6,31,1015808,1113121,3248099,4329604,8659208,33047056],[]),([6,31,1015808,1113121,3248099,4329604,17318416,32776456],[]),([6,31,1015808,1113151,2165730,4329604,17318416,32776456],[]),([6,31,1015808,1114081,2164802,4329604,8659208,32506368],[(96,0)]),([6,31,1015808,1114081,2164802,4329604,8659720,32505856],[(96,0)]),([6,31,1015808,1114081,2164802,4330468,17318416,32776456],[]),([6,31,1015808,1114081,2165730,4329604,17318416,32776456],[]),([6,31,1015808,1114081,3248099,4329604,8659208,33047056],[]),([6,31,1015808,1114081,3248099,4329604,17318416,32776456],[]),([6,31,1015808,3180513,4357252,8659208,17318416,32505856],[]),([6,31,1015808,3210273,4330468,8659208,17318416,32505856],[]),([6,31,1015812,1083361,2194498,8659208,17318416,32505856],[]),([6,31,1015812,1113121,2165730,8659208,17318416,32505856],[]),([6,31,1016320,1083361,2164802,4357252,8659208,32505856],[]),([6,31,1016320,1083361,2194498,4329604,8659208,32505856],[]),([6,31,1016320,1114081,2164802,4329604,8659208,32505856],[(96,0)]),([6,31,1081344,2165730,4357252,8659208,17318416,32505856],[]),([6,31,1081344,2194498,4330468,8659208,17318416,32505856],[]),([6,31,1082401,1083361,2194498,4329604,17809936,32776456],[]),([6,31,1082401,1083361,2194498,5214340,17318416,32776456],[(56,0)])]
def t23 : BT := .nd (blockTree b26) [6,31,1015808,1113121,2165730,12988812,17318416,32776456] (blockTree b27)
def t24 : BT := .nd t22 [6,31,1015808,1083361,2195426,4329604,17318416,32776456] t23
def b28 : List Row := [([6,31,1082401,1113121,2165730,5214340,17318416,32776456],[]),([6,31,1082401,2098144,4329604,8659208,17333776,33521664],[]),([6,31,1082401,2098144,4357252,8659208,17318416,33521664],[]),([6,31,1082401,2098144,4357252,8659208,17809936,32505856],[]),([6,31,1082401,2098144,5214340,8659208,17333776,32505856],[]),([6,31,1082401,2128896,4330468,8659208,17318416,33521664],[]),([6,31,1082401,2165730,2194498,5214340,8659208,33047056],[]),([6,31,1082401,2165730,2194498,5214340,17318416,32776456],[]),([6,31,1082401,2165730,2195426,5214340,8659208,33047056],[]),([6,31,1082401,2165730,2195426,5214340,17318416,32776456],[(188,0)]),([6,31,1082401,2165730,3115074,4357252,8659208,33047056],[]),([6,31,1082401,2165730,4357252,5214340,8659208,33047056],[]),([6,31,1082401,2165730,4357252,8659208,9412872,33047056],[]),([6,31,1082401,2165730,4357252,8659208,17318416,32538624],[]),([6,31,1082401,2165730,4357252,8659208,17351184,32505856],[]),([6,31,1082401,2165730,4357252,8659208,17809936,33047056],[]),([6,31,1082401,2165730,4357252,8659208,33047056,33521664],[]),([6,31,1082401,2165730,4357252,8659208,33047056,33538576],[]),([6,31,1082401,2165730,4357252,8691976,17318416,32505856],[]),([6,31,1082401,2165730,4357252,9412872,17318416,32776456],[]),([6,31,1082401,2165730,4357252,9412872,25977624,32505856],[]),([6,31,1082401,2165730,4358116,8659208,17809936,32505856],[]),([6,31,1082401,2165730,5214340,8659208,17326608,32505856],[]),([6,31,1082401,2165730,5214340,8659208,17333776,33047056],[]),([6,31,1082401,2165730,33317656,33538576],[(1024,501861),(1024,309314)])]
def b29 : List Row := [([6,31,1082401,2194498,4330468,8659208,17318416,32538624],[]),([6,31,1082401,2194498,4330468,8659208,17351184,32505856],[]),([6,31,1082401,2194498,4330468,8691976,17318416,32505856],[]),([6,31,1082401,2194498,4330468,9412872,17318416,32776456],[]),([6,31,1082401,2194498,4330468,9412872,25977624,32505856],[]),([6,31,1082401,2195426,4330468,8659208,17809936,32505856],[]),([6,31,1082401,3115074,4330468,8659208,17326608,32505856],[]),([6,31,1082401,3115074,4338660,8659208,17318416,32505856],[(168,0)]),([6,31,1082401,3115074,12989420,32641156],[(1024,277170),(1024,502023)]),([6,31,1082401,7313606,12989420,32505856],[(1024,277175),(1024,502023)]),([6,31,1083361,1113121,2164802,4329604,9412872,33047056],[]),([6,31,1083361,1113121,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,1083361,1113121,2164802,5214340,8659208,33047056],[]),([6,31,1083361,1113121,2164802,5214340,17318416,32776456],[]),([6,31,1083361,1113121,2164802,8659208,17809936,32641156],[(96,0)]),([6,31,1083361,1113121,2164802,9412872,17318416,32641156],[]),([6,31,1083361,1114081,2164802,4329604,9412872,33047056],[]),([6,31,1083361,1114081,2164802,4329604,17809936,32776456],[(96,0)]),([6,31,1083361,2097152,4357252,8659208,17318416,33521664],[(72,0)]),([6,31,1083361,2097152,4357252,8659208,17809936,32505856],[(72,0)]),([6,31,1083361,2128896,4329604,8659208,17318416,33521664],[]),([6,31,1083361,2128896,4329604,8659208,17809936,32505856],[]),([6,31,1083361,2128896,4329604,9412872,17318416,32505856],[]),([6,31,1083361,2164802,2194498,4329604,17809936,32776456],[(72,0)])]
def t25 : BT := .nd (blockTree b28) [6,31,1082401,2173922,5214340,8659208,17318416,32505856] (blockTree b29)
def b30 : List Row := [([6,31,1083361,2164802,4357252,8659208,9412872,33047056],[]),([6,31,1083361,2164802,4357252,8659208,17318416,32538624],[]),([6,31,1083361,2164802,4357252,8659208,17351184,32505856],[]),([6,31,1083361,2164802,4357252,8659208,17809936,32505856],[]),([6,31,1083361,2164802,4357252,8659208,17809936,32776456],[]),([6,31,1083361,2164802,4357252,8659208,17809936,33047056],[]),([6,31,1083361,2164802,4357252,8659208,26207000,32505856],[]),([6,31,1083361,2164802,4357252,8659208,32505856,33538576],[]),([6,31,1083361,2164802,4357252,8659208,33047056,33521664],[]),([6,31,1083361,2164802,4357252,8659208,33047056,33538576],[]),([6,31,1083361,2164802,4357252,8691976,17318416,32505856],[]),([6,31,1083361,2164802,4357252,9412872,17318416,32776456],[]),([6,31,1083361,2164802,4357252,9412872,25977624,32505856],[]),([6,31,1083361,2164802,4358116,8659208,17809936,32505856],[]),([6,31,1083361,2164802,9412872,33538576],[(1024,300101),(1024,267953)]),([6,31,1083361,2164802,26207000,33538576],[(1024,660581),(1024,267953)]),([6,31,1083361,2164802,32776456,33538576],[(1024,300101),(1024,309313)]),([6,31,1083361,2164802,33317656,33538576],[(1024,496741),(1024,309313)]),([6,31,1083361,2164831,4357252,8659208,17809936,32505856],[]),([6,31,1083361,2165730,4357252,8659208,17809936,32505856],[]),([6,31,1083361,2172994,4329604,8659208,17809936,32505856],[(72,0)]),([6,31,1083361,2194498,4329604,8659208,17318416,32538624],[]),([6,31,1083361,2194498,4329604,8659208,17351184,32505856],[]),([6,31,1083361,2194498,4329604,8659208,17809936,32505856],[])]
def b31 : List Row := [([6,31,1083361,2194498,4329604,8659208,26207000,32505856],[]),([6,31,1083361,2194498,4329604,8659208,32505856,33538576],[]),([6,31,1083361,2194498,4329604,8659208,33047056,33521664],[]),([6,31,1083361,2194498,4329604,8691976,17318416,32505856],[]),([6,31,1083361,2194498,4329604,9412872,17318416,32776456],[]),([6,31,1083361,2194498,4329604,9412872,25977624,32505856],[]),([6,31,1083361,2194498,4329604,17318416,17809936,32776456],[]),([6,31,1083361,2194498,4329604,17318416,32776456,33521664],[]),([6,31,1083361,2194498,4329604,17318416,32776456,33530120],[]),([6,31,1083361,2194498,4329604,17809936,32505856,32776456],[]),([6,31,1083361,2194498,4329604,17809936,32776456],[]),([6,31,1083361,2194498,4330468,8659208,17809936,32505856],[]),([6,31,1083361,2194498,4357252,8659208,17809936,32505856],[]),([6,31,1083361,2194498,4357252,9412872,17318416,32505856],[]),([6,31,1083361,2194498,5214340,8659208,17809936,32505856],[]),([6,31,1083361,2194498,8659208,12988812,17809936,32505856],[]),([6,31,1083361,2194498,8659208,17318416,32641156,33521664],[]),([6,31,1083361,2194498,8659208,17809936,32505856,32641156],[]),([6,31,1083361,2194498,9412872,12988812,17318416,32505856],[]),([6,31,1083361,2194498,17809936,32776456],[(1024,284737),(1024,300101)]),([6,31,1083361,2194527,4329604,8659208,17809936,32505856],[]),([6,31,1083361,2195426,4329604,8659208,17809936,32505856],[]),([6,31,1083361,3112960,4357252,8659208,17318416,32505856],[]),([6,31,1083361,3115074,4357252,8659208,17809936,32505856],[])]
def t26 : BT := .nd (blockTree b30) [6,31,1083361,2194498,4329604,8659208,17809936,32776456] (blockTree b31)
def t27 : BT := .nd t25 [6,31,1083361,2164802,4337796,8659208,17809936,32505856] t26
def t28 : BT := .nd t24 [6,31,1082401,1113121,2165730,5214340,8659208,33047056] t27
def t29 : BT := .nd t21 [6,31,33280,1083361,2194498,4329604,8659208,32505856] t28
def t30 : BT := .nd t14 [6,31,992,1090593,2164802,5214340,8659208,33047056] t29
def b32 : List Row := [([6,31,1083361,3247203,4357252,8659208,17809936,32505856],[]),([6,31,1083361,3248099,4357252,8659208,17809936,32505856],[]),([6,31,1083361,3275875,4329604,8659208,17809936,32505856],[]),([6,31,1083361,3275875,5214340,8659208,17318416,32505856],[]),([6,31,1083361,3276771,4329604,8659208,17809936,32505856],[]),([6,31,1083361,19909202,26207000,32505856],[(1024,267961),(1024,309313)]),([6,31,1090593,2165730,5214340,8659208,17318416,32505856],[]),([6,31,1090593,3115074,4330468,8659208,17318416,32505856],[]),([6,31,1091553,2164802,4329604,8659208,17809936,32505856],[(72,0)]),([6,31,1091553,2164802,4329604,9412872,17318416,32505856],[]),([6,31,1113121,2097152,4330468,8659208,17318416,33521664],[]),([6,31,1113121,2098144,4329604,8659208,17318416,33521664],[(168,0)]),([6,31,1113121,2098144,4329604,9412872,17318416,32505856],[]),([6,31,1113121,2164802,4330468,8659208,17318416,32538624],[]),([6,31,1113121,2164802,4330468,8691976,17318416,32505856],[]),([6,31,1113121,2164802,4330468,9412872,17318416,32776456],[]),([6,31,1113121,2164802,4330468,9412872,25977624,32505856],[]),([6,31,1113121,2165730,4329604,8659208,17318416,32538624],[]),([6,31,1113121,2165730,4329604,8659208,33047056,33521664],[]),([6,31,1113121,2165730,4329604,8691976,17318416,32505856],[]),([6,31,1113121,2165730,4329604,9412872,17318416,32776456],[]),([6,31,1113121,2165730,4329604,9412872,25977624,32505856],[]),([6,31,1113121,2165730,4329604,17318416,32776456,33521664],[]),([6,31,1113121,2165730,4329604,17318416,32776456,33530120],[]),([6,31,1113121,2165730,4330468,9412872,17318416,32505856],[])]
def b33 : List Row := [([6,31,1113121,2165730,9412872,12988812,17318416,32505856],[]),([6,31,1113121,3112960,4330468,8659208,17318416,32505856],[]),([6,31,1113121,3248099,5214340,8659208,17318416,32505856],[]),([6,31,1114081,2164802,4330468,9412872,17318416,32505856],[]),([6,31,1114081,2165730,4329604,9412872,17318416,32505856],[]),([6,31,1114081,3248099,4329604,8659208,17809936,32505856],[]),([6,31,1114081,3248099,4329604,9412872,17318416,32505856],[]),([6,31,3115074,5412005,12989420,32505856],[(1024,276978),(1024,502023)]),([6,516,1082401,3115074,8659208,32505856],[(1024,491635),(1024,655480)]),([6,543,31744,1082401,3115074,4330468,8659208,32505856],[]),([6,543,32736,1015808,1082401,2164802,4329604,32776456],[]),([6,543,32736,1015808,1082401,2164802,8659208,32641156],[]),([6,543,32736,1082401,2164802,4329604,9412872,32505856],[]),([6,543,32736,1082401,2164802,5214340,8659208,32505856],[]),([6,543,32736,1082401,3115074,4329604,8659208,32505856],[]),([6,543,1015808,1082401,2164802,4358116,8659208,32505856],[]),([6,543,1015808,1082401,2194498,4330468,8659208,32505856],[]),([6,543,1015808,1113121,2164802,4330468,8659208,32505856],[]),([6,8192,1015808,1082431,2165730,4329604,17318416,32776456],[]),([6,8192,1082401,3115074,4330468,8659208,17318431,32505856],[(96,0)]),([6,8192,1082431,2165730,5214340,8659208,17318416,32505856],[]),([6,8223,1015808,1082401,2165730,4329604,8659208,33047056],[]),([6,8223,1015808,1082401,2165730,4329604,17318416,32776456],[]),([6,8223,1015808,1083361,2164802,4329604,8659208,33047056],[])]
def t31 : BT := .nd (blockTree b32) [6,31,1113121,2165730,8659208,17318416,32641156,33521664] (blockTree b33)
def b34 : List Row := [([6,8223,1082401,2165730,5214340,8659208,17318416,32505856],[]),([6,8223,1082401,3115074,4330468,8659208,17318416,32505856],[]),([6,8223,1083361,2164802,4329604,8659208,17809936,32505856],[(72,0)]),([6,8223,1083361,2164802,4329604,9412872,17318416,32505856],[]),([6,31744,32768,1082431,2165730,4329604,17318416,32776456],[]),([6,31744,32768,3247203,4330468,8659208,17318431,32505856],[]),([6,31744,32772,1082431,2165730,8659208,17318416,32505856],[]),([6,31744,1014750,4330468,8659208,17318431],[(1024,99832),(1024,67046)]),([6,31744,1015808,1082401,3145728,4330468,8659208,17318431],[]),([6,31744,1015808,1082431,2098144,4329604,17318416,32776456],[]),([6,31744,1015808,1082431,2165730,4329604,8659208,32506368],[]),([6,31744,1015808,1082431,2165730,4329604,8659720,32505856],[]),([6,31744,1015808,1082431,2165730,4329604,17318416,32776456],[]),([6,31744,1015808,1082431,2165730,4329604,25977624,32776456],[]),([6,31744,1015808,1082431,2165730,4329604,32776456,33047056],[]),([6,31744,1015808,1082431,2165730,4329604,32776456,33317656],[]),([6,31744,1015808,1082431,2165730,5214340,17318416,32776456],[]),([6,31744,1015808,1082431,2165730,8659208,17318416,32505860],[]),([6,31744,1015808,1082431,2165730,8659208,32641156,33047056],[]),([6,31744,1015808,1082431,2165730,8659212,17318416,32505856],[]),([6,31744,1015808,1082431,2165730,12988812,17318416,32776456],[]),([6,31744,1015808,1082431,2165730,12988812,25977624,32505856],[]),([6,31744,1015808,1082431,2165730,17318416,32641156,32776456],[]),([6,31744,1015808,1082431,2165730,17318416,32776456,32911756],[]),([6,31744,1015808,1082431,3248099,4329604,8659208,33047056],[])]
def b35 : List Row := [([6,31744,1015808,3179553,4330468,8659208,17318431,32505856],[]),([6,31744,1015812,1082431,2165730,8659208,17318416,32505856],[]),([6,31744,1081344,2164802,4330468,8659208,17318431,32505856],[]),([6,31744,1082401,1082431,2165730,5214340,8659208,33047056],[]),([6,31744,1082401,1082431,2165730,5214340,17318416,32776456],[]),([6,31744,1082401,2097152,4330468,8659208,17318431,33521664],[]),([6,31744,1082401,2097183,4330468,8659208,17318416,33521664],[]),([6,31744,1082401,2164802,4330468,8659208,17318431,32538624],[]),([6,31744,1082401,2164802,4330468,8691976,17318431,32505856],[]),([6,31744,1082401,2164802,4330468,9412872,17318431,32776456],[]),([6,31744,1082401,2197570,4330468,8659208,17318431,32505856],[]),([6,31744,1082401,3112960,4330468,8659208,17318431,32505856],[]),([6,31744,1082401,3115074,4330468,8659208,17318431,32505856],[]),([6,31744,1082431,1083361,2164802,4329604,9412872,33047056],[]),([6,31744,1082431,1083361,2164802,4329604,17809936,32776456],[(104,0)]),([6,31744,1082431,1083361,2164802,5214340,8659208,33047056],[]),([6,31744,1082431,2098144,4329604,8659208,17318416,33521664],[]),([6,31744,1082431,2098144,4329604,9412872,17318416,32505856],[]),([6,31744,1082431,2098144,5214340,8659208,17318416,32505856],[]),([6,31744,1082431,2164802,2165730,5214340,17318416,32776456],[]),([6,31744,1082431,2165730,4329604,5214340,17318416,32776456],[]),([6,31744,1082431,2165730,4329604,8659208,17318416,32538624],[]),([6,31744,1082431,2165730,4329604,8659208,33047056,33521664],[]),([6,31744,1082431,2165730,4329604,8691976,17318416,32505856],[])]
def t32 : BT := .nd (blockTree b34) [6,31744,1015808,1082431,3248099,4329604,17318416,32776456] (blockTree b35)
def t33 : BT := .nd t31 [6,8223,1015808,1083361,2164802,4329604,17318416,32776456] t32
def b36 : List Row := [([6,31744,1082431,2165730,4329604,9412872,25977624,32505856],[]),([6,31744,1082431,2165730,4329604,17318416,32776456,33521664],[]),([6,31744,1082431,2165730,4329604,17318416,32776456,33530120],[]),([6,31744,1082431,2165730,4362372,8659208,17318416,32505856],[]),([6,31744,1082431,2165730,5214340,8659208,17318416,32505856],[]),([6,31744,1082431,2165730,5214340,8659208,17318416,32776456],[]),([6,31744,1082431,2165730,5214340,8659208,25977624,32505856],[]),([6,31744,1082431,2165730,5214340,8659208,32505856,33047056],[]),([6,31744,1082431,2165730,5214340,17318416,32505856,32776456],[]),([6,31744,1082431,2165730,5214340,17318416,32776456],[(150,0)]),([6,31744,1082431,2165730,8659208,13611404,17318416,32505856],[]),([6,31744,1082431,2165730,8659208,17318416,32505856,33525892],[]),([6,31744,1082431,2165730,8659208,17318416,32641156,33521664],[]),([6,31744,1082431,2165730,9412872,12988812,17318416,32505856],[]),([6,31744,1082431,3248099,5214340,8659208,17318416,32505856],[]),([6,31744,3179553,4330468,8659208,17318431],[(1024,444907),(1024,67046)]),([6,31744,4330468,8659208,16236000,32539681],[(1024,99832),(1024,67046)]),([6,31744,4330468,8659208,17318431,32538624],[(1024,98808),(1024,66039)]),([6,31744,4330468,8659208,17318431,32539681],[(1024,99832),(1024,67046)]),([6,31744,4330468,8659208,17333791,32539681],[(1024,67046),(1024,72161),(1025,450233)]),([6,31744,4330468,8659208,17383967],[(1024,66022),(1024,98803),(1024,71137),(1025,122553),(1025,285368)]),([6,31744,4330468,8724744,17318431],[(1024,66022),(1024,98801),(1024,71137),(1025,122553),(1025,285368)]),([6,31744,4330468,17318431,24895223,32539681],[(1024,515170),(1024,67046)]),([6,31775,1015808,1082401,2165730,8659208,17318416,32505860],[]),([6,31775,1015808,1082401,2165730,8659212,17318416,32505856],[])]
def b37 : List Row := [([6,31775,1015808,1083361,2164802,8659208,17318416,32505860],[(96,0)]),([6,31775,1015808,1083361,2164802,8659212,17318416,32505856],[(96,0)]),([6,31775,1015808,1083361,2164831,4329604,17318416,32776456],[]),([6,31775,1015812,1082401,2165730,8659208,17318416,32505856],[]),([6,31775,1015812,1083361,2164802,8659208,17318416,32505856],[]),([6,31775,1082401,3115074,4330468,8659208,17318431,32505856],[]),([6,31775,1082431,2165730,5214340,8659208,17318416,32505856],[]),([6,31775,1083361,2164831,4329604,8659208,17809936,32505856],[]),([6,31775,1083361,2164831,4329604,9412872,17318416,32505856],[]),([6,31775,4330468,8659208,17318431,32539681],[(1024,444907),(1024,67046)]),([6,32768,1082401,2194498,4330468,8659208,17318431,32505856],[]),([6,32768,1113121,2164802,4330468,8659208,17318431,32505856],[]),([6,97280,4330468,8659208,17318431],[(1024,66022),(1024,98803),(1024,71137),(1025,122553),(1025,285368)]),([6,1015808,1082401,2128896,4330468,8659208,17318431,32505856],[]),([6,1015808,1082401,2164802,4330468,8659208,17326623,32505856],[]),([6,1015808,1082401,2164802,8659724,32505856],[(1024,491603),(1024,655448)]),([6,1015808,1082401,2164806,8659944,32641156],[(1024,66664),(1024,77927)]),([6,1015808,1082401,2164831,8659720,32641156],[(1024,660760),(1024,496915)]),([6,1015808,1082401,2172994,4330468,8659208,17318431,32505856],[]),([6,1015808,1082401,2194498,4330468,8659208,17318431,32505856],[]),([6,1015808,1082401,2194498,4330468,8659208,17318431,32776456],[]),([6,1015808,1082401,2194527,4330468,8659208,17318431,32505856],[]),([6,1015808,1082401,3275875,4330468,8659208,17318431,32505856],[]),([6,1015808,1082401,12989420,25977631,32505856],[(1024,67255),(1024,72377)])]
def t34 : BT := .nd (blockTree b36) [6,31775,1015808,1082431,2165730,4329604,17318416,32776456] (blockTree b37)
def b38 : List Row := [([6,1015808,1082431,1083361,2194498,4329604,17318416,32776456],[(128,0)]),([6,1015808,1082431,1113121,2165730,4329604,8659208,33047056],[]),([6,1015808,1082431,1113121,2165730,4329604,17318416,32776456],[]),([6,1015808,1082431,1113151,2165730,4329604,17318416,32776456],[]),([6,1015808,1082431,2098144,4329604,8659208,17333776,32505856],[]),([6,1015808,1082431,2164802,8659720,32641156],[(1024,65816),(1024,491795)]),([6,1015808,1082431,2165730,2194498,4329604,17318416,32776456],[]),([6,1015808,1082431,2165730,2194498,8659208,17318416,32641156],[]),([6,1015808,1082431,2165730,2195426,4329604,17318416,32776456],[(188,0)]),([6,1015808,1082431,2165730,4329604,8659208,17326608,32505856],[]),([6,1015808,1082431,2165730,4337796,8659208,17318416,32505856],[]),([6,1015808,1082431,2173922,4329604,8659208,17318416,32505856],[]),([6,1015808,1082431,2194498,4330468,8659208,17318431,32505856],[]),([6,1015808,1082431,2194527,4330468,8659208,17318416,32505856],[]),([6,1015808,1082431,3247203,8659944,32641156],[(1024,700518),(1024,69896)]),([6,1015808,1090593,2164802,4330468,8659208,17318431,32505856],[]),([6,1015808,1090623,2165730,4329604,8659208,17318416,32505856],[]),([6,1015808,1113121,2097152,4330468,8659208,17318431,32505856],[]),([6,1015808,1113121,2097183,4330468,8659208,17318416,32505856],[]),([6,1015808,1113121,2164802,4330468,8659208,17318431,32505856],[]),([6,1015808,1113121,2164802,4330468,8659208,17318431,32776456],[]),([6,1015808,1113121,2164831,2165730,4329604,17318416,32776456],[]),([6,1015808,1113121,2164831,4330468,8659208,17318431,32505856],[]),([6,1015808,1113121,2194498,4330468,8659208,17318431,32505856],[])]
def b39 : List Row := [([6,1015808,1113121,3247203,4330468,8659208,17318431,32505856],[]),([6,1015808,1113121,3275875,4330468,8659208,17318431,32505856],[]),([6,1015808,1113151,2164802,4330468,8659208,17318431,32505856],[]),([6,1015808,1113151,2164831,4330468,8659208,17318416,32505856],[]),([6,1015808,2164802,12989420,25977631,32505856],[(1024,66034),(1024,71156)]),([6,1015808,2164831,3247203,8659944,32641156],[(1024,78321),(1024,69896)]),([6,1082401,1113121,3115074,4330468,8659208,17318431,32505856],[]),([6,1082401,2164831,3115074,8659944,32641156],[(1024,501863),(1024,69896)]),([6,1082401,2194498,3115074,4330468,8659208,17318431,32505856],[]),([6,1082401,2194498,4330468,5214340,8659208,17318431,32505856],[]),([6,1082401,2194498,4330468,8659208,9412872,17318431,32505856],[]),([6,1082401,2194498,4330468,8659208,17318431,32505856,33521664],[]),([6,1082401,3115074,4330468,4357252,8659208,17318431,32505856],[]),([6,1082401,3115074,4330468,4358116,8659208,17318431,32505856],[]),([6,1082405,2164802,5214340,8659944,32505856],[(1024,77926),(1024,65640)]),([6,1082405,3115074,4329604,8659944,32505856],[(1024,77926),(1024,65640)]),([6,1082431,1083361,2194498,4329604,8659208,17809936,32505856],[]),([6,1082431,1113121,2165730,5214340,8659208,17318416,32505856],[]),([6,1082431,1113151,2165730,5214340,8659208,17318416,32505856],[]),([6,1082431,2164802,5214340,8659720,32505856],[(1024,655640),(1024,65811)]),([6,1082431,2165730,2194498,5214340,8659208,17318416,32505856],[]),([6,1082431,2165730,2195426,5214340,8659208,17318416,32505856],[(180,0)]),([6,1082431,2165730,4357252,5214340,8659208,17318416,32505856],[]),([6,1082431,2165730,5214340,8659208,17318416,17333776,32505856],[])]
def t35 : BT := .nd (blockTree b38) [6,1015808,1113121,3115074,4330468,8659208,17318431,32505856] (blockTree b39)
def t36 : BT := .nd t34 [6,1015808,1082405,2164802,8659944,32641156] t35
def t37 : BT := .nd t33 [6,31744,1082431,2165730,4329604,9412872,17318416,32776456] t36
def b40 : List Row := [([6,1082431,2194498,4330468,5214340,8659208,17318416,32505856],[]),([6,1082431,3247203,5214340,8659944,32505856],[(1024,712806),(1024,69896)]),([6,1082431,5214340,8659944,25977624,32505856],[(1024,104121),(1024,65811)]),([6,1113121,2164802,4330468,8659208,9412872,17318431,32505856],[]),([6,1113121,2164802,4330468,8659208,17318431,32505856,33521664],[]),([6,1113121,4330468,8659208,17333791,32505856],[(1024,67046),(1024,72161),(1025,450233)]),([6,2164831,3248099,8659208,17809936,32505856],[(1024,309313),(1024,65839)]),([6,4330468,4357252,8659208,17318431,32539681],[(1024,99832),(1024,73185)]),([6,4330468,4358116,8659208,17318431,32539681],[(1024,444907),(1024,72161),(1025,285368)]),([6,4330468,8659208,17318431,32539681,33521664],[(1024,502195),(1024,67063)]),([6,4330468,8659208,17318431,32539681,33522687],[(1024,67046),(1024,72161)]),([7,4,31,992,31744,1082401,2164802,9412872,33047056],[]),([7,4,31,992,31744,1082401,2164802,17809936,32776456],[(272,0)]),([7,4,31,992,1015808,1082401,2194498,17318416,32776456],[(272,0)]),([7,4,31,992,1015808,1113121,2164802,17318416,32776456],[(272,0)]),([7,4,31,992,1082401,2194498,8659208,17809936,32505856],[(168,0),(272,0)]),([7,4,31,992,1082401,3115074,8659208,17333776,32505856],[(168,0),(272,0)]),([7,4,31,992,1113121,2164802,9412872,17318416,32505856],[(168,0),(272,0)]),([7,4,31,31744,1015808,1082401,2165730,8659208,33047056],[]),([7,4,31,31744,1015808,1082401,2165730,17318416,32776456],[]),([7,4,31,31744,1015808,1083361,2164802,8659208,33047056],[]),([7,4,31,31744,1015808,1083361,2164802,17318416,32776456],[]),([7,4,31,31744,1083361,2164802,8659208,17809936,32505856],[]),([7,4,31,31744,1083361,2164802,9412872,17318416,32505856],[]),([7,4,31,1015808,1083361,2194498,8659208,17318416,32505856],[])]
def b41 : List Row := [([7,4,512,1082401,3115074,8659208,32505856],[(128,0),(1024,491635),(1024,655480)]),([7,4,992,31744,1015808,1082401,2164831,17318416,32776456],[(272,0)]),([7,4,992,31744,1015808,1082431,2164802,17318416,32776456],[(96,0),(272,0)]),([7,4,992,31744,1082401,2164831,8659208,17809936,32505856],[(168,0),(272,0)]),([7,4,992,31744,1082401,3115074,8659208,17318431,32505856],[(56,0),(168,0)]),([7,4,992,31744,1082431,2164802,9412872,17318416,32505856],[(168,0),(272,0)]),([7,4,992,31775,1015808,1082401,2164802,8659208,33047056],[(56,0),(96,0),(216,0)]),([7,4,992,31775,1015808,1082401,2164802,17318416,32776456],[(56,0),(96,0),(272,0)]),([7,4,992,31775,1082401,2164802,8659208,17809936,32505856],[(56,0),(168,0),(272,0)]),([7,4,992,31775,1082401,2164802,9412872,17318416,32505856],[(56,0),(168,0),(272,0)]),([7,4,992,31775,1082401,3115074,8659208,17318416,32505856],[(56,0),(168,0),(272,0)]),([7,4,992,1015808,1082401,2164802,8659208,17333791,32505856],[(56,0),(168,0)]),([7,4,992,1015808,1082401,2164831,8659208,17333776,32505856],[(168,0),(272,0)]),([7,4,992,1015808,1082401,2194498,8659208,17318431,32505856],[(56,0),(168,0)]),([7,4,992,1015808,1082401,2194527,8659208,17318416,32505856],[(168,0),(272,0)]),([7,4,992,1015808,1082431,2164802,8659208,17333776,32505856],[(72,0),(168,0),(272,0)]),([7,4,992,1015808,1082431,2194498,8659208,17318416,32505856],[(72,0),(168,0),(272,0)]),([7,4,992,1015808,1113121,2164802,8659208,17318431,32505856],[(56,0),(168,0)]),([7,4,992,1015808,1113121,2164831,8659208,17318416,32505856],[(168,0),(272,0)]),([7,4,992,1015808,1113151,2164802,8659208,17318416,32505856],[(72,0),(168,0),(272,0)]),([7,4,31744,1015808,1082431,2165730,8659208,17318416,32505856],[]),([7,4,31744,1015808,1083361,2164831,8659208,17318416,32505856],[(168,0),(272,0)]),([7,4,31775,1015808,1082401,2165730,8659208,17318416,32505856],[]),([7,4,31775,1015808,1083361,2164802,8659208,17318416,32505856],[])]
def t38 : BT := .nd (blockTree b40) [7,4,31,1015808,1113121,2165730,8659208,17318416,32505856] (blockTree b41)
def b42 : List Row := [([7,4,1015808,1082401,2164802,8659944,32641156],[(1024,511078),(1024,491635)]),([7,4,1015808,1082401,2165730,8659208,33047056],[(128,0),(1024,655480),(1024,491635)]),([7,4,1015808,1083361,2164802,8659208,33047056],[(128,0),(1024,295032),(1024,491635)]),([7,4,1082401,2164802,5214340,8659944,32505856],[(1024,503910),(1024,491624)]),([7,4,1082401,3115074,4329604,8659944,32505856],[(1024,492646),(1024,491623)]),([7,4,1083361,2164802,8659208,17809936,32505856],[(96,0),(1024,655480),(1024,295027)]),([7,12,992,31744,1015808,1082401,2164802,8659208,33047056],[]),([7,12,992,31744,1015808,1082401,2164802,17318416,32776456],[]),([7,12,992,31744,1082401,2164802,8659208,17809936,32505856],[]),([7,12,992,31744,1082401,2164802,9412872,17318416,32505856],[]),([7,12,992,31744,1082401,3115074,8659208,17318416,32505856],[]),([7,12,992,1015808,1082401,2164802,8659208,17333776,32505856],[]),([7,12,992,1015808,1082401,2194498,8659208,17318416,32505856],[]),([7,12,992,1015808,1113121,2164802,8659208,17318416,32505856],[]),([7,12,31744,1015808,1082401,2165730,8659208,17318416,32505856],[]),([7,12,31744,1015808,1083361,2164802,8659208,17318416,32505856],[]),([7,31,992,8192,1082401,2164802,4329604,9412872,33047056],[(72,0)]),([7,31,992,8192,1082401,2164802,4329604,17809936,32776456],[(72,0),(128,0)]),([7,31,992,8192,1082401,2164802,5214340,8659208,33047056],[(72,0)]),([7,31,992,31744,32768,3145728,4329604,8659208,17318416],[(184,0),(272,0)]),([7,31,992,31744,32768,3247203,4329604,8659208,33047056],[]),([7,31,992,31744,32768,3247203,4329604,17318416,32776456],[(128,0),(192,0)]),([7,31,992,31744,1015808,1082401,2164802,4329604,32776968],[(128,0),(168,0)]),([7,31,992,31744,1015808,1082401,2164802,8659212,33047056],[(72,0)])]
def b43 : List Row := [([7,31,992,31744,1015808,1082401,2164802,32911756,33317656],[(128,0),(168,0),(240,0)]),([7,31,992,31744,1015808,3179553,4329604,8659208,33047056],[]),([7,31,992,31744,1015808,3179553,4329604,17318416,32776456],[(128,0),(192,0)]),([7,31,992,31744,1015812,1082401,2164802,8659208,33047056],[(72,0)]),([7,31,992,31744,1015812,1082401,2164802,17318416,32776456],[(72,0),(128,0)]),([7,31,992,31744,1081344,2097152,4329604,8659208,17318416],[(184,0),(272,0)]),([7,31,992,31744,1081344,2164802,4329604,8659208,33047056],[]),([7,31,992,31744,1081344,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,992,31744,1082401,2097152,4329604,8659208,33538576],[]),([7,31,992,31744,1082401,2097152,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2097152,4329604,17318416,33530120],[(96,0),(128,0)]),([7,31,992,31744,1082401,2097152,4329604,17809936,32776456],[(128,0)]),([7,31,992,31744,1082401,2097152,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,8659208,33079824],[]),([7,31,992,31744,1082401,2164802,4329604,8691976,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,9412872,32506368],[(96,0)]),([7,31,992,31744,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4329604,9412872,33317656],[]),([7,31,992,31744,1082401,2164802,4329604,9413384,32505856],[(96,0),(312,0)]),([7,31,992,31744,1082401,2164802,4329604,17318416,32809224],[(96,0),(128,0)]),([7,31,992,31744,1082401,2164802,4329604,17351184,32776456],[(128,0)]),([7,31,992,31744,1082401,2164802,4329604,17809936,32776456],[(128,0)]),([7,31,992,31744,1082401,2164802,4329604,26207000,32776456],[(128,0),(312,0)]),([7,31,992,31744,1082401,2164802,4329604,32776456,33538576],[(128,0)])]
def t39 : BT := .nd (blockTree b42) [7,31,992,31744,1015808,1082401,2164802,12988812,33317656] (blockTree b43)
def t40 : BT := .nd t38 [7,4,1015808,1082401,2164802,8659720,32505856] t39
def b44 : List Row := [([7,31,992,31744,1082401,2164802,4329604,33047056,33530120],[(96,0)]),([7,31,992,31744,1082401,2164802,4329604,33317656,33530120],[(96,0),(128,0),(312,0)]),([7,31,992,31744,1082401,2164802,4330468,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4330468,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,4357252,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,4357252,17809936,32776456],[]),([7,31,992,31744,1082401,2164802,4362372,8659208,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,8659208,32506368],[(96,0)]),([7,31,992,31744,1082401,2164802,5214340,8659208,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,8659208,33317656],[]),([7,31,992,31744,1082401,2164802,5214340,8659720,32505856],[(96,0)]),([7,31,992,31744,1082401,2164802,5214340,9412872,33047056],[]),([7,31,992,31744,1082401,2164802,5214340,17809936,32776456],[(96,0)]),([7,31,992,31744,1082401,2164802,5214340,25977624,32776456],[(96,0),(228,0)]),([7,31,992,31744,1082401,2164802,5214340,32776456,33047056],[(96,0)]),([7,31,992,31744,1082401,2164802,5214340,32776456,33317656],[(96,0),(256,0),(284,0)]),([7,31,992,31744,1082401,2164802,8659208,13611404,33047056],[]),([7,31,992,31744,1082401,2164802,8659208,32641156,33538576],[(128,0)]),([7,31,992,31744,1082401,2164802,9412872,12988812,33047056],[]),([7,31,992,31744,1082401,2164802,9412872,13611404,33047056],[]),([7,31,992,31744,1082401,2164802,9412872,32641156,33047056],[(96,0)]),([7,31,992,31744,1082401,2164802,12988812,26207000,32505856],[(128,0),(312,0)]),([7,31,992,31744,1082401,2164802,13611404,26207000,32505856],[(96,0)]),([7,31,992,31744,1082401,2164831,4329604,17809936,32776456],[(72,0),(128,0)]),([7,31,992,31744,1082401,2164831,5214340,17318416,32776456],[(72,0),(96,0),(216,0)])]
def b45 : List Row := [([7,31,992,31744,1082401,2164831,9412872,17318416,32641156],[(72,0),(96,0),(216,0)]),([7,31,992,31744,1082401,2194498,4329604,17809936,32776456],[]),([7,31,992,31744,1082401,2197570,4329604,8659208,33047056],[]),([7,31,992,31744,1082401,2197570,4329604,17318416,32776456],[]),([7,31,992,31744,1082401,3115074,4329604,8659208,32506368],[]),([7,31,992,31744,1082401,3115074,4329604,8659720,32505856],[]),([7,31,992,31744,1082401,3115074,4329604,32776456,33047056],[]),([7,31,992,31744,1082401,3115074,8659208,32641156,33047056],[]),([7,31,992,31744,1082401,3115074,12988812,25977624,32505856],[]),([7,31,992,31744,1082401,3145728,4329604,8659208,17809936],[]),([7,31,992,31744,1082401,3145728,4329604,9412872,17318416],[(96,0)]),([7,31,992,31744,1082401,3247203,4329604,9412872,33047056],[(96,0)]),([7,31,992,31744,1082401,3247203,4329604,17809936,32776456],[(96,0),(128,0)]),([7,31,992,31744,1082401,3247203,5214340,8659208,33047056],[(96,0)]),([7,31,992,31744,1082431,2164802,5214340,17318416,32776456],[(72,0),(96,0),(128,0),(216,0)]),([7,31,992,31744,1082431,2164802,9412872,17318416,32641156],[(72,0),(96,0),(128,0),(216,0)]),([7,31,992,31744,3179553,4329604,8659208,17318416,33521664],[(96,0),(144,0),(216,0),(304,0)]),([7,31,992,31744,3179553,4329604,8659208,17809936,32505856],[(304,0)]),([7,31,992,31744,3179553,4329604,9412872,17318416,32505856],[(96,0),(304,0)]),([7,31,992,31744,3247203,4329604,8659208,17318416,32538624],[(96,0),(144,0),(216,0),(304,0)]),([7,31,992,31744,3247203,4329604,8659208,17351184,32505856],[(304,0)]),([7,31,992,31744,3247203,4329604,8691976,17318416,32505856],[(96,0),(144,0),(216,0),(304,0)]),([7,31,992,31744,12988812,25977624,32539681],[(1024,67063),(1024,83425)]),([7,31,992,31748,1015808,1082401,2164802,8659208,33047056],[])]
def t41 : BT := .nd (blockTree b44) [7,31,992,31744,1082401,2164831,8659208,17809936,32641156] (blockTree b45)
def b46 : List Row := [([7,31,992,31748,1082401,2164802,8659208,17809936,32505856],[]),([7,31,992,31748,1082401,2164802,9412872,17318416,32505856],[]),([7,31,992,31748,1082401,3115074,8659208,17318416,32505856],[]),([7,31,992,31775,1082401,2164802,4329604,9412872,33047056],[]),([7,31,992,31775,1082401,2164802,4329604,17809936,32776456],[(128,0)]),([7,31,992,31775,1082401,2164802,5214340,8659208,33047056],[]),([7,31,992,31775,1082401,2164802,5214340,17318416,32776456],[(96,0),(128,0),(216,0)]),([7,31,992,31775,1082401,2164802,8659208,17809936,32641156],[(128,0)]),([7,31,992,31775,1082401,2164802,9412872,17318416,32641156],[(96,0),(128,0),(216,0)]),([7,31,992,32768,1082401,2164802,4357252,8659208,33047056],[]),([7,31,992,32768,1082401,2194498,4329604,17318416,32776456],[(96,0),(184,0)]),([7,31,992,32768,1113121,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,992,32768,3247203,4329604,8659208,17333776,32505856],[(96,0),(144,0),(304,0)]),([7,31,992,32768,3275875,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,992,1014750,4329604,8659208,17333776],[(1024,99832),(1024,67063)]),([7,31,992,1015808,1082401,2097152,4357252,8659208,33047056],[]),([7,31,992,1015808,1082401,2105344,4329604,17318416,32776456],[(96,0),(128,0),(184,0)]),([7,31,992,1015808,1082401,2128896,4329604,17318416,32776456],[(96,0),(184,0)]),([7,31,992,1015808,1082401,2164802,4337796,8659208,33047056],[]),([7,31,992,1015808,1082401,2164802,4357252,8659208,32506368],[]),([7,31,992,1015808,1082401,2164802,4357252,8659208,33047056],[]),([7,31,992,1015808,1082401,2164802,4357252,8659208,33317656],[]),([7,31,992,1015808,1082401,2164802,4357252,8659720,32505856],[]),([7,31,992,1015808,1082401,2164802,4357252,17333776,32776456],[])]
def b47 : List Row := [([7,31,992,1015808,1082401,2164802,4358116,8659208,33047056],[]),([7,31,992,1015808,1082401,2164831,8659208,17333776,32641156],[(96,0),(128,0),(216,0)]),([7,31,992,1015808,1082401,2172994,4329604,8659208,33047056],[]),([7,31,992,1015808,1082401,2172994,4329604,17318416,32776456],[(96,0),(128,0),(184,0)]),([7,31,992,1015808,1082401,2194498,4329604,8659208,32506368],[(96,0)]),([7,31,992,1015808,1082401,2194498,4329604,8659720,32505856],[(96,0)]),([7,31,992,1015808,1082401,2194498,4329604,17318416,32776456],[(96,0),(184,0)]),([7,31,992,1015808,1082401,2194498,4329604,17318431,32776456],[(96,0),(128,0),(184,0)]),([7,31,992,1015808,1082401,2194498,4329604,17333776,32776456],[(96,0),(184,0)]),([7,31,992,1015808,1082401,2194498,4329604,17809936,32776456],[(96,0)]),([7,31,992,1015808,1082401,2194498,4329604,25977624,32776456],[(96,0),(228,0)]),([7,31,992,1015808,1082401,2194498,4329604,32776456,33047056],[(96,0)]),([7,31,992,1015808,1082401,2194498,4329604,32776456,33317656],[(96,0),(284,0)]),([7,31,992,1015808,1082401,2194498,8659208,32641156,33047056],[(96,0),(232,0)]),([7,31,992,1015808,1082401,2194498,12988812,25977624,32505856],[(96,0),(184,0)]),([7,31,992,1015808,1082401,2194527,4329604,17318416,32776456],[(96,0),(216,0)]),([7,31,992,1015808,1082401,3145728,4329604,8659208,17333776],[(96,0),(184,0)]),([7,31,992,1015808,1082401,3247203,4357252,8659208,33047056],[]),([7,31,992,1015808,1082401,3275875,4329604,17318416,32776456],[(96,0),(184,0)]),([7,31,992,1015808,1082431,2164802,8659208,17333776,32641156],[(96,0),(128,0),(216,0)]),([7,31,992,1015808,1082431,2194498,4329604,17318416,32776456],[(96,0),(128,0),(216,0)]),([7,31,992,1015808,1090593,2164802,4329604,8659208,33047056],[]),([7,31,992,1015808,1090593,2164802,4329604,17318416,32776456],[(96,0),(128,0),(184,0)]),([7,31,992,1015808,1113121,2097152,4329604,17318416,32776456],[(128,0)])]
def t42 : BT := .nd (blockTree b46) [7,31,992,1015808,1082401,2164802,4357252,25977624,32776456] (blockTree b47)
def t43 : BT := .nd t41 [7,31,992,31748,1015808,1082401,2164802,17318416,32776456] t42
def t44 : BT := .nd t40 [7,31,992,31744,1082401,2164802,4329604,32776456,33547032] t43
def t45 : BT := .nd t37 [6,1082431,2165730,7313606,8659208,32505856] t44
def b48 : List Row := [([7,31,992,1015808,1113121,2164802,4329604,8659720,32505856],[(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,17318431,32776456],[(96,0),(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,17333776,32776456],[(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,17809936,32776456],[(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,25977624,32776456],[(128,0),(228,0)]),([7,31,992,1015808,1113121,2164802,4329604,32776456,33047056],[(128,0)]),([7,31,992,1015808,1113121,2164802,4329604,32776456,33317656],[(128,0),(284,0)]),([7,31,992,1015808,1113121,2164802,8659208,32641156,33047056],[(128,0)]),([7,31,992,1015808,1113121,2164802,12988812,25977624,32505856],[(128,0)]),([7,31,992,1015808,1113121,2164831,4329604,17318416,32776456],[(96,0),(128,0),(216,0)]),([7,31,992,1015808,1113121,2194498,4329604,17318416,32776456],[]),([7,31,992,1015808,1113121,3145728,4329604,8659208,17318416],[(272,0)]),([7,31,992,1015808,1113121,3247203,4329604,8659208,33047056],[]),([7,31,992,1015808,1113121,3247203,4329604,17318416,32776456],[(128,0),(184,0)]),([7,31,992,1015808,1113121,3275875,4329604,17318416,32776456],[]),([7,31,992,1015808,1113151,2164802,4329604,17318416,32776456],[(128,0),(216,0)]),([7,31,992,1015808,3179553,4329604,8659208,17333776,32505856],[(96,0),(144,0),(304,0)]),([7,31,992,1015808,3210273,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,992,1015812,1082401,2164802,8659208,17333776,32505856],[(96,0)]),([7,31,992,1015812,1082401,2194498,8659208,17318416,32505856],[(96,0)]),([7,31,992,1015812,1113121,2164802,8659208,17318416,32505856],[(96,0),(184,0)]),([7,31,992,1081344,2164802,4329604,8659208,17333776,32505856],[(96,0),(304,0)]),([7,31,992,1081344,2194498,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,992,1082401,1113121,2164802,4329604,9412872,33047056],[(72,0)])]
def b49 : List Row := [([7,31,992,1082401,1113121,2164802,5214340,8659208,33047056],[(72,0)]),([7,31,992,1082401,2097152,4329604,8659208,17333776,33521664],[(72,0),(96,0),(304,0)]),([7,31,992,1082401,2097152,4357252,8659208,17809936,32505856],[(96,0)]),([7,31,992,1082401,2128896,4329604,8659208,17318416,33521664],[(72,0),(216,0)]),([7,31,992,1082401,2128896,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2128896,4329604,9412872,17318416,32505856],[(72,0)]),([7,31,992,1082401,2164802,2194498,4329604,17809936,32776456],[(96,0)]),([7,31,992,1082401,2164802,2194498,5214340,8659208,33047056],[]),([7,31,992,1082401,2164802,3115074,4357252,8659208,33047056],[]),([7,31,992,1082401,2164802,4329604,8659208,17333776,32538624],[(72,0),(96,0),(304,0)]),([7,31,992,1082401,2164802,4329604,8691976,17333776,32505856],[(72,0),(96,0),(304,0)]),([7,31,992,1082401,2164802,4329604,9412872,17333776,32776456],[(72,0),(96,0),(200,0),(304,0)]),([7,31,992,1082401,2164802,4337796,8659208,17809936,32505856],[(96,0)]),([7,31,992,1082401,2164802,4357252,5214340,8659208,33047056],[]),([7,31,992,1082401,2164802,4357252,8659208,9412872,33047056],[]),([7,31,992,1082401,2164802,4357252,8659208,17351184,32505856],[]),([7,31,992,1082401,2164802,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,2164802,4357252,8659208,17809936,32641156],[(96,0)]),([7,31,992,1082401,2164802,4357252,8659208,17809936,32776456],[]),([7,31,992,1082401,2164802,4357252,8659208,17809936,33047056],[]),([7,31,992,1082401,2164802,4357252,8659208,26207000,32505856],[]),([7,31,992,1082401,2164802,4357252,8659208,32505856,33538576],[]),([7,31,992,1082401,2164802,4357252,8659208,33047056,33521664],[]),([7,31,992,1082401,2164802,4357252,8659208,33047056,33538576],[])]
def t46 : BT := .nd (blockTree b48) [7,31,992,1082401,1113121,2164802,4329604,17809936,32776456] (blockTree b49)
def b50 : List Row := [([7,31,992,1082401,2164802,4357252,9412872,25977624,32505856],[]),([7,31,992,1082401,2164802,4358116,8659208,17809936,32505856],[]),([7,31,992,1082401,2164802,9412872,33525892],[(72,0),(1024,665896),(1024,103089),(1025,110257),(1025,431608)]),([7,31,992,1082401,2164802,13611404,33525892],[(72,0),(1024,665864),(1024,103089),(1025,431608)]),([7,31,992,1082401,2164802,32776456,33525892],[(72,0),(1024,502056),(1024,504102),(1025,431769)]),([7,31,992,1082401,2164802,32911756,33525892],[(72,0),(96,0),(1024,502024),(1024,511270),(1025,431769)]),([7,31,992,1082401,2164831,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,2164831,5214340,8659208,17333776,32505856],[(72,0),(216,0)]),([7,31,992,1082401,2172994,4329604,8659208,17809936,32505856],[(96,0),(304,0)]),([7,31,992,1082401,2194498,3115074,4329604,8659208,33047056],[]),([7,31,992,1082401,2194498,3115074,4329604,17318416,32776456],[]),([7,31,992,1082401,2194498,4329604,5214340,17318416,32776456],[(72,0),(200,0)]),([7,31,992,1082401,2194498,4329604,8659208,17318416,32538624],[(72,0),(216,0)]),([7,31,992,1082401,2194498,4329604,8659208,17351184,32505856],[]),([7,31,992,1082401,2194498,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,4329604,8659208,17809936,32776456],[(200,0)]),([7,31,992,1082401,2194498,4329604,8659208,26207000,32505856],[]),([7,31,992,1082401,2194498,4329604,8659208,32505856,33538576],[]),([7,31,992,1082401,2194498,4329604,8659208,33047056,33521664],[(72,0),(304,0)]),([7,31,992,1082401,2194498,4329604,8691976,17318416,32505856],[(72,0),(216,0)]),([7,31,992,1082401,2194498,4329604,9412872,17318416,32776456],[(72,0),(200,0),(216,0)]),([7,31,992,1082401,2194498,4329604,9412872,17333776,32505856],[(72,0)]),([7,31,992,1082401,2194498,4329604,9412872,25977624,32505856],[(72,0),(200,0)]),([7,31,992,1082401,2194498,4329604,17318416,32776456,33521664],[(72,0),(304,0)]),([7,31,992,1082401,2194498,4329604,17318416,32776456,33530120],[(72,0),(248,0),(304,0)])]
def b51 : List Row := [([7,31,992,1082401,2194498,4329604,17809936,32776456],[(73,0),(82,0),(106,0),(249,0)]),([7,31,992,1082401,2194498,4330468,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,2194498,5214340,8659208,17809936,32505856],[(72,0)]),([7,31,992,1082401,2194498,5214340,8659208,25977624,32505856],[(72,0),(200,0),(228,0)]),([7,31,992,1082401,2194498,5214340,8659208,32505856,33047056],[(72,0),(248,0)]),([7,31,992,1082401,2194498,5214340,32776456],[(72,0),(1024,449831),(1024,69928)]),([7,31,992,1082401,2194527,4329604,8659208,17809936,32505856],[]),([7,31,992,1082401,2194527,5214340,8659208,17318416,32505856],[(72,0),(216,0)]),([7,31,992,1082401,2197570,4329604,8659208,17333776,32505856],[(304,0)]),([7,31,992,1082401,3112960,4329604,8659208,17333776,32505856],[(72,0)]),([7,31,992,1082401,3115074,4329604,8659208,17326608,32505856],[(216,0)]),([7,31,992,1082401,3115074,4329604,8659208,17333776,32505856],[]),([7,31,992,1082401,3115074,4329604,8659208,17333791,32505856],[]),([7,31,992,1082401,3115074,4330468,8659208,17333776,32505856],[]),([7,31,992,1082401,3115074,4357252,8659208,17333776,32505856],[]),([7,31,992,1082401,3115074,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,3115074,4357252,8659208,25977624,32505856],[(228,0)]),([7,31,992,1082401,3115074,4357252,8659208,32505856,33047056],[]),([7,31,992,1082401,3115074,9412872,32641156],[(72,0),(1024,665896),(1024,103090),(1025,431604)]),([7,31,992,1082401,3115074,12988812,32641156],[(1024,665864),(1024,103090)]),([7,31,992,1082401,3247203,4357252,8659208,17809936,32505856],[]),([7,31,992,1082401,3275875,4329604,8659208,17809936,32505856],[(72,0)]),([7,31,992,1082401,4357252,25977624,33047056],[(1024,100020),(1024,67051),(1025,300729)])]
def t47 : BT := .nd (blockTree b50) [7,31,992,1082401,2194498,4329604,17809936,32505856,32776456] (blockTree b51)
def t48 : BT := .nd t46 [7,31,992,1082401,2164802,4357252,9412872,17333776,32505856] t47
def b52 : List Row := [([7,31,992,1082401,7313606,13611404,32505856],[(72,0),(1024,441015),(1024,504102),(1025,431604)]),([7,31,992,1082401,8659208,21659284,32641156],[(1024,301547),(1024,69928),(1025,66233)]),([7,31,992,1082431,2164802,5214340,8659208,17333776,32505856],[(72,0),(96,0),(216,0)]),([7,31,992,1082431,2194498,5214340,8659208,17318416,32505856],[(72,0),(96,0),(216,0)]),([7,31,992,1090593,2164802,4329604,8659208,17809936,32505856],[(96,0),(304,0)]),([7,31,992,1090593,2164802,4329604,9412872,17318416,32505856],[(72,0),(304,0)]),([7,31,992,1090593,3115074,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,992,1113121,2097152,4329604,8659208,17318416,33521664],[(96,0),(216,0)]),([7,31,992,1113121,2097152,4329604,9412872,17318416,32505856],[(96,0)]),([7,31,992,1113121,2164802,4329604,8659208,17318416,32538624],[(96,0),(216,0)]),([7,31,992,1113121,2164802,4329604,8659208,33047056,33521664],[(96,0)]),([7,31,992,1113121,2164802,4329604,8691976,17318416,32505856],[(96,0),(216,0)]),([7,31,992,1113121,2164802,4329604,9412872,17318416,32505856],[]),([7,31,992,1113121,2164802,4329604,9412872,17318416,32776456],[(96,0),(216,0)]),([7,31,992,1113121,2164802,4329604,9412872,17318431,32505856],[(72,0),(96,0)]),([7,31,992,1113121,2164802,4329604,9412872,17333776,32505856],[]),([7,31,992,1113121,2164802,4329604,9412872,17809936,32505856],[]),([7,31,992,1113121,2164802,4329604,9412872,25977624,32505856],[(96,0),(228,0)]),([7,31,992,1113121,2164802,4329604,9412872,26207000,32505856],[(228,0)]),([7,31,992,1113121,2164802,4329604,9412872,32505856,33047056],[]),([7,31,992,1113121,2164802,4329604,17318416,32505856,33530120],[(248,0)]),([7,31,992,1113121,2164802,4329604,17318416,32776456,33521664],[(96,0)]),([7,31,992,1113121,2164802,4329604,17318416,32776456,33530120],[(96,0),(248,0)]),([7,31,992,1113121,2164802,5214340,8659208,17809936,32505856],[]),([7,31,992,1113121,2164831,4329604,9412872,17318416,32505856],[(72,0),(216,0)])]
def b53 : List Row := [([7,31,992,1113121,3112960,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,992,1113121,3115074,4329604,8659208,17809936,32505856],[]),([7,31,992,1113121,3115074,4329604,9412872,17318416,32505856],[]),([7,31,992,1113121,3247203,4329604,8659208,17809936,32505856],[(96,0),(304,0)]),([7,31,992,1113121,3247203,4329604,9412872,17318416,32505856],[(304,0)]),([7,31,992,1113121,3275875,4329604,9412872,17318416,32505856],[]),([7,31,992,1113151,2164802,4329604,9412872,17318416,32505856],[(96,0),(216,0)]),([7,31,992,3115074,5412005,12988812,32505856],[(1024,440818),(1024,502055)]),([7,31,992,3179553,4329604,8659208,17333776],[(1024,117217),(1024,281062)]),([7,31,992,3247203,4357252,8659208,32539681],[(1024,516391),(1024,69928)]),([7,31,992,4329604,8659208,16220655,32539681],[(1024,502055),(1024,67063)]),([7,31,992,4329604,8659208,17333776,32538624],[(1024,66039),(1024,98808)]),([7,31,992,4329604,8659208,17333776,32539681],[(1024,99832),(1024,67063)]),([7,31,992,4329604,8659208,17333791,32539681],[(1024,301547),(1024,67063),(1025,88761)]),([7,31,992,4329604,8659208,17399312],[(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]),([7,31,992,4329604,8659208,21659284,32539681],[(1024,301547),(1024,69928),(1025,66233)]),([7,31,992,4329604,8724744,17333776],[(1024,66034),(1024,98801),(1024,83425),(1025,67255),(1025,268984)]),([7,31,992,4329604,12988812,17333776,32539681],[(1024,99832),(1024,83425),(1025,66232)]),([7,31,992,4329604,17333776,24895223,32539681],[(1024,515170),(1024,67063)]),([7,31,992,4330468,8659208,17333776,32539681],[(1024,67063),(1024,83425),(1025,285368)]),([7,31,992,4357252,8659208,16236015,32539681],[(1024,99832),(1024,67051)]),([7,31,992,4357252,8659208,17333776,32539681],[(1024,67063),(1024,83425)]),([7,31,992,4357252,8659208,17383952],[(1024,66027),(1024,98803),(1024,76257),(1025,67255),(1025,268984)]),([7,31,992,4357252,8659208,21648020,32539681],[(1024,69928),(1024,78305)])]
def t49 : BT := .nd (blockTree b52) [7,31,992,1113121,2194498,4329604,9412872,17318416,32505856] (blockTree b53)
def b54 : List Row := [([7,31,992,4357252,8659208,25977624,32539681],[(1024,301561),(1024,67051),(1025,99001)]),([7,31,996,31744,1015808,1082401,2164802,8659208,33047056],[(72,0)]),([7,31,996,31744,1015808,1082401,2164802,17318416,32776456],[(72,0)]),([7,31,996,31744,1082401,2164802,8659208,17809936,32505856],[(72,0)]),([7,31,996,31744,1082401,2164802,9412872,17318416,32505856],[(72,0)]),([7,31,996,31744,1082401,3115074,8659208,17318416,32505856],[(72,0),(216,0)]),([7,31,996,1015808,1082401,2164802,8659208,17333776,32505856],[(216,0)]),([7,31,996,1015808,1082401,2194498,8659208,17318416,32505856],[(216,0)]),([7,31,996,1015808,1113121,2164802,8659208,17318416,32505856],[(216,0)]),([7,31,1023,4329604,8659208,17333776,32539681],[(1024,281062),(1024,67063),(1025,71351)]),([7,31,1023,4357252,8659208,17318416,32539681],[(1024,281062),(1024,67051),(1025,71351)]),([7,31,8192,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,8192,1015808,1082401,2165730,4329604,17318416,32776456],[]),([7,31,8192,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,8192,1015808,1083361,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,8192,1082401,2165730,5214340,8659208,17318416,32505856],[]),([7,31,8192,1082401,3115074,4330468,8659208,17318416,32505856],[]),([7,31,8192,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,8192,1083361,2164802,4329604,9412872,17318416,32505856],[]),([7,31,9184,1015808,1082401,2164802,4329604,8659208,33047056],[]),([7,31,9184,1015808,1082401,2164802,4329604,17318416,32776456],[(96,0),(128,0)]),([7,31,9184,1015808,1082401,2164802,8659208,17318416,32641156],[(96,0),(128,0)]),([7,31,9184,1082401,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,9184,1082401,2164802,4329604,9412872,17318416,32505856],[(72,0)])]
def b55 : List Row := [([7,31,9184,1082401,3115074,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,31744,32768,1082401,2165730,4329604,8659208,33047056],[]),([7,31,31744,32768,1082401,2165730,4329604,17318416,32776456],[]),([7,31,31744,32768,1083361,2164802,4329604,8659208,33047056],[]),([7,31,31744,32768,1083361,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,31744,32768,3247203,4330468,8659208,17318416,32505856],[]),([7,31,31744,32768,3248099,4329604,8659208,17318416,32505856],[]),([7,31,31744,33280,1083361,2164802,4329604,8659208,32505856],[(128,0)]),([7,31,31744,1014750,4330468,8659208,17318416],[(1024,67046),(1024,72161)]),([7,31,31744,1015808,1082401,2098144,4329604,8659208,33047056],[]),([7,31,31744,1015808,1082401,2098144,4329604,17318416,32776456],[]),([7,31,31744,1015808,1082401,2164802,4330468,8659720,32505856],[]),([7,31,31744,1015808,1082401,2164802,4330468,25977624,32776456],[]),([7,31,31744,1015808,1082401,2165730,4329604,8659208,32506368],[]),([7,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,4329604,8659208,33317656],[]),([7,31,31744,1015808,1082401,2165730,4329604,8659720,32505856],[]),([7,31,31744,1015808,1082401,2165730,4329604,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,4329604,25977624,32776456],[]),([7,31,31744,1015808,1082401,2165730,4329604,32776456,33047056],[]),([7,31,31744,1015808,1082401,2165730,4329604,32776456,33317656],[]),([7,31,31744,1015808,1082401,2165730,4330468,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,4330468,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,4357252,8659208,33047056],[])]
def t50 : BT := .nd (blockTree b54) [7,31,9184,1082401,2164802,5214340,8659208,17318416,32505856] (blockTree b55)
def t51 : BT := .nd t49 [7,31,992,4357252,8659208,21659284,32539681] t50
def t52 : BT := .nd t48 [7,31,992,1082401,7313606,12988812,32505856] t51
def b56 : List Row := [([7,31,31744,1015808,1082401,2165730,5214340,8659208,33047056],[]),([7,31,31744,1015808,1082401,2165730,5214340,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,8659208,12988812,33047056],[]),([7,31,31744,1015808,1082401,2165730,8659208,17318416,32505860],[]),([7,31,31744,1015808,1082401,2165730,8659208,32641156,33047056],[]),([7,31,31744,1015808,1082401,2165730,8659212,17318416,32505856],[]),([7,31,31744,1015808,1082401,2165730,12988812,17318416,32776456],[]),([7,31,31744,1015808,1082401,2165730,12988812,25977624,32505856],[]),([7,31,31744,1015808,1082401,2165730,17318416,32641156,32776456],[]),([7,31,31744,1015808,1082401,2165730,17318416,32776456,32911756],[]),([7,31,31744,1015808,1082401,3145728,4330468,8659208,17318416],[]),([7,31,31744,1015808,1082401,3248099,4329604,8659208,33047056],[]),([7,31,31744,1015808,1082401,3248099,4329604,17318416,32776456],[]),([7,31,31744,1015808,1082431,2165730,4329604,17318416,32776456],[]),([7,31,31744,1015808,1083361,2097152,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2097152,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,8659208,32506368],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4329604,8659208,33317656],[]),([7,31,31744,1015808,1083361,2164802,4329604,8659720,32505856],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,9412872,33047056],[]),([7,31,31744,1015808,1083361,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,17809936,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,25977624,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,4329604,32776456,33047056],[(128,0)])]
def b57 : List Row := [([7,31,31744,1015808,1083361,2164802,4330468,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4330468,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,4357252,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,4357252,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,5214340,8659208,33047056],[]),([7,31,31744,1015808,1083361,2164802,5214340,17318416,32776456],[]),([7,31,31744,1015808,1083361,2164802,8659208,12988812,33047056],[]),([7,31,31744,1015808,1083361,2164802,8659208,17318416,32505860],[(128,0)]),([7,31,31744,1015808,1083361,2164802,8659208,32641156,33047056],[(128,0)]),([7,31,31744,1015808,1083361,2164802,8659212,17318416,32505856],[(128,0)]),([7,31,31744,1015808,1083361,2164802,12988812,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,12988812,25977624,32505856],[(128,0)]),([7,31,31744,1015808,1083361,2164802,17318416,32641156,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2164802,17318416,32776456,32911756],[(128,0)]),([7,31,31744,1015808,1083361,2164831,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,2165730,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,2165730,4329604,17318416,32776456],[]),([7,31,31744,1015808,1083361,2194498,4329604,17318416,32776456],[]),([7,31,31744,1015808,1083361,3145728,4329604,8659208,17318416],[]),([7,31,31744,1015808,1083361,3247203,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,3247203,4329604,17318416,32776456],[(128,0)]),([7,31,31744,1015808,1083361,3247203,8659208,17318416,32641156],[(128,0)]),([7,31,31744,1015808,1083361,3248099,4329604,8659208,33047056],[]),([7,31,31744,1015808,1083361,3248099,4329604,17318416,32776456],[])]
def t53 : BT := .nd (blockTree b56) [7,31,31744,1015808,1083361,2164802,4329604,32776456,33317656] (blockTree b57)
def b58 : List Row := [([7,31,31744,1015808,3179553,4330468,8659208,17318416,32505856],[]),([7,31,31744,1015808,3180513,4329604,8659208,17318416,32505856],[]),([7,31,31744,1015812,1082401,2165730,8659208,17318416,32505856],[]),([7,31,31744,1015812,1083361,2164802,8659208,17318416,32505856],[]),([7,31,31744,1016320,1083361,2164802,4329604,8659208,32505856],[(128,0)]),([7,31,31744,1081344,2164802,4330468,8659208,17318416,32505856],[]),([7,31,31744,1081344,2165730,4329604,8659208,17318416,32505856],[]),([7,31,31744,1082401,1083361,2164802,4329604,9412872,33047056],[]),([7,31,31744,1082401,1083361,2164802,4329604,17809936,32776456],[(128,0)]),([7,31,31744,1082401,1083361,2164802,5214340,8659208,33047056],[]),([7,31,31744,1082401,1083361,2164802,5214340,17318416,32776456],[(72,0)]),([7,31,31744,1082401,1083361,2164802,8659208,17809936,32641156],[(72,0),(128,0)]),([7,31,31744,1082401,1083361,2164802,9412872,17318416,32641156],[(72,0)]),([7,31,31744,1082401,2097152,4330468,8659208,17318416,33521664],[]),([7,31,31744,1082401,2098144,4329604,8659208,17318416,33521664],[(216,0)]),([7,31,31744,1082401,2098144,4329604,8659208,17809936,32505856],[]),([7,31,31744,1082401,2098144,4329604,9412872,17318416,32505856],[]),([7,31,31744,1082401,2098144,5214340,8659208,17318416,32505856],[]),([7,31,31744,1082401,2164802,2165730,5214340,8659208,33047056],[]),([7,31,31744,1082401,2164802,2165730,5214340,17318416,32776456],[]),([7,31,31744,1082401,2164802,4330468,8659208,17318416,32538624],[]),([7,31,31744,1082401,2164802,4330468,8659208,17351184,32505856],[]),([7,31,31744,1082401,2164802,4330468,8659208,17809936,33047056],[]),([7,31,31744,1082401,2164802,4330468,8691976,17318416,32505856],[])]
def b59 : List Row := [([7,31,31744,1082401,2164802,4330468,9412872,25977624,32505856],[]),([7,31,31744,1082401,2165730,3115074,4329604,8659208,33047056],[]),([7,31,31744,1082401,2165730,3115074,4329604,17318416,32776456],[]),([7,31,31744,1082401,2165730,3115074,8659208,17318416,32641156],[]),([7,31,31744,1082401,2165730,4329604,5214340,8659208,33047056],[]),([7,31,31744,1082401,2165730,4329604,5214340,17318416,32776456],[]),([7,31,31744,1082401,2165730,4329604,8659208,9412872,33047056],[]),([7,31,31744,1082401,2165730,4329604,8659208,17318416,32538624],[]),([7,31,31744,1082401,2165730,4329604,8659208,17351184,32505856],[]),([7,31,31744,1082401,2165730,4329604,8659208,17809936,33047056],[]),([7,31,31744,1082401,2165730,4329604,8659208,33047056,33521664],[]),([7,31,31744,1082401,2165730,4329604,8659208,33047056,33538576],[]),([7,31,31744,1082401,2165730,4329604,8691976,17318416,32505856],[]),([7,31,31744,1082401,2165730,4329604,9412872,17318416,32776456],[]),([7,31,31744,1082401,2165730,4329604,9412872,25977624,32505856],[]),([7,31,31744,1082401,2165730,4329604,17318416,17809936,32776456],[]),([7,31,31744,1082401,2165730,4329604,17318416,32776456,33521664],[]),([7,31,31744,1082401,2165730,4329604,17318416,32776456,33530120],[]),([7,31,31744,1082401,2165730,4330468,8659208,17809936,32505856],[]),([7,31,31744,1082401,2165730,4330468,9412872,17318416,32505856],[]),([7,31,31744,1082401,2165730,4362372,8659208,17318416,32505856],[]),([7,31,31744,1082401,2165730,5214340,8659208,17318416,32505856],[]),([7,31,31744,1082401,2165730,5214340,8659208,17318416,32776456],[]),([7,31,31744,1082401,2165730,5214340,8659208,17318416,33047056],[])]
def t54 : BT := .nd (blockTree b58) [7,31,31744,1082401,2164802,4330468,9412872,17318416,32776456] (blockTree b59)
def t55 : BT := .nd t53 [7,31,31744,1015808,1113121,2165730,4329604,17318416,32776456] t54
def b60 : List Row := [([7,31,31744,1082401,2165730,5214340,8659208,32505856,33047056],[]),([7,31,31744,1082401,2165730,5214340,8659208,33047056],[]),([7,31,31744,1082401,2165730,5214340,17318416,32505856,32776456],[]),([7,31,31744,1082401,2165730,5214340,17318416,32776456],[(198,0)]),([7,31,31744,1082401,2165730,8659208,13611404,17318416,32505856],[]),([7,31,31744,1082401,2165730,8659208,17318416,32505856,33525892],[]),([7,31,31744,1082401,2165730,8659208,17318416,32641156,33521664],[]),([7,31,31744,1082401,2165730,9412872,12988812,17318416,32505856],[]),([7,31,31744,1082401,2197570,4330468,8659208,17318416,32505856],[]),([7,31,31744,1082401,3112960,4330468,8659208,17318416,32505856],[]),([7,31,31744,1082401,3115074,4330468,8659208,17318416,32505856],[]),([7,31,31744,1082401,3115074,4330468,8659208,17318431,32505856],[]),([7,31,31744,1082401,3115074,4330468,8659208,25977624,32505856],[]),([7,31,31744,1082401,3248099,5214340,8659208,17318416,32505856],[]),([7,31,31744,1082431,2165730,5214340,8659208,17318416,32505856],[]),([7,31,31744,1083361,2097152,4329604,8659208,17318416,33521664],[(96,0)]),([7,31,31744,1083361,2097152,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2097152,4329604,9412872,17318416,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,9412872,33047056],[]),([7,31,31744,1083361,2164802,4329604,8659208,17318416,32538624],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17351184,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,17809936,33047056],[]),([7,31,31744,1083361,2164802,4329604,8659208,26207000,32505856],[(96,0)])]
def b61 : List Row := [([7,31,31744,1083361,2164802,4329604,8659208,33047056,33521664],[(96,0)]),([7,31,31744,1083361,2164802,4329604,8659208,33047056,33538576],[]),([7,31,31744,1083361,2164802,4329604,8691976,17318416,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,2164802,4329604,9412872,17318416,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,9412872,17318416,33047056],[]),([7,31,31744,1083361,2164802,4329604,9412872,17809936,32505856],[]),([7,31,31744,1083361,2164802,4329604,9412872,25977624,32505856],[(96,0)]),([7,31,31744,1083361,2164802,4329604,9412872,26207000,32505856],[]),([7,31,31744,1083361,2164802,4329604,9412872,32505856,33047056],[]),([7,31,31744,1083361,2164802,4329604,9412872,33047056],[]),([7,31,31744,1083361,2164802,4329604,17318416,17809936,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,17318416,32505856,33530120],[]),([7,31,31744,1083361,2164802,4329604,17318416,32776456,33521664],[(96,0)]),([7,31,31744,1083361,2164802,4329604,17318416,32776456,33530120],[(96,0)]),([7,31,31744,1083361,2164802,4329604,17809936,32505856,32776456],[(96,0)]),([7,31,31744,1083361,2164802,4329604,17809936,32776456],[(96,0),(97,0)]),([7,31,31744,1083361,2164802,4330468,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,4330468,9412872,17318416,32505856],[]),([7,31,31744,1083361,2164802,4357252,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,4357252,9412872,17318416,32505856],[]),([7,31,31744,1083361,2164802,5214340,8659208,17809936,32505856],[]),([7,31,31744,1083361,2164802,5214340,9412872,17318416,32505856],[]),([7,31,31744,1083361,2164802,8659208,12988812,17809936,32505856],[(96,0)])]
def t56 : BT := .nd (blockTree b60) [7,31,31744,1083361,2164802,4329604,8659208,32505856,33538576] (blockTree b61)
def b62 : List Row := [([7,31,31744,1083361,2164802,8659208,17809936,32505856,32641156],[(96,0)]),([7,31,31744,1083361,2164802,9412872,12988812,17318416,32505856],[(96,0)]),([7,31,31744,1083361,2164802,9412872,13611404,17318416,32505856],[]),([7,31,31744,1083361,2164802,9412872,17318416,32505856,32641156],[]),([7,31,31744,1083361,2164802,9412872,33047056],[(1024,279617),(1024,300101)]),([7,31,31744,1083361,2164802,17809936,32776456],[(1024,284737),(1024,300101)]),([7,31,31744,1083361,2164831,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,2164831,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,2165730,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,2165730,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,2194498,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,2194498,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,3112960,4329604,8659208,17318416,32505856],[]),([7,31,31744,1083361,3115074,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,3115074,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,3115074,5214340,8659208,17318416,32505856],[]),([7,31,31744,1083361,3247203,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,31744,1083361,3247203,4329604,9412872,17318416,32505856],[]),([7,31,31744,1083361,3247203,5214340,8659208,17318416,32505856],[]),([7,31,31744,1083361,3248099,4329604,8659208,17809936,32505856],[]),([7,31,31744,1083361,3248099,4329604,9412872,17318416,32505856],[]),([7,31,31744,3179553,4330468,8659208,17318416],[(1024,444907),(1024,67046)]),([7,31,31744,4330468,8659208,16236015,32539681],[(1024,99832),(1024,67046)]),([7,31,31744,4330468,8659208,17318416,32538624],[(1024,66039),(1024,98808)])]
def b63 : List Row := [([7,31,31744,4330468,8659208,17318431,32539681],[(1024,268792),(1024,67046),(1025,88761)]),([7,31,31744,4330468,8659208,17333776,32539681],[(1024,67046),(1024,72161),(1025,78130),(1025,450233)]),([7,31,31744,4330468,8659208,17383952],[(1024,66022),(1024,98803),(1024,71137),(1025,67255),(1025,437944)]),([7,31,31744,4330468,8659208,25977624,32539681],[(1024,301561),(1024,67046),(1025,99001)]),([7,31,31744,4330468,8724744,17318416],[(1024,66022),(1024,98801),(1024,71137),(1025,67255),(1025,437944)]),([7,31,31744,4330468,17318416,24895223,32539681],[(1024,515170),(1024,67046)]),([7,31,31744,4330468,17318416,25977624,32539681],[(1024,99832),(1024,67046),(1025,318137)]),([7,31,31744,4358116,8659208,17318416,32539681],[(128,0),(1024,67046),(1024,72161),(1025,449208)]),([7,31,31744,4396004,8659208,17318416],[(128,0),(1024,66022),(1024,98803),(1024,71137),(1025,67255),(1025,437944)]),([7,31,31744,8659208,17318416,29223963,32539681],[(96,0),(1024,496706),(1024,72161)]),([7,31,31748,1015808,1082401,2165730,8659208,17318416,32505856],[]),([7,31,31748,1015808,1083361,2164802,8659208,17318416,32505856],[]),([7,31,31775,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,31775,1015808,1082401,2165730,4329604,17318416,32776456],[]),([7,31,31775,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,31775,1015808,1083361,2164802,4329604,17318416,32776456],[]),([7,31,31775,1082401,2165730,5214340,8659208,17318416,32505856],[]),([7,31,31775,1082401,2165730,8659208,33047056],[(1024,444907),(1024,280642),(1025,263603)]),([7,31,31775,1082401,2165730,17318416,32776456],[(1024,444907),(1024,280642),(1025,426648)]),([7,31,31775,1082401,3115074,4330468,8659208,17318416,32505856],[]),([7,31,31775,1083361,2164802,4329604,8659208,17809936,32505856],[]),([7,31,31775,1083361,2164802,4329604,9412872,17318416,32505856],[]),([7,31,31775,4330468,8659208,17318416,32539681],[(1024,281062),(1024,99832),(1025,76471)]),([7,31,32736,1015808,1082401,2164802,4329604,8659208,32506368],[(96,0),(128,0)])]
def t57 : BT := .nd (blockTree b62) [7,31,31744,4330468,8659208,17318416,32539681] (blockTree b63)
def t58 : BT := .nd t56 [7,31,31744,1083361,2164802,8659208,17318416,32641156,33521664] t57
def t59 : BT := .nd t55 [7,31,31744,1082401,2165730,5214340,8659208,25977624,32505856] t58
def t60 : BT := .nd t52 [7,31,31744,1015808,1082401,2165730,4357252,17318416,32776456] t59
def t61 : BT := .nd t45 [7,31,992,1015808,1113121,2164802,4329604,8659208,32506368] t60
def t62 : BT := .nd t30 [6,31,1083361,3115074,9412872,33047056] t61
def b64 : List Row := [([7,31,32736,1015808,1082401,2164802,4330468,8659208,33047056],[]),([7,31,32736,1015808,1082401,2164802,4330468,17318416,32776456],[]),([7,31,32736,1015808,1082401,2165730,4329604,8659208,33047056],[]),([7,31,32736,1015808,1082401,2165730,4329604,17318416,32776456],[(96,0)]),([7,31,32736,1015808,1083361,2164802,4329604,8659208,33047056],[]),([7,31,32736,1015808,1083361,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,32736,1016320,1082401,2164802,4329604,8659208,32505856],[(96,0),(128,0)]),([7,31,32736,1082401,2164802,4330468,8659208,17809936,32505856],[]),([7,31,32736,1082401,2164802,4330468,9412872,17318416,32505856],[]),([7,31,32736,1082401,2164802,5214340,8659944],[(1024,286347),(1024,69896)]),([7,31,32736,1082401,2164802,8659944,32641156],[(1024,281067),(1024,69896),(1025,104883)]),([7,31,32736,1082401,2165730,4329604,8659208,17809936,32505856],[]),([7,31,32736,1082401,2165730,4329604,9412872,17318416,32505856],[(72,0)]),([7,31,32736,1082401,2165730,5214340,8659208,17318416,32505856],[(72,0)]),([7,31,32736,1082401,3115074,4330468,8659208,17318416,32505856],[(216,0)]),([7,31,32736,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,32736,1083361,2164802,4329604,9412872,17318416,32505856],[]),([7,31,32736,4330468,8659208,17318416,32539681],[(128,0),(1024,67063),(1024,83425)]),([7,31,32736,4357252,8659208,17318416,32539681],[(1024,281062),(1024,66863),(1025,80180)]),([7,31,32768,1082401,2165730,4357252,8659208,17318416,32505856],[]),([7,31,32768,1082401,2194498,4330468,8659208,17318416,32505856],[]),([7,31,32768,1083361,2164802,4357252,8659208,17318416,32505856],[]),([7,31,32768,1083361,2194498,4329604,8659208,17318416,32505856],[]),([7,31,32768,1113121,2164802,4330468,8659208,17318416,32505856],[]),([7,31,32768,1113121,2165730,4329604,8659208,17318416,32505856],[])]
def b65 : List Row := [([7,31,66528,4357252,8659208,17318416],[(1024,66027),(1024,98803),(1024,76257),(1025,67255),(1025,279224)]),([7,31,97280,4330468,8659208,17318416],[(1024,66022),(1024,98803),(1024,71137),(1025,67255),(1025,443064)]),([7,31,507375,1015808,1082401,2165730,8659208],[(1024,69927),(1024,309314)]),([7,31,507375,1015808,1083361,2164802,8659208],[(1024,69926),(1024,309313)]),([7,31,913275,1015808,1082401,2164802,8659944],[(1024,269381),(1024,502035)]),([7,31,1015808,1082401,1083361,2164802,4357252,8659208,33047056],[]),([7,31,1015808,1082401,1083361,2194498,4329604,17318416,32776456],[]),([7,31,1015808,1082401,1113121,2165730,4329604,8659208,33047056],[]),([7,31,1015808,1082401,1113121,2165730,4329604,17318416,32776456],[]),([7,31,1015808,1082401,2098144,4329604,8659208,17333776,32505856],[]),([7,31,1015808,1082401,2098144,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2128896,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2164802,2165730,4357252,8659208,33047056],[]),([7,31,1015808,1082401,2164802,4330468,8659208,17326608,32505856],[]),([7,31,1015808,1082401,2164802,4330468,8659208,17333776,33047056],[]),([7,31,1015808,1082401,2164802,4338660,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1082401,2164802,8659720,32641156],[(1024,660760),(1024,496915)]),([7,31,1015808,1082401,2164802,8659944,32641156],[(1024,665864),(1024,502035)]),([7,31,1015808,1082401,2164802,8659944,33525892],[(1024,665864),(1024,509190),(1025,431608)]),([7,31,1015808,1082401,2164802,12989420,32641156],[(1024,665864),(1024,502035)]),([7,31,1015808,1082401,2164802,24894487,32641156],[(1024,665864),(1024,502035)]),([7,31,1015808,1082401,2164831,8659944,32641156],[(1024,511238),(1024,66824),(1025,103847),(1025,104883)]),([7,31,1015808,1082401,2165314,8659208,33047056],[(128,0),(1024,301125),(1024,309314)]),([7,31,1015808,1082401,2165730,2194498,4329604,8659208,33047056],[])]
def t63 : BT := .nd (blockTree b64) [7,31,66528,4329604,8659208,17333776] (blockTree b65)
def b66 : List Row := [([7,31,1015808,1082401,2165730,2194498,8659208,17318416,32641156],[]),([7,31,1015808,1082401,2165730,2195426,4329604,8659208,33047056],[]),([7,31,1015808,1082401,2165730,2195426,4329604,17318416,32776456],[(244,0)]),([7,31,1015808,1082401,2165730,4329604,4357252,8659208,33047056],[]),([7,31,1015808,1082401,2165730,4329604,8659208,17326608,32505856],[]),([7,31,1015808,1082401,2165730,4329604,8659208,17333776,33047056],[]),([7,31,1015808,1082401,2165730,4330468,8659208,17333776,32505856],[]),([7,31,1015808,1082401,2165730,4337796,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2165730,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2165730,4357252,8659208,17318416,32776456],[]),([7,31,1015808,1082401,2165730,4357252,8659208,17318416,33047056],[]),([7,31,1015808,1082401,2165730,4357252,8659208,25977624,32505856],[]),([7,31,1015808,1082401,2165730,4357252,8659208,32505856,33047056],[]),([7,31,1015808,1082401,2165730,4357252,8659208,33047056],[(1024,296056)]),([7,31,1015808,1082401,2165730,4358116,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2165730,8659208,33047056],[(1024,301125),(1024,309314)]),([7,31,1015808,1082401,2165730,8659208,33538576],[(1024,301125),(1024,309314),(1025,66036),(1025,274097)]),([7,31,1015808,1082401,2165730,8659231,33047056],[(1024,301125),(1024,309314)]),([7,31,1015808,1082401,2165730,9412872,33047056],[(1024,309314),(1024,301125),(1025,274097)]),([7,31,1015808,1082401,2165730,24895223,33047056],[(1024,301125),(1024,309314)]),([7,31,1015808,1082401,2165730,25977624,33047056],[(1024,309314),(1024,502195)]),([7,31,1015808,1082401,2165730,32776456,33047056],[(1024,301125),(1024,309314)]),([7,31,1015808,1082401,2165730,33047056,33317656],[(1024,309314),(1024,502195)]),([7,31,1015808,1082401,2172994,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2173922,4329604,8659208,17318416,32505856],[])]
def b67 : List Row := [([7,31,1015808,1082401,2194498,4330468,8659208,17318416,32776456],[]),([7,31,1015808,1082401,2194498,4330468,8659208,17318431,32505856],[]),([7,31,1015808,1082401,2194498,4330468,8659208,25977624,32505856],[]),([7,31,1015808,1082401,2194527,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1082401,2195426,4330468,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1082401,3115074,8659944,32641156],[(1024,665864),(1024,508166),(1025,83641),(1025,431604)]),([7,31,1015808,1082401,3116002,8659208,33047056],[(1024,309314),(1024,301125),(1025,66034)]),([7,31,1015808,1082401,3247203,8659944,32641156],[(1024,700679),(1024,69896),(1025,436723)]),([7,31,1015808,1082401,3248099,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1082401,3248099,8659208,33047056],[(1024,309314),(1024,301125),(1025,70283)]),([7,31,1015808,1082401,3275875,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1082401,6494406,12989420,32505856],[(1024,277175),(1024,502035)]),([7,31,1015808,1082401,8659208,31388701,33047056],[(1024,66863),(1024,301125)]),([7,31,1015808,1082401,8659944,31389629,32641156],[(1024,268973),(1024,69896)]),([7,31,1015808,1082401,12989420,25977624,32505856],[(1024,277175),(1024,268985)]),([7,31,1015808,1082431,2164802,8659944,32641156],[(1024,511238),(1024,65800),(1025,103847)]),([7,31,1015808,1082431,2165730,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1082431,2194498,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1082913,2164802,8659208,33047056],[(128,0),(1024,300101),(1024,309313)]),([7,31,1015808,1083361,1113121,2164802,4329604,8659208,33047056],[]),([7,31,1015808,1083361,1113121,2164802,4329604,17318416,32776456],[(128,0)]),([7,31,1015808,1083361,1113121,2164802,8659208,17318416,32641156],[(128,0)]),([7,31,1015808,1083361,1114081,2164802,4329604,8659208,33047056],[]),([7,31,1015808,1083361,1114081,2164802,4329604,17318416,32776456],[(128,0),(236,0)])]
def t64 : BT := .nd (blockTree b66) [7,31,1015808,1082401,2194498,4330468,8659208,17318416,32505856] (blockTree b67)
def t65 : BT := .nd t63 [7,31,1015808,1082401,2165730,2194498,4329604,17318416,32776456] t64
def b68 : List Row := [([7,31,1015808,1083361,2128896,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2164802,2194498,4329604,8659208,33047056],[(96,0)]),([7,31,1015808,1083361,2164802,2194498,4329604,17318416,32776456],[(96,0)]),([7,31,1015808,1083361,2164802,4329604,4357252,8659208,33047056],[]),([7,31,1015808,1083361,2164802,4329604,8659208,17326608,32505856],[(96,0)]),([7,31,1015808,1083361,2164802,4329604,8659208,17333776,33047056],[]),([7,31,1015808,1083361,2164802,4330468,8659208,17333776,32505856],[]),([7,31,1015808,1083361,2164802,4337796,8659208,17318416,32505856],[(96,0)]),([7,31,1015808,1083361,2164802,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2164802,4357252,8659208,17318416,32776456],[]),([7,31,1015808,1083361,2164802,4357252,8659208,17318416,33047056],[]),([7,31,1015808,1083361,2164802,4357252,8659208,17809936,32505856],[]),([7,31,1015808,1083361,2164802,4357252,8659208,25977624,32505856],[]),([7,31,1015808,1083361,2164802,4357252,8659208,32505856,33047056],[]),([7,31,1015808,1083361,2164802,4357252,8659208,33047056],[(1024,295032)]),([7,31,1015808,1083361,2164802,4358116,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2164802,8659208,33047056],[(1024,309313),(1024,300101)]),([7,31,1015808,1083361,2164802,8659208,33538576],[(1024,300101),(1024,309313),(1025,66036)]),([7,31,1015808,1083361,2164802,8659231,33047056],[(1024,309313),(1024,300101)]),([7,31,1015808,1083361,2164802,9412872,33047056],[(1024,300101),(1024,309313)]),([7,31,1015808,1083361,2164802,24895223,33047056],[(1024,300101),(1024,309313)]),([7,31,1015808,1083361,2164802,25977624,33047056],[(1024,309313),(1024,497075)]),([7,31,1015808,1083361,2164802,32776456,33047056],[(1024,309313),(1024,300101)]),([7,31,1015808,1083361,2164802,33047056,33317656],[(1024,309313),(1024,497075)]),([7,31,1015808,1083361,2164831,4357252,8659208,17318416,32505856],[])]
def b69 : List Row := [([7,31,1015808,1083361,2165730,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2165730,8659208,33047056],[(1024,508993),(1024,300101),(1025,262562)]),([7,31,1015808,1083361,2172994,4329604,8659208,17318416,32505856],[(96,0)]),([7,31,1015808,1083361,2194498,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2194498,4329604,8659208,17318416,32776456],[]),([7,31,1015808,1083361,2194498,4329604,8659208,17809936,32505856],[]),([7,31,1015808,1083361,2194498,4329604,8659208,25977624,32505856],[]),([7,31,1015808,1083361,2194498,4329604,8659208,32505856,33047056],[]),([7,31,1015808,1083361,2194498,4329604,17318416,32505856,32776456],[]),([7,31,1015808,1083361,2194498,4329604,17318416,32776456],[(190,0)]),([7,31,1015808,1083361,2194498,4330468,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1083361,2194498,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2194498,5214340,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2194498,8659208,12988812,17318416,32505856],[]),([7,31,1015808,1083361,2194498,8659208,17318416,32505856,32641156],[]),([7,31,1015808,1083361,2194498,17318416,32776456],[(1024,284737),(1024,300101)]),([7,31,1015808,1083361,2194527,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1083361,2195426,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1083361,3115074,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,3115074,8659208,33047056],[(1024,300101),(1024,309313),(1025,66034)]),([7,31,1015808,1083361,3247203,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,3247203,8659208,33047056],[(128,0),(1024,702530),(1024,302149)]),([7,31,1015808,1083361,3248099,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1083361,3248099,8659208,33047056],[(1024,702530),(1024,300101),(1025,70283)])]
def t66 : BT := .nd (blockTree b68) [7,31,1015808,1083361,2165730,4329604,8659208,17333776,32505856] (blockTree b69)
def b70 : List Row := [([7,31,1015808,1083361,3276771,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1083361,8659208,31389629,33047056],[(1024,67247),(1024,300101)]),([7,31,1015808,1083361,12988812,25977624,32505856],[(1024,270009),(1024,67255)]),([7,31,1015808,1083361,19483218,25977624,32505856],[(1024,267961),(1024,309313)]),([7,31,1015808,1090593,2164802,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1090593,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1091553,2164802,4329604,8659208,17318416,32505856],[(96,0)]),([7,31,1015808,1113121,2097152,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,2098144,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1113121,2164802,2165730,4329604,17318416,32776456],[]),([7,31,1015808,1113121,2164802,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,2164802,4330468,8659208,17318416,32776456],[]),([7,31,1015808,1113121,2164802,4330468,8659208,17318431,32505856],[]),([7,31,1015808,1113121,2164802,4330468,8659208,25977624,32505856],[]),([7,31,1015808,1113121,2164831,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1113121,2165730,4329604,8659208,17318416,32776456],[]),([7,31,1015808,1113121,2165730,4329604,8659208,25977624,32505856],[]),([7,31,1015808,1113121,2165730,4329604,8659208,32505856,33047056],[]),([7,31,1015808,1113121,2165730,4329604,17318416,32505856,32776456],[]),([7,31,1015808,1113121,2165730,4329604,17318416,32776456],[(198,0)]),([7,31,1015808,1113121,2165730,4330468,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1113121,2165730,4357252,8659208,17318416,32505856],[]),([7,31,1015808,1113121,2165730,5214340,8659208,17318416,32505856],[])]
def b71 : List Row := [([7,31,1015808,1113121,2165730,8659208,17318416,32505856,32641156],[]),([7,31,1015808,1113121,2165730,17318416,32776456],[(1024,284738),(1024,301125)]),([7,31,1015808,1113121,2194498,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,3115074,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,3247203,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113121,3248099,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1113121,3275875,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113151,2164802,4330468,8659208,17318416,32505856],[]),([7,31,1015808,1113151,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1015808,1114081,2164802,4330468,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1114081,2165730,4329604,8659208,17318416,32505856],[(216,0)]),([7,31,1015808,1114081,3248099,4329604,8659208,17318416,32505856],[]),([7,31,1015808,2164802,3247203,8659944,32641156],[(1024,511238),(1024,69896),(1025,437944)]),([7,31,1015808,2164802,3248099,8659208,33047056],[(1024,309313),(1024,300101),(1025,70316)]),([7,31,1015808,2164802,5412005,12989420,32505856],[(1024,276978),(1024,502035)]),([7,31,1015808,2164802,8659208,32471070,33047056],[(1024,65839),(1024,300101)]),([7,31,1015808,2164802,8659944,32472030,32641156],[(1024,267764),(1024,69896)]),([7,31,1015808,2164802,12989420,25977624,32505856],[(1024,276978),(1024,267764)]),([7,31,1015808,2165730,3247203,8659208,33047056],[(128,0),(1024,508993),(1024,302149)]),([7,31,1015808,2165730,3248099,8659208,33047056],[(1024,508993),(1024,300101),(1025,70316)]),([7,31,1015808,2165730,8659208,32472030,33047056],[(1024,66034),(1024,301125)]),([7,31,1015808,2165730,12988812,25977624,32505856],[(1024,269812),(1024,66034)]),([7,31,1015808,2165730,18400817,25977624,32505856],[(1024,268788),(1024,309314)]),([7,31,1015808,3247203,5412005,8659944,32505856],[(1024,508168),(1024,502035)])]
def t67 : BT := .nd (blockTree b70) [7,31,1015808,1113121,2165730,8659208,12988812,17318416,32505856] (blockTree b71)
def t68 : BT := .nd t66 [7,31,1015808,1083361,3275875,4329604,8659208,17318416,32505856] t67
def t69 : BT := .nd t65 [7,31,1015808,1083361,2097152,4357252,8659208,17318416,32505856] t68
def b72 : List Row := [([7,31,1015839,1082401,2164802,8659944,32641156],[(1024,502035),(1024,69896),(1025,104883)]),([7,31,1016800,1082401,2165730,8659208,33047056],[(1024,502195),(1024,280642),(1025,263603)]),([7,31,1048575,1082401,2164802,5214340,8659944],[(1024,286347),(1024,69896)]),([7,31,1048575,1082401,3115074,4329604,8659944],[(1024,286347),(1024,69896)]),([7,31,1048575,1083361,2164802,8659208,17809936],[(1024,450182),(1024,300101)]),([7,31,1082401,1083361,2164802,4357252,8659208,17809936,32505856],[]),([7,31,1082401,1083361,2194498,4329604,8659208,17809936,32505856],[]),([7,31,1082401,1083361,2194498,5214340,8659208,17318416,32505856],[(56,0)]),([7,31,1082401,1083361,3115074,4357252,8659208,17318416,32505856],[]),([7,31,1082401,1113121,2165730,5214340,8659208,17318416,32505856],[]),([7,31,1082401,1113121,3115074,4330468,8659208,17318416,32505856],[]),([7,31,1082401,2164802,3115074,8659944,32641156],[(1024,502035),(1024,69896),(1025,445112)]),([7,31,1082401,2164802,4330468,8659208,17333776,17809936,32505856],[]),([7,31,1082401,2164802,5214340,8659720,32505856],[(1024,496915),(1024,660760)]),([7,31,1082401,2164802,5214340,8659944,32505856],[(1024,502024),(1024,504070)]),([7,31,1082401,2164802,5214340,8659944,32505887],[(1024,665880),(1024,69896)]),([7,31,1082401,2164802,5214340,8659944,32641156],[(1024,665880),(1024,502035)]),([7,31,1082401,2164802,5214340,8659944,33521664],[(1024,665880),(1024,69896)]),([7,31,1082401,2164802,5214340,8659944,33525892],[(1024,665880),(1024,504070),(1025,431608)]),([7,31,1082401,2164802,5214340,12989420,32505856],[(1024,502024),(1024,511238)]),([7,31,1082401,2164802,5214340,24894487,32505856],[(1024,502024),(1024,504070)]),([7,31,1082401,2164802,7313606,8659944,32505856],[(1024,502024),(1024,504070),(1025,66661)]),([7,31,1082401,2164802,8659944,28340091,32505856],[(1024,269381),(1024,504070)]),([7,31,1082401,2164802,8659944,32505856,33525892],[(1024,502024),(1024,504070),(1025,431769)]),([7,31,1082401,2164802,8659944,32538623,32641156],[(1024,281067),(1024,69896)])]
def b73 : List Row := [([7,31,1082401,2164802,8659944,32641156,33525892],[(1024,502035),(1024,511238),(1025,431769)]),([7,31,1082401,2164831,5214340,8659944,32505856],[(1024,712967),(1024,66824),(1025,103847)]),([7,31,1082401,2165730,2194498,5214340,8659208,17318416,32505856],[]),([7,31,1082401,2165730,2195426,5214340,8659208,17318416,32505856],[(236,0)]),([7,31,1082401,2165730,3115074,4357252,8659208,17318416,32505856],[]),([7,31,1082401,2165730,3115074,8659208,33047056],[(128,0),(1024,502195),(1024,302149)]),([7,31,1082401,2165730,3116002,8659208,33047056],[(1024,502195),(1024,281062),(1025,70321)]),([7,31,1082401,2165730,4329604,8659208,17333776,17809936,32505856],[]),([7,31,1082401,2165730,4357252,5214340,8659208,17318416,32505856],[]),([7,31,1082401,2165730,4357252,8659208,9412872,17318416,32505856],[]),([7,31,1082401,2165730,4357252,8659208,17318416,17809936,32505856],[]),([7,31,1082401,2165730,4357252,8659208,17318416,32505856,33521664],[]),([7,31,1082401,2165730,4357252,8659208,33047056],[(1024,281062),(1024,78305)]),([7,31,1082401,2165730,5214340,8659208,17318416,17333776,32505856],[]),([7,31,1082401,2165730,5214340,8659208,33047056],[(1024,502195),(1024,301496)]),([7,31,1082401,2165730,7313606,8659208,32505856],[(1024,502055),(1024,309314),(1025,66661)]),([7,31,1082401,2165730,8659208,17809936,33047056],[(1024,502195),(1024,309314)]),([7,31,1082401,2165730,8659208,32538623,33047056],[(1024,444907),(1024,301125)]),([7,31,1082401,2165730,8659208,33047056,33521664],[(1024,502195),(1024,301125)]),([7,31,1082401,2165730,8659208,33047056,33538576],[(1024,502195),(1024,309314),(1025,66201)]),([7,31,1082401,2165730,17318416,32776456,33521664],[(1024,502195),(1024,301125)]),([7,31,1082401,2165730,17809936,25977624,32505856],[(1024,501861),(1024,309314)]),([7,31,1082401,2194498,3115074,4330468,8659208,17318416,32505856],[]),([7,31,1082401,2194498,4330468,5214340,8659208,17318416,32505856],[])]
def t70 : BT := .nd (blockTree b72) [7,31,1082401,2164802,8659944,32641156,33521664] (blockTree b73)
def b74 : List Row := [([7,31,1082401,2194498,4330468,8659208,17318416,17809936,32505856],[(168,0)]),([7,31,1082401,2194498,4330468,8659208,17318416,32505856,33521664],[]),([7,31,1082401,3115074,4329604,8659720,32505856],[(1024,496915),(1024,660760)]),([7,31,1082401,3115074,4329604,8659944,32505856],[(1024,502023),(1024,69896)]),([7,31,1082401,3115074,4329604,8659944,32505887],[(1024,665880),(1024,69896)]),([7,31,1082401,3115074,4329604,8659944,32641156],[(1024,665880),(1024,502023)]),([7,31,1082401,3115074,4329604,12989420,32505856],[(1024,502023),(1024,503046)]),([7,31,1082401,3115074,4329604,24894487,32505856],[(1024,502023),(1024,69896)]),([7,31,1082401,3115074,4330468,4357252,8659208,17318416,32505856],[]),([7,31,1082401,3115074,4330468,4358116,8659208,17318416,32505856],[(244,0)]),([7,31,1082401,3115074,4330468,8659208,17318416,17333776,32505856],[(168,0)]),([7,31,1082401,3115074,4330468,8659208,32641156],[(1024,309938),(1024,502055)]),([7,31,1082401,3115074,5214340,8659944,32505856],[(1024,665880),(1024,69896)]),([7,31,1082401,3115074,5412005,8659944,32505856],[(1024,69896),(1024,502023),(1025,65637)]),([7,31,1082401,3115074,6494406,8659944,32505856],[(1024,710722),(1024,69896)]),([7,31,1082401,3115074,7313606,8659944,32505856],[(1024,69896),(1024,503046),(1025,66661)]),([7,31,1082401,3115074,8659720,17318416,32505856],[(1024,496706),(1024,497729)]),([7,31,1082401,3115074,8659944,25977624,32505856],[(1024,269381),(1024,501826)]),([7,31,1082401,3115074,8659944,29224827,32505856],[(1024,269381),(1024,502023)]),([7,31,1082401,3115074,8659944,32505856,32641156],[(1024,69896),(1024,502023),(1025,431769)]),([7,31,1082401,3115103,4329604,8659944,32505856],[(1024,502023),(1024,66824)]),([7,31,1082401,3247203,5214340,8659944,32505856],[(1024,712967),(1024,69896),(1025,436723)]),([7,31,1082401,4329604,7313606,8659944,32505856],[(1024,502023),(1024,67255)]),([7,31,1082401,4329604,8659944,30439357,32505856],[(1024,268779),(1024,69896)])]
def b75 : List Row := [([7,31,1082401,4330468,8659208,17333776,32641156],[(1024,281062),(1024,73185),(1025,66231)]),([7,31,1082401,5214340,6494406,8659944,32505856],[(1024,665880),(1024,66835)]),([7,31,1082401,5214340,7313606,8659944,32505856],[(1024,712967),(1024,67255),(1025,431604)]),([7,31,1082401,5214340,8659944,25977624,32505856],[(1024,268985),(1024,66835)]),([7,31,1082401,5214340,8659944,31389629,32505856],[(1024,268985),(1024,69896)]),([7,31,1082431,2164802,5214340,8659944,32505856],[(1024,504070),(1024,65800),(1025,103847)]),([7,31,1082431,3115074,4329604,8659944,32505856],[(1024,503046),(1024,65800)]),([7,31,1082913,2164802,8659208,17809936,32505856],[(96,0),(1024,309313),(1024,300101)]),([7,31,1082913,3115074,8659208,17318416,32505856],[(96,0),(1024,309313),(1024,300101)]),([7,31,1083361,1113121,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,1083361,1113121,2164802,4329604,9412872,17318416,32505856],[]),([7,31,1083361,1113121,2164802,5214340,8659208,17318416,32505856],[]),([7,31,1083361,1113121,3115074,4329604,8659208,17318416,32505856],[]),([7,31,1083361,1114081,2164802,4329604,8659208,17809936,32505856],[(96,0)]),([7,31,1083361,1114081,2164802,4329604,9412872,17318416,32505856],[(228,0)]),([7,31,1083361,2164802,2194498,4329604,8659208,17809936,32505856],[(72,0)]),([7,31,1083361,2164802,3115074,8659208,33047056],[(1024,309313),(1024,300101),(1025,70321),(1025,268779)]),([7,31,1083361,2164802,4329604,4357252,8659208,17809936,32505856],[(72,0)]),([7,31,1083361,2164802,4329604,8659208,17333776,17809936,32505856],[(72,0)]),([7,31,1083361,2164802,4357252,8659208,9412872,17318416,32505856],[]),([7,31,1083361,2164802,4357252,8659208,17318416,17809936,32505856],[]),([7,31,1083361,2164802,4357252,8659208,17318416,32505856,33521664],[]),([7,31,1083361,2164802,4357252,8659208,17809936,32505856],[(1024,295027)]),([7,31,1083361,2164802,8659208,15744495,32505856],[(1024,69926),(1024,309313)])]
def t71 : BT := .nd (blockTree b74) [7,31,1082401,4330468,7313606,8659208,32505856] (blockTree b75)
def t72 : BT := .nd t70 [7,31,1082401,2194498,4330468,8659208,9412872,17318416,32505856] t71
def b76 : List Row := [([7,31,1083361,2164802,8659208,17809936,33047056],[(1024,309313),(1024,497075)]),([7,31,1083361,2164802,8659208,17809936,33521664],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,8659208,17809936,33538576],[(1024,660920),(1024,309313),(1025,66041)]),([7,31,1083361,2164802,8659208,19909202,32505856],[(72,0),(1024,309313),(1024,300101),(1025,268779)]),([7,31,1083361,2164802,8659208,32505856,33538576],[(1024,300101),(1024,309313),(1025,66201)]),([7,31,1083361,2164802,8659208,32538623,33047056],[(1024,444902),(1024,300101)]),([7,31,1083361,2164802,8659208,33047056,33521664],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,8659208,33047056,33538576],[(1024,497075),(1024,309313),(1025,66201)]),([7,31,1083361,2164802,8659231,17809936,32505856],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,9412872,17318416,33521664],[(1024,309313),(1024,267953)]),([7,31,1083361,2164802,9412872,17809936,32505856],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,17318416,32776456,33521664],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,17809936,24895223,32505856],[(1024,309313),(1024,300101)]),([7,31,1083361,2164802,17809936,25977624,32505856],[(1024,309313),(1024,496741)]),([7,31,1083361,2164802,17809936,26207000,32505856],[(1024,309313),(1024,660920)]),([7,31,1083361,2164802,17809936,32505856,32776456],[(1024,309313),(1024,300101)]),([7,31,1083361,2165730,8659208,17809936,32505856],[(1024,710722),(1024,300101),(1025,262562)]),([7,31,1083361,2194498,4329604,8659208,9412872,17318416,32505856],[]),([7,31,1083361,2194498,4329604,8659208,17318416,17809936,32505856],[(168,0)]),([7,31,1083361,2194498,4329604,8659208,17318416,32505856,33521664],[]),([7,31,1083361,2194498,4329604,8659208,17809936,32505856],[(1024,295027),(1024,300101)]),([7,31,1083361,2194498,8659208,17809936,32505856],[(1024,312385),(1024,300101)]),([7,31,1083361,3115074,8659208,17809936,32505856],[(1024,309313),(1024,300101)]),([7,31,1083361,3115074,9412872,17318416,32505856],[(1024,309313),(1024,300101)]),([7,31,1083361,3247203,8659208,17809936,32505856],[(96,0),(1024,710722),(1024,302149)])]
def b77 : List Row := [([7,31,1083361,4357252,8659208,17809936,32505856],[(1024,67255),(1024,100024)]),([7,31,1083361,4358116,8659208,17318416,32505856],[(1024,67046),(1024,77281),(1025,285368)]),([7,31,1083361,8659208,12988812,17809936,32505856],[(72,0),(1024,67255),(1024,300467)]),([7,31,1083361,8659208,17809936,19483218,32505856],[(1024,309313),(1024,301491)]),([7,31,1083361,8659208,17809936,19909202,32505856],[(1024,309313),(1024,301753),(1025,66036)]),([7,31,1083361,8659208,17809936,31389629,32505856],[(1024,67255),(1024,300101)]),([7,31,1113121,2164802,4330468,8659208,9412872,17318416,32505856],[]),([7,31,1113121,2164802,4330468,8659208,17318416,32505856,33521664],[]),([7,31,1113121,2165730,4329604,8659208,9412872,17318416,32505856],[]),([7,31,1113121,2165730,4329604,8659208,17318416,32505856,33521664],[]),([7,31,1113121,4330468,8659208,17333776,32505856],[(1024,67046),(1024,72161),(1025,450233)]),([7,31,1113121,4358116,8659208,17318416,32505856],[(128,0),(1024,67046),(1024,72161),(1025,449208)]),([7,31,2164802,3247203,5214340,8659944,32505856],[(1024,502024),(1024,504070),(1025,82420),(1025,437944)]),([7,31,2164802,3248099,8659208,17809936,32505856],[(1024,309313),(1024,300101)]),([7,31,2164802,5214340,8659944,32472030,32505856],[(1024,267757),(1024,69896)]),([7,31,2164802,8659208,17809936,32471070,32505856],[(1024,65839),(1024,300101)]),([7,31,2165730,3247203,5214340,8659208,32505856],[(72,0),(1024,309745),(1024,69928),(1025,437944)]),([7,31,3115074,4329604,5412005,8659944,32505856],[(1024,503046),(1024,66034)]),([7,31,3115074,4329604,8659944,32472030,32505856],[(1024,267756),(1024,69896)]),([7,31,3115074,4330468,5412005,8659208,32505856],[(1024,503078),(1024,66034)]),([7,31,4329604,4330468,8659208,17333776,32539681],[(1024,281062),(1024,73185),(1025,66231)]),([7,31,4329604,8659208,17333776,32539681,33553439],[(1024,496915),(1024,67063)]),([7,31,4330468,4357252,8659208,17318416,32539681],[(1024,99832),(1024,73185)]),([7,31,4330468,4358116,8659208,17318416,32539681],[(1024,444907),(1024,72161),(1025,66231)])]
def t73 : BT := .nd (blockTree b76) [7,31,1083361,3248099,8659208,17809936,32505856] (blockTree b77)
def b78 : List Row := [([7,31,4330468,8659208,17318416,32539681,33521664],[(1024,309751),(1024,99832)]),([7,31,4330468,8659208,17318416,32539681,33522687],[(1024,67046),(1024,72161)]),([7,31,4357252,4358116,8659208,17318416,32539681],[(1024,281062),(1024,73185),(1025,66231)]),([7,31,4357252,8659208,17318416,32539681,33521664],[(1024,301561),(1024,66863)]),([7,31,4357252,8659208,17318416,32539681,33553439],[(1024,496915),(1024,67051)]),([7,516,1015808,1082401,2164802,8659208,32505856],[(1024,491635),(1024,655480)]),([7,543,31744,1015808,1082401,2164802,4330468,8659208,32505856],[]),([7,543,32736,1015808,1082401,2164802,4329604,8659208,32505856],[]),([7,1023,31775,4329604,8659208,17318416,32539681],[(1024,78310),(1024,67063)]),([7,1023,1082431,4329604,8659208,17333776,32505856],[(1024,72997),(1024,66231),(1025,71351)]),([7,8192,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[(128,0)]),([7,8192,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[]),([7,8223,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[]),([7,8223,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[]),([7,8223,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[(96,0)]),([7,31744,31775,4330468,8659208,17318416,32539681],[(1024,67046),(1024,72161),(1025,78130),(1025,437944)]),([7,31744,32768,1082401,2164802,4330468,8659208,17318431,32505856],[]),([7,31744,32768,1082431,2165730,4329604,8659208,17318416,32505856],[]),([7,31744,32768,4330468,8659208,17318431,32505856],[(1024,98968),(1024,66199)]),([7,31744,65536,4330468,8659208,17318431],[(80,0),(1024,66022),(1024,98803),(1024,71137),(1025,122553),(1025,285368),(1025,318137)]),([7,31744,65567,4330468,8659208,17318416],[(1024,66022),(1024,98803),(1024,71137),(1025,82615),(1025,437944)]),([7,31744,1015808,1082401,1082431,2165730,4329604,8659208,33047056],[]),([7,31744,1015808,1082401,1082431,2165730,4329604,17318416,32776456],[]),([7,31744,1015808,1082401,2097152,4330468,8659208,17318431,32505856],[])]
def b79 : List Row := [([7,31744,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,2164802,4330468,8659208,17318431,32641156],[]),([7,31744,1015808,1082401,2164802,4330468,8659208,17318431,32776456],[]),([7,31744,1015808,1082401,2164831,2165730,4329604,8659208,33047056],[]),([7,31744,1015808,1082401,2164831,2165730,4329604,17318416,32776456],[]),([7,31744,1015808,1082401,2164831,4330468,8659208,17318416,32641156],[]),([7,31744,1015808,1082401,2164831,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,2194498,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,3115074,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,3247203,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,4329631,8659208,17318896,32573506],[]),([7,31744,1015808,1082431,1083361,2164802,4329604,8659208,33047056],[]),([7,31744,1015808,1082431,1083361,2164802,4329604,17318416,32776456],[(144,0),(176,0)]),([7,31744,1015808,1082431,2098144,4329604,8659208,17318416,32505856],[]),([7,31744,1015808,1082431,2164802,2165730,4329604,17318416,32776456],[]),([7,31744,1015808,1082431,2164802,2165730,8659208,17318416,32641156],[]),([7,31744,1015808,1082431,2164802,4330468,8659208,17318416,32641156],[]),([7,31744,1015808,1082431,2164802,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,1082431,2164831,4330468,8659208,17318416,32505856],[]),([7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[]),([7,31744,1015808,1082431,2165730,4329604,8659208,17318416,32776456],[]),([7,31744,1015808,1082431,2165730,4329604,8659208,25977624,32505856],[]),([7,31744,1015808,1082431,2165730,4329604,8659208,32505856,33047056],[]),([7,31744,1015808,1082431,2165730,4329604,17318416,32505856,32776456],[])]
def t74 : BT := .nd (blockTree b78) [7,31744,1015808,1082401,2097183,4330468,8659208,17318416,32505856] (blockTree b79)
def t75 : BT := .nd t73 [7,31,4330468,8659208,17318416,17333776,32539681] t74
def t76 : BT := .nd t72 [7,31,1083361,2164802,8659208,17809936,32505856] t75
def t77 : BT := .nd t69 [7,31,1015808,3247203,6494406,8659944,32505856] t76
def b80 : List Row := [([7,31744,1015808,1082431,2165730,5214340,8659208,17318416,32505856],[]),([7,31744,1015808,1082431,2165730,8659208,12988812,17318416,32505856],[]),([7,31744,1015808,1082431,2165730,8659208,17318416,32505856,32641156],[]),([7,31744,1015808,1082431,3248099,4329604,8659208,17318416,32505856],[]),([7,31744,1015808,1113121,2164802,4330468,8659208,17318431,32505856],[]),([7,31744,1015808,2164802,4329631,8659208,17318896,32539681],[(1024,507969)]),([7,31744,1015808,4330468,8659208,17318431,32539681],[(1024,67206),(1024,72321)]),([7,31744,1015808,4330468,8659208,17318431,32573506],[(1024,66034),(1024,71156),(1025,122553)]),([7,31744,1048575,1082401,4330468,8659208,17318431],[(1024,67046),(1024,72161)]),([7,31744,1082401,1082431,2165730,5214340,8659208,17318416,32505856],[]),([7,31744,1082401,2097152,4330468,8659208,17318431],[(1024,444907),(1024,67046)]),([7,31744,1082401,2164802,3115074,4330468,8659208,17318431,32505856],[]),([7,31744,1082401,2164802,4330468,5214340,8659208,17318431,32505856],[]),([7,31744,1082401,2164802,4330468,8659208,9412872,17318431,32505856],[]),([7,31744,1082401,2164802,4330468,8659208,17318431,32505856,33521664],[]),([7,31744,1082401,2164831,4330468,5214340,8659208,17318416,32505856],[]),([7,31744,1082401,3115074,4329604,4330468,8659208,17318431,32505856],[]),([7,31744,1082401,3115074,4329631,17318896,32505856],[(1024,704599),(1024,507969)]),([7,31744,1082401,3115074,4330468,8659208,17318431,32505856],[(169,0),(1024,70278),(1024,66199),(1024,491635)]),([7,31744,1082401,4330468,8659208,16236000,32505856],[(1024,491591),(1024,67046)]),([7,31744,1082401,4330468,8659208,17318431,32505856],[(1024,100024),(1024,67046)]),([7,31744,1082401,4330468,8659208,17318431,32539681],[(1024,100024),(1024,67046)]),([7,31744,1082401,4330468,8659208,17333791,32505856],[(1024,67046),(1024,72161),(1025,450233)]),([7,31744,1082401,4330468,17318431,24895223,32505856],[(1024,711778),(1024,67046)]),([7,31744,1082431,1083361,2164802,4329604,8659208,17809936,32505856],[(104,0),(304,0)])]
def b81 : List Row := [([7,31744,1082431,1083361,3115074,4329604,8659208,17318416,32505856],[]),([7,31744,1082431,2164802,2165730,5214340,8659208,17318416,32505856],[]),([7,31744,1082431,2164802,4330468,5214340,8659208,17318416,32505856],[]),([7,31744,1082431,2165730,4329604,5214340,8659208,17318416,32505856],[]),([7,31744,1082431,2165730,4329604,8659208,9412872,17318416,32505856],[]),([7,31744,1082431,2165730,4329604,8659208,17318416,32505856,33521664],[]),([7,31744,1082431,2165730,5214340,8659208,17318416,32505856],[(190,0)]),([7,31744,1113121,4330468,8659208,17318431,32505856],[(72,0),(1024,67046),(1024,72161),(1025,437944)]),([7,31744,2065441,2164802,4329631,8659208,17318896,32505856],[(1024,437747)]),([7,31744,2065441,2164802,4330468,8659208,17318431],[(1024,102899),(1024,70118),(1025,122553)]),([7,31744,2164802,4330468,8659208,17318431,32539681],[(1024,102904),(1024,70118)]),([7,31744,4329604,4330468,8659208,17318431,32539681],[(1024,99832),(1024,73185),(1025,88761)]),([7,31744,4329604,8659208,17318431,32539681,33553439],[(1024,496915),(1024,67063)]),([7,31744,4330468,8659208,17318431,32472030,32505856],[(1024,100024),(1024,67046)]),([7,31744,4330468,8659208,17318431,32505856,32539681],[(1024,67046),(1024,72161)]),([7,31744,4330468,8659208,17318431,32539681],[(6,0),(58,0),(97,0),(1024,67046),(1024,99832),(1024,72161),(1025,122553),(1025,285368),(1025,437944)]),([7,31775,32736,4329604,8659208,17318416,32539681],[(1024,83247),(1024,67063)]),([7,31775,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[]),([7,31775,1015808,1082401,2164831,4330468,8659208,17318416,32505856],[]),([7,31775,1015808,1082431,2164802,4330468,8659208,17318416,32505856],[]),([7,31775,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[]),([7,31775,1015808,1083361,2164831,4329604,8659208,17318416,32505856],[]),([7,31775,1082401,3115074,8659231,17318416,32505856],[(1024,302149),(1024,496706)]),([7,31775,1082401,4330468,8659208,17318431,32505856],[(1024,444907),(1024,67046)])]
def t78 : BT := .nd (blockTree b80) [7,31744,1082431,1083361,2164802,4329604,9412872,17318416,32505856] (blockTree b81)
def b82 : List Row := [([7,1015808,1015839,1082401,2164802,8659944,32641156],[(1024,665864),(1024,491602),(1025,83641)]),([7,1015808,1082401,1082431,2164802,8659944,32641156],[(1024,491795),(1024,69896)]),([7,1015808,1082401,1113121,2164802,4330468,8659208,17318431,32505856],[]),([7,1015808,1082401,2164802,2164831,8659944,32641156],[(1024,511238),(1024,69896)]),([7,1015808,1082401,2164802,2194498,4330468,8659208,17318431,32505856],[]),([7,1015808,1082401,2164802,4330468,4357252,8659208,17318431,32505856],[]),([7,1015808,1082401,2164802,4330468,4358116,8659208,17318431,32505856],[]),([7,1015808,1082401,2164802,8659231,33047056,33553439],[(1024,508993),(1024,302149)]),([7,1015808,1082401,2164806,4329604,8659944,32505856],[(1024,511078),(1024,66664)]),([7,1015808,1082401,2164831,4329604,8659720,32505856],[(1024,660760),(1024,496915)]),([7,1015808,1082401,2164831,4330468,4357252,8659208,17318416,32505856],[]),([7,1015808,1082401,2164831,8659208,8659944,32641156],[(1024,66840),(1024,78119)]),([7,1015808,1082401,2164831,8659208,32641156,33553439],[(1024,67000),(1024,78119)]),([7,1015808,1082401,2194498,4329604,4330468,8659208,17318431,32505856],[]),([7,1015808,1082401,2194498,4330468,8659208,17318431,32505856],[(1024,66199),(1024,70118),(1024,491635)]),([7,1015808,1082401,4329604,8659944,25977631,32505856],[(1024,78521),(1024,67255)]),([7,1015808,1082401,4330468,8659208,25977631,32505856],[(1024,72377),(1024,67255)]),([7,1015808,1082405,2164802,4329604,8659944,32505856],[(1024,77926),(1024,65640)]),([7,1015808,1082431,1083361,2194498,4329604,8659208,17318416,32505856],[(128,0)]),([7,1015808,1082431,1113121,2165730,4329604,8659208,17318416,32505856],[]),([7,1015808,1082431,1113151,2165730,4329604,8659208,17318416,32505856],[]),([7,1015808,1082431,2164802,4329604,8659720,32505856],[(1024,491795),(1024,655640)]),([7,1015808,1082431,2164802,4330468,4357252,8659208,17318416,32505856],[]),([7,1015808,1082431,2164802,8659208,8659944,32641156],[(1024,78118),(1024,65816)]),([7,1015808,1082431,2164802,8659208,32641156,33553439],[(1024,65976),(1024,78118)])]
def b83 : List Row := [([7,1015808,1082431,2165730,2195426,4329604,8659208,17318416,32505856],[(236,0)]),([7,1015808,1082431,2165730,4329604,4357252,8659208,17318416,32505856],[]),([7,1015808,1082431,2165730,4329604,8659208,17318416,17333776,32505856],[]),([7,1015808,1082431,2165730,6494406,8659208,32505856],[(1024,78118),(1024,65831)]),([7,1015808,1082431,2165730,8659208,18400817,32505856],[(1024,78118),(1024,301121)]),([7,1015808,1082431,2194498,4329604,4330468,8659208,17318416,32505856],[]),([7,1015808,1082431,3247203,4329604,8659944,32505856],[(1024,69896),(1024,491795)]),([7,1015808,1082431,3248099,8659208,17318416,32505856],[(1024,309313),(1024,65839),(1025,70283)]),([7,1015808,1082431,4329604,8659944,25977624,32505856],[(1024,66231),(1024,104121)]),([7,1015808,1113121,2164802,4329604,4330468,8659208,17318431,32505856],[]),([7,1015808,1113121,2164802,4330468,8659208,17318431,32505856],[(1024,491635)]),([7,1015808,1113121,2164831,2165730,4329604,8659208,17318416,32505856],[]),([7,1015808,1113121,2164831,4329604,4330468,8659208,17318416,32505856],[]),([7,1015808,1113121,4330468,8659208,17318431,32505856],[(1024,67255),(1024,72377)]),([7,1015808,2164802,4329604,8659944,25977631,32505856],[(1024,78324),(1024,66034)]),([7,1015808,2164802,4330468,8659208,25977631,32505856],[(1024,71156),(1024,66034)]),([7,1015808,2164831,3247203,4329604,8659944,32505856],[(1024,78321),(1024,69896),(1025,82420)]),([7,1015808,2164831,3248099,8659208,17318416,32505856],[(1024,309313),(1024,65839),(1025,70316)]),([7,1015808,2164831,4329604,8659944,25977624,32505856],[(1024,78321),(1024,66034)]),([7,1015808,2194498,4330468,8659208,17318431,32505856],[(1024,66199),(1024,71156)]),([7,1015808,4330468,8659208,17318431,32505856,32539681],[(1024,67223),(1024,72345)]),([7,1015839,1082401,2164802,4329604,8659944,33521664],[(1024,78513),(1024,69896)]),([7,1015839,1082401,3115074,4329604,8659944,32505856],[(1024,491602),(1024,69896),(1025,83641)]),([7,1082401,1082431,2164802,5214340,8659944,32505856],[(1024,69896),(1024,655640)])]
def t79 : BT := .nd (blockTree b82) [7,1015808,1082431,2165730,2194498,4329604,8659208,17318416,32505856] (blockTree b83)
def t80 : BT := .nd t78 [7,31775,1113121,4330468,8659208,17318416,32505856] t79
def b84 : List Row := [([7,1082401,2164802,2164831,5214340,8659944,32505856],[(1024,502024),(1024,504070),(1025,82420)]),([7,1082401,2164802,4329604,8659944,32505887,33521664],[(1024,501847),(1024,69896)]),([7,1082401,2164802,5214340,8659944,32505856,32505887],[(1024,502024),(1024,504070)]),([7,1082401,2164802,5214340,8659944,32505856,33554400],[(1024,504070),(1024,69896)]),([7,1082401,2164831,2165730,5214340,8659208,32505856],[(56,0),(1024,78114),(1024,69928)]),([7,1082401,2164831,3115074,4329604,8659944,32505856],[(1024,69896),(1024,501863)]),([7,1082401,2194498,4330468,8659208,17318431,32505856],[(1024,70118),(1024,73185)]),([7,1082401,3115074,3115103,4329604,8659944,32505856],[(1024,491602),(1024,69896)]),([7,1082401,3115074,4329604,8659231,8659944,32505856],[(1024,501875),(1024,69928)]),([7,1082401,3115074,4329604,8659944,8683496,32505856],[(1024,69736),(1024,491602)]),([7,1082401,3115074,4329604,8659944,17318431,32505856],[(1024,502023),(1024,69896)]),([7,1082401,3115074,4329604,8659944,17333776,32505856],[(1024,299080),(1024,491602)]),([7,1082401,3115074,4329604,8659944,32505856,32505887],[(1024,655447),(1024,69896)]),([7,1082401,3115074,4329604,8659944,32505856,33554400],[(1024,502023),(1024,69896)]),([7,1082401,3115074,4330468,8659208,17318431,32505856],[(1024,502195),(1024,666040)]),([7,1082401,4330468,4357252,8659208,17318431,32505856],[(1024,100024),(1024,73185)]),([7,1082401,4330468,4358116,8659208,17318431,32505856],[(1024,444907),(1024,72161),(1025,285368),(1025,295410)]),([7,1082401,4330468,8659208,17318431,32505856,33521664],[(1024,502195),(1024,67255)]),([7,1082401,4330468,8659208,17318431,32505856,33522687],[(1024,502195),(1024,67046)]),([7,1082431,2164802,2165730,5214340,8659208,32505856],[(56,0),(1024,78118),(1024,65832)]),([7,1082431,2164802,5214340,8659208,8659944,32505856],[(1024,78118),(1024,65811)]),([7,1082431,2164802,5214340,8659208,32505856,33553439],[(1024,78118),(1024,65832)]),([7,1082431,2165730,3115074,4329604,8659208,32505856],[(1024,78118),(1024,65832),(1025,302769)]),([7,1082431,2165730,5214340,8659208,17318416,32505856],[(1024,655800),(1024,65971)]),([7,1082431,2194498,5214340,8659208,17318416,32505856],[(1024,72997),(1024,65811)])]
def b85 : List Row := [([7,1082431,5214340,8659208,8659944,17318416,32505856],[(1024,655640),(1024,65811)]),([7,2194498,4330468,8659208,17318431,32505856],[(1024,66022),(1024,98803),(1024,71137),(1025,442867),(1025,122521),(1025,117236)]),([8,4,31,992,31744,1015808,1082401,2164802,8659208,33047056],[]),([8,4,31,992,31744,1015808,1082401,2164802,17318416,32776456],[(336,0)]),([8,4,31,992,31744,1082401,2164802,8659208,17809936,32505856],[(216,0),(336,0)]),([8,4,31,992,31744,1082401,2164802,9412872,17318416,32505856],[(216,0),(336,0)]),([8,4,31,992,31744,1082401,3115074,8659208,17318416,32505856],[(216,0),(336,0)]),([8,4,31,992,1015808,1082401,2164802,8659208,17333776,32505856],[(216,0),(336,0)]),([8,4,31,992,1015808,1082401,2194498,8659208,17318416,32505856],[(216,0),(336,0)]),([8,4,31,992,1015808,1113121,2164802,8659208,17318416,32505856],[(216,0),(336,0)]),([8,4,31,31744,1015808,1082401,2165730,8659208,17318416,32505856],[]),([8,4,31,31744,1015808,1083361,2164802,8659208,17318416,32505856],[]),([8,4,512,1015808,1082401,2164802,8659208,32505856],[(168,0),(1024,491635),(1024,655480)]),([8,4,992,31744,1015808,1082401,2164802,8659208,17318431,32505856],[(56,0),(216,0)]),([8,4,992,31744,1015808,1082401,2164831,8659208,17318416,32505856],[(216,0),(336,0)]),([8,4,992,31744,1015808,1082431,2164802,8659208,17318416,32505856],[(96,0),(216,0),(336,0)]),([8,4,992,31775,1015808,1082401,2164802,8659208,17318416,32505856],[(56,0),(96,0),(216,0),(336,0)]),([8,4,992,1015808,1082401,2164802,8659208,32641156],[(96,0),(128,0),(1024,511270),(1024,491635)]),([8,4,992,1015808,1082401,2164802,8659208,33047056],[(168,0),(1024,655480),(1024,491635)]),([8,4,992,1082401,2164802,5214340,8659208,32505856],[(72,0),(1024,504102),(1024,491635)]),([8,4,992,1082401,2164802,8659208,17809936,32505856],[(128,0),(1024,491635),(1024,655480)]),([8,4,992,1082401,3115074,4329604,8659208,32505856],[(72,0),(168,0),(1024,492838),(1024,491635)]),([8,4,992,1082401,3115074,8659208,17318416,32505856],[(128,0),(1024,491635),(1024,655480)]),([8,4,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,511078),(1024,491635)])]
def t81 : BT := .nd (blockTree b84) [7,1082431,2194498,5214340,8659208,32505856] (blockTree b85)
def b86 : List Row := [([8,4,1015808,1083361,2164802,8659208,17318416,32505856],[(128,0),(1024,491635),(1024,655480)]),([8,12,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,31,992,8192,1015808,1082401,2164802,4329604,8659208,33047056],[(72,0)]),([8,31,992,8192,1015808,1082401,2164802,4329604,17318416,32776456],[(72,0),(128,0),(168,0),(240,0)]),([8,31,992,8192,1082401,2164802,4329604,8659208,17809936,32505856],[(72,0),(128,0),(376,0)]),([8,31,992,8192,1082401,2164802,4329604,9412872,17318416,32505856],[(72,0),(96,0),(376,0)]),([8,31,992,8192,1082401,3115074,4329604,8659208,17318416,32505856],[(72,0),(184,0),(272,0)]),([8,31,992,31744,32768,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,32768,1082401,2164802,4329604,17318416,32776456],[(128,0),(168,0),(240,0)]),([8,31,992,31744,32768,3247203,4329604,8659208,17318416,32505856],[(128,0),(184,0),(192,0),(272,0),(376,0)]),([8,31,992,31744,1014750,4329604,8659208,17318416],[(144,0),(216,0),(1024,99832),(1024,67063)]),([8,31,992,31744,1015808,1082401,2097152,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2097152,4329604,17318416,32776456],[(128,0),(168,0),(240,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,32506368],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33317656],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,8659720,32505856],[(128,0),(168,0),(384,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,9412872,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],[(128,0),(168,0),(240,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318431,32776456],[(72,0),(128,0),(168,0),(240,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,17333776,32776456],[(128,0),(168,0),(240,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,17809936,32776456],[(128,0),(168,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,25977624,32776456],[(128,0),(168,0),(284,0),(384,0)]),([8,31,992,31744,1015808,1082401,2164802,4329604,32776456,33047056],[(128,0),(168,0)])]
def b87 : List Row := [([8,31,992,31744,1015808,1082401,2164802,4330468,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,4357252,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,5214340,8659208,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,12988812,33047056],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,32641156,33047056],[(128,0),(168,0),(296,0)]),([8,31,992,31744,1015808,1082401,2164802,12988812,25977624,32505856],[(128,0),(168,0),(240,0),(384,0)]),([8,31,992,31744,1015808,1082401,2164831,4329604,17318416,32776456],[(72,0),(128,0),(168,0),(272,0)]),([8,31,992,31744,1015808,1082401,2164831,8659208,17318416,32641156],[(72,0),(128,0),(168,0),(272,0)]),([8,31,992,31744,1015808,1082401,2194498,4329604,17318416,32776456],[(128,0),(232,0),(240,0)]),([8,31,992,31744,1015808,1082401,3145728,4329604,8659208,17318416],[(128,0),(232,0),(240,0),(336,0)]),([8,31,992,31744,1015808,1082401,3247203,4329604,8659208,33047056],[(128,0)]),([8,31,992,31744,1015808,1082401,3247203,4329604,17318416,32776456],[(128,0),(168,0),(240,0)]),([8,31,992,31744,1015808,1082431,2164802,4329604,17318416,32776456],[(72,0),(128,0),(168,0),(272,0)]),([8,31,992,31744,1015808,1082431,2164802,8659208,17318416,32641156],[(72,0),(128,0),(168,0),(272,0)]),([8,31,992,31744,1015808,1113121,2164802,4329604,17318416,32776456],[(168,0),(232,0)]),([8,31,992,31744,1015808,3179553,4329604,8659208,17318416,32505856],[(128,0),(184,0),(192,0),(272,0),(376,0)]),([8,31,992,31744,1015812,1082401,2164802,8659208,17318416,32505856],[(72,0),(128,0),(240,0)]),([8,31,992,31744,1081344,2164802,4329604,8659208,17318416,32505856],[(128,0),(184,0),(272,0),(376,0)]),([8,31,992,31744,1082401,2097152,4329604,8659208,17318416,33521664],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,31744,1082401,2097152,4329604,8659208,17809936,32505856],[(128,0),(376,0)]),([8,31,992,31744,1082401,2097152,4329604,9412872,17318416,32505856],[(96,0),(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,3115074,4329604,8659208,33047056],[(128,0)]),([8,31,992,31744,1082401,2164802,3115074,4329604,17318416,32776456],[(128,0)]),([8,31,992,31744,1082401,2164802,4329604,5214340,8659208,33047056],[])]
def t82 : BT := .nd (blockTree b86) [8,31,992,31744,1015808,1082401,2164802,4329604,32776456,33317656] (blockTree b87)
def t83 : BT := .nd t81 [8,4,1015808,1082401,2165730,8659208,17318416,32505856] t82
def t84 : BT := .nd t80 [7,1082401,1082431,3115074,4329604,8659944,32505856] t83
def b88 : List Row := [([8,31,992,31744,1082401,2164802,4329604,8659208,9412872,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,17318416,32538624],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17351184,32505856],[(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32641156],[(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,32776456],[(128,0),(256,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,17809936,33047056],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,26207000,32505856],[(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,32505856,33538576],[(128,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,33047056,33521664],[(96,0),(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,8659208,33047056,33538576],[]),([8,31,992,31744,1082401,2164802,4329604,8691976,17318416,32505856],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],[(96,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32641156],[(96,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32776456],[(96,0),(128,0),(184,0),(256,0),(272,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17318431,32505856],[(72,0),(96,0),(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17333776,32505856],[(96,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,17809936,32505856],[(96,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,25977624,32505856],[(96,0),(128,0),(256,0),(284,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,26207000,32505856],[(96,0),(284,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,32505856,33047056],[(96,0)]),([8,31,992,31744,1082401,2164802,4329604,9412872,33047056],[(82,0),(97,0),(106,0),(138,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32505856,33530120],[(96,0),(312,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32776456,33521664],[(96,0),(128,0),(376,0)]),([8,31,992,31744,1082401,2164802,4329604,17318416,32776456,33530120],[(96,0),(128,0),(312,0),(376,0)])]
def b89 : List Row := [([8,31,992,31744,1082401,2164802,4329604,17809936,32776456],[(82,0),(97,0),(106,0),(128,0),(129,0),(138,0),(313,0)]),([8,31,992,31744,1082401,2164802,4330468,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,4357252,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2164802,5214340,8659208,17809936,32505856],[(96,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,25977624,32505856],[(96,0),(256,0),(284,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,32505856,33047056],[(96,0),(312,0)]),([8,31,992,31744,1082401,2164802,5214340,8659208,33047056],[(82,0),(97,0),(138,0),(1024,502024),(1024,509355)]),([8,31,992,31744,1082401,2164802,5214340,8659944],[(1024,450187),(1024,69896),(1025,69928)]),([8,31,992,31744,1082401,2164802,5214340,32776456],[(96,0),(1024,711975),(1024,69928)]),([8,31,992,31744,1082401,2164802,5214340,33047056],[(1024,509025),(1024,711778)]),([8,31,992,31744,1082401,2164802,8659231,33047056],[(72,0),(1024,444907),(1024,281062),(1025,99603),(1025,266536)]),([8,31,992,31744,1082401,2164802,9412872,32641156],[(96,0),(1024,69928),(1024,510246)]),([8,31,992,31744,1082401,2164831,4329604,8659208,17809936,32505856],[(72,0),(128,0)]),([8,31,992,31744,1082401,2164831,4329604,9412872,17318416,32505856],[(72,0),(96,0),(272,0)]),([8,31,992,31744,1082401,2164831,5214340,8659208,17318416,32505856],[(72,0),(96,0),(272,0)]),([8,31,992,31744,1082401,2194498,4329604,8659208,17809936,32505856],[]),([8,31,992,31744,1082401,2194498,4329604,9412872,17318416,32505856],[(96,0),(184,0)]),([8,31,992,31744,1082401,2197570,4329604,8659208,17318416,32505856],[(184,0),(272,0),(376,0)]),([8,31,992,31744,1082401,3112960,4329604,8659208,17318416,32505856],[(96,0),(184,0),(272,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],[(184,0),(272,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,17318431,32505856],[(72,0),(184,0),(272,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,17333776,32505856],[]),([8,31,992,31744,1082401,3115074,4329604,8659208,17809936,32505856],[(96,0)]),([8,31,992,31744,1082401,3115074,4329604,8659208,25977624,32505856],[(284,0)])]
def t85 : BT := .nd (blockTree b88) [8,31,992,31744,1082401,2164802,4329604,17809936,32505856,32776456] (blockTree b89)
def b90 : List Row := [([8,31,992,31744,1082401,3115074,4329604,9412872,17318416,32505856],[(96,0)]),([8,31,992,31744,1082401,3115074,4329604,17318416,32505856,32776456],[(312,0)]),([8,31,992,31744,1082401,3247203,4329604,8659208,17809936,32505856],[(96,0),(128,0),(376,0)]),([8,31,992,31744,1082401,3247203,4329604,9412872,17318416,32505856],[(96,0),(376,0)]),([8,31,992,31744,1082401,3247203,4329604,32776456],[(1024,444907),(1024,69928),(1025,66034),(1025,99001)]),([8,31,992,31744,1082401,3247203,4329604,33047056],[(1024,707682),(1024,83425),(1025,66034),(1025,300729)]),([8,31,992,31744,1082401,3247203,8659208,32641156],[(1024,705831),(1024,69928),(1025,66233),(1025,98803)]),([8,31,992,31744,1082401,4329604,25977624,32776456],[(1024,444907),(1024,67255),(1025,99001),(1025,285369),(1025,449209)]),([8,31,992,31744,1082401,4329604,25977624,33047056],[(1024,100020),(1024,67255),(1025,300729),(1025,318137)]),([8,31,992,31744,1082401,8659208,21648020,32641156],[(1024,69928),(1024,83425),(1025,66233)]),([8,31,992,31744,1082401,12988812,25977624,32505856],[(1024,67255),(1024,83425)]),([8,31,992,31744,1082431,2164802,4329604,9412872,17318416,32505856],[(72,0),(96,0),(128,0),(272,0)]),([8,31,992,31744,1082431,2164802,5214340,8659208,17318416,32505856],[(72,0),(96,0),(128,0),(272,0)]),([8,31,992,31744,1113121,2164802,4329604,9412872,17318416,32505856],[(184,0)]),([8,31,992,31744,3115074,4329604,8659208,17318416,32539681],[(1024,70295),(1024,73345),(1024,78465),(1024,309894),(1024,507969),(1024,508001),(1024,508166),(1024,508198),(1024,508331)]),([8,31,992,31744,3179553,4329604,8659208,17318416],[(144,0),(216,0),(1024,444907),(1024,83425)]),([8,31,992,31744,3247203,4329604,8659208,32539681],[(1024,444907),(1024,69928),(1025,66233),(1025,99001)]),([8,31,992,31744,3247203,4329604,17318416,32539681],[(1024,444907),(1024,83425),(1025,66232),(1025,300729)]),([8,31,992,31744,4329604,8659208,16236015,32539681],[(1024,516391),(1024,67063)]),([8,31,992,31744,4329604,8659208,17318416,32538624],[(112,0),(168,0),(1024,98808),(1024,66039)]),([8,31,992,31744,4329604,8659208,17318416,32539681],[(112,0),(168,0),(1024,99832),(1024,67063)]),([8,31,992,31744,4329604,8659208,17318431,32539681],[(72,0),(112,0),(168,0),(1024,268792),(1024,67063),(1025,88761)]),([8,31,992,31744,4329604,8659208,17333776,32539681],[(72,0),(168,0),(1024,99832),(1024,67063),(1025,450233)]),([8,31,992,31744,4329604,8659208,17383952],[(168,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)])]
def b91 : List Row := [([8,31,992,31744,4329604,8659208,25977624,32539681],[(1024,301561),(1024,67063),(1025,99001)]),([8,31,992,31744,4329604,8724744,17318416],[(112,0),(168,0),(1024,66034),(1024,98801),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,31744,4329604,12988812,17318416,32539681],[(168,0),(1024,99832),(1024,83425),(1025,66232),(1025,268584)]),([8,31,992,31744,4329604,17318416,24895223,32539681],[(112,0),(128,0),(1024,515170),(1024,67063)]),([8,31,992,31748,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,31,992,31775,1015808,1082401,2164802,4329604,8659208,33047056],[]),([8,31,992,31775,1015808,1082401,2164802,4329604,17318416,32776456],[(128,0),(168,0),(272,0)]),([8,31,992,31775,1015808,1082401,2164802,8659208,17318416,32641156],[(128,0),(168,0),(272,0),(288,0)]),([8,31,992,31775,1082401,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,31775,1082401,2164802,4329604,9412872,17318416,32505856],[(96,0),(128,0),(272,0)]),([8,31,992,31775,1082401,2164802,5214340,8659208,17318416,32505856],[(96,0),(128,0),(272,0),(288,0)]),([8,31,992,31775,1082401,2164802,8659208,17809936],[(168,0),(1024,450187),(1024,286342),(1025,69928)]),([8,31,992,31775,1082401,2164802,8659208,33047056],[(168,0),(1024,444907),(1024,281062),(1025,69928)]),([8,31,992,31775,1082401,2164802,9412872,17318416],[(1024,444043),(1024,270001),(1025,69928),(1025,426488)]),([8,31,992,31775,1082401,2164802,17318416,32776456],[(1024,444907),(1024,281062),(1025,69928),(1025,426648)]),([8,31,992,31775,1082401,3115074,4329604,8659208,17318416,32505856],[(272,0)]),([8,31,992,31775,4329604,8659208,17318416,32539681],[(168,0),(1024,99832),(1024,67063),(1025,76471)]),([8,31,992,32768,1082401,2164802,4329604,8659208,17333776,32505856],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,32768,1082401,2194498,4329604,8659208,17318416,32505856],[(96,0),(184,0),(272,0)]),([8,31,992,32768,1113121,2164802,4329604,8659208,17318416,32505856],[(128,0),(272,0)]),([8,31,992,32768,4329604,8659208,17333776,32505856],[(1024,66199),(1024,98968)]),([8,31,992,65536,4329604,8659208,17333776],[(72,0),(112,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,97280,4329604,8659208,17318416],[(112,0),(168,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]),([8,31,992,507375,1015808,1082401,2164802,8659208],[(216,0),(1024,69928),(1024,502195)])]
def t86 : BT := .nd (blockTree b90) [8,31,992,31744,4329604,8659208,21648020,32539681] (blockTree b91)
def t87 : BT := .nd t85 [8,31,992,31744,1082401,3115074,4329604,8659208,32505856,33047056] t86
def b92 : List Row := [([8,31,992,1015808,1082401,1113121,2164802,4329604,17318416,32776456],[(96,0),(168,0),(232,0)]),([8,31,992,1015808,1082401,2097152,4329604,8659208,17333776,32505856],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,1015808,1082401,2128896,4329604,8659208,17318416,32505856],[(96,0),(184,0),(272,0)]),([8,31,992,1015808,1082401,2164802,2194498,4329604,8659208,33047056],[(128,0)]),([8,31,992,1015808,1082401,2164802,2194498,4329604,17318416,32776456],[(96,0),(128,0),(232,0)]),([8,31,992,1015808,1082401,2164802,4329604,4357252,8659208,33047056],[]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17326608,32505856],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17333776,32641156],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17333776,32776456],[(96,0),(128,0),(184,0),(256,0),(376,0)]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17333776,33047056],[(184,0)]),([8,31,992,1015808,1082401,2164802,4329604,8659208,17333791,32505856],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,1015808,1082401,2164802,4330468,8659208,17333776,32505856],[]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17333776,32505856],[]),([8,31,992,1015808,1082401,2164802,4357252,8659208,17809936,32505856],[]),([8,31,992,1015808,1082401,2164802,4357252,8659208,25977624,32505856],[(284,0)]),([8,31,992,1015808,1082401,2164802,4357252,8659208,32505856,33047056],[]),([8,31,992,1015808,1082401,2164802,4357252,8659208,33047056],[(106,0),(138,0),(1024,302200),(1024,680033)]),([8,31,992,1015808,1082401,2164802,8659208,32641156],[(96,0),(128,0),(1024,665896),(1024,502195)]),([8,31,992,1015808,1082401,2164802,8659208,33525892],[(96,0),(128,0),(1024,665896),(1024,509222),(1025,300532)]),([8,31,992,1015808,1082401,2164802,8659231,33047056],[(168,0),(1024,666040),(1024,502195),(1025,266536)]),([8,31,992,1015808,1082401,2164802,9412872,32641156],[(96,0),(128,0),(1024,665896),(1024,510246),(1025,431604)]),([8,31,992,1015808,1082401,2164802,12988812,32641156],[(96,0),(128,0),(1024,665864),(1024,502195)]),([8,31,992,1015808,1082401,2164802,24895223,32641156],[(96,0),(128,0),(1024,665896),(1024,502195)]),([8,31,992,1015808,1082401,2164802,32641156,32776456],[(96,0),(128,0),(1024,69928),(1024,502195),(1025,431769),(1025,445113)])]
def b93 : List Row := [([8,31,992,1015808,1082401,2164831,4329604,8659208,17333776,32505856],[(96,0),(128,0),(272,0)]),([8,31,992,1015808,1082401,2164831,4357252,8659208,17318416,32505856],[(96,0),(272,0)]),([8,31,992,1015808,1082401,2164831,8659208,32641156],[(72,0),(96,0),(128,0),(1024,511270),(1024,66856),(1025,71976)]),([8,31,992,1015808,1082401,2172994,4329604,8659208,17318416,32505856],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,17318416,32505856],[(96,0),(184,0),(272,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,17318416,32776456],[(96,0),(184,0),(256,0),(272,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,17318431,32505856],[(96,0),(128,0),(184,0),(272,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,17333776,32505856],[(96,0),(184,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,17809936,32505856],[(96,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,25977624,32505856],[(96,0),(284,0)]),([8,31,992,1015808,1082401,2194498,4329604,8659208,32505856,33047056],[(96,0)]),([8,31,992,1015808,1082401,2194498,4329604,17318416,32505856,32776456],[(96,0),(184,0),(312,0)]),([8,31,992,1015808,1082401,2194498,4329604,17318416,32776456],[(96,0),(97,0),(106,0),(138,0),(178,0),(184,0),(186,0),(230,0),(233,0),(313,0),(1024,117217)]),([8,31,992,1015808,1082401,2194498,4329604,32776456],[(96,0),(1024,449831),(1024,69928)]),([8,31,992,1015808,1082401,2194527,4329604,8659208,17318416,32505856],[(96,0),(272,0)]),([8,31,992,1015808,1082401,3115074,4329604,8659208,17333776,32505856],[(96,0),(184,0)]),([8,31,992,1015808,1082401,3115074,8659208,32641156],[(96,0),(128,0),(1024,665896),(1024,508198),(1025,83641),(1025,300532)]),([8,31,992,1015808,1082401,3247203,4329604,8659208,17333776,32505856],[(96,0),(128,0),(184,0),(376,0)]),([8,31,992,1015808,1082401,3247203,8659208,32641156],[(96,0),(128,0),(1024,700711),(1024,69928),(1025,302731),(1025,436723)]),([8,31,992,1015808,1082401,3275875,4329604,8659208,17318416,32505856],[(96,0),(184,0),(272,0)]),([8,31,992,1015808,1082401,4329604,8682760,17318416,32573506],[(1024,83618),(1024,315047)]),([8,31,992,1015808,1082401,6494406,12988812,32505856],[(96,0),(1024,441015),(1024,502195)]),([8,31,992,1015808,1082401,8659208,31389629,32641156],[(96,0),(1024,301741),(1024,69928)]),([8,31,992,1015808,1082401,12988812,25977624,32505856],[(96,0),(168,0),(1024,438969),(1024,67255)])]
def t88 : BT := .nd (blockTree b92) [8,31,992,1015808,1082401,2164802,32641156,32911756] (blockTree b93)
def b94 : List Row := [([8,31,992,1015808,1082431,2164802,4357252,8659208,17318416,32505856],[(128,0),(272,0)]),([8,31,992,1015808,1082431,2164802,8659208,32641156],[(96,0),(128,0),(1024,511270),(1024,65832),(1025,70952)]),([8,31,992,1015808,1082431,2194498,4329604,8659208,17318416,32505856],[(96,0),(128,0),(272,0)]),([8,31,992,1015808,1090593,2164802,4329604,8659208,17318416,32505856],[(96,0),(128,0),(184,0),(272,0),(376,0)]),([8,31,992,1015808,1113121,2097152,4329604,8659208,17318416,32505856],[(128,0),(272,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17318416,32505856],[(128,0),(272,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17318416,32776456],[(128,0),(256,0),(272,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17318431,32505856],[(96,0),(128,0),(272,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17333776,32505856],[(128,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,25977624,32505856],[(128,0),(284,0)]),([8,31,992,1015808,1113121,2164802,4329604,8659208,32505856,33047056],[(128,0)]),([8,31,992,1015808,1113121,2164802,4329604,9412872,17318416,32505856],[(184,0)]),([8,31,992,1015808,1113121,2164802,4329604,17318416,32505856,32776456],[(128,0),(312,0)]),([8,31,992,1015808,1113121,2164802,4329604,17318416,32776456],[(106,0),(128,0),(129,0),(138,0),(178,0),(186,0),(230,0),(313,0)]),([8,31,992,1015808,1113121,2164802,4329604,32776456],[(128,0),(1024,449830),(1024,69928)]),([8,31,992,1015808,1113121,2164831,4329604,8659208,17318416,32505856],[(96,0),(128,0),(272,0)]),([8,31,992,1015808,1113121,2194498,4329604,8659208,17318416,32505856],[(272,0)]),([8,31,992,1015808,1113121,3115074,4329604,8659208,17318416,32505856],[(184,0),(272,0)]),([8,31,992,1015808,1113121,3247203,4329604,8659208,17318416,32505856],[(128,0),(184,0),(272,0),(376,0)]),([8,31,992,1015808,1113121,3275875,4329604,8659208,17318416,32505856],[(272,0)]),([8,31,992,1015808,1113151,2164802,4329604,8659208,17318416,32505856],[(128,0),(272,0)]),([8,31,992,1015808,2164802,3247203,8659208,32641156],[(96,0),(128,0),(1024,511270),(1024,69928),(1025,302764),(1025,437944)]),([8,31,992,1015808,2164802,4329604,8682760,17318416,32539681],[(1024,508331)])]
def b95 : List Row := [([8,31,992,1015808,2164802,8659208,32472030,32641156],[(96,0),(1024,300532),(1024,69928)]),([8,31,992,1015808,2164802,12988812,25977624,32505856],[(96,0),(168,0),(1024,438772),(1024,66034)]),([8,31,992,1015808,3247203,5412005,8659208,32505856],[(1024,508200),(1024,502195)]),([8,31,992,1015808,3247203,6494406,8659208,32505856],[(1024,511042),(1024,69928)]),([8,31,992,1015808,4329604,8659208,17333776,32539681],[(1024,301707),(1024,67223)]),([8,31,992,1015808,4329604,8659208,17333776,32573506],[(1024,98803),(1024,66034),(1025,67255)]),([8,31,992,1015839,1082401,2164802,8659208,32641156],[(128,0),(1024,502195),(1024,69928),(1025,69928)]),([8,31,992,1048575,1082401,2164802,5214340,8659208],[(96,0),(1024,450187),(1024,69928)]),([8,31,992,1048575,1082401,3115074,4329604,8659208],[(1024,450187),(1024,69928)]),([8,31,992,1048575,1082401,4329604,8659208,17333776],[(1024,83425),(1024,67255)]),([8,31,992,1082401,1113121,2164802,4329604,8659208,17809936,32505856],[(72,0),(128,0),(376,0)]),([8,31,992,1082401,1113121,2164802,4329604,9412872,17318416,32505856],[(72,0),(376,0)]),([8,31,992,1082401,1113121,3115074,4329604,8659208,17318416,32505856],[(72,0),(272,0)]),([8,31,992,1082401,2097152,4329604,8659208,17333776],[(1024,117217),(1024,281062)]),([8,31,992,1082401,2164802,2194498,4329604,8659208,17809936,32505856],[(96,0),(376,0)]),([8,31,992,1082401,2164802,3115074,4329604,8659208,17333776,32505856],[(96,0),(376,0)]),([8,31,992,1082401,2164802,3115074,8659208,32641156],[(72,0),(96,0),(1024,502195),(1024,69928),(1025,302769),(1025,445112)]),([8,31,992,1082401,2164802,4329604,4357252,8659208,17809936,32505856],[(96,0)]),([8,31,992,1082401,2164802,4329604,5214340,8659208,17333776,32505856],[(72,0),(96,0),(200,0),(368,0)]),([8,31,992,1082401,2164802,4329604,8659208,9412872,17333776,32505856],[(72,0),(96,0),(200,0),(248,0),(368,0)]),([8,31,992,1082401,2164802,4329604,8659208,17333776,17809936,32505856],[(96,0),(368,0)]),([8,31,992,1082401,2164802,4329604,8659208,17333776,32505856,33521664],[(72,0),(96,0),(304,0),(368,0)]),([8,31,992,1082401,2164802,4329604,9412872,33521664],[(72,0),(1024,666035),(1024,69928),(1025,110257),(1025,431608)]),([8,31,992,1082401,2164802,4329604,32776456,33521664],[(72,0),(96,0),(1024,706855),(1024,69928),(1025,431769)])]
def t89 : BT := .nd (blockTree b94) [8,31,992,1015808,2164802,5412005,12988812,32505856] (blockTree b95)
def t90 : BT := .nd t88 [8,31,992,1015808,1082431,2164802,4329604,8659208,17333776,32505856] t89
def t91 : BT := .nd t87 [8,31,992,1015808,1082401,1113121,2164802,4329604,8659208,33047056] t90
def t92 : BT := .nd t84 [8,31,992,31744,1082401,2164802,4329604,5214340,17318416,32776456] t91
def t93 : BT := .nd t77 [7,31744,1015808,1082431,2165730,4329604,17318416,32776456] t92
def b96 : List Row := [([8,31,992,1082401,2164802,4357252,8659208,17809936,32505856],[(82,0),(106,0),(1024,67211),(1024,78498),(1024,302195),(1024,511073)]),([8,31,992,1082401,2164802,4357252,8659208,32539681],[(1024,69928),(1024,78305)]),([8,31,992,1082401,2164802,4357252,8659208,33047056],[(1024,281062),(1024,78305)]),([8,31,992,1082401,2164802,5214340,8659208,32505856],[(72,0),(1024,502056),(1024,504102)]),([8,31,992,1082401,2164802,5214340,8659208,32505887],[(1024,666040),(1024,69928),(1025,69928)]),([8,31,992,1082401,2164802,5214340,8659208,32641156],[(72,0),(96,0),(1024,666040),(1024,502195)]),([8,31,992,1082401,2164802,5214340,8659208,33047056],[(1024,666040),(1024,502195)]),([8,31,992,1082401,2164802,5214340,8659208,33521664],[(72,0),(1024,666040),(1024,69928),(1025,77489)]),([8,31,992,1082401,2164802,5214340,8659208,33525892],[(72,0),(1024,666040),(1024,504102),(1025,300535)]),([8,31,992,1082401,2164802,5214340,8659944,32505856],[(72,0),(1024,502195),(1024,504070),(1025,69928)]),([8,31,992,1082401,2164802,5214340,9412872,32505856],[(72,0),(1024,69928),(1024,509222),(1025,76913),(1025,431604)]),([8,31,992,1082401,2164802,5214340,12988812,32505856],[(72,0),(96,0),(1024,502024),(1024,511270)]),([8,31,992,1082401,2164802,5214340,13611404,32505856],[(72,0),(1024,504102),(1024,666040),(1025,431604)]),([8,31,992,1082401,2164802,5214340,24895223,32505856],[(72,0),(1024,502056),(1024,504102)]),([8,31,992,1082401,2164802,5214340,32505856,32776456],[(72,0),(1024,711975),(1024,69928),(1025,431769)]),([8,31,992,1082401,2164802,5214340,33047056],[(1024,502189),(1024,665701),(1024,503905),(1025,437945),(1025,436723)]),([8,31,992,1082401,2164802,7313606,8659208,32505856],[(72,0),(1024,502056),(1024,504102),(1025,66661)]),([8,31,992,1082401,2164802,8659208,15744495,32505856],[(128,0),(1024,69928),(1024,505921)]),([8,31,992,1082401,2164802,8659208,32505856,33525892],[(72,0),(1024,502056),(1024,504102),(1025,300697)]),([8,31,992,1082401,2164802,8659208,32538623,32641156],[(72,0),(96,0),(1024,444907),(1024,69928)]),([8,31,992,1082401,2164802,8659208,32641156,33521664],[(72,0),(96,0),(1024,502195),(1024,69928)]),([8,31,992,1082401,2164802,8659208,32641156,33525892],[(72,0),(96,0),(1024,502195),(1024,511270),(1025,300697)]),([8,31,992,1082401,2164831,5214340,8659208,32505856],[(72,0),(1024,712999),(1024,66856),(1025,71976)]),([8,31,992,1082401,2194498,3115074,4329604,8659208,17318416,32505856],[(272,0),(376,0)]),([8,31,992,1082401,2194498,4329604,5214340,8659208,17318416,32505856],[(72,0),(200,0),(272,0)])]
def b97 : List Row := [([8,31,992,1082401,2194498,4329604,8659208,17318416,32505856,33521664],[(72,0),(216,0),(304,0),(368,0)]),([8,31,992,1082401,2194498,4329604,8659208,17809936,32505856],[(73,0),(82,0),(106,0),(201,0),(305,0),(1024,302195),(1024,314440)]),([8,31,992,1082401,2194498,4329604,17318416,32776456],[(1024,117217),(1024,281062)]),([8,31,992,1082401,2194498,4329604,32776456],[(1024,314854),(1024,69928),(1024,83425),(1025,300532),(1025,66034),(1025,69928),(1025,98969),(1025,300697)]),([8,31,992,1082401,2194498,5214340,8659208,32505856],[(72,0),(1024,712999),(1024,69928)]),([8,31,992,1082401,3115074,4329604,4357252,8659208,17318416,32505856],[(200,0),(272,0)]),([8,31,992,1082401,3115074,4329604,8659208,17333776,32505856],[(73,0),(201,0),(305,0),(1024,309894),(1024,704792),(1024,66199),(1024,309320),(1024,491635)]),([8,31,992,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,502055)]),([8,31,992,1082401,3115074,4329604,8659208,32505887],[(1024,666040),(1024,69928),(1025,69928)]),([8,31,992,1082401,3115074,4329604,8659208,32641156],[(1024,666040),(1024,502055)]),([8,31,992,1082401,3115074,4329604,8659944,32505856],[(1024,502195),(1024,69896),(1025,69928)]),([8,31,992,1082401,3115074,4329604,9412872,32505856],[(72,0),(1024,69928),(1024,508198),(1025,431604)]),([8,31,992,1082401,3115074,4329604,12988812,32505856],[(1024,502055),(1024,503078)]),([8,31,992,1082401,3115074,4329604,24895223,32505856],[(1024,502055),(1024,69928)]),([8,31,992,1082401,3115074,4357252,8659208,32505856],[(1024,69928),(1024,508198)]),([8,31,992,1082401,3115074,5214340,8659208,32505856],[(72,0),(1024,69928),(1024,508198)]),([8,31,992,1082401,3115074,5412005,8659208,32505856],[(1024,69928),(1024,502055),(1025,65637),(1025,301547)]),([8,31,992,1082401,3115074,6494406,8659208,32505856],[(1024,710722),(1024,69928),(1025,67051)]),([8,31,992,1082401,3115074,7313606,8659208,32505856],[(1024,69928),(1024,503078),(1025,66661),(1025,300532)]),([8,31,992,1082401,3115074,8659208,12988812,32505856],[(128,0),(1024,69928),(1024,502055),(1025,267560)]),([8,31,992,1082401,3115074,8659208,16236015,32505856],[(128,0),(1024,69928),(1024,501826)]),([8,31,992,1082401,3115074,8659208,32505856,32641156],[(1024,69928),(1024,502055),(1025,300697),(1025,445113)]),([8,31,992,1082401,3115103,4329604,8659208,32505856],[(1024,502055),(1024,66856),(1025,71976)]),([8,31,992,1082401,3247203,4357252,8659208,32505856],[(1024,712999),(1024,69928),(1025,98803)])]
def t94 : BT := .nd (blockTree b96) [8,31,992,1082401,2194498,4329604,8659208,9412872,17318416,32505856] (blockTree b97)
def b98 : List Row := [([8,31,992,1082401,4329604,7313606,8659208,32505856],[(1024,67255),(1024,502055)]),([8,31,992,1082401,4329604,8659208,16220655,32505856],[(1024,502055),(1024,67255)]),([8,31,992,1082401,4329604,8659208,17333776,32505856],[(1024,100024),(1024,67255)]),([8,31,992,1082401,4329604,8659208,17333776,32539681],[(1024,100024),(1024,67255)]),([8,31,992,1082401,4329604,8659208,17333776,32641156],[(152,0),(1024,100024),(1024,83425),(1025,66231)]),([8,31,992,1082401,4329604,8659208,17333776,33047056],[(192,0),(1024,100024),(1024,67255),(1025,300729),(1025,318137)]),([8,31,992,1082401,4329604,8659208,17333791,32505856],[(72,0),(1024,301547),(1024,67255),(1025,88761)]),([8,31,992,1082401,4329604,8659208,21659284,32505856],[(1024,301547),(1024,69928),(1025,66034)]),([8,31,992,1082401,4329604,8659208,30439357,32505856],[(1024,301547),(1024,69928)]),([8,31,992,1082401,4329604,12988812,17333776,32505856],[(240,0),(1024,100024),(1024,83425),(1025,66034)]),([8,31,992,1082401,4329604,17333776,24895223,32505856],[(1024,711778),(1024,67255)]),([8,31,992,1082401,4330468,8659208,17333776,32505856],[(1024,67255),(1024,83425),(1025,285368),(1025,302571)]),([8,31,992,1082401,4357252,8659208,16236015,32505856],[(1024,712999),(1024,67051)]),([8,31,992,1082401,4357252,8659208,17333776,32505856],[(1024,67255),(1024,83425)]),([8,31,992,1082401,4357252,8659208,17809936],[(1024,67244),(1024,100024),(1024,77441),(1025,301753),(1025,67255)]),([8,31,992,1082401,4357252,8659208,17809936,32505856],[(1024,301753),(1024,67255)]),([8,31,992,1082401,4357252,8659208,21648020,32505856],[(1024,69928),(1024,78305)]),([8,31,992,1082401,4357252,8659208,21659284,32505856],[(1024,301753),(1024,69928),(1025,66034),(1025,450233)]),([8,31,992,1082401,4357252,8659208,25977624,32505856],[(1024,301753),(1024,67051),(1025,98803),(1025,449209)]),([8,31,992,1082401,5214340,6494406,8659208,32505856],[(72,0),(1024,666040),(1024,66995)]),([8,31,992,1082401,5214340,7313606,8659208,32505856],[(72,0),(1024,712999),(1024,67255),(1025,300532)]),([8,31,992,1082401,5214340,8659208,25977624,32505856],[(72,0),(1024,301753),(1024,66995),(1025,436723)]),([8,31,992,1082401,5214340,8659208,31389629,32505856],[(72,0),(1024,301753),(1024,69928)]),([8,31,992,1082431,2164802,5214340,8659208,32505856],[(72,0),(96,0),(1024,504102),(1024,65832),(1025,70952)]),([8,31,992,1082431,3115074,4329604,8659208,32505856],[(1024,503078),(1024,65832),(1025,70952)])]
def b99 : List Row := [([8,31,992,1113121,2164802,4329604,8659208,9412872,17318416,32505856],[(96,0),(200,0),(272,0)]),([8,31,992,1113121,2164802,4329604,8659208,17318416,32505856,33521664],[(96,0),(216,0),(304,0)]),([8,31,992,1113121,2164802,4329604,9412872,17318416,32505856],[(82,0),(106,0),(138,0),(201,0),(230,0),(305,0)]),([8,31,992,1113121,2164802,4329604,9412872,32505856],[(1024,444710),(1024,69928)]),([8,31,992,1113121,4329604,8659208,17333776,32505856],[(168,0),(1024,100024),(1024,67255),(1025,450233)]),([8,31,992,1113121,4329604,9412872,17318416,32505856],[(1024,100024),(1024,67255)]),([8,31,992,2065441,2164802,4329604,8659208,17333776],[(1024,440819),(1024,88545),(1025,67255)]),([8,31,992,2065441,2164802,4329604,8682760,17318416,32505856],[]),([8,31,992,2164802,3247203,5214340,8659208,32505856],[(96,0),(1024,502056),(1024,504102),(1025,82420),(1025,437944)]),([8,31,992,2164802,4329604,8659208,17333776,32539681],[(1024,440824),(1024,83425)]),([8,31,992,2164802,5214340,8659208,32472030,32505856],[(1024,300525),(1024,69928)]),([8,31,992,3115074,4329604,5412005,8659208,32505856],[(1024,66034),(1024,502055)]),([8,31,992,3115074,4329604,8659208,32472030,32505856],[(1024,300524),(1024,69928)]),([8,31,992,4329604,4357252,8659208,17318416,32539681],[(112,0),(168,0),(1024,99832),(1024,78305),(1025,66231)]),([8,31,992,4329604,8659208,17318416,32539681,33521664],[(128,0),(1024,502195),(1024,67063),(1025,76471),(1025,273080)]),([8,31,992,4329604,8659208,17318416,32539681,33522687],[(128,0),(1024,502195),(1024,67063)]),([8,31,992,4329604,8659208,17333776,32472030,32505856],[(1024,100024),(1024,67255)]),([8,31,992,4329604,8659208,17333776,32505856,32539681],[(1024,99992),(1024,67223)]),([8,31,992,4329604,8659208,17333776,32539681],[(2,0),(10,0),(57,0),(113,0),(129,0),(145,0),(1024,67063),(1024,99832),(1024,83425),(1025,450233),(1025,66231),(1025,67255),(1025,268984)]),([8,31,996,31744,1015808,1082401,2164802,8659208,17318416,32505856],[(72,0),(272,0)]),([8,31,1023,31744,4329604,8659208,17318416,32539681],[(1024,281062),(1024,67063),(1025,71351)]),([8,31,1023,1082401,4329604,8659208,17333776,32505856],[(1024,281062),(1024,67255),(1025,67255)]),([8,31,1023,1082401,4357252,8659208,17318416,32505856],[(1024,281062),(1024,67051),(1025,67255),(1025,71147)]),([8,31,8192,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[])]
def t95 : BT := .nd (blockTree b98) [8,31,992,1082431,4329604,8659208,17333776,32505856] (blockTree b99)
def t96 : BT := .nd t94 [8,31,992,1082401,3247203,5214340,8659208,32505856] t95
def b100 : List Row := [([8,31,8192,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[(128,0)]),([8,31,9184,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(96,0),(128,0),(272,0)]),([8,31,31744,32736,4329604,8659208,17318416,32539681],[(168,0),(1024,99832),(1024,67063),(1025,437944)]),([8,31,31744,32768,1082401,2164802,4330468,8659208,17318416,32505856],[]),([8,31,31744,32768,1082401,2165730,4329604,8659208,17318416,32505856],[]),([8,31,31744,32768,1083361,2164802,4329604,8659208,17318416,32505856],[(128,0)]),([8,31,31744,32768,4330468,8659208,17318416,32505856],[(1024,98968),(1024,66199)]),([8,31,31744,65536,4330468,8659208,17318416],[(1024,66022),(1024,98803),(1024,71137),(1025,67255),(1025,437944)]),([8,31,31744,66528,4329604,8659208,17318416],[(168,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,279224)]),([8,31,31744,1015808,1082401,1083361,2164802,4329604,8659208,33047056],[]),([8,31,31744,1015808,1082401,1083361,2164802,4329604,17318416,32776456],[(168,0)]),([8,31,31744,1015808,1082401,1083361,2164802,8659208,17318416,32641156],[(96,0),(168,0)]),([8,31,31744,1015808,1082401,2097152,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,2098144,4329604,8659208,17318416,32505856],[(272,0)]),([8,31,31744,1015808,1082401,2164802,2165730,4329604,8659208,33047056],[]),([8,31,31744,1015808,1082401,2164802,2165730,4329604,17318416,32776456],[]),([8,31,31744,1015808,1082401,2164802,2165730,8659208,17318416,32641156],[(128,0)]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,32641156],[]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,32776456],[]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,33047056],[(272,0)]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[]),([8,31,31744,1015808,1082401,2164802,4330468,8659208,25977624,32505856],[]),([8,31,31744,1015808,1082401,2164802,8659944,32641156],[(1024,69896),(1024,511238)]),([8,31,31744,1015808,1082401,2164802,17318896,32641156],[(1024,88325),(1024,510049)])]
def b101 : List Row := [([8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32776456],[]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,33047056],[(272,0)]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,25977624,32505856],[]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,32505856,33047056],[]),([8,31,31744,1015808,1082401,2165730,4329604,8659208,33047056],[(1024,301125),(1024,296056)]),([8,31,31744,1015808,1082401,2165730,4329604,17318416,32505856,32776456],[]),([8,31,31744,1015808,1082401,2165730,4329604,17318416,32776456],[(254,0),(1024,117217)]),([8,31,31744,1015808,1082401,2165730,4330468,8659208,17318416,32505856],[(272,0)]),([8,31,31744,1015808,1082401,2165730,4357252,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,2165730,5214340,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,2165730,8659208,12988812,17318416,32505856],[]),([8,31,31744,1015808,1082401,2165730,8659208,17318416,32505856,32641156],[]),([8,31,31744,1015808,1082401,2165730,8659208,33047056],[(1024,301125),(1024,317506)]),([8,31,31744,1015808,1082401,2165730,17318416,32776456],[(1024,284738),(1024,301125)]),([8,31,31744,1015808,1082401,2194498,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,3115074,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,3247203,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,3248099,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,4329604,8659208,17318896,32573506],[(1024,78117),(1024,83237)]),([8,31,31744,1015808,1082401,4329604,8659944,17318416,32573506],[(1024,69896),(1024,83618),(1024,309927)]),([8,31,31744,1015808,1082431,2164802,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1083361,2097152,4329604,8659208,17318416,32505856],[(128,0)])]
def t97 : BT := .nd (blockTree b100) [8,31,31744,1015808,1082401,2164831,4330468,8659208,17318416,32505856] (blockTree b101)
def b102 : List Row := [([8,31,31744,1015808,1083361,2164802,4329604,8659208,17318416,32776456],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,17318416,33047056],[(272,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,25977624,32505856],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,32505856,33047056],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,8659208,33047056],[(129,0),(1024,300101),(1024,295032)]),([8,31,31744,1015808,1083361,2164802,4329604,9412872,17318416,32505856],[]),([8,31,31744,1015808,1083361,2164802,4329604,17318416,32505856,32776456],[(128,0)]),([8,31,31744,1015808,1083361,2164802,4329604,17318416,32776456],[(128,0),(129,0),(246,0)]),([8,31,31744,1015808,1083361,2164802,4330468,8659208,17318416,32505856],[(272,0)]),([8,31,31744,1015808,1083361,2164802,4357252,8659208,17318416,32505856],[]),([8,31,31744,1015808,1083361,2164802,5214340,8659208,17318416,32505856],[]),([8,31,31744,1015808,1083361,2164802,8659208,12988812,17318416,32505856],[(128,0)]),([8,31,31744,1015808,1083361,2164802,8659208,17318416,32505856,32641156],[(128,0)]),([8,31,31744,1015808,1083361,2164802,8659208,33047056],[(1024,317505),(1024,300101)]),([8,31,31744,1015808,1083361,2164802,17318416,32776456],[(1024,284737),(1024,300101)]),([8,31,31744,1015808,1083361,2164831,4329604,8659208,17318416,32505856],[(128,0)]),([8,31,31744,1015808,1083361,2165730,4329604,8659208,17318416,32505856],[(272,0)]),([8,31,31744,1015808,1083361,2194498,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1083361,3115074,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1083361,3247203,4329604,8659208,17318416,32505856],[(128,0)]),([8,31,31744,1015808,1083361,3248099,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,1113121,2164802,4330468,8659208,17318416,32505856],[]),([8,31,31744,1015808,1113121,2165730,4329604,8659208,17318416,32505856],[])]
def b103 : List Row := [([8,31,31744,1015808,2164802,4329604,8659944,17318416,32539681],[(1024,69896),(1024,309894),(1024,508166)]),([8,31,31744,1015808,4330468,8659208,17318416,32539681],[(1024,67206),(1024,72321)]),([8,31,31744,1015808,4330468,8659208,17318416,32573506],[(1024,66034),(1024,71298),(1025,67255)]),([8,31,31744,1048575,1082401,4330468,8659208,17318416],[(1024,67046),(1024,72161)]),([8,31,31744,1082401,1083361,2164802,4329604,8659208,17809936,32505856],[(128,0)]),([8,31,31744,1082401,1083361,2164802,4329604,9412872,17318416,32505856],[]),([8,31,31744,1082401,1083361,2164802,5214340,8659208,17318416,32505856],[(72,0)]),([8,31,31744,1082401,1083361,3115074,4329604,8659208,17318416,32505856],[]),([8,31,31744,1082401,2097152,4330468,8659208,17318416],[(1024,444907),(1024,67046)]),([8,31,31744,1082401,2164802,2165730,5214340,8659208,17318416,32505856],[]),([8,31,31744,1082401,2164802,3115074,4330468,8659208,17318416,32505856],[]),([8,31,31744,1082401,2164802,4330468,5214340,8659208,17318416,32505856],[]),([8,31,31744,1082401,2164802,4330468,8659208,9412872,17318416,32505856],[]),([8,31,31744,1082401,2164802,4330468,8659208,17318416,17809936,32505856],[(216,0)]),([8,31,31744,1082401,2164802,4330468,8659208,17318416,32505856,33521664],[]),([8,31,31744,1082401,2164802,5214340,8659944,32505856],[(1024,69896),(1024,509190)]),([8,31,31744,1082401,2164802,5214340,17318896,32505856],[(1024,83205),(1024,509025)]),([8,31,31744,1082401,2165730,3115074,4329604,8659208,17318416,32505856],[]),([8,31,31744,1082401,2165730,4329604,5214340,8659208,17318416,32505856],[]),([8,31,31744,1082401,2165730,4329604,8659208,9412872,17318416,32505856],[]),([8,31,31744,1082401,2165730,4329604,8659208,17318416,17809936,32505856],[(216,0)]),([8,31,31744,1082401,2165730,4329604,8659208,17318416,32505856,33521664],[]),([8,31,31744,1082401,2165730,4329604,8659208,33047056],[(1024,444907),(1024,83425)]),([8,31,31744,1082401,2165730,4329604,17318416,32776456],[(1024,444907),(1024,83425)])]
def t98 : BT := .nd (blockTree b102) [8,31,31744,1015808,2164802,4329604,8659208,17318896,32539681] (blockTree b103)
def t99 : BT := .nd t97 [8,31,31744,1015808,1083361,2164802,4329604,8659208,17318416,32505856] t98
def t100 : BT := .nd t96 [8,31,8192,1015808,1082401,2165730,4329604,8659208,17318416,32505856] t99
def b104 : List Row := [([8,31,31744,1082401,2165730,8659208,33047056],[(1024,83425),(1024,280642),(1024,301125),(1025,66034),(1025,98803),(1025,99603),(1025,661177)]),([8,31,31744,1082401,2165730,17318416,32776456],[(1024,83425),(1024,280642),(1024,301125),(1025,66034),(1025,98968),(1025,300532)]),([8,31,31744,1082401,3115074,4329604,4330468,8659208,17318416,32505856],[]),([8,31,31744,1082401,3115074,4329604,8659944,32505856],[(1024,704792),(1024,69896)]),([8,31,31744,1082401,3115074,4329604,17318896,32505856],[(1024,704793),(1024,508001)]),([8,31,31744,1082401,3115074,4330468,8659208,17318416,32505856],[(217,0),(254,0),(1024,73345),(1024,66199),(1024,302181)]),([8,31,31744,1082401,3115074,8659231,17318416,32505856],[(1024,302149),(1024,496706),(1025,266536)]),([8,31,31744,1082401,3115074,17318416,25977624,32505856],[(1024,72997),(1024,496706),(1025,300532)]),([8,31,31744,1082401,4330468,8659208,16236015,32505856],[(1024,712999),(1024,67046)]),([8,31,31744,1082401,4330468,8659208,17318416,32505856],[(1024,67046),(1024,72161)]),([8,31,31744,1082401,4330468,8659208,17318416,32539681],[(1024,100024),(1024,67046)]),([8,31,31744,1082401,4330468,8659208,17318416,32641156],[(1024,100024),(1024,73185),(1025,66231),(1025,88761)]),([8,31,31744,1082401,4330468,8659208,17318431,32505856],[(1024,268984),(1024,67046),(1025,70118),(1025,88761)]),([8,31,31744,1082401,4330468,8659208,17333776,32505856],[(1024,67046),(1024,72161),(1025,78130),(1025,450233)]),([8,31,31744,1082401,4330468,8659208,25977624,32505856],[(1024,301753),(1024,67046),(1025,98803),(1025,285369)]),([8,31,31744,1082401,4330468,17318416,24895223,32505856],[(1024,711778),(1024,67046)]),([8,31,31744,1082401,4330468,17318416,25977624,32505856],[(1024,100024),(1024,67046),(1025,300532),(1025,318137)]),([8,31,31744,1082401,4358116,8659208,17318416,32505856],[(168,0),(1024,67046),(1024,72161),(1025,449208)]),([8,31,31744,1082401,8659208,17318416,29223963,32505856],[(128,0),(1024,496706),(1024,72161)]),([8,31,31744,1083361,2164802,4329604,8659208,9412872,17318416,32505856],[(96,0)]),([8,31,31744,1083361,2164802,4329604,8659208,17318416,17809936,32505856],[(96,0),(216,0)]),([8,31,31744,1083361,2164802,4329604,8659208,17318416,32505856,33521664],[(96,0)]),([8,31,31744,1083361,2164802,4329604,8659208,17809936,32505856],[(96,0),(97,0),(1024,267960),(1024,300101),(1024,295027)]),([8,31,31744,1083361,2164802,4329604,9412872,17318416,32505856],[(238,0)]),([8,31,31744,1083361,2164802,8659208,17809936,32505856],[(1024,312385),(1024,300101)])]
def b105 : List Row := [([8,31,31744,1083361,4329604,8659208,17809936,32505856],[(1024,267960),(1024,67255)]),([8,31,31744,1083361,4329604,9412872,17318416,32505856],[(1024,100024),(1024,67255)]),([8,31,31744,1083361,4330468,8659208,17318416,32505856],[(1024,67046),(1024,83425),(1025,285368),(1025,295400),(1025,302571)]),([8,31,31744,1113121,4330468,8659208,17318416,32505856],[(1024,67046),(1024,72161),(1025,437944)]),([8,31,31744,2065441,2164802,4329604,8659208,17318896,32505856],[(1024,66856),(1024,78117),(1024,437747)]),([8,31,31744,2065441,2164802,4329604,8659944,17318416,32505856],[(1024,69896),(1024,309734)]),([8,31,31744,2065441,2164802,4330468,8659208,17318416],[(1024,269811),(1024,73185),(1025,67255)]),([8,31,31744,2164802,4330468,8659208,17318416,32539681],[(1024,269816),(1024,73185)]),([8,31,31744,4329604,4330468,8659208,17318416,32539681],[(1024,99832),(1024,73185),(1025,66231)]),([8,31,31744,4329604,8659208,17318416,32539681,33521664],[(1024,301561),(1024,67063),(1025,71351),(1025,437944)]),([8,31,31744,4329604,8659208,17318416,32539681,33553439],[(1024,496915),(1024,67063)]),([8,31,31744,4330468,8659208,17318416,32472030,32505856],[(1024,67255),(1024,72161)]),([8,31,31744,4330468,8659208,17318416,32505856,32539681],[(1024,67046),(1024,72161)]),([8,31,31744,4330468,8659208,17318416,32539681],[(2,0),(129,0),(1024,67046),(1024,99832),(1024,72161),(1025,285368),(1025,67255),(1025,318137),(1025,437944)]),([8,31,31775,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[]),([8,31,31775,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[]),([8,31,31775,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[]),([8,31,31775,1082401,2165730,8659208,17318416,32505856],[(1024,444907),(1024,280642),(1025,66199),(1025,263603)]),([8,31,31775,1082401,3115074,8659208,17318416,32505856],[(1024,302149),(1024,496706),(1025,66199)]),([8,31,31775,1082401,4330468,8659208,17318416,32505856],[(1024,281062),(1024,100024),(1025,67255),(1025,71147)]),([8,31,32736,1015808,1082401,2164802,4329604,8659944],[(1024,286347),(1024,69896),(1025,431608)]),([8,31,32736,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[(272,0)]),([8,31,32736,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[(96,0),(272,0)]),([8,31,32736,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[(128,0),(272,0)])]
def t101 : BT := .nd (blockTree b104) [8,31,31744,1083361,2164802,9412872,17318416,32505856] (blockTree b105)
def b106 : List Row := [([8,31,32736,1082401,4330468,8659208,17318416,32505856],[(168,0),(1024,67255),(1024,83425)]),([8,31,32736,1082401,4357252,8659208,17318416,32505856],[(1024,281062),(1024,66863),(1025,80180)]),([8,31,32736,1083361,4329604,8659208,17318416,32505856],[(1024,300729),(1024,67255),(1025,273080),(1025,295403)]),([8,31,32736,1113121,4329604,8659208,17318416,32505856],[(168,0),(1024,100024),(1024,67255),(1025,437944)]),([8,31,1015808,1016800,1082401,2164802,8659208,33047056],[(168,0),(1024,665669),(1024,496915),(1025,66034),(1025,315065)]),([8,31,1015808,1048575,1082401,2164802,4329604,8659944],[(1024,286347),(1024,69896)]),([8,31,1015808,1048575,1082401,2165730,8659208,17318416],[(1024,450187),(1024,301125)]),([8,31,1015808,1048575,1083361,2164802,8659208,17318416],[(1024,450182),(1024,300101)]),([8,31,1015808,1082401,1083361,2164802,4357252,8659208,17318416,32505856],[]),([8,31,1015808,1082401,1083361,2164802,8659208,33047056],[(168,0),(1024,497075),(1024,302149),(1025,70283)]),([8,31,1015808,1082401,1083361,2194498,4329604,8659208,17318416,32505856],[]),([8,31,1015808,1082401,1113121,2164802,4330468,8659208,17318416,32505856],[]),([8,31,1015808,1082401,1113121,2165730,4329604,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2164802,2165730,4357252,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2164802,2165730,8659208,33047056],[(168,0),(1024,508993),(1024,302149),(1025,70316)]),([8,31,1015808,1082401,2164802,2194498,4330468,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2164802,4329604,8659720,32505856],[(1024,496915),(1024,660760)]),([8,31,1015808,1082401,2164802,4329604,8659944,17333776,32505856],[(1024,309734),(1024,309894),(1024,309927),(1024,508166),(1024,509190),(1024,678150)]),([8,31,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,69896),(1024,502035)]),([8,31,1015808,1082401,2164802,4329604,8659944,32505887],[(1024,665880),(1024,69896),(1025,117176)]),([8,31,1015808,1082401,2164802,4329604,8659944,32641156],[(1024,511238),(1024,502035)]),([8,31,1015808,1082401,2164802,4329604,8659944,33521664],[(1024,665880),(1024,69896),(1025,431608)]),([8,31,1015808,1082401,2164802,4329604,12989420,32505856],[(1024,511238),(1024,502035)]),([8,31,1015808,1082401,2164802,4329604,24894487,32505856],[(1024,69896),(1024,502035)])]
def b107 : List Row := [([8,31,1015808,1082401,2164802,4330468,4358116,8659208,17318416,32505856],[(308,0)]),([8,31,1015808,1082401,2164802,4330468,8659208,17318416,17333776,32505856],[(216,0)]),([8,31,1015808,1082401,2164802,4330468,8659208,32641156],[(1024,665896),(1024,502195),(1025,70967),(1025,71991)]),([8,31,1015808,1082401,2164802,5214340,8659944,32505856],[(1024,665880),(1024,69896),(1025,431604)]),([8,31,1015808,1082401,2164802,5412005,8659944,32505856],[(1024,69896),(1024,502035),(1025,65637)]),([8,31,1015808,1082401,2164802,6494406,8659944,32505856],[(1024,69896),(1024,502035),(1025,66661)]),([8,31,1015808,1082401,2164802,8659208,8659944,32641156],[(1024,511270),(1024,69912),(1025,70072)]),([8,31,1015808,1082401,2164802,8659208,32641156,33553439],[(1024,666040),(1024,502195)]),([8,31,1015808,1082401,2164802,8659208,33047056,33553439],[(1024,508993),(1024,302149)]),([8,31,1015808,1082401,2164802,8659720,17318416,32505856],[(1024,508993),(1024,496915)]),([8,31,1015808,1082401,2164802,8659944,17318416,32641156],[(1024,665864),(1024,502035)]),([8,31,1015808,1082401,2164802,8659944,25977624,32505856],[(1024,269381),(1024,502035),(1025,65637),(1025,66661)]),([8,31,1015808,1082401,2164802,8659944,29224827,32505856],[(1024,269381),(1024,502035)]),([8,31,1015808,1082401,2164802,8659944,32505856,32641156],[(1024,69896),(1024,502035),(1025,431769)]),([8,31,1015808,1082401,2164802,8659944,32641156],[(2,0),(1024,69896),(1024,502035),(1024,511238),(1025,70072),(1025,431604),(1025,431769),(1025,436723),(1025,437944)]),([8,31,1015808,1082401,2164802,8682760,17318416,32641156],[(1024,660749),(1024,72997)]),([8,31,1015808,1082401,2164831,4329604,8659944,32505856],[(1024,712967),(1024,66824),(1025,103847),(1025,104883)]),([8,31,1015808,1082401,2165314,8659208,17318416,32505856],[(128,0),(1024,508993),(1024,301125)]),([8,31,1015808,1082401,2165730,2194498,4329604,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2165730,2195426,4329604,8659208,17318416,32505856],[(300,0)]),([8,31,1015808,1082401,2165730,4329604,4357252,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2165730,4329604,8659208,17318416,17333776,32505856],[(216,0)]),([8,31,1015808,1082401,2165730,4329604,8659208,33047056],[(1024,301496),(1024,502195)]),([8,31,1015808,1082401,2165730,4357252,8659208,17318416,32505856],[(246,0),(1024,66199),(1024,78305),(1024,491635)])]
def t102 : BT := .nd (blockTree b106) [8,31,1015808,1082401,2164802,4330468,4357252,8659208,17318416,32505856] (blockTree b107)
def t103 : BT := .nd t101 [8,31,32736,1082401,2164802,4329604,8659944,32505856] t102
def b108 : List Row := [([8,31,1015808,1082401,2165730,8659208,16236015,32505856],[(1024,69927),(1024,309314)]),([8,31,1015808,1082401,2165730,8659208,17318416,32505856],[(1024,309314),(1024,301125)]),([8,31,1015808,1082401,2165730,8659208,17318416,33047056],[(1024,502195),(1024,309314),(1025,66873)]),([8,31,1015808,1082401,2165730,8659208,17318416,33521664],[(1024,309314),(1024,301125),(1025,66034),(1025,274097),(1025,306865)]),([8,31,1015808,1082401,2165730,8659208,17809936,32505856],[(1024,309314),(1024,301125),(1025,66036),(1025,273713),(1025,306865)]),([8,31,1015808,1082401,2165730,8659208,18400817,32505856],[(1024,301125),(1024,309314),(1025,267564)]),([8,31,1015808,1082401,2165730,8659208,25977624,32505856],[(1024,301125),(1024,309314),(1025,65637),(1025,66661)]),([8,31,1015808,1082401,2165730,8659208,32505856,33047056],[(1024,301125),(1024,309314),(1025,66201)]),([8,31,1015808,1082401,2165730,8659208,33047056],[(2,0),(129,0),(1024,309314),(1024,502195),(1024,301125),(1025,66034),(1025,66201),(1025,70283),(1025,70316),(1025,436723),(1025,437944)]),([8,31,1015808,1082401,2165730,8659231,17318416,32505856],[(1024,309314),(1024,301125)]),([8,31,1015808,1082401,2165730,9412872,17318416,32505856],[(1024,309314),(1024,301125),(1025,273713),(1025,274097)]),([8,31,1015808,1082401,2165730,17318416,24895223,32505856],[(1024,309314),(1024,301125)]),([8,31,1015808,1082401,2165730,17318416,25977624,32505856],[(1024,666040),(1024,309314)]),([8,31,1015808,1082401,2165730,17318416,32505856,32776456],[(1024,301125),(1024,309314)]),([8,31,1015808,1082401,2194498,4329604,4330468,8659208,17318416,32505856],[]),([8,31,1015808,1082401,2194498,4330468,8659208,17318416,32505856],[(217,0),(254,0),(1024,66199),(1024,73185)]),([8,31,1015808,1082401,2194498,8659231,17318416,32505856],[(1024,302149),(1024,496915)]),([8,31,1015808,1082401,2194498,17318416,25977624,32505856],[(1024,72997),(1024,496915),(1025,300532)]),([8,31,1015808,1082401,3115074,4329604,8659944,32505856],[(1024,69896),(1024,508166),(1025,431604)]),([8,31,1015808,1082401,3116002,8659208,17318416,32505856],[(1024,309314),(1024,301125),(1025,66034)]),([8,31,1015808,1082401,3247203,4329604,8659944,32505856],[(1024,69896),(1024,502035),(1025,436723)]),([8,31,1015808,1082401,3248099,8659208,17318416,32505856],[(1024,309314),(1024,301125)]),([8,31,1015808,1082401,4329604,6494406,8659944,32505856],[(1024,67255),(1024,502035),(1025,678585)]),([8,31,1015808,1082401,4329604,8659944,25977624,32505856],[(1024,67255),(1024,268985),(1025,436723)]),([8,31,1015808,1082401,4329604,8659944,31389629,32505856],[(1024,268985),(1024,69896)])]
def b109 : List Row := [([8,31,1015808,1082401,4330468,8659208,25977624,32505856],[(1024,301753),(1024,67255),(1025,436723)]),([8,31,1015808,1082401,8659208,12989420,17318416,32505856],[(96,0),(168,0),(1024,309943),(1024,301753)]),([8,31,1015808,1082401,8659208,17318416,31388701,32505856],[(1024,66863),(1024,301125)]),([8,31,1015808,1082431,2164802,4329604,8659944,32505856],[(1024,511238),(1024,65800),(1025,103847)]),([8,31,1015808,1082913,2164802,8659208,17318416,32505856],[(128,0),(1024,309313),(1024,300101)]),([8,31,1015808,1083361,1113121,2164802,4329604,8659208,17318416,32505856],[(128,0)]),([8,31,1015808,1083361,1114081,2164802,4329604,8659208,17318416,32505856],[(128,0),(292,0)]),([8,31,1015808,1083361,2164802,2194498,4329604,8659208,17318416,32505856],[(96,0)]),([8,31,1015808,1083361,2164802,4329604,4357252,8659208,17318416,32505856],[(96,0)]),([8,31,1015808,1083361,2164802,4329604,8659208,17318416,17333776,32505856],[(96,0),(216,0)]),([8,31,1015808,1083361,2164802,4329604,8659208,33047056],[(1024,300472),(1024,497075)]),([8,31,1015808,1083361,2164802,4357252,8659208,17318416,32505856],[(238,0),(1024,491635)]),([8,31,1015808,1083361,2164802,5412005,8659208,32505856],[(96,0),(1024,309313),(1024,69926),(1025,65637),(1025,301547)]),([8,31,1015808,1083361,2164802,8659208,16236015,32505856],[(1024,69926),(1024,309313)]),([8,31,1015808,1083361,2164802,8659208,17318416,32505856],[(1024,309313),(1024,300101)]),([8,31,1015808,1083361,2164802,8659208,17318416,33047056],[(1024,508993),(1024,497075),(1025,65849)]),([8,31,1015808,1083361,2164802,8659208,17318416,33521664],[(1024,309313),(1024,300101),(1025,66034)]),([8,31,1015808,1083361,2164802,8659208,17809936,32505856],[(1024,309313),(1024,300101),(1025,66036)]),([8,31,1015808,1083361,2164802,8659208,19483218,32505856],[(96,0),(1024,309313),(1024,300101),(1025,268587),(1025,301547)]),([8,31,1015808,1083361,2164802,8659208,25977624,32505856],[(1024,300101),(1024,309313),(1025,65637),(1025,66661)]),([8,31,1015808,1083361,2164802,8659208,32505856,33047056],[(1024,309313),(1024,300101),(1025,66201)]),([8,31,1015808,1083361,2164802,8659208,33047056],[(2,0),(129,0),(1024,309313),(1024,497075),(1024,300101),(1025,66034),(1025,66201),(1025,70283),(1025,70316),(1025,436723),(1025,437944)]),([8,31,1015808,1083361,2164802,8659231,17318416,32505856],[(1024,309313),(1024,300101)]),([8,31,1015808,1083361,2164802,9412872,17318416,32505856],[(1024,309313),(1024,300101)])]
def t104 : BT := .nd (blockTree b108) [8,31,1015808,1082401,4330468,6494406,8659208,32505856] (blockTree b109)
def b110 : List Row := [([8,31,1015808,1083361,2164802,17318416,25977624,32505856],[(1024,309313),(1024,497075)]),([8,31,1015808,1083361,2164802,17318416,32505856,32776456],[(1024,309313),(1024,300101)]),([8,31,1015808,1083361,2165730,8659208,17318416,32505856],[(1024,508993),(1024,300101),(1025,262562)]),([8,31,1015808,1083361,2194498,4329604,8659208,17318416,32505856],[(217,0),(238,0),(1024,300101),(1024,491635)]),([8,31,1015808,1083361,2194498,8659208,17318416,32505856],[(1024,677953),(1024,300101)]),([8,31,1015808,1083361,3115074,8659208,17318416,32505856],[(1024,309313),(1024,300101),(1025,66034)]),([8,31,1015808,1083361,3247203,4329604,8659208,32505856],[(96,0),(1024,497075),(1024,69928),(1025,302571),(1025,302731),(1025,436723)]),([8,31,1015808,1083361,3247203,8659208,17318416,32505856],[(128,0),(1024,302149),(1024,497075)]),([8,31,1015808,1083361,3248099,8659208,17318416,32505856],[(1024,710722),(1024,300101),(1025,69931)]),([8,31,1015808,1083361,4329604,8659208,25977624,32505856],[(1024,300729),(1024,67255),(1025,436723)]),([8,31,1015808,1083361,4357252,8659208,17318416,32505856],[(1024,300729),(1024,67255)]),([8,31,1015808,1083361,8659208,12988812,17318416,32505856],[(96,0),(1024,300729),(1024,67255)]),([8,31,1015808,1083361,8659208,17318416,19483218,32505856],[(1024,309313),(1024,301753),(1025,65839)]),([8,31,1015808,1083361,8659208,17318416,31389629,32505856],[(1024,67255),(1024,300101)]),([8,31,1015808,1113121,2164802,2165730,4329604,8659208,17318416,32505856],[]),([8,31,1015808,1113121,2164802,4329604,4330468,8659208,17318416,32505856],[]),([8,31,1015808,1113121,2164802,4330468,8659208,17318416,32505856],[(217,0),(254,0)]),([8,31,1015808,1113121,2164802,8659231,17318416,32505856],[(1024,509231),(1024,302149)]),([8,31,1015808,1113121,2164802,17318416,25977624,32505856],[(1024,508993),(1024,72997),(1025,301753)]),([8,31,1015808,1113121,2165730,4329604,8659208,17318416,32505856],[(217,0),(246,0),(1024,301125),(1024,491635)]),([8,31,1015808,1113121,2165730,8659208,17318416,32505856],[(1024,677953),(1024,301125)]),([8,31,1015808,1113121,4330468,8659208,17318416,32505856],[(1024,67255),(1024,100024)]),([8,31,1015808,2164802,3247203,4329604,8659944,32505856],[(1024,69896),(1024,502035),(1025,437944)]),([8,31,1015808,2164802,3248099,8659208,17318416,32505856],[(1024,309313),(1024,300101)])]
def b111 : List Row := [([8,31,1015808,2164802,4329604,8659944,25977624,32505856],[(1024,502035),(1024,66034),(1025,437944)]),([8,31,1015808,2164802,4329604,8659944,32472030,32505856],[(1024,267764),(1024,69896)]),([8,31,1015808,2164802,4330468,5412005,8659208,32505856],[(1024,511270),(1024,66034),(1025,71981)]),([8,31,1015808,2164802,4330468,8659208,25977624,32505856],[(1024,300532),(1024,66034),(1025,437944)]),([8,31,1015808,2164802,8659208,12989420,17318416,32505856],[(96,0),(168,0),(1024,309746),(1024,300532)]),([8,31,1015808,2164802,8659208,17318416,32471070,32505856],[(1024,65839),(1024,300101)]),([8,31,1015808,2165730,3247203,4329604,8659208,32505856],[(96,0),(1024,69928),(1024,309745),(1025,302764),(1025,437944)]),([8,31,1015808,2165730,3247203,8659208,17318416,32505856],[(128,0),(1024,309745),(1024,302149),(1025,311796)]),([8,31,1015808,2165730,3248099,8659208,17318416,32505856],[(1024,508993),(1024,300101),(1025,69932)]),([8,31,1015808,2165730,4329604,8659208,25977624,32505856],[(1024,300532),(1024,66034),(1025,437944)]),([8,31,1015808,2165730,4357252,8659208,17318416,32505856],[(1024,66199),(1024,98803)]),([8,31,1015808,2165730,8659208,12988812,17318416,32505856],[(96,0),(1024,66034),(1024,300532)]),([8,31,1015808,2165730,8659208,17318416,18400817,32505856],[(1024,508993),(1024,300532),(1025,66863)]),([8,31,1015808,2165730,8659208,17318416,32472030,32505856],[(1024,66034),(1024,301125)]),([8,31,1015808,2194498,4330468,8659208,17318416,32505856],[(1024,66199),(1024,98803)]),([8,31,1015808,4330468,8659208,17318416,32505856,32539681],[(1024,309911),(1024,99992)]),([8,31,1015808,4357252,8659208,17318416,32505856,32539681],[(1024,301721),(1024,66863)]),([8,31,1015839,1082401,2164802,4329604,8659944,32505856],[(1024,502035),(1024,69896),(1025,104883),(1025,117176)]),([8,31,1016800,1082401,2164802,8659208,17318416,33521664],[(128,0),(1024,309937),(1024,302149)]),([8,31,1016800,1082401,2165730,8659208,17318416,32505856],[(1024,281062),(1024,301125),(1025,263603)]),([8,31,1016800,1082401,3115074,8659208,17318416,32505856],[(128,0),(1024,302149),(1024,496706),(1025,315065)]),([8,31,1082401,1083361,2164802,8659208,17809936,32505856],[(128,0),(1024,302149),(1024,660920),(1025,70123)]),([8,31,1082401,1083361,3115074,8659208,17318416,32505856],[(128,0),(1024,302149),(1024,496706),(1025,67051)]),([8,31,1082401,2164802,2165730,5214340,8659208,32505856],[(1024,502056),(1024,504102),(1025,437944)])]
def t105 : BT := .nd (blockTree b110) [8,31,1015808,2164802,4329604,5412005,8659944,32505856] (blockTree b111)
def t106 : BT := .nd t104 [8,31,1015808,1083361,2164802,17318416,24895223,32505856] t105
def t107 : BT := .nd t103 [8,31,1015808,1082401,2165730,6494406,8659208,32505856] t106
def t108 : BT := .nd t100 [8,31,31744,1082401,2165730,5214340,8659208,17318416,32505856] t107
def b112 : List Row := [([8,31,1082401,2164802,3115074,4329604,8659944,32505856],[(1024,69896),(1024,502035),(1025,445112)]),([8,31,1082401,2164802,4329604,5214340,8659944,32505856],[(1024,511238),(1024,502035)]),([8,31,1082401,2164802,4329604,8659944,32505856,32538623],[(1024,281067),(1024,69896)]),([8,31,1082401,2164802,4329604,8659944,32505856,33521664],[(1024,502035),(1024,69896),(1025,431769)]),([8,31,1082401,2164802,4330468,5214340,8659208,32505856],[(1024,502056),(1024,511270),(1025,70962),(1025,71986)]),([8,31,1082401,2164802,5214340,8659208,8659944,32505856],[(1024,504102),(1024,69907),(1025,70067)]),([8,31,1082401,2164802,5214340,8659208,32505856,33553439],[(1024,502195),(1024,504102)]),([8,31,1082401,2164802,5214340,8659944,17318416,32505856],[(1024,502024),(1024,504070)]),([8,31,1082401,2164802,5214340,8659944,32505856],[(1024,69896),(1024,504070),(1024,665880),(1025,70067),(1025,431604),(1025,431769),(1025,436723),(1025,437944)]),([8,31,1082401,2164802,5214340,8682760,17318416,32505856],[(1024,496909),(1024,72997)]),([8,31,1082401,2164802,8659208,17318416,32506848,33521664],[(96,0),(1024,302149),(1024,502040)]),([8,31,1082401,2164802,8659208,17809936,32505856,32506848],[(96,0),(1024,501829),(1024,505921),(1025,66199)]),([8,31,1082401,2164802,8659208,17809936,32505856,33553439],[(96,0),(1024,505921),(1024,302149)]),([8,31,1082401,2165730,3115074,4329604,8659208,32505856],[(1024,69928),(1024,502055),(1025,302769),(1025,445112)]),([8,31,1082401,2165730,3115074,8659208,17318416,32505856],[(128,0),(1024,302149),(1024,502195)]),([8,31,1082401,2165730,3116002,8659208,17318416,32505856],[(1024,502195),(1024,281062),(1025,69937)]),([8,31,1082401,2165730,4357252,8659208,17318416,32505856],[(1024,281062),(1024,78305)]),([8,31,1082401,2165730,5214340,8659208,17318416,32505856],[(1024,502195),(1024,666040)]),([8,31,1082401,2165730,8659208,17318416,17809936,32505856],[(1024,502195),(1024,309314),(1025,66868)]),([8,31,1082401,2165730,8659208,17318416,32505856,32538623],[(1024,444907),(1024,301125)]),([8,31,1082401,2165730,8659208,17318416,32505856,33521664],[(1024,309314),(1024,301125),(1025,66199)]),([8,31,1082401,2194498,4330468,8659208,17318416,32505856],[(1024,281062),(1024,73185)]),([8,31,1082401,2194498,5214340,8659208,17318416,32505856],[(1024,496915),(1024,72997)]),([8,31,1082401,2194498,5214340,8659208,32505856],[(1024,69928),(1024,498982),(1024,72997),(1025,69940),(1025,300697)]),([8,31,1082401,3115074,3116002,8659208,17318416,32505856],[(128,0),(1024,302149),(1024,496915),(1025,66034)])]
def b113 : List Row := [([8,31,1082401,3115074,4329604,8659208,8659944,32505856],[(1024,69928),(1024,502035)]),([8,31,1082401,3115074,4329604,8659208,32505856,33553439],[(1024,502195),(1024,69928)]),([8,31,1082401,3115074,4329604,8659944,17318416,32505856],[(1024,502023),(1024,503046)]),([8,31,1082401,3115074,4329604,8659944,32505856],[(1024,69896),(1024,502023),(1024,503046),(1025,70056),(1025,431604),(1025,431769),(1025,436723)]),([8,31,1082401,3115074,4329604,8682760,17318416,32505856],[(1024,496908),(1024,72997)]),([8,31,1082401,3115074,4330468,8659208,17318416,32505856],[(128,0),(1024,502195),(1024,666040)]),([8,31,1082401,3115074,4357252,8659208,17318416,32505856],[(128,0),(1024,496915),(1024,72997)]),([8,31,1082401,3115074,4357252,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69935),(1025,300532)]),([8,31,1082401,3115074,8659208,8659944,17318416,32505856],[(96,0),(1024,302149),(1024,501826)]),([8,31,1082401,3115074,8659208,17318416,32505856,32506848],[(96,0),(1024,660760),(1024,302149),(1025,66199)]),([8,31,1082401,3115074,8659208,17318416,32505856,33553439],[(96,0),(1024,501826),(1024,302149)]),([8,31,1082401,4329604,4330468,8659208,17333776,32505856],[(1024,281062),(1024,73185),(1025,66034)]),([8,31,1082401,4329604,8659208,17333776,32505856,33553439],[(1024,496915),(1024,67255)]),([8,31,1082401,4330468,4357252,8659208,17318416,32505856],[(1024,100024),(1024,73185)]),([8,31,1082401,4330468,4358116,8659208,17318416,32505856],[(1024,444907),(1024,72161),(1025,66034),(1025,285368)]),([8,31,1082401,4330468,8659208,17318416,17333776,32505856],[(128,0),(1024,67046),(1024,72161),(1025,300532),(1025,318137)]),([8,31,1082401,4330468,8659208,17318416,32505856,33521664],[(1024,502195),(1024,67255),(1025,67255)]),([8,31,1082401,4330468,8659208,17318416,32505856,33522687],[(1024,502195),(1024,67046)]),([8,31,1082401,4357252,4358116,8659208,17318416,32505856],[(1024,281062),(1024,73185),(1025,66034),(1025,449208)]),([8,31,1082401,4357252,8659208,17318416,32505856,33521664],[(1024,496915),(1024,66863),(1025,67255)]),([8,31,1082401,4357252,8659208,17318416,32505856,33553439],[(1024,496915),(1024,67051)]),([8,31,1082401,5214340,8659208,8659944,17318416,32505856],[(1024,66835),(1024,301753),(1025,66995)]),([8,31,1083361,2164802,3115074,8659208,17318416,32505856],[(72,0),(1024,309313),(1024,300101),(1025,268779),(1025,301547)]),([8,31,1083361,2164802,4329604,8659208,17809936,32505856],[(72,0),(1024,660920),(1024,300467)])]
def t109 : BT := .nd (blockTree b112) [8,31,1082401,3115074,4329604,4330468,8659208,32505856] (blockTree b113)
def b114 : List Row := [([8,31,1083361,2164802,8659208,17318416,32505856,32538623],[(1024,444902),(1024,300101)]),([8,31,1083361,2164802,8659208,17318416,32505856,33521664],[(1024,309313),(1024,300101),(1025,66199)]),([8,31,1083361,2164802,8659208,17809936,32505856],[(2,0),(73,0),(97,0),(1024,309313),(1024,660920),(1024,300101),(1025,66036),(1025,66199),(1025,70123),(1025,436723),(1025,437944)]),([8,31,1083361,4329604,8659208,17318416,32505856,33521664],[(1024,497075),(1024,67255),(1025,67255),(1025,273080)]),([8,31,1083361,4329604,8659208,17809936,32505856],[(97,0),(1024,67255),(1024,100024),(1024,300467),(1025,67255),(1025,273080),(1025,436723),(1025,437944)]),([8,31,1113121,4329604,8659208,17318416,32505856,33521664],[(1024,496915),(1024,67255),(1025,67255),(1025,437944)]),([8,31,2165730,4357252,8659208,17318416,32505856],[(1024,66027),(1024,98803),(1024,76257),(1025,311796),(1025,66034),(1025,66199)]),([8,31,2194498,4330468,8659208,17318416,32505856],[(1024,66022),(1024,98803),(1024,71137),(1025,442867),(1025,66034),(1025,66199)]),([8,1023,31744,1082431,4329604,8659208,17318416,32505856],[(1024,72997),(1024,66231),(1025,71147),(1025,71351)]),([8,1023,31775,1082401,4329604,8659208,17318416,32505856],[(1024,78310),(1024,67255)]),([8,31744,31775,1082401,4330468,8659208,17318416,32505856],[(1024,67046),(1024,72161),(1025,78130),(1025,437944)]),([8,31744,1015808,1082401,1082431,2165730,4329604,8659208,17318416,32505856],[]),([8,31744,1015808,1082401,2164802,4329604,4330468,8659208,17318431,32505856],[]),([8,31744,1015808,1082401,2164802,4329631,8659208,17318896,32505856],[(1024,491602),(1024,501842),(1024,507969),(1024,699479)]),([8,31744,1015808,1082401,2164802,4329631,17318896,32505856],[(1024,510017),(1024,711746)]),([8,31744,1015808,1082401,2164802,4330468,8659208,17318431],[(1024,450187),(1024,70278),(1025,122553)]),([8,31744,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[(217,0),(1024,70130),(1024,70327),(1024,70278),(1024,66199),(1024,491635)]),([8,31744,1015808,1082401,2164831,2165730,4329604,8659208,17318416,32505856],[(376,0)]),([8,31744,1015808,1082401,2164831,4329604,4330468,8659208,17318416,32505856],[]),([8,31744,1015808,1082401,2164831,8659208,17318416,32641156],[(1024,66840),(1024,72997),(1025,305652)]),([8,31744,1015808,1082401,2164831,8659208,32641156],[(1024,66856),(1024,496915),(1024,72994),(1025,301753),(1025,300532)]),([8,31744,1015808,1082401,4330468,8659208,17318431],[(1024,67239),(1024,100024),(1024,72321),(1025,437944),(1025,318137)]),([8,31744,1015808,1082401,4330468,8659208,17318431,32505856],[(1024,67255),(1024,72377)]),([8,31744,1015808,1082431,1083361,2164802,4329604,8659208,17318416,32505856],[(144,0),(176,0),(376,0)])]
def b115 : List Row := [([8,31744,1015808,1082431,2164802,4329604,4330468,8659208,17318416,32505856],[]),([8,31744,1015808,1082431,2164802,8659208,17318416,32641156],[(1024,65816),(1024,72997),(1025,305652)]),([8,31744,1015808,1082431,2164802,8659208,32641156],[(1024,65832),(1024,491795),(1024,72993),(1025,300532),(1025,301753)]),([8,31744,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[(246,0)]),([8,31744,1015808,2164802,4330468,8659208,17318431],[(1024,66182),(1024,98803),(1024,71156),(1025,436888),(1025,318105),(1025,122553)]),([8,31744,1015808,2164802,4330468,8659208,17318431,32505856],[(1024,66034),(1024,71156),(1025,117236)]),([8,31744,1082401,2164802,4330468,8659208,17318431,32505856],[(1024,444907),(1024,70118)]),([8,31744,1082401,3115074,4329604,8659231,17318416,32505856],[(96,0),(1024,72997),(1024,496738)]),([8,31744,1082401,3115074,4329604,8659944,32505856],[(1024,69736),(1024,102472),(1024,491602),(1025,69928),(1025,66034),(1025,73135)]),([8,31744,1082401,4329604,4330468,8659208,17318431,32505856],[(1024,100024),(1024,73185),(1025,66034),(1025,88761)]),([8,31744,1082401,4329604,8659208,17318431,32505856,33553439],[(1024,496915),(1024,67255)]),([8,31744,1082401,4330468,8659208,17318431,32505856],[(10,0),(74,0),(129,0),(1024,100024),(1024,67046),(1024,72161),(1025,122553),(1025,98803),(1025,285368),(1025,295410),(1025,300532),(1025,437944)]),([8,31744,1082431,2164802,5214340,8659208,17318416,32505856],[(1024,72997),(1024,65811),(1025,305652)]),([8,31744,1082431,2164802,5214340,8659208,32505856],[(1024,65832),(1024,655640),(1024,72993),(1025,300532),(1025,301753)]),([8,31744,1082431,4329604,8659208,17318416,32505856,33521664],[(1024,491795),(1024,66231),(1025,71351),(1025,437944)]),([8,31744,1082431,5214340,8659208,17318416,32505856],[(1024,72997),(1024,65811),(1024,99000),(1025,301753),(1025,437944),(1025,104120),(1025,268984)]),([8,31744,2164802,4330468,8659208,17318431,32505856],[(1024,66022),(1024,98803),(1024,71137),(1025,117236),(1025,122521),(1025,280051),(1025,312820)]),([8,31775,32736,1082401,4329604,8659208,17318416,32505856],[(1024,83247),(1024,67255)]),([8,31775,1015808,1082401,2164802,8659231,17318416,32505856],[(1024,302149),(1024,496915)]),([8,1015808,1015839,1082401,2164802,4329604,8659944,32505856],[(1024,69896),(1024,491602)]),([8,1015808,1082401,1082431,2164802,4329604,8659944,32505856],[(1024,69896),(1024,491795)]),([8,1015808,1082401,1082431,2165730,8659208,17318416,32505856],[(1024,309314),(1024,301125),(1025,70283)]),([8,1015808,1082401,2164802,2164831,4329604,8659944,32505856],[(1024,69896),(1024,502035)]),([8,1015808,1082401,2164802,4329604,8659231,8659944,32505856],[(1024,69928),(1024,501875),(1025,70067),(1025,70072)])]
def t110 : BT := .nd (blockTree b114) [8,31744,1015808,1082431,2164802,2165730,4329604,8659208,17318416,32505856] (blockTree b115)
def t111 : BT := .nd t109 [8,31,1083361,2164802,8659208,17318416,17809936,32505856] t110
def b116 : List Row := [([8,1015808,1082401,2164802,4329604,8659944,17318431,32505856],[(1024,69896),(1024,502035)]),([8,1015808,1082401,2164802,4329604,8659944,17333776,32505856],[(1024,299080),(1024,491602)]),([8,1015808,1082401,2164802,4329604,8659944,32505856,32505887],[(1024,655447),(1024,69896)]),([8,1015808,1082401,2164802,4329604,8659944,32505856,33554400],[(192,0),(1024,511238),(1024,69896)]),([8,1015808,1082401,2164802,4330468,8659208,17318431,32505856],[(1024,502195),(1024,666040)]),([8,1015808,1082401,2164831,2165730,4329604,8659208,32505856],[(80,0),(1024,78114),(1024,69928),(1025,302764)]),([8,1015808,1082401,2164831,4329604,8659208,8659944,32505856],[(1024,78119),(1024,66856)]),([8,1015808,1082401,2164831,4329604,8659208,32505856,33553439],[(1024,78119),(1024,66856)]),([8,1015808,1082401,4329604,8659208,8659944,17318431,32505856],[(144,0),(1024,78521),(1024,67255)]),([8,1015808,1082401,4329604,8659231,8659944,17318416,32505856],[(144,0),(1024,67255),(1024,301753),(1025,66995),(1025,301491)]),([8,1015808,1082401,4330468,8659208,17318431,32505856],[(113,0),(1024,67255),(1024,72377),(1024,100024),(1025,437944),(1025,436723)]),([8,1015808,1082431,1083361,2164802,4329604,8659208,32505856],[(104,0),(1024,78113),(1024,69928),(1025,301547),(1025,302571),(1025,302731)]),([8,1015808,1082431,2164802,2165730,4329604,8659208,32505856],[(80,0),(1024,78118),(1024,65832),(1025,302764)]),([8,1015808,1082431,2164802,4329604,8659208,8659944,32505856],[(1024,78118),(1024,65832)]),([8,1015808,1082431,2164802,4329604,8659208,32505856,33553439],[(1024,78118),(1024,65832)]),([8,1015808,1082431,2165730,4329604,8659208,17318416,32505856],[(1024,655800),(1024,491955)]),([8,1015808,1082431,2194498,4329604,8659208,17318416,32505856],[(1024,72997),(1024,491795)]),([8,1015808,1082431,2194498,4329604,8659208,32505856],[(1024,65832),(1024,491795),(1024,72993),(1025,70952),(1025,309945)]),([8,1015808,1082431,4329604,8659208,8659944,17318416,32505856],[(1024,66231),(1024,301753)]),([8,1015808,1113121,2164831,4329604,8659208,17318416,32505856],[(1024,72997),(1024,496915)]),([8,1015808,1113121,2164831,4329604,8659208,32505856],[(1024,66856),(1024,496915),(1024,72994),(1025,71976),(1025,309748)]),([8,1015808,2164802,4329604,8659208,8659944,17318431,32505856],[(144,0),(1024,502035),(1024,66034)]),([8,1015808,2164802,4329604,8659231,8659944,17318416,32505856],[(144,0),(1024,66034),(1024,300532)]),([8,1015808,2164802,4330468,8659208,17318431,32505856],[(113,0),(1024,66034),(1024,71156),(1024,98803),(1025,436723),(1025,437944),(1025,436888)]),([8,1015808,2164831,4329604,8659208,8659944,17318416,32505856],[(1024,78321),(1024,66034)])]
def b117 : List Row := [([9,4,992,1015808,1082401,2164802,4329604,8659208,32505856],[(96,0),(128,0),(216,0),(1024,511270),(1024,491635)]),([9,4,992,1015808,1082401,2164802,8659208,17318416,32505856],[(168,0),(1024,491635),(1024,655480)]),([9,31,992,8192,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(72,0),(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,32768,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,32768,4329604,8659208,17318416,32505856],[(144,0),(216,0),(1024,98968),(1024,66199)]),([9,31,992,31744,65536,4329604,8659208,17318416],[(96,0),(144,0),(152,0),(216,0),(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,268984)]),([9,31,992,31744,1015808,1082401,2097152,4329604,8659208,17318416,32505856],[(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32641156],[(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32776456],[(128,0),(168,0),(232,0),(240,0),(320,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318431,32505856],[(72,0),(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[(128,0),(168,0),(240,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17809936,32505856],[(128,0),(168,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,25977624,32505856],[(128,0),(168,0),(348,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856,33047056],[(128,0),(168,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056],[(82,0),(129,0),(138,0),(169,0),(178,0),(1024,679174),(1024,680001),(1024,302200),(1024,680033),(1024,680363)]),([9,31,992,31744,1015808,1082401,2164802,4329604,8659944],[(1024,450187),(1024,69896),(1025,69928),(1025,300536),(1025,302520)]),([9,31,992,31744,1015808,1082401,2164802,4329604,9412872,17318416,32505856],[(128,0),(240,0),(456,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856,32776456],[(128,0),(168,0),(240,0),(384,0)]),([9,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456],[(82,0),(128,0),(129,0),(138,0),(168,0),(169,0),(178,0),(226,0),(234,0),(240,0),(242,0),(286,0),(297,0),(385,0),(1024,117217)]),([9,31,992,31744,1015808,1082401,2164802,4329604,32776456],[(128,0),(168,0),(1024,711975),(1024,69928)]),([9,31,992,31744,1015808,1082401,2164802,4329604,33047056],[(216,0),(1024,679174),(1024,711778)]),([9,31,992,31744,1015808,1082401,2164802,8659208,32641156],[(128,0),(168,0),(1024,69928),(1024,511270)]),([9,31,992,31744,1015808,1082401,2164831,4329604,8659208,17318416,32505856],[(72,0),(128,0),(168,0),(336,0)])]
def t112 : BT := .nd (blockTree b116) [9,4,31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856] (blockTree b117)
def b118 : List Row := [([9,31,992,31744,1015808,1082401,3115074,4329604,8659208,17318416,32505856],[(128,0),(232,0),(240,0),(336,0)]),([9,31,992,31744,1015808,1082401,3247203,4329604,8659208,17318416,32505856],[(128,0),(168,0),(232,0),(240,0),(336,0),(456,0)]),([9,31,992,31744,1015808,1082401,4329604,8659208,17318416,32573506],[(168,0),(216,0),(1024,83618),(1024,70327),(1024,73378),(1024,78498),(1024,117410),(1024,309927),(1024,315047)]),([9,31,992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856],[(72,0),(128,0),(168,0),(336,0)]),([9,31,992,31744,1015808,1113121,2164802,4329604,8659208,17318416,32505856],[(168,0),(232,0),(336,0)]),([9,31,992,31744,1015808,2164802,4329604,8659208,17318416,32539681],[(168,0),(216,0),(1024,67063),(1024,70295),(1024,73345),(1024,78465),(1024,309894)]),([9,31,992,31744,1015808,4329604,8659208,17318416,32539681],[(144,0),(216,0),(1024,99992),(1024,67223)]),([9,31,992,31744,1015808,4329604,8659208,17318416,32573506],[(144,0),(216,0),(1024,98803),(1024,66034),(1025,67255)]),([9,31,992,31744,1048575,1082401,4329604,8659208,17318416],[(184,0),(272,0),(1024,100024),(1024,67255)]),([9,31,992,31744,1082401,2097152,4329604,8659208,17318416],[(184,0),(272,0),(1024,444907),(1024,83425)]),([9,31,992,31744,1082401,2164802,3115074,4329604,8659208,17318416,32505856],[(128,0),(232,0),(336,0),(456,0)]),([9,31,992,31744,1082401,2164802,4329604,5214340,8659208,17318416,32505856],[(96,0),(128,0),(184,0),(256,0),(336,0),(448,0)]),([9,31,992,31744,1082401,2164802,4329604,8659208,9412872,17318416,32505856],[(96,0),(128,0),(184,0),(256,0),(312,0),(336,0),(448,0)]),([9,31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856,33521664],[(96,0),(128,0),(184,0),(272,0),(376,0),(448,0)]),([9,31,992,31744,1082401,2164802,4329604,8659208,17809936],[(1024,450187),(1024,88705)]),([9,31,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[(82,0),(97,0),(106,0),(128,0),(129,0),(138,0),(257,0),(376,0),(377,0),(1024,314440),(1024,315014),(1024,502195),(1024,511073),(1024,302195),(1024,315047),(1024,511403)]),([9,31,992,31744,1082401,2164802,4329604,8659208,32539681],[(1024,444907),(1024,69928),(1025,66201),(1025,98969),(1025,656057),(1025,666297)]),([9,31,992,31744,1082401,2164802,4329604,8659208,33047056],[(1024,314854),(1024,83425)]),([9,31,992,31744,1082401,2164802,4329604,8659944,32505856],[(312,0),(1024,444907),(1024,69896),(1025,69928),(1025,104755),(1025,300697),(1025,301491),(1025,302515)]),([9,31,992,31744,1082401,2164802,4329604,9412872],[(82,0),(1024,69928),(1024,103089),(1024,88705),(1025,301753),(1025,300697),(1025,69928),(1025,300536)]),([9,31,992,31744,1082401,2164802,4329604,9412872,17318416],[(1024,445067),(1024,88705)]),([9,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856],[(82,0),(96,0),(97,0),(106,0),(138,0),(178,0),(186,0),(257,0),(286,0),(376,0),(377,0),(394,0),(1024,117377),(1024,117410)]),([9,31,992,31744,1082401,2164802,4329604,9412872,32505856],[(96,0),(1024,69928),(1024,510246)]),([9,31,992,31744,1082401,2164802,4329604,17318416,32539681],[(1024,444907),(1024,83425),(1025,66200),(1025,300697)])]
def b119 : List Row := [([9,31,992,31744,1082401,2164802,4329604,17809936],[(1024,122497),(1024,286342),(1024,450187),(1025,100024),(1025,267928)]),([9,31,992,31744,1082401,2164802,4329604,17809936,32505856],[(168,0),(312,0),(1024,711943),(1024,510049)]),([9,31,992,31744,1082401,2164802,4329604,32776456],[(82,0),(128,0),(1024,314854),(1024,69928),(1024,83425),(1025,300532),(1025,66034),(1025,69928),(1025,98969),(1025,300697)]),([9,31,992,31744,1082401,2164802,4329604,33047056],[(1024,117217),(1024,281062),(1024,444907),(1025,98803),(1025,66034),(1025,267763),(1025,300697)]),([9,31,992,31744,1082401,2164802,5214340,8659208],[(82,0),(1024,320134),(1024,69928),(1024,83585),(1025,301753),(1025,300697),(1025,69928)]),([9,31,992,31744,1082401,2164802,5214340,8659208,32505856],[(96,0),(1024,712999),(1024,69928)]),([9,31,992,31744,1082401,2164802,8659208,32641156],[(82,0),(128,0),(178,0),(1024,314854),(1024,69928),(1024,83425),(1025,300532),(1025,66201),(1025,69928),(1025,98803)]),([9,31,992,31744,1082401,3115074,4329604,8659208,17318416,32505856],[(82,0),(97,0),(178,0),(184,0),(186,0),(257,0),(272,0),(273,0),(286,0),(289,0),(377,0),(1024,507969),(1024,508001),(1024,508198),(1024,508166),(1024,66199),(1024,83425),(1024,491635),(1024,496915),(1024,508331)]),([9,31,992,31744,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,508198)]),([9,31,992,31744,1082401,3115074,4329604,17318416,32505856],[(168,0),(1024,508001),(1024,711778)]),([9,31,992,31744,1082401,3247203,4329604,8659208,32505856],[(1024,444907),(1024,69928),(1025,66034),(1025,98803)]),([9,31,992,31744,1082401,3247203,4329604,17318416,32505856],[(312,0),(1024,444907),(1024,83425),(1025,66034),(1025,300532)]),([9,31,992,31744,1082401,4329604,8659208,16236015,32505856],[(1024,712999),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32505856],[(144,0),(216,0),(1024,100024),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32539681],[(144,0),(216,0),(1024,100024),(1024,67255)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32641156],[(144,0),(200,0),(1024,100024),(1024,83425),(1025,66231),(1025,88761)]),([9,31,992,31744,1082401,4329604,8659208,17318416,32776456],[(200,0),(1024,444907),(1024,67255),(1025,99000),(1025,122553),(1025,285368),(1025,449208),(1025,450233)]),([9,31,992,31744,1082401,4329604,8659208,17318431,32505856],[(72,0),(96,0),(144,0),(216,0),(1024,268984),(1024,67255),(1025,88761)]),([9,31,992,31744,1082401,4329604,8659208,17333776,32505856],[(72,0),(216,0),(1024,100024),(1024,67255),(1025,450233)]),([9,31,992,31744,1082401,4329604,8659208,17809936],[(1024,67255),(1024,100024),(1024,88705),(1025,301753),(1025,67255)]),([9,31,992,31744,1082401,4329604,8659208,17809936,32505856],[(1024,67255),(1024,100024)]),([9,31,992,31744,1082401,4329604,8659208,21648020,32505856],[(1024,100024),(1024,69928),(1025,66034),(1025,268584)]),([9,31,992,31744,1082401,4329604,8659208,25977624,32505856],[(1024,444907),(1024,67255),(1025,98803)]),([9,31,992,31744,1082401,4329604,9412872,17318416],[(1024,67255),(1024,100017),(1024,88705),(1025,100024),(1025,301753)])]
def t113 : BT := .nd (blockTree b118) [9,31,992,31744,1082401,2164802,4329604,17318416,32776456] (blockTree b119)
def t114 : BT := .nd t112 [9,31,992,31744,1015808,1082401,2194498,4329604,8659208,17318416,32505856] t113
def t115 : BT := .nd t111 [8,1015808,1082401,2164802,4329604,8659944,8683496,32505856] t114
def b120 : List Row := [([9,31,992,31744,1082401,4329604,12988812,17318416,32505856],[(216,0),(304,0),(1024,100024),(1024,83425),(1025,66034),(1025,268584)]),([9,31,992,31744,1082401,4329604,17318416,24895223,32505856],[(144,0),(168,0),(1024,711778),(1024,67255)]),([9,31,992,31744,1082431,4329604,8659208,17318416,32505856],[(72,0),(216,0),(1024,66231),(1024,99000),(1025,67046),(1025,67051),(1025,67255)]),([9,31,992,31744,1113121,4329604,8659208,17318416,32505856],[(72,0),(144,0),(216,0),(1024,100024),(1024,67255),(1025,437944)]),([9,31,992,31744,2065441,2164802,4329604,8659208,17318416],[(184,0),(272,0),(1024,88545),(1024,286182),(1025,67255)]),([9,31,992,31744,2065441,2164802,4329604,8659208,17318416,32505856],[(168,0),(216,0),(1024,67058),(1024,70130),(1024,73185),(1024,78305),(1024,268787),(1024,309734),(1024,437747)]),([9,31,992,31744,2164802,4329604,8659208,17318416,32539681],[(144,0),(216,0),(1024,444907),(1024,83425)]),([9,31,992,31744,4329604,8659208,17318416,32472030,32505856],[(112,0),(168,0),(1024,100024),(1024,67255)]),([9,31,992,31744,4329604,8659208,17318416,32505856,32539681],[(112,0),(168,0),(1024,99992),(1024,67223)]),([9,31,992,31744,4329604,8659208,17318416,32539681],[(2,0),(14,0),(57,0),(73,0),(82,0),(106,0),(112,0),(114,0),(153,0),(168,0),(169,0),(185,0),(193,0),(201,0),(1024,67063),(1024,99832),(1024,83425),(1025,66231),(1025,67255),(1025,99000),(1025,268984),(1025,300729),(1025,437944)]),([9,31,992,31775,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(168,0),(336,0)]),([9,31,992,31775,1015808,1082401,2164802,8659208,17318416],[(216,0),(1024,450187),(1024,286342),(1025,66034),(1025,69928)]),([9,31,992,31775,1082401,2164802,8659208,17318416,32505856],[(168,0),(1024,444907),(1024,281062),(1025,66199),(1025,69928)]),([9,31,992,31775,1082401,4329604,8659208,17318416,32505856],[(96,0),(216,0),(1024,67255),(1024,100024),(1025,67255)]),([9,31,992,1015808,1048575,1082401,2164802,4329604,8659208],[(128,0),(168,0),(1024,450187),(1024,69928)]),([9,31,992,1015808,1082401,1113121,2164802,4329604,8659208,17318416,32505856],[(96,0),(168,0),(232,0),(336,0),(456,0)]),([9,31,992,1015808,1082401,2164802,2194498,4329604,8659208,17318416,32505856],[(96,0),(128,0),(232,0),(336,0),(456,0)]),([9,31,992,1015808,1082401,2164802,4329604,4357252,8659208,17318416,32505856],[(96,0),(128,0),(184,0),(256,0),(336,0),(448,0)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,17333776],[(184,0),(1024,122497),(1024,286342),(1025,67255)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[(96,0),(97,0),(106,0),(128,0),(129,0),(138,0),(184,0),(186,0),(257,0),(376,0),(377,0),(1024,309320),(1024,309734),(1024,309894),(1024,309927),(1024,66199),(1024,491635),(1024,496915)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,32505856],[(96,0),(128,0),(1024,69928),(1024,502195)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,32505887],[(1024,666040),(1024,69928),(1025,69928),(1025,117176)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,32641156],[(96,0),(128,0),(1024,511270),(1024,502195)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,33047056],[(216,0),(1024,502195),(1024,666040)]),([9,31,992,1015808,1082401,2164802,4329604,8659208,33521664],[(72,0),(96,0),(128,0),(1024,69928),(1024,511270),(1025,300532)])]
def b121 : List Row := [([9,31,992,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[(1024,508331),(1024,509355),(1024,511403),(1024,678315),(1024,680363)]),([9,31,992,1015808,1082401,2164802,4329604,9412872,32505856],[(96,0),(128,0),(1024,69928),(1024,510246),(1025,431604)]),([9,31,992,1015808,1082401,2164802,4329604,12988812,32505856],[(96,0),(128,0),(1024,511270),(1024,502195)]),([9,31,992,1015808,1082401,2164802,4329604,24895223,32505856],[(96,0),(128,0),(1024,69928),(1024,502195)]),([9,31,992,1015808,1082401,2164802,4329604,32505856,32776456],[(96,0),(128,0),(1024,711975),(1024,69928),(1025,431769),(1025,445113)]),([9,31,992,1015808,1082401,2164802,4329604,33047056],[(1024,502195),(1024,665701),(1024,510049),(1025,436889),(1025,436723),(1025,437945)]),([9,31,992,1015808,1082401,2164802,4357252,8659208],[(1024,320134),(1024,69928),(1024,78465),(1025,300697),(1025,301753),(1025,69928),(1025,300532),(1025,302520)]),([9,31,992,1015808,1082401,2164802,4357252,8659208,32505856],[(1024,712999),(1024,69928)]),([9,31,992,1015808,1082401,2164802,5214340,8659208,32505856],[(96,0),(128,0),(1024,69928),(1024,509222),(1025,300532)]),([9,31,992,1015808,1082401,2164802,5412005,8659208,32505856],[(128,0),(1024,508993),(1024,69928),(1025,65637)]),([9,31,992,1015808,1082401,2164802,6494406,8659208,32505856],[(96,0),(1024,710722),(1024,69928),(1025,66661)]),([9,31,992,1015808,1082401,2164802,8659208,12988812,32505856],[(96,0),(128,0),(168,0),(1024,69928),(1024,502195),(1025,267560),(1025,268584)]),([9,31,992,1015808,1082401,2164802,8659208,16236015,32505856],[(168,0),(1024,69928),(1024,502195)]),([9,31,992,1015808,1082401,2164802,8659208,32505856,32641156],[(96,0),(128,0),(1024,69928),(1024,502195),(1025,300697)]),([9,31,992,1015808,1082401,2164802,8659208,32641156],[(2,0),(26,0),(73,0),(96,0),(97,0),(128,0),(129,0),(178,0),(1024,502195),(1024,69928),(1024,511270),(1025,69928),(1025,70072),(1025,300532),(1025,300697),(1025,302731),(1025,302764),(1025,436723),(1025,437944)]),([9,31,992,1015808,1082401,2164831,4329604,8659208,32505856],[(72,0),(96,0),(128,0),(1024,511270),(1024,66856),(1025,71976)]),([9,31,992,1015808,1082401,2194498,4329604,8659208,17318416,32505856],[(96,0),(97,0),(106,0),(138,0),(178,0),(184,0),(186,0),(257,0),(272,0),(273,0),(286,0),(289,0),(377,0),(1024,436888),(1024,117217),(1024,491635),(1024,496915),(1024,437747),(1024,699479),(1024,699705)]),([9,31,992,1015808,1082401,2194498,4329604,8659208,32505856],[(96,0),(1024,712999),(1024,69928)]),([9,31,992,1015808,1082401,3115074,4329604,8659208,32505856],[(72,0),(96,0),(128,0),(1024,69928),(1024,508198),(1025,300532)]),([9,31,992,1015808,1082401,3247203,4329604,8659208,32505856],[(96,0),(128,0),(1024,69928),(1024,502195),(1025,436723)]),([9,31,992,1015808,1082401,4329604,6494406,8659208,32505856],[(96,0),(1024,67255),(1024,502195),(1025,678585)]),([9,31,992,1015808,1082401,4329604,8659208,17333776],[(144,0),(1024,67255),(1024,100024),(1024,88705),(1025,67255),(1025,268984)]),([9,31,992,1015808,1082401,4329604,8659208,17333776,32505856],[(96,0),(144,0),(1024,268984),(1024,67255)]),([9,31,992,1015808,1082401,4329604,8659208,25977624,32505856],[(96,0),(216,0),(1024,67255),(1024,301753),(1025,436723)])]
def t116 : BT := .nd (blockTree b120) [9,31,992,1015808,1082401,2164802,4329604,8659944,32505856] (blockTree b121)
def b122 : List Row := [([9,31,992,1015808,1082431,2164802,4329604,8659208,32505856],[(96,0),(128,0),(1024,511270),(1024,65832),(1025,70952)]),([9,31,992,1015808,1113121,2164802,4329604,8659208,17318416,32505856],[(106,0),(128,0),(129,0),(138,0),(178,0),(186,0),(257,0),(272,0),(273,0),(286,0),(377,0),(1024,491635),(1024,496915),(1024,501842),(1024,502068)]),([9,31,992,1015808,1113121,2164802,4329604,8659208,32505856],[(128,0),(1024,511270),(1024,69928)]),([9,31,992,1015808,1113121,4329604,8659208,17318416,32505856],[(216,0),(1024,436920),(1024,67255)]),([9,31,992,1015808,2164802,3247203,4329604,8659208,32505856],[(96,0),(128,0),(1024,69928),(1024,502195),(1025,437944)]),([9,31,992,1015808,2164802,4329604,5412005,8659208,32505856],[(96,0),(1024,66034),(1024,502195),(1025,678585)]),([9,31,992,1015808,2164802,4329604,8659208,17333776],[(1024,66199),(1024,98803),(1024,88705),(1025,66199),(1025,267928),(1025,67255)]),([9,31,992,1015808,2164802,4329604,8659208,17333776,32505856],[(96,0),(1024,267763),(1024,66034),(1025,67058)]),([9,31,992,1015808,2164802,4329604,8659208,25977624,32505856],[(96,0),(216,0),(1024,66034),(1024,300532),(1025,437944)]),([9,31,992,1015808,2164802,4329604,8659208,32472030,32505856],[(96,0),(1024,300532),(1024,69928)]),([9,31,992,1015808,2194498,4329604,8659208,17318416,32505856],[(216,0),(1024,66199),(1024,98803)]),([9,31,992,1015808,4329604,8659208,17318416,32505856,32539681],[(168,0),(1024,67223),(1024,99992),(1025,76471),(1025,273080),(1025,502455),(1025,502457)]),([9,31,992,1015839,1082401,2164802,4329604,8659208,32505856],[(128,0),(1024,83425),(1024,69928),(1025,69928),(1025,117176)]),([9,31,992,1082401,2164802,3115074,4329604,8659208,32505856],[(72,0),(96,0),(1024,69928),(1024,502195),(1025,445112)]),([9,31,992,1082401,2164802,4329604,5214340,8659208,32505856],[(72,0),(96,0),(1024,511270),(1024,502195)]),([9,31,992,1082401,2164802,4329604,8659208,17333776,32505856],[(96,0),(304,0),(1024,117217),(1024,281062)]),([9,31,992,1082401,2164802,4329604,8659208,17809936,32505856],[(96,0),(168,0),(304,0),(1024,502195),(1024,666040)]),([9,31,992,1082401,2164802,4329604,8659208,32505856,32538623],[(72,0),(96,0),(1024,444907),(1024,69928)]),([9,31,992,1082401,2164802,4329604,8659208,32505856,33521664],[(72,0),(96,0),(216,0),(1024,69928),(1024,502195),(1025,300697)]),([9,31,992,1082401,2164802,4329604,17809936,32505856],[(248,0),(1024,502191),(1024,666040),(1024,505953),(1025,436724),(1025,437944)]),([9,31,992,1082401,2164802,4357252,8659208,32505856],[(1024,314854),(1024,69928),(1024,78305),(1025,300532),(1025,300697),(1025,69928),(1025,98803),(1025,302515)]),([9,31,992,1082401,2164802,5214340,8659208,32505856],[(2,0),(18,0),(72,0),(73,0),(97,0),(217,0),(1024,504102),(1024,69928),(1024,666040),(1025,69928),(1025,70067),(1025,300532),(1025,300697),(1025,302571),(1025,436723),(1025,437944)]),([9,31,992,1082401,2194498,4329604,8659208,17318416,32505856],[(216,0),(1024,444907),(1024,83425)]),([9,31,992,1082401,2194498,4329604,8659208,32505856],[(1024,314854),(1024,69928),(1024,83425),(1025,300532),(1025,300697),(1025,66034),(1025,69928),(1025,98803),(1025,301491),(1025,666297)])]
def b123 : List Row := [([9,31,992,1082401,3115074,4329604,8659208,32505856],[(2,0),(18,0),(73,0),(97,0),(169,0),(217,0),(1024,69928),(1024,502055),(1024,503078),(1025,69928),(1025,300532),(1025,300697),(1025,301547),(1025,436723),(1025,445113),(1025,446136)]),([9,31,992,1082401,3115074,4329604,17318416,32505856],[(1024,502188),(1024,666040),(1024,502881),(1025,436723),(1025,436888),(1025,445112)]),([9,31,992,1082401,4329604,4357252,8659208,17318416,32505856],[(152,0),(216,0),(296,0),(1024,100024),(1024,78305),(1025,66034)]),([9,31,992,1082401,4329604,8659208,17318416,32505856,33521664],[(72,0),(168,0),(1024,502195),(1024,67255),(1025,67255),(1025,268984)]),([9,31,992,1082401,4329604,8659208,17318416,32505856,33522687],[(168,0),(1024,502195),(1024,67255)]),([9,31,992,1082401,4329604,8659208,17333776,32505856],[(2,0),(14,0),(57,0),(153,0),(169,0),(193,0),(1024,67255),(1024,100024),(1024,83425),(1025,66034),(1025,67255),(1025,98803),(1025,268984),(1025,300532),(1025,301547),(1025,450233)]),([9,31,992,1082401,4329604,8659208,17809936,32505856],[(129,0),(153,0),(1024,67255),(1024,100024),(1024,301491),(1025,437944),(1025,67255),(1025,268984),(1025,301491),(1025,436723),(1025,502457)]),([9,31,992,2164802,4329604,8659208,17333776,32505856],[(72,0),(1024,66034),(1024,98803),(1024,83425),(1025,66034),(1025,267763),(1025,66199)]),([9,31,992,2194498,4329604,8659208,17318416,32505856],[(168,0),(1024,66034),(1024,98803),(1024,83425),(1025,442867),(1025,66034),(1025,66199)]),([9,31,1023,31744,1082401,4329604,8659208,17318416,32505856],[(1024,72997),(1024,67255),(1025,67255)]),([9,31,31744,32736,1082401,4329604,8659208,17318416,32505856],[(216,0),(1024,100024),(1024,67255),(1025,437944)]),([9,31,31744,1015808,1082401,1083361,2164802,4329604,8659208,17318416,32505856],[(168,0)]),([9,31,31744,1015808,1082401,2164802,2165730,4329604,8659208,17318416,32505856],[]),([9,31,31744,1015808,1082401,2164802,4329604,4330468,8659208,17318416,32505856],[]),([9,31,31744,1015808,1082401,2164802,4329604,8659208,17318896,32505856],[(1024,78117),(1024,65832),(1024,66856),(1024,83237),(1024,88357),(1024,502068),(1024,508198),(1024,699705)]),([9,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856],[(1024,69896),(1024,440392),(1024,508166),(1024,509190),(1024,678150)]),([9,31,31744,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,69896),(1024,511238)]),([9,31,31744,1015808,1082401,2164802,4329604,17318896,32505856],[(1024,510049),(1024,711778)]),([9,31,31744,1015808,1082401,2164802,4330468,8659208,17318416],[(1024,450187),(1024,73345),(1025,67255)]),([9,31,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[(273,0),(318,0),(1024,269811),(1024,270008),(1024,73345),(1024,66199),(1024,302181)]),([9,31,31744,1015808,1082401,2164802,8659208,17318416,32641156],[(1024,496915),(1024,72997),(1025,69945)]),([9,31,31744,1015808,1082401,2164802,8659208,32641156],[(1024,69928),(1024,496915),(1024,72997),(1025,69945),(1025,300532)]),([9,31,31744,1015808,1082401,2164802,8659231,17318416,32505856],[(1024,660760),(1024,302149),(1025,266536)]),([9,31,31744,1015808,1082401,2164802,17318416,25977624,32505856],[(1024,72997),(1024,496915),(1025,300532),(1025,301753)])]
def t117 : BT := .nd (blockTree b122) [9,31,992,1082401,3115074,4329604,8659208,17318416,32505856] (blockTree b123)
def t118 : BT := .nd t116 [9,31,992,1015808,1082401,4329604,8659208,31389629,32505856] t117
def b124 : List Row := [([9,31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[(273,0),(310,0),(1024,267928),(1024,301125),(1024,268787),(1024,491635)]),([9,31,31744,1015808,1082401,2165730,8659208,17318416,32505856],[(1024,677953),(1024,301125)]),([9,31,31744,1015808,1082401,4330468,8659208,17318416],[(1024,67239),(1024,100024),(1024,72321),(1025,437944),(1025,67255)]),([9,31,31744,1015808,1082401,4330468,8659208,17318416,32505856],[(1024,100024),(1024,67255)]),([9,31,31744,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[(128,0),(129,0),(273,0),(302,0),(1024,267960),(1024,300101),(1024,491635)]),([9,31,31744,1015808,1083361,2164802,8659208,17318416,32505856],[(1024,508993),(1024,300101)]),([9,31,31744,1015808,1083361,4329604,8659208,17318416,32505856],[(1024,300729),(1024,67255)]),([9,31,31744,1015808,2164802,4330468,8659208,17318416],[(1024,66182),(1024,98803),(1024,71297),(1025,436888),(1025,66199),(1025,67255)]),([9,31,31744,1015808,2164802,4330468,8659208,17318416,32505856],[(1024,98803),(1024,66034),(1025,67058)]),([9,31,31744,1015808,2165730,4329604,8659208,17318416,32505856],[(1024,66199),(1024,98803)]),([9,31,31744,1015808,4329604,8659208,17318416,32505856,32539681],[(1024,72997),(1024,67223),(1025,71351),(1025,437944),(1025,497335)]),([9,31,31744,1082401,2164802,4330468,8659208,17318416,32505856],[(1024,444907),(1024,73185)]),([9,31,31744,1082401,2164802,5214340,8659208,17318416,32505856],[(1024,660760),(1024,72997),(1025,69940)]),([9,31,31744,1082401,2164802,5214340,8659208,32505856],[(1024,69928),(1024,498982),(1024,72997),(1025,69940),(1025,300697)]),([9,31,31744,1082401,2164802,5214340,17318416,32505856],[(1024,72997),(1024,496904),(1024,498785),(1025,268984),(1025,267763),(1025,436723)]),([9,31,31744,1082401,2165730,4329604,8659208,17318416,32505856],[(1024,444907),(1024,83425)]),([9,31,31744,1082401,2165730,8659208,17318416,32505856],[(1024,83425),(1024,280642),(1024,301125),(1025,66034),(1025,66199),(1025,98803),(1025,99603),(1025,300532),(1025,661175)]),([9,31,31744,1082401,3115074,4329604,8659208,17318416,32505856],[(1024,72997),(1024,496915),(1025,69933)]),([9,31,31744,1082401,3115074,4329604,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69928),(1025,300532)]),([9,31,31744,1082401,3115074,4329604,17318416,32505856],[(1024,72997),(1024,496738),(1024,497761),(1025,267763),(1025,267928),(1025,281272),(1025,436723)]),([9,31,31744,1082401,3115074,8659208,17318416,32505856],[(128,0),(1024,72997),(1024,302149),(1024,496706),(1025,69928),(1025,66199),(1025,69933),(1025,300532)]),([9,31,31744,1082401,4329604,4330468,8659208,17318416,32505856],[(1024,100024),(1024,73185),(1025,66034)]),([9,31,31744,1082401,4329604,8659208,17318416,32505856,33521664],[(1024,496915),(1024,67255),(1025,67255),(1025,437944)]),([9,31,31744,1082401,4329604,8659208,17318416,32505856,33553439],[(1024,496915),(1024,67255)]),([9,31,31744,1082401,4330468,8659208,17318416,32505856],[(2,0),(169,0),(1024,72161),(1024,100024),(1024,67046),(1025,285368),(1025,66034),(1025,67046),(1025,67255),(1025,98803),(1025,300532),(1025,318137),(1025,437944)])]
def b125 : List Row := [([9,31,31744,2164802,4330468,8659208,17318416,32505856],[(1024,66022),(1024,98803),(1024,71137),(1025,66034),(1025,436723),(1025,66199)]),([9,31,31744,2165730,4329604,8659208,17318416,32505856],[(1024,66034),(1024,98803),(1024,83425),(1025,279027),(1025,66034),(1025,66199)]),([9,31,31775,1015808,1082401,2164802,8659208,17318416,32505856],[(1024,302149),(1024,496915),(1025,66034),(1025,66199)]),([9,31,1015808,1016800,1082401,2164802,8659208,17318416,32505856],[(168,0),(1024,302149),(1024,496915),(1025,66034)]),([9,31,1015808,1082401,1083361,2164802,4329604,8659208,32505856],[(128,0),(1024,69928),(1024,497075),(1025,301547),(1025,302571),(1025,302731),(1025,436723)]),([9,31,1015808,1082401,1083361,2164802,8659208,17318416,32505856],[(72,0),(168,0),(1024,302149),(1024,497075)]),([9,31,1015808,1082401,2164802,2165730,4329604,8659208,32505856],[(1024,69928),(1024,502195),(1025,302764),(1025,437944)]),([9,31,1015808,1082401,2164802,2165730,8659208,17318416,32505856],[(96,0),(168,0),(1024,302149),(1024,502195)]),([9,31,1015808,1082401,2164802,4329604,4330468,8659208,32505856],[(1024,511270),(1024,502195),(1025,70957),(1025,71981)]),([9,31,1015808,1082401,2164802,4329604,8659208,8659944,32505856],[(1024,69928),(1024,502035)]),([9,31,1015808,1082401,2164802,4329604,8659208,32505856,33553439],[(1024,69928),(1024,502195)]),([9,31,1015808,1082401,2164802,4329604,8659944,17318416,32505856],[(1024,502035),(1024,665880)]),([9,31,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,69896),(1024,502035),(1024,511238),(1025,70056),(1025,431604),(1025,431769),(1025,436723),(1025,437944)]),([9,31,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[(1024,660760),(1024,72997)]),([9,31,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[(168,0),(1024,502195),(1024,666040)]),([9,31,1015808,1082401,2164802,4357252,8659208,17318416,32505856],[(168,0),(1024,496915),(1024,72997)]),([9,31,1015808,1082401,2164802,4357252,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69935),(1025,300532)]),([9,31,1015808,1082401,2164802,8659208,8659944,17318416,32505856],[(128,0),(1024,302149),(1024,502035),(1025,302515),(1025,302520),(1025,436723),(1025,437944)]),([9,31,1015808,1082401,2164802,8659208,17318416,32505856,32506848],[(128,0),(1024,660760),(1024,302149),(1025,66199)]),([9,31,1015808,1082401,2164802,8659208,17318416,32505856,33553439],[(128,0),(1024,302149),(1024,502195)]),([9,31,1015808,1082401,2165730,4329604,8659208,17318416,32505856],[(1024,694712),(1024,502195)]),([9,31,1015808,1082401,2165730,8659208,17318416,32505856],[(2,0),(129,0),(1024,301125),(1024,502195),(1024,309314),(1025,66034),(1025,66199),(1025,66863),(1025,69932),(1025,436723),(1025,437944)]),([9,31,1015808,1082401,2194498,4329604,8659208,17318416,32505856],[(1024,72997),(1024,496915)]),([9,31,1015808,1082401,2194498,4329604,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69928),(1025,300532)])]
def t119 : BT := .nd (blockTree b124) [9,31,31744,1082401,5214340,8659208,17318416,32505856] (blockTree b125)
def b126 : List Row := [([9,31,1015808,1082401,4329604,8659208,8659944,17318416,32505856],[(1024,67255),(1024,301753),(1025,301491),(1025,436723)]),([9,31,1015808,1082401,4330468,8659208,17318416,32505856],[(129,0),(1024,437944),(1024,67255),(1024,301753),(1025,437944),(1025,67255),(1025,436723)]),([9,31,1015808,1082401,4357252,8659208,17318416,32505856],[(1024,72997),(1024,66863),(1024,100024),(1025,268984),(1025,301753),(1025,67255)]),([9,31,1015808,1083361,2164802,4329604,8659208,17318416,32505856],[(96,0),(1024,497075),(1024,660920)]),([9,31,1015808,1083361,2164802,8659208,17318416,32505856],[(2,0),(97,0),(129,0),(1024,300101),(1024,497075),(1024,309313),(1025,65839),(1025,66034),(1025,66199),(1025,69931),(1025,436723),(1025,437944)]),([9,31,1015808,1083361,4329604,8659208,17318416,32505856],[(129,0),(1024,67255),(1024,100024),(1024,300729),(1025,67255),(1025,273080),(1025,436723),(1025,437944)]),([9,31,1015808,1113121,2164802,4329604,8659208,17318416,32505856],[(1024,72997),(1024,496915)]),([9,31,1015808,1113121,2164802,4329604,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69928),(1025,301753)]),([9,31,1015808,1113121,2164802,8659208,17318416,32505856],[(1024,72997),(1024,302149),(1024,496915),(1025,69928),(1025,66034),(1025,66199),(1025,301753)]),([9,31,1015808,1113121,4329604,8659208,17318416,32505856],[(1024,67255),(1024,72997),(1024,100024),(1025,268984),(1025,301753),(1025,67255),(1025,437944)]),([9,31,1015808,2164802,4329604,8659208,8659944,17318416,32505856],[(1024,66034),(1024,300532),(1025,437944)]),([9,31,1015808,2164802,4330468,8659208,17318416,32505856],[(129,0),(1024,436723),(1024,66034),(1024,300532),(1025,436723),(1025,436888),(1025,437944)]),([9,31,1015808,2164802,4357252,8659208,17318416,32505856],[(1024,72997),(1024,65839),(1024,98803),(1025,267763),(1025,300697),(1025,268787)]),([9,31,1015808,2165730,4329604,8659208,17318416,32505856],[(129,0),(1024,309745),(1024,66034),(1024,98803),(1025,436723),(1025,436888),(1025,437944)]),([9,31,1015808,2194498,4329604,8659208,17318416,32505856],[(1024,72997),(1024,66034),(1024,98803),(1025,267763),(1025,300697)]),([9,31744,1015808,1082401,2164802,4329604,8659231,17318416,32505856],[(128,0),(1024,72997),(1024,496755)]),([9,31744,1015808,1082401,2164802,4329604,8659944,32505856],[(1024,69736),(1024,102472),(1024,491602),(1025,69928),(1025,66034),(1025,67255),(1025,73135)]),([9,31744,1015808,1082401,2164831,4329604,8659208,17318416,32505856],[(1024,496915),(1024,72997),(1025,77101)]),([9,31744,1015808,1082401,2164831,4329604,8659208,32505856],[(1024,66856),(1024,496915),(1024,72994),(1025,71976),(1025,300532)]),([9,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856],[(1024,72997),(1024,491795),(1025,76077)]),([9,31744,1015808,1082431,2164802,4329604,8659208,32505856],[(1024,65832),(1024,491795),(1024,72993),(1025,70952),(1025,301753)]),([9,31744,1015808,1082431,4329604,8659208,17318416,32505856],[(1024,66231),(1024,99000),(1024,72997),(1025,268984),(1025,301753),(1025,437944),(1025,71351)]),([9,31744,1015808,2164831,4329604,8659208,17318416,32505856],[(1024,66034),(1024,72997),(1024,98803),(1025,267763),(1025,300697),(1025,305652)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208],[(82,0),(1024,69928),(1024,122497),(1024,286342),(1025,300697),(1025,301753),(1025,69928),(1025,300532)])]
def b127 : List Row := [([10,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(82,0),(128,0),(129,0),(138,0),(168,0),(169,0),(178,0),(216,0),(226,0),(232,0),(234,0),(240,0),(242,0),(272,0),(321,0),(336,0),(337,0),(350,0),(353,0),(361,0),(456,0),(457,0),(474,0),(1024,66034),(1024,67255),(1024,69928),(1024,299080),(1024,302149),(1024,510049),(1024,491635),(1024,496915),(1024,66199),(1024,83425),(1024,88705)]),([10,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[(128,0),(168,0),(1024,69928),(1024,511270)]),([10,31,992,31744,1015808,1082401,2164802,4329604,17318416],[(240,0),(1024,122497),(1024,286342),(1024,450187),(1025,98968),(1025,268984)]),([10,31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],[(216,0),(240,0),(384,0),(1024,510049),(1024,711778)]),([10,31,992,31744,1015808,1082401,4329604,8659208,17318416],[(184,0),(192,0),(272,0),(1024,67255),(1024,100024),(1024,88705),(1025,67255),(1025,268984)]),([10,31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],[(128,0),(184,0),(192,0),(272,0),(1024,100024),(1024,67255)]),([10,31,992,31744,1015808,2164802,4329604,8659208,17318416],[(184,0),(272,0),(1024,66199),(1024,98803),(1024,88705),(1025,66199),(1025,267928),(1025,67255)]),([10,31,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],[(128,0),(184,0),(272,0),(1024,98803),(1024,66034),(1025,67058)]),([10,31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856],[(128,0),(184,0),(272,0),(376,0),(1024,444907),(1024,83425)]),([10,31,992,31744,1082401,2164802,4329604,8659208,32505856],[(82,0),(128,0),(1024,314854),(1024,69928),(1024,83425),(1025,300532),(1025,300697),(1025,66034),(1025,69928),(1025,98803)]),([10,31,992,31744,1082401,2164802,4329604,17318416,32505856],[(312,0),(1024,117217),(1024,281062),(1024,444907),(1025,98803),(1025,98968),(1025,66034),(1025,267763),(1025,300532)]),([10,31,992,31744,1082401,4329604,8659208,17318416,32505856],[(2,0),(18,0),(57,0),(73,0),(82,0),(106,0),(138,0),(144,0),(146,0),(201,0),(216,0),(217,0),(233,0),(249,0),(257,0),(322,0),(1024,67255),(1024,100024),(1024,83425),(1025,66034),(1025,67255),(1025,98803),(1025,268984),(1025,300532),(1025,437944)]),([10,31,992,31744,2164802,4329604,8659208,17318416,32505856],[(96,0),(144,0),(216,0),(1024,66034),(1024,98803),(1024,83425),(1025,66034),(1025,267763),(1025,66199)]),([10,31,992,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(96,0),(128,0),(184,0),(216,0),(272,0),(284,0),(376,0),(1024,502195),(1024,666040)]),([10,31,992,1015808,1082401,2164802,4329604,8659208,32505856],[(2,0),(22,0),(73,0),(96,0),(97,0),(128,0),(129,0),(217,0),(273,0),(1024,69928),(1024,502195),(1024,511270),(1025,69928),(1025,300532),(1025,300697),(1025,436723),(1025,437944)]),([10,31,992,1015808,1082401,2164802,4329604,17318416,32505856],[(184,0),(312,0),(1024,502195),(1024,666040),(1024,510049),(1025,436723),(1025,437944)]),([10,31,992,1015808,1082401,4329604,8659208,17318416,32505856],[(96,0),(144,0),(169,0),(201,0),(216,0),(1024,67255),(1024,100024),(1024,301753),(1025,437944),(1025,67255),(1025,268984),(1025,436723)]),([10,31,992,1015808,2164802,4329604,8659208,17318416,32505856],[(96,0),(169,0),(201,0),(216,0),(1024,66034),(1024,98803),(1024,300532),(1025,436723),(1025,436888),(1025,437944)]),([10,31,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[(1024,72997),(1024,496915),(1025,69933)]),([10,31,31744,1015808,1082401,2164802,4329604,8659208,32505856],[(1024,69928),(1024,72997),(1024,496915),(1025,69928),(1025,300532)]),([10,31,31744,1015808,1082401,2164802,4329604,17318416,32505856],[(1024,72997),(1024,496915),(1024,510049),(1025,267763),(1025,268984),(1025,436723)]),([10,31,31744,1015808,1082401,2164802,8659208,17318416,32505856],[(168,0),(1024,72997),(1024,302149),(1024,496915),(1025,69928),(1025,66034),(1025,66199),(1025,69933),(1025,300532),(1025,301753)]),([10,31,31744,1015808,1082401,4329604,8659208,17318416,32505856],[(1024,67255),(1024,72997),(1024,100024),(1025,268984),(1025,301753),(1025,437944),(1025,67255)]),([10,31,31744,1015808,2164802,4329604,8659208,17318416,32505856],[(1024,72997),(1024,66034),(1024,98803),(1025,267763),(1025,300697),(1025,268787),(1025,305652)])]
def t120 : BT := .nd (blockTree b126) [10,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416] (blockTree b127)
def t121 : BT := .nd t119 [9,31,1015808,1082401,2194498,8659208,17318416,32505856] t120
def t122 : BT := .nd t118 [9,31,31744,1015808,1082401,2164802,17318416,32641156] t121
def t123 : BT := .nd t115 [9,31,992,31744,1082401,4329604,9412872,17318416,32505856] t122
def t124 : BT := .nd t108 [8,31,1082401,2164802,2165730,8659208,17809936,32505856] t123
def t125 : BT := .nd t93 [8,31,992,1082401,2164802,4357252,8659208,17809936] t124
def t126 : BT := .nd t62 [7,31,32736,1015808,1082401,2164802,4329604,8659720,32505856] t125
def mT : BT := t126
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
theorem cb64 : Covered mP (blockTree b64) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb65 : Covered mP (blockTree b65) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb66 : Covered mP (blockTree b66) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb67 : Covered mP (blockTree b67) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb68 : Covered mP (blockTree b68) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb69 : Covered mP (blockTree b69) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb70 : Covered mP (blockTree b70) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb71 : Covered mP (blockTree b71) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb72 : Covered mP (blockTree b72) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb73 : Covered mP (blockTree b73) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb74 : Covered mP (blockTree b74) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb75 : Covered mP (blockTree b75) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb76 : Covered mP (blockTree b76) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb77 : Covered mP (blockTree b77) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb78 : Covered mP (blockTree b78) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb79 : Covered mP (blockTree b79) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb80 : Covered mP (blockTree b80) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb81 : Covered mP (blockTree b81) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb82 : Covered mP (blockTree b82) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb83 : Covered mP (blockTree b83) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb84 : Covered mP (blockTree b84) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb85 : Covered mP (blockTree b85) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb86 : Covered mP (blockTree b86) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb87 : Covered mP (blockTree b87) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb88 : Covered mP (blockTree b88) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb89 : Covered mP (blockTree b89) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb90 : Covered mP (blockTree b90) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb91 : Covered mP (blockTree b91) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb92 : Covered mP (blockTree b92) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb93 : Covered mP (blockTree b93) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb94 : Covered mP (blockTree b94) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb95 : Covered mP (blockTree b95) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb96 : Covered mP (blockTree b96) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb97 : Covered mP (blockTree b97) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb98 : Covered mP (blockTree b98) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb99 : Covered mP (blockTree b99) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb100 : Covered mP (blockTree b100) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb101 : Covered mP (blockTree b101) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb102 : Covered mP (blockTree b102) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb103 : Covered mP (blockTree b103) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb104 : Covered mP (blockTree b104) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb105 : Covered mP (blockTree b105) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb106 : Covered mP (blockTree b106) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb107 : Covered mP (blockTree b107) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb108 : Covered mP (blockTree b108) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb109 : Covered mP (blockTree b109) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb110 : Covered mP (blockTree b110) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb111 : Covered mP (blockTree b111) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb112 : Covered mP (blockTree b112) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb113 : Covered mP (blockTree b113) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb114 : Covered mP (blockTree b114) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb115 : Covered mP (blockTree b115) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb116 : Covered mP (blockTree b116) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb117 : Covered mP (blockTree b117) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb118 : Covered mP (blockTree b118) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb119 : Covered mP (blockTree b119) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb120 : Covered mP (blockTree b120) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb121 : Covered mP (blockTree b121) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb122 : Covered mP (blockTree b122) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb123 : Covered mP (blockTree b123) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb124 : Covered mP (blockTree b124) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb125 : Covered mP (blockTree b125) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb126 : Covered mP (blockTree b126) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb127 : Covered mP (blockTree b127) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct0 : Covered mP t0 := coveredNode cb0 cb1 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct1 : Covered mP t1 := coveredNode cb2 cb3 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct2 : Covered mP t2 := coveredNode ct0 ct1 (h := [(168,0)]) (by decide +kernel)
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
theorem ct7 : Covered mP t7 := coveredNode cb8 cb9 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct8 : Covered mP t8 := coveredNode cb10 cb11 (h := []) (by decide +kernel)
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
theorem ct12 : Covered mP t12 := coveredNode ct10 ct11 (h := [(96,0),(184,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct13 : Covered mP t13 := coveredNode ct9 ct12 (h := [(128,0),(216,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct14 : Covered mP t14 := coveredNode ct6 ct13 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct15 : Covered mP t15 := coveredNode cb16 cb17 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct16 : Covered mP t16 := coveredNode cb18 cb19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct17 : Covered mP t17 := coveredNode ct15 ct16 (h := [(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct18 : Covered mP t18 := coveredNode cb20 cb21 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct19 : Covered mP t19 := coveredNode cb22 cb23 (h := [(96,0),(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct20 : Covered mP t20 := coveredNode ct18 ct19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct21 : Covered mP t21 := coveredNode ct17 ct20 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct22 : Covered mP t22 := coveredNode cb24 cb25 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct23 : Covered mP t23 := coveredNode cb26 cb27 (h := []) (by decide +kernel)
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
theorem ct27 : Covered mP t27 := coveredNode ct25 ct26 (h := [(72,0)]) (by decide +kernel)
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
theorem ct31 : Covered mP t31 := coveredNode cb32 cb33 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct32 : Covered mP t32 := coveredNode cb34 cb35 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct33 : Covered mP t33 := coveredNode ct31 ct32 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct34 : Covered mP t34 := coveredNode cb36 cb37 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct35 : Covered mP t35 := coveredNode cb38 cb39 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct36 : Covered mP t36 := coveredNode ct34 ct35 (h := [(1024,65640),(1024,77926)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct37 : Covered mP t37 := coveredNode ct33 ct36 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct38 : Covered mP t38 := coveredNode cb40 cb41 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct39 : Covered mP t39 := coveredNode cb42 cb43 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct40 : Covered mP t40 := coveredNode ct38 ct39 (h := [(1024,491635),(1024,655480)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct41 : Covered mP t41 := coveredNode cb44 cb45 (h := [(72,0),(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct42 : Covered mP t42 := coveredNode cb46 cb47 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct43 : Covered mP t43 := coveredNode ct41 ct42 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct44 : Covered mP t44 := coveredNode ct40 ct43 (h := [(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct45 : Covered mP t45 := coveredNode ct37 ct44 (h := [(1024,78118),(1024,65831)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct46 : Covered mP t46 := coveredNode cb48 cb49 (h := [(72,0),(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct47 : Covered mP t47 := coveredNode cb50 cb51 (h := [(248,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct48 : Covered mP t48 := coveredNode ct46 ct47 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct49 : Covered mP t49 := coveredNode cb52 cb53 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct50 : Covered mP t50 := coveredNode cb54 cb55 (h := [(72,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct51 : Covered mP t51 := coveredNode ct49 ct50 (h := [(1024,301561),(1024,69928),(1025,66233)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct52 : Covered mP t52 := coveredNode ct48 ct51 (h := [(1024,502024),(1024,67255)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct53 : Covered mP t53 := coveredNode cb56 cb57 (h := [(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct54 : Covered mP t54 := coveredNode cb58 cb59 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct55 : Covered mP t55 := coveredNode ct53 ct54 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct56 : Covered mP t56 := coveredNode cb60 cb61 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct57 : Covered mP t57 := coveredNode cb62 cb63 (h := [(1024,67046),(1024,72161)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct58 : Covered mP t58 := coveredNode ct56 ct57 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct59 : Covered mP t59 := coveredNode ct55 ct58 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct60 : Covered mP t60 := coveredNode ct52 ct59 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct61 : Covered mP t61 := coveredNode ct45 ct60 (h := [(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct62 : Covered mP t62 := coveredNode ct30 ct61 (h := [(1024,267956),(1024,300101)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct63 : Covered mP t63 := coveredNode cb64 cb65 (h := [(1024,66034),(1024,98803),(1024,83425),(1025,67255),(1025,279224)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct64 : Covered mP t64 := coveredNode cb66 cb67 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct65 : Covered mP t65 := coveredNode ct63 ct64 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct66 : Covered mP t66 := coveredNode cb68 cb69 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct67 : Covered mP t67 := coveredNode cb70 cb71 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct68 : Covered mP t68 := coveredNode ct66 ct67 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct69 : Covered mP t69 := coveredNode ct65 ct68 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct70 : Covered mP t70 := coveredNode cb72 cb73 (h := [(1024,502035),(1024,69896)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct71 : Covered mP t71 := coveredNode cb74 cb75 (h := [(1024,502055),(1024,67255)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct72 : Covered mP t72 := coveredNode ct70 ct71 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct73 : Covered mP t73 := coveredNode cb76 cb77 (h := [(1024,710722),(1024,300101),(1025,70123)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct74 : Covered mP t74 := coveredNode cb78 cb79 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct75 : Covered mP t75 := coveredNode ct73 ct74 (h := [(96,0),(1024,67046),(1024,72161),(1025,318137)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct76 : Covered mP t76 := coveredNode ct72 ct75 (h := [(1024,309313),(1024,300101)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct77 : Covered mP t77 := coveredNode ct69 ct76 (h := [(1024,511042),(1024,69896)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct78 : Covered mP t78 := coveredNode cb80 cb81 (h := [(304,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct79 : Covered mP t79 := coveredNode cb82 cb83 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct80 : Covered mP t80 := coveredNode ct78 ct79 (h := [(1024,67046),(1024,72161),(1025,437944)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct81 : Covered mP t81 := coveredNode cb84 cb85 (h := [(1024,65832),(1024,655640),(1024,72993),(1025,300532),(1025,309945)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct82 : Covered mP t82 := coveredNode cb86 cb87 (h := [(128,0),(168,0),(348,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct83 : Covered mP t83 := coveredNode ct81 ct82 (h := [(128,0),(1024,655480),(1024,491635)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct84 : Covered mP t84 := coveredNode ct80 ct83 (h := [(1024,492646),(1024,69896)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct85 : Covered mP t85 := coveredNode cb88 cb89 (h := [(128,0),(312,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct86 : Covered mP t86 := coveredNode cb90 cb91 (h := [(1024,99832),(1024,69928),(1025,66233),(1025,268584)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct87 : Covered mP t87 := coveredNode ct85 ct86 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct88 : Covered mP t88 := coveredNode cb92 cb93 (h := [(96,0),(128,0),(1024,700711),(1024,502195),(1025,431769)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct89 : Covered mP t89 := coveredNode cb94 cb95 (h := [(96,0),(1024,440818),(1024,502195)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct90 : Covered mP t90 := coveredNode ct88 ct89 (h := [(96,0),(128,0),(272,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct91 : Covered mP t91 := coveredNode ct87 ct90 (h := [(96,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct92 : Covered mP t92 := coveredNode ct84 ct91 (h := [(96,0),(128,0),(256,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct93 : Covered mP t93 := coveredNode ct77 ct92 (h := [(198,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct94 : Covered mP t94 := coveredNode cb96 cb97 (h := [(72,0),(200,0),(248,0),(272,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct95 : Covered mP t95 := coveredNode cb98 cb99 (h := [(168,0),(1024,66231),(1024,99000),(1025,67255)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct96 : Covered mP t96 := coveredNode ct94 ct95 (h := [(72,0),(1024,712999),(1024,69928),(1025,302571),(1025,436723)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct97 : Covered mP t97 := coveredNode cb100 cb101 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct98 : Covered mP t98 := coveredNode cb102 cb103 (h := [(1024,78117),(1024,508198)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct99 : Covered mP t99 := coveredNode ct97 ct98 (h := [(128,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct100 : Covered mP t100 := coveredNode ct96 ct99 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct101 : Covered mP t101 := coveredNode cb104 cb105 (h := [(1024,279617),(1024,300101)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct102 : Covered mP t102 := coveredNode cb106 cb107 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct103 : Covered mP t103 := coveredNode ct101 ct102 (h := [(1024,281067),(1024,69896),(1025,104883),(1025,431769)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct104 : Covered mP t104 := coveredNode cb108 cb109 (h := [(1024,309943),(1024,502195),(1025,70957)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct105 : Covered mP t105 := coveredNode cb110 cb111 (h := [(1024,66034),(1024,502035),(1025,678585)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct106 : Covered mP t106 := coveredNode ct104 ct105 (h := [(1024,309313),(1024,300101)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct107 : Covered mP t107 := coveredNode ct103 ct106 (h := [(1024,309314),(1024,69927),(1025,66661)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct108 : Covered mP t108 := coveredNode ct100 ct107 (h := [(246,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct109 : Covered mP t109 := coveredNode cb112 cb113 (h := [(1024,502055),(1024,503078)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct110 : Covered mP t110 := coveredNode cb114 cb115 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct111 : Covered mP t111 := coveredNode ct109 ct110 (h := [(1024,508993),(1024,497075),(1025,65844)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct112 : Covered mP t112 := coveredNode cb116 cb117 (h := [(272,0),(408,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct113 : Covered mP t113 := coveredNode cb118 cb119 (h := [(128,0),(1024,444907),(1024,83425)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct114 : Covered mP t114 := coveredNode ct112 ct113 (h := [(128,0),(232,0),(240,0),(336,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct115 : Covered mP t115 := coveredNode ct111 ct114 (h := [(1024,511078),(1024,69736)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct116 : Covered mP t116 := coveredNode cb120 cb121 (h := [(96,0),(128,0),(312,0),(1024,666040),(1024,69896),(1025,69928)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct117 : Covered mP t117 := coveredNode cb122 cb123 (h := [(168,0),(216,0),(228,0),(1024,502195),(1024,666040)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct118 : Covered mP t118 := coveredNode ct116 ct117 (h := [(96,0),(1024,301753),(1024,69928)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct119 : Covered mP t119 := coveredNode cb124 cb125 (h := [(1024,72997),(1024,100024),(1024,66835),(1025,301753),(1025,268984),(1025,437944),(1025,67255),(1025,497335)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct120 : Covered mP t120 := coveredNode cb126 cb127 (h := [(232,0),(240,0),(336,0),(1024,450187),(1024,88705),(1025,67255)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct121 : Covered mP t121 := coveredNode ct119 ct120 (h := [(1024,72997),(1024,302149),(1024,496915),(1025,69928),(1025,66034),(1025,66199),(1025,300532)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct122 : Covered mP t122 := coveredNode ct118 ct121 (h := [(1024,72997),(1024,496915),(1024,510049),(1025,267763),(1025,268984),(1025,436723)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct123 : Covered mP t123 := coveredNode ct115 ct122 (h := [(96,0),(1024,100024),(1024,67255)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct124 : Covered mP t124 := coveredNode ct108 ct123 (h := [(72,0),(128,0),(1024,501829),(1024,505921),(1025,311796)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct125 : Covered mP t125 := coveredNode ct93 ct124 (h := [(1024,450187),(1024,78465)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct126 : Covered mP t126 := coveredNode ct62 ct125 (h := [(96,0),(128,0)]) (by decide +kernel)
theorem mgood : Covered mP mT := ct126
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3187468 : ℕ).testBit (5 * u.val + v.val)) C) :=
  bigSigned 3187468 10 2 0 PD_ PM_ XS_ G_ mT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) mgood (by decide +kernel)
end PEqualNP.Outside.L_meta_19527_aux

theorem PEqualNP.Outside.L_meta_19527 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3187468 : ℕ).testBit (5 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19527_aux.result
