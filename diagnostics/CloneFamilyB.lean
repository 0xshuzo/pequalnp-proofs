import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21872.Duplication

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
theorem mono_primitives {C : Circuit} (hm : Monotone2 C) :
    FanInTwo C ∧ ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  constructor
  · intro g hg
    obtain ⟨hh,hd⟩ := hm _ hg
    refine ⟨?_,hd⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh ⊢
    tauto
  · intro g hg h
    have hh := (hm g hg).1
    simp [h] at hh

def MonSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : MonSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ MonSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, hm, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  obtain ⟨ok, noNot⟩ := mono_primitives hm
  set gs := C.gates with hgs
  have hnok : ∀ g ∈ gs, NOk g := fun g hg =>
    ⟨ok g hg, fun hgnot => False.elim (noNot g hg hgnot)⟩
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x :=
    fun x => hev x
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
    have hmono : Monotone2 (⟨acc.2, j⟩ : Circuit) := by
      intro g hg
      obtain ⟨hh,hd⟩ := elim_ok n gs (initStats n b, []) (by simp) g hg
      have hh' := elim_nonot n gs (initStats n b, []) noNot (by simp) g hg
      refine ⟨?_,hd⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
      tauto
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, hmono, le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ExtendsBits (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (x y : List Bool) (h : ExtendsBits x y) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => h.2 i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h.2 i ht⟩

theorem getD_snoc (x : List Bool) (b : Bool) : (x ++ [b]).getD x.length false = b := by
  simp

theorem gate_step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : ExtendsBits x y) : ExtendsBits (step x g) (step y g) := by
  refine ⟨by simp [step, h.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i x.length with hlt | heq | hgt
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 i hi
  · subst i
    rw [step, getD_snoc] at hi
    rw [h.1, step, getD_snoc]
    exact gate_map_mono g.op hop g.inputs x y h hi
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
    contradiction

theorem gates_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ExtendsBits x y) :
    ExtendsBits (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have ht : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (List.mem_cons_of_mem _ hk)
    exact ih ht _ _ (gate_step_mono g (hgs g (by simp)) x y hxy)

theorem circuit_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hxy : ExtendsBits x y) (hx : C.eval x = true) : C.eval y = true := by
  have hop g (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hC g hg).1
  exact (gates_mono C.gates hop x y hxy).2 C.output hx



def bank {r c : Nat} (u : Fin r) (bits : Fin c → Bool) : Fin (r+c) → Bool :=
  Fin.append (fun i => decide (i = u)) bits

def hot {c : Nat} (v : Fin c) : Fin c → Bool := fun i => decide (i = v)

theorem bank_list {r c : Nat} (u : Fin r) (v : Fin c) :
    List.ofFn (bank u (hot v)) = oneEach u v := by
  rw [bank, List.ofFn_fin_append]
  rfl

theorem hot_cast {c : Nat} (v : Fin c) :
    hot v.castSucc = Fin.snoc (hot v) false := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hot]
  intro eq
  have hv := congrArg Fin.val eq
  change c = v.val at hv
  omega

theorem hot_last (c : Nat) :
    hot (Fin.last c) = Fin.snoc (fun _ : Fin c => false) true := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hot]

theorem withLast {r c : Nat} (u : Fin r) (x : Fin c → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (bank u x) b) = List.ofFn (bank u (Fin.snoc x b)) := by
  rw [ofFn_snoc, bank, List.ofFn_fin_append, bank, List.ofFn_fin_append, ofFn_snoc, List.append_assoc]

theorem castRow {r c : Nat} (u : Fin r) (v : Fin c) :
    List.ofFn (Fin.snoc (bank u (hot v)) false) = oneEach u v.castSucc := by
  rw [withLast, ← hot_cast, bank_list]

theorem lastRow {r c : Nat} (u : Fin r) :
    List.ofFn (Fin.snoc (bank u (fun _ : Fin c => false)) true) = oneEach u (Fin.last c) := by
  rw [withLast, ← hot_last, bank_list]

theorem extends_ofFn {n : Nat} {a b : Fin n → Bool} (h : ∀ i, a i = true → b i = true) :
    ExtendsBits (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using h ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem extends_row {r c : Nat} (u : Fin r) (v : Fin c) :
    ExtendsBits (List.ofFn (Fin.snoc (bank u (fun _ : Fin c => false)) false))
      (List.ofFn (Fin.snoc (bank u (hot v)) false)) := by
  apply extends_ofFn
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.snoc_castSucc]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j <;> simp [bank]

theorem toggleLast {n : Nat} (v : Fin n → Bool) :
    Function.update (Fin.snoc v false : Fin (n+1) → Bool) (Fin.last n) (!((Fin.snoc v false : Fin (n+1) → Bool) (Fin.last n))) = (Fin.snoc v true : Fin (n+1) → Bool) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem paidColumn {r c s : Nat} (A : Fin r → Fin (c+1) → Bool)
    (u p : Fin r) (z q : Fin c) (hlast : A u (Fin.last c) = true)
    (hzero : A u z.castSucc = false) (hpos : A p q.castSucc = true)
    (h : RepSizeAtMost A s) :
    ∃ k, k+1 ≤ s ∧ RepSizeAtMost (fun i (v : Fin c) => A i v.castSucc) k := by
  obtain ⟨C,hm,hs,rep⟩ := h
  let n := r+c
  let f : BFn (n+1) := fun x => C.eval (List.ofFn x)
  let bare : Fin n → Bool := bank u (fun _ : Fin c => false)
  have old (i : Fin r) (v : Fin c) : f (Fin.snoc (bank i (hot v)) false) = A i v.castSucc := by
    change C.eval (List.ofFn (Fin.snoc (bank i (hot v)) false)) = _
    rw [castRow]
    exact rep i v.castSucc
  have yes : f (Fin.snoc bare true) = true := by
    change C.eval (List.ofFn (Fin.snoc (bank u (fun _ : Fin c => false)) true)) = true
    rw [lastRow,rep,hlast]
  have no : f (Fin.snoc bare false) = false := by
    cases hv : f (Fin.snoc bare false) with
    | false => rfl
    | true =>
      have bad := circuit_mono C hm _ _ (extends_row u z) hv
      change f (Fin.snoc (bank u (hot z)) false) = true at bad
      rw [old,hzero] at bad
      contradiction
  have dep : ∃ x : Fin (n+1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x := by
    refine ⟨Fin.snoc bare false, ?_⟩
    rw [toggleLast,yes,no]
    decide
  have nc : ∃ x y : Fin n → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false) := by
    refine ⟨bank p (hot q),bank u (hot z),?_⟩
    rw [old,old,hpos,hzero]
    decide
  obtain ⟨k,hk,D,hd,hsize,ev⟩ := gate_elim_one n f false s dep nc ⟨C,hm,hs,fun _ => rfl⟩
  refine ⟨k,hk,D,hd,hsize,?_⟩
  intro i v
  rw [← bank_list,ev]
  exact old i v
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

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
    (hc : MonSize n h s) : MonSize m (fun x => h (x ∘ π)) s := by
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


def joinMap {n : Nat} (p i : Fin n) : Fin (n+2) :=
  if i = p then Fin.last (n+1) else i.castSucc.castSucc

def meld {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) (i : Fin n) : Bool :=
  if i = p then x p.castSucc || x (Fin.last n) else x i.castSucc

def extraBit {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) : Fin (n+2) → Bool :=
  Fin.snoc x (x p.castSucc || x (Fin.last n))

def joinGate {n : Nat} (p : Fin n) : Gate := ⟨.or,[p.val,n]⟩

theorem joinRead {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) :
    extraBit p x ∘ joinMap p = meld p x := by
  funext i
  by_cases h : i = p <;> simp [extraBit,joinMap,meld,h]

theorem arrayGet {k : Nat} (x : Fin k → Bool) (i : Fin k) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem joinStep {n : Nat} (p : Fin n) (x : Fin (n+1) → Bool) :
    step (List.ofFn x) (joinGate p) = List.ofFn (extraBit p x) := by
  have hp := arrayGet x p.castSucc
  have hn := arrayGet x (Fin.last n)
  simp only [Fin.val_castSucc,Fin.val_last] at hp hn
  rw [extraBit,ofFn_snoc]
  change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD p.val false, (List.ofFn x).getD n false]] = _
  rw [hp,hn]
  cases x p.castSucc <;> cases x (Fin.last n) <;> rfl

theorem mergePhysical {n s : Nat} (p : Fin n) (f : BFn n) (h : MonSize n f s) :
    MonSize (n+1) (fun x => f (meld p x)) (s+1) := by
  obtain ⟨D,hm,hs,ev⟩ := relabel_size (joinMap p) f s h
  let E : Circuit := ⟨joinGate p :: D.gates,D.output⟩
  refine ⟨E,?_,?_,?_⟩
  · intro g hg
    change g ∈ joinGate p :: D.gates at hg
    rcases List.mem_cons.mp hg with h | h
    · subst g
      simp [joinGate]
    · exact hm _ h
  · change (joinGate p :: D.gates).length ≤ s+1
    change D.gates.length ≤ s at hs
    simpa using Nat.succ_le_succ hs
  · intro x
    change D.eval (step (List.ofFn x) (joinGate p)) = _
    rw [joinStep,ev]
    exact congrArg f (joinRead p x)

theorem meldFalse {n : Nat} (p : Fin n) (x : Fin n → Bool) :
    meld p (Fin.snoc x false) = x := by
  funext i
  by_cases h : i = p <;> simp [meld,h]

theorem meldTrue {r c : Nat} (u : Fin r) (t : Fin c) :
    meld (Fin.natAdd r t) (Fin.snoc (bank u (fun _ : Fin c => false)) true) = bank u (hot t) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have ne : Fin.castAdd c a ≠ Fin.natAdd r t := by
      intro eq
      have hh := congrArg Fin.val eq
      simp at hh
      omega
    simp [meld,ne,bank]
  · by_cases h : b = t
    · subst b
      simp [meld,bank,hot]
    · have ne : Fin.natAdd r b ≠ Fin.natAdd r t := by
        intro eq
        apply h
        apply Fin.ext
        have hh := congrArg Fin.val eq
        simpa using hh
      simp only [meld, if_neg ne, Fin.snoc_castSucc]
      simp [bank,hot,h]

def duplicate {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (u : Fin r) (v : Fin (c+1)) : Bool :=
  A u (Fin.lastCases t (fun j => j) v)

theorem duplicate_upper {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (h : RepSizeAtMost A s) :
    RepSizeAtMost (duplicate A t) (s+1) := by
  obtain ⟨C,hm,hs,rep⟩ := h
  let f : BFn (r+c) := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hk,ev⟩ := mergePhysical (Fin.natAdd r t) f ⟨C,hm,hs,fun _ => rfl⟩
  refine ⟨D,hd,hk,?_⟩
  intro u v
  refine Fin.lastCases ?_ (fun i => ?_) v
  · rw [← lastRow,ev]
    change f (meld (Fin.natAdd r t) (Fin.snoc (bank u (fun _ : Fin c => false)) true)) = _
    rw [meldTrue]
    change C.eval (List.ofFn (bank u (hot t))) = _
    rw [bank_list]
    simpa [duplicate] using rep u t
  · rw [← castRow,ev]
    change f (meld (Fin.natAdd r t) (Fin.snoc (bank u (hot i)) false)) = _
    rw [meldFalse]
    change C.eval (List.ofFn (bank u (hot i))) = _
    rw [bank_list]
    simpa [duplicate] using rep u i

def tr {r c : Nat} (A : Fin r → Fin c → Bool) : Fin c → Fin r → Bool := fun v u => A u v

def swapBank (r c : Nat) : Fin (r+c) → Fin (c+r) :=
  Fin.addCases (fun i => Fin.natAdd c i) (fun j => Fin.castAdd r j)

theorem swapInput {r c : Nat} (u : Fin r) (v : Fin c) :
    bank v (hot u) ∘ swapBank r c = bank u (hot v) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [swapBank,bank,hot]

theorem transpose_cost {r c s : Nat} (A : Fin r → Fin c → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost (tr A) s := by
  obtain ⟨C,hm,hs,rep⟩ := h
  let f : BFn (r+c) := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hk,ev⟩ := relabel_size (swapBank r c) f s ⟨C,hm,hs,fun _ => rfl⟩
  refine ⟨D,hd,hk,?_⟩
  intro v u
  rw [← bank_list,ev]
  change f (bank v (hot u) ∘ swapBank r c) = _
  rw [swapInput]
  change C.eval (List.ofFn (bank u (hot v))) = _
  rw [bank_list]
  exact rep u v

theorem twinColumnIff {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c)
    (u : Fin r) (v : Fin c) (ht : A u t = true) (hv : A u v = false) :
    RepSizeAtMost (duplicate A t) (s+1) ↔ RepSizeAtMost A s := by
  refine ⟨?_,duplicate_upper A t⟩
  intro h
  obtain ⟨k,hk,D,hm,hs,hrep⟩ := paidColumn (duplicate A t) u u v t
    (by simpa [duplicate] using ht) (by simpa [duplicate] using hv) (by simpa [duplicate] using ht) h
  refine ⟨D,hm,by omega,?_⟩
  intro i j
  simpa [duplicate] using hrep i j

def duplicateRow {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin r) := tr (duplicate (tr A) t)

theorem twinRowIff {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin r)
    (u : Fin c) (v : Fin r) (ht : A t u = true) (hv : A v u = false) :
    RepSizeAtMost (duplicateRow A t) (s+1) ↔ RepSizeAtMost A s := by
  constructor
  · intro h
    have h' : RepSizeAtMost (duplicate (tr A) t) (s+1) := transpose_cost _ h
    exact transpose_cost _ ((twinColumnIff (tr A) t u v ht hv).mp h')
  · intro h
    exact transpose_cost _ ((twinColumnIff (tr A) t u v ht hv).mpr (transpose_cost _ h))
end PEqualNP.Outside.L_meta_21872.Duplication



namespace PEqualNP.Outside.L_meta_21872.BaseMinor

open PEqualNP.CircuitLowerBounds


open PEqualNP.MetaComplexity

def formulaVars {n : ℕ} : DMFormula n → Set (Fin n)
  | .lit i _ => {i}
  | .and f g => formulaVars f ∪ formulaVars g
  | .or f g => formulaVars f ∪ formulaVars g

def positiveReadOnce {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False
  | .or f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False

def singletonInput {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun i => decide (i = a)

def pairInput {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i => decide (i = a ∨ i = b)

def cornerIndices {n : ℕ} (a b c d : Fin n) : Set (Fin n) := {a, b, c, d}

theorem formula_agree {n : ℕ} (f : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ i ∈ formulaVars f, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | lit i b =>
      have hi := h i (by simp [formulaVars])
      simp [DMFormula.eval, hi]
  | and f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]
  | or f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]

theorem formula_zero {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f) :
    f.eval (fun _ => false) = false := by
  induction f with
  | lit i b =>
      change b = true at h
      simp [DMFormula.eval, h]
  | and f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]
  | or f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]

theorem formula_mono {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    f.eval x = true → f.eval y = true := by
  induction f with
  | lit i b =>
      change b = true at h
      simpa [DMFormula.eval, h] using hxy i
  | and f g ihf ihg =>
      simp only [DMFormula.eval, Bool.and_eq_true]
      rintro ⟨hxF, hxG⟩
      exact ⟨ihf h.1 hxF, ihg h.2.1 hxG⟩
  | or f g ihf ihg =>
      simp only [DMFormula.eval, Bool.or_eq_true]
      rintro (hxF | hxG)
      · exact Or.inl (ihf h.1 hxF)
      · exact Or.inr (ihg h.2.1 hxG)

theorem input_pair_comm {n : ℕ} (a b : Fin n) : pairInput a b = pairInput b a := by
  funext i
  simp [pairInput, or_comm]

theorem formula_pair_swap {n : ℕ} (f : DMFormula n) (a : Fin n) {b c : Fin n}
    (hb : b ∉ formulaVars f) (hc : c ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (pairInput a c) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  have hindC : i ≠ c := fun he => hc (he ▸ hi)
  simp [pairInput, hindB, hindC]

theorem formula_pair_singleton {n : ℕ} (f : DMFormula n) (a : Fin n) {b : Fin n}
    (hb : b ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (singletonInput a) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  simp [pairInput, singletonInput, hindB]

theorem some_vars_of_pair {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f) {a b : Fin n}
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∨ b ∈ formulaVars f := by
  classical
  by_contra hab
  have hzero : f.eval (pairInput a b) = f.eval (fun _ => false) := by
    apply formula_agree
    intro i hi
    have hiA : i ≠ a := fun he => hab (Or.inl (he ▸ hi))
    have hiB : i ≠ b := fun he => hab (Or.inr (he ▸ hi))
    simp [pairInput, hiA, hiB]
  rw [h, formula_zero f hf] at hzero
  contradiction

theorem both_vars_of_pair {n : ℕ} (f : DMFormula n) {a b : Fin n}
    (hsa : f.eval (singletonInput a) = false)
    (hsb : f.eval (singletonInput b) = false)
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∧ b ∈ formulaVars f := by
  classical
  constructor
  · by_contra hA
    have he := formula_pair_singleton f b hA
    rw [← input_pair_comm a b, h, hsb] at he
    contradiction
  · by_contra hB
    have he := formula_pair_singleton f a hB
    rw [h, hsa] at he
    contradiction

theorem opposite_vars_of_and_pair {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b : Fin n}
    (hF : f.eval (pairInput a b) = true) (hG : g.eval (pairInput a b) = true) :
    a ∈ formulaVars f ↔ b ∉ formulaVars f := by
  rcases some_vars_of_pair f hf hF with hFa | hFb
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact False.elim (hfg a hFa hGa)
    · exact ⟨fun _ hFb => hfg b hFb hGb, fun _ => hFa⟩
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact ⟨fun hFa => False.elim (hfg a hFa hGa), fun hnFb => False.elim (hnFb hFb)⟩
    · exact False.elim (hfg b hFb hGb)

theorem formula_and_corner_side {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hacF : f.eval (pairInput a c) = true) (hacG : g.eval (pairInput a c) = true)
    (hadF : f.eval (pairInput a d) = true) (hadG : g.eval (pairInput a d) = true)
    (hbcF : f.eval (pairInput b c) = true) (hbcG : g.eval (pairInput b c) = true) :
    f.eval (pairInput b d) = true := by
  classical
  have hac := opposite_vars_of_and_pair f g hf hg hfg hacF hacG
  have had := opposite_vars_of_and_pair f g hf hg hfg hadF hadG
  have hbc := opposite_vars_of_and_pair f g hf hg hfg hbcF hbcG
  by_cases hA : a ∈ formulaVars f
  · exact (formula_pair_swap f b (had.mp hA) (hac.mp hA)).trans hbcF
  · have hC : c ∈ formulaVars f :=
      Classical.byContradiction (fun hnC => hA (hac.mpr hnC))
    have hB : b ∉ formulaVars f := fun hb => hbc.mp hb hC
    have he : f.eval (pairInput b d) = f.eval (pairInput a d) := by
      rw [input_pair_comm b d, input_pair_comm a d]
      exact formula_pair_swap f d hB hA
    exact he.trans hadF

theorem force_or_corner {n : ℕ} (f g : DMFormula n)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hsF : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hsG : ∀ i ∈ cornerIndices a b c d, g.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true ∨ g.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true ∨ g.eval (pairInput b c) = true) :
    f.eval (pairInput a d) = true ∧ f.eval (pairInput b c) = true := by
  have ha := both_vars_of_pair f (hsF a (by simp [cornerIndices]))
    (hsF c (by simp [cornerIndices])) hac
  constructor
  · rcases had with had | had
    · exact had
    · exact False.elim (hfg a ha.1
        (both_vars_of_pair g (hsG a (by simp [cornerIndices]))
          (hsG d (by simp [cornerIndices])) had).1)
  · rcases hbc with hbc | hbc
    · exact hbc
    · exact False.elim (hfg c ha.2
        (both_vars_of_pair g (hsG b (by simp [cornerIndices]))
          (hsG c (by simp [cornerIndices])) hbc).2)

theorem positive_read_once_corners {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f)
    (a b c d : Fin n)
    (hs : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true) : f.eval (pairInput b d) = true := by
  induction f with
  | lit i polarity =>
      change polarity = true at hf
      have ha : i = a ∨ i = c := by
        simpa [DMFormula.eval, hf, pairInput] using hac
      have hin : i ∈ cornerIndices a b c d := by
        rcases ha with h | h <;> simp [cornerIndices, h]
      have hi := hs i hin
      simp [DMFormula.eval, hf, singletonInput] at hi
  | and f g ihF ihG =>
      simp only [DMFormula.eval, Bool.and_eq_true] at hac had hbc ⊢
      exact
        ⟨formula_and_corner_side f g hf.1 hf.2.1 hf.2.2
            hac.1 hac.2 had.1 had.2 hbc.1 hbc.2,
          formula_and_corner_side g f hf.2.1 hf.1 (fun i hg hf' => hf.2.2 i hf' hg)
            hac.2 hac.1 had.2 had.1 hbc.2 hbc.1⟩
  | or f g ihF ihG =>
      simp only [DMFormula.eval, Bool.or_eq_true] at hac had hbc ⊢
      have hsF (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          f.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : f.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      have hsG (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          g.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : g.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      rcases hac with hacF | hacG
      · have h := force_or_corner f g hf.2.2 hsF hsG hacF had hbc
        exact Or.inl (ihF hf.1 hsF hacF h.1 h.2)
      · have h := force_or_corner g f (fun i hg hf' => hf.2.2 i hf' hg) hsG hsF
          hacG had.symm hbc.symm
        exact Or.inr (ihG hf.2.1 hsG hacG h.1 h.2)

theorem formula_singleton_false_of_pair {n : ℕ} (f : DMFormula n)
    (hf : positiveReadOnce f) (a b : Fin n) (h : f.eval (pairInput a b) = false) :
    f.eval (singletonInput a) = false := by
  cases hsingle : f.eval (singletonInput a) with
  | false => rfl
  | true =>
      have hsubset (i : Fin n) (hi : singletonInput a i = true) : pairInput a b i = true := by
        have he : i = a := of_decide_eq_true hi
        simp [pairInput, he]
      have hpair := formula_mono f hf hsubset hsingle
      exact False.elim (Bool.false_ne_true (h.symm.trans hpair))


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def expand (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) : Finset ℕ :=
  if wire ∈ live then live.erase wire ∪ deps.toFinset else live

theorem expand_le (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2) :
    (expand live wire deps).card ≤ live.card + 1 := by
  by_cases hw : wire ∈ live
  · rw [expand, ite_eq_left hw]
    have hs := Finset.card_erase_add_one hw
    have hu := Finset.card_union_le (live.erase wire) deps.toFinset
    have hdf := List.toFinset_card_le deps
    omega
  · simp [expand, hw]

theorem expand_full (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2)
    (he : (expand live wire deps).card = live.card + 1) :
    wire ∈ live ∧ deps.length = 2 ∧ deps.Nodup ∧ Disjoint (live.erase wire) deps.toFinset := by
  have hw : wire ∈ live := by
    by_contra hn
    simp [expand, hn] at he
  rw [expand, ite_eq_left hw] at he
  have hs := Finset.card_erase_add_one hw
  have hu := Finset.card_union_add_card_inter (live.erase wire) deps.toFinset
  have hdf := List.toFinset_card_le deps
  have hi : ((live.erase wire) ∩ deps.toFinset).card = 0 := by omega
  refine ⟨hw, by omega, ?_, ?_⟩
  · exact Multiset.toFinset_card_eq_card_iff_nodup.mp (by
      change deps.toFinset.card = deps.length
      omega)
  · exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)

def frontier : ℕ → List Gate → Finset ℕ → Finset ℕ
  | _, [], live => live
  | n, g :: gs, live => expand (frontier (n + 1) gs live) n (g.inputs.filter (· < n))

theorem frontier_le (n : ℕ) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (frontier n gs live).card ≤ live.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [frontier]
  | cons g gs ih =>
    have ht := ih (n + 1) (fun a ha => hf a (List.mem_cons_of_mem g ha))
    have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
    simpa [frontier, List.length_cons, Nat.add_assoc] using
      (expand_le (frontier (n + 1) gs live) n _ hg).trans (Nat.add_le_add_right ht 1)

theorem frontier_full (n : ℕ) (g : Gate) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ a ∈ g :: gs, a.inputs.length ≤ 2)
    (h : (frontier n (g :: gs) live).card = live.card + (g :: gs).length) :
    let rest := frontier (n + 1) gs live
    let deps := g.inputs.filter (· < n)
    rest.card = live.card + gs.length ∧ n ∈ rest ∧ deps.length = 2 ∧ deps.Nodup ∧
      Disjoint (rest.erase n) deps.toFinset := by
  dsimp only
  have ht := frontier_le (n + 1) gs live (fun a ha => hf a (List.mem_cons_of_mem g ha))
  have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
  have hb := expand_le (frontier (n + 1) gs live) n _ hg
  rw [frontier, List.length_cons] at h
  refine ⟨by omega, expand_full (frontier (n + 1) gs live) n _ hg ?_⟩
  omega

def Agree (live : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ live, x.getD i false = y.getD i false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst i; simp [step]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem agree_step (n : ℕ) (g : Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (expand live n (g.inputs.filter (· < n))) x y) :
    Agree live (step x g) (step y g) := by
  intro i hi
  rw [getD_step, getD_step, hx, hy]
  by_cases hn : i = n
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    congr 1
    apply List.map_congr_left
    intro j hj
    by_cases hjn : j < n
    · apply ha j
      simp [expand, hi, hj, hjn]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · rw [ite_eq_right hn, ite_eq_right hn]
    apply ha i
    by_cases h : n ∈ live
    · simp [expand, h, hi, hn]
    · simpa [expand, h] using hi

theorem agree_frontier (n : ℕ) (gs : List Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (frontier n gs live) x y) : Agree live (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing n x y with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih (n + 1) (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy]) ?_
    exact agree_step n g (frontier (n + 1) gs live) x y hx hy ha

theorem eval_agree_frontier (n : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ frontier n C.gates {C.output}, x.getD i false = y.getD i false) :
    C.eval x = C.eval y :=
  agree_frontier n C.gates {C.output} x y hx hy h C.output (by simp)

def plug {m : ℕ} (t : Fin m) (r : DMFormula m) : DMFormula m → DMFormula m
  | .lit i b => if i = t then r else .lit i b
  | .and f g => .and (plug t r f) (plug t r g)
  | .or f g => .or (plug t r f) (plug t r g)

theorem plug_vars {m : ℕ} (t i : Fin m) (r f : DMFormula m) :
    i ∈ formulaVars (plug t r f) ↔
      (i ∈ formulaVars f ∧ i ≠ t) ∨ (t ∈ formulaVars f ∧ i ∈ formulaVars r) := by
  induction f with
  | lit j b =>
    by_cases h : j = t
    · subst j; simp [plug, formulaVars]
    · simp only [plug, h, ite_false, formulaVars, Set.mem_singleton_iff]
      grind
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug,formulaVars,Set.mem_union,ihf,ihg]
    constructor
    · rintro ((⟨h, hne⟩ | ⟨h, hr⟩) | (⟨h, hne⟩ | ⟨h, hr⟩))
      · exact Or.inl ⟨Or.inl h, hne⟩
      · exact Or.inr ⟨Or.inl h, hr⟩
      · exact Or.inl ⟨Or.inr h, hne⟩
      · exact Or.inr ⟨Or.inr h, hr⟩
    · rintro (⟨h | h, hne⟩ | ⟨h | h, hr⟩)
      · exact Or.inl (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inl ⟨h, hne⟩)
      · exact Or.inl (Or.inr ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, hr⟩)

theorem plug_read {m : ℕ} (t : Fin m) (r f : DMFormula m)
    (hr : positiveReadOnce r) (hf : positiveReadOnce f)
    (hs : ∀ i ∈ formulaVars f, i ≠ t → i ∈ formulaVars r → False) :
    positiveReadOnce (plug t r f) := by
  induction f with
  | lit i b =>
    by_cases h : i = t
    · simpa [plug, h] using hr
    · simpa [plug, h] using hf
  | and f g ihf ihg | or f g ihf ihg =>
    refine ⟨ihf hf.1 (fun i hi => hs i (Or.inl hi)),
      ihg hf.2.1 (fun i hi => hs i (Or.inr hi)), ?_⟩
    intro i hiF hiG
    rw [plug_vars] at hiF hiG
    rcases hiF with ⟨hiF, hiT⟩ | ⟨htF, hiR⟩ <;> rcases hiG with ⟨hiG, hiT'⟩ | ⟨htG, hiR'⟩
    · exact hf.2.2 i hiF hiG
    · exact hs i (Or.inl hiF) hiT hiR'
    · exact hs i (Or.inr hiG) hiT' hiR
    · exact hf.2.2 t htF htG

theorem plug_eval {m : ℕ} (t : Fin m) (r f : DMFormula m) (hf : positiveReadOnce f)
    (x : Fin m → Bool) : (plug t r f).eval x = f.eval (fun i => if i = t then r.eval x else x i) := by
  induction f with
  | lit i b =>
    change b = true at hf
    subst b
    by_cases h : i = t <;> simp [plug, DMFormula.eval, h]
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug, DMFormula.eval, ihf hf.1, ihg hf.2.1]

def value {m : ℕ} (w : List Bool) (i : Fin m) : Bool := w.getD i.val false

def supportsFrontier {m : ℕ} (live : Finset ℕ) (f : DMFormula m) : Prop :=
  ∀ i : Fin m, i.val ∈ live ↔ i ∈ formulaVars f

def twoGate {m : ℕ} (o : GateOp) (a b : Fin m) : DMFormula m :=
  match o with
  | .and => .and (.lit a true) (.lit b true)
  | _ => .or (.lit a true) (.lit b true)

theorem twoGate_vars {m : ℕ} (o : GateOp) (a b i : Fin m) :
    i ∈ formulaVars (twoGate o a b) ↔ i = a ∨ i = b := by
  cases o <;> simp only [twoGate, formulaVars, Set.mem_union, Set.mem_singleton_iff]

theorem twoGate_read {m : ℕ} (o : GateOp) (a b : Fin m) (hne : a ≠ b) :
    positiveReadOnce (twoGate o a b) := by
  cases o <;> simp [twoGate, formulaVars, positiveReadOnce, hne]

theorem twoGate_eval {m : ℕ} (g : Gate) (a b : Fin m) (x : List Bool)
    (ho : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hi : g.inputs = [a.val,b.val]) :
    (twoGate g.op a b).eval (value x) = g.op.eval (g.inputs.map fun j => x.getD j false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  rcases ho with h | h <;> simp [twoGate, DMFormula.eval, hi, h, value, GateOp.eval]

theorem frontier_tree {m : ℕ} (n : ℕ) (gs : List Gate) (live : Finset ℕ) (f : DMFormula m)
    (hn : n + gs.length ≤ m) (hr : positiveReadOnce f) (hm : supportsFrontier live f)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier n gs live).card = live.card + gs.length) :
    ∃ F : DMFormula m, positiveReadOnce F ∧ supportsFrontier (frontier n gs live) F ∧
      ∀ w : List Bool, w.length = n → F.eval (value w) = f.eval (value (gs.foldl step w)) := by
  induction gs generalizing n with
  | nil => exact ⟨f, hr, hm, fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ht, hmem, hlen, hnd, hdj⟩ :=
      frontier_full n g gs live (fun a ha => (hf a ha).2) hfull
    obtain ⟨F, hFr, hFm, hFe⟩ := ih (n + 1) (by simp only [List.length_cons] at hn; omega)
      (fun a ha => hf a (List.mem_cons_of_mem g ha)) ht
    have hg := hf g (by simp)
    have he : g.inputs.filter (· < n) = g.inputs :=
      List.filter_sublist.eq_of_length_le (by omega)
    have hb : n < m := by simp only [List.length_cons] at hn; omega
    let t : Fin m := ⟨n, hb⟩
    rw [he] at hlen hnd hdj
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
      cases he' : g.inputs with
      | nil => simp [he'] at hlen
      | cons a rest =>
        cases rest with
        | nil => simp [he'] at hlen
        | cons b tail =>
          have hc : tail = [] := by simpa [he'] using hlen
          exact ⟨a, b, by simp [hc]⟩
    have hn' := List.filter_eq_self.mp he
    have ha : a < n := of_decide_eq_true (hn' a (by simp [hab]))
    have hb' : b < n := of_decide_eq_true (hn' b (by simp [hab]))
    let A : Fin m := ⟨a, ha.trans hb⟩
    let B : Fin m := ⟨b, hb'.trans hb⟩
    have hab' : A ≠ B := by
      intro e
      have ea := congrArg Fin.val e
      simp [hab, show a = b from ea] at hnd
    let r := twoGate g.op A B
    have htv : t ∈ formulaVars F := (hFm t).mp hmem
    have hpd : ∀ i ∈ formulaVars F, i ≠ t → i ∈ formulaVars r → False := by
      intro i hif hit hir
      apply (Finset.disjoint_left.mp hdj) (a := i.val)
      · exact Finset.mem_erase.mpr ⟨fun equ => hit (Fin.ext equ), (hFm i).mpr hif⟩
      · obtain hi | hi := (twoGate_vars g.op A B i).mp hir <;> simp [hi, hab, A, B]
    refine ⟨plug t r F, plug_read t r F (twoGate_read g.op A B hab') hFr hpd, ?_, ?_⟩
    · intro i
      rw [frontier, expand, ite_eq_left hmem, he, Finset.mem_union, Finset.mem_erase,
        List.mem_toFinset, hFm i, plug_vars, twoGate_vars]
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqA : i.val = a ↔ i = A := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqB : i.val = b ↔ i = B := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false, hEqA, hEqB, htv, true_and]
      constructor
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨h2, fun e => h1 (hEq.mpr e)⟩
        · exact Or.inr h
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨fun e => h2 (hEq.mp e), h1⟩
        · exact Or.inr h
    · intro w hw
      rw [plug_eval t r F hFr]
      simp only [List.foldl_cons]
      rw [← hFe (step w g) (by simp [step, hw])]
      congr 1
      funext i
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [value, getD_step, hw, hEq]
      rw [show r.eval (value w) = g.op.eval (g.inputs.map fun j => w.getD j false) from
        twoGate_eval g A B w hg.1 hab]

theorem circuit_tree (n m : ℕ) (C : Circuit) (hn : n + C.gates.length ≤ m) (ho : C.output < m)
    (hf : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier n C.gates {C.output}).card = 1 + C.gates.length) :
    ∃ F : DMFormula m, positiveReadOnce F ∧ supportsFrontier (frontier n C.gates {C.output}) F ∧
      ∀ w : List Bool, w.length = n → F.eval (value w) = C.eval w := by
  let t : Fin m := ⟨C.output, ho⟩
  have hm : supportsFrontier {C.output} (.lit t true) := by
    intro i
    simpa [formulaVars] using (show i.val = C.output ↔ i = t from
      ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩)
  have h : (frontier n C.gates {C.output}).card = ({C.output} : Finset ℕ).card + C.gates.length := by
    simpa using hfull
  obtain ⟨F, fr, fm, fe⟩ := frontier_tree n C.gates {C.output} (.lit t true) hn rfl hm hf h
  refine ⟨F, fr, fm, ?_⟩
  intro w hw
  change F.eval (value w) = (C.gates.foldl step w).getD C.output false
  simpa [DMFormula.eval, value, t] using fe w hw


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ExtendsBits (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (x y : List Bool) (h : ExtendsBits x y) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => h.2 i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h.2 i ht⟩

theorem getD_snoc (x : List Bool) (b : Bool) : (x ++ [b]).getD x.length false = b := by
  simp

theorem gate_step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : ExtendsBits x y) : ExtendsBits (step x g) (step y g) := by
  refine ⟨by simp [step, h.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i x.length with hlt | heq | hgt
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 i hi
  · subst i
    rw [step, getD_snoc] at hi
    rw [h.1, step, getD_snoc]
    exact gate_map_mono g.op hop g.inputs x y h hi
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
    contradiction

theorem gates_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ExtendsBits x y) :
    ExtendsBits (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have ht : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (List.mem_cons_of_mem _ hk)
    exact ih ht _ _ (gate_step_mono g (hgs g (by simp)) x y hxy)

theorem circuit_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hxy : ExtendsBits x y) (hx : C.eval x = true) : C.eval y = true := by
  have hop g (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hC g hg).1
  exact (gates_mono C.gates hop x y hxy).2 C.output hx

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, step, Nat.add_comm, Nat.add_left_comm]

def Essential (C : Circuit) (n i : ℕ) : Prop :=
  ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ C.eval x ≠ C.eval y ∧
    ∀ k : ℕ, k ≠ i → x.getD k false = y.getD k false

def Trace (C : Circuit) (n : ℕ) (x : Fin (2*n) → Bool) (b : Bool) : Prop :=
  ∃ w : List Bool, w.length = n ∧ value w = x ∧ C.eval w = b

theorem essential_frontier (C : Circuit) (n : ℕ) (S : Finset ℕ)
    (he : ∀ i ∈ S, Essential C n i) : S ⊆ frontier n C.gates {C.output} := by
  intro i hi
  obtain ⟨x, y, hx, hy, hne, hxy⟩ := he i hi
  by_contra hnot
  apply hne
  apply eval_agree_frontier n C x y hx hy
  intro j hj
  exact hxy j (fun eq => hnot (eq ▸ hj))

theorem essential_price (C : Circuit) (n : ℕ) (S : Finset ℕ) (hm : Monotone2 C)
    (he : ∀ i ∈ S, Essential C n i) : S.card ≤ 1 + C.size := by
  have hmin := Finset.card_le_card (essential_frontier C n S he)
  have bound := frontier_le n C.gates {C.output} (fun g hg => (hm g hg).2)
  rw [Finset.card_singleton] at bound
  exact hmin.trans bound

theorem subset_corner_price (C : Circuit) (n : ℕ) (S : Finset ℕ) (hS : S.card ≤ n)
    (hm : Monotone2 C) (he : ∀ i ∈ S, Essential C n i) (a b c d : Fin (2*n))
    (hs : ∀ i ∈ cornerIndices a b c d, Trace C n (singletonInput i) false)
    (hac : Trace C n (pairInput a c) true) (had : Trace C n (pairInput a d) true)
    (hbc : Trace C n (pairInput b c) true) (hbd : Trace C n (pairInput b d) false) :
    S.card ≤ C.size := by
  by_contra hsmall
  have hlen : C.gates.length < S.card := by change ¬ S.card ≤ C.gates.length at hsmall; omega
  have hmin := Finset.card_le_card (essential_frontier C n S he)
  have bound := frontier_le n C.gates {C.output} (fun g hg => (hm g hg).2)
  rw [Finset.card_singleton] at bound
  have tight : (frontier n C.gates {C.output}).card = 1+C.gates.length := by omega
  have hout : C.output < 2*n := by
    obtain ⟨w, hw, _, val⟩ := hac
    by_contra h
    change (C.gates.foldl step w).getD C.output false = true at val
    rw [List.getD_eq_default _ _ (by rw [run_length, hw]; omega)] at val
    contradiction
  obtain ⟨f, hread, _, eval⟩ := circuit_tree n (2*n) C (by omega) hout hm tight
  have real (x : Fin (2*n) → Bool) (out : Bool) (h : Trace C n x out) : f.eval x = out := by
    obtain ⟨w, hw, rfl, hv⟩ := h
    exact (eval w hw).trans hv
  have htrue := positive_read_once_corners f hread a b c d
    (fun i hi => real _ _ (hs i hi)) (real _ _ hac) (real _ _ had) (real _ _ hbc)
  exact Bool.false_ne_true ((real _ _ hbd).symm.trans htrue)

def table (u : Fin 3) (v : Fin 4) : Bool := (379 : ℕ).testBit (4 * u.val + v.val)

def oneWire (i : Fin 7) : List Bool := List.ofFn fun j : Fin 7 => decide (j = i)

theorem one_len (i : Fin 7) : (oneWire i).length = 7 := by simp [oneWire]
theorem pair_len (u : Fin 3) (v : Fin 4) : (oneEach u v).length = 7 := by simp [oneEach]

abbrev Witness := Fin 3 × Fin 4 × Fin 3 × Fin 4 × Fin 7

def requiredPins : Finset ℕ := {0, 1, 3, 4, 5, 6}

def witness (i : Fin 7) : Witness :=
  ([(0, 1, 2, 1, 4), (1, 1, 2, 1, 4), (0, 1, 2, 1, 4), (0, 0, 0, 2, 0), (0, 1, 0, 2, 0), (1, 2, 1, 3, 1), (0, 3, 0, 2, 0)] : List Witness).getD i.val (0, 1, 2, 1, 4)

def certifies (i : Fin 7) (w : Witness) : Prop :=
  let (u,v,q,p,j) := w
  table u v = true ∧ table q p = false ∧
    (∀ k : Fin 7, (oneWire j).getD k.val false = true → (oneEach q p).getD k.val false = true) ∧
    ∀ k : Fin 7, k ≠ i → (oneWire j).getD k.val false = (oneEach u v).getD k.val false

instance (i : Fin 7) (w : Witness) : Decidable (certifies i w) := by
  rcases w with ⟨u,v,q,p,j⟩
  unfold certifies
  infer_instance

theorem witnesses : ∀ i : Fin 7, i.val ∈ requiredPins → certifies i (witness i) := by decide +kernel

theorem one_false (C : Circuit) (hm : Monotone2 C) (hc : Represents table C)
    (j : Fin 7) (q : Fin 3) (p : Fin 4) (ha : table q p = false)
    (hh : ∀ k : Fin 7, (oneWire j).getD k.val false = true → (oneEach q p).getD k.val false = true) :
    C.eval (oneWire j) = false := by
  cases h : C.eval (oneWire j) with
  | false => rfl
  | true =>
    have he : ExtendsBits (oneWire j) (oneEach q p) := by
      refine ⟨(one_len _).trans (pair_len _ _).symm, ?_⟩
      intro k val
      by_cases hk : k < 7
      · exact hh ⟨k,hk⟩ val
      · rw [List.getD_eq_default _ _ (by rw [one_len]; omega)] at val
        contradiction
    have bad := circuit_mono C hm _ _ he h
    rw [hc _ _, ha] at bad
    contradiction

theorem mandatory (C : Circuit) (hm : Monotone2 C) (hc : Represents table C) :
    ∀ i ∈ requiredPins, Essential C 7 i := by
  intro i hmem
  have bounded : requiredPins ⊆ Finset.range 7 := by decide
  have hi : i < 7 := Finset.mem_range.mp (bounded hmem)
  obtain ⟨u,v,q,p,j,hp,hn,hle,heq⟩ : ∃ (u : Fin 3) (v : Fin 4) (q : Fin 3) (p : Fin 4) (j : Fin 7),
      certifies ⟨i,hi⟩ (u,v,q,p,j) := by
    have aux (w : Witness) (hw : certifies ⟨i,hi⟩ w) :
        ∃ (u : Fin 3) (v : Fin 4) (q : Fin 3) (p : Fin 4) (j : Fin 7),
          certifies ⟨i,hi⟩ (u,v,q,p,j) := by
      rcases w with ⟨u,v,q,p,j⟩
      exact ⟨u,v,q,p,j,hw⟩
    exact aux _ (witnesses ⟨i,hi⟩ hmem)
  refine ⟨oneWire j, oneEach u v, one_len _, pair_len _ _, ?_, ?_⟩
  · rw [one_false C hm hc j q p hn hle, hc _ _, hp]
    decide
  · intro k hk
    by_cases h : k < 7
    · exact heq ⟨k,h⟩ (fun e => hk (congrArg Fin.val e))
    · rw [List.getD_eq_default _ _ (by rw [one_len]; omega),
          List.getD_eq_default _ _ (by rw [pair_len]; omega)]

theorem price (C : Circuit) (hm : Monotone2 C) (hc : Represents table C) : 6 ≤ C.size := by
  have count : requiredPins.card = 6 := by decide
  rw [← count]
  apply subset_corner_price C 7 requiredPins (by decide) hm (mandatory C hm hc) 0 1 4 6
  · intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 6 := by simpa [cornerIndices] using hi
    rcases hi' with rfl | rfl | rfl | rfl
    · refine ⟨oneWire 0, one_len _, ?_, one_false C hm hc 0 0 2 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 14, value (oneWire 0) k = singletonInput 0 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 1, one_len _, ?_, one_false C hm hc 1 1 3 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 14, value (oneWire 1) k = singletonInput 1 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 4, one_len _, ?_, one_false C hm hc 4 2 1 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 14, value (oneWire 4) k = singletonInput 4 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 6, one_len _, ?_, one_false C hm hc 6 1 3 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 14, value (oneWire 6) k = singletonInput 6 k := by decide +kernel
      exact h k
  · refine ⟨oneEach (0 : Fin 3) (1 : Fin 4), pair_len _ _, ?_, (hc 0 1).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 14, value (oneEach (0 : Fin 3) (1 : Fin 4)) k = pairInput 0 4 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (0 : Fin 3) (3 : Fin 4), pair_len _ _, ?_, (hc 0 3).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 14, value (oneEach (0 : Fin 3) (3 : Fin 4)) k = pairInput 0 6 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (1 : Fin 3) (1 : Fin 4), pair_len _ _, ?_, (hc 1 1).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 14, value (oneEach (1 : Fin 3) (1 : Fin 4)) k = pairInput 1 4 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (1 : Fin 3) (3 : Fin 4), pair_len _ _, ?_, (hc 1 3).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 14, value (oneEach (1 : Fin 3) (3 : Fin 4)) k = pairInput 1 6 k := by decide +kernel
    exact h k

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 5) := by
  rintro ⟨C, hm, hs, hr⟩
  have hp := price C hm hr
  omega

end PEqualNP.Outside.L_meta_21872.BaseMinor

namespace PEqualNP.Outside.L_meta_21872.Duplication
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Copies {a b : Nat} (A : Fin a → Fin b → Bool) :
    {r c : Nat} → (Fin r → Fin c → Bool) → Nat → Prop where
  | start : Copies A A 0
  | column {r c n} {B : Fin r → Fin c → Bool} (h : Copies A B n)
      (t : Fin c) (u : Fin r) (v : Fin c) (ht : B u t = true) (hv : B u v = false) :
      Copies A (duplicate B t) (n+1)
  | row {r c n} {B : Fin r → Fin c → Bool} (h : Copies A B n)
      (t : Fin r) (u : Fin c) (v : Fin r) (ht : B t u = true) (hv : B v u = false) :
      Copies A (duplicateRow B t) (n+1)

theorem copies_cost {a b r c n : Nat} {A : Fin a → Fin b → Bool} {B : Fin r → Fin c → Bool}
    (h : Copies A B n) (s : Nat) : RepSizeAtMost B (s+n) ↔ RepSizeAtMost A s := by
  induction h with
  | start => rfl
  | column h t u v ht hv ih => exact (twinColumnIff _ t u v ht hv).trans ih
  | row h t u v ht hv ih => exact (twinRowIff _ t u v ht hv).trans ih

def baseTable (u : Fin 3) (v : Fin 4) := (379 : Nat).testBit (4*u.val+v.val)
def baseCircuit : Circuit := ⟨[⟨.or,[4,6]⟩,⟨.or,[4,5]⟩,⟨.and,[0,7]⟩,
  ⟨.and,[1,8]⟩,⟨.or,[9,10]⟩,⟨.or,[11,3]⟩],12⟩
theorem baseUpper : RepSizeAtMost baseTable 6 := by
  exact ⟨baseCircuit,by simp [baseCircuit,Monotone2],by decide,by decide +kernel⟩

theorem baseLower : ¬ RepSizeAtMost baseTable 5 := PEqualNP.Outside.L_meta_21872.BaseMinor.result

theorem familyBounds {r c n : Nat} {B : Fin r → Fin c → Bool} (h : Copies baseTable B n) :
    ¬ RepSizeAtMost B (5+n) ∧ RepSizeAtMost B (6+n) :=
  ⟨fun hsmall => baseLower ((copies_cost h 5).mp hsmall), (copies_cost h 6).mpr baseUpper⟩

def stage1 := duplicateRow baseTable 0
def stage2 := duplicate stage1 1
def stage3 := duplicate stage2 3

theorem sourceChain : Copies baseTable stage3 3 := by
  have a : Copies baseTable stage1 1 :=
    Copies.row Copies.start 0 1 2 (by decide) (by decide)
  have b : Copies baseTable stage2 2 :=
    Copies.column a 1 0 2 (by decide) (by decide)
  exact Copies.column b 3 0 2 (by decide) (by decide)

def original (u : Fin 4) (v : Fin 6) := (327159 : Nat).testBit (6*u.val+v.val)
def rowMap : Fin 4 → Fin 4 := ![0,2,3,1]
def colMap : Fin 6 → Fin 6 := ![0,1,3,4,2,5]
def rawMap : Fin 10 → Fin 10 := ![0,3,1,2,4,5,8,6,7,9]
theorem sampleMap : ∀ (u : Fin 4) (v : Fin 6),
    bank u (hot v) ∘ rawMap = bank (rowMap u) (hot (colMap v)) := by decide +kernel
theorem valueMap : ∀ (u : Fin 4) (v : Fin 6), original (rowMap u) (colMap v) = stage3 u v := by decide +kernel

theorem permuteSource {s : Nat} (h : RepSizeAtMost original s) : RepSizeAtMost stage3 s := by
  obtain ⟨C,hm,hk,rows⟩ := h
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hsize,ev⟩ := relabel_size rawMap f s ⟨C,hm,hk,fun _ => rfl⟩
  refine ⟨D,hd,hsize,?_⟩
  intro i v
  rw [← bank_list, ev]
  change f (bank i (hot v) ∘ rawMap) = _
  rw [sampleMap]
  change C.eval (List.ofFn (bank (rowMap i) (hot (colMap v)))) = _
  rw [bank_list, rows, valueMap]
end PEqualNP.Outside.L_meta_21872.Duplication

open PEqualNP.Represents PEqualNP.Outside.L_meta_21872.Duplication in
theorem PEqualNP.Outside.L_meta_21872 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327159 : ℕ).testBit (6 * u.val + v.val)) 8) := fun h => (familyBounds sourceChain).1 (permuteSource h)
