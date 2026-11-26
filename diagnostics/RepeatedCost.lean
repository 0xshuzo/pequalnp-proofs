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


def bareRow {r c : Nat} (u : Fin r) := bank u (fun _ : Fin c => false)

def BareSize {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (s : Nat) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ Represents A C ∧
    ∀ u : Fin r, C.eval (List.ofFn (bareRow (c := c) u)) = A u t

theorem monoBudget {r c a b : Nat} {A : Fin r → Fin c → Bool}
    (h : RepSizeAtMost A a) (hb : a ≤ b) : RepSizeAtMost A b := by
  obtain ⟨C,hm,hs,hr⟩ := h
  exact ⟨C,hm,hs.trans hb,hr⟩

theorem snocRestrict {n : Nat} (x : Fin n → Bool) (v : Bool) :
    (Fin.snoc x v : Fin (n+1) → Bool) ∘ Fin.castSucc = x := by
  funext i
  simp

theorem noCharge {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (h : BareSize A t s) :
    RepSizeAtMost (duplicate A t) s := by
  obtain ⟨C,hm,hk,rows,bare⟩ := h
  let f : BFn (r+c) := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hs,ev⟩ := relabel_size Fin.castSucc f s ⟨C,hm,hk,fun _ => rfl⟩
  refine ⟨D,hd,hs,?_⟩
  intro u v
  refine Fin.lastCases ?_ (fun i => ?_) v
  · rw [← lastRow,ev]
    change f ((Fin.snoc (bareRow (c := c) u) true) ∘ Fin.castSucc) = _
    rw [snocRestrict]
    simpa [f,duplicate] using bare u
  · rw [← castRow,ev]
    change f ((Fin.snoc (bank u (hot i)) false) ∘ Fin.castSucc) = _
    rw [snocRestrict]
    change C.eval (List.ofFn (bank u (hot i))) = _
    rw [bank_list]
    simpa [duplicate] using rows u i

def repeatLast {n : Nat} (p : Fin n) : Fin (n+1) → Fin n := Fin.lastCases p (fun i => i)

theorem copySnoc {n : Nat} (p : Fin n) (x : Fin n → Bool) :
    x ∘ repeatLast p = (Fin.snoc x (x p) : Fin (n+1) → Bool) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [repeatLast]

theorem independence {n : Nat} (f : BFn (n+1))
    (h : ¬ ∃ y : Fin (n+1) → Bool, f (Function.update y (Fin.last n) (!y (Fin.last n))) ≠ f y)
    (x : Fin n → Bool) (a b : Bool) : f (Fin.snoc x a) = f (Fin.snoc x b) := by
  have htf : f (Fin.snoc x true) = f (Fin.snoc x false) := by
    by_contra bad
    apply h
    refine ⟨Fin.snoc x false, ?_⟩
    rw [toggleLast]
    exact bad
  cases a <;> cases b <;> first | rfl | exact htf | exact htf.symm

theorem duplicationCriterion {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c)
    (u p : Fin r) (v q : Fin c) (hp : A u v = true) (hq : A p q = false) :
    RepSizeAtMost (duplicate A t) s ↔ BareSize A t s ∨ ∃ k, k+1 ≤ s ∧ RepSizeAtMost A k := by
  constructor
  · intro h
    obtain ⟨C,hm,hcap,rep⟩ := h
    let n := r+c
    let f : BFn (n+1) := fun x => C.eval (List.ofFn x)
    have orig : MonSize (n+1) f s := ⟨C,hm,hcap,fun _ => rfl⟩
    have old (i : Fin r) (j : Fin c) : f (Fin.snoc (bank i (hot j)) false) = A i j := by
      change C.eval (List.ofFn (Fin.snoc (bank i (hot j)) false)) = _
      rw [castRow]
      simpa [duplicate] using rep i j.castSucc
    have newCol (i : Fin r) : f (Fin.snoc (bareRow (c := c) i) true) = A i t := by
      change C.eval (List.ofFn (Fin.snoc (bank i (fun _ : Fin c => false)) true)) = _
      rw [lastRow]
      simpa [duplicate] using rep i (Fin.last c)
    have nonconst : ∃ x y : Fin n → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false) := by
      refine ⟨bank u (hot v),bank p (hot q),?_⟩
      rw [old,old,hp,hq]
      decide
    by_cases dep : ∃ x : Fin (n+1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x
    · right
      obtain ⟨k,hk,D,hd,hs,ev⟩ := gate_elim_one n f false s dep nonconst orig
      refine ⟨k,hk,D,hd,hs,?_⟩
      intro i j
      rw [← bank_list,ev]
      exact old i j
    · left
      let pick : Fin n := Fin.natAdd r t
      obtain ⟨D,hd,hs,ev⟩ := relabel_size (repeatLast pick) f s orig
      have evalD (x : Fin n → Bool) (b : Bool) : D.eval (List.ofFn x) = f (Fin.snoc x b) := by
        rw [ev]
        change f (x ∘ repeatLast pick) = _
        rw [copySnoc]
        exact independence f dep x (x pick) b
      refine ⟨D,hd,hs,?_,?_⟩
      · intro i j
        rw [← bank_list]
        exact (evalD _ false).trans (old i j)
      · intro i
        exact (evalD _ true).trans (newCol i)
  · rintro (h | ⟨k,hk,h⟩)
    · exact noCharge A t h
    · exact monoBudget (duplicate_upper A t h) hk

theorem bare_snoc {r c : Nat} (u : Fin r) :
    List.ofFn (Fin.snoc (bareRow (c := c) u) false) = List.ofFn (bareRow (c := c+1) u) := by
  change List.ofFn (Fin.snoc (bank u (fun _ : Fin c => false)) false) = _
  rw [withLast]
  have eqv : (Fin.snoc (fun _ : Fin c => false) false : Fin (c+1) → Bool) = fun _ => false := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [eqv]
  rfl

theorem restrictFalse {n s : Nat} (p : Fin n) (f : BFn (n+1)) (h : MonSize (n+1) f s)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false)) :
    MonSize n (fun x => f (Fin.snoc x false)) s := by
  by_cases dep : ∃ x : Fin (n+1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x
  · obtain ⟨k,hk,D,hm,hs,hv⟩ := gate_elim_one n f false s dep hnc h
    exact ⟨D,hm,by omega,hv⟩
  · obtain ⟨D,hm,hs,hv⟩ := relabel_size (repeatLast p) f s h
    refine ⟨D,hm,hs,?_⟩
    intro x
    rw [hv]
    change f (x ∘ repeatLast p) = _
    rw [copySnoc]
    exact independence f dep x (x p) false

theorem bare_lower {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c)
    (u p : Fin r) (v q : Fin c) (hp : A u v = true) (hq : A p q = false)
    (h : BareSize (duplicate A t) t.castSucc s) : BareSize A t s := by
  obtain ⟨C,hm,hs,rep,bare⟩ := h
  let f : BFn (r+c+1) := fun x => C.eval (List.ofFn x)
  have core (i : Fin r) (j : Fin c) : f (Fin.snoc (bank i (hot j)) false) = A i j := by
    change C.eval (List.ofFn (Fin.snoc (bank i (hot j)) false)) = _
    rw [castRow]
    simpa [duplicate] using rep i j.castSucc
  have hnc : ∃ x y : Fin (r+c) → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false) := by
    refine ⟨bank u (hot v),bank p (hot q),?_⟩
    rw [core,core,hp,hq]
    decide
  obtain ⟨D,hd,hk,ev⟩ := restrictFalse (Fin.natAdd r t) f ⟨C,hm,hs,fun _ => rfl⟩ hnc
  refine ⟨D,hd,hk,?_,?_⟩
  · intro i j
    rw [← bank_list,ev]
    exact core i j
  · intro i
    rw [ev]
    change C.eval (List.ofFn (Fin.snoc (bareRow (c := c) i) false)) = _
    rw [bare_snoc]
    simpa [duplicate] using bare i

theorem bare_upper {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (h : BareSize A t s) :
    BareSize (duplicate A t) t.castSucc s := by
  obtain ⟨C,hm,hk,rows,bare⟩ := h
  let f : BFn (r+c) := fun x => C.eval (List.ofFn x)
  obtain ⟨D,hd,hs,ev⟩ := relabel_size Fin.castSucc f s ⟨C,hm,hk,fun _ => rfl⟩
  refine ⟨D,hd,hs,?_,?_⟩
  ·
    intro u v
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [← lastRow,ev]
      change f ((Fin.snoc (bareRow (c := c) u) true) ∘ Fin.castSucc) = _
      rw [snocRestrict]
      simpa [f,duplicate] using bare u
    · rw [← castRow,ev]
      change f ((Fin.snoc (bank u (hot i)) false) ∘ Fin.castSucc) = _
      rw [snocRestrict]
      change C.eval (List.ofFn (bank u (hot i))) = _
      rw [bank_list]
      simpa [duplicate] using rows u i
  · intro u
    rw [← bare_snoc,ev]
    change f ((Fin.snoc (bareRow (c := c) u) false) ∘ Fin.castSucc) = _
    rw [snocRestrict]
    simpa [f,duplicate] using bare u

def carry {c : Nat} (j : Fin c) : (k : Nat) → Fin (c+k)
  | 0 => j
  | k+1 => (carry j k).castSucc

def copiesOfColumn {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) :
    (k : Nat) → Fin r → Fin (c+k) → Bool
  | 0 => A
  | k+1 => duplicate (copiesOfColumn A t k) (carry t k)

theorem carry_value {r c : Nat} (A : Fin r → Fin c → Bool) (t j : Fin c) (u : Fin r) :
    ∀ k : Nat, copiesOfColumn A t k u (carry j k) = A u j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simpa [copiesOfColumn,carry,duplicate] using ih

theorem repeatedBare {r c s : Nat} (A : Fin r → Fin c → Bool) (t : Fin c)
    (u p : Fin r) (v q : Fin c) (hp : A u v = true) (hq : A p q = false) (n : Nat) :
    BareSize (copiesOfColumn A t n) (carry t n) s ↔ BareSize A t s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have a := (carry_value A t v u n).trans hp
    have b := (carry_value A t q p n).trans hq
    exact (Iff.intro (bare_lower _ (carry t n) u p (carry v n) (carry q n) a b) (bare_upper _ _)).trans ih

theorem bareMono {r c a b : Nat} {A : Fin r → Fin c → Bool} {t : Fin c}
    (h : BareSize A t a) (hb : a ≤ b) : BareSize A t b := by
  obtain ⟨C,hm,hs,hr,hex⟩ := h
  exact ⟨C,hm,hs.trans hb,hr,hex⟩

theorem repeatedCost {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c)
    (u p : Fin r) (v q : Fin c) (hp : A u v = true) (hq : A p q = false) (n s : Nat) :
    RepSizeAtMost (copiesOfColumn A t n) s ↔ BareSize A t s ∨ ∃ k, k+n ≤ s ∧ RepSizeAtMost A k := by
  induction n generalizing s with
  | zero =>
    constructor
    · exact fun h => Or.inr ⟨s,le_rfl,h⟩
    · rintro (⟨C,hm,hs,hr,_⟩ | ⟨k,hk,h⟩)
      · exact ⟨C,hm,hs,hr⟩
      · exact monoBudget h hk
  | succ n ih =>
    have a := (carry_value A t v u n).trans hp
    have b := (carry_value A t q p n).trans hq
    rw [copiesOfColumn, duplicationCriterion _ (carry t n) u p (carry v n) (carry q n) a b]
    constructor
    · rintro (h | ⟨k,hk,h⟩)
      · exact Or.inl ((repeatedBare A t u p v q hp hq n).mp h)
      · rcases (ih k).mp h with hx | ⟨g,hg,hy⟩
        · exact Or.inl (bareMono hx (by omega))
        · exact Or.inr ⟨g,by omega,hy⟩
    · rintro (h | ⟨k,hk,h⟩)
      · exact Or.inl ((repeatedBare A t u p v q hp hq n).mpr h)
      · exact Or.inr ⟨k+n,by omega,(ih (k+n)).mpr (Or.inr ⟨k,le_rfl,h⟩)⟩
end PEqualNP.Outside.L_meta_21872.Duplication

open PEqualNP.Represents PEqualNP.Outside.L_meta_21872.Duplication in
theorem PEqualNP.Outside.L_meta_21872 {r c : Nat} (A : Fin r → Fin c → Bool) (t : Fin c) (u p : Fin r) (v q : Fin c) (hp : A u v = true) (hq : A p q = false) (n s : Nat) : RepSizeAtMost (copiesOfColumn A t n) s ↔ BareSize A t s ∨ ∃ k, k+n ≤ s ∧ RepSizeAtMost A k := repeatedCost A t u p v q hp hq n s
