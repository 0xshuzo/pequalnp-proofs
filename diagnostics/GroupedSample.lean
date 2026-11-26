import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20550_aux

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
def urootHint (ws : List Nat) : Nat := (([([31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],238723),([31,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],237667),([31,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],133354),([31,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],132298),([31,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],469657),([31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416],647824),([31,992,31744,1082401,2164802,4329604,8659208,17318416,32505856],671353),([31,992,1015808,1082401,2164802,4329604,8659208,17318416,32505856],666073),([31,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],632017),([992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],689272)] : List (List Nat × Nat)).lookup (isort ws)).getD 0


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



def Y_ : Nat := 7880921
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
def PD_ : List (Nat × Nat) := [(1,4481205),(2,6705391),(3,3623106),(4,2082004),(5,754399),(6,106970),(7,45144),(8,14489),(9,31993),(10,24265),(11,4049),(12,1885),(13,795),(14,312),(15,41),(16,161),(17,229),(18,71),(19,22),(20,30),(21,10),(23,1),(24,1)]
def PM_ : List (Nat × Nat) := [(1,7880921),(2,7880921),(5,7880921),(8,7880921),(9,7880921),(10,7880921),(11,7880921),(12,7880921),(13,7880921),(15,7880921),(16,7880921),(17,7880921),(18,7880921),(23,7880921),(24,7880921)]
def G_ : List (List Nat) := [[0,2,1,3,4,5,7,6,8,9,10,12,11,13,14,15,17,16,18,19,20,22,21,23,24],[0,1,2,3,4,5,6,7,8,9,15,16,17,18,19,10,11,12,13,14,20,21,22,23,24],[0,2,1,3,4,5,7,6,8,9,15,17,16,18,19,10,12,11,13,14,20,22,21,23,24]]

def z0 : List Nat := [4,31,2096161,6494406,8659944,33047056]
def z1 : List Nat := [4,31,9436424,17318449]
def z2 : List Nat := [4,31,9436457,17318416]
def z3 : List Nat := [4,31,10485033,18366992]
def z4 : List Nat := [4,1047552,1082401,6494431,8659944,33047056]
def z5 : List Nat := [4,1047552,1082401,6494431,17318896,32776456]
def z6 : List Nat := [4,1048607,10485033,17318416]
def z7 : List Nat := [4,7542982,17318431,32506848]
def z8 : List Nat := [4,8659208,17318713,32506848]
def z9 : List Nat := [5,31,33,9436424,17318416]
def z10 : List Nat := [5,31,992,1082401,7339206,8659208,33047056]
def z11 : List Nat := [5,31,992,1113121,7313606,8659208,33047056]
def z12 : List Nat := [5,31,992,2096161,6494406,8659208,33047056]
def z13 : List Nat := [5,31,31744,2065441,6494406,8659944,33047056]
def z14 : List Nat := [5,31,31744,9412872,17318449]
def z15 : List Nat := [5,31,31744,9412905,17318416]
def z16 : List Nat := [5,31,31744,9413929,17318416]
def z17 : List Nat := [5,31,31744,10462505,18366992]
def z18 : List Nat := [5,31,31777,9412872,17318416]
def z19 : List Nat := [5,31,33825,9436424,17318416]
def z20 : List Nat := [5,31,64545,9412872,17318416]
def z21 : List Nat := [5,31,1047552,1082401,6494406,8659944,33047056]
def z22 : List Nat := [5,31,1047552,1082401,6494406,17318896,32776456]
def z23 : List Nat := [5,31,1047552,7542982,17318416]
def z24 : List Nat := [5,31,1047552,8659208,17318449]
def z25 : List Nat := [5,31,1047552,8659241,17318416]
def z26 : List Nat := [5,31,1047552,8693033,17318416]
def z27 : List Nat := [5,31,1047552,9741609,18366992]
def z28 : List Nat := [5,31,1047585,8659208,17318416]
def z29 : List Nat := [5,31,1048576,10485033,17318416]
def z30 : List Nat := [5,31,1082401,7339206,8659208,17318896,32505856]
def z31 : List Nat := [5,31,1082401,9436424,17318448]
def z32 : List Nat := [5,31,1082401,9436424,18366992]
def z33 : List Nat := [5,31,1082401,9436456,17318416]
def z34 : List Nat := [5,31,1083361,6494406,9436424,17318416,32505856]
def z35 : List Nat := [5,31,1113121,9412872,18366992]
def z36 : List Nat := [5,31,2096161,2164802,4329604,8659944,33047056]
def z37 : List Nat := [5,31,2096161,6494406,8659944,17318416,32505856]
def z38 : List Nat := [5,31,2096161,6494406,33047056]
def z39 : List Nat := [5,31,2096161,8659208,18366992]
def z40 : List Nat := [5,31,2096161,25977624,32776456]
def z41 : List Nat := [5,31,2096161,25977624,33047056]
def z42 : List Nat := [5,31,6494406,25977848,32777192]
def z43 : List Nat := [5,31,7542982,17318416,32506848]
def z44 : List Nat := [5,31,8659208,17318416,32506846]
def z45 : List Nat := [5,31,8659208,17318449,32506848]
def z46 : List Nat := [5,31,8659208,17318449,32506879]
def z47 : List Nat := [5,31,8659241,17318416,32506848]
def z48 : List Nat := [5,31,8659241,17318416,32506879]
def z49 : List Nat := [5,31,8682760,17318416,32537566]
def z50 : List Nat := [5,31,8693033,17318416,32506848]
def z51 : List Nat := [5,31,9436424,17318416,32708806]
def z52 : List Nat := [5,31,9436424,17318416,33520606]
def z53 : List Nat := [5,31,9436424,17318896,18400817]
def z54 : List Nat := [5,31,9437160,10485033,17318416]
def z55 : List Nat := [5,31,9741609,18366992,32506848]
def z56 : List Nat := [5,31,9742313,18400817,32776456]
def z57 : List Nat := [5,297,8659208,17318416,32506848]
def z58 : List Nat := [5,990,8659208,17318416,32505887]
def z59 : List Nat := [5,992,1047552,1082401,6494431,8659208,33047056]
def z60 : List Nat := [5,992,1047552,1082401,6494431,17318416,32776456]
def z61 : List Nat := [5,992,1082401,2164831,5241988,8659208,33047056]
def z62 : List Nat := [5,992,1082431,6494406,32776479]
def z63 : List Nat := [5,992,1082431,9436424,18400817]
def z64 : List Nat := [5,992,6494406,9437183,17318431]
def z65 : List Nat := [5,992,6494406,17318431,24117248]
def z66 : List Nat := [5,992,6494406,25707039,32505856]
def z67 : List Nat := [5,992,7542982,17318431,32505856]
def z68 : List Nat := [5,992,8659208,17318713,32505856]
def z69 : List Nat := [5,992,9436424,17318416,33553441]
def z70 : List Nat := [5,992,25977624,32539681,33047071]
def z71 : List Nat := [5,1023,8659208,17318449,32505887]
def z72 : List Nat := [5,1023,8659208,17318449,32506848]
def z73 : List Nat := [5,1023,8659241,17318416,32505887]
def z74 : List Nat := [5,1023,8659241,17318416,32506848]
def z75 : List Nat := [5,1023,9741609,18400817,32505887]
def z76 : List Nat := [5,1023,9741609,18400817,32506848]
def z77 : List Nat := [5,1023,9741609,25977624,32505887]
def z78 : List Nat := [5,1023,9741609,25977624,32506848]
def z79 : List Nat := [5,1023,18400817,25977624,32505887]
def z80 : List Nat := [5,1023,18400817,25977624,32506848]
def z81 : List Nat := [5,31744,1015808,1082401,6494431,8659944,33047056]
def z82 : List Nat := [5,31744,1015808,1082401,6494431,17318896,32776456]
def z83 : List Nat := [5,31744,1048607,10462505,17318416]
def z84 : List Nat := [5,1047552,1048607,6494406,17318416]
def z85 : List Nat := [5,1047552,1048607,9741609,17318416]
def z86 : List Nat := [5,1047552,1082401,2164802,4329631,8659944,33047056]
def z87 : List Nat := [5,1047552,1082401,2164802,4329631,17318896,32776456]
def z88 : List Nat := [5,1047552,1082401,6494431,8659208,17318896,32505856]
def z89 : List Nat := [5,1047552,1082401,6494431,8659944,17318416,32505856]
def z90 : List Nat := [5,1047552,1083361,6494431,8659208,17318416,32505856]
def z91 : List Nat := [5,1048544,8659208,17318416,33553441]
def z92 : List Nat := [5,1048544,9436424,17318416,32539681]
def z93 : List Nat := [5,1048576,6494406,17318431,32506848]
def z94 : List Nat := [5,1048607,1082401,9436424,17318416]
def z95 : List Nat := [5,1048607,1113121,9412872,17318416]
def z96 : List Nat := [5,1048607,2096161,8659208,17318416]
def z97 : List Nat := [5,1048607,6494406,17318416,32506848]
def z98 : List Nat := [5,1048607,9741609,17318416,32506848]
def z99 : List Nat := [5,1049568,6494406,17318431,32505856]
def z100 : List Nat := [5,1082401,2164831,5241988,8659208,17318896,32505856]
def z101 : List Nat := [5,1082401,6494406,17318911,32506848]
def z102 : List Nat := [5,1082401,6494406,32506848,33047071]
def z103 : List Nat := [5,1082401,17318911,25977624,32506848]
def z104 : List Nat := [5,1082401,25977624,32506848,33047071]
def z105 : List Nat := [5,1082431,6494406,8659944,32505887]
def z106 : List Nat := [5,1083361,9741609,17318425,32505856]
def z107 : List Nat := [5,1083391,6494406,8659208,32505887]
def z108 : List Nat := [5,1083391,6494406,17318416,32505887]
def z109 : List Nat := [5,1083391,8659208,18400817,32505887]
def z110 : List Nat := [5,1083391,9741609,17318416,32505887]
def z111 : List Nat := [5,2164802,5378180,17318431,32506848]
def z112 : List Nat := [5,6494406,8389600,17318431,32505856]
def z113 : List Nat := [5,6494406,8659208,17318911,32506848]
def z114 : List Nat := [5,6494406,8659944,17318431,32506848]
def z115 : List Nat := [5,6494406,8659944,17318431,32776456]
def z116 : List Nat := [5,8659208,17318416,32505887,33553441]
def z117 : List Nat := [5,8659208,17318431,32506848,32708806]
def z118 : List Nat := [5,8659208,17318911,18400817,32506848]
def z119 : List Nat := [5,8659944,9741609,17318425,32505856]
def z120 : List Nat := [5,8659944,17318431,18400817,32776456]
def z121 : List Nat := [5,8659944,25977624,32505887,32539681]
def z122 : List Nat := [5,8682760,17318416,32505887,33522721]
def z123 : List Nat := [5,9436424,17318416,32505887,32539681]
def z124 : List Nat := [5,9741609,18400817,32505887,32506848]
def z125 : List Nat := [5,9741609,25977624,32505887,32506848]
def z126 : List Nat := [5,18400817,25977624,32505887,32506848]
def z127 : List Nat := [6,9,992,9741609,18400817,32505856]
def z128 : List Nat := [6,9,992,9741609,25977624,32505856]
def z129 : List Nat := [6,9,1083361,9741609,17318416,32505856]
def z130 : List Nat := [6,9,8659944,9741609,17318416,32505856]
def z131 : List Nat := [6,31,32,1082401,9436424,17318416]
def z132 : List Nat := [6,31,33,31744,9412872,17318416]
def z133 : List Nat := [6,31,33,1047552,8659208,17318416]
def z134 : List Nat := [6,31,33,8659208,17318416,32506848]
def z135 : List Nat := [6,31,33,8659208,17318416,32506879]
def z136 : List Nat := [6,31,990,8659208,17318416,32505856]
def z137 : List Nat := [6,31,992,31744,1082401,7313606,8659208,33047056]
def z138 : List Nat := [6,31,992,31744,2065441,6494406,8659208,33047056]
def z139 : List Nat := [6,31,992,777975,1082401,6494406]
def z140 : List Nat := [6,31,992,777975,1082401,25977624]
def z141 : List Nat := [6,31,992,1047552,1082401,6494406,8659208,33047056]
def z142 : List Nat := [6,31,992,1047552,1082401,6494406,17318416,32776456]
def z143 : List Nat := [6,31,992,1047552,9741609,18400817]
def z144 : List Nat := [6,31,992,1047552,9741609,25977624]
def z145 : List Nat := [6,31,992,1047552,18400817,25977624]
def z146 : List Nat := [6,31,992,1048575,8693033,17318416]
def z147 : List Nat := [6,31,992,1048575,9741609,18400817]
def z148 : List Nat := [6,31,992,1048575,9741609,25977624]
def z149 : List Nat := [6,31,992,1048575,18400817,25977624]
def z150 : List Nat := [6,31,992,1082401,2164802,5241988,8659208,33047056]
def z151 : List Nat := [6,31,992,1082401,2194498,5214340,8659208,33047056]
def z152 : List Nat := [6,31,992,1082401,6494406,9436424,17318416,32505856]
def z153 : List Nat := [6,31,992,1082401,6494406,32776456]
def z154 : List Nat := [6,31,992,1082401,6494406,32776479]
def z155 : List Nat := [6,31,992,1082401,6494406,32777192]
def z156 : List Nat := [6,31,992,1082401,6520006,9412872,17318416,32505856]
def z157 : List Nat := [6,31,992,1082401,7339206,8659208,17318416,32505856]
def z158 : List Nat := [6,31,992,1082401,7576807,32776456]
def z159 : List Nat := [6,31,992,1082401,9436424,16236015]
def z160 : List Nat := [6,31,992,1082401,9436424,17318416]
def z161 : List Nat := [6,31,992,1082401,9436424,18400817]
def z162 : List Nat := [6,31,992,1082401,17318416,24118007]
def z163 : List Nat := [6,31,992,1082401,25436424,33047056]
def z164 : List Nat := [6,31,992,1082401,25977624,32776456]
def z165 : List Nat := [6,31,992,1082401,25977624,32776479]
def z166 : List Nat := [6,31,992,1082401,25977624,32777192]
def z167 : List Nat := [6,31,992,1082401,27060025,32776456]
def z168 : List Nat := [6,31,992,1082431,6494406,32776456]
def z169 : List Nat := [6,31,992,1083361,6494406,32776456]
def z170 : List Nat := [6,31,992,1113121,2164802,5214340,8659208,33047056]
def z171 : List Nat := [6,31,992,1113121,6494406,9412872,17318416,32505856]
def z172 : List Nat := [6,31,992,1113121,7313606,8659208,17318416,32505856]
def z173 : List Nat := [6,31,992,1113121,9436424,17318416]
def z174 : List Nat := [6,31,992,1113121,25977624,32776456]
def z175 : List Nat := [6,31,992,2096161,2164802,4329604,8659208,33047056]
def z176 : List Nat := [6,31,992,2096161,6494406,8659208,17318416,32505856]
def z177 : List Nat := [6,31,992,2096161,9436424,17318416]
def z178 : List Nat := [6,31,992,3247203,5412005,32776456]
def z179 : List Nat := [6,31,992,3247203,6494406,32776456]
def z180 : List Nat := [6,31,992,6494406,7576807,32776456]
def z181 : List Nat := [6,31,992,6494406,9436424,17318416]
def z182 : List Nat := [6,31,992,6494406,9437183,17318416]
def z183 : List Nat := [6,31,992,6494406,17318416,24117248]
def z184 : List Nat := [6,31,992,6494406,25707024,32505856]
def z185 : List Nat := [6,31,992,6494406,25977624,32776456]
def z186 : List Nat := [6,31,992,6494406,32472030,32776456]
def z187 : List Nat := [6,31,992,7542982,17318416,32505856]
def z188 : List Nat := [6,31,992,7576807,9741609,32505856]
def z189 : List Nat := [6,31,992,7576807,15153614,32505856]
def z190 : List Nat := [6,31,992,7576807,18400817,32505856]
def z191 : List Nat := [6,31,992,7576807,23812822,32505856]
def z192 : List Nat := [6,31,992,8659208,17318416,32505889]
def z193 : List Nat := [6,31,992,8659208,17318449,32505856]
def z194 : List Nat := [6,31,992,8659241,17318416,32505856]
def z195 : List Nat := [6,31,992,8693033,17318416,32505856]
def z196 : List Nat := [6,31,992,9436424,9741609,17318416]
def z197 : List Nat := [6,31,992,9436424,9764137,17318416]
def z198 : List Nat := [6,31,992,9436424,10485033,17318416]
def z199 : List Nat := [6,31,992,9436424,17318416,18400817]
def z200 : List Nat := [6,31,992,9436424,17318416,32472030]
def z201 : List Nat := [6,31,992,9436424,17318416,32539681]
def z202 : List Nat := [6,31,992,9437183,9741609,17318416]
def z203 : List Nat := [6,31,992,9741609,15153614,32505856]
def z204 : List Nat := [6,31,992,9741609,17318416,24117248]
def z205 : List Nat := [6,31,992,9741609,18366992,32505856]
def z206 : List Nat := [6,31,992,9741609,18400817,32505856]
def z207 : List Nat := [6,31,992,9741609,18400817,32505887]
def z208 : List Nat := [6,31,992,9741609,18400817,32506848]
def z209 : List Nat := [6,31,992,9741609,18400817,32776456]
def z210 : List Nat := [6,31,992,9741609,25707024,32505856]
def z211 : List Nat := [6,31,992,9741609,25977624,32505856]
def z212 : List Nat := [6,31,992,9741609,25977624,32505887]
def z213 : List Nat := [6,31,992,9741609,25977624,32506848]
def z214 : List Nat := [6,31,992,9741609,25977624,32776456]
def z215 : List Nat := [6,31,992,15153614,23812822,32505856]
def z216 : List Nat := [6,31,992,15153614,25977624,32505856]
def z217 : List Nat := [6,31,992,18400817,23812822,32505856]
def z218 : List Nat := [6,31,992,18400817,25977624,32505856]
def z219 : List Nat := [6,31,992,18400817,25977624,32505887]
def z220 : List Nat := [6,31,992,18400817,25977624,32506848]
def z221 : List Nat := [6,31,992,18400817,25977624,32776456]
def z222 : List Nat := [6,31,992,23812822,25977624,32505856]
def z223 : List Nat := [6,31,992,25977624,27060025,32776456]
def z224 : List Nat := [6,31,992,25977624,32472030,32776456]
def z225 : List Nat := [6,31,992,25977624,32505856,32810281]
def z226 : List Nat := [6,31,992,25977624,32505856,33080881]
def z227 : List Nat := [6,31,992,25977624,32539681,32776456]
def z228 : List Nat := [6,31,992,25977624,32539681,33047056]
def z229 : List Nat := [6,31,992,25977624,32776456,32810281]
def z230 : List Nat := [6,31,1023,1082401,6494406,32776456]
def z231 : List Nat := [6,31,1023,1082401,9436424,17318416]
def z232 : List Nat := [6,31,1023,1082401,25977624,32776456]
def z233 : List Nat := [6,31,1023,8659208,17318416,32505889]
def z234 : List Nat := [6,31,1023,8659208,17318449,32505856]
def z235 : List Nat := [6,31,1023,8659241,17318416,32505856]
def z236 : List Nat := [6,31,1023,9741609,18400817,32505856]
def z237 : List Nat := [6,31,1023,9741609,25977624,32505856]
def z238 : List Nat := [6,31,1023,18400817,25977624,32505856]
def z239 : List Nat := [6,31,31744,33825,9412872,17318416]
def z240 : List Nat := [6,31,31744,1015808,1082401,6494406,8659944,33047056]
def z241 : List Nat := [6,31,31744,1015808,1082401,6494406,17318896,32776456]
def z242 : List Nat := [6,31,31744,1015808,7542982,17318416]
def z243 : List Nat := [6,31,31744,1015808,8659208,17318449]
def z244 : List Nat := [6,31,31744,1015808,8659241,17318416]
def z245 : List Nat := [6,31,31744,1015808,8693033,17318416]
def z246 : List Nat := [6,31,31744,1015808,9741609,18366992]
def z247 : List Nat := [6,31,31744,1015841,8659208,17318416]
def z248 : List Nat := [6,31,31744,1016865,8659208,17318416]
def z249 : List Nat := [6,31,31744,1048576,10462505,17318416]
def z250 : List Nat := [6,31,31744,1082401,7313606,8659208,17318896,32505856]
def z251 : List Nat := [6,31,31744,1082401,9412872,17318448]
def z252 : List Nat := [6,31,31744,1082401,9412872,18366992]
def z253 : List Nat := [6,31,31744,1082401,9412904,17318416]
def z254 : List Nat := [6,31,31744,1083361,6494406,9412872,17318416,32505856]
def z255 : List Nat := [6,31,31744,2065441,2164802,4329604,8659944,33047056]
def z256 : List Nat := [6,31,31744,2065441,6494406,8659944,17318416,32505856]
def z257 : List Nat := [6,31,31744,2065441,6494406,33047056]
def z258 : List Nat := [6,31,31744,2065441,8659208,18366992]
def z259 : List Nat := [6,31,31744,2065441,25977624,32776456]
def z260 : List Nat := [6,31,31744,2065441,25977624,33047056]
def z261 : List Nat := [6,31,31744,8659208,17318416,32537566]
def z262 : List Nat := [6,31,31744,9412872,17318416,32708806]
def z263 : List Nat := [6,31,31744,9412872,17318416,33520606]
def z264 : List Nat := [6,31,31744,9412872,17318896,18400817]
def z265 : List Nat := [6,31,31744,9413608,10462505,17318416]
def z266 : List Nat := [6,31,31776,1082401,9412872,17318416]
def z267 : List Nat := [6,31,32736,1082401,9436424,17318416]
def z268 : List Nat := [6,31,32736,1113121,9412872,17318416]
def z269 : List Nat := [6,31,33825,1047552,8659208,17318416]
def z270 : List Nat := [6,31,33825,8659208,17318416,32506848]
def z271 : List Nat := [6,31,777975,1082401,8659944,17318416]
def z272 : List Nat := [6,31,1047552,1048576,6494406,17318416]
def z273 : List Nat := [6,31,1047552,1048576,9741609,17318416]
def z274 : List Nat := [6,31,1047552,1082401,2164802,4329604,8659944,33047056]
def z275 : List Nat := [6,31,1047552,1082401,2164802,4329604,17318896,32776456]
def z276 : List Nat := [6,31,1047552,1082401,6494406,8659208,17318896,32505856]
def z277 : List Nat := [6,31,1047552,1082401,6494406,8659944]
def z278 : List Nat := [6,31,1047552,1082401,6494406,8659944,17318416,32505856]
def z279 : List Nat := [6,31,1047552,1082401,6494406,17318896]
def z280 : List Nat := [6,31,1047552,1082401,6494406,32776456]
def z281 : List Nat := [6,31,1047552,1082401,6494406,33047056]
def z282 : List Nat := [6,31,1047552,1082401,8659208,17318448]
def z283 : List Nat := [6,31,1047552,1082401,8659208,18366992]
def z284 : List Nat := [6,31,1047552,1082401,8659240,17318416]
def z285 : List Nat := [6,31,1047552,1082401,8659944,25977624]
def z286 : List Nat := [6,31,1047552,1082401,9707784,17318416]
def z287 : List Nat := [6,31,1047552,1082401,17318896,25977624]
def z288 : List Nat := [6,31,1047552,1082401,25977624,32776456]
def z289 : List Nat := [6,31,1047552,1082401,25977624,33047056]
def z290 : List Nat := [6,31,1047552,1083361,6494406,8659208,17318416,32505856]
def z291 : List Nat := [6,31,1047552,2164802,5378180,17318416]
def z292 : List Nat := [6,31,1047552,6494406,8659208,17318896]
def z293 : List Nat := [6,31,1047552,6494406,8659944,17318416]
def z294 : List Nat := [6,31,1047552,8659208,17318416,32708806]
def z295 : List Nat := [6,31,1047552,8659208,17318416,33520606]
def z296 : List Nat := [6,31,1047552,8659208,17318896,18400817]
def z297 : List Nat := [6,31,1047552,8659944,9741609,17318416]
def z298 : List Nat := [6,31,1047552,9741609,18400817,32505856]
def z299 : List Nat := [6,31,1047552,9741609,25977624,32505856]
def z300 : List Nat := [6,31,1047552,18400817,25977624,32505856]
def z301 : List Nat := [6,31,1047584,1082401,8659208,17318416]
def z302 : List Nat := [6,31,1048544,1082401,9436424,17318416]
def z303 : List Nat := [6,31,1048544,2096161,8659208,17318416]
def z304 : List Nat := [6,31,1048575,1082401,6494406,8659944]
def z305 : List Nat := [6,31,1048575,1082401,8659944,25977624]
def z306 : List Nat := [6,31,1048575,1082401,9436424,17318416]
def z307 : List Nat := [6,31,1048575,1083361,6494406,8659208]
def z308 : List Nat := [6,31,1048575,1083361,6494406,17318416]
def z309 : List Nat := [6,31,1048575,1083361,8659208,18400817]
def z310 : List Nat := [6,31,1048575,1083361,9741609,17318416]
def z311 : List Nat := [6,31,1048575,1113121,9412872,17318416]
def z312 : List Nat := [6,31,1048575,2096161,8659208,17318416]
def z313 : List Nat := [6,31,1048575,6494406,8659944,17318416]
def z314 : List Nat := [6,31,1048575,8659944,9741609,17318416]
def z315 : List Nat := [6,31,1048576,1082401,9436424,17318416]
def z316 : List Nat := [6,31,1048576,1113121,9412872,17318416]
def z317 : List Nat := [6,31,1048576,2096161,8659208,17318416]
def z318 : List Nat := [6,31,1048576,6494406,17318416,32506848]
def z319 : List Nat := [6,31,1048576,9741609,17318416,32506848]
def z320 : List Nat := [6,31,1049568,6494406,17318416,32505856]
def z321 : List Nat := [6,31,1049568,9741609,17318416,32505856]
def z322 : List Nat := [6,31,1082401,1083361,6494406,32776456]
def z323 : List Nat := [6,31,1082401,1083361,25977624,32776456]
def z324 : List Nat := [6,31,1082401,2164802,5241988,8659208,17318896,32505856]
def z325 : List Nat := [6,31,1082401,2165730,9436424,17318416]
def z326 : List Nat := [6,31,1082401,2194498,5214340,8659208,17318896,32505856]
def z327 : List Nat := [6,31,1082401,6494406,8659944,32505856]
def z328 : List Nat := [6,31,1082401,6494406,8659944,32505887]
def z329 : List Nat := [6,31,1082401,6494406,8659944,32506848]
def z330 : List Nat := [6,31,1082401,6494406,8659944,32776456]
def z331 : List Nat := [6,31,1082401,6494406,8659944,32777192]
def z332 : List Nat := [6,31,1082401,6494406,8659967,32505856]
def z333 : List Nat := [6,31,1082401,6494406,9742313,32505856]
def z334 : List Nat := [6,31,1082401,6494406,17318896,32506848]
def z335 : List Nat := [6,31,1082401,6494406,24894487,32505856]
def z336 : List Nat := [6,31,1082401,6494406,32505856,32777192]
def z337 : List Nat := [6,31,1082401,6494406,32506848,32776456]
def z338 : List Nat := [6,31,1082401,6494406,32506848,33047056]
def z339 : List Nat := [6,31,1082401,6494406,32776456,32777192]
def z340 : List Nat := [6,31,1082401,6494406,32776456,33553439]
def z341 : List Nat := [6,31,1082401,7576807,8659944,32505856]
def z342 : List Nat := [6,31,1082401,8659208,16778208,33047056]
def z343 : List Nat := [6,31,1082401,8659208,17318416,32506816]
def z344 : List Nat := [6,31,1082401,8659208,17318448,32506848]
def z345 : List Nat := [6,31,1082401,8659208,17318896,32506368]
def z346 : List Nat := [6,31,1082401,8659208,18366992,32506848]
def z347 : List Nat := [6,31,1082401,8659240,17318416,32506848]
def z348 : List Nat := [6,31,1082401,8659720,17318896,32505856]
def z349 : List Nat := [6,31,1082401,8659944,9436424,17318416]
def z350 : List Nat := [6,31,1082401,8659944,16236015,32776456]
def z351 : List Nat := [6,31,1082401,8659944,17318416,32776456]
def z352 : List Nat := [6,31,1082401,8659944,17318416,32776479]
def z353 : List Nat := [6,31,1082401,8659944,18400817,32776456]
def z354 : List Nat := [6,31,1082401,8659944,25977624,32505856]
def z355 : List Nat := [6,31,1082401,8659944,25977624,32505887]
def z356 : List Nat := [6,31,1082401,8659944,25977624,32506848]
def z357 : List Nat := [6,31,1082401,8659944,25977624,32776456]
def z358 : List Nat := [6,31,1082401,8659944,25977624,32777192]
def z359 : List Nat := [6,31,1082401,8659944,27060025,32505856]
def z360 : List Nat := [6,31,1082401,8659967,17318416,32776456]
def z361 : List Nat := [6,31,1082401,8659967,25977624,32505856]
def z362 : List Nat := [6,31,1082401,8683496,9436424,17318416]
def z363 : List Nat := [6,31,1082401,8683496,17318416,32800008]
def z364 : List Nat := [6,31,1082401,9436424,9437160,17318416]
def z365 : List Nat := [6,31,1082401,9436424,16236015,32505856]
def z366 : List Nat := [6,31,1082401,9436424,17318416,17318896]
def z367 : List Nat := [6,31,1082401,9436424,17318416,32505856]
def z368 : List Nat := [6,31,1082401,9436424,17318416,32505887]
def z369 : List Nat := [6,31,1082401,9436424,17318416,32537600]
def z370 : List Nat := [6,31,1082401,9436424,17318416,32573506]
def z371 : List Nat := [6,31,1082401,9436424,17318416,32776456]
def z372 : List Nat := [6,31,1082401,9436424,17318416,32800008]
def z373 : List Nat := [6,31,1082401,9436424,17318416,33047056]
def z374 : List Nat := [6,31,1082401,9436424,17318416,33553408]
def z375 : List Nat := [6,31,1082401,9436424,17318416,33553439]
def z376 : List Nat := [6,31,1082401,9436424,17318416,33553672]
def z377 : List Nat := [6,31,1082401,9436424,18400817,32505856]
def z378 : List Nat := [6,31,1082401,9707784,17318416,32506848]
def z379 : List Nat := [6,31,1082401,9742313,17318416,32776456]
def z380 : List Nat := [6,31,1082401,9742313,25977624,32505856]
def z381 : List Nat := [6,31,1082401,9742313,27060025,32505856]
def z382 : List Nat := [6,31,1082401,10485033,17318416,32505856]
def z383 : List Nat := [6,31,1082401,17318416,24118007,32505856]
def z384 : List Nat := [6,31,1082401,17318416,24894487,32776456]
def z385 : List Nat := [6,31,1082401,17318896,25977624,32506848]
def z386 : List Nat := [6,31,1082401,24894487,25977624,32505856]
def z387 : List Nat := [6,31,1082401,25977624,32505856,32777192]
def z388 : List Nat := [6,31,1082401,25977624,32506848,32776456]
def z389 : List Nat := [6,31,1082401,25977624,32506848,33047056]
def z390 : List Nat := [6,31,1082401,25977624,32776456,32777192]
def z391 : List Nat := [6,31,1082401,25977624,32776456,33553439]
def z392 : List Nat := [6,31,1082431,6494406,8659944,32505856]
def z393 : List Nat := [6,31,1082913,8659208,17318896,32505856]
def z394 : List Nat := [6,31,1083361,2164802,4329604,9436424,17318416,32505856]
def z395 : List Nat := [6,31,1083361,6494406,8659208,32505856]
def z396 : List Nat := [6,31,1083361,6494406,8659208,32505887]
def z397 : List Nat := [6,31,1083361,6494406,8659208,32776456]
def z398 : List Nat := [6,31,1083361,6494406,8659231,32505856]
def z399 : List Nat := [6,31,1083361,6494406,8659944,32505856]
def z400 : List Nat := [6,31,1083361,6494406,9741609,32505856]
def z401 : List Nat := [6,31,1083361,6494406,9742313,32505856]
def z402 : List Nat := [6,31,1083361,6494406,10824010,32505856]
def z403 : List Nat := [6,31,1083361,6494406,15153614,32505856]
def z404 : List Nat := [6,31,1083361,6494406,16236015,32505856]
def z405 : List Nat := [6,31,1083361,6494406,17318416,32505856]
def z406 : List Nat := [6,31,1083361,6494406,17318416,32505887]
def z407 : List Nat := [6,31,1083361,6494406,17318431,32505856]
def z408 : List Nat := [6,31,1083361,6494406,17318896,32505856]
def z409 : List Nat := [6,31,1083361,6494406,18400817,32505856]
def z410 : List Nat := [6,31,1083361,6494406,18401265,32505856]
def z411 : List Nat := [6,31,1083361,6494406,19483218,32505856]
def z412 : List Nat := [6,31,1083361,6494406,23812822,32505856]
def z413 : List Nat := [6,31,1083361,6494406,24895223,32505856]
def z414 : List Nat := [6,31,1083361,6494406,32505856,32776456]
def z415 : List Nat := [6,31,1083361,6494406,32505856,33047056]
def z416 : List Nat := [6,31,1083361,8659208,15153614,32505856]
def z417 : List Nat := [6,31,1083361,8659208,18400817,32505856]
def z418 : List Nat := [6,31,1083361,8659208,18400817,32505887]
def z419 : List Nat := [6,31,1083361,8659208,18400817,32776456]
def z420 : List Nat := [6,31,1083361,8659208,27060025,32505856]
def z421 : List Nat := [6,31,1083361,8682760,18400817,32505856]
def z422 : List Nat := [6,31,1083361,9741609,16236015,32505856]
def z423 : List Nat := [6,31,1083361,9741609,17318416,32505856]
def z424 : List Nat := [6,31,1083361,9741609,17318416,32505887]
def z425 : List Nat := [6,31,1083361,9741609,18400817,32505856]
def z426 : List Nat := [6,31,1083361,9741609,25977624,32505856]
def z427 : List Nat := [6,31,1083361,9741609,27060025,32505856]
def z428 : List Nat := [6,31,1083361,9764137,17318416,32505856]
def z429 : List Nat := [6,31,1083361,10824010,12988812,32505856]
def z430 : List Nat := [6,31,1083361,17318416,23812822,32505856]
def z431 : List Nat := [6,31,1083361,17318416,27060025,32505856]
def z432 : List Nat := [6,31,1083361,18400817,24895223,32505856]
def z433 : List Nat := [6,31,1083361,18400817,25977624,32505856]
def z434 : List Nat := [6,31,1083361,18400817,27060025,32505856]
def z435 : List Nat := [6,31,1083361,19483218,21648020,32505856]
def z436 : List Nat := [6,31,1083391,6494406,8659208,32505856]
def z437 : List Nat := [6,31,1083391,6494406,17318416,32505856]
def z438 : List Nat := [6,31,1083391,8659208,18400817,32505856]
def z439 : List Nat := [6,31,1083391,9741609,17318416,32505856]
def z440 : List Nat := [6,31,1113121,8659944,17318416,32776456]
def z441 : List Nat := [6,31,1113121,8659944,25977624,32505856]
def z442 : List Nat := [6,31,1113121,9412872,16236015,32505856]
def z443 : List Nat := [6,31,1113121,9412872,17318416,32505856]
def z444 : List Nat := [6,31,1113121,9412872,17318416,32505887]
def z445 : List Nat := [6,31,1113121,9412872,17318416,32776456]
def z446 : List Nat := [6,31,1113121,9412872,17318416,33047056]
def z447 : List Nat := [6,31,1113121,9412872,17318416,33521664]
def z448 : List Nat := [6,31,1113121,9412872,17318416,33530120]
def z449 : List Nat := [6,31,1113121,9436424,17318416,32505856]
def z450 : List Nat := [6,31,1113121,10462505,17318416,32505856]
def z451 : List Nat := [6,31,1113121,10485033,17318416,32505856]
def z452 : List Nat := [6,31,1113121,17318416,24141559,32505856]
def z453 : List Nat := [6,31,1114081,9764137,17318416,32505856]
def z454 : List Nat := [6,31,2096161,2164802,4329604,8659944,17318416,32505856]
def z455 : List Nat := [6,31,2096161,2164802,4329604,33047056]
def z456 : List Nat := [6,31,2096161,6494406,17318416,32505856]
def z457 : List Nat := [6,31,2096161,8659208,16236015,32505856]
def z458 : List Nat := [6,31,2096161,8659208,17318416,32505856]
def z459 : List Nat := [6,31,2096161,8659208,17318416,32505887]
def z460 : List Nat := [6,31,2096161,8659208,17318416,32776456]
def z461 : List Nat := [6,31,2096161,8659208,17318416,33047056]
def z462 : List Nat := [6,31,2096161,8659208,25977624,32505856]
def z463 : List Nat := [6,31,2096161,8682760,17318416,32505856]
def z464 : List Nat := [6,31,2096161,9436424,17318416,32505856]
def z465 : List Nat := [6,31,2096161,9741609,17318416,32505856]
def z466 : List Nat := [6,31,2096161,9764137,17318416,32505856]
def z467 : List Nat := [6,31,2096161,10485033,17318416,32505856]
def z468 : List Nat := [6,31,2096161,17318416,24895223,32505856]
def z469 : List Nat := [6,31,2096161,17318416,25977624,32505856]
def z470 : List Nat := [6,31,2164802,4329604,25977848,32777192]
def z471 : List Nat := [6,31,2164802,5378180,17318416,32506848]
def z472 : List Nat := [6,31,2164802,9436424,17318416,32641156]
def z473 : List Nat := [6,31,3247203,5412005,8659944,32505856]
def z474 : List Nat := [6,31,3247203,6494406,8659944,32505856]
def z475 : List Nat := [6,31,6494406,7576807,8659944,32505856]
def z476 : List Nat := [6,31,6494406,8389600,17318416,32505856]
def z477 : List Nat := [6,31,6494406,8659208,9742313,32505856]
def z478 : List Nat := [6,31,6494406,8659208,17318896,32506848]
def z479 : List Nat := [6,31,6494406,8659208,32471070,32505856]
def z480 : List Nat := [6,31,6494406,8659944,9741609,32505856]
def z481 : List Nat := [6,31,6494406,8659944,9742313,32505856]
def z482 : List Nat := [6,31,6494406,8659944,16236015,32505856]
def z483 : List Nat := [6,31,6494406,8659944,17318416,32505856]
def z484 : List Nat := [6,31,6494406,8659944,17318416,32505887]
def z485 : List Nat := [6,31,6494406,8659944,17318416,32506848]
def z486 : List Nat := [6,31,6494406,8659944,17318416,32776456]
def z487 : List Nat := [6,31,6494406,8659944,17318416,32777192]
def z488 : List Nat := [6,31,6494406,8659944,17318431,32505856]
def z489 : List Nat := [6,31,6494406,8659944,17318896,32505856]
def z490 : List Nat := [6,31,6494406,8659944,19483218,32505856]
def z491 : List Nat := [6,31,6494406,8659944,23812822,32505856]
def z492 : List Nat := [6,31,6494406,8659944,25977624,32505856]
def z493 : List Nat := [6,31,6494406,8659944,25977848,32505856]
def z494 : List Nat := [6,31,6494406,8659944,32472030,32505856]
def z495 : List Nat := [6,31,6494406,8659967,17318416,32505856]
def z496 : List Nat := [6,31,6494406,9436424,17318416,32505856]
def z497 : List Nat := [6,31,6494406,17318416,24894487,32505856]
def z498 : List Nat := [6,31,6494406,17318416,32471070,32505856]
def z499 : List Nat := [6,31,8389600,9741609,17318416,32505856]
def z500 : List Nat := [6,31,8659208,9742313,18400817,32505856]
def z501 : List Nat := [6,31,8659208,9742313,27060025,32505856]
def z502 : List Nat := [6,31,8659208,10485033,17318416,32505856]
def z503 : List Nat := [6,31,8659208,17318416,31458270,32505856]
def z504 : List Nat := [6,31,8659208,17318416,32472030,32506816]
def z505 : List Nat := [6,31,8659208,17318416,32505856,33553441]
def z506 : List Nat := [6,31,8659208,17318416,32506848,32708806]
def z507 : List Nat := [6,31,8659208,17318416,32506848,33520606]
def z508 : List Nat := [6,31,8659208,17318896,18400817,32506848]
def z509 : List Nat := [6,31,8659208,18400817,32471070,32505856]
def z510 : List Nat := [6,31,8659944,9741609,16236015,32505856]
def z511 : List Nat := [6,31,8659944,9741609,17318416,32505856]
def z512 : List Nat := [6,31,8659944,9741609,17318416,32505887]
def z513 : List Nat := [6,31,8659944,9741609,17318416,32506848]
def z514 : List Nat := [6,31,8659944,9741609,17318416,32776456]
def z515 : List Nat := [6,31,8659944,9741609,17318416,32777192]
def z516 : List Nat := [6,31,8659944,9741609,18400817,32505856]
def z517 : List Nat := [6,31,8659944,9741609,25977624,32505856]
def z518 : List Nat := [6,31,8659944,9741609,27060025,32505856]
def z519 : List Nat := [6,31,8659944,9764137,17318416,32505856]
def z520 : List Nat := [6,31,8659944,17318416,18400817,32776456]
def z521 : List Nat := [6,31,8659944,17318416,23812822,32505856]
def z522 : List Nat := [6,31,8659944,17318416,27060025,32505856]
def z523 : List Nat := [6,31,8659944,17318416,32472030,32776456]
def z524 : List Nat := [6,31,8659944,17318416,32505856,32708806]
def z525 : List Nat := [6,31,8659944,17318416,32505856,32810281]
def z526 : List Nat := [6,31,8659944,17318416,32539681,32776456]
def z527 : List Nat := [6,31,8659944,17318416,32573506,32641156]
def z528 : List Nat := [6,31,8659944,17318416,32776456,32810281]
def z529 : List Nat := [6,31,8659944,18400817,25977624,32505856]
def z530 : List Nat := [6,31,8659944,19483218,21648020,32505856]
def z531 : List Nat := [6,31,8659944,25977624,27060025,32505856]
def z532 : List Nat := [6,31,8659944,25977624,32472030,32505856]
def z533 : List Nat := [6,31,8659944,25977624,32505856,32539681]
def z534 : List Nat := [6,31,8659967,9741609,17318416,32505856]
def z535 : List Nat := [6,31,8682760,10462505,17318416,32505856]
def z536 : List Nat := [6,31,8682760,10485033,17318416,32505856]
def z537 : List Nat := [6,31,8682760,17318416,31488990,32505856]
def z538 : List Nat := [6,31,8682760,17318416,32505856,33522721]
def z539 : List Nat := [6,31,8683496,9764137,17318416,32505856]
def z540 : List Nat := [6,31,9436424,9741609,17318416,32505856]
def z541 : List Nat := [6,31,9436424,9764137,17318416,32505856]
def z542 : List Nat := [6,31,9436424,10485033,17318416,32505856]
def z543 : List Nat := [6,31,9436424,17318416,18400817,32505856]
def z544 : List Nat := [6,31,9436424,17318416,32472030,32505856]
def z545 : List Nat := [6,31,9436424,17318416,32505856,32539681]
def z546 : List Nat := [6,31,9741609,9742313,18400817,32505856]
def z547 : List Nat := [6,31,9741609,9742313,25977624,32505856]
def z548 : List Nat := [6,31,9741609,17318416,24894487,32505856]
def z549 : List Nat := [6,31,9741609,17318416,32471070,32505856]
def z550 : List Nat := [6,31,9741609,18400817,32505856,32506848]
def z551 : List Nat := [6,31,9741609,18400817,32505856,33553439]
def z552 : List Nat := [6,31,9741609,25977624,32505856,32506848]
def z553 : List Nat := [6,31,9741609,25977624,32505856,33553439]
def z554 : List Nat := [6,31,18400817,25977624,32505856,32506848]
def z555 : List Nat := [6,31,18400817,25977624,32505856,33553439]
def z556 : List Nat := [6,33,1023,8659208,17318416,32505887]
def z557 : List Nat := [6,33,1023,8659208,17318416,32506848]
def z558 : List Nat := [6,63,1082401,8659208,17318416,32506848]
def z559 : List Nat := [6,297,992,8659208,17318416,32505856]
def z560 : List Nat := [6,992,1023,1082401,6494406,32776456]
def z561 : List Nat := [6,992,1023,1082401,9436424,17318416]
def z562 : List Nat := [6,992,1023,1082401,25977624,32776456]
def z563 : List Nat := [6,992,1023,8659208,17318416,32505889]
def z564 : List Nat := [6,992,1023,8659208,17318449,32505856]
def z565 : List Nat := [6,992,1023,8659241,17318416,32505856]
def z566 : List Nat := [6,992,1023,9741609,18400817,32505856]
def z567 : List Nat := [6,992,1023,9741609,25977624,32505856]
def z568 : List Nat := [6,992,1023,18400817,25977624,32505856]
def z569 : List Nat := [6,992,31744,1015808,1082401,6494431,8659208,33047056]
def z570 : List Nat := [6,992,31744,1015808,1082401,6494431,17318416,32776456]
def z571 : List Nat := [6,992,31744,1082401,2164831,5214340,8659208,33047056]
def z572 : List Nat := [6,992,31744,1082431,9412872,18400817]
def z573 : List Nat := [6,992,31744,9412872,17318416,33522721]
def z574 : List Nat := [6,992,1014750,1047552,8659208,17318416]
def z575 : List Nat := [6,992,1014750,8659208,17318416,32505887]
def z576 : List Nat := [6,992,1047552,1082401,2164802,4329631,8659208,33047056]
def z577 : List Nat := [6,992,1047552,1082401,2164802,4329631,17318416,32776456]
def z578 : List Nat := [6,992,1047552,1082401,6494431,8659208,17318416,32505856]
def z579 : List Nat := [6,992,1047552,1082431,6494406,8659208]
def z580 : List Nat := [6,992,1047552,1082431,6494406,17318416]
def z581 : List Nat := [6,992,1047552,1082431,8659208,18400817]
def z582 : List Nat := [6,992,1047552,1082431,9741609,17318416]
def z583 : List Nat := [6,992,1047552,8659208,16236015,32539681]
def z584 : List Nat := [6,992,1047552,8659208,17318416,32539681]
def z585 : List Nat := [6,992,1047552,8659208,17318416,32570401]
def z586 : List Nat := [6,992,1047552,8659208,17318416,33553441]
def z587 : List Nat := [6,992,1047552,8659208,25977624,32539681]
def z588 : List Nat := [6,992,1047552,8682760,17318416,32539681]
def z589 : List Nat := [6,992,1047552,9436424,17318416,32539681]
def z590 : List Nat := [6,992,1047552,9741609,18400817,32505856]
def z591 : List Nat := [6,992,1047552,9741609,25977624,32505856]
def z592 : List Nat := [6,992,1047552,17318416,24895223,32539681]
def z593 : List Nat := [6,992,1047552,17318416,25977624,32539681]
def z594 : List Nat := [6,992,1047552,18400817,25977624,32505856]
def z595 : List Nat := [6,992,1048544,8659208,17318416,32539681]
def z596 : List Nat := [6,992,1048575,1082401,6494406,17318431]
def z597 : List Nat := [6,992,1048575,1082401,17318431,25977624]
def z598 : List Nat := [6,992,1048575,6494406,8659208,17318431]
def z599 : List Nat := [6,992,1048575,8659208,17318431,18400817]
def z600 : List Nat := [6,992,1048576,6494406,17318431,32505856]
def z601 : List Nat := [6,992,1048607,6494406,17318416,32505856]
def z602 : List Nat := [6,992,1048607,9741609,17318416,32505856]
def z603 : List Nat := [6,992,1082401,1082431,9436424,17318416]
def z604 : List Nat := [6,992,1082401,2164831,5241988,8659208,17318416,32505856]
def z605 : List Nat := [6,992,1082401,2164831,6494406,32776456]
def z606 : List Nat := [6,992,1082401,2164831,25977624,32776456]
def z607 : List Nat := [6,992,1082401,6494406,6494431,32776456]
def z608 : List Nat := [6,992,1082401,6494406,16236000,32505856]
def z609 : List Nat := [6,992,1082401,6494406,17318431,32505856]
def z610 : List Nat := [6,992,1082401,6494406,17318431,32506848]
def z611 : List Nat := [6,992,1082401,6494406,17318911,32505856]
def z612 : List Nat := [6,992,1082401,6494406,19483231,32505856]
def z613 : List Nat := [6,992,1082401,6494406,23812831,32505856]
def z614 : List Nat := [6,992,1082401,6494406,32505856,33047071]
def z615 : List Nat := [6,992,1082401,6494406,32776456,33554400]
def z616 : List Nat := [6,992,1082401,6494431,17318416,32776456]
def z617 : List Nat := [6,992,1082401,7339206,17318416,32505856]
def z618 : List Nat := [6,992,1082401,7576807,17318431,32505856]
def z619 : List Nat := [6,992,1082401,8659208,17318425,32505856]
def z620 : List Nat := [6,992,1082401,8659231,17318424,32505856]
def z621 : List Nat := [6,992,1082401,9436424,17318416,33553408]
def z622 : List Nat := [6,992,1082401,9436424,17318416,33554400]
def z623 : List Nat := [6,992,1082401,9741609,17318425,32505856]
def z624 : List Nat := [6,992,1082401,16236000,25977624,32505856]
def z625 : List Nat := [6,992,1082401,17318431,25977624,32505856]
def z626 : List Nat := [6,992,1082401,17318431,25977624,32506848]
def z627 : List Nat := [6,992,1082401,17318431,25984792,32505856]
def z628 : List Nat := [6,992,1082401,17318431,27060025,32505856]
def z629 : List Nat := [6,992,1082401,17318911,25977624,32505856]
def z630 : List Nat := [6,992,1082401,19483231,25977624,32505856]
def z631 : List Nat := [6,992,1082401,25977624,32505856,33047071]
def z632 : List Nat := [6,992,1082401,25977624,32776456,33554400]
def z633 : List Nat := [6,992,1082409,8659231,17318416,32505856]
def z634 : List Nat := [6,992,1082431,2164802,4329604,32776479]
def z635 : List Nat := [6,992,1082431,6494406,8659208,32505887]
def z636 : List Nat := [6,992,1082431,6494406,8659231,32505856]
def z637 : List Nat := [6,992,1082431,6494406,17318416,32505887]
def z638 : List Nat := [6,992,1082431,6494406,17318431,32505856]
def z639 : List Nat := [6,992,1082431,8659208,17318416,32505857]
def z640 : List Nat := [6,992,1082431,8659208,17318417,32505856]
def z641 : List Nat := [6,992,1082431,8659208,18400817,32505887]
def z642 : List Nat := [6,992,1082431,8659209,17318416,32505856]
def z643 : List Nat := [6,992,1082431,9741609,17318416,32505887]
def z644 : List Nat := [6,992,1083361,6494406,17318431,32505856]
def z645 : List Nat := [6,992,1113121,6494406,17318431,32505856]
def z646 : List Nat := [6,992,1113121,17318431,25977624,32505856]
def z647 : List Nat := [6,992,2096161,9436424,17318416,32505856]
def z648 : List Nat := [6,992,2164802,4329604,9437183,17318431]
def z649 : List Nat := [6,992,2164802,4329604,17318431,24117248]
def z650 : List Nat := [6,992,2164802,4329604,25707039,32505856]
def z651 : List Nat := [6,992,2164802,5378180,17318431,32505856]
def z652 : List Nat := [6,992,2164831,9741609,18400817,32505856]
def z653 : List Nat := [6,992,2164831,9741609,25977624,32505856]
def z654 : List Nat := [6,992,2164831,18400817,25977624,32505856]
def z655 : List Nat := [6,992,3247203,5412005,17318431,32505856]
def z656 : List Nat := [6,992,3247203,6494406,17318431,32505856]
def z657 : List Nat := [6,992,6494406,7576807,17318431,32505856]
def z658 : List Nat := [6,992,6494406,8388608,17318431,32505856]
def z659 : List Nat := [6,992,6494406,8388639,17318416,32505856]
def z660 : List Nat := [6,992,6494406,8659208,16236000,32505856]
def z661 : List Nat := [6,992,6494406,8659208,17318431,32505856]
def z662 : List Nat := [6,992,6494406,8659208,17318431,32506848]
def z663 : List Nat := [6,992,6494406,8659208,17318431,32776456]
def z664 : List Nat := [6,992,6494406,8659208,17318911,32505856]
def z665 : List Nat := [6,992,6494406,8659208,19483231,32505856]
def z666 : List Nat := [6,992,6494406,8659208,23812831,32505856]
def z667 : List Nat := [6,992,6494406,8659231,17318431,32505856]
def z668 : List Nat := [6,992,6494406,8659944,17318431,32505856]
def z669 : List Nat := [6,992,6494406,8682760,17318431,32505856]
def z670 : List Nat := [6,992,6494406,10824010,17318431,32505856]
def z671 : List Nat := [6,992,6494406,15153614,17318431,32505856]
def z672 : List Nat := [6,992,6494406,17318431,18400817,32505856]
def z673 : List Nat := [6,992,6494406,17318431,18400831,32505856]
def z674 : List Nat := [6,992,6494406,17318431,24895223,32505856]
def z675 : List Nat := [6,992,6494406,17318431,25977624,32505856]
def z676 : List Nat := [6,992,6494406,17318431,25977631,32505856]
def z677 : List Nat := [6,992,6494406,17318431,32472030,32505856]
def z678 : List Nat := [6,992,7339206,8659208,17318416,32505856]
def z679 : List Nat := [6,992,8388639,9741609,17318416,32505856]
def z680 : List Nat := [6,992,8659208,9741609,17318425,32505856]
def z681 : List Nat := [6,992,8659208,15153614,17318431,32505856]
def z682 : List Nat := [6,992,8659208,16236000,18400817,32505856]
def z683 : List Nat := [6,992,8659208,16236015,32505887,32539681]
def z684 : List Nat := [6,992,8659208,17318416,17825296,32539681]
def z685 : List Nat := [6,992,8659208,17318416,32505887,32539681]
def z686 : List Nat := [6,992,8659208,17318416,32505887,32570401]
def z687 : List Nat := [6,992,8659208,17318416,32506879,32539681]
def z688 : List Nat := [6,992,8659208,17318416,32539681,32573535]
def z689 : List Nat := [6,992,8659208,17318416,32539681,33047071]
def z690 : List Nat := [6,992,8659208,17318431,18400817,32505856]
def z691 : List Nat := [6,992,8659208,17318431,18400817,32506848]
def z692 : List Nat := [6,992,8659208,17318431,18400817,32776456]
def z693 : List Nat := [6,992,8659208,17318431,18415153,32505856]
def z694 : List Nat := [6,992,8659208,17318431,27060025,32505856]
def z695 : List Nat := [6,992,8659208,17318431,32505856,32708806]
def z696 : List Nat := [6,992,8659208,17318431,32505856,33080881]
def z697 : List Nat := [6,992,8659208,17318431,32539681,33047056]
def z698 : List Nat := [6,992,8659208,17318431,32573506,32641156]
def z699 : List Nat := [6,992,8659208,17318911,18400817,32505856]
def z700 : List Nat := [6,992,8659208,17333776,17809936,32539681]
def z701 : List Nat := [6,992,8659208,18400817,19483231,32505856]
def z702 : List Nat := [6,992,8659208,25977624,32505887,32539681]
def z703 : List Nat := [6,992,8682760,17318416,32505887,32539681]
def z704 : List Nat := [6,992,8682760,17318431,18400817,32505856]
def z705 : List Nat := [6,992,9741609,17318431,18400817,32505856]
def z706 : List Nat := [6,992,9741609,17318431,25977624,32505856]
def z707 : List Nat := [6,992,9741609,18400817,32505856,32505887]
def z708 : List Nat := [6,992,9741609,18400817,32505856,33554400]
def z709 : List Nat := [6,992,9741609,25977624,32505856,32505887]
def z710 : List Nat := [6,992,9741609,25977624,32505856,33554400]
def z711 : List Nat := [6,992,10824010,12988812,17318431,32505856]
def z712 : List Nat := [6,992,17318416,24895223,32505887,32539681]
def z713 : List Nat := [6,992,17318416,25977624,32505887,32539681]
def z714 : List Nat := [6,992,17318431,18400817,24895223,32505856]
def z715 : List Nat := [6,992,17318431,18400817,25977624,32505856]
def z716 : List Nat := [6,992,17318431,18400817,27060025,32505856]
def z717 : List Nat := [6,992,17318431,25977624,27060025,32505856]
def z718 : List Nat := [6,992,17318431,25977624,32472030,32505856]
def z719 : List Nat := [6,992,17318431,25977624,32505856,32539681]
def z720 : List Nat := [6,992,18400817,25977624,32505856,32505887]
def z721 : List Nat := [6,992,18400817,25977624,32505856,33554400]
def z722 : List Nat := [6,1023,31775,1082401,9412872,17318416]
def z723 : List Nat := [6,1023,32736,1082401,9412872,17318416]
def z724 : List Nat := [6,1023,1047583,1082401,8659208,17318416]
def z725 : List Nat := [6,1023,1048544,1082401,8659208,17318416]
def z726 : List Nat := [6,1023,1082401,6494406,8659208,32505887]
def z727 : List Nat := [6,1023,1082401,6494406,8659208,32506848]
def z728 : List Nat := [6,1023,1082401,6494406,17318416,32505887]
def z729 : List Nat := [6,1023,1082401,6494406,17318416,32506848]
def z730 : List Nat := [6,1023,1082401,8659208,16236015,32505887]
def z731 : List Nat := [6,1023,1082401,8659208,16236015,32506848]
def z732 : List Nat := [6,1023,1082401,8659208,17318416,32505887]
def z733 : List Nat := [6,1023,1082401,8659208,17318416,32506848]
def z734 : List Nat := [6,1023,1082401,8659208,18400817,32505887]
def z735 : List Nat := [6,1023,1082401,8659208,18400817,32506848]
def z736 : List Nat := [6,1023,1082401,8659208,25977624,32505887]
def z737 : List Nat := [6,1023,1082401,8659208,25977624,32506848]
def z738 : List Nat := [6,1023,1082401,8682760,17318416,32505887]
def z739 : List Nat := [6,1023,1082401,8682760,17318416,32506848]
def z740 : List Nat := [6,1023,1082401,9741609,17318416,32505887]
def z741 : List Nat := [6,1023,1082401,9741609,17318416,32506848]
def z742 : List Nat := [6,1023,1082401,17318416,24895223,32505887]
def z743 : List Nat := [6,1023,1082401,17318416,24895223,32506848]
def z744 : List Nat := [6,1023,1082401,17318416,25977624,32505887]
def z745 : List Nat := [6,1023,1082401,17318416,25977624,32506848]
def z746 : List Nat := [6,1023,1113121,8659208,17318416,32505887]
def z747 : List Nat := [6,1023,1113121,8659208,17318416,32506848]
def z748 : List Nat := [6,1023,6494406,8659208,17318416,32505887]
def z749 : List Nat := [6,1023,6494406,8659208,17318416,32506848]
def z750 : List Nat := [6,1023,8659208,9741609,17318416,32505887]
def z751 : List Nat := [6,1023,8659208,9741609,17318416,32506848]
def z752 : List Nat := [6,1023,8659208,17318416,18400817,32505887]
def z753 : List Nat := [6,1023,8659208,17318416,18400817,32506848]
def z754 : List Nat := [6,1023,8659208,17318416,32472030,32505887]
def z755 : List Nat := [6,1023,8659208,17318416,32472030,32506848]
def z756 : List Nat := [6,1023,8659208,17318416,32505887,32539681]
def z757 : List Nat := [6,1023,8659208,17318416,32506848,32539681]
def z758 : List Nat := [6,31744,1015808,1048607,6494406,17318416]
def z759 : List Nat := [6,31744,1015808,1048607,9741609,17318416]
def z760 : List Nat := [6,31744,1015808,1082401,2164802,4329631,8659944,33047056]
def z761 : List Nat := [6,31744,1015808,1082401,2164802,4329631,17318896,32776456]
def z762 : List Nat := [6,31744,1015808,1082401,6494431,8659208,17318896,32505856]
def z763 : List Nat := [6,31744,1015808,1082401,6494431,8659944,17318416,32505856]
def z764 : List Nat := [6,31744,1015808,1083361,6494431,8659208,17318416,32505856]
def z765 : List Nat := [6,31744,1016800,8659208,17318416,33522721]
def z766 : List Nat := [6,31744,1016800,9412872,17318416,32539681]
def z767 : List Nat := [6,31744,1048607,1082401,9412872,17318416]
def z768 : List Nat := [6,31744,1048607,2065441,8659208,17318416]
def z769 : List Nat := [6,31744,1082401,2164831,5214340,8659208,17318896,32505856]
def z770 : List Nat := [6,31744,8659208,17318416,32505887,33522721]
def z771 : List Nat := [6,31744,9412872,17318416,32505887,32539681]
def z772 : List Nat := [6,31775,32736,1082401,9412872,17318416]
def z773 : List Nat := [6,31775,1082401,9412872,17318416,32505887]
def z774 : List Nat := [6,31775,1082401,9412872,17318416,32537600]
def z775 : List Nat := [6,31775,2065441,8659208,17318416,32505887]
def z776 : List Nat := [6,31775,2065441,8659208,17318416,32537600]
def z777 : List Nat := [6,32736,1016800,8659208,17318416,32539681]
def z778 : List Nat := [6,32736,1047552,8659208,17318416,32539681]
def z779 : List Nat := [6,1047552,1048544,8659208,17318416,32539681]
def z780 : List Nat := [6,1047552,1048607,1082401,8659208,17318416]
def z781 : List Nat := [6,1047552,1048607,2164802,4329604,17318416]
def z782 : List Nat := [6,1047552,1082401,2164802,4329631,8659208,17318896,32505856]
def z783 : List Nat := [6,1047552,1082401,2164802,4329631,8659944,17318416,32505856]
def z784 : List Nat := [6,1047552,1083361,2164802,4329631,8659208,17318416,32505856]
def z785 : List Nat := [6,1047552,8659208,17318416,32505887,32539681]
def z786 : List Nat := [6,1047552,8659208,17318416,32539681,33553439]
def z787 : List Nat := [6,1047583,1048544,1082401,8659208,17318416]
def z788 : List Nat := [6,1047583,1082401,8659208,17318416,32505887]
def z789 : List Nat := [6,1047583,1082401,8659208,17318416,33553408]
def z790 : List Nat := [6,1048544,1082401,8659208,17318416,32506848]
def z791 : List Nat := [6,1048544,1082401,8659208,17318416,33553408]
def z792 : List Nat := [6,1048544,1082401,9436424,17318416,32505856]
def z793 : List Nat := [6,1048544,2096161,8659208,17318416,32505856]
def z794 : List Nat := [6,1048576,2164802,4329604,17318431,32506848]
def z795 : List Nat := [6,1048607,1082401,8659208,17318416,32506848]
def z796 : List Nat := [6,1048607,2164802,4329604,17318416,32506848]
def z797 : List Nat := [6,1049568,2164802,4329604,17318431,32505856]
def z798 : List Nat := [6,1082401,1083361,6494406,17318431,32505856]
def z799 : List Nat := [6,1082401,1083361,17318431,25977624,32505856]
def z800 : List Nat := [6,1082401,1083391,8659208,17318416,32505887]
def z801 : List Nat := [6,1082401,2164802,4329604,17318911,32506848]
def z802 : List Nat := [6,1082401,2164802,4329604,32506848,33047071]
def z803 : List Nat := [6,1082401,2164831,6494406,8659944,32505856]
def z804 : List Nat := [6,1082401,2164831,8659944,17318416,32776456]
def z805 : List Nat := [6,1082401,2164831,8659944,25977624,32505856]
def z806 : List Nat := [6,1082401,2165759,8659208,17318416,32506848]
def z807 : List Nat := [6,1082401,6494406,6494431,8659944,32505856]
def z808 : List Nat := [6,1082401,6494406,8659208,32505887,32506848]
def z809 : List Nat := [6,1082401,6494406,8659944,32505856,32505887]
def z810 : List Nat := [6,1082401,6494406,8659944,32505856,33554400]
def z811 : List Nat := [6,1082401,6494406,17318416,32505887,32506848]
def z812 : List Nat := [6,1082401,6494406,17318431,32505856,32506848]
def z813 : List Nat := [6,1082401,6494406,17318431,32505856,33553439]
def z814 : List Nat := [6,1082401,6494431,8659944,17318416,32505856]
def z815 : List Nat := [6,1082401,8659208,16236015,32505887,32506848]
def z816 : List Nat := [6,1082401,8659208,17318416,17318911,32506848]
def z817 : List Nat := [6,1082401,8659208,17318416,32505887,32506848]
def z818 : List Nat := [6,1082401,8659208,17318416,32505887,32540641]
def z819 : List Nat := [6,1082401,8659208,17318416,32505887,33553408]
def z820 : List Nat := [6,1082401,8659208,17318416,32506848,32573535]
def z821 : List Nat := [6,1082401,8659208,17318416,32506848,33047071]
def z822 : List Nat := [6,1082401,8659208,17318416,32506848,33553408]
def z823 : List Nat := [6,1082401,8659208,17318431,17318896,32506848]
def z824 : List Nat := [6,1082401,8659208,17318431,32506848,33047056]
def z825 : List Nat := [6,1082401,8659208,18400817,32505887,32506848]
def z826 : List Nat := [6,1082401,8659208,25977624,32505887,32506848]
def z827 : List Nat := [6,1082401,8659944,17318416,17318431,32776456]
def z828 : List Nat := [6,1082401,8659944,17318416,32776456,33554400]
def z829 : List Nat := [6,1082401,8659944,25977624,32505856,32505887]
def z830 : List Nat := [6,1082401,8659944,25977624,32505856,33554400]
def z831 : List Nat := [6,1082401,8682760,17318416,32505887,32506848]
def z832 : List Nat := [6,1082401,8682760,17318416,32505887,33521664]
def z833 : List Nat := [6,1082401,9436424,17318416,32505856,32505887]
def z834 : List Nat := [6,1082401,9436424,17318416,32505856,33554400]
def z835 : List Nat := [6,1082401,9741609,17318416,32505887,32506848]
def z836 : List Nat := [6,1082401,17318416,24895223,32505887,32506848]
def z837 : List Nat := [6,1082401,17318416,25977624,32505887,32506848]
def z838 : List Nat := [6,1082401,17318431,25977624,32505856,32506848]
def z839 : List Nat := [6,1082401,17318431,25977624,32505856,33553439]
def z840 : List Nat := [6,1082431,1083361,8659208,17318416,32505887]
def z841 : List Nat := [6,1082431,2164802,4329604,8659944,32505887]
def z842 : List Nat := [6,1083361,2164831,6494406,8659208,32505856]
def z843 : List Nat := [6,1083361,2164831,6494406,17318416,32505856]
def z844 : List Nat := [6,1083361,2164831,8659208,18400817,32505856]
def z845 : List Nat := [6,1083361,2164831,9741609,17318416,32505856]
def z846 : List Nat := [6,1083361,6494406,6494431,8659208,32505856]
def z847 : List Nat := [6,1083361,6494406,6494431,17318416,32505856]
def z848 : List Nat := [6,1083361,6494406,8659208,32505856,32505887]
def z849 : List Nat := [6,1083361,6494406,8659208,32505856,33554400]
def z850 : List Nat := [6,1083361,6494406,17318416,17318431,32505856]
def z851 : List Nat := [6,1083361,6494406,17318416,32505856,32505887]
def z852 : List Nat := [6,1083361,6494406,17318416,32505856,33554400]
def z853 : List Nat := [6,1083361,6494431,8659208,17318416,32505856]
def z854 : List Nat := [6,1083361,8659208,17318416,32505887,32539681]
def z855 : List Nat := [6,1083361,8659208,18400817,32505856,32505887]
def z856 : List Nat := [6,1083361,8659208,18400817,32505856,33554400]
def z857 : List Nat := [6,1083361,9741609,17318416,17318431,32505856]
def z858 : List Nat := [6,1083361,9741609,17318416,32505856,32505887]
def z859 : List Nat := [6,1083361,9741609,17318416,32505856,33554400]
def z860 : List Nat := [6,1083391,2164802,4329604,8659208,32505887]
def z861 : List Nat := [6,1083391,2164802,4329604,17318416,32505887]
def z862 : List Nat := [6,1113121,8659208,17318416,32505887,32506848]
def z863 : List Nat := [6,1113121,8659208,17318416,32505887,33521664]
def z864 : List Nat := [6,1113121,9412872,17318416,32505856,32505887]
def z865 : List Nat := [6,1113121,9412872,17318416,32505856,33554400]
def z866 : List Nat := [6,2096161,8659208,17318416,32505856,32505887]
def z867 : List Nat := [6,2096161,8659208,17318416,32505856,33554400]
def z868 : List Nat := [6,2164802,4329604,8389600,17318431,32505856]
def z869 : List Nat := [6,2164802,4329604,8659208,17318911,32506848]
def z870 : List Nat := [6,2164802,4329604,8659944,17318431,32506848]
def z871 : List Nat := [6,2164802,4329604,8659944,17318431,32776456]
def z872 : List Nat := [6,2164802,8659208,17318431,32506848,32641156]
def z873 : List Nat := [6,2164831,6494406,8659944,17318416,32505856]
def z874 : List Nat := [6,2164831,8659944,9741609,17318416,32505856]
def z875 : List Nat := [6,6494406,6494431,8659944,17318416,32505856]
def z876 : List Nat := [6,6494406,8659208,8659944,17318431,32505856]
def z877 : List Nat := [6,6494406,8659208,17318416,32505887,32506848]
def z878 : List Nat := [6,6494406,8659208,17318431,32505856,32506848]
def z879 : List Nat := [6,6494406,8659208,17318431,32505856,33553439]
def z880 : List Nat := [6,6494406,8659944,17318416,17318431,32505856]
def z881 : List Nat := [6,6494406,8659944,17318416,32505856,32505887]
def z882 : List Nat := [6,6494406,8659944,17318416,32505856,33554400]
def z883 : List Nat := [6,8659208,8659944,17318416,32505887,32539681]
def z884 : List Nat := [6,8659208,8659944,17318431,18400817,32505856]
def z885 : List Nat := [6,8659208,9741609,17318416,32505887,32506848]
def z886 : List Nat := [6,8659208,17318416,18400817,32505887,32506848]
def z887 : List Nat := [6,8659208,17318416,32472030,32505887,32506848]
def z888 : List Nat := [6,8659208,17318416,32505887,32506848,32539681]
def z889 : List Nat := [6,8659208,17318416,32505887,32506879,32539681]
def z890 : List Nat := [6,8659208,17318416,32505887,32539681,32540641]
def z891 : List Nat := [6,8659208,17318416,32505887,32539681,33553439]
def z892 : List Nat := [6,8659208,17318431,18400817,32505856,32506848]
def z893 : List Nat := [6,8659208,17318431,18400817,32505856,33553439]
def z894 : List Nat := [6,8659944,9741609,17318416,17318431,32505856]
def z895 : List Nat := [6,8659944,9741609,17318416,32505856,32505887]
def z896 : List Nat := [6,8659944,9741609,17318416,32505856,33554400]
def z897 : List Nat := [7,1,992,1082431,8659208,17318416,32505856]
def z898 : List Nat := [7,8,992,1082401,8659231,17318416,32505856]
def z899 : List Nat := [7,9,992,1082401,8659208,17318416,32505856]
def z900 : List Nat := [7,9,992,1082401,9741609,17318416,32505856]
def z901 : List Nat := [7,9,992,8659208,9741609,17318416,32505856]
def z902 : List Nat := [7,15,992,1082401,8659208,16236015,32505856]
def z903 : List Nat := [7,15,992,1082401,8659208,17318416,32505856]
def z904 : List Nat := [7,27,992,1082401,8659208,17318416,32505856]
def z905 : List Nat := [7,31,32,31744,1082401,9412872,17318416]
def z906 : List Nat := [7,31,32,1047552,1082401,8659208,17318416]
def z907 : List Nat := [7,31,32,1082401,8659208,17318416,32506848]
def z908 : List Nat := [7,31,33,992,8659208,17318416,32505856]
def z909 : List Nat := [7,31,33,1023,8659208,17318416,32505856]
def z910 : List Nat := [7,31,33,31744,1015808,8659208,17318416]
def z911 : List Nat := [7,31,512,1082401,8659208,17318896,32505856]
def z912 : List Nat := [7,31,736,1082401,8659208,17318416,32505856]
def z913 : List Nat := [7,31,736,1082401,17318416,24895223,32505856]
def z914 : List Nat := [7,31,960,1082401,8659208,17318416,32505856]
def z915 : List Nat := [7,31,960,8659208,17318416,32472030,32505856]
def z916 : List Nat := [7,31,992,31744,1015808,1082401,6494406,8659208,33047056]
def z917 : List Nat := [7,31,992,31744,1015808,1082401,6494406,17318416,32776456]
def z918 : List Nat := [7,31,992,31744,1015808,9741609,18400817]
def z919 : List Nat := [7,31,992,31744,1015808,9741609,25977624]
def z920 : List Nat := [7,31,992,31744,1015808,18400817,25977624]
def z921 : List Nat := [7,31,992,31744,1082401,2164802,5214340,8659208,33047056]
def z922 : List Nat := [7,31,992,31744,1082401,6494406,9412872,17318416,32505856]
def z923 : List Nat := [7,31,992,31744,1082401,6494406,32776456]
def z924 : List Nat := [7,31,992,31744,1082401,7313606,8659208,17318416,32505856]
def z925 : List Nat := [7,31,992,31744,1082401,9412872,16236015]
def z926 : List Nat := [7,31,992,31744,1082401,9412872,17318416]
def z927 : List Nat := [7,31,992,31744,1082401,9412872,18400817]
def z928 : List Nat := [7,31,992,31744,1082401,9436424,17318416]
def z929 : List Nat := [7,31,992,31744,1082401,17318416,24141559]
def z930 : List Nat := [7,31,992,31744,1082401,25977624,32776456]
def z931 : List Nat := [7,31,992,31744,1113121,9412872,17318416]
def z932 : List Nat := [7,31,992,31744,2065441,2164802,4329604,8659208,33047056]
def z933 : List Nat := [7,31,992,31744,2065441,6494406,8659208,17318416,32505856]
def z934 : List Nat := [7,31,992,31744,2065441,9412872,17318416]
def z935 : List Nat := [7,31,992,31744,6494406,9412872,17318416]
def z936 : List Nat := [7,31,992,31744,9412872,9741609,17318416]
def z937 : List Nat := [7,31,992,31744,9412872,10462505,17318416]
def z938 : List Nat := [7,31,992,31744,9412872,17318416,18400817]
def z939 : List Nat := [7,31,992,31744,9412872,17318416,32472030]
def z940 : List Nat := [7,31,992,31744,9412872,17318416,32539681]
def z941 : List Nat := [7,31,992,31744,9741609,18400817,32505856]
def z942 : List Nat := [7,31,992,31744,9741609,25977624,32505856]
def z943 : List Nat := [7,31,992,31744,18400817,25977624,32505856]
def z944 : List Nat := [7,31,992,31775,1082401,9412872,17318416]
def z945 : List Nat := [7,31,992,32736,1082401,9412872,17318416]
def z946 : List Nat := [7,31,992,33825,1048575,8659208,17318416]
def z947 : List Nat := [7,31,992,33825,8659208,17318416,32505856]
def z948 : List Nat := [7,31,992,777975,1082401,2164802,4329604]
def z949 : List Nat := [7,31,992,777975,1082401,8659208,17318416]
def z950 : List Nat := [7,31,992,1014750,8659208,17318416,32505856]
def z951 : List Nat := [7,31,992,1047552,1082401,2164802,4329604,8659208,33047056]
def z952 : List Nat := [7,31,992,1047552,1082401,2164802,4329604,17318416,32776456]
def z953 : List Nat := [7,31,992,1047552,1082401,6494406,8659208]
def z954 : List Nat := [7,31,992,1047552,1082401,6494406,8659208,17318416,32505856]
def z955 : List Nat := [7,31,992,1047552,1082401,6494406,17318416]
def z956 : List Nat := [7,31,992,1047552,1082401,8659208,16236015]
def z957 : List Nat := [7,31,992,1047552,1082401,8659208,17318416]
def z958 : List Nat := [7,31,992,1047552,1082401,8659208,18400817]
def z959 : List Nat := [7,31,992,1047552,1082401,8659208,25977624]
def z960 : List Nat := [7,31,992,1047552,1082401,8682760,17318416]
def z961 : List Nat := [7,31,992,1047552,1082401,9436424,17318416]
def z962 : List Nat := [7,31,992,1047552,1082401,9741609,17318416]
def z963 : List Nat := [7,31,992,1047552,1082401,17318416,24895223]
def z964 : List Nat := [7,31,992,1047552,1082401,17318416,25977624]
def z965 : List Nat := [7,31,992,1047552,1113121,8659208,17318416]
def z966 : List Nat := [7,31,992,1047552,2096161,8659208,17318416]
def z967 : List Nat := [7,31,992,1047552,6494406,8659208,17318416]
def z968 : List Nat := [7,31,992,1047552,8659208,9741609,17318416]
def z969 : List Nat := [7,31,992,1047552,8659208,17318416,18400817]
def z970 : List Nat := [7,31,992,1047552,8659208,17318416,32472030]
def z971 : List Nat := [7,31,992,1047552,8659208,17318416,32539681]
def z972 : List Nat := [7,31,992,1047583,1082401,8659208,17318416]
def z973 : List Nat := [7,31,992,1048544,1082401,8659208,17318416]
def z974 : List Nat := [7,31,992,1048575,1082401,6494406,8659208]
def z975 : List Nat := [7,31,992,1048575,1082401,6494406,17318416]
def z976 : List Nat := [7,31,992,1048575,1082401,8659208,16236015]
def z977 : List Nat := [7,31,992,1048575,1082401,8659208,17318416]
def z978 : List Nat := [7,31,992,1048575,1082401,8659208,18400817]
def z979 : List Nat := [7,31,992,1048575,1082401,8659208,25977624]
def z980 : List Nat := [7,31,992,1048575,1082401,8682760,17318416]
def z981 : List Nat := [7,31,992,1048575,1082401,9741609,17318416]
def z982 : List Nat := [7,31,992,1048575,1082401,17318416,24895223]
def z983 : List Nat := [7,31,992,1048575,1082401,17318416,25977624]
def z984 : List Nat := [7,31,992,1048575,1113121,8659208,17318416]
def z985 : List Nat := [7,31,992,1048575,6494406,8659208,17318416]
def z986 : List Nat := [7,31,992,1048575,8659208,9741609,17318416]
def z987 : List Nat := [7,31,992,1048575,8659208,17318416,18400817]
def z988 : List Nat := [7,31,992,1048575,8659208,17318416,32472030]
def z989 : List Nat := [7,31,992,1048575,8659208,17318416,32539681]
def z990 : List Nat := [7,31,992,1048576,6494406,17318416,32505856]
def z991 : List Nat := [7,31,992,1048576,9741609,17318416,32505856]
def z992 : List Nat := [7,31,992,1049633,8659208,17318416,32505856]
def z993 : List Nat := [7,31,992,1082401,2164802,4329604,9436424,17318416,32505856]
def z994 : List Nat := [7,31,992,1082401,2164802,4329604,32776456]
def z995 : List Nat := [7,31,992,1082401,2164802,4329604,32776479]
def z996 : List Nat := [7,31,992,1082401,2164802,4329604,32777192]
def z997 : List Nat := [7,31,992,1082401,2164802,4357252,9412872,17318416,32505856]
def z998 : List Nat := [7,31,992,1082401,2164802,5241988,8659208,17318416,32505856]
def z999 : List Nat := [7,31,992,1082401,2164802,5412005,32776456]
def z1000 : List Nat := [7,31,992,1082401,2164802,6494406,32776456]
def z1001 : List Nat := [7,31,992,1082401,2164802,9436424,17318416]
def z1002 : List Nat := [7,31,992,1082401,2164802,25977624,32776456]
def z1003 : List Nat := [7,31,992,1082401,2164802,29224827,32776456]
def z1004 : List Nat := [7,31,992,1082401,2194498,5214340,8659208,17318416,32505856]
def z1005 : List Nat := [7,31,992,1082401,6494406,8659208,32505856]
def z1006 : List Nat := [7,31,992,1082401,6494406,8659208,32505887]
def z1007 : List Nat := [7,31,992,1082401,6494406,8659208,32506848]
def z1008 : List Nat := [7,31,992,1082401,6494406,8659208,32776456]
def z1009 : List Nat := [7,31,992,1082401,6494406,8659231,32505856]
def z1010 : List Nat := [7,31,992,1082401,6494406,8659944,32505856]
def z1011 : List Nat := [7,31,992,1082401,6494406,9741609,32505856]
def z1012 : List Nat := [7,31,992,1082401,6494406,10824010,32505856]
def z1013 : List Nat := [7,31,992,1082401,6494406,15153614,32505856]
def z1014 : List Nat := [7,31,992,1082401,6494406,16236015,32505856]
def z1015 : List Nat := [7,31,992,1082401,6494406,17318416,32505856]
def z1016 : List Nat := [7,31,992,1082401,6494406,17318416,32505887]
def z1017 : List Nat := [7,31,992,1082401,6494406,17318416,32506848]
def z1018 : List Nat := [7,31,992,1082401,6494406,17318416,32776456]
def z1019 : List Nat := [7,31,992,1082401,6494406,17318431,32505856]
def z1020 : List Nat := [7,31,992,1082401,6494406,17318896,32505856]
def z1021 : List Nat := [7,31,992,1082401,6494406,18400817,32505856]
def z1022 : List Nat := [7,31,992,1082401,6494406,19483218,32505856]
def z1023 : List Nat := [7,31,992,1082401,6494406,23812822,32505856]
def z1024 : List Nat := [7,31,992,1082401,6494406,24895223,32505856]
def z1025 : List Nat := [7,31,992,1082401,6494406,32505856,32776456]
def z1026 : List Nat := [7,31,992,1082401,6494406,32505856,33047056]
def z1027 : List Nat := [7,31,992,1082401,6494406,32776456]
def z1028 : List Nat := [7,31,992,1082401,6520006,17318416,32505856]
def z1029 : List Nat := [7,31,992,1082401,7576807,8659208,32505856]
def z1030 : List Nat := [7,31,992,1082401,7576807,17318416,32505856]
def z1031 : List Nat := [7,31,992,1082401,8397064,17318416,32505856]
def z1032 : List Nat := [7,31,992,1082401,8659208,9436424,17318416]
def z1033 : List Nat := [7,31,992,1082401,8659208,9437183,17318416]
def z1034 : List Nat := [7,31,992,1082401,8659208,15153614,32505856]
def z1035 : List Nat := [7,31,992,1082401,8659208,16236015,32505856]
def z1036 : List Nat := [7,31,992,1082401,8659208,16236015,32505887]
def z1037 : List Nat := [7,31,992,1082401,8659208,16236015,32506848]
def z1038 : List Nat := [7,31,992,1082401,8659208,16236015,32776456]
def z1039 : List Nat := [7,31,992,1082401,8659208,16777216,33047056]
def z1040 : List Nat := [7,31,992,1082401,8659208,17318416,24117248]
def z1041 : List Nat := [7,31,992,1082401,8659208,17318416,32505856]
def z1042 : List Nat := [7,31,992,1082401,8659208,17318416,32505857]
def z1043 : List Nat := [7,31,992,1082401,8659208,17318416,32505858]
def z1044 : List Nat := [7,31,992,1082401,8659208,17318416,32505864]
def z1045 : List Nat := [7,31,992,1082401,8659208,17318416,32505872]
def z1046 : List Nat := [7,31,992,1082401,8659208,17318416,32505887]
def z1047 : List Nat := [7,31,992,1082401,8659208,17318416,32505888]
def z1048 : List Nat := [7,31,992,1082401,8659208,17318416,32505920]
def z1049 : List Nat := [7,31,992,1082401,8659208,17318416,32506112]
def z1050 : List Nat := [7,31,992,1082401,8659208,17318416,32506368]
def z1051 : List Nat := [7,31,992,1082401,8659208,17318416,32506848]
def z1052 : List Nat := [7,31,992,1082401,8659208,17318416,32506879]
def z1053 : List Nat := [7,31,992,1082401,8659208,17318416,32514048]
def z1054 : List Nat := [7,31,992,1082401,8659208,17318416,32776456]
def z1055 : List Nat := [7,31,992,1082401,8659208,17318416,32776479]
def z1056 : List Nat := [7,31,992,1082401,8659208,17318416,32777192]
def z1057 : List Nat := [7,31,992,1082401,8659208,17318417,32505856]
def z1058 : List Nat := [7,31,992,1082401,8659208,17318424,32505856]
def z1059 : List Nat := [7,31,992,1082401,8659208,17318448,32505856]
def z1060 : List Nat := [7,31,992,1082401,8659208,17318672,32505856]
def z1061 : List Nat := [7,31,992,1082401,8659208,17319440,32505856]
def z1062 : List Nat := [7,31,992,1082401,8659208,17326608,32505856]
def z1063 : List Nat := [7,31,992,1082401,8659208,18366992,32505856]
def z1064 : List Nat := [7,31,992,1082401,8659208,18400817,32505856]
def z1065 : List Nat := [7,31,992,1082401,8659208,18400817,32505887]
def z1066 : List Nat := [7,31,992,1082401,8659208,18400817,32506848]
def z1067 : List Nat := [7,31,992,1082401,8659208,18400817,32776456]
def z1068 : List Nat := [7,31,992,1082401,8659208,25707024,32505856]
def z1069 : List Nat := [7,31,992,1082401,8659208,25977624,32505856]
def z1070 : List Nat := [7,31,992,1082401,8659208,25977624,32505887]
def z1071 : List Nat := [7,31,992,1082401,8659208,25977624,32506848]
def z1072 : List Nat := [7,31,992,1082401,8659208,25977624,32776456]
def z1073 : List Nat := [7,31,992,1082401,8659208,27060025,32505856]
def z1074 : List Nat := [7,31,992,1082401,8659209,17318416,32505856]
def z1075 : List Nat := [7,31,992,1082401,8659224,17318416,32505856]
def z1076 : List Nat := [7,31,992,1082401,8659231,17318416,32776456]
def z1077 : List Nat := [7,31,992,1082401,8659231,25977624,32505856]
def z1078 : List Nat := [7,31,992,1082401,8659240,17318416,32505856]
def z1079 : List Nat := [7,31,992,1082401,8659720,17318416,32505856]
def z1080 : List Nat := [7,31,992,1082401,8659944,17318416,32776456]
def z1081 : List Nat := [7,31,992,1082401,8659944,25977624,32505856]
def z1082 : List Nat := [7,31,992,1082401,8660232,17318416,32505856]
def z1083 : List Nat := [7,31,992,1082401,8661256,17318416,32505856]
def z1084 : List Nat := [7,31,992,1082401,8675592,17318416,32505856]
def z1085 : List Nat := [7,31,992,1082401,8682760,9412872,17318416]
def z1086 : List Nat := [7,31,992,1082401,8682760,9436424,17318416]
def z1087 : List Nat := [7,31,992,1082401,8682760,16236015,32505856]
def z1088 : List Nat := [7,31,992,1082401,8682760,17318416,32505856]
def z1089 : List Nat := [7,31,992,1082401,8682760,17318416,32505887]
def z1090 : List Nat := [7,31,992,1082401,8682760,17318416,32506848]
def z1091 : List Nat := [7,31,992,1082401,8682760,17318416,32537600]
def z1092 : List Nat := [7,31,992,1082401,8682760,17318416,32538623]
def z1093 : List Nat := [7,31,992,1082401,8682760,17318416,32776456]
def z1094 : List Nat := [7,31,992,1082401,8682760,17318416,32800008]
def z1095 : List Nat := [7,31,992,1082401,8682760,18400817,32505856]
def z1096 : List Nat := [7,31,992,1082401,9436424,17318416]
def z1097 : List Nat := [7,31,992,1082401,9436424,17318416,32505856]
def z1098 : List Nat := [7,31,992,1082401,9707784,17318416,32505856]
def z1099 : List Nat := [7,31,992,1082401,9741609,16236015,32505856]
def z1100 : List Nat := [7,31,992,1082401,9741609,17318416,32505856]
def z1101 : List Nat := [7,31,992,1082401,9741609,17318416,32505887]
def z1102 : List Nat := [7,31,992,1082401,9741609,17318416,32506848]
def z1103 : List Nat := [7,31,992,1082401,9741609,17318416,32776456]
def z1104 : List Nat := [7,31,992,1082401,9741609,18400817,32505856]
def z1105 : List Nat := [7,31,992,1082401,9741609,25977624,32505856]
def z1106 : List Nat := [7,31,992,1082401,9741609,27060025,32505856]
def z1107 : List Nat := [7,31,992,1082401,9764137,17318416,32505856]
def z1108 : List Nat := [7,31,992,1082401,10824010,12988812,32505856]
def z1109 : List Nat := [7,31,992,1082401,10824010,19483218,32505856]
def z1110 : List Nat := [7,31,992,1082401,10824010,25977624,32505856]
def z1111 : List Nat := [7,31,992,1082401,16236015,24895223,32505856]
def z1112 : List Nat := [7,31,992,1082401,16236015,25977624,32505856]
def z1113 : List Nat := [7,31,992,1082401,17318416,23812822,32505856]
def z1114 : List Nat := [7,31,992,1082401,17318416,24117248,24895223]
def z1115 : List Nat := [7,31,992,1082401,17318416,24141559,32505856]
def z1116 : List Nat := [7,31,992,1082401,17318416,24895223,32505856]
def z1117 : List Nat := [7,31,992,1082401,17318416,24895223,32505887]
def z1118 : List Nat := [7,31,992,1082401,17318416,24895223,32506848]
def z1119 : List Nat := [7,31,992,1082401,17318416,24895223,32776456]
def z1120 : List Nat := [7,31,992,1082401,17318416,24903415,32505856]
def z1121 : List Nat := [7,31,992,1082401,17318416,25436424,32505856]
def z1122 : List Nat := [7,31,992,1082401,17318416,25977624,32505856]
def z1123 : List Nat := [7,31,992,1082401,17318416,25977624,32505887]
def z1124 : List Nat := [7,31,992,1082401,17318416,25977624,32506848]
def z1125 : List Nat := [7,31,992,1082401,17318416,25977624,32776456]
def z1126 : List Nat := [7,31,992,1082401,17318416,25984792,32505856]
def z1127 : List Nat := [7,31,992,1082401,17318416,27060025,32505856]
def z1128 : List Nat := [7,31,992,1082401,17318431,25977624,32505856]
def z1129 : List Nat := [7,31,992,1082401,17318896,25977624,32505856]
def z1130 : List Nat := [7,31,992,1082401,18400817,24895223,32505856]
def z1131 : List Nat := [7,31,992,1082401,18400817,25977624,32505856]
def z1132 : List Nat := [7,31,992,1082401,18400817,27060025,32505856]
def z1133 : List Nat := [7,31,992,1082401,19483218,21648020,32505856]
def z1134 : List Nat := [7,31,992,1082401,19483218,25977624,32505856]
def z1135 : List Nat := [7,31,992,1082401,24895223,25977624,32505856]
def z1136 : List Nat := [7,31,992,1082401,25977624,32505856,32776456]
def z1137 : List Nat := [7,31,992,1082401,25977624,32505856,33047056]
def z1138 : List Nat := [7,31,992,1082401,25977624,32776456]
def z1139 : List Nat := [7,31,992,1082409,8659208,17318416,32505856]
def z1140 : List Nat := [7,31,992,1082417,8659208,17318416,32505856]
def z1141 : List Nat := [7,31,992,1082431,2164802,4329604,32776456]
def z1142 : List Nat := [7,31,992,1082431,6494406,8659208,32505856]
def z1143 : List Nat := [7,31,992,1082431,6494406,17318416,32505856]
def z1144 : List Nat := [7,31,992,1082431,8659208,18400817,32505856]
def z1145 : List Nat := [7,31,992,1082431,9741609,17318416,32505856]
def z1146 : List Nat := [7,31,992,1082657,8659208,17318416,32505856]
def z1147 : List Nat := [7,31,992,1082913,8659208,17318416,32505856]
def z1148 : List Nat := [7,31,992,1083361,2164802,4329604,32776456]
def z1149 : List Nat := [7,31,992,1083361,6494406,8659208,32505856]
def z1150 : List Nat := [7,31,992,1083361,6494406,17318416,32505856]
def z1151 : List Nat := [7,31,992,1083361,8659208,18400817,32505856]
def z1152 : List Nat := [7,31,992,1083361,9741609,17318416,32505856]
def z1153 : List Nat := [7,31,992,1084449,8659208,17318416,32505856]
def z1154 : List Nat := [7,31,992,1090593,8659208,17318416,32505856]
def z1155 : List Nat := [7,31,992,1098785,8659208,17318416,32505856]
def z1156 : List Nat := [7,31,992,1113121,2164802,4329604,9412872,17318416,32505856]
def z1157 : List Nat := [7,31,992,1113121,2164802,5214340,8659208,17318416,32505856]
def z1158 : List Nat := [7,31,992,1113121,6494406,17318416,32505856]
def z1159 : List Nat := [7,31,992,1113121,8659208,16236015,32505856]
def z1160 : List Nat := [7,31,992,1113121,8659208,17318416,32505856]
def z1161 : List Nat := [7,31,992,1113121,8659208,17318416,32505887]
def z1162 : List Nat := [7,31,992,1113121,8659208,17318416,32506848]
def z1163 : List Nat := [7,31,992,1113121,8659208,17318416,32776456]
def z1164 : List Nat := [7,31,992,1113121,8659208,25977624,32505856]
def z1165 : List Nat := [7,31,992,1113121,8682760,17318416,32505856]
def z1166 : List Nat := [7,31,992,1113121,9412872,17318416,32505856]
def z1167 : List Nat := [7,31,992,1113121,9741609,17318416,32505856]
def z1168 : List Nat := [7,31,992,1113121,9764137,17318416,32505856]
def z1169 : List Nat := [7,31,992,1113121,17318416,24895223,32505856]
def z1170 : List Nat := [7,31,992,1113121,17318416,25977624,32505856]
def z1171 : List Nat := [7,31,992,2096161,2164802,4329604,8659208,17318416,32505856]
def z1172 : List Nat := [7,31,992,2096161,8659208,17318416,32505856]
def z1173 : List Nat := [7,31,992,2164802,3247203,4329604,32776456]
def z1174 : List Nat := [7,31,992,2164802,4329604,9436424,17318416]
def z1175 : List Nat := [7,31,992,2164802,4329604,9437183,17318416]
def z1176 : List Nat := [7,31,992,2164802,4329604,17318416,24117248]
def z1177 : List Nat := [7,31,992,2164802,4329604,25707024,32505856]
def z1178 : List Nat := [7,31,992,2164802,4329604,25977624,32776456]
def z1179 : List Nat := [7,31,992,2164802,4329604,32472030,32776456]
def z1180 : List Nat := [7,31,992,2164802,5378180,17318416,32505856]
def z1181 : List Nat := [7,31,992,2164802,5412005,9741609,32505856]
def z1182 : List Nat := [7,31,992,2164802,5412005,12988812,32505856]
def z1183 : List Nat := [7,31,992,2164802,5412005,18400817,32505856]
def z1184 : List Nat := [7,31,992,2164802,5412005,21648020,32505856]
def z1185 : List Nat := [7,31,992,2164802,9741609,12988812,32505856]
def z1186 : List Nat := [7,31,992,2164802,9741609,18400817,32505856]
def z1187 : List Nat := [7,31,992,2164802,9741609,25977624,32505856]
def z1188 : List Nat := [7,31,992,2164802,12988812,21648020,32505856]
def z1189 : List Nat := [7,31,992,2164802,12988812,25977624,32505856]
def z1190 : List Nat := [7,31,992,2164802,18400817,21648020,32505856]
def z1191 : List Nat := [7,31,992,2164802,18400817,25977624,32505856]
def z1192 : List Nat := [7,31,992,2164802,21648020,25977624,32505856]
def z1193 : List Nat := [7,31,992,3179553,8659208,17318416,32505856]
def z1194 : List Nat := [7,31,992,3247203,5412005,8659208,32505856]
def z1195 : List Nat := [7,31,992,3247203,5412005,17318416,32505856]
def z1196 : List Nat := [7,31,992,3247203,6494406,8659208,32505856]
def z1197 : List Nat := [7,31,992,3247203,6494406,17318416,32505856]
def z1198 : List Nat := [7,31,992,3247203,8659208,18400817,32505856]
def z1199 : List Nat := [7,31,992,3247203,8659208,19483218,32505856]
def z1200 : List Nat := [7,31,992,3247203,9741609,17318416,32505856]
def z1201 : List Nat := [7,31,992,3247203,10824010,17318416,32505856]
def z1202 : List Nat := [7,31,992,6494406,7576807,8659208,32505856]
def z1203 : List Nat := [7,31,992,6494406,7576807,17318416,32505856]
def z1204 : List Nat := [7,31,992,6494406,8388608,17318416,32505856]
def z1205 : List Nat := [7,31,992,6494406,8659208,9741609,32505856]
def z1206 : List Nat := [7,31,992,6494406,8659208,16236015,32505856]
def z1207 : List Nat := [7,31,992,6494406,8659208,17318416,32505856]
def z1208 : List Nat := [7,31,992,6494406,8659208,17318416,32505887]
def z1209 : List Nat := [7,31,992,6494406,8659208,17318416,32506848]
def z1210 : List Nat := [7,31,992,6494406,8659208,17318416,32776456]
def z1211 : List Nat := [7,31,992,6494406,8659208,17318431,32505856]
def z1212 : List Nat := [7,31,992,6494406,8659208,17318896,32505856]
def z1213 : List Nat := [7,31,992,6494406,8659208,19483218,32505856]
def z1214 : List Nat := [7,31,992,6494406,8659208,23812822,32505856]
def z1215 : List Nat := [7,31,992,6494406,8659208,25977624,32505856]
def z1216 : List Nat := [7,31,992,6494406,8659208,32472030,32505856]
def z1217 : List Nat := [7,31,992,6494406,8659231,17318416,32505856]
def z1218 : List Nat := [7,31,992,6494406,8659944,17318416,32505856]
def z1219 : List Nat := [7,31,992,6494406,8682760,17318416,32505856]
def z1220 : List Nat := [7,31,992,6494406,10824010,17318416,32505856]
def z1221 : List Nat := [7,31,992,6494406,15153614,17318416,32505856]
def z1222 : List Nat := [7,31,992,6494406,17318416,18400817,32505856]
def z1223 : List Nat := [7,31,992,6494406,17318416,24895223,32505856]
def z1224 : List Nat := [7,31,992,6494406,17318416,25977624,32505856]
def z1225 : List Nat := [7,31,992,6494406,17318416,32472030,32505856]
def z1226 : List Nat := [7,31,992,6520006,8659208,17318416,32505856]
def z1227 : List Nat := [7,31,992,8388608,9741609,17318416,32505856]
def z1228 : List Nat := [7,31,992,8659208,9471009,17318416,32505856]
def z1229 : List Nat := [7,31,992,8659208,9741609,16236015,32505856]
def z1230 : List Nat := [7,31,992,8659208,9741609,17318416,32505856]
def z1231 : List Nat := [7,31,992,8659208,9741609,17318416,32505887]
def z1232 : List Nat := [7,31,992,8659208,9741609,17318416,32506848]
def z1233 : List Nat := [7,31,992,8659208,9741609,17318416,32776456]
def z1234 : List Nat := [7,31,992,8659208,9741609,18400817,32505856]
def z1235 : List Nat := [7,31,992,8659208,9741609,25977624,32505856]
def z1236 : List Nat := [7,31,992,8659208,9741609,27060025,32505856]
def z1237 : List Nat := [7,31,992,8659208,9764137,17318416,32505856]
def z1238 : List Nat := [7,31,992,8659208,15153614,17318416,32505856]
def z1239 : List Nat := [7,31,992,8659208,16236015,18400817,32505856]
def z1240 : List Nat := [7,31,992,8659208,16236015,32472030,32505856]
def z1241 : List Nat := [7,31,992,8659208,16236015,32505856,32539681]
def z1242 : List Nat := [7,31,992,8659208,17318416,17859617,32505856]
def z1243 : List Nat := [7,31,992,8659208,17318416,18400817,32505856]
def z1244 : List Nat := [7,31,992,8659208,17318416,18400817,32505887]
def z1245 : List Nat := [7,31,992,8659208,17318416,18400817,32506848]
def z1246 : List Nat := [7,31,992,8659208,17318416,18400817,32776456]
def z1247 : List Nat := [7,31,992,8659208,17318416,18415153,32505856]
def z1248 : List Nat := [7,31,992,8659208,17318416,23812822,32505856]
def z1249 : List Nat := [7,31,992,8659208,17318416,27060025,32505856]
def z1250 : List Nat := [7,31,992,8659208,17318416,31488990,32505856]
def z1251 : List Nat := [7,31,992,8659208,17318416,32472030,32505856]
def z1252 : List Nat := [7,31,992,8659208,17318416,32472030,32505887]
def z1253 : List Nat := [7,31,992,8659208,17318416,32472030,32506848]
def z1254 : List Nat := [7,31,992,8659208,17318416,32472030,32776456]
def z1255 : List Nat := [7,31,992,8659208,17318416,32473054,32505856]
def z1256 : List Nat := [7,31,992,8659208,17318416,32505856,32539681]
def z1257 : List Nat := [7,31,992,8659208,17318416,32505856,32570401]
def z1258 : List Nat := [7,31,992,8659208,17318416,32505856,32708806]
def z1259 : List Nat := [7,31,992,8659208,17318416,32505856,32810281]
def z1260 : List Nat := [7,31,992,8659208,17318416,32505856,33080881]
def z1261 : List Nat := [7,31,992,8659208,17318416,32505856,33520606]
def z1262 : List Nat := [7,31,992,8659208,17318416,32505887,32539681]
def z1263 : List Nat := [7,31,992,8659208,17318416,32506848,32539681]
def z1264 : List Nat := [7,31,992,8659208,17318416,32539681,32573506]
def z1265 : List Nat := [7,31,992,8659208,17318416,32539681,32776456]
def z1266 : List Nat := [7,31,992,8659208,17318416,32539681,33047056]
def z1267 : List Nat := [7,31,992,8659208,17318416,32573506,32641156]
def z1268 : List Nat := [7,31,992,8659208,17318416,32776456,32810281]
def z1269 : List Nat := [7,31,992,8659208,17318431,18400817,32505856]
def z1270 : List Nat := [7,31,992,8659208,17318896,18400817,32505856]
def z1271 : List Nat := [7,31,992,8659208,18400817,19483218,32505856]
def z1272 : List Nat := [7,31,992,8659208,18400817,25977624,32505856]
def z1273 : List Nat := [7,31,992,8659208,18400817,32472030,32505856]
def z1274 : List Nat := [7,31,992,8659208,19483218,21648020,32505856]
def z1275 : List Nat := [7,31,992,8659208,25977624,27060025,32505856]
def z1276 : List Nat := [7,31,992,8659208,25977624,32472030,32505856]
def z1277 : List Nat := [7,31,992,8659208,25977624,32505856,32539681]
def z1278 : List Nat := [7,31,992,8659231,9741609,17318416,32505856]
def z1279 : List Nat := [7,31,992,8659944,9741609,17318416,32505856]
def z1280 : List Nat := [7,31,992,8682760,9741609,17318416,32505856]
def z1281 : List Nat := [7,31,992,8682760,9764137,17318416,32505856]
def z1282 : List Nat := [7,31,992,8682760,17318416,18400817,32505856]
def z1283 : List Nat := [7,31,992,8682760,17318416,32472030,32505856]
def z1284 : List Nat := [7,31,992,8682760,17318416,32505856,32539681]
def z1285 : List Nat := [7,31,992,9741609,10824010,17318416,32505856]
def z1286 : List Nat := [7,31,992,9741609,17318416,18400817,32505856]
def z1287 : List Nat := [7,31,992,9741609,17318416,24895223,32505856]
def z1288 : List Nat := [7,31,992,9741609,17318416,25977624,32505856]
def z1289 : List Nat := [7,31,992,9741609,17318416,32472030,32505856]
def z1290 : List Nat := [7,31,992,9741609,18400817,32505856]
def z1291 : List Nat := [7,31,992,9741609,25977624,32505856]
def z1292 : List Nat := [7,31,992,10824010,12988812,17318416,32505856]
def z1293 : List Nat := [7,31,992,17318416,18400817,24895223,32505856]
def z1294 : List Nat := [7,31,992,17318416,18400817,25977624,32505856]
def z1295 : List Nat := [7,31,992,17318416,18400817,27060025,32505856]
def z1296 : List Nat := [7,31,992,17318416,24895223,32472030,32505856]
def z1297 : List Nat := [7,31,992,17318416,24895223,32505856,32539681]
def z1298 : List Nat := [7,31,992,17318416,25977624,27060025,32505856]
def z1299 : List Nat := [7,31,992,17318416,25977624,32472030,32505856]
def z1300 : List Nat := [7,31,992,17318416,25977624,32505856,32539681]
def z1301 : List Nat := [7,31,992,18400817,25977624,32505856]
def z1302 : List Nat := [7,31,993,1082401,8659208,17318416,32505856]
def z1303 : List Nat := [7,31,994,1082401,8659208,17318416,32505856]
def z1304 : List Nat := [7,31,1000,1082401,8659208,17318416,32505856]
def z1305 : List Nat := [7,31,1008,1082401,8659208,17318416,32505856]
def z1306 : List Nat := [7,31,1023,31744,1082401,9412872,17318416]
def z1307 : List Nat := [7,31,1023,1047552,1082401,8659208,17318416]
def z1308 : List Nat := [7,31,1023,1048575,1082401,8659208,17318416]
def z1309 : List Nat := [7,31,1023,1082401,2164802,4329604,32776456]
def z1310 : List Nat := [7,31,1023,1082401,6494406,8659208,32505856]
def z1311 : List Nat := [7,31,1023,1082401,6494406,17318416,32505856]
def z1312 : List Nat := [7,31,1023,1082401,8659208,16236015,32505856]
def z1313 : List Nat := [7,31,1023,1082401,8659208,17318416,32505856]
def z1314 : List Nat := [7,31,1023,1082401,8659208,17318416,32505887]
def z1315 : List Nat := [7,31,1023,1082401,8659208,17318416,32506848]
def z1316 : List Nat := [7,31,1023,1082401,8659208,17318416,32506879]
def z1317 : List Nat := [7,31,1023,1082401,8659208,17318416,32776456]
def z1318 : List Nat := [7,31,1023,1082401,8659208,18400817,32505856]
def z1319 : List Nat := [7,31,1023,1082401,8659208,25977624,32505856]
def z1320 : List Nat := [7,31,1023,1082401,8682760,17318416,32505856]
def z1321 : List Nat := [7,31,1023,1082401,9741609,17318416,32505856]
def z1322 : List Nat := [7,31,1023,1082401,17318416,24895223,32505856]
def z1323 : List Nat := [7,31,1023,1082401,17318416,25977624,32505856]
def z1324 : List Nat := [7,31,1023,1113121,8659208,17318416,32505856]
def z1325 : List Nat := [7,31,1023,6494406,8659208,17318416,32505856]
def z1326 : List Nat := [7,31,1023,8659208,9741609,17318416,32505856]
def z1327 : List Nat := [7,31,1023,8659208,17318416,18400817,32505856]
def z1328 : List Nat := [7,31,1023,8659208,17318416,32472030,32505856]
def z1329 : List Nat := [7,31,1023,8659208,17318416,32505856,32539681]
def z1330 : List Nat := [7,31,2016,1082401,8659208,17318416,32505856]
def z1331 : List Nat := [7,31,9184,1082401,8659208,17318416,32505856]
def z1332 : List Nat := [7,31,31744,32736,1082401,9412872,17318416]
def z1333 : List Nat := [7,31,31744,33825,1015808,8659208,17318416]
def z1334 : List Nat := [7,31,31744,1015808,1048576,6494406,17318416]
def z1335 : List Nat := [7,31,31744,1015808,1048576,9741609,17318416]
def z1336 : List Nat := [7,31,31744,1015808,1082401,2164802,4329604,8659944,33047056]
def z1337 : List Nat := [7,31,31744,1015808,1082401,2164802,4329604,17318896,32776456]
def z1338 : List Nat := [7,31,31744,1015808,1082401,6494406,8659208,17318896,32505856]
def z1339 : List Nat := [7,31,31744,1015808,1082401,6494406,8659944]
def z1340 : List Nat := [7,31,31744,1015808,1082401,6494406,8659944,17318416,32505856]
def z1341 : List Nat := [7,31,31744,1015808,1082401,6494406,17318896]
def z1342 : List Nat := [7,31,31744,1015808,1082401,6494406,32776456]
def z1343 : List Nat := [7,31,31744,1015808,1082401,6494406,33047056]
def z1344 : List Nat := [7,31,31744,1015808,1082401,8659208,17318448]
def z1345 : List Nat := [7,31,31744,1015808,1082401,8659208,18366992]
def z1346 : List Nat := [7,31,31744,1015808,1082401,8659240,17318416]
def z1347 : List Nat := [7,31,31744,1015808,1082401,8659944,25977624]
def z1348 : List Nat := [7,31,31744,1015808,1082401,9707784,17318416]
def z1349 : List Nat := [7,31,31744,1015808,1082401,17318896,25977624]
def z1350 : List Nat := [7,31,31744,1015808,1082401,25977624,32776456]
def z1351 : List Nat := [7,31,31744,1015808,1082401,25977624,33047056]
def z1352 : List Nat := [7,31,31744,1015808,1083361,6494406,8659208,17318416,32505856]
def z1353 : List Nat := [7,31,31744,1015808,2164802,5378180,17318416]
def z1354 : List Nat := [7,31,31744,1015808,6494406,8659208,17318896]
def z1355 : List Nat := [7,31,31744,1015808,6494406,8659944,17318416]
def z1356 : List Nat := [7,31,31744,1015808,8659208,17318416,32708806]
def z1357 : List Nat := [7,31,31744,1015808,8659208,17318416,33520606]
def z1358 : List Nat := [7,31,31744,1015808,8659208,17318896,18400817]
def z1359 : List Nat := [7,31,31744,1015808,8659944,9741609,17318416]
def z1360 : List Nat := [7,31,31744,1015808,9741609,18400817,32505856]
def z1361 : List Nat := [7,31,31744,1015808,9741609,25977624,32505856]
def z1362 : List Nat := [7,31,31744,1015808,18400817,25977624,32505856]
def z1363 : List Nat := [7,31,31744,1015840,1082401,8659208,17318416]
def z1364 : List Nat := [7,31,31744,1016800,1082401,9412872,17318416]
def z1365 : List Nat := [7,31,31744,1016800,2065441,8659208,17318416]
def z1366 : List Nat := [7,31,31744,1048575,1082401,9412872,17318416]
def z1367 : List Nat := [7,31,31744,1048575,2065441,8659208,17318416]
def z1368 : List Nat := [7,31,31744,1048576,1082401,9412872,17318416]
def z1369 : List Nat := [7,31,31744,1048576,2065441,8659208,17318416]
def z1370 : List Nat := [7,31,31744,1082401,2164802,5214340,8659208,17318896,32505856]
def z1371 : List Nat := [7,31,31744,1082401,2165730,9412872,17318416]
def z1372 : List Nat := [7,31,31744,1082401,6494406,8659944,32505856]
def z1373 : List Nat := [7,31,31744,1082401,8659944,9412872,17318416]
def z1374 : List Nat := [7,31,31744,1082401,8659944,17318416,32776456]
def z1375 : List Nat := [7,31,31744,1082401,8659944,25977624,32505856]
def z1376 : List Nat := [7,31,31744,1082401,9412872,9413608,17318416]
def z1377 : List Nat := [7,31,31744,1082401,9412872,16236015,32505856]
def z1378 : List Nat := [7,31,31744,1082401,9412872,17318416,17318896]
def z1379 : List Nat := [7,31,31744,1082401,9412872,17318416,32505856]
def z1380 : List Nat := [7,31,31744,1082401,9412872,17318416,32505887]
def z1381 : List Nat := [7,31,31744,1082401,9412872,17318416,32537600]
def z1382 : List Nat := [7,31,31744,1082401,9412872,17318416,32573506]
def z1383 : List Nat := [7,31,31744,1082401,9412872,17318416,32776456]
def z1384 : List Nat := [7,31,31744,1082401,9412872,17318416,33047056]
def z1385 : List Nat := [7,31,31744,1082401,9412872,17318416,33521664]
def z1386 : List Nat := [7,31,31744,1082401,9412872,17318416,33530120]
def z1387 : List Nat := [7,31,31744,1082401,9412872,17318416,33553439]
def z1388 : List Nat := [7,31,31744,1082401,9412872,18400817,32505856]
def z1389 : List Nat := [7,31,31744,1082401,9436424,17318416,32505856]
def z1390 : List Nat := [7,31,31744,1082401,10462505,17318416,32505856]
def z1391 : List Nat := [7,31,31744,1082401,17318416,24141559,32505856]
def z1392 : List Nat := [7,31,31744,1083361,2164802,4329604,9412872,17318416,32505856]
def z1393 : List Nat := [7,31,31744,1083361,6494406,8659208,32505856]
def z1394 : List Nat := [7,31,31744,1083361,6494406,17318416,32505856]
def z1395 : List Nat := [7,31,31744,1083361,8659208,18400817,32505856]
def z1396 : List Nat := [7,31,31744,1083361,9741609,17318416,32505856]
def z1397 : List Nat := [7,31,31744,1113121,9412872,17318416,32505856]
def z1398 : List Nat := [7,31,31744,2065441,2164802,4329604,8659944,17318416,32505856]
def z1399 : List Nat := [7,31,31744,2065441,2164802,4329604,33047056]
def z1400 : List Nat := [7,31,31744,2065441,6494406,17318416,32505856]
def z1401 : List Nat := [7,31,31744,2065441,8659208,16236015,32505856]
def z1402 : List Nat := [7,31,31744,2065441,8659208,17318416,32505856]
def z1403 : List Nat := [7,31,31744,2065441,8659208,17318416,32505887]
def z1404 : List Nat := [7,31,31744,2065441,8659208,17318416,32537600]
def z1405 : List Nat := [7,31,31744,2065441,8659208,17318416,32776456]
def z1406 : List Nat := [7,31,31744,2065441,8659208,17318416,33047056]
def z1407 : List Nat := [7,31,31744,2065441,8659208,25977624,32505856]
def z1408 : List Nat := [7,31,31744,2065441,8682760,17318416,32505856]
def z1409 : List Nat := [7,31,31744,2065441,9412872,17318416,32505856]
def z1410 : List Nat := [7,31,31744,2065441,9741609,17318416,32505856]
def z1411 : List Nat := [7,31,31744,2065441,10462505,17318416,32505856]
def z1412 : List Nat := [7,31,31744,2065441,17318416,24895223,32505856]
def z1413 : List Nat := [7,31,31744,2065441,17318416,25977624,32505856]
def z1414 : List Nat := [7,31,31744,2096161,8659208,17318416,32505856]
def z1415 : List Nat := [7,31,31744,2164802,9412872,17318416,32641156]
def z1416 : List Nat := [7,31,31744,6494406,8659944,17318416,32505856]
def z1417 : List Nat := [7,31,31744,6494406,9412872,17318416,32505856]
def z1418 : List Nat := [7,31,31744,8659208,10462505,17318416,32505856]
def z1419 : List Nat := [7,31,31744,8659208,17318416,31488990,32505856]
def z1420 : List Nat := [7,31,31744,8659208,17318416,32505856,33522721]
def z1421 : List Nat := [7,31,31744,8659944,9741609,17318416,32505856]
def z1422 : List Nat := [7,31,31744,9412872,9741609,17318416,32505856]
def z1423 : List Nat := [7,31,31744,9412872,10462505,17318416,32505856]
def z1424 : List Nat := [7,31,31744,9412872,17318416,18400817,32505856]
def z1425 : List Nat := [7,31,31744,9412872,17318416,32472030,32505856]
def z1426 : List Nat := [7,31,31744,9412872,17318416,32505856,32539681]
def z1427 : List Nat := [7,31,31775,1082401,9412872,17318416,32505856]
def z1428 : List Nat := [7,31,31775,2065441,8659208,17318416,32505856]
def z1429 : List Nat := [7,31,32736,1016800,1082401,8659208,17318416]
def z1430 : List Nat := [7,31,32736,1047552,1082401,8659208,17318416]
def z1431 : List Nat := [7,31,32736,1082401,8659208,17318416,32506848]
def z1432 : List Nat := [7,31,32736,1082401,8659208,17318416,32537600]
def z1433 : List Nat := [7,31,32736,1082401,8682760,17318416,32505856]
def z1434 : List Nat := [7,31,32736,1113121,8659208,17318416,32505856]
def z1435 : List Nat := [7,31,1047552,1048544,1082401,8659208,17318416]
def z1436 : List Nat := [7,31,1047552,1048575,1082401,8659208,17318416]
def z1437 : List Nat := [7,31,1047552,1048576,1082401,8659208,17318416]
def z1438 : List Nat := [7,31,1047552,1048576,2164802,4329604,17318416]
def z1439 : List Nat := [7,31,1047552,1082401,2164802,4329604,8659208,17318896,32505856]
def z1440 : List Nat := [7,31,1047552,1082401,2164802,4329604,8659944]
def z1441 : List Nat := [7,31,1047552,1082401,2164802,4329604,8659944,17318416,32505856]
def z1442 : List Nat := [7,31,1047552,1082401,2164802,4329604,17318896]
def z1443 : List Nat := [7,31,1047552,1082401,2164802,4329604,32776456]
def z1444 : List Nat := [7,31,1047552,1082401,2164802,4329604,33047056]
def z1445 : List Nat := [7,31,1047552,1082401,2165730,8659208,17318416]
def z1446 : List Nat := [7,31,1047552,1082401,6494406,8659208,32505856]
def z1447 : List Nat := [7,31,1047552,1082401,6494406,17318416,32505856]
def z1448 : List Nat := [7,31,1047552,1082401,8659208,8659944,17318416]
def z1449 : List Nat := [7,31,1047552,1082401,8659208,16236015,32505856]
def z1450 : List Nat := [7,31,1047552,1082401,8659208,17318416,17318896]
def z1451 : List Nat := [7,31,1047552,1082401,8659208,17318416,32505856]
def z1452 : List Nat := [7,31,1047552,1082401,8659208,17318416,32505887]
def z1453 : List Nat := [7,31,1047552,1082401,8659208,17318416,32537600]
def z1454 : List Nat := [7,31,1047552,1082401,8659208,17318416,32573506]
def z1455 : List Nat := [7,31,1047552,1082401,8659208,17318416,32776456]
def z1456 : List Nat := [7,31,1047552,1082401,8659208,17318416,33047056]
def z1457 : List Nat := [7,31,1047552,1082401,8659208,17318416,33553408]
def z1458 : List Nat := [7,31,1047552,1082401,8659208,17318416,33553439]
def z1459 : List Nat := [7,31,1047552,1082401,8659208,18400817,32505856]
def z1460 : List Nat := [7,31,1047552,1082401,8659208,25977624,32505856]
def z1461 : List Nat := [7,31,1047552,1082401,8682760,17318416,32505856]
def z1462 : List Nat := [7,31,1047552,1082401,9436424,17318416,32505856]
def z1463 : List Nat := [7,31,1047552,1082401,9741609,17318416,32505856]
def z1464 : List Nat := [7,31,1047552,1082401,17318416,24895223,32505856]
def z1465 : List Nat := [7,31,1047552,1082401,17318416,25977624,32505856]
def z1466 : List Nat := [7,31,1047552,1083361,2164802,4329604,8659208,17318416,32505856]
def z1467 : List Nat := [7,31,1047552,1113121,8659208,17318416,32505856]
def z1468 : List Nat := [7,31,1047552,2096161,8659208,17318416,32505856]
def z1469 : List Nat := [7,31,1047552,2164802,4329604,8659208,17318896]
def z1470 : List Nat := [7,31,1047552,2164802,4329604,8659944,17318416]
def z1471 : List Nat := [7,31,1047552,2164802,8659208,17318416,32641156]
def z1472 : List Nat := [7,31,1047552,6494406,8659208,17318416,32505856]
def z1473 : List Nat := [7,31,1047552,8659208,9741609,17318416,32505856]
def z1474 : List Nat := [7,31,1047552,8659208,17318416,18400817,32505856]
def z1475 : List Nat := [7,31,1047552,8659208,17318416,32472030,32505856]
def z1476 : List Nat := [7,31,1047552,8659208,17318416,32505856,32539681]
def z1477 : List Nat := [7,31,1047583,1082401,8659208,17318416,32505856]
def z1478 : List Nat := [7,31,1048575,1082401,1083361,8659208,17318416]
def z1479 : List Nat := [7,31,1048575,1082401,2164802,4329604,8659944]
def z1480 : List Nat := [7,31,1048575,1082401,8659208,8659944,17318416]
def z1481 : List Nat := [7,31,1048575,1082401,8659208,17318416,32506848]
def z1482 : List Nat := [7,31,1048575,1082401,8659208,17318416,33553439]
def z1483 : List Nat := [7,31,1048575,1083361,2164802,4329604,8659208]
def z1484 : List Nat := [7,31,1048575,1083361,2164802,4329604,17318416]
def z1485 : List Nat := [7,31,1048575,2164802,4329604,8659944,17318416]
def z1486 : List Nat := [7,31,1048576,1082401,8659208,17318416,32506848]
def z1487 : List Nat := [7,31,1048576,2164802,4329604,17318416,32506848]
def z1488 : List Nat := [7,31,1049568,1082401,8659208,17318416,32505856]
def z1489 : List Nat := [7,31,1049568,2164802,4329604,17318416,32505856]
def z1490 : List Nat := [7,31,1082401,1083361,2164802,4329604,32776456]
def z1491 : List Nat := [7,31,1082401,1083361,6494406,8659208,32505856]
def z1492 : List Nat := [7,31,1082401,1083361,6494406,17318416,32505856]
def z1493 : List Nat := [7,31,1082401,1083361,8659208,16236015,32505856]
def z1494 : List Nat := [7,31,1082401,1083361,8659208,17318416,32505856]
def z1495 : List Nat := [7,31,1082401,1083361,8659208,17318416,32505887]
def z1496 : List Nat := [7,31,1082401,1083361,8659208,17318416,32776456]
def z1497 : List Nat := [7,31,1082401,1083361,8659208,18400817,32505856]
def z1498 : List Nat := [7,31,1082401,1083361,8659208,25977624,32505856]
def z1499 : List Nat := [7,31,1082401,1083361,8682760,17318416,32505856]
def z1500 : List Nat := [7,31,1082401,1083361,9741609,17318416,32505856]
def z1501 : List Nat := [7,31,1082401,1083361,17318416,24895223,32505856]
def z1502 : List Nat := [7,31,1082401,1083361,17318416,25977624,32505856]
def z1503 : List Nat := [7,31,1082401,1083391,8659208,17318416,32505856]
def z1504 : List Nat := [7,31,1082401,1113121,9412872,17318416,32505856]
def z1505 : List Nat := [7,31,1082401,2096161,8659208,17318416,32505856]
def z1506 : List Nat := [7,31,1082401,2098144,8659208,17318416,32505856]
def z1507 : List Nat := [7,31,1082401,2164802,4329604,8659944,32505856]
def z1508 : List Nat := [7,31,1082401,2164802,4329604,8659944,32505887]
def z1509 : List Nat := [7,31,1082401,2164802,4329604,8659944,32506848]
def z1510 : List Nat := [7,31,1082401,2164802,4329604,8659944,32776456]
def z1511 : List Nat := [7,31,1082401,2164802,4329604,8659944,32777192]
def z1512 : List Nat := [7,31,1082401,2164802,4329604,8659967,32505856]
def z1513 : List Nat := [7,31,1082401,2164802,4329604,9742313,32505856]
def z1514 : List Nat := [7,31,1082401,2164802,4329604,17318896,32506848]
def z1515 : List Nat := [7,31,1082401,2164802,4329604,24894487,32505856]
def z1516 : List Nat := [7,31,1082401,2164802,4329604,32505856,32777192]
def z1517 : List Nat := [7,31,1082401,2164802,4329604,32506848,32776456]
def z1518 : List Nat := [7,31,1082401,2164802,4329604,32506848,33047056]
def z1519 : List Nat := [7,31,1082401,2164802,4329604,32776456,32777192]
def z1520 : List Nat := [7,31,1082401,2164802,4329604,32776456,33553439]
def z1521 : List Nat := [7,31,1082401,2164802,5412005,8659944,32505856]
def z1522 : List Nat := [7,31,1082401,2164802,6494406,8659944,32505856]
def z1523 : List Nat := [7,31,1082401,2164802,8659944,17318416,32776456]
def z1524 : List Nat := [7,31,1082401,2164802,8659944,25977624,32505856]
def z1525 : List Nat := [7,31,1082401,2164802,8659944,29224827,32505856]
def z1526 : List Nat := [7,31,1082401,2164802,9436424,17318416,32505856]
def z1527 : List Nat := [7,31,1082401,2165730,8659208,17318416,32506848]
def z1528 : List Nat := [7,31,1082401,6494406,8659208,8659944,32505856]
def z1529 : List Nat := [7,31,1082401,6494406,8659208,32505856,32506848]
def z1530 : List Nat := [7,31,1082401,6494406,8659208,32505856,33553439]
def z1531 : List Nat := [7,31,1082401,6494406,8659944,17318416,32505856]
def z1532 : List Nat := [7,31,1082401,6494406,8659944,32505856]
def z1533 : List Nat := [7,31,1082401,6494406,17318416,32505856,32506848]
def z1534 : List Nat := [7,31,1082401,6494406,17318416,32505856,33553439]
def z1535 : List Nat := [7,31,1082401,8389600,8659208,17318416,32505856]
def z1536 : List Nat := [7,31,1082401,8659208,8659944,16236015,32505856]
def z1537 : List Nat := [7,31,1082401,8659208,8659944,17318416,32505856]
def z1538 : List Nat := [7,31,1082401,8659208,8659944,17318416,32505887]
def z1539 : List Nat := [7,31,1082401,8659208,8659944,17318416,32506848]
def z1540 : List Nat := [7,31,1082401,8659208,8659944,17318416,32776456]
def z1541 : List Nat := [7,31,1082401,8659208,8659944,17318416,32777192]
def z1542 : List Nat := [7,31,1082401,8659208,8659944,18400817,32505856]
def z1543 : List Nat := [7,31,1082401,8659208,8659944,25977624,32505856]
def z1544 : List Nat := [7,31,1082401,8659208,8659967,17318416,32505856]
def z1545 : List Nat := [7,31,1082401,8659208,9436424,17318416,32505856]
def z1546 : List Nat := [7,31,1082401,8659208,9742313,17318416,32505856]
def z1547 : List Nat := [7,31,1082401,8659208,16236015,32505856,32506848]
def z1548 : List Nat := [7,31,1082401,8659208,16236015,32505856,33553439]
def z1549 : List Nat := [7,31,1082401,8659208,16778208,17318416,32505856]
def z1550 : List Nat := [7,31,1082401,8659208,17318416,17318896,32506848]
def z1551 : List Nat := [7,31,1082401,8659208,17318416,24894487,32505856]
def z1552 : List Nat := [7,31,1082401,8659208,17318416,32471070,32505856]
def z1553 : List Nat := [7,31,1082401,8659208,17318416,32505856,32506848]
def z1554 : List Nat := [7,31,1082401,8659208,17318416,32505856,32506879]
def z1555 : List Nat := [7,31,1082401,8659208,17318416,32505856,32540641]
def z1556 : List Nat := [7,31,1082401,8659208,17318416,32505856,32777192]
def z1557 : List Nat := [7,31,1082401,8659208,17318416,32505856,33553408]
def z1558 : List Nat := [7,31,1082401,8659208,17318416,32505856,33553439]
def z1559 : List Nat := [7,31,1082401,8659208,17318416,32505856,33553471]
def z1560 : List Nat := [7,31,1082401,8659208,17318416,32505856,33553695]
def z1561 : List Nat := [7,31,1082401,8659208,17318416,32505887,32506848]
def z1562 : List Nat := [7,31,1082401,8659208,17318416,32505887,32506879]
def z1563 : List Nat := [7,31,1082401,8659208,17318416,32505887,33553439]
def z1564 : List Nat := [7,31,1082401,8659208,17318416,32506848,32537600]
def z1565 : List Nat := [7,31,1082401,8659208,17318416,32506848,32573506]
def z1566 : List Nat := [7,31,1082401,8659208,17318416,32506848,32776456]
def z1567 : List Nat := [7,31,1082401,8659208,17318416,32506848,33047056]
def z1568 : List Nat := [7,31,1082401,8659208,17318416,32506848,33553439]
def z1569 : List Nat := [7,31,1082401,8659208,17318416,32537600,33521664]
def z1570 : List Nat := [7,31,1082401,8659208,17318416,32776456,32777192]
def z1571 : List Nat := [7,31,1082401,8659208,17318416,32776456,33553439]
def z1572 : List Nat := [7,31,1082401,8659208,18400817,32505856,32506848]
def z1573 : List Nat := [7,31,1082401,8659208,18400817,32505856,33553439]
def z1574 : List Nat := [7,31,1082401,8659208,25977624,32505856,32506848]
def z1575 : List Nat := [7,31,1082401,8659208,25977624,32505856,33553439]
def z1576 : List Nat := [7,31,1082401,8659231,8659944,17318416,32505856]
def z1577 : List Nat := [7,31,1082401,8659944,8682760,17318416,32505856]
def z1578 : List Nat := [7,31,1082401,8659944,9741609,17318416,32505856]
def z1579 : List Nat := [7,31,1082401,8659944,17318416,24895223,32505856]
def z1580 : List Nat := [7,31,1082401,8659944,17318416,25977624,32505856]
def z1581 : List Nat := [7,31,1082401,8659944,17318416,32505856,32776456]
def z1582 : List Nat := [7,31,1082401,8659944,17318416,32776456]
def z1583 : List Nat := [7,31,1082401,8659944,25977624,32505856]
def z1584 : List Nat := [7,31,1082401,8682760,8683496,17318416,32505856]
def z1585 : List Nat := [7,31,1082401,8682760,9412872,17318416,32505856]
def z1586 : List Nat := [7,31,1082401,8682760,9436424,17318416,32505856]
def z1587 : List Nat := [7,31,1082401,8682760,17318416,32505856,32506848]
def z1588 : List Nat := [7,31,1082401,8682760,17318416,32505856,32538623]
def z1589 : List Nat := [7,31,1082401,8682760,17318416,32505856,33521664]
def z1590 : List Nat := [7,31,1082401,8682760,17318416,32505856,33553439]
def z1591 : List Nat := [7,31,1082401,9436424,17318416,32505856]
def z1592 : List Nat := [7,31,1082401,9741609,9742313,17318416,32505856]
def z1593 : List Nat := [7,31,1082401,9741609,17318416,32505856,32506848]
def z1594 : List Nat := [7,31,1082401,9741609,17318416,32505856,33553439]
def z1595 : List Nat := [7,31,1082401,17318416,24895223,32505856,32506848]
def z1596 : List Nat := [7,31,1082401,17318416,24895223,32505856,33553439]
def z1597 : List Nat := [7,31,1082401,17318416,25977624,32505856,32506848]
def z1598 : List Nat := [7,31,1082401,17318416,25977624,32505856,33553439]
def z1599 : List Nat := [7,31,1082431,1083361,8659208,17318416,32505856]
def z1600 : List Nat := [7,31,1082431,2164802,4329604,8659944,32505856]
def z1601 : List Nat := [7,31,1083361,1113121,8659208,17318416,32505856]
def z1602 : List Nat := [7,31,1083361,2164802,4329604,8659208,32505856]
def z1603 : List Nat := [7,31,1083361,2164802,4329604,8659208,32505887]
def z1604 : List Nat := [7,31,1083361,2164802,4329604,8659208,32776456]
def z1605 : List Nat := [7,31,1083361,2164802,4329604,8659231,32505856]
def z1606 : List Nat := [7,31,1083361,2164802,4329604,8659944,32505856]
def z1607 : List Nat := [7,31,1083361,2164802,4329604,9741609,32505856]
def z1608 : List Nat := [7,31,1083361,2164802,4329604,9742313,32505856]
def z1609 : List Nat := [7,31,1083361,2164802,4329604,10824010,32505856]
def z1610 : List Nat := [7,31,1083361,2164802,4329604,16236015,32505856]
def z1611 : List Nat := [7,31,1083361,2164802,4329604,17318416,32505856]
def z1612 : List Nat := [7,31,1083361,2164802,4329604,17318416,32505887]
def z1613 : List Nat := [7,31,1083361,2164802,4329604,17318431,32505856]
def z1614 : List Nat := [7,31,1083361,2164802,4329604,17318896,32505856]
def z1615 : List Nat := [7,31,1083361,2164802,4329604,18400817,32505856]
def z1616 : List Nat := [7,31,1083361,2164802,4329604,18401265,32505856]
def z1617 : List Nat := [7,31,1083361,2164802,4329604,19483218,32505856]
def z1618 : List Nat := [7,31,1083361,2164802,4329604,24895223,32505856]
def z1619 : List Nat := [7,31,1083361,2164802,4329604,32505856,32776456]
def z1620 : List Nat := [7,31,1083361,2164802,4329604,32505856,33047056]
def z1621 : List Nat := [7,31,1083361,2164802,6494406,8659208,32505856]
def z1622 : List Nat := [7,31,1083361,2164802,6494406,17318416,32505856]
def z1623 : List Nat := [7,31,1083361,2164802,8659208,12988812,32505856]
def z1624 : List Nat := [7,31,1083361,2164802,8659208,18400817,32505856]
def z1625 : List Nat := [7,31,1083361,2164802,8659208,29224827,32505856]
def z1626 : List Nat := [7,31,1083361,2164802,9741609,17318416,32505856]
def z1627 : List Nat := [7,31,1083361,2164802,17318416,21648020,32505856]
def z1628 : List Nat := [7,31,1083361,2164802,17318416,29224827,32505856]
def z1629 : List Nat := [7,31,1083361,6494406,8659208,17318416,32505856]
def z1630 : List Nat := [7,31,1083361,6494406,8659208,32505856]
def z1631 : List Nat := [7,31,1083361,6494406,17318416,32505856]
def z1632 : List Nat := [7,31,1083361,8659208,9741609,17318416,32505856]
def z1633 : List Nat := [7,31,1083361,8659208,17318416,18400817,32505856]
def z1634 : List Nat := [7,31,1083361,8659208,17318416,32472030,32505856]
def z1635 : List Nat := [7,31,1083361,8659208,17318416,32505856,32539681]
def z1636 : List Nat := [7,31,1083361,8659208,18400817,32505856]
def z1637 : List Nat := [7,31,1083361,9741609,17318416,32505856]
def z1638 : List Nat := [7,31,1083391,2164802,4329604,8659208,32505856]
def z1639 : List Nat := [7,31,1083391,2164802,4329604,17318416,32505856]
def z1640 : List Nat := [7,31,1113121,1114081,8659208,17318416,32505856]
def z1641 : List Nat := [7,31,1113121,2065441,8659208,17318416,32505856]
def z1642 : List Nat := [7,31,1113121,2096161,8659208,17318416,32505856]
def z1643 : List Nat := [7,31,1113121,2164802,9412872,17318416,32505856]
def z1644 : List Nat := [7,31,1113121,8659208,8659944,17318416,32505856]
def z1645 : List Nat := [7,31,1113121,8659208,9412872,17318416,32505856]
def z1646 : List Nat := [7,31,1113121,8659208,17318416,32505856,32506848]
def z1647 : List Nat := [7,31,1113121,8659208,17318416,32505856,32538623]
def z1648 : List Nat := [7,31,1113121,8659208,17318416,32505856,33521664]
def z1649 : List Nat := [7,31,1113121,8659208,17318416,32505856,33553439]
def z1650 : List Nat := [7,31,1113121,9412872,17318416,32505856]
def z1651 : List Nat := [7,31,2096161,2164802,4329604,17318416,32505856]
def z1652 : List Nat := [7,31,2096161,2164802,8659208,17318416,32505856]
def z1653 : List Nat := [7,31,2096161,8659208,17318416,32505856]
def z1654 : List Nat := [7,31,2164802,3247203,4329604,8659944,32505856]
def z1655 : List Nat := [7,31,2164802,4329604,8389600,17318416,32505856]
def z1656 : List Nat := [7,31,2164802,4329604,8659208,9742313,32505856]
def z1657 : List Nat := [7,31,2164802,4329604,8659208,17318896,32506848]
def z1658 : List Nat := [7,31,2164802,4329604,8659208,32471070,32505856]
def z1659 : List Nat := [7,31,2164802,4329604,8659944,9741609,32505856]
def z1660 : List Nat := [7,31,2164802,4329604,8659944,9742313,32505856]
def z1661 : List Nat := [7,31,2164802,4329604,8659944,16236015,32505856]
def z1662 : List Nat := [7,31,2164802,4329604,8659944,17318416,32505856]
def z1663 : List Nat := [7,31,2164802,4329604,8659944,17318416,32505887]
def z1664 : List Nat := [7,31,2164802,4329604,8659944,17318416,32506848]
def z1665 : List Nat := [7,31,2164802,4329604,8659944,17318416,32776456]
def z1666 : List Nat := [7,31,2164802,4329604,8659944,17318416,32777192]
def z1667 : List Nat := [7,31,2164802,4329604,8659944,17318431,32505856]
def z1668 : List Nat := [7,31,2164802,4329604,8659944,17318896,32505856]
def z1669 : List Nat := [7,31,2164802,4329604,8659944,19483218,32505856]
def z1670 : List Nat := [7,31,2164802,4329604,8659944,25977624,32505856]
def z1671 : List Nat := [7,31,2164802,4329604,8659944,25977848,32505856]
def z1672 : List Nat := [7,31,2164802,4329604,8659944,32472030,32505856]
def z1673 : List Nat := [7,31,2164802,4329604,8659967,17318416,32505856]
def z1674 : List Nat := [7,31,2164802,4329604,9436424,17318416,32505856]
def z1675 : List Nat := [7,31,2164802,4329604,17318416,24894487,32505856]
def z1676 : List Nat := [7,31,2164802,4329604,17318416,32471070,32505856]
def z1677 : List Nat := [7,31,2164802,6494406,8659944,17318416,32505856]
def z1678 : List Nat := [7,31,2164802,8659208,17318416,32506848,32641156]
def z1679 : List Nat := [7,31,2164802,8659944,9741609,17318416,32505856]
def z1680 : List Nat := [7,31,2164802,8659944,17318416,21648020,32505856]
def z1681 : List Nat := [7,31,2164802,8659944,17318416,29224827,32505856]
def z1682 : List Nat := [7,31,2164802,8659944,17318416,32505856,32641156]
def z1683 : List Nat := [7,31,6494406,8659208,8659944,17318416,32505856]
def z1684 : List Nat := [7,31,6494406,8659208,17318416,32505856,32506848]
def z1685 : List Nat := [7,31,6494406,8659208,17318416,32505856,33553439]
def z1686 : List Nat := [7,31,6494406,8659944,17318416,32505856]
def z1687 : List Nat := [7,31,8659208,8659944,9741609,17318416,32505856]
def z1688 : List Nat := [7,31,8659208,8659944,17318416,18400817,32505856]
def z1689 : List Nat := [7,31,8659208,8659944,17318416,32472030,32505856]
def z1690 : List Nat := [7,31,8659208,8659944,17318416,32505856,32539681]
def z1691 : List Nat := [7,31,8659208,9741609,9742313,17318416,32505856]
def z1692 : List Nat := [7,31,8659208,9741609,17318416,32505856,32506848]
def z1693 : List Nat := [7,31,8659208,9741609,17318416,32505856,33553439]
def z1694 : List Nat := [7,31,8659208,17318416,18400817,32505856,32506848]
def z1695 : List Nat := [7,31,8659208,17318416,18400817,32505856,33553439]
def z1696 : List Nat := [7,31,8659208,17318416,32472030,32505856,32506848]
def z1697 : List Nat := [7,31,8659208,17318416,32472030,32505856,33553439]
def z1698 : List Nat := [7,31,8659208,17318416,32505856,32506848,32539681]
def z1699 : List Nat := [7,31,8659208,17318416,32505856,32539681,32540641]
def z1700 : List Nat := [7,31,8659208,17318416,32505856,32539681,33553439]
def z1701 : List Nat := [7,31,8659944,9741609,17318416,32505856]
def z1702 : List Nat := [7,33,992,1023,8659208,17318416,32505856]
def z1703 : List Nat := [7,63,992,1082401,8659208,17318416,32505856]
def z1704 : List Nat := [7,95,992,1082401,8659208,17318416,32505856]
def z1705 : List Nat := [7,287,992,1082401,8659208,17318416,32505856]
def z1706 : List Nat := [7,543,992,1082401,8659208,17318416,32505856]
def z1707 : List Nat := [7,992,1023,31744,1082401,9412872,17318416]
def z1708 : List Nat := [7,992,1023,1047552,1082401,8659208,17318416]
def z1709 : List Nat := [7,992,1023,1048575,1082401,8659208,17318416]
def z1710 : List Nat := [7,992,1023,1082401,2164802,4329604,32776456]
def z1711 : List Nat := [7,992,1023,1082401,6494406,8659208,32505856]
def z1712 : List Nat := [7,992,1023,1082401,6494406,17318416,32505856]
def z1713 : List Nat := [7,992,1023,1082401,8659208,16236015,32505856]
def z1714 : List Nat := [7,992,1023,1082401,8659208,17318416,32505856]
def z1715 : List Nat := [7,992,1023,1082401,8659208,17318416,32505887]
def z1716 : List Nat := [7,992,1023,1082401,8659208,17318416,32506848]
def z1717 : List Nat := [7,992,1023,1082401,8659208,17318416,32506879]
def z1718 : List Nat := [7,992,1023,1082401,8659208,17318416,32776456]
def z1719 : List Nat := [7,992,1023,1082401,8659208,18400817,32505856]
def z1720 : List Nat := [7,992,1023,1082401,8659208,25977624,32505856]
def z1721 : List Nat := [7,992,1023,1082401,8682760,17318416,32505856]
def z1722 : List Nat := [7,992,1023,1082401,9741609,17318416,32505856]
def z1723 : List Nat := [7,992,1023,1082401,17318416,24895223,32505856]
def z1724 : List Nat := [7,992,1023,1082401,17318416,25977624,32505856]
def z1725 : List Nat := [7,992,1023,1113121,8659208,17318416,32505856]
def z1726 : List Nat := [7,992,1023,6494406,8659208,17318416,32505856]
def z1727 : List Nat := [7,992,1023,8659208,9741609,17318416,32505856]
def z1728 : List Nat := [7,992,1023,8659208,17318416,18400817,32505856]
def z1729 : List Nat := [7,992,1023,8659208,17318416,32472030,32505856]
def z1730 : List Nat := [7,992,1023,8659208,17318416,32505856,32539681]
def z1731 : List Nat := [7,992,2079,1082401,8659208,17318416,32505856]
def z1732 : List Nat := [7,992,16415,1082401,8659208,17318416,32505856]
def z1733 : List Nat := [7,992,31744,31775,1082401,9412872,17318416]
def z1734 : List Nat := [7,992,31744,1014750,1015808,8659208,17318416]
def z1735 : List Nat := [7,992,31744,1015808,1082401,2164802,4329631,8659208,33047056]
def z1736 : List Nat := [7,992,31744,1015808,1082401,2164802,4329631,17318416,32776456]
def z1737 : List Nat := [7,992,31744,1015808,1082401,6494431,8659208,17318416,32505856]
def z1738 : List Nat := [7,992,31744,1015808,1082431,6494406,8659208]
def z1739 : List Nat := [7,992,31744,1015808,1082431,6494406,17318416]
def z1740 : List Nat := [7,992,31744,1015808,1082431,8659208,18400817]
def z1741 : List Nat := [7,992,31744,1015808,1082431,9741609,17318416]
def z1742 : List Nat := [7,992,31744,1015808,8659208,16236015,32539681]
def z1743 : List Nat := [7,992,31744,1015808,8659208,17318416,32539681]
def z1744 : List Nat := [7,992,31744,1015808,8659208,17318416,32570401]
def z1745 : List Nat := [7,992,31744,1015808,8659208,25977624,32539681]
def z1746 : List Nat := [7,992,31744,1015808,8682760,17318416,32539681]
def z1747 : List Nat := [7,992,31744,1015808,9741609,18400817,32505856]
def z1748 : List Nat := [7,992,31744,1015808,9741609,25977624,32505856]
def z1749 : List Nat := [7,992,31744,1015808,17318416,24895223,32539681]
def z1750 : List Nat := [7,992,31744,1015808,17318416,25977624,32539681]
def z1751 : List Nat := [7,992,31744,1015808,18400817,25977624,32505856]
def z1752 : List Nat := [7,992,31744,1016800,8659208,17318416,32539681]
def z1753 : List Nat := [7,992,31744,1047552,8659208,17318416,32539681]
def z1754 : List Nat := [7,992,31744,1082401,1082431,9412872,17318416]
def z1755 : List Nat := [7,992,31744,1082401,2164831,5214340,8659208,17318416,32505856]
def z1756 : List Nat := [7,992,31744,1082401,6494406,17318431,32505856]
def z1757 : List Nat := [7,992,31744,1082401,7313606,17318416,32505856]
def z1758 : List Nat := [7,992,31744,1082401,9412872,17318416,33521664]
def z1759 : List Nat := [7,992,31744,1082401,9412872,17318416,33554400]
def z1760 : List Nat := [7,992,31744,1082401,17318431,25977624,32505856]
def z1761 : List Nat := [7,992,31744,2065441,9412872,17318416,32505856]
def z1762 : List Nat := [7,992,31744,6494406,8659208,17318431,32505856]
def z1763 : List Nat := [7,992,31744,7313606,8659208,17318416,32505856]
def z1764 : List Nat := [7,992,31744,8659208,17318416,17809936,32539681]
def z1765 : List Nat := [7,992,31744,8659208,17318416,32505887,32539681]
def z1766 : List Nat := [7,992,31744,8659208,17318416,32538623,32539681]
def z1767 : List Nat := [7,992,31744,8659208,17318431,18400817,32505856]
def z1768 : List Nat := [7,992,31775,1015839,1082401,8659208,17318416]
def z1769 : List Nat := [7,992,31775,1047552,1082401,8659208,17318416]
def z1770 : List Nat := [7,992,31775,1082401,8659208,17318416,32505887]
def z1771 : List Nat := [7,992,31775,1082401,8659208,17318416,32537600]
def z1772 : List Nat := [7,992,1047552,1047583,1082401,8659208,17318416]
def z1773 : List Nat := [7,992,1047552,1048575,1082401,8659208,17318416]
def z1774 : List Nat := [7,992,1047552,1082401,1082431,8659208,17318416]
def z1775 : List Nat := [7,992,1047552,1082401,2164802,4329631,8659208,17318416,32505856]
def z1776 : List Nat := [7,992,1047552,1082401,6494406,8659208,32505856]
def z1777 : List Nat := [7,992,1047552,1082401,6494406,17318416,32505856]
def z1778 : List Nat := [7,992,1047552,1082401,8659208,16236015,32505856]
def z1779 : List Nat := [7,992,1047552,1082401,8659208,17318416,32505856]
def z1780 : List Nat := [7,992,1047552,1082401,8659208,17318416,32506848]
def z1781 : List Nat := [7,992,1047552,1082401,8659208,17318416,32537600]
def z1782 : List Nat := [7,992,1047552,1082401,8659208,17318416,32539681]
def z1783 : List Nat := [7,992,1047552,1082401,8659208,17318416,33553408]
def z1784 : List Nat := [7,992,1047552,1082401,8659208,17318416,33554400]
def z1785 : List Nat := [7,992,1047552,1082401,8659208,18400817,32505856]
def z1786 : List Nat := [7,992,1047552,1082401,8659208,25977624,32505856]
def z1787 : List Nat := [7,992,1047552,1082401,8682760,17318416,32505856]
def z1788 : List Nat := [7,992,1047552,1082401,9436424,17318416,32505856]
def z1789 : List Nat := [7,992,1047552,1082401,9741609,17318416,32505856]
def z1790 : List Nat := [7,992,1047552,1082401,17318416,24895223,32505856]
def z1791 : List Nat := [7,992,1047552,1082401,17318416,25977624,32505856]
def z1792 : List Nat := [7,992,1047552,1082431,2164802,4329604,8659208]
def z1793 : List Nat := [7,992,1047552,1082431,2164802,4329604,17318416]
def z1794 : List Nat := [7,992,1047552,1113121,8659208,17318416,32505856]
def z1795 : List Nat := [7,992,1047552,2096161,8659208,17318416,32505856]
def z1796 : List Nat := [7,992,1047552,2164802,8659208,17318416,32539681]
def z1797 : List Nat := [7,992,1047552,6494406,8659208,17318416,32505856]
def z1798 : List Nat := [7,992,1047552,8659208,9741609,17318416,32505856]
def z1799 : List Nat := [7,992,1047552,8659208,17318416,18400817,32505856]
def z1800 : List Nat := [7,992,1047552,8659208,17318416,32472030,32505856]
def z1801 : List Nat := [7,992,1047552,8659208,17318416,32505856,32539681]
def z1802 : List Nat := [7,992,1047552,8659208,17318416,32539681]
def z1803 : List Nat := [7,992,1048544,1082401,8659208,17318416,32505856]
def z1804 : List Nat := [7,992,1048575,1082401,2164802,4329604,17318431]
def z1805 : List Nat := [7,992,1048575,1082401,2164831,8659208,17318416]
def z1806 : List Nat := [7,992,1048575,1082401,8659208,17318416,17318431]
def z1807 : List Nat := [7,992,1048575,1082401,8659208,17318416,32505887]
def z1808 : List Nat := [7,992,1048575,1082401,8659208,17318416,33554400]
def z1809 : List Nat := [7,992,1048575,2164802,4329604,8659208,17318431]
def z1810 : List Nat := [7,992,1048576,2164802,4329604,17318431,32505856]
def z1811 : List Nat := [7,992,1048607,1082401,8659208,17318416,32505856]
def z1812 : List Nat := [7,992,1048607,2164802,4329604,17318416,32505856]
def z1813 : List Nat := [7,992,1082401,1082431,8659208,17318416,32505887]
def z1814 : List Nat := [7,992,1082401,2097183,8659208,17318416,32505856]
def z1815 : List Nat := [7,992,1082401,2164802,2164831,4329604,32776456]
def z1816 : List Nat := [7,992,1082401,2164802,4329604,16236000,32505856]
def z1817 : List Nat := [7,992,1082401,2164802,4329604,17318431,32505856]
def z1818 : List Nat := [7,992,1082401,2164802,4329604,17318431,32506848]
def z1819 : List Nat := [7,992,1082401,2164802,4329604,17318911,32505856]
def z1820 : List Nat := [7,992,1082401,2164802,4329604,19483231,32505856]
def z1821 : List Nat := [7,992,1082401,2164802,4329604,32505856,33047071]
def z1822 : List Nat := [7,992,1082401,2164802,4329604,32776456,33554400]
def z1823 : List Nat := [7,992,1082401,2164802,4329631,17318416,32776456]
def z1824 : List Nat := [7,992,1082401,2164802,5241988,17318416,32505856]
def z1825 : List Nat := [7,992,1082401,2164802,5412005,17318431,32505856]
def z1826 : List Nat := [7,992,1082401,2164802,6494406,17318431,32505856]
def z1827 : List Nat := [7,992,1082401,2164802,17318431,25977624,32505856]
def z1828 : List Nat := [7,992,1082401,2164802,17318431,29224827,32505856]
def z1829 : List Nat := [7,992,1082401,2164831,6494406,8659208,32505856]
def z1830 : List Nat := [7,992,1082401,2164831,6494406,17318416,32505856]
def z1831 : List Nat := [7,992,1082401,2164831,8659208,16236015,32505856]
def z1832 : List Nat := [7,992,1082401,2164831,8659208,17318416,32505856]
def z1833 : List Nat := [7,992,1082401,2164831,8659208,17318416,32506848]
def z1834 : List Nat := [7,992,1082401,2164831,8659208,17318416,32776456]
def z1835 : List Nat := [7,992,1082401,2164831,8659208,18400817,32505856]
def z1836 : List Nat := [7,992,1082401,2164831,8659208,25977624,32505856]
def z1837 : List Nat := [7,992,1082401,2164831,9741609,17318416,32505856]
def z1838 : List Nat := [7,992,1082401,2164831,17318416,24895223,32505856]
def z1839 : List Nat := [7,992,1082401,2164831,17318416,25977624,32505856]
def z1840 : List Nat := [7,992,1082401,2165759,8659208,17318416,32505856]
def z1841 : List Nat := [7,992,1082401,2194498,5214340,17318416,32505856]
def z1842 : List Nat := [7,992,1082401,3144770,8659208,17318416,32505856]
def z1843 : List Nat := [7,992,1082401,6494406,6494431,8659208,32505856]
def z1844 : List Nat := [7,992,1082401,6494406,6494431,17318416,32505856]
def z1845 : List Nat := [7,992,1082401,6494406,8659208,17318431,32505856]
def z1846 : List Nat := [7,992,1082401,6494406,8659208,32505856,32505887]
def z1847 : List Nat := [7,992,1082401,6494406,8659208,32505856,33554400]
def z1848 : List Nat := [7,992,1082401,6494406,17318416,17318431,32505856]
def z1849 : List Nat := [7,992,1082401,6494406,17318416,32505856,32505887]
def z1850 : List Nat := [7,992,1082401,6494406,17318416,32505856,33554400]
def z1851 : List Nat := [7,992,1082401,6494406,17318431,32505856]
def z1852 : List Nat := [7,992,1082401,6494431,8659208,17318416,32505856]
def z1853 : List Nat := [7,992,1082401,8388639,8659208,17318416,32505856]
def z1854 : List Nat := [7,992,1082401,8659208,16236000,17318416,32505856]
def z1855 : List Nat := [7,992,1082401,8659208,16236015,17318431,32505856]
def z1856 : List Nat := [7,992,1082401,8659208,16236015,32505856,32505887]
def z1857 : List Nat := [7,992,1082401,8659208,16236015,32505856,33554400]
def z1858 : List Nat := [7,992,1082401,8659208,16777247,17318416,32505856]
def z1859 : List Nat := [7,992,1082401,8659208,17318416,17318431,32505856]
def z1860 : List Nat := [7,992,1082401,8659208,17318416,17318431,32506848]
def z1861 : List Nat := [7,992,1082401,8659208,17318416,17318431,32776456]
def z1862 : List Nat := [7,992,1082401,8659208,17318416,17318911,32505856]
def z1863 : List Nat := [7,992,1082401,8659208,17318416,17825296,32505856]
def z1864 : List Nat := [7,992,1082401,8659208,17318416,19483231,32505856]
def z1865 : List Nat := [7,992,1082401,8659208,17318416,29224800,32505856]
def z1866 : List Nat := [7,992,1082401,8659208,17318416,32505856,32505887]
def z1867 : List Nat := [7,992,1082401,8659208,17318416,32505856,32506879]
def z1868 : List Nat := [7,992,1082401,8659208,17318416,32505856,32573535]
def z1869 : List Nat := [7,992,1082401,8659208,17318416,32505856,33047071]
def z1870 : List Nat := [7,992,1082401,8659208,17318416,32505856,33553408]
def z1871 : List Nat := [7,992,1082401,8659208,17318416,32505856,33554400]
def z1872 : List Nat := [7,992,1082401,8659208,17318416,32505856,33554402]
def z1873 : List Nat := [7,992,1082401,8659208,17318416,32505856,33554416]
def z1874 : List Nat := [7,992,1082401,8659208,17318416,32505887,32506848]
def z1875 : List Nat := [7,992,1082401,8659208,17318416,32505887,32537600]
def z1876 : List Nat := [7,992,1082401,8659208,17318416,32505887,32539681]
def z1877 : List Nat := [7,992,1082401,8659208,17318416,32505887,33554400]
def z1878 : List Nat := [7,992,1082401,8659208,17318416,32506848,32506879]
def z1879 : List Nat := [7,992,1082401,8659208,17318416,32506848,33554400]
def z1880 : List Nat := [7,992,1082401,8659208,17318416,32537600,33521664]
def z1881 : List Nat := [7,992,1082401,8659208,17318416,32776456,33554400]
def z1882 : List Nat := [7,992,1082401,8659208,17318431,17318896,32505856]
def z1883 : List Nat := [7,992,1082401,8659208,17318431,17333776,32505856]
def z1884 : List Nat := [7,992,1082401,8659208,17318431,18400817,32505856]
def z1885 : List Nat := [7,992,1082401,8659208,17318431,25977624,32505856]
def z1886 : List Nat := [7,992,1082401,8659208,17318431,32505856,33047056]
def z1887 : List Nat := [7,992,1082401,8659208,17333776,17809936,32505856]
def z1888 : List Nat := [7,992,1082401,8659208,18400817,32505856,32505887]
def z1889 : List Nat := [7,992,1082401,8659208,18400817,32505856,33554400]
def z1890 : List Nat := [7,992,1082401,8659208,25977624,32505856,32505887]
def z1891 : List Nat := [7,992,1082401,8659208,25977624,32505856,33554400]
def z1892 : List Nat := [7,992,1082401,8682760,17318416,17318431,32505856]
def z1893 : List Nat := [7,992,1082401,8682760,17318416,32505856,32505887]
def z1894 : List Nat := [7,992,1082401,8682760,17318416,32505856,33554400]
def z1895 : List Nat := [7,992,1082401,9741609,17318416,17318431,32505856]
def z1896 : List Nat := [7,992,1082401,9741609,17318416,32505856,32505887]
def z1897 : List Nat := [7,992,1082401,9741609,17318416,32505856,33554400]
def z1898 : List Nat := [7,992,1082401,17318416,17318431,24895223,32505856]
def z1899 : List Nat := [7,992,1082401,17318416,17318431,25977624,32505856]
def z1900 : List Nat := [7,992,1082401,17318416,24895223,32505856,32505887]
def z1901 : List Nat := [7,992,1082401,17318416,24895223,32505856,33554400]
def z1902 : List Nat := [7,992,1082401,17318416,25977624,32505856,32505887]
def z1903 : List Nat := [7,992,1082401,17318416,25977624,32505856,33554400]
def z1904 : List Nat := [7,992,1082401,17318431,25977624,32505856]
def z1905 : List Nat := [7,992,1082431,2164802,4329604,8659208,32505887]
def z1906 : List Nat := [7,992,1082431,2164802,4329604,8659231,32505856]
def z1907 : List Nat := [7,992,1082431,2164802,4329604,17318416,32505887]
def z1908 : List Nat := [7,992,1082431,2164802,4329604,17318431,32505856]
def z1909 : List Nat := [7,992,1083361,2164802,4329604,17318431,32505856]
def z1910 : List Nat := [7,992,1113121,2164802,4329604,17318431,32505856]
def z1911 : List Nat := [7,992,1113121,8659208,17318416,17318431,32505856]
def z1912 : List Nat := [7,992,1113121,8659208,17318416,32505856,32505887]
def z1913 : List Nat := [7,992,1113121,8659208,17318416,32505856,33554400]
def z1914 : List Nat := [7,992,2164802,3247203,4329604,17318431,32505856]
def z1915 : List Nat := [7,992,2164802,4329604,8388608,17318431,32505856]
def z1916 : List Nat := [7,992,2164802,4329604,8388639,17318416,32505856]
def z1917 : List Nat := [7,992,2164802,4329604,8659208,16236000,32505856]
def z1918 : List Nat := [7,992,2164802,4329604,8659208,17318431,32505856]
def z1919 : List Nat := [7,992,2164802,4329604,8659208,17318431,32506848]
def z1920 : List Nat := [7,992,2164802,4329604,8659208,17318431,32776456]
def z1921 : List Nat := [7,992,2164802,4329604,8659208,17318911,32505856]
def z1922 : List Nat := [7,992,2164802,4329604,8659208,19483231,32505856]
def z1923 : List Nat := [7,992,2164802,4329604,8659231,17318431,32505856]
def z1924 : List Nat := [7,992,2164802,4329604,8659944,17318431,32505856]
def z1925 : List Nat := [7,992,2164802,4329604,8682760,17318431,32505856]
def z1926 : List Nat := [7,992,2164802,4329604,10824010,17318431,32505856]
def z1927 : List Nat := [7,992,2164802,4329604,17318431,18400817,32505856]
def z1928 : List Nat := [7,992,2164802,4329604,17318431,18400831,32505856]
def z1929 : List Nat := [7,992,2164802,4329604,17318431,24895223,32505856]
def z1930 : List Nat := [7,992,2164802,4329604,17318431,25977624,32505856]
def z1931 : List Nat := [7,992,2164802,4329604,17318431,25977631,32505856]
def z1932 : List Nat := [7,992,2164802,4329604,17318431,32472030,32505856]
def z1933 : List Nat := [7,992,2164802,5241988,8659208,17318416,32505856]
def z1934 : List Nat := [7,992,2164802,6494406,8659208,17318431,32505856]
def z1935 : List Nat := [7,992,2164802,8659208,12988812,17318431,32505856]
def z1936 : List Nat := [7,992,2164802,8659208,17318416,32505887,32539681]
def z1937 : List Nat := [7,992,2164802,8659208,17318431,18400817,32505856]
def z1938 : List Nat := [7,992,2164802,8659208,17318431,29224827,32505856]
def z1939 : List Nat := [7,992,2164802,8659208,17318431,32505856,32641156]
def z1940 : List Nat := [7,992,2164831,6494406,8659208,17318416,32505856]
def z1941 : List Nat := [7,992,2164831,8659208,9741609,17318416,32505856]
def z1942 : List Nat := [7,992,2164831,8659208,17318416,18400817,32505856]
def z1943 : List Nat := [7,992,2164831,8659208,17318416,32472030,32505856]
def z1944 : List Nat := [7,992,2164831,8659208,17318416,32505856,32539681]
def z1945 : List Nat := [7,992,2194498,5214340,8659208,17318416,32505856]
def z1946 : List Nat := [7,992,6494406,6494431,8659208,17318416,32505856]
def z1947 : List Nat := [7,992,6494406,8659208,17318416,17318431,32505856]
def z1948 : List Nat := [7,992,6494406,8659208,17318416,32505856,32505887]
def z1949 : List Nat := [7,992,6494406,8659208,17318416,32505856,33554400]
def z1950 : List Nat := [7,992,6494406,8659208,17318431,32505856]
def z1951 : List Nat := [7,992,8659208,9741609,17318416,17318431,32505856]
def z1952 : List Nat := [7,992,8659208,9741609,17318416,32505856,32505887]
def z1953 : List Nat := [7,992,8659208,9741609,17318416,32505856,33554400]
def z1954 : List Nat := [7,992,8659208,17318416,17318431,18400817,32505856]
def z1955 : List Nat := [7,992,8659208,17318416,17318431,32472030,32505856]
def z1956 : List Nat := [7,992,8659208,17318416,17318431,32505856,32539681]
def z1957 : List Nat := [7,992,8659208,17318416,18400817,32505856,32505887]
def z1958 : List Nat := [7,992,8659208,17318416,18400817,32505856,33554400]
def z1959 : List Nat := [7,992,8659208,17318416,32472030,32505856,32505887]
def z1960 : List Nat := [7,992,8659208,17318416,32472030,32505856,33554400]
def z1961 : List Nat := [7,992,8659208,17318416,32505856,32505887,32539681]
def z1962 : List Nat := [7,992,8659208,17318416,32505856,32539681,33554400]
def z1963 : List Nat := [7,992,8659208,17318416,32505887,32539681]
def z1964 : List Nat := [7,992,8659208,17318431,18400817,32505856]
def z1965 : List Nat := [7,1023,31744,1015839,1082401,8659208,17318416]
def z1966 : List Nat := [7,1023,31744,1016800,1082401,8659208,17318416]
def z1967 : List Nat := [7,1023,31744,1082401,8659208,17318416,32505887]
def z1968 : List Nat := [7,1023,31744,1082401,8659208,17318416,32506848]
def z1969 : List Nat := [7,1023,31775,1082401,8659208,17318416,32505856]
def z1970 : List Nat := [7,1023,32736,1082401,8659208,17318416,32505856]
def z1971 : List Nat := [7,1023,1082401,2164802,4329604,8659208,32505887]
def z1972 : List Nat := [7,1023,1082401,2164802,4329604,8659208,32506848]
def z1973 : List Nat := [7,1023,1082401,2164802,4329604,17318416,32505887]
def z1974 : List Nat := [7,1023,1082401,2164802,4329604,17318416,32506848]
def z1975 : List Nat := [7,1023,1082401,2164802,8659208,17318416,32505887]
def z1976 : List Nat := [7,1023,1082401,2164802,8659208,17318416,32506848]
def z1977 : List Nat := [7,1023,1082401,8659208,17318416,32505856,32505887]
def z1978 : List Nat := [7,1023,1082401,8659208,17318416,32505856,32506848]
def z1979 : List Nat := [7,1023,1082401,8659208,17318416,32505856,33553439]
def z1980 : List Nat := [7,1023,1082401,8659208,17318416,32505856,33554400]
def z1981 : List Nat := [7,1023,1082401,8659208,17318416,32505887]
def z1982 : List Nat := [7,1023,1082401,8659208,17318416,32506848]
def z1983 : List Nat := [7,1023,2164802,4329604,8659208,17318416,32505887]
def z1984 : List Nat := [7,1023,2164802,4329604,8659208,17318416,32506848]
def z1985 : List Nat := [7,31744,31775,1082401,9412872,17318416,32505856]
def z1986 : List Nat := [7,31744,31775,2065441,8659208,17318416,32505856]
def z1987 : List Nat := [7,31744,32736,1015808,8659208,17318416,32539681]
def z1988 : List Nat := [7,31744,1015808,1048607,1082401,8659208,17318416]
def z1989 : List Nat := [7,31744,1015808,1048607,2164802,4329604,17318416]
def z1990 : List Nat := [7,31744,1015808,1082401,2164802,4329631,8659208,17318896,32505856]
def z1991 : List Nat := [7,31744,1015808,1082401,2164802,4329631,8659944,17318416,32505856]
def z1992 : List Nat := [7,31744,1015808,1083361,2164802,4329631,8659208,17318416,32505856]
def z1993 : List Nat := [7,31744,1015808,8659208,17318416,32505887,32539681]
def z1994 : List Nat := [7,31744,1015808,8659208,17318416,32539681,33553439]
def z1995 : List Nat := [7,31744,1015839,1016800,1082401,8659208,17318416]
def z1996 : List Nat := [7,31744,1015839,1082401,8659208,17318416,32505887]
def z1997 : List Nat := [7,31744,1015839,1082401,8659208,17318416,33521664]
def z1998 : List Nat := [7,31744,1016800,1082401,8659208,17318416,32506848]
def z1999 : List Nat := [7,31744,1016800,1082401,8659208,17318416,33521664]
def z2000 : List Nat := [7,31744,1016800,1082401,9412872,17318416,32505856]
def z2001 : List Nat := [7,31744,1016800,2065441,8659208,17318416,32505856]
def z2002 : List Nat := [7,31744,1082401,8659208,17318416,32505887,32506848]
def z2003 : List Nat := [7,31744,1082401,8659208,17318416,32505887,33521664]
def z2004 : List Nat := [7,31744,1082401,8659208,17318416,32506848,33521664]
def z2005 : List Nat := [7,31744,1082401,9412872,17318416,32505856,32505887]
def z2006 : List Nat := [7,31744,1082401,9412872,17318416,32505856,33554400]
def z2007 : List Nat := [7,31744,2065441,8659208,17318416,32505856,32505887]
def z2008 : List Nat := [7,31744,2065441,8659208,17318416,32505856,33554400]
def z2009 : List Nat := [7,31775,32736,1082401,8659208,17318416,32505856]
def z2010 : List Nat := [7,31775,1015839,1082401,8659208,17318416,32505856]
def z2011 : List Nat := [7,31775,1047552,1082401,8659208,17318416,32505856]
def z2012 : List Nat := [7,32736,1016800,1082401,8659208,17318416,32505856]
def z2013 : List Nat := [7,32736,1047552,1082401,8659208,17318416,32505856]
def z2014 : List Nat := [7,1047552,1047583,1082401,8659208,17318416,32505856]
def z2015 : List Nat := [7,1047552,1048544,1082401,8659208,17318416,32505856]
def z2016 : List Nat := [7,1047552,1082401,8659208,17318416,32505856,32505887]
def z2017 : List Nat := [7,1047552,1082401,8659208,17318416,32505856,32506848]
def z2018 : List Nat := [7,1047552,1082401,8659208,17318416,32505856,33553439]
def z2019 : List Nat := [7,1047552,1082401,8659208,17318416,32505856,33554400]
def z2020 : List Nat := [7,1082401,1083361,2164802,4329604,17318431,32505856]
def z2021 : List Nat := [7,1082401,1083361,2164831,8659208,17318416,32505856]
def z2022 : List Nat := [7,1082401,1083361,8659208,17318416,17318431,32505856]
def z2023 : List Nat := [7,1082401,1083361,8659208,17318416,32505856,32505887]
def z2024 : List Nat := [7,1082401,1083361,8659208,17318416,32505856,33554400]
def z2025 : List Nat := [7,1082401,2164802,2164831,4329604,8659944,32505856]
def z2026 : List Nat := [7,1082401,2164802,4329604,8659208,32505887,32506848]
def z2027 : List Nat := [7,1082401,2164802,4329604,8659944,32505856,32505887]
def z2028 : List Nat := [7,1082401,2164802,4329604,8659944,32505856,33554400]
def z2029 : List Nat := [7,1082401,2164802,4329604,17318416,32505887,32506848]
def z2030 : List Nat := [7,1082401,2164802,4329604,17318431,32505856,32506848]
def z2031 : List Nat := [7,1082401,2164802,4329604,17318431,32505856,33553439]
def z2032 : List Nat := [7,1082401,2164802,4329631,8659944,17318416,32505856]
def z2033 : List Nat := [7,1082401,2164802,8659208,17318416,32505887,32506848]
def z2034 : List Nat := [7,1082401,2164831,8659208,8659944,17318416,32505856]
def z2035 : List Nat := [7,1082401,2164831,8659208,17318416,32505856,32506848]
def z2036 : List Nat := [7,1082401,2164831,8659208,17318416,32505856,33553439]
def z2037 : List Nat := [7,1082401,8659208,8659944,17318416,17318431,32505856]
def z2038 : List Nat := [7,1082401,8659208,8659944,17318416,32505856,32505887]
def z2039 : List Nat := [7,1082401,8659208,8659944,17318416,32505856,33554400]
def z2040 : List Nat := [7,1082401,8659208,17318416,17318431,32505856,32506848]
def z2041 : List Nat := [7,1082401,8659208,17318416,17318431,32505856,33553439]
def z2042 : List Nat := [7,1082401,8659208,17318416,32505856,32505887,32506848]
def z2043 : List Nat := [7,1082401,8659208,17318416,32505856,32505887,32506879]
def z2044 : List Nat := [7,1082401,8659208,17318416,32505856,32505887,33553439]
def z2045 : List Nat := [7,1082401,8659208,17318416,32505856,32506848,32506879]
def z2046 : List Nat := [7,1082401,8659208,17318416,32505856,32506848,33554400]
def z2047 : List Nat := [7,1082401,8659208,17318416,32505856,33553439,33554400]
def z2048 : List Nat := [7,1082401,8659208,17318416,32505887,32506848]
def z2049 : List Nat := [7,1083361,2164802,2164831,4329604,8659208,32505856]
def z2050 : List Nat := [7,1083361,2164802,2164831,4329604,17318416,32505856]
def z2051 : List Nat := [7,1083361,2164802,4329604,8659208,32505856,32505887]
def z2052 : List Nat := [7,1083361,2164802,4329604,8659208,32505856,33554400]
def z2053 : List Nat := [7,1083361,2164802,4329604,17318416,17318431,32505856]
def z2054 : List Nat := [7,1083361,2164802,4329604,17318416,32505856,32505887]
def z2055 : List Nat := [7,1083361,2164802,4329604,17318416,32505856,33554400]
def z2056 : List Nat := [7,1083361,2164802,4329631,8659208,17318416,32505856]
def z2057 : List Nat := [7,2164802,2164831,4329604,8659944,17318416,32505856]
def z2058 : List Nat := [7,2164802,4329604,8659208,8659944,17318431,32505856]
def z2059 : List Nat := [7,2164802,4329604,8659208,17318416,32505887,32506848]
def z2060 : List Nat := [7,2164802,4329604,8659208,17318431,32505856,32506848]
def z2061 : List Nat := [7,2164802,4329604,8659208,17318431,32505856,33553439]
def z2062 : List Nat := [7,2164802,4329604,8659944,17318416,17318431,32505856]
def z2063 : List Nat := [7,2164802,4329604,8659944,17318416,32505856,32505887]
def z2064 : List Nat := [7,2164802,4329604,8659944,17318416,32505856,33554400]
def z2065 : List Nat := [8,0,31,992,1082401,8659208,17318416,32505856]
def z2066 : List Nat := [8,1,31,992,1082401,8659208,17318416,32505856]
def z2067 : List Nat := [8,2,31,992,1082401,8659208,17318416,32505856]
def z2068 : List Nat := [8,8,31,992,1082401,8659208,17318416,32505856]
def z2069 : List Nat := [8,16,31,992,1082401,8659208,17318416,32505856]
def z2070 : List Nat := [8,31,31,992,1082401,8659208,17318416,32505856]
def z2071 : List Nat := [8,31,32,992,1082401,8659208,17318416,32505856]
def z2072 : List Nat := [8,31,32,31744,1015808,1082401,8659208,17318416]
def z2073 : List Nat := [8,31,64,992,1082401,8659208,17318416,32505856]
def z2074 : List Nat := [8,31,256,992,1082401,8659208,17318416,32505856]
def z2075 : List Nat := [8,31,512,992,1082401,8659208,17318416,32505856]
def z2076 : List Nat := [8,31,992,992,1082401,8659208,17318416,32505856]
def z2077 : List Nat := [8,31,992,1023,1082401,8659208,17318416,32505856]
def z2078 : List Nat := [8,31,992,1024,1082401,8659208,17318416,32505856]
def z2079 : List Nat := [8,31,992,2048,1082401,8659208,17318416,32505856]
def z2080 : List Nat := [8,31,992,8192,1082401,8659208,17318416,32505856]
def z2081 : List Nat := [8,31,992,16384,1082401,8659208,17318416,32505856]
def z2082 : List Nat := [8,31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056]
def z2083 : List Nat := [8,31,992,31744,1015808,1082401,2164802,4329604,17318416,32776456]
def z2084 : List Nat := [8,31,992,31744,1015808,1082401,6494406,8659208]
def z2085 : List Nat := [8,31,992,31744,1015808,1082401,6494406,8659208,17318416,32505856]
def z2086 : List Nat := [8,31,992,31744,1015808,1082401,6494406,17318416]
def z2087 : List Nat := [8,31,992,31744,1015808,1082401,8659208,16236015]
def z2088 : List Nat := [8,31,992,31744,1015808,1082401,8659208,17318416]
def z2089 : List Nat := [8,31,992,31744,1015808,1082401,8659208,18400817]
def z2090 : List Nat := [8,31,992,31744,1015808,1082401,8659208,25977624]
def z2091 : List Nat := [8,31,992,31744,1015808,1082401,8682760,17318416]
def z2092 : List Nat := [8,31,992,31744,1015808,1082401,9741609,17318416]
def z2093 : List Nat := [8,31,992,31744,1015808,1082401,17318416,24895223]
def z2094 : List Nat := [8,31,992,31744,1015808,1082401,17318416,25977624]
def z2095 : List Nat := [8,31,992,31744,1015808,1113121,8659208,17318416]
def z2096 : List Nat := [8,31,992,31744,1015808,6494406,8659208,17318416]
def z2097 : List Nat := [8,31,992,31744,1015808,8659208,9741609,17318416]
def z2098 : List Nat := [8,31,992,31744,1015808,8659208,17318416,18400817]
def z2099 : List Nat := [8,31,992,31744,1015808,8659208,17318416,32472030]
def z2100 : List Nat := [8,31,992,31744,1015808,8659208,17318416,32539681]
def z2101 : List Nat := [8,31,992,31744,1015839,1082401,8659208,17318416]
def z2102 : List Nat := [8,31,992,31744,1016800,1082401,8659208,17318416]
def z2103 : List Nat := [8,31,992,31744,1047552,1082401,8659208,17318416]
def z2104 : List Nat := [8,31,992,31744,1048575,1082401,8659208,17318416]
def z2105 : List Nat := [8,31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856]
def z2106 : List Nat := [8,31,992,31744,1082401,2164802,4329604,32776456]
def z2107 : List Nat := [8,31,992,31744,1082401,2164802,5214340,8659208,17318416,32505856]
def z2108 : List Nat := [8,31,992,31744,1082401,2164802,9412872,17318416]
def z2109 : List Nat := [8,31,992,31744,1082401,6494406,8659208,32505856]
def z2110 : List Nat := [8,31,992,31744,1082401,6494406,17318416,32505856]
def z2111 : List Nat := [8,31,992,31744,1082401,8659208,9412872,17318416]
def z2112 : List Nat := [8,31,992,31744,1082401,8659208,16236015,32505856]
def z2113 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32505856]
def z2114 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32505887]
def z2115 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32506848]
def z2116 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32537600]
def z2117 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32538623]
def z2118 : List Nat := [8,31,992,31744,1082401,8659208,17318416,32776456]
def z2119 : List Nat := [8,31,992,31744,1082401,8659208,18400817,32505856]
def z2120 : List Nat := [8,31,992,31744,1082401,8659208,25977624,32505856]
def z2121 : List Nat := [8,31,992,31744,1082401,8682760,17318416,32505856]
def z2122 : List Nat := [8,31,992,31744,1082401,9412872,17318416]
def z2123 : List Nat := [8,31,992,31744,1082401,9412872,17318416,32505856]
def z2124 : List Nat := [8,31,992,31744,1082401,9741609,17318416,32505856]
def z2125 : List Nat := [8,31,992,31744,1082401,17318416,24895223,32505856]
def z2126 : List Nat := [8,31,992,31744,1082401,17318416,25977624,32505856]
def z2127 : List Nat := [8,31,992,31744,1113121,8659208,17318416,32505856]
def z2128 : List Nat := [8,31,992,31744,2065441,2164802,4329604,8659208,17318416,32505856]
def z2129 : List Nat := [8,31,992,31744,2065441,8659208,17318416,32505856]
def z2130 : List Nat := [8,31,992,31744,2164802,4329604,9412872,17318416]
def z2131 : List Nat := [8,31,992,31744,6494406,8659208,17318416,32505856]
def z2132 : List Nat := [8,31,992,31744,8659208,9741609,17318416,32505856]
def z2133 : List Nat := [8,31,992,31744,8659208,17318416,18400817,32505856]
def z2134 : List Nat := [8,31,992,31744,8659208,17318416,32472030,32505856]
def z2135 : List Nat := [8,31,992,31744,8659208,17318416,32505856,32539681]
def z2136 : List Nat := [8,31,992,31775,1082401,8659208,17318416,32505856]
def z2137 : List Nat := [8,31,992,32736,1082401,8659208,17318416,32505856]
def z2138 : List Nat := [8,31,992,1047552,1082401,2164802,4329604,8659208]
def z2139 : List Nat := [8,31,992,1047552,1082401,2164802,4329604,8659208,17318416,32505856]
def z2140 : List Nat := [8,31,992,1047552,1082401,2164802,4329604,17318416]
def z2141 : List Nat := [8,31,992,1047552,1082401,2164802,8659208,17318416]
def z2142 : List Nat := [8,31,992,1047552,1082401,8659208,17318416]
def z2143 : List Nat := [8,31,992,1047552,1082401,8659208,17318416,32505856]
def z2144 : List Nat := [8,31,992,1047552,2164802,4329604,8659208,17318416]
def z2145 : List Nat := [8,31,992,1048575,1082401,2164802,4329604,8659208]
def z2146 : List Nat := [8,31,992,1048575,1082401,2164802,4329604,17318416]
def z2147 : List Nat := [8,31,992,1048575,1082401,2164802,8659208,17318416]
def z2148 : List Nat := [8,31,992,1048575,1082401,8659208,17318416]
def z2149 : List Nat := [8,31,992,1048575,1082401,8659208,17318416,32505856]
def z2150 : List Nat := [8,31,992,1048575,2164802,4329604,8659208,17318416]
def z2151 : List Nat := [8,31,992,1048576,1082401,8659208,17318416,32505856]
def z2152 : List Nat := [8,31,992,1048576,2164802,4329604,17318416,32505856]
def z2153 : List Nat := [8,31,992,1082401,1082401,8659208,17318416,32505856]
def z2154 : List Nat := [8,31,992,1082401,1082431,8659208,17318416,32505856]
def z2155 : List Nat := [8,31,992,1082401,1083361,8659208,17318416,32505856]
def z2156 : List Nat := [8,31,992,1082401,1113121,8659208,17318416,32505856]
def z2157 : List Nat := [8,31,992,1082401,2097152,8659208,17318416,32505856]
def z2158 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,32505856]
def z2159 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,32505887]
def z2160 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,32506848]
def z2161 : List Nat := [8,31,992,1082401,2164802,4329604,8659208,32776456]
def z2162 : List Nat := [8,31,992,1082401,2164802,4329604,8659231,32505856]
def z2163 : List Nat := [8,31,992,1082401,2164802,4329604,8659944,32505856]
def z2164 : List Nat := [8,31,992,1082401,2164802,4329604,9741609,32505856]
def z2165 : List Nat := [8,31,992,1082401,2164802,4329604,10824010,32505856]
def z2166 : List Nat := [8,31,992,1082401,2164802,4329604,16236015,32505856]
def z2167 : List Nat := [8,31,992,1082401,2164802,4329604,17318416,32505856]
def z2168 : List Nat := [8,31,992,1082401,2164802,4329604,17318416,32505887]
def z2169 : List Nat := [8,31,992,1082401,2164802,4329604,17318416,32506848]
def z2170 : List Nat := [8,31,992,1082401,2164802,4329604,17318416,32776456]
def z2171 : List Nat := [8,31,992,1082401,2164802,4329604,17318431,32505856]
def z2172 : List Nat := [8,31,992,1082401,2164802,4329604,17318896,32505856]
def z2173 : List Nat := [8,31,992,1082401,2164802,4329604,18400817,32505856]
def z2174 : List Nat := [8,31,992,1082401,2164802,4329604,19483218,32505856]
def z2175 : List Nat := [8,31,992,1082401,2164802,4329604,24895223,32505856]
def z2176 : List Nat := [8,31,992,1082401,2164802,4329604,32505856,32776456]
def z2177 : List Nat := [8,31,992,1082401,2164802,4329604,32505856,33047056]
def z2178 : List Nat := [8,31,992,1082401,2164802,4329604,32776456]
def z2179 : List Nat := [8,31,992,1082401,2164802,4357252,17318416,32505856]
def z2180 : List Nat := [8,31,992,1082401,2164802,5412005,8659208,32505856]
def z2181 : List Nat := [8,31,992,1082401,2164802,5412005,17318416,32505856]
def z2182 : List Nat := [8,31,992,1082401,2164802,6494406,8659208,32505856]
def z2183 : List Nat := [8,31,992,1082401,2164802,6494406,17318416,32505856]
def z2184 : List Nat := [8,31,992,1082401,2164802,8659208,12988812,32505856]
def z2185 : List Nat := [8,31,992,1082401,2164802,8659208,16236015,32505856]
def z2186 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,32505856]
def z2187 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,32505887]
def z2188 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,32506848]
def z2189 : List Nat := [8,31,992,1082401,2164802,8659208,17318416,32776456]
def z2190 : List Nat := [8,31,992,1082401,2164802,8659208,18400817,32505856]
def z2191 : List Nat := [8,31,992,1082401,2164802,8659208,19483218,32505856]
def z2192 : List Nat := [8,31,992,1082401,2164802,8659208,25977624,32505856]
def z2193 : List Nat := [8,31,992,1082401,2164802,8659208,29224827,32505856]
def z2194 : List Nat := [8,31,992,1082401,2164802,8682760,17318416,32505856]
def z2195 : List Nat := [8,31,992,1082401,2164802,9741609,17318416,32505856]
def z2196 : List Nat := [8,31,992,1082401,2164802,10824010,17318416,32505856]
def z2197 : List Nat := [8,31,992,1082401,2164802,17318416,21648020,32505856]
def z2198 : List Nat := [8,31,992,1082401,2164802,17318416,24895223,32505856]
def z2199 : List Nat := [8,31,992,1082401,2164802,17318416,25977624,32505856]
def z2200 : List Nat := [8,31,992,1082401,2164802,17318416,29224827,32505856]
def z2201 : List Nat := [8,31,992,1082401,2164831,8659208,17318416,32505856]
def z2202 : List Nat := [8,31,992,1082401,2165730,8659208,17318416,32505856]
def z2203 : List Nat := [8,31,992,1082401,2194498,8659208,17318416,32505856]
def z2204 : List Nat := [8,31,992,1082401,3247203,8659208,17318416,32505856]
def z2205 : List Nat := [8,31,992,1082401,6494406,8659208,17318416,32505856]
def z2206 : List Nat := [8,31,992,1082401,6494406,8659208,32505856]
def z2207 : List Nat := [8,31,992,1082401,6494406,17318416,32505856]
def z2208 : List Nat := [8,31,992,1082401,8388608,8659208,17318416,32505856]
def z2209 : List Nat := [8,31,992,1082401,8659208,8659208,17318416,32505856]
def z2210 : List Nat := [8,31,992,1082401,8659208,8659231,17318416,32505856]
def z2211 : List Nat := [8,31,992,1082401,8659208,8659944,17318416,32505856]
def z2212 : List Nat := [8,31,992,1082401,8659208,8682760,17318416,32505856]
def z2213 : List Nat := [8,31,992,1082401,8659208,9741609,17318416,32505856]
def z2214 : List Nat := [8,31,992,1082401,8659208,10824010,17318416,32505856]
def z2215 : List Nat := [8,31,992,1082401,8659208,16236015,17318416,32505856]
def z2216 : List Nat := [8,31,992,1082401,8659208,16236015,32505856]
def z2217 : List Nat := [8,31,992,1082401,8659208,16777216,17318416,32505856]
def z2218 : List Nat := [8,31,992,1082401,8659208,17318416,17318416,32505856]
def z2219 : List Nat := [8,31,992,1082401,8659208,17318416,17318431,32505856]
def z2220 : List Nat := [8,31,992,1082401,8659208,17318416,17318896,32505856]
def z2221 : List Nat := [8,31,992,1082401,8659208,17318416,17333776,32505856]
def z2222 : List Nat := [8,31,992,1082401,8659208,17318416,18400817,32505856]
def z2223 : List Nat := [8,31,992,1082401,8659208,17318416,19483218,32505856]
def z2224 : List Nat := [8,31,992,1082401,8659208,17318416,24895223,32505856]
def z2225 : List Nat := [8,31,992,1082401,8659208,17318416,25977624,32505856]
def z2226 : List Nat := [8,31,992,1082401,8659208,17318416,29224827,32505856]
def z2227 : List Nat := [8,31,992,1082401,8659208,17318416,32472030,32505856]
def z2228 : List Nat := [8,31,992,1082401,8659208,17318416,32505856]
def z2229 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32505856]
def z2230 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32505887]
def z2231 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32506848]
def z2232 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32537600]
def z2233 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32538623]
def z2234 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32539681]
def z2235 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32573506]
def z2236 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,32776456]
def z2237 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,33047056]
def z2238 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,33553439]
def z2239 : List Nat := [8,31,992,1082401,8659208,17318416,32505856,33554400]
def z2240 : List Nat := [8,31,992,1082401,8659208,17318416,32505887]
def z2241 : List Nat := [8,31,992,1082401,8659208,17318416,32506848]
def z2242 : List Nat := [8,31,992,1082401,8659208,17318416,32776456]
def z2243 : List Nat := [8,31,992,1082401,8659208,18400817,32505856]
def z2244 : List Nat := [8,31,992,1082401,8659208,25977624,32505856]
def z2245 : List Nat := [8,31,992,1082401,8682760,17318416,32505856]
def z2246 : List Nat := [8,31,992,1082401,9741609,17318416,32505856]
def z2247 : List Nat := [8,31,992,1082401,17318416,24895223,32505856]
def z2248 : List Nat := [8,31,992,1082401,17318416,25977624,32505856]
def z2249 : List Nat := [8,31,992,1082431,2164802,4329604,8659208,32505856]
def z2250 : List Nat := [8,31,992,1082431,2164802,4329604,17318416,32505856]
def z2251 : List Nat := [8,31,992,1083361,2164802,4329604,8659208,32505856]
def z2252 : List Nat := [8,31,992,1083361,2164802,4329604,17318416,32505856]
def z2253 : List Nat := [8,31,992,1113121,2164802,4329604,17318416,32505856]
def z2254 : List Nat := [8,31,992,1113121,2164802,8659208,17318416,32505856]
def z2255 : List Nat := [8,31,992,1113121,8659208,17318416,32505856]
def z2256 : List Nat := [8,31,992,2164802,3247203,4329604,8659208,32505856]
def z2257 : List Nat := [8,31,992,2164802,3247203,4329604,17318416,32505856]
def z2258 : List Nat := [8,31,992,2164802,3247203,8659208,17318416,32505856]
def z2259 : List Nat := [8,31,992,2164802,4329604,8388608,17318416,32505856]
def z2260 : List Nat := [8,31,992,2164802,4329604,8659208,9741609,32505856]
def z2261 : List Nat := [8,31,992,2164802,4329604,8659208,16236015,32505856]
def z2262 : List Nat := [8,31,992,2164802,4329604,8659208,17318416,32505856]
def z2263 : List Nat := [8,31,992,2164802,4329604,8659208,17318416,32505887]
def z2264 : List Nat := [8,31,992,2164802,4329604,8659208,17318416,32506848]
def z2265 : List Nat := [8,31,992,2164802,4329604,8659208,17318416,32776456]
def z2266 : List Nat := [8,31,992,2164802,4329604,8659208,17318431,32505856]
def z2267 : List Nat := [8,31,992,2164802,4329604,8659208,17318896,32505856]
def z2268 : List Nat := [8,31,992,2164802,4329604,8659208,19483218,32505856]
def z2269 : List Nat := [8,31,992,2164802,4329604,8659208,25977624,32505856]
def z2270 : List Nat := [8,31,992,2164802,4329604,8659208,32472030,32505856]
def z2271 : List Nat := [8,31,992,2164802,4329604,8659231,17318416,32505856]
def z2272 : List Nat := [8,31,992,2164802,4329604,8659944,17318416,32505856]
def z2273 : List Nat := [8,31,992,2164802,4329604,8682760,17318416,32505856]
def z2274 : List Nat := [8,31,992,2164802,4329604,10824010,17318416,32505856]
def z2275 : List Nat := [8,31,992,2164802,4329604,17318416,18400817,32505856]
def z2276 : List Nat := [8,31,992,2164802,4329604,17318416,24895223,32505856]
def z2277 : List Nat := [8,31,992,2164802,4329604,17318416,25977624,32505856]
def z2278 : List Nat := [8,31,992,2164802,4329604,17318416,32472030,32505856]
def z2279 : List Nat := [8,31,992,2164802,4357252,8659208,17318416,32505856]
def z2280 : List Nat := [8,31,992,2164802,6494406,8659208,17318416,32505856]
def z2281 : List Nat := [8,31,992,2164802,8659208,9741609,17318416,32505856]
def z2282 : List Nat := [8,31,992,2164802,8659208,12988812,17318416,32505856]
def z2283 : List Nat := [8,31,992,2164802,8659208,17318416,18400817,32505856]
def z2284 : List Nat := [8,31,992,2164802,8659208,17318416,21648020,32505856]
def z2285 : List Nat := [8,31,992,2164802,8659208,17318416,29224827,32505856]
def z2286 : List Nat := [8,31,992,2164802,8659208,17318416,32472030,32505856]
def z2287 : List Nat := [8,31,992,2164802,8659208,17318416,32505856,32539681]
def z2288 : List Nat := [8,31,992,2164802,8659208,17318416,32505856,32641156]
def z2289 : List Nat := [8,31,992,6494406,8659208,17318416,32505856]
def z2290 : List Nat := [8,31,992,8659208,9741609,17318416,32505856]
def z2291 : List Nat := [8,31,992,8659208,17318416,18400817,32505856]
def z2292 : List Nat := [8,31,992,8659208,17318416,32472030,32505856]
def z2293 : List Nat := [8,31,992,8659208,17318416,32505856,32539681]
def z2294 : List Nat := [8,31,1023,31744,1015808,1082401,8659208,17318416]
def z2295 : List Nat := [8,31,1023,31744,1082401,8659208,17318416,32505856]
def z2296 : List Nat := [8,31,1023,1082401,2164802,4329604,8659208,32505856]
def z2297 : List Nat := [8,31,1023,1082401,2164802,4329604,17318416,32505856]
def z2298 : List Nat := [8,31,1023,1082401,2164802,8659208,17318416,32505856]
def z2299 : List Nat := [8,31,1023,1082401,8659208,17318416,32505856]
def z2300 : List Nat := [8,31,1023,2164802,4329604,8659208,17318416,32505856]
def z2301 : List Nat := [8,31,31744,32736,1015808,1082401,8659208,17318416]
def z2302 : List Nat := [8,31,31744,32736,1082401,8659208,17318416,32505856]
def z2303 : List Nat := [8,31,31744,1015808,1048575,1082401,8659208,17318416]
def z2304 : List Nat := [8,31,31744,1015808,1048576,1082401,8659208,17318416]
def z2305 : List Nat := [8,31,31744,1015808,1048576,2164802,4329604,17318416]
def z2306 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,8659208,17318896,32505856]
def z2307 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,8659944]
def z2308 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856]
def z2309 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,17318896]
def z2310 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,32776456]
def z2311 : List Nat := [8,31,31744,1015808,1082401,2164802,4329604,33047056]
def z2312 : List Nat := [8,31,31744,1015808,1082401,2165730,8659208,17318416]
def z2313 : List Nat := [8,31,31744,1015808,1082401,6494406,8659208,32505856]
def z2314 : List Nat := [8,31,31744,1015808,1082401,6494406,17318416,32505856]
def z2315 : List Nat := [8,31,31744,1015808,1082401,8659208,8659944,17318416]
def z2316 : List Nat := [8,31,31744,1015808,1082401,8659208,16236015,32505856]
def z2317 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,17318896]
def z2318 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,32505856]
def z2319 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,32505887]
def z2320 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,32537600]
def z2321 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,32573506]
def z2322 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,32776456]
def z2323 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,33047056]
def z2324 : List Nat := [8,31,31744,1015808,1082401,8659208,17318416,33553439]
def z2325 : List Nat := [8,31,31744,1015808,1082401,8659208,18400817,32505856]
def z2326 : List Nat := [8,31,31744,1015808,1082401,8659208,25977624,32505856]
def z2327 : List Nat := [8,31,31744,1015808,1082401,8682760,17318416,32505856]
def z2328 : List Nat := [8,31,31744,1015808,1082401,9741609,17318416,32505856]
def z2329 : List Nat := [8,31,31744,1015808,1082401,17318416,24895223,32505856]
def z2330 : List Nat := [8,31,31744,1015808,1082401,17318416,25977624,32505856]
def z2331 : List Nat := [8,31,31744,1015808,1083361,2164802,4329604,8659208,17318416,32505856]
def z2332 : List Nat := [8,31,31744,1015808,1113121,8659208,17318416,32505856]
def z2333 : List Nat := [8,31,31744,1015808,2164802,4329604,8659208,17318896]
def z2334 : List Nat := [8,31,31744,1015808,2164802,4329604,8659944,17318416]
def z2335 : List Nat := [8,31,31744,1015808,2164802,8659208,17318416,32641156]
def z2336 : List Nat := [8,31,31744,1015808,6494406,8659208,17318416,32505856]
def z2337 : List Nat := [8,31,31744,1015808,8659208,9741609,17318416,32505856]
def z2338 : List Nat := [8,31,31744,1015808,8659208,17318416,18400817,32505856]
def z2339 : List Nat := [8,31,31744,1015808,8659208,17318416,32472030,32505856]
def z2340 : List Nat := [8,31,31744,1015808,8659208,17318416,32505856,32539681]
def z2341 : List Nat := [8,31,31744,1015839,1082401,8659208,17318416,32505856]
def z2342 : List Nat := [8,31,31744,1047552,1082401,8659208,17318416,32505856]
def z2343 : List Nat := [8,31,31744,1082401,1083361,8659208,17318416,32505856]
def z2344 : List Nat := [8,31,31744,1082401,2065441,8659208,17318416,32505856]
def z2345 : List Nat := [8,31,31744,1082401,2164802,4329604,8659944,32505856]
def z2346 : List Nat := [8,31,31744,1082401,2164802,9412872,17318416,32505856]
def z2347 : List Nat := [8,31,31744,1082401,8659208,8659944,17318416,32505856]
def z2348 : List Nat := [8,31,31744,1082401,8659208,9412872,17318416,32505856]
def z2349 : List Nat := [8,31,31744,1082401,8659208,17318416,32505856,32506848]
def z2350 : List Nat := [8,31,31744,1082401,8659208,17318416,32505856,32538623]
def z2351 : List Nat := [8,31,31744,1082401,8659208,17318416,32505856,33521664]
def z2352 : List Nat := [8,31,31744,1082401,8659208,17318416,32505856,33553439]
def z2353 : List Nat := [8,31,31744,1082401,9412872,17318416,32505856]
def z2354 : List Nat := [8,31,31744,1083361,2164802,4329604,8659208,32505856]
def z2355 : List Nat := [8,31,31744,1083361,2164802,4329604,17318416,32505856]
def z2356 : List Nat := [8,31,31744,2065441,2164802,4329604,17318416,32505856]
def z2357 : List Nat := [8,31,31744,2065441,2164802,8659208,17318416,32505856]
def z2358 : List Nat := [8,31,31744,2065441,8659208,17318416,32505856]
def z2359 : List Nat := [8,31,31744,2164802,4329604,8659944,17318416,32505856]
def z2360 : List Nat := [8,31,31744,2164802,4329604,9412872,17318416,32505856]
def z2361 : List Nat := [8,31,1047552,1082401,2164802,4329604,8659208,32505856]
def z2362 : List Nat := [8,31,1047552,1082401,2164802,4329604,17318416,32505856]
def z2363 : List Nat := [8,31,1047552,1082401,2164802,8659208,17318416,32505856]
def z2364 : List Nat := [8,31,1047552,1082401,8659208,17318416,32505856]
def z2365 : List Nat := [8,31,1047552,2164802,4329604,8659208,17318416,32505856]
def z2366 : List Nat := [8,31,1082401,1083361,2164802,4329604,8659208,32505856]
def z2367 : List Nat := [8,31,1082401,1083361,2164802,4329604,17318416,32505856]
def z2368 : List Nat := [8,31,1082401,1083361,2164802,8659208,17318416,32505856]
def z2369 : List Nat := [8,31,1082401,1083361,8659208,17318416,32505856]
def z2370 : List Nat := [8,31,1082401,2164802,4329604,8659208,8659944,32505856]
def z2371 : List Nat := [8,31,1082401,2164802,4329604,8659208,32505856,32506848]
def z2372 : List Nat := [8,31,1082401,2164802,4329604,8659208,32505856,33553439]
def z2373 : List Nat := [8,31,1082401,2164802,4329604,8659944,17318416,32505856]
def z2374 : List Nat := [8,31,1082401,2164802,4329604,8659944,32505856]
def z2375 : List Nat := [8,31,1082401,2164802,4329604,17318416,32505856,32506848]
def z2376 : List Nat := [8,31,1082401,2164802,4329604,17318416,32505856,33553439]
def z2377 : List Nat := [8,31,1082401,2164802,8659208,8659944,17318416,32505856]
def z2378 : List Nat := [8,31,1082401,2164802,8659208,17318416,32505856,32506848]
def z2379 : List Nat := [8,31,1082401,2164802,8659208,17318416,32505856,33553439]
def z2380 : List Nat := [8,31,1082401,8659208,8659944,17318416,32505856]
def z2381 : List Nat := [8,31,1082401,8659208,17318416,32505856,32506848]
def z2382 : List Nat := [8,31,1082401,8659208,17318416,32505856,33553439]
def z2383 : List Nat := [8,31,1083361,2164802,4329604,8659208,17318416,32505856]
def z2384 : List Nat := [8,31,1083361,2164802,4329604,8659208,32505856]
def z2385 : List Nat := [8,31,1083361,2164802,4329604,17318416,32505856]
def z2386 : List Nat := [8,31,2164802,4329604,8659208,8659944,17318416,32505856]
def z2387 : List Nat := [8,31,2164802,4329604,8659208,17318416,32505856,32506848]
def z2388 : List Nat := [8,31,2164802,4329604,8659208,17318416,32505856,33553439]
def z2389 : List Nat := [8,31,2164802,4329604,8659944,17318416,32505856]
def z2390 : List Nat := [8,992,1023,31744,1015808,1082401,8659208,17318416]
def z2391 : List Nat := [8,992,1023,31744,1082401,8659208,17318416,32505856]
def z2392 : List Nat := [8,992,1023,1082401,2164802,4329604,8659208,32505856]
def z2393 : List Nat := [8,992,1023,1082401,2164802,4329604,17318416,32505856]
def z2394 : List Nat := [8,992,1023,1082401,2164802,8659208,17318416,32505856]
def z2395 : List Nat := [8,992,1023,1082401,8659208,17318416,32505856]
def z2396 : List Nat := [8,992,1023,2164802,4329604,8659208,17318416,32505856]
def z2397 : List Nat := [8,992,31744,31775,1015808,1082401,8659208,17318416]
def z2398 : List Nat := [8,992,31744,31775,1082401,8659208,17318416,32505856]
def z2399 : List Nat := [8,992,31744,1015808,1048575,1082401,8659208,17318416]
def z2400 : List Nat := [8,992,31744,1015808,1082401,1082431,8659208,17318416]
def z2401 : List Nat := [8,992,31744,1015808,1082401,2164802,4329631,8659208,17318416,32505856]
def z2402 : List Nat := [8,992,31744,1015808,1082401,6494406,8659208,32505856]
def z2403 : List Nat := [8,992,31744,1015808,1082401,6494406,17318416,32505856]
def z2404 : List Nat := [8,992,31744,1015808,1082401,8659208,16236015,32505856]
def z2405 : List Nat := [8,992,31744,1015808,1082401,8659208,17318416,32505856]
def z2406 : List Nat := [8,992,31744,1015808,1082401,8659208,17318416,32506848]
def z2407 : List Nat := [8,992,31744,1015808,1082401,8659208,17318416,32537600]
def z2408 : List Nat := [8,992,31744,1015808,1082401,8659208,17318416,32539681]
def z2409 : List Nat := [8,992,31744,1015808,1082401,8659208,17318416,33554400]
def z2410 : List Nat := [8,992,31744,1015808,1082401,8659208,18400817,32505856]
def z2411 : List Nat := [8,992,31744,1015808,1082401,8659208,25977624,32505856]
def z2412 : List Nat := [8,992,31744,1015808,1082401,8682760,17318416,32505856]
def z2413 : List Nat := [8,992,31744,1015808,1082401,9741609,17318416,32505856]
def z2414 : List Nat := [8,992,31744,1015808,1082401,17318416,24895223,32505856]
def z2415 : List Nat := [8,992,31744,1015808,1082401,17318416,25977624,32505856]
def z2416 : List Nat := [8,992,31744,1015808,1082431,2164802,4329604,8659208]
def z2417 : List Nat := [8,992,31744,1015808,1082431,2164802,4329604,17318416]
def z2418 : List Nat := [8,992,31744,1015808,1113121,8659208,17318416,32505856]
def z2419 : List Nat := [8,992,31744,1015808,2164802,8659208,17318416,32539681]
def z2420 : List Nat := [8,992,31744,1015808,6494406,8659208,17318416,32505856]
def z2421 : List Nat := [8,992,31744,1015808,8659208,9741609,17318416,32505856]
def z2422 : List Nat := [8,992,31744,1015808,8659208,17318416,18400817,32505856]
def z2423 : List Nat := [8,992,31744,1015808,8659208,17318416,32472030,32505856]
def z2424 : List Nat := [8,992,31744,1015808,8659208,17318416,32505856,32539681]
def z2425 : List Nat := [8,992,31744,1015808,8659208,17318416,32539681]
def z2426 : List Nat := [8,992,31744,1016800,1082401,8659208,17318416,32505856]
def z2427 : List Nat := [8,992,31744,1047552,1082401,8659208,17318416,32505856]
def z2428 : List Nat := [8,992,31744,1082401,2164802,4329604,17318431,32505856]
def z2429 : List Nat := [8,992,31744,1082401,2164802,5214340,17318416,32505856]
def z2430 : List Nat := [8,992,31744,1082401,2164831,8659208,17318416,32505856]
def z2431 : List Nat := [8,992,31744,1082401,3115074,8659208,17318416,32505856]
def z2432 : List Nat := [8,992,31744,1082401,8659208,17318416,17318431,32505856]
def z2433 : List Nat := [8,992,31744,1082401,8659208,17318416,17809936,32505856]
def z2434 : List Nat := [8,992,31744,1082401,8659208,17318416,32505856,32505887]
def z2435 : List Nat := [8,992,31744,1082401,8659208,17318416,32505856,32538623]
def z2436 : List Nat := [8,992,31744,1082401,8659208,17318416,32505856,33521664]
def z2437 : List Nat := [8,992,31744,1082401,8659208,17318416,32505856,33554400]
def z2438 : List Nat := [8,992,31744,2164802,4329604,8659208,17318431,32505856]
def z2439 : List Nat := [8,992,31744,2164802,5214340,8659208,17318416,32505856]
def z2440 : List Nat := [8,992,1047552,1082401,2164802,4329604,8659208,32505856]
def z2441 : List Nat := [8,992,1047552,1082401,2164802,4329604,17318416,32505856]
def z2442 : List Nat := [8,992,1047552,1082401,2164802,8659208,17318416,32505856]
def z2443 : List Nat := [8,992,1047552,1082401,8659208,17318416,32505856]
def z2444 : List Nat := [8,992,1047552,2164802,4329604,8659208,17318416,32505856]
def z2445 : List Nat := [8,992,1082401,2164802,2164831,4329604,8659208,32505856]
def z2446 : List Nat := [8,992,1082401,2164802,2164831,4329604,17318416,32505856]
def z2447 : List Nat := [8,992,1082401,2164802,2164831,8659208,17318416,32505856]
def z2448 : List Nat := [8,992,1082401,2164802,4329604,8659208,17318431,32505856]
def z2449 : List Nat := [8,992,1082401,2164802,4329604,8659208,32505856,32505887]
def z2450 : List Nat := [8,992,1082401,2164802,4329604,8659208,32505856,33554400]
def z2451 : List Nat := [8,992,1082401,2164802,4329604,17318416,17318431,32505856]
def z2452 : List Nat := [8,992,1082401,2164802,4329604,17318416,32505856,32505887]
def z2453 : List Nat := [8,992,1082401,2164802,4329604,17318416,32505856,33554400]
def z2454 : List Nat := [8,992,1082401,2164802,4329604,17318431,32505856]
def z2455 : List Nat := [8,992,1082401,2164802,4329631,8659208,17318416,32505856]
def z2456 : List Nat := [8,992,1082401,2164802,8659208,17318416,17318431,32505856]
def z2457 : List Nat := [8,992,1082401,2164802,8659208,17318416,32505856,32505887]
def z2458 : List Nat := [8,992,1082401,2164802,8659208,17318416,32505856,33554400]
def z2459 : List Nat := [8,992,1082401,2164831,8659208,17318416,32505856]
def z2460 : List Nat := [8,992,1082401,8659208,17318416,17318431,32505856]
def z2461 : List Nat := [8,992,1082401,8659208,17318416,32505856,32505887]
def z2462 : List Nat := [8,992,1082401,8659208,17318416,32505856,33554400]
def z2463 : List Nat := [8,992,2164802,2164831,4329604,8659208,17318416,32505856]
def z2464 : List Nat := [8,992,2164802,4329604,8659208,17318416,17318431,32505856]
def z2465 : List Nat := [8,992,2164802,4329604,8659208,17318416,32505856,32505887]
def z2466 : List Nat := [8,992,2164802,4329604,8659208,17318416,32505856,33554400]
def z2467 : List Nat := [8,992,2164802,4329604,8659208,17318431,32505856]
def z2468 : List Nat := [8,31744,31775,1015808,1082401,8659208,17318416,32505856]
def z2469 : List Nat := [8,31744,32736,1015808,1082401,8659208,17318416,32505856]
def z2470 : List Nat := [8,31744,1015808,1082401,8659208,17318416,32505856,32505887]
def z2471 : List Nat := [8,31744,1015808,1082401,8659208,17318416,32505856,32506848]
def z2472 : List Nat := [8,31744,1015808,1082401,8659208,17318416,32505856,33553439]
def z2473 : List Nat := [8,31744,1015808,1082401,8659208,17318416,32505856,33554400]
def z2474 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,8659208]
def z2475 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856]
def z2476 : List Nat := [9,31,992,31744,1015808,1082401,2164802,4329604,17318416]
def z2477 : List Nat := [9,31,992,31744,1015808,1082401,2164802,8659208,17318416]
def z2478 : List Nat := [9,31,992,31744,1015808,1082401,8659208,17318416]
def z2479 : List Nat := [9,31,992,31744,1015808,1082401,8659208,17318416,32505856]
def z2480 : List Nat := [9,31,992,31744,1015808,2164802,4329604,8659208,17318416]
def z2481 : List Nat := [9,31,992,31744,1082401,2164802,4329604,8659208,32505856]
def z2482 : List Nat := [9,31,992,31744,1082401,2164802,4329604,17318416,32505856]
def z2483 : List Nat := [9,31,992,31744,1082401,2164802,8659208,17318416,32505856]
def z2484 : List Nat := [9,31,992,31744,1082401,8659208,17318416,32505856]
def z2485 : List Nat := [9,31,992,31744,2164802,4329604,8659208,17318416,32505856]
def z2486 : List Nat := [9,31,992,1082401,2164802,4329604,8659208,17318416,32505856]
def z2487 : List Nat := [9,31,992,1082401,2164802,4329604,8659208,32505856]
def z2488 : List Nat := [9,31,992,1082401,2164802,4329604,17318416,32505856]
def z2489 : List Nat := [9,31,992,1082401,2164802,8659208,17318416,32505856]
def z2490 : List Nat := [9,31,992,1082401,8659208,17318416,32505856]
def z2491 : List Nat := [9,31,992,2164802,4329604,8659208,17318416,32505856]
def z2492 : List Nat := [9,31,31744,1015808,1082401,2164802,4329604,8659208,32505856]
def z2493 : List Nat := [9,31,31744,1015808,1082401,2164802,4329604,17318416,32505856]
def z2494 : List Nat := [9,31,31744,1015808,1082401,2164802,8659208,17318416,32505856]
def z2495 : List Nat := [9,31,31744,1015808,1082401,8659208,17318416,32505856]
def z2496 : List Nat := [9,31,31744,1015808,2164802,4329604,8659208,17318416,32505856]
def z2497 : List Nat := [9,992,31744,1015808,1082401,2164802,4329604,8659208,32505856]
def z2498 : List Nat := [9,992,31744,1015808,1082401,2164802,4329604,17318416,32505856]
def z2499 : List Nat := [9,992,31744,1015808,1082401,2164802,8659208,17318416,32505856]
def z2500 : List Nat := [9,992,31744,1015808,1082401,8659208,17318416,32505856]
def z2501 : List Nat := [9,992,31744,1015808,2164802,4329604,8659208,17318416,32505856]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def T_ : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z0 .lf) z1 .lf) z2 (.nd .lf z3 .lf)) z4 (.nd (.nd (.nd .lf z5 .lf) z6 .lf) z7 (.nd .lf z8 .lf))) z9 (.nd (.nd (.nd (.nd .lf z10 .lf) z11 .lf) z12 (.nd .lf z13 .lf)) z14 (.nd (.nd (.nd .lf z15 .lf) z16 .lf) z17 (.nd .lf z18 .lf)))) z19 (.nd (.nd (.nd (.nd (.nd .lf z20 .lf) z21 .lf) z22 (.nd .lf z23 .lf)) z24 (.nd (.nd (.nd .lf z25 .lf) z26 .lf) z27 (.nd .lf z28 .lf))) z29 (.nd (.nd (.nd (.nd .lf z30 .lf) z31 .lf) z32 (.nd .lf z33 .lf)) z34 (.nd (.nd (.nd .lf z35 .lf) z36 .lf) z37 (.nd .lf z38 .lf))))) z39 (.nd (.nd (.nd (.nd (.nd (.nd .lf z40 .lf) z41 .lf) z42 (.nd .lf z43 .lf)) z44 (.nd (.nd (.nd .lf z45 .lf) z46 .lf) z47 (.nd .lf z48 .lf))) z49 (.nd (.nd (.nd (.nd .lf z50 .lf) z51 .lf) z52 (.nd .lf z53 .lf)) z54 (.nd (.nd (.nd .lf z55 .lf) z56 .lf) z57 (.nd .lf z58 .lf)))) z59 (.nd (.nd (.nd (.nd (.nd .lf z60 .lf) z61 .lf) z62 (.nd .lf z63 .lf)) z64 (.nd (.nd (.nd .lf z65 .lf) z66 .lf) z67 (.nd .lf z68 .lf))) z69 (.nd (.nd (.nd (.nd .lf z70 .lf) z71 .lf) z72 (.nd .lf z73 .lf)) z74 (.nd (.nd .lf z75 .lf) z76 (.nd .lf z77 .lf)))))) z78 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z79 .lf) z80 .lf) z81 (.nd .lf z82 .lf)) z83 (.nd (.nd (.nd .lf z84 .lf) z85 .lf) z86 (.nd .lf z87 .lf))) z88 (.nd (.nd (.nd (.nd .lf z89 .lf) z90 .lf) z91 (.nd .lf z92 .lf)) z93 (.nd (.nd (.nd .lf z94 .lf) z95 .lf) z96 (.nd .lf z97 .lf)))) z98 (.nd (.nd (.nd (.nd (.nd .lf z99 .lf) z100 .lf) z101 (.nd .lf z102 .lf)) z103 (.nd (.nd (.nd .lf z104 .lf) z105 .lf) z106 (.nd .lf z107 .lf))) z108 (.nd (.nd (.nd (.nd .lf z109 .lf) z110 .lf) z111 (.nd .lf z112 .lf)) z113 (.nd (.nd .lf z114 .lf) z115 (.nd .lf z116 .lf))))) z117 (.nd (.nd (.nd (.nd (.nd (.nd .lf z118 .lf) z119 .lf) z120 (.nd .lf z121 .lf)) z122 (.nd (.nd (.nd .lf z123 .lf) z124 .lf) z125 (.nd .lf z126 .lf))) z127 (.nd (.nd (.nd (.nd .lf z128 .lf) z129 .lf) z130 (.nd .lf z131 .lf)) z132 (.nd (.nd (.nd .lf z133 .lf) z134 .lf) z135 (.nd .lf z136 .lf)))) z137 (.nd (.nd (.nd (.nd (.nd .lf z138 .lf) z139 .lf) z140 (.nd .lf z141 .lf)) z142 (.nd (.nd (.nd .lf z143 .lf) z144 .lf) z145 (.nd .lf z146 .lf))) z147 (.nd (.nd (.nd (.nd .lf z148 .lf) z149 .lf) z150 (.nd .lf z151 .lf)) z152 (.nd (.nd .lf z153 .lf) z154 (.nd .lf z155 .lf))))))) z156 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z157 .lf) z158 .lf) z159 (.nd .lf z160 .lf)) z161 (.nd (.nd (.nd .lf z162 .lf) z163 .lf) z164 (.nd .lf z165 .lf))) z166 (.nd (.nd (.nd (.nd .lf z167 .lf) z168 .lf) z169 (.nd .lf z170 .lf)) z171 (.nd (.nd (.nd .lf z172 .lf) z173 .lf) z174 (.nd .lf z175 .lf)))) z176 (.nd (.nd (.nd (.nd (.nd .lf z177 .lf) z178 .lf) z179 (.nd .lf z180 .lf)) z181 (.nd (.nd (.nd .lf z182 .lf) z183 .lf) z184 (.nd .lf z185 .lf))) z186 (.nd (.nd (.nd (.nd .lf z187 .lf) z188 .lf) z189 (.nd .lf z190 .lf)) z191 (.nd (.nd .lf z192 .lf) z193 (.nd .lf z194 .lf))))) z195 (.nd (.nd (.nd (.nd (.nd (.nd .lf z196 .lf) z197 .lf) z198 (.nd .lf z199 .lf)) z200 (.nd (.nd (.nd .lf z201 .lf) z202 .lf) z203 (.nd .lf z204 .lf))) z205 (.nd (.nd (.nd (.nd .lf z206 .lf) z207 .lf) z208 (.nd .lf z209 .lf)) z210 (.nd (.nd (.nd .lf z211 .lf) z212 .lf) z213 (.nd .lf z214 .lf)))) z215 (.nd (.nd (.nd (.nd (.nd .lf z216 .lf) z217 .lf) z218 (.nd .lf z219 .lf)) z220 (.nd (.nd (.nd .lf z221 .lf) z222 .lf) z223 (.nd .lf z224 .lf))) z225 (.nd (.nd (.nd (.nd .lf z226 .lf) z227 .lf) z228 (.nd .lf z229 .lf)) z230 (.nd (.nd .lf z231 .lf) z232 (.nd .lf z233 .lf)))))) z234 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z235 .lf) z236 .lf) z237 (.nd .lf z238 .lf)) z239 (.nd (.nd (.nd .lf z240 .lf) z241 .lf) z242 (.nd .lf z243 .lf))) z244 (.nd (.nd (.nd (.nd .lf z245 .lf) z246 .lf) z247 (.nd .lf z248 .lf)) z249 (.nd (.nd (.nd .lf z250 .lf) z251 .lf) z252 (.nd .lf z253 .lf)))) z254 (.nd (.nd (.nd (.nd (.nd .lf z255 .lf) z256 .lf) z257 (.nd .lf z258 .lf)) z259 (.nd (.nd (.nd .lf z260 .lf) z261 .lf) z262 (.nd .lf z263 .lf))) z264 (.nd (.nd (.nd (.nd .lf z265 .lf) z266 .lf) z267 (.nd .lf z268 .lf)) z269 (.nd (.nd .lf z270 .lf) z271 (.nd .lf z272 .lf))))) z273 (.nd (.nd (.nd (.nd (.nd (.nd .lf z274 .lf) z275 .lf) z276 (.nd .lf z277 .lf)) z278 (.nd (.nd (.nd .lf z279 .lf) z280 .lf) z281 (.nd .lf z282 .lf))) z283 (.nd (.nd (.nd (.nd .lf z284 .lf) z285 .lf) z286 (.nd .lf z287 .lf)) z288 (.nd (.nd (.nd .lf z289 .lf) z290 .lf) z291 (.nd .lf z292 .lf)))) z293 (.nd (.nd (.nd (.nd (.nd .lf z294 .lf) z295 .lf) z296 (.nd .lf z297 .lf)) z298 (.nd (.nd (.nd .lf z299 .lf) z300 .lf) z301 (.nd .lf z302 .lf))) z303 (.nd (.nd (.nd (.nd .lf z304 .lf) z305 .lf) z306 (.nd .lf z307 .lf)) z308 (.nd (.nd .lf z309 .lf) z310 (.nd .lf z311 .lf)))))))) z312 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z313 .lf) z314 .lf) z315 (.nd .lf z316 .lf)) z317 (.nd (.nd (.nd .lf z318 .lf) z319 .lf) z320 (.nd .lf z321 .lf))) z322 (.nd (.nd (.nd (.nd .lf z323 .lf) z324 .lf) z325 (.nd .lf z326 .lf)) z327 (.nd (.nd (.nd .lf z328 .lf) z329 .lf) z330 (.nd .lf z331 .lf)))) z332 (.nd (.nd (.nd (.nd (.nd .lf z333 .lf) z334 .lf) z335 (.nd .lf z336 .lf)) z337 (.nd (.nd (.nd .lf z338 .lf) z339 .lf) z340 (.nd .lf z341 .lf))) z342 (.nd (.nd (.nd (.nd .lf z343 .lf) z344 .lf) z345 (.nd .lf z346 .lf)) z347 (.nd (.nd (.nd .lf z348 .lf) z349 .lf) z350 (.nd .lf z351 .lf))))) z352 (.nd (.nd (.nd (.nd (.nd (.nd .lf z353 .lf) z354 .lf) z355 (.nd .lf z356 .lf)) z357 (.nd (.nd (.nd .lf z358 .lf) z359 .lf) z360 (.nd .lf z361 .lf))) z362 (.nd (.nd (.nd (.nd .lf z363 .lf) z364 .lf) z365 (.nd .lf z366 .lf)) z367 (.nd (.nd (.nd .lf z368 .lf) z369 .lf) z370 (.nd .lf z371 .lf)))) z372 (.nd (.nd (.nd (.nd (.nd .lf z373 .lf) z374 .lf) z375 (.nd .lf z376 .lf)) z377 (.nd (.nd (.nd .lf z378 .lf) z379 .lf) z380 (.nd .lf z381 .lf))) z382 (.nd (.nd (.nd (.nd .lf z383 .lf) z384 .lf) z385 (.nd .lf z386 .lf)) z387 (.nd (.nd .lf z388 .lf) z389 (.nd .lf z390 .lf)))))) z391 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z392 .lf) z393 .lf) z394 (.nd .lf z395 .lf)) z396 (.nd (.nd (.nd .lf z397 .lf) z398 .lf) z399 (.nd .lf z400 .lf))) z401 (.nd (.nd (.nd (.nd .lf z402 .lf) z403 .lf) z404 (.nd .lf z405 .lf)) z406 (.nd (.nd (.nd .lf z407 .lf) z408 .lf) z409 (.nd .lf z410 .lf)))) z411 (.nd (.nd (.nd (.nd (.nd .lf z412 .lf) z413 .lf) z414 (.nd .lf z415 .lf)) z416 (.nd (.nd (.nd .lf z417 .lf) z418 .lf) z419 (.nd .lf z420 .lf))) z421 (.nd (.nd (.nd (.nd .lf z422 .lf) z423 .lf) z424 (.nd .lf z425 .lf)) z426 (.nd (.nd .lf z427 .lf) z428 (.nd .lf z429 .lf))))) z430 (.nd (.nd (.nd (.nd (.nd (.nd .lf z431 .lf) z432 .lf) z433 (.nd .lf z434 .lf)) z435 (.nd (.nd (.nd .lf z436 .lf) z437 .lf) z438 (.nd .lf z439 .lf))) z440 (.nd (.nd (.nd (.nd .lf z441 .lf) z442 .lf) z443 (.nd .lf z444 .lf)) z445 (.nd (.nd (.nd .lf z446 .lf) z447 .lf) z448 (.nd .lf z449 .lf)))) z450 (.nd (.nd (.nd (.nd (.nd .lf z451 .lf) z452 .lf) z453 (.nd .lf z454 .lf)) z455 (.nd (.nd (.nd .lf z456 .lf) z457 .lf) z458 (.nd .lf z459 .lf))) z460 (.nd (.nd (.nd (.nd .lf z461 .lf) z462 .lf) z463 (.nd .lf z464 .lf)) z465 (.nd (.nd .lf z466 .lf) z467 (.nd .lf z468 .lf))))))) z469 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z470 .lf) z471 .lf) z472 (.nd .lf z473 .lf)) z474 (.nd (.nd (.nd .lf z475 .lf) z476 .lf) z477 (.nd .lf z478 .lf))) z479 (.nd (.nd (.nd (.nd .lf z480 .lf) z481 .lf) z482 (.nd .lf z483 .lf)) z484 (.nd (.nd (.nd .lf z485 .lf) z486 .lf) z487 (.nd .lf z488 .lf)))) z489 (.nd (.nd (.nd (.nd (.nd .lf z490 .lf) z491 .lf) z492 (.nd .lf z493 .lf)) z494 (.nd (.nd (.nd .lf z495 .lf) z496 .lf) z497 (.nd .lf z498 .lf))) z499 (.nd (.nd (.nd (.nd .lf z500 .lf) z501 .lf) z502 (.nd .lf z503 .lf)) z504 (.nd (.nd .lf z505 .lf) z506 (.nd .lf z507 .lf))))) z508 (.nd (.nd (.nd (.nd (.nd (.nd .lf z509 .lf) z510 .lf) z511 (.nd .lf z512 .lf)) z513 (.nd (.nd (.nd .lf z514 .lf) z515 .lf) z516 (.nd .lf z517 .lf))) z518 (.nd (.nd (.nd (.nd .lf z519 .lf) z520 .lf) z521 (.nd .lf z522 .lf)) z523 (.nd (.nd (.nd .lf z524 .lf) z525 .lf) z526 (.nd .lf z527 .lf)))) z528 (.nd (.nd (.nd (.nd (.nd .lf z529 .lf) z530 .lf) z531 (.nd .lf z532 .lf)) z533 (.nd (.nd (.nd .lf z534 .lf) z535 .lf) z536 (.nd .lf z537 .lf))) z538 (.nd (.nd (.nd (.nd .lf z539 .lf) z540 .lf) z541 (.nd .lf z542 .lf)) z543 (.nd (.nd .lf z544 .lf) z545 (.nd .lf z546 .lf)))))) z547 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z548 .lf) z549 .lf) z550 (.nd .lf z551 .lf)) z552 (.nd (.nd (.nd .lf z553 .lf) z554 .lf) z555 (.nd .lf z556 .lf))) z557 (.nd (.nd (.nd (.nd .lf z558 .lf) z559 .lf) z560 (.nd .lf z561 .lf)) z562 (.nd (.nd (.nd .lf z563 .lf) z564 .lf) z565 (.nd .lf z566 .lf)))) z567 (.nd (.nd (.nd (.nd (.nd .lf z568 .lf) z569 .lf) z570 (.nd .lf z571 .lf)) z572 (.nd (.nd (.nd .lf z573 .lf) z574 .lf) z575 (.nd .lf z576 .lf))) z577 (.nd (.nd (.nd (.nd .lf z578 .lf) z579 .lf) z580 (.nd .lf z581 .lf)) z582 (.nd (.nd .lf z583 .lf) z584 (.nd .lf z585 .lf))))) z586 (.nd (.nd (.nd (.nd (.nd (.nd .lf z587 .lf) z588 .lf) z589 (.nd .lf z590 .lf)) z591 (.nd (.nd (.nd .lf z592 .lf) z593 .lf) z594 (.nd .lf z595 .lf))) z596 (.nd (.nd (.nd (.nd .lf z597 .lf) z598 .lf) z599 (.nd .lf z600 .lf)) z601 (.nd (.nd (.nd .lf z602 .lf) z603 .lf) z604 (.nd .lf z605 .lf)))) z606 (.nd (.nd (.nd (.nd (.nd .lf z607 .lf) z608 .lf) z609 (.nd .lf z610 .lf)) z611 (.nd (.nd (.nd .lf z612 .lf) z613 .lf) z614 (.nd .lf z615 .lf))) z616 (.nd (.nd (.nd (.nd .lf z617 .lf) z618 .lf) z619 (.nd .lf z620 .lf)) z621 (.nd (.nd .lf z622 .lf) z623 (.nd .lf z624 .lf))))))))) z625 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z626 .lf) z627 .lf) z628 (.nd .lf z629 .lf)) z630 (.nd (.nd (.nd .lf z631 .lf) z632 .lf) z633 (.nd .lf z634 .lf))) z635 (.nd (.nd (.nd (.nd .lf z636 .lf) z637 .lf) z638 (.nd .lf z639 .lf)) z640 (.nd (.nd (.nd .lf z641 .lf) z642 .lf) z643 (.nd .lf z644 .lf)))) z645 (.nd (.nd (.nd (.nd (.nd .lf z646 .lf) z647 .lf) z648 (.nd .lf z649 .lf)) z650 (.nd (.nd (.nd .lf z651 .lf) z652 .lf) z653 (.nd .lf z654 .lf))) z655 (.nd (.nd (.nd (.nd .lf z656 .lf) z657 .lf) z658 (.nd .lf z659 .lf)) z660 (.nd (.nd (.nd .lf z661 .lf) z662 .lf) z663 (.nd .lf z664 .lf))))) z665 (.nd (.nd (.nd (.nd (.nd (.nd .lf z666 .lf) z667 .lf) z668 (.nd .lf z669 .lf)) z670 (.nd (.nd (.nd .lf z671 .lf) z672 .lf) z673 (.nd .lf z674 .lf))) z675 (.nd (.nd (.nd (.nd .lf z676 .lf) z677 .lf) z678 (.nd .lf z679 .lf)) z680 (.nd (.nd (.nd .lf z681 .lf) z682 .lf) z683 (.nd .lf z684 .lf)))) z685 (.nd (.nd (.nd (.nd (.nd .lf z686 .lf) z687 .lf) z688 (.nd .lf z689 .lf)) z690 (.nd (.nd (.nd .lf z691 .lf) z692 .lf) z693 (.nd .lf z694 .lf))) z695 (.nd (.nd (.nd (.nd .lf z696 .lf) z697 .lf) z698 (.nd .lf z699 .lf)) z700 (.nd (.nd .lf z701 .lf) z702 (.nd .lf z703 .lf)))))) z704 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z705 .lf) z706 .lf) z707 (.nd .lf z708 .lf)) z709 (.nd (.nd (.nd .lf z710 .lf) z711 .lf) z712 (.nd .lf z713 .lf))) z714 (.nd (.nd (.nd (.nd .lf z715 .lf) z716 .lf) z717 (.nd .lf z718 .lf)) z719 (.nd (.nd (.nd .lf z720 .lf) z721 .lf) z722 (.nd .lf z723 .lf)))) z724 (.nd (.nd (.nd (.nd (.nd .lf z725 .lf) z726 .lf) z727 (.nd .lf z728 .lf)) z729 (.nd (.nd (.nd .lf z730 .lf) z731 .lf) z732 (.nd .lf z733 .lf))) z734 (.nd (.nd (.nd (.nd .lf z735 .lf) z736 .lf) z737 (.nd .lf z738 .lf)) z739 (.nd (.nd .lf z740 .lf) z741 (.nd .lf z742 .lf))))) z743 (.nd (.nd (.nd (.nd (.nd (.nd .lf z744 .lf) z745 .lf) z746 (.nd .lf z747 .lf)) z748 (.nd (.nd (.nd .lf z749 .lf) z750 .lf) z751 (.nd .lf z752 .lf))) z753 (.nd (.nd (.nd (.nd .lf z754 .lf) z755 .lf) z756 (.nd .lf z757 .lf)) z758 (.nd (.nd (.nd .lf z759 .lf) z760 .lf) z761 (.nd .lf z762 .lf)))) z763 (.nd (.nd (.nd (.nd (.nd .lf z764 .lf) z765 .lf) z766 (.nd .lf z767 .lf)) z768 (.nd (.nd (.nd .lf z769 .lf) z770 .lf) z771 (.nd .lf z772 .lf))) z773 (.nd (.nd (.nd (.nd .lf z774 .lf) z775 .lf) z776 (.nd .lf z777 .lf)) z778 (.nd (.nd .lf z779 .lf) z780 (.nd .lf z781 .lf))))))) z782 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z783 .lf) z784 .lf) z785 (.nd .lf z786 .lf)) z787 (.nd (.nd (.nd .lf z788 .lf) z789 .lf) z790 (.nd .lf z791 .lf))) z792 (.nd (.nd (.nd (.nd .lf z793 .lf) z794 .lf) z795 (.nd .lf z796 .lf)) z797 (.nd (.nd (.nd .lf z798 .lf) z799 .lf) z800 (.nd .lf z801 .lf)))) z802 (.nd (.nd (.nd (.nd (.nd .lf z803 .lf) z804 .lf) z805 (.nd .lf z806 .lf)) z807 (.nd (.nd (.nd .lf z808 .lf) z809 .lf) z810 (.nd .lf z811 .lf))) z812 (.nd (.nd (.nd (.nd .lf z813 .lf) z814 .lf) z815 (.nd .lf z816 .lf)) z817 (.nd (.nd .lf z818 .lf) z819 (.nd .lf z820 .lf))))) z821 (.nd (.nd (.nd (.nd (.nd (.nd .lf z822 .lf) z823 .lf) z824 (.nd .lf z825 .lf)) z826 (.nd (.nd (.nd .lf z827 .lf) z828 .lf) z829 (.nd .lf z830 .lf))) z831 (.nd (.nd (.nd (.nd .lf z832 .lf) z833 .lf) z834 (.nd .lf z835 .lf)) z836 (.nd (.nd (.nd .lf z837 .lf) z838 .lf) z839 (.nd .lf z840 .lf)))) z841 (.nd (.nd (.nd (.nd (.nd .lf z842 .lf) z843 .lf) z844 (.nd .lf z845 .lf)) z846 (.nd (.nd (.nd .lf z847 .lf) z848 .lf) z849 (.nd .lf z850 .lf))) z851 (.nd (.nd (.nd (.nd .lf z852 .lf) z853 .lf) z854 (.nd .lf z855 .lf)) z856 (.nd (.nd .lf z857 .lf) z858 (.nd .lf z859 .lf)))))) z860 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z861 .lf) z862 .lf) z863 (.nd .lf z864 .lf)) z865 (.nd (.nd (.nd .lf z866 .lf) z867 .lf) z868 (.nd .lf z869 .lf))) z870 (.nd (.nd (.nd (.nd .lf z871 .lf) z872 .lf) z873 (.nd .lf z874 .lf)) z875 (.nd (.nd (.nd .lf z876 .lf) z877 .lf) z878 (.nd .lf z879 .lf)))) z880 (.nd (.nd (.nd (.nd (.nd .lf z881 .lf) z882 .lf) z883 (.nd .lf z884 .lf)) z885 (.nd (.nd (.nd .lf z886 .lf) z887 .lf) z888 (.nd .lf z889 .lf))) z890 (.nd (.nd (.nd (.nd .lf z891 .lf) z892 .lf) z893 (.nd .lf z894 .lf)) z895 (.nd (.nd .lf z896 .lf) z897 (.nd .lf z898 .lf))))) z899 (.nd (.nd (.nd (.nd (.nd (.nd .lf z900 .lf) z901 .lf) z902 (.nd .lf z903 .lf)) z904 (.nd (.nd (.nd .lf z905 .lf) z906 .lf) z907 (.nd .lf z908 .lf))) z909 (.nd (.nd (.nd (.nd .lf z910 .lf) z911 .lf) z912 (.nd .lf z913 .lf)) z914 (.nd (.nd (.nd .lf z915 .lf) z916 .lf) z917 (.nd .lf z918 .lf)))) z919 (.nd (.nd (.nd (.nd (.nd .lf z920 .lf) z921 .lf) z922 (.nd .lf z923 .lf)) z924 (.nd (.nd (.nd .lf z925 .lf) z926 .lf) z927 (.nd .lf z928 .lf))) z929 (.nd (.nd (.nd (.nd .lf z930 .lf) z931 .lf) z932 (.nd .lf z933 .lf)) z934 (.nd (.nd .lf z935 .lf) z936 (.nd .lf z937 .lf)))))))) z938 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z939 .lf) z940 .lf) z941 (.nd .lf z942 .lf)) z943 (.nd (.nd (.nd .lf z944 .lf) z945 .lf) z946 (.nd .lf z947 .lf))) z948 (.nd (.nd (.nd (.nd .lf z949 .lf) z950 .lf) z951 (.nd .lf z952 .lf)) z953 (.nd (.nd (.nd .lf z954 .lf) z955 .lf) z956 (.nd .lf z957 .lf)))) z958 (.nd (.nd (.nd (.nd (.nd .lf z959 .lf) z960 .lf) z961 (.nd .lf z962 .lf)) z963 (.nd (.nd (.nd .lf z964 .lf) z965 .lf) z966 (.nd .lf z967 .lf))) z968 (.nd (.nd (.nd (.nd .lf z969 .lf) z970 .lf) z971 (.nd .lf z972 .lf)) z973 (.nd (.nd (.nd .lf z974 .lf) z975 .lf) z976 (.nd .lf z977 .lf))))) z978 (.nd (.nd (.nd (.nd (.nd (.nd .lf z979 .lf) z980 .lf) z981 (.nd .lf z982 .lf)) z983 (.nd (.nd (.nd .lf z984 .lf) z985 .lf) z986 (.nd .lf z987 .lf))) z988 (.nd (.nd (.nd (.nd .lf z989 .lf) z990 .lf) z991 (.nd .lf z992 .lf)) z993 (.nd (.nd (.nd .lf z994 .lf) z995 .lf) z996 (.nd .lf z997 .lf)))) z998 (.nd (.nd (.nd (.nd (.nd .lf z999 .lf) z1000 .lf) z1001 (.nd .lf z1002 .lf)) z1003 (.nd (.nd (.nd .lf z1004 .lf) z1005 .lf) z1006 (.nd .lf z1007 .lf))) z1008 (.nd (.nd (.nd (.nd .lf z1009 .lf) z1010 .lf) z1011 (.nd .lf z1012 .lf)) z1013 (.nd (.nd .lf z1014 .lf) z1015 (.nd .lf z1016 .lf)))))) z1017 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1018 .lf) z1019 .lf) z1020 (.nd .lf z1021 .lf)) z1022 (.nd (.nd (.nd .lf z1023 .lf) z1024 .lf) z1025 (.nd .lf z1026 .lf))) z1027 (.nd (.nd (.nd (.nd .lf z1028 .lf) z1029 .lf) z1030 (.nd .lf z1031 .lf)) z1032 (.nd (.nd (.nd .lf z1033 .lf) z1034 .lf) z1035 (.nd .lf z1036 .lf)))) z1037 (.nd (.nd (.nd (.nd (.nd .lf z1038 .lf) z1039 .lf) z1040 (.nd .lf z1041 .lf)) z1042 (.nd (.nd (.nd .lf z1043 .lf) z1044 .lf) z1045 (.nd .lf z1046 .lf))) z1047 (.nd (.nd (.nd (.nd .lf z1048 .lf) z1049 .lf) z1050 (.nd .lf z1051 .lf)) z1052 (.nd (.nd .lf z1053 .lf) z1054 (.nd .lf z1055 .lf))))) z1056 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1057 .lf) z1058 .lf) z1059 (.nd .lf z1060 .lf)) z1061 (.nd (.nd (.nd .lf z1062 .lf) z1063 .lf) z1064 (.nd .lf z1065 .lf))) z1066 (.nd (.nd (.nd (.nd .lf z1067 .lf) z1068 .lf) z1069 (.nd .lf z1070 .lf)) z1071 (.nd (.nd (.nd .lf z1072 .lf) z1073 .lf) z1074 (.nd .lf z1075 .lf)))) z1076 (.nd (.nd (.nd (.nd (.nd .lf z1077 .lf) z1078 .lf) z1079 (.nd .lf z1080 .lf)) z1081 (.nd (.nd (.nd .lf z1082 .lf) z1083 .lf) z1084 (.nd .lf z1085 .lf))) z1086 (.nd (.nd (.nd (.nd .lf z1087 .lf) z1088 .lf) z1089 (.nd .lf z1090 .lf)) z1091 (.nd (.nd .lf z1092 .lf) z1093 (.nd .lf z1094 .lf))))))) z1095 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1096 .lf) z1097 .lf) z1098 (.nd .lf z1099 .lf)) z1100 (.nd (.nd (.nd .lf z1101 .lf) z1102 .lf) z1103 (.nd .lf z1104 .lf))) z1105 (.nd (.nd (.nd (.nd .lf z1106 .lf) z1107 .lf) z1108 (.nd .lf z1109 .lf)) z1110 (.nd (.nd (.nd .lf z1111 .lf) z1112 .lf) z1113 (.nd .lf z1114 .lf)))) z1115 (.nd (.nd (.nd (.nd (.nd .lf z1116 .lf) z1117 .lf) z1118 (.nd .lf z1119 .lf)) z1120 (.nd (.nd (.nd .lf z1121 .lf) z1122 .lf) z1123 (.nd .lf z1124 .lf))) z1125 (.nd (.nd (.nd (.nd .lf z1126 .lf) z1127 .lf) z1128 (.nd .lf z1129 .lf)) z1130 (.nd (.nd .lf z1131 .lf) z1132 (.nd .lf z1133 .lf))))) z1134 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1135 .lf) z1136 .lf) z1137 (.nd .lf z1138 .lf)) z1139 (.nd (.nd (.nd .lf z1140 .lf) z1141 .lf) z1142 (.nd .lf z1143 .lf))) z1144 (.nd (.nd (.nd (.nd .lf z1145 .lf) z1146 .lf) z1147 (.nd .lf z1148 .lf)) z1149 (.nd (.nd (.nd .lf z1150 .lf) z1151 .lf) z1152 (.nd .lf z1153 .lf)))) z1154 (.nd (.nd (.nd (.nd (.nd .lf z1155 .lf) z1156 .lf) z1157 (.nd .lf z1158 .lf)) z1159 (.nd (.nd (.nd .lf z1160 .lf) z1161 .lf) z1162 (.nd .lf z1163 .lf))) z1164 (.nd (.nd (.nd (.nd .lf z1165 .lf) z1166 .lf) z1167 (.nd .lf z1168 .lf)) z1169 (.nd (.nd .lf z1170 .lf) z1171 (.nd .lf z1172 .lf)))))) z1173 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1174 .lf) z1175 .lf) z1176 (.nd .lf z1177 .lf)) z1178 (.nd (.nd (.nd .lf z1179 .lf) z1180 .lf) z1181 (.nd .lf z1182 .lf))) z1183 (.nd (.nd (.nd (.nd .lf z1184 .lf) z1185 .lf) z1186 (.nd .lf z1187 .lf)) z1188 (.nd (.nd (.nd .lf z1189 .lf) z1190 .lf) z1191 (.nd .lf z1192 .lf)))) z1193 (.nd (.nd (.nd (.nd (.nd .lf z1194 .lf) z1195 .lf) z1196 (.nd .lf z1197 .lf)) z1198 (.nd (.nd (.nd .lf z1199 .lf) z1200 .lf) z1201 (.nd .lf z1202 .lf))) z1203 (.nd (.nd (.nd (.nd .lf z1204 .lf) z1205 .lf) z1206 (.nd .lf z1207 .lf)) z1208 (.nd (.nd .lf z1209 .lf) z1210 (.nd .lf z1211 .lf))))) z1212 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1213 .lf) z1214 .lf) z1215 (.nd .lf z1216 .lf)) z1217 (.nd (.nd (.nd .lf z1218 .lf) z1219 .lf) z1220 (.nd .lf z1221 .lf))) z1222 (.nd (.nd (.nd (.nd .lf z1223 .lf) z1224 .lf) z1225 (.nd .lf z1226 .lf)) z1227 (.nd (.nd (.nd .lf z1228 .lf) z1229 .lf) z1230 (.nd .lf z1231 .lf)))) z1232 (.nd (.nd (.nd (.nd (.nd .lf z1233 .lf) z1234 .lf) z1235 (.nd .lf z1236 .lf)) z1237 (.nd (.nd (.nd .lf z1238 .lf) z1239 .lf) z1240 (.nd .lf z1241 .lf))) z1242 (.nd (.nd (.nd (.nd .lf z1243 .lf) z1244 .lf) z1245 (.nd .lf z1246 .lf)) z1247 (.nd (.nd .lf z1248 .lf) z1249 (.nd .lf z1250 .lf)))))))))) z1251 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1252 .lf) z1253 .lf) z1254 (.nd .lf z1255 .lf)) z1256 (.nd (.nd (.nd .lf z1257 .lf) z1258 .lf) z1259 (.nd .lf z1260 .lf))) z1261 (.nd (.nd (.nd (.nd .lf z1262 .lf) z1263 .lf) z1264 (.nd .lf z1265 .lf)) z1266 (.nd (.nd (.nd .lf z1267 .lf) z1268 .lf) z1269 (.nd .lf z1270 .lf)))) z1271 (.nd (.nd (.nd (.nd (.nd .lf z1272 .lf) z1273 .lf) z1274 (.nd .lf z1275 .lf)) z1276 (.nd (.nd (.nd .lf z1277 .lf) z1278 .lf) z1279 (.nd .lf z1280 .lf))) z1281 (.nd (.nd (.nd (.nd .lf z1282 .lf) z1283 .lf) z1284 (.nd .lf z1285 .lf)) z1286 (.nd (.nd (.nd .lf z1287 .lf) z1288 .lf) z1289 (.nd .lf z1290 .lf))))) z1291 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1292 .lf) z1293 .lf) z1294 (.nd .lf z1295 .lf)) z1296 (.nd (.nd (.nd .lf z1297 .lf) z1298 .lf) z1299 (.nd .lf z1300 .lf))) z1301 (.nd (.nd (.nd (.nd .lf z1302 .lf) z1303 .lf) z1304 (.nd .lf z1305 .lf)) z1306 (.nd (.nd (.nd .lf z1307 .lf) z1308 .lf) z1309 (.nd .lf z1310 .lf)))) z1311 (.nd (.nd (.nd (.nd (.nd .lf z1312 .lf) z1313 .lf) z1314 (.nd .lf z1315 .lf)) z1316 (.nd (.nd (.nd .lf z1317 .lf) z1318 .lf) z1319 (.nd .lf z1320 .lf))) z1321 (.nd (.nd (.nd (.nd .lf z1322 .lf) z1323 .lf) z1324 (.nd .lf z1325 .lf)) z1326 (.nd (.nd .lf z1327 .lf) z1328 (.nd .lf z1329 .lf)))))) z1330 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1331 .lf) z1332 .lf) z1333 (.nd .lf z1334 .lf)) z1335 (.nd (.nd (.nd .lf z1336 .lf) z1337 .lf) z1338 (.nd .lf z1339 .lf))) z1340 (.nd (.nd (.nd (.nd .lf z1341 .lf) z1342 .lf) z1343 (.nd .lf z1344 .lf)) z1345 (.nd (.nd (.nd .lf z1346 .lf) z1347 .lf) z1348 (.nd .lf z1349 .lf)))) z1350 (.nd (.nd (.nd (.nd (.nd .lf z1351 .lf) z1352 .lf) z1353 (.nd .lf z1354 .lf)) z1355 (.nd (.nd (.nd .lf z1356 .lf) z1357 .lf) z1358 (.nd .lf z1359 .lf))) z1360 (.nd (.nd (.nd (.nd .lf z1361 .lf) z1362 .lf) z1363 (.nd .lf z1364 .lf)) z1365 (.nd (.nd .lf z1366 .lf) z1367 (.nd .lf z1368 .lf))))) z1369 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1370 .lf) z1371 .lf) z1372 (.nd .lf z1373 .lf)) z1374 (.nd (.nd (.nd .lf z1375 .lf) z1376 .lf) z1377 (.nd .lf z1378 .lf))) z1379 (.nd (.nd (.nd (.nd .lf z1380 .lf) z1381 .lf) z1382 (.nd .lf z1383 .lf)) z1384 (.nd (.nd (.nd .lf z1385 .lf) z1386 .lf) z1387 (.nd .lf z1388 .lf)))) z1389 (.nd (.nd (.nd (.nd (.nd .lf z1390 .lf) z1391 .lf) z1392 (.nd .lf z1393 .lf)) z1394 (.nd (.nd (.nd .lf z1395 .lf) z1396 .lf) z1397 (.nd .lf z1398 .lf))) z1399 (.nd (.nd (.nd (.nd .lf z1400 .lf) z1401 .lf) z1402 (.nd .lf z1403 .lf)) z1404 (.nd (.nd .lf z1405 .lf) z1406 (.nd .lf z1407 .lf))))))) z1408 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1409 .lf) z1410 .lf) z1411 (.nd .lf z1412 .lf)) z1413 (.nd (.nd (.nd .lf z1414 .lf) z1415 .lf) z1416 (.nd .lf z1417 .lf))) z1418 (.nd (.nd (.nd (.nd .lf z1419 .lf) z1420 .lf) z1421 (.nd .lf z1422 .lf)) z1423 (.nd (.nd (.nd .lf z1424 .lf) z1425 .lf) z1426 (.nd .lf z1427 .lf)))) z1428 (.nd (.nd (.nd (.nd (.nd .lf z1429 .lf) z1430 .lf) z1431 (.nd .lf z1432 .lf)) z1433 (.nd (.nd (.nd .lf z1434 .lf) z1435 .lf) z1436 (.nd .lf z1437 .lf))) z1438 (.nd (.nd (.nd (.nd .lf z1439 .lf) z1440 .lf) z1441 (.nd .lf z1442 .lf)) z1443 (.nd (.nd .lf z1444 .lf) z1445 (.nd .lf z1446 .lf))))) z1447 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1448 .lf) z1449 .lf) z1450 (.nd .lf z1451 .lf)) z1452 (.nd (.nd (.nd .lf z1453 .lf) z1454 .lf) z1455 (.nd .lf z1456 .lf))) z1457 (.nd (.nd (.nd (.nd .lf z1458 .lf) z1459 .lf) z1460 (.nd .lf z1461 .lf)) z1462 (.nd (.nd (.nd .lf z1463 .lf) z1464 .lf) z1465 (.nd .lf z1466 .lf)))) z1467 (.nd (.nd (.nd (.nd (.nd .lf z1468 .lf) z1469 .lf) z1470 (.nd .lf z1471 .lf)) z1472 (.nd (.nd (.nd .lf z1473 .lf) z1474 .lf) z1475 (.nd .lf z1476 .lf))) z1477 (.nd (.nd (.nd (.nd .lf z1478 .lf) z1479 .lf) z1480 (.nd .lf z1481 .lf)) z1482 (.nd (.nd .lf z1483 .lf) z1484 (.nd .lf z1485 .lf)))))) z1486 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1487 .lf) z1488 .lf) z1489 (.nd .lf z1490 .lf)) z1491 (.nd (.nd (.nd .lf z1492 .lf) z1493 .lf) z1494 (.nd .lf z1495 .lf))) z1496 (.nd (.nd (.nd (.nd .lf z1497 .lf) z1498 .lf) z1499 (.nd .lf z1500 .lf)) z1501 (.nd (.nd (.nd .lf z1502 .lf) z1503 .lf) z1504 (.nd .lf z1505 .lf)))) z1506 (.nd (.nd (.nd (.nd (.nd .lf z1507 .lf) z1508 .lf) z1509 (.nd .lf z1510 .lf)) z1511 (.nd (.nd (.nd .lf z1512 .lf) z1513 .lf) z1514 (.nd .lf z1515 .lf))) z1516 (.nd (.nd (.nd (.nd .lf z1517 .lf) z1518 .lf) z1519 (.nd .lf z1520 .lf)) z1521 (.nd (.nd .lf z1522 .lf) z1523 (.nd .lf z1524 .lf))))) z1525 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1526 .lf) z1527 .lf) z1528 (.nd .lf z1529 .lf)) z1530 (.nd (.nd (.nd .lf z1531 .lf) z1532 .lf) z1533 (.nd .lf z1534 .lf))) z1535 (.nd (.nd (.nd (.nd .lf z1536 .lf) z1537 .lf) z1538 (.nd .lf z1539 .lf)) z1540 (.nd (.nd (.nd .lf z1541 .lf) z1542 .lf) z1543 (.nd .lf z1544 .lf)))) z1545 (.nd (.nd (.nd (.nd (.nd .lf z1546 .lf) z1547 .lf) z1548 (.nd .lf z1549 .lf)) z1550 (.nd (.nd (.nd .lf z1551 .lf) z1552 .lf) z1553 (.nd .lf z1554 .lf))) z1555 (.nd (.nd (.nd (.nd .lf z1556 .lf) z1557 .lf) z1558 (.nd .lf z1559 .lf)) z1560 (.nd (.nd .lf z1561 .lf) z1562 (.nd .lf z1563 .lf)))))))) z1564 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1565 .lf) z1566 .lf) z1567 (.nd .lf z1568 .lf)) z1569 (.nd (.nd (.nd .lf z1570 .lf) z1571 .lf) z1572 (.nd .lf z1573 .lf))) z1574 (.nd (.nd (.nd (.nd .lf z1575 .lf) z1576 .lf) z1577 (.nd .lf z1578 .lf)) z1579 (.nd (.nd (.nd .lf z1580 .lf) z1581 .lf) z1582 (.nd .lf z1583 .lf)))) z1584 (.nd (.nd (.nd (.nd (.nd .lf z1585 .lf) z1586 .lf) z1587 (.nd .lf z1588 .lf)) z1589 (.nd (.nd (.nd .lf z1590 .lf) z1591 .lf) z1592 (.nd .lf z1593 .lf))) z1594 (.nd (.nd (.nd (.nd .lf z1595 .lf) z1596 .lf) z1597 (.nd .lf z1598 .lf)) z1599 (.nd (.nd (.nd .lf z1600 .lf) z1601 .lf) z1602 (.nd .lf z1603 .lf))))) z1604 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1605 .lf) z1606 .lf) z1607 (.nd .lf z1608 .lf)) z1609 (.nd (.nd (.nd .lf z1610 .lf) z1611 .lf) z1612 (.nd .lf z1613 .lf))) z1614 (.nd (.nd (.nd (.nd .lf z1615 .lf) z1616 .lf) z1617 (.nd .lf z1618 .lf)) z1619 (.nd (.nd (.nd .lf z1620 .lf) z1621 .lf) z1622 (.nd .lf z1623 .lf)))) z1624 (.nd (.nd (.nd (.nd (.nd .lf z1625 .lf) z1626 .lf) z1627 (.nd .lf z1628 .lf)) z1629 (.nd (.nd (.nd .lf z1630 .lf) z1631 .lf) z1632 (.nd .lf z1633 .lf))) z1634 (.nd (.nd (.nd (.nd .lf z1635 .lf) z1636 .lf) z1637 (.nd .lf z1638 .lf)) z1639 (.nd (.nd .lf z1640 .lf) z1641 (.nd .lf z1642 .lf)))))) z1643 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1644 .lf) z1645 .lf) z1646 (.nd .lf z1647 .lf)) z1648 (.nd (.nd (.nd .lf z1649 .lf) z1650 .lf) z1651 (.nd .lf z1652 .lf))) z1653 (.nd (.nd (.nd (.nd .lf z1654 .lf) z1655 .lf) z1656 (.nd .lf z1657 .lf)) z1658 (.nd (.nd (.nd .lf z1659 .lf) z1660 .lf) z1661 (.nd .lf z1662 .lf)))) z1663 (.nd (.nd (.nd (.nd (.nd .lf z1664 .lf) z1665 .lf) z1666 (.nd .lf z1667 .lf)) z1668 (.nd (.nd (.nd .lf z1669 .lf) z1670 .lf) z1671 (.nd .lf z1672 .lf))) z1673 (.nd (.nd (.nd (.nd .lf z1674 .lf) z1675 .lf) z1676 (.nd .lf z1677 .lf)) z1678 (.nd (.nd .lf z1679 .lf) z1680 (.nd .lf z1681 .lf))))) z1682 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1683 .lf) z1684 .lf) z1685 (.nd .lf z1686 .lf)) z1687 (.nd (.nd (.nd .lf z1688 .lf) z1689 .lf) z1690 (.nd .lf z1691 .lf))) z1692 (.nd (.nd (.nd (.nd .lf z1693 .lf) z1694 .lf) z1695 (.nd .lf z1696 .lf)) z1697 (.nd (.nd (.nd .lf z1698 .lf) z1699 .lf) z1700 (.nd .lf z1701 .lf)))) z1702 (.nd (.nd (.nd (.nd (.nd .lf z1703 .lf) z1704 .lf) z1705 (.nd .lf z1706 .lf)) z1707 (.nd (.nd (.nd .lf z1708 .lf) z1709 .lf) z1710 (.nd .lf z1711 .lf))) z1712 (.nd (.nd (.nd (.nd .lf z1713 .lf) z1714 .lf) z1715 (.nd .lf z1716 .lf)) z1717 (.nd (.nd .lf z1718 .lf) z1719 (.nd .lf z1720 .lf))))))) z1721 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1722 .lf) z1723 .lf) z1724 (.nd .lf z1725 .lf)) z1726 (.nd (.nd (.nd .lf z1727 .lf) z1728 .lf) z1729 (.nd .lf z1730 .lf))) z1731 (.nd (.nd (.nd (.nd .lf z1732 .lf) z1733 .lf) z1734 (.nd .lf z1735 .lf)) z1736 (.nd (.nd (.nd .lf z1737 .lf) z1738 .lf) z1739 (.nd .lf z1740 .lf)))) z1741 (.nd (.nd (.nd (.nd (.nd .lf z1742 .lf) z1743 .lf) z1744 (.nd .lf z1745 .lf)) z1746 (.nd (.nd (.nd .lf z1747 .lf) z1748 .lf) z1749 (.nd .lf z1750 .lf))) z1751 (.nd (.nd (.nd (.nd .lf z1752 .lf) z1753 .lf) z1754 (.nd .lf z1755 .lf)) z1756 (.nd (.nd .lf z1757 .lf) z1758 (.nd .lf z1759 .lf))))) z1760 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1761 .lf) z1762 .lf) z1763 (.nd .lf z1764 .lf)) z1765 (.nd (.nd (.nd .lf z1766 .lf) z1767 .lf) z1768 (.nd .lf z1769 .lf))) z1770 (.nd (.nd (.nd (.nd .lf z1771 .lf) z1772 .lf) z1773 (.nd .lf z1774 .lf)) z1775 (.nd (.nd (.nd .lf z1776 .lf) z1777 .lf) z1778 (.nd .lf z1779 .lf)))) z1780 (.nd (.nd (.nd (.nd (.nd .lf z1781 .lf) z1782 .lf) z1783 (.nd .lf z1784 .lf)) z1785 (.nd (.nd (.nd .lf z1786 .lf) z1787 .lf) z1788 (.nd .lf z1789 .lf))) z1790 (.nd (.nd (.nd (.nd .lf z1791 .lf) z1792 .lf) z1793 (.nd .lf z1794 .lf)) z1795 (.nd (.nd .lf z1796 .lf) z1797 (.nd .lf z1798 .lf)))))) z1799 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1800 .lf) z1801 .lf) z1802 (.nd .lf z1803 .lf)) z1804 (.nd (.nd (.nd .lf z1805 .lf) z1806 .lf) z1807 (.nd .lf z1808 .lf))) z1809 (.nd (.nd (.nd (.nd .lf z1810 .lf) z1811 .lf) z1812 (.nd .lf z1813 .lf)) z1814 (.nd (.nd (.nd .lf z1815 .lf) z1816 .lf) z1817 (.nd .lf z1818 .lf)))) z1819 (.nd (.nd (.nd (.nd (.nd .lf z1820 .lf) z1821 .lf) z1822 (.nd .lf z1823 .lf)) z1824 (.nd (.nd (.nd .lf z1825 .lf) z1826 .lf) z1827 (.nd .lf z1828 .lf))) z1829 (.nd (.nd (.nd (.nd .lf z1830 .lf) z1831 .lf) z1832 (.nd .lf z1833 .lf)) z1834 (.nd (.nd .lf z1835 .lf) z1836 (.nd .lf z1837 .lf))))) z1838 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1839 .lf) z1840 .lf) z1841 (.nd .lf z1842 .lf)) z1843 (.nd (.nd (.nd .lf z1844 .lf) z1845 .lf) z1846 (.nd .lf z1847 .lf))) z1848 (.nd (.nd (.nd (.nd .lf z1849 .lf) z1850 .lf) z1851 (.nd .lf z1852 .lf)) z1853 (.nd (.nd (.nd .lf z1854 .lf) z1855 .lf) z1856 (.nd .lf z1857 .lf)))) z1858 (.nd (.nd (.nd (.nd (.nd .lf z1859 .lf) z1860 .lf) z1861 (.nd .lf z1862 .lf)) z1863 (.nd (.nd (.nd .lf z1864 .lf) z1865 .lf) z1866 (.nd .lf z1867 .lf))) z1868 (.nd (.nd (.nd (.nd .lf z1869 .lf) z1870 .lf) z1871 (.nd .lf z1872 .lf)) z1873 (.nd (.nd .lf z1874 .lf) z1875 (.nd .lf z1876 .lf))))))))) z1877 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1878 .lf) z1879 .lf) z1880 (.nd .lf z1881 .lf)) z1882 (.nd (.nd (.nd .lf z1883 .lf) z1884 .lf) z1885 (.nd .lf z1886 .lf))) z1887 (.nd (.nd (.nd (.nd .lf z1888 .lf) z1889 .lf) z1890 (.nd .lf z1891 .lf)) z1892 (.nd (.nd (.nd .lf z1893 .lf) z1894 .lf) z1895 (.nd .lf z1896 .lf)))) z1897 (.nd (.nd (.nd (.nd (.nd .lf z1898 .lf) z1899 .lf) z1900 (.nd .lf z1901 .lf)) z1902 (.nd (.nd (.nd .lf z1903 .lf) z1904 .lf) z1905 (.nd .lf z1906 .lf))) z1907 (.nd (.nd (.nd (.nd .lf z1908 .lf) z1909 .lf) z1910 (.nd .lf z1911 .lf)) z1912 (.nd (.nd (.nd .lf z1913 .lf) z1914 .lf) z1915 (.nd .lf z1916 .lf))))) z1917 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1918 .lf) z1919 .lf) z1920 (.nd .lf z1921 .lf)) z1922 (.nd (.nd (.nd .lf z1923 .lf) z1924 .lf) z1925 (.nd .lf z1926 .lf))) z1927 (.nd (.nd (.nd (.nd .lf z1928 .lf) z1929 .lf) z1930 (.nd .lf z1931 .lf)) z1932 (.nd (.nd (.nd .lf z1933 .lf) z1934 .lf) z1935 (.nd .lf z1936 .lf)))) z1937 (.nd (.nd (.nd (.nd (.nd .lf z1938 .lf) z1939 .lf) z1940 (.nd .lf z1941 .lf)) z1942 (.nd (.nd (.nd .lf z1943 .lf) z1944 .lf) z1945 (.nd .lf z1946 .lf))) z1947 (.nd (.nd (.nd (.nd .lf z1948 .lf) z1949 .lf) z1950 (.nd .lf z1951 .lf)) z1952 (.nd (.nd .lf z1953 .lf) z1954 (.nd .lf z1955 .lf)))))) z1956 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z1957 .lf) z1958 .lf) z1959 (.nd .lf z1960 .lf)) z1961 (.nd (.nd (.nd .lf z1962 .lf) z1963 .lf) z1964 (.nd .lf z1965 .lf))) z1966 (.nd (.nd (.nd (.nd .lf z1967 .lf) z1968 .lf) z1969 (.nd .lf z1970 .lf)) z1971 (.nd (.nd (.nd .lf z1972 .lf) z1973 .lf) z1974 (.nd .lf z1975 .lf)))) z1976 (.nd (.nd (.nd (.nd (.nd .lf z1977 .lf) z1978 .lf) z1979 (.nd .lf z1980 .lf)) z1981 (.nd (.nd (.nd .lf z1982 .lf) z1983 .lf) z1984 (.nd .lf z1985 .lf))) z1986 (.nd (.nd (.nd (.nd .lf z1987 .lf) z1988 .lf) z1989 (.nd .lf z1990 .lf)) z1991 (.nd (.nd .lf z1992 .lf) z1993 (.nd .lf z1994 .lf))))) z1995 (.nd (.nd (.nd (.nd (.nd (.nd .lf z1996 .lf) z1997 .lf) z1998 (.nd .lf z1999 .lf)) z2000 (.nd (.nd (.nd .lf z2001 .lf) z2002 .lf) z2003 (.nd .lf z2004 .lf))) z2005 (.nd (.nd (.nd (.nd .lf z2006 .lf) z2007 .lf) z2008 (.nd .lf z2009 .lf)) z2010 (.nd (.nd (.nd .lf z2011 .lf) z2012 .lf) z2013 (.nd .lf z2014 .lf)))) z2015 (.nd (.nd (.nd (.nd (.nd .lf z2016 .lf) z2017 .lf) z2018 (.nd .lf z2019 .lf)) z2020 (.nd (.nd (.nd .lf z2021 .lf) z2022 .lf) z2023 (.nd .lf z2024 .lf))) z2025 (.nd (.nd (.nd (.nd .lf z2026 .lf) z2027 .lf) z2028 (.nd .lf z2029 .lf)) z2030 (.nd (.nd .lf z2031 .lf) z2032 (.nd .lf z2033 .lf))))))) z2034 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2035 .lf) z2036 .lf) z2037 (.nd .lf z2038 .lf)) z2039 (.nd (.nd (.nd .lf z2040 .lf) z2041 .lf) z2042 (.nd .lf z2043 .lf))) z2044 (.nd (.nd (.nd (.nd .lf z2045 .lf) z2046 .lf) z2047 (.nd .lf z2048 .lf)) z2049 (.nd (.nd (.nd .lf z2050 .lf) z2051 .lf) z2052 (.nd .lf z2053 .lf)))) z2054 (.nd (.nd (.nd (.nd (.nd .lf z2055 .lf) z2056 .lf) z2057 (.nd .lf z2058 .lf)) z2059 (.nd (.nd (.nd .lf z2060 .lf) z2061 .lf) z2062 (.nd .lf z2063 .lf))) z2064 (.nd (.nd (.nd (.nd .lf z2065 .lf) z2066 .lf) z2067 (.nd .lf z2068 .lf)) z2069 (.nd (.nd .lf z2070 .lf) z2071 (.nd .lf z2072 .lf))))) z2073 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2074 .lf) z2075 .lf) z2076 (.nd .lf z2077 .lf)) z2078 (.nd (.nd (.nd .lf z2079 .lf) z2080 .lf) z2081 (.nd .lf z2082 .lf))) z2083 (.nd (.nd (.nd (.nd .lf z2084 .lf) z2085 .lf) z2086 (.nd .lf z2087 .lf)) z2088 (.nd (.nd (.nd .lf z2089 .lf) z2090 .lf) z2091 (.nd .lf z2092 .lf)))) z2093 (.nd (.nd (.nd (.nd (.nd .lf z2094 .lf) z2095 .lf) z2096 (.nd .lf z2097 .lf)) z2098 (.nd (.nd (.nd .lf z2099 .lf) z2100 .lf) z2101 (.nd .lf z2102 .lf))) z2103 (.nd (.nd (.nd (.nd .lf z2104 .lf) z2105 .lf) z2106 (.nd .lf z2107 .lf)) z2108 (.nd (.nd .lf z2109 .lf) z2110 (.nd .lf z2111 .lf)))))) z2112 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2113 .lf) z2114 .lf) z2115 (.nd .lf z2116 .lf)) z2117 (.nd (.nd (.nd .lf z2118 .lf) z2119 .lf) z2120 (.nd .lf z2121 .lf))) z2122 (.nd (.nd (.nd (.nd .lf z2123 .lf) z2124 .lf) z2125 (.nd .lf z2126 .lf)) z2127 (.nd (.nd (.nd .lf z2128 .lf) z2129 .lf) z2130 (.nd .lf z2131 .lf)))) z2132 (.nd (.nd (.nd (.nd (.nd .lf z2133 .lf) z2134 .lf) z2135 (.nd .lf z2136 .lf)) z2137 (.nd (.nd (.nd .lf z2138 .lf) z2139 .lf) z2140 (.nd .lf z2141 .lf))) z2142 (.nd (.nd (.nd (.nd .lf z2143 .lf) z2144 .lf) z2145 (.nd .lf z2146 .lf)) z2147 (.nd (.nd .lf z2148 .lf) z2149 (.nd .lf z2150 .lf))))) z2151 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2152 .lf) z2153 .lf) z2154 (.nd .lf z2155 .lf)) z2156 (.nd (.nd (.nd .lf z2157 .lf) z2158 .lf) z2159 (.nd .lf z2160 .lf))) z2161 (.nd (.nd (.nd (.nd .lf z2162 .lf) z2163 .lf) z2164 (.nd .lf z2165 .lf)) z2166 (.nd (.nd (.nd .lf z2167 .lf) z2168 .lf) z2169 (.nd .lf z2170 .lf)))) z2171 (.nd (.nd (.nd (.nd (.nd .lf z2172 .lf) z2173 .lf) z2174 (.nd .lf z2175 .lf)) z2176 (.nd (.nd (.nd .lf z2177 .lf) z2178 .lf) z2179 (.nd .lf z2180 .lf))) z2181 (.nd (.nd (.nd (.nd .lf z2182 .lf) z2183 .lf) z2184 (.nd .lf z2185 .lf)) z2186 (.nd (.nd .lf z2187 .lf) z2188 (.nd .lf z2189 .lf)))))))) z2190 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2191 .lf) z2192 .lf) z2193 (.nd .lf z2194 .lf)) z2195 (.nd (.nd (.nd .lf z2196 .lf) z2197 .lf) z2198 (.nd .lf z2199 .lf))) z2200 (.nd (.nd (.nd (.nd .lf z2201 .lf) z2202 .lf) z2203 (.nd .lf z2204 .lf)) z2205 (.nd (.nd (.nd .lf z2206 .lf) z2207 .lf) z2208 (.nd .lf z2209 .lf)))) z2210 (.nd (.nd (.nd (.nd (.nd .lf z2211 .lf) z2212 .lf) z2213 (.nd .lf z2214 .lf)) z2215 (.nd (.nd (.nd .lf z2216 .lf) z2217 .lf) z2218 (.nd .lf z2219 .lf))) z2220 (.nd (.nd (.nd (.nd .lf z2221 .lf) z2222 .lf) z2223 (.nd .lf z2224 .lf)) z2225 (.nd (.nd .lf z2226 .lf) z2227 (.nd .lf z2228 .lf))))) z2229 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2230 .lf) z2231 .lf) z2232 (.nd .lf z2233 .lf)) z2234 (.nd (.nd (.nd .lf z2235 .lf) z2236 .lf) z2237 (.nd .lf z2238 .lf))) z2239 (.nd (.nd (.nd (.nd .lf z2240 .lf) z2241 .lf) z2242 (.nd .lf z2243 .lf)) z2244 (.nd (.nd (.nd .lf z2245 .lf) z2246 .lf) z2247 (.nd .lf z2248 .lf)))) z2249 (.nd (.nd (.nd (.nd (.nd .lf z2250 .lf) z2251 .lf) z2252 (.nd .lf z2253 .lf)) z2254 (.nd (.nd (.nd .lf z2255 .lf) z2256 .lf) z2257 (.nd .lf z2258 .lf))) z2259 (.nd (.nd (.nd (.nd .lf z2260 .lf) z2261 .lf) z2262 (.nd .lf z2263 .lf)) z2264 (.nd (.nd .lf z2265 .lf) z2266 (.nd .lf z2267 .lf)))))) z2268 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2269 .lf) z2270 .lf) z2271 (.nd .lf z2272 .lf)) z2273 (.nd (.nd (.nd .lf z2274 .lf) z2275 .lf) z2276 (.nd .lf z2277 .lf))) z2278 (.nd (.nd (.nd (.nd .lf z2279 .lf) z2280 .lf) z2281 (.nd .lf z2282 .lf)) z2283 (.nd (.nd (.nd .lf z2284 .lf) z2285 .lf) z2286 (.nd .lf z2287 .lf)))) z2288 (.nd (.nd (.nd (.nd (.nd .lf z2289 .lf) z2290 .lf) z2291 (.nd .lf z2292 .lf)) z2293 (.nd (.nd (.nd .lf z2294 .lf) z2295 .lf) z2296 (.nd .lf z2297 .lf))) z2298 (.nd (.nd (.nd (.nd .lf z2299 .lf) z2300 .lf) z2301 (.nd .lf z2302 .lf)) z2303 (.nd (.nd .lf z2304 .lf) z2305 (.nd .lf z2306 .lf))))) z2307 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2308 .lf) z2309 .lf) z2310 (.nd .lf z2311 .lf)) z2312 (.nd (.nd (.nd .lf z2313 .lf) z2314 .lf) z2315 (.nd .lf z2316 .lf))) z2317 (.nd (.nd (.nd (.nd .lf z2318 .lf) z2319 .lf) z2320 (.nd .lf z2321 .lf)) z2322 (.nd (.nd (.nd .lf z2323 .lf) z2324 .lf) z2325 (.nd .lf z2326 .lf)))) z2327 (.nd (.nd (.nd (.nd (.nd .lf z2328 .lf) z2329 .lf) z2330 (.nd .lf z2331 .lf)) z2332 (.nd (.nd (.nd .lf z2333 .lf) z2334 .lf) z2335 (.nd .lf z2336 .lf))) z2337 (.nd (.nd (.nd (.nd .lf z2338 .lf) z2339 .lf) z2340 (.nd .lf z2341 .lf)) z2342 (.nd (.nd .lf z2343 .lf) z2344 (.nd .lf z2345 .lf))))))) z2346 (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2347 .lf) z2348 .lf) z2349 (.nd .lf z2350 .lf)) z2351 (.nd (.nd (.nd .lf z2352 .lf) z2353 .lf) z2354 (.nd .lf z2355 .lf))) z2356 (.nd (.nd (.nd (.nd .lf z2357 .lf) z2358 .lf) z2359 (.nd .lf z2360 .lf)) z2361 (.nd (.nd (.nd .lf z2362 .lf) z2363 .lf) z2364 (.nd .lf z2365 .lf)))) z2366 (.nd (.nd (.nd (.nd (.nd .lf z2367 .lf) z2368 .lf) z2369 (.nd .lf z2370 .lf)) z2371 (.nd (.nd (.nd .lf z2372 .lf) z2373 .lf) z2374 (.nd .lf z2375 .lf))) z2376 (.nd (.nd (.nd (.nd .lf z2377 .lf) z2378 .lf) z2379 (.nd .lf z2380 .lf)) z2381 (.nd (.nd .lf z2382 .lf) z2383 (.nd .lf z2384 .lf))))) z2385 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2386 .lf) z2387 .lf) z2388 (.nd .lf z2389 .lf)) z2390 (.nd (.nd (.nd .lf z2391 .lf) z2392 .lf) z2393 (.nd .lf z2394 .lf))) z2395 (.nd (.nd (.nd (.nd .lf z2396 .lf) z2397 .lf) z2398 (.nd .lf z2399 .lf)) z2400 (.nd (.nd (.nd .lf z2401 .lf) z2402 .lf) z2403 (.nd .lf z2404 .lf)))) z2405 (.nd (.nd (.nd (.nd (.nd .lf z2406 .lf) z2407 .lf) z2408 (.nd .lf z2409 .lf)) z2410 (.nd (.nd (.nd .lf z2411 .lf) z2412 .lf) z2413 (.nd .lf z2414 .lf))) z2415 (.nd (.nd (.nd (.nd .lf z2416 .lf) z2417 .lf) z2418 (.nd .lf z2419 .lf)) z2420 (.nd (.nd .lf z2421 .lf) z2422 (.nd .lf z2423 .lf)))))) z2424 (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf z2425 .lf) z2426 .lf) z2427 (.nd .lf z2428 .lf)) z2429 (.nd (.nd (.nd .lf z2430 .lf) z2431 .lf) z2432 (.nd .lf z2433 .lf))) z2434 (.nd (.nd (.nd (.nd .lf z2435 .lf) z2436 .lf) z2437 (.nd .lf z2438 .lf)) z2439 (.nd (.nd (.nd .lf z2440 .lf) z2441 .lf) z2442 (.nd .lf z2443 .lf)))) z2444 (.nd (.nd (.nd (.nd (.nd .lf z2445 .lf) z2446 .lf) z2447 (.nd .lf z2448 .lf)) z2449 (.nd (.nd (.nd .lf z2450 .lf) z2451 .lf) z2452 (.nd .lf z2453 .lf))) z2454 (.nd (.nd (.nd (.nd .lf z2455 .lf) z2456 .lf) z2457 (.nd .lf z2458 .lf)) z2459 (.nd (.nd .lf z2460 .lf) z2461 (.nd .lf z2462 .lf))))) z2463 (.nd (.nd (.nd (.nd (.nd (.nd .lf z2464 .lf) z2465 .lf) z2466 (.nd .lf z2467 .lf)) z2468 (.nd (.nd (.nd .lf z2469 .lf) z2470 .lf) z2471 (.nd .lf z2472 .lf))) z2473 (.nd (.nd (.nd (.nd .lf z2474 .lf) z2475 .lf) z2476 (.nd .lf z2477 .lf)) z2478 (.nd (.nd (.nd .lf z2479 .lf) z2480 .lf) z2481 (.nd .lf z2482 .lf)))) z2483 (.nd (.nd (.nd (.nd (.nd .lf z2484 .lf) z2485 .lf) z2486 (.nd .lf z2487 .lf)) z2488 (.nd (.nd (.nd .lf z2489 .lf) z2490 .lf) z2491 (.nd .lf z2492 .lf))) z2493 (.nd (.nd (.nd (.nd .lf z2494 .lf) z2495 .lf) z2496 (.nd .lf z2497 .lf)) z2498 (.nd (.nd .lf z2499 .lf) z2500 (.nd .lf z2501 .lf)))))))))))
def P_ := stepOK 33554431 Y_ PD_ PM_ G_ T_
def b0 : List (List Nat × List (Nat × Nat)) := [(z0,[]),(z1,[(1024,1222),(1024,5314)]),(z2,[(1024,1222),(1024,5314)]),(z3,[(1024,1222),(1024,5314)]),(z4,[]),(z5,[]),(z6,[(1024,1222),(1024,5314)]),(z7,[(1024,201730),(1024,207882)]),(z8,[(1024,197638),(1024,1222)]),(z9,[(1024,5314),(1024,1222)]),(z10,[]),(z11,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : b0.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b1 : List (List Nat × List (Nat × Nat)) := [(z12,[]),(z13,[]),(z14,[(1024,1222),(1024,5314)]),(z15,[(1024,132298),(1024,1222)]),(z16,[(1024,132298),(1024,1222)]),(z17,[(1024,132298),(1024,1222)]),(z18,[(1024,5314),(1024,1222)]),(z19,[(1024,5314),(1024,1222)]),(z20,[(1024,5314),(1024,1222)]),(z21,[]),(z22,[]),(z23,[(1024,201730),(1024,5314)])]
def b2 : List (List Nat × List (Nat × Nat)) := [(z24,[(1024,1222),(1024,5314)]),(z25,[(1024,5314),(1024,1222)]),(z26,[(1024,5314),(1024,1222)]),(z27,[(1024,132298),(1024,1222)]),(z28,[(1024,5314),(1024,1222)]),(z29,[(1024,1222),(1024,5314)]),(z30,[]),(z31,[(1024,106690),(1024,99529)]),(z32,[(1024,5314),(1024,1222)]),(z33,[(1024,106690),(1024,99529)]),(z34,[]),(z35,[(1024,5314),(1024,1222)])]
def b3 : List (List Nat × List (Nat × Nat)) := [(z36,[]),(z37,[]),(z38,[(1024,204898),(1024,5314)]),(z39,[(1024,5314),(1024,1222)]),(z40,[(1024,1222),(1024,5314)]),(z41,[(1024,99529),(1024,1222)]),(z42,[(1024,469638),(1024,201730)]),(z43,[(1024,201730),(1024,208330)]),(z44,[(1024,5314),(1024,99529)]),(z45,[(1024,207302),(1024,1222)]),(z46,[(1024,5314),(1024,1222)]),(z47,[(1024,207306),(1024,1222)])]
def b4 : List (List Nat × List (Nat × Nat)) := [(z48,[(1024,5314),(1024,1222)]),(z49,[(1024,5314),(1024,99529)]),(z50,[(1024,208330),(1024,1222)]),(z51,[(1024,201730),(1024,1222)]),(z52,[(1024,5314),(1024,99529)]),(z53,[(1024,99529),(1024,1222)]),(z54,[(1024,464074),(1024,1222)]),(z55,[(1024,664774),(1024,132298)]),(z56,[(1024,132294),(1024,201858)]),(z57,[(1024,197638),(1024,1222)]),(z58,[(1024,5314),(1024,99352)]),(z59,[])]
def b5 : List (List Nat × List (Nat × Nat)) := [(z60,[]),(z61,[]),(z62,[(1024,205826),(1024,1226)]),(z63,[(1024,1131),(1024,25035)]),(z64,[(1024,10905),(1024,25227)]),(z65,[(1024,10905),(1024,201730)]),(z66,[(1024,10904),(1024,201730)]),(z67,[(1024,201730),(1024,207882)]),(z68,[(1024,1222),(1024,197638)]),(z69,[(1024,1131),(1024,99339)]),(z70,[(1024,99352),(1024,1144)]),(z71,[(1024,5314),(1024,1222)])]
def b6 : List (List Nat × List (Nat × Nat)) := [(z72,[(1024,197638),(1024,1222)]),(z73,[(1024,5314),(1024,1222)]),(z74,[(1024,197638),(1024,1222)]),(z75,[(1024,5314),(1024,99529)]),(z76,[(1024,10886),(1024,99529)]),(z77,[(1024,1222),(1024,5314)]),(z78,[(1024,10886),(1024,1222)]),(z79,[(1024,1222),(1024,5314)]),(z80,[(1024,1222),(1024,10886)]),(z81,[]),(z82,[]),(z83,[(1024,132298),(1024,1222)])]
def b7 : List (List Nat × List (Nat × Nat)) := [(z84,[(1024,201730),(1024,5314)]),(z85,[(1024,5314),(1024,1222)]),(z86,[]),(z87,[]),(z88,[]),(z89,[]),(z90,[]),(z91,[(1024,1144),(1024,99352)]),(z92,[(1024,1144),(1024,99352)]),(z93,[(1024,207882),(1024,201730)]),(z94,[(1024,5314),(1024,1222)]),(z95,[(1024,5314),(1024,1222)])]
def b8 : List (List Nat × List (Nat × Nat)) := [(z96,[(1024,5314),(1024,1222)]),(z97,[(1024,208330),(1024,201730)]),(z98,[(1024,208330),(1024,1222)]),(z99,[(1024,201730),(1024,207882)]),(z100,[]),(z101,[(1024,10886),(1024,197638)]),(z102,[(1024,207978),(1024,107724)]),(z103,[(1024,197638),(1024,1222)]),(z104,[(1024,207978),(1024,1222)]),(z105,[(1024,204802),(1024,1225)]),(z106,[(1024,5322),(1024,9414)]),(z107,[(1024,5314),(1024,25030)])]
def b9 : List (List Nat × List (Nat × Nat)) := [(z108,[(1024,140761),(1024,24010)]),(z109,[(1024,5314),(1024,1222)]),(z110,[(1024,5314),(1024,1222)]),(z111,[(1024,207882),(1024,201730)]),(z112,[(1024,10905),(1024,201730)]),(z113,[(1024,197638),(1024,5314)]),(z114,[(1024,665625),(1024,10905)]),(z115,[(1024,10905),(1024,107545)]),(z116,[(1024,1144),(1024,5314)]),(z117,[(1024,201730),(1024,1222)]),(z118,[(1024,197638),(1024,1222)]),(z119,[(1024,10442),(1024,107718)])]
def b10 : List (List Nat × List (Nat × Nat)) := [(z120,[(1024,1222),(1024,10905)]),(z121,[(1024,132121),(1024,1144)]),(z122,[(1024,1144),(1024,5314)]),(z123,[(1024,1144),(1024,5314)]),(z124,[(1024,132298),(1024,99529)]),(z125,[(1024,132298),(1024,1222)]),(z126,[(1024,1222),(1024,99529)]),(z127,[(1024,132298),(1024,197770)]),(z128,[(1024,132298),(1024,197770)]),(z129,[(1024,197770),(1024,132298)]),(z130,[(1024,197770),(1024,132298)]),(z131,[(1024,106690),(1024,99529)])]
def b11 : List (List Nat × List (Nat × Nat)) := [(z132,[(1024,1222),(1024,5314)]),(z133,[(1024,1222),(1024,5314)]),(z134,[(1024,207306),(1024,1222)]),(z135,[(1024,5314),(1024,1222)]),(z136,[(1024,5314),(1024,99529)]),(z137,[]),(z138,[(144,1)]),(z139,[(1024,472715),(1024,205954)]),(z140,[(1024,472748),(1024,1222)]),(z141,[]),(z142,[]),(z143,[(1024,99787),(1024,122530)])]
def b12 : List (List Nat × List (Nat × Nat)) := [(z144,[(1024,1486),(1024,122530)]),(z145,[(1024,1222),(1024,99529)]),(z146,[(1024,483980),(1024,1222)]),(z147,[(1024,132298),(1024,99529)]),(z148,[(1024,132298),(1024,1222)]),(z149,[(1024,1222),(1024,99529)]),(z150,[]),(z151,[]),(z152,[]),(z153,[(1024,666062),(1024,205954)]),(z154,[(1024,205922),(1024,112290)]),(z155,[(1024,666062),(1024,204930)])]
def b13 : List (List Nat × List (Nat × Nat)) := [(z156,[]),(z157,[]),(z158,[(1024,205954),(1024,1222)]),(z159,[(1024,712834),(1024,1222)]),(z160,[(1024,110242),(1024,1222)]),(z161,[(1024,132793),(1024,99529)]),(z162,[(1024,699490),(1024,1222)]),(z163,[(1024,99529),(1024,1222)]),(z164,[(1024,132298),(1024,1222)]),(z165,[(1024,99530),(1024,1222)]),(z166,[(1024,666062),(1024,1222)]),(z167,[(1024,470218),(1024,205954)])]
def b14 : List (List Nat × List (Nat × Nat)) := [(z168,[(1024,669131),(1024,205826)]),(z169,[(1024,666062),(1024,201858)]),(z170,[]),(z171,[]),(z172,[]),(z173,[(1024,115362),(1024,1222)]),(z174,[(1024,469646),(1024,1222)]),(z175,[]),(z176,[]),(z177,[(1024,122530),(1024,1222)]),(z178,[(1024,1155),(1024,2178)]),(z179,[(1024,669131),(1024,201730)])]
def b15 : List (List Nat × List (Nat × Nat)) := [(z180,[(1024,669131),(1024,201730)]),(z181,[(1024,201730),(1024,109218)]),(z182,[(1024,483979),(1024,201730)]),(z183,[(1024,201730),(1024,208330)]),(z184,[(1024,201730),(1024,208330)]),(z185,[(1024,469646),(1024,201730)]),(z186,[(1024,469646),(1024,205954)]),(z187,[(1024,201730),(1024,208330)]),(z188,[(1024,205954),(1024,1222)]),(z189,[(1024,201730),(1024,1222)]),(z190,[(1024,1222),(1024,201730)]),(z191,[(1024,205954),(1024,132298)])]
def b16 : List (List Nat × List (Nat × Nat)) := [(z192,[(1024,1222),(1024,99529)]),(z193,[(1024,1222),(1024,99529)]),(z194,[(1024,1222),(1024,132298)]),(z195,[(1024,1222),(1024,132298)]),(z196,[(1024,1222),(1024,109218)]),(z197,[(1024,1222),(1024,109218)]),(z198,[(1024,1222),(1024,109218)]),(z199,[(1024,1222),(1024,99529)]),(z200,[(1024,99529),(1024,110242)]),(z201,[(1024,1222),(1024,99529)]),(z202,[(1024,484012),(1024,1222)]),(z203,[(1024,205954),(1024,99529)])]
def b17 : List (List Nat × List (Nat × Nat)) := [(z204,[(1024,132298),(1024,1222)]),(z205,[(1024,132298),(1024,1222)]),(z206,[(1024,132298),(1024,99529)]),(z207,[(1024,132298),(1024,99529)]),(z208,[(1024,132793),(1024,99529)]),(z209,[(1024,132298),(1024,205954)]),(z210,[(1024,1222),(1024,132298)]),(z211,[(1024,132298),(1024,1222)]),(z212,[(1024,132298),(1024,1222)]),(z213,[(1024,1486),(1024,132298)]),(z214,[(1024,132298),(1024,1222)]),(z215,[(1024,205954),(1024,132298)])]
def b18 : List (List Nat × List (Nat × Nat)) := [(z216,[(1024,99529),(1024,201730)]),(z217,[(1024,132298),(1024,204898)]),(z218,[(1024,1222),(1024,99529)]),(z219,[(1024,1222),(1024,99529)]),(z220,[(1024,1222),(1024,99529)]),(z221,[(1024,1222),(1024,201730)]),(z222,[(1024,132298),(1024,201730)]),(z223,[(1024,469646),(1024,1222)]),(z224,[(1024,132298),(1024,201730)]),(z225,[(1024,132298),(1024,1222)]),(z226,[(1024,1222),(1024,99529)]),(z227,[(1024,1222),(1024,132298)])]
def b19 : List (List Nat × List (Nat × Nat)) := [(z228,[(1024,99529),(1024,1222)]),(z229,[(1024,1222),(1024,132298)]),(z230,[(1024,205954),(1024,5314)]),(z231,[(1024,5314),(1024,1222)]),(z232,[(1024,1222),(1024,5314)]),(z233,[(1024,1222),(1024,5314)]),(z234,[(1024,1222),(1024,5314)]),(z235,[(1024,1222),(1024,5314)]),(z236,[(1024,99529),(1024,5314)]),(z237,[(1024,1222),(1024,5314)]),(z238,[(1024,1222),(1024,5314)]),(z239,[(1024,5314),(1024,1222)])]
def b20 : List (List Nat × List (Nat × Nat)) := [(z240,[(104,1)]),(z241,[]),(z242,[(1024,201730),(1024,5314)]),(z243,[(104,1),(1024,1222),(1024,5314)]),(z244,[(104,1),(1024,5314),(1024,1222)]),(z245,[(104,1),(1024,5314),(1024,1222)]),(z246,[(104,1),(1024,132298),(1024,1222)]),(z247,[(104,1),(1024,5314),(1024,1222)]),(z248,[(104,1),(1024,5314),(1024,1222)]),(z249,[(1024,1222),(1024,5314)]),(z250,[]),(z251,[(1024,106690),(1024,99529)])]
def b21 : List (List Nat × List (Nat × Nat)) := [(z252,[(1024,132298),(1024,1222)]),(z253,[(1024,106690),(1024,99529)]),(z254,[]),(z255,[]),(z256,[]),(z257,[(1024,204898),(1024,5314)]),(z258,[(104,1),(1024,5314),(1024,1222)]),(z259,[(1024,132298),(1024,1222)]),(z260,[(1024,99529),(1024,1222)]),(z261,[(1024,201730),(1024,1222)]),(z262,[(1024,201730),(1024,1222)]),(z263,[(1024,132298),(1024,5314)])]
def b22 : List (List Nat × List (Nat × Nat)) := [(z264,[(1024,469638),(1024,1222)]),(z265,[(1024,627914),(1024,1222)]),(z266,[(1024,106690),(1024,99529)]),(z267,[(1024,115362),(1024,1222)]),(z268,[(1024,464074),(1024,1222)]),(z269,[(1024,5314),(1024,1222)]),(z270,[(1024,1222),(1024,99529)]),(z271,[(1024,205484),(1024,1222)]),(z272,[(1024,5314),(1024,201730)]),(z273,[(1024,5314),(1024,1222)]),(z274,[(96,0)]),(z275,[(96,0)])]
def b23 : List (List Nat × List (Nat × Nat)) := [(z276,[]),(z277,[(1024,483979),(1024,107170)]),(z278,[]),(z279,[(1024,472710),(1024,122530)]),(z280,[(1024,468172),(1024,5314)]),(z281,[(1024,468172),(1024,5314)]),(z282,[(1024,106690),(1024,99529)]),(z283,[(1024,5314),(1024,1222)]),(z284,[(1024,106690),(1024,99529)]),(z285,[(1024,132297),(1024,1222)]),(z286,[(1024,5314),(1024,1222)]),(z287,[(1024,472710),(1024,1222)])]
def b24 : List (List Nat × List (Nat × Nat)) := [(z288,[(1024,132298),(1024,1222)]),(z289,[(1024,99529),(1024,1222)]),(z290,[]),(z291,[(1024,5314),(1024,201730)]),(z292,[(1024,469638),(1024,122530)]),(z293,[(1024,201730),(1024,104098)]),(z294,[(1024,201730),(1024,1222)]),(z295,[(1024,201730),(1024,1222)]),(z296,[(1024,469638),(1024,1222)]),(z297,[(1024,1222),(1024,104098)]),(z298,[(1024,132298),(1024,5314)]),(z299,[(1024,1222),(1024,5314)])]
def b25 : List (List Nat × List (Nat × Nat)) := [(z300,[(1024,1222),(1024,5314)]),(z301,[(1024,106690),(1024,99529)]),(z302,[(1024,122530),(1024,1222)]),(z303,[(1024,122530),(1024,1222)]),(z304,[(1024,483979),(1024,204930)]),(z305,[(1024,208329),(1024,1222)]),(z306,[(1024,5314),(1024,1222)]),(z307,[(1024,483974),(1024,201858)]),(z308,[(1024,208330),(1024,201826)]),(z309,[(1024,208326),(1024,99529)]),(z310,[(1024,208330),(1024,99526)]),(z311,[(1024,5314),(1024,1222)])]
def b26 : List (List Nat × List (Nat × Nat)) := [(z312,[(1024,5314),(1024,1222)]),(z313,[(1024,483979),(1024,201730)]),(z314,[(1024,208330),(1024,1222)]),(z315,[(1024,5314),(1024,1222)]),(z316,[(1024,1222),(1024,5314)]),(z317,[(1024,1222),(1024,5314)]),(z318,[(1024,208330),(1024,201730)]),(z319,[(1024,208330),(1024,1222)]),(z320,[(1024,201730),(1024,208330)]),(z321,[(1024,208330),(1024,1222)]),(z322,[(1024,208330),(1024,205954)]),(z323,[(1024,208330),(1024,132298)])]
def b27 : List (List Nat × List (Nat × Nat)) := [(z324,[]),(z325,[(1024,110786),(1024,2246)]),(z326,[]),(z327,[(1024,204930),(1024,208329)]),(z328,[(1024,204930),(1024,122530)]),(z329,[(1024,666073),(1024,204930)]),(z330,[(1024,666073),(1024,205954)]),(z331,[(1024,666073),(1024,204930)]),(z332,[(1024,204898),(1024,5314)]),(z333,[(1024,208329),(1024,204930)]),(z334,[(1024,699849),(1024,204898)]),(z335,[(1024,467148),(1024,204930)])]
def b28 : List (List Nat × List (Nat × Nat)) := [(z336,[(1024,208329),(1024,204930)]),(z337,[(1024,208330),(1024,205954)]),(z338,[(1024,208330),(1024,204898)]),(z339,[(1024,208330),(1024,205954)]),(z340,[(1024,468172),(1024,205954)]),(z341,[(1024,204930),(1024,1222)]),(z342,[(1024,99529),(1024,1222)]),(z343,[(1024,99529),(1024,132298)]),(z344,[(1024,99529),(1024,132298)]),(z345,[(1024,99529),(1024,1222)]),(z346,[(1024,99529),(1024,1222)]),(z347,[(1024,99529),(1024,132298)])]
def b29 : List (List Nat × List (Nat × Nat)) := [(z348,[(1024,99529),(1024,1222)]),(z349,[(1024,107170),(1024,1222)]),(z350,[(1024,206284),(1024,1222)]),(z351,[(1024,208330),(1024,1222)]),(z352,[(1024,99786),(1024,1222)]),(z353,[(1024,132298),(1024,205954)]),(z354,[(1024,132297),(1024,1222)]),(z355,[(1024,122530),(1024,1222)]),(z356,[(1024,1222),(1024,132297)]),(z357,[(1024,132298),(1024,1222)]),(z358,[(1024,666073),(1024,1222)]),(z359,[(1024,470217),(1024,204930)])]
def b30 : List (List Nat × List (Nat × Nat)) := [(z360,[(1024,5314),(1024,1222)]),(z361,[(1024,1222),(1024,5314)]),(z362,[(1024,467146),(1024,1222)]),(z363,[(1024,213610),(1024,1222)]),(z364,[(1024,467146),(1024,1222)]),(z365,[(1024,205954),(1024,1222)]),(z366,[(1024,467146),(1024,1222)]),(z367,[(1024,5314),(1024,1222)]),(z368,[(1024,122530),(1024,1222)]),(z369,[(1024,1222),(1024,5314)]),(z370,[(1024,5314),(1024,2278)]),(z371,[(1024,1222),(1024,5314)])]
def b31 : List (List Nat × List (Nat × Nat)) := [(z372,[(1024,1222),(1024,5314)]),(z373,[(1024,468664),(1024,1222)]),(z374,[(1024,1222),(1024,5314)]),(z375,[(1024,110242),(1024,1222)]),(z376,[(1024,1222),(1024,5314)]),(z377,[(1024,132298),(1024,5314)]),(z378,[(1024,208330),(1024,1222)]),(z379,[(1024,208330),(1024,132298)]),(z380,[(1024,208329),(1024,132297)]),(z381,[(1024,208329),(1024,132297)]),(z382,[(1024,99529),(1024,5314)]),(z383,[(1024,204898),(1024,1222)])]
def b32 : List (List Nat × List (Nat × Nat)) := [(z384,[(1024,468172),(1024,1222)]),(z385,[(1024,1222),(1024,99529)]),(z386,[(1024,467148),(1024,1222)]),(z387,[(1024,208329),(1024,1222)]),(z388,[(1024,132298),(1024,1222)]),(z389,[(1024,1222),(1024,99529)]),(z390,[(1024,208330),(1024,1222)]),(z391,[(1024,468172),(1024,1222)]),(z392,[(1024,680395),(1024,204802)]),(z393,[(1024,99529),(1024,1222)]),(z394,[]),(z395,[(1024,208326),(1024,201858)])]
def b33 : List (List Nat × List (Nat × Nat)) := [(z396,[(1024,201858),(1024,122530)]),(z397,[(1024,208326),(1024,201858)]),(z398,[(1024,208326),(1024,201826)]),(z399,[(1024,680395),(1024,201858)]),(z400,[(1024,208330),(1024,205954)]),(z401,[(1024,699865),(1024,201858)]),(z402,[(1024,204898),(1024,208326)]),(z403,[(1024,204898),(1024,208326)]),(z404,[(1024,201826),(1024,208330)]),(z405,[(1024,208330),(1024,201826)]),(z406,[(1024,201826),(1024,122530)]),(z407,[(1024,208330),(1024,201826)])]
def b34 : List (List Nat × List (Nat × Nat)) := [(z408,[(1024,679366),(1024,201826)]),(z409,[(1024,680390),(1024,204898)]),(z410,[(1024,680390),(1024,201826)]),(z411,[(1024,208330),(1024,205923)]),(z412,[(1024,208330),(1024,205954)]),(z413,[(1024,208326),(1024,201858)]),(z414,[(1024,208326),(1024,201858)]),(z415,[(1024,679370),(1024,201826)]),(z416,[(1024,201858),(1024,99529)]),(z417,[(1024,208326),(1024,99529)]),(z418,[(1024,660953),(1024,99529)]),(z419,[(1024,660953),(1024,132294)])]
def b35 : List (List Nat × List (Nat × Nat)) := [(z420,[(1024,470214),(1024,201858)]),(z421,[(1024,213451),(1024,99529)]),(z422,[(1024,206284),(1024,99526)]),(z423,[(1024,208330),(1024,99526)]),(z424,[(1024,660953),(1024,99526)]),(z425,[(1024,208330),(1024,99529)]),(z426,[(1024,132298),(1024,205954)]),(z427,[(1024,470218),(1024,205954)]),(z428,[(1024,213610),(1024,99526)]),(z429,[(1024,99459),(1024,100482)]),(z430,[(1024,208330),(1024,132298)]),(z431,[(1024,99526),(1024,208330)])]
def b36 : List (List Nat × List (Nat × Nat)) := [(z432,[(1024,132294),(1024,201858)]),(z433,[(1024,99529),(1024,204898)]),(z434,[(1024,680390),(1024,99529)]),(z435,[(1024,132195),(1024,100482)]),(z436,[(1024,201730),(1024,5314)]),(z437,[(1024,201730),(1024,5314)]),(z438,[(1024,208326),(1024,1222)]),(z439,[(1024,208330),(1024,1222)]),(z440,[(1024,1222),(1024,132298)]),(z441,[(1024,1222),(1024,132297)]),(z442,[(1024,205954),(1024,1222)]),(z443,[(1024,1222),(1024,5314)])]
def b37 : List (List Nat × List (Nat × Nat)) := [(z444,[(1024,122530),(1024,1222)]),(z445,[(1024,1222),(1024,5314)]),(z446,[(1024,646826),(1024,1222)]),(z447,[(1024,1222),(1024,5314)]),(z448,[(1024,1222),(1024,5314)]),(z449,[(1024,1222),(1024,5314)]),(z450,[(1024,99529),(1024,5314)]),(z451,[(1024,99529),(1024,5314)]),(z452,[(1024,1222),(1024,5314)]),(z453,[(1024,213610),(1024,99526)]),(z454,[]),(z455,[(1024,5314),(1024,204898)])]
def b38 : List (List Nat × List (Nat × Nat)) := [(z456,[(1024,204898),(1024,5314)]),(z457,[(1024,205954),(1024,1222)]),(z458,[(1024,1222),(1024,5314)]),(z459,[(1024,122530),(1024,1222)]),(z460,[(1024,1222),(1024,5314)]),(z461,[(1024,1222),(1024,5314)]),(z462,[(1024,1222),(1024,5314)]),(z463,[(1024,1222),(1024,5314)]),(z464,[(1024,1222),(1024,5314)]),(z465,[(1024,99529),(1024,5314)]),(z466,[(1024,99529),(1024,5314)]),(z467,[(1024,99529),(1024,5314)])]
def b39 : List (List Nat × List (Nat × Nat)) := [(z468,[(1024,1222),(1024,5314)]),(z469,[(1024,1222),(1024,5314)]),(z470,[(1024,469638),(1024,201730)]),(z471,[(1024,208330),(1024,201730)]),(z472,[(1024,234499),(1024,5314)]),(z473,[(1024,1155),(1024,2178)]),(z474,[(1024,680395),(1024,201730)]),(z475,[(1024,680395),(1024,201730)]),(z476,[(1024,201730),(1024,208330)]),(z477,[(1024,208326),(1024,201858)]),(z478,[(1024,666054),(1024,201730)]),(z479,[(1024,464076),(1024,201858)])]
def b40 : List (List Nat × List (Nat × Nat)) := [(z480,[(1024,666073),(1024,205954)]),(z481,[(1024,680395),(1024,201858)]),(z482,[(1024,680395),(1024,201730)]),(z483,[(1024,201730),(1024,208330)]),(z484,[(1024,666073),(1024,122530)]),(z485,[(1024,666073),(1024,201730)]),(z486,[(1024,666073),(1024,201730)]),(z487,[(1024,666073),(1024,201730)]),(z488,[(1024,469657),(1024,201730)]),(z489,[(1024,469657),(1024,201730)]),(z490,[(1024,205954),(1024,208330)]),(z491,[(1024,205954),(1024,208330)])]
def b41 : List (List Nat × List (Nat × Nat)) := [(z492,[(1024,469657),(1024,201730)]),(z493,[(1024,469657),(1024,201730)]),(z494,[(1024,469657),(1024,204930)]),(z495,[(1024,201730),(1024,5314)]),(z496,[(1024,201730),(1024,5314)]),(z497,[(1024,468172),(1024,201730)]),(z498,[(1024,468172),(1024,201826)]),(z499,[(1024,1222),(1024,132298)]),(z500,[(1024,208326),(1024,132294)]),(z501,[(1024,208326),(1024,132294)]),(z502,[(1024,1222),(1024,5314)]),(z503,[(1024,5314),(1024,99529)])]
def b42 : List (List Nat × List (Nat × Nat)) := [(z504,[(1024,99529),(1024,132298)]),(z505,[(1024,1222),(1024,5314)]),(z506,[(1024,201730),(1024,208330)]),(z507,[(1024,99529),(1024,132298)]),(z508,[(1024,99529),(1024,1222)]),(z509,[(1024,464076),(1024,99529)]),(z510,[(1024,206284),(1024,1222)]),(z511,[(1024,208330),(1024,1222)]),(z512,[(1024,666073),(1024,1222)]),(z513,[(1024,666073),(1024,1222)]),(z514,[(1024,208330),(1024,1222)]),(z515,[(1024,666073),(1024,1222)])]
def b43 : List (List Nat × List (Nat × Nat)) := [(z516,[(1024,132298),(1024,205954)]),(z517,[(1024,132298),(1024,1222)]),(z518,[(1024,470218),(1024,205954)]),(z519,[(1024,1222),(1024,132298)]),(z520,[(1024,1222),(1024,201730)]),(z521,[(1024,132298),(1024,201730)]),(z522,[(1024,1222),(1024,208330)]),(z523,[(1024,208330),(1024,132298)]),(z524,[(1024,201730),(1024,208330)]),(z525,[(1024,1222),(1024,132298)]),(z526,[(1024,1222),(1024,132298)]),(z527,[(1024,201730),(1024,208330)])]
def b44 : List (List Nat × List (Nat × Nat)) := [(z528,[(1024,1222),(1024,132298)]),(z529,[(1024,1222),(1024,201730)]),(z530,[(1024,132099),(1024,2178)]),(z531,[(1024,469657),(1024,1222)]),(z532,[(1024,132297),(1024,201730)]),(z533,[(1024,1222),(1024,132297)]),(z534,[(1024,1222),(1024,5314)]),(z535,[(1024,1222),(1024,5314)]),(z536,[(1024,1222),(1024,5314)]),(z537,[(1024,5314),(1024,99529)]),(z538,[(1024,1222),(1024,5314)]),(z539,[(1024,468166),(1024,132298)])]
def b45 : List (List Nat × List (Nat × Nat)) := [(z540,[(1024,1222),(1024,5314)]),(z541,[(1024,1222),(1024,5314)]),(z542,[(1024,1222),(1024,5314)]),(z543,[(1024,1222),(1024,5314)]),(z544,[(1024,5314),(1024,99529)]),(z545,[(1024,1222),(1024,5314)]),(z546,[(1024,208330),(1024,132298)]),(z547,[(1024,208330),(1024,132298)]),(z548,[(1024,468172),(1024,1222)]),(z549,[(1024,468172),(1024,99526)]),(z550,[(1024,132298),(1024,99529)]),(z551,[(1024,132298),(1024,99529)])]
def b46 : List (List Nat × List (Nat × Nat)) := [(z552,[(1024,132298),(1024,1222)]),(z553,[(1024,132298),(1024,1222)]),(z554,[(1024,1222),(1024,99529)]),(z555,[(1024,1222),(1024,99529)]),(z556,[(1024,5314),(1024,1222)]),(z557,[(1024,197638),(1024,1222)]),(z558,[(1024,665606),(1024,5324)]),(z559,[(1024,132298),(1024,1222)]),(z560,[(1024,666062),(1024,197638)]),(z561,[(1024,110242),(1024,1222)]),(z562,[(1024,1222),(1024,132298)]),(z563,[(1024,1222),(1024,99529)])]
def b47 : List (List Nat × List (Nat × Nat)) := [(z564,[(1024,1222),(1024,99529)]),(z565,[(1024,132298),(1024,1222)]),(z566,[(1024,132298),(1024,99529)]),(z567,[(1024,132298),(1024,1222)]),(z568,[(1024,1222),(1024,99529)]),(z569,[]),(z570,[]),(z571,[]),(z572,[(1024,1136),(1024,25035)]),(z573,[(1024,1136),(1024,99344)]),(z574,[(1024,121858),(1024,1144)]),(z575,[(1024,121858),(1024,1144)])]
def b48 : List (List Nat × List (Nat × Nat)) := [(z576,[(104,0)]),(z577,[]),(z578,[]),(z579,[(1024,25035),(1024,205826)]),(z580,[(1024,24226),(1024,204802)]),(z581,[(1024,25035),(1024,1226)]),(z582,[(1024,24226),(1024,1225)]),(z583,[(1024,1144),(1024,24706)]),(z584,[(1024,1144),(1024,99352)]),(z585,[(1024,1144),(1024,99352)]),(z586,[(1024,1144),(1024,99352)]),(z587,[(1024,132121),(1024,1144)])]
def b49 : List (List Nat × List (Nat × Nat)) := [(z588,[(1024,1144),(1024,99352)]),(z589,[(1024,99352),(1024,1144)]),(z590,[(1024,99529),(1024,132298)]),(z591,[(1024,1222),(1024,132298)]),(z592,[(1024,1144),(1024,23650)]),(z593,[(1024,99352),(1024,1144)]),(z594,[(1024,1222),(1024,99529)]),(z595,[(1024,208330),(1024,1144)]),(z596,[(1024,123531),(1024,204898)]),(z597,[(1024,99529),(1024,1222)]),(z598,[(1024,10905),(1024,25227)]),(z599,[(1024,10905),(1024,1222)])]
def b50 : List (List Nat × List (Nat × Nat)) := [(z600,[(1024,201730),(1024,207882)]),(z601,[(1024,201730),(1024,208330)]),(z602,[(1024,699865),(1024,1222)]),(z603,[(1024,110242),(1024,1131)]),(z604,[]),(z605,[(1024,666062),(1024,198090)]),(z606,[(1024,132330),(1024,1254)]),(z607,[(1024,198090),(1024,666062)]),(z608,[(1024,204898),(1024,207978)]),(z609,[(1024,204898),(1024,207978)]),(z610,[(1024,699513),(1024,204898)]),(z611,[(1024,204898),(1024,197638)])]
def b51 : List (List Nat × List (Nat × Nat)) := [(z612,[(1024,205922),(1024,197738)]),(z613,[(1024,197738),(1024,205922)]),(z614,[(1024,689272),(1024,204898)]),(z615,[(1024,206284),(1024,208330)]),(z616,[(1024,99801),(1024,198090)]),(z617,[(1024,204811),(1024,197638)]),(z618,[(1024,204898),(1024,1222)]),(z619,[(1024,197770),(1024,10442)]),(z620,[(1024,208330),(1024,1222)]),(z621,[(1024,99529),(1024,1222)]),(z622,[(1024,689260),(1024,1222)]),(z623,[(1024,197770),(1024,10442)])]
def b52 : List (List Nat × List (Nat × Nat)) := [(z624,[(1024,99529),(1024,1222)]),(z625,[(1024,99529),(1024,1222)]),(z626,[(1024,665721),(1024,1222)]),(z627,[(1024,99529),(1024,1222)]),(z628,[(1024,99529),(1024,207978)]),(z629,[(1024,1222),(1024,99529)]),(z630,[(1024,99530),(1024,1254)]),(z631,[(1024,1222),(1024,99529)]),(z632,[(1024,132298),(1024,1222)]),(z633,[(1024,208330),(1024,1222)]),(z634,[(1024,10702),(1024,13771)]),(z635,[(1024,205826),(1024,10713)])]
def b53 : List (List Nat × List (Nat × Nat)) := [(z636,[(1024,13771),(1024,10702)]),(z637,[(1024,204802),(1024,10713)]),(z638,[(1024,204802),(1024,208330)]),(z639,[(1024,111814),(1024,1497)]),(z640,[(1024,111814),(1024,1226)]),(z641,[(1024,1226),(1024,10713)]),(z642,[(1024,13510),(1024,1225)]),(z643,[(1024,24226),(1024,1225)]),(z644,[(1024,699513),(1024,201826)]),(z645,[(1024,204898),(1024,213098)]),(z646,[(1024,99529),(1024,1222)]),(z647,[(1024,99339),(1024,1131)])]
def b54 : List (List Nat × List (Nat × Nat)) := [(z648,[(1024,10905),(1024,25227)]),(z649,[(1024,10905),(1024,201730)]),(z650,[(1024,10904),(1024,201730)]),(z651,[(1024,201730),(1024,207882)]),(z652,[(1024,132330),(1024,99561)]),(z653,[(1024,132330),(1024,1254)]),(z654,[(1024,1254),(1024,99561)]),(z655,[(1024,1123),(1024,2146)]),(z656,[(1024,201730),(1024,207978)]),(z657,[(1024,201730),(1024,207978)]),(z658,[(1024,10905),(1024,201730)]),(z659,[(1024,10904),(1024,201730)])]
def b55 : List (List Nat × List (Nat × Nat)) := [(z660,[(1024,679947),(1024,10905)]),(z661,[(1024,10905),(1024,201730)]),(z662,[(1024,665625),(1024,10905)]),(z663,[(1024,10905),(1024,123534)]),(z664,[(1024,10905),(1024,197638)]),(z665,[(1024,10905),(1024,197642)]),(z666,[(1024,10905),(1024,197642)]),(z667,[(1024,13977),(1024,201730)]),(z668,[(1024,10905),(1024,201730)]),(z669,[(1024,16025),(1024,201730)]),(z670,[(1024,10905),(1024,204803)]),(z671,[(1024,10905),(1024,204898)])]
def b56 : List (List Nat × List (Nat × Nat)) := [(z672,[(1024,10905),(1024,204898)]),(z673,[(1024,10905),(1024,204802)]),(z674,[(1024,10905),(1024,201730)]),(z675,[(1024,201730),(1024,207978)]),(z676,[(1024,201730),(1024,207882)]),(z677,[(1024,204898),(1024,207978)]),(z678,[(1024,201730),(1024,197638)]),(z679,[(1024,10904),(1024,1222)]),(z680,[(1024,197770),(1024,10442)]),(z681,[(1024,10905),(1024,99529)]),(z682,[(1024,679947),(1024,1222)]),(z683,[(1024,206284),(1024,1144)])]
def b57 : List (List Nat × List (Nat × Nat)) := [(z684,[(1024,1144),(1024,99352)]),(z685,[(1024,1144),(1024,99352)]),(z686,[(1024,1144),(1024,10713)]),(z687,[(1024,1144),(1024,99352)]),(z688,[(1024,1144),(1024,99352)]),(z689,[(1024,1144),(1024,99352)]),(z690,[(1024,10905),(1024,1222)]),(z691,[(1024,665625),(1024,1222)]),(z692,[(1024,1222),(1024,10905)]),(z693,[(1024,10905),(1024,1222)]),(z694,[(1024,1222),(1024,10905)]),(z695,[(1024,201730),(1024,1222)])]
def b58 : List (List Nat × List (Nat × Nat)) := [(z696,[(1024,1222),(1024,10905)]),(z697,[(1024,10905),(1024,1177)]),(z698,[(1024,201730),(1024,1222)]),(z699,[(1024,1222),(1024,10905)]),(z700,[(1024,1144),(1024,99352)]),(z701,[(1024,10905),(1024,1226)]),(z702,[(1024,132121),(1024,1144)]),(z703,[(1024,1144),(1024,99352)]),(z704,[(1024,16025),(1024,1222)]),(z705,[(1024,99529),(1024,208010)]),(z706,[(1024,132760),(1024,1222)]),(z707,[(1024,132298),(1024,99529)])]
def b59 : List (List Nat × List (Nat × Nat)) := [(z708,[(1024,132298),(1024,99529)]),(z709,[(1024,132298),(1024,1222)]),(z710,[(1024,132298),(1024,1222)]),(z711,[(1024,10905),(1024,99331)]),(z712,[(1024,23650),(1024,1144)]),(z713,[(1024,99352),(1024,1144)]),(z714,[(1024,1222),(1024,10905)]),(z715,[(1024,1222),(1024,99529)]),(z716,[(1024,10905),(1024,99529)]),(z717,[(1024,1222),(1024,207978)]),(z718,[(1024,99529),(1024,201730)]),(z719,[(1024,1222),(1024,99529)])]
def b60 : List (List Nat × List (Nat × Nat)) := [(z720,[(1024,1222),(1024,99529)]),(z721,[(1024,1222),(1024,99529)]),(z722,[(1024,5314),(1024,1222)]),(z723,[(1024,115146),(1024,1222)]),(z724,[(1024,5314),(1024,1222)]),(z725,[(1024,122314),(1024,1222)]),(z726,[(1024,5314),(1024,122314)]),(z727,[(1024,10886),(1024,197638)]),(z728,[(1024,140761),(1024,122314)]),(z729,[(1024,10886),(1024,197638)]),(z730,[(1024,5314),(1024,1222)]),(z731,[(1024,197638),(1024,1222)])]
def b61 : List (List Nat × List (Nat × Nat)) := [(z732,[(1024,5314),(1024,1222)]),(z733,[(1024,197638),(1024,1222)]),(z734,[(1024,5314),(1024,99529)]),(z735,[(1024,10886),(1024,99529)]),(z736,[(1024,5314),(1024,1222)]),(z737,[(1024,132298),(1024,1222)]),(z738,[(1024,5314),(1024,1222)]),(z739,[(1024,197638),(1024,1222)]),(z740,[(1024,106690),(1024,99529)]),(z741,[(1024,10886),(1024,99529)]),(z742,[(1024,5314),(1024,1222)]),(z743,[(1024,197638),(1024,1222)])]
def b62 : List (List Nat × List (Nat × Nat)) := [(z744,[(1024,140761),(1024,1222)]),(z745,[(1024,1222),(1024,10886)]),(z746,[(1024,5314),(1024,1222)]),(z747,[(1024,197638),(1024,1222)]),(z748,[(1024,5314),(1024,122314)]),(z749,[(1024,197638),(1024,5314)]),(z750,[(1024,5314),(1024,1222)]),(z751,[(1024,197638),(1024,1222)]),(z752,[(1024,5314),(1024,1222)]),(z753,[(1024,197638),(1024,1222)]),(z754,[(1024,5314),(1024,99529)]),(z755,[(1024,10886),(1024,99529)])]
def b63 : List (List Nat × List (Nat × Nat)) := [(z756,[(1024,1222),(1024,5314)]),(z757,[(1024,1222),(1024,10886)]),(z758,[(1024,201730),(1024,5314)]),(z759,[(96,1),(1024,5314),(1024,1222)]),(z760,[]),(z761,[]),(z762,[]),(z763,[]),(z764,[]),(z765,[(1024,1144),(1024,99352)]),(z766,[(1024,1144),(1024,99352)]),(z767,[(1024,5314),(1024,1222)])]
def b64 : List (List Nat × List (Nat × Nat)) := [(z768,[(96,1),(1024,5314),(1024,1222)]),(z769,[]),(z770,[(1024,1144),(1024,5314)]),(z771,[(128,1),(1024,132121),(1024,1144)]),(z772,[(1024,114892),(1024,1222)]),(z773,[(1024,122060),(1024,1222)]),(z774,[(1024,5314),(1024,1222)]),(z775,[(1024,122060),(1024,1222)]),(z776,[(1024,5314),(1024,1222)]),(z777,[(1024,1144),(1024,99352)]),(z778,[(1024,1144),(1024,99352)]),(z779,[(1024,197638),(1024,1144)])]
def b65 : List (List Nat × List (Nat × Nat)) := [(z780,[(1024,5314),(1024,1222)]),(z781,[(1024,5314),(1024,201730)]),(z782,[(72,0)]),(z783,[]),(z784,[]),(z785,[(1024,1144),(1024,5314)]),(z786,[(1024,1144),(1024,5314)]),(z787,[(1024,122060),(1024,1222)]),(z788,[(1024,122060),(1024,1222)]),(z789,[(1024,5314),(1024,1222)]),(z790,[(1024,207992),(1024,1222)]),(z791,[(1024,197638),(1024,1222)])]
def b66 : List (List Nat × List (Nat × Nat)) := [(z792,[(1024,99529),(1024,1222)]),(z793,[(1024,132298),(1024,1222)]),(z794,[(56,0),(1024,207882),(1024,201730)]),(z795,[(1024,208330),(1024,1222)]),(z796,[(1024,208330),(1024,201730)]),(z797,[(1024,207882),(1024,201730)]),(z798,[(1024,207978),(1024,107724)]),(z799,[(1024,207978),(1024,99529)]),(z800,[(1024,5314),(1024,1222)]),(z801,[(1024,10886),(1024,197638)]),(z802,[(1024,207978),(1024,107724)]),(z803,[(1024,198089),(1024,237698)])]
def b67 : List (List Nat × List (Nat × Nat)) := [(z804,[(1024,198090),(1024,1254)]),(z805,[(1024,132329),(1024,1254)]),(z806,[(1024,197638),(1024,1222)]),(z807,[(1024,198089),(1024,666073)]),(z808,[(1024,207992),(1024,205954)]),(z809,[(1024,208329),(1024,204930)]),(z810,[(1024,205260),(1024,208329)]),(z811,[(1024,207992),(1024,204898)]),(z812,[(1024,207978),(1024,204898)]),(z813,[(1024,107724),(1024,204898)]),(z814,[(1024,99786),(1024,666073)]),(z815,[(1024,206284),(1024,1222)])]
def b68 : List (List Nat × List (Nat × Nat)) := [(z816,[(1024,197638),(1024,1222)]),(z817,[(1024,207992),(1024,1222)]),(z818,[(1024,207992),(1024,99529)]),(z819,[(1024,5314),(1024,1222)]),(z820,[(1024,197752),(1024,1254)]),(z821,[(1024,207992),(1024,1222)]),(z822,[(1024,197638),(1024,1222)]),(z823,[(1024,10442),(1024,1222)]),(z824,[(1024,10922),(1024,1222)]),(z825,[(1024,207992),(1024,99529)]),(z826,[(1024,132298),(1024,1222)]),(z827,[(1024,208010),(1024,1222)])]
def b69 : List (List Nat × List (Nat × Nat)) := [(z828,[(1024,208330),(1024,1222)]),(z829,[(1024,208329),(1024,1222)]),(z830,[(1024,132297),(1024,1222)]),(z831,[(1024,213112),(1024,1222)]),(z832,[(1024,5314),(1024,1222)]),(z833,[(1024,5314),(1024,1222)]),(z834,[(1024,197638),(1024,1222)]),(z835,[(1024,207992),(1024,99529)]),(z836,[(1024,204898),(1024,1222)]),(z837,[(1024,1222),(1024,99529)]),(z838,[(1024,1222),(1024,99529)]),(z839,[(1024,99529),(1024,1222)])]
def b70 : List (List Nat × List (Nat × Nat)) := [(z840,[(1024,1482),(1024,5593)]),(z841,[(1024,208329),(1024,10713)]),(z842,[(1024,198086),(1024,234626)]),(z843,[(1024,198090),(1024,234594)]),(z844,[(1024,198086),(1024,99561)]),(z845,[(1024,198090),(1024,99558)]),(z846,[(1024,198086),(1024,660953)]),(z847,[(1024,198090),(1024,660953)]),(z848,[(1024,689272),(1024,201858)]),(z849,[(1024,202188),(1024,208326)]),(z850,[(1024,208010),(1024,201826)]),(z851,[(1024,689272),(1024,201826)])]
def b71 : List (List Nat × List (Nat × Nat)) := [(z852,[(1024,208330),(1024,201826)]),(z853,[(1024,1482),(1024,660953)]),(z854,[(1024,208330),(1024,99529)]),(z855,[(1024,689272),(1024,99529)]),(z856,[(1024,208326),(1024,99529)]),(z857,[(1024,208010),(1024,99526)]),(z858,[(1024,689272),(1024,99526)]),(z859,[(1024,208330),(1024,99526)]),(z860,[(1024,5314),(1024,25030)]),(z861,[(1024,140761),(1024,24010)]),(z862,[(1024,213112),(1024,1222)]),(z863,[(1024,5314),(1024,1222)])]
def b72 : List (List Nat × List (Nat × Nat)) := [(z864,[(96,1),(1024,5314),(1024,1222)]),(z865,[(1024,197638),(1024,1222)]),(z866,[(1024,5314),(1024,1222)]),(z867,[(1024,197638),(1024,1222)]),(z868,[(1024,10905),(1024,201730)]),(z869,[(1024,197638),(1024,5314)]),(z870,[(1024,665625),(1024,10905)]),(z871,[(1024,10905),(1024,107545)]),(z872,[(1024,207882),(1024,9420)]),(z873,[(1024,198090),(1024,234498)]),(z874,[(1024,198090),(1024,1254)]),(z875,[(1024,198090),(1024,469657)])]
def b73 : List (List Nat × List (Nat × Nat)) := [(z876,[(1024,10905),(1024,201730)]),(z877,[(1024,208025),(1024,122060)]),(z878,[(1024,207882),(1024,9420)]),(z879,[(1024,9420),(1024,10905)]),(z880,[(1024,208536),(1024,201730)]),(z881,[(1024,208330),(1024,201730)]),(z882,[(1024,469657),(1024,201730)]),(z883,[(1024,208330),(1024,1144)]),(z884,[(1024,1222),(1024,10905)]),(z885,[(1024,208025),(1024,1222)]),(z886,[(1024,207992),(1024,1222)]),(z887,[(1024,207992),(1024,99529)])]
def b74 : List (List Nat × List (Nat × Nat)) := [(z888,[(1024,208330),(1024,1222)]),(z889,[(1024,1144),(1024,5314)]),(z890,[(1024,208330),(1024,99352)]),(z891,[(1024,1144),(1024,99352)]),(z892,[(1024,207882),(1024,1222)]),(z893,[(1024,10905),(1024,1222)]),(z894,[(1024,1222),(1024,208010)]),(z895,[(1024,208330),(1024,1222)]),(z896,[(1024,208330),(1024,1222)]),(z897,[(1024,111814),(1024,99529)]),(z898,[(1024,208330),(1024,1222)]),(z899,[(1024,197770),(1024,132298)])]
def b75 : List (List Nat × List (Nat × Nat)) := [(z900,[(1024,132298),(1024,197770)]),(z901,[(1024,197770),(1024,132298)]),(z902,[(1024,205964),(1024,1222)]),(z903,[(1024,99529),(1024,1222)]),(z904,[(1024,99529),(1024,1222)]),(z905,[(1024,106690),(1024,99529)]),(z906,[(1024,106690),(1024,99529)]),(z907,[(1024,99529),(1024,132298)]),(z908,[(1024,1222),(1024,99529)]),(z909,[(1024,1222),(1024,5314)]),(z910,[(80,1),(144,1),(1024,1222),(1024,5314)]),(z911,[(1024,99529),(1024,1222)])]
def b76 : List (List Nat × List (Nat × Nat)) := [(z912,[(1024,100024),(1024,1222)]),(z913,[(1024,711778),(1024,1222)]),(z914,[(1024,99529),(1024,132298)]),(z915,[(1024,99529),(1024,132298)]),(z916,[(144,1),(184,1)]),(z917,[]),(z918,[(1024,99787),(1024,122530)]),(z919,[(1024,1486),(1024,122530)]),(z920,[(1024,1222),(1024,99529)]),(z921,[]),(z922,[]),(z923,[(1024,671347),(1024,205954)])]
def b77 : List (List Nat × List (Nat × Nat)) := [(z924,[(184,1)]),(z925,[(1024,712834),(1024,1222)]),(z926,[(1024,115362),(1024,1222)]),(z927,[(1024,132793),(1024,99529)]),(z928,[(1024,115362),(1024,1222)]),(z929,[(1024,704610),(1024,1222)]),(z930,[(1024,132298),(1024,1222)]),(z931,[(1024,1222),(1024,99529)]),(z932,[(144,2),(184,1)]),(z933,[(144,1),(184,1)]),(z934,[(144,1),(1024,1222),(1024,99529)]),(z935,[(1024,201730),(1024,114338)])]
def b78 : List (List Nat × List (Nat × Nat)) := [(z936,[(1024,1222),(1024,114338)]),(z937,[(112,1),(1024,1222),(1024,114338)]),(z938,[(1024,1222),(1024,99529)]),(z939,[(1024,132298),(1024,99529)]),(z940,[(1024,1222),(1024,99529)]),(z941,[(1024,132298),(1024,99529)]),(z942,[(1024,132298),(1024,1222)]),(z943,[(1024,1222),(1024,99529)]),(z944,[(1024,483979),(1024,1222)]),(z945,[(1024,115362),(1024,1222)]),(z946,[(1024,483980),(1024,1222)]),(z947,[(1024,1222),(1024,99529)])]
def b79 : List (List Nat × List (Nat × Nat)) := [(z948,[(1024,472715),(1024,205954)]),(z949,[(1024,484012),(1024,1222)]),(z950,[(1024,99529),(1024,132298)]),(z951,[(128,0),(144,0)]),(z952,[(128,0)]),(z953,[(1024,483979),(1024,122530)]),(z954,[]),(z955,[(1024,204898),(1024,122530)]),(z956,[(1024,712834),(1024,1222)]),(z957,[(1024,122530),(1024,1222)]),(z958,[(1024,132793),(1024,99529)]),(z959,[(1024,132298),(1024,1222)])]
def b80 : List (List Nat × List (Nat × Nat)) := [(z960,[(1024,122530),(1024,1222)]),(z961,[(1024,122530),(1024,1222)]),(z962,[(1024,100024),(1024,122530)]),(z963,[(1024,711778),(1024,1222)]),(z964,[(1024,99529),(1024,1222)]),(z965,[(1024,122530),(1024,1222)]),(z966,[(1024,99529),(1024,1222)]),(z967,[(1024,201730),(1024,122530)]),(z968,[(1024,1222),(1024,122530)]),(z969,[(1024,1222),(1024,99529)]),(z970,[(1024,122530),(1024,99529)]),(z971,[(1024,1222),(1024,99529)])]
def b81 : List (List Nat × List (Nat × Nat)) := [(z972,[(1024,99529),(1024,1222)]),(z973,[(1024,122530),(1024,1222)]),(z974,[(1024,483979),(1024,205954)]),(z975,[(1024,483979),(1024,204898)]),(z976,[(1024,206284),(1024,1222)]),(z977,[(1024,484012),(1024,1222)]),(z978,[(1024,483979),(1024,99529)]),(z979,[(1024,484012),(1024,1222)]),(z980,[(1024,647857),(1024,1222)]),(z981,[(1024,483979),(1024,99529)]),(z982,[(1024,484012),(1024,1222)]),(z983,[(1024,99529),(1024,1222)])]
def b82 : List (List Nat × List (Nat × Nat)) := [(z984,[(1024,647857),(1024,1222)]),(z985,[(1024,483979),(1024,201730)]),(z986,[(1024,484012),(1024,1222)]),(z987,[(1024,1222),(1024,99529)]),(z988,[(1024,99529),(1024,132298)]),(z989,[(1024,99529),(1024,1222)]),(z990,[(1024,201730),(1024,208330)]),(z991,[(1024,1222),(1024,132298)]),(z992,[(1024,99529),(1024,1222)]),(z993,[]),(z994,[(1024,666062),(1024,205954)]),(z995,[(1024,666062),(1024,112290)])]
def b83 : List (List Nat × List (Nat × Nat)) := [(z996,[(1024,666062),(1024,204930)]),(z997,[]),(z998,[]),(z999,[(1024,238723),(1024,2278)]),(z1000,[(1024,666062),(1024,208330)]),(z1001,[(1024,111299),(1024,2278)]),(z1002,[(1024,133354),(1024,2278)]),(z1003,[(1024,471274),(1024,205954)]),(z1004,[]),(z1005,[(1024,205954),(1024,208330)]),(z1006,[(1024,205954),(1024,122530)]),(z1007,[(1024,666073),(1024,205954)])]
def b84 : List (List Nat × List (Nat × Nat)) := [(z1008,[(1024,666073),(1024,205954)]),(z1009,[(1024,666073),(1024,205922)]),(z1010,[(1024,680395),(1024,204930)]),(z1011,[(1024,205954),(1024,208330)]),(z1012,[(1024,204898),(1024,208330)]),(z1013,[(1024,204898),(1024,208330)]),(z1014,[(1024,204898),(1024,208330)]),(z1015,[(1024,204898),(1024,208330)]),(z1016,[(1024,204898),(1024,122530)]),(z1017,[(1024,699865),(1024,204898)]),(z1018,[(1024,666073),(1024,208330)]),(z1019,[(1024,699865),(1024,204898)])]
def b85 : List (List Nat × List (Nat × Nat)) := [(z1020,[(1024,699865),(1024,204898)]),(z1021,[(1024,666073),(1024,204898)]),(z1022,[(1024,205954),(1024,208330)]),(z1023,[(1024,205954),(1024,208330)]),(z1024,[(1024,205954),(1024,208330)]),(z1025,[(1024,205954),(1024,208330)]),(z1026,[(1024,204898),(1024,208330)]),(z1027,[(1024,206284),(1024,666062),(1024,208330)]),(z1028,[(1024,204898),(1024,208490)]),(z1029,[(1024,205954),(1024,1222)]),(z1030,[(1024,204898),(1024,1222)]),(z1031,[(1024,99529),(1024,1222)])]
def b86 : List (List Nat × List (Nat × Nat)) := [(z1032,[(1024,132298),(1024,1222)]),(z1033,[(1024,484012),(1024,1222)]),(z1034,[(1024,99529),(1024,205954)]),(z1035,[(1024,206284),(1024,1222)]),(z1036,[(1024,205954),(1024,1222)]),(z1037,[(1024,713164),(1024,1222)]),(z1038,[(1024,206284),(1024,1222)]),(z1039,[(1024,99529),(1024,1222)]),(z1040,[(1024,99529),(1024,1222)]),(z1041,[(1024,99529),(1024,1222)]),(z1042,[(1024,99529),(1024,132298)]),(z1043,[(1024,10914),(1024,2246)])]
def b87 : List (List Nat × List (Nat × Nat)) := [(z1044,[(1024,208330),(1024,1222)]),(z1045,[(1024,99529),(1024,1222)]),(z1046,[(1024,100024),(1024,1222)]),(z1047,[(1024,99529),(1024,132298)]),(z1048,[(1024,99561),(1024,1254)]),(z1049,[(1024,100024),(1024,1222)]),(z1050,[(1024,99529),(1024,1222)]),(z1051,[(1024,99529),(1024,1222)]),(z1052,[(1024,699865),(1024,1222)]),(z1053,[(1024,99529),(1024,1222)]),(z1054,[(1024,666073),(1024,1222)]),(z1055,[(1024,112290),(1024,1222)])]
def b88 : List (List Nat × List (Nat × Nat)) := [(z1056,[(1024,666073),(1024,1222)]),(z1057,[(1024,99529),(1024,132298)]),(z1058,[(1024,208330),(1024,1222)]),(z1059,[(1024,99529),(1024,132298)]),(z1060,[(1024,100024),(1024,1222)]),(z1061,[(1024,99529),(1024,1222)]),(z1062,[(1024,99529),(1024,1222)]),(z1063,[(1024,99529),(1024,1222)]),(z1064,[(1024,99529),(1024,132298)]),(z1065,[(1024,100024),(1024,122530)]),(z1066,[(1024,99529),(1024,132298)]),(z1067,[(1024,132298),(1024,208330)])]
def b89 : List (List Nat × List (Nat × Nat)) := [(z1068,[(1024,99529),(1024,1222)]),(z1069,[(1024,132298),(1024,1222)]),(z1070,[(1024,132298),(1024,1222)]),(z1071,[(1024,132298),(1024,1222)]),(z1072,[(1024,132298),(1024,1222)]),(z1073,[(1024,470218),(1024,205954)]),(z1074,[(1024,99529),(1024,132298)]),(z1075,[(1024,99529),(1024,1222)]),(z1076,[(1024,132298),(1024,1222)]),(z1077,[(1024,470218),(1024,1222)]),(z1078,[(1024,99529),(1024,132298)]),(z1079,[(1024,99529),(1024,1222)])]
def b90 : List (List Nat × List (Nat × Nat)) := [(z1080,[(1024,666073),(1024,1222)]),(z1081,[(1024,132793),(1024,1222)]),(z1082,[(1024,99529),(1024,1222)]),(z1083,[(1024,99529),(1024,1222)]),(z1084,[(1024,208490),(1024,1222)]),(z1085,[(1024,132298),(1024,1222)]),(z1086,[(1024,132298),(1024,1222)]),(z1087,[(1024,206449),(1024,1222)]),(z1088,[(1024,213610),(1024,1222)]),(z1089,[(1024,122530),(1024,1222)]),(z1090,[(1024,671353),(1024,1222)]),(z1091,[(1024,1222),(1024,99529)])]
def b91 : List (List Nat × List (Nat × Nat)) := [(z1092,[(1024,705145),(1024,1222)]),(z1093,[(1024,671353),(1024,1222)]),(z1094,[(1024,1222),(1024,132298)]),(z1095,[(1024,132298),(1024,99529)]),(z1096,[(1024,1222),(1024,99529),(1024,110242)]),(z1097,[(1024,1222),(1024,99529)]),(z1098,[(1024,99529),(1024,1222)]),(z1099,[(1024,206284),(1024,99529)]),(z1100,[(1024,132298),(1024,99529)]),(z1101,[(1024,132298),(1024,99529)]),(z1102,[(1024,699865),(1024,99529)]),(z1103,[(1024,699865),(1024,132298)])]
def b92 : List (List Nat × List (Nat × Nat)) := [(z1104,[(1024,132298),(1024,99529)]),(z1105,[(1024,132298),(1024,208330)]),(z1106,[(1024,470218),(1024,205954)]),(z1107,[(1024,99529),(1024,132298)]),(z1108,[(1024,99459),(1024,100482)]),(z1109,[(1024,100482),(1024,2278)]),(z1110,[(1024,133354),(1024,2278)]),(z1111,[(1024,1222),(1024,204898)]),(z1112,[(1024,1222),(1024,99529)]),(z1113,[(1024,132298),(1024,204898)]),(z1114,[(1024,204898),(1024,1222)]),(z1115,[(1024,204898),(1024,1222)])]
def b93 : List (List Nat × List (Nat × Nat)) := [(z1116,[(1024,204898),(1024,1222)]),(z1117,[(1024,122530),(1024,1222)]),(z1118,[(1024,666073),(1024,1222)]),(z1119,[(1024,1222),(1024,132298)]),(z1120,[(1024,204898),(1024,1222)]),(z1121,[(1024,1222),(1024,99529)]),(z1122,[(1024,99529),(1024,1222)]),(z1123,[(1024,99529),(1024,1222)]),(z1124,[(1024,1222),(1024,99529)]),(z1125,[(1024,1222),(1024,208330)]),(z1126,[(1024,99529),(1024,1222)]),(z1127,[(1024,99529),(1024,208330)])]
def b94 : List (List Nat × List (Nat × Nat)) := [(z1128,[(1024,208330),(1024,1222)]),(z1129,[(1024,1222),(1024,99529)]),(z1130,[(1024,132298),(1024,204898)]),(z1131,[(1024,99529),(1024,208330)]),(z1132,[(1024,99529),(1024,208330)]),(z1133,[(1024,132195),(1024,133218)]),(z1134,[(1024,100585),(1024,2278)]),(z1135,[(1024,1222),(1024,132298)]),(z1136,[(1024,132298),(1024,1222)]),(z1137,[(1024,99529),(1024,1222)]),(z1138,[(1024,1222),(1024,132298),(1024,208330)]),(z1139,[(1024,208330),(1024,1222)])]
def b95 : List (List Nat × List (Nat × Nat)) := [(z1140,[(1024,99529),(1024,1222)]),(z1141,[(1024,669131),(1024,205826)]),(z1142,[(1024,666073),(1024,205826)]),(z1143,[(1024,699865),(1024,204802)]),(z1144,[(1024,470218),(1024,99529)]),(z1145,[(1024,132298),(1024,1225)]),(z1146,[(1024,100024),(1024,1222)]),(z1147,[(1024,99529),(1024,1222)]),(z1148,[(1024,666062),(1024,201858)]),(z1149,[(1024,680395),(1024,201858)]),(z1150,[(1024,699865),(1024,201826)]),(z1151,[(1024,100024),(1024,132294)])]
def b96 : List (List Nat × List (Nat × Nat)) := [(z1152,[(1024,699865),(1024,99526)]),(z1153,[(1024,99529),(1024,1222)]),(z1154,[(1024,99529),(1024,1222)]),(z1155,[(1024,99529),(1024,1222)]),(z1156,[]),(z1157,[]),(z1158,[(1024,204898),(1024,213610)]),(z1159,[(1024,206449),(1024,1222)]),(z1160,[(1024,99529),(1024,1222)]),(z1161,[(1024,100024),(1024,1222)]),(z1162,[(1024,99529),(1024,1222)]),(z1163,[(1024,1222),(1024,132298)])]
def b97 : List (List Nat × List (Nat × Nat)) := [(z1164,[(1024,1222),(1024,132298)]),(z1165,[(1024,1222),(1024,99529)]),(z1166,[(1024,1222),(1024,99529)]),(z1167,[(1024,705145),(1024,99529)]),(z1168,[(1024,99529),(1024,132298)]),(z1169,[(1024,1222),(1024,132298)]),(z1170,[(1024,99529),(1024,1222)]),(z1171,[]),(z1172,[(1024,100024),(1024,1222)]),(z1173,[(1024,669131),(1024,201730)]),(z1174,[(1024,109218),(1024,201730)]),(z1175,[(1024,483979),(1024,201730)])]
def b98 : List (List Nat × List (Nat × Nat)) := [(z1176,[(1024,201730),(1024,208330)]),(z1177,[(1024,201730),(1024,208330)]),(z1178,[(1024,469646),(1024,201730)]),(z1179,[(1024,469646),(1024,205954)]),(z1180,[(1024,201730),(1024,208330)]),(z1181,[(1024,238723),(1024,2278)]),(z1182,[(1024,234499),(1024,205954)]),(z1183,[(1024,2278),(1024,204898)]),(z1184,[(1024,238723),(1024,204898)]),(z1185,[(1024,238723),(1024,100585)]),(z1186,[(1024,133354),(1024,100585)]),(z1187,[(1024,133354),(1024,2278)])]
def b99 : List (List Nat × List (Nat × Nat)) := [(z1188,[(1024,238723),(1024,201730)]),(z1189,[(1024,100585),(1024,201730)]),(z1190,[(1024,133354),(1024,204898)]),(z1191,[(1024,2278),(1024,100585)]),(z1192,[(1024,133354),(1024,201730)]),(z1193,[(1024,99529),(1024,1222)]),(z1194,[(1024,1155),(1024,2178)]),(z1195,[(1024,1123),(1024,2146)]),(z1196,[(1024,680395),(1024,201730)]),(z1197,[(1024,201730),(1024,208330)]),(z1198,[(1024,133354),(1024,100585)]),(z1199,[(1024,2178),(1024,100585)])]
def b100 : List (List Nat × List (Nat × Nat)) := [(z1200,[(1024,733657),(1024,1222)]),(z1201,[(1024,2146),(1024,100354)]),(z1202,[(1024,680395),(1024,201730)]),(z1203,[(1024,201730),(1024,208330)]),(z1204,[(1024,201730),(1024,208330)]),(z1205,[(1024,666073),(1024,205954)]),(z1206,[(1024,680395),(1024,201730)]),(z1207,[(1024,201730),(1024,208330)]),(z1208,[(1024,666073),(1024,122530)]),(z1209,[(1024,666073),(1024,201730)]),(z1210,[(1024,666073),(1024,201730)]),(z1211,[(1024,469657),(1024,201730)])]
def b101 : List (List Nat × List (Nat × Nat)) := [(z1212,[(1024,469657),(1024,201730)]),(z1213,[(1024,205954),(1024,208330)]),(z1214,[(1024,205954),(1024,208330)]),(z1215,[(1024,469657),(1024,201730)]),(z1216,[(1024,469657),(1024,205954)]),(z1217,[(1024,469657),(1024,201730)]),(z1218,[(1024,469657),(1024,201730)]),(z1219,[(1024,201730),(1024,213610)]),(z1220,[(1024,204898),(1024,208330)]),(z1221,[(1024,204898),(1024,208330)]),(z1222,[(1024,469657),(1024,204898)]),(z1223,[(1024,201730),(1024,208330)])]
def b102 : List (List Nat × List (Nat × Nat)) := [(z1224,[(1024,201730),(1024,208330)]),(z1225,[(1024,204898),(1024,208330)]),(z1226,[(1024,201730),(1024,207466)]),(z1227,[(1024,208330),(1024,1222)]),(z1228,[(1024,99529),(1024,1222)]),(z1229,[(1024,206284),(1024,1222)]),(z1230,[(1024,1222),(1024,132298)]),(z1231,[(1024,666073),(1024,1222)]),(z1232,[(1024,666073),(1024,1222)]),(z1233,[(1024,208330),(1024,1222)]),(z1234,[(1024,132298),(1024,208330)]),(z1235,[(1024,132298),(1024,1222)])]
def b103 : List (List Nat × List (Nat × Nat)) := [(z1236,[(1024,470218),(1024,205954)]),(z1237,[(1024,1222),(1024,132298)]),(z1238,[(1024,99529),(1024,201730)]),(z1239,[(1024,99529),(1024,1222)]),(z1240,[(1024,99529),(1024,201730)]),(z1241,[(1024,206284),(1024,1222)]),(z1242,[(1024,1222),(1024,99529)]),(z1243,[(1024,1222),(1024,99529)]),(z1244,[(1024,1222),(1024,99529)]),(z1245,[(1024,99529),(1024,1222)]),(z1246,[(1024,1222),(1024,208330)]),(z1247,[(1024,1222),(1024,99529)])]
def b104 : List (List Nat × List (Nat × Nat)) := [(z1248,[(1024,132298),(1024,201730)]),(z1249,[(1024,1222),(1024,208330)]),(z1250,[(1024,99529),(1024,132298)]),(z1251,[(1024,99529),(1024,132298)]),(z1252,[(1024,100024),(1024,122530)]),(z1253,[(1024,99529),(1024,132298)]),(z1254,[(1024,201730),(1024,132298)]),(z1255,[(1024,99529),(1024,132298)]),(z1256,[(1024,1222),(1024,99529)]),(z1257,[(1024,1222),(1024,99529)]),(z1258,[(1024,201730),(1024,208330)]),(z1259,[(1024,1222),(1024,132298)])]
def b105 : List (List Nat × List (Nat × Nat)) := [(z1260,[(1024,1222),(1024,99529)]),(z1261,[(1024,99529),(1024,132298)]),(z1262,[(1024,208330),(1024,1222)]),(z1263,[(1024,99529),(1024,1222)]),(z1264,[(1024,2278),(1024,100585)]),(z1265,[(1024,1222),(1024,132298)]),(z1266,[(1024,1222),(1024,99529)]),(z1267,[(1024,201730),(1024,208330)]),(z1268,[(1024,1222),(1024,132298)]),(z1269,[(1024,469657),(1024,1222)]),(z1270,[(1024,99529),(1024,1222)]),(z1271,[(1024,2278),(1024,100585)])]
def b106 : List (List Nat × List (Nat × Nat)) := [(z1272,[(1024,1222),(1024,208330)]),(z1273,[(1024,99529),(1024,132298)]),(z1274,[(1024,132099),(1024,133122)]),(z1275,[(1024,469657),(1024,1222)]),(z1276,[(1024,132298),(1024,201730)]),(z1277,[(1024,1222),(1024,132298)]),(z1278,[(1024,132298),(1024,1222)]),(z1279,[(1024,132793),(1024,1222)]),(z1280,[(1024,1222),(1024,132298)]),(z1281,[(1024,1222),(1024,132298)]),(z1282,[(1024,1222),(1024,99529)]),(z1283,[(1024,201730),(1024,99529)])]
def b107 : List (List Nat × List (Nat × Nat)) := [(z1284,[(1024,1222),(1024,99529)]),(z1285,[(1024,666073),(1024,2249)]),(z1286,[(1024,99529),(1024,208330)]),(z1287,[(1024,132298),(1024,1222)]),(z1288,[(1024,1222),(1024,208330)]),(z1289,[(1024,132298),(1024,99529)]),(z1290,[(1024,208330),(1024,99529),(1024,132298)]),(z1291,[(1024,1222),(1024,132298),(1024,208330)]),(z1292,[(1024,99331),(1024,100354)]),(z1293,[(1024,1222),(1024,201730)]),(z1294,[(1024,1222),(1024,99529)]),(z1295,[(1024,99529),(1024,208330)])]
def b108 : List (List Nat × List (Nat × Nat)) := [(z1296,[(1024,132298),(1024,201730)]),(z1297,[(1024,1222),(1024,132298)]),(z1298,[(1024,1222),(1024,208330)]),(z1299,[(1024,99529),(1024,201730)]),(z1300,[(1024,1222),(1024,99529)]),(z1301,[(1024,666073),(1024,1222)]),(z1302,[(1024,99529),(1024,132298)]),(z1303,[(1024,208330),(1024,2246)]),(z1304,[(1024,208330),(1024,1222)]),(z1305,[(1024,99529),(1024,1222)]),(z1306,[(1024,5314),(1024,1222)]),(z1307,[(1024,5314),(1024,1222)])]
def b109 : List (List Nat × List (Nat × Nat)) := [(z1308,[(1024,5314),(1024,1222)]),(z1309,[(1024,666062),(1024,5314)]),(z1310,[(1024,205954),(1024,5314)]),(z1311,[(1024,204898),(1024,5314)]),(z1312,[(1024,205954),(1024,1222)]),(z1313,[(1024,5314),(1024,1222)]),(z1314,[(1024,208330),(1024,1222)]),(z1315,[(1024,666073),(1024,1222)]),(z1316,[(1024,5314),(1024,1222)]),(z1317,[(1024,1222),(1024,5314)]),(z1318,[(1024,99529),(1024,5314)]),(z1319,[(1024,132298),(1024,1222)])]
def b110 : List (List Nat × List (Nat × Nat)) := [(z1320,[(1024,5314),(1024,1222)]),(z1321,[(1024,99529),(1024,5314)]),(z1322,[(1024,1222),(1024,5314)]),(z1323,[(1024,1222),(1024,5314)]),(z1324,[(1024,1222),(1024,5314)]),(z1325,[(1024,201730),(1024,5314)]),(z1326,[(1024,1222),(1024,5314)]),(z1327,[(1024,1222),(1024,5314)]),(z1328,[(1024,5314),(1024,99529)]),(z1329,[(1024,1222),(1024,5314)]),(z1330,[(1024,99529),(1024,1222)]),(z1331,[(1024,99529),(1024,1222)])]
def b111 : List (List Nat × List (Nat × Nat)) := [(z1332,[(1024,470218),(1024,1222)]),(z1333,[(80,1),(136,1),(1024,5314),(1024,1222)]),(z1334,[(1024,468172),(1024,5314)]),(z1335,[(136,1),(1024,5314),(1024,1222)]),(z1336,[(104,1),(128,0)]),(z1337,[(128,0)]),(z1338,[(136,1)]),(z1339,[(1024,483979),(1024,107170)]),(z1340,[(104,1)]),(z1341,[(1024,472710),(1024,122530)]),(z1342,[(1024,468172),(1024,5314)]),(z1343,[(104,1),(1024,468172),(1024,5314)])]
def b112 : List (List Nat × List (Nat × Nat)) := [(z1344,[(136,1),(1024,106690),(1024,99529)]),(z1345,[(104,1),(136,1),(1024,5314),(1024,1222)]),(z1346,[(136,1),(1024,106690),(1024,99529)]),(z1347,[(1024,132297),(1024,1222)]),(z1348,[(1024,5314),(1024,1222)]),(z1349,[(1024,472710),(1024,1222)]),(z1350,[(104,1),(1024,132298),(1024,1222)]),(z1351,[(104,1),(1024,99529),(1024,1222)]),(z1352,[(176,1)]),(z1353,[(1024,468172),(1024,5314)]),(z1354,[(1024,469638),(1024,122530)]),(z1355,[(1024,201730),(1024,104098)])]
def b113 : List (List Nat × List (Nat × Nat)) := [(z1356,[(104,1),(1024,201730),(1024,1222)]),(z1357,[(104,1),(1024,201730),(1024,1222)]),(z1358,[(104,1),(1024,469638),(1024,1222)]),(z1359,[(1024,1222),(1024,104098)]),(z1360,[(1024,132298),(1024,5314)]),(z1361,[(1024,132298),(1024,1222)]),(z1362,[(1024,1222),(1024,5314)]),(z1363,[(136,1),(1024,106690),(1024,99529)]),(z1364,[(136,1),(1024,630986),(1024,1222)]),(z1365,[(136,1),(1024,627914),(1024,1222)]),(z1366,[(1024,5314),(1024,1222)]),(z1367,[(136,1),(1024,5314),(1024,1222)])]
def b114 : List (List Nat × List (Nat × Nat)) := [(z1368,[(1024,5314),(1024,1222)]),(z1369,[(136,1),(1024,5314),(1024,1222)]),(z1370,[]),(z1371,[(1024,115906),(1024,2246)]),(z1372,[(1024,204930),(1024,213454)]),(z1373,[(1024,132298),(1024,1222)]),(z1374,[(1024,213610),(1024,1222)]),(z1375,[(1024,132297),(1024,1222)]),(z1376,[(104,1),(1024,630986),(1024,1222)]),(z1377,[(1024,205954),(1024,1222)]),(z1378,[(1024,630986),(1024,1222)]),(z1379,[(1024,5314),(1024,1222)])]
def b115 : List (List Nat × List (Nat × Nat)) := [(z1380,[(1024,122530),(1024,1222)]),(z1381,[(1024,470713),(1024,1222)]),(z1382,[(1024,5314),(1024,2278)]),(z1383,[(1024,5314),(1024,1222)]),(z1384,[(1024,646826),(1024,1222)]),(z1385,[(104,1),(1024,639673),(1024,1222)]),(z1386,[(104,1),(1024,631481),(1024,1222)]),(z1387,[(1024,115362),(1024,1222)]),(z1388,[(1024,132298),(1024,5314)]),(z1389,[(1024,5314),(1024,1222)]),(z1390,[(1024,99529),(1024,5314)]),(z1391,[(1024,204898),(1024,1222)])]
def b116 : List (List Nat × List (Nat × Nat)) := [(z1392,[]),(z1393,[(1024,213606),(1024,201858)]),(z1394,[(1024,213610),(1024,201826)]),(z1395,[(1024,99529),(1024,132294)]),(z1396,[(1024,213610),(1024,99526)]),(z1397,[(1024,1222),(1024,5314)]),(z1398,[]),(z1399,[(1024,468172),(1024,5314)]),(z1400,[(1024,204898),(1024,5314)]),(z1401,[(104,1),(1024,205954),(1024,1222)]),(z1402,[(104,1),(1024,1222),(1024,5314)]),(z1403,[(104,1),(1024,100024),(1024,1222)])]
def b117 : List (List Nat × List (Nat × Nat)) := [(z1404,[(104,1),(1024,1222),(1024,5314)]),(z1405,[(104,1),(1024,1222),(1024,5314)]),(z1406,[(104,1),(1024,5314),(1024,1222)]),(z1407,[(1024,1222),(1024,5314)]),(z1408,[(104,1),(176,1),(1024,1222),(1024,5314)]),(z1409,[(80,1),(104,1),(1024,1222),(1024,5314)]),(z1410,[(104,1),(1024,99529),(1024,5314)]),(z1411,[(80,1),(104,1),(1024,99529),(1024,5314)]),(z1412,[(1024,204898),(1024,1222)]),(z1413,[(1024,99529),(1024,1222)]),(z1414,[(1024,1222),(1024,5314)]),(z1415,[(1024,234499),(1024,5314)])]
def b118 : List (List Nat × List (Nat × Nat)) := [(z1416,[(1024,201730),(1024,213610)]),(z1417,[(1024,201730),(1024,5314)]),(z1418,[(1024,1222),(1024,5314)]),(z1419,[(1024,201730),(1024,5314)]),(z1420,[(1024,1222),(1024,5314)]),(z1421,[(1024,213610),(1024,1222)]),(z1422,[(104,1),(1024,1222),(1024,5314)]),(z1423,[(80,1),(104,1),(1024,1222),(1024,5314)]),(z1424,[(1024,1222),(1024,5314)]),(z1425,[(1024,132298),(1024,5314)]),(z1426,[(176,1),(1024,1222),(1024,5314)]),(z1427,[(1024,468172),(1024,1222)])]
def b119 : List (List Nat × List (Nat × Nat)) := [(z1428,[(1024,99529),(1024,1222)]),(z1429,[(1024,122530),(1024,1222)]),(z1430,[(1024,122530),(1024,1222)]),(z1431,[(1024,99529),(1024,1222)]),(z1432,[(1024,99529),(1024,1222)]),(z1433,[(1024,132298),(1024,1222)]),(z1434,[(1024,99529),(1024,1222)]),(z1435,[(1024,99529),(1024,1222)]),(z1436,[(1024,5314),(1024,1222)]),(z1437,[(1024,5314),(1024,1222)]),(z1438,[(112,0),(1024,5314),(1024,201730)]),(z1439,[(96,0),(104,0)])]
def b120 : List (List Nat × List (Nat × Nat)) := [(z1440,[(1024,483979),(1024,107170)]),(z1441,[(96,0)]),(z1442,[(1024,472710),(1024,122530)]),(z1443,[(1024,468172),(1024,5314)]),(z1444,[(1024,468172),(1024,5314)]),(z1445,[(1024,122050),(1024,2246)]),(z1446,[(1024,468172),(1024,5314)]),(z1447,[(1024,204898),(1024,5314)]),(z1448,[(1024,107170),(1024,1222)]),(z1449,[(1024,205954),(1024,1222)]),(z1450,[(1024,1222),(1024,99529)]),(z1451,[(1024,5314),(1024,1222)])]
def b121 : List (List Nat × List (Nat × Nat)) := [(z1452,[(1024,100024),(1024,1222)]),(z1453,[(1024,1222),(1024,5314)]),(z1454,[(1024,5314),(1024,2278)]),(z1455,[(1024,5314),(1024,1222)]),(z1456,[(1024,1222),(1024,5314)]),(z1457,[(1024,1222),(1024,5314)]),(z1458,[(1024,122530),(1024,1222)]),(z1459,[(1024,132298),(1024,5314)]),(z1460,[(1024,132298),(1024,1222)]),(z1461,[(1024,5314),(1024,1222)]),(z1462,[(1024,1222),(1024,5314)]),(z1463,[(1024,99529),(1024,5314)])]
def b122 : List (List Nat × List (Nat × Nat)) := [(z1464,[(1024,204898),(1024,1222)]),(z1465,[(1024,1222),(1024,5314)]),(z1466,[(96,0)]),(z1467,[(1024,1222),(1024,5314)]),(z1468,[(1024,1222),(1024,5314)]),(z1469,[(1024,469638),(1024,122530)]),(z1470,[(1024,104098),(1024,201730)]),(z1471,[(1024,234499),(1024,5314)]),(z1472,[(1024,201730),(1024,5314)]),(z1473,[(1024,1222),(1024,5314)]),(z1474,[(1024,1222),(1024,5314)]),(z1475,[(1024,201730),(1024,5314)])]
def b123 : List (List Nat × List (Nat × Nat)) := [(z1476,[(1024,1222),(1024,5314)]),(z1477,[(1024,99529),(1024,1222)]),(z1478,[(1024,208330),(1024,99529)]),(z1479,[(1024,483979),(1024,204930)]),(z1480,[(1024,208330),(1024,1222)]),(z1481,[(1024,99529),(1024,1222)]),(z1482,[(1024,468172),(1024,1222)]),(z1483,[(1024,483974),(1024,201858)]),(z1484,[(1024,208330),(1024,201826)]),(z1485,[(1024,483979),(1024,201730)]),(z1486,[(1024,1222),(1024,99529)]),(z1487,[(80,0),(1024,208330),(1024,201730)])]
def b124 : List (List Nat × List (Nat × Nat)) := [(z1488,[(1024,99529),(1024,1222)]),(z1489,[(1024,208330),(1024,201730)]),(z1490,[(1024,208330),(1024,205954)]),(z1491,[(1024,208330),(1024,205954)]),(z1492,[(1024,208330),(1024,204898)]),(z1493,[(1024,206284),(1024,99529)]),(z1494,[(1024,208330),(1024,99529)]),(z1495,[(1024,100024),(1024,122530)]),(z1496,[(1024,208330),(1024,132298)]),(z1497,[(1024,99529),(1024,132298)]),(z1498,[(1024,132298),(1024,208330)]),(z1499,[(1024,213610),(1024,99529)])]
def b125 : List (List Nat × List (Nat × Nat)) := [(z1500,[(1024,208330),(1024,99529)]),(z1501,[(1024,208330),(1024,132298)]),(z1502,[(1024,99529),(1024,208330)]),(z1503,[(1024,208330),(1024,1222)]),(z1504,[(1024,132298),(1024,5314)]),(z1505,[(1024,132298),(1024,5314)]),(z1506,[(1024,99529),(1024,1222)]),(z1507,[(1024,208329),(1024,204930)]),(z1508,[(1024,666073),(1024,122530)]),(z1509,[(1024,666073),(1024,204930)]),(z1510,[(1024,666073),(1024,205954)]),(z1511,[(1024,666073),(1024,204930)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k125 : b125.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b126 : List (List Nat × List (Nat × Nat)) := [(z1512,[(1024,5314),(1024,204898)]),(z1513,[(1024,208329),(1024,204930)]),(z1514,[(1024,699849),(1024,204898)]),(z1515,[(1024,467148),(1024,204930)]),(z1516,[(1024,208329),(1024,204930)]),(z1517,[(1024,208330),(1024,205954)]),(z1518,[(1024,208330),(1024,204898)]),(z1519,[(1024,208330),(1024,205954)]),(z1520,[(1024,468172),(1024,205954)]),(z1521,[(1024,208329),(1024,2278)]),(z1522,[(1024,237699),(1024,208329)]),(z1523,[(1024,242122),(1024,2278)])]
def b127 : List (List Nat × List (Nat × Nat)) := [(z1524,[(1024,133353),(1024,2278)]),(z1525,[(1024,471273),(1024,204930)]),(z1526,[(1024,5347),(1024,2278)]),(z1527,[(1024,666073),(1024,2246)]),(z1528,[(1024,666073),(1024,205954)]),(z1529,[(1024,208330),(1024,205954)]),(z1530,[(1024,468172),(1024,205954)]),(z1531,[(1024,208330),(1024,666073)]),(z1532,[(1024,205260),(1024,666073),(1024,208329)]),(z1533,[(1024,208330),(1024,204898)]),(z1534,[(1024,468172),(1024,204898)]),(z1535,[(1024,99529),(1024,1222)])]
def b128 : List (List Nat × List (Nat × Nat)) := [(z1536,[(1024,206284),(1024,1222)]),(z1537,[(1024,208330),(1024,1222)]),(z1538,[(1024,208330),(1024,1222)]),(z1539,[(1024,666073),(1024,1222)]),(z1540,[(1024,208330),(1024,1222)]),(z1541,[(1024,666073),(1024,1222)]),(z1542,[(1024,132298),(1024,208330)]),(z1543,[(1024,132298),(1024,1222)]),(z1544,[(1024,5314),(1024,1222)]),(z1545,[(1024,1222),(1024,5314)]),(z1546,[(1024,208330),(1024,132298)]),(z1547,[(1024,206284),(1024,1222)])]
def b129 : List (List Nat × List (Nat × Nat)) := [(z1548,[(1024,206284),(1024,1222)]),(z1549,[(1024,1222),(1024,99529)]),(z1550,[(1024,99529),(1024,1222)]),(z1551,[(1024,468172),(1024,1222)]),(z1552,[(1024,100024),(1024,132298)]),(z1553,[(1024,99529),(1024,1222)]),(z1554,[(1024,208330),(1024,1222)]),(z1555,[(1024,208330),(1024,99529)]),(z1556,[(1024,208330),(1024,1222)]),(z1557,[(1024,5314),(1024,1222)]),(z1558,[(1024,468172),(1024,1222)]),(z1559,[(1024,468172),(1024,99529)])]
def b130 : List (List Nat × List (Nat × Nat)) := [(z1560,[(1024,468172),(1024,1222)]),(z1561,[(1024,208330),(1024,1222)]),(z1562,[(1024,122530),(1024,1222)]),(z1563,[(1024,122530),(1024,1222)]),(z1564,[(1024,99529),(1024,1222)]),(z1565,[(1024,242122),(1024,2278)]),(z1566,[(1024,208330),(1024,1222)]),(z1567,[(1024,1222),(1024,99529)]),(z1568,[(1024,100024),(1024,1222)]),(z1569,[(1024,5314),(1024,1222)]),(z1570,[(1024,208330),(1024,1222)]),(z1571,[(1024,468172),(1024,1222)])]
def b131 : List (List Nat × List (Nat × Nat)) := [(z1572,[(1024,99529),(1024,132298)]),(z1573,[(1024,468172),(1024,99529)]),(z1574,[(1024,1222),(1024,132298)]),(z1575,[(1024,468172),(1024,1222)]),(z1576,[(1024,208330),(1024,1222)]),(z1577,[(1024,213610),(1024,1222)]),(z1578,[(1024,208330),(1024,132298)]),(z1579,[(1024,1222),(1024,132298)]),(z1580,[(1024,1222),(1024,208330)]),(z1581,[(1024,208330),(1024,1222)]),(z1582,[(1024,1222),(1024,132298),(1024,208330)]),(z1583,[(1024,1222),(1024,132297),(1024,208329)])]
def b132 : List (List Nat × List (Nat × Nat)) := [(z1584,[(1024,213610),(1024,1222)]),(z1585,[(80,1),(1024,132298),(1024,1222)]),(z1586,[(1024,1222),(1024,5314)]),(z1587,[(1024,213610),(1024,1222)]),(z1588,[(1024,213610),(1024,1222)]),(z1589,[(1024,5314),(1024,1222)]),(z1590,[(1024,632017),(1024,1222)]),(z1591,[(1024,1222),(1024,99529),(1024,5314)]),(z1592,[(1024,208330),(1024,132298)]),(z1593,[(1024,208330),(1024,99529)]),(z1594,[(1024,468172),(1024,99529)]),(z1595,[(1024,204898),(1024,1222)])]
def b133 : List (List Nat × List (Nat × Nat)) := [(z1596,[(1024,468172),(1024,1222)]),(z1597,[(1024,1222),(1024,99529)]),(z1598,[(1024,99529),(1024,1222)]),(z1599,[(1024,208330),(1024,99529)]),(z1600,[(1024,680395),(1024,204802)]),(z1601,[(1024,213610),(1024,99529)]),(z1602,[(1024,208326),(1024,201858)]),(z1603,[(1024,660953),(1024,122530)]),(z1604,[(1024,208326),(1024,201858)]),(z1605,[(1024,208326),(1024,201826)]),(z1606,[(1024,680395),(1024,201858)]),(z1607,[(1024,208330),(1024,205954)])]
def b134 : List (List Nat × List (Nat × Nat)) := [(z1608,[(1024,699865),(1024,201858)]),(z1609,[(1024,208326),(1024,204898)]),(z1610,[(1024,208330),(1024,201826)]),(z1611,[(1024,208330),(1024,201826)]),(z1612,[(1024,660953),(1024,122530)]),(z1613,[(1024,208330),(1024,201826)]),(z1614,[(1024,679366),(1024,201826)]),(z1615,[(1024,680390),(1024,204898)]),(z1616,[(1024,680390),(1024,201826)]),(z1617,[(1024,208330),(1024,205954)]),(z1618,[(1024,208326),(1024,201858)]),(z1619,[(1024,208326),(1024,201858)])]
def b135 : List (List Nat × List (Nat × Nat)) := [(z1620,[(1024,679370),(1024,201826)]),(z1621,[(1024,242118),(1024,234627)]),(z1622,[(1024,242122),(1024,234595)]),(z1623,[(1024,208326),(1024,100585)]),(z1624,[(1024,242118),(1024,100585)]),(z1625,[(1024,471270),(1024,201858)]),(z1626,[(1024,242122),(1024,100582)]),(z1627,[(1024,208330),(1024,133354)]),(z1628,[(1024,100582),(1024,201826)]),(z1629,[(1024,208330),(1024,660953)]),(z1630,[(1024,202188),(1024,660953),(1024,208326)]),(z1631,[(1024,201826),(1024,660953),(1024,208330)])]
def b136 : List (List Nat × List (Nat × Nat)) := [(z1632,[(1024,208330),(1024,132298)]),(z1633,[(1024,99529),(1024,208330)]),(z1634,[(1024,99529),(1024,132298)]),(z1635,[(1024,208330),(1024,99529)]),(z1636,[(1024,99529),(1024,132294),(1024,208326)]),(z1637,[(1024,99526),(1024,132298),(1024,208330)]),(z1638,[(1024,208326),(1024,5314)]),(z1639,[(1024,208330),(1024,5314)]),(z1640,[(1024,213610),(1024,99529)]),(z1641,[(104,1),(1024,132298),(1024,5314)]),(z1642,[(1024,632017),(1024,5314)]),(z1643,[(1024,2278),(1024,5314)])]
def b137 : List (List Nat × List (Nat × Nat)) := [(z1644,[(1024,213610),(1024,1222)]),(z1645,[(80,1),(1024,1222),(1024,5314)]),(z1646,[(1024,99529),(1024,1222)]),(z1647,[(1024,213610),(1024,1222)]),(z1648,[(1024,5314),(1024,1222)]),(z1649,[(1024,632017),(1024,1222)]),(z1650,[(6,1),(81,1),(137,1),(1024,1222),(1024,99529),(1024,5314)]),(z1651,[(1024,5314),(1024,204898)]),(z1652,[(1024,2278),(1024,5314)]),(z1653,[(1024,1222),(1024,99529),(1024,5314)]),(z1654,[(1024,680395),(1024,201730)]),(z1655,[(1024,201730),(1024,208330)])]
def b138 : List (List Nat × List (Nat × Nat)) := [(z1656,[(1024,208326),(1024,201858)]),(z1657,[(1024,666054),(1024,201730)]),(z1658,[(1024,464076),(1024,201858)]),(z1659,[(1024,666073),(1024,205954)]),(z1660,[(1024,680395),(1024,201858)]),(z1661,[(1024,680395),(1024,201730)]),(z1662,[(1024,208330),(1024,201730)]),(z1663,[(1024,666073),(1024,122530)]),(z1664,[(1024,666073),(1024,201730)]),(z1665,[(1024,208330),(1024,201730)]),(z1666,[(1024,666073),(1024,201730)]),(z1667,[(1024,469657),(1024,201730)])]
def b139 : List (List Nat × List (Nat × Nat)) := [(z1668,[(1024,469657),(1024,201730)]),(z1669,[(1024,208330),(1024,205954)]),(z1670,[(1024,208329),(1024,201730)]),(z1671,[(1024,469657),(1024,201730)]),(z1672,[(1024,469657),(1024,204930)]),(z1673,[(1024,5314),(1024,201730)]),(z1674,[(176,0),(1024,5314),(1024,201730)]),(z1675,[(1024,468172),(1024,201730)]),(z1676,[(1024,468172),(1024,201826)]),(z1677,[(1024,234499),(1024,208330)]),(z1678,[(1024,208330),(1024,201730)]),(z1679,[(1024,242122),(1024,2278)])]
def b140 : List (List Nat × List (Nat × Nat)) := [(z1680,[(1024,208330),(1024,133354)]),(z1681,[(1024,2278),(1024,201730)]),(z1682,[(1024,208330),(1024,201730)]),(z1683,[(1024,201730),(1024,208330)]),(z1684,[(1024,208330),(1024,201730)]),(z1685,[(1024,468172),(1024,201730)]),(z1686,[(1024,201730),(1024,208330),(1024,469657)]),(z1687,[(1024,208330),(1024,1222)]),(z1688,[(1024,1222),(1024,208330)]),(z1689,[(1024,201730),(1024,132298)]),(z1690,[(1024,208330),(1024,1222)]),(z1691,[(1024,208330),(1024,132298)])]
def b141 : List (List Nat × List (Nat × Nat)) := [(z1692,[(1024,208330),(1024,1222)]),(z1693,[(1024,468172),(1024,1222)]),(z1694,[(1024,1222),(1024,99529)]),(z1695,[(1024,1222),(1024,99529)]),(z1696,[(1024,99529),(1024,132298)]),(z1697,[(1024,468172),(1024,99529)]),(z1698,[(1024,1222),(1024,99529)]),(z1699,[(1024,208330),(1024,99529)]),(z1700,[(1024,468172),(1024,1222)]),(z1701,[(1024,1222),(1024,132298),(1024,208330)]),(z1702,[(1024,1222),(1024,99529)]),(z1703,[(1024,99529),(1024,132298)])]
def b142 : List (List Nat × List (Nat × Nat)) := [(z1704,[(1024,99561),(1024,1254)]),(z1705,[(1024,100024),(1024,1222)]),(z1706,[(1024,99529),(1024,1222)]),(z1707,[(1024,1222),(1024,99529)]),(z1708,[(1024,122530),(1024,1222)]),(z1709,[(1024,197638),(1024,1222)]),(z1710,[(1024,666062),(1024,197638)]),(z1711,[(1024,205954),(1024,197638)]),(z1712,[(1024,204898),(1024,197638)]),(z1713,[(1024,713164),(1024,1222)]),(z1714,[(1024,99529),(1024,1222)]),(z1715,[(1024,122530),(1024,1222)])]
def b143 : List (List Nat × List (Nat × Nat)) := [(z1716,[(1024,100024),(1024,1222)]),(z1717,[(1024,122530),(1024,1222)]),(z1718,[(1024,666073),(1024,1222)]),(z1719,[(1024,99529),(1024,132298)]),(z1720,[(1024,132298),(1024,1222)]),(z1721,[(1024,197638),(1024,1222)]),(z1722,[(1024,132298),(1024,99529)]),(z1723,[(1024,204898),(1024,1222)]),(z1724,[(1024,1222),(1024,99529)]),(z1725,[(1024,1222),(1024,99529)]),(z1726,[(1024,201730),(1024,197638)]),(z1727,[(1024,1222),(1024,132298)])]
def b144 : List (List Nat × List (Nat × Nat)) := [(z1728,[(1024,1222),(1024,99529)]),(z1729,[(1024,201730),(1024,1222)]),(z1730,[(1024,1222),(1024,99529)]),(z1731,[(1024,99529),(1024,1222)]),(z1732,[(1024,99529),(1024,1222)]),(z1733,[(1024,115362),(1024,1222)]),(z1734,[(1024,121858),(1024,1144)]),(z1735,[(136,2),(144,0)]),(z1736,[]),(z1737,[]),(z1738,[(1024,25035),(1024,205826)]),(z1739,[(1024,24226),(1024,204802)])]
def b145 : List (List Nat × List (Nat × Nat)) := [(z1740,[(136,1),(1024,25035),(1024,1226)]),(z1741,[(1024,24226),(1024,1225)]),(z1742,[(1024,1144),(1024,24706)]),(z1743,[(1024,1144),(1024,99352)]),(z1744,[(56,1),(104,1),(1024,1144),(1024,99352)]),(z1745,[(1024,132121),(1024,1144)]),(z1746,[(56,1),(176,1),(1024,99352),(1024,1144)]),(z1747,[(1024,99529),(1024,132298)]),(z1748,[(1024,1222),(1024,132298)]),(z1749,[(1024,1144),(1024,23650)]),(z1750,[(1024,99352),(1024,1144)]),(z1751,[(1024,1222),(1024,99529)])]
def b146 : List (List Nat × List (Nat × Nat)) := [(z1752,[(1024,1144),(1024,99352)]),(z1753,[(1024,1144),(1024,99352)]),(z1754,[(1024,115362),(1024,1136)]),(z1755,[]),(z1756,[(1024,204898),(1024,213098)]),(z1757,[(1024,204816),(1024,197638)]),(z1758,[(1024,99529),(1024,1222)]),(z1759,[(1024,689265),(1024,1222)]),(z1760,[(1024,99529),(1024,1222)]),(z1761,[(1024,99344),(1024,1136)]),(z1762,[(1024,16025),(1024,201730)]),(z1763,[(1024,201730),(1024,197638)])]
def b147 : List (List Nat × List (Nat × Nat)) := [(z1764,[(1024,1144),(1024,99352)]),(z1765,[(1024,1144),(1024,99352)]),(z1766,[(1024,1144),(1024,99352)]),(z1767,[(1024,16025),(1024,1222)]),(z1768,[(1024,10896),(1024,1222)]),(z1769,[(1024,122530),(1024,1222)]),(z1770,[(1024,99529),(1024,1222)]),(z1771,[(1024,16011),(1024,1222)]),(z1772,[(1024,122530),(1024,1222)]),(z1773,[(1024,122530),(1024,1222)]),(z1774,[(1024,122530),(1024,99529)]),(z1775,[(104,0)])]
def b148 : List (List Nat × List (Nat × Nat)) := [(z1776,[(1024,205954),(1024,197638)]),(z1777,[(1024,204898),(1024,197638)]),(z1778,[(1024,205954),(1024,1222)]),(z1779,[(1024,99529),(1024,1222)]),(z1780,[(1024,689272),(1024,1222)]),(z1781,[(1024,99529),(1024,1222)]),(z1782,[(1024,99529),(1024,132298)]),(z1783,[(1024,197638),(1024,1222)]),(z1784,[(1024,689272),(1024,1222)]),(z1785,[(1024,99529),(1024,132298)]),(z1786,[(1024,132298),(1024,1222)]),(z1787,[(1024,99529),(1024,1222)])]
def b149 : List (List Nat × List (Nat × Nat)) := [(z1788,[(1024,99529),(1024,1222)]),(z1789,[(1024,99529),(1024,132298)]),(z1790,[(1024,204898),(1024,1222)]),(z1791,[(1024,99529),(1024,1222)]),(z1792,[(1024,25035),(1024,205826)]),(z1793,[(1024,24226),(1024,204802)]),(z1794,[(1024,99529),(1024,1222)]),(z1795,[(1024,197638),(1024,1222)]),(z1796,[(1024,2168),(1024,100376)]),(z1797,[(1024,201730),(1024,197638)]),(z1798,[(1024,1222),(1024,132298)]),(z1799,[(1024,1222),(1024,99529)])]
def b150 : List (List Nat × List (Nat × Nat)) := [(z1800,[(1024,201730),(1024,1222)]),(z1801,[(1024,1222),(1024,99529)]),(z1802,[(1024,1144),(1024,99529),(1024,132121)]),(z1803,[(1024,99529),(1024,1222)]),(z1804,[(1024,123531),(1024,204898)]),(z1805,[(1024,484045),(1024,1254)]),(z1806,[(1024,99529),(1024,1222)]),(z1807,[(1024,99529),(1024,1222)]),(z1808,[(1024,208330),(1024,1222)]),(z1809,[(1024,10905),(1024,25227)]),(z1810,[(80,0),(1024,201730),(1024,207882)]),(z1811,[(1024,1222),(1024,99529)])]
def b151 : List (List Nat × List (Nat × Nat)) := [(z1812,[(1024,699865),(1024,201730)]),(z1813,[(1024,100024),(1024,10713)]),(z1814,[(1024,99529),(1024,1222)]),(z1815,[(1024,666062),(1024,198090)]),(z1816,[(1024,699513),(1024,204898)]),(z1817,[(1024,699513),(1024,204898)]),(z1818,[(1024,699513),(1024,204898)]),(z1819,[(1024,197638),(1024,204898)]),(z1820,[(1024,205922),(1024,197738)]),(z1821,[(1024,689272),(1024,204898)]),(z1822,[(1024,666062),(1024,205954)]),(z1823,[(1024,100825),(1024,208330)])]
def b152 : List (List Nat × List (Nat × Nat)) := [(z1824,[(1024,237579),(1024,197638)]),(z1825,[(1024,237667),(1024,2278)]),(z1826,[(1024,237667),(1024,207978)]),(z1827,[(1024,100585),(1024,2278)]),(z1828,[(1024,100585),(1024,204898)]),(z1829,[(1024,238722),(1024,198090)]),(z1830,[(1024,237666),(1024,198090)]),(z1831,[(1024,239053),(1024,1254)]),(z1832,[(1024,99561),(1024,1254)]),(z1833,[(1024,99561),(1024,1254)]),(z1834,[(1024,666073),(1024,1254)]),(z1835,[(1024,99561),(1024,132330)])]
def b153 : List (List Nat × List (Nat × Nat)) := [(z1836,[(1024,132330),(1024,1254)]),(z1837,[(1024,132330),(1024,99561)]),(z1838,[(1024,237666),(1024,1254)]),(z1839,[(1024,99561),(1024,1254)]),(z1840,[(1024,99529),(1024,1222)]),(z1841,[(1024,204811),(1024,197638)]),(z1842,[(1024,100585),(1024,2278)]),(z1843,[(1024,198090),(1024,666073)]),(z1844,[(1024,198090),(1024,666073)]),(z1845,[(1024,208010),(1024,665753)]),(z1846,[(1024,680395),(1024,205954)]),(z1847,[(1024,206284),(1024,208330)])]
def b154 : List (List Nat × List (Nat × Nat)) := [(z1848,[(1024,204898),(1024,208010)]),(z1849,[(1024,689272),(1024,204898)]),(z1850,[(1024,699865),(1024,204898)]),(z1851,[(1024,204898),(1024,665721),(1024,207978)]),(z1852,[(1024,198090),(1024,666073)]),(z1853,[(1024,99529),(1024,1222)]),(z1854,[(1024,99529),(1024,1222)]),(z1855,[(1024,99529),(1024,1222)]),(z1856,[(1024,206284),(1024,1222)]),(z1857,[(1024,99529),(1024,1222)]),(z1858,[(1024,99529),(1024,1222)]),(z1859,[(1024,99529),(1024,1222)])]
def b155 : List (List Nat × List (Nat × Nat)) := [(z1860,[(1024,99529),(1024,1222)]),(z1861,[(1024,1222),(1024,208010)]),(z1862,[(1024,1222),(1024,99529)]),(z1863,[(1024,99529),(1024,1222)]),(z1864,[(1024,99561),(1024,1254)]),(z1865,[(1024,99529),(1024,1222)]),(z1866,[(1024,99529),(1024,1222)]),(z1867,[(1024,99529),(1024,1222)]),(z1868,[(1024,99561),(1024,1254)]),(z1869,[(1024,1222),(1024,99529)]),(z1870,[(1024,99529),(1024,1222)]),(z1871,[(1024,99529),(1024,1222)])]
def b156 : List (List Nat × List (Nat × Nat)) := [(z1872,[(1024,100553),(1024,2246)]),(z1873,[(1024,99529),(1024,1222)]),(z1874,[(1024,100024),(1024,1222)]),(z1875,[(1024,15833),(1024,1222)]),(z1876,[(1024,99529),(1024,132298)]),(z1877,[(1024,100024),(1024,1222)]),(z1878,[(1024,689272),(1024,1222)]),(z1879,[(1024,666073),(1024,1222)]),(z1880,[(1024,99529),(1024,1222)]),(z1881,[(1024,208330),(1024,1222)]),(z1882,[(1024,1222),(1024,10442)]),(z1883,[(1024,99529),(1024,1222)])]
def b157 : List (List Nat × List (Nat × Nat)) := [(z1884,[(1024,99529),(1024,208010)]),(z1885,[(1024,1222),(1024,208010)]),(z1886,[(1024,10937),(1024,1222)]),(z1887,[(1024,99529),(1024,1222)]),(z1888,[(1024,99529),(1024,132298)]),(z1889,[(1024,99529),(1024,132298)]),(z1890,[(1024,132298),(1024,1222)]),(z1891,[(1024,132298),(1024,1222)]),(z1892,[(1024,1222),(1024,99529)]),(z1893,[(1024,1222),(1024,99529)]),(z1894,[(1024,213610),(1024,1222)]),(z1895,[(1024,99529),(1024,208010)])]
def b158 : List (List Nat × List (Nat × Nat)) := [(z1896,[(1024,132793),(1024,99529)]),(z1897,[(1024,470218),(1024,99529)]),(z1898,[(1024,204898),(1024,1222)]),(z1899,[(1024,1222),(1024,99529)]),(z1900,[(1024,711778),(1024,1222)]),(z1901,[(1024,204898),(1024,1222)]),(z1902,[(1024,1222),(1024,99529)]),(z1903,[(1024,99529),(1024,1222)]),(z1904,[(1024,1222),(1024,99529),(1024,207978)]),(z1905,[(1024,10713),(1024,25035)]),(z1906,[(1024,13771),(1024,10702)]),(z1907,[(1024,24226),(1024,10713)])]
def b159 : List (List Nat × List (Nat × Nat)) := [(z1908,[(1024,699865),(1024,204802)]),(z1909,[(1024,699513),(1024,201826)]),(z1910,[(1024,704633),(1024,204898)]),(z1911,[(1024,99529),(1024,1222)]),(z1912,[(1024,99529),(1024,1222)]),(z1913,[(1024,99529),(1024,1222)]),(z1914,[(1024,201730),(1024,207978)]),(z1915,[(1024,10905),(1024,201730)]),(z1916,[(1024,10904),(1024,201730)]),(z1917,[(1024,679947),(1024,10905)]),(z1918,[(1024,10905),(1024,201730)]),(z1919,[(1024,665625),(1024,10905)])]
def b160 : List (List Nat × List (Nat × Nat)) := [(z1920,[(1024,10905),(1024,123534)]),(z1921,[(1024,10905),(1024,197638)]),(z1922,[(1024,10905),(1024,197642)]),(z1923,[(1024,13977),(1024,201730)]),(z1924,[(1024,10905),(1024,201730)]),(z1925,[(1024,16025),(1024,201730)]),(z1926,[(1024,10905),(1024,204898)]),(z1927,[(1024,10905),(1024,204898)]),(z1928,[(1024,10905),(1024,204802)]),(z1929,[(1024,10905),(1024,201730)]),(z1930,[(1024,201730),(1024,207978)]),(z1931,[(1024,201730),(1024,207882)])]
def b161 : List (List Nat × List (Nat × Nat)) := [(z1932,[(1024,204898),(1024,207978)]),(z1933,[(1024,234499),(1024,197638)]),(z1934,[(1024,10905),(1024,207882)]),(z1935,[(1024,10905),(1024,100585)]),(z1936,[(1024,2168),(1024,100376)]),(z1937,[(1024,10905),(1024,2278)]),(z1938,[(1024,2278),(1024,10905)]),(z1939,[(1024,234499),(1024,10905)]),(z1940,[(1024,234498),(1024,198090)]),(z1941,[(1024,1254),(1024,132330)]),(z1942,[(1024,1254),(1024,99561)]),(z1943,[(1024,99561),(1024,132330)])]
def b162 : List (List Nat × List (Nat × Nat)) := [(z1944,[(1024,1254),(1024,99561)]),(z1945,[(1024,201730),(1024,197638)]),(z1946,[(1024,198090),(1024,469657)]),(z1947,[(1024,201730),(1024,208010)]),(z1948,[(1024,689305),(1024,201730)]),(z1949,[(1024,469657),(1024,201730)]),(z1950,[(1024,10905),(1024,201730),(1024,207882)]),(z1951,[(1024,1222),(1024,208010)]),(z1952,[(1024,132793),(1024,1222)]),(z1953,[(1024,208330),(1024,1222)]),(z1954,[(1024,99529),(1024,1222)]),(z1955,[(1024,99529),(1024,201730)])]
def b163 : List (List Nat × List (Nat × Nat)) := [(z1956,[(1024,99529),(1024,1222)]),(z1957,[(1024,1222),(1024,99529)]),(z1958,[(1024,1222),(1024,99529)]),(z1959,[(1024,99529),(1024,132298)]),(z1960,[(1024,99529),(1024,132298)]),(z1961,[(1024,1222),(1024,99529)]),(z1962,[(1024,1222),(1024,99529)]),(z1963,[(1024,1144),(1024,99529),(1024,132121)]),(z1964,[(1024,665625),(1024,1222)]),(z1965,[(136,1),(1024,5314),(1024,1222)]),(z1966,[(136,1),(1024,122474),(1024,1222)]),(z1967,[(1024,5314),(1024,1222)])]
def b164 : List (List Nat × List (Nat × Nat)) := [(z1968,[(1024,197638),(1024,1222)]),(z1969,[(1024,5314),(1024,1222)]),(z1970,[(1024,197638),(1024,1222)]),(z1971,[(1024,5314),(1024,122314)]),(z1972,[(1024,10886),(1024,197638)]),(z1973,[(1024,140761),(1024,122314)]),(z1974,[(1024,10886),(1024,197638)]),(z1975,[(1024,5347),(1024,2278)]),(z1976,[(1024,231430),(1024,2278)]),(z1977,[(1024,5314),(1024,1222)]),(z1978,[(1024,99529),(1024,1222)]),(z1979,[(1024,5314),(1024,1222)])]
def b165 : List (List Nat × List (Nat × Nat)) := [(z1980,[(1024,99529),(1024,1222)]),(z1981,[(1024,1222),(1024,122314)]),(z1982,[(1024,1222),(1024,10886),(1024,99529)]),(z1983,[(1024,5314),(1024,122314)]),(z1984,[(1024,197638),(1024,5314)]),(z1985,[(1024,5314),(1024,1222)]),(z1986,[(1024,1222),(1024,5314)]),(z1987,[(96,1),(168,1),(1024,1144),(1024,99352)]),(z1988,[(96,1),(128,1),(1024,5314),(1024,1222)]),(z1989,[(1024,468172),(1024,5314)]),(z1990,[(96,2),(104,0)]),(z1991,[])]
def b166 : List (List Nat × List (Nat × Nat)) := [(z1992,[]),(z1993,[(72,1),(168,1),(1024,5314),(1024,1144)]),(z1994,[(1024,1144),(1024,5314)]),(z1995,[(128,1),(1024,122065),(1024,1222)]),(z1996,[(72,1),(96,1),(1024,99529),(1024,1222)]),(z1997,[(72,1),(96,1),(1024,5314),(1024,1222)]),(z1998,[(1024,99529),(1024,1222)]),(z1999,[(1024,99529),(1024,1222)]),(z2000,[(1024,99529),(1024,1222)]),(z2001,[(1024,1222),(1024,99529)]),(z2002,[(1024,99529),(1024,1222)]),(z2003,[(1024,5314),(1024,1222)])]
def b167 : List (List Nat × List (Nat × Nat)) := [(z2004,[(1024,99529),(1024,1222)]),(z2005,[(128,1),(1024,5314),(1024,1222)]),(z2006,[(1024,197638),(1024,1222)]),(z2007,[(72,1),(128,1),(1024,5314),(1024,1222)]),(z2008,[(72,1),(1024,197638),(1024,1222)]),(z2009,[(1024,15564),(1024,1222)]),(z2010,[(1024,10449),(1024,1222)]),(z2011,[(1024,5314),(1024,1222)]),(z2012,[(1024,99529),(1024,1222)]),(z2013,[(1024,99529),(1024,1222)]),(z2014,[(1024,5314),(1024,1222)]),(z2015,[(1024,197638),(1024,1222)])]
def b168 : List (List Nat × List (Nat × Nat)) := [(z2016,[(1024,5314),(1024,1222)]),(z2017,[(1024,197638),(1024,1222)]),(z2018,[(1024,5314),(1024,1222)]),(z2019,[(1024,197638),(1024,1222)]),(z2020,[(1024,207978),(1024,107724)]),(z2021,[(1024,198090),(1024,99561)]),(z2022,[(1024,99529),(1024,208010)]),(z2023,[(1024,99529),(1024,132298)]),(z2024,[(1024,208330),(1024,99529)]),(z2025,[(1024,198089),(1024,237699)]),(z2026,[(1024,207992),(1024,205954)]),(z2027,[(1024,208329),(1024,204930)])]
def b169 : List (List Nat × List (Nat × Nat)) := [(z2028,[(1024,666073),(1024,204930)]),(z2029,[(1024,207992),(1024,204898)]),(z2030,[(1024,207978),(1024,204898)]),(z2031,[(1024,107724),(1024,204898)]),(z2032,[(1024,100810),(1024,666073)]),(z2033,[(1024,241784),(1024,2278)]),(z2034,[(1024,198090),(1024,1254)]),(z2035,[(1024,99561),(1024,1254)]),(z2036,[(1024,468205),(1024,1254)]),(z2037,[(1024,1222),(1024,208010)]),(z2038,[(1024,208330),(1024,1222)]),(z2039,[(1024,208330),(1024,1222)])]
def b170 : List (List Nat × List (Nat × Nat)) := [(z2040,[(1024,1222),(1024,99529)]),(z2041,[(1024,100024),(1024,1222)]),(z2042,[(1024,1222),(1024,99529)]),(z2043,[(1024,5314),(1024,1222)]),(z2044,[(1024,468172),(1024,1222)]),(z2045,[(1024,197638),(1024,1222)]),(z2046,[(1024,208330),(1024,1222)]),(z2047,[(1024,100024),(1024,1222)]),(z2048,[(1024,1222),(1024,99529),(1024,132298)]),(z2049,[(1024,198086),(1024,234627)]),(z2050,[(1024,198090),(1024,234595)]),(z2051,[(1024,689272),(1024,201858)])]
def b171 : List (List Nat × List (Nat × Nat)) := [(z2052,[(1024,208326),(1024,201858)]),(z2053,[(1024,208010),(1024,201826)]),(z2054,[(1024,689272),(1024,201826)]),(z2055,[(1024,208330),(1024,201826)]),(z2056,[(1024,2506),(1024,660953)]),(z2057,[(1024,198090),(1024,234499)]),(z2058,[(1024,10905),(1024,201730)]),(z2059,[(1024,208025),(1024,122060)]),(z2060,[(128,0),(1024,207882),(1024,9420)]),(z2061,[(1024,9420),(1024,10905)]),(z2062,[(1024,208536),(1024,201730)]),(z2063,[(1024,208330),(1024,201730)])]
def b172 : List (List Nat × List (Nat × Nat)) := [(z2064,[(1024,208330),(1024,201730)]),(z2065,[(1024,99529),(1024,1222)]),(z2066,[(1024,99529),(1024,132298)]),(z2067,[(1024,100553),(1024,2246)]),(z2068,[(1024,208330),(1024,1222)]),(z2069,[(1024,99529),(1024,1222)]),(z2070,[(1024,99529),(1024,1222)]),(z2071,[(1024,99529),(1024,132298)]),(z2072,[(80,1),(184,1),(1024,106690),(1024,99529)]),(z2073,[(1024,99561),(1024,1254)]),(z2074,[(1024,100024),(1024,1222)]),(z2075,[(1024,99529),(1024,1222)])]
def b173 : List (List Nat × List (Nat × Nat)) := [(z2076,[(1024,100024),(1024,1222)]),(z2077,[(1024,666073),(1024,1222)]),(z2078,[(1024,99529),(1024,1222)]),(z2079,[(1024,99529),(1024,1222)]),(z2080,[(1024,99529),(1024,1222)]),(z2081,[(1024,99529),(1024,1222)]),(z2082,[(144,1),(168,0),(184,2),(192,0),(232,1)]),(z2083,[(168,0)]),(z2084,[(1024,483979),(1024,122530)]),(z2085,[(144,1),(184,1),(232,1)]),(z2086,[(1024,483979),(1024,122530)]),(z2087,[(184,1),(1024,712834),(1024,1222)])]
def b174 : List (List Nat × List (Nat × Nat)) := [(z2088,[(184,1),(1024,122530),(1024,1222)]),(z2089,[(184,1),(1024,132793),(1024,99529)]),(z2090,[(1024,132298),(1024,1222)]),(z2091,[(80,1),(144,1),(184,1),(1024,122530),(1024,1222)]),(z2092,[(1024,100024),(1024,122530)]),(z2093,[(1024,711778),(1024,1222)]),(z2094,[(1024,99529),(1024,1222)]),(z2095,[(80,1),(184,1),(1024,122530),(1024,1222)]),(z2096,[(184,1),(1024,201730),(1024,122530)]),(z2097,[(144,1),(1024,1222),(1024,122530)]),(z2098,[(144,1),(1024,1222),(1024,99529)]),(z2099,[(144,1),(1024,122530),(1024,99529)])]
def b175 : List (List Nat × List (Nat × Nat)) := [(z2100,[(144,1),(1024,1222),(1024,99529)]),(z2101,[(184,1),(1024,99529),(1024,1222)]),(z2102,[(184,1),(1024,122530),(1024,1222)]),(z2103,[(1024,122530),(1024,1222)]),(z2104,[(1024,99529),(1024,1222)]),(z2105,[(144,0)]),(z2106,[(1024,671347),(1024,205954)]),(z2107,[(232,1)]),(z2108,[(1024,116419),(1024,2278)]),(z2109,[(1024,205954),(1024,213610)]),(z2110,[(1024,204898),(1024,213610)]),(z2111,[(1024,132298),(1024,1222)])]
def b176 : List (List Nat × List (Nat × Nat)) := [(z2112,[(1024,99529),(1024,1222)]),(z2113,[(1024,99529),(1024,1222)]),(z2114,[(1024,100024),(1024,1222)]),(z2115,[(1024,99529),(1024,1222)]),(z2116,[(1024,99529),(1024,1222)]),(z2117,[(1024,705145),(1024,1222)]),(z2118,[(1024,671353),(1024,1222)]),(z2119,[(1024,99529),(1024,132298)]),(z2120,[(1024,132298),(1024,1222)]),(z2121,[(1024,213610),(1024,1222)]),(z2122,[(10,1),(145,1),(1024,1222),(1024,99529),(1024,115362)]),(z2123,[(1024,1222),(1024,99529)])]
def b177 : List (List Nat × List (Nat × Nat)) := [(z2124,[(1024,132298),(1024,99529)]),(z2125,[(1024,204898),(1024,1222)]),(z2126,[(1024,99529),(1024,1222)]),(z2127,[(1024,99529),(1024,1222)]),(z2128,[(144,2),(184,1),(232,1)]),(z2129,[(144,1),(1024,100024),(1024,1222)]),(z2130,[(1024,201730),(1024,114338)]),(z2131,[(1024,201730),(1024,213610)]),(z2132,[(1024,1222),(1024,132298)]),(z2133,[(1024,99529),(1024,1222)]),(z2134,[(1024,99529),(1024,132298)]),(z2135,[(1024,1222),(1024,99529)])]
def b178 : List (List Nat × List (Nat × Nat)) := [(z2136,[(1024,99529),(1024,1222)]),(z2137,[(1024,100024),(1024,1222)]),(z2138,[(1024,483979),(1024,122530)]),(z2139,[(128,0),(144,0)]),(z2140,[(1024,483979),(1024,122530)]),(z2141,[(1024,122563),(1024,2278)]),(z2142,[(1024,1222),(1024,99529),(1024,122530)]),(z2143,[(1024,99529),(1024,1222)]),(z2144,[(1024,122530),(1024,201730)]),(z2145,[(1024,483979),(1024,205954)]),(z2146,[(1024,483979),(1024,204898)]),(z2147,[(1024,484045),(1024,2278)])]
def b179 : List (List Nat × List (Nat × Nat)) := [(z2148,[(1024,484012),(1024,1222)]),(z2149,[(1024,99529),(1024,1222)]),(z2150,[(1024,483979),(1024,201730)]),(z2151,[(1024,99529),(1024,1222)]),(z2152,[(112,0),(1024,201730),(1024,208330)]),(z2153,[(1024,99529),(1024,132298)]),(z2154,[(1024,470218),(1024,99529)]),(z2155,[(1024,100024),(1024,132298)]),(z2156,[(1024,99529),(1024,132298)]),(z2157,[(1024,99529),(1024,1222)]),(z2158,[(1024,666073),(1024,205954)]),(z2159,[(1024,666073),(1024,122530)])]
def b180 : List (List Nat × List (Nat × Nat)) := [(z2160,[(1024,666073),(1024,205954)]),(z2161,[(1024,666073),(1024,205954)]),(z2162,[(1024,666073),(1024,205922)]),(z2163,[(1024,666073),(1024,204930)]),(z2164,[(112,0),(1024,205954),(1024,208330)]),(z2165,[(112,0),(1024,204898),(1024,208330)]),(z2166,[(1024,204898),(1024,208330)]),(z2167,[(1024,699865),(1024,204898)]),(z2168,[(1024,699865),(1024,122530)]),(z2169,[(1024,699865),(1024,204898)]),(z2170,[(96,0),(1024,666073),(1024,208330)]),(z2171,[(1024,699865),(1024,204898)])]
def b181 : List (List Nat × List (Nat × Nat)) := [(z2172,[(1024,699865),(1024,204898)]),(z2173,[(112,0),(1024,666073),(1024,204898)]),(z2174,[(112,0),(1024,205954),(1024,208330)]),(z2175,[(1024,666073),(1024,205954)]),(z2176,[(1024,208330),(1024,205954)]),(z2177,[(1024,204898),(1024,208330)]),(z2178,[(14,0),(114,0),(129,0),(145,0),(153,0),(1024,206284),(1024,238723),(1024,208330)]),(z2179,[(1024,237667),(1024,204898)]),(z2180,[(1024,2278),(1024,205954)]),(z2181,[(1024,2278),(1024,204898)]),(z2182,[(1024,680395),(1024,208330)]),(z2183,[(1024,237667),(1024,208330)])]
def b182 : List (List Nat × List (Nat × Nat)) := [(z2184,[(1024,100585),(1024,205954)]),(z2185,[(1024,239053),(1024,2278)]),(z2186,[(1024,100585),(1024,2278)]),(z2187,[(1024,101080),(1024,2278)]),(z2188,[(1024,100585),(1024,2278)]),(z2189,[(1024,666073),(1024,2278)]),(z2190,[(1024,100585),(1024,133354)]),(z2191,[(1024,100585),(1024,2278)]),(z2192,[(1024,133354),(1024,2278)]),(z2193,[(1024,471274),(1024,205954)]),(z2194,[(1024,247402),(1024,2278)]),(z2195,[(1024,133354),(1024,100585)])]
def b183 : List (List Nat × List (Nat × Nat)) := [(z2196,[(1024,100585),(1024,2278)]),(z2197,[(1024,133354),(1024,204898)]),(z2198,[(1024,237667),(1024,2278)]),(z2199,[(1024,100585),(1024,2278)]),(z2200,[(1024,100585),(1024,204898)]),(z2201,[(1024,242122),(1024,1254)]),(z2202,[(1024,101080),(1024,2246)]),(z2203,[(1024,100585),(1024,2278)]),(z2204,[(1024,100585),(1024,1222)]),(z2205,[(1024,208330),(1024,666073)]),(z2206,[(1024,206284),(1024,666073),(1024,208330)]),(z2207,[(1024,204898),(1024,666073),(1024,208330)])]
def b184 : List (List Nat × List (Nat × Nat)) := [(z2208,[(1024,99529),(1024,1222)]),(z2209,[(1024,208330),(1024,1222)]),(z2210,[(1024,208330),(1024,1222)]),(z2211,[(1024,132793),(1024,1222)]),(z2212,[(1024,213610),(1024,1222)]),(z2213,[(1024,132298),(1024,208330)]),(z2214,[(1024,99529),(1024,2278)]),(z2215,[(1024,99529),(1024,1222)]),(z2216,[(1024,1222),(1024,205954)]),(z2217,[(1024,1222),(1024,99529)]),(z2218,[(1024,99529),(1024,1222)]),(z2219,[(1024,99529),(1024,1222)])]
def b185 : List (List Nat × List (Nat × Nat)) := [(z2220,[(1024,100024),(1024,1222)]),(z2221,[(1024,99529),(1024,1222)]),(z2222,[(1024,99529),(1024,208330)]),(z2223,[(1024,100585),(1024,2278)]),(z2224,[(1024,208330),(1024,1222)]),(z2225,[(1024,1222),(1024,208330)]),(z2226,[(1024,99529),(1024,1222)]),(z2227,[(1024,99529),(1024,132298)]),(z2228,[(1024,1222),(1024,99529),(1024,132298)]),(z2229,[(1024,99529),(1024,1222)]),(z2230,[(1024,208330),(1024,1222)]),(z2231,[(1024,99529),(1024,1222)])]
def b186 : List (List Nat × List (Nat × Nat)) := [(z2232,[(1024,99529),(1024,1222)]),(z2233,[(1024,99529),(1024,1222)]),(z2234,[(1024,99529),(1024,132298)]),(z2235,[(1024,100585),(1024,2278)]),(z2236,[(1024,1222),(1024,132298)]),(z2237,[(1024,99529),(1024,1222)]),(z2238,[(1024,100024),(1024,1222)]),(z2239,[(1024,99529),(1024,1222)]),(z2240,[(1024,100024),(1024,666073)]),(z2241,[(1024,100024),(1024,1222),(1024,132298)]),(z2242,[(1024,1222),(1024,132298),(1024,208330)]),(z2243,[(1024,470218),(1024,666073)])]
def b187 : List (List Nat × List (Nat × Nat)) := [(z2244,[(1024,1222),(1024,132298),(1024,208330)]),(z2245,[(14,1),(1024,1222),(1024,99529),(1024,132298)]),(z2246,[(1024,99529),(1024,132298),(1024,208330)]),(z2247,[(1024,204898),(1024,1222)]),(z2248,[(1024,1222),(1024,99529),(1024,208330)]),(z2249,[(1024,666073),(1024,205826)]),(z2250,[(1024,699865),(1024,204802)]),(z2251,[(1024,680395),(1024,201858)]),(z2252,[(1024,699865),(1024,201826)]),(z2253,[(1024,705145),(1024,204898)]),(z2254,[(1024,100585),(1024,2278)]),(z2255,[(10,1),(1024,1222),(1024,99529),(1024,132298)])]
def b188 : List (List Nat × List (Nat × Nat)) := [(z2256,[(184,0),(1024,201730),(1024,208330)]),(z2257,[(184,0),(1024,201730),(1024,208330)]),(z2258,[(1024,100585),(1024,2278)]),(z2259,[(1024,201730),(1024,208330)]),(z2260,[(144,0),(1024,666073),(1024,205954)]),(z2261,[(1024,680395),(1024,201730)]),(z2262,[(1024,201730),(1024,208330)]),(z2263,[(1024,666073),(1024,122530)]),(z2264,[(1024,666073),(1024,201730)]),(z2265,[(1024,201730),(1024,208330)]),(z2266,[(1024,469657),(1024,201730)]),(z2267,[(1024,469657),(1024,201730)])]
def b189 : List (List Nat × List (Nat × Nat)) := [(z2268,[(144,0),(1024,205954),(1024,208330)]),(z2269,[(144,0),(1024,469657),(1024,201730)]),(z2270,[(1024,469657),(1024,205954)]),(z2271,[(1024,201730),(1024,208330)]),(z2272,[(1024,469657),(1024,201730)]),(z2273,[(1024,201730),(1024,213610)]),(z2274,[(184,0),(1024,204898),(1024,208330)]),(z2275,[(144,0),(1024,469657),(1024,204898)]),(z2276,[(1024,201730),(1024,208330)]),(z2277,[(144,0),(1024,201730),(1024,208330)]),(z2278,[(1024,204898),(1024,208330)]),(z2279,[(1024,234499),(1024,201730)])]
def b190 : List (List Nat × List (Nat × Nat)) := [(z2280,[(1024,469657),(1024,208330)]),(z2281,[(1024,2278),(1024,133354)]),(z2282,[(1024,100585),(1024,201730)]),(z2283,[(1024,2278),(1024,100585)]),(z2284,[(1024,133354),(1024,201730)]),(z2285,[(1024,2278),(1024,201730)]),(z2286,[(1024,100585),(1024,133354)]),(z2287,[(1024,2278),(1024,100585)]),(z2288,[(1024,234499),(1024,201730)]),(z2289,[(1024,201730),(1024,208330),(1024,469657)]),(z2290,[(1024,1222),(1024,132298),(1024,208330)]),(z2291,[(1024,1222),(1024,469657)])]
def b191 : List (List Nat × List (Nat × Nat)) := [(z2292,[(1024,201730),(1024,99529)]),(z2293,[(1024,1222),(1024,99529),(1024,132298)]),(z2294,[(72,1),(184,1),(1024,5314),(1024,1222)]),(z2295,[(1024,5314),(1024,1222)]),(z2296,[(1024,666073),(1024,5314)]),(z2297,[(1024,699865),(1024,5314)]),(z2298,[(1024,5347),(1024,2278)]),(z2299,[(1024,208330),(1024,1222)]),(z2300,[(1024,5314),(1024,201730)]),(z2301,[(56,1),(136,1),(176,1),(1024,122530),(1024,1222)]),(z2302,[(1024,99529),(1024,1222)]),(z2303,[(136,1),(176,1),(1024,5314),(1024,1222)])]
def b192 : List (List Nat × List (Nat × Nat)) := [(z2304,[(136,1),(176,1),(1024,5314),(1024,1222)]),(z2305,[(152,0),(1024,468172),(1024,5314)]),(z2306,[(128,0),(136,2),(144,0),(176,1)]),(z2307,[(1024,483979),(1024,107170)]),(z2308,[(104,1),(128,0)]),(z2309,[(1024,472710),(1024,122530)]),(z2310,[(1024,468172),(1024,5314)]),(z2311,[(104,1),(1024,468172),(1024,5314)]),(z2312,[(176,1),(1024,122050),(1024,2246)]),(z2313,[(1024,468172),(1024,5314)]),(z2314,[(104,1),(1024,468172),(1024,5314)]),(z2315,[(136,1),(1024,107170),(1024,1222)])]
def b193 : List (List Nat × List (Nat × Nat)) := [(z2316,[(104,1),(136,1),(1024,205954),(1024,1222)]),(z2317,[(136,1),(1024,1222),(1024,99529)]),(z2318,[(104,1),(136,1),(1024,5314),(1024,1222)]),(z2319,[(56,1),(104,1),(136,1),(1024,100024),(1024,1222)]),(z2320,[(56,1),(136,1),(1024,5314),(1024,1222)]),(z2321,[(136,1),(1024,5314),(1024,2278)]),(z2322,[(104,1),(136,1),(1024,5314),(1024,1222)]),(z2323,[(104,1),(136,1),(1024,5314),(1024,1222)]),(z2324,[(136,1),(1024,122530),(1024,1222)]),(z2325,[(136,1),(1024,132298),(1024,5314)]),(z2326,[(104,1),(1024,132298),(1024,1222)]),(z2327,[(104,1),(136,1),(224,1),(1024,5314),(1024,1222)])]
def b194 : List (List Nat × List (Nat × Nat)) := [(z2328,[(104,1),(136,1),(1024,132298),(1024,5314)]),(z2329,[(104,1),(1024,204898),(1024,1222)]),(z2330,[(104,1),(1024,99529),(1024,1222)]),(z2331,[(128,0),(224,1)]),(z2332,[(104,1),(136,1),(1024,5314),(1024,1222)]),(z2333,[(1024,469638),(1024,122530)]),(z2334,[(1024,104098),(1024,201730)]),(z2335,[(136,1),(1024,234499),(1024,5314)]),(z2336,[(136,1),(1024,201730),(1024,5314)]),(z2337,[(104,1),(136,1),(1024,1222),(1024,5314)]),(z2338,[(104,1),(1024,1222),(1024,5314)]),(z2339,[(104,1),(1024,201730),(1024,5314)])]
def b195 : List (List Nat × List (Nat × Nat)) := [(z2340,[(104,1),(224,1),(1024,5314),(1024,1222)]),(z2341,[(104,1),(136,1),(1024,99529),(1024,1222)]),(z2342,[(1024,5314),(1024,1222)]),(z2343,[(1024,99529),(1024,132298)]),(z2344,[(136,1),(1024,132298),(1024,5314)]),(z2345,[(1024,213609),(1024,204930)]),(z2346,[(1024,5347),(1024,2278)]),(z2347,[(1024,213610),(1024,1222)]),(z2348,[(1024,5314),(1024,1222)]),(z2349,[(1024,99529),(1024,1222)]),(z2350,[(1024,213610),(1024,1222)]),(z2351,[(1024,5314),(1024,1222)])]
def b196 : List (List Nat × List (Nat × Nat)) := [(z2352,[(1024,100024),(1024,1222)]),(z2353,[(6,1),(105,1),(177,1),(1024,1222),(1024,99529),(1024,5314)]),(z2354,[(1024,213606),(1024,201858)]),(z2355,[(1024,213610),(1024,201826)]),(z2356,[(1024,468172),(1024,5314)]),(z2357,[(136,1),(1024,2278),(1024,5314)]),(z2358,[(6,1),(81,1),(104,1),(105,1),(177,1),(1024,1222),(1024,99529),(1024,5314)]),(z2359,[(1024,213610),(1024,201730)]),(z2360,[(232,0),(1024,201730),(1024,5314)]),(z2361,[(1024,468172),(1024,5314)]),(z2362,[(1024,468172),(1024,5314)]),(z2363,[(1024,5347),(1024,2278)])]
def b197 : List (List Nat × List (Nat × Nat)) := [(z2364,[(1024,1222),(1024,99529),(1024,5314)]),(z2365,[(232,0),(1024,5314),(1024,201730)]),(z2366,[(1024,208330),(1024,205954)]),(z2367,[(1024,208330),(1024,204898)]),(z2368,[(1024,242122),(1024,100585)]),(z2369,[(1024,99529),(1024,132298),(1024,208330)]),(z2370,[(1024,666073),(1024,205954)]),(z2371,[(1024,208330),(1024,205954)]),(z2372,[(1024,468172),(1024,205954)]),(z2373,[(72,0),(1024,208330),(1024,666073)]),(z2374,[(10,0),(82,0),(97,0),(105,0),(113,0),(1024,205260),(1024,237699),(1024,208329)]),(z2375,[(1024,208330),(1024,204898)])]
def b198 : List (List Nat × List (Nat × Nat)) := [(z2376,[(1024,468172),(1024,204898)]),(z2377,[(1024,242122),(1024,2278)]),(z2378,[(1024,100585),(1024,2278)]),(z2379,[(1024,468205),(1024,2278)]),(z2380,[(1024,1222),(1024,132298),(1024,208330)]),(z2381,[(1024,1222),(1024,99529),(1024,132298)]),(z2382,[(1024,1222),(1024,99529),(1024,132298)]),(z2383,[(72,0),(1024,208330),(1024,660953)]),(z2384,[(10,0),(97,0),(113,0),(145,0),(154,0),(1024,202188),(1024,234627),(1024,208326)]),(z2385,[(10,0),(97,0),(113,0),(145,0),(154,0),(1024,201826),(1024,234595),(1024,208330)]),(z2386,[(1024,201730),(1024,208330)]),(z2387,[(176,0),(1024,208330),(1024,201730)])]
def b199 : List (List Nat × List (Nat × Nat)) := [(z2388,[(1024,468172),(1024,201730)]),(z2389,[(6,0),(73,0),(81,0),(137,0),(146,0),(177,0),(1024,469657),(1024,201730),(1024,208330)]),(z2390,[(72,1),(184,1),(1024,122530),(1024,1222)]),(z2391,[(1024,99529),(1024,1222)]),(z2392,[(1024,197638),(1024,205954)]),(z2393,[(1024,197638),(1024,204898)]),(z2394,[(1024,100585),(1024,2278)]),(z2395,[(1024,1222),(1024,99529),(1024,132298)]),(z2396,[(1024,197638),(1024,201730)]),(z2397,[(56,1),(1024,122530),(1024,1222)]),(z2398,[(1024,99529),(1024,1222)]),(z2399,[(1024,122530),(1024,1222)])]
def b200 : List (List Nat × List (Nat × Nat)) := [(z2400,[(176,1),(1024,122530),(1024,99529)]),(z2401,[(136,2),(144,0)]),(z2402,[(1024,680395),(1024,197638)]),(z2403,[(136,1),(1024,204898),(1024,197638)]),(z2404,[(1024,205954),(1024,1222)]),(z2405,[(1024,99529),(1024,1222)]),(z2406,[(56,1),(1024,99529),(1024,1222)]),(z2407,[(56,1),(136,1),(1024,99529),(1024,1222)]),(z2408,[(1024,99529),(1024,132298)]),(z2409,[(136,1),(1024,689272),(1024,1222)]),(z2410,[(1024,99529),(1024,132298)]),(z2411,[(1024,132298),(1024,1222)])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k200 : b200.all (fun a => P_ a.1 a.2) = true := by decide +kernel
def b201 : List (List Nat × List (Nat × Nat)) := [(z2412,[(56,1),(104,1),(224,1),(1024,99529),(1024,1222)]),(z2413,[(1024,99529),(1024,132298)]),(z2414,[(1024,204898),(1024,1222)]),(z2415,[(1024,99529),(1024,1222)]),(z2416,[(1024,25035),(1024,205826)]),(z2417,[(1024,24226),(1024,204802)]),(z2418,[(56,1),(136,1),(1024,1222),(1024,99529)]),(z2419,[(1024,2168),(1024,100376)]),(z2420,[(104,1),(1024,201730),(1024,197638)]),(z2421,[(1024,1222),(1024,132298)]),(z2422,[(1024,1222),(1024,99529)]),(z2423,[(1024,201730),(1024,1222)])]
def b202 : List (List Nat × List (Nat × Nat)) := [(z2424,[(1024,1222),(1024,99529)]),(z2425,[(6,1),(58,1),(73,1),(81,1),(114,1),(137,1),(186,1),(1024,1144),(1024,99529),(1024,132121)]),(z2426,[(1024,99529),(1024,1222)]),(z2427,[(1024,99529),(1024,1222)]),(z2428,[(1024,704633),(1024,204898)]),(z2429,[(1024,237584),(1024,197638)]),(z2430,[(1024,99561),(1024,1254)]),(z2431,[(1024,100585),(1024,2278)]),(z2432,[(1024,99529),(1024,1222)]),(z2433,[(1024,99529),(1024,1222)]),(z2434,[(1024,99529),(1024,1222)]),(z2435,[(1024,99529),(1024,1222)])]
def b203 : List (List Nat × List (Nat × Nat)) := [(z2436,[(1024,99529),(1024,1222)]),(z2437,[(1024,99529),(1024,1222)]),(z2438,[(1024,16025),(1024,201730)]),(z2439,[(1024,234499),(1024,197638)]),(z2440,[(1024,689272),(1024,197638)]),(z2441,[(104,0),(1024,689272),(1024,197638)]),(z2442,[(1024,100585),(1024,2278)]),(z2443,[(1024,1222),(1024,99529),(1024,132298)]),(z2444,[(80,0),(1024,197638),(1024,201730)]),(z2445,[(1024,666073),(1024,198090)]),(z2446,[(1024,689625),(1024,198090)]),(z2447,[(1024,100585),(1024,2278)])]
def b204 : List (List Nat × List (Nat × Nat)) := [(z2448,[(1024,208010),(1024,665753)]),(z2449,[(1024,689272),(1024,205954)]),(z2450,[(1024,666073),(1024,205954)]),(z2451,[(1024,204898),(1024,208010)]),(z2452,[(1024,689272),(1024,204898)]),(z2453,[(1024,699865),(1024,204898)]),(z2454,[(10,0),(82,0),(105,0),(113,0),(154,0),(1024,204898),(1024,237667),(1024,207978)]),(z2455,[(1024,231882),(1024,666073)]),(z2456,[(1024,100585),(1024,2278)]),(z2457,[(1024,100585),(1024,2278)]),(z2458,[(1024,100585),(1024,2278)]),(z2459,[(10,0),(1024,1254),(1024,99561),(1024,132330)])]
def b205 : List (List Nat × List (Nat × Nat)) := [(z2460,[(1024,1222),(1024,99529),(1024,208010)]),(z2461,[(1024,1222),(1024,99529),(1024,132298)]),(z2462,[(1024,1222),(1024,99529),(1024,132298)]),(z2463,[(1024,469657),(1024,198090)]),(z2464,[(1024,201730),(1024,208010)]),(z2465,[(1024,689305),(1024,201730)]),(z2466,[(1024,208330),(1024,201730)]),(z2467,[(6,0),(81,0),(105,0),(114,0),(146,0),(177,0),(1024,10905),(1024,201730),(1024,207882)]),(z2468,[(216,1),(1024,5314),(1024,1222)]),(z2469,[(96,1),(128,1),(216,1),(1024,99529),(1024,1222)]),(z2470,[(72,1),(96,1),(168,1),(1024,5314),(1024,1222)]),(z2471,[(168,1),(1024,1222),(1024,99529)])]
def b206 : List (List Nat × List (Nat × Nat)) := [(z2472,[(1024,5314),(1024,1222)]),(z2473,[(72,1),(96,1),(1024,197638),(1024,1222)]),(z2474,[(1024,483979),(1024,122530)]),(z2475,[(144,1),(168,0),(184,2),(192,0),(232,1),(288,1)]),(z2476,[(1024,483979),(1024,122530)]),(z2477,[(232,1),(1024,122563),(1024,2278)]),(z2478,[(10,1),(74,1),(82,1),(97,1),(105,1),(113,1),(154,1),(184,1),(185,1),(194,1),(1024,1222),(1024,99529),(1024,122530)]),(z2479,[(144,1),(184,1),(1024,99529),(1024,1222)]),(z2480,[(232,1),(1024,122530),(1024,201730)]),(z2481,[(1024,671353),(1024,205954)]),(z2482,[(144,0),(1024,705145),(1024,204898)]),(z2483,[(1024,100585),(1024,2278)])]
def b207 : List (List Nat × List (Nat × Nat)) := [(z2484,[(10,1),(1024,1222),(1024,99529),(1024,132298)]),(z2485,[(112,0),(1024,201730),(1024,213610)]),(z2486,[(96,0),(1024,208330),(1024,666073)]),(z2487,[(14,0),(114,0),(129,0),(145,0),(153,0),(193,0),(202,0),(1024,206284),(1024,238723),(1024,208330)]),(z2488,[(14,0),(114,0),(129,0),(145,0),(153,0),(193,0),(202,0),(1024,204898),(1024,237667),(1024,208330)]),(z2489,[(14,0),(1024,2278),(1024,100585),(1024,133354)]),(z2490,[]),(z2491,[(10,0),(97,0),(113,0),(145,0),(154,0),(185,0),(194,0),(233,0),(1024,469657),(1024,201730),(1024,208330)]),(z2492,[(1024,468172),(1024,5314)]),(z2493,[(104,1),(1024,468172),(1024,5314)]),(z2494,[(104,1),(176,1),(1024,5347),(1024,2278)]),(z2495,[(6,1),(58,1),(73,1),(81,1),(104,1),(105,1),(114,1),(136,1),(137,1),(146,1),(225,1),(234,1),(1024,1222),(1024,99529),(1024,5314)])]
def b208 : List (List Nat × List (Nat × Nat)) := [(z2496,[(176,1),(296,0),(1024,5314),(1024,201730)]),(z2497,[(1024,680395),(1024,197638)]),(z2498,[(136,2),(144,0),(176,1),(1024,689272),(1024,197638)]),(z2499,[(136,1),(1024,100585),(1024,2278)]),(z2500,[(6,1),(58,1),(73,1),(81,1),(114,1),(146,1),(177,1),(225,1),(234,1),(1024,1222),(1024,99529),(1024,132298)]),(z2501,[(104,2),(112,0),(136,1),(1024,197638),(1024,201730)])]
end PEqualNP.Outside.L_meta_20550_aux

theorem PEqualNP.Outside.L_meta_20550 : True := True.intro
