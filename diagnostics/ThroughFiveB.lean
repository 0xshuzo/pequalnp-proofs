import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20404_aux

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




end PEqualNP.Outside.L_meta_20404_aux


namespace PaidChainProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_app_ge (l l2 : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i false = l2.getD (i - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_row {n : ℕ} (u v a : Fin n) :
    (oneEach u v).getD a.val false = decide (a = u) := by
  unfold oneEach
  rw [getD_app_lt _ _ _ (by simp), ofFn_getD _ a.val a.isLt]

theorem oneEach_col {n : ℕ} (u v b : Fin n) :
    (oneEach u v).getD (n + b.val) false = decide (b = v) := by
  unfold oneEach
  rw [getD_app_ge _ _ _ (by simp), List.length_ofFn, ofFn_getD _ (n + b.val - n) (by omega)]
  congr 1
  simp [Fin.ext_iff]

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

def Mono (e : List Gate) : Prop :=
  ∀ g ∈ e, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Reach (gs : List Gate) (c : ℕ) (gs' : List Gate) : Prop :=
  ∃ e, gs' = gs ++ e ∧ Mono e ∧ e.length ≤ c

theorem reach_refl (gs : List Gate) : Reach gs 0 gs := by
  refine ⟨[], (List.append_nil gs).symm, ?_, Nat.le_refl 0⟩
  intro g hg
  cases hg

theorem reach_trans {gs gs1 gs2 : List Gate} {c1 c2 c : ℕ} (h1 : Reach gs c1 gs1)
    (h2 : Reach gs1 c2 gs2) (hc : c1 + c2 ≤ c) : Reach gs c gs2 := by
  obtain ⟨e1, rfl, m1, l1⟩ := h1
  obtain ⟨e2, rfl, m2, l2⟩ := h2
  refine ⟨e1 ++ e2, List.append_assoc _ _ _, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact m1 g h
    · exact m2 g h
  · rw [List.length_append]; omega

def Has (n : ℕ) (gs : List Gate) (w : ℕ) (f : Fin n → Fin n → Bool) : Prop :=
  w < n + n + gs.length ∧ ∀ u v : Fin n, (W gs (oneEach u v)).getD w false = f u v

theorem has_reach {n : ℕ} {gs gs' : List Gate} {c w : ℕ} {f : Fin n → Fin n → Bool}
    (h : Reach gs c gs') (hw : Has n gs w f) : Has n gs' w f := by
  obtain ⟨e, rfl, _, _⟩ := h
  refine ⟨by rw [List.length_append]; have := hw.1; omega, fun u v => ?_⟩
  rw [W_append, W_prefix e _ w (by rw [W_length, oneEach_length]; exact hw.1)]
  exact hw.2 u v

theorem has_congr {n : ℕ} {gs : List Gate} {w : ℕ} {f g : Fin n → Fin n → Bool}
    (h : ∀ u v, f u v = g u v) (hw : Has n gs w f) : Has n gs w g :=
  ⟨hw.1, fun u v => (hw.2 u v).trans (h u v)⟩

theorem has_row {n : ℕ} (gs : List Gate) (a : Fin n) :
    Has n gs a.val (fun u _ => decide (a = u)) := by
  refine ⟨by have := a.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := a.isLt; omega), oneEach_row]

theorem has_col {n : ℕ} (gs : List Gate) (b : Fin n) :
    Has n gs (n + b.val) (fun _ v => decide (b = v)) := by
  refine ⟨by have := b.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := b.isLt; omega), oneEach_col]

theorem has_or {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v || g u v) := by
  refine ⟨gs ++ [⟨GateOp.or, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.or.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_or2]

theorem has_and {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v && g u v) := by
  refine ⟨gs ++ [⟨GateOp.and, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inl rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.and.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_and2]

open PEqualNP.Outside.L_meta_20404_aux (Run kept BFn exists_run_m)
abbrev Matrix (n : ℕ) := Fin n → Fin n → Bool
def blank {n : ℕ} : Matrix n := fun _ _ => false
def mulM {n : ℕ} (a b : Matrix n) : Matrix n := fun u v => a u v && b u v
def addM {n : ℕ} (a b : Matrix n) : Matrix n := fun u v => a u v || b u v

def bank {n} (gs : List Gate) (ws : List (Matrix n)) : Prop :=
  ∀ f ∈ ws, f ≠ blank → ∃ w, Has n gs w f

theorem combine {n : ℕ} (c : Bool) (a b : Matrix n) (gs : List Gate)
    (ha : a ≠ blank → ∃ w, Has n gs w a) (hb : b ≠ blank → ∃ w, Has n gs w b) :
    ∃ z : ℕ, ∃ gs', Reach gs z gs' ∧
      ((if c then mulM a b else addM a b) ≠ blank →
        ∃ w, Has n gs' w (if c then mulM a b else addM a b)) ∧
      z + (if a = blank then 1 else 0) + (if b = blank then 1 else 0) ≤
        1 + (if (if c then mulM a b else addM a b) = blank then 1 else 0) := by
  classical
  by_cases ea : a = blank
  · subst a
    cases c
    · have he : addM blank b = b := by funext u v; simp [addM, blank]
      exact ⟨0, gs, reach_refl gs, by simpa [he] using hb, by simp [he]⟩
    · have he : mulM blank b = blank := by funext u v; simp [mulM, blank]
      exact ⟨0, gs, reach_refl gs, by simp [he], by simp [he] <;> split <;> omega⟩
  · by_cases eb : b = blank
    · subst b
      cases c
      · have he : addM a blank = a := by funext u v; simp [addM, blank]
        exact ⟨0, gs, reach_refl gs, by simpa [he] using ha, by simp [he, ea]⟩
      · have he : mulM a blank = blank := by funext u v; simp [mulM, blank]
        exact ⟨0, gs, reach_refl gs, by simp [he], by simp [he, ea]⟩
    · obtain ⟨i,hi⟩ := ha ea
      obtain ⟨j,hj⟩ := hb eb
      cases c
      · obtain ⟨gs',w,ext,hw⟩ := has_or hi hj
        exact ⟨1,gs',ext,fun _ => ⟨w,hw⟩, by simp [ea,eb]⟩
      · obtain ⟨gs',w,ext,hw⟩ := has_and hi hj
        exact ⟨1,gs',ext,fun _ => ⟨w,hw⟩, by simp [ea,eb]⟩

theorem paid_projection {n s : ℕ} {y : Matrix n} (hy : y ≠ blank)
    {ws : List (Matrix n)} (run : Run id mulM addM y s ws) :
    ∀ gs, bank gs ws → ∃ cost gs' w, Reach gs cost gs' ∧ Has n gs' w y ∧
      cost + ws.count blank ≤ s := by
  classical
  refine run (fun t regs => ∀ gs, bank gs regs → ∃ cost gs' w, Reach gs cost gs' ∧ Has n gs' w y ∧ cost + regs.count blank ≤ t) ?_ ?_ ?_ ?_
  · intro gs avail
    obtain ⟨w,hw⟩ := avail y (by simp) hy
    exact ⟨0,gs,w,reach_refl _,hw,by simp [List.count_cons, beq_iff_eq,hy]⟩
  · intro s xs zs hp ih gs hz
    have hx : bank gs xs := fun f hf => hz f (hp.mem_iff.mp hf)
    obtain ⟨c,gs',w,he,hw,hc⟩ := ih gs hx
    exact ⟨c,gs',w,he,hw,by rw [← hp.count_eq blank]; exact hc⟩
  · intro s a r neg save ih gs hb
    have he : (if neg then id a else a) = a := by simp
    rw [he] at ih
    have hx : bank gs (a :: kept save a r) := by
      cases save <;> simpa [bank,kept] using hb
    obtain ⟨c,gs',w,ext,hw,hc⟩ := ih gs hx
    refine ⟨c,gs',w,ext,hw,?_⟩
    cases save <;> simp [kept,List.count_cons] at hc ⊢ <;> omega
  · intro s a b r c ka kb ih gs hb
    obtain ⟨d,gs1,ext1,hr,hprice⟩ := combine c a b gs
      (hb a (by simp)) (hb b (by simp))
    have hx : bank gs1 ((if c then mulM a b else addM a b) :: kept ka a (kept kb b r)) := by
      intro f hf hn
      rcases List.mem_cons.mp hf with he | hrest
      · subst f; exact hr hn
      · have hold : f ∈ a :: b :: r := by
          cases ka <;> cases kb <;> simp [kept] at hrest ⊢ <;> tauto
        obtain ⟨w,hw⟩ := hb f hold hn
        exact ⟨w,has_reach ext1 hw⟩
    obtain ⟨c',gs',w,ext',hw,hc⟩ := ih gs1 hx
    refine ⟨d+c',gs',w,reach_trans ext1 ext' le_rfl,hw,?_⟩
    cases ka <;> cases kb <;> simp only [kept, Bool.false_eq_true, ↓reduceIte,
      List.count_cons, beq_iff_eq] at hc ⊢ <;> omega


def sel {n : ℕ} (u v : Fin n) : Fin (n+n) → Bool :=
  Fin.append (fun i => decide (i = u)) (fun j => decide (j = v))

theorem sel_right {n : ℕ} (u v j : Fin n) : sel u v (Fin.natAdd n j) = decide (j = v) :=
  Fin.append_right _ _ j

theorem sel_left {n : ℕ} (u v j : Fin n) : sel u v (Fin.castAdd n j) = decide (j = u) :=
  Fin.append_left _ _ j

def obs {n : ℕ} (f : BFn (n+n)) : Matrix n := fun u v => f (sel u v)

theorem sel_list {n : ℕ} (u v : Fin n) : List.ofFn (sel u v) = oneEach u v := by
  rw [sel, List.ofFn_fin_append]
  rfl

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

theorem physical_run {n s : ℕ} {A : Matrix n}
    (hn : ∃ u v u' v', A u v ≠ A u' v') (h : RepSizeAtMost A s) :
    ∃ t ≤ s, ∃ ws : List (BFn (n+n)),
      ws.Sublist (List.ofFn fun i : Fin (n+n) => (fun x : Fin (n+n) → Bool => x i)) ∧
      Run id mulM addM A t (ws.map obs) := by
  obtain ⟨C,hm,hsize,hr⟩ := h
  let f : BFn (n+n) := fun x => C.eval (List.ofFn x)
  have he : obs f = A := by
    funext u v
    change C.eval (List.ofFn (sel u v)) = _
    rw [sel_list,hr u v]
  have hnc : ∃ x y, f x ≠ f y := by
    obtain ⟨u,v,u',v',hu⟩ := hn
    exact ⟨sel u v,sel u' v',fun eq => hu (by rw [← he]; exact eq)⟩
  obtain ⟨hf,hnn⟩ := mono_primitives hm
  obtain ⟨t,ht,ws,hws,hw⟩ := exists_run_m f hnc s ⟨C,hf,hnn,hsize,fun _ => rfl⟩
  refine ⟨t,ht,ws,hws,?_⟩
  rw [← he]
  exact Run.map obs (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hw

def project {n k : ℕ} (rows cols : Fin k → Fin n) (f : Matrix n) : Matrix k :=
  fun u v => f (rows u) (cols v)

theorem projected_bank {n k : ℕ} (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    {ws : List (BFn (n+n))}
    (hw : ws.Sublist (List.ofFn fun i : Fin (n+n) => (fun x : Fin (n+n) → Bool => x i))) :
    bank [] ((ws.map obs).map (project rows cols)) := by
  intro a ha hn
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  obtain ⟨w,hw',rfl⟩ := List.mem_map.mp hb
  obtain ⟨i,hei⟩ := List.mem_ofFn.mp (hw.subset hw')
  subst w
  refine Fin.addCases (motive := fun j : Fin (n+n) =>
    project rows cols (obs (fun x : Fin (n+n) → Bool => x j)) ≠ blank →
      ∃ z, Has k [] z (project rows cols (obs (fun x : Fin (n+n) → Bool => x j)))) ?_ ?_ i hn
  · intro j hh
    by_cases h : ∃ a, rows a = j
    · obtain ⟨a,rfl⟩ := h
      refine ⟨a.val, has_congr (fun u v => ?_) (has_row [] a)⟩
      simp [project,obs,sel,hr.eq_iff]
    · exfalso
      apply hh
      funext u v
      have h' : j ≠ rows u := fun he => h ⟨u,he.symm⟩
      simp only [project,obs,sel_left,sel_right,blank]; simp [h']
  · intro j hh
    by_cases h : ∃ a, cols a = j
    · obtain ⟨a,rfl⟩ := h
      refine ⟨k+a.val, has_congr (fun u v => ?_) (has_col [] a)⟩
      simp only [project,obs,sel_right,hc.eq_iff]
    · exfalso
      apply hh
      funext u v
      have h' : j ≠ cols v := fun he => h ⟨v,he.symm⟩
      simp only [project,obs,sel_left,sel_right,blank]; simp [h']

theorem physical_projection {n k s : ℕ} {A : Matrix n} (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hn : ∃ u v u' v', A u v ≠ A u' v')
    (hy : project rows cols A ≠ blank) (h : RepSizeAtMost A s) :
    ∃ (ws : List (BFn (n+n))) (cost : ℕ),
      ws.Sublist (List.ofFn fun i : Fin (n+n) => (fun x : Fin (n+n) → Bool => x i)) ∧
      (∃ t ≤ s, Run id mulM addM A t (ws.map obs)) ∧
      RepSizeAtMost (project rows cols A) cost ∧
      cost + ((ws.map obs).map (project rows cols)).count blank ≤ s := by
  obtain ⟨t,ht,ws,hws,hRun⟩ := physical_run hn h
  have hsmall : Run id mulM addM (project rows cols A) t ((ws.map obs).map (project rows cols)) :=
    Run.map (project rows cols) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hRun
  obtain ⟨d,gs,w,ext,hout,hprice⟩ := paid_projection hy hsmall [] (projected_bank rows cols hr hc hws)
  obtain ⟨e,he,hm,hd⟩ := ext
  simp only [List.nil_append] at he
  subst gs
  refine ⟨ws,d,hws,⟨t,ht,hRun⟩,⟨⟨e,w⟩,hm,hd,?_⟩,by omega⟩
  intro u v
  exact hout.2 u v

theorem run_forward {n t : ℕ} {A : Matrix n} {ws : List (Matrix n)}
    (hw : Run id mulM addM A t ws) (u v u' v' : Fin n) :
    (∀ a ∈ ws, a u v = true → a u' v' = true) → A u v = true → A u' v' = true := by
  refine hw (fun _ bank => (∀ a ∈ bank, a u v = true → a u' v' = true) →
    A u v = true → A u' v' = true) ?_ ?_ ?_ ?_
  · intro h; exact h A (by simp)
  · intro _ xs zs hp ih h
    exact ih (fun a ha => h a (hp.mem_iff.mp ha))
  · intro _ a r neg save ih h
    apply ih
    cases neg <;> cases save <;> simpa [kept] using h
  · intro _ a b r c ka kb ih h
    apply ih
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      have ha := h a (by simp)
      have hb := h b (by simp)
      cases c <;> simp [mulM,addM] <;> tauto
    · apply h
      cases ka <;> cases kb <;> simp [kept] at hx ⊢ <;> tauto

abbrev raw {n : ℕ} (i : Fin (n+n)) : BFn (n+n) := fun x => x i

def forces {n : ℕ} (A : Matrix n) (i : Fin (n+n)) : Prop :=
  ∃ u v u' v', A u v = true ∧ A u' v' = false ∧
    ∀ j : Fin (n+n), sel u v j = true → sel u' v' j = false → j = i

theorem forced_mem {n t} {A : Matrix n} {ws : List (BFn (n+n))}
    (hws : ws.Sublist (List.ofFn fun i : Fin (n+n) => raw (n:=n) i))
    (hrun : Run id mulM addM A t (ws.map obs)) (i : Fin (n+n)) (hf : forces A i) :
    raw i ∈ ws := by
  obtain ⟨u,v,u',v',hp,hn,huniq⟩ := hf
  by_contra h
  have bad := run_forward hrun u v u' v' (by
    intro a ha hap
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp (hws.subset hf)
    subst f
    cases hneg : obs (raw j) u' v' with
    | true => rfl
    | false =>
      have he := huniq j hap hneg
      subst j
      exact (h hf).elim) hp
  rw [hn] at bad
  contradiction

theorem mark_count {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (z : β) :
    ∀ (l : List α) (s : Finset α),
      (∀ x ∈ s, x ∈ l ∧ f x = z) → s.card ≤ (l.map f).count z := by
  intro l
  induction l with
  | nil =>
    intro s h
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a ha => (h a ha).1
    simp [hs]
  | cons a l ih =>
    intro s h
    by_cases ha : a ∈ s
    · have hs := ih (s.erase a) (by
        intro x hx
        obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hx
        obtain ⟨hin,hv⟩ := h x hm
        exact ⟨(List.mem_cons.mp hin).resolve_left hne,hv⟩)
      have hv := (h a ha).2
      rw [List.map_cons,List.count_cons, hv]
      simp only [beq_self_eq_true,↓reduceIte]
      rw [Finset.card_erase_of_mem ha] at hs
      omega
    · have hs := ih s (by
        intro x hx
        obtain ⟨hin,hv⟩ := h x hx
        exact ⟨(List.mem_cons.mp hin).resolve_left (fun he => ha (he ▸ hx)),hv⟩)
      simp only [List.map_cons,List.count_cons]
      omega

theorem priced_submatrix {n k s : ℕ} {A : Matrix n} (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hn : ∃ u v u' v', A u v ≠ A u' v')
    (hy : project rows cols A ≠ blank) (h : RepSizeAtMost A s)
    (D : Finset (Fin (n+n))) (hforce : ∀ i ∈ D, forces A i)
    (hzero : ∀ i ∈ D, project rows cols (obs (raw i)) = blank) :
    ∃ cost, RepSizeAtMost (project rows cols A) cost ∧ cost + D.card ≤ s := by
  classical
  obtain ⟨ws,c,hws,⟨t,_,hrun⟩,out,hprice⟩ := physical_projection rows cols hr hc hn hy h
  let F : BFn (n+n) → Matrix k := fun f => project rows cols (obs f)
  have hcount := mark_count F blank ws (D.image (raw (n:=n))) (by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨forced_mem hws hrun i (hforce i hi),hzero i hi⟩)
  have hinj : Function.Injective (raw (n:=n)) := by
    intro i j he
    have eq := congrFun he (fun k => decide (i = k))
    simpa [raw] using eq
  rw [Finset.card_image_of_injective _ hinj] at hcount
  have heq : (ws.map obs).map (project rows cols) = ws.map F := by rw [List.map_map]; rfl
  rw [heq] at hprice
  exact ⟨c,out,by omega⟩

def rpin {n} (u : Fin n) : Fin (n+n) := Fin.castAdd n u
def cpin {n} (v : Fin n) : Fin (n+n) := Fin.natAdd n v

theorem row_forces {n} {A : Matrix n} {u u' v : Fin n}
    (h1 : A u v = true) (h0 : A u' v = false) : forces A (rpin u) := by
  refine ⟨u,v,u',v,h1,h0,?_⟩
  intro j
  refine Fin.addCases (motive := fun i : Fin (n+n) => sel u v i = true →
    sel u' v i = false → i = rpin u) ?_ ?_ j
  · intro i h _
    have he : i = u := by simpa only [sel_left,sel_right,decide_eq_true_eq] using h
    exact congrArg (Fin.castAdd n) he
  · intro i h hn
    simp only [sel_left,sel_right] at h hn
    simp at h hn
    contradiction

theorem col_forces {n} {A : Matrix n} {u v v' : Fin n}
    (h1 : A u v = true) (h0 : A u v' = false) : forces A (cpin v) := by
  refine ⟨u,v,u,v',h1,h0,?_⟩
  intro j
  refine Fin.addCases (motive := fun i : Fin (n+n) => sel u v i = true →
    sel u v' i = false → i = cpin v) ?_ ?_ j
  · intro i h hn
    simp only [sel_left,sel_right] at h hn
    simp at h hn
    contradiction
  · intro i h _
    have he : i = v := by simpa only [sel_left,sel_right,decide_eq_true_eq] using h
    exact congrArg (Fin.natAdd n) he

def outside {n k : ℕ} (U : Finset (Fin n)) (r : Fin k → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => u ∉ U ∧ u ∉ Finset.univ.image r

theorem outside_price {n k : ℕ} (U : Finset (Fin n)) (r : Fin k → Fin n)
    (i : Fin k) (hi : r i ∈ U) : n ≤ U.card + (k-1) + (outside U r).card := by
  classical
  let tail := (Finset.univ.erase i).image r
  have ht : tail.card ≤ k-1 := by
    calc _ ≤ (Finset.univ.erase i).card := Finset.card_image_le
         _ = _ := by simp
  have hcover : (Finset.univ : Finset (Fin n)) ⊆ (U ∪ tail) ∪ outside U r := by
    intro x _
    by_cases h : x ∈ U
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · by_cases h' : x ∈ Finset.univ.image r
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h'
        have hj : j ≠ i := fun he => h (he ▸ hi)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,h'⟩)
  have h := Finset.card_le_card hcover
  simp only [Finset.card_univ,Fintype.card_fin] at h
  have h1 := Finset.card_union_le U tail
  have h2 := Finset.card_union_le (U ∪ tail) (outside U r)
  omega

theorem exterior_price {n k s : ℕ} {A : Matrix n} (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hn : ∃ u v u' v', A u v ≠ A u' v') (hy : project rows cols A ≠ blank)
    (h : RepSizeAtMost A s) (U V : Finset (Fin n))
    (hU : ∀ u ∉ U, ∃ u' v, A u v = true ∧ A u' v = false)
    (hV : ∀ v ∉ V, ∃ v' u, A u v = true ∧ A u v' = false)
    (iu iv : Fin k) (hu : rows iu ∈ U) (hv : cols iv ∈ V) :
    ∃ cost, RepSizeAtMost (project rows cols A) cost ∧
      cost + 2*n ≤ s + U.card + V.card + 2*(k-1) := by
  classical
  let R := outside U rows
  let S := outside V cols
  let D := R.image rpin ∪ S.image cpin
  have hforce : ∀ i ∈ D, forces A i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hr | hc
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨u',v,h1,h0⟩ := hU u (Finset.mem_filter.mp hu).2.1
      exact row_forces h1 h0
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨v',u,h1,h0⟩ := hV v (Finset.mem_filter.mp hv).2.1
      exact col_forces h1 h0
  have hzero : ∀ i ∈ D, project rows cols (obs (raw i)) = blank := by
    intro i hi
    rcases Finset.mem_union.mp hi with hr | hc
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
      funext u v
      have h' : a ≠ rows u := fun he => (Finset.mem_filter.mp ha).2.2
        (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,he.symm⟩)
      simp only [project,obs,raw,rpin,sel_left,blank]; simp [h']
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
      funext u v
      have h' : a ≠ cols v := fun he => (Finset.mem_filter.mp ha).2.2
        (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,he.symm⟩)
      simp only [project,obs,raw,cpin,sel_right,blank]; simp [h']
  have hd : Disjoint (R.image rpin) (S.image cpin) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,_,he⟩ := Finset.mem_image.mp hj
    have ee := congrArg Fin.val he
    simp [rpin,cpin] at ee
    omega
  have hDr : Function.Injective (rpin (n:=n)) := fun a b he => Fin.ext (congrArg Fin.val he)
  have hDc : Function.Injective (cpin (n:=n)) := by
    intro a b he
    have eq := congrArg Fin.val he
    exact Fin.ext (by simpa [cpin] using eq)
  have hD : D.card = R.card + S.card := by
    rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hDr,
      Finset.card_image_of_injective _ hDc]
  obtain ⟨cost,hh,hp⟩ := priced_submatrix rows cols hr hc hn hy h D hforce hzero
  have hR : n ≤ U.card + (k-1) + R.card := outside_price U rows iu hu
  have hS : n ≤ V.card + (k-1) + S.card := outside_price V cols iv hv
  exact ⟨cost,hh,by omega⟩

theorem staircase_reduction (n k a b : ℕ) (hk : 3 ≤ k) (t : Fin n → ℕ)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ n) (htop : ∃ u, t u = n)
    (hcard : (Finset.univ.image t).card = k)
    (ha : (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a)
    (hb : (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
      (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
      (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b)
    (s : ℕ) (h : RepSizeAtMost (fun u v : Fin n => decide (v.val < t u)) s) :
    ∃ cost, RepSizeAtMost (fun i j : Fin k => decide (j ≤ i)) cost ∧
      cost + 2*n ≤ s + a + b + 2*(k-1) := by
  classical
  let T := Finset.univ.image t
  let e := T.orderIsoOfFin hcard
  let τ (i : Fin k) : ℕ := (e i).val
  let rank (u : Fin n) : Fin k := e.symm ⟨t u,Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩
  have tr (u : Fin n) : τ (rank u) = t u := by
    dsimp [τ,rank]
    rw [e.apply_symm_apply]
  have hex (i : Fin k) : ∃ u, t u = τ i := by
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp (e i).property
    exact ⟨u,hu⟩
  choose rows hrows using hex
  have inc : StrictMono τ := fun _ _ hi => e.strictMono hi
  have bounded (i : Fin k) : 1 ≤ τ i ∧ τ i ≤ n := hrows i ▸ ht (rows i)
  let lo : Fin k := ⟨0,by omega⟩
  let hi : Fin k := ⟨k-1,by omega⟩
  have top : τ hi = n := by
    obtain ⟨u,hu⟩ := htop
    have hu' : rank u ≤ hi := by change (rank u).val ≤ k-1; have := (rank u).isLt; omega
    have hle := inc.monotone hu'
    rw [tr,hu] at hle
    exact Nat.le_antisymm (bounded hi).2 hle
  let prev (i : Fin k) : Fin k := ⟨i.val-1,by have := i.isLt; omega⟩
  let cols (j : Fin k) : Fin n := if hj : j.val = 0 then ⟨0,by have := bounded lo; omega⟩
    else ⟨τ (prev j),by
      have hj' : prev j < j := by change j.val-1 < j.val; omega
      exact lt_of_lt_of_le (inc hj') (bounded j).2⟩
  have cmp (i j : Fin k) : (cols j).val < t (rows i) ↔ j ≤ i := by
    rw [hrows]
    by_cases h0 : j.val = 0
    · have hb0 := (bounded i).1
      simpa [cols,h0,Fin.le_def] using (show 0 < τ i ↔ 0 ≤ i.val by omega)
    · change (if hj : j.val = 0 then _ else _ : Fin n).val < τ i ↔ j.val ≤ i.val
      rw [dif_neg h0]
      change τ (prev j) < τ i ↔ j.val ≤ i.val
      rw [inc.lt_iff_lt]
      change j.val-1 < i.val ↔ j.val ≤ i.val
      omega
  let A : Matrix n := fun u v => decide (v.val < t u)
  have he (i j : Fin k) : A (rows i) (cols j) = decide (j ≤ i) :=
    decide_eq_decide.mpr (cmp i j)
  have hp : project rows cols A = fun i j => decide (j ≤ i) := by funext i j; exact he i j
  have hr : Function.Injective rows := by
    intro i j hij
    exact inc.injective ((hrows i).symm.trans ((congrArg t hij).trans (hrows j)))
  have hc : Function.Injective cols := by
    intro i j hij
    apply le_antisymm
    · exact (cmp j i).mp (by rw [hij]; exact (cmp j j).mpr le_rfl)
    · exact (cmp i j).mp (by rw [← hij]; exact (cmp i i).mpr le_rfl)
  let U := Finset.univ.filter fun u => ∀ u', t u ≤ t u'
  let V := Finset.univ.filter fun v : Fin n => ∀ v' : Fin n,
    (Finset.univ.filter fun u => v.val < t u).card ≤ (Finset.univ.filter fun u => v'.val < t u).card
  have ulo : rows lo ∈ U := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun u => ?_⟩
    rw [hrows,← tr u]
    exact inc.monotone (show lo ≤ rank u by change 0 ≤ _; omega)
  have hlast : hi.val ≠ 0 := by dsimp [hi]; omega
  have vhi : cols hi ∈ V := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v => Finset.card_le_card ?_⟩
    intro u hu
    have hpos := (Finset.mem_filter.mp hu).2
    have hrank : prev hi < rank u := by
      apply inc.lt_iff_lt.mp
      rw [tr]
      simpa [cols,hlast] using hpos
    have huu : rank u = hi := by
      apply Fin.ext
      change hi.val-1 < (rank u).val at hrank
      have hu' := (rank u).isLt
      dsimp [hi] at hrank ⊢
      omega
    have hn : t u = n := by rw [← tr u,huu,top]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hn]; exact v.isLt⟩
  have hU : ∀ u ∉ U, ∃ u' v, A u v = true ∧ A u' v = false := by
    intro u hu
    have hh : ¬ ∀ u', t u ≤ t u' := fun hm => hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
    push_neg at hh
    obtain ⟨u',hlt⟩ := hh
    refine ⟨u',⟨t u',lt_of_lt_of_le hlt (ht u).2⟩,?_,?_⟩ <;> simp [A,hlt]
  have hV : ∀ v ∉ V, ∃ v' u, A u v = true ∧ A u v' = false := by
    intro v hv
    let N (v : Fin n) := Finset.univ.filter fun u => v.val < t u
    have hh : ¬ ∀ v', (N v).card ≤ (N v').card := fun hm => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
    push_neg at hh
    obtain ⟨v',hlt⟩ := hh
    have hs : ¬ N v ⊆ N v' := fun he => (Nat.not_le_of_lt hlt) (Finset.card_le_card he)
    obtain ⟨u,hu,hu'⟩ := Finset.not_subset.mp hs
    have hyes := (Finset.mem_filter.mp hu).2
    have hno : ¬ v'.val < t u := fun he => hu' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    exact ⟨v',u,by simp [A,hyes],by simp [A,hno]⟩
  have hlohi : ¬ hi ≤ lo := by change ¬ k-1 ≤ 0; omega
  have hn : ∃ u v u' v', A u v ≠ A u' v' := ⟨rows lo,cols lo,rows lo,cols hi,by simp [he,hlohi]⟩
  have hy : project rows cols A ≠ blank := fun hz => by
    have h0 := congrFun (congrFun hz lo) lo
    simp [hp,blank] at h0
  obtain ⟨cost,hcost,hprice⟩ := exterior_price rows cols hr hc hn hy h U V hU hV lo hi ulo vhi
  rw [hp] at hcost
  exact ⟨cost,hcost,by simpa only [show U.card = a from ha,show V.card = b from hb] using hprice⟩

theorem lift_staircase_lower (n k a b : ℕ) (hk : 3 ≤ k) (t : Fin n → ℕ)
    (ht : ∀ u, 1 ≤ t u ∧ t u ≤ n) (htop : ∃ u, t u = n)
    (hcard : (Finset.univ.image t).card = k)
    (ha : (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a)
    (hb : (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
      (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
      (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b)
    (s : ℕ) (h : RepSizeAtMost (fun u v : Fin n => decide (v.val < t u)) s)
    (stair : ∀ c, RepSizeAtMost (fun i j : Fin k => decide (j ≤ i)) c → 3*k-6 ≤ c) :
    2*n+k-4-a-b ≤ s := by
  obtain ⟨c,hc,hp⟩ := staircase_reduction n k a b hk t ht htop hcard ha hb s h
  have hl := stair c hc
  omega


end PaidChainProjection

namespace PEqualNP.Outside.L_meta_20404_aux

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





end PEqualNP.Outside.L_meta_20404_aux

namespace ChainStairFive
open PEqualNP.Outside.L_meta_20404_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def code (k : ℕ) : ℕ := 2 ^ (k / 5) + 2 ^ (5 + k % 5)

def ohPts : List ℕ := List.ofFn fun k : Fin 25 => code k.val

theorem ofFn_code : ∀ k : Fin 25, List.ofFn (pt 10 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 5) (by have := k.isLt; omega) : Fin 5)
      (Fin.mk (k.val % 5) (by have := k.isLt; omega) : Fin 5) := by
  decide +kernel

theorem ohPts_length : ohPts.length = 25 := by simp [ohPts]

theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => M.testBit (5 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 25) : C.eval (List.ofFn (pt 10 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (5 * (k / 5) + k % 5) = M.testBit k
  rw [Nat.div_add_mod]

theorem enc_rep (M : ℕ) (hM : M < 2 ^ 25) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => M.testBit (5 * u.val + v.val)) C) :
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

theorem rep_lb (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ) (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 25) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 25) (h0' : zer < 25)
    (hxs : (List.ofFn fun (i : Fin 10) => (fun x : Fin 10 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 0 M PD PM = true) (hG : symOK 0 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK 0 M PD PM G T x h = true)
    (hi : XS.sublists.all (rootOK M PD PM G T s) = true) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => M.testBit (5 * u.val + v.val)) s := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have hnot : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h] <;> exact fun h' => GateOp.noConfusion h'
  have hfan : FanInTwo C := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  have hnc : ∃ a b : Fin 10 → Bool, (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 10 (code one), pt 10 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run_m (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) hnc s
    ⟨C, hfan, hnot, hsize, fun x => rfl⟩
  have hr : NatRun 0 (encL (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) ohPts) s'
      (ws.map fun a => encL a ohPts) :=
    Run.map (fun a : BFn 10 => encL a ohPts) (fun a => (Nat.xor_zero _).symm)
      (fun a b => encL_and a b ohPts) (fun a b => encL_or a b ohPts) hrun
  rw [enc_rep M hM C hrep] at hr
  exact cert_core hp hG hT hi hs' (by rw [← hxs]; exact hsub.map _) hr



def PD_ : List (Nat × Nat) := [(1,807505),(2,686969),(3,618477),(4,583079),(5,532610),(6,16912),(7,29529),(8,27645),(9,26543),(10,24966),(11,8850),(12,792),(13,989),(14,959),(15,910),(16,406),(17,154),(18,28),(19,31),(20,30),(21,14),(22,6),(23,2)]
def PM_ : List (Nat × Nat) := [(1,33004641),(2,33004641),(3,33004641),(4,33004641),(7,33004641),(8,33004641),(9,33004641),(13,33004641),(14,33004641),(19,33004641)]
def XS_ : List Nat := [31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def T_ : BT := (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [3,1015808,6494406,8682760,32539745] .lf) [3,1015808,6494406,8682824,32539681] (.nd .lf [3,1015872,6494406,8682760,32539681] .lf)) [3,1047552,2164802,4330468,32801825] (.nd (.nd .lf [3,1047552,2164802,4592612,32539681] .lf) [3,1047552,2426946,4330468,32539681] .lf)) [3,3115074,17318431,32543777] (.nd (.nd (.nd .lf [3,3119170,17318431,32539681] .lf) [4,31,1082401,17327088,32573506] .lf) [4,31,2065441,17318416,32577602] (.nd (.nd .lf [4,31,2069537,17318416,32573506] .lf) [4,31,2164802,17327088,32539681] .lf))) [4,31,3115074,17318416,32543777] (.nd (.nd (.nd (.nd .lf [4,31,3119170,17318416,32539681] .lf) [4,64,1015808,6494406,8682760,32539681] (.nd .lf [4,992,1015808,2164802,32674981,32832809] .lf)) [4,992,1015808,4329604,32607331,32832809] (.nd (.nd .lf [4,992,1015808,8682760,32607331,32674981] .lf) [4,992,1047552,2164802,4329604,32801825] .lf)) [4,992,1047552,2164802,4591748,32539681] (.nd (.nd (.nd .lf [4,992,1047552,2426946,4329604,32539681] .lf) [4,992,2164802,4329604,32832809,33522721] .lf) [4,992,2164802,8682760,32674981,33522721] (.nd (.nd .lf [4,992,2164802,17326623,32539681] .lf) [4,992,4329604,8682760,32607331,33522721] .lf)))) [4,4096,3115074,17318431,32539681] (.nd (.nd (.nd (.nd (.nd .lf [4,8223,1082401,17318896,32573506] .lf) [4,8223,2164802,17318896,32539681] (.nd .lf [4,9184,2164802,17318431,32539681] .lf)) [4,31744,1015808,2164802,4330468,32801825] (.nd (.nd .lf [4,31744,1015808,2164802,4592612,32539681] .lf) [4,31744,1015808,2426946,4330468,32539681] .lf)) [4,31744,1015808,4329604,32607331,32810985] (.nd (.nd (.nd .lf [4,31744,1015808,4330468,32607331,32810281] .lf) [4,31744,1015808,6494406,8659208,32539745] .lf) [4,31744,1015808,6494406,8659272,32539681] (.nd (.nd .lf [4,31744,1015808,8659208,32607331,32675813] .lf) [4,31744,1015808,8659944,32607331,32674981] .lf))) [4,31744,1015872,6494406,8659208,32539681] (.nd (.nd (.nd (.nd .lf [4,31744,2164802,4329604,32810985,33522721] .lf) [4,31744,2164802,4330468,32810281,33522721] (.nd .lf [4,31744,2164802,8659208,32675813,33522721] .lf)) [4,31744,2164802,8659944,32674981,33522721] (.nd (.nd .lf [4,31744,4329604,8659944,32607331,33522721] .lf) [4,31744,4330468,8659208,32607331,33522721] .lf)) [4,31808,1015808,6494406,8659208,32539681] (.nd (.nd (.nd .lf [4,262144,1047552,2164802,4330468,32539681] .lf) [4,263136,1047552,2164802,4329604,32539681] .lf) [4,293888,1015808,2164802,4330468,32539681] (.nd (.nd .lf [4,1015808,1082401,6494406,8682760,32505920] .lf) [4,1015808,1082401,6494406,8682824,32505856] .lf))))) [4,1015808,1082465,6494406,8682760,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [4,1015808,2164802,4329604,8682760,32539745] .lf) [4,1015808,2164802,4329604,8682824,32539681] (.nd .lf [4,1015808,2164802,4329668,8682760,32539681] .lf)) [4,1015808,2164802,8659208,32570401,32675813] (.nd (.nd .lf [4,1015808,2164802,8659944,32570401,32674981] .lf) [4,1015808,2164802,17318431,32543777] .lf)) [4,1015808,2168898,17318431,32539681] (.nd (.nd (.nd .lf [4,1015808,4329604,8659944,32570401,32607331] .lf) [4,1015808,4329604,8682760,32540641,32607331] .lf) [4,1015808,4330468,8659208,32570401,32607331] (.nd (.nd .lf [4,1015808,8659208,17318559,32539681] .lf) [4,1015808,8659231,17318544,32539681] .lf))) [4,1015808,8659336,17318431,32539681] (.nd (.nd (.nd (.nd .lf [4,1015808,8659359,17318416,32539681] .lf) [4,1015872,1082401,6494406,8682760,32505856] (.nd .lf [4,1015872,2164802,4329604,8682760,32539681] .lf)) [4,1019904,2164802,17318431,32539681] (.nd (.nd .lf [4,1047552,1082401,2164802,4330468,32768000] .lf) [4,1047552,1082401,2164802,4592612,32505856] .lf)) [4,1047552,1082401,2426946,4330468,32505856] (.nd (.nd (.nd .lf [4,1047552,1344545,2164802,4330468,32505856] .lf) [4,1082401,3115074,17318431,32509952] .lf) [4,1082401,3119170,17318431,32505856] (.nd (.nd .lf [4,1086497,3115074,17318431,32505856] .lf) [4,2065441,8659231,17318544,32505856] .lf)))) [4,2065441,8659359,17318416,32505856] (.nd (.nd (.nd (.nd (.nd .lf [4,2164802,4329604,8659944,32570401,33522721] .lf) [4,2164802,4329604,8682760,32540641,33522721] (.nd .lf [4,2164802,4330468,8659208,32570401,33522721] .lf)) [4,3115074,8659944,17318431,32539681] (.nd (.nd .lf [5,31,992,1082401,2164802,32903300] .lf) [5,31,992,1082401,2426946,32641156] .lf)) [5,31,992,1082401,4329604,32835650] (.nd (.nd (.nd .lf [5,31,992,1082401,4591748,32573506] .lf) [5,31,992,1082401,17326608,32573506] .lf) [5,31,992,1344545,2164802,32641156] (.nd (.nd .lf [5,31,992,1344545,4329604,32573506] .lf) [5,31,992,2164802,4329604,32801825] .lf))) [5,31,992,2164802,4591748,32539681] (.nd (.nd (.nd (.nd .lf [5,31,992,2164802,17326608,32539681] .lf) [5,31,992,2426946,4329604,32539681] (.nd .lf [5,31,4096,2065441,17318416,32573506] .lf)) [5,31,4096,3115074,17318416,32539681] (.nd (.nd .lf [5,31,8192,1082401,17318896,32573506] .lf) [5,31,8192,2164802,17318896,32539681] .lf)) [5,31,9184,1082401,17318416,32573506] (.nd (.nd (.nd .lf [5,31,9184,2164802,17318416,32539681] .lf) [5,31,1015808,1082401,17318416,32577602] .lf) [5,31,1015808,1086497,17318416,32573506] (.nd (.nd .lf [5,31,1015808,2164802,17318416,32543777] .lf) [5,31,1015808,2168898,17318416,32539681] .lf)))))) [5,31,1015808,8659208,17318544,32539681] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,31,1015808,8659336,17318416,32539681] .lf) [5,31,1019904,1082401,17318416,32573506] (.nd .lf [5,31,1019904,2164802,17318416,32539681] .lf)) [5,31,1082401,2164802,17327088,32505856] (.nd (.nd .lf [5,31,1082401,3115074,17318416,32509952] .lf) [5,31,1082401,3119170,17318416,32505856] .lf)) [5,31,1082401,5214340,17318896,32573506] (.nd (.nd (.nd .lf [5,31,1086497,3115074,17318416,32505856] .lf) [5,31,2065441,2164802,17318416,32509952] .lf) [5,31,2065441,2168898,17318416,32505856] (.nd (.nd .lf [5,31,2065441,8659208,17318544,32505856] .lf) [5,31,2065441,8659336,17318416,32505856] .lf))) [5,31,2065441,8659944,17318416,32573506] (.nd (.nd (.nd (.nd .lf [5,31,2069537,2164802,17318416,32505856] .lf) [5,31,2164802,5214340,17318896,32539681] (.nd .lf [5,31,3115074,8659944,17318416,32539681] .lf)) [5,64,31744,1015808,6494406,8659208,32539681] (.nd (.nd .lf [5,64,1015808,1082401,6494406,8682760,32505856] .lf) [5,64,1015808,2164802,4329604,8682760,32539681] .lf)) [5,128,1015808,8659208,17318431,32539681] (.nd (.nd (.nd .lf [5,128,1015808,8659231,17318416,32539681] .lf) [5,128,2065441,8659231,17318416,32505856] .lf) [5,159,1015808,8659208,17318416,32539681] (.nd (.nd .lf [5,159,2065441,8659208,17318416,32505856] .lf) [5,992,8192,2164802,17318431,32539681] .lf)))) [5,992,8223,1082401,17318416,32573506] (.nd (.nd (.nd (.nd (.nd .lf [5,992,8223,2164802,17318416,32539681] .lf) [5,992,31744,1015808,2164802,4329604,32801825] (.nd .lf [5,992,31744,1015808,2164802,4591748,32539681] .lf)) [5,992,31744,1015808,2164802,32674981,32810281] (.nd (.nd .lf [5,992,31744,1015808,2426946,4329604,32539681] .lf) [5,992,31744,1015808,4329604,32607331,32810281] .lf)) [5,992,31744,1015808,6494406,10824010,32539681] (.nd (.nd (.nd .lf [5,992,31744,1015808,8659208,32607331,32674981] .lf) [5,992,31744,2164802,4329604,32810281,33522721] .lf) [5,992,31744,2164802,8659208,32674981,33522721] (.nd (.nd .lf [5,992,31744,4329604,8659208,32607331,33522721] .lf) [5,992,262144,1047552,2164802,4329604,32539681] .lf))) [5,992,293888,1015808,2164802,4329604,32539681] (.nd (.nd (.nd (.nd .lf [5,992,1015808,1082401,2164802,32641156,32800008] .lf) [5,992,1015808,1082401,4329604,32573506,32800008] (.nd .lf [5,992,1015808,1082401,8682760,32573506,32641156] .lf)) [5,992,1015808,2164802,4329604,8682760,32539681] (.nd (.nd .lf [5,992,1015808,2164802,4329604,9764137,32539681] .lf) [5,992,1015808,2164802,4329604,32539681,32800008] .lf)) [5,992,1015808,2164802,4329604,32539681,32832809] (.nd (.nd (.nd .lf [5,992,1015808,2164802,5412005,8682760,32539681] .lf) [5,992,1015808,2164802,5412005,9764137,32505856] .lf) [5,992,1015808,2164802,6494406,8682760,32539681] (.nd (.nd .lf [5,992,1015808,2164802,8659208,32570401,32674981] .lf) [5,992,1015808,2164802,8682760,32539681,32641156] .lf))))) [5,992,1015808,2164802,8682760,32539681,32674981] (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,992,1015808,3247203,4329604,8682760,32539681] .lf) [5,992,1015808,3247203,4329604,9764137,32505856] (.nd .lf [5,992,1015808,3247203,5412005,8682760,32505856] .lf)) [5,992,1015808,4329604,8659208,32570401,32607331] (.nd (.nd .lf [5,992,1015808,4329604,8682760,32539681,32573506] .lf) [5,992,1015808,4329604,8682760,32539681,32607331] .lf)) [5,992,1047552,1082401,2164802,4329604,32768000] (.nd (.nd (.nd .lf [5,992,1047552,1082401,2164802,4591748,32505856] .lf) [5,992,1047552,1082401,2426946,4329604,32505856] .lf) [5,992,1047552,1344545,2164802,4329604,32505856] (.nd (.nd .lf [5,992,1082401,2164802,4329604,32800008,33521664] .lf) [5,992,1082401,2164802,8682760,32641156,33521664] .lf))) [5,992,1082401,2164802,17326623,32505856] (.nd (.nd (.nd (.nd .lf [5,992,1082401,4329604,8682760,32573506,33521664] .lf) [5,992,2065441,2164802,4329604,8682760,32539681] (.nd .lf [5,992,2065441,2164802,4329604,9764137,32505856] .lf)) [5,992,2065441,2164802,5412005,8682760,32505856] (.nd (.nd .lf [5,992,2065441,3247203,4329604,8682760,32505856] .lf) [5,992,2164802,4329604,8659208,32570401,33522721] .lf)) [5,992,2164802,4329604,8682760,32539681,33521664] (.nd (.nd (.nd .lf [5,992,2164802,4329604,8682760,32539681,33522721] .lf) [5,992,2164802,5214340,17318431,32539681] .lf) [5,992,2194498,8659208,17318431,32539681] (.nd (.nd .lf [5,992,3115074,4329604,17318431,32539681] .lf) [5,992,3115074,8659208,17318431,32539681] .lf)))) [5,992,4357252,8659208,17318431,32539681] (.nd (.nd (.nd (.nd (.nd .lf [5,992,5214340,8659208,17318431,32539681] .lf) [5,4096,1015808,2164802,17318431,32539681] (.nd .lf [5,4096,1082401,3115074,17318431,32505856] .lf)) [5,8223,1082401,2164802,17318896,32505856] (.nd (.nd .lf [5,9184,1082401,2164802,17318431,32505856] .lf) [5,31744,262144,1015808,2164802,4330468,32539681] .lf)) [5,31744,263136,1015808,2164802,4329604,32539681] (.nd (.nd (.nd .lf [5,31744,1015808,1082401,2164802,4330468,32768000] .lf) [5,31744,1015808,1082401,2164802,4592612,32505856] .lf) [5,31744,1015808,1082401,2426946,4330468,32505856] (.nd (.nd .lf [5,31744,1015808,1082401,4329604,32573506,32777192] .lf) [5,31744,1015808,1082401,4330468,32573506,32776456] .lf))) [5,31744,1015808,1082401,6494406,8659208,32505920] (.nd (.nd (.nd (.nd .lf [5,31744,1015808,1082401,6494406,8659272,32505856] .lf) [5,31744,1015808,1082401,8659208,32573506,32642020] .lf) [5,31744,1015808,1082401,8659944,32573506,32641156] (.nd (.nd .lf [5,31744,1015808,1082465,6494406,8659208,32505856] .lf) [5,31744,1015808,1344545,2164802,4330468,32505856] .lf)) [5,31744,1015808,2164802,4329604,8659208,32539745] (.nd (.nd (.nd .lf [5,31744,1015808,2164802,4329604,8659272,32539681] .lf) [5,31744,1015808,2164802,4329604,8659944,32539681] .lf) [5,31744,1015808,2164802,4329604,8683496,32539681] (.nd (.nd .lf [5,31744,1015808,2164802,4329604,9742313,32539681] .lf) [5,31744,1015808,2164802,4329604,12989420,32539681] .lf))))))) [5,31744,1015808,2164802,4329604,32539681,32777192] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,31744,1015808,2164802,4329604,32539681,32810985] .lf) [5,31744,1015808,2164802,4329631,8659944,32539681] (.nd .lf [5,31744,1015808,2164802,4329668,8659208,32539681] .lf)) [5,31744,1015808,2164802,4330468,8659208,32539681] (.nd (.nd .lf [5,31744,1015808,2164802,4330468,8659231,32539681] .lf) [5,31744,1015808,2164802,4330468,8659944,32539681] .lf)) [5,31744,1015808,2164802,4330468,8682760,32539681] (.nd (.nd (.nd .lf [5,31744,1015808,2164802,4330468,9741609,32539681] .lf) [5,31744,1015808,2164802,4330468,10824010,32539681] .lf) [5,31744,1015808,2164802,4330468,12988812,32539681] (.nd (.nd .lf [5,31744,1015808,2164802,4330468,12989420,32539681] .lf) [5,31744,1015808,2164802,4330468,32539681,32776456] .lf))) [5,31744,1015808,2164802,4330468,32539681,32810281] (.nd (.nd (.nd (.nd .lf [5,31744,1015808,2164802,5412005,8659944,32539681] .lf) [5,31744,1015808,2164802,5412837,8659208,32539681] (.nd .lf [5,31744,1015808,2164802,6494406,8659944,32539681] .lf)) [5,31744,1015808,2164802,8659208,32539681,32642020] (.nd (.nd .lf [5,31744,1015808,2164802,8659208,32539681,32675813] .lf) [5,31744,1015808,2164802,8659944,32539681,32641156] .lf)) [5,31744,1015808,2164802,8659944,32539681,32674981] (.nd (.nd (.nd .lf [5,31744,1015808,3247203,4329604,8659944,32539681] .lf) [5,31744,1015808,3247203,4329604,9742313,32505856] .lf) [5,31744,1015808,3247203,4330468,8659208,32539681] (.nd (.nd .lf [5,31744,1015808,3247203,4330468,9741609,32505856] .lf) [5,31744,1015808,3247203,5412005,8659944,32505856] .lf)))) [5,31744,1015808,3247203,5412837,8659208,32505856] (.nd (.nd (.nd (.nd (.nd .lf [5,31744,1015808,4329604,8659208,32540641,32607331] .lf) [5,31744,1015808,4329604,8659944,32539681,32573506] (.nd .lf [5,31744,1015808,4329604,8659944,32539681,32607331] .lf)) [5,31744,1015808,4330468,8659208,32539681,32573506] (.nd (.nd .lf [5,31744,1015808,4330468,8659208,32539681,32607331] .lf) [5,31744,1015808,8659208,17318416,32539745] .lf)) [5,31744,1015872,1082401,6494406,8659208,32505856] (.nd (.nd (.nd .lf [5,31744,1015872,2164802,4329604,8659208,32539681] .lf) [5,31744,1015872,8659208,17318416,32539681] .lf) [5,31744,1082401,2164802,4329604,32777192,33521664] (.nd (.nd .lf [5,31744,1082401,2164802,4330468,32776456,33521664] .lf) [5,31744,1082401,2164802,8659208,32642020,33521664] .lf))) [5,31744,1082401,2164802,8659944,32641156,33521664] (.nd (.nd (.nd (.nd .lf [5,31744,1082401,4329604,8659944,32573506,33521664] .lf) [5,31744,1082401,4330468,8659208,32573506,33521664] (.nd .lf [5,31744,2065441,2164802,4329604,8659944,32539681] .lf)) [5,31744,2065441,2164802,4329604,9742313,32505856] (.nd (.nd .lf [5,31744,2065441,2164802,4330468,8659208,32539681] .lf) [5,31744,2065441,2164802,4330468,9741609,32505856] .lf)) [5,31744,2065441,2164802,5412005,8659944,32505856] (.nd (.nd (.nd .lf [5,31744,2065441,2164802,5412837,8659208,32505856] .lf) [5,31744,2065441,3247203,4329604,8659944,32505856] .lf) [5,31744,2065441,3247203,4330468,8659208,32505856] (.nd (.nd .lf [5,31744,2065441,8659208,17318416,32505920] .lf) [5,31744,2065505,8659208,17318416,32505856] .lf))))) [5,31744,2164802,4329604,8659208,32540641,33522721] (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,31744,2164802,4329604,8659944,32539681,33521664] .lf) [5,31744,2164802,4329604,8659944,32539681,33522721] (.nd .lf [5,31744,2164802,4330468,8659208,32539681,33521664] .lf)) [5,31744,2164802,4330468,8659208,32539681,33522721] (.nd (.nd .lf [5,31744,3115074,4329604,17318431,32539681] .lf) [5,31744,3115074,8659208,17318431,32539681] .lf)) [5,31808,1015808,1082401,6494406,8659208,32505856] (.nd (.nd (.nd .lf [5,31808,1015808,2164802,4329604,8659208,32539681] .lf) [5,31808,1015808,8659208,17318416,32539681] .lf) [5,31808,2065441,8659208,17318416,32505856] (.nd (.nd .lf [5,32736,1015808,2164802,4329604,8682760,32539681] .lf) [5,262144,1047552,1082401,2164802,4330468,32505856] .lf))) [5,263136,1047552,1082401,2164802,4329604,32505856] (.nd (.nd (.nd (.nd .lf [5,293888,1015808,1082401,2164802,4330468,32505856] .lf) [5,1015808,1016800,2164802,4329604,8682760,32539681] (.nd .lf [5,1015808,1047552,2164802,4329604,8659944,32539681] .lf)) [5,1015808,1047552,2164802,4330468,8659208,32539681] (.nd (.nd .lf [5,1015808,1082401,2164802,4329604,8682760,32505920] .lf) [5,1015808,1082401,2164802,4329604,8682824,32505856] .lf)) [5,1015808,1082401,2164802,4329668,8682760,32505856] (.nd (.nd (.nd .lf [5,1015808,1082401,2164802,8659208,32537600,32642020] .lf) [5,1015808,1082401,2164802,8659944,32537600,32641156] .lf) [5,1015808,1082401,2164802,17318431,32509952] (.nd (.nd .lf [5,1015808,1082401,2168898,17318431,32505856] .lf) [5,1015808,1082401,4329604,8659944,32537600,32573506] .lf)))) [5,1015808,1082401,4329604,8682760,32506848,32573506] (.nd (.nd (.nd (.nd (.nd .lf [5,1015808,1082401,4330468,8659208,32537600,32573506] .lf) [5,1015808,1082401,8659208,17318559,32505856] (.nd .lf [5,1015808,1082401,8659231,17318544,32505856] .lf)) [5,1015808,1082401,8659336,17318431,32505856] (.nd (.nd .lf [5,1015808,1082401,8659359,17318416,32505856] .lf) [5,1015808,1082465,2164802,4329604,8682760,32505856] .lf)) [5,1015808,1083361,2164802,4329604,8682760,32539681] (.nd (.nd (.nd .lf [5,1015808,1083361,3247203,4329604,8682760,32505856] .lf) [5,1015808,1086497,2164802,17318431,32505856] .lf) [5,1015808,1113121,2164802,4329604,8659944,32539681] (.nd (.nd .lf [5,1015808,1113121,2164802,4330468,8659208,32539681] .lf) [5,1015808,1113121,2164802,5412005,8659944,32505856] .lf))) [5,1015808,1113121,2164802,5412837,8659208,32505856] (.nd (.nd (.nd (.nd .lf [5,1015808,1113121,3247203,4329604,8659944,32505856] .lf) [5,1015808,1113121,3247203,4330468,8659208,32505856] (.nd .lf [5,1015808,1113121,8659208,17318416,32505920] .lf)) [5,1015808,1113185,8659208,17318416,32505856] (.nd (.nd .lf [5,1015808,2164802,4329604,4330468,8682760,32539681] .lf) [5,1015808,2164802,4329604,8659208,32540641,32570401] .lf)) [5,1015808,2164802,4329604,8659944,8682760,32539681] (.nd (.nd (.nd .lf [5,1015808,2164802,4329604,8659944,17333776,32539681] .lf) [5,1015808,2164802,4329604,8659944,32537600,32539681] .lf) [5,1015808,2164802,4329604,8659944,32539681,32570401] (.nd (.nd .lf [5,1015808,2164802,4329604,8682760,8683496,32539681] .lf) [5,1015808,2164802,4329604,8682760,17318896,32539681] .lf)))))) [5,1015808,2164802,4329604,8682760,32506848,32539681] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [5,1015808,2164802,4329604,8682760,32539681,32540641] .lf) [5,1015808,2164802,4330468,8659208,32537600,32539681] (.nd .lf [5,1015808,2164802,4330468,8659208,32539681,32570401] .lf)) [5,1015808,2164802,8659231,17318896,32539681] (.nd (.nd .lf [5,1015808,2164802,8659944,17318431,32539681] .lf) [5,1015808,2194498,8659208,17318431,32539681] .lf)) [5,1015808,2194498,8659231,17318416,32539681] (.nd (.nd (.nd .lf [5,1015872,1082401,2164802,4329604,8682760,32505856] .lf) [5,1015872,1113121,8659208,17318416,32505856] .lf) [5,1016800,1047552,2164802,4329604,8659208,32539681] (.nd (.nd .lf [5,1019904,1082401,2164802,17318431,32505856] .lf) [5,1082401,2164802,4329604,8659944,32537600,33521664] .lf))) [5,1082401,2164802,4329604,8682760,32506848,33521664] (.nd (.nd (.nd (.nd .lf [5,1082401,2164802,4330468,8659208,32537600,33521664] .lf) [5,1082401,3115074,8659944,17318431,32505856] (.nd .lf [5,1083361,2065441,2164802,4329604,8682760,32505856] .lf)) [5,1113121,2065441,2164802,4329604,8659944,32505856] (.nd (.nd .lf [5,1113121,2065441,2164802,4330468,8659208,32505856] .lf) [5,2065441,2194498,8659231,17318416,32505856] .lf)) [6,31,128,1015808,8659208,17318416,32539681] (.nd (.nd (.nd .lf [6,31,128,2065441,8659208,17318416,32505856] .lf) [6,31,992,8192,1082401,17318416,32573506] .lf) [6,31,992,8192,2164802,17318416,32539681] (.nd (.nd .lf [6,31,992,262144,1082401,2164802,32641156] .lf) [6,31,992,262144,1082401,4329604,32573506] .lf)))) [6,31,992,262144,2164802,4329604,32539681] (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,556032,1082401,2164802,4329604] .lf) [6,31,992,1015808,2164802,4329604,8682760,32539681] (.nd .lf [6,31,992,1082401,2164802,4329604,32768000] .lf)) [6,31,992,1082401,2164802,4591748,32505856] (.nd (.nd .lf [6,31,992,1082401,2164802,17326608,32505856] .lf) [6,31,992,1082401,2164802,17333776,32641156] .lf)) [6,31,992,1082401,2426946,4329604,32505856] (.nd (.nd (.nd .lf [6,31,992,1082401,3115074,17318416,32641156] .lf) [6,31,992,1082401,4329604,17333776,32573506] .lf) [6,31,992,1082401,5214340,17318416,32573506] (.nd (.nd .lf [6,31,992,1113121,3115074,8659208,17318416] .lf) [6,31,992,1113121,5214340,8659208,17318416] .lf))) [6,31,992,1113121,8659208,17318416,32573506] (.nd (.nd (.nd (.nd .lf [6,31,992,1113121,8659208,17318416,32641156] .lf) [6,31,992,1344545,2164802,4329604,32505856] (.nd .lf [6,31,992,2065441,2164802,17318416,32641156] .lf)) [6,31,992,2065441,2194498,8659208,17318416] (.nd (.nd .lf [6,31,992,2065441,4329604,17318416,32573506] .lf) [6,31,992,2065441,4357252,8659208,17318416] .lf)) [6,31,992,2065441,8659208,17318416,32573506] (.nd (.nd (.nd .lf [6,31,992,2065441,8659208,17318416,32641156] .lf) [6,31,992,2164802,4329604,17333776,32539681] .lf) [6,31,992,2164802,5214340,17318416,32539681] (.nd (.nd .lf [6,31,992,2194498,5214340,8659208,17318416] .lf) [6,31,992,2194498,8659208,17318416,32539681] .lf))))) [6,31,992,2194498,8659208,17318416,32641156] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31,992,3115074,4329604,17318416,32539681] .lf) [6,31,992,3115074,4357252,8659208,17318416] (.nd .lf [6,31,992,3115074,8659208,17318416,32539681] .lf)) [6,31,992,3115074,8659208,17318416,32641156] (.nd (.nd .lf [6,31,992,4357252,8659208,17318416,32539681] .lf) [6,31,992,4357252,8659208,17318416,32573506] .lf)) [6,31,992,5214340,8659208,17318416,32539681] (.nd (.nd (.nd .lf [6,31,992,5214340,8659208,17318416,32573506] .lf) [6,31,4096,1015808,1082401,17318416,32573506] .lf) [6,31,4096,1015808,2164802,17318416,32539681] (.nd (.nd .lf [6,31,4096,1082401,3115074,17318416,32505856] .lf) [6,31,4096,2065441,2164802,17318416,32505856] .lf))) [6,31,8192,1082401,2164802,17318896,32505856] (.nd (.nd (.nd (.nd .lf [6,31,9184,1082401,2164802,17318416,32505856] .lf) [6,31,31744,525280,1082401,2164802,4329604] (.nd .lf [6,31,31744,1015808,2164802,4329604,8659944,32539681] .lf)) [6,31,31744,1015808,2164802,4330468,8659208,32539681] (.nd (.nd .lf [6,31,31744,1082401,4329604,17318896,32573506] .lf) [6,31,31744,1082401,8659208,17318896,32573506] .lf)) [6,31,31744,2065441,4329604,17318416,32573506] (.nd (.nd (.nd .lf [6,31,31744,2065441,8659208,17318416,32573506] .lf) [6,31,31744,2164802,4329604,17318896,32539681] .lf) [6,31,31744,2164802,8659208,17318896,32539681] (.nd (.nd .lf [6,31,31744,3115074,4329604,17318416,32539681] .lf) [6,31,31744,3115074,8659208,17318416,32539681] .lf)))) [6,31,1015808,1082401,2164802,17318416,32509952] (.nd (.nd (.nd (.nd (.nd .lf [6,31,1015808,1082401,2168898,17318416,32505856] .lf) [6,31,1015808,1082401,4329604,8659944,32573506] (.nd .lf [6,31,1015808,1082401,4329604,8682760,32573506] .lf)) [6,31,1015808,1082401,4329604,17318896,32573506] (.nd (.nd .lf [6,31,1015808,1082401,4329604,17333776,32573506] .lf) [6,31,1015808,1082401,8659208,17318544,32505856] .lf)) [6,31,1015808,1082401,8659208,17318896,32573506] (.nd (.nd (.nd .lf [6,31,1015808,1082401,8659336,17318416,32505856] .lf) [6,31,1015808,1082401,8659944,17318416,32573506] .lf) [6,31,1015808,1086497,2164802,17318416,32505856] (.nd (.nd .lf [6,31,1015808,1113121,8659208,17318416,32573506] .lf) [6,31,1015808,2164802,4329604,8659944,32539681] .lf))) [6,31,1015808,2164802,4329604,8682760,32539681] (.nd (.nd (.nd (.nd .lf [6,31,1015808,2164802,4329604,17318896,32539681] .lf) [6,31,1015808,2164802,4329604,17333776,32539681] .lf) [6,31,1015808,2164802,8659208,17318896,32539681] (.nd (.nd .lf [6,31,1015808,2164802,8659944,17318416,32539681] .lf) [6,31,1015808,2194498,8659208,17318416,32539681] .lf)) [6,31,1019904,1082401,2164802,17318416,32505856] (.nd (.nd (.nd .lf [6,31,1082401,2164802,5214340,17318896,32505856] .lf) [6,31,1082401,3115074,8659944,17318416,32505856] .lf) [6,31,1113121,3115074,8659208,17318416,32505856] (.nd (.nd .lf [6,31,2065441,2164802,8659944,17318416,32505856] .lf) [6,31,2065441,2194498,8659208,17318416,32505856] .lf)))))))) [6,64,31744,1015808,1082401,6494406,8659208,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,64,31744,1015808,2164802,4329604,8659208,32539681] .lf) [6,64,31744,1015808,8659208,17318416,32539681] (.nd .lf [6,64,31744,2065441,8659208,17318416,32505856] .lf)) [6,64,1015808,1082401,2164802,4329604,8682760,32505856] (.nd (.nd .lf [6,64,1015808,1113121,8659208,17318416,32505856] .lf) [6,128,1015808,1082401,8659208,17318431,32505856] .lf)) [6,128,1015808,1082401,8659231,17318416,32505856] (.nd (.nd (.nd .lf [6,159,1015808,1082401,8659208,17318416,32505856] .lf) [6,992,8192,1082401,2164802,17318431,32505856] .lf) [6,992,8223,1082401,2164802,17318416,32505856] (.nd (.nd .lf [6,992,31744,262144,1015808,2164802,4329604,32539681] .lf) [6,992,31744,524319,1082401,2164802,4329604] .lf))) [6,992,31744,1015808,1082401,2164802,4329604,32768000] (.nd (.nd (.nd (.nd .lf [6,992,31744,1015808,1082401,2164802,4591748,32505856] .lf) [6,992,31744,1015808,1082401,2164802,32641156,32776456] (.nd .lf [6,992,31744,1015808,1082401,2426946,4329604,32505856] .lf)) [6,992,31744,1015808,1082401,4329604,32573506,32776456] (.nd (.nd .lf [6,992,31744,1015808,1082401,6494406,10824010,32505856] .lf) [6,992,31744,1015808,1082401,8659208,32573506,32641156] .lf)) [6,992,31744,1015808,1344545,2164802,4329604,32505856] (.nd (.nd (.nd .lf [6,992,31744,1015808,2164802,4329604,8659208,32539681] .lf) [6,992,31744,1015808,2164802,4329604,8659231,32539681] .lf) [6,992,31744,1015808,2164802,4329604,8659944,32539681] (.nd (.nd .lf [6,992,31744,1015808,2164802,4329604,8682760,32539681] .lf) [6,992,31744,1015808,2164802,4329604,9741609,32539681] .lf)))) [6,992,31744,1015808,2164802,4329604,10824010,32539681] (.nd (.nd (.nd (.nd (.nd .lf [6,992,31744,1015808,2164802,4329604,12988812,32539681] .lf) [6,992,31744,1015808,2164802,4329604,32539681,32776456] (.nd .lf [6,992,31744,1015808,2164802,4329604,32539681,32810281] .lf)) [6,992,31744,1015808,2164802,4329631,8659208,32539681] (.nd (.nd .lf [6,992,31744,1015808,2164802,4330468,8659208,32539681] .lf) [6,992,31744,1015808,2164802,5412005,8659208,32539681] .lf)) [6,992,31744,1015808,2164802,5412005,9741609,32505856] (.nd (.nd (.nd .lf [6,992,31744,1015808,2164802,6494406,8659208,32539681] .lf) [6,992,31744,1015808,2164802,8659208,32539681,32641156] .lf) [6,992,31744,1015808,2164802,8659208,32539681,32674981] (.nd (.nd .lf [6,992,31744,1015808,2164831,4329604,8659208,32539681] .lf) [6,992,31744,1015808,3247203,4329604,8659208,32539681] .lf))) [6,992,31744,1015808,3247203,4329604,9741609,32505856] (.nd (.nd (.nd (.nd .lf [6,992,31744,1015808,3247203,5412005,8659208,32505856] .lf) [6,992,31744,1015808,4329604,8659208,32539681,32573506] (.nd .lf [6,992,31744,1015808,4329604,8659208,32539681,32607331] .lf)) [6,992,31744,1082401,2164802,4329604,32776456,33521664] (.nd (.nd .lf [6,992,31744,1082401,2164802,8659208,32641156,33521664] .lf) [6,992,31744,1082401,4329604,8659208,32573506,33521664] .lf)) [6,992,31744,2065441,2164802,4329604,8659208,32539681] (.nd (.nd (.nd .lf [6,992,31744,2065441,2164802,4329604,9741609,32505856] .lf) [6,992,31744,2065441,2164802,5412005,8659208,32505856] .lf) [6,992,31744,2065441,3247203,4329604,8659208,32505856] (.nd (.nd .lf [6,992,31744,2164802,4329604,8659208,17809936,32539681] .lf) [6,992,31744,2164802,4329604,8659208,32539681,33521664] .lf))))) [6,992,31744,2164802,4329604,8659208,32539681,33522721] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,992,31744,2164802,4329604,17318431,32539681] .lf) [6,992,31744,2164802,8659208,17318431,32539681] (.nd .lf [6,992,31744,4329604,8659208,17318431,32539681] .lf)) [6,992,262144,1047552,1082401,2164802,4329604,32505856] (.nd (.nd .lf [6,992,293888,1015808,1082401,2164802,4329604,32505856] .lf) [6,992,1015808,1047552,2164802,4329604,8659208,32539681] .lf)) [6,992,1015808,1082401,2164802,4329604,8682760,32505856] (.nd (.nd (.nd .lf [6,992,1015808,1082401,2164802,4329604,8682760,32539681] .lf) [6,992,1015808,1082401,2164802,4329604,9764137,32505856] .lf) [6,992,1015808,1082401,2164802,4329604,32505856,32800008] (.nd (.nd .lf [6,992,1015808,1082401,2164802,5412005,8682760,32505856] .lf) [6,992,1015808,1082401,2164802,6494406,8682760,32505856] .lf))) [6,992,1015808,1082401,2164802,8659208,32537600,32641156] (.nd (.nd (.nd (.nd .lf [6,992,1015808,1082401,2164802,8682760,32505856,32641156] .lf) [6,992,1015808,1082401,3247203,4329604,8682760,32505856] (.nd .lf [6,992,1015808,1082401,4329604,8659208,32537600,32573506] .lf)) [6,992,1015808,1082401,4329604,8682760,32505856,32573506] (.nd (.nd .lf [6,992,1015808,1113121,2164802,4329604,8659208,32539681] .lf) [6,992,1015808,1113121,2164802,5412005,8659208,32505856] .lf)) [6,992,1015808,1113121,3247203,4329604,8659208,32505856] (.nd (.nd (.nd .lf [6,992,1015808,2164802,4329604,8659208,8682760,32539681] .lf) [6,992,1015808,2164802,4329604,8659208,17333776,32539681] .lf) [6,992,1015808,2164802,4329604,8659208,32537600,32539681] (.nd (.nd .lf [6,992,1015808,2164802,4329604,8659208,32539681,32570401] .lf) [6,992,1015808,2164802,4329604,8659231,32539681] .lf)))) [6,992,1015808,2164802,4329604,8682760,17318416,32539681] (.nd (.nd (.nd (.nd (.nd .lf [6,992,1015808,2164802,4329604,8682760,32505856,32539681] .lf) [6,992,1015808,2164802,4329604,8682760,32539681] (.nd .lf [6,992,1015808,2164802,4329604,17318431,32539681] .lf)) [6,992,1015808,2164802,4329604,17333776,32539681] (.nd (.nd .lf [6,992,1015808,2164802,8659208,17318431,32539681] .lf) [6,992,1015808,2164802,8659231,17318416,32539681] .lf)) [6,992,1015808,4329604,8659208,17318431,32539681] (.nd (.nd (.nd .lf [6,992,1015808,4329604,8659231,17318416,32539681] .lf) [6,992,1082401,2065441,2164802,4329604,8682760,32505856] .lf) [6,992,1082401,2164802,4329604,8659208,32537600,33521664] (.nd (.nd .lf [6,992,1082401,2164802,4329604,8682760,32505856,33521664] .lf) [6,992,1082401,2164802,5214340,17318431,32505856] .lf))) [6,992,1082401,2194498,8659208,17318431,32505856] (.nd (.nd (.nd (.nd .lf [6,992,1082401,3115074,4329604,17318431,32505856] .lf) [6,992,1082401,3115074,8659208,17318431,32505856] (.nd .lf [6,992,1082401,4357252,8659208,17318431,32505856] .lf)) [6,992,1082401,5214340,8659208,17318431,32505856] (.nd (.nd .lf [6,992,1113121,2065441,2164802,4329604,8659208,32505856] .lf) [6,992,2065441,2164802,8659231,17318416,32505856] .lf)) [6,992,2065441,4329604,8659231,17318416,32505856] (.nd (.nd (.nd .lf [6,4096,1015808,1082401,2164802,17318431,32505856] .lf) [6,31744,32736,1015808,2164802,4329604,8659208,32539681] .lf) [6,31744,262144,1015808,1082401,2164802,4330468,32505856] (.nd (.nd .lf [6,31744,263136,1015808,1082401,2164802,4329604,32505856] .lf) [6,31744,1015808,1016800,2164802,4329604,8659208,32539681] .lf)))))) [6,31744,1015808,1082401,2164802,4329604,8659208,32505920] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4329604,8659272,32505856] .lf) [6,31744,1015808,1082401,2164802,4329604,8659944,32505856] (.nd .lf [6,31744,1015808,1082401,2164802,4329604,8659944,32539681] .lf)) [6,31744,1015808,1082401,2164802,4329604,8683496,32505856] (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4329604,9742313,32505856] .lf) [6,31744,1015808,1082401,2164802,4329604,12989420,32505856] .lf)) [6,31744,1015808,1082401,2164802,4329604,32505856,32777192] (.nd (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4329631,8659944,32505856] .lf) [6,31744,1015808,1082401,2164802,4329668,8659208,32505856] .lf) [6,31744,1015808,1082401,2164802,4330468,8659208,32505856] (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4330468,8659208,32539681] .lf) [6,31744,1015808,1082401,2164802,4330468,8659231,32505856] .lf))) [6,31744,1015808,1082401,2164802,4330468,8659944,32505856] (.nd (.nd (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4330468,8682760,32505856] .lf) [6,31744,1015808,1082401,2164802,4330468,9741609,32505856] (.nd .lf [6,31744,1015808,1082401,2164802,4330468,10824010,32505856] .lf)) [6,31744,1015808,1082401,2164802,4330468,12988812,32505856] (.nd (.nd .lf [6,31744,1015808,1082401,2164802,4330468,12989420,32505856] .lf) [6,31744,1015808,1082401,2164802,4330468,32505856,32776456] .lf)) [6,31744,1015808,1082401,2164802,5412005,8659944,32505856] (.nd (.nd (.nd .lf [6,31744,1015808,1082401,2164802,5412837,8659208,32505856] .lf) [6,31744,1015808,1082401,2164802,6494406,8659944,32505856] .lf) [6,31744,1015808,1082401,2164802,8659208,32505856,32642020] (.nd (.nd .lf [6,31744,1015808,1082401,2164802,8659944,32505856,32641156] .lf) [6,31744,1015808,1082401,3247203,4329604,8659944,32505856] .lf)))) [6,31744,1015808,1082401,3247203,4330468,8659208,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,31744,1015808,1082401,4329604,8659208,32506848,32573506] .lf) [6,31744,1015808,1082401,4329604,8659944,32505856,32573506] (.nd .lf [6,31744,1015808,1082401,4330468,8659208,32505856,32573506] .lf)) [6,31744,1015808,1082401,8659208,17318416,32505920] (.nd (.nd .lf [6,31744,1015808,1082465,2164802,4329604,8659208,32505856] .lf) [6,31744,1015808,1082465,8659208,17318416,32505856] .lf)) [6,31744,1015808,1083361,2164802,4329604,8659208,32539681] (.nd (.nd (.nd .lf [6,31744,1015808,1083361,3247203,4329604,8659208,32505856] .lf) [6,31744,1015808,2164802,4329604,4330468,8659208,32539681] .lf) [6,31744,1015808,2164802,4329604,8659208,8659944,32539681] (.nd (.nd .lf [6,31744,1015808,2164802,4329604,8659208,17318896,32539681] .lf) [6,31744,1015808,2164802,4329604,8659208,32506848,32539681] .lf))) [6,31744,1015808,2164802,4329604,8659208,32539681,32540641] (.nd (.nd (.nd (.nd .lf [6,31744,1015808,2164802,4329604,8659231,32539681] .lf) [6,31744,1015808,2164802,4329604,8659944,17318416,32539681] (.nd .lf [6,31744,1015808,2164802,4329604,8659944,32505856,32539681] .lf)) [6,31744,1015808,2164802,4329604,8659944,32539681] (.nd (.nd .lf [6,31744,1015808,2164802,4329604,17318431,32539681] .lf) [6,31744,1015808,2164802,4329604,17318896,32539681] .lf)) [6,31744,1015808,2164802,4329631,8659208,32539681] (.nd (.nd (.nd .lf [6,31744,1015808,2164802,4329631,17318416,32539681] .lf) [6,31744,1015808,2164802,4330468,8659208,17318416,32539681] .lf) [6,31744,1015808,2164802,4330468,8659208,32505856,32539681] (.nd (.nd .lf [6,31744,1015808,2164802,4330468,8659208,32539681] .lf) [6,31744,1015808,2164802,4330468,17318416,32539681] .lf))))) [6,31744,1015808,2164802,8659208,17318431,32539681] (.nd (.nd (.nd (.nd (.nd (.nd .lf [6,31744,1015808,2164802,8659208,17318896,32539681] .lf) [6,31744,1015808,2164802,8659231,17318416,32539681] (.nd .lf [6,31744,1015808,2164802,8659944,17318416,32539681] .lf)) [6,31744,1015808,4329604,8659208,17318418,32505856] (.nd (.nd .lf [6,31744,1015808,4329604,8659208,17318431,32539681] .lf) [6,31744,1015808,4329604,8659210,17318416,32505856] .lf)) [6,31744,1015808,4329604,8659231,17318416,32539681] (.nd (.nd (.nd .lf [6,31744,1015808,4329606,8659208,17318416,32505856] .lf) [6,31744,1015808,4329631,8659208,17318416,32539681] .lf) [6,31744,1015872,1082401,2164802,4329604,8659208,32505856] (.nd (.nd .lf [6,31744,1015872,1082401,8659208,17318416,32505856] .lf) [6,31744,1082401,2065441,2164802,4329604,8659944,32505856] .lf))) [6,31744,1082401,2065441,2164802,4330468,8659208,32505856] (.nd (.nd (.nd (.nd .lf [6,31744,1082401,2164802,4329604,8659208,32506848,33521664] .lf) [6,31744,1082401,2164802,4329604,8659944,32505856,33521664] (.nd .lf [6,31744,1082401,2164802,4330468,8659208,32505856,33521664] .lf)) [6,31744,1082401,3115074,4329604,17318431,32505856] (.nd (.nd .lf [6,31744,1082401,3115074,8659208,17318431,32505856] .lf) [6,31744,1083361,2065441,2164802,4329604,8659208,32505856] .lf)) [6,31744,2065441,2164802,4329631,17318416,32505856] (.nd (.nd (.nd .lf [6,31744,2065441,2164802,4330468,17318416,32505856] .lf) [6,31744,2065441,2164802,8659231,17318416,32505856] .lf) [6,31744,2065441,2164802,8659944,17318416,32505856] (.nd (.nd .lf [6,31744,2065441,4329604,8659231,17318416,32505856] .lf) [6,31744,2065441,4329631,8659208,17318416,32505856] .lf)))) [6,31808,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd (.nd .lf [6,31808,1015808,1082401,8659208,17318416,32505856] .lf) [6,32736,1015808,1082401,2164802,4329604,8682760,32505856] (.nd .lf [6,1015808,1016800,1082401,2164802,4329604,8682760,32505856] .lf)) [6,1015808,1047552,1082401,2164802,4329604,8659944,32505856] (.nd (.nd .lf [6,1015808,1047552,1082401,2164802,4330468,8659208,32505856] .lf) [6,1015808,1082401,1083361,2164802,4329604,8682760,32505856] .lf)) [6,1015808,1082401,1113121,2164802,4329604,8659944,32505856] (.nd (.nd (.nd .lf [6,1015808,1082401,1113121,2164802,4330468,8659208,32505856] .lf) [6,1015808,1082401,2164802,4329604,4330468,8682760,32505856] .lf) [6,1015808,1082401,2164802,4329604,8659208,32506848,32537600] (.nd (.nd .lf [6,1015808,1082401,2164802,4329604,8659944,8682760,32505856] .lf) [6,1015808,1082401,2164802,4329604,8659944,17333776,32505856] .lf))) [6,1015808,1082401,2164802,4329604,8659944,32505856,32537600] (.nd (.nd (.nd (.nd .lf [6,1015808,1082401,2164802,4329604,8682760,8683496,32505856] .lf) [6,1015808,1082401,2164802,4329604,8682760,17318896,32505856] .lf) [6,1015808,1082401,2164802,4329604,8682760,32505856,32506848] (.nd (.nd .lf [6,1015808,1082401,2164802,4330468,8659208,32505856,32537600] .lf) [6,1015808,1082401,2164802,8659231,17318896,32505856] .lf)) [6,1015808,1082401,2164802,8659944,17318431,32505856] (.nd (.nd (.nd .lf [6,1015808,1082401,2194498,8659208,17318431,32505856] .lf) [6,1015808,1082401,2194498,8659231,17318416,32505856] .lf) [6,1015808,1083361,1113121,2164802,4329604,8659208,32505856] (.nd (.nd .lf [6,1015808,1113121,4329631,8659208,17318416,32505856] .lf) [6,1016800,1047552,1082401,2164802,4329604,8659208,32505856] .lf))))))) [7,2,31744,1015808,4329604,8659208,17318416,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,128,1015808,1082401,8659208,17318416,32505856] .lf) [7,31,992,8192,1082401,2164802,17318416,32505856] (.nd .lf [7,31,992,31744,524288,1082401,2164802,4329604] .lf)) [7,31,992,31744,1015808,2164802,4329604,8659208,32539681] (.nd (.nd .lf [7,31,992,31744,1082401,2164802,4329604,32776456] .lf) [7,31,992,31744,1082401,2164802,5214340,17318416] .lf)) [7,31,992,31744,1082401,2164802,8659208,32641156] (.nd (.nd (.nd .lf [7,31,992,31744,1082401,2164802,9412872,17318416] .lf) [7,31,992,31744,1082401,2164802,17318416,32641156] .lf) [7,31,992,31744,1082401,2164802,17318416,32776456] (.nd (.nd .lf [7,31,992,31744,1082401,3115074,4329604,17318416] .lf) [7,31,992,31744,1082401,3115074,8659208,17318416] .lf))) [7,31,992,31744,1082401,4329604,8659208,32573506] (.nd (.nd (.nd (.nd .lf [7,31,992,31744,1082401,4329604,9412872,17318416] .lf) [7,31,992,31744,1082401,4329604,17318416,32573506] (.nd .lf [7,31,992,31744,1082401,4329604,17318416,32776456] .lf)) [7,31,992,31744,1082401,5214340,8659208,17318416] (.nd (.nd .lf [7,31,992,31744,1082401,8659208,17318416,32573506] .lf) [7,31,992,31744,1082401,8659208,17318416,32641156] .lf)) [7,31,992,31744,2065441,2164802,4329604,17318416] (.nd (.nd (.nd .lf [7,31,992,31744,2065441,2164802,8659208,17318416] .lf) [7,31,992,31744,2065441,4329604,8659208,17318416] .lf) [7,31,992,31744,2164802,4329604,8659208,32539681] (.nd (.nd .lf [7,31,992,31744,2164802,4329604,9412872,17318416] .lf) [7,31,992,31744,2164802,4329604,17318416,32539681] .lf)))) [7,31,992,31744,2164802,4329604,17318416,32776456] (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,31744,2164802,5214340,8659208,17318416] .lf) [7,31,992,31744,2164802,8659208,17318416,32539681] (.nd .lf [7,31,992,31744,2164802,8659208,17318416,32641156] .lf)) [7,31,992,31744,3115074,4329604,8659208,17318416] (.nd (.nd .lf [7,31,992,31744,4329604,8659208,17318416,32539681] .lf) [7,31,992,31744,4329604,8659208,17318416,32573506] .lf)) [7,31,992,262144,1082401,2164802,4329604,32505856] (.nd (.nd (.nd .lf [7,31,992,1015808,1082401,2164802,4329604,8682760,32505856] .lf) [7,31,992,1015808,1082401,2164802,8659208,32641156] .lf) [7,31,992,1015808,1082401,2164802,17318416,32641156] (.nd (.nd .lf [7,31,992,1015808,1082401,2194498,8659208,17318416] .lf) [7,31,992,1015808,1082401,4329604,8659208,32573506] .lf))) [7,31,992,1015808,1082401,4329604,17318416,32573506] (.nd (.nd (.nd (.nd .lf [7,31,992,1015808,1082401,4357252,8659208,17318416] .lf) [7,31,992,1015808,1082401,8659208,17318416,32573506] (.nd .lf [7,31,992,1015808,1082401,8659208,17318416,32641156] .lf)) [7,31,992,1015808,1113121,2164802,8659208,17318416] (.nd (.nd .lf [7,31,992,1015808,1113121,4329604,8659208,17318416] .lf) [7,31,992,1015808,2164802,4329604,8659208,32539681] .lf)) [7,31,992,1015808,2164802,4329604,17318416,32539681] (.nd (.nd (.nd .lf [7,31,992,1015808,2164802,4357252,8659208,17318416] .lf) [7,31,992,1015808,2164802,8659208,17318416,32539681] .lf) [7,31,992,1015808,2164802,8659208,17318416,32641156] (.nd (.nd .lf [7,31,992,1015808,2194498,4329604,8659208,17318416] .lf) [7,31,992,1015808,4329604,8659208,17318416,32539681] .lf))))) [7,31,992,1015808,4329604,8659208,17318416,32573506] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31,992,1082401,2164802,4329604,17333776,32505856] .lf) [7,31,992,1082401,2164802,5214340,17318416,32505856] (.nd .lf [7,31,992,1082401,2194498,8659208,17318416,32505856] .lf)) [7,31,992,1082401,3115074,4329604,17318416,32505856] (.nd (.nd .lf [7,31,992,1082401,3115074,8659208,17318416,32505856] .lf) [7,31,992,1082401,4357252,8659208,17318416,32505856] .lf)) [7,31,992,1082401,5214340,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,992,1113121,2164802,8659208,17318416,32505856] .lf) [7,31,992,1113121,4329604,8659208,17318416,32505856] .lf) [7,31,992,2065441,2164802,4329604,17318416,32505856] (.nd (.nd .lf [7,31,992,2065441,2164802,8659208,17318416,32505856] .lf) [7,31,992,2065441,4329604,8659208,17318416,32505856] .lf))) [7,31,992,2164802,4357252,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,992,2164802,5214340,8659208,17318416,32505856] .lf) [7,31,992,2194498,4329604,8659208,17318416,32505856] (.nd .lf [7,31,992,3115074,4329604,8659208,17318416,32505856] .lf)) [7,31,4096,1015808,1082401,2164802,17318416,32505856] (.nd (.nd .lf [7,31,31744,1015808,1082401,2164802,4329604,8659944,32505856] .lf) [7,31,31744,1015808,1082401,2164802,4330468,8659208,32505856] .lf)) [7,31,31744,1015808,1082401,4329604,8659208,32573506] (.nd (.nd (.nd .lf [7,31,31744,1015808,1082401,4329604,17318416,32573506] .lf) [7,31,31744,1015808,1082401,8659208,17318416,32573506] .lf) [7,31,31744,1015808,1083361,4329604,8659208,17318416] (.nd (.nd .lf [7,31,31744,1015808,2164802,4329604,8659208,32539681] .lf) [7,31,31744,1015808,2164802,4329604,17318416,32539681] .lf)))) [7,31,31744,1015808,2164802,8659208,17318416,32539681] (.nd (.nd (.nd (.nd (.nd .lf [7,31,31744,1015808,2165730,4329604,8659208,17318416] .lf) [7,31,31744,1015808,4329604,8659208,17318416,32539681] (.nd .lf [7,31,31744,1015808,4329604,8659208,17318416,32573506] .lf)) [7,31,31744,1082401,2164802,4329604,17318896,32505856] (.nd (.nd .lf [7,31,31744,1082401,2164802,8659208,17318896,32505856] .lf) [7,31,31744,1082401,3115074,4329604,17318416,32505856] .lf)) [7,31,31744,1082401,3115074,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,31744,1083361,4329604,8659208,17318416,32505856] .lf) [7,31,31744,2065441,2164802,4329604,17318416,32505856] .lf) [7,31,31744,2065441,2164802,8659208,17318416,32505856] (.nd (.nd .lf [7,31,31744,2065441,4329604,8659208,17318416,32505856] .lf) [7,31,31744,2165730,4329604,8659208,17318416,32505856] .lf))) [7,31,31744,3115074,4329604,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31,1015808,1082401,2164802,4329604,8659944,32505856] .lf) [7,31,1015808,1082401,2164802,4329604,8682760,32505856] (.nd .lf [7,31,1015808,1082401,2164802,4329604,17318896,32505856] .lf)) [7,31,1015808,1082401,2164802,4329604,17333776,32505856] (.nd (.nd .lf [7,31,1015808,1082401,2164802,8659208,17318896,32505856] .lf) [7,31,1015808,1082401,2164802,8659944,17318416,32505856] .lf)) [7,31,1015808,1082401,2194498,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,31,1015808,1083361,4329604,8659208,17318416,32505856] .lf) [7,31,1015808,1113121,2164802,8659208,17318416,32505856] .lf) [7,31,1015808,1113121,4329604,8659208,17318416,32505856] (.nd (.nd .lf [7,31,1015808,2165730,4329604,8659208,17318416,32505856] .lf) [7,31,1015808,2194498,4329604,8659208,17318416,32505856] .lf)))))) [7,64,31744,1015808,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,64,31744,1015808,1082401,8659208,17318416,32505856] .lf) [7,992,31744,262144,1015808,1082401,2164802,4329604,32505856] (.nd .lf [7,992,31744,1015808,1082401,2164802,4329604,8659208,32505856] .lf)) [7,992,31744,1015808,1082401,2164802,4329604,8659208,32539681] (.nd (.nd .lf [7,992,31744,1015808,1082401,2164802,4329604,8659231,32505856] .lf) [7,992,31744,1015808,1082401,2164802,4329604,8659944,32505856] .lf)) [7,992,31744,1015808,1082401,2164802,4329604,8682760,32505856] (.nd (.nd (.nd .lf [7,992,31744,1015808,1082401,2164802,4329604,9741609,32505856] .lf) [7,992,31744,1015808,1082401,2164802,4329604,10824010,32505856] .lf) [7,992,31744,1015808,1082401,2164802,4329604,12988812,32505856] (.nd (.nd .lf [7,992,31744,1015808,1082401,2164802,4329604,32505856,32776456] .lf) [7,992,31744,1015808,1082401,2164802,4329631,8659208,32505856] .lf))) [7,992,31744,1015808,1082401,2164802,4330468,8659208,32505856] (.nd (.nd (.nd (.nd .lf [7,992,31744,1015808,1082401,2164802,5412005,8659208,32505856] .lf) [7,992,31744,1015808,1082401,2164802,6494406,8659208,32505856] (.nd .lf [7,992,31744,1015808,1082401,2164802,8659208,32505856,32641156] .lf)) [7,992,31744,1015808,1082401,2164831,4329604,8659208,32505856] (.nd (.nd .lf [7,992,31744,1015808,1082401,3247203,4329604,8659208,32505856] .lf) [7,992,31744,1015808,1082401,4329604,8659208,32505856,32573506] .lf)) [7,992,31744,1015808,2164802,4329604,8659208,17318416,32539681] (.nd (.nd (.nd .lf [7,992,31744,1015808,2164802,4329604,8659208,32505856,32539681] .lf) [7,992,31744,1015808,2164802,4329604,8659208,32539681] .lf) [7,992,31744,1015808,2164802,4329604,17318416,32539681] (.nd (.nd .lf [7,992,31744,1015808,2164802,8659208,17318416,32539681] .lf) [7,992,31744,1015808,4329604,8659208,17318416,32539681] .lf)))) [7,992,31744,1082401,2065441,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd (.nd .lf [7,992,31744,1082401,2164802,4329604,8659208,17809936,32505856] .lf) [7,992,31744,1082401,2164802,4329604,8659208,32505856,33521664] (.nd .lf [7,992,31744,1082401,2164802,4329604,17318431,32505856] .lf)) [7,992,31744,1082401,2164802,8659208,17318431,32505856] (.nd (.nd .lf [7,992,31744,1082401,4329604,8659208,17318431,32505856] .lf) [7,992,31744,2065441,2164802,4329604,17318416,32505856] .lf)) [7,992,31744,2065441,2164802,8659208,17318416,32505856] (.nd (.nd (.nd .lf [7,992,31744,2065441,4329604,8659208,17318416,32505856] .lf) [7,992,1015808,1047552,1082401,2164802,4329604,8659208,32505856] .lf) [7,992,1015808,1082401,1113121,2164802,4329604,8659208,32505856] (.nd (.nd .lf [7,992,1015808,1082401,2164802,4329604,8659208,8682760,32505856] .lf) [7,992,1015808,1082401,2164802,4329604,8659208,17333776,32505856] .lf))) [7,992,1015808,1082401,2164802,4329604,8659208,32505856,32537600] (.nd (.nd (.nd (.nd .lf [7,992,1015808,1082401,2164802,4329604,8659231,32505856] .lf) [7,992,1015808,1082401,2164802,4329604,8682760,17318416,32505856] (.nd .lf [7,992,1015808,1082401,2164802,4329604,8682760,32505856] .lf)) [7,992,1015808,1082401,2164802,4329604,17318431,32505856] (.nd (.nd .lf [7,992,1015808,1082401,2164802,4329604,17333776,32505856] .lf) [7,992,1015808,1082401,2164802,8659208,17318431,32505856] .lf)) [7,992,1015808,1082401,2164802,8659231,17318416,32505856] (.nd (.nd (.nd .lf [7,992,1015808,1082401,4329604,8659208,17318431,32505856] .lf) [7,992,1015808,1082401,4329604,8659231,17318416,32505856] .lf) [7,992,1015808,1113121,2164802,8659208,17318416,32505856] (.nd (.nd .lf [7,992,1015808,1113121,4329604,8659208,17318416,32505856] .lf) [7,31744,32736,1015808,1082401,2164802,4329604,8659208,32505856] .lf))))) [7,31744,1015808,1016800,1082401,2164802,4329604,8659208,32505856] (.nd (.nd (.nd (.nd (.nd (.nd .lf [7,31744,1015808,1082401,1083361,2164802,4329604,8659208,32505856] .lf) [7,31744,1015808,1082401,2164802,4329604,4330468,8659208,32505856] (.nd .lf [7,31744,1015808,1082401,2164802,4329604,8659208,8659944,32505856] .lf)) [7,31744,1015808,1082401,2164802,4329604,8659208,17318896,32505856] (.nd (.nd .lf [7,31744,1015808,1082401,2164802,4329604,8659208,32505856,32506848] .lf) [7,31744,1015808,1082401,2164802,4329604,8659231,32505856] .lf)) [7,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856] (.nd (.nd (.nd .lf [7,31744,1015808,1082401,2164802,4329604,8659944,32505856] .lf) [7,31744,1015808,1082401,2164802,4329604,17318431,32505856] .lf) [7,31744,1015808,1082401,2164802,4329604,17318896,32505856] (.nd (.nd .lf [7,31744,1015808,1082401,2164802,4329631,8659208,32505856] .lf) [7,31744,1015808,1082401,2164802,4329631,17318416,32505856] .lf))) [7,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [7,31744,1015808,1082401,2164802,4330468,8659208,32505856] .lf) [7,31744,1015808,1082401,2164802,4330468,17318416,32505856] (.nd .lf [7,31744,1015808,1082401,2164802,8659208,17318431,32505856] .lf)) [7,31744,1015808,1082401,2164802,8659208,17318896,32505856] (.nd (.nd .lf [7,31744,1015808,1082401,2164802,8659231,17318416,32505856] .lf) [7,31744,1015808,1082401,2164802,8659944,17318416,32505856] .lf)) [7,31744,1015808,1082401,4329604,8659208,17318431,32505856] (.nd (.nd (.nd .lf [7,31744,1015808,1082401,4329604,8659231,17318416,32505856] .lf) [7,31744,1015808,1082401,4329631,8659208,17318416,32505856] .lf) [7,31744,1015808,1083361,4329604,8659208,17318416,32505856] (.nd (.nd .lf [8,31,992,31744,1015808,1082401,2164802,4329604,8659208] .lf) [8,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856] .lf)))) [8,31,992,31744,1015808,1082401,2164802,4329604,17318416] (.nd (.nd (.nd (.nd (.nd .lf [8,31,992,31744,1015808,1082401,2164802,8659208,17318416] .lf) [8,31,992,31744,1015808,1082401,4329604,8659208,17318416] (.nd .lf [8,31,992,31744,1015808,2164802,4329604,8659208,17318416] .lf)) [8,31,992,31744,1082401,2164802,4329604,8659208,32505856] (.nd (.nd .lf [8,31,992,31744,1082401,2164802,4329604,17318416,32505856] .lf) [8,31,992,31744,1082401,2164802,8659208,17318416,32505856] .lf)) [8,31,992,31744,1082401,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,31,992,31744,2164802,4329604,8659208,17318416,32505856] .lf) [8,31,992,1015808,1082401,2164802,4329604,8659208,32505856] .lf) [8,31,992,1015808,1082401,2164802,4329604,17318416,32505856] (.nd (.nd .lf [8,31,992,1015808,1082401,2164802,8659208,17318416,32505856] .lf) [8,31,992,1015808,1082401,4329604,8659208,17318416,32505856] .lf))) [8,31,992,1015808,2164802,4329604,8659208,17318416,32505856] (.nd (.nd (.nd (.nd .lf [8,31,31744,1015808,1082401,2164802,4329604,8659208,32505856] .lf) [8,31,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [8,31,31744,1015808,1082401,2164802,8659208,17318416,32505856] (.nd (.nd .lf [8,31,31744,1015808,1082401,4329604,8659208,17318416,32505856] .lf) [8,31,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf)) [8,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856] (.nd (.nd (.nd .lf [8,992,31744,1015808,1082401,2164802,4329604,8659208,32505856] .lf) [8,992,31744,1015808,1082401,2164802,4329604,17318416,32505856] .lf) [8,992,31744,1015808,1082401,2164802,8659208,17318416,32505856] (.nd (.nd .lf [8,992,31744,1015808,1082401,4329604,8659208,17318416,32505856] .lf) [8,992,31744,1015808,2164802,4329604,8659208,17318416,32505856] .lf)))))))))
def P_ := stepOK 0 33004641 PD_ PM_ [] T_
def b0 : List (List Nat × List (Nat × Nat)) := [([3,1015808,6494406,8682760,32539745],[]),([3,1015808,6494406,8682824,32539681],[]),([3,1015872,6494406,8682760,32539681],[]),([3,1047552,2164802,4330468,32801825],[]),([3,1047552,2164802,4592612,32539681],[]),([3,1047552,2426946,4330468,32539681],[]),([3,3115074,17318431,32543777],[]),([3,3119170,17318431,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0 : b0.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b1 : List (List Nat × List (Nat × Nat)) := [([4,31,1082401,17327088,32573506],[]),([4,31,2065441,17318416,32577602],[]),([4,31,2069537,17318416,32573506],[]),([4,31,2164802,17327088,32539681],[]),([4,31,3115074,17318416,32543777],[]),([4,31,3119170,17318416,32539681],[]),([4,64,1015808,6494406,8682760,32539681],[]),([4,992,1015808,2164802,32674981,32832809],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1 : b1.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b2 : List (List Nat × List (Nat × Nat)) := [([4,992,1015808,4329604,32607331,32832809],[]),([4,992,1015808,8682760,32607331,32674981],[]),([4,992,1047552,2164802,4329604,32801825],[]),([4,992,1047552,2164802,4591748,32539681],[]),([4,992,1047552,2426946,4329604,32539681],[]),([4,992,2164802,4329604,32832809,33522721],[]),([4,992,2164802,8682760,32674981,33522721],[]),([4,992,2164802,17326623,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2 : b2.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b3 : List (List Nat × List (Nat × Nat)) := [([4,992,4329604,8682760,32607331,33522721],[]),([4,4096,3115074,17318431,32539681],[]),([4,8223,1082401,17318896,32573506],[]),([4,8223,2164802,17318896,32539681],[]),([4,9184,2164802,17318431,32539681],[]),([4,31744,1015808,2164802,4330468,32801825],[]),([4,31744,1015808,2164802,4592612,32539681],[]),([4,31744,1015808,2426946,4330468,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3 : b3.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b4 : List (List Nat × List (Nat × Nat)) := [([4,31744,1015808,4329604,32607331,32810985],[]),([4,31744,1015808,4330468,32607331,32810281],[]),([4,31744,1015808,6494406,8659208,32539745],[]),([4,31744,1015808,6494406,8659272,32539681],[]),([4,31744,1015808,8659208,32607331,32675813],[]),([4,31744,1015808,8659944,32607331,32674981],[]),([4,31744,1015872,6494406,8659208,32539681],[]),([4,31744,2164802,4329604,32810985,33522721],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4 : b4.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b5 : List (List Nat × List (Nat × Nat)) := [([4,31744,2164802,4330468,32810281,33522721],[]),([4,31744,2164802,8659208,32675813,33522721],[]),([4,31744,2164802,8659944,32674981,33522721],[]),([4,31744,4329604,8659944,32607331,33522721],[]),([4,31744,4330468,8659208,32607331,33522721],[]),([4,31808,1015808,6494406,8659208,32539681],[]),([4,262144,1047552,2164802,4330468,32539681],[]),([4,263136,1047552,2164802,4329604,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5 : b5.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b6 : List (List Nat × List (Nat × Nat)) := [([4,293888,1015808,2164802,4330468,32539681],[]),([4,1015808,1082401,6494406,8682760,32505920],[]),([4,1015808,1082401,6494406,8682824,32505856],[]),([4,1015808,1082465,6494406,8682760,32505856],[]),([4,1015808,2164802,4329604,8682760,32539745],[]),([4,1015808,2164802,4329604,8682824,32539681],[]),([4,1015808,2164802,4329668,8682760,32539681],[]),([4,1015808,2164802,8659208,32570401,32675813],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6 : b6.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b7 : List (List Nat × List (Nat × Nat)) := [([4,1015808,2164802,8659944,32570401,32674981],[]),([4,1015808,2164802,17318431,32543777],[]),([4,1015808,2168898,17318431,32539681],[]),([4,1015808,4329604,8659944,32570401,32607331],[]),([4,1015808,4329604,8682760,32540641,32607331],[]),([4,1015808,4330468,8659208,32570401,32607331],[]),([4,1015808,8659208,17318559,32539681],[]),([4,1015808,8659231,17318544,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7 : b7.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b8 : List (List Nat × List (Nat × Nat)) := [([4,1015808,8659336,17318431,32539681],[]),([4,1015808,8659359,17318416,32539681],[]),([4,1015872,1082401,6494406,8682760,32505856],[]),([4,1015872,2164802,4329604,8682760,32539681],[]),([4,1019904,2164802,17318431,32539681],[]),([4,1047552,1082401,2164802,4330468,32768000],[]),([4,1047552,1082401,2164802,4592612,32505856],[]),([4,1047552,1082401,2426946,4330468,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8 : b8.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b9 : List (List Nat × List (Nat × Nat)) := [([4,1047552,1344545,2164802,4330468,32505856],[]),([4,1082401,3115074,17318431,32509952],[]),([4,1082401,3119170,17318431,32505856],[]),([4,1086497,3115074,17318431,32505856],[]),([4,2065441,8659231,17318544,32505856],[]),([4,2065441,8659359,17318416,32505856],[]),([4,2164802,4329604,8659944,32570401,33522721],[]),([4,2164802,4329604,8682760,32540641,33522721],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9 : b9.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b10 : List (List Nat × List (Nat × Nat)) := [([4,2164802,4330468,8659208,32570401,33522721],[]),([4,3115074,8659944,17318431,32539681],[]),([5,31,992,1082401,2164802,32903300],[]),([5,31,992,1082401,2426946,32641156],[]),([5,31,992,1082401,4329604,32835650],[]),([5,31,992,1082401,4591748,32573506],[]),([5,31,992,1082401,17326608,32573506],[]),([5,31,992,1344545,2164802,32641156],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10 : b10.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b11 : List (List Nat × List (Nat × Nat)) := [([5,31,992,1344545,4329604,32573506],[]),([5,31,992,2164802,4329604,32801825],[]),([5,31,992,2164802,4591748,32539681],[]),([5,31,992,2164802,17326608,32539681],[]),([5,31,992,2426946,4329604,32539681],[]),([5,31,4096,2065441,17318416,32573506],[]),([5,31,4096,3115074,17318416,32539681],[]),([5,31,8192,1082401,17318896,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11 : b11.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b12 : List (List Nat × List (Nat × Nat)) := [([5,31,8192,2164802,17318896,32539681],[]),([5,31,9184,1082401,17318416,32573506],[]),([5,31,9184,2164802,17318416,32539681],[]),([5,31,1015808,1082401,17318416,32577602],[]),([5,31,1015808,1086497,17318416,32573506],[]),([5,31,1015808,2164802,17318416,32543777],[]),([5,31,1015808,2168898,17318416,32539681],[]),([5,31,1015808,8659208,17318544,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12 : b12.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b13 : List (List Nat × List (Nat × Nat)) := [([5,31,1015808,8659336,17318416,32539681],[]),([5,31,1019904,1082401,17318416,32573506],[]),([5,31,1019904,2164802,17318416,32539681],[]),([5,31,1082401,2164802,17327088,32505856],[]),([5,31,1082401,3115074,17318416,32509952],[]),([5,31,1082401,3119170,17318416,32505856],[]),([5,31,1082401,5214340,17318896,32573506],[]),([5,31,1086497,3115074,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13 : b13.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b14 : List (List Nat × List (Nat × Nat)) := [([5,31,2065441,2164802,17318416,32509952],[]),([5,31,2065441,2168898,17318416,32505856],[]),([5,31,2065441,8659208,17318544,32505856],[]),([5,31,2065441,8659336,17318416,32505856],[]),([5,31,2065441,8659944,17318416,32573506],[]),([5,31,2069537,2164802,17318416,32505856],[]),([5,31,2164802,5214340,17318896,32539681],[]),([5,31,3115074,8659944,17318416,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14 : b14.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b15 : List (List Nat × List (Nat × Nat)) := [([5,64,31744,1015808,6494406,8659208,32539681],[]),([5,64,1015808,1082401,6494406,8682760,32505856],[]),([5,64,1015808,2164802,4329604,8682760,32539681],[]),([5,128,1015808,8659208,17318431,32539681],[]),([5,128,1015808,8659231,17318416,32539681],[]),([5,128,2065441,8659231,17318416,32505856],[]),([5,159,1015808,8659208,17318416,32539681],[]),([5,159,2065441,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15 : b15.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b16 : List (List Nat × List (Nat × Nat)) := [([5,992,8192,2164802,17318431,32539681],[]),([5,992,8223,1082401,17318416,32573506],[]),([5,992,8223,2164802,17318416,32539681],[]),([5,992,31744,1015808,2164802,4329604,32801825],[]),([5,992,31744,1015808,2164802,4591748,32539681],[]),([5,992,31744,1015808,2164802,32674981,32810281],[]),([5,992,31744,1015808,2426946,4329604,32539681],[]),([5,992,31744,1015808,4329604,32607331,32810281],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16 : b16.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b17 : List (List Nat × List (Nat × Nat)) := [([5,992,31744,1015808,6494406,10824010,32539681],[]),([5,992,31744,1015808,8659208,32607331,32674981],[]),([5,992,31744,2164802,4329604,32810281,33522721],[]),([5,992,31744,2164802,8659208,32674981,33522721],[]),([5,992,31744,4329604,8659208,32607331,33522721],[]),([5,992,262144,1047552,2164802,4329604,32539681],[]),([5,992,293888,1015808,2164802,4329604,32539681],[]),([5,992,1015808,1082401,2164802,32641156,32800008],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17 : b17.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b18 : List (List Nat × List (Nat × Nat)) := [([5,992,1015808,1082401,4329604,32573506,32800008],[]),([5,992,1015808,1082401,8682760,32573506,32641156],[]),([5,992,1015808,2164802,4329604,8682760,32539681],[]),([5,992,1015808,2164802,4329604,9764137,32539681],[]),([5,992,1015808,2164802,4329604,32539681,32800008],[]),([5,992,1015808,2164802,4329604,32539681,32832809],[]),([5,992,1015808,2164802,5412005,8682760,32539681],[]),([5,992,1015808,2164802,5412005,9764137,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18 : b18.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b19 : List (List Nat × List (Nat × Nat)) := [([5,992,1015808,2164802,6494406,8682760,32539681],[]),([5,992,1015808,2164802,8659208,32570401,32674981],[]),([5,992,1015808,2164802,8682760,32539681,32641156],[]),([5,992,1015808,2164802,8682760,32539681,32674981],[]),([5,992,1015808,3247203,4329604,8682760,32539681],[]),([5,992,1015808,3247203,4329604,9764137,32505856],[]),([5,992,1015808,3247203,5412005,8682760,32505856],[]),([5,992,1015808,4329604,8659208,32570401,32607331],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19 : b19.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b20 : List (List Nat × List (Nat × Nat)) := [([5,992,1015808,4329604,8682760,32539681,32573506],[]),([5,992,1015808,4329604,8682760,32539681,32607331],[]),([5,992,1047552,1082401,2164802,4329604,32768000],[]),([5,992,1047552,1082401,2164802,4591748,32505856],[]),([5,992,1047552,1082401,2426946,4329604,32505856],[]),([5,992,1047552,1344545,2164802,4329604,32505856],[]),([5,992,1082401,2164802,4329604,32800008,33521664],[]),([5,992,1082401,2164802,8682760,32641156,33521664],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20 : b20.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b21 : List (List Nat × List (Nat × Nat)) := [([5,992,1082401,2164802,17326623,32505856],[]),([5,992,1082401,4329604,8682760,32573506,33521664],[]),([5,992,2065441,2164802,4329604,8682760,32539681],[]),([5,992,2065441,2164802,4329604,9764137,32505856],[]),([5,992,2065441,2164802,5412005,8682760,32505856],[]),([5,992,2065441,3247203,4329604,8682760,32505856],[]),([5,992,2164802,4329604,8659208,32570401,33522721],[]),([5,992,2164802,4329604,8682760,32539681,33521664],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21 : b21.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b22 : List (List Nat × List (Nat × Nat)) := [([5,992,2164802,4329604,8682760,32539681,33522721],[]),([5,992,2164802,5214340,17318431,32539681],[]),([5,992,2194498,8659208,17318431,32539681],[]),([5,992,3115074,4329604,17318431,32539681],[]),([5,992,3115074,8659208,17318431,32539681],[]),([5,992,4357252,8659208,17318431,32539681],[]),([5,992,5214340,8659208,17318431,32539681],[]),([5,4096,1015808,2164802,17318431,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22 : b22.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b23 : List (List Nat × List (Nat × Nat)) := [([5,4096,1082401,3115074,17318431,32505856],[]),([5,8223,1082401,2164802,17318896,32505856],[]),([5,9184,1082401,2164802,17318431,32505856],[]),([5,31744,262144,1015808,2164802,4330468,32539681],[]),([5,31744,263136,1015808,2164802,4329604,32539681],[]),([5,31744,1015808,1082401,2164802,4330468,32768000],[]),([5,31744,1015808,1082401,2164802,4592612,32505856],[]),([5,31744,1015808,1082401,2426946,4330468,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p23 : b23.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b24 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,1082401,4329604,32573506,32777192],[]),([5,31744,1015808,1082401,4330468,32573506,32776456],[]),([5,31744,1015808,1082401,6494406,8659208,32505920],[]),([5,31744,1015808,1082401,6494406,8659272,32505856],[]),([5,31744,1015808,1082401,8659208,32573506,32642020],[]),([5,31744,1015808,1082401,8659944,32573506,32641156],[]),([5,31744,1015808,1082465,6494406,8659208,32505856],[]),([5,31744,1015808,1344545,2164802,4330468,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p24 : b24.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b25 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,2164802,4329604,8659208,32539745],[]),([5,31744,1015808,2164802,4329604,8659272,32539681],[]),([5,31744,1015808,2164802,4329604,8659944,32539681],[]),([5,31744,1015808,2164802,4329604,8683496,32539681],[]),([5,31744,1015808,2164802,4329604,9742313,32539681],[]),([5,31744,1015808,2164802,4329604,12989420,32539681],[]),([5,31744,1015808,2164802,4329604,32539681,32777192],[]),([5,31744,1015808,2164802,4329604,32539681,32810985],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25 : b25.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b26 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,2164802,4329631,8659944,32539681],[]),([5,31744,1015808,2164802,4329668,8659208,32539681],[]),([5,31744,1015808,2164802,4330468,8659208,32539681],[]),([5,31744,1015808,2164802,4330468,8659231,32539681],[]),([5,31744,1015808,2164802,4330468,8659944,32539681],[]),([5,31744,1015808,2164802,4330468,8682760,32539681],[]),([5,31744,1015808,2164802,4330468,9741609,32539681],[]),([5,31744,1015808,2164802,4330468,10824010,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26 : b26.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b27 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,2164802,4330468,12988812,32539681],[]),([5,31744,1015808,2164802,4330468,12989420,32539681],[]),([5,31744,1015808,2164802,4330468,32539681,32776456],[]),([5,31744,1015808,2164802,4330468,32539681,32810281],[]),([5,31744,1015808,2164802,5412005,8659944,32539681],[]),([5,31744,1015808,2164802,5412837,8659208,32539681],[]),([5,31744,1015808,2164802,6494406,8659944,32539681],[]),([5,31744,1015808,2164802,8659208,32539681,32642020],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27 : b27.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b28 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,2164802,8659208,32539681,32675813],[]),([5,31744,1015808,2164802,8659944,32539681,32641156],[]),([5,31744,1015808,2164802,8659944,32539681,32674981],[]),([5,31744,1015808,3247203,4329604,8659944,32539681],[]),([5,31744,1015808,3247203,4329604,9742313,32505856],[]),([5,31744,1015808,3247203,4330468,8659208,32539681],[]),([5,31744,1015808,3247203,4330468,9741609,32505856],[]),([5,31744,1015808,3247203,5412005,8659944,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28 : b28.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b29 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015808,3247203,5412837,8659208,32505856],[]),([5,31744,1015808,4329604,8659208,32540641,32607331],[]),([5,31744,1015808,4329604,8659944,32539681,32573506],[]),([5,31744,1015808,4329604,8659944,32539681,32607331],[]),([5,31744,1015808,4330468,8659208,32539681,32573506],[]),([5,31744,1015808,4330468,8659208,32539681,32607331],[]),([5,31744,1015808,8659208,17318416,32539745],[]),([5,31744,1015872,1082401,6494406,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29 : b29.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b30 : List (List Nat × List (Nat × Nat)) := [([5,31744,1015872,2164802,4329604,8659208,32539681],[]),([5,31744,1015872,8659208,17318416,32539681],[]),([5,31744,1082401,2164802,4329604,32777192,33521664],[]),([5,31744,1082401,2164802,4330468,32776456,33521664],[]),([5,31744,1082401,2164802,8659208,32642020,33521664],[]),([5,31744,1082401,2164802,8659944,32641156,33521664],[]),([5,31744,1082401,4329604,8659944,32573506,33521664],[]),([5,31744,1082401,4330468,8659208,32573506,33521664],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30 : b30.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b31 : List (List Nat × List (Nat × Nat)) := [([5,31744,2065441,2164802,4329604,8659944,32539681],[]),([5,31744,2065441,2164802,4329604,9742313,32505856],[]),([5,31744,2065441,2164802,4330468,8659208,32539681],[]),([5,31744,2065441,2164802,4330468,9741609,32505856],[]),([5,31744,2065441,2164802,5412005,8659944,32505856],[]),([5,31744,2065441,2164802,5412837,8659208,32505856],[]),([5,31744,2065441,3247203,4329604,8659944,32505856],[]),([5,31744,2065441,3247203,4330468,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31 : b31.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b32 : List (List Nat × List (Nat × Nat)) := [([5,31744,2065441,8659208,17318416,32505920],[]),([5,31744,2065505,8659208,17318416,32505856],[]),([5,31744,2164802,4329604,8659208,32540641,33522721],[]),([5,31744,2164802,4329604,8659944,32539681,33521664],[]),([5,31744,2164802,4329604,8659944,32539681,33522721],[]),([5,31744,2164802,4330468,8659208,32539681,33521664],[]),([5,31744,2164802,4330468,8659208,32539681,33522721],[]),([5,31744,3115074,4329604,17318431,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p32 : b32.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b33 : List (List Nat × List (Nat × Nat)) := [([5,31744,3115074,8659208,17318431,32539681],[]),([5,31808,1015808,1082401,6494406,8659208,32505856],[]),([5,31808,1015808,2164802,4329604,8659208,32539681],[]),([5,31808,1015808,8659208,17318416,32539681],[]),([5,31808,2065441,8659208,17318416,32505856],[]),([5,32736,1015808,2164802,4329604,8682760,32539681],[]),([5,262144,1047552,1082401,2164802,4330468,32505856],[]),([5,263136,1047552,1082401,2164802,4329604,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p33 : b33.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b34 : List (List Nat × List (Nat × Nat)) := [([5,293888,1015808,1082401,2164802,4330468,32505856],[]),([5,1015808,1016800,2164802,4329604,8682760,32539681],[]),([5,1015808,1047552,2164802,4329604,8659944,32539681],[]),([5,1015808,1047552,2164802,4330468,8659208,32539681],[]),([5,1015808,1082401,2164802,4329604,8682760,32505920],[]),([5,1015808,1082401,2164802,4329604,8682824,32505856],[]),([5,1015808,1082401,2164802,4329668,8682760,32505856],[]),([5,1015808,1082401,2164802,8659208,32537600,32642020],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p34 : b34.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b35 : List (List Nat × List (Nat × Nat)) := [([5,1015808,1082401,2164802,8659944,32537600,32641156],[]),([5,1015808,1082401,2164802,17318431,32509952],[]),([5,1015808,1082401,2168898,17318431,32505856],[]),([5,1015808,1082401,4329604,8659944,32537600,32573506],[]),([5,1015808,1082401,4329604,8682760,32506848,32573506],[]),([5,1015808,1082401,4330468,8659208,32537600,32573506],[]),([5,1015808,1082401,8659208,17318559,32505856],[]),([5,1015808,1082401,8659231,17318544,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p35 : b35.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b36 : List (List Nat × List (Nat × Nat)) := [([5,1015808,1082401,8659336,17318431,32505856],[]),([5,1015808,1082401,8659359,17318416,32505856],[]),([5,1015808,1082465,2164802,4329604,8682760,32505856],[]),([5,1015808,1083361,2164802,4329604,8682760,32539681],[]),([5,1015808,1083361,3247203,4329604,8682760,32505856],[]),([5,1015808,1086497,2164802,17318431,32505856],[]),([5,1015808,1113121,2164802,4329604,8659944,32539681],[]),([5,1015808,1113121,2164802,4330468,8659208,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p36 : b36.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b37 : List (List Nat × List (Nat × Nat)) := [([5,1015808,1113121,2164802,5412005,8659944,32505856],[]),([5,1015808,1113121,2164802,5412837,8659208,32505856],[]),([5,1015808,1113121,3247203,4329604,8659944,32505856],[]),([5,1015808,1113121,3247203,4330468,8659208,32505856],[]),([5,1015808,1113121,8659208,17318416,32505920],[]),([5,1015808,1113185,8659208,17318416,32505856],[]),([5,1015808,2164802,4329604,4330468,8682760,32539681],[]),([5,1015808,2164802,4329604,8659208,32540641,32570401],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p37 : b37.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b38 : List (List Nat × List (Nat × Nat)) := [([5,1015808,2164802,4329604,8659944,8682760,32539681],[]),([5,1015808,2164802,4329604,8659944,17333776,32539681],[]),([5,1015808,2164802,4329604,8659944,32537600,32539681],[]),([5,1015808,2164802,4329604,8659944,32539681,32570401],[]),([5,1015808,2164802,4329604,8682760,8683496,32539681],[]),([5,1015808,2164802,4329604,8682760,17318896,32539681],[]),([5,1015808,2164802,4329604,8682760,32506848,32539681],[]),([5,1015808,2164802,4329604,8682760,32539681,32540641],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p38 : b38.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b39 : List (List Nat × List (Nat × Nat)) := [([5,1015808,2164802,4330468,8659208,32537600,32539681],[]),([5,1015808,2164802,4330468,8659208,32539681,32570401],[]),([5,1015808,2164802,8659231,17318896,32539681],[]),([5,1015808,2164802,8659944,17318431,32539681],[]),([5,1015808,2194498,8659208,17318431,32539681],[]),([5,1015808,2194498,8659231,17318416,32539681],[]),([5,1015872,1082401,2164802,4329604,8682760,32505856],[]),([5,1015872,1113121,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p39 : b39.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b40 : List (List Nat × List (Nat × Nat)) := [([5,1016800,1047552,2164802,4329604,8659208,32539681],[]),([5,1019904,1082401,2164802,17318431,32505856],[]),([5,1082401,2164802,4329604,8659944,32537600,33521664],[]),([5,1082401,2164802,4329604,8682760,32506848,33521664],[]),([5,1082401,2164802,4330468,8659208,32537600,33521664],[]),([5,1082401,3115074,8659944,17318431,32505856],[]),([5,1083361,2065441,2164802,4329604,8682760,32505856],[]),([5,1113121,2065441,2164802,4329604,8659944,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p40 : b40.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b41 : List (List Nat × List (Nat × Nat)) := [([5,1113121,2065441,2164802,4330468,8659208,32505856],[]),([5,2065441,2194498,8659231,17318416,32505856],[]),([6,31,128,1015808,8659208,17318416,32539681],[]),([6,31,128,2065441,8659208,17318416,32505856],[]),([6,31,992,8192,1082401,17318416,32573506],[]),([6,31,992,8192,2164802,17318416,32539681],[]),([6,31,992,262144,1082401,2164802,32641156],[]),([6,31,992,262144,1082401,4329604,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p41 : b41.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b42 : List (List Nat × List (Nat × Nat)) := [([6,31,992,262144,2164802,4329604,32539681],[]),([6,31,992,556032,1082401,2164802,4329604],[]),([6,31,992,1015808,2164802,4329604,8682760,32539681],[]),([6,31,992,1082401,2164802,4329604,32768000],[]),([6,31,992,1082401,2164802,4591748,32505856],[]),([6,31,992,1082401,2164802,17326608,32505856],[]),([6,31,992,1082401,2164802,17333776,32641156],[]),([6,31,992,1082401,2426946,4329604,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p42 : b42.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b43 : List (List Nat × List (Nat × Nat)) := [([6,31,992,1082401,3115074,17318416,32641156],[]),([6,31,992,1082401,4329604,17333776,32573506],[]),([6,31,992,1082401,5214340,17318416,32573506],[]),([6,31,992,1113121,3115074,8659208,17318416],[]),([6,31,992,1113121,5214340,8659208,17318416],[]),([6,31,992,1113121,8659208,17318416,32573506],[]),([6,31,992,1113121,8659208,17318416,32641156],[]),([6,31,992,1344545,2164802,4329604,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p43 : b43.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b44 : List (List Nat × List (Nat × Nat)) := [([6,31,992,2065441,2164802,17318416,32641156],[]),([6,31,992,2065441,2194498,8659208,17318416],[]),([6,31,992,2065441,4329604,17318416,32573506],[]),([6,31,992,2065441,4357252,8659208,17318416],[]),([6,31,992,2065441,8659208,17318416,32573506],[]),([6,31,992,2065441,8659208,17318416,32641156],[]),([6,31,992,2164802,4329604,17333776,32539681],[]),([6,31,992,2164802,5214340,17318416,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p44 : b44.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b45 : List (List Nat × List (Nat × Nat)) := [([6,31,992,2194498,5214340,8659208,17318416],[]),([6,31,992,2194498,8659208,17318416,32539681],[]),([6,31,992,2194498,8659208,17318416,32641156],[]),([6,31,992,3115074,4329604,17318416,32539681],[]),([6,31,992,3115074,4357252,8659208,17318416],[]),([6,31,992,3115074,8659208,17318416,32539681],[]),([6,31,992,3115074,8659208,17318416,32641156],[]),([6,31,992,4357252,8659208,17318416,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p45 : b45.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b46 : List (List Nat × List (Nat × Nat)) := [([6,31,992,4357252,8659208,17318416,32573506],[]),([6,31,992,5214340,8659208,17318416,32539681],[]),([6,31,992,5214340,8659208,17318416,32573506],[]),([6,31,4096,1015808,1082401,17318416,32573506],[]),([6,31,4096,1015808,2164802,17318416,32539681],[]),([6,31,4096,1082401,3115074,17318416,32505856],[]),([6,31,4096,2065441,2164802,17318416,32505856],[]),([6,31,8192,1082401,2164802,17318896,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p46 : b46.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b47 : List (List Nat × List (Nat × Nat)) := [([6,31,9184,1082401,2164802,17318416,32505856],[]),([6,31,31744,525280,1082401,2164802,4329604],[]),([6,31,31744,1015808,2164802,4329604,8659944,32539681],[]),([6,31,31744,1015808,2164802,4330468,8659208,32539681],[]),([6,31,31744,1082401,4329604,17318896,32573506],[]),([6,31,31744,1082401,8659208,17318896,32573506],[]),([6,31,31744,2065441,4329604,17318416,32573506],[]),([6,31,31744,2065441,8659208,17318416,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p47 : b47.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b48 : List (List Nat × List (Nat × Nat)) := [([6,31,31744,2164802,4329604,17318896,32539681],[]),([6,31,31744,2164802,8659208,17318896,32539681],[]),([6,31,31744,3115074,4329604,17318416,32539681],[]),([6,31,31744,3115074,8659208,17318416,32539681],[]),([6,31,1015808,1082401,2164802,17318416,32509952],[]),([6,31,1015808,1082401,2168898,17318416,32505856],[]),([6,31,1015808,1082401,4329604,8659944,32573506],[]),([6,31,1015808,1082401,4329604,8682760,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p48 : b48.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b49 : List (List Nat × List (Nat × Nat)) := [([6,31,1015808,1082401,4329604,17318896,32573506],[]),([6,31,1015808,1082401,4329604,17333776,32573506],[]),([6,31,1015808,1082401,8659208,17318544,32505856],[]),([6,31,1015808,1082401,8659208,17318896,32573506],[]),([6,31,1015808,1082401,8659336,17318416,32505856],[]),([6,31,1015808,1082401,8659944,17318416,32573506],[]),([6,31,1015808,1086497,2164802,17318416,32505856],[]),([6,31,1015808,1113121,8659208,17318416,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p49 : b49.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b50 : List (List Nat × List (Nat × Nat)) := [([6,31,1015808,2164802,4329604,8659944,32539681],[]),([6,31,1015808,2164802,4329604,8682760,32539681],[]),([6,31,1015808,2164802,4329604,17318896,32539681],[]),([6,31,1015808,2164802,4329604,17333776,32539681],[]),([6,31,1015808,2164802,8659208,17318896,32539681],[]),([6,31,1015808,2164802,8659944,17318416,32539681],[]),([6,31,1015808,2194498,8659208,17318416,32539681],[]),([6,31,1019904,1082401,2164802,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p50 : b50.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b51 : List (List Nat × List (Nat × Nat)) := [([6,31,1082401,2164802,5214340,17318896,32505856],[]),([6,31,1082401,3115074,8659944,17318416,32505856],[]),([6,31,1113121,3115074,8659208,17318416,32505856],[]),([6,31,2065441,2164802,8659944,17318416,32505856],[]),([6,31,2065441,2194498,8659208,17318416,32505856],[]),([6,64,31744,1015808,1082401,6494406,8659208,32505856],[]),([6,64,31744,1015808,2164802,4329604,8659208,32539681],[]),([6,64,31744,1015808,8659208,17318416,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p51 : b51.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b52 : List (List Nat × List (Nat × Nat)) := [([6,64,31744,2065441,8659208,17318416,32505856],[]),([6,64,1015808,1082401,2164802,4329604,8682760,32505856],[]),([6,64,1015808,1113121,8659208,17318416,32505856],[]),([6,128,1015808,1082401,8659208,17318431,32505856],[]),([6,128,1015808,1082401,8659231,17318416,32505856],[]),([6,159,1015808,1082401,8659208,17318416,32505856],[]),([6,992,8192,1082401,2164802,17318431,32505856],[]),([6,992,8223,1082401,2164802,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p52 : b52.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b53 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,262144,1015808,2164802,4329604,32539681],[]),([6,992,31744,524319,1082401,2164802,4329604],[]),([6,992,31744,1015808,1082401,2164802,4329604,32768000],[]),([6,992,31744,1015808,1082401,2164802,4591748,32505856],[]),([6,992,31744,1015808,1082401,2164802,32641156,32776456],[]),([6,992,31744,1015808,1082401,2426946,4329604,32505856],[]),([6,992,31744,1015808,1082401,4329604,32573506,32776456],[]),([6,992,31744,1015808,1082401,6494406,10824010,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p53 : b53.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b54 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,1015808,1082401,8659208,32573506,32641156],[]),([6,992,31744,1015808,1344545,2164802,4329604,32505856],[]),([6,992,31744,1015808,2164802,4329604,8659208,32539681],[]),([6,992,31744,1015808,2164802,4329604,8659231,32539681],[]),([6,992,31744,1015808,2164802,4329604,8659944,32539681],[]),([6,992,31744,1015808,2164802,4329604,8682760,32539681],[]),([6,992,31744,1015808,2164802,4329604,9741609,32539681],[]),([6,992,31744,1015808,2164802,4329604,10824010,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p54 : b54.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b55 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,1015808,2164802,4329604,12988812,32539681],[]),([6,992,31744,1015808,2164802,4329604,32539681,32776456],[]),([6,992,31744,1015808,2164802,4329604,32539681,32810281],[]),([6,992,31744,1015808,2164802,4329631,8659208,32539681],[]),([6,992,31744,1015808,2164802,4330468,8659208,32539681],[]),([6,992,31744,1015808,2164802,5412005,8659208,32539681],[]),([6,992,31744,1015808,2164802,5412005,9741609,32505856],[]),([6,992,31744,1015808,2164802,6494406,8659208,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p55 : b55.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b56 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,1015808,2164802,8659208,32539681,32641156],[]),([6,992,31744,1015808,2164802,8659208,32539681,32674981],[]),([6,992,31744,1015808,2164831,4329604,8659208,32539681],[]),([6,992,31744,1015808,3247203,4329604,8659208,32539681],[]),([6,992,31744,1015808,3247203,4329604,9741609,32505856],[]),([6,992,31744,1015808,3247203,5412005,8659208,32505856],[]),([6,992,31744,1015808,4329604,8659208,32539681,32573506],[]),([6,992,31744,1015808,4329604,8659208,32539681,32607331],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p56 : b56.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b57 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,1082401,2164802,4329604,32776456,33521664],[]),([6,992,31744,1082401,2164802,8659208,32641156,33521664],[]),([6,992,31744,1082401,4329604,8659208,32573506,33521664],[]),([6,992,31744,2065441,2164802,4329604,8659208,32539681],[]),([6,992,31744,2065441,2164802,4329604,9741609,32505856],[]),([6,992,31744,2065441,2164802,5412005,8659208,32505856],[]),([6,992,31744,2065441,3247203,4329604,8659208,32505856],[]),([6,992,31744,2164802,4329604,8659208,17809936,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p57 : b57.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b58 : List (List Nat × List (Nat × Nat)) := [([6,992,31744,2164802,4329604,8659208,32539681,33521664],[]),([6,992,31744,2164802,4329604,8659208,32539681,33522721],[]),([6,992,31744,2164802,4329604,17318431,32539681],[]),([6,992,31744,2164802,8659208,17318431,32539681],[]),([6,992,31744,4329604,8659208,17318431,32539681],[]),([6,992,262144,1047552,1082401,2164802,4329604,32505856],[]),([6,992,293888,1015808,1082401,2164802,4329604,32505856],[]),([6,992,1015808,1047552,2164802,4329604,8659208,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p58 : b58.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b59 : List (List Nat × List (Nat × Nat)) := [([6,992,1015808,1082401,2164802,4329604,8682760,32505856],[]),([6,992,1015808,1082401,2164802,4329604,8682760,32539681],[]),([6,992,1015808,1082401,2164802,4329604,9764137,32505856],[]),([6,992,1015808,1082401,2164802,4329604,32505856,32800008],[]),([6,992,1015808,1082401,2164802,5412005,8682760,32505856],[]),([6,992,1015808,1082401,2164802,6494406,8682760,32505856],[]),([6,992,1015808,1082401,2164802,8659208,32537600,32641156],[]),([6,992,1015808,1082401,2164802,8682760,32505856,32641156],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p59 : b59.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b60 : List (List Nat × List (Nat × Nat)) := [([6,992,1015808,1082401,3247203,4329604,8682760,32505856],[]),([6,992,1015808,1082401,4329604,8659208,32537600,32573506],[]),([6,992,1015808,1082401,4329604,8682760,32505856,32573506],[]),([6,992,1015808,1113121,2164802,4329604,8659208,32539681],[]),([6,992,1015808,1113121,2164802,5412005,8659208,32505856],[]),([6,992,1015808,1113121,3247203,4329604,8659208,32505856],[]),([6,992,1015808,2164802,4329604,8659208,8682760,32539681],[]),([6,992,1015808,2164802,4329604,8659208,17333776,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p60 : b60.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b61 : List (List Nat × List (Nat × Nat)) := [([6,992,1015808,2164802,4329604,8659208,32537600,32539681],[]),([6,992,1015808,2164802,4329604,8659208,32539681,32570401],[]),([6,992,1015808,2164802,4329604,8659231,32539681],[]),([6,992,1015808,2164802,4329604,8682760,17318416,32539681],[]),([6,992,1015808,2164802,4329604,8682760,32505856,32539681],[]),([6,992,1015808,2164802,4329604,8682760,32539681],[]),([6,992,1015808,2164802,4329604,17318431,32539681],[]),([6,992,1015808,2164802,4329604,17333776,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p61 : b61.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b62 : List (List Nat × List (Nat × Nat)) := [([6,992,1015808,2164802,8659208,17318431,32539681],[]),([6,992,1015808,2164802,8659231,17318416,32539681],[]),([6,992,1015808,4329604,8659208,17318431,32539681],[]),([6,992,1015808,4329604,8659231,17318416,32539681],[]),([6,992,1082401,2065441,2164802,4329604,8682760,32505856],[]),([6,992,1082401,2164802,4329604,8659208,32537600,33521664],[]),([6,992,1082401,2164802,4329604,8682760,32505856,33521664],[]),([6,992,1082401,2164802,5214340,17318431,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p62 : b62.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b63 : List (List Nat × List (Nat × Nat)) := [([6,992,1082401,2194498,8659208,17318431,32505856],[]),([6,992,1082401,3115074,4329604,17318431,32505856],[]),([6,992,1082401,3115074,8659208,17318431,32505856],[]),([6,992,1082401,4357252,8659208,17318431,32505856],[]),([6,992,1082401,5214340,8659208,17318431,32505856],[]),([6,992,1113121,2065441,2164802,4329604,8659208,32505856],[]),([6,992,2065441,2164802,8659231,17318416,32505856],[]),([6,992,2065441,4329604,8659231,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p63 : b63.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b64 : List (List Nat × List (Nat × Nat)) := [([6,4096,1015808,1082401,2164802,17318431,32505856],[]),([6,31744,32736,1015808,2164802,4329604,8659208,32539681],[]),([6,31744,262144,1015808,1082401,2164802,4330468,32505856],[]),([6,31744,263136,1015808,1082401,2164802,4329604,32505856],[]),([6,31744,1015808,1016800,2164802,4329604,8659208,32539681],[]),([6,31744,1015808,1082401,2164802,4329604,8659208,32505920],[]),([6,31744,1015808,1082401,2164802,4329604,8659272,32505856],[]),([6,31744,1015808,1082401,2164802,4329604,8659944,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p64 : b64.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b65 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,1082401,2164802,4329604,8659944,32539681],[]),([6,31744,1015808,1082401,2164802,4329604,8683496,32505856],[]),([6,31744,1015808,1082401,2164802,4329604,9742313,32505856],[]),([6,31744,1015808,1082401,2164802,4329604,12989420,32505856],[]),([6,31744,1015808,1082401,2164802,4329604,32505856,32777192],[]),([6,31744,1015808,1082401,2164802,4329631,8659944,32505856],[]),([6,31744,1015808,1082401,2164802,4329668,8659208,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p65 : b65.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b66 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,1082401,2164802,4330468,8659208,32539681],[]),([6,31744,1015808,1082401,2164802,4330468,8659231,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,8659944,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,8682760,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,9741609,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,10824010,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,12988812,32505856],[]),([6,31744,1015808,1082401,2164802,4330468,12989420,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p66 : b66.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b67 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,1082401,2164802,4330468,32505856,32776456],[]),([6,31744,1015808,1082401,2164802,5412005,8659944,32505856],[]),([6,31744,1015808,1082401,2164802,5412837,8659208,32505856],[]),([6,31744,1015808,1082401,2164802,6494406,8659944,32505856],[]),([6,31744,1015808,1082401,2164802,8659208,32505856,32642020],[]),([6,31744,1015808,1082401,2164802,8659944,32505856,32641156],[]),([6,31744,1015808,1082401,3247203,4329604,8659944,32505856],[]),([6,31744,1015808,1082401,3247203,4330468,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p67 : b67.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b68 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,1082401,4329604,8659208,32506848,32573506],[]),([6,31744,1015808,1082401,4329604,8659944,32505856,32573506],[]),([6,31744,1015808,1082401,4330468,8659208,32505856,32573506],[]),([6,31744,1015808,1082401,8659208,17318416,32505920],[]),([6,31744,1015808,1082465,2164802,4329604,8659208,32505856],[]),([6,31744,1015808,1082465,8659208,17318416,32505856],[]),([6,31744,1015808,1083361,2164802,4329604,8659208,32539681],[]),([6,31744,1015808,1083361,3247203,4329604,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p68 : b68.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b69 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,2164802,4329604,4330468,8659208,32539681],[]),([6,31744,1015808,2164802,4329604,8659208,8659944,32539681],[]),([6,31744,1015808,2164802,4329604,8659208,17318896,32539681],[]),([6,31744,1015808,2164802,4329604,8659208,32506848,32539681],[]),([6,31744,1015808,2164802,4329604,8659208,32539681,32540641],[]),([6,31744,1015808,2164802,4329604,8659231,32539681],[]),([6,31744,1015808,2164802,4329604,8659944,17318416,32539681],[]),([6,31744,1015808,2164802,4329604,8659944,32505856,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p69 : b69.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b70 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,2164802,4329604,8659944,32539681],[]),([6,31744,1015808,2164802,4329604,17318431,32539681],[]),([6,31744,1015808,2164802,4329604,17318896,32539681],[]),([6,31744,1015808,2164802,4329631,8659208,32539681],[]),([6,31744,1015808,2164802,4329631,17318416,32539681],[]),([6,31744,1015808,2164802,4330468,8659208,17318416,32539681],[]),([6,31744,1015808,2164802,4330468,8659208,32505856,32539681],[]),([6,31744,1015808,2164802,4330468,8659208,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p70 : b70.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b71 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,2164802,4330468,17318416,32539681],[]),([6,31744,1015808,2164802,8659208,17318431,32539681],[]),([6,31744,1015808,2164802,8659208,17318896,32539681],[]),([6,31744,1015808,2164802,8659231,17318416,32539681],[]),([6,31744,1015808,2164802,8659944,17318416,32539681],[]),([6,31744,1015808,4329604,8659208,17318418,32505856],[]),([6,31744,1015808,4329604,8659208,17318431,32539681],[]),([6,31744,1015808,4329604,8659210,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p71 : b71.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b72 : List (List Nat × List (Nat × Nat)) := [([6,31744,1015808,4329604,8659231,17318416,32539681],[]),([6,31744,1015808,4329606,8659208,17318416,32505856],[]),([6,31744,1015808,4329631,8659208,17318416,32539681],[]),([6,31744,1015872,1082401,2164802,4329604,8659208,32505856],[]),([6,31744,1015872,1082401,8659208,17318416,32505856],[]),([6,31744,1082401,2065441,2164802,4329604,8659944,32505856],[]),([6,31744,1082401,2065441,2164802,4330468,8659208,32505856],[]),([6,31744,1082401,2164802,4329604,8659208,32506848,33521664],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p72 : b72.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b73 : List (List Nat × List (Nat × Nat)) := [([6,31744,1082401,2164802,4329604,8659944,32505856,33521664],[]),([6,31744,1082401,2164802,4330468,8659208,32505856,33521664],[]),([6,31744,1082401,3115074,4329604,17318431,32505856],[]),([6,31744,1082401,3115074,8659208,17318431,32505856],[]),([6,31744,1083361,2065441,2164802,4329604,8659208,32505856],[]),([6,31744,2065441,2164802,4329631,17318416,32505856],[]),([6,31744,2065441,2164802,4330468,17318416,32505856],[]),([6,31744,2065441,2164802,8659231,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p73 : b73.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b74 : List (List Nat × List (Nat × Nat)) := [([6,31744,2065441,2164802,8659944,17318416,32505856],[]),([6,31744,2065441,4329604,8659231,17318416,32505856],[]),([6,31744,2065441,4329631,8659208,17318416,32505856],[]),([6,31808,1015808,1082401,2164802,4329604,8659208,32505856],[]),([6,31808,1015808,1082401,8659208,17318416,32505856],[]),([6,32736,1015808,1082401,2164802,4329604,8682760,32505856],[]),([6,1015808,1016800,1082401,2164802,4329604,8682760,32505856],[]),([6,1015808,1047552,1082401,2164802,4329604,8659944,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p74 : b74.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b75 : List (List Nat × List (Nat × Nat)) := [([6,1015808,1047552,1082401,2164802,4330468,8659208,32505856],[]),([6,1015808,1082401,1083361,2164802,4329604,8682760,32505856],[]),([6,1015808,1082401,1113121,2164802,4329604,8659944,32505856],[]),([6,1015808,1082401,1113121,2164802,4330468,8659208,32505856],[]),([6,1015808,1082401,2164802,4329604,4330468,8682760,32505856],[]),([6,1015808,1082401,2164802,4329604,8659208,32506848,32537600],[]),([6,1015808,1082401,2164802,4329604,8659944,8682760,32505856],[]),([6,1015808,1082401,2164802,4329604,8659944,17333776,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p75 : b75.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b76 : List (List Nat × List (Nat × Nat)) := [([6,1015808,1082401,2164802,4329604,8659944,32505856,32537600],[]),([6,1015808,1082401,2164802,4329604,8682760,8683496,32505856],[]),([6,1015808,1082401,2164802,4329604,8682760,17318896,32505856],[]),([6,1015808,1082401,2164802,4329604,8682760,32505856,32506848],[]),([6,1015808,1082401,2164802,4330468,8659208,32505856,32537600],[]),([6,1015808,1082401,2164802,8659231,17318896,32505856],[]),([6,1015808,1082401,2164802,8659944,17318431,32505856],[]),([6,1015808,1082401,2194498,8659208,17318431,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p76 : b76.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b77 : List (List Nat × List (Nat × Nat)) := [([6,1015808,1082401,2194498,8659231,17318416,32505856],[]),([6,1015808,1083361,1113121,2164802,4329604,8659208,32505856],[]),([6,1015808,1113121,4329631,8659208,17318416,32505856],[]),([6,1016800,1047552,1082401,2164802,4329604,8659208,32505856],[]),([7,2,31744,1015808,4329604,8659208,17318416,32505856],[]),([7,31,128,1015808,1082401,8659208,17318416,32505856],[]),([7,31,992,8192,1082401,2164802,17318416,32505856],[]),([7,31,992,31744,524288,1082401,2164802,4329604],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p77 : b77.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b78 : List (List Nat × List (Nat × Nat)) := [([7,31,992,31744,1015808,2164802,4329604,8659208,32539681],[]),([7,31,992,31744,1082401,2164802,4329604,32776456],[]),([7,31,992,31744,1082401,2164802,5214340,17318416],[]),([7,31,992,31744,1082401,2164802,8659208,32641156],[]),([7,31,992,31744,1082401,2164802,9412872,17318416],[]),([7,31,992,31744,1082401,2164802,17318416,32641156],[]),([7,31,992,31744,1082401,2164802,17318416,32776456],[]),([7,31,992,31744,1082401,3115074,4329604,17318416],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p78 : b78.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b79 : List (List Nat × List (Nat × Nat)) := [([7,31,992,31744,1082401,3115074,8659208,17318416],[]),([7,31,992,31744,1082401,4329604,8659208,32573506],[]),([7,31,992,31744,1082401,4329604,9412872,17318416],[]),([7,31,992,31744,1082401,4329604,17318416,32573506],[]),([7,31,992,31744,1082401,4329604,17318416,32776456],[]),([7,31,992,31744,1082401,5214340,8659208,17318416],[]),([7,31,992,31744,1082401,8659208,17318416,32573506],[]),([7,31,992,31744,1082401,8659208,17318416,32641156],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p79 : b79.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b80 : List (List Nat × List (Nat × Nat)) := [([7,31,992,31744,2065441,2164802,4329604,17318416],[]),([7,31,992,31744,2065441,2164802,8659208,17318416],[]),([7,31,992,31744,2065441,4329604,8659208,17318416],[]),([7,31,992,31744,2164802,4329604,8659208,32539681],[]),([7,31,992,31744,2164802,4329604,9412872,17318416],[]),([7,31,992,31744,2164802,4329604,17318416,32539681],[]),([7,31,992,31744,2164802,4329604,17318416,32776456],[]),([7,31,992,31744,2164802,5214340,8659208,17318416],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p80 : b80.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b81 : List (List Nat × List (Nat × Nat)) := [([7,31,992,31744,2164802,8659208,17318416,32539681],[]),([7,31,992,31744,2164802,8659208,17318416,32641156],[]),([7,31,992,31744,3115074,4329604,8659208,17318416],[]),([7,31,992,31744,4329604,8659208,17318416,32539681],[]),([7,31,992,31744,4329604,8659208,17318416,32573506],[]),([7,31,992,262144,1082401,2164802,4329604,32505856],[]),([7,31,992,1015808,1082401,2164802,4329604,8682760,32505856],[]),([7,31,992,1015808,1082401,2164802,8659208,32641156],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p81 : b81.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b82 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1015808,1082401,2164802,17318416,32641156],[]),([7,31,992,1015808,1082401,2194498,8659208,17318416],[]),([7,31,992,1015808,1082401,4329604,8659208,32573506],[]),([7,31,992,1015808,1082401,4329604,17318416,32573506],[]),([7,31,992,1015808,1082401,4357252,8659208,17318416],[]),([7,31,992,1015808,1082401,8659208,17318416,32573506],[]),([7,31,992,1015808,1082401,8659208,17318416,32641156],[]),([7,31,992,1015808,1113121,2164802,8659208,17318416],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p82 : b82.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b83 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1015808,1113121,4329604,8659208,17318416],[]),([7,31,992,1015808,2164802,4329604,8659208,32539681],[]),([7,31,992,1015808,2164802,4329604,17318416,32539681],[]),([7,31,992,1015808,2164802,4357252,8659208,17318416],[]),([7,31,992,1015808,2164802,8659208,17318416,32539681],[]),([7,31,992,1015808,2164802,8659208,17318416,32641156],[]),([7,31,992,1015808,2194498,4329604,8659208,17318416],[]),([7,31,992,1015808,4329604,8659208,17318416,32539681],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p83 : b83.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b84 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1015808,4329604,8659208,17318416,32573506],[]),([7,31,992,1082401,2164802,4329604,17333776,32505856],[]),([7,31,992,1082401,2164802,5214340,17318416,32505856],[]),([7,31,992,1082401,2194498,8659208,17318416,32505856],[]),([7,31,992,1082401,3115074,4329604,17318416,32505856],[]),([7,31,992,1082401,3115074,8659208,17318416,32505856],[]),([7,31,992,1082401,4357252,8659208,17318416,32505856],[]),([7,31,992,1082401,5214340,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p84 : b84.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b85 : List (List Nat × List (Nat × Nat)) := [([7,31,992,1113121,2164802,8659208,17318416,32505856],[]),([7,31,992,1113121,4329604,8659208,17318416,32505856],[]),([7,31,992,2065441,2164802,4329604,17318416,32505856],[]),([7,31,992,2065441,2164802,8659208,17318416,32505856],[]),([7,31,992,2065441,4329604,8659208,17318416,32505856],[]),([7,31,992,2164802,4357252,8659208,17318416,32505856],[]),([7,31,992,2164802,5214340,8659208,17318416,32505856],[]),([7,31,992,2194498,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p85 : b85.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b86 : List (List Nat × List (Nat × Nat)) := [([7,31,992,3115074,4329604,8659208,17318416,32505856],[]),([7,31,4096,1015808,1082401,2164802,17318416,32505856],[]),([7,31,31744,1015808,1082401,2164802,4329604,8659944,32505856],[]),([7,31,31744,1015808,1082401,2164802,4330468,8659208,32505856],[]),([7,31,31744,1015808,1082401,4329604,8659208,32573506],[]),([7,31,31744,1015808,1082401,4329604,17318416,32573506],[]),([7,31,31744,1015808,1082401,8659208,17318416,32573506],[]),([7,31,31744,1015808,1083361,4329604,8659208,17318416],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p86 : b86.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b87 : List (List Nat × List (Nat × Nat)) := [([7,31,31744,1015808,2164802,4329604,8659208,32539681],[]),([7,31,31744,1015808,2164802,4329604,17318416,32539681],[]),([7,31,31744,1015808,2164802,8659208,17318416,32539681],[]),([7,31,31744,1015808,2165730,4329604,8659208,17318416],[]),([7,31,31744,1015808,4329604,8659208,17318416,32539681],[]),([7,31,31744,1015808,4329604,8659208,17318416,32573506],[]),([7,31,31744,1082401,2164802,4329604,17318896,32505856],[]),([7,31,31744,1082401,2164802,8659208,17318896,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p87 : b87.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b88 : List (List Nat × List (Nat × Nat)) := [([7,31,31744,1082401,3115074,4329604,17318416,32505856],[]),([7,31,31744,1082401,3115074,8659208,17318416,32505856],[]),([7,31,31744,1083361,4329604,8659208,17318416,32505856],[]),([7,31,31744,2065441,2164802,4329604,17318416,32505856],[]),([7,31,31744,2065441,2164802,8659208,17318416,32505856],[]),([7,31,31744,2065441,4329604,8659208,17318416,32505856],[]),([7,31,31744,2165730,4329604,8659208,17318416,32505856],[]),([7,31,31744,3115074,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p88 : b88.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b89 : List (List Nat × List (Nat × Nat)) := [([7,31,1015808,1082401,2164802,4329604,8659944,32505856],[]),([7,31,1015808,1082401,2164802,4329604,8682760,32505856],[]),([7,31,1015808,1082401,2164802,4329604,17318896,32505856],[]),([7,31,1015808,1082401,2164802,4329604,17333776,32505856],[]),([7,31,1015808,1082401,2164802,8659208,17318896,32505856],[]),([7,31,1015808,1082401,2164802,8659944,17318416,32505856],[]),([7,31,1015808,1082401,2194498,8659208,17318416,32505856],[]),([7,31,1015808,1083361,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p89 : b89.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b90 : List (List Nat × List (Nat × Nat)) := [([7,31,1015808,1113121,2164802,8659208,17318416,32505856],[]),([7,31,1015808,1113121,4329604,8659208,17318416,32505856],[]),([7,31,1015808,2165730,4329604,8659208,17318416,32505856],[]),([7,31,1015808,2194498,4329604,8659208,17318416,32505856],[]),([7,64,31744,1015808,1082401,2164802,4329604,8659208,32505856],[]),([7,64,31744,1015808,1082401,8659208,17318416,32505856],[]),([7,992,31744,262144,1015808,1082401,2164802,4329604,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p90 : b90.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b91 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1015808,1082401,2164802,4329604,8659208,32539681],[]),([7,992,31744,1015808,1082401,2164802,4329604,8659231,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,8659944,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,8682760,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,9741609,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,10824010,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,12988812,32505856],[]),([7,992,31744,1015808,1082401,2164802,4329604,32505856,32776456],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p91 : b91.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b92 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1015808,1082401,2164802,4329631,8659208,32505856],[]),([7,992,31744,1015808,1082401,2164802,4330468,8659208,32505856],[]),([7,992,31744,1015808,1082401,2164802,5412005,8659208,32505856],[]),([7,992,31744,1015808,1082401,2164802,6494406,8659208,32505856],[]),([7,992,31744,1015808,1082401,2164802,8659208,32505856,32641156],[]),([7,992,31744,1015808,1082401,2164831,4329604,8659208,32505856],[]),([7,992,31744,1015808,1082401,3247203,4329604,8659208,32505856],[]),([7,992,31744,1015808,1082401,4329604,8659208,32505856,32573506],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p92 : b92.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b93 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1015808,2164802,4329604,8659208,17318416,32539681],[]),([7,992,31744,1015808,2164802,4329604,8659208,32505856,32539681],[]),([7,992,31744,1015808,2164802,4329604,8659208,32539681],[]),([7,992,31744,1015808,2164802,4329604,17318416,32539681],[]),([7,992,31744,1015808,2164802,8659208,17318416,32539681],[]),([7,992,31744,1015808,4329604,8659208,17318416,32539681],[]),([7,992,31744,1082401,2065441,2164802,4329604,8659208,32505856],[]),([7,992,31744,1082401,2164802,4329604,8659208,17809936,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p93 : b93.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b94 : List (List Nat × List (Nat × Nat)) := [([7,992,31744,1082401,2164802,4329604,8659208,32505856,33521664],[]),([7,992,31744,1082401,2164802,4329604,17318431,32505856],[]),([7,992,31744,1082401,2164802,8659208,17318431,32505856],[]),([7,992,31744,1082401,4329604,8659208,17318431,32505856],[]),([7,992,31744,2065441,2164802,4329604,17318416,32505856],[]),([7,992,31744,2065441,2164802,8659208,17318416,32505856],[]),([7,992,31744,2065441,4329604,8659208,17318416,32505856],[]),([7,992,1015808,1047552,1082401,2164802,4329604,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p94 : b94.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b95 : List (List Nat × List (Nat × Nat)) := [([7,992,1015808,1082401,1113121,2164802,4329604,8659208,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8659208,8682760,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8659208,17333776,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8659208,32505856,32537600],[]),([7,992,1015808,1082401,2164802,4329604,8659231,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8682760,17318416,32505856],[]),([7,992,1015808,1082401,2164802,4329604,8682760,32505856],[]),([7,992,1015808,1082401,2164802,4329604,17318431,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p95 : b95.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b96 : List (List Nat × List (Nat × Nat)) := [([7,992,1015808,1082401,2164802,4329604,17333776,32505856],[]),([7,992,1015808,1082401,2164802,8659208,17318431,32505856],[]),([7,992,1015808,1082401,2164802,8659231,17318416,32505856],[]),([7,992,1015808,1082401,4329604,8659208,17318431,32505856],[]),([7,992,1015808,1082401,4329604,8659231,17318416,32505856],[]),([7,992,1015808,1113121,2164802,8659208,17318416,32505856],[]),([7,992,1015808,1113121,4329604,8659208,17318416,32505856],[]),([7,31744,32736,1015808,1082401,2164802,4329604,8659208,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p96 : b96.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b97 : List (List Nat × List (Nat × Nat)) := [([7,31744,1015808,1016800,1082401,2164802,4329604,8659208,32505856],[]),([7,31744,1015808,1082401,1083361,2164802,4329604,8659208,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,4330468,8659208,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,8659208,8659944,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,8659208,17318896,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,8659208,32505856,32506848],[]),([7,31744,1015808,1082401,2164802,4329604,8659231,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,8659944,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p97 : b97.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b98 : List (List Nat × List (Nat × Nat)) := [([7,31744,1015808,1082401,2164802,4329604,8659944,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,17318431,32505856],[]),([7,31744,1015808,1082401,2164802,4329604,17318896,32505856],[]),([7,31744,1015808,1082401,2164802,4329631,8659208,32505856],[]),([7,31744,1015808,1082401,2164802,4329631,17318416,32505856],[]),([7,31744,1015808,1082401,2164802,4330468,8659208,17318416,32505856],[]),([7,31744,1015808,1082401,2164802,4330468,8659208,32505856],[]),([7,31744,1015808,1082401,2164802,4330468,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p98 : b98.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b99 : List (List Nat × List (Nat × Nat)) := [([7,31744,1015808,1082401,2164802,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,2164802,8659208,17318896,32505856],[]),([7,31744,1015808,1082401,2164802,8659231,17318416,32505856],[]),([7,31744,1015808,1082401,2164802,8659944,17318416,32505856],[]),([7,31744,1015808,1082401,4329604,8659208,17318431,32505856],[]),([7,31744,1015808,1082401,4329604,8659231,17318416,32505856],[]),([7,31744,1015808,1082401,4329631,8659208,17318416,32505856],[]),([7,31744,1015808,1083361,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p99 : b99.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b100 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1015808,1082401,2164802,4329604,8659208],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[]),([8,31,992,31744,1015808,1082401,2164802,4329604,17318416],[]),([8,31,992,31744,1015808,1082401,2164802,8659208,17318416],[]),([8,31,992,31744,1015808,1082401,4329604,8659208,17318416],[]),([8,31,992,31744,1015808,2164802,4329604,8659208,17318416],[]),([8,31,992,31744,1082401,2164802,4329604,8659208,32505856],[]),([8,31,992,31744,1082401,2164802,4329604,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p100 : b100.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b101 : List (List Nat × List (Nat × Nat)) := [([8,31,992,31744,1082401,2164802,8659208,17318416,32505856],[]),([8,31,992,31744,1082401,4329604,8659208,17318416,32505856],[]),([8,31,992,31744,2164802,4329604,8659208,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,4329604,8659208,32505856],[]),([8,31,992,1015808,1082401,2164802,4329604,17318416,32505856],[]),([8,31,992,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,31,992,1015808,1082401,4329604,8659208,17318416,32505856],[]),([8,31,992,1015808,2164802,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p101 : b101.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b102 : List (List Nat × List (Nat × Nat)) := [([8,31,31744,1015808,1082401,2164802,4329604,8659208,32505856],[]),([8,31,31744,1015808,1082401,2164802,4329604,17318416,32505856],[]),([8,31,31744,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,31,31744,1015808,1082401,4329604,8659208,17318416,32505856],[]),([8,31,31744,1015808,2164802,4329604,8659208,17318416,32505856],[]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[]),([8,992,31744,1015808,1082401,2164802,4329604,8659208,32505856],[]),([8,992,31744,1015808,1082401,2164802,4329604,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p102 : b102.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
def b103 : List (List Nat × List (Nat × Nat)) := [([8,992,31744,1015808,1082401,2164802,8659208,17318416,32505856],[]),([8,992,31744,1015808,1082401,4329604,8659208,17318416,32505856],[]),([8,992,31744,1015808,2164802,4329604,8659208,17318416,32505856],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p103 : b103.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowsOk : T_.toList = (((((((b0 ++ (b1 ++ b2)) ++ (b3 ++ (b4 ++ b5))) ++ ((b6 ++ (b7 ++ b8)) ++ ((b9 ++ b10) ++ (b11 ++ b12)))) ++ (((b13 ++ (b14 ++ b15)) ++ (b16 ++ (b17 ++ b18))) ++ ((b19 ++ (b20 ++ b21)) ++ ((b22 ++ b23) ++ (b24 ++ b25))))) ++ ((((b26 ++ (b27 ++ b28)) ++ (b29 ++ (b30 ++ b31))) ++ ((b32 ++ (b33 ++ b34)) ++ ((b35 ++ b36) ++ (b37 ++ b38)))) ++ (((b39 ++ (b40 ++ b41)) ++ (b42 ++ (b43 ++ b44))) ++ ((b45 ++ (b46 ++ b47)) ++ ((b48 ++ b49) ++ (b50 ++ b51)))))) ++ (((((b52 ++ (b53 ++ b54)) ++ (b55 ++ (b56 ++ b57))) ++ ((b58 ++ (b59 ++ b60)) ++ ((b61 ++ b62) ++ (b63 ++ b64)))) ++ (((b65 ++ (b66 ++ b67)) ++ (b68 ++ (b69 ++ b70))) ++ ((b71 ++ (b72 ++ b73)) ++ ((b74 ++ b75) ++ (b76 ++ b77))))) ++ ((((b78 ++ (b79 ++ b80)) ++ (b81 ++ (b82 ++ b83))) ++ ((b84 ++ (b85 ++ b86)) ++ ((b87 ++ b88) ++ (b89 ++ b90)))) ++ (((b91 ++ (b92 ++ b93)) ++ (b94 ++ (b95 ++ b96))) ++ ((b97 ++ (b98 ++ b99)) ++ ((b100 ++ b101) ++ (b102 ++ b103)))))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed : ∀ x, T_.mem x = true → ∃ h, P_ x h = true := cover _ _ rowsOk (all_app (all_app (all_app (all_app (all_app (all_app p0 (all_app p1 p2)) (all_app p3 (all_app p4 p5))) (all_app (all_app p6 (all_app p7 p8)) (all_app (all_app p9 p10) (all_app p11 p12)))) (all_app (all_app (all_app p13 (all_app p14 p15)) (all_app p16 (all_app p17 p18))) (all_app (all_app p19 (all_app p20 p21)) (all_app (all_app p22 p23) (all_app p24 p25))))) (all_app (all_app (all_app (all_app p26 (all_app p27 p28)) (all_app p29 (all_app p30 p31))) (all_app (all_app p32 (all_app p33 p34)) (all_app (all_app p35 p36) (all_app p37 p38)))) (all_app (all_app (all_app p39 (all_app p40 p41)) (all_app p42 (all_app p43 p44))) (all_app (all_app p45 (all_app p46 p47)) (all_app (all_app p48 p49) (all_app p50 p51)))))) (all_app (all_app (all_app (all_app (all_app p52 (all_app p53 p54)) (all_app p55 (all_app p56 p57))) (all_app (all_app p58 (all_app p59 p60)) (all_app (all_app p61 p62) (all_app p63 p64)))) (all_app (all_app (all_app p65 (all_app p66 p67)) (all_app p68 (all_app p69 p70))) (all_app (all_app p71 (all_app p72 p73)) (all_app (all_app p74 p75) (all_app p76 p77))))) (all_app (all_app (all_app (all_app p78 (all_app p79 p80)) (all_app p81 (all_app p82 p83))) (all_app (all_app p84 (all_app p85 p86)) (all_app (all_app p87 p88) (all_app p89 p90)))) (all_app (all_app (all_app p91 (all_app p92 p93)) (all_app p94 (all_app p95 p96))) (all_app (all_app p97 (all_app p98 p99)) (all_app (all_app p100 p101) (all_app p102 p103)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 5) => (33004641 : ℕ).testBit (5 * u.val + v.val)) 8) :=
  rep_lb 33004641 8 0 1 PD_ PM_ XS_ [] T_ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) closed (by decide +kernel)
end ChainStairFive

theorem PEqualNP.Outside.L_meta_19456_stair_five : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 5) => (33004641 : ℕ).testBit (5 * u.val + v.val)) 8) := ChainStairFive.result

theorem PEqualNP.Outside.L_meta_19456_stair_five_lower (s : ℕ)
    (hs : PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 5) => decide (v.val ≤ u.val)) s) :
    9 ≤ s := by
  by_contra! h
  obtain ⟨C, hm, hz, hr⟩ := hs
  apply PEqualNP.Outside.L_meta_19456_stair_five
  refine ⟨C, hm, by omega, ?_⟩
  intro u v
  rw [hr u v]
  exact (by decide +kernel : ∀ (i j : Fin 5), decide (j.val ≤ i.val) =
    (33004641 : ℕ).testBit (5 * i.val + j.val)) u v
namespace ChainStairFour
open PEqualNP.Outside.L_meta_20404_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def code (k : ℕ) : ℕ := 2 ^ (k / 4) + 2 ^ (4 + k % 4)

def ohPts : List ℕ := List.ofFn fun k : Fin 16 => code k.val

theorem ofFn_code : ∀ k : Fin 16, List.ofFn (pt 8 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 4) (by have := k.isLt; omega) : Fin 4)
      (Fin.mk (k.val % 4) (by have := k.isLt; omega) : Fin 4) := by
  decide +kernel

theorem ohPts_length : ohPts.length = 16 := by simp [ohPts]

theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => M.testBit (4 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 16) : C.eval (List.ofFn (pt 8 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (4 * (k / 4) + k % 4) = M.testBit k
  rw [Nat.div_add_mod]

theorem enc_rep (M : ℕ) (hM : M < 2 ^ 16) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => M.testBit (4 * u.val + v.val)) C) :
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

theorem rep_lb (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ) (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 16) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 16) (h0' : zer < 16)
    (hxs : (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 0 M PD PM = true) (hG : symOK 0 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK 0 M PD PM G T x h = true)
    (hi : XS.sublists.all (rootOK M PD PM G T s) = true) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 4) => M.testBit (4 * u.val + v.val)) s := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have hnot : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h] <;> exact fun h' => GateOp.noConfusion h'
  have hfan : FanInTwo C := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  have hnc : ∃ a b : Fin 8 → Bool, (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 8 (code one), pt 8 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run_m (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) hnc s
    ⟨C, hfan, hnot, hsize, fun x => rfl⟩
  have hr : NatRun 0 (encL (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) ohPts) s'
      (ws.map fun a => encL a ohPts) :=
    Run.map (fun a : BFn 8 => encL a ohPts) (fun a => (Nat.xor_zero _).symm)
      (fun a b => encL_and a b ohPts) (fun a b => encL_or a b ohPts) hrun
  rw [enc_rep M hM C hrep] at hr
  exact cert_core hp hG hT hi hs' (by rw [← hxs]; exact hsub.map _) hr




def PD_ : List (Nat × Nat) := [(1,3241),(2,2813),(3,2519),(4,2114),(5,136),(6,237),(7,223),(8,198),(9,74),(10,12),(11,15),(12,14),(13,6),(14,2)]
def PM_ : List (Nat × Nat) := [(1,63281),(2,63281),(3,63281),(6,63281),(7,63281),(11,63281)]
def XS_ : List Nat := [15,240,3840,61440,4369,8738,17476,34952]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def T_ : BT := (.nd (.nd (.nd .lf [3,3840,8738,17652,61713] .lf) [4,240,3840,8738,17476,61713] .lf) [4,3840,4369,8738,17652,61440] (.nd .lf [5,240,3840,4369,8738,17476,61440] .lf))
def P_ := stepOK 0 63281 PD_ PM_ [] T_
def b0 : List (List Nat × List (Nat × Nat)) := [([3,3840,8738,17652,61713],[]),([4,240,3840,8738,17476,61713],[]),([4,3840,4369,8738,17652,61440],[]),([5,240,3840,4369,8738,17476,61440],[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0 : b0.all (fun kh => P_ kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowsOk : T_.toList = (b0).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed : ∀ x, T_.mem x = true → ∃ h, P_ x h = true := cover _ _ rowsOk p0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 4) => (63281 : ℕ).testBit (4 * u.val + v.val)) 5) :=
  rep_lb 63281 5 0 1 PD_ PM_ XS_ [] T_ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) closed (by decide +kernel)
end ChainStairFour

theorem PEqualNP.Outside.L_meta_19456_stair_four : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 4) => (63281 : ℕ).testBit (4 * u.val + v.val)) 5) := ChainStairFour.result
theorem PEqualNP.Outside.L_meta_19456_stair_four_lower (s : ℕ)
    (hs : PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin 4) => decide (v.val ≤ u.val)) s) :
    6 ≤ s := by
  by_contra! h
  obtain ⟨C, hm, hz, hr⟩ := hs
  apply PEqualNP.Outside.L_meta_19456_stair_four
  refine ⟨C, hm, by omega, ?_⟩
  intro u v
  rw [hr u v]
  exact (by decide +kernel : ∀ (i j : Fin 4), decide (j.val ≤ i.val) =
    (63281 : ℕ).testBit (4 * i.val + j.val)) u v



namespace PEqualNP.Outside.L_meta_19456_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp [stepW]; omega

private def effInputs (N : ℕ) (C : Circuit) (k : ℕ) : List ℕ :=
  let g := C.gates.getD k ⟨GateOp.or, []⟩
  let raw := match g.op with
    | GateOp.not => g.inputs.take 1
    | _ => g.inputs
  raw.filter fun i => decide (i < N + k)

private lemma effInputs_lt (N : ℕ) (C : Circuit) (k i : ℕ) (hi : i ∈ effInputs N C k) :
    i < N + k := by
  simp only [effInputs, List.mem_filter, decide_eq_true_eq] at hi
  exact hi.2

private def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma effInputs_len (N : ℕ) (C : Circuit) (hF : FanInTwo C) (k : ℕ) (hk : k < C.gates.length) :
    (effInputs N C k).length ≤ if isNot C.gates[k].op then 1 else 2 := by
  have hg : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  have hlen : C.gates[k].inputs.length ≤ 2 := (hF _ (List.getElem_mem hk)).2
  simp only [effInputs, hg]
  cases hop : C.gates[k].op <;> simp only [isNot, Bool.false_eq_true, ↓reduceIte]
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen

private def reachAux (N : ℕ) (C : Circuit) : ℕ → Finset ℕ → Finset ℕ
  | 0, acc => acc
  | m + 1, acc =>
    let acc' :=
      if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    reachAux N C m acc'

private lemma reachAux_sub (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    acc ⊆ reachAux N C m acc := by
  induction m generalizing acc with
  | zero => exact Finset.Subset.rfl
  | succ m ih =>
    dsimp [reachAux]
    split_ifs
    · exact Finset.Subset.trans Finset.subset_union_left (ih _)
    · exact ih _

private lemma reachAux_le (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) (M : ℕ)
    (hacc : ∀ w ∈ acc, w ≤ M) : ∀ w ∈ reachAux N C m acc, w ≤ M := by
  induction m generalizing acc with
  | zero => exact hacc
  | succ m ih =>
    dsimp [reachAux]
    apply ih
    intro w hw
    split_ifs at hw with h
    · rcases Finset.mem_union.mp hw with ha | hi
      · exact hacc w ha
      · have hlt := effInputs_lt N C m w (List.mem_toFinset.mp hi)
        have hle := hacc (N + m) h.2
        omega
    · exact hacc w hw

private lemma reachAux_closed (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ)
    (hhi : ∀ k, m ≤ k → k < C.gates.length → N + k ∈ acc → ∀ i ∈ effInputs N C k, i ∈ acc) :
    ∀ k, k < C.gates.length → N + k ∈ reachAux N C m acc → ∀ i ∈ effInputs N C k, i ∈ reachAux N C m acc := by
  induction m generalizing acc with
  | zero =>
    intro k hk hmem i hi
    exact hhi k (Nat.zero_le k) hk hmem i hi
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    rw [hstep]
    apply ih acc'
    intro k hmk hk hmem i hi
    by_cases heq : k = m
    · subst heq
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · exact h.2
        · exact hmem
      have hsub : (effInputs N C k).toFinset ⊆ acc' := by
        dsimp [acc']
        simp only [hk, hmem_acc, and_self, ↓reduceIte]
        exact Finset.subset_union_right
      exact hsub (List.mem_toFinset.mpr hi)
    · have hlt : m + 1 ≤ k := by omega
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · rcases Finset.mem_union.mp hmem with ha | hin
          · exact ha
          · have := effInputs_lt N C m (N + k) (List.mem_toFinset.mp hin)
            omega
        · exact hmem
      have hsub : acc ⊆ acc' := by
        dsimp [acc']; split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.rfl
      exact hsub (hhi k hlt hk hmem_acc i hi)

private lemma reachAux_bound (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    reachAux N C m acc ⊆ acc ∪
      ((Finset.range m).filter fun k => k < C.gates.length ∧ N + k ∈ reachAux N C m acc).biUnion
        (fun k => (effInputs N C k).toFinset) := by
  induction m generalizing acc with
  | zero => dsimp [reachAux]; exact Finset.subset_union_left
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    intro w hw
    have h1 := ih acc' (hstep ▸ hw)
    rcases Finset.mem_union.mp h1 with hacc' | hbi
    · dsimp [acc'] at hacc'
      split_ifs at hacc' with h
      · rcases Finset.mem_union.mp hacc' with ha | hin
        · exact Finset.mem_union_left _ ha
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨m, ?_, hin⟩
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_self m, h.1, ?_⟩
          rw [hstep]
          apply reachAux_sub
          dsimp [acc']
          simp only [h.1, h.2, and_self, ↓reduceIte]
          exact Finset.mem_union_left _ h.2
      · exact Finset.mem_union_left _ hacc'
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion] at hbi ⊢
      obtain ⟨k, hk, hwk⟩ := hbi
      rw [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨k, ?_, hwk⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_lt hk.1, hk.2.1, hstep.symm ▸ hk.2.2⟩

private def subW (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  reachAux N C C.gates.length {w}

private lemma self_mem_subW (N : ℕ) (C : Circuit) (w : ℕ) : w ∈ subW N C w :=
  reachAux_sub N C C.gates.length {w} (Finset.mem_singleton_self w)

private lemma subW_le (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) : u ≤ w :=
  reachAux_le N C C.gates.length {w} w (fun z hz => by rw [Finset.mem_singleton.mp hz]) u hu

private lemma subW_closed (N : ℕ) (C : Circuit) (w k : ℕ) (hk : k < C.gates.length)
    (hmem : N + k ∈ subW N C w) (i : ℕ) (hi : i ∈ effInputs N C k) : i ∈ subW N C w :=
  reachAux_closed N C C.gates.length {w} (fun _ h1 h2 => by omega) k hk hmem i hi

private lemma subW_sub_of_mem (N : ℕ) (C : Circuit) (w1 w2 : ℕ) (h : w1 ∈ subW N C w2) :
    subW N C w1 ⊆ subW N C w2 := by
  have haux : ∀ m (acc : Finset ℕ), acc ⊆ subW N C w2 → reachAux N C m acc ⊆ subW N C w2 := by
    intro m
    induction m with
    | zero => intro acc hacc; exact hacc
    | succ m ih =>
      intro acc hacc
      dsimp [reachAux]
      apply ih
      split_ifs with hm
      · refine Finset.union_subset hacc ?_
        intro i hi
        exact subW_closed N C w2 m hm.1 (hacc hm.2) i (List.mem_toFinset.mp hi)
      · exact hacc
  exact haux C.gates.length {w1} (Finset.singleton_subset_iff.mpr h)

private lemma subW_parent (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) (hne : u ≠ w) :
    ∃ k < C.gates.length, N + k ∈ subW N C w ∧ u ∈ effInputs N C k := by
  have hb := reachAux_bound N C C.gates.length {w} hu
  rcases Finset.mem_union.mp hb with hsing | hbi
  · exact absurd (Finset.mem_singleton.mp hsing) hne
  · obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hbi
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.2.1, hk.2.2, List.mem_toFinset.mp huk⟩

private lemma wire_getD_input (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (i : ℕ) (hi : i < N) :
    (C.wires x).getD i false = x.getD i false := by
  change (C.gates.foldl stepW x).getD i false = x.getD i false
  exact foldl_getD_lt C.gates x i (by omega)

private lemma wire_getD_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => if i < N + k then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  change (C.gates.foldl stepW x).getD (N + k) false = _
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen1 : ((C.gates.take k).foldl stepW x).length = N + k := by
    rw [foldl_len, hx, List.length_take]; omega
  have hlt : N + k < (stepW ((C.gates.take k).foldl stepW x) C.gates[k]).length := by
    simp only [stepW, List.length_append, List.length_singleton, hlen1]; omega
  rw [foldl_getD_lt _ _ _ hlt]
  simp only [stepW]
  have hget : ((C.gates.take k).foldl stepW x ++
      [C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false)]).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false) := by
    rw [← hlen1]
    simp [List.getD_eq_getElem?_getD]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < N + k
  · simp only [hi, ↓reduceIte]
    have hsplit2 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    change ((C.gates.take k).foldl stepW x).getD i false = (C.gates.foldl stepW x).getD i false
    conv_rhs => rw [hsplit2]
    rw [List.foldl_append]
    exact (foldl_getD_lt _ _ i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

private lemma eval_gate_eff (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.gates[k].op = GateOp.and → (C.wires x).getD (N + k) false =
      (if C.gates[k].inputs.all (fun i => decide (i < N + k)) then (effInputs N C k).all (fun i => (C.wires x).getD i false) else false)) ∧
    (C.gates[k].op = GateOp.or → (C.wires x).getD (N + k) false = (effInputs N C k).any (fun i => (C.wires x).getD i false)) ∧
    (C.gates[k].op = GateOp.not → (C.wires x).getD (N + k) false =
      match effInputs N C k with | a :: _ => !((C.wires x).getD a false) | [] => true) := by
  have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  refine ⟨?_, ?_, ?_⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.all_map]
    by_cases hall : C.gates[k].inputs.all (fun i => decide (i < N + k)) = true
    · simp only [hall, ↓reduceIte]
      have hfilt : C.gates[k].inputs.filter (fun i => decide (i < N + k)) = C.gates[k].inputs :=
        List.filter_eq_self.mpr (fun i hi => List.all_eq_true.mp hall i hi)
      rw [hfilt]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
      have hex : ∃ i ∈ C.gates[k].inputs, ¬ i < N + k := by
        by_contra hno
        push Not at hno
        exact hall (List.all_eq_true.mpr (fun i hi => decide_eq_true (hno i hi)))
      obtain ⟨i, hi, hnot⟩ := hex
      rw [Bool.eq_false_iff]
      intro ht
      have := List.all_eq_true.mp ht i hi
      simp [hnot] at this
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, hv⟩
      by_cases hlt : i < N + k
      · simp only [hlt, ↓reduceIte] at hv
        exact ⟨i, ⟨hi, hlt⟩, hv⟩
      · simp [hlt] at hv
    · rintro ⟨i, ⟨hi, hlt⟩, hv⟩
      exact ⟨i, hi, by simp only [hlt, ↓reduceIte]; exact hv⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval]
    cases hin : C.gates[k].inputs with
    | nil => rfl
    | cons a rest =>
      simp only [List.take_succ_cons, List.take_zero, List.filter_cons, List.filter_nil, List.map_cons, List.headD_cons]
      by_cases ha : a < N + k
      · simp [ha]
      · simp [ha]

private lemma wires_agree_of_subW (N : ℕ) (C : Circuit) (hF : FanInTwo C) (w0 : ℕ)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C w0 → x.getD i false = y.getD i false) :
    ∀ w, w ∈ subW N C w0 → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn, wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw ⊢
        obtain ⟨hand, hor, hnot⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', hnot'⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = (C.wires y).getD i false := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C w0 (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1, hand' h1]
          split_ifs
          · apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
            constructor <;> intro h i hi
            · rw [← hrec i hi]; exact h i hi
            · rw [hrec i hi]; exact h i hi
          · rfl
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2, hor' h2]
            apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
            constructor <;> rintro ⟨i, hi, hv⟩
            · exact ⟨i, hi, hrec i hi ▸ hv⟩
            · exact ⟨i, hi, (hrec i hi).symm ▸ hv⟩
          · have h3' : C.gates[w - N].op = GateOp.not := Set.mem_singleton_iff.mp h3
            rw [hnot h3', hnot' h3']
            cases heff : effInputs N C (w - N) with
            | nil => rfl
            | cons a rest =>
              have ha : a ∈ effInputs N C (w - N) := by rw [heff]; simp
              dsimp only
              rw [hrec a ha]
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        have hly : (C.wires y).length = N + C.gates.length := by
          change (C.gates.foldl stepW y).length = N + C.gates.length; rw [foldl_len, hy]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma mono_of_no_not (N : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ subW N C C.output → C.gates[k].op ≠ GateOp.not)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C C.output → x.getD i false = true → y.getD i false = true) :
    ∀ w, w ∈ subW N C C.output → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hvx
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn] at hvx
      rw [wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw hvx
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw hvx ⊢
        obtain ⟨hand, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C C.output (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1] at hvx; rw [hand' h1]
          split_ifs at hvx ⊢
          · rw [List.all_eq_true] at hvx ⊢
            intro i hi; exact hrec i hi (hvx i hi)
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2] at hvx; rw [hor' h2]
            rw [List.any_eq_true] at hvx ⊢
            obtain ⟨i, hi, hv⟩ := hvx
            exact ⟨i, hi, hrec i hi hv⟩
          · exact absurd (Set.mem_singleton_iff.mp h3) (hnonot (w - N) hk hw)
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        rw [List.getD_eq_default _ _ (by omega)] at hvx
        exact Bool.noConfusion hvx

private lemma repInput_len {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma repInput_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (oneEach u v).getD i false =
      if h : i < n then decide (⟨i, h⟩ = u) else decide (⟨i - n, by omega⟩ = v) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
    simp [h]
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_ofFn]
    simp [show i - n < m by omega]

theorem mono_bound {n m s minR minC : ℕ} (A : Fin n → Fin m → Bool)
    (hminR : (Finset.univ.filter fun u : Fin n => ∀ u' v, A u v = true → A u' v = true).card ≤ minR)
    (hminC : (Finset.univ.filter fun v : Fin m => ∀ v' u, A u v = true → A u v' = true).card ≤ minC)
    (hrep : RepSizeAtMost A s) : (n - minR) + (m - minC) ≤ s + 1 := by
  classical
  obtain ⟨C, hM, hsz, hRep⟩ := hrep
  have hF : FanInTwo C := by
    intro g hg
    obtain ⟨hop,har⟩ := hM g hg
    refine ⟨?_,har⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    tauto
  let N := n + m
  let W : Finset ℕ := subW N C C.output
  let R : Finset ℕ := (Finset.range C.gates.length).filter fun k => N + k ∈ W
  let Rnot : Finset ℕ := R.filter fun k => (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not
  let Win : Finset ℕ := W.filter fun i => i < N
  let Wgate : Finset ℕ := R.image fun k => N + k
  have hRle : R.card ≤ C.size := by
    calc R.card ≤ (Finset.range C.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C.size := Finset.card_range _
  have hdisj : Disjoint Win Wgate := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hw1 : w < N := (Finset.mem_filter.mp h1).2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h2
    omega
  have hsubW : Win ∪ Wgate ⊆ W := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h2
      exact (Finset.mem_filter.mp hk).2
  have hWgate_card : Wgate.card = R.card := Finset.card_image_of_injective R (fun a b h => by omega)
  have hWcard : Win.card + R.card ≤ W.card := by
    calc Win.card + R.card = Win.card + Wgate.card := by rw [hWgate_card]
      _ = (Win ∪ Wgate).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ W.card := Finset.card_le_card hsubW
  let inDeg : ℕ → ℕ := fun u => ∑ k ∈ R, (effInputs N C k).count u
  have htotal_eq : ∑ u ∈ W, inDeg u = ∑ k ∈ R, (effInputs N C k).length := by
    dsimp [inDeg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkW : N + k ∈ W := (Finset.mem_filter.mp hk).2
    have hsub : (effInputs N C k).toFinset ⊆ W := fun i hi =>
      subW_closed N C C.output k hklt hkW i (List.mem_toFinset.mp hi)
    have hlen : ∀ l : List ℕ, l.toFinset ⊆ W → ∑ u ∈ W, l.count u = l.length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a tl ih =>
        intro htl
        have haW : a ∈ W := htl (by simp)
        have htlW : tl.toFinset ⊆ W := fun i hi => htl (by simp [List.mem_toFinset.mp hi])
        simp only [List.count_cons, List.length_cons]
        rw [Finset.sum_add_distrib, ih htlW]
        have h1 : ∑ u ∈ W, (if a == u then 1 else 0) = 1 := by
          simp [beq_iff_eq, haW]
        omega
    exact hlen (effInputs N C k) hsub
  have htotal_le : ∑ k ∈ R, (effInputs N C k).length + Rnot.card ≤ 2 * R.card := by
    have hsplit : ∑ k ∈ R, ((effInputs N C k).length + if (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not then 1 else 0) ≤
        ∑ _k ∈ R, 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hklt
      have hlen := effInputs_len N C hF k hklt
      rw [hgk]
      cases hop : C.gates[k].op <;> simp only [hop, isNot, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hlen ⊢ <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsplit
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] at hsplit
    exact hsplit
  have hdeg_pos : ∀ u ∈ W.erase C.output, 1 ≤ inDeg u := by
    intro u hu
    have hne : u ≠ C.output := (Finset.mem_erase.mp hu).1
    have huW : u ∈ W := (Finset.mem_erase.mp hu).2
    obtain ⟨k, hk, hkW, huk⟩ := subW_parent N C C.output u huW hne
    have hkR : k ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkW⟩
    exact le_trans (List.count_pos_iff.mpr huk)
      (Finset.single_le_sum (f := fun j => (effInputs N C j).count u) (fun _ _ => Nat.zero_le _) hkR)
  have houtW : C.output ∈ W := self_mem_subW N C C.output
  have herase_card : (W.erase C.output).card + 1 = W.card := by
    rw [Finset.card_erase_of_mem houtW]
    have := Finset.card_pos.mpr ⟨C.output, houtW⟩
    omega
  let Ur : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∉ W
  let Uc : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∉ W
  have hWin_card : (n - Ur.card) + (m - Uc.card) ≤ Win.card := by
    let Rw : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∈ W
    let Cw : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∈ W
    have hRsum : Rw.card + Ur.card = n := by
      simpa [Rw, Ur] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun u : Fin n => u.val ∈ W)
    have hCsum : Cw.card + Uc.card = m := by
      simpa [Cw, Uc] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun v : Fin m => n + v.val ∈ W)
    let Sr : Finset ℕ := Rw.image Fin.val
    let Sc : Finset ℕ := Cw.image (fun v : Fin m => n + v.val)
    have hdisjRC : Disjoint Sr Sc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h2
      omega
    have hsubRC : Sr ∪ Sc ⊆ Win := by
      intro w hw
      rcases Finset.mem_union.mp hw with h1 | h2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, by omega⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by omega⟩
    have hSr : Sr.card = Rw.card := Finset.card_image_of_injective _ Fin.val_injective
    have hSc : Sc.card = Cw.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    have hle : Rw.card + Cw.card ≤ Win.card := by
      calc Rw.card + Cw.card = Sr.card + Sc.card := by rw [hSr, hSc]
        _ = (Sr ∪ Sc).card := (Finset.card_union_of_disjoint hdisjRC).symm
        _ ≤ Win.card := Finset.card_le_card hsubRC
    omega
  have hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ W → C.gates[k].op ≠ GateOp.not := by
    intro k hk _ hnot
    have h := (hM _ (List.getElem_mem hk)).1
    simp [hnot] at h
  have hUr_le : Ur.card ≤ minR := by
    refine le_trans (Finset.card_le_card ?_) hminR
    intro u hu
    have huW : u.val ∉ W := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' v hAuv => ?_⟩
    rw [← hRep u v] at hAuv; rw [← hRep u' v]
    apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u' v) _ C.output houtW hAuv
    intro i hi hiW hx
    rw [repInput_getD u v i hi] at hx
    rw [repInput_getD u' v i hi]
    split_ifs at hx ⊢ with h1
    · have heq : (⟨i, h1⟩ : Fin n) = u := decide_eq_true_eq.mp hx
      exact absurd (congrArg Fin.val heq ▸ hiW) huW
    · exact hx
  have hUc_le : Uc.card ≤ minC := by
    refine le_trans (Finset.card_le_card ?_) hminC
    intro v hv
    have hvW : n + v.val ∉ W := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' u hAuv => ?_⟩
    rw [← hRep u v] at hAuv; rw [← hRep u v']
    apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u v') _ C.output houtW hAuv
    intro i hi hiW hx
    rw [repInput_getD u v i hi] at hx
    rw [repInput_getD u v' i hi]
    split_ifs at hx ⊢ with h1
    · exact hx
    · have heq : (⟨i - n, by omega⟩ : Fin m) = v := decide_eq_true_eq.mp hx
      have hi_eq : i = n + v.val := by have := congrArg Fin.val heq; dsimp at this; omega
      exact absurd (hi_eq ▸ hiW) hvW
  have hsum_ge : W.card - 1 ≤ ∑ u ∈ W, inDeg u := by
    calc W.card - 1 = (W.erase C.output).card := by omega
      _ = ∑ _u ∈ W.erase C.output, 1 := by simp
      _ ≤ ∑ u ∈ W.erase C.output, inDeg u := Finset.sum_le_sum hdeg_pos
      _ ≤ ∑ u ∈ W, inDeg u := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  omega

theorem three_levels : ∀ n k a b : ℕ, k = 3 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s := by
  intro n k a b hk t ht _ _ ha hb s hs
  let A : Fin n → Fin n → Bool := fun u v => decide (v.val < t u)
  have hr : (Finset.univ.filter fun u : Fin n => ∀ u' v, A u v = true → A u' v = true).card ≤ a := by
    rw [← ha]
    apply Finset.card_le_card
    intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' => ?_⟩
    have h := (Finset.mem_filter.mp hu).2
    by_contra! hlt
    let v : Fin n := ⟨t u', lt_of_lt_of_le hlt (ht u).2⟩
    have hbad := h u' v (by simpa [A,v] using hlt)
    simp [A,v] at hbad
  have hc : (Finset.univ.filter fun v : Fin n => ∀ v' u, A u v = true → A u v' = true).card ≤ b := by
    rw [← hb]
    apply Finset.card_le_card
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' => Finset.card_le_card ?_⟩
    intro u hu
    have h := (Finset.mem_filter.mp hv).2 v' u
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [A] using h (by simpa [A] using (Finset.mem_filter.mp hu).2)⟩
  have h := mono_bound A hr hc hs
  omega

end PEqualNP.Outside.L_meta_19456_aux

theorem PEqualNP.Outside.L_meta_19456_upto_five : ∀ n k a b : ℕ, 3 ≤ k → k ≤ 5 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s := by
  intro n k a b hk hle t ht htop hkcard ha hb s hs
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_19456_aux.three_levels n 3 a b rfl t ht htop hkcard ha hb s hs
  · apply PaidChainProjection.lift_staircase_lower n 4 a b hk t ht htop hkcard ha hb s hs
    exact PEqualNP.Outside.L_meta_19456_stair_four_lower
  · apply PaidChainProjection.lift_staircase_lower n 5 a b hk t ht htop hkcard ha hb s hs
    exact PEqualNP.Outside.L_meta_19456_stair_five_lower
