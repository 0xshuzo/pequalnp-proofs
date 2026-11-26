import PEqualNP.Outside.L_meta_517

namespace PEqualNP.Outside.L_meta_18723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
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
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

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

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def reads (pin : ℕ) (g : Gate) : Bool := (normGate g).inputs.contains pin

def restrict (bank : List (Option (Fin m))) (x : Fin m → Bool) : List Bool :=
  bank.map fun p => p.elim false x

def layout (bank : List (Option (Fin m))) : List Stat :=
  bank.map (fun p => p.elim (.inl false) (fun k => .inr k.val))

theorem eliminate_pin (bank : List (Option (Fin m))) (pin : ℕ) (C : Circuit)
    (fan : FanInTwo C) (absent : bank[pin]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (reads pin) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  let initial := layout bank
  let gs := C.gates.map normGate
  let acc := elim m gs (initial, [])
  let S := Finset.univ.filter (fun i : Fin C.gates.length => reads pin (C.gates.get i))
  have cardS : C.gates.countP (reads pin) = S.card := by
    simpa [S] using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) (reads pin)
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  have hp : pin < bank.length := (List.getElem?_eq_some_iff.mp absent).1
  have constant : initial.getD pin (.inl false) = .inl false := by
    simp [initial, layout, List.getD_eq_getElem?_getD, absent]
  have penalty := elim_count m (initial, []) gs normOk (S.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    have member : pin ∈ (normGate (C.gates.get i)).inputs := by simpa [reads] using hr
    refine ⟨normGate (C.gates.get i), ?_, pin, member, ?_, false, ?_⟩
    · simp [gs, i.isLt]
    · have len : initial.length = bank.length := by simp [initial,layout]
      change pin < initial.length + i.val
      omega
    · rw [elim_getD m pin _ gs _ (by simp [initial,layout,hp])]
      exact constant)
  have count : acc.2.length + C.gates.countP (reads pin) ≤ C.size := by
    rw [cardS]
    simpa [acc, gs, Circuit.size, Finset.card_image_of_injective S Fin.val_injective] using penalty
  have inv (x : Fin m → Bool) :
      Inv m (List.ofFn x) (wiresFrom gs (restrict bank x)) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (normOk g hg).1)
    refine ⟨by simp [initial,layout,restrict], ?_⟩
    intro k
    by_cases h : k < bank.length
    · have index := List.getElem?_eq_getElem h
      cases val : bank[k] with
      | none =>
        have eq : bank[k]? = some none := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
      | some i =>
        have eq : bank[k]? = some (some i) := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,
          wiresFrom,i.isLt]
    · have eq : bank[k]? = none := List.getElem?_eq_none (by omega)
      simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
  have eval (x : Fin m → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = C.eval (restrict bank x) := by
    rw [((inv x).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  cases hout : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok m gs _ (by simp), count, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [hout,Stat.val] using eval x
  | inl b =>
    have fixed (x : Fin m → Bool) : b = C.eval (restrict bank x) := by
      simpa only [hout,Stat.val] using eval x
    obtain ⟨x, hx⟩ := hasFalse
    have hb := (fixed x).trans hx
    subst b
    refine ⟨⟨[], m⟩, by simp [FanInTwo], by change 0 + _ ≤ _; omega, fun x => ?_⟩
    change (List.ofFn x).getD m false = _
    simpa using fixed x

def anyRead (pins : Finset (Fin n)) (g : Gate) : Bool :=
  decide (∃ i ∈ pins, reads i.val g = true)

theorem eliminateSet (pins : Finset (Fin n)) (bank : List (Option (Fin m))) (C : Circuit)
    (fan : FanInTwo C) (absent : ∀ i ∈ pins, bank[i.val]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (anyRead pins) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  let initial := layout bank
  let gs := C.gates.map normGate
  let acc := elim m gs (initial, [])
  let S := Finset.univ.filter (fun i : Fin C.gates.length => anyRead pins (C.gates.get i))
  have cardS : C.gates.countP (anyRead pins) = S.card := by
    simpa [S] using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) (anyRead pins)
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  have penalty := elim_count m (initial, []) gs normOk (S.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    obtain ⟨pin, hip, hread⟩ := of_decide_eq_true hr
    have hab := absent pin hip
    have hp : pin.val < bank.length := (List.getElem?_eq_some_iff.mp hab).1
    have constant : initial.getD pin.val (.inl false) = .inl false := by
      simp [initial,layout,List.getD_eq_getElem?_getD,hab]
    have member : pin.val ∈ (normGate (C.gates.get i)).inputs := by simpa [reads] using hread
    refine ⟨normGate (C.gates.get i), ?_, pin.val, member, ?_, false, ?_⟩
    · simp [gs, i.isLt]
    · have len : initial.length = bank.length := by simp [initial,layout]
      change pin.val < initial.length + i.val
      omega
    · rw [elim_getD m pin.val _ gs _ (by simp [initial,layout,hp])]
      exact constant)
  have count : acc.2.length + C.gates.countP (anyRead pins) ≤ C.size := by
    rw [cardS]
    simpa [acc, gs, Circuit.size, Finset.card_image_of_injective S Fin.val_injective] using penalty
  have inv (x : Fin m → Bool) :
      Inv m (List.ofFn x) (wiresFrom gs (restrict bank x)) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (normOk g hg).1)
    refine ⟨by simp [initial,layout,restrict], ?_⟩
    intro k
    by_cases h : k < bank.length
    · have index := List.getElem?_eq_getElem h
      cases val : bank[k] with
      | none =>
        have eq : bank[k]? = some none := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
      | some i =>
        have eq : bank[k]? = some (some i) := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,
          wiresFrom,i.isLt]
    · have eq : bank[k]? = none := List.getElem?_eq_none (by omega)
      simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
  have eval (x : Fin m → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = C.eval (restrict bank x) := by
    rw [((inv x).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  cases hout : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok m gs _ (by simp), count, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [hout,Stat.val] using eval x
  | inl b =>
    have fixed (x : Fin m → Bool) : b = C.eval (restrict bank x) := by
      simpa only [hout,Stat.val] using eval x
    obtain ⟨x, hx⟩ := hasFalse
    have hb := (fixed x).trans hx
    subst b
    refine ⟨⟨[], m⟩, by simp [FanInTwo], by change 0 + _ ≤ _; omega, fun x => ?_⟩
    change (List.ofFn x).getD m false = _
    simpa using fixed x


def graphFn {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any fun e => x e.1 && x e.2

def zeroed {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ S then false else x i

theorem true_expand {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (x : Fin n → Bool) :
    graphFn E (Function.update x v true) = ((graphFn E (zeroed {v,u,w} x) || x u) || x w) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [graphFn, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, h, ha, hb⟩
    by_cases av : a = v
    · subst a
      rcases hn b (Or.inl h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using hb))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using hb)
    by_cases bv : b = v
    · subst b
      rcases hn a (Or.inr h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using ha))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using ha)
    have xa : x a = true := by simpa [Function.update_of_ne av] using ha
    have xb : x b = true := by simpa [Function.update_of_ne bv] using hb
    by_cases au : a = u
    · exact Or.inl (Or.inr (au ▸ xa))
    by_cases bu : b = u
    · exact Or.inl (Or.inr (bu ▸ xb))
    by_cases aw : a = w
    · exact Or.inr (aw ▸ xa)
    by_cases bw : b = w
    · exact Or.inr (bw ▸ xb)
    exact Or.inl (Or.inl ⟨(a,b),h,by simpa [zeroed,av,au,aw] using xa, by simpa [zeroed,bv,bu,bw] using xb⟩)
  · rintro ((⟨⟨a,b⟩,h,ha,hb⟩ | hu') | hw')
    · have lift (i : Fin n) (hi : zeroed {v,u,w} x i = true) : Function.update x v true i = true := by
        by_cases mem : i ∈ ({v,u,w} : Finset (Fin n))
        · simp [zeroed,mem] at hi
        · have nv : i ≠ v := by intro eq; subst i; simp at mem
          simpa [zeroed,mem,Function.update_of_ne nv] using hi
      exact ⟨(a,b),h,lift a ha,lift b hb⟩
    · rcases hu with h | h
      · exact ⟨(v,u),h,by simp,by simpa [Function.update_of_ne vu.symm] using hu'⟩
      · exact ⟨(u,v),h,by simpa [Function.update_of_ne vu.symm] using hu',by simp⟩
    · rcases hw with h | h
      · exact ⟨(v,w),h,by simp,by simpa [Function.update_of_ne vw.symm] using hw'⟩
      · exact ⟨(w,v),h,by simpa [Function.update_of_ne vw.symm] using hw',by simp⟩

def addPin (n : ℕ) (D : Circuit) (i : Fin n) : Circuit :=
  ⟨D.gates ++ [⟨.or,[D.output,i.val]⟩], n+D.size⟩

theorem addPin_size (D : Circuit) (i : Fin n) : (addPin n D i).size = D.size+1 := by
  simp [addPin,Circuit.size]

theorem addPin_fan (D : Circuit) (i : Fin n) (h : FanInTwo D) : FanInTwo (addPin n D i) := by
  intro g hg
  simp only [addPin,List.mem_append,List.mem_singleton] at hg
  rcases hg with hv | rfl
  · exact h g hv
  · simp

theorem addPin_eval (D : Circuit) (i : Fin n) (x : Fin n → Bool) :
    (addPin n D i).eval (List.ofFn x) = (D.eval (List.ofFn x) || x i) := by
  let W := wiresFrom D.gates (List.ofFn x)
  have len : W.length = n+D.size := by simp [W,length_wiresFrom,Circuit.size]
  have input : W.getD i.val false = x i := by
    obtain ⟨t,h,_⟩ := wiresFrom_prefix D.gates (List.ofFn x)
    dsimp [W]
    rw [h,List.getD_append _ _ _ _ (by simpa using i.isLt)]
    simp
  change (wiresFrom (D.gates++[⟨.or,[D.output,i.val]⟩]) (List.ofFn x)).getD (n+D.size) false = _
  rw [wiresFrom_append]
  change (W ++ [_]).getD (n+D.size) false = _
  rw [← len, getD_snoc_eq]
  change GateOp.or.eval [W.getD D.output false,W.getD i.val false] = _
  have old : W.getD D.output false = D.eval (List.ofFn x) := rfl
  rw [input,old]
  simp [GateOp.eval]

theorem rebuild {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n) (C D : Circuit)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (hd : FanInTwo D) (sz : D.size + 6 ≤ C.size)
    (mem : ∀ x, D.eval (List.ofFn x) = graphFn E (zeroed {v,u,w} x)) :
    ∃ T : Circuit, FanInTwo T ∧ T.size + 4 ≤ C.size ∧
      ∀ x, T.eval (List.ofFn x) = graphFn E (Function.update x v true) := by
  refine ⟨addPin n (addPin n D u) w, addPin_fan _ _ (addPin_fan _ _ hd), ?_, ?_⟩
  · simpa only [addPin_size, Nat.add_assoc] using sz
  · intro x
    rw [addPin_eval,addPin_eval,mem,true_expand E v u w vu vw hu hw hn]

theorem zeroedReaders (E : List (Fin n × Fin n)) (pins : Finset (Fin n)) (C : Circuit)
    (fan : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = graphFn E x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (anyRead pins) ≤ C.size ∧
      ∀ x, D.eval (List.ofFn x) = graphFn E (zeroed pins x) := by
  classical
  let f (i : Fin n) : Option (Fin n) := if i ∈ pins then none else some i
  let bank := List.ofFn f
  have pull (x : Fin n → Bool) : restrict bank x = List.ofFn (zeroed pins x) := by
    simp only [restrict,bank,List.map_ofFn]
    congr 1
    funext i
    by_cases hi : i ∈ pins <;> simp [Function.comp_def,f,zeroed,hi]
  have hnone (i : Fin n) (hi : i ∈ pins) : bank[i.val]? = some none := by simp [bank,f,hi]
  have hfalse : ∃ x : Fin n → Bool, C.eval (restrict bank x) = false := by
    refine ⟨fun _ => false, ?_⟩
    rw [pull,comp]
    simp [graphFn,zeroed]
  obtain ⟨D,hd,hs,he⟩ := eliminateSet pins bank C fan hnone hfalse
  exact ⟨D,hd,hs,fun x => by rw [he,pull,comp]⟩

theorem sixReaders (E : List (Fin n × Fin n)) (v u w : Fin n) (C : Circuit)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (fan : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = graphFn E x)
    (six : 6 ≤ C.gates.countP (anyRead {v,u,w})) :
    ∃ T : Circuit, FanInTwo T ∧ T.size + 4 ≤ C.size ∧
      ∀ x, T.eval (List.ofFn x) = graphFn E (Function.update x v true) := by
  obtain ⟨D,hd,hs,he⟩ := zeroedReaders E {v,u,w} C fan comp
  exact rebuild E v u w C D vu vw hu hw hn hd (by omega) he

theorem threeReaders (E : List (Fin n × Fin n)) (v : Fin n) (C : Circuit)
    (fan : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = graphFn E x)
    (three : 3 ≤ C.gates.countP (anyRead {v})) :
    ∃ T : Circuit, FanInTwo T ∧ T.size + 3 ≤ C.size ∧
      ∀ x, T.eval (List.ofFn x) = graphFn E (Function.update x v false) := by
  obtain ⟨D,hd,hs,he⟩ := zeroedReaders E {v} C fan comp
  refine ⟨D,hd,by omega,fun x => ?_⟩
  rw [he]
  congr 1
  funext k
  by_cases eq : k=v
  · subst k; simp [zeroed]
  · simp [zeroed,eq,Function.update_of_ne eq]


def evalGate (g : Gate) (a : List Bool) := g.op.eval (g.inputs.map fun k => a.getD k false)
def advance (a : List Bool) (g : Gate) := a ++ [evalGate g a]
def near (v : ℕ) (a b : List Bool) := a.length=b.length ∧ ∀ j, j ≠ v → a.getD j false = b.getD j false

theorem nearStep (v : ℕ) (a b : List Bool) (g : Gate) (h : near v a b)
    (same : evalGate g a = evalGate g b) : near v (advance a g) (advance b g) := by
  obtain ⟨len,eq⟩ := h
  refine ⟨by simp [advance,len], ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [advance, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [advance,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),len,same]

theorem rawPin {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    (C.gates.foldl advance (List.ofFn x)).getD i.val false = x i := by
  have aux (gs : List Gate) (s : List Bool) (hi : i.val < s.length) :
      (gs.foldl advance s).getD i.val false = s.getD i.val false := by
    induction gs generalizing s with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl advance (advance s g)).getD i.val false = _
      rw [ih _ (by simp [advance]; omega)]
      exact List.getD_append _ _ _ _ hi
  rw [aux C.gates _ (by simpa using i.isLt)]
  simp


def PriceModel (n t : Nat) (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ t ∧ ∀ x, C.eval (List.ofFn x) = F x

theorem peelLiteral {n : ℕ} (v : Fin n) (F : (Fin n → Bool) → Bool)
    (silent : ∀ x, F (Function.update x v false) = F x)
    (pt : ∃ x, F x=true) (pf : ∃ x, F x=false) (C : Circuit) (fan : FanInTwo C)
    (rep : ∀ x, C.eval (List.ofFn x) = (F x || x v)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size+1 ≤ C.size ∧ ∀ x, D.eval (List.ofFn x) = F x := by
  classical
  let f (i : Fin n) : Option (Fin n) := if i=v then none else some i
  let bank := List.ofFn f
  have absent : bank[v.val]? = some none := by simp [bank,f]
  have pull (x : Fin n → Bool) : restrict bank x = List.ofFn (Function.update x v false) := by
    simp only [restrict,bank,List.map_ofFn]
    congr 1
    funext i
    by_cases eq : i=v
    · subst i; simp [Function.comp_def,f]
    · simp [Function.comp_def,f,eq,Function.update_of_ne eq]
  obtain ⟨x0,h0⟩ := pf
  obtain ⟨x1,h1⟩ := pt
  have hasFalse : ∃ x, C.eval (restrict bank x) = false := by
    refine ⟨x0,?_⟩
    rw [pull,rep,silent,h0]
    simp
  have out : C.output ≠ v.val := by
    intro ho
    let p := Function.update x1 v false
    have val := rep p
    change (C.gates.foldl advance (List.ofFn p)).getD C.output false = _ at val
    rw [ho, rawPin] at val
    simp [p,silent,h1] at val
  have read : 0 < C.gates.countP (reads v.val) := by
    by_contra hn
    have hz : C.gates.countP (reads v.val) = 0 := by omega
    have quiet (g : Gate) (hg : g ∈ C.gates) : reads v.val g = false := by
      by_contra h
      have ht : reads v.val g = true := by cases e : reads v.val g <;> simp_all
      have pos : 0 < C.gates.countP (reads v.val) := List.countP_pos_iff.mpr ⟨g,hg,ht⟩
      omega
    let a := Function.update x0 v false
    let b := Function.update x0 v true
    have eq : near v.val (List.ofFn a) (List.ofFn b) := by
      refine ⟨by simp, ?_⟩
      intro j hj
      by_cases bound : j < n
      · let k : Fin n := ⟨j,bound⟩
        have kv : k ≠ v := by intro e; exact hj (congrArg Fin.val e)
        change (List.ofFn a).getD k.val false = (List.ofFn b).getD k.val false
        simp [a,b,Function.update_of_ne kv]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound)]
    have eqfold (gs : List Gate) (as bs : List Bool) (nearby : near v.val as bs)
        (q : ∀ g ∈ gs, reads v.val g = false) : near v.val (gs.foldl advance as) (gs.foldl advance bs) := by
      induction gs generalizing as bs with
      | nil => exact nearby
      | cons g gs ih =>
        have same : evalGate g as = evalGate g bs := by
          unfold evalGate
          rw [← normGate_eval g (fun i => as.getD i false), ← normGate_eval g (fun i => bs.getD i false)]
          congr 1
          apply List.map_congr_left
          intro j hj
          apply nearby.2 j
          rintro rfl
          have hl : reads v.val g = true := List.contains_iff_mem.mpr hj
          rw [q g (by simp)] at hl
          contradiction
        exact ih _ _ (nearStep v.val as bs g nearby same) (fun z hz => q z (by simp [hz]))
    have equal : C.eval (List.ofFn a) = C.eval (List.ofFn b) := (eqfold _ _ _ eq quiet).2 _ out
    rw [rep,rep] at equal
    simp [a,b,silent,h0] at equal
  obtain ⟨D,hd,hs,he⟩ := eliminate_pin bank v.val C fan absent hasFalse
  refine ⟨D,hd,by omega,fun x => ?_⟩
  rw [he,pull,rep,silent]
  simp

theorem literalEquivalence (v : Fin n) (F : (Fin n → Bool) → Bool)
    (silent : ∀ x, F (Function.update x v false) = F x)
    (pt : ∃ x, F x=true) (pf : ∃ x, F x=false) (s : ℕ) :
    PriceModel n (s+1) (fun x => F x || x v) ↔ PriceModel n s F := by
  constructor
  · rintro ⟨C,hm,hs,hr⟩
    obtain ⟨D,hd,hle,he⟩ := peelLiteral v F silent pt pf C hm hr
    exact ⟨D,hd,by omega,he⟩
  · rintro ⟨D,hd,hle,he⟩
    exact ⟨addPin n D v,addPin_fan D v hd,by rw [addPin_size]; omega,fun x => by rw [addPin_eval,he]⟩


theorem zeroedSilent (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (x : Fin n → Bool) :
    zeroed S (Function.update x i false) = zeroed S x := by
  funext j
  by_cases mem : j ∈ S
  · simp [zeroed,mem]
  · have ne : j ≠ i := by intro h; exact mem (h.symm ▸ hi)
    simp [zeroed,mem,Function.update_of_ne ne]

theorem truePrice (E : List (Fin n × Fin n)) (v u w : Fin n) (s : ℕ)
    (vu : v ≠ u) (vw : v ≠ w) (uw : u ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (edge : ∃ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ≠ w ∧ e.2 ≠ w) :
    PriceModel n (s+2) (fun x => graphFn E (Function.update x v true)) ↔
    PriceModel n s (fun x => graphFn E (zeroed {v,u,w} x)) := by
  classical
  let S : Finset (Fin n) := {v,u,w}
  let F (x : Fin n → Bool) := graphFn E (zeroed S x)
  have fu (x : Fin n → Bool) : F (Function.update x u false) = F x := by
    unfold F; rw [zeroedSilent S u (by simp [S])]
  have fw (x : Fin n → Bool) : F (Function.update x w false) = F x := by
    unfold F; rw [zeroedSilent S w (by simp [S])]
  have pf : F (fun _ => false) = false := by simp [F,graphFn,zeroed]
  have pt : F (fun _ => true) = true := by
    obtain ⟨⟨a,b⟩,he,av,bv,au,bu,aw,bw⟩ := edge
    change a ≠ v at av
    change b ≠ v at bv
    change a ≠ u at au
    change b ≠ u at bu
    change a ≠ w at aw
    change b ≠ w at bw
    apply List.any_eq_true.mpr
    exact ⟨(a,b),he,by simp [zeroed,S,av,bv,au,bu,aw,bw]⟩
  let H (x : Fin n → Bool) := F x || x u
  have hs (x : Fin n → Bool) : H (Function.update x w false) = H x := by simp [H,fw,Function.update_of_ne uw]
  have ht : H (fun _ => true) = true := by simp [H]
  have hf : H (fun _ => false) = false := by simp [H,pf]
  have same : (fun x => graphFn E (Function.update x v true)) = (fun x => H x || x w) := by
    funext x; exact true_expand E v u w vu vw hu hw hn x
  rw [same]
  exact (literalEquivalence w H hs ⟨_,ht⟩ ⟨_,hf⟩ (s+1)).trans (literalEquivalence u F fu ⟨_,pt⟩ ⟨_,pf⟩ s)

end PEqualNP.Outside.L_meta_18723

namespace PetersenFaces
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18723
set_option maxHeartbeats 4000000

def es : List (Fin 10 × Fin 10) :=
  [(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)

def lift (p : Fin 10 → Option (Fin 7)) (x : Fin 7 → Bool) (i : Fin 10) :=
  (p i).elim false x

theorem corePrice (v u w : Fin 10) (p : Fin 10 → Option (Fin 7))
    (absent : p v = none)
    (same : ∀ x, graphFn es (zeroed {v,u,w} (lift p x)) = theta x) :
    ¬ PriceModel 10 10 (fun x => graphFn es (zeroed {v,u,w} x)) := by
  rintro ⟨C,fan,size,sem⟩
  let bank := List.ofFn p
  have pull (x : Fin 7 → Bool) : restrict bank x = List.ofFn (lift p x) := by
    simp [restrict,bank,List.map_ofFn,Function.comp_def,lift]
  have noneAt : bank[v.val]? = some none := by simp [bank,absent]
  have calc (x : Fin 7 → Bool) : C.eval (restrict bank x) = theta x := by
    rw [pull,sem,same]
  have hf : ∃ x : Fin 7 → Bool, C.eval (restrict bank x) = false :=
    ⟨fun _ => false, by rw [calc]; rfl⟩
  obtain ⟨D,fd,sd,ev⟩ := eliminate_pin bank v.val C fan noneAt hf
  have h : HasCircuitSize 7 theta 10 := ⟨D,fd,by omega,fun x => (ev x).trans (calc x)⟩
  have bad := PEqualNP.Outside.L_meta_517 10 h
  omega

def m0 : Fin 10 → Option (Fin 7) := ![none, some 2, some 0, some 3, none, none, some 1, some 5, some 4, some 6]

theorem price0 : ¬ PriceModel 10 12 (fun x => graphFn es (Function.update x 0 true)) := by
  have small := corePrice 0 4 5 m0 (by decide) (by
    intro x
    change ((false && false) || ((false && false) || ((x 2 && x 0) || ((x 2 && x 1) || ((x 0 && x 3) || ((x 0 && x 5) || ((x 3 && false) || ((x 3 && x 4) || ((false && x 6) || ((false && x 5) || ((false && x 4) || ((x 1 && x 4) || ((x 1 && x 6) || ((x 5 && x 6) || (false))))))))))))))) = theta x
    simp only [theta, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false,
      Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm])
  intro h
  apply small
  exact (truePrice es 0 4 5 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).mp h

def m1 : Fin 10 → Option (Fin 7) := ![some 2, none, none, some 3, some 0, some 1, none, some 6, some 4, some 5]

theorem price1 : ¬ PriceModel 10 12 (fun x => graphFn es (Function.update x 1 true)) := by
  have small := corePrice 1 2 6 m1 (by decide) (by
    intro x
    change ((x 2 && x 0) || ((x 2 && x 1) || ((false && false) || ((false && false) || ((false && x 3) || ((false && x 6) || ((x 3 && x 0) || ((x 3 && x 4) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 1 && x 4) || ((false && x 4) || ((false && x 5) || ((x 6 && x 5) || (false))))))))))))))) = theta x
    simp only [theta, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false,
      Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm])
  intro h
  apply small
  exact (truePrice es 1 2 6 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).mp h

end PetersenFaces
