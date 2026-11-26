import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23519.Projection
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

def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not
theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    NotFree gs → NotFree acc.2 → NotFree (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem eliminate_pin (bank : List (Option (Fin m))) (pin : ℕ) (C : Circuit)
    (hm : Monotone2 C) (absent : bank[pin]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + C.gates.countP (reads pin) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨h,a⟩ := hm g hg
    rcases h with h | h
    · exact ⟨Or.inl h,a⟩
    · exact ⟨Or.inr (Or.inl h),a⟩
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
  have firstNF : NotFree gs := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hh,_⟩ := hm t ht
    rcases hh with hh | hh <;> simp [normGate,hh]
  have clean : Monotone2 ⟨acc.2,0⟩ := by
    intro g hg
    have h := elim_ok m gs (initial,[]) (by simp) g hg
    have nf := elim_mono m gs (initial,[]) firstNF (by intro t ht; simp at ht) g hg
    rcases h.1 with h1 | h2 | h3
    · exact ⟨Or.inl h1,h.2⟩
    · exact ⟨Or.inr h2,h.2⟩
    · exact (nf h3).elim
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
    refine ⟨⟨acc.2, k⟩, clean, count, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [hout,Stat.val] using eval x
  | inl b =>
    have fixed (x : Fin m → Bool) : b = C.eval (restrict bank x) := by
      simpa only [hout,Stat.val] using eval x
    obtain ⟨x, hx⟩ := hasFalse
    have hb := (fixed x).trans hx
    subst b
    refine ⟨⟨[], m⟩, by simp [Monotone2], by change 0 + _ ≤ _; omega, fun x => ?_⟩
    change (List.ofFn x).getD m false = _
    simpa using fixed x

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => w.getD j false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value g w]

private def AgreeAway (pin : Nat) (a b : List Bool) : Prop :=
  a.length = b.length ∧ pin < b.length ∧
    ∀ j, j ≠ pin → a.getD j false = b.getD j false

private theorem unread_value (g : Gate) (a b : List Bool) (near : AgreeAway pin a b)
    (_legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h : reads pin g = false) : value g a = value g b := by
  unfold value
  rw [← normGate_eval g (fun i => a.getD i false), ← normGate_eval g (fun i => b.getD i false)]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply near.2.2 j
  rintro rfl
  have yes : reads pin g = true := List.contains_iff_mem.mpr hj
  simp [h] at yes

private theorem step_agree (a b : List Bool) (g : Gate) (near : AgreeAway pin a b)
    (same : value g a = value g b) : AgreeAway pin (step a g) (step b g) := by
  obtain ⟨length, bound, eq⟩ := near
  refine ⟨by simp [step,length], by simp [step]; omega, ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [step, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),length,same]

private theorem fold_agree (p : List Gate) (a b : List Bool)
    (near : AgreeAway pin a b) (fan : FanInTwo ⟨p, 0⟩) (silent : ∀ g ∈ p, reads pin g = false) :
    AgreeAway pin (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact near
  | cons g p ih =>
    exact ih _ _ (step_agree a b g near (unread_value g a b near (fan g (by simp)).1 (silent g (by simp))))
      (fun k hk => fan k (by simp [hk])) (fun k hk => silent k (by simp [hk]))


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem boolD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [boolD_snoc_eq]
          have e2 := boolD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'


theorem apart {p : Nat} (a b : List Bool) (hl : a.length=b.length) (hp : p<b.length)
    (diff : ∀ i : Fin a.length, i.val≠p → a.getD i.val false = b.getD i.val false) : AgreeAway p a b := by
  refine ⟨hl,hp,?_⟩
  intro i h
  by_cases hi : i<a.length
  · exact diff ⟨i,hi⟩ h
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

theorem essential (p : Nat) (C : Circuit) (hm : Monotone2 C) (x z y v : List Bool)
    (hx : C.eval x = true) (hy : C.eval y = false) (hv : C.eval v = true)
    (hp : p<v.length) (hraw : v.getD p false = false)
    (near : AgreeAway p x z) (sames : z.length=y.length)
    (smaller : ∀ i : Fin z.length, z.getD i.val false = true → y.getD i.val false = true) :
    0<C.gates.countP (reads p) := by
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨h,a⟩ := hm g hg
    rcases h with h | h
    · exact ⟨Or.inl h,a⟩
    · exact ⟨Or.inr (Or.inl h),a⟩
  have raw : C.output≠p := by
    intro e
    obtain ⟨t,ht,_⟩ := wiresFrom_prefix C.gates v
    change (wiresFrom C.gates v).getD C.output false = true at hv
    rw [e,ht,List.getD_append _ _ _ _ hp,hraw] at hv
    contradiction
  by_contra! no
  have silent : ∀ g ∈ C.gates, reads p g=false := by
    intro g hg
    by_contra! nh
    have h : reads p g=true := by cases eq : reads p g <;> simp_all
    have n := List.countP_pos_iff.mpr ⟨g,hg,h⟩
    omega
  have eq := (fold_agree C.gates x z near (fun g hg => fan g hg) silent).2.2 C.output raw
  have yes : C.eval z=true := eq.symm.trans hx
  have impossible := mono2 C.gates (fun g hg => hm g hg) z y sames (by
    intro i hi
    by_cases lt : i<z.length
    · exact smaller ⟨i,lt⟩ hi
    · rw [List.getD_eq_default _ _ (by omega)] at hi
      contradiction) C.output yes
  change C.eval y = true at impossible
  rw [hy] at impossible
  contradiction

open PEqualNP.Represents

def bank0 : List (Option (Fin 9)) := [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8, none]
def embed0 : Fin 5 → Fin 6 := ![0, 1, 2, 3, 4]
def arr0 (i : Fin 4) (j : Fin 5) (k : Fin 9) : Bool := (oneEach i j).getD k.val false
theorem pairLayout0 : ∀ i j, List.ofFn (arr0 i j)=oneEach i j ∧
    restrict bank0 (arr0 i j) = oneEach i (embed0 j) := by decide +kernel
theorem drop0 (k : Nat) : RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) (k+1) → RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245535 : ℕ).testBit (5 * u.val + v.val)) k := by
  rintro ⟨C,hm,hs,hr⟩
  have hp := essential 9 C hm (oneEach (1:Fin 4) (5:Fin 6)) [false, true, false, false, false, false, false, false, false, false] (oneEach (1:Fin 4) (0:Fin 6)) (oneEach (0:Fin 4) (0:Fin 6))
    (by rw [hr]; decide) (by rw [hr]; decide) (by rw [hr]; decide) (by decide) (by decide)
    (apart _ _ (by decide) (by decide) (by decide +kernel)) (by decide) (by decide +kernel)
  have first : ∀ i j, C.eval (restrict bank0 (arr0 i j)) =
      (fun (u : Fin 4) (v : Fin 5) => (245535 : ℕ).testBit (5 * u.val + v.val)) i j := by
    intro i j
    rw [(pairLayout0 i j).2,hr]
    exact (show ∀ (a : Fin 4) (b : Fin 5), (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) a (embed0 b) = (fun (u : Fin 4) (v : Fin 5) => (245535 : ℕ).testBit (5 * u.val + v.val)) a b by decide +kernel) i j
  obtain ⟨D,md,sm,ev⟩ := eliminate_pin bank0 9 C hm (by decide)
    ⟨arr0 1 0,by rw [first]; decide⟩
  refine ⟨D,md,by omega,?_⟩
  intro i j
  rw [←(pairLayout0 i j).1,ev]
  exact first i j

def bank1 : List (Option (Fin 8)) := [some 0, some 1, some 2, some 3, some 4, some 5, none, some 6, some 7]
def embed1 : Fin 4 → Fin 5 := ![0, 1, 3, 4]
def arr1 (i : Fin 4) (j : Fin 4) (k : Fin 8) : Bool := (oneEach i j).getD k.val false
theorem pairLayout1 : ∀ i j, List.ofFn (arr1 i j)=oneEach i j ∧
    restrict bank1 (arr1 i j) = oneEach i (embed1 j) := by decide +kernel
theorem drop1 (k : Nat) : RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245535 : ℕ).testBit (5 * u.val + v.val)) (k+1) → RepSizeAtMost (fun (u : Fin 4) (v : Fin 4) => (14287 : ℕ).testBit (4 * u.val + v.val)) k := by
  rintro ⟨C,hm,hs,hr⟩
  have hp := essential 6 C hm (oneEach (2:Fin 4) (2:Fin 5)) [false, false, true, false, false, false, false, false, false] (oneEach (2:Fin 4) (4:Fin 5)) (oneEach (0:Fin 4) (0:Fin 5))
    (by rw [hr]; decide) (by rw [hr]; decide) (by rw [hr]; decide) (by decide) (by decide)
    (apart _ _ (by decide) (by decide) (by decide +kernel)) (by decide) (by decide +kernel)
  have first : ∀ i j, C.eval (restrict bank1 (arr1 i j)) =
      (fun (u : Fin 4) (v : Fin 4) => (14287 : ℕ).testBit (4 * u.val + v.val)) i j := by
    intro i j
    rw [(pairLayout1 i j).2,hr]
    exact (show ∀ (a : Fin 4) (b : Fin 4), (fun (u : Fin 4) (v : Fin 5) => (245535 : ℕ).testBit (5 * u.val + v.val)) a (embed1 b) = (fun (u : Fin 4) (v : Fin 4) => (14287 : ℕ).testBit (4 * u.val + v.val)) a b by decide +kernel) i j
  obtain ⟨D,md,sm,ev⟩ := eliminate_pin bank1 6 C hm (by decide)
    ⟨arr1 2 3,by rw [first]; decide⟩
  refine ⟨D,md,by omega,?_⟩
  intro i j
  rw [←(pairLayout1 i j).1,ev]
  exact first i j

def bank2 : List (Option (Fin 7)) := [some 0, some 1, some 2, some 3, some 4, none, some 5, some 6]
def embed2 : Fin 3 → Fin 4 := ![0, 2, 3]
def arr2 (i : Fin 4) (j : Fin 3) (k : Fin 7) : Bool := (oneEach i j).getD k.val false
theorem pairLayout2 : ∀ i j, List.ofFn (arr2 i j)=oneEach i j ∧
    restrict bank2 (arr2 i j) = oneEach i (embed2 j) := by decide +kernel
theorem drop2 (k : Nat) : RepSizeAtMost (fun (u : Fin 4) (v : Fin 4) => (14287 : ℕ).testBit (4 * u.val + v.val)) (k+1) → RepSizeAtMost (fun (u : Fin 4) (v : Fin 3) => (759 : ℕ).testBit (3 * u.val + v.val)) k := by
  rintro ⟨C,hm,hs,hr⟩
  have hp := essential 5 C hm (oneEach (2:Fin 4) (1:Fin 4)) [false, false, true, false, false, false, false, false] (oneEach (2:Fin 4) (3:Fin 4)) (oneEach (0:Fin 4) (0:Fin 4))
    (by rw [hr]; decide) (by rw [hr]; decide) (by rw [hr]; decide) (by decide) (by decide)
    (apart _ _ (by decide) (by decide) (by decide +kernel)) (by decide) (by decide +kernel)
  have first : ∀ i j, C.eval (restrict bank2 (arr2 i j)) =
      (fun (u : Fin 4) (v : Fin 3) => (759 : ℕ).testBit (3 * u.val + v.val)) i j := by
    intro i j
    rw [(pairLayout2 i j).2,hr]
    exact (show ∀ (a : Fin 4) (b : Fin 3), (fun (u : Fin 4) (v : Fin 4) => (14287 : ℕ).testBit (4 * u.val + v.val)) a (embed2 b) = (fun (u : Fin 4) (v : Fin 3) => (759 : ℕ).testBit (3 * u.val + v.val)) a b by decide +kernel) i j
  obtain ⟨D,md,sm,ev⟩ := eliminate_pin bank2 5 C hm (by decide)
    ⟨arr2 2 2,by rw [first]; decide⟩
  refine ⟨D,md,by omega,?_⟩
  intro i j
  rw [←(pairLayout2 i j).1,ev]
  exact first i j
end PEqualNP.Outside.L_meta_23519.Projection


namespace PEqualNP.Outside.L_meta_23519.Quotient

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 64

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 32 := ((x >>> 32) &&& ~~~x).setWidth 32

def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xfff00000000, 0xff00011111111, 0xff0000022222222, 0xf0000000cccccccc, 0xf0f0000f11111111, 0xf00f0f044444444, 0xf0f00aaaaaaaa]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (32 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (32 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 32, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 32) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 64 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 64 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 64, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 64 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 64 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 64 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 64 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 64) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 64 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 3 → Bool := fun (u : Fin 4) (v : Fin 3) => (759 : ℕ).testBit (3 * u.val + v.val)

def posL : List (Fin 4 × Fin 3) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

def negL : List (Fin 4 × Fin 3) :=
  [(1, 0), (2, 2), (3, 1), (3, 2)]

def samp (k : Fin 64) : Fin 4 × Fin 3 :=
  if k.val < 32 then negL.getD (k.val % 4) (0, 0) else posL.getD ((k.val - 32) / 4) (0, 0)

theorem input_rows : ∀ k : Fin 64,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 64, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 64) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem all_front : inputs.sublists.all
    (fun l => decide (8 < l.length) || !(optimized 7 (8 - l.length) l)) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 7)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 7 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 7 l (8 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (8 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  exact Bool.noConfusion hrow

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 3) => (759 : ℕ).testBit (3 * u.val + v.val)) 7) := by
  rintro ⟨C, hm, hs, hr⟩
  exact no_small C hm hs hr

end PEqualNP.Outside.L_meta_23519.Quotient

open PEqualNP.Outside.L_meta_23519.Projection in
theorem PEqualNP.Outside.L_meta_23519 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) 10) := fun h => PEqualNP.Outside.L_meta_23519.Quotient.result (drop2 7 (drop1 8 (drop0 9 h)))
