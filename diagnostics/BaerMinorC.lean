import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9743.Baer
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

def anyRead (pins : Finset (Fin n)) (g : Gate) : Bool :=
  decide (∃ i ∈ pins, reads i.val g = true)

def OnlyAO (gs : List Gate) := ∀ g∈gs,g.op=.and ∨ g.op=.or
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
    OnlyAO gs → OnlyAO acc.2 → OnlyAO (elim n gs acc).2 := by
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

theorem eliminateSet (pins : Finset (Fin n)) (bank : List (Option (Fin m))) (C : Circuit)
    (mono : Monotone2 C) (absent : ∀ i ∈ pins, bank[i.val]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + C.gates.countP (anyRead pins) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  have fan : FanInTwo C := by
    intro g hg; obtain ⟨h,l⟩ := mono g hg
    exact ⟨h.imp_right Or.inl,l⟩
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
  have ao : OnlyAO acc.2 := by
    apply elim_mono m gs _ _ (by simp [OnlyAO])
    intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    rcases (mono t ht).1 with e|e <;> cases t with | mk op inputs => cases e <;> simp [normGate]
  cases hout : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, (fun g hg => ⟨ao g hg,(elim_ok m gs _ (by simp) g hg).2⟩), count, fun x => ?_⟩
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


theorem same_without (pins : Finset (Fin n)) (gs : List Gate)
    (avoid : ∀ g∈gs,∀ i∈pins,i.val∉g.inputs)
    (x y : List Bool) (lx : n≤x.length) (len : x.length=y.length)
    (hx : ∀ i, (∀ p∈pins,p.val≠i) → x.getD i false=y.getD i false) :
    ∀ i, (∀ p∈pins,p.val≠i) → (wiresFrom gs x).getD i false=(wiresFrom gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact hx
  | cons g gs ih =>
    have sig : (g.inputs.map fun i => x.getD i false)=g.inputs.map fun i => y.getD i false := by
      apply List.map_congr_left; intro i hi
      apply hx; intro p hp eq; exact avoid g (by simp) p hp (eq ▸ hi)
    let z := g.op.eval (g.inputs.map fun i => x.getD i false)
    change ∀ i, _ → (wiresFrom gs (x++[z])).getD i false=(wiresFrom gs (y++[_])).getD i false
    rw [←sig]
    apply ih (fun t ht => avoid t (by simp [ht])) _ _ (by simp;omega) (by simp [len])
    intro i hi
    by_cases eq : i=x.length
    · simp [eq,len,z,List.getD_eq_getElem?_getD]
    · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]; exact hx i hi

/-- A paid gate is lost when two physical inputs distinguish the cut, and a surviving
positive input has zero on every bank port selected for pinning. -/
theorem mustRead (pins : Finset (Fin n)) (C : Circuit) (mono : Monotone2 C)
    (x y z : Fin n → Bool) (eq : ∀ i, i∉pins → x i=y i)
    (sep : C.eval (List.ofFn x)≠C.eval (List.ofFn y))
    (nilOn : ∀ i∈pins,z i=false) (yes : C.eval (List.ofFn z)=true) :
    0<C.gates.countP (anyRead pins) := by
  by_contra! none
  have noRead (g : Gate) (hg : g∈C.gates) : anyRead pins g=false := by
    by_contra! h
    have pos := (List.countP_pos_iff.mpr ⟨g,hg,by simpa using h⟩ : 0<C.gates.countP (anyRead pins))
    omega
  have avoid : ∀ g∈C.gates,∀ i∈pins,i.val∉g.inputs := by
    intro g hg i hi mem
    have norm : normGate g=g := by rcases (mono g hg).1 with e|e <;> cases g with | mk op ins => cases e <;> rfl
    have r : reads i.val g=true := by simpa [reads,norm] using mem
    have rhs : anyRead pins g=true := decide_eq_true (show ∃ p∈pins, reads p.val g=true from ⟨i,hi,r⟩)
    rw [noRead g hg] at rhs; contradiction
  by_cases raw : ∃ p∈pins,p.val=C.output
  · obtain ⟨p,hp,out⟩ := raw
    have pre := wiresFrom_prefix C.gates (List.ofFn z)
    obtain ⟨t,ht,_⟩ := pre
    change (wiresFrom C.gates (List.ofFn z)).getD C.output false=true at yes
    rw [ht,←out,List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn] at yes
    exact Bool.noConfusion ((nilOn p hp).symm.trans yes)
  · apply sep
    apply same_without pins C.gates avoid _ _ (by simp) (by simp) _ C.output (fun p hp e => raw ⟨p,hp,e⟩)
    intro i hi
    by_cases h : i<n
    · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
      simpa only [List.getElem_ofFn] using eq ⟨i,h⟩ (fun m => hi ⟨i,h⟩ m rfl)
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
end PEqualNP.Outside.L_meta_9743.Baer


namespace PEqualNP.Outside.L_meta_9743.Panel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Raw := Fin 27
abbrev Port := Fin 332
def masks : List ℕ := [0,1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,16512,17408,18432,20480,32768,32896,33024,33792,40960,49152,50176,65536,65664,66048,69632,73728,81920,82048,98304,106496,131072,131200,132096,133120,135168,163840,163968,196608,200704,262144,262656,263168,264192,270336,278528,279552,294912,295936,311296,312320,327680,328192,393216,395264,524288,524416,524544,525312,532480,540672,540800,589824,589952,606208,606336,655360,656384,786432,794624,1048576,1048704,1049088,1052672,1056768,1064960,1069056,1081344,1081472,1179648,1179776,1212416,1212544,1310720,1318912,1572864,1581056,1835008,1843200,2097152,2097280,2097408,2097664,2099200,2113536,2113664,2129920,2130176,2162688,2162816,2179072,2179200,2228224,2230272,2359296,2361344,2490368,2492416,2621440,2621568,2637824,2637952,2686976,2687104,2703360,2703488,3145728,3146240,4194304,4194432,4194560,4194816,4196352,4210688,4212736,4227072,4227200,4259840,4260352,4325376,4325504,4358144,4358272,4456448,4456960,4521984,4522496,4718592,4718848,5242880,5243008,5275648,5275776,5373952,5374080,5406720,5406848,8388608,8388864,8390656,8392704,8396800,8404992,8409088,8421376,8429568,8454144,8462336,8486912,8495104,8519680,8521728,8650752,8652800,8781824,8783872,8912896,8913152,9437184,9441280,9453568,9457664,10485760,10487808,10616832,10618880,10747904,10749952,10878976,10881024,12582912,12583168,13107200,13107456,16777216,16777472,16777728,16778240,16781312,16793600,16797696,16809984,16810240,16842752,16843264,16908288,16909312,17039360,17039872,17104896,17105408,17301504,17302528,17432576,17433600,17825792,17829888,17842176,17846272,18874368,18874624,18907136,18907392,20971520,20972032,21037056,21037568,21233664,21234176,21299200,21299712,25165824,25169920,25182208,25186304,26214400,26218496,26230784,26234880,33554432,33554688,33556480,33558528,33562624,33570816,33572864,33587200,33587456,33619968,33624064,33685504,33689600,33751040,33755136,33816576,33824768,34078720,34086912,34340864,34349056,34603008,34611200,34865152,34873344,35127296,35135488,35389440,35397632,35651584,35651840,35684352,35684608,37748736,37750784,37765120,37767168,50331648,50331904,50364416,50364672,52428800,52429056,52461568,52461824,67108864,67109376,67109888,67110912,67117056,67125248,67127296,67141632,67149824,67174400,67182592,67207168,67215360,67239936,67240960,67633152,67634176,67764224,67765248,68157440,68157952,69206016,69206528,70254592,70255104,71303168,71305216,71319552,71321600,75497472,75505664,75530240,75538432,75563008,75571200,75595776,75603968,83886080,83887104,84017152,84018176,84410368,84411392,84541440,84542464,100663296,100665344,100679680,100681728,104857600,104859648,104873984,104876032]
def low : List ℕ := [134061188,133637536,133051024,133962884,66596354,133178784,132133520,125832128,125832128,83900680,100669185,67123464,11778]
def high : List ℕ := [134077572,133670304,133116560,134093956,66858498,133703072,133182096,127929280,130026432,92289288,117446401,100677896,67120642]
def signal (i : Port) (j : Raw) := (masks.getD i.val 0).testBit j.val
def board (x : Raw→Bool) (i : Port) := decide (∃ j : Raw,signal i j=true ∧ x j=true)
def targetEdges : List (ℕ×ℕ) := [(0,7),(0,11),(0,13),(0,24),(1,7),(1,8),(1,12),(1,18),(1,26),(2,8),(2,9),(2,13),(2,14),(2,17),(3,7),(3,9),(3,10),(3,23),(3,25),(4,8),(4,10),(4,11),(4,16),(4,20),(5,9),(5,11),(5,12),(5,15),(5,19),(6,10),(6,12),(6,13),(6,21),(6,22)]
def want (x : Raw→Bool) := ∃ a b : Raw,(a.val,b.val)∈targetEdges ∧ x a=true ∧ x b=true
def word (w : ℕ) (j : Raw) := w.testBit j.val
def lo (k : Fin 13) := word (low.getD k.val 0)
def hi (k : Fin 13) := word (high.getD k.val 0)
def ok (k : ℕ) (x : Raw→Bool) := ∀ j : Raw, 14≤j.val → j.val<14+k → x j=false
def select (k : Fin 13) : Finset Port := Finset.univ.filter (fun i => board (lo k) i≠board (hi k) i)
def alive := word 129
theorem geometry : ∀ k : Fin 13, ok k.val (lo k) ∧ ok k.val (hi k) ∧ ¬want (lo k) ∧ want (hi k) := by
  intro k
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (unfold ok; decide +kernel) | (unfold want; decide +kernel)
theorem retained : want alive ∧ ∀ k : Fin 13,ok (k.val+1) alive := by unfold want ok; decide +kernel
set_option maxHeartbeats 4000000 in
theorem omitted_bits : ∀ k : Fin 13,∀ i : Port,i∈select k → ∀j : Raw,signal i j=true → 14≤j.val ∧ j.val<14+(k.val+1) := by
  decide +kernel
theorem quiet (k : Fin 13) (x : Raw→Bool) (clean : ok (k.val+1) x) (i : Port) (m : i∈select k) : board x i=false := by
  apply decide_eq_false
  rintro ⟨j,e,on⟩
  obtain ⟨a,b⟩ := omitted_bits k i m j e
  rw [clean j a b] at on; contradiction
theorem agree (k : Fin 13) (i : Port) (m : i∉select k) : board (lo k) i=board (hi k) i := by simpa [select] using m
def finalMap (i : Port) : Option (Fin 14) :=
  let j := ([14,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,7,10,11,12,14,7,8,10,13,14,10,14,7,9,12,13,14,7,14,13,14,7,10,11,12,14,7,14,12,14,9,10,11,13,14,10,14,10,14,10,14,9,14,11,14,7,8,10,13,14,7,14,7,14,7,14,10,14,13,14,7,9,12,13,14,12,14,7,14,7,14,7,14,13,14,13,14,13,14,7,8,9,11,14,7,14,8,14,7,14,7,14,11,14,11,14,11,14,7,14,7,14,7,14,7,14,9,14,7,8,9,11,14,11,14,7,14,9,14,7,14,7,14,9,14,9,14,8,14,7,14,7,14,7,14,7,14,8,11,12,13,14,12,14,13,14,13,14,13,14,11,14,11,14,11,14,8,14,12,14,12,14,11,14,11,14,11,14,11,14,8,14,8,14,8,9,10,12,14,12,14,8,14,9,14,10,14,9,14,9,14,10,14,10,14,12,14,12,14,8,14,8,14,9,14,9,14,9,14,9,14,12,14,12,14,12,14,12,14,8,11,12,13,14,11,14,8,14,12,14,12,14,12,14,13,14,13,14,13,14,13,14,13,14,13,14,13,14,8,14,8,14,11,14,11,14,8,14,8,14,8,14,8,14,9,10,11,13,14,11,14,13,14,13,14,13,14,10,14,10,14,10,14,9,14,9,14,9,14,11,14,11,14,13,14,13,14,13,14,13,14,10,14,10,14,10,14,10,14,11,14,11,14,11,14,11] : List ℕ).getD i.val 14
  if h : j<14 then some ⟨j,h⟩ else none
theorem retained_port : ∀ i : Port,∀ j : Fin 14,signal i ⟨j.val,by omega⟩=true ↔ finalMap i=some j := by decide +kernel
def lift (x : Fin 14→Bool) (j : Raw) := if h : j.val<14 then x ⟨j.val,h⟩ else false
theorem final_clean (x : Fin 14→Bool) : ok 13 (lift x) := by intro j lo _; simp [lift,Nat.not_lt.mpr lo]
theorem final_read (x : Fin 14→Bool) (i : Port) : board (lift x) i=(finalMap i).elim false x := by
  cases h : finalMap i with
  | none =>
    apply decide_eq_false
    rintro ⟨j,s,on⟩
    by_cases b : j.val<14
    · have eq := (retained_port i ⟨j.val,b⟩).mp s; rw [h] at eq; cases eq
    · simp [lift,b] at on
  | some j =>
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro yes
      obtain ⟨r,rr,on⟩ := of_decide_eq_true yes
      by_cases b : r.val<14
      · have eq := (retained_port i ⟨r.val,b⟩).mp rr
        rw [h] at eq
        have id := Option.some.inj eq
        change x j=true
        simpa only [lift,dif_pos b,←id] using on
      · simp [lift,b] at on
    · intro on
      exact decide_eq_true ⟨⟨j.val,by omega⟩,(retained_port i j).mpr h,by simpa [lift,j.isLt] using on⟩
def Fano (x : Fin 14→Bool) := ∃ p l : Fin 7,(p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
theorem final_target : ∀ x : Fin 14→Bool,want (lift x) ↔ Fano x := by
  intro x
  have form : ∀ a b : Fin 14,(a.val,b.val)∈targetEdges ↔ ∃p l : Fin 7,(p=l ∨ p=l+1 ∨ p=l+3) ∧ a=Fin.castAdd 7 p ∧ b=Fin.natAdd 7 l := by decide +kernel
  constructor
  · rintro ⟨a,b,ab,pa,lb⟩
    by_cases da : a.val<14
    · by_cases db : b.val<14
      · obtain ⟨p,l,e,eq,eq'⟩ := (form ⟨a.val,da⟩ ⟨b.val,db⟩).mp ab
        exact ⟨p,l,e,eq ▸ (show x ⟨a.val,da⟩=true from by simpa [lift,da] using pa),eq' ▸ (show x ⟨b.val,db⟩=true from by simpa [lift,db] using lb)⟩
      · simp [lift,db] at lb
    · simp [lift,da] at pa
  · rintro ⟨p,l,e,pa,lb⟩
    let a := Fin.castAdd 7 p
    let b := Fin.natAdd 7 l
    exact ⟨⟨a.val,by have := a.isLt;omega⟩,⟨b.val,by have := b.isLt;omega⟩,(form a b).mpr ⟨p,l,e,rfl,rfl⟩,by simpa only [lift,dif_pos a.isLt] using pa,by simpa only [lift,dif_pos b.isLt] using lb⟩
end PEqualNP.Outside.L_meta_9743.Panel

namespace PEqualNP.Outside.L_meta_9743.Baer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9743.Panel
abbrev Good (k : ℕ) (C : Circuit) := ∀ x, ok k x → (C.eval (List.ofFn (board x))=true ↔ want x)
def clear {n} (S : Finset (Fin n)) (i : Fin n) : Option (Fin n) := if i∈S then none else some i

lemma restricted {n m : ℕ} (r : Fin n→Option (Fin m)) (y : Fin m→Bool) :
    restrict (List.ofFn r) y=List.ofFn (fun i => (r i).elim false y) := by
  simp [restrict,List.map_ofFn,Function.comp_def]
lemma fixed {n} (S : Finset (Fin n)) (y : Fin n→Bool) (h : ∀i∈S,y i=false) :
    restrict (List.ofFn (clear S)) y=List.ofFn y := by
  rw [restricted]
  apply congrArg List.ofFn
  funext i; by_cases hi : i∈S <;> simp [clear,hi,*]

lemma advance (k : Fin 13) (C : Circuit) (hm : Monotone2 C) (good : Good k.val C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1≤C.size ∧ Good (k.val+1) D := by
  obtain ⟨loClean,hiClean,loOff,hiOn⟩ := geometry k
  have sep : C.eval (List.ofFn (board (lo k)))≠C.eval (List.ofFn (board (hi k))) :=
    fun e => loOff ((good _ loClean).mp (e.trans ((good _ hiClean).mpr hiOn)))
  have old {x} (h : ok (k.val+1) x) : ok k.val x := fun j lo top => h j lo (by omega)
  have anyYes := (good alive (old (retained.2 k))).mpr retained.1
  have anyCost := mustRead (select k) C hm (board (lo k)) (board (hi k)) (board alive)
    (agree k) sep (quiet k alive (retained.2 k)) anyYes
  let zero : Raw→Bool := fun _ => false
  have h0 : ok (k.val+1) zero := by simp [ok,zero]
  have no : ¬want zero := by simp [want,zero]
  have off : C.eval (List.ofFn (board zero))=false := by
    apply Bool.eq_false_iff.mpr; exact fun e => no ((good _ (old h0)).mp e)
  have absent (i) (hi : i∈select k) : (List.ofFn (clear (select k)))[i.val]?=some none := by
    simp [clear,hi]
  obtain ⟨D,hD,hcost,ev⟩ := eliminateSet (select k) (List.ofFn (clear (select k))) C hm absent
    ⟨board zero,by rw [fixed _ _ (quiet k zero h0)];exact off⟩
  refine ⟨D,hD,by omega,?_⟩
  intro x hx
  rw [ev,fixed _ _ (quiet k x hx)]
  exact good x (old hx)

theorem residual (C : Circuit) (mono : Monotone2 C) (correct : Good 0 C) :
    ∃ D : Circuit,Monotone2 D ∧ D.size+13≤C.size ∧ ∀ x : Fin 14→Bool,D.eval (List.ofFn x)=true ↔ Fano x := by
  have prefix (i : ℕ) (hi : i≤13) : ∃ D : Circuit, Monotone2 D ∧ D.size+i≤C.size ∧ Good i D := by
    induction i with
    | zero => exact ⟨C,mono,by simp,correct⟩
    | succ i ih =>
      obtain ⟨A,m,h,g⟩ := ih (by omega)
      obtain ⟨D,md,sz,gd⟩ := advance ⟨i,by omega⟩ A m g
      exact ⟨D,md,by omega,gd⟩
  obtain ⟨A,ma,ha,ga⟩ := prefix 13 le_rfl
  have eq (x : Fin 14→Bool) : restrict (List.ofFn finalMap) x=List.ofFn (board (lift x)) := by
    rw [restricted];apply congrArg List.ofFn;funext i;exact (final_read x i).symm
  let blank : Fin 14→Bool := fun _ => false
  have off : A.eval (restrict (List.ofFn finalMap) blank)=false := by
    rw [eq];apply Bool.eq_false_iff.mpr
    intro e
    have f := (final_target blank).mp ((ga _ (final_clean _)).mp e)
    simpa [Fano,blank] using f
  obtain ⟨D,md,mc,ev⟩ := eliminateSet (∅ : Finset Port) (List.ofFn finalMap) A ma (by simp) ⟨blank,off⟩
  refine ⟨D,md,by omega,?_⟩
  intro x
  rw [ev,eq];exact (ga _ (final_clean x)).trans (final_target x)
end PEqualNP.Outside.L_meta_9743.Baer
