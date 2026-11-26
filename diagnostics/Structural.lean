import PEqualNP.Defs

namespace Twin3321.Restriction

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

end Twin3321.Restriction

namespace Twin3321.WireEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

end Twin3321.WireEval

namespace Twin3321.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Twin3321.Restriction Twin3321.WireEval

def pull {n m : ℕ} (source : Fin n → Option (Fin m)) (y : Fin m → Bool) (i : Fin n) : Bool :=
  ((source i).map y).getD false

def code {n m : ℕ} (source : Fin n → Option (Fin m)) (i : Fin n) : Stat :=
  match source i with
  | none => Sum.inl false
  | some j => Sum.inr j.val

theorem deleteInput {n m : ℕ} (C : Circuit) (mono : Monotone2 C) (source : Fin n → Option (Fin m))
    (p : Fin n) (removed : source p = none) (reader : ∃ g ∈ C.gates, p.val ∈ g.inputs)
    (rejects : ∃ y, circuitFun n C (pull source y) = false) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun m D = (fun y => circuitFun n C (pull source y)) ∧
      D.size < C.size := by
  let start : List Stat × List Gate := (List.ofFn (code source),[])
  let finish := elim m C.gates start
  have seed (y : Fin m → Bool) : Inv m (List.ofFn y) (List.ofFn (pull source y)) start := by
    refine ⟨by simp [start],?_⟩
    intro i
    by_cases inside : i < n
    · let t : Fin n := ⟨i,inside⟩
      change ((List.ofFn (code source)).getD t.val _).Valid (m+0) ∧
        ((List.ofFn (code source)).getD t.val _).val (List.ofFn y) = (List.ofFn (pull source y)).getD t.val _
      rw [getD_ofFn',getD_ofFn']
      cases h : source t with
      | none => simp [code,h,pull,Stat.Valid,Stat.val]
      | some u => simp [code,h,pull,Stat.Valid,Stat.val,u.isLt]
    · have a : start.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [start]; omega)
      have b : (List.ofFn (pull source y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [a,b]; exact ⟨trivial,rfl⟩
  have known : start.1.getD p.val (Sum.inl false) = Sum.inl false := by
    change (List.ofFn (code source)).getD p.val _ = _
    rw [getD_ofFn']; simp [code,removed]
  have limit := elim_count m p.val C.gates start mono (by simp [start]) ⟨false,known⟩
  have cost : finish.2.length + C.gates.countP (fun g => decide (p.val ∈ g.inputs)) ≤ C.size := by
    simpa [start,finish,Circuit.size] using limit
  obtain ⟨g,hg,read⟩ := reader
  have charge : 0 < C.gates.countP (fun h => decide (p.val ∈ h.inputs)) := by
    by_contra! zero
    exact (List.countP_eq_zero.mp (Nat.le_zero.mp zero) g hg) (decide_eq_true read)
  have short : finish.2.length < C.size := by omega
  let out := finish.1.getD C.output (Sum.inl false)
  have eval (y : Fin m → Bool) :
      out.val (wiresFrom finish.2 (List.ofFn y)) = circuitFun n C (pull source y) :=
    ((inv_elim m (List.ofFn y) (by simp) C.gates _ start mono (seed y)).2 C.output).2
  have legal : ∀ h ∈ finish.2, Ok h := elim_ok m C.gates start (by simp [start])
  cases result : out with
  | inr i =>
    refine ⟨⟨finish.2,i⟩,legal,?_,short⟩
    funext y
    have h := eval y
    rw [result] at h
    exact h
  | inl b =>
    have const (y : Fin m → Bool) : b = circuitFun n C (pull source y) := by
      have h := eval y
      rw [result] at h
      exact h
    obtain ⟨y,hy⟩ := rejects
    have off : b = false := (const y).trans hy
    refine ⟨⟨[],m⟩,by intro h mem; simp at mem,?_,by change 0 < C.size; omega⟩
    funext z
    change (List.ofFn z).getD m false = _
    rw [List.getD_eq_default _ _ (by simp)]
    exact off.symm.trans (const z)

theorem read_of_separation {n : ℕ} (C : Circuit) (mono : Monotone2 C) (p : Fin n)
    (out : C.output ≠ p.val) (x y : Fin n → Bool)
    (ordered : ∀ t, t ≠ p → x t = true → y t = true)
    (on : circuitFun n C x = true) (off : circuitFun n C y = false) :
    ∃ g ∈ C.gates, p.val ∈ g.inputs := by
  by_contra! unread
  have wires (w : ℕ) : w ≠ p.val → val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ne
      by_cases raw : w < n
      · let t : Fin n := ⟨w,raw⟩
        rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
        simpa [t,raw] using ordered t (fun eq => ne (congrArg Fin.val eq))
      by_cases past : n+C.gates.length ≤ w
      · rw [val_ge List.length_ofFn past]; simp
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have valid : k < C.gates.length := by omega
      rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn valid]
      apply opMono_imp _ (mono_ops mono k valid)
      intro i hi
      by_cases earlier : i < n+k
      · simp only [earlier,ite_true]
        exact ih i earlier (fun eq => unread _ (gateAt_mem valid) (eq ▸ hi))
      · simp [earlier]
  have contradiction := wires C.output out on
  change circuitFun n C y = true at contradiction
  simp [off] at contradiction
end Twin3321.DeleteInput
namespace Twin3321.Strict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev Ref := Bool ⊕ ℕ

def fixed : Ref := .inl false

def value (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr i => w.getD i false

def valid (n : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr i => i < n

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step]
    omega

lemma run_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

def allowed (g : Gate) : Prop := g.op = .and ∨ g.op = .or

def binaryGate (g : Gate) : Prop := allowed g ∧ g.inputs.length = 2

def back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

lemma back_append {n : ℕ} {a b : List Gate} (ha : back n a)
    (hb : back (n + a.length) b) : back n (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi
    exact ha j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have hb' := hb (j - a.length) (by simp at hj; omega) i hi
    omega

def binary (op : GateOp) (neutral : Bool) (n : ℕ) (a b : Ref) : Ref × List Gate :=
  match a, b with
  | .inl c, _ => (if c = neutral then b else .inl c, [])
  | _, .inl c => (if c = neutral then a else .inl c, [])
  | .inr i, .inr j => (.inr n, [⟨op, [i, j]⟩])

def emit (op : GateOp) (n : ℕ) (rs : List Ref) : Ref × List Gate :=
  match op, rs with
  | .and, [] => (.inl true, [])
  | .or, [] => (.inl false, [])
  | .and, [a] | .or, [a] => (a, [])
  | .and, a :: b :: _ => binary .and true n a b
  | .or, a :: b :: _ => binary .or false n a b
  | _, _ => (fixed, [])

lemma emit_ok (op : GateOp) (n : ℕ) (rs : List Ref)
    (hop : op = .and ∨ op = .or) (hl : rs.length ≤ 2)
    (hv : ∀ r ∈ rs, valid n r) :
    let e := emit op n rs
    e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
      back n e.2 ∧
      ∀ w : List Bool, w.length = n →
        valid (run e.2 w).length e.1 ∧
          value (run e.2 w) e.1 = op.eval (rs.map (value w)) := by
  dsimp only
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [emit, back, valid, value, GateOp.eval]
  · rcases hop with rfl | rfl
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
  · have ha := hv a (by simp)
    have hb := hv b (by simp)
    rcases hop with rfl | rfl <;>
      rcases a with (a | a) <;> rcases b with (b | b) <;>
      (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
      simp_all [emit, binary, run, step, binaryGate, allowed, back, valid, value, GateOp.eval,
        -List.getD_eq_getElem?_getD] <;>
      intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · simp at hl

def read (refs : List Ref) (i : ℕ) : Ref := refs.getD i fixed

def related (refs : List Ref) (w old : List Bool) : Prop :=
  old = refs.map (value w) ∧ ∀ r ∈ refs, valid w.length r

lemma read_value {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    value w (read refs i) = old.getD i false := by
  rw [h.1]
  exact (List.getD_map refs fixed (value w)).symm

lemma related_extend {refs : List Ref} {w old : List Bool} (h : related refs w old)
    (extra : List Gate) (r : Ref) (b : Bool) (hv : valid (run extra w).length r)
    (he : value (run extra w) r = b) :
    related (refs ++ [r]) (run extra w) (old ++ [b]) := by
  have same : refs.map (value (run extra w)) = refs.map (value w) := by
    apply List.map_congr_left
    intro q hq
    rcases q with c | i
    · rfl
    · exact run_prefix _ _ _ (h.2 _ hq)
  constructor
  · rw [List.map_append, same, ← h.1]
    simp [he]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have hqv := h.2 q hq
      cases q with
      | inl c => trivial
      | inr i =>
        change i < w.length at hqv
        change i < (run extra w).length
        rw [run_length]
        omega
    · simpa using (List.mem_singleton.mp hq ▸ hv : valid (run extra w).length q)

lemma table_valid {refs : List Ref} {n : ℕ} (h : ∀ r ∈ refs, valid n r) (i : ℕ) :
    valid n (read refs i) := by
  by_cases hi : i < refs.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [read, List.getD_eq_default _ _ (by omega)]
    trivial

lemma sweep (gs : List Gate) (hg : ∀ g ∈ gs, allowed g ∧ g.inputs.length ≤ 2)
    (refs : List Ref) (n : ℕ) (hvalid : ∀ r ∈ refs, valid n r) :
    ∃ (out : List Gate) (outRefs : List Ref),
      (∀ g ∈ out, binaryGate g) ∧ back n out ∧ out.length ≤ gs.length ∧
      ((∃ g ∈ gs, g.inputs = []) → out.length < gs.length) ∧
      ∀ w old, w.length = n → related refs w old →
        related outRefs (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil => exact ⟨[], refs, by simp, by simp [back], by simp, by simp, fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have hv : ∀ r ∈ rs, valid n r := by
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact table_valid hvalid i
    obtain ⟨hlen, hzero, hgood, hback, heval⟩ :
        e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
        back n e.2 ∧ ∀ w : List Bool, w.length = n →
          valid (run e.2 w).length e.1 ∧
            value (run e.2 w) e.1 = g.op.eval (rs.map (value w)) :=
      emit_ok g.op n rs hg'.1 (by simpa [rs] using hg'.2) hv
    have heValid : valid (n + e.2.length) e.1 := by
      obtain ⟨h, _⟩ := heval (List.replicate n false) (by simp)
      simpa [run_length] using h
    obtain ⟨tail, outRefs, htail, htback, hsize, hstrict, hcorrect⟩ :=
      ih (fun g hg₀ => hg g (by simp [hg₀])) (refs ++ [e.1]) (n + e.2.length) (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · have h := hvalid r hr
          cases r with
          | inl _ => trivial
          | inr i => exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
        · rwa [List.mem_singleton.mp hr])
    refine ⟨e.2 ++ tail, outRefs, ?_, back_append hback htback, ?_, ?_, ?_⟩
    · intro g hg
      exact (List.mem_append.mp hg).elim (hgood g) (htail g)
    · simp only [List.length_append, List.length_cons]
      omega
    · rintro ⟨a, ha, hnil⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · have hz := hzero (by simp [rs, hnil])
        simp [hz]
        omega
      · have hs := hstrict ⟨a, ha, hnil⟩
        simp only [List.length_append, List.length_cons]
        omega
    · intro w old hw hr
      obtain ⟨hv', he'⟩ := heval w hw
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related outRefs (run tail (run e.2 w)) (run gs (step old g))
      exact hcorrect _ _ (by rw [run_length, hw]) (related_extend hr _ _ _ hv' he')

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

lemma gateAt_get {C : Circuit} {j : ℕ} (h : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ h

lemma normalize {n : ℕ} (C : Circuit) (hM : Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      ((∃ g ∈ C.gates, g.inputs = []) → D.size < C.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let refs : List Ref := List.ofFn (fun i : Fin n => .inr i.val)
  have hr : ∀ r ∈ refs, valid n r := by
    intro r h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact i.isLt
  obtain ⟨gs, rs, hgood, hb, hsz, hlt, heval⟩ :=
    sweep C.gates (fun g hg => ⟨by simpa [allowed] using (hM g hg).1, (hM g hg).2⟩) refs n hr
  have hv (x : Fin n → Bool) : value (run gs (List.ofFn x)) (read rs C.output) =
      C.eval (List.ofFn x) := by
    have hinit : related refs (List.ofFn x) (List.ofFn x) := by
      refine ⟨?_, by simpa using hr⟩
      simp only [refs, List.map_ofFn]
      congr 1
      funext i
      simp [value, i.isLt]
    exact read_value (heval _ _ (by simp) hinit) C.output
  cases ho : read rs C.output with
  | inl b =>
    obtain ⟨x, y, hne⟩ := hnc
    exact (hne ((hv x).symm.trans ((congrArg (value (run gs (List.ofFn x))) ho).trans
      ((congrArg (value (run gs (List.ofFn y))) ho).symm.trans (hv y))))).elim
  | inr i =>
    refine ⟨⟨gs, i⟩, ⟨fun g hg => (hgood g hg).1, ?_, fun g hg => (hgood g hg).2⟩,
      hsz, hlt, ?_⟩
    · intro j hj k hk
      rw [gateAt_get hj] at hk
      exact hb j hj k hk
    · intro x
      rw [ho] at hv
      exact hv x

end Twin3321.Strict
namespace Twin3321.Rename

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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


end Twin3321.Rename

namespace Twin3321

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Rename

abbrev Input (n : ℕ) := Fin n → Bool

def mask {n : ℕ} (color : Fin n → Bool) (side : Bool) (x : Input n) : Input n :=
  fun i => decide (color i = side) && x i

def one {n : ℕ} (v : Fin n) : Input n := fun i => decide (i=v)

def clean {n : ℕ} (color : Fin n → Bool) (F : Input n → Prop) (C : Circuit) : Prop :=
  ∀ j<C.size, (gateAt C j).op=.and →
    (∀ x : Input n, (C.wires (List.ofFn x)).getD (n+j) false=true →
      (C.wires (List.ofFn (mask color false x))).getD (n+j) false=true ∨
      (C.wires (List.ofFn (mask color true x))).getD (n+j) false=true ∨ F x) ∧
    ∀ v : Fin n, (C.wires (List.ofFn (one v))).getD (n+j) false=false

def normal {n : ℕ} (color : Fin n → Bool) (F : Input n → Prop) : Prop :=
  ∀ C : Circuit, Monotone2 C → ReadsBack n C → (∀ x, circuitFun n C x=true ↔ F x) →
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size≤C.size ∧
    (∀ x, circuitFun n D x=true ↔ F x) ∧ clean color F D

structure Duplicate (n k : ℕ) where
  rep : Fin n → Fin k
  orig : Fin k → Fin n
  extra : Fin k
  center : Fin n
  leftInv : Function.LeftInverse orig rep
  new : ∀ i, rep i ≠ extra
  extraAt : orig extra = center
  all : ∀ j : Fin k, j = extra ∨ j = rep (orig j)

namespace Duplicate

variable {n k : ℕ} (d : Duplicate n k)

def fold (x : Input k) (i : Fin n) : Bool :=
  if i=d.center then x (d.rep i) || x d.extra else x (d.rep i)

def source (j : Fin k) : Option (Fin n) := if j=d.extra then none else some (d.orig j)

theorem fold_pull (x : Input n) : d.fold (DeleteInput.pull d.source x) = x := by
  funext i
  simp [fold,DeleteInput.pull,source,d.new,d.leftInv i]

theorem fold_one (j : Fin k) : d.fold (one j) = one (d.orig j) := by
  have inj := d.leftInv.injective
  rcases d.all j with je|je
  · subst j
    funext i
    by_cases h : i=d.center <;> simp [fold,one,h,d.new,d.extraAt]
  · funext i
    have ei : d.extra ≠ j := fun e => d.new (d.orig j) (je.symm.trans e.symm)
    have iffEq : d.rep i=j ↔ i=d.orig j := ⟨fun e => inj (e.trans je),fun h => by rw [h,←je]⟩
    simp [fold,one,ei,iffEq]

theorem fold_mask (col : Fin n→Bool) (b : Bool) (x : Input k) :
    d.fold (mask (col ∘ d.orig) b x) = mask col b (d.fold x) := by
  funext i
  by_cases ic : i=d.center
  · subst i
    cases h : col d.center <;> cases b <;> simp [fold,mask,Function.comp_apply,d.leftInv d.center,d.extraAt,h]
  · simp [fold,mask,ic,Function.comp_apply,d.leftInv i]

def ref (i : Fin n) : Fin (k+1) :=
  if i=d.center then Fin.last k else (d.rep i).castSucc

def mergeGate : Gate := ⟨.or,[(d.rep d.center).val,d.extra.val]⟩

def lift (C : Circuit) : Circuit :=
  ⟨d.mergeGate :: C.gates.map (relGate n (k+1) d.ref), wmap n (k+1) d.ref C.output⟩

theorem length_lift (C : Circuit) : (d.lift C).size=C.size+1 := by simp [Circuit.size,lift]

theorem lookup_old (C : Circuit) (j : ℕ) (hj : j<C.size) :
    gateAt (d.lift C) (j+1) = relGate n (k+1) d.ref (gateAt C j) := by
  change j<C.gates.length at hj
  simp [lift,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,hj]

theorem model_lift (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C) :
    Monotone2 (d.lift C) ∧ ReadsBack k (d.lift C) := by
  constructor
  · intro g hg
    change g ∈ d.mergeGate :: C.gates.map _ at hg
    rcases List.mem_cons.mp hg with rfl|h
    · simp [mergeGate]
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      simpa [relGate] using hm t ht
  · intro j hj i hi
    change j < (d.lift C).size at hj
    rw [length_lift] at hj
    cases j with
    | zero =>
      change i ∈ [(d.rep d.center).val,d.extra.val] at hi
      rcases (show i=(d.rep d.center).val ∨ i=d.extra.val by simpa using hi) with rfl|rfl <;> omega
    | succ j =>
      rw [lookup_old _ _ _ (by omega)] at hi
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
      have back := hb j (by change j<C.size; omega) w hw
      unfold wmap
      split
      · rename_i h
        have := (d.ref ⟨w,h⟩).isLt
        omega
      · omega

theorem wire_lift (C : Circuit) (x : Input k) (i : ℕ) :
    ((d.lift C).wires (List.ofFn x)).getD (wmap n (k+1) d.ref i) false =
      (C.wires (List.ofFn (d.fold x))).getD i false := by
  let y := x (d.rep d.center) || x d.extra
  have startWire : step (List.ofFn x) d.mergeGate = List.ofFn x ++ [y] := by
    simp [step,mergeGate,y,GateOp.eval,List.getD_eq_getElem?_getD]
  have base : Rel n (k+1) d.ref (List.ofFn (d.fold x)) (List.ofFn x ++ [y]) := by
    refine ⟨by simp,by simp <;> omega,?_⟩
    intro w
    by_cases h : w<n
    · let u : Fin n := ⟨w,h⟩
      have raw : (List.ofFn (d.fold x)).getD w false = d.fold x u := by simp [u,List.getD_eq_getElem?_getD,h]
      rw [raw,show wmap n (k+1) d.ref w=(d.ref u).val by simp [wmap,h,u]]
      by_cases uc : u=d.center
      · simp [ref,uc,fold,y,List.getD_eq_getElem?_getD]
      · rw [show (d.ref u).val=(d.rep u).val by simp [ref,uc],List.getD_append _ _ _ _ (by simp)]
        simp [fold,uc,List.getD_eq_getElem?_getD]
    · have newIndex : (List.ofFn x ++ [y]).length ≤ wmap n (k+1) d.ref w := by
        simp [wmap,h]
      rw [List.getD_eq_default _ _ newIndex,List.getD_eq_default _ _ (by simp <;> omega)]
  have h := (rel_fold n (k+1) d.ref C.gates _ _ base).2.2 i
  change ((C.gates.map _).foldl step (step (List.ofFn x) d.mergeGate)).getD _ false = _
  rw [startWire]
  exact h

theorem reuse (col : Fin n → Bool) (F : Input n → Prop) (C : Circuit)
    (hm : Monotone2 C) (hb : ReadsBack n C) (hc : clean col F C) :
    Monotone2 (d.lift C) ∧ ReadsBack k (d.lift C) ∧
      (∀ x, circuitFun k (d.lift C) x=circuitFun n C (d.fold x)) ∧
      clean (col ∘ d.orig) (fun x => F (d.fold x)) (d.lift C) := by
  obtain ⟨mon,back⟩ := d.model_lift C hm hb
  refine ⟨mon,back,fun x => d.wire_lift C x C.output,?_⟩
  intro j hj hand
  rw [length_lift] at hj
  cases j with
  | zero => cases hand
  | succ j =>
    have old : j<C.size := by omega
    rw [lookup_old _ _ _ old] at hand
    obtain ⟨cleanJ,oneJ⟩ := hc j old hand
    have index : wmap n (k+1) d.ref (n+j) = k+(j+1) := by simp [wmap]; omega
    have ev (x : Input k) := (index ▸ d.wire_lift C x (n+j) :
      ((d.lift C).wires (List.ofFn x)).getD (k+(j+1)) false =
      (C.wires (List.ofFn (d.fold x))).getD (n+j) false)
    constructor
    · intro x up
      rw [ev] at up
      simpa only [ev,fold_mask] using cleanJ _ up
    · intro v
      rw [ev,fold_one]
      exact oneJ (d.orig v)

theorem fold_setExtra (y : Input n) :
    d.fold (Function.update (DeleteInput.pull d.source y) d.extra true) =
      Function.update y d.center true := by
  funext i
  by_cases eq : i=d.center <;> simp [fold,DeleteInput.pull,source,d.new,d.leftInv i,d.leftInv d.center,eq]

theorem transfer (col : Fin n→Bool) (F : Input n→Prop) (base : normal col F)
    (noSingle : ¬ F (one d.center)) (y : Input n) (off : ¬ F y)
    (on : F (Function.update y d.center true)) :
    normal (col ∘ d.orig) (fun x => F (d.fold x)) := by
  classical
  intro C hm _ correct
  have pr (z : Input n) : circuitFun k C (DeleteInput.pull d.source z)=true ↔ F z := by
    simpa only [fold_pull] using correct (DeleteInput.pull d.source z)
  let lo := DeleteInput.pull d.source y
  let hi := Function.update lo d.extra true
  have low : circuitFun k C lo=false := Bool.eq_false_iff.mpr (fun h => off ((pr y).mp h))
  have high : circuitFun k C hi=true := (correct hi).mpr (by simpa only [hi,lo,fold_setExtra] using on)
  have notOut : C.output ≠ d.extra.val := by
    intro eq
    have val : circuitFun k C (one d.extra)=true := by
      change WireEval.val C (List.ofFn (one d.extra)) C.output = true
      rw [eq,WireEval.val_input List.length_ofFn d.extra.isLt]
      simp [one,List.getD_eq_getElem?_getD]
    exact noSingle (by simpa only [fold_one,d.extraAt] using (correct _).mp val)
  have read := DeleteInput.read_of_separation C hm d.extra notOut hi lo
    (fun i ne => by simp [hi,Function.update_of_ne ne]) high low
  obtain ⟨E,mon,sem,small⟩ := DeleteInput.deleteInput C hm d.source d.extra (by simp [source]) read ⟨y,low⟩
  have oldSpec (x : Input n) : circuitFun n E x=true ↔ F x := by rw [sem]; exact pr x
  have offE : circuitFun n E y=false := Bool.eq_false_iff.mpr (fun h => off ((oldSpec y).mp h))
  have onE := (oldSpec _).mpr on
  obtain ⟨E',model,sz,_,eq⟩ := Strict.normalize E mon ⟨_,y,by
    change circuitFun n E (Function.update y d.center true) ≠ circuitFun n E y
    rw [onE,offE]; decide⟩
  have mon' : Monotone2 E' := fun g hg => ⟨model.1 g hg,(model.2.2 g hg).le⟩
  obtain ⟨D,dm,db,dc,ds,dg⟩ := base E' mon' model.2.1 (by
    intro x
    change E'.eval (List.ofFn x)=true ↔ _
    rw [eq]
    exact oldSpec x)
  obtain ⟨lm,lb,lv,lc⟩ := d.reuse col F D dm db dg
  exact ⟨d.lift D,lm,lb,by rw [length_lift]; omega,fun x => (lv x) ▸ ds (d.fold x),lc⟩

theorem fiber (x : Input k) (u : Fin n) :
    d.fold x u=true ↔ ∃ j : Fin k, d.orig j=u ∧ x j=true := by
  constructor
  · intro h
    by_cases uc : u=d.center
    · rw [fold,if_pos uc,Bool.or_eq_true] at h
      exact h.elim (fun r => ⟨d.rep u,d.leftInv u,r⟩)
        (fun s => ⟨d.extra,d.extraAt.trans uc.symm,s⟩)
    · exact ⟨d.rep u,d.leftInv u,by simpa [fold,uc] using h⟩
  · rintro ⟨j,rfl,hj⟩
    rcases d.all j with e|e
    · subst j
      simp [fold,d.extraAt,hj]
    · have tr : x (d.rep (d.orig j)) = true := e ▸ hj
      simp [fold,tr]

def edgeTruth {m : ℕ} (R : Fin m → Fin m → Prop) (x : Input m) : Prop :=
  ∃ u v : Fin m, R u v ∧ x u = true ∧ x v = true

theorem graphTransfer (col : Fin n→Bool) (G : SimpleGraph (Fin n)) (base : normal col (edgeTruth G.Adj))
    (neighbor : ∃ b, G.Adj d.center b) :
    normal (col ∘ d.orig) (edgeTruth fun u v => G.Adj (d.orig u) (d.orig v)) := by
  classical
  have single (v : Fin n) : ¬ edgeTruth G.Adj (one v) := by
    rintro ⟨i,j,e,hi,hj⟩
    exact e.ne ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
  obtain ⟨b,ab⟩ := neighbor
  have promotes : edgeTruth G.Adj (Function.update (one b) d.center true) :=
    ⟨d.center,b,ab,by simp,by simp [one,Function.update_of_ne ab.ne.symm]⟩
  have t := d.transfer col (edgeTruth G.Adj) base (single d.center) (one b) (single b) promotes
  have eq : (fun x => edgeTruth G.Adj (d.fold x)) = edgeTruth (fun u v => G.Adj (d.orig u) (d.orig v)) := by
    funext x
    apply propext
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      obtain ⟨u,rfl,hu⟩ := (d.fiber _ _).mp hi
      obtain ⟨v,rfl,hv⟩ := (d.fiber _ _).mp hj
      exact ⟨u,v,ij,hu,hv⟩
    · rintro ⟨u,v,uv,hu,hv⟩
      exact ⟨d.orig u,d.orig v,uv,(d.fiber _ _).mpr ⟨u,rfl,hu⟩,(d.fiber _ _).mpr ⟨v,rfl,hv⟩⟩
  rwa [eq] at t

end Duplicate
end Twin3321

namespace Twin3321.Elim

-- Gate restriction adapted from the project proof of L-meta-726.
open PEqualNP.CircuitLowerBounds

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  all_goals simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_count (n k : ℕ) (b : Bool) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → acc.1.getD k (Sum.inl false) = Sum.inl b →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨b, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, if_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false]
      simp
      omega

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

def initStats (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = v then Sum.inl b else Sum.inr i)

theorem inv_init (n : ℕ) (v : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y v b)) (initStats n v b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hv : (⟨i, hlt⟩ : Fin n) = v
    · subst hv
      simp [initStats, hlt, Stat.Valid, Stat.val]
    · simp [initStats, hlt, hv, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hv]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem sum_eq_countP (l : List Gate) (k : ℕ) :
    (∑ i : Fin l.length, if k ∈ (l.get i).inputs then 1 else 0)
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  induction l with
  | nil => simp
  | cons g l ih =>
    show (∑ i : Fin (l.length + 1), if k ∈ ((g :: l).get i).inputs then 1 else 0) = _
    rw [Fin.sum_univ_succ, List.countP_cons]
    simp at ih
    by_cases h : k ∈ g.inputs <;> simp [h] <;> omega

theorem countP_eq_card (l : List Gate) (k : ℕ) :
    (Finset.univ.filter (fun j : Fin l.length => k ∈ (l.get j).inputs)).card
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  rw [Finset.card_filter]
  exact sum_eq_countP l k

theorem eliminate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool), PEqualNP.MetaComplexity.Monotone2 C → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v b hmono hy
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  set acc := elim n C.gates (initStats n v b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y v b))) acc := by
    intro y
    exact inv_elim n _ (by simp) C.gates _ _ hok (inv_init n v b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn (Function.update y v b)) := by
    intro y
    exact ((hinv y).2 C.output).2
  have hcnt := elim_count n v.val b C.gates (initStats n v b, []) hok (by simp [initStats])
    (by simp [initStats])
  rw [← hacc] at hcnt
  simp only [List.length_nil, zero_add] at hcnt
  have hmD : ∀ out : ℕ, PEqualNP.MetaComplexity.Monotone2 ⟨acc.2, out⟩ := by
    intro out g hg
    obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  have hsz : ∀ out : ℕ, (⟨acc.2, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).size
      + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card
      ≤ C.size := by
    intro out
    rw [countP_eq_card]
    exact hcnt
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      obtain ⟨y, hy⟩ := hy
      have := hval y
      rw [hst] at this
      rw [← this] at hy
      exact absurd hy (by simp [Stat.val])
    | false =>
      refine ⟨⟨acc.2, n + acc.2.length⟩, hmD _, hsz _, ?_⟩
      intro x
      rw [← hval x, hst]
      show (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = false
      rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)]
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hmD _, hsz _, ?_⟩
    intro x
    have := hval x
    rw [hst] at this
    exact this

end Twin3321.Elim
namespace Twin3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def aug (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates++[⟨op,[a,b]⟩],n+C.size⟩

theorem aug_size (n) (C) (op) (a b) : (aug n C op a b).size = C.size+1 := by simp [aug,Circuit.size]

theorem aug_old {n C op a b j} (hj : j<C.size) : gateAt (aug n C op a b) j=gateAt C j := by
  change j<C.gates.length at hj
  simp [aug,gateAt,List.getElem?_append_left hj]

theorem aug_new (n C op a b) : gateAt (aug n C op a b) C.size=⟨op,[a,b]⟩ := by
  simp [aug,gateAt,Circuit.size,List.getD_eq_getElem?_getD]

theorem aug_model {n C op a b} (hm : Monotone2 C) (hb : ReadsBack n C)
    (good : op=.and ∨ op=.or) (ha : a<n+C.size) (bb : b<n+C.size) :
    Monotone2 (aug n C op a b) ∧ ReadsBack n (aug n C op a b) := by
  constructor
  · intro g hg
    change g ∈ C.gates++[_] at hg
    rcases List.mem_append.mp hg with h|h
    · exact hm g h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨good,le_rfl⟩
  · intro j hj i hi
    change j < (aug n C op a b).size at hj
    rw [aug_size] at hj
    by_cases old : j<C.size
    · rw [aug_old old] at hi
      exact hb j old i hi
    · have eq : j=C.size := by omega
      subst j
      rw [aug_new] at hi
      rcases (show i=a ∨ i=b by simpa using hi) with rfl|rfl <;> assumption

def wv {n : ℕ} (C : Circuit) (x : Input n) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem aug_wires {n} (C op a b) (x : Input n) :
    (aug n C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [wv C x a,wv C x b]] := by
  simp [aug,Circuit.wires,List.foldl_append,wv]

theorem aug_prior {n C op a b w} (x : Input n) (h : w<n+C.size) :
    wv (aug n C op a b) x w=wv C x w := by
  have len : (C.wires (List.ofFn x)).length=n+C.size := by
    change (Restriction.wiresFrom _ _).length = _
    simp [Restriction.length_wiresFrom,Circuit.size]
  rw [wv,aug_wires,List.getD_append _ _ _ _ (by omega)] <;> rfl

theorem aug_val {n} (C op a b) (x : Input n) :
    wv (aug n C op a b) x (n+C.size)=op.eval [wv C x a,wv C x b] := by
  have len : (C.wires (List.ofFn x)).length=n+C.size := by
    change (Restriction.wiresFrom _ _).length = _
    simp [Restriction.length_wiresFrom,Circuit.size]
  rw [wv,aug_wires,←len,Rename.getD_snoc_eq]

theorem raw_val {n} (C : Circuit) (x : Input n) (v : Fin n) : wv C x v.val=x v := by
  change WireEval.val C (List.ofFn x) v.val = _
  rw [WireEval.val_input List.length_ofFn v.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem pin_smaller {n : ℕ} (C : Circuit) (m : Monotone2 C) (v : Fin n) (b : Bool)
    (x y yes : Input n) (sep : ∀ i, i ≠ v → x i=true → y i=true)
    (hx : circuitFun n C x=true) (hy : circuitFun n C y=false)
    (hz : circuitFun n C yes=true) (zv : yes v=false)
    (reject : ∃ z, circuitFun n C (Function.update z v b)=false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size<C.size ∧
      ∀ z, circuitFun n D z=circuitFun n C (Function.update z v b) := by
  have out : C.output ≠ v.val := by
    intro eq
    change wv C yes C.output=true at hz
    rw [eq,raw_val,zv] at hz
    contradiction
  obtain ⟨g,hg,reads⟩ := DeleteInput.read_of_separation C m v out x y sep hx hy
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
  have positive : 0 < (Finset.univ.filter (fun i : Fin C.gates.length => v.val ∈ (C.gates.get i).inputs)).card :=
    Finset.card_pos.mpr ⟨⟨j,hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,reads⟩⟩
  obtain ⟨D,dm,save,ev⟩ := Elim.eliminate n C v b m reject
  exact ⟨D,dm,by omega,ev⟩

theorem restore_edge {n : ℕ} (col : Fin n → Bool) (F : Input n → Prop)
    (u v : Fin n) (uv : u ≠ v) (z : Input n) (hz : F z) (D : Circuit)
    (dm : Monotone2 D) (db : ReadsBack n D) (df : ∀ x, circuitFun n D x=true ↔ F x)
    (dg : clean col F D) :
    ∃ M : Circuit, Monotone2 M ∧ ReadsBack n M ∧ M.size=D.size+2 ∧
      (∀ x, circuitFun n M x=true ↔ F x ∨ (x u=true ∧ x v=true)) ∧
      clean col (fun x => F x ∨ (x u=true ∧ x v=true)) M := by
  have live : D.output<n+D.size := by
    have hit := (df z).mpr hz
    by_contra! big
    change WireEval.val D (List.ofFn z) D.output=true at hit
    rw [WireEval.val_ge List.length_ofFn big] at hit
    contradiction
  let B := aug n D .and u.val v.val
  let M := aug n B .or D.output (n+D.size)
  have bs : B.size=D.size+1 := aug_size _ _ _ _ _
  have ms : M.size=B.size+1 := aug_size _ _ _ _ _
  have bu : u.val<n+D.size := by have := u.isLt; omega
  have bv : v.val<n+D.size := by have := v.isLt; omega
  obtain ⟨bm,bb⟩ := aug_model dm db (Or.inl rfl) bu bv
  have mdl : Monotone2 M ∧ ReadsBack n M := aug_model bm bb (Or.inr rfl) (by omega) (by omega)
  have atEdge (t : Input n) : wv B t (n+D.size) = (t u && t v) := by
    rw [show wv B t (n+D.size) = _ from aug_val D .and _ _ t,raw_val,raw_val]
    simp [GateOp.eval]
  have valM (t : Input n) : circuitFun n M t = (circuitFun n D t || (t u && t v)) := by
    change wv M t (n+B.size)=_
    rw [show wv M t (n+B.size) = _ from aug_val B .or _ _ t,atEdge,
      show wv B t D.output=wv D t D.output from aug_prior t live]
    simp [GateOp.eval,wv,circuitFun,Circuit.eval]
  refine ⟨M,mdl.1,mdl.2,by omega,fun t => by rw [valM,Bool.or_eq_true,Bool.and_eq_true,df],?_⟩
  intro j hj hand
  by_cases jB : j<B.size
  · have jop : (gateAt B j).op=.and := by
      rwa [show gateAt M j = gateAt B j from aug_old jB] at hand
    have mprior (t : Input n) : wv M t (n+j)=wv B t (n+j) := aug_prior t (by omega)
    by_cases jD : j<D.size
    · rw [show gateAt B j=gateAt D j from aug_old jD] at jop
      obtain ⟨weak,raw⟩ := dg j jD jop
      have prior (t : Input n) : wv M t (n+j)=wv D t (n+j) := (mprior t).trans (aug_prior t (by omega))
      constructor
      · intro t ht
        change wv M t (n+j)=true at ht
        have dh : wv D t (n+j)=true := (prior t).symm.trans ht
        obtain h|h|h := weak t dh
        · exact Or.inl ((prior _).trans h)
        · exact Or.inr (Or.inl ((prior _).trans h))
        · exact Or.inr (Or.inr (Or.inl h))
      · intro a
        exact (prior _).trans (raw a)
    · have eq : j=D.size := by omega
      subst j
      constructor
      · intro t ht
        change wv M t (n+D.size)=true at ht
        rw [mprior,atEdge,Bool.and_eq_true] at ht
        exact Or.inr (Or.inr (Or.inr ht))
      · intro a
        change wv M (one a) (n+D.size)=false
        rw [mprior,atEdge]
        by_cases ua : u=a
        · subst a; simp [one,uv.symm]
        · simp [one,ua]
  · have eq : j=B.size := by omega
    subst j
    rw [show gateAt M B.size=⟨.or,[D.output,n+D.size]⟩ from aug_new _ _ _ _ _] at hand
    cases hand

theorem disjoint_edge {n : ℕ} (col : Fin n → Bool) (F : Input n → Prop) (u v : Fin n) (uv : u ≠ v)
    (base : normal col F) (ignU : ∀ x b, F (Function.update x u b) ↔ F x)
    (ignV : ∀ x b, F (Function.update x v b) ↔ F x)
    (on : ∃ x, F x) (off : ¬ F (fun _ => false)) :
    normal col (fun x => F x ∨ (x u=true ∧ x v=true)) := by
  classical
  intro C hm _ cc
  let zero : Input n := fun _ => false
  let y := Function.update zero v true
  let x := Function.update y u true
  obtain ⟨z,hz⟩ := on
  let yes := Function.update (Function.update z u false) v false
  have yesF : F yes := (ignV _ _).mpr ((ignU _ _).mpr hz)
  have yesU : yes u=false := by simp [yes,Function.update_of_ne uv]
  have yesV : yes v=false := by simp [yes]
  have xu : x u=true := by simp [x]
  have xv : x v=true := by simp [x,y,Function.update_of_ne uv.symm]
  have yF : ¬ F y := fun h => off ((ignV _ _).mp h)
  have yu : y u=false := by simp [y,zero,Function.update_of_ne uv]
  obtain ⟨E,em,es,ee⟩ := pin_smaller C hm u true x y yes
    (fun i ne => by simp [x,Function.update_of_ne ne])
    ((cc x).mpr (Or.inr ⟨xu,xv⟩)) (Bool.eq_false_iff.mpr (by simpa [cc,yF,yu]))
    ((cc yes).mpr (Or.inl yesF)) yesU
    ⟨zero,Bool.eq_false_iff.mpr (by simp [cc,ignU,zero,off,Function.update_of_ne uv.symm])⟩
  have specE (t : Input n) : circuitFun n E t = true ↔ F t ∨ t v=true := by
    rw [ee,cc]
    simp [ignU,Function.update_of_ne uv.symm]
  obtain ⟨K,km,ks,ke⟩ := pin_smaller E em v false y zero yes
    (fun i ne => by simp [y,Function.update_of_ne ne])
    ((specE y).mpr (Or.inr (by simp [y]))) (Bool.eq_false_iff.mpr (by simpa [specE,zero,off]))
    ((specE yes).mpr (Or.inl yesF)) yesV
    ⟨zero,Bool.eq_false_iff.mpr (by simp [specE,ignV,zero,off])⟩
  have specK (t) : circuitFun n K t=true ↔ F t := by rw [ke,specE,ignV]; simp
  have kOff : circuitFun n K zero=false := Bool.eq_false_iff.mpr (fun ht => off ((specK _).mp ht))
  obtain ⟨K',kb,ks',_,kf⟩ := Strict.normalize K km ⟨z,zero,by
    change circuitFun n K z ≠ circuitFun n K zero
    rw [(specK _).mpr hz,kOff]; decide⟩
  have kmon : Monotone2 K' := fun g hg => ⟨kb.1 g hg,(kb.2.2 g hg).le⟩
  obtain ⟨D,dm,db,ds,df,dg⟩ := base K' kmon kb.2.1 (fun t => by
    change K'.eval (List.ofFn t)=true ↔ F t
    rw [kf]; exact specK t)
  obtain ⟨M,mm,mb,ms,mf,mg⟩ := restore_edge col F u v uv z hz D dm db df dg
  exact ⟨M,mm,mb,by omega,mf,mg⟩

theorem leaf_fanout {n : ℕ} (col : Fin n → Bool) (F : Input n → Prop) (u v : Fin n) (uv : u ≠ v)
    (base : normal col F) (ign : ∀ x, F (Function.update x u false) ↔ F x)
    (on : ∃ z, F z) (off : ¬ F (fun _ => false)) (C : Circuit) (cm : Monotone2 C)
    (rc : 2 ≤ (Finset.univ.filter (fun j : Fin C.gates.length => u.val ∈ (C.gates.get j).inputs)).card)
    (cc : ∀ x, circuitFun n C x=true ↔ F x ∨ (x u=true ∧ x v=true)) :
    ∃ M : Circuit, Monotone2 M ∧ ReadsBack n M ∧ M.size≤C.size ∧
      (∀ x, circuitFun n M x=true ↔ F x ∨ (x u=true ∧ x v=true)) ∧
      clean col (fun x => F x ∨ (x u=true ∧ x v=true)) M := by
  classical
  let zero : Input n := fun _ => false
  have pinned (t : Input n) : circuitFun n C (Function.update t u false)=true ↔ F t := by
    rw [cc,ign]; simp
  have no : circuitFun n C (Function.update zero u false)=false :=
    Bool.eq_false_iff.mpr (fun h => off ((pinned zero).mp h))
  obtain ⟨E,em,sz,ev⟩ := Elim.eliminate n C u false cm ⟨zero,no⟩
  have spec (t : Input n) : circuitFun n E t=true ↔ F t := by
    change E.eval (List.ofFn t)=true ↔ F t
    rw [ev]; exact pinned t
  obtain ⟨z,hz⟩ := on
  have elo : circuitFun n E zero=false := Bool.eq_false_iff.mpr (fun h => off ((spec zero).mp h))
  obtain ⟨K,kb,ks,_,kf⟩ := Strict.normalize E em ⟨z,zero,by
    change circuitFun n E z ≠ circuitFun n E zero
    rw [(spec z).mpr hz,elo]; decide⟩
  have mon : Monotone2 K := fun g hg => ⟨kb.1 g hg,(kb.2.2 g hg).le⟩
  obtain ⟨D,dm,db,ds,df,dg⟩ := base K mon kb.2.1 (fun t => by
    change K.eval (List.ofFn t)=true ↔ F t
    rw [kf]; exact spec t)
  obtain ⟨M,mm,mb,ms,mf,mg⟩ := restore_edge col F u v uv z hz D dm db df dg
  exact ⟨M,mm,mb,by omega,mf,mg⟩

end Twin3321

namespace Twin3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Rename WireEval

theorem wire_implication {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Input n)
    (ordered : ∀ i, x i=true → y i=true) (w : ℕ) :
    val C (List.ofFn x) w=true → val C (List.ofFn y) w=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<n
    · rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
      simpa [raw] using ordered ⟨w,raw⟩
    by_cases past : n+C.gates.length ≤ w
    · rw [val_ge List.length_ofFn past]; simp
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have valid : k < C.gates.length := by omega
    rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn valid]
    apply opMono_imp _ (mono_ops hm k valid)
    intro i _
    by_cases smaller : i < n+k
    · simpa only [smaller,ite_true] using ih i smaller
    · simp [smaller]

def remap {n m : ℕ} (e : Fin n→Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m e),wmap n m e C.output⟩

theorem remap_size {n m : ℕ} (e : Fin n→Fin m) (C : Circuit) : (remap e C).size=C.size := by
  simp [remap,Circuit.size]

theorem remap_gate {n m : ℕ} (e : Fin n→Fin m) (C : Circuit) (j : ℕ) (hj : j<C.size) :
    gateAt (remap e C) j=relGate n m e (gateAt C j) := by
  change j<C.gates.length at hj
  simp [remap,gateAt,List.getD_eq_getElem?_getD,hj]

theorem remap_model {n m : ℕ} (e : Fin n→Fin m) (C : Circuit)
    (cm : Monotone2 C) (cb : ReadsBack n C) : Monotone2 (remap e C) ∧ ReadsBack m (remap e C) := by
  constructor
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using cm a ha
  · intro j hj i hi
    change j<(remap e C).size at hj
    rw [remap_size] at hj
    rw [remap_gate e C j hj] at hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    have back := cb j hj w hw
    unfold wmap
    split
    · rename_i h
      have := (e ⟨w,h⟩).isLt
      omega
    · omega

theorem remap_wire {n m : ℕ} (e : Fin n→Fin m) (C : Circuit) (x : Input m) (w : ℕ) :
    ((remap e C).wires (List.ofFn x)).getD (wmap n m e w) false =
      (C.wires (List.ofFn (x ∘ e))).getD w false :=
  (rel_fold n m e C.gates _ _ (rel_init n m e x)).2.2 w

theorem isolates {n m : ℕ} (e : Fin n→Fin m) (s : Fin m→Fin n) (left : Function.LeftInverse s e)
    (col : Fin m→Bool) (F : Input n→Prop) (old : normal (col ∘ e) F) :
    normal col (fun x => F (x ∘ e)) := by
  intro C cm cb cc
  obtain ⟨km,kb⟩ := remap_model s C cm cb
  have ks (x : Input n) : circuitFun n (remap s C) x=true ↔ F x := by
    have eq : (x ∘ s) ∘ e = x := by funext i; simp [Function.comp_apply,left i]
    change ((remap s C).wires (List.ofFn x)).getD (wmap m n s C.output) false=true ↔ F x
    rw [remap_wire]
    simpa only [eq] using cc (x ∘ s)
  obtain ⟨D,dm,db,ds,df,dg⟩ := old (remap s C) km kb ks
  obtain ⟨bm,bb⟩ := remap_model e D dm db
  rw [remap_size] at ds
  refine ⟨remap e D,bm,bb,by rwa [remap_size],fun x => ?_,?_⟩
  · change ((remap e D).wires (List.ofFn x)).getD (wmap n m e D.output) false=true ↔ _
    rw [remap_wire]
    exact df _
  intro j hj op
  rw [remap_size] at hj
  rw [remap_gate e D j hj] at op
  obtain ⟨weak,single⟩ := dg j hj op
  have index : wmap n m e (n+j)=m+j := by simp [wmap] <;> omega
  have read (x : Input m) : ((remap e D).wires (List.ofFn x)).getD (m+j) false =
      (D.wires (List.ofFn (x ∘ e))).getD (n+j) false := index ▸ remap_wire e D x (n+j)
  constructor
  · intro x up
    rw [read] at up
    simpa only [read] using weak (x ∘ e) up
  · intro v
    rw [read]
    apply Bool.eq_false_iff.mpr
    intro hit
    have incl (i : Fin n) : (one v ∘ e) i=true → one (s v) i=true := by
      intro h
      have q : e i=v := of_decide_eq_true h
      have q' : i=s v := (left i).symm.trans (congrArg s q)
      simp [one,q']
    have bad := wire_implication D dm _ _ incl (n+j) hit
    change (D.wires (List.ofFn (one (s v)))).getD (n+j) false=true at bad
    rw [single] at bad
    contradiction

end Twin3321

namespace Twin3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def incident {m n : ℕ} (I : Fin m → Fin n → Prop) (x : Input (m+n)) : Prop :=
  ∃ p l, I p l ∧ x (Fin.castAdd n p)=true ∧ x (Fin.natAdd m l)=true

def splitColor (m n : ℕ) (i : Fin (m+n)) : Bool := decide (m≤i.val)

theorem mask_left {m n : ℕ} (x : Input (m+n)) :
    mask (splitColor m n) false x=(fun i => decide (i.val<m) && x i) := by
  funext i
  by_cases lt : i.val<m
  · simp [mask,splitColor,lt,Nat.not_le.mpr lt]
  · simp [mask,splitColor,lt,Nat.le_of_not_gt lt]

theorem mask_right {m n : ℕ} (x : Input (m+n)) :
    mask (splitColor m n) true x=(fun i => decide (m≤i.val) && x i) := by
  funext i
  by_cases le : m≤i.val <;> simp [mask,splitColor,le]

theorem unroll {m n : ℕ} (I : Fin m → Fin n → Prop)
    (H : normal (splitColor m n) (incident I)) (C : Circuit) (cm : Monotone2 C)
    (cb : ReadsBack (m+n) C) (cf : ∀ x, circuitFun (m+n) C x=true ↔ incident I x) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (m+n) D ∧ D.size≤C.size ∧
      (∀ x, circuitFun (m+n) D x=true ↔ incident I x) ∧
      (∀ j<D.gates.length, (gateAt D j).op=.and → ∀ z : Input (m+n),
        (D.wires (List.ofFn z)).getD (m+n+j) false=true →
        (D.wires (List.ofFn (fun i => decide (i.val<m) && z i))).getD (m+n+j) false=true ∨
        (D.wires (List.ofFn (fun i => decide (m≤i.val) && z i))).getD (m+n+j) false=true ∨ incident I z) ∧
      (∀ j<D.gates.length, (gateAt D j).op=.and →
        (∀ p : Fin m, (D.wires (List.ofFn (fun i => decide (i=Fin.castAdd n p)))).getD (m+n+j) false=false) ∧
        (∀ l : Fin n, (D.wires (List.ofFn (fun i => decide (i=Fin.natAdd m l)))).getD (m+n+j) false=false)) := by
  obtain ⟨D,dm,db,ds,df,dg⟩ := H C cm cb cf
  refine ⟨D,dm,db,ds,df,?_,?_⟩
  · intro j hj andj z up
    simpa only [mask_left,mask_right] using (dg j hj andj).1 z up
  · intro j hj andj
    exact ⟨fun p => (dg j hj andj).2 (Fin.castAdd n p),fun l => (dg j hj andj).2 (Fin.natAdd m l)⟩

theorem adjoin_isolated_pair {m n : ℕ} (I : Fin m→Fin n→Prop) (p₀ : Fin m) (l₀ : Fin n)
    (H : normal (splitColor m n) (incident I)) (nonempty : ∃ p l, I p l)
    (row : ∀ l, ¬ I p₀ l) (column : ∀ p, ¬ I p l₀) :
    normal (splitColor m n) (incident fun p l => I p l ∨ (p=p₀ ∧ l=l₀)) := by
  classical
  let u := Fin.castAdd n p₀
  let v := Fin.natAdd m l₀
  have apart (p : Fin m) (l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd m l := by
    intro h
    have eq := congrArg Fin.val h
    change p.val = m+l.val at eq
    have := p.isLt
    omega
  have uv : u≠v := apart p₀ l₀
  have changes (x : Input (m+n)) (b : Bool) (p : Fin m) (l : Fin n) (pl : I p l) :
      Function.update x u b (Fin.castAdd n p) = x (Fin.castAdd n p) ∧
      Function.update x u b (Fin.natAdd m l) = x (Fin.natAdd m l) ∧
      Function.update x v b (Fin.castAdd n p) = x (Fin.castAdd n p) ∧
      Function.update x v b (Fin.natAdd m l) = x (Fin.natAdd m l) := by
    have a : Fin.castAdd n p≠u := by
      intro e
      have eq : p=p₀ := Fin.ext (congrArg Fin.val e)
      exact row l (eq ▸ pl)
    have d : Fin.natAdd m l≠v := by
      intro e
      have eq := congrArg Fin.val e
      change m+l.val=m+l₀.val at eq
      exact column p ((show l=l₀ from Fin.ext (by omega)) ▸ pl)
    exact ⟨Function.update_of_ne a _ _, Function.update_of_ne (apart p₀ l).symm _ _,
      Function.update_of_ne (apart p l₀) _ _,Function.update_of_ne d _ _⟩
  have ignU (x : Input (m+n)) (b) : incident I (Function.update x u b) ↔ incident I x := by
    constructor <;> rintro ⟨p,l,pl,hp,hl⟩ <;> refine ⟨p,l,pl,?_,?_⟩
    · rwa [←(changes x b p l pl).1]
    · rwa [←(changes x b p l pl).2.1]
    · rwa [(changes x b p l pl).1]
    · rwa [(changes x b p l pl).2.1]
  have ignV (x : Input (m+n)) (b) : incident I (Function.update x v b) ↔ incident I x := by
    constructor <;> rintro ⟨p,l,pl,hp,hl⟩ <;> refine ⟨p,l,pl,?_,?_⟩
    · rwa [←(changes x b p l pl).2.2.1]
    · rwa [←(changes x b p l pl).2.2.2]
    · rwa [(changes x b p l pl).2.2.1]
    · rwa [(changes x b p l pl).2.2.2]
  obtain ⟨p,l,pl⟩ := nonempty
  have bound := disjoint_edge (splitColor m n) (incident I) u v uv H ignU ignV
    ⟨fun _ => true,p,l,pl,rfl,rfl⟩ (by rintro ⟨a,b,_,h,_⟩; cases h)
  have eq : (fun x : Input (m+n) => incident I x ∨ (x u=true ∧ x v=true)) =
      incident (fun p l => I p l ∨ (p=p₀ ∧ l=l₀)) := by
    funext x
    apply propext
    constructor
    · rintro (⟨a,b,ab,ha,hb⟩ | ⟨hu,hv⟩)
      · exact ⟨a,b,Or.inl ab,ha,hb⟩
      · exact ⟨p₀,l₀,Or.inr ⟨rfl,rfl⟩,hu,hv⟩
    · rintro ⟨a,b,(ab|⟨rfl,rfl⟩),ha,hb⟩
      · exact Or.inl ⟨a,b,ab,ha,hb⟩
      · exact Or.inr ⟨ha,hb⟩
  rwa [eq] at bound

end Twin3321

namespace Twin3321
namespace Duplicate

def noRectangle {A B : Type*} (I : A→B→Prop) : Prop :=
  ∀ p q a b, p≠q → a≠b → ¬(I p a ∧ I p b ∧ I q a ∧ I q b)

variable {n k : ℕ} (d : Duplicate n k)

theorem collision {u v : Fin k} (uv : u ≠ v) (same : d.orig u = d.orig v) : d.orig u=d.center := by
  rcases d.all u with a|a
  · rw [a,d.extraAt]
  rcases d.all v with b|b
  · rw [same,b,d.extraAt]
  · exact False.elim (uv (a.trans ((congrArg d.rep same).trans b.symm)))

theorem rectangle_iff {B : Type*} (I : Fin n→B→Prop) :
    noRectangle (fun p l => I (d.orig p) l) ↔
    noRectangle I ∧ ∀ a b, I d.center a → I d.center b → a=b := by
  constructor
  · intro h
    constructor
    · intro p q a b pq ab rect
      apply h (d.rep p) (d.rep q) a b (fun eq => pq (d.leftInv.injective eq)) ab
      simpa only [d.leftInv p,d.leftInv q] using rect
    · intro a b ha hb
      by_contra ne
      apply h d.extra (d.rep d.center) a b (d.new d.center).symm ne
      simpa only [d.extraAt,d.leftInv d.center] using And.intro ha (And.intro hb (And.intro ha hb))
  · rintro ⟨old,degree⟩ p q a b pq ab ⟨pa,pb,qa,qb⟩
    by_cases same : d.orig p=d.orig q
    · have eq := d.collision pq same
      exact ab (degree a b (eq ▸ pa) (eq ▸ pb))
    · exact old _ _ _ _ same ab ⟨pa,pb,qa,qb⟩

end Duplicate
end Twin3321
