import PEqualNP.Outside.L_meta_9752

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.MetaComplexity.Helpers


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.MetaComplexity.Helpers


/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
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

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

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
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
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

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
input is the constant `b`. -/
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- If no gate reads wire `n`, no other wire has the last input in its support. -/
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

/-- Gate elimination: fix the last input of `f` to `b`. If `f` depends on that input and the
restriction is not constant, a circuit of size `s + 1` for `f` gives one of size `s` for the
restriction. -/
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers


/-!
# Parity needs `2 (n - 1)` gates

Helper for `L-meta-020`. The pass of `Elim.lean` fixes the last input of a circuit to a
constant `b`. Here it is shown to save two gates for a suitable `b`, when the function depends
on the last input and both restrictions are non-constant. Either two gates read the fixed
input, or the only gate reading it becomes a constant for a suitable `b` and a later gate
reads that constant, or the output does not depend on the last input. Parity and its
complement satisfy the hypotheses, and their restrictions are again parity or its complement.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-! ## The pass, cut at one gate -/

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

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

/-- A normalized allowed gate that reads a constant `b`, where `b` is `false` for an AND gate
and `true` for an OR gate, becomes a constant. -/
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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

/-- A normalized allowed gate that reads a wire of constant status emits no gate. -/
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

/-- The value to give the fixed input so that a gate reading it becomes a constant. -/
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

/-! ## Supports -/

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

/-- If no gate reads a wire of the set `D`, no wire outside `D` gets the last input in its
support. -/
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

/-! ## Two gates saved -/

/-- If the output wire has the last input in its support and its status is never a constant,
then for some value of the last input the pass emits two gates fewer than it reads. -/
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
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

/-- Gate elimination saving two gates: if `f` depends on its last input and stays non-constant
whichever value that input is fixed to, then for some value `b` the restriction has a circuit
with two gates fewer. -/
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

/-! ## Parity -/

/-- Parity of `n` bits: the number of true bits is odd. -/
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

/-- Parity or its complement on `n + 1` inputs needs `2 n` gates. -/
theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

/-- Parity of `n` inputs needs at least `2 (n - 1)` gates. -/
theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.MetaComplexity.Helpers


/-!
# Parity needs `3 (n - 1)` gates

Helper for `L-meta-025`. The pass of `Elim.lean` is run from other starting statuses: with no
input fixed it only cleans a circuit (every emitted gate is a NOT of one earlier wire or an
AND or OR of two earlier wires), and with input `i` fixed to `b` it restricts the circuit.

In a clean circuit the first gate `g0` reads only inputs. Let `x` be one of them. Three gates
disappear when `x` is fixed to a suitable constant. Some gate `g2` other than `g0` reads `x` or
`g0`, because the output depends on `x`. If `g2` becomes a constant for a suitable value of
`x`, a third gate reads `x`, `g0` or `g2`. Otherwise `g2` reads `g0` and not `x`, and then
either another gate reads `x`, or `g0` is the only reader of `x`. In the last case `g0` reads
`x` only (then its value can be set either way, which makes `g2` a constant) or `g0` reads a
second input `y`, and fixing `y` to the absorbing constant makes the circuit independent of
`x`, which parity does not allow.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-! ## Clean circuits -/

/-- A gate of a clean circuit, where `m` wires exist before it: a NOT of one earlier wire, or
an AND or OR of two earlier wires. -/
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

/-- A clean list of gates on `m` inputs. -/
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

/-- The pass emits a clean list of gates. -/
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

/-- A clean circuit with at most `s` gates computes `f`. -/
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

/-- The statuses at the start when no input is fixed. -/
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- A circuit for a non-constant function can be cleaned without growing. -/
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

/-! ## Fixing input `i` -/

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

/-- The statuses at the start when input `i` is fixed to `b`: the other inputs are the new
input wires, in order. -/
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- The final status of old wire `a` when input `i` is fixed to `b`. -/
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

/-! ## The pass, position by position -/

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

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

/-- A gate that reads an earlier wire whose final status is the absorbing constant of the gate
has a constant final status. -/
theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

/-- Every position of `S` holds a gate that reads an earlier wire of constant final status: the
pass emits at least `|S|` gates fewer than it reads. -/
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

/-! ## Readers -/

/-- `B` is a set of wires containing input `i`. If every gate outside `B` reads no wire of `B`,
no wire outside `B` has `i` in its support. -/
theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

/-- If the wire `o` outside `B` has `i` in its support, some gate outside `B` reads a wire of
`B`. -/
theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

/-- If no gate reads wire `k`, two wire lists that agree off `k` still agree off `k`. -/
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

/-! ## Three gates saved -/

/-- Position `p` holds a gate that reads a wire of constant final status. -/
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

/-- The core of the count. `g0` is the first gate and reads input `i`. Either the status of
`g0` can be made any constant, or another gate reads input `i`. -/
theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  -- the third gate, once `g2` has a constant status under some `b`
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

/-- The final status of the first gate. -/
theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

/-- A first gate that reads only input `i` can be given either constant status. -/
theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

/-- The first gate is an AND or OR of the inputs `i` and `k`, and no other gate reads input
`i`: then the output does not depend on input `i` once input `k` is the absorbing constant. -/
theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- In a clean circuit whose output flips with every input and is never a constant after one
input is fixed, some input and some value of it make the pass emit three gates fewer. -/
theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

/-! ## Parity -/

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

/-- One step for parity or its complement: a clean circuit on `n + 2` inputs gives a clean
circuit on `n + 1` inputs with three gates fewer. -/
theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

/-- A clean circuit for parity or its complement on `n + 1` inputs has at least `3 n` gates. -/
theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

/-- Parity of `n` inputs needs at least `3 (n - 1)` gates. -/
theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.MetaComplexity.Helpers


/-!
# Parity needs `4 (n - 1)` gates

Helper for `L-meta-031`. Take a clean circuit of least size for parity or its complement on at
least two inputs. Least size gives two facts: no gate computes a constant, and no gate computes
the same function as an earlier wire, because such a gate can be dropped.

Fix one input to a constant and run the pass of `Elim.lean`. A gate is touched when it reads a
wire of constant status; touched gates are not emitted. It is shown that for some input and
some constant either four gates are touched, or three are touched and the restricted circuit
has a gate equal to an earlier wire, which is then dropped. So four gates are saved.

The argument, by contradiction. If two gates are constant for the same fixing, four gates are
touched. So no input has a NOT gate on it, and the first gate `G` is an AND or OR of two
inputs `x`, `y`. Each of `x`, `y` has exactly one other reader. If these readers differ, the
other reader of `x` copies `x` once `y` is fixed to the absorbing constant of `G`. If they are
the same gate `r`, then `G` has one reader `h1` and `r` has one reader `h2`, and each of the
second inputs of `h1`, `h2` must depend on the fixed input through the other gate, which the
order of the gates forbids.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-! ## Values of wires -/

/-- The value of wire `j` of the gate list `gs` on the input `u`. -/
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

/-- An AND or OR gate with an input at its absorbing value has that value. -/
theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

/-- Two inputs that agree outside the wire set `B` give wires that agree outside `B`, below the
bound `L`, as soon as every gate outside `B` that reads `B` agrees whenever the earlier wires
outside `B` do. -/
theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

/-- A wire that is not a constant function takes both values. -/
theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

/-! ## Dropping a gate -/

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

/-- A gate that computes the same function as an earlier wire can be dropped. -/
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

/-- A gate that computes a constant can be dropped. -/
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

/-! ## Statuses -/

/-- The input `y` with the value `b` inserted at position `i`. -/
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

/-- The gates the pass emits when input `i` is fixed to `b`. -/
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

/-- The final status of wire `a` is a constant when input `i` is fixed to `b`. -/
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

/-- The final status of a gate is what `simplify` makes of the final statuses of its inputs. -/
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

/-- A gate that reads no wire of constant status gets a fresh wire. -/
theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

/-- A gate of non-constant status that reads a wire of constant status `c`: it is an AND or OR
gate, `c` is not its absorbing value, and another input has non-constant status. -/
theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

/-! ## A least circuit that cannot be reduced by four -/

/-- Fixing some input of `gs` to some constant gives a clean circuit with four gates fewer. -/
def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

/-- The hypotheses of the contradiction: a clean circuit whose output flips with every input,
whose restrictions are not constant, with no constant gate and no gate equal to an earlier
wire, and which cannot be reduced by four gates. -/
structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

theorem Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

theorem Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

/-- Three gates are touched and, after the pass, the old wire `p` is a new gate that agrees
with the old wire `j`, an earlier new wire: impossible. -/
theorem Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

theorem Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

/-- A set `B` of wires of constant status containing the fixed input: two gates outside `B`
are touched. -/
theorem Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

/-- No two gates have constant status for the same fixing. -/
theorem Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

theorem Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

/-- No NOT gate reads an input. -/
theorem Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

/-- The only readers of input `X` are the gates `p` and `q`. If `q` agrees on `u` and on `u`
with `X` flipped, or nothing reads `q`, then `p` has the value of `X` on `u`. -/
theorem Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

/-- Flip input `Z`. Outside the wire set `B` only the gates `ha`, `hb` read `B`; `ha` has an
input outside `B` at its absorbing value and the inputs of `hb` in `B` agree: impossible. -/
theorem Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

/-- A wire outside `B` that changes when input `Z` is flipped comes after some gate outside `B`
that reads `B`. -/
theorem Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

/-- The gate `G` is an AND or OR of the inputs `X` and `Y`: another gate reads `X`. -/
theorem Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

/-- The gate `G` is an AND or OR of the inputs `X` and `Y`: exactly one other gate `r` reads
`X`. It is an AND or OR gate with the other absorbing value, and it does not read `G`. -/
theorem Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

/-- No gate is an AND or OR of two distinct inputs. -/
theorem Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

/-- The hypotheses are contradictory. -/
theorem Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end

/-! ## Parity -/

/-- A clean circuit for parity or its complement on `n + 1` inputs has at least `4 n` gates. -/
theorem par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

/-- Parity of `n` inputs needs at least `4 (n - 1)` gates. -/
theorem parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.MetaComplexity.Helpers


/-!
# Relabelling the inputs of a circuit, and fixing many inputs with two-gate savings

Helper module (proofs only, no statement may use it).

* `relabel_size`: if `h` on `n` inputs has a circuit with at most `s` gates, then for every map
  `π : Fin n → Fin m` the function `x ↦ h (x ∘ π)` on `m` inputs has one too. The input wires
  of the circuit are renamed along `π` and the gate wires are shifted by `m - n`; a wire that
  does not exist stays one that does not exist, so every wire keeps its value.
* `dep_lower_set`: a function that depends on every input of a set `T` has no circuit with
  fewer than `|T| - 1` gates (L-meta-011 for a set of inputs).
* `gate_elim_at`: the two-gate elimination `gate_elim_two` at any input position, the arity
  kept: the restriction is `x ↦ f (update x p b)`.
* `fix_many`: fixing the inputs of a list `L` one at a time, each saving two gates, then the
  inputs of `T` all matter: at least `|T| + 2 |L| - 1` gates.
-/

namespace PEqualNP.MetaComplexity.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
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

/-- Renaming inputs along any map keeps the circuit size. -/
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

/-- L-meta-011 for a set of inputs. -/
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

/-- Two-gate elimination at any input position, the arity kept. -/
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
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

/-- Fixing the inputs of `L` in order, each with a two-gate saving, then every input of `T`
matters. Condition on `L`: for every assignment `a` and every split `L = pre ++ p :: post`,
the function depends on `p` among the inputs agreeing with `a` on `pre`. Condition on `T`: for
every `a` and `i ∈ T`, the function depends on `i` among the inputs agreeing with `a` on `L`. -/
theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.MetaComplexity.Helpers.PermInputs


/-!
# One-gate elimination at any input, the arity kept

Helper for `L-meta-104` (proofs only, no statement may use it). The one-gate elimination
`gate_elim` of `Elim.lean` fixes the last input; renaming the inputs by a transposition moves
any input to the last place, as `gate_elim_at` of `PermInputs.lean` does for two gates.
-/

namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

/-- One-gate elimination at input `p` with the chosen value `b`, the arity kept. -/
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.MetaComplexity.Helpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.MetaComplexity.Helpers.Forest


/-!
# Reader patterns of an input in a least circuit: definitions and the least circuit

Helper for `L-meta-107`. Layer A of the reader-pattern tool, on the names of `Parity3.lean`
and `Parity4.lean` (`CleanL`, `vl`, `stF`, `passG`, `IsC`, `RC`). A least circuit is a clean
gate list of least length for a function; it has no constant gate, no gate equal to an earlier
wire, and no dead gate. Fixing an input to a constant saves every gate that reads a wire of
constant status (`save`), and a gate of constant status is read by a later gate (`Least.next`).
-/

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

/-! ## Definitions on functions -/

/-- The function depends on input `p`. -/
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

/-- The input `x` with inputs `p` and `q` set to `a` and `b`. -/
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

/-- A pair funnel: of the four restrictions of `f` to the values of `(p, q)`, the three other
than the one at `(a, b)` coincide. -/
def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

/-- Fixing input `y` to `b` saves `k` gates out of `s`, the arity kept. -/
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

/-- The input `y` pays: drops `(3, 3)`, or `(4, 2)`, or `(2, 4)` at the values false, true. -/
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

/-- Both restrictions at every input the function depends on are not constant. -/
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

/-- No two inputs the function depends on form a pair funnel. -/
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

/-! ## Layer A: the least circuit -/

/-- A clean circuit of least size for `f`. -/
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

/-- Gate `p` of `gs` reads wire `w`. -/
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

/-! ## Small facts -/

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

/-- A clean gate list is a circuit. -/
theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

/-! ## A1: a least circuit exists -/

/-- A1. A function that is not constant and has a circuit has a least clean one. -/
theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

/-! ## A2: a dead gate can be dropped -/

/-- A2. A gate that no gate reads and that is not the output can be dropped. -/
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

/-! ## A3: no constant, no alias, no dead gate -/

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

/-- A least circuit is no longer than any circuit for the function. -/
theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

/-- A3. No gate of a least circuit computes a constant. -/
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

/-- A3. No gate of a least circuit computes the function of an earlier wire, inputs included. -/
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

/-- A3. Every gate of a least circuit is the output or is read by a later gate. -/
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

/-- A3. An input the function depends on is read by some gate. -/
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

/-! ## A4: the count as a size statement -/

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

/-- A4. Fix input `i` of a clean circuit to `b`; if the restriction is not constant, every set
`S` of gates that read a wire of constant status is saved. -/
theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

/-! ## A5 and helpers at arity `n + 1` -/

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.MetaComplexity.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

/-- A3. An input that some gate of a least circuit reads is one the function depends on. -/
theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

/-- A5. The successor step: in a least circuit, a gate whose status is a constant under a
fixing with a restriction that is not constant is read by a later gate (which is then touched). -/
theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers


/-!
# Reader patterns of an input in a least circuit: two readers

Helper for `L-meta-107`. If gate `p` reads wire `a` and gate `q` reads both `a` and gate `p`,
then gate `q` is a constant or equal to `a` or to gate `p`, which a least circuit forbids
(`Least.no_tri`). With it, two distinct readers of an input pay `(3, 3)`, `(4, 2)` or `(2, 4)`,
and a NOT gate on an input with two readers pays `(3, 3)`.
-/

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- The shape of a gate that reads wire `a`: a NOT of `a`, or an AND or OR of `a` and `w`. -/
theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

/-- In a least circuit no gate reads both a wire `a` and a gate that reads `a`. -/
theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

/-- A gate that reads input `i` has constant status when `i` is fixed to its absorbing value,
and at both values if it is a NOT gate. -/
theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

/-- Two readers of input `i`, the first of constant status: three gates saved. -/
theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

/-- Two readers of input `i`, both of constant status: four gates saved. -/
theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

/-- A6. The death table at fan-out two: two distinct gates read input `i`. -/
theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

/-- A6. A NOT gate on input `i` with two distinct readers: three gates at both values. -/
theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers


/-!
# Reader patterns of an input in a least circuit: the first binary gate

Helper for `L-meta-107`. In a least circuit every gate before the first AND or OR gate `t` is
a NOT gate on an input (a NOT of a NOT gate would equal an earlier wire). So the two operands
of `t` are literals of inputs `p`, `q`. If every input and every NOT gate on an input has at
most one reader, then `p ≠ q`, the only gate outside `{p, q, operands}` that reads one of them
is `t`, and the function sees `x p`, `x q` only through `t`: three of the four restrictions to
the values of `(p, q)` coincide.
-/

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- A function that is a literal contradicts `RestrNC`. -/
theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

/-- Before a position `t` with only NOT gates in front, every gate is a NOT gate on an input. -/
theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

/-- Before such a position, every wire is a literal: an input or a NOT gate on an input. -/
theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

/-- A7. The first binary gate: if every input has at most one reader and every NOT gate on an
input has at most one reader, the function has a pair funnel. -/
theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  -- a reader of the variable of an operand
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  -- the only reader outside the operand of the operand and its variable is `t`
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  -- the two variables differ
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  -- the function sees `x vj`, `x vk` only through gate `t`
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

end PEqualNP.MetaComplexity.Helpers.Readers


/-!
# Reader patterns of an input in a least circuit: the exports

Helper for `L-meta-107`. Statements about `HasCircuitSize` only. Take a least circuit. An
input with two readers pays (`Least.two_readers`), a NOT gate on an input with two readers
pays (`Least.not_two_readers`), and otherwise the first binary gate is a pair funnel
(`Least.funnel`).
-/

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- B1. The fan-out step. A function that depends on some input, whose restrictions at the
inputs it depends on are not constant, and that has no pair funnel: in any circuit, some input
pays `(3, 3)`, `(4, 2)` or `(2, 4)`. -/
theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

/-- B2, the headline: three gates at false for some input, or four at true for some input. -/
theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

/-- B3. A way to prove `NoFunnel`: the restrictions at `(0, 0)`, `(1, 0)`, `(0, 1)` are
pairwise distinct for every two inputs. Any three of the four points contain two of these. -/
theorem noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.Outside.L_meta_9829.Paid
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.Readers
def target (x : Fin 24 → Bool) : Bool := (x 0 && x 15) || (x 0 && x 21) || (x 0 && x 23) || (x 1 && x 16) || (x 1 && x 22) || (x 2 && x 13) || (x 2 && x 17) || (x 2 && x 23) || (x 3 && x 13) || (x 3 && x 14) || (x 3 && x 18) || (x 4 && x 14) || (x 4 && x 15) || (x 4 && x 19) || (x 5 && x 13) || (x 5 && x 15) || (x 5 && x 16) || (x 5 && x 20) || (x 6 && x 14) || (x 6 && x 16) || (x 6 && x 17) || (x 6 && x 21) || (x 7 && x 15) || (x 7 && x 17) || (x 7 && x 18) || (x 7 && x 22) || (x 8 && x 16) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 23) || (x 9 && x 17) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 18) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 13) || (x 11 && x 19) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 14) || (x 12 && x 20) || (x 12 && x 22) || (x 12 && x 23)
def single (i : Fin 24) (x : Fin 24) := decide (x=i)
def row (i j : Fin 24) (x : Fin 24) := decide (x=i ∨ x=j)
def choose (p q : Fin 24) : Fin 24 :=
  (([
[0, 15, 15, 15, 21, 21, 15, 21, 15, 15, 15, 15, 15, 15, 15, 21, 15, 15, 15, 15, 15, 15, 15, 15],
[16, 0, 16, 16, 16, 22, 22, 16, 22, 16, 16, 16, 16, 16, 16, 16, 22, 16, 16, 16, 16, 16, 16, 16],
[13, 13, 0, 17, 13, 17, 13, 13, 13, 13, 13, 17, 13, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
[13, 13, 14, 0, 13, 14, 13, 13, 13, 13, 13, 14, 13, 14, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
[14, 14, 14, 15, 0, 14, 15, 14, 14, 14, 14, 14, 15, 14, 15, 14, 14, 14, 14, 14, 14, 14, 14, 14],
[13, 13, 15, 15, 13, 0, 13, 13, 13, 13, 13, 15, 13, 15, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
[14, 14, 14, 16, 16, 14, 0, 14, 14, 14, 14, 14, 16, 14, 16, 14, 14, 14, 14, 14, 14, 14, 14, 14],
[17, 15, 15, 15, 17, 17, 15, 0, 15, 15, 15, 15, 15, 15, 15, 17, 15, 15, 15, 15, 15, 15, 15, 15],
[16, 18, 16, 16, 16, 18, 18, 16, 0, 16, 16, 16, 16, 16, 16, 16, 18, 16, 16, 16, 16, 16, 16, 16],
[17, 17, 19, 17, 17, 17, 19, 19, 17, 0, 17, 17, 17, 17, 17, 17, 17, 19, 17, 17, 17, 17, 17, 17],
[18, 18, 18, 20, 18, 18, 18, 20, 20, 18, 0, 18, 18, 18, 18, 18, 18, 18, 20, 18, 18, 18, 18, 18],
[13, 13, 19, 19, 13, 19, 13, 13, 13, 13, 13, 0, 13, 19, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
[14, 14, 14, 20, 20, 14, 20, 14, 14, 14, 14, 14, 0, 14, 20, 14, 14, 14, 14, 14, 14, 14, 14, 14],
[2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3],
[3, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 0, 3, 3, 3, 4, 3, 3, 3, 3, 3],
[4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4],
[1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 5, 1],
[2, 2, 6, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 2, 2, 2, 0, 2, 2, 2, 2, 2, 6],
[3, 3, 3, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 3, 3, 3, 0, 3, 3, 3, 3, 3],
[4, 4, 4, 4, 8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 4, 4, 4, 0, 4, 4, 4, 4],
[5, 5, 5, 5, 5, 9, 5, 5, 5, 5, 5, 5, 5, 9, 5, 9, 9, 5, 5, 5, 0, 5, 5, 5],
[6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6],
[1, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 0, 1],
[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0]] : List (List (Fin 24))).getD p.val []).getD q.val 0

def cell (p q : Fin 24) : Bool :=
  let a := single (choose p q)
  target (set2 a p true q false) && !(target (set2 a p false q false)) &&
    !(target (set2 a p false q true))
def checkedRow (p : Fin 24) : Bool :=
  (List.finRange 24).all (fun q => decide (p=q) || cell p q)
set_option maxHeartbeats 800000 in
theorem row0_ok : checkedRow 0 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row1_ok : checkedRow 1 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row2_ok : checkedRow 2 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row3_ok : checkedRow 3 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row4_ok : checkedRow 4 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row5_ok : checkedRow 5 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row6_ok : checkedRow 6 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row7_ok : checkedRow 7 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row8_ok : checkedRow 8 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row9_ok : checkedRow 9 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row10_ok : checkedRow 10 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row11_ok : checkedRow 11 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row12_ok : checkedRow 12 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row13_ok : checkedRow 13 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row14_ok : checkedRow 14 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row15_ok : checkedRow 15 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row16_ok : checkedRow 16 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row17_ok : checkedRow 17 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row18_ok : checkedRow 18 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row19_ok : checkedRow 19 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row20_ok : checkedRow 20 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row21_ok : checkedRow 21 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row22_ok : checkedRow 22 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem row23_ok : checkedRow 23 = true := by decide +kernel
set_option maxHeartbeats 800000 in
theorem everyRow (p : Fin 24) : checkedRow p = true := by
  fin_cases p
  · exact row0_ok
  · exact row1_ok
  · exact row2_ok
  · exact row3_ok
  · exact row4_ok
  · exact row5_ok
  · exact row6_ok
  · exact row7_ok
  · exact row8_ok
  · exact row9_ok
  · exact row10_ok
  · exact row11_ok
  · exact row12_ok
  · exact row13_ok
  · exact row14_ok
  · exact row15_ok
  · exact row16_ok
  · exact row17_ok
  · exact row18_ok
  · exact row19_ok
  · exact row20_ok
  · exact row21_ok
  · exact row22_ok
  · exact row23_ok

theorem separates {p q : Fin 24} (h : p≠q) :
    target (set2 (single (choose p q)) p true q false)=true ∧
    target (set2 (single (choose p q)) p false q false)=false ∧
    target (set2 (single (choose p q)) p false q true)=false := by
  have v := List.all_eq_true.mp (everyRow p) q (List.mem_finRange q)
  simpa [h,cell,Bool.and_eq_true,and_assoc] using v

theorem swap_row (a : Fin 24 → Bool) {p q : Fin 24} (hpq : p≠q) (b c : Bool) :
    set2 a q c p b = set2 a p b q c := by
  funext u
  by_cases h : u=p
  · subst u; simp [set2,Function.update_of_ne,hpq]
  · by_cases h' : u=q
    · subst u; simp [set2,Function.update_of_ne,hpq.symm]
    · simp [set2,Function.update_of_ne,h,h']

theorem no_funnel : NoFunnel target := by
  apply noFunnel_of_sep
  intro p q h _ _
  have a := separates h
  have b := separates h.symm
  refine ⟨⟨single (choose p q), ?_⟩,⟨single (choose q p),?_⟩,⟨single (choose p q),?_⟩⟩
  · rw [a.1,a.2.1]; decide
  · rw [←swap_row _ h false true,←swap_row _ h false false,b.1,b.2.1]; decide
  · rw [a.1,a.2.2]; decide

def outsideEdge (p : Fin 24) : Fin 24 → Bool :=
  if p=0 ∨ p=15 then row 1 16 else row 0 15

set_option maxHeartbeats 500000 in
theorem mixed : ∀ (p : Fin 24) (b : Bool),
    target (Function.update (outsideEdge p) p b) ≠ target (Function.update (fun _ => false) p b) := by
  decide +kernel

theorem nonconstant : RestrNC target := by
  intro p _ b
  exact ⟨outsideEdge p,fun _ => false,mixed p b⟩

theorem depends : ∃ p, Dep target p := by
  refine ⟨0,single 15,?_⟩
  decide +kernel

theorem split (s : Nat) (h : HasCircuitSize 24 target s) :
    ∃ p : Fin 24, Dep target p ∧ Pays target p s :=
  fanout_step 23 target s depends nonconstant no_funnel h

theorem cofactor_lower (s : Nat) (h : HasCircuitSize 24 target s)
    (lo hi : Fin 24 → Nat)
    (low : ∀ (p : Fin 24) (c : Nat), HasCircuitSize 24 (fun x => target (Function.update x p false)) c → lo p ≤ c)
    (high : ∀ (p : Fin 24) (c : Nat), HasCircuitSize 24 (fun x => target (Function.update x p true)) c → hi p ≤ c) :
    ∃ p : Fin 24, min (max (lo p+3) (hi p+3)) (min (max (lo p+4) (hi p+2)) (max (lo p+2) (hi p+4))) ≤ s := by
  obtain ⟨p,_,hp⟩ := split s h
  refine ⟨p,?_⟩
  rcases hp with ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩
  all_goals have la := low p a ha
  all_goals have lb := high p b hb
  all_goals omega

open PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Helpers.PermInputs
abbrev Ticket := Fin 24 × Nat
abbrev Word := Fin 24 → Bool
def word (m : Nat) (i : Fin 24) : Bool := m.testBit i.val
def cofactor (p : Fin 24) (b : Bool) (x : Word) : Bool := target (Function.update x p b)
def leave (f : Word → Bool) : List Ticket → (Word → Bool)
  | [] => f
  | t :: ts => leave (fun x => f (Function.update x t.1 false)) ts

def certified (f : Word → Bool) (z : Nat) : List Ticket → Bool
  | [] => true
  | t :: ts =>
      let a := word t.2
      let g := fun x => f (Function.update x t.1 false)
      (decide (f (Function.update a t.1 (!(a t.1))) ≠ f a) &&
        decide (g (word z) ≠ g (word 0))) && certified g z ts

theorem deduct (s : Nat) (z : Nat) (f : Word → Bool) (ts : List Ticket) :
    certified f z ts = true → HasCircuitSize 24 f (s+ts.length) →
      HasCircuitSize 24 (leave f ts) s := by
  induction ts generalizing f with
  | nil => intro _ h; simpa [leave] using h
  | cons t ts ih =>
    intro hcert h
    simp only [certified, Bool.and_eq_true, decide_eq_true_eq] at hcert
    apply ih (f:=fun x => f (Function.update x t.1 false)) hcert.2
    apply one_gate_at 23 f t.1 false (s+ts.length)
    · exact ⟨word t.2,hcert.1.1⟩
    · exact ⟨word z,word 0,hcert.1.2⟩
    · simpa [Nat.add_assoc] using h

def donor (x : Fin 12 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)

def t0_0 : List Ticket := [(22,2),(18,8),(15,16),(14,8),(12,1048576),(10,1048576),(7,131072),(5,8192),(4,524288),(3,8192),(1,65536)]
def r0_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,0,3,0,2,1,0,4,0,6,0,0,8,10,0,9,5,7,0,11]
set_option maxHeartbeats 2000000 in
theorem valid0_0 : certified (cofactor 0 false) 8196 t0_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq0_0 (x : Fin 12 → Bool) :
    leave (cofactor 0 false) t0_0 (x ∘ r0_0) = donor x := by
  simp [leave,t0_0,cofactor,target,Function.update,Function.comp_def,r0_0,donor] <;> ac_rfl
theorem lower0_0 : ¬ HasCircuitSize 24 (cofactor 0 false) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 0 false) t0_0 valid0_0 h
  have rr := relabel_size r0_0 (leave (cofactor 0 false) t0_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 0 false) t0_0 (x ∘ r0_0)) = donor := funext eq0_0
  rw [←eq]
  exact rr

def t0_1 : List Ticket := [(23,0),(22,2),(21,0),(20,32),(17,4),(15,0),(12,16384),(9,524288),(7,262144),(2,8192),(1,65536)]
def r0_1 : Fin 24 → Fin 12 := ![0,0,0,10,7,11,8,0,9,0,5,6,0,0,3,0,2,0,1,4,0,0,0,0]
set_option maxHeartbeats 2000000 in
theorem valid0_1 : certified (cofactor 0 true) 10240 t0_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq0_1 (x : Fin 12 → Bool) :
    leave (cofactor 0 true) t0_1 (x ∘ r0_1) = donor x := by
  simp [leave,t0_1,cofactor,target,Function.update,Function.comp_def,r0_1,donor] <;> ac_rfl
theorem lower0_1 : ¬ HasCircuitSize 24 (cofactor 0 true) 29 := by
  intro h
  have hh := deduct 18 10240 (cofactor 0 true) t0_1 valid0_1 h
  have rr := relabel_size r0_1 (leave (cofactor 0 true) t0_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 0 true) t0_1 (x ∘ r0_1)) = donor := funext eq0_1
  rw [←eq]
  exact rr

def t1_0 : List Ticket := [(22,128),(20,32),(18,8),(17,4),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192)]
def r1_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid1_0 : certified (cofactor 1 false) 2097153 t1_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq1_0 (x : Fin 12 → Bool) :
    leave (cofactor 1 false) t1_0 (x ∘ r1_0) = donor x := by
  simp [leave,t1_0,cofactor,target,Function.update,Function.comp_def,r1_0,donor] <;> ac_rfl
theorem lower1_0 : ¬ HasCircuitSize 24 (cofactor 1 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 1 false) t1_0 valid1_0 h
  have rr := relabel_size r1_0 (leave (cofactor 1 false) t1_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 1 false) t1_0 (x ∘ r1_0)) = donor := funext eq1_0
  rw [←eq]
  exact rr

def t1_1 : List Ticket := [(22,0),(21,1),(20,32),(17,4),(16,0),(15,1),(9,524288),(7,262144),(6,16384),(5,8192),(0,8388608)]
def r1_1 : Fin 24 → Fin 12 := ![0,0,6,10,8,0,0,0,9,0,5,11,7,0,3,0,0,0,1,2,0,0,0,4]
set_option maxHeartbeats 2000000 in
theorem valid1_1 : certified (cofactor 1 true) 8196 t1_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq1_1 (x : Fin 12 → Bool) :
    leave (cofactor 1 true) t1_1 (x ∘ r1_1) = donor x := by
  simp [leave,t1_1,cofactor,target,Function.update,Function.comp_def,r1_1,donor] <;> ac_rfl
theorem lower1_1 : ¬ HasCircuitSize 24 (cofactor 1 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 1 true) t1_1 valid1_1 h
  have rr := relabel_size r1_1 (leave (cofactor 1 true) t1_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 1 true) t1_1 (x ∘ r1_1)) = donor := funext eq1_1
  rw [←eq]
  exact rr

def t2_0 : List Ticket := [(22,2),(20,32),(18,8),(17,64),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(1,65536)]
def r2_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid2_0 : certified (cofactor 2 false) 2097153 t2_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq2_0 (x : Fin 12 → Bool) :
    leave (cofactor 2 false) t2_0 (x ∘ r2_0) = donor x := by
  simp [leave,t2_0,cofactor,target,Function.update,Function.comp_def,r2_0,donor] <;> ac_rfl
theorem lower2_0 : ¬ HasCircuitSize 24 (cofactor 2 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 2 false) t2_0 valid2_0 h
  have rr := relabel_size r2_0 (leave (cofactor 2 false) t2_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 2 false) t2_0 (x ∘ r2_0)) = donor := funext eq2_0
  rw [←eq]
  exact rr

def t2_1 : List Ticket := [(23,0),(22,2),(21,1),(20,32),(17,0),(13,0),(12,16384),(11,524288),(10,262144),(1,65536),(0,32768)]
def r2_1 : Fin 24 → Fin 12 := ![0,0,0,6,10,8,11,7,9,5,0,0,0,0,0,3,2,0,4,1,0,0,0,0]
set_option maxHeartbeats 2000000 in
theorem valid2_1 : certified (cofactor 2 true) 16392 t2_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq2_1 (x : Fin 12 → Bool) :
    leave (cofactor 2 true) t2_1 (x ∘ r2_1) = donor x := by
  simp [leave,t2_1,cofactor,target,Function.update,Function.comp_def,r2_1,donor] <;> ac_rfl
theorem lower2_1 : ¬ HasCircuitSize 24 (cofactor 2 true) 29 := by
  intro h
  have hh := deduct 18 16392 (cofactor 2 true) t2_1 valid2_1 h
  have rr := relabel_size r2_1 (leave (cofactor 2 true) t2_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 2 true) t2_1 (x ∘ r2_1)) = donor := funext eq2_1
  rw [←eq]
  exact rr

def t3_0 : List Ticket := [(22,2),(20,32),(18,128),(17,4),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(2,8192),(1,65536)]
def r3_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid3_0 : certified (cofactor 3 false) 2097153 t3_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq3_0 (x : Fin 12 → Bool) :
    leave (cofactor 3 false) t3_0 (x ∘ r3_0) = donor x := by
  simp [leave,t3_0,cofactor,target,Function.update,Function.comp_def,r3_0,donor] <;> ac_rfl
theorem lower3_0 : ¬ HasCircuitSize 24 (cofactor 3 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 3 false) t3_0 valid3_0 h
  have rr := relabel_size r3_0 (leave (cofactor 3 false) t3_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 3 false) t3_0 (x ∘ r3_0)) = donor := funext eq3_0
  rw [←eq]
  exact rr

def t3_1 : List Ticket := [(20,32),(18,0),(17,4),(16,2),(14,0),(13,0),(9,524288),(6,2097152),(5,32768),(2,8388608),(1,4194304)]
def r3_1 : Fin 24 → Fin 12 := ![10,0,0,0,11,0,0,6,8,0,5,9,7,0,0,0,0,0,0,2,0,1,4,3]
set_option maxHeartbeats 2000000 in
theorem valid3_1 : certified (cofactor 3 true) 32896 t3_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq3_1 (x : Fin 12 → Bool) :
    leave (cofactor 3 true) t3_1 (x ∘ r3_1) = donor x := by
  simp [leave,t3_1,cofactor,target,Function.update,Function.comp_def,r3_1,donor] <;> ac_rfl
theorem lower3_1 : ¬ HasCircuitSize 24 (cofactor 3 true) 29 := by
  intro h
  have hh := deduct 18 32896 (cofactor 3 true) t3_1 valid3_1 h
  have rr := relabel_size r3_1 (leave (cofactor 3 true) t3_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 3 true) t3_1 (x ∘ r3_1)) = donor := funext eq3_1
  rw [←eq]
  exact rr

def t4_0 : List Ticket := [(22,2),(19,256),(14,8),(13,4),(12,1048576),(11,2097152),(10,262144),(9,131072),(3,262144),(2,131072),(1,65536)]
def r4_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,1,4,3,2,0,0,0,0,0,0,10,9,7,8,0,5,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid4_0 : certified (cofactor 4 false) 2097153 t4_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq4_0 (x : Fin 12 → Bool) :
    leave (cofactor 4 false) t4_0 (x ∘ r4_0) = donor x := by
  simp [leave,t4_0,cofactor,target,Function.update,Function.comp_def,r4_0,donor] <;> ac_rfl
theorem lower4_0 : ¬ HasCircuitSize 24 (cofactor 4 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 4 false) t4_0 valid4_0 h
  have rr := relabel_size r4_0 (leave (cofactor 4 false) t4_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 4 false) t4_0 (x ∘ r4_0)) = donor := funext eq4_0
  rw [←eq]
  exact rr

def t4_1 : List Ticket := [(22,2),(20,32),(19,0),(18,8),(15,0),(14,0),(12,8388608),(10,2097152),(7,131072),(3,8192),(1,65536)]
def r4_1 : Fin 24 → Fin 12 := ![7,0,10,0,0,11,9,0,8,5,0,6,0,0,0,0,2,1,0,0,0,4,0,3]
set_option maxHeartbeats 2000000 in
theorem valid4_1 : certified (cofactor 4 true) 10240 t4_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq4_1 (x : Fin 12 → Bool) :
    leave (cofactor 4 true) t4_1 (x ∘ r4_1) = donor x := by
  simp [leave,t4_1,cofactor,target,Function.update,Function.comp_def,r4_1,donor] <;> ac_rfl
theorem lower4_1 : ¬ HasCircuitSize 24 (cofactor 4 true) 29 := by
  intro h
  have hh := deduct 18 10240 (cofactor 4 true) t4_1 valid4_1 h
  have rr := relabel_size r4_1 (leave (cofactor 4 true) t4_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 4 true) t4_1 (x ∘ r4_1)) = donor := funext eq4_1
  rw [←eq]
  exact rr

def t5_0 : List Ticket := [(20,512),(17,4),(16,2),(13,4),(12,16384),(10,262144),(9,524288),(6,16384),(3,16384),(2,8388608),(1,4194304)]
def r5_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,0,0,3,2,0,0,4,0,0,5,10,0,0,8,9,0,6,7,11]
set_option maxHeartbeats 2000000 in
theorem valid5_0 : certified (cofactor 5 false) 2097153 t5_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq5_0 (x : Fin 12 → Bool) :
    leave (cofactor 5 false) t5_0 (x ∘ r5_0) = donor x := by
  simp [leave,t5_0,cofactor,target,Function.update,Function.comp_def,r5_0,donor] <;> ac_rfl
theorem lower5_0 : ¬ HasCircuitSize 24 (cofactor 5 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 5 false) t5_0 valid5_0 h
  have rr := relabel_size r5_0 (leave (cofactor 5 false) t5_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 5 false) t5_0 (x ∘ r5_0)) = donor := funext eq5_0
  rw [←eq]
  exact rr

def t5_1 : List Ticket := [(20,0),(18,8),(17,4),(16,0),(15,0),(13,0),(10,2097152),(9,524288),(7,4194304),(3,16384),(2,8388608)]
def r5_1 : Fin 24 → Fin 12 := ![7,5,0,0,11,0,6,0,8,0,0,9,10,0,0,0,0,0,0,2,0,4,1,3]
set_option maxHeartbeats 2000000 in
theorem valid5_1 : certified (cofactor 5 true) 16448 t5_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq5_1 (x : Fin 12 → Bool) :
    leave (cofactor 5 true) t5_1 (x ∘ r5_1) = donor x := by
  simp [leave,t5_1,cofactor,target,Function.update,Function.comp_def,r5_1,donor] <;> ac_rfl
theorem lower5_1 : ¬ HasCircuitSize 24 (cofactor 5 true) 29 := by
  intro h
  have hh := deduct 18 16448 (cofactor 5 true) t5_1 valid5_1 h
  have rr := relabel_size r5_1 (leave (cofactor 5 true) t5_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 5 true) t5_1 (x ∘ r5_1)) = donor := funext eq5_1
  rw [←eq]
  exact rr

def t6_0 : List Ticket := [(22,2),(19,16),(14,8),(13,4),(12,1048576),(11,2097152),(9,131072),(4,32768),(3,262144),(2,131072),(1,65536)]
def r6_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,3,0,1,2,0,4,0,0,0,0,10,8,5,9,0,7,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid6_0 : certified (cofactor 6 false) 2097153 t6_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq6_0 (x : Fin 12 → Bool) :
    leave (cofactor 6 false) t6_0 (x ∘ r6_0) = donor x := by
  simp [leave,t6_0,cofactor,target,Function.update,Function.comp_def,r6_0,donor] <;> ac_rfl
theorem lower6_0 : ¬ HasCircuitSize 24 (cofactor 6 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 6 false) t6_0 valid6_0 h
  have rr := relabel_size r6_0 (leave (cofactor 6 false) t6_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 6 false) t6_0 (x ∘ r6_0)) = donor := funext eq6_0
  rw [←eq]
  exact rr

def t6_1 : List Ticket := [(21,0),(20,32),(17,0),(16,0),(15,1),(14,0),(10,262144),(5,8192),(4,524288),(1,4194304),(0,8388608)]
def r6_1 : Fin 24 → Fin 12 := ![0,0,6,11,0,0,0,8,9,5,0,10,7,0,0,0,0,0,2,1,0,0,3,4]
set_option maxHeartbeats 2000000 in
theorem valid6_1 : certified (cofactor 6 true) 8196 t6_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq6_1 (x : Fin 12 → Bool) :
    leave (cofactor 6 true) t6_1 (x ∘ r6_1) = donor x := by
  simp [leave,t6_1,cofactor,target,Function.update,Function.comp_def,r6_1,donor] <;> ac_rfl
theorem lower6_1 : ¬ HasCircuitSize 24 (cofactor 6 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 6 true) t6_1 valid6_1 h
  have rr := relabel_size r6_1 (leave (cofactor 6 true) t6_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 6 true) t6_1 (x ∘ r6_1)) = donor := funext eq6_1
  rw [←eq]
  exact rr

def t7_0 : List Ticket := [(22,2),(20,32),(18,8),(17,4),(12,16384),(10,2097152),(9,524288),(6,16384),(3,8192),(2,8192),(1,65536)]
def r7_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid7_0 : certified (cofactor 7 false) 2097153 t7_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq7_0 (x : Fin 12 → Bool) :
    leave (cofactor 7 false) t7_0 (x ∘ r7_0) = donor x := by
  simp [leave,t7_0,cofactor,target,Function.update,Function.comp_def,r7_0,donor] <;> ac_rfl
theorem lower7_0 : ¬ HasCircuitSize 24 (cofactor 7 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 7 false) t7_0 valid7_0 h
  have rr := relabel_size r7_0 (leave (cofactor 7 false) t7_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 7 false) t7_0 (x ∘ r7_0)) = donor := funext eq7_0
  rw [←eq]
  exact rr

def t7_1 : List Ticket := [(22,0),(20,32),(18,0),(17,0),(15,0),(14,8),(12,8388608),(10,2097152),(4,524288),(3,8192),(1,65536)]
def r7_1 : Fin 24 → Fin 12 := ![7,0,6,0,0,11,8,0,9,5,0,10,0,0,0,0,2,0,0,1,0,3,0,4]
set_option maxHeartbeats 2000000 in
theorem valid7_1 : certified (cofactor 7 true) 8196 t7_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq7_1 (x : Fin 12 → Bool) :
    leave (cofactor 7 true) t7_1 (x ∘ r7_1) = donor x := by
  simp [leave,t7_1,cofactor,target,Function.update,Function.comp_def,r7_1,donor] <;> ac_rfl
theorem lower7_1 : ¬ HasCircuitSize 24 (cofactor 7 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 7 true) t7_1 valid7_1 h
  have rr := relabel_size r7_1 (leave (cofactor 7 true) t7_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 7 true) t7_1 (x ∘ r7_1)) = donor := funext eq7_1
  rw [←eq]
  exact rr

def t8_0 : List Ticket := [(22,2),(20,32),(19,16),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(4,32768),(3,8192),(1,65536)]
def r8_0 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid8_0 : certified (cofactor 8 false) 2097153 t8_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq8_0 (x : Fin 12 → Bool) :
    leave (cofactor 8 false) t8_0 (x ∘ r8_0) = donor x := by
  simp [leave,t8_0,cofactor,target,Function.update,Function.comp_def,r8_0,donor] <;> ac_rfl
theorem lower8_0 : ¬ HasCircuitSize 24 (cofactor 8 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 8 false) t8_0 valid8_0 h
  have rr := relabel_size r8_0 (leave (cofactor 8 false) t8_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 8 false) t8_0 (x ∘ r8_0)) = donor := funext eq8_0
  rw [←eq]
  exact rr

def t8_1 : List Ticket := [(23,0),(20,32),(19,0),(18,0),(16,0),(15,1),(10,2097152),(9,131072),(5,8192),(4,16384),(1,4194304)]
def r8_1 : Fin 24 → Fin 12 := ![5,0,11,6,0,0,9,8,0,0,0,10,7,0,4,0,0,2,0,0,0,1,3,0]
set_option maxHeartbeats 2000000 in
theorem valid8_1 : certified (cofactor 8 true) 8200 t8_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq8_1 (x : Fin 12 → Bool) :
    leave (cofactor 8 true) t8_1 (x ∘ r8_1) = donor x := by
  simp [leave,t8_1,cofactor,target,Function.update,Function.comp_def,r8_1,donor] <;> ac_rfl
theorem lower8_1 : ¬ HasCircuitSize 24 (cofactor 8 true) 29 := by
  intro h
  have hh := deduct 18 8200 (cofactor 8 true) t8_1 valid8_1 h
  have rr := relabel_size r8_1 (leave (cofactor 8 true) t8_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 8 true) t8_1 (x ∘ r8_1)) = donor := funext eq8_1
  rw [←eq]
  exact rr

def t9_0 : List Ticket := [(22,2),(20,32),(18,8),(17,4),(12,16384),(10,2097152),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r9_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid9_0 : certified (cofactor 9 false) 2097153 t9_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq9_0 (x : Fin 12 → Bool) :
    leave (cofactor 9 false) t9_0 (x ∘ r9_0) = donor x := by
  simp [leave,t9_0,cofactor,target,Function.update,Function.comp_def,r9_0,donor] <;> ac_rfl
theorem lower9_0 : ¬ HasCircuitSize 24 (cofactor 9 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 9 false) t9_0 valid9_0 h
  have rr := relabel_size r9_0 (leave (cofactor 9 false) t9_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 9 false) t9_0 (x ∘ r9_0)) = donor := funext eq9_0
  rw [←eq]
  exact rr

def t9_1 : List Ticket := [(22,2),(21,1),(20,0),(19,0),(17,0),(15,1),(11,8192),(7,262144),(4,16384),(1,65536),(0,8388608)]
def r9_1 : Fin 24 → Fin 12 := ![0,0,6,10,0,11,8,0,9,0,5,0,7,0,3,0,2,0,1,0,0,0,0,4]
set_option maxHeartbeats 2000000 in
theorem valid9_1 : certified (cofactor 9 true) 8196 t9_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq9_1 (x : Fin 12 → Bool) :
    leave (cofactor 9 true) t9_1 (x ∘ r9_1) = donor x := by
  simp [leave,t9_1,cofactor,target,Function.update,Function.comp_def,r9_1,donor] <;> ac_rfl
theorem lower9_1 : ¬ HasCircuitSize 24 (cofactor 9 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 9 true) t9_1 valid9_1 h
  have rr := relabel_size r9_1 (leave (cofactor 9 true) t9_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 9 true) t9_1 (x ∘ r9_1)) = donor := funext eq9_1
  rw [←eq]
  exact rr

def t10_0 : List Ticket := [(22,2),(20,32),(18,8),(17,4),(12,16384),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r10_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid10_0 : certified (cofactor 10 false) 2097153 t10_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq10_0 (x : Fin 12 → Bool) :
    leave (cofactor 10 false) t10_0 (x ∘ r10_0) = donor x := by
  simp [leave,t10_0,cofactor,target,Function.update,Function.comp_def,r10_0,donor] <;> ac_rfl
theorem lower10_0 : ¬ HasCircuitSize 24 (cofactor 10 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 10 false) t10_0 valid10_0 h
  have rr := relabel_size r10_0 (leave (cofactor 10 false) t10_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 10 false) t10_0 (x ∘ r10_0)) = donor := funext eq10_0
  rw [←eq]
  exact rr

def t10_1 : List Ticket := [(22,2),(21,0),(20,0),(19,16),(18,0),(15,1),(11,8192),(7,131072),(4,16384),(1,65536),(0,8388608)]
def r10_1 : Fin 24 → Fin 12 := ![0,0,10,6,0,11,9,0,8,5,0,0,7,0,4,0,2,1,0,0,0,0,0,3]
set_option maxHeartbeats 2000000 in
theorem valid10_1 : certified (cofactor 10 true) 8200 t10_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq10_1 (x : Fin 12 → Bool) :
    leave (cofactor 10 true) t10_1 (x ∘ r10_1) = donor x := by
  simp [leave,t10_1,cofactor,target,Function.update,Function.comp_def,r10_1,donor] <;> ac_rfl
theorem lower10_1 : ¬ HasCircuitSize 24 (cofactor 10 true) 29 := by
  intro h
  have hh := deduct 18 8200 (cofactor 10 true) t10_1 valid10_1 h
  have rr := relabel_size r10_1 (leave (cofactor 10 true) t10_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 10 true) t10_1 (x ∘ r10_1)) = donor := funext eq10_1
  rw [←eq]
  exact rr

def t11_0 : List Ticket := [(22,2),(19,16),(14,8),(13,4),(12,1048576),(9,131072),(6,65536),(4,32768),(3,262144),(2,131072),(1,65536)]
def r11_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,3,0,1,2,0,4,0,0,0,0,10,8,5,9,0,7,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid11_0 : certified (cofactor 11 false) 2097153 t11_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq11_0 (x : Fin 12 → Bool) :
    leave (cofactor 11 false) t11_0 (x ∘ r11_0) = donor x := by
  simp [leave,t11_0,cofactor,target,Function.update,Function.comp_def,r11_0,donor] <;> ac_rfl
theorem lower11_0 : ¬ HasCircuitSize 24 (cofactor 11 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 11 false) t11_0 valid11_0 h
  have rr := relabel_size r11_0 (leave (cofactor 11 false) t11_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 11 false) t11_0 (x ∘ r11_0)) = donor := funext eq11_0
  rw [←eq]
  exact rr

def t11_1 : List Ticket := [(22,0),(21,0),(19,0),(18,8),(17,4),(13,0),(10,1048576),(7,32768),(3,16384),(2,8388608),(1,65536)]
def r11_1 : Fin 24 → Fin 12 := ![7,0,0,0,6,9,11,0,8,5,0,0,10,0,0,4,2,0,0,0,1,0,0,3]
set_option maxHeartbeats 2000000 in
theorem valid11_1 : certified (cofactor 11 true) 16400 t11_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq11_1 (x : Fin 12 → Bool) :
    leave (cofactor 11 true) t11_1 (x ∘ r11_1) = donor x := by
  simp [leave,t11_1,cofactor,target,Function.update,Function.comp_def,r11_1,donor] <;> ac_rfl
theorem lower11_1 : ¬ HasCircuitSize 24 (cofactor 11 true) 29 := by
  intro h
  have hh := deduct 18 16400 (cofactor 11 true) t11_1 valid11_1 h
  have rr := relabel_size r11_1 (leave (cofactor 11 true) t11_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 11 true) t11_1 (x ∘ r11_1)) = donor := funext eq11_1
  rw [←eq]
  exact rr

def t12_0 : List Ticket := [(22,2),(20,32),(18,8),(17,4),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r12_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid12_0 : certified (cofactor 12 false) 2097153 t12_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq12_0 (x : Fin 12 → Bool) :
    leave (cofactor 12 false) t12_0 (x ∘ r12_0) = donor x := by
  simp [leave,t12_0,cofactor,target,Function.update,Function.comp_def,r12_0,donor] <;> ac_rfl
theorem lower12_0 : ¬ HasCircuitSize 24 (cofactor 12 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 12 false) t12_0 valid12_0 h
  have rr := relabel_size r12_0 (leave (cofactor 12 false) t12_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 12 false) t12_0 (x ∘ r12_0)) = donor := funext eq12_0
  rw [←eq]
  exact rr

def t12_1 : List Ticket := [(23,0),(22,0),(20,0),(17,4),(15,1),(14,0),(7,262144),(4,524288),(2,8192),(1,65536),(0,2097152)]
def r12_1 : Fin 24 → Fin 12 := ![0,0,0,6,0,11,8,0,9,5,7,10,0,0,0,0,2,0,4,1,0,3,0,0]
set_option maxHeartbeats 2000000 in
theorem valid12_1 : certified (cofactor 12 true) 8200 t12_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq12_1 (x : Fin 12 → Bool) :
    leave (cofactor 12 true) t12_1 (x ∘ r12_1) = donor x := by
  simp [leave,t12_1,cofactor,target,Function.update,Function.comp_def,r12_1,donor] <;> ac_rfl
theorem lower12_1 : ¬ HasCircuitSize 24 (cofactor 12 true) 29 := by
  intro h
  have hh := deduct 18 8200 (cofactor 12 true) t12_1 valid12_1 h
  have rr := relabel_size r12_1 (leave (cofactor 12 true) t12_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 12 true) t12_1 (x ∘ r12_1)) = donor := funext eq12_1
  rw [←eq]
  exact rr

def t13_0 : List Ticket := [(20,32),(17,4),(16,2),(12,16384),(10,262144),(9,524288),(6,16384),(5,32768),(3,16384),(2,8388608),(1,4194304)]
def r13_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,0,0,3,2,0,0,4,0,0,5,10,0,0,8,9,0,6,7,11]
set_option maxHeartbeats 2000000 in
theorem valid13_0 : certified (cofactor 13 false) 2097153 t13_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq13_0 (x : Fin 12 → Bool) :
    leave (cofactor 13 false) t13_0 (x ∘ r13_0) = donor x := by
  simp [leave,t13_0,cofactor,target,Function.update,Function.comp_def,r13_0,donor] <;> ac_rfl
theorem lower13_0 : ¬ HasCircuitSize 24 (cofactor 13 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 13 false) t13_0 valid13_0 h
  have rr := relabel_size r13_0 (leave (cofactor 13 false) t13_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 13 false) t13_0 (x ∘ r13_0)) = donor := funext eq13_0
  rw [←eq]
  exact rr

def t13_1 : List Ticket := [(20,512),(18,128),(16,2),(11,0),(10,2097152),(9,131072),(8,524288),(5,0),(3,0),(2,0),(1,4194304)]
def r13_1 : Fin 24 → Fin 12 := ![0,0,0,0,1,0,4,3,0,0,0,0,2,0,9,10,0,7,0,5,0,6,8,11]
set_option maxHeartbeats 2000000 in
theorem valid13_1 : certified (cofactor 13 true) 2097153 t13_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq13_1 (x : Fin 12 → Bool) :
    leave (cofactor 13 true) t13_1 (x ∘ r13_1) = donor x := by
  simp [leave,t13_1,cofactor,target,Function.update,Function.comp_def,r13_1,donor] <;> ac_rfl
theorem lower13_1 : ¬ HasCircuitSize 24 (cofactor 13 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 13 true) t13_1 valid13_1 h
  have rr := relabel_size r13_1 (leave (cofactor 13 true) t13_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 13 true) t13_1 (x ∘ r13_1)) = donor := funext eq13_1
  rw [←eq]
  exact rr

def t14_0 : List Ticket := [(22,2),(19,16),(13,4),(12,1048576),(11,2097152),(10,262144),(9,131072),(4,32768),(3,262144),(2,131072),(1,65536)]
def r14_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,1,4,3,2,0,0,0,0,0,0,10,9,7,8,0,5,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid14_0 : certified (cofactor 14 false) 2097153 t14_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq14_0 (x : Fin 12 → Bool) :
    leave (cofactor 14 false) t14_0 (x ∘ r14_0) = donor x := by
  simp [leave,t14_0,cofactor,target,Function.update,Function.comp_def,r14_0,donor] <;> ac_rfl
theorem lower14_0 : ¬ HasCircuitSize 24 (cofactor 14 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 14 false) t14_0 valid14_0 h
  have rr := relabel_size r14_0 (leave (cofactor 14 false) t14_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 14 false) t14_0 (x ∘ r14_0)) = donor := funext eq14_0
  rw [←eq]
  exact rr

def t14_1 : List Ticket := [(20,32),(19,256),(18,128),(12,0),(10,2097152),(9,131072),(8,65536),(6,0),(4,0),(3,0),(1,65536)]
def r14_1 : Fin 24 → Fin 12 := ![0,0,2,0,0,1,0,3,0,0,0,4,0,9,0,10,5,8,0,0,0,6,7,11]
set_option maxHeartbeats 2000000 in
theorem valid14_1 : certified (cofactor 14 true) 2097153 t14_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq14_1 (x : Fin 12 → Bool) :
    leave (cofactor 14 true) t14_1 (x ∘ r14_1) = donor x := by
  simp [leave,t14_1,cofactor,target,Function.update,Function.comp_def,r14_1,donor] <;> ac_rfl
theorem lower14_1 : ¬ HasCircuitSize 24 (cofactor 14 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 14 true) t14_1 valid14_1 h
  have rr := relabel_size r14_1 (leave (cofactor 14 true) t14_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 14 true) t14_1 (x ∘ r14_1)) = donor := funext eq14_1
  rw [←eq]
  exact rr

def t15_0 : List Ticket := [(22,2),(18,8),(14,8),(12,1048576),(10,1048576),(7,131072),(5,8192),(4,524288),(3,8192),(1,65536),(0,2097152)]
def r15_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,0,3,0,2,1,0,4,0,6,0,0,8,10,0,9,5,7,0,11]
set_option maxHeartbeats 2000000 in
theorem valid15_0 : certified (cofactor 15 false) 8196 t15_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq15_0 (x : Fin 12 → Bool) :
    leave (cofactor 15 false) t15_0 (x ∘ r15_0) = donor x := by
  simp [leave,t15_0,cofactor,target,Function.update,Function.comp_def,r15_0,donor] <;> ac_rfl
theorem lower15_0 : ¬ HasCircuitSize 24 (cofactor 15 false) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 15 false) t15_0 valid15_0 h
  have rr := relabel_size r15_0 (leave (cofactor 15 false) t15_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 15 false) t15_0 (x ∘ r15_0)) = donor := funext eq15_0
  rw [←eq]
  exact rr

def t15_1 : List Ticket := [(22,2),(18,8),(14,8),(12,1048576),(10,1048576),(7,0),(5,0),(4,0),(3,8192),(1,65536),(0,0)]
def r15_1 : Fin 24 → Fin 12 := ![0,0,0,0,0,0,3,0,2,1,0,4,0,6,0,0,8,10,0,9,5,7,0,11]
set_option maxHeartbeats 2000000 in
theorem valid15_1 : certified (cofactor 15 true) 8196 t15_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq15_1 (x : Fin 12 → Bool) :
    leave (cofactor 15 true) t15_1 (x ∘ r15_1) = donor x := by
  simp [leave,t15_1,cofactor,target,Function.update,Function.comp_def,r15_1,donor] <;> ac_rfl
theorem lower15_1 : ¬ HasCircuitSize 24 (cofactor 15 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 15 true) t15_1 valid15_1 h
  have rr := relabel_size r15_1 (leave (cofactor 15 true) t15_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 15 true) t15_1 (x ∘ r15_1)) = donor := funext eq15_1
  rw [←eq]
  exact rr

def t16_0 : List Ticket := [(20,32),(17,4),(13,4),(12,16384),(10,262144),(9,524288),(6,16384),(5,32768),(3,16384),(2,8388608),(1,4194304)]
def r16_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,0,0,3,2,0,0,4,0,0,5,10,0,0,8,9,0,6,7,11]
set_option maxHeartbeats 2000000 in
theorem valid16_0 : certified (cofactor 16 false) 2097153 t16_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq16_0 (x : Fin 12 → Bool) :
    leave (cofactor 16 false) t16_0 (x ∘ r16_0) = donor x := by
  simp [leave,t16_0,cofactor,target,Function.update,Function.comp_def,r16_0,donor] <;> ac_rfl
theorem lower16_0 : ¬ HasCircuitSize 24 (cofactor 16 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 16 false) t16_0 valid16_0 h
  have rr := relabel_size r16_0 (leave (cofactor 16 false) t16_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 16 false) t16_0 (x ∘ r16_0)) = donor := funext eq16_0
  rw [←eq]
  exact rr

def t16_1 : List Ticket := [(20,512),(18,8),(13,4),(10,2097152),(9,131072),(8,0),(6,0),(5,0),(3,16384),(2,131072),(1,0)]
def r16_1 : Fin 24 → Fin 12 := ![0,0,0,0,3,0,0,1,0,0,0,4,2,0,8,10,0,5,0,7,0,6,9,11]
set_option maxHeartbeats 2000000 in
theorem valid16_1 : certified (cofactor 16 true) 2097153 t16_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq16_1 (x : Fin 12 → Bool) :
    leave (cofactor 16 true) t16_1 (x ∘ r16_1) = donor x := by
  simp [leave,t16_1,cofactor,target,Function.update,Function.comp_def,r16_1,donor] <;> ac_rfl
theorem lower16_1 : ¬ HasCircuitSize 24 (cofactor 16 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 16 true) t16_1 valid16_1 h
  have rr := relabel_size r16_1 (leave (cofactor 16 true) t16_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 16 true) t16_1 (x ∘ r16_1)) = donor := funext eq16_1
  rw [←eq]
  exact rr

def t17_0 : List Ticket := [(22,2),(20,32),(18,8),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r17_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid17_0 : certified (cofactor 17 false) 2097153 t17_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq17_0 (x : Fin 12 → Bool) :
    leave (cofactor 17 false) t17_0 (x ∘ r17_0) = donor x := by
  simp [leave,t17_0,cofactor,target,Function.update,Function.comp_def,r17_0,donor] <;> ac_rfl
theorem lower17_0 : ¬ HasCircuitSize 24 (cofactor 17 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 17 false) t17_0 valid17_0 h
  have rr := relabel_size r17_0 (leave (cofactor 17 false) t17_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 17 false) t17_0 (x ∘ r17_0)) = donor := funext eq17_0
  rw [←eq]
  exact rr

def t17_1 : List Ticket := [(22,2),(20,32),(18,8),(12,16384),(10,2097152),(9,0),(7,0),(6,0),(3,8192),(2,0),(1,65536)]
def r17_1 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid17_1 : certified (cofactor 17 true) 2097153 t17_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq17_1 (x : Fin 12 → Bool) :
    leave (cofactor 17 true) t17_1 (x ∘ r17_1) = donor x := by
  simp [leave,t17_1,cofactor,target,Function.update,Function.comp_def,r17_1,donor] <;> ac_rfl
theorem lower17_1 : ¬ HasCircuitSize 24 (cofactor 17 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 17 true) t17_1 valid17_1 h
  have rr := relabel_size r17_1 (leave (cofactor 17 true) t17_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 17 true) t17_1 (x ∘ r17_1)) = donor := funext eq17_1
  rw [←eq]
  exact rr

def t18_0 : List Ticket := [(22,2),(20,32),(17,4),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r18_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid18_0 : certified (cofactor 18 false) 2097153 t18_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq18_0 (x : Fin 12 → Bool) :
    leave (cofactor 18 false) t18_0 (x ∘ r18_0) = donor x := by
  simp [leave,t18_0,cofactor,target,Function.update,Function.comp_def,r18_0,donor] <;> ac_rfl
theorem lower18_0 : ¬ HasCircuitSize 24 (cofactor 18 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 18 false) t18_0 valid18_0 h
  have rr := relabel_size r18_0 (leave (cofactor 18 false) t18_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 18 false) t18_0 (x ∘ r18_0)) = donor := funext eq18_0
  rw [←eq]
  exact rr

def t18_1 : List Ticket := [(22,2),(17,4),(13,4),(11,524288),(10,0),(9,524288),(8,0),(7,0),(3,0),(2,8388608),(1,65536)]
def r18_1 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,4,0,0,0,0,0,2,0,9,10,7,0,0,5,8,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid18_1 : certified (cofactor 18 true) 2097153 t18_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq18_1 (x : Fin 12 → Bool) :
    leave (cofactor 18 true) t18_1 (x ∘ r18_1) = donor x := by
  simp [leave,t18_1,cofactor,target,Function.update,Function.comp_def,r18_1,donor] <;> ac_rfl
theorem lower18_1 : ¬ HasCircuitSize 24 (cofactor 18 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 18 true) t18_1 valid18_1 h
  have rr := relabel_size r18_1 (leave (cofactor 18 true) t18_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 18 true) t18_1 (x ∘ r18_1)) = donor := funext eq18_1
  rw [←eq]
  exact rr

def t19_0 : List Ticket := [(22,2),(14,8),(13,4),(12,1048576),(11,2097152),(10,262144),(9,131072),(4,32768),(3,262144),(2,131072),(1,65536)]
def r19_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,1,4,3,2,0,0,0,0,0,0,10,9,7,8,0,5,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid19_0 : certified (cofactor 19 false) 2097153 t19_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq19_0 (x : Fin 12 → Bool) :
    leave (cofactor 19 false) t19_0 (x ∘ r19_0) = donor x := by
  simp [leave,t19_0,cofactor,target,Function.update,Function.comp_def,r19_0,donor] <;> ac_rfl
theorem lower19_0 : ¬ HasCircuitSize 24 (cofactor 19 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 19 false) t19_0 valid19_0 h
  have rr := relabel_size r19_0 (leave (cofactor 19 false) t19_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 19 false) t19_0 (x ∘ r19_0)) = donor := funext eq19_0
  rw [←eq]
  exact rr

def t19_1 : List Ticket := [(17,4),(14,8),(13,4),(11,0),(9,0),(8,0),(6,65536),(4,0),(3,262144),(2,8388608),(1,65536)]
def r19_1 : Fin 24 → Fin 12 := ![0,0,0,0,0,1,0,3,0,0,4,0,2,0,0,10,5,0,7,0,9,6,8,11]
set_option maxHeartbeats 2000000 in
theorem valid19_1 : certified (cofactor 19 true) 2097153 t19_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq19_1 (x : Fin 12 → Bool) :
    leave (cofactor 19 true) t19_1 (x ∘ r19_1) = donor x := by
  simp [leave,t19_1,cofactor,target,Function.update,Function.comp_def,r19_1,donor] <;> ac_rfl
theorem lower19_1 : ¬ HasCircuitSize 24 (cofactor 19 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 19 true) t19_1 valid19_1 h
  have rr := relabel_size r19_1 (leave (cofactor 19 true) t19_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 19 true) t19_1 (x ∘ r19_1)) = donor := funext eq19_1
  rw [←eq]
  exact rr

def t20_0 : List Ticket := [(22,2),(18,8),(17,4),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r20_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid20_0 : certified (cofactor 20 false) 2097153 t20_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq20_0 (x : Fin 12 → Bool) :
    leave (cofactor 20 false) t20_0 (x ∘ r20_0) = donor x := by
  simp [leave,t20_0,cofactor,target,Function.update,Function.comp_def,r20_0,donor] <;> ac_rfl
theorem lower20_0 : ¬ HasCircuitSize 24 (cofactor 20 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 20 false) t20_0 valid20_0 h
  have rr := relabel_size r20_0 (leave (cofactor 20 false) t20_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 20 false) t20_0 (x ∘ r20_0)) = donor := funext eq20_0
  rw [←eq]
  exact rr

def t20_1 : List Ticket := [(17,4),(16,2),(13,4),(12,0),(10,0),(9,0),(6,16384),(5,0),(3,16384),(2,8388608),(1,4194304)]
def r20_1 : Fin 24 → Fin 12 := ![0,0,0,0,1,0,0,3,2,0,0,4,0,0,5,10,0,0,8,9,0,6,7,11]
set_option maxHeartbeats 2000000 in
theorem valid20_1 : certified (cofactor 20 true) 2097153 t20_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq20_1 (x : Fin 12 → Bool) :
    leave (cofactor 20 true) t20_1 (x ∘ r20_1) = donor x := by
  simp [leave,t20_1,cofactor,target,Function.update,Function.comp_def,r20_1,donor] <;> ac_rfl
theorem lower20_1 : ¬ HasCircuitSize 24 (cofactor 20 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 20 true) t20_1 valid20_1 h
  have rr := relabel_size r20_1 (leave (cofactor 20 true) t20_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 20 true) t20_1 (x ∘ r20_1)) = donor := funext eq20_1
  rw [←eq]
  exact rr

def t21_0 : List Ticket := [(16,2),(15,1),(14,8),(12,1048576),(10,262144),(6,131072),(5,8192),(4,524288),(3,8192),(1,4194304),(0,8388608)]
def r21_0 : Fin 24 → Fin 12 := ![0,0,0,0,0,0,0,3,2,1,0,4,0,6,0,0,0,10,8,9,5,0,7,11]
set_option maxHeartbeats 2000000 in
theorem valid21_0 : certified (cofactor 21 false) 8196 t21_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq21_0 (x : Fin 12 → Bool) :
    leave (cofactor 21 false) t21_0 (x ∘ r21_0) = donor x := by
  simp [leave,t21_0,cofactor,target,Function.update,Function.comp_def,r21_0,donor] <;> ac_rfl
theorem lower21_0 : ¬ HasCircuitSize 24 (cofactor 21 false) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 21 false) t21_0 valid21_0 h
  have rr := relabel_size r21_0 (leave (cofactor 21 false) t21_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 21 false) t21_0 (x ∘ r21_0)) = donor := funext eq21_0
  rw [←eq]
  exact rr

def t21_1 : List Ticket := [(18,8),(16,2),(14,8),(11,0),(10,0),(8,524288),(6,0),(4,32768),(3,8192),(1,4194304),(0,0)]
def r21_1 : Fin 24 → Fin 12 := ![0,0,0,0,0,4,0,3,0,1,0,0,2,6,0,7,0,10,0,5,9,0,8,11]
set_option maxHeartbeats 2000000 in
theorem valid21_1 : certified (cofactor 21 true) 8196 t21_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq21_1 (x : Fin 12 → Bool) :
    leave (cofactor 21 true) t21_1 (x ∘ r21_1) = donor x := by
  simp [leave,t21_1,cofactor,target,Function.update,Function.comp_def,r21_1,donor] <;> ac_rfl
theorem lower21_1 : ¬ HasCircuitSize 24 (cofactor 21 true) 29 := by
  intro h
  have hh := deduct 18 8196 (cofactor 21 true) t21_1 valid21_1 h
  have rr := relabel_size r21_1 (leave (cofactor 21 true) t21_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 21 true) t21_1 (x ∘ r21_1)) = donor := funext eq21_1
  rw [←eq]
  exact rr

def t22_0 : List Ticket := [(20,32),(18,8),(17,4),(12,16384),(10,2097152),(9,524288),(7,32768),(6,16384),(3,8192),(2,8192),(1,65536)]
def r22_0 : Fin 24 → Fin 12 := ![0,0,0,0,1,3,0,0,2,0,0,4,0,7,5,10,8,0,0,9,0,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid22_0 : certified (cofactor 22 false) 2097153 t22_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq22_0 (x : Fin 12 → Bool) :
    leave (cofactor 22 false) t22_0 (x ∘ r22_0) = donor x := by
  simp [leave,t22_0,cofactor,target,Function.update,Function.comp_def,r22_0,donor] <;> ac_rfl
theorem lower22_0 : ¬ HasCircuitSize 24 (cofactor 22 false) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 22 false) t22_0 valid22_0 h
  have rr := relabel_size r22_0 (leave (cofactor 22 false) t22_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 22 false) t22_0 (x ∘ r22_0)) = donor := funext eq22_0
  rw [←eq]
  exact rr

def t22_1 : List Ticket := [(18,8),(17,4),(13,4),(12,0),(11,0),(10,1048576),(9,524288),(7,0),(3,16384),(2,8388608),(1,0)]
def r22_1 : Fin 24 → Fin 12 := ![0,0,0,0,3,1,4,0,2,0,0,0,0,0,7,10,9,0,0,8,5,6,0,11]
set_option maxHeartbeats 2000000 in
theorem valid22_1 : certified (cofactor 22 true) 2097153 t22_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq22_1 (x : Fin 12 → Bool) :
    leave (cofactor 22 true) t22_1 (x ∘ r22_1) = donor x := by
  simp [leave,t22_1,cofactor,target,Function.update,Function.comp_def,r22_1,donor] <;> ac_rfl
theorem lower22_1 : ¬ HasCircuitSize 24 (cofactor 22 true) 29 := by
  intro h
  have hh := deduct 18 2097153 (cofactor 22 true) t22_1 valid22_1 h
  have rr := relabel_size r22_1 (leave (cofactor 22 true) t22_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 22 true) t22_1 (x ∘ r22_1)) = donor := funext eq22_1
  rw [←eq]
  exact rr

def t23_0 : List Ticket := [(21,1),(20,32),(17,4),(12,16384),(10,262144),(9,524288),(6,16384),(5,8192),(2,8192),(1,65536),(0,32768)]
def r23_0 : Fin 24 → Fin 12 := ![0,0,0,0,2,0,0,3,1,0,0,4,0,6,11,8,5,0,10,9,0,0,7,0]
set_option maxHeartbeats 2000000 in
theorem valid23_0 : certified (cofactor 23 false) 8200 t23_0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq23_0 (x : Fin 12 → Bool) :
    leave (cofactor 23 false) t23_0 (x ∘ r23_0) = donor x := by
  simp [leave,t23_0,cofactor,target,Function.update,Function.comp_def,r23_0,donor] <;> ac_rfl
theorem lower23_0 : ¬ HasCircuitSize 24 (cofactor 23 false) 29 := by
  intro h
  have hh := deduct 18 8200 (cofactor 23 false) t23_0 valid23_0 h
  have rr := relabel_size r23_0 (leave (cofactor 23 false) t23_0) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 23 false) t23_0 (x ∘ r23_0)) = donor := funext eq23_0
  rw [←eq]
  exact rr

def t23_1 : List Ticket := [(19,16),(16,2),(15,16),(12,0),(9,131072),(8,0),(5,8192),(4,16384),(2,0),(1,4194304),(0,0)]
def r23_1 : Fin 24 → Fin 12 := ![0,0,0,0,0,0,4,3,0,0,1,2,0,11,6,0,0,7,10,0,5,9,8,0]
set_option maxHeartbeats 2000000 in
theorem valid23_1 : certified (cofactor 23 true) 16392 t23_1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem eq23_1 (x : Fin 12 → Bool) :
    leave (cofactor 23 true) t23_1 (x ∘ r23_1) = donor x := by
  simp [leave,t23_1,cofactor,target,Function.update,Function.comp_def,r23_1,donor] <;> ac_rfl
theorem lower23_1 : ¬ HasCircuitSize 24 (cofactor 23 true) 29 := by
  intro h
  have hh := deduct 18 16392 (cofactor 23 true) t23_1 valid23_1 h
  have rr := relabel_size r23_1 (leave (cofactor 23 true) t23_1) 18 hh
  apply PEqualNP.Outside.L_meta_9752
  change HasCircuitSize 12 donor 18
  have eq : (fun x => leave (cofactor 23 true) t23_1 (x ∘ r23_1)) = donor := funext eq23_1
  rw [←eq]
  exact rr

theorem around (p : Fin 24) (b : Bool) : ¬ HasCircuitSize 24 (cofactor p b) 29 := by
  fin_cases p <;> cases b
  · exact lower0_0
  · exact lower0_1
  · exact lower1_0
  · exact lower1_1
  · exact lower2_0
  · exact lower2_1
  · exact lower3_0
  · exact lower3_1
  · exact lower4_0
  · exact lower4_1
  · exact lower5_0
  · exact lower5_1
  · exact lower6_0
  · exact lower6_1
  · exact lower7_0
  · exact lower7_1
  · exact lower8_0
  · exact lower8_1
  · exact lower9_0
  · exact lower9_1
  · exact lower10_0
  · exact lower10_1
  · exact lower11_0
  · exact lower11_1
  · exact lower12_0
  · exact lower12_1
  · exact lower13_0
  · exact lower13_1
  · exact lower14_0
  · exact lower14_1
  · exact lower15_0
  · exact lower15_1
  · exact lower16_0
  · exact lower16_1
  · exact lower17_0
  · exact lower17_1
  · exact lower18_0
  · exact lower18_1
  · exact lower19_0
  · exact lower19_1
  · exact lower20_0
  · exact lower20_1
  · exact lower21_0
  · exact lower21_1
  · exact lower22_0
  · exact lower22_1
  · exact lower23_0
  · exact lower23_1

theorem physical33 : ¬ HasCircuitSize 24 target 32 := by
  intro h
  obtain ⟨p,_,hp⟩ := split 32 h
  have cap (b : Bool) (s : Nat) (c : HasCircuitSize 24 (fun x => target (Function.update x p b)) s) : 30 ≤ s := by
    by_contra! bad
    apply around p b
    obtain ⟨C,hC,z,ev⟩ := c
    exact ⟨C,hC,by omega,ev⟩
  rcases hp with ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩
  all_goals have la := cap false a ha
  all_goals have lb := cap true b hb
  all_goals omega


private abbrev clip (f : Word → Bool) (p : Fin 24) (b : Bool) : Word → Bool :=
  fun x => f (Function.update x p b)
private theorem pairCut (f : Word → Bool) (p u : Fin 24) (m : Nat)
    (pd : ∃ x, clip f p (!(x p)) x ≠ f x)
    (ps : ∀ b, ∃ x y, clip f p b x ≠ clip f p b y)
    (ud : ∀ b, ∃ x, clip (clip f p b) u (!(x u)) x ≠ clip f p b x)
    (us : ∀ b, ∃ x y, clip (clip f p b) u false x ≠ clip (clip f p b) u false y)
    (h : HasCircuitSize 24 f (m+3)) :
    ∃ b, HasCircuitSize 24 (clip (clip f p b) u false) m := by
  obtain ⟨b,t,le,hc⟩ := gate_elim_at 23 f p (m+3) pd ps h
  obtain ⟨C,fan,size,ev⟩ := hc
  have hh : HasCircuitSize 24 (clip f p b) (m+1) := ⟨C,fan,size.trans (by omega),ev⟩
  exact ⟨b,one_gate_at 23 _ u false m (ud b) (us b) hh⟩

private def paidList0 : List Ticket := [(22,2),(21,64),(20,32),(12,16384),(11,8192),(10,262144),(9,131072),(8,65536),(1,65536)]
private def costMap0 : Fin 24 → Fin 12 := ![0,0,1,0,0,3,2,4,0,0,0,0,0,10,11,7,8,9,6,0,0,0,0,5]
private abbrev left0 := leave (cofactor 0 false) paidList0
set_option maxHeartbeats 2000000 in
private theorem innerValid0 : certified (cofactor 0 false) 262152 paidList0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow0 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left0 19 b) 4 false) (x ∘ costMap0) = donor x := by
  cases b <;> simp [clip,left0,leave,paidList0,cofactor,target,Function.update,Function.comp_def,costMap0,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar0 : ¬ HasCircuitSize 24 (cofactor 0 false) 30 := by
  intro h
  have hh := deduct 21 262152 (cofactor 0 false) paidList0 innerValid0 h
  obtain ⟨b,hc⟩ := pairCut left0 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 16384,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap0 (clip (clip left0 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left0 19 b) 4 false) (x ∘ costMap0)) = donor := funext (mapLow0 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList1 : List Ticket := [(22,128),(20,32),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(8,65536),(3,8192)]
private def costMap1 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left1 := leave (cofactor 1 false) paidList1
set_option maxHeartbeats 2000000 in
private theorem innerValid1 : certified (cofactor 1 false) 2097153 paidList1 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow1 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left1 19 b) 4 false) (x ∘ costMap1) = donor x := by
  cases b <;> simp [clip,left1,leave,paidList1,cofactor,target,Function.update,Function.comp_def,costMap1,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar1 : ¬ HasCircuitSize 24 (cofactor 1 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 1 false) paidList1 innerValid1 h
  obtain ⟨b,hc⟩ := pairCut left1 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap1 (clip (clip left1 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left1 19 b) 4 false) (x ∘ costMap1)) = donor := funext (mapLow1 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList2 : List Ticket := [(20,32),(18,8),(17,64),(12,16384),(11,8192),(10,2097152),(9,524288),(7,32768),(3,8192)]
private def costMap2 : Fin 24 → Fin 12 := ![0,0,0,0,3,1,2,0,4,0,0,0,0,5,8,10,9,0,0,7,0,11,0,6]
private abbrev left2 := leave (cofactor 2 false) paidList2
set_option maxHeartbeats 2000000 in
private theorem innerValid2 : certified (cofactor 2 false) 8388609 paidList2 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow2 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left2 22 b) 1 false) (x ∘ costMap2) = donor x := by
  cases b <;> simp [clip,left2,leave,paidList2,cofactor,target,Function.update,Function.comp_def,costMap2,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar2 : ¬ HasCircuitSize 24 (cofactor 2 false) 30 := by
  intro h
  have hh := deduct 21 8388609 (cofactor 2 false) paidList2 innerValid2 h
  obtain ⟨b,hc⟩ := pairCut left2 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap2 (clip (clip left2 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left2 22 b) 1 false) (x ∘ costMap2)) = donor := funext (mapLow2 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList3 : List Ticket := [(22,2),(20,32),(14,16),(12,8388608),(11,8192),(10,262144),(9,131072),(8,65536),(1,65536)]
private def costMap3 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left3 := leave (cofactor 3 false) paidList3
set_option maxHeartbeats 2000000 in
private theorem innerValid3 : certified (cofactor 3 false) 2097153 paidList3 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow3 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left3 19 b) 4 false) (x ∘ costMap3) = donor x := by
  cases b <;> simp [clip,left3,leave,paidList3,cofactor,target,Function.update,Function.comp_def,costMap3,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar3 : ¬ HasCircuitSize 24 (cofactor 3 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 3 false) paidList3 innerValid3 h
  obtain ⟨b,hc⟩ := pairCut left3 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap3 (clip (clip left3 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left3 19 b) 4 false) (x ∘ costMap3)) = donor := funext (mapLow3 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList4 : List Ticket := [(22,2),(20,32),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(3,8192),(1,65536)]
private def costMap4 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left4 := leave (cofactor 4 false) paidList4
set_option maxHeartbeats 2000000 in
private theorem innerValid4 : certified (cofactor 4 false) 2097153 paidList4 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow4 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left4 19 b) 8 false) (x ∘ costMap4) = donor x := by
  cases b <;> simp [clip,left4,leave,paidList4,cofactor,target,Function.update,Function.comp_def,costMap4,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar4 : ¬ HasCircuitSize 24 (cofactor 4 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 4 false) paidList4 innerValid4 h
  obtain ⟨b,hc⟩ := pairCut left4 19 8 18 ⟨word 256,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap4 (clip (clip left4 19 b) 8 false) 18 hc
  have eq : (fun x => (clip (clip left4 19 b) 8 false) (x ∘ costMap4)) = donor := funext (mapLow4 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList5 : List Ticket := [(22,2),(19,16),(14,8),(12,1048576),(11,8192),(10,262144),(4,32768),(3,8192),(1,65536)]
private def costMap5 : Fin 24 → Fin 12 := ![0,0,1,0,0,0,2,4,3,0,0,0,0,5,0,6,8,9,7,0,0,11,0,10]
private abbrev left5 := leave (cofactor 5 false) paidList5
set_option maxHeartbeats 2000000 in
private theorem innerValid5 : certified (cofactor 5 false) 32769 paidList5 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow5 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left5 20 b) 9 false) (x ∘ costMap5) = donor x := by
  cases b <;> simp [clip,left5,leave,paidList5,cofactor,target,Function.update,Function.comp_def,costMap5,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar5 : ¬ HasCircuitSize 24 (cofactor 5 false) 30 := by
  intro h
  have hh := deduct 21 32769 (cofactor 5 false) paidList5 innerValid5 h
  obtain ⟨b,hc⟩ := pairCut left5 20 9 18 ⟨word 512,by decide +kernel⟩
    (fun b => ⟨word 0,word 32769,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 131072,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 32769,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap5 (clip (clip left5 20 b) 9 false) 18 hc
  have eq : (fun x => (clip (clip left5 20 b) 9 false) (x ∘ costMap5)) = donor := funext (mapLow5 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList6 : List Ticket := [(22,2),(20,32),(19,16),(12,16384),(11,8192),(10,262144),(9,131072),(4,16384),(1,65536)]
private def costMap6 : Fin 24 → Fin 12 := ![1,0,0,0,0,2,0,4,3,0,0,0,0,11,0,9,8,6,7,0,0,5,0,10]
private abbrev left6 := leave (cofactor 6 false) paidList6
set_option maxHeartbeats 2000000 in
private theorem innerValid6 : certified (cofactor 6 false) 131076 paidList6 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow6 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left6 14 b) 3 false) (x ∘ costMap6) = donor x := by
  cases b <;> simp [clip,left6,leave,paidList6,cofactor,target,Function.update,Function.comp_def,costMap6,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar6 : ¬ HasCircuitSize 24 (cofactor 6 false) 30 := by
  intro h
  have hh := deduct 21 131076 (cofactor 6 false) paidList6 innerValid6 h
  obtain ⟨b,hc⟩ := pairCut left6 14 3 18 ⟨word 8,by decide +kernel⟩
    (fun b => ⟨word 0,word 131076,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 8192,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 131076,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap6 (clip (clip left6 14 b) 3 false) 18 hc
  have eq : (fun x => (clip (clip left6 14 b) 3 false) (x ∘ costMap6)) = donor := funext (mapLow6 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList7 : List Ticket := [(20,32),(19,16),(14,8),(12,4194304),(11,8192),(10,262144),(9,131072),(4,32768),(3,8192)]
private def costMap7 : Fin 24 → Fin 12 := ![0,0,3,0,0,2,4,0,1,0,0,0,0,8,0,11,9,7,5,0,0,6,0,10]
private abbrev left7 := leave (cofactor 7 false) paidList7
set_option maxHeartbeats 2000000 in
private theorem innerValid7 : certified (cofactor 7 false) 2097153 paidList7 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow7 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left7 22 b) 1 false) (x ∘ costMap7) = donor x := by
  cases b <;> simp [clip,left7,leave,paidList7,cofactor,target,Function.update,Function.comp_def,costMap7,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar7 : ¬ HasCircuitSize 24 (cofactor 7 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 7 false) paidList7 innerValid7 h
  obtain ⟨b,hc⟩ := pairCut left7 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap7 (clip (clip left7 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left7 22 b) 1 false) (x ∘ costMap7)) = donor := funext (mapLow7 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList8 : List Ticket := [(22,2),(20,32),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(3,8192),(1,65536)]
private def costMap8 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left8 := leave (cofactor 8 false) paidList8
set_option maxHeartbeats 2000000 in
private theorem innerValid8 : certified (cofactor 8 false) 2097153 paidList8 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow8 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left8 19 b) 4 false) (x ∘ costMap8) = donor x := by
  cases b <;> simp [clip,left8,leave,paidList8,cofactor,target,Function.update,Function.comp_def,costMap8,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar8 : ¬ HasCircuitSize 24 (cofactor 8 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 8 false) paidList8 innerValid8 h
  obtain ⟨b,hc⟩ := pairCut left8 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap8 (clip (clip left8 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left8 19 b) 4 false) (x ∘ costMap8)) = donor := funext (mapLow8 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList9 : List Ticket := [(22,2),(20,32),(14,8),(12,8388608),(11,8192),(10,262144),(8,65536),(3,8192),(1,65536)]
private def costMap9 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left9 := leave (cofactor 9 false) paidList9
set_option maxHeartbeats 2000000 in
private theorem innerValid9 : certified (cofactor 9 false) 2097153 paidList9 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow9 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left9 19 b) 4 false) (x ∘ costMap9) = donor x := by
  cases b <;> simp [clip,left9,leave,paidList9,cofactor,target,Function.update,Function.comp_def,costMap9,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar9 : ¬ HasCircuitSize 24 (cofactor 9 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 9 false) paidList9 innerValid9 h
  obtain ⟨b,hc⟩ := pairCut left9 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap9 (clip (clip left9 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left9 19 b) 4 false) (x ∘ costMap9)) = donor := funext (mapLow9 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList10 : List Ticket := [(22,2),(20,32),(14,8),(12,8388608),(11,8192),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap10 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left10 := leave (cofactor 10 false) paidList10
set_option maxHeartbeats 2000000 in
private theorem innerValid10 : certified (cofactor 10 false) 2097153 paidList10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow10 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left10 19 b) 4 false) (x ∘ costMap10) = donor x := by
  cases b <;> simp [clip,left10,leave,paidList10,cofactor,target,Function.update,Function.comp_def,costMap10,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar10 : ¬ HasCircuitSize 24 (cofactor 10 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 10 false) paidList10 innerValid10 h
  obtain ⟨b,hc⟩ := pairCut left10 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap10 (clip (clip left10 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left10 19 b) 4 false) (x ∘ costMap10)) = donor := funext (mapLow10 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList11 : List Ticket := [(22,2),(20,32),(14,8),(12,8388608),(10,262144),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap11 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left11 := leave (cofactor 11 false) paidList11
set_option maxHeartbeats 2000000 in
private theorem innerValid11 : certified (cofactor 11 false) 2097153 paidList11 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow11 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left11 19 b) 4 false) (x ∘ costMap11) = donor x := by
  cases b <;> simp [clip,left11,leave,paidList11,cofactor,target,Function.update,Function.comp_def,costMap11,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar11 : ¬ HasCircuitSize 24 (cofactor 11 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 11 false) paidList11 innerValid11 h
  obtain ⟨b,hc⟩ := pairCut left11 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap11 (clip (clip left11 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left11 19 b) 4 false) (x ∘ costMap11)) = donor := funext (mapLow11 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList12 : List Ticket := [(22,2),(20,32),(14,8),(11,8192),(10,262144),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap12 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left12 := leave (cofactor 12 false) paidList12
set_option maxHeartbeats 2000000 in
private theorem innerValid12 : certified (cofactor 12 false) 2097153 paidList12 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow12 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left12 19 b) 4 false) (x ∘ costMap12) = donor x := by
  cases b <;> simp [clip,left12,leave,paidList12,cofactor,target,Function.update,Function.comp_def,costMap12,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar12 : ¬ HasCircuitSize 24 (cofactor 12 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 12 false) paidList12 innerValid12 h
  obtain ⟨b,hc⟩ := pairCut left12 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap12 (clip (clip left12 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left12 19 b) 4 false) (x ∘ costMap12)) = donor := funext (mapLow12 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList13 : List Ticket := [(18,8),(17,4),(12,16384),(11,524288),(10,1048576),(9,524288),(7,32768),(3,16384),(2,8388608)]
private def costMap13 : Fin 24 → Fin 12 := ![0,0,0,0,3,1,2,0,4,0,0,0,0,0,8,10,9,0,0,7,5,11,0,6]
private abbrev left13 := leave (cofactor 13 false) paidList13
set_option maxHeartbeats 2000000 in
private theorem innerValid13 : certified (cofactor 13 false) 8388609 paidList13 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow13 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left13 22 b) 1 false) (x ∘ costMap13) = donor x := by
  cases b <;> simp [clip,left13,leave,paidList13,cofactor,target,Function.update,Function.comp_def,costMap13,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar13 : ¬ HasCircuitSize 24 (cofactor 13 false) 30 := by
  intro h
  have hh := deduct 21 8388609 (cofactor 13 false) paidList13 innerValid13 h
  obtain ⟨b,hc⟩ := pairCut left13 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap13 (clip (clip left13 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left13 22 b) 1 false) (x ∘ costMap13)) = donor := funext (mapLow13 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList14 : List Ticket := [(22,2),(20,32),(12,8388608),(11,8192),(10,262144),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap14 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left14 := leave (cofactor 14 false) paidList14
set_option maxHeartbeats 2000000 in
private theorem innerValid14 : certified (cofactor 14 false) 2097153 paidList14 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow14 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left14 19 b) 4 false) (x ∘ costMap14) = donor x := by
  cases b <;> simp [clip,left14,leave,paidList14,cofactor,target,Function.update,Function.comp_def,costMap14,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar14 : ¬ HasCircuitSize 24 (cofactor 14 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 14 false) paidList14 innerValid14 h
  obtain ⟨b,hc⟩ := pairCut left14 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap14 (clip (clip left14 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left14 19 b) 4 false) (x ∘ costMap14)) = donor := funext (mapLow14 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList15 : List Ticket := [(21,1),(19,16),(12,16384),(11,8192),(10,262144),(9,131072),(7,131072),(4,16384),(0,8388608)]
private def costMap15 : Fin 24 → Fin 12 := ![0,0,0,3,0,1,2,0,4,0,0,0,0,10,8,0,9,11,7,0,5,0,0,6]
private abbrev left15 := leave (cofactor 15 false) paidList15
set_option maxHeartbeats 2000000 in
private theorem innerValid15 : certified (cofactor 15 false) 8388612 paidList15 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow15 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left15 22 b) 1 false) (x ∘ costMap15) = donor x := by
  cases b <;> simp [clip,left15,leave,paidList15,cofactor,target,Function.update,Function.comp_def,costMap15,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar15 : ¬ HasCircuitSize 24 (cofactor 15 false) 30 := by
  intro h
  have hh := deduct 21 8388612 (cofactor 15 false) paidList15 innerValid15 h
  obtain ⟨b,hc⟩ := pairCut left15 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 8388612,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 8388612,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap15 (clip (clip left15 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left15 22 b) 1 false) (x ∘ costMap15)) = donor := funext (mapLow15 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList16 : List Ticket := [(19,16),(18,8),(12,16384),(10,1048576),(9,131072),(8,8388608),(6,16384),(4,16384),(1,4194304)]
private def costMap16 : Fin 24 → Fin 12 := ![0,0,2,0,0,1,0,3,0,0,0,4,0,9,0,10,0,8,0,0,5,6,7,11]
private abbrev left16 := leave (cofactor 16 false) paidList16
set_option maxHeartbeats 2000000 in
private theorem innerValid16 : certified (cofactor 16 false) 2097153 paidList16 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow16 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left16 14 b) 3 false) (x ∘ costMap16) = donor x := by
  cases b <;> simp [clip,left16,leave,paidList16,cofactor,target,Function.update,Function.comp_def,costMap16,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar16 : ¬ HasCircuitSize 24 (cofactor 16 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 16 false) paidList16 innerValid16 h
  obtain ⟨b,hc⟩ := pairCut left16 14 3 18 ⟨word 8,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 8192,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap16 (clip (clip left16 14 b) 3 false) 18 hc
  have eq : (fun x => (clip (clip left16 14 b) 3 false) (x ∘ costMap16)) = donor := funext (mapLow16 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList17 : List Ticket := [(20,32),(18,8),(12,16384),(11,8192),(10,2097152),(9,524288),(7,32768),(3,8192),(2,8192)]
private def costMap17 : Fin 24 → Fin 12 := ![0,0,0,0,3,1,2,0,4,0,0,0,0,5,8,10,9,0,0,7,0,11,0,6]
private abbrev left17 := leave (cofactor 17 false) paidList17
set_option maxHeartbeats 2000000 in
private theorem innerValid17 : certified (cofactor 17 false) 8388609 paidList17 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow17 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left17 22 b) 1 false) (x ∘ costMap17) = donor x := by
  cases b <;> simp [clip,left17,leave,paidList17,cofactor,target,Function.update,Function.comp_def,costMap17,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar17 : ¬ HasCircuitSize 24 (cofactor 17 false) 30 := by
  intro h
  have hh := deduct 21 8388609 (cofactor 17 false) paidList17 innerValid17 h
  obtain ⟨b,hc⟩ := pairCut left17 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 8388609,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap17 (clip (clip left17 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left17 22 b) 1 false) (x ∘ costMap17)) = donor := funext (mapLow17 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList18 : List Ticket := [(20,32),(14,8),(12,4194304),(11,8192),(10,2097152),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap18 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,0,0,0,6,5,11]
private abbrev left18 := leave (cofactor 18 false) paidList18
set_option maxHeartbeats 2000000 in
private theorem innerValid18 : certified (cofactor 18 false) 2097153 paidList18 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow18 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left18 19 b) 4 false) (x ∘ costMap18) = donor x := by
  cases b <;> simp [clip,left18,leave,paidList18,cofactor,target,Function.update,Function.comp_def,costMap18,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar18 : ¬ HasCircuitSize 24 (cofactor 18 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 18 false) paidList18 innerValid18 h
  obtain ⟨b,hc⟩ := pairCut left18 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap18 (clip (clip left18 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left18 19 b) 4 false) (x ∘ costMap18)) = donor := funext (mapLow18 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList19 : List Ticket := [(20,32),(14,8),(12,4194304),(11,8192),(10,262144),(9,131072),(7,32768),(4,32768),(3,8192)]
private def costMap19 : Fin 24 → Fin 12 := ![0,0,3,0,0,2,4,0,1,0,0,0,0,8,0,11,9,7,5,0,0,6,0,10]
private abbrev left19 := leave (cofactor 19 false) paidList19
set_option maxHeartbeats 2000000 in
private theorem innerValid19 : certified (cofactor 19 false) 2097153 paidList19 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow19 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left19 22 b) 1 false) (x ∘ costMap19) = donor x := by
  cases b <;> simp [clip,left19,leave,paidList19,cofactor,target,Function.update,Function.comp_def,costMap19,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar19 : ¬ HasCircuitSize 24 (cofactor 19 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 19 false) paidList19 innerValid19 h
  obtain ⟨b,hc⟩ := pairCut left19 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap19 (clip (clip left19 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left19 22 b) 1 false) (x ∘ costMap19)) = donor := funext (mapLow19 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList20 : List Ticket := [(22,2),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap20 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left20 := leave (cofactor 20 false) paidList20
set_option maxHeartbeats 2000000 in
private theorem innerValid20 : certified (cofactor 20 false) 2097153 paidList20 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow20 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left20 19 b) 4 false) (x ∘ costMap20) = donor x := by
  cases b <;> simp [clip,left20,leave,paidList20,cofactor,target,Function.update,Function.comp_def,costMap20,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar20 : ¬ HasCircuitSize 24 (cofactor 20 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 20 false) paidList20 innerValid20 h
  obtain ⟨b,hc⟩ := pairCut left20 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap20 (clip (clip left20 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left20 19 b) 4 false) (x ∘ costMap20)) = donor := funext (mapLow20 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList21 : List Ticket := [(22,2),(20,32),(12,16384),(11,8192),(10,262144),(9,131072),(8,65536),(1,65536),(0,32768)]
private def costMap21 : Fin 24 → Fin 12 := ![0,0,1,0,0,3,2,4,0,0,0,0,0,10,11,7,8,9,6,0,0,0,0,5]
private abbrev left21 := leave (cofactor 21 false) paidList21
set_option maxHeartbeats 2000000 in
private theorem innerValid21 : certified (cofactor 21 false) 262152 paidList21 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow21 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left21 19 b) 4 false) (x ∘ costMap21) = donor x := by
  cases b <;> simp [clip,left21,leave,paidList21,cofactor,target,Function.update,Function.comp_def,costMap21,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar21 : ¬ HasCircuitSize 24 (cofactor 21 false) 30 := by
  intro h
  have hh := deduct 21 262152 (cofactor 21 false) paidList21 innerValid21 h
  obtain ⟨b,hc⟩ := pairCut left21 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 16384,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap21 (clip (clip left21 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left21 19 b) 4 false) (x ∘ costMap21)) = donor := funext (mapLow21 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList22 : List Ticket := [(20,32),(14,8),(12,8388608),(11,8192),(10,262144),(9,131072),(8,65536),(3,8192),(1,65536)]
private def costMap22 : Fin 24 → Fin 12 := ![0,0,2,0,0,3,4,1,0,0,0,0,0,8,0,10,7,9,5,0,0,6,0,11]
private abbrev left22 := leave (cofactor 22 false) paidList22
set_option maxHeartbeats 2000000 in
private theorem innerValid22 : certified (cofactor 22 false) 2097153 paidList22 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow22 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left22 19 b) 4 false) (x ∘ costMap22) = donor x := by
  cases b <;> simp [clip,left22,leave,paidList22,cofactor,target,Function.update,Function.comp_def,costMap22,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar22 : ¬ HasCircuitSize 24 (cofactor 22 false) 30 := by
  intro h
  have hh := deduct 21 2097153 (cofactor 22 false) paidList22 innerValid22 h
  obtain ⟨b,hc⟩ := pairCut left22 19 4 18 ⟨word 16,by decide +kernel⟩
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 32768,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 2097153,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap22 (clip (clip left22 19 b) 4 false) 18 hc
  have eq : (fun x => (clip (clip left22 19 b) 4 false) (x ∘ costMap22)) = donor := funext (mapLow22 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private def paidList23 : List Ticket := [(21,1),(20,32),(12,16384),(11,8192),(10,262144),(9,131072),(7,32768),(2,8192),(0,32768)]
private def costMap23 : Fin 24 → Fin 12 := ![0,0,0,0,3,2,1,0,4,0,0,0,0,11,10,8,9,5,6,7,0,0,0,0]
private abbrev left23 := leave (cofactor 23 false) paidList23
set_option maxHeartbeats 2000000 in
private theorem innerValid23 : certified (cofactor 23 false) 262152 paidList23 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem mapLow23 (b : Bool) (x : Fin 12 → Bool) : (clip (clip left23 22 b) 1 false) (x ∘ costMap23) = donor x := by
  cases b <;> simp [clip,left23,leave,paidList23,cofactor,target,Function.update,Function.comp_def,costMap23,donor] <;> ac_rfl
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem lowEar23 : ¬ HasCircuitSize 24 (cofactor 23 false) 30 := by
  intro h
  have hh := deduct 21 262152 (cofactor 23 false) paidList23 innerValid23 h
  obtain ⟨b,hc⟩ := pairCut left23 22 1 18 ⟨word 2,by decide +kernel⟩
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 65536,by cases b <;> decide +kernel⟩)
    (fun b => ⟨word 0,word 262152,by cases b <;> decide +kernel⟩) hh
  have rr := relabel_size costMap23 (clip (clip left23 22 b) 1 false) 18 hc
  have eq : (fun x => (clip (clip left23 22 b) 1 false) (x ∘ costMap23)) = donor := funext (mapLow23 b)
  rw [eq] at rr
  exact PEqualNP.Outside.L_meta_9752 rr

private theorem everyLow (p : Fin 24) : ¬ HasCircuitSize 24 (cofactor p false) 30 := by
  fin_cases p
  · exact lowEar0
  · exact lowEar1
  · exact lowEar2
  · exact lowEar3
  · exact lowEar4
  · exact lowEar5
  · exact lowEar6
  · exact lowEar7
  · exact lowEar8
  · exact lowEar9
  · exact lowEar10
  · exact lowEar11
  · exact lowEar12
  · exact lowEar13
  · exact lowEar14
  · exact lowEar15
  · exact lowEar16
  · exact lowEar17
  · exact lowEar18
  · exact lowEar19
  · exact lowEar20
  · exact lowEar21
  · exact lowEar22
  · exact lowEar23

theorem physical34 : ¬ HasCircuitSize 24 target 33 := by
  intro h
  obtain ⟨p,dep,hp⟩ := split 33 h
  have lo (s : Nat) (hs : HasCircuitSize 24 (cofactor p false) s) : 31 ≤ s := by
    by_contra! hc
    obtain ⟨C,fan,small,ev⟩ := hs
    exact everyLow p ⟨C,fan,by omega,ev⟩
  have hi (s : Nat) (hs : HasCircuitSize 24 (cofactor p true) s) : 30 ≤ s := by
    by_contra! hc
    obtain ⟨C,fan,small,ev⟩ := hs
    exact around p true ⟨C,fan,by omega,ev⟩
  rcases hp with ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩ | ⟨⟨a,da,ha⟩,⟨b,db,hb⟩⟩
  all_goals have hlow := lo a ha
  all_goals have hhigh := hi b hb
  all_goals omega
end PEqualNP.Outside.L_meta_9829.Paid
