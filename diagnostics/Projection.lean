import Mathlib
import PEqualNP.Defs

namespace Projection4817
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Adapts the constant propagation pass from L-meta-2038 for a single input bit.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]


private def marked (m : ℕ) (l : List ℕ) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (m ≤ l.getD i 0)

private def uses (m : ℕ) (l : List ℕ) (g : Gate) : Bool :=
  (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
    fun i => decide (m ≤ l.getD i 0)

private lemma normalized (m : ℕ) (l : List ℕ) (g : Gate) (hg : OkGate g) :
    marked m l (normGate g) = uses m l g := by
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [marked,uses,normGate,GateOp.eval,OkGate]

private lemma count_normalized (m : ℕ) (l : List ℕ) (gs : List Gate) (h : ∀ g ∈ gs, OkGate g) :
    (gs.map normGate).countP (marked m l) = gs.countP (uses m l) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.countP_cons,normalized m l g (h g List.mem_cons_self),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

private lemma count_delete (m : ℕ) (l : List ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (h : ∀ g ∈ gs, NOkGate g)
    (fixed : ∀ i, m ≤ l.getD i 0 →
      i < acc.1.length ∧ acc.1.getD i (Sum.inl false) = Sum.inl (l.getD i 0 == m+1)) :
    (elimPass m gs acc).2.length + gs.countP (marked m l) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    have kept (i : ℕ) (hi : m ≤ l.getD i 0) :
        i < (elimStep m acc g).1.length ∧
        (elimStep m acc g).1.getD i (Sum.inl false) = Sum.inl (l.getD i 0 == m+1) := by
      obtain ⟨hlt,eq⟩ := fixed i hi
      refine ⟨by simp [elimStep]; omega, ?_⟩
      unfold elimStep
      rw [getD_snoc_lt _ _ _ _ hlt,eq]
    have ht := ih (elimStep m acc g) (fun a ha => h a (List.mem_cons_of_mem _ ha)) kept
    let ins := g.inputs.map fun j => acc.1.getD j (Sum.inl false)
    let part := simplifyGate g.op (m + acc.2.length) ins
    have hbnd : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length ≤ _
      rw [List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    rw [elimPass_cons, List.countP_cons, List.length_cons]
    cases he : marked m l g with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | true =>
      have hn : part.1 = none := by
        have hg := h g List.mem_cons_self
        apply simplifyGate_none_of_const _ _ _ hg.1.1
        · simpa [ins] using hg.1.2
        · intro hn
          simpa [ins] using hg.2 hn
        · obtain ⟨i,hi,eq⟩ := List.any_eq_true.mp he
          exact ⟨_,List.mem_map.mpr ⟨i,hi,(fixed i (by simpa using eq)).2⟩⟩
      have hd : (elimStep m acc g).2.length = acc.2.length := by
        change (acc.2 ++ part.1.toList).length = _
        simp [hn]
      simp only [↓reduceIte]
      omega

private def seed (m : ℕ) (l : List ℕ) : List (Bool ⊕ ℕ) × List Gate :=
  (l.map (fun j => if j < m then Sum.inr j else Sum.inl (j == m+1)), [])

private lemma init (m : ℕ) (l : List ℕ) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (l.map fun j => ((List.ofFn x).getD j false || (j == m+1))) (seed m l) := by
  refine ⟨by simp,by simp [seed],?_⟩
  intro i
  by_cases hi : i < l.length
  · let j := l[i]
    have h₁ : (seed m l).1.getD i (Sum.inl false) =
        (if j < m then Sum.inr j else Sum.inl (j == m+1)) := by
      rw [List.getD_eq_getElem _ _ (by simpa [seed] using hi)]
      simp [seed,j]
    have h₂ : (l.map fun k => ((List.ofFn x).getD k false || (k == m+1))).getD i false =
        ((List.ofFn x).getD j false || (j == m+1)) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [j]
    rw [h₁,h₂]
    by_cases hj : j < m
    · have hn : j ≠ m+1 := by omega
      simp [hj,hn,statValid,statVal,seed,wiresFrom]
    · simp [hj,statValid,statVal,List.getD_eq_default (List.ofFn x) false (by simpa using Nat.le_of_not_gt hj)]
  · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩

theorem project (m : ℕ) (hm : 0 < m) (l : List ℕ) (C : Circuit) (hc : FanInTwo C)
    (hnc : ∃ x y : Fin m → Bool,
      C.eval (l.map fun i => ((List.ofFn x).getD i false || (i == m+1))) ≠
      C.eval (l.map fun i => ((List.ofFn y).getD i false || (i == m+1)))) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + C.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          fun i => decide (m ≤ l.getD i 0)) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (l.map fun i => ((List.ofFn x).getD i false || (i == m+1))) := by
  let gs := C.gates.map normGate
  let acc := elimPass m gs (seed m l)
  have hn : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hc a ha)
  have hs : acc.2.length + C.gates.countP (uses m l) ≤ C.size := by
    have fixed (i : ℕ) (hi : m ≤ l.getD i 0) : i < (seed m l).1.length ∧
        (seed m l).1.getD i (Sum.inl false) = Sum.inl (l.getD i 0 == m+1) := by
      have hlt : i < l.length := by
        by_contra! ge
        rw [List.getD_eq_default _ _ ge] at hi
        omega
      have eq : m ≤ l[i] := by simpa only [List.getD_eq_getElem _ _ hlt] using hi
      refine ⟨by simpa [seed] using hlt,?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa [seed] using hlt)]
      simp [seed,not_lt.mpr eq,List.getD_eq_getElem _ _ hlt]
    have h := count_delete m l gs (seed m l) hn fixed
    change acc.2.length + gs.countP (marked m l) ≤ 0 + gs.length at h
    rw [show gs.countP (marked m l) = C.gates.countP (uses m l) from count_normalized _ _ _ hc] at h
    have len : gs.length = C.size := List.length_map _
    omega
  have ev (x : Fin m → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        C.eval (l.map fun i => ((List.ofFn x).getD i false || (i == m+1))) := by
    let xs := l.map (fun i => ((List.ofFn x).getD i false || (i == m+1)))
    have h := ((elimInv_pass m (List.ofFn x) gs xs (seed m l)
      (fun g hg => (hn g hg).1) (init m l x)).2.2 C.output).2
    exact h.trans (congrArg (fun w => w.getD C.output false) (wiresFrom_norm C.gates xs))
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl v =>
    obtain ⟨x,y,diff⟩ := hnc
    have hx := ev x
    have hy := ev y
    rw [ho] at hx hy
    exact False.elim (diff (hx.symm.trans hy))
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elimPass_ok m gs _ (by simp [seed]),hs,?_⟩
    intro x
    have hx := ev x
    rw [ho] at hx
    exact hx

end Projection4817
