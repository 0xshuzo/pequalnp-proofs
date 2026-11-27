import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_17467.GraphSource

private def left (m : ℕ) {n : ℕ} (a : Fin n) : Fin (n + m) := Fin.castAdd m a
private def right (n : ℕ) {m : ℕ} (b : Fin m) : Fin (n + m) := Fin.natAdd n b

private lemma disjoint_lr {n m : ℕ} (a : Fin n) (b : Fin m) : left m a ≠ right n b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at h'
  have := a.isLt
  omega

private def graph (n m : ℕ) (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n + m)) where
  Adj := fun u v => ∃ p ∈ E, u = left m p.1 ∧ v = right n p.2 ∨ v = left m p.1 ∧ u = right n p.2
  symm := ⟨by intro u v; rintro ⟨p, hp, h | h⟩; exact ⟨p, hp, Or.inr h⟩; exact ⟨p, hp, Or.inl h⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨p, hp, h | h⟩
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)⟩

private def edge {n m : ℕ} (p : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(left m p.1, right n p.2)

private lemma edge_injective {n m : ℕ} : Function.Injective (@edge n m) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with h | h
  · apply Prod.ext
    · apply Fin.ext
      simpa [left] using congrArg Fin.val h.1
    · apply Fin.ext
      have hh := congrArg Fin.val h.2
      simp [right] at hh
      omega
  · exact (disjoint_lr p.1 q.2 h.1).elim

private lemma edges (n m : ℕ) (E : Finset (Fin n × Fin m)) :
    (graph n m E).edgeSet = ↑(E.image edge) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨p, hp, h | h⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2]⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2, Sym2.eq_swap]⟩
    · rintro ⟨p, hp, he⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact ⟨p, hp, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
      · exact ⟨p, hp, Or.inr ⟨h.1.symm, h.2.symm⟩⟩

end PEqualNP.Outside.L_meta_17467.GraphSource

theorem PEqualNP.Outside.L_meta_17467.GraphSource : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) → ∃ (x8 : SimpleGraph (Fin (x1 + x2))), (∀ (x9 x10 : Fin (x1 + x2)), x8.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) ∧ x8.edgeSet.ncard = x3.card ∧ ∀ (x9 : Finset (Fin (x1 + x2))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x8 x9 → x4.card ≤ x9.card := by
  classical
  intro n m E M hME hleft hright
  let G := PEqualNP.Outside.L_meta_17467.GraphSource.graph n m E
  refine ⟨G, ?_, ?_, ?_⟩
  · intro u v
    rfl
  · rw [PEqualNP.Outside.L_meta_17467.GraphSource.edges, Set.ncard_coe_finset]
    exact Finset.card_image_iff.mpr PEqualNP.Outside.L_meta_17467.GraphSource.edge_injective.injOn
  · intro S hS
    let f : Fin n × Fin m → Fin (n+m) := fun p =>
      if PEqualNP.Outside.L_meta_17467.GraphSource.left m p.1 ∈ S then PEqualNP.Outside.L_meta_17467.GraphSource.left m p.1 else PEqualNP.Outside.L_meta_17467.GraphSource.right n p.2
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have hadj : G.Adj (PEqualNP.Outside.L_meta_17467.GraphSource.left m p.1) (PEqualNP.Outside.L_meta_17467.GraphSource.right n p.2) :=
        ⟨p, hME hp, Or.inl ⟨rfl, rfl⟩⟩
      have hc := hS _ _ hadj
      dsimp [f]
      split_ifs <;> tauto
    · intro p hp q hq he
      dsimp [f] at he
      split_ifs at he with hpS hqS
      · apply hleft p hp q hq
        apply Fin.ext
        simpa [PEqualNP.Outside.L_meta_17467.GraphSource.left] using congrArg Fin.val he
      · exact (PEqualNP.Outside.L_meta_17467.GraphSource.disjoint_lr p.1 q.2 he).elim
      · exact (PEqualNP.Outside.L_meta_17467.GraphSource.disjoint_lr q.1 p.2 he.symm).elim
      · apply hright p hp q hq
        apply Fin.ext
        have hh := congrArg Fin.val he
        simp [PEqualNP.Outside.L_meta_17467.GraphSource.right] at hh
        omega

namespace PEqualNP.Outside.L_meta_17467.ForestSource

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
open SimpleGraph

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

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

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


variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [(Sum.inl b : Stat)]

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
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

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
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

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
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
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
  have h' := PEqualNP.Outside.L_meta_17467.ForestSource.gate_elim n _ b s hdep' hnc' hg
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

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

theorem F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

theorem F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

theorem F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

theorem restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

theorem restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

theorem cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

theorem ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

theorem claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

end PEqualNP.Outside.L_meta_17467.ForestSource

theorem PEqualNP.Outside.L_meta_17467.ForestSource : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3.IsAcyclic → (∀ (x6 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x6 → x2 ≤ x6.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin x1 → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → x3.edgeSet.ncard + x2 ≤ x4.size + (1 : ℕ) := by
  intro n t G C hac hmin hM hev
  by_cases hE : ∃ (a : Fin n) (b : Fin n), G.Adj a b
  · have hC : PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.Outside.L_meta_17467.ForestSource.F G ∅) C.size := by
      refine ⟨C, fun g hg => ⟨?_, (hM g hg).2⟩, le_refl _, fun x => ?_⟩
      · rcases (hM g hg).1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rw [Bool.eq_iff_iff, hev x, PEqualNP.Outside.L_meta_17467.ForestSource.F_true]
        simp
    have h := PEqualNP.Outside.L_meta_17467.ForestSource.claimQ G.edgeSet.ncard n G ∅ t C.size rfl hac
      (fun _ _ _ => Finset.notMem_empty _) (fun T hT => hmin T hT) (Or.inr hE) hC
    simpa using h
  · have h0 : t ≤ (∅ : Finset (Fin n)).card := by
      refine hmin ∅ ?_
      intro u v huv
      exact absurd ⟨u, v, huv⟩ hE
    have he : G.edgeSet = ∅ := by
      ext e
      refine e.ind ?_
      intro u v
      simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
      intro huv
      exact hE ⟨u, v, huv⟩
    rw [he, Set.ncard_empty]
    simp at h0
    omega

namespace PEqualNP.Outside.L_meta_17467.StarSource

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, ∃ b : Bool, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b))

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, b0, hin, ha, hc⟩
      exact ⟨a, c, b0, hin, hSub b0 ha, hSub (!b0) hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {a c : ℕ} (ha : a ∈ S b) (hc : c ∈ S (!b)) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt b a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt (!b) c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, b, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, ∃ b : Bool, (gateAt C j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b)) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end PEqualNP.Outside.L_meta_17467.StarSource

open PEqualNP.Outside.L_meta_17467.StarSource in
theorem PEqualNP.Outside.L_meta_17467.StarSource.stars :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),
      (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →
        ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
          PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
            x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
              (∀ (x9 : Fin (x1 + x2) → Bool),
                PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
                  Decidable.decide
                    (∃ (x10 : Fin x1) (x11 : Fin x2),
                      (x10, x11) ∈ x3 ∧
                        x9 (Fin.castAdd x2 x10) = Bool.true ∧
                          x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
                have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate :=
                  PEqualNP.MetaComplexity.NestedCover.gateAt x7;
                (∀ (x10 : Bool), ∀ x11 ∈ x8 x10,
                  x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
                    ∃ x13 < x7.size,
                      x11 = x1 + x2 + x13 ∧
                        (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                          ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧
                  ∀ x10 < x7.size,
                    (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                      ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
                        (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

/- The star construction above follows L-meta-2874. The matching and cover
   construction below follows the Hall argument of R-meta-2685-41. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.L_meta_17467.StarSource.matchingCircuit : ∀ (n m : ℕ) (F : Finset (Fin n × Fin m)),
      ∃ (T : Finset (Fin n × Fin m)) (D : Circuit),
        T ⊆ F ∧ Set.InjOn Prod.fst (T : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (T : Set (Fin n × Fin m)) ∧
        D.size ≤ F.card + T.card - 1 ∧ IsAO2 (n+m) D ∧
        ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
          (∃ p l, (p,l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
  classical
  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  intro n m F
  obtain ⟨T,A,B,ss,hr,hc,cover,count⟩ := matchingCover n m F
  obtain ⟨D,_,dAO,db,de,_⟩ := PEqualNP.Outside.L_meta_17467.StarSource.stars n m F A B cover
  exact ⟨T,D,ss,hr,hc,by omega,dAO,de⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_17467.StarSource.matchingCircuitExplicit : ∀ (n m : ℕ) (F : Finset (Fin n × Fin m)),
      ∃ (T : Finset (Fin n × Fin m)) (D : Circuit),
        T ⊆ F ∧ (∀ e ∈ T, ∀ f ∈ T, e.1 = f.1 → e = f) ∧
        (∀ e ∈ T, ∀ f ∈ T, e.2 = f.2 → e = f) ∧
        D.size ≤ F.card + T.card - 1 ∧ IsAO2 (n+m) D ∧
        ∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide
          (∃ p l, (p,l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) := by
  intro n m F
  obtain ⟨T,D,ss,hr,hc,hd,ha,hf⟩ := PEqualNP.Outside.L_meta_17467.StarSource.matchingCircuit n m F
  exact ⟨T,D,ss,fun e he f h eq => hr he h eq,fun e he f h eq => hc he h eq,hd,ha,hf⟩

namespace PEqualNP.Outside.L_meta_17467

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

private def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wiresLen {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  unfold Circuit.wires Circuit.size
  have h (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega
  rw [h]
  simp

private lemma gateGet {C : Circuit} {j : ℕ} (hj : j < C.size) :
    gateAt C j = C.gates[j]'hj := by
  simp [gateAt, List.getD, List.getElem?_eq_getElem hj]

private lemma gateSpec {n : ℕ} {C : Circuit} (hc : IsAO2 n C) {j : ℕ} (hj : j < C.size) :
    ∃ (op : GateOp) (a b : ℕ), gateAt C j = ⟨op, [a, b]⟩ ∧
      (op = .and ∨ op = .or) ∧ a < n + j ∧ b < n + j := by
  have hm : gateAt C j ∈ C.gates := gateGet hj ▸ List.getElem_mem hj
  have hlen := hc.2.2 _ hm
  have ht : ∀ L : List ℕ, L.length = 2 → ∃ a b, L = [a,b] := by
    intro L h
    match L with
    | [a,b] => exact ⟨a,b,rfl⟩
    | [] | [_] | _ :: _ :: _ :: _ => simp at h
  obtain ⟨a,b,hi⟩ := ht _ hlen
  have hg : gateAt C j = ⟨(gateAt C j).op, [a,b]⟩ := by
    exact congrArg (Gate.mk (gateAt C j).op) hi
  exact ⟨_, a, b, hg, hc.1 _ hm,
    hc.2.1 j hj a (by rw [hi]; simp), hc.2.1 j hj b (by rw [hi]; simp)⟩

private def push (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

private lemma pushSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (push n C op a b).size = C.size + 1 := by simp [push, Circuit.size]

private lemma pushLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ}
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (push n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.1 g hg
    · have e := List.mem_singleton.mp hg
      simpa [e] using hop
  · intro j hj w hw
    have hj' : j < C.size + 1 := by rw [← pushSize n C op a b]; exact hj
    rw [gateGet hj] at hw
    by_cases h : j < C.size
    · rw [show (push n C op a b).gates[j]'hj = C.gates[j]'h from
        List.getElem_append_left h] at hw
      exact hc.2.1 j h w (by rwa [gateGet h])
    · have e : j = C.size := by omega
      subst j
      have hlast : (push n C op a b).gates[C.size]'hj = ⟨op, [a,b]⟩ := by
        simp [push, Circuit.size]
      rw [hlast] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.2.2 g hg
    · simp [List.mem_singleton.mp hg]

private lemma pushWires {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (push n C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [wire C x a, wire C x b]] := by
  simp [push, Circuit.wires, List.foldl_append, wire]

private lemma pushOld {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + C.size) :
    wire (push n C op a b) x w = wire C x w := by
  unfold wire
  rw [pushWires, List.getD_append _ _ _ _ (by rwa [wiresLen])]

private lemma pushNew {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    wire (push n C op a b) x (n + C.size) = op.eval [wire C x a, wire C x b] := by
  conv_lhs => unfold wire; rw [pushWires, ← wiresLen C x]
  simp

private def firstGates (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.take k, 0⟩

private lemma prefixNext {C : Circuit} {k : ℕ} (hk : k < C.size) :
    (firstGates C (k + 1)).gates = (firstGates C k).gates ++ [gateAt C k] := by
  rw [gateGet hk]
  exact List.take_succ_eq_append_getElem hk

private lemma prefixSize {C : Circuit} {k : ℕ} (hk : k ≤ C.size) :
    (firstGates C k).size = k := by simp [firstGates, Circuit.size, Nat.min_eq_left (show k ≤ C.gates.length from hk)]

private lemma prefixOld {n k : ℕ} {C : Circuit} (hk : k < C.size) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + k) :
    wire (firstGates C (k + 1)) x w = wire (firstGates C k) x w := by
  unfold wire Circuit.wires
  rw [prefixNext hk, List.foldl_append]
  exact List.getD_append _ _ _ _ (by
    change w < ((firstGates C k).wires (List.ofFn x)).length
    rwa [wiresLen, prefixSize (Nat.le_of_lt hk)])

private lemma prefixNew {n k a b : ℕ} {C : Circuit} {op : GateOp}
    (hk : k < C.size) (hg : gateAt C k = ⟨op, [a,b]⟩) (x : Fin n → Bool) :
    wire (firstGates C (k + 1)) x (n + k) =
      op.eval [wire (firstGates C k) x a, wire (firstGates C k) x b] := by
  calc
    _ = wire (push n (firstGates C k) op a b) x (n + (firstGates C k).size) := by
      unfold wire Circuit.wires
      rw [prefixNext hk, hg, prefixSize (Nat.le_of_lt hk)]
      rfl
    _ = _ := pushNew _ _ _ _ _

private def pinned {n : ℕ} (v : Fin n) (x : Fin n → Bool) (w : Fin n) : Bool :=
  if w = v then false else x w

private def read {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : Option ℕ) : Bool :=
  w.elim false (wire C x)

private def available (bound : ℕ) (w : Option ℕ) : Prop :=
  ∀ a, w = some a → a < bound

private lemma advance {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : Option ℕ}
    (ha : available (n + C.size) a) (hb : available (n + C.size) b) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ available (n + S.size) u ∧
      C.size ≤ S.size ∧ S.size ≤ C.size + 1 ∧
      ((a = none ∨ b = none) → S.size = C.size) ∧
      (op = .and → a = none ∨ b = none → u = none) ∧
      (∀ x : Fin n → Bool, read S x u = op.eval [read C x a, read C x b]) ∧
      (∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w) := by
  cases a with
  | none =>
    rcases hop with rfl | rfl
    · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
        fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    · exact ⟨C, b, hc, hb, le_rfl, by omega, fun _ => rfl,
        by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
  | some a =>
    cases b with
    | none =>
      rcases hop with rfl | rfl
      · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
          fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
      · exact ⟨C, some a, hc, ha, le_rfl, by omega, fun _ => rfl,
          by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    | some b =>
      let S := push n C op a b
      have hs : S.size = C.size + 1 := pushSize _ _ _ _ _
      refine ⟨S, some (n + C.size), pushLegal hc hop (ha _ rfl) (hb _ rfl), ?_,
        by omega, by omega, by simp, by simp, pushNew _ _ _ _, ?_⟩
      · intro w hw
        injection hw with e
        omega
      · intro x w hw
        cases w with
        | none => rfl
        | some w => exact pushOld _ _ _ _ _ (hw _ rfl)

private lemma cutPrefix {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z) :
    ∀ k ≤ C.size, ∃ (S : Circuit) (loc : ℕ → Option ℕ), IsAO2 n S ∧
      S.size + ((Finset.range k).filter (· ∈ D)).card ≤ k ∧
      (∀ w < n + k, available (n + S.size) (loc w)) ∧
      (∀ w < n + k, w ∈ Z → loc w = none) ∧
      ∀ x w, w < n + k → read S x (loc w) = wire (firstGates C k) (pinned v x) w := by
  intro k
  induction k with
  | zero =>
    intro _
    let loc (w : ℕ) : Option ℕ := if w = v.val then none else some w
    refine ⟨⟨[], 0⟩, loc, ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly],
      by simp [ReadsBack], by simp⟩, by simp [Circuit.size], ?_, ?_, ?_⟩
    · intro w hw a ha
      by_cases e : w = v.val
      · simp [loc, e] at ha
      · have : w = a := by simpa [loc, e] using ha
        simp [Circuit.size]; omega
    · intro w hw hz
      simp [loc, hzin w (by omega) hz]
    · intro x w hw
      have h : w < n := by omega
      have he : (⟨w,h⟩ : Fin n) = v ↔ w = v.val := Fin.ext_iff
      by_cases e : w = v.val <;>
        simp [loc, e, read, wire, Circuit.wires, firstGates, pinned, he, List.getD, h]
  | succ k ih =>
    intro hk
    have hk' : k < C.size := by omega
    obtain ⟨S, loc, hs, cost, av, z, ev⟩ := ih (by omega)
    obtain ⟨op, a, b, hg, hop, ha, hb⟩ := gateSpec hc hk'
    obtain ⟨T, u, ht, uav, grow, cost1, cost0, uz, eu, preserve⟩ :=
      advance hs hop (av a ha) (av b hb)
    have zeroInput (h : ∃ w ∈ (gateAt C k).inputs, w ∈ Z) :
        loc a = none ∨ loc b = none := by
      obtain ⟨w, hw, hz⟩ := h
      rw [hg] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact Or.inl (z _ ha hz)
      · exact Or.inr (z _ hb hz)
    let newLoc (w : ℕ) := if w = n + k then u else loc w
    refine ⟨T, newLoc, ht, ?_, ?_, ?_, ?_⟩
    · rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        have := cost0 (zeroInput (hdg k h))
        omega
      · omega
    · intro w hw q hq
      by_cases e : w = n + k
      · exact uav q (by simpa [newLoc, e] using hq)
      · have := av w (by omega) q (by simpa [newLoc, e] using hq)
        omega
    · intro w hw hz
      by_cases e : w = n + k
      · subst w
        obtain ⟨hand, hin⟩ := hzg k hk' hz
        rw [hg] at hand
        simp [newLoc, uz hand (zeroInput hin)]
      · simp [newLoc, e, z w (by omega) hz]
    · intro x w hw
      by_cases e : w = n + k
      · subst w
        simp only [newLoc, ite_eq_left rfl, eu, prefixNew hk' hg, ev x a ha, ev x b hb]
      · have hw' : w < n + k := by omega
        rw [prefixOld hk' _ hw', show newLoc w = loc w by simp [newLoc, e],
          preserve x _ (av w hw'), ev x w hw']

private lemma cutCircuit {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hd : ∀ j ∈ D, j < C.size) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + D.card ≤ C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  obtain ⟨S, loc, hs, cost, av, _, ev⟩ := cutPrefix hc v Z D hzin hzg hdg _ le_rfl
  have hD : (Finset.range C.size).filter (· ∈ D) = D := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨hd _ h, h⟩⟩
  rw [hD] at cost
  by_cases ho : C.output < n + C.size
  · refine ⟨S, loc C.output, hs, cost, av _ ho, fun x => ?_⟩
    have hp : (firstGates C C.size).gates = C.gates := by simp [firstGates, Circuit.size]
    simpa only [wire, Circuit.wires, hp, circuitFun, Circuit.eval] using ev x _ ho
  · refine ⟨S, none, hs, cost, by simp [available], fun x => ?_⟩
    change false = wire C (pinned v x) C.output
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen]; omega)]

private lemma memReaders {n j k : ℕ} {C : Circuit} :
    k ∈ readers n C j ↔ k < C.size ∧ n + j ∈ (gateAt C k).inputs := by
  simp [readers, Circuit.size]

private lemma cutMany {n d : ℕ} {C : Circuit} (hc : IsAO2 n C) (v : Fin n)
    (h : let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + d < C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  let R := readers 0 C v.val
  change d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
    (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R at h
  have hr (j) (hj : j ∈ R) : j < C.size ∧ v.val ∈ (gateAt C j).inputs := by
    simpa only [R, memReaders, Nat.zero_add] using hj
  rcases h with h | ⟨he, g, hg, hand, hsub⟩
  · obtain ⟨S,u,hs,hcst,hu,hev⟩ := cutCircuit hc v {v.val} R
      (by simp) (by intro j hj hz; simp at hz; have := v.isLt; omega)
      (fun j hj => ⟨v.val, (hr j hj).2, by simp⟩) (fun j hj => (hr j hj).1)
    exact ⟨S,u,hs,by omega,hu,hev⟩
  · obtain ⟨k,hk,hkr⟩ := Finset.not_subset.mp hsub
    have hk' := memReaders.mp hk
    have hz (w : ℕ) : w ∈ ({v.val, n + g} : Finset ℕ) ↔ w = v.val ∨ w = n + g := by simp
    obtain ⟨S,u,hs,hcst,hu,hev⟩ :=
      cutCircuit hc v {v.val, n + g} (insert k R) (by
        intro w hw hm
        rcases (hz w).mp hm with e | e
        · exact e
        · omega) (by
        intro j hj hm
        have hv := v.isLt
        have e : j = g := by rcases (hz _).mp hm with h | h <;> omega
        subst j
        exact ⟨hand, v.val, (hr _ hg).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨n + g, hk'.2, by simp⟩
        · exact ⟨v.val, (hr _ hj).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hk'.1
        · exact (hr _ hj).1)
    rw [Finset.card_insert_of_notMem hkr, ← he] at hcst
    exact ⟨S,u,hs,by omega,hu,hev⟩

private lemma inputWire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : Fin n) :
    wire C x a.val = x a := by
  unfold wire Circuit.wires
  have h (gs : List Gate) (w : List Bool) (hw : a.val < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        a.val false = w.getD a.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih, List.getD_append _ _ _ _ hw]
      simp; omega
  rw [h _ _ (by simp)]
  simp

private lemma orList {n : ℕ} {C : Circuit} (hc : IsAO2 n C) :
    ∀ (tail : List (Fin n)) (a : Fin n),
    ∃ (S : Circuit) (u : ℕ), IsAO2 n S ∧ S.size = C.size + tail.length ∧
      u < n + S.size ∧
      (∀ x : Fin n → Bool, wire S x u = (a :: tail).any x) ∧
      ∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w := by
  intro tail
  induction tail with
  | nil =>
    intro a
    refine ⟨C, a, hc, by simp, by have := a.isLt; omega, ?_, fun _ _ _ => rfl⟩
    intro x
    simpa using inputWire C x a
  | cons b tail ih =>
    intro a
    obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := ih b
    let T := push n S .or a.val u
    have ha : a.val < n + S.size := by have := a.isLt; omega
    have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
    refine ⟨T, n + S.size, pushLegal hs (Or.inr rfl) ha hu, ?_, by omega, ?_, ?_⟩
    · simp only [ht, hlen, List.length_cons]; omega
    · intro x
      rw [show wire T x (n + S.size) = _ from pushNew S .or a.val u x, inputWire, hev]
      simp [GateOp.eval]
    · intro x w hw
      rw [← hpres x w hw]
      cases w with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hw w rfl; omega)

private def withOutput (n : ℕ) (C : Circuit) (u : Option ℕ) : Circuit :=
  ⟨C.gates, u.getD (n + C.size)⟩

private lemma withOutputLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C) (u : Option ℕ) :
    IsAO2 n (withOutput n C u) :=
  hc

private lemma withOutputEval {n : ℕ} (C : Circuit) (u : Option ℕ) (x : Fin n → Bool) :
    circuitFun n (withOutput n C u) x = read C x u := by
  cases u with
  | some u => rfl
  | none =>
    change wire C x (n + C.size) = false
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen])]

private lemma restore {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v a : Fin n) (tail : List (Fin n)) (base : Option ℕ)
    (hb : available (n + C.size) base) :
    ∃ S : Circuit, IsAO2 n S ∧ S.size ≤ C.size + tail.length + 2 ∧
      ∀ x, circuitFun n S x = (read C x base || (x v && (a :: tail).any x)) := by
  obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := orList hc tail a
  let T := push n S .and v.val u
  have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
  have hv : v.val < n + S.size := by have := v.isLt; omega
  have ht' : IsAO2 n T := pushLegal hs (Or.inl rfl) hv hu
  have hbase : available (n + T.size) base := by
    intro w hw
    have := hb _ hw
    omega
  obtain ⟨U,out,hU,_,_,hsz,_,_,he,hp⟩ :=
    advance ht' (op := .or) (Or.inr rfl) hbase
      (show available (n + T.size) (some (n + S.size)) from by
        intro w hw; injection hw with e; omega)
  refine ⟨withOutput n U out, withOutputLegal hU _, ?_, fun x => ?_⟩
  · change U.size ≤ _
    omega
  · rw [withOutputEval, he]
    have old : read T x base = read S x base := by
      cases base with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hb w rfl; omega)
    rw [old, hpres x _ hb]
    change GateOp.or.eval [read C x base, wire T x (n + S.size)] = _
    rw [show wire T x (n + S.size) = _ from pushNew S .and v.val u x, inputWire, hev]
    simp [GateOp.eval]

private def leftEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.1.castAdd r

private def rightEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.2.natAdd l

private lemma endsNe {l r : ℕ} (e f : Fin l × Fin r) : leftEnd e ≠ rightEnd f := by
  intro h
  have he := congrArg Fin.val h
  change e.1.val = l + f.2.val at he
  have := e.1.isLt
  omega

private lemma leftEq {l r : ℕ} {e f : Fin l × Fin r} (h : leftEnd e = leftEnd f) :
    e.1 = f.1 :=
  Fin.ext (congrArg (fun z : Fin (l + r) => z.val) h)

private lemma rightEq {l r : ℕ} {e f : Fin l × Fin r} (h : rightEnd e = rightEnd f) :
    e.2 = f.2 := by
  apply Fin.ext
  have he := congrArg Fin.val h
  change l + e.2.val = l + f.2.val at he
  omega

private def linked {l r : ℕ} (v w : Fin (l + r)) (e : Fin l × Fin r) : Prop :=
  v = leftEnd e ∧ w = rightEnd e ∨ w = leftEnd e ∧ v = rightEnd e

private lemma sameEdge {l r : ℕ} {v w : Fin (l + r)} {e f : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w f) : e = f := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))
  · exact (endsNe e f (ha.symm.trans hd)).elim
  · exact (endsNe f e (hc.symm.trans hb)).elim
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))

private lemma sameNeighbor {l r : ℕ} {v w w' : Fin (l + r)} {e : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w' e) : w = w' := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact hb.trans hd.symm
  · exact (endsNe e e (ha.symm.trans hd)).elim
  · exact (endsNe e e (hc.symm.trans hb)).elim
  · exact ha.trans hc.symm

private noncomputable def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Finset (Fin n) := (G.neighborSet v).toFinite.toFinset

private lemma memNeighbors {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n} :
    w ∈ neighbors G v ↔ G.Adj v w := by
  simp [neighbors]

private lemma neighborsCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (neighbors G v).card = (G.neighborSet v).ncard := by
  exact (Set.ncard_eq_toFinset_card _ _).symm

private lemma chooseEdge {l r : ℕ} {E M : Finset (Fin l × Fin r)}
    {G : SimpleGraph (Fin (l + r))} (v : Fin (l + r))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hd : 2 ≤ (neighbors G v).card) :
    ∃ w ∈ neighbors G v, ∃ e ∈ E, e ∉ M ∧ linked v w e := by
  obtain ⟨w, hw, z, hz, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (neighbors G v).card)
  obtain ⟨e,he,hel⟩ := (adj _ _).mp (memNeighbors.mp hw)
  obtain ⟨f,hf,hfl⟩ := (adj _ _).mp (memNeighbors.mp hz)
  by_cases hem : e ∈ M
  · refine ⟨z,hz,f,hf,?_,hfl⟩
    intro hfm
    apply hne
    have h : e = f := by
      rcases hel with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hfl with ⟨hc,hd⟩ | ⟨hc,hd⟩
      · exact ml e hem f hfm (leftEq (ha.symm.trans hc))
      · exact (endsNe e f (ha.symm.trans hd)).elim
      · exact (endsNe f e (hc.symm.trans hb)).elim
      · exact mr e hem f hfm (rightEq (hb.symm.trans hd))
    exact sameNeighbor hel (h ▸ hfl)
  · exact ⟨w,hw,e,he,hem,hel⟩

private def onEdge {l r : ℕ} (x : Fin (l + r) → Bool) (e : Fin l × Fin r) : Prop :=
  x (leftEnd e) = true ∧ x (rightEnd e) = true

private def edgeFun {l r : ℕ} (E : Finset (Fin l × Fin r)) (x : Fin (l + r) → Bool) : Bool :=
  decide (∃ (i : Fin l) (j : Fin r), (i,j) ∈ E ∧ x (i.castAdd r) = true ∧ x (j.natAdd l) = true)

private lemma edgeTrue {l r : ℕ} {E : Finset (Fin l × Fin r)} {x : Fin (l + r) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, onEdge x e := by
  rw [edgeFun, decide_eq_true_iff]
  exact ⟨fun ⟨i,j,h,hx,hy⟩ => ⟨(i,j),h,hx,hy⟩,
    fun ⟨e,h,hx,hy⟩ => ⟨e.1,e.2,h,hx,hy⟩⟩

private lemma pinEdge {l r : ℕ} {e : Fin l × Fin r} {v : Fin (l + r)} {x : Fin (l + r) → Bool} :
    onEdge (pinned v x) e ↔ v ≠ leftEnd e ∧ v ≠ rightEnd e ∧ onEdge x e := by
  rw [ne_comm (a := v) (b := leftEnd e), ne_comm (a := v) (b := rightEnd e)]
  by_cases hl : leftEnd e = v <;> by_cases hr : rightEnd e = v <;>
    simp [onEdge, pinned, hl, hr]

private lemma eraseSpec {l r : ℕ} {E : Finset (Fin l × Fin r)} {G : SimpleGraph (Fin (l + r))}
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    {v w₀ : Fin (l + r)} {e₀ : Fin l × Fin r} (hl : linked v w₀ e₀)
    {x : Fin (l + r) → Bool} :
    ((∃ e ∈ E, onEdge (pinned v x) e) ∨
      x v = true ∧ ∃ w ∈ (neighbors G v).erase w₀, x w = true) ↔
      ∃ e ∈ E.erase e₀, onEdge x e := by
  constructor
  · rintro (⟨e,he,hx⟩ | ⟨hv,w,hw,hx⟩)
    · obtain ⟨ha,hb,h⟩ := pinEdge.mp hx
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, h⟩
      rintro rfl
      exact hl.elim (fun h => ha h.1) (fun h => hb h.2)
    · obtain ⟨e,he,h⟩ := (adj _ _).mp (memNeighbors.mp (Finset.mem_of_mem_erase hw))
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, ?_⟩
      · rintro rfl
        exact (Finset.mem_erase.mp hw).1 (sameNeighbor h hl)
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hv,hx⟩
        · exact ⟨hx,hv⟩
  · rintro ⟨e,he,hx⟩
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp he
    by_cases ha : v = leftEnd e
    · have h : linked v (rightEnd e) e := Or.inl ⟨ha,rfl⟩
      refine Or.inr ⟨ha.symm ▸ hx.1, rightEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.2⟩
      · intro eq
        exact hne (sameEdge (eq ▸ h) hl)
      · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
    · by_cases hb : v = rightEnd e
      · have h : linked v (leftEnd e) e := Or.inr ⟨rfl,hb⟩
        refine Or.inr ⟨hb.symm ▸ hx.2, leftEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.1⟩
        · intro eq
          exact hne (sameEdge (eq ▸ h) hl)
        · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
      · exact Or.inl ⟨e,hm,pinEdge.mpr ⟨ha,hb,hx⟩⟩

private lemma solve {l r : ℕ} (E M : Finset (Fin l × Fin r)) (C : Circuit)
    (G : SimpleGraph (Fin (l + r)))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (hc : IsAO2 (l + r) C)
    (hev : ∀ x, circuitFun (l + r) C x = edgeFun E x)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (v : Fin (l + r)) (hd : 2 ≤ (G.neighborSet v).ncard)
    (h : let d := (G.neighborSet v).ncard
      let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers (l + r) C g ⊆ R) :
    ∃ e ∈ E, e ∉ M ∧ ∃ S : Circuit, S.size < C.size ∧
      IsAO2 (l + r) S ∧ ∀ x, circuitFun (l + r) S x = edgeFun (E.erase e) x := by
  let N := neighbors G v
  have hN : N.card = (G.neighborSet v).ncard := neighborsCard _ _
  have hd' : 2 ≤ N.card := by omega
  obtain ⟨w,hw,e,he,hem,hl⟩ := chooseEdge v adj ml mr hd'
  let W := N.erase w
  have hW : W.card = N.card - 1 := Finset.card_erase_of_mem hw
  have hpos : 0 < W.card := by omega
  obtain ⟨a,tail,hlist⟩ : ∃ a tail, W.toList = a :: tail := by
    cases eq : W.toList with
    | nil =>
      have hz : W.card = 0 := by rw [← Finset.length_toList, eq]; rfl
      omega
    | cons a tail => exact ⟨a,tail,rfl⟩
  have ht : W.card = tail.length + 1 := by
    rw [← Finset.length_toList, hlist]
    rfl
  obtain ⟨S,base,hs,hsz,hav,hspec⟩ := cutMany hc v h
  obtain ⟨T,ht',htsz,htspec⟩ := restore hs v a tail base hav
  refine ⟨e,he,hem,T,by omega,ht',fun x => ?_⟩
  have hAny : (a :: tail).any x = true ↔ ∃ z ∈ W, x z = true := by
    rw [← hlist, List.any_eq_true]
    simp only [Finset.mem_toList]
  apply Bool.eq_iff_iff.mpr
  rw [htspec, hspec, hev, Bool.or_eq_true, Bool.and_eq_true, edgeTrue, hAny, edgeTrue]
  exact eraseSpec adj hl


private def graph {a b : Nat} (E : Finset (Fin a × Fin b)) : SimpleGraph (Fin (a+b)) :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ E, u = leftEnd e ∧ v = rightEnd e

private def computes {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Prop :=
  IsAO2 (a+b) C ∧ circuitFun (a+b) C = PEqualNP.ReadTwo.fpl a (fun i j => (i,j) ∈ E)

private def leaf {a b : Nat} (E : Finset (Fin a × Fin b)) (e : Fin a × Fin b) : Prop :=
  (∀ f ∈ E, f.1 = e.1 → f = e) ∨ ∀ f ∈ E, f.2 = e.2 → f = e

private def goodEdges {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Set (Fin a × Fin b) :=
  {e | e ∈ E ∧ (leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ computes (E.erase e) D)}

private def regular {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Prop :=
  ∀ v : Fin (a+b), let d := ((graph E).neighborSet v).ncard
    let R := readers 0 C v.val
    2 ≤ d → R.card ≤ d ∧ (d = R.card → ∀ g ∈ R, (gateAt C g).op = .and → readers (a+b) C g ⊆ R)

private theorem adj_graph {a b : Nat} (E : Finset (Fin a × Fin b)) (u v : Fin (a+b)) :
    (graph E).Adj u v ↔ ∃ e ∈ E, linked u v e := by
  constructor
  · rintro ⟨_, ⟨e,he,hu,hv⟩ | ⟨e,he,hv,hu⟩⟩
    · exact ⟨e,he,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,he,Or.inr ⟨hv,hu⟩⟩
  · rintro ⟨e,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endsNe e e,Or.inl ⟨e,he,rfl,rfl⟩⟩
    · exact ⟨(endsNe e e).symm,Or.inr ⟨e,he,rfl,rfl⟩⟩

theorem matchingForcesReaders {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (rep : computes E C) (p : Set.InjOn Prod.fst (goodEdges E C))
    (q : Set.InjOn Prod.snd (goodEdges E C)) : regular E C := by
  classical
  let M := Finset.univ.filter (fun f => f ∈ goodEdges E C)
  have mem (f : Fin a × Fin b) : f ∈ M ↔ f ∈ goodEdges E C := by simp [M]
  have ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f :=
    fun e he f hf h => p ((mem e).mp he) ((mem f).mp hf) h
  have mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f :=
    fun e he f hf h => q ((mem e).mp he) ((mem f).mp hf) h
  unfold regular
  intro v
  dsimp only
  intro hd
  let R := readers 0 C v.val
  let d := ((graph E).neighborSet v).ncard
  have impossible (bad : d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
      (gateAt C g).op = .and ∧ ¬readers (a+b) C g ⊆ R) : False := by
    obtain ⟨e,he,out,S,small,legal,ev⟩ := solve E M C (graph E) (adj_graph E) rep.1
      (fun x => congrFun rep.2 x) ml mr v hd bad
    exact out ((mem e).mpr ⟨he,Or.inr ⟨S,small,legal,funext ev⟩⟩)
  constructor
  · exact le_of_not_gt (fun h => impossible (Or.inl h))
  · intro eq g hg hOp
    by_contra no
    exact impossible (Or.inr ⟨eq,g,hg,hOp,no⟩)

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
private theorem pinOne : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := {congrConsts := false})
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := {congrConsts := false}) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := {congrConsts := false}) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := {congrConsts := false}) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp (config := {congrConsts := false}) [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp (config := {congrConsts := false}) [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp (config := {congrConsts := false}) [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp (config := {congrConsts := false}) only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp (config := {congrConsts := false}) only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hout : C.output ≠ n + r)
      (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
      (fun h => h.elim fun k hk => absurd hk.2 (hno k hk.1)) _ hout).symm

  have bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
      ∀ k < (bypass n C r i).gates.length,
        (gateAt (bypass n C r i) k).op = GateOp.and ∨
          (gateAt (bypass n C r i) k).op = GateOp.or := by
    intro k hk
    rw [bypass_length] at hk
    rw [gateAt_bypass hk]
    split_ifs with h
    · exact hAO k (by omega)
    · exact hAO (k + 1) (by omega)

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp (config := {congrConsts := false}) only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp (config := {congrConsts := false}) [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp (config := {congrConsts := false}) only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  -- Erase gates one at a time on the zero restriction. Any false output of a
  -- removed gate can be redirected to the pinned input during this process.
  have pinZero (n : ℕ) (p : Fin n) : ∀ k (C : Circuit), C.size = k → IsAO2 n C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
        C.eval (List.ofFn (Function.update y p false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠
          C.eval (List.ofFn (Function.update x p false))) → D.size < C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x p false)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C hk hC hn
      let row := fun (x : Fin n → Bool) => List.ofFn (Function.update x p false)
      have lengths (x : Fin n → Bool) : (row x).length = n := by simp (config := {congrConsts := false}) [row]
      have pinned (x : Fin n → Bool) : val C (row x) p.val = false := by
        rw [val_input (lengths x) p.isLt]
        change (List.ofFn (Function.update x p false)).getD p.val false = false
        rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
        simp (config := {congrConsts := false})
      have opGood : ∀ j < C.gates.length,
          (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
        fun j hj => hC.1 _ (gateAt_mem hj)
      have outNe : C.output ≠ p.val := by
        intro eq
        obtain ⟨x,y,hnxy⟩ := hn
        apply hnxy
        rw [eval_eq_val,eval_eq_val,eq,pinned,pinned]
      by_cases reads : ∃ j < C.gates.length, p.val ∈ (gateAt C j).inputs
      · obtain ⟨j,hj,hr⟩ := reads
        have canErase (u : ℕ) (hu : u < n+j)
            (eq : ∀ x : Fin n → Bool, val C (row x) (n+j) = val C (row x) u) :
            ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
              ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (row x)) → D.size < C.size) ∧
              ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (row x) := by
          let B := bypass n C j u
          have hlt : B.size < C.size := by
            change (bypass n C j u).gates.length < C.gates.length
            rw [bypass_length]
            omega
          have hB : IsAO2 n B := by
            refine ⟨?_,bypass_readsBack hu hC.2.1,?_⟩
            · intro g hg
              obtain ⟨g',hg',ho,_⟩ := bypass_mem g hg
              simpa (config := {congrConsts := false}) only [ho] using hC.1 g' hg'
            · intro g hg
              obtain ⟨g',hg',_,hl⟩ := bypass_mem g hg
              rw [hl]
              exact hC.2.2 g' hg'
          have same (x : Fin n → Bool) : B.eval (row x) = C.eval (row x) :=
            bypass_eval_eq (lengths x) opGood hj (Or.inl hu) (eq x)
          have hnB : ∃ x y : Fin n → Bool, B.eval (row x) ≠ B.eval (row y) := by
            obtain ⟨x,y,hxy⟩ := hn
            exact ⟨x,y,by rw [same,same]; exact hxy⟩
          obtain ⟨D,hD,hDsize,_,heval⟩ := ih B.size (by omega) B rfl hB hnB
          refine ⟨D,hD,by omega,fun _ => by omega,?_⟩
          intro x
          exact (heval x).trans (same x)
        rcases opGood j hj with hop | hop
        · refine canErase p.val (by have := p.isLt; omega) ?_
          intro x
          rw [pinned]
          apply Bool.eq_false_iff.mpr
          intro h
          have h' := ((val_and (lengths x) hj hop).mp h p.val hr).2
          rw [pinned] at h'
          cases h'
        · obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hj))
          have ha : a < n+j := hC.2.1 j hj a (by simp (config := {congrConsts := false}) [hab])
          have hb : b < n+j := hC.2.1 j hj b (by simp (config := {congrConsts := false}) [hab])
          have hmem : p.val = a ∨ p.val = b := by simpa (config := {congrConsts := false}) [hab] using hr
          rcases hmem with h | h
          · refine canErase b hb ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) b <;> rfl
          · refine canErase a ha ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) a <;> rfl
      · have absent : ∀ j < C.gates.length, p.val ∉ (gateAt C j).inputs := by
          intro j hj hr
          exact reads ⟨j,hj,hr⟩
        have stable (x : Fin n → Bool) : ∀ w : ℕ, w ≠ p.val →
            val C (List.ofFn x) w = val C (row x) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hi : w < n
            · rw [val_input (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hi,val_input (lengths x) hi]
              change (List.ofFn x).getD w false =
                (List.ofFn (Function.update x p false)).getD w false
              rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),
                List.getElem_ofFn,List.getElem_ofFn]
              exact (Function.update_of_ne (fun h => hw (congrArg Fin.val h)) _ _).symm
            · by_cases hl : w < n+C.gates.length
              · let j := w-n
                have hj : j < C.gates.length := by dsimp [j]; omega
                have eq : w = n+j := by dsimp [j]; omega
                rw [eq,val_gate (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hj,val_gate (lengths x) hj]
                apply congrArg (gateAt C j).op.eval
                apply List.map_congr_left
                intro i hii
                have earlier := hC.2.1 j hj i hii
                rw [ite_eq_left earlier,ite_eq_left earlier]
                exact ih i (by omega) (fun h => absent j hj (h ▸ hii))
              · rw [val_ge (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) (by omega),val_ge (lengths x) (by omega)]
        have same (x : Fin n → Bool) : C.eval (List.ofFn x) = C.eval (row x) := stable x C.output outNe
        refine ⟨C,hC,le_rfl,?_,same⟩
        rintro ⟨x,hx⟩
        exact (hx (same x)).elim
  intro x1 x2 x3 x4 h1 h2 h3
  exact pinZero x1 x2 x3 x4 h1 h2 h3


private def pairRow {a b : Nat} (e : Fin a × Fin b) (v : Fin (a+b)) : Bool :=
  decide (v = leftEnd e ∨ v = rightEnd e)

private theorem onPair {a b : Nat} (e f : Fin a × Fin b) : onEdge (pairRow e) f ↔ f = e := by
  constructor
  · rintro ⟨hl,hr⟩
    change decide (_ ∨ _) = true at hl hr
    rcases of_decide_eq_true hl with h|h
    · rcases of_decide_eq_true hr with g|g
      · exact False.elim (endsNe e f g.symm)
      · exact Prod.ext (leftEq h) (rightEq g)
    · exact False.elim (endsNe f e h)
  · rintro rfl
    simp [onEdge, pairRow]

private theorem pair_test {a b : Nat} (E : Finset (Fin a × Fin b)) (e : Fin a × Fin b) :
    edgeFun E (pairRow e) = decide (e ∈ E) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeTrue, onPair, decide_eq_true_eq]
  simp

private theorem zero_test {a b : Nat} (E : Finset (Fin a × Fin b)) :
    edgeFun E (fun _ => false) = false := by simp [edgeFun]

private theorem leafEndpoint {a b : Nat} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    (hle : leaf E e) : ∃ v : Fin (a+b), ∀ f ∈ E,
    (v = leftEnd f ∨ v = rightEnd f) ↔ f = e := by
  rcases hle with h|h
  · refine ⟨leftEnd e, fun f hf => ⟨?_,?_⟩⟩
    · rintro (eq|eq)
      · exact h f hf (leftEq eq.symm)
      · exact False.elim (endsNe e f eq)
    · rintro rfl
      exact Or.inl rfl
  · refine ⟨rightEnd e, fun f hf => ⟨?_,?_⟩⟩
    · rintro (eq|eq)
      · exact False.elim (endsNe f e eq.symm)
      · exact h f hf (rightEq eq.symm)
    · rintro rfl
      exact Or.inr rfl

private theorem leafPinned {a b : Nat} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    {v : Fin (a+b)} (endp : ∀ f ∈ E, (v = leftEnd f ∨ v = rightEnd f) ↔ f = e)
    (x : Fin (a+b) → Bool) :
    edgeFun E (Function.update x v false) = edgeFun (E.erase e) x := by
  have eq : Function.update x v false = pinned v x := by
    funext k
    by_cases h : k = v
    · subst k
      simp [pinned]
    · simp [pinned, Function.update_of_ne h, h]
  rw [eq]
  apply Bool.eq_iff_iff.mpr
  rw [edgeTrue, edgeTrue]
  constructor
  · rintro ⟨f,hf,hx⟩
    obtain ⟨hl,hr,hh⟩ := pinEdge.mp hx
    refine ⟨f, Finset.mem_erase.mpr ⟨?_,hf⟩, hh⟩
    intro fe
    exact ((endp f hf).mpr fe).elim hl hr
  · rintro ⟨f,hf,hx⟩
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hf
    exact ⟨f,hm,pinEdge.mpr ⟨fun hl => hne ((endp f hm).mp (Or.inl hl)),
      fun hr => hne ((endp f hm).mp (Or.inr hr)),hx⟩⟩

theorem strictLeaf {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (rep : computes E C) (e : Fin a × Fin b) (he : e ∈ E) (hle : leaf E e)
    (non : (E.erase e).Nonempty) : ∃ S : Circuit, S.size < C.size ∧ computes (E.erase e) S := by
  obtain ⟨v,hv⟩ := leafEndpoint hle
  obtain ⟨f,hf⟩ := non
  have eq (x : Fin (a+b) → Bool) :
      C.eval (List.ofFn x) = edgeFun E x := congrFun rep.2 x
  have pin (x : Fin (a+b) → Bool) : C.eval (List.ofFn (Function.update x v false)) = edgeFun (E.erase e) x :=
    (eq _).trans (leafPinned hv x)
  have nc : ∃ x y : Fin (a+b) → Bool,
      C.eval (List.ofFn (Function.update x v false)) ≠ C.eval (List.ofFn (Function.update y v false)) := by
    refine ⟨pairRow f, fun _ => false, ?_⟩
    rw [pin, pin, pair_test, zero_test]
    simp [hf]
  have differs : ∃ x : Fin (a+b) → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x v false)) := by
    refine ⟨pairRow e, ?_⟩
    rw [pin, eq, pair_test, pair_test]
    simp [he]
  obtain ⟨S,law,_,cut,ev⟩ := pinOne (a+b) v C.size C rfl rep.1 nc
  exact ⟨S,cut differs,law,funext (fun x => (ev x).trans (pin x))⟩

theorem addEdge {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) (rep : computes E C)
    (e : Fin a × Fin b) : ∃ S : Circuit, S.size ≤ C.size+2 ∧ computes (insert e E) S := by
  let n := a+b
  let base : Option Nat := if C.output < n+C.size then some C.output else none
  have av : available (n+C.size) base := by
    by_cases h : C.output < n+C.size <;> simp [base, h, available, h]
  have src (x : Fin (a+b) → Bool) : read C x base = edgeFun E x := by
    have hh : wire C x C.output = edgeFun E x := congrFun rep.2 x
    by_cases h : C.output < n+C.size
    · simpa [base,h,read] using hh
    · have bad : wire C x C.output = false := by
        unfold wire
        rw [List.getD_eq_default _ _ (by rw [wiresLen]; change a+b+C.size ≤ C.output; omega)]
      simpa [base,h,read,bad] using hh
  obtain ⟨S,legal,limit,ev⟩ := restore rep.1 (leftEnd e) (rightEnd e) [] base av
  refine ⟨S,by simpa using limit,legal,funext (fun x => ?_)⟩
  change circuitFun (a+b) S x = edgeFun (insert e E) x
  rw [ev, src]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, edgeTrue]
  change ((∃ f ∈ E, onEdge x f) ∨ onEdge x e) ↔ ∃ f ∈ insert e E, onEdge x f
  simp [or_comm]


open Sym2
private theorem girth (n m : ℕ) (E : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (rect : ∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) :
    6 ≤ E.card := by
  classical
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have left (a b : Fin n) : ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b) := by
    rintro h
    obtain ⟨e, _, ⟨_, bad⟩ | ⟨_, bad⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad
  have right (a b : Fin m) : ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b) := by
    intro h
    obtain ⟨e, _, ⟨bad,_⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad.symm
  have lr (a : Fin n) (b : Fin m) (h : G.Adj (Fin.castAdd m a) (Fin.natAdd n b)) : (a,b) ∈ E := by
    obtain ⟨⟨c,d⟩, he, ⟨ac,bd⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h
    · have : a = c := Fin.castAdd_inj.mp ac
      have : b = d := by simpa [Fin.ext_iff] using congrArg Fin.val bd
      subst c; subst d; exact he
    · exact (sep _ _ bad.symm).elim
  have square (v w x y : Fin (n+m)) (hv : v ≠ x) (hw : w ≠ y)
      (h1 : G.Adj v w) (h2 : G.Adj w x) (h3 : G.Adj x y) (h4 : G.Adj y v) : False := by
    cases v using Fin.addCases <;> cases w using Fin.addCases <;> cases x using Fin.addCases <;>
      cases y using Fin.addCases <;> first
      | exact (left _ _) h1 | exact (right _ _) h1 | exact (left _ _) h2 | exact (right _ _) h2
      | exact (left _ _) h3 | exact (right _ _) h3
      | exact rect _ _ _ _ (fun h => hv (congrArg _ h)) (fun h => hw (congrArg _ h))
          ⟨lr _ _ h1,lr _ _ h4.symm,lr _ _ h2.symm,lr _ _ h3⟩
      | exact rect _ _ _ _ (fun h => hw (congrArg _ h)) (fun h => hv (congrArg _ h))
          ⟨lr _ _ h1.symm,lr _ _ h2,lr _ _ h4,lr _ _ h3.symm⟩
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  let col : G.Coloring Bool := SimpleGraph.Coloring.mk (fun u => decide (u.val < n)) (by
    intro i j hij
    obtain ⟨⟨a,b⟩, _, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj _ _).1 hij <;> simp)
  have ev := (col.even_length_iff_congr w).2 Iff.rfl
  have three := hw.three_le_length
  have six : 6 ≤ w.length := by
    by_contra! h
    obtain ⟨k,hk⟩ := ev
    have four : w.length = 4 := by omega
    have neq (a b : ℕ) (ha : a < 4) (hb : b < 4) (ne : a ≠ b) : w.getVert a ≠ w.getVert b :=
      fun eq => ne (hw.getVert_injOn' (by change a ≤ w.length-1; omega) (by change b ≤ w.length-1; omega) eq)
    apply square (w.getVert 0) (w.getVert 1) (w.getVert 2) (w.getVert 3)
      (neq _ _ (by decide) (by decide) (by decide)) (neq _ _ (by decide) (by decide) (by decide))
      (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega))
    simpa [←four, SimpleGraph.Walk.getVert_length] using (w.adj_getVert_succ (i:=3) (by omega))
  let edge := fun e : Fin n × Fin m => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have sub : G.edgeSet ⊆ ↑(E.image edge) := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]; exact Finset.mem_image_of_mem edge he
  exact six.trans (hw.isTrail.length_le_ncard_edgeSet.trans
    ((Set.ncard_le_ncard sub).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=E) (f:=edge))))


private def badGraph {a b : Nat} (E : Finset (Fin a × Fin b)) : Prop :=
  6 ≤ E.card ∧ ∃ C : Circuit, C.size + 3 ≤ 2 * E.card ∧ computes E C ∧
    (PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E) ∧ ¬(graph E).IsAcyclic ∧ regular E C ∧
    Set.InjOn Prod.fst (goodEdges E C) ∧ Set.InjOn Prod.snd (goodEdges E C)

private theorem unmatched (n m : ℕ) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (ml : ∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b)
    (mr : ∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) : ∃ e ∈ E, e ∉ M := by
  classical
  by_contra! allM
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have unique (v u w : Fin (n+m)) (hu : G.Adj v u) (hw : G.Adj v w) : u = w := by
    obtain ⟨e, he, ⟨ve,ue⟩ | ⟨ue,ve⟩⟩ := (adj _ _).mp hu <;>
      obtain ⟨f, hf, ⟨vf,wf⟩ | ⟨wf,vf⟩⟩ := (adj _ _).mp hw
    · have ef := ml e (allM e he) f (allM f hf) (Fin.castAdd_inj.mp (ve.symm.trans vf))
      simp [ue,wf,ef]
    · exact (sep _ _ (ve.symm.trans vf)).elim
    · exact (sep _ _ (vf.symm.trans ve)).elim
    · have eq := congrArg Fin.val (ve.symm.trans vf)
      have ef := mr e (allM e he) f (allM f hf) (by simpa [Fin.ext_iff] using eq)
      simp [ue,wf,ef]
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  have h3 := hw.three_le_length
  have eq := unique (w.getVert 1) (w.getVert 0) (w.getVert 2)
    (w.adj_getVert_succ (i:=0) (by omega)).symm (w.adj_getVert_succ (i:=1) (by omega))
  have bad := hw.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ w.length-1; omega)
    (by change 2 ≤ w.length-1; omega) eq
  contradiction


private def mat {a b : Nat} (T : Finset (Fin a × Fin b)) : Prop :=
  Set.InjOn Prod.fst (↑T : Set (Fin a × Fin b)) ∧ Set.InjOn Prod.snd (↑T : Set (Fin a × Fin b))

private def deficit {a b : Nat} (F : Finset (Fin a × Fin b)) : Prop :=
  ∃ (T : Finset (Fin a × Fin b)) (C : Circuit), T ⊆ F ∧ mat T ∧
    computes F C ∧ C.size+2 ≤ F.card+T.card

private theorem deficitCyclic {a b : Nat} (E : Finset (Fin a × Fin b)) (h : deficit E) :
    ¬(graph E).IsAcyclic := by
  obtain ⟨T,C,sub,⟨ml,mr⟩,rep,gap⟩ := h
  obtain ⟨G,adj,card,cover⟩ := PEqualNP.Outside.L_meta_17467.GraphSource a b E T sub
    (fun _ he _ hr h => ml he hr h) (fun _ he _ hr h => mr he hr h)
  have eq : G=graph E := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    exact (adj x y).trans (adj_graph E x y).symm
  subst G
  intro forest
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨rep.1.1 g hg, Nat.le_of_eq (rep.1.2.2 g hg)⟩
  have dom (x : Fin (a+b) → Bool) :
      C.eval (List.ofFn x) = true ↔ ∃ u v, (graph E).Adj u v ∧ x u=true ∧ x v=true := by
    change circuitFun (a+b) C x = true ↔ _
    rw [congrFun rep.2 x]
    change edgeFun E x = true ↔ _
    rw [edgeTrue]
    constructor
    · rintro ⟨e,he,hx,hy⟩
      exact ⟨leftEnd e,rightEnd e,(adj_graph _ _ _).mpr ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩,hx,hy⟩
    · rintro ⟨u,v,edge,hx,hy⟩
      obtain ⟨e,he,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj_graph _ _ _).mp edge
      · exact ⟨e,he,hx,hy⟩
      · exact ⟨e,he,hy,hx⟩
  have lower := PEqualNP.Outside.L_meta_17467.ForestSource (a+b) T.card (graph E) C forest cover mono dom
  omega

theorem minimalDeficit {a b : Nat} (E : Finset (Fin a × Fin b)) (lin : PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E)
    (h : deficit E) (subs : ∀ F ⊂ E, ¬deficit F) : badGraph E := by
  classical
  have cyc := deficitCyclic E h
  have six := girth a b E (graph E) (adj_graph E) cyc (by
    intro i k j l hik hjl hh
    exact lin i k j l hik hjl ⟨hh.1,hh.2.2.1,hh.2.1,hh.2.2.2⟩)
  obtain ⟨T,C,ss,⟨p,q⟩,rep,cost⟩ := h
  obtain ⟨unused,he,nt⟩ := unmatched a b E T (graph E) (adj_graph E) cyc
    (fun _ hm _ hm' z => p hm hm' z) (fun _ hm _ hm' z => q hm hm' z)
  have proper : T ⊂ E := ⟨ss,fun back => nt (back he)⟩
  have nlt := Finset.card_lt_card proper
  have mono : goodEdges E C ⊆ (↑T : Set (Fin a × Fin b)) := by
    intro e hg
    obtain ⟨he,why⟩ := hg
    by_contra ne
    have sub : T ⊆ E.erase e := by
      intro f hf
      exact Finset.mem_erase.mpr ⟨fun h => ne (h ▸ hf),ss hf⟩
    have small : ∃ B : Circuit, B.size < C.size ∧ computes (E.erase e) B := by
      rcases why with leaf|cheap
      · exact strictLeaf E C rep e he leaf (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem he]; omega))
      · exact cheap
    obtain ⟨D,lt,ok⟩ := small
    apply subs (E.erase e) (Finset.erase_ssubset he)
    exact ⟨T,D,sub,⟨p,q⟩,ok,by rw [Finset.card_erase_of_mem he]; omega⟩
  have pp := p.mono mono
  have qq := q.mono mono
  exact ⟨six,C,by omega,rep,lin,cyc,matchingForcesReaders E C rep pp qq,pp,qq⟩

theorem extractDescendant {a b : Nat} (E : Finset (Fin a × Fin b)) :
    (PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E) → deficit E → ∃ F ⊆ E, badGraph F := by
  classical
  apply Finset.strongInductionOn E
  intro E ih lin defic
  by_cases h : ∃ F ⊂ E, deficit F
  · obtain ⟨F,sub,hf⟩ := h
    have lf : PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ F := by
      intro i k j l hik hjl h
      exact lin i k j l hik hjl ⟨sub.1 h.1,sub.1 h.2.1,sub.1 h.2.2.1,sub.1 h.2.2.2⟩
    obtain ⟨Z,hz,ok⟩ := ih F sub lf hf
    exact ⟨Z,hz.trans sub.1,ok⟩
  · exact ⟨E,fun _ h => h,minimalDeficit E lin defic (fun F sub cheap => h ⟨F,sub,cheap⟩)⟩

theorem badImpliesDeficit {a b : Nat} (E : Finset (Fin a × Fin b)) (h : badGraph E) : deficit E := by
  classical
  obtain ⟨six,C,_,rep,_,cyc,_,p,q⟩ := h
  let M := Finset.univ.filter (fun f => f ∈ goodEdges E C)
  have mem (f : Fin a × Fin b) : f ∈ M ↔ f ∈ goodEdges E C := by simp [M]
  obtain ⟨e,he,out⟩ := unmatched a b E M (graph E) (adj_graph E) cyc
    (fun i hi j hj eq => p ((mem i).mp hi) ((mem j).mp hj) eq)
    (fun i hi j hj eq => q ((mem i).mp hi) ((mem j).mp hj) eq)
  obtain ⟨T,D,ss,tt,uu,cost,ok,test⟩ := PEqualNP.Outside.L_meta_17467.StarSource.matchingCircuitExplicit a b (E.erase e)
  have le : C.size ≤ D.size := by
    by_contra! lt
    exact out ((mem e).mpr ⟨he,Or.inr ⟨D,lt,ok,funext test⟩⟩)
  refine ⟨T,C,fun _ hf => Finset.mem_of_mem_erase (ss hf),⟨?_,?_⟩,rep,?_⟩
  · exact fun h₁ h₂ eq => tt _ h₁ _ h₂ eq
  · exact fun h₁ h₂ eq => uu _ h₁ _ h₂ eq
  · rw [Finset.card_erase_of_mem he] at cost
    omega

theorem scalarDescentIff {a b : Nat} (E : Finset (Fin a × Fin b))
    (lin : PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E) :
    (∃ F ⊂ E, badGraph F) ↔ ∃ F ⊂ E, deficit F := by
  constructor
  · rintro ⟨F,sub,h⟩
    exact ⟨F,sub,badImpliesDeficit F h⟩
  · rintro ⟨F,sub,h⟩
    have lf : PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ F := by
      intro i k j l hik hjl hh
      exact lin i k j l hik hjl ⟨sub.1 hh.1,sub.1 hh.2.1,sub.1 hh.2.2.1,sub.1 hh.2.2.2⟩
    obtain ⟨Z,hz,hb⟩ := extractDescendant F lf h
    exact ⟨Z,⟨hz.trans sub.1,fun back => sub.2 (back.trans hz)⟩,hb⟩


-- A surviving matching of optimal cardinality suffices, even when the physical
-- leaf restriction saves exactly one gate.
theorem matchingStableLeaf {a b : Nat} (E : Finset (Fin a × Fin b))
    (h : badGraph E) (e : Fin a × Fin b) (he : e ∈ E) (hle : leaf E e)
    (M : Finset (Fin a × Fin b)) (hm : M ⊆ E.erase e) (matchM : mat M)
    (maxM : ∀ T ⊆ E, mat T → T.card ≤ M.card) : ∃ F ⊂ E, badGraph F := by
  obtain ⟨T,C,sub,matT,rep,cost⟩ := badImpliesDeficit E h
  obtain ⟨six,_,_,_,lin,_,_,_,_⟩ := h
  obtain ⟨D,less,repD⟩ := strictLeaf E C rep e he hle
    (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem he]; omega))
  have max := maxM T sub matT
  apply (scalarDescentIff E lin).mpr
  exact ⟨E.erase e,Finset.erase_ssubset he,M,D,hm,matchM,repD,by
    rw [Finset.card_erase_of_mem he]
    omega⟩

theorem everyMaximumUsesLeaf {a b : Nat} (E : Finset (Fin a × Fin b))
    (h : badGraph E) (none : ¬∃ F ⊂ E, badGraph F)
    (e : Fin a × Fin b) (he : e ∈ E) (hle : leaf E e)
    (M : Finset (Fin a × Fin b)) (sub : M ⊆ E) (matchM : mat M)
    (maxM : ∀ T ⊆ E, mat T → T.card ≤ M.card) : e ∈ M := by
  by_contra ne
  apply none (matchingStableLeaf E h e he hle M _ matchM maxM)
  intro f hf
  exact Finset.mem_erase.mpr ⟨fun hh => ne (hh ▸ hf),sub hf⟩


-- At a minimal posted obstruction with a leaf, *every* scalar witness must
-- have exactly one gate of deficit. Its matching contains the leaf, and the
-- punctured circuit has size at least the original size minus one.
theorem obstructionPrices {a b : Nat} (E : Finset (Fin a × Fin b)) (h : badGraph E)
    (none : ¬∃ F ⊂ E, badGraph F) (e : Fin a × Fin b) (he : e ∈ E) (hle : leaf E e)
    (T : Finset (Fin a × Fin b)) (C : Circuit) (ss : T ⊆ E) (mt : mat T)
    (rep : computes E C) (gap : C.size + 2 ≤ E.card + T.card) :
    e ∈ T ∧ C.size+2 = E.card+T.card ∧
      ∀ D : Circuit, computes (E.erase e) D → C.size ≤ D.size+1 := by
  classical
  obtain ⟨six,_,_,_,lin,_,_,_,_⟩ := h
  have forbid : ¬deficit (E.erase e) := fun hd =>
    none ((scalarDescentIff E lin).mpr ⟨E.erase e,Finset.erase_ssubset he,hd⟩)
  obtain ⟨D,lt,ok⟩ := strictLeaf E C rep e he hle (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem he]; omega))
  have et : e ∈ T := by
    by_contra no
    apply forbid
    refine ⟨T,D,?_,mt,ok,by rw [Finset.card_erase_of_mem he]; omega⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun eq => no (eq ▸ hx),ss hx⟩
  have sub : T.erase e ⊆ E.erase e := by
    intro x hx
    obtain ⟨ne,hm⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨ne,ss hm⟩
  have ms : (↑(T.erase e) : Set (Fin a × Fin b)) ⊆ (↑T : Set (Fin a × Fin b)) := fun _ hx => Finset.mem_of_mem_erase hx
  have mat' : mat (T.erase e) := ⟨mt.1.mono ms,mt.2.mono ms⟩
  have price (B : Circuit) (hb : computes (E.erase e) B) : E.card+T.card ≤ B.size+3 := by
    by_contra! hh
    apply forbid
    exact ⟨T.erase e,B,sub,mat',hb,by rw [Finset.card_erase_of_mem he, Finset.card_erase_of_mem et]; omega⟩
  have lower := price D ok
  exact ⟨et,by omega,fun B hb => by have := price B hb; omega⟩

end PEqualNP.Outside.L_meta_17467
