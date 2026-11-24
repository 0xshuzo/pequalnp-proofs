import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3921
namespace BinaryPart

-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

end FiniteGraph

end BranchGraph

namespace CircuitProof

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ Nat

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

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
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

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp


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


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

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

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
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
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
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


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

lemma Least.hcl {m f gs o} (L : Least m f gs o) : CleanL m gs := L.1
lemma Least.hev {m f gs o} (L : Least m f gs o) (x : Fin m → Bool) : vl gs x o = f x := L.2.1 x
lemma Least.hmin {m f gs o} (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
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
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

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

end LocalSection1

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_3921_binary.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenNine

def cube (i j k : Vertex) (m u : Nat) (b : Bool) (v : Vertex) : Bool :=
  if v = k then b else if v = i then u.testBit 0 else if v = j then u.testBit 1 else m.testBit v.val

def witnessTable : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,57,0,53,53,57,0,0,0,549,0,2085,8229,549,0,1061,0,0,16421,2085,0,165,293,0,0,165,0,53,0,57,0,53,0,0,0,0,53,0,0,53,0,0,57,57,0,1061,0,0,16421,0,0,0,1061,0,0,1061,0,293,165,0,0,0,0,549,0,165,4133,165,1061,0,0,0,0,53,0,57,57,53,0,0,0,0,0,0,0,0,0,0,0,53,0,0,57,0,0,53,57,0,16421,0,101,0,4133,0,1061,0,101,293,0,0,4133,0,0,549,0,0,293,0,16421,0,0,0,8229,4133,293,53,0,53,0,0,0,0,0,57,0,0,101,0,0,4133,2085,0,0,549,0,2085,101,0,293,101,0,0,0,549,0,2085,8229,549,0,1061,0,57,0,0,53,0,0,57,53,0,0,0,0,0,0,0,0,0,0,0,53,0,0,57,0,0,53,57,8229,0,0,101,0,0,0,101,0,549,16421,0,101,0,0,0,101,165,0,549,0,0,0,0,0,16421,8229,0,53,0,53,0,57,0,0,0,0,2085,0,165,0,165,8229,4133,0,0,16421,2085,0,165,293,0,0,165,16421,0,101,0,4133,0,1061,0,101,0,57,0,0,53,0,0,57,53,0,0,0,0,0,0,0,0,0,57,0,53,0,0,0,0,0,53,293,0,101,0,8229,0,0,1061,101,0,1061,0,0,165,0,0,0,165,0,0,1061,0,2085,1061,0,0,0,0,0,53,0,53,57,57,0,0,0,57,0,53,0,57,0,0,0,293,0,0,4133,0,0,549,0,0,8229,0,0,101,0,0,0,101,0,53,0,57,0,0,0,0,0,57,0,0,0,0,0,0,0,0,0,549,0,0,8229,0,0,0,549,0,16421,549,0,165,0,0,0,0,101,293,0,101,2085,0,549,0,0,0,4133,0,0,101,0,0,101,0,0,0,57,0,0,57,0,0,53,53,293,0,16421,0,0,0,8229,4133,293,549,16421,0,101,0,0,0,101,165,293,0,101,0,8229,0,0,1061,101,549,0,0,8229,0,0,0,549,0,0,0,0,0,0,0,0,0,0,0,8229,0,0,0,0,0,165,101,53,0,57,0,0,0,0,0,53,53,0,0,57,0,0,57,53,0,0,1061,0,0,16421,0,0,0,1061,57,0,57,0,0,0,0,0,53,0,549,0,0,0,0,0,16421,8229,0,1061,0,0,165,0,0,0,165,16421,549,0,165,0,0,0,0,101,0,8229,0,0,0,0,0,165,101,0,0,0,0,0,0,0,0,0,0,2085,16421,0,0,165,0,0,293,0,53,0,57,0,57,0,0,0,0,0,1061,0,293,165,0,0,0,0,0,101,0,0,4133,2085,0,0,0,57,0,57,0,53,0,0,0,0,0,1061,0,2085,1061,0,0,0,293,0,101,2085,0,549,0,0,0,57,0,53,0,0,0,0,0,57,0,2085,16421,0,0,165,0,0,293,0,0,0,0,0,0,0,0,0,0,0,4133,0,0,293,293,0,0,0,549,0,165,4133,165,1061,0,0,549,0,2085,101,0,293,101,0,0,0,2085,0,165,0,165,8229,4133,0,0,0,57,0,57,53,53,0,0,4133,0,0,101,0,0,101,0,0,57,0,0,53,0,0,53,57,0,0,57,0,53,0,53,0,0,0,0,0,4133,0,0,293,293,0,0,0,0,0,0,0,0,0,0,0]

def witness (i j k : Vertex) : Nat := witnessTable[i.val * 81 + j.val * 9 + k.val]?.getD 0

def bad (i j k : Vertex) : Prop := witness i j k ≠ 0

def response (i j k : Vertex) (m u : Nat) : Bool × Bool :=
  (petersenF (cube i j k m u false), petersenF (cube i j k m u true))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i j k : Vertex, witness i j k ≠ 0 →
    let w := witness i j k - 1
    let a := response i j k (w / 64) (w % 4)
    let b := response i j k (w / 64) (w / 4 % 4)
    let c := response i j k (w / 64) (w / 16 % 4)
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by decide +kernel

lemma excludes_tie {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (out : Fin (9 + gs.length)) (hout : out.val = o)
    (live : ∀ w : Fin (9 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i j k : Vertex)
    (tie : firstInputBoundary L.hcl out live i = firstInputBoundary L.hcl out live j)
    (later : firstInputBoundary L.hcl out live i < firstInputBoundary L.hcl out live k) :
    ¬ bad i j k := by
  intro tested
  let label := firstInputBoundary L.hcl out live
  let cut := label i
  have stop : FirstBranchRoute.Terminal (readEdge gs) out cut :=
    FirstBranchRoute.first_stops _ _ _ _ _
  let w := witness i j k - 1
  let m := w / 64
  let bit (u : Nat) := vl gs (cube i j k m u false) cut.val
  have eqbit (u : Nat) (b : Bool) : vl gs (cube i j k m u b) cut.val = bit u := by
    apply agree_on_input_ancestors L.hcl
    intro s path
    have prior : label s ≤ cut :=
      FirstBranchRoute.ancestor_first_le _ _ (read_order L.hcl) live path stop
    have ne : s ≠ k := fun e => (not_lt_of_ge (e ▸ prior)) later
    simp [cube, ne]
  have same (u v : Nat) (h : bit u = bit v) (b : Bool) :
      petersenF (cube i j k m u b) = petersenF (cube i j k m v b) := by
    let group := firstInputGroup L.hcl out live cut
    have memI : i ∈ group := (mem_firstInputGroup _ _ _ _ _).2 rfl
    have memJ : j ∈ group := (mem_firstInputGroup _ _ _ _ _).2 tie.symm
    obtain ⟨f, hf⟩ := PetersenCutIndependent.cut_factors L.hcl cut out
      (fun z => z ∈ group) (cube i j k m v b) (firstInputGroup_controlled L.hcl out live cut)
    have hu := hf (cube i j k m u b) (by
      intro z hz
      have ni : z ≠ i := fun e => hz (e ▸ memI)
      have nj : z ≠ j := fun e => hz (e ▸ memJ)
      simp [cube, ni, nj])
    have hv := hf (cube i j k m v b) (fun _ _ => rfl)
    rw [hout, L.hev] at hu hv
    rw [← hu, ← hv, eqbit, eqbit, h]
  have resp (u v : Nat) (h : bit u = bit v) : response i j k m u = response i j k m v :=
    Prod.ext (same u v h false) (same u v h true)
  obtain ⟨ab, bc, ac⟩ := witness_valid i j k tested
  let a := w % 4
  let b := w / 4 % 4
  let c := w / 16 % 4
  have one : bit a ≠ bit b := fun h => ab (resp a b h)
  have two : bit b ≠ bit c := fun h => bc (resp b c h)
  have three : bit a ≠ bit c := fun h => ac (resp a c h)
  cases ha : bit a <;> cases hb : bit b <;> cases hc : bit c <;> simp_all

def cuts : List (Finset Vertex) :=
  [{1,4,7,8}, {2,4,5,6}, {0,3,6,7}]

def maskSet (m : BitVec 9) : Finset Vertex := Finset.univ.filter fun i => m.getLsbD i.val

lemma represented (s : Finset Vertex) : ∃ m, maskSet m = s := by
  let bits := List.ofFn (fun i : Vertex => decide (i ∈ s))
  let m : BitVec 9 := (BitVec.ofBoolListLE bits).cast (by simp [bits])
  refine ⟨m,?_⟩
  ext i
  simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and,m,BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE,bits]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt] <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cover_shapes (s : Finset Vertex) (card : s.card ≤ 5)
    (covers : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s) : sᶜ ∈ cuts ∧ s.card = 5 := by
  obtain ⟨m,rfl⟩ := represented s
  have hh : ∀ m : BitVec 9, (maskSet m).card ≤ 5 →
      edges.all (fun e => decide (e.1 ∈ maskSet m ∨ e.2 ∈ maskSet m)) = true →
      (maskSet m)ᶜ ∈ cuts ∧ (maskSet m).card = 5 := by decide +kernel
  exact hh m card (List.all_eq_true.mpr fun e he => decide_eq_true (covers e he))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pair_check :
    ∀ i j k : Vertex, i ≠ j → petersenGraph.Adj i k → petersenGraph.Adj j k →
      witness i j k ≠ 0 := by
  change ∀ i j k : Vertex, i ≠ j → ((i,k) ∈ edges ∨ (k,i) ∈ edges) →
    ((j,k) ∈ edges ∨ (k,j) ∈ edges) → witness i j k ≠ 0
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cut_check :
    ∀ t ∈ cuts, ∀ i ∉ t, ∀ j ∈ t, ¬petersenGraph.Adj i j →
      ∃ k ∈ t, petersenGraph.Adj i k ∧ witness i j k ≠ 0 := by
  intro t ht
  simp only [cuts,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> unfold petersenGraph graph <;> decide +kernel

lemma terminal_class {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (bound : nonNotCount gs ≤ 13) :
    ∃ t ∈ cuts, ∀ v ∈ t, PetersenScratch.occurrences v (PetersenCutFormula.wireFormula 0 gs o) ≤ 1 := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have valid := least_petersen_output_valid L
  let out : Fin (9 + gs.length) := ⟨o,valid⟩
  have live := least_read_edge_live L petersen_nonconstant petersen_depends petersen_restrict_nonconstant valid
  let label := firstInputBoundary L.hcl out live
  let bs : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x out.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x o = _
    rw [L.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have indep (r) := firstInputGroup_independent L.hcl out live (predecessors_nodup L petersen_nonconstant)
    petersenGraph computes petersen_graph_alternate_neighbors r
  have diff (i j : Vertex) (e : petersenGraph.Adj i j) : label i ≠ label j := by
    intro h
    exact indep (label i) i ((mem_firstInputGroup _ _ _ _ _).2 rfl)
      j ((mem_firstInputGroup _ _ _ _ _).2 h.symm) e
  have marked (S : Finset Vertex) : vl gs (setInput S) out.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) o = true ↔ _
    rw [L.hev]
    exact petersen_graph_marked_edges S
  have leout (v : Vertex) : label v ≤ out := wire_le_output L.hcl out live _
  have branch (v : Vertex) (h : label v ≠ out) : label v ∈ bs := by
    have stop := FirstBranchRoute.first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs v)
    exact in_circuit_branches.mpr (stop.resolve_left h)
  let s := Finset.univ.filter fun i : Vertex => ∃ k, petersenGraph.Adj i k ∧ label i < label k
  have smem (i : Vertex) : i ∈ s ↔ ∃ k, petersenGraph.Adj i k ∧ label i < label k := by simp [s]
  have contained : s.image label ⊆ bs := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, _, lt⟩ := (smem v).mp hv
    exact branch v (ne_of_lt (lt_of_lt_of_le lt (leout k)))
  have inject : Set.InjOn label (s : Set Vertex) := by
    intro i hi j hj same
    by_contra ne
    obtain ⟨k, e, lk⟩ := (smem i).mp hi
    obtain ⟨l, f, ll⟩ := (smem j).mp hj
    have stop := FirstBranchRoute.first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs i)
    have twin := circuit_branch_class_twins L.hcl out live petersenGraph marked (label i) (leout i)
      stop (indep (label i))
    have im := (class_mem label (label i) i).mpr rfl
    have jm := (class_mem label (label i) j).mpr same.symm
    have km : k ∈ BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) i := by
      simp [BranchGraph.neighborsAfter, e, classes_before_mem, lk.le]
    have lm : l ∈ BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) j := by
      rw [← same] at ll
      simp [BranchGraph.neighborsAfter, f, classes_before_mem, ll.le]
    have sameNeighbors := twin i im j jm ⟨k, km⟩ ⟨l, lm⟩
    change BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) i =
      BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) j at sameNeighbors
    rw [sameNeighbors] at km
    have jk := (Finset.mem_filter.mp km).2.1
    exact excludes_tie L out rfl live i j k same lk (pair_check i j k ne e jk)
  have cardImage := Finset.card_image_of_injOn inject
  have bb := branching_budget L.hcl valid (fun w hw hne => by
    let wire : Fin (9 + gs.length) := ⟨w, hw⟩
    obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
    exact ⟨p, g, hg, hw'⟩)
    (bs.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bb
  have total := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at total
  have small : bs.card ≤ 5 := by omega
  have smallS : s.card ≤ 5 := by
    rw [← cardImage]
    exact (Finset.card_le_card contained).trans small
  have covers : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s := by
    intro e he
    have adj : petersenGraph.Adj e.1 e.2 := Or.inl he
    rcases lt_or_gt_of_ne (diff _ _ adj) with h | h
    · exact Or.inl ((smem _).mpr ⟨_, adj, h⟩)
    · exact Or.inr ((smem _).mpr ⟨_, adj.symm, h⟩)
  obtain ⟨shape, sc⟩ := cover_shapes s smallS covers
  have allBranches : s.image label = bs := Finset.eq_of_subset_of_card_le contained (by omega)
  refine ⟨sᶜ, shape, ?_⟩
  intro j hj
  have last : label j = out := by
    by_contra h
    have bj := branch j h
    rw [← allBranches] at bj
    obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp bj
    have na : ¬petersenGraph.Adj i j := fun a => diff i j a eq
    obtain ⟨k, hk, e, tested⟩ := cut_check _ shape i (by simpa using hi) j hj na
    have lt : label i < label k := by
      rcases lt_or_gt_of_ne (diff i k e) with l | l
      · exact l
      · exact False.elim ((Finset.mem_compl.mp hk) ((smem k).mpr ⟨i, e.symm, l⟩))
    exact excludes_tie L out rfl live i j k eq lt tested
  have occ := firstInputBoundary_occurrences_le_one L.hcl out live (predecessors_nodup L petersen_nonconstant) 0 j
  change PetersenScratch.occurrences j (PetersenCutFormula.wireFormula 0 gs (label j).val) ≤ 1 at occ
  rwa [last] at occ

namespace CoverCheck

abbrev M := BitVec 7

def raw : List M := [66, 68, 8, 16, 32]
def profiles : List M := [102, 74, 84, 56]
def cells : List (M × M) :=
  [(102,1),(102,8),(102,16),(74,1),(74,4),(74,16),(74,32),(84,1),(84,2),(84,8),(84,32),(56,1),(56,2),(56,4),(56,64)]

def hit (cell : M × M) (z : M) : Bool :=
  (cell.1 &&& z) == 0 && (cell.2 &&& z) != 0

def key (z : M) : M := if z.toNat ≤ (~~~z).toNat then z else ~~~z

lemma key_flip (z : M) : key (~~~z) = key z := by
  exact (show ∀ a : M, key (~~~a) = key a by decide +kernel) z

def seeds : List M := raw.map key
def lits (xs : List M) := xs ++ xs.map (fun z => ~~~z)
def products (xs : List M) := (lits xs).flatMap fun a =>
  (lits xs).map fun b => key (a &&& b)

def Builds : List M → List M → Prop
  | _, [] => True
  | xs, a :: tail => a ∈ products xs ∧ Builds (a :: xs) tail

def unseen (xs wanted : List M) := (wanted.filter (fun a => !(xs.contains a))).dedup

def candidates (xs need : List M) (fuel : Nat) : List M :=
  if need.length < fuel then (products xs).eraseDups
  else need.filter fun a => (products xs).contains a

lemma candidate_mem {xs need : List M} {fuel : Nat} {a : M}
    (prod : a ∈ products xs) (room : need.length < fuel ∨ a ∈ need) :
    a ∈ candidates xs need fuel := by
  unfold candidates
  split
  · simpa using prod
  · rename_i tight
    exact List.mem_filter.mpr ⟨room.resolve_left tight, List.contains_iff_mem.mpr prod⟩

def weCan (wanted : List M) : Nat → List M → Bool
  | fuel, xs =>
    let need := unseen xs wanted
    if need.isEmpty then true else if need.length > fuel then false else
      match fuel with
      | 0 => false
      | k + 1 =>
        (candidates xs need fuel).any fun a =>
          !(xs.contains a) && (need.length < fuel || need.contains a) && weCan wanted k (a :: xs)

lemma mem_unseen {a : M} {xs wanted : List M} :
    a ∈ unseen xs wanted ↔ a ∈ wanted ∧ a ∉ xs := by simp [unseen]

lemma distinct_unseen (xs wanted : List M) : (unseen xs wanted).Nodup := by
  exact List.nodup_dedup _

lemma count_unseen {xs wanted tail : List M} (hall : ∀ a ∈ wanted, a ∈ xs ∨ a ∈ tail) :
    (unseen xs wanted).length ≤ tail.length := by
  have subset : (unseen xs wanted).toFinset ⊆ tail.toFinset := by
    intro a ha
    obtain ⟨hw, hnot⟩ := mem_unseen.mp (List.mem_toFinset.mp ha)
    exact List.mem_toFinset.mpr ((hall _ hw).resolve_left hnot)
  exact (List.toFinset_card_of_nodup (distinct_unseen xs wanted)) ▸
    ((Finset.card_le_card subset).trans (List.toFinset_card_le _))

lemma builds_mono {xs ys tail : List M} (inc : ∀ a ∈ xs, a ∈ ys) (b : Builds xs tail) : Builds ys tail := by
  induction tail generalizing xs ys with
  | nil => trivial
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := b
    have li : ∀ b ∈ lits xs, b ∈ lits ys := by
      intro b bh
      simp only [lits, List.mem_append, List.mem_map] at *
      rcases bh with h | ⟨c,h,rfl⟩
      · exact Or.inl (inc _ h)
      · exact Or.inr ⟨_,inc _ h,rfl⟩
    refine ⟨?_, ih (fun z h => ?_) ht⟩
    · unfold products at *
      simp only [List.mem_flatMap, List.mem_map] at ha ⊢
      obtain ⟨x,hx,y,hy,e⟩ := ha
      exact ⟨x,li _ hx,y,li _ hy,e⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (inc _ h)

lemma weCan_ok_aux {wanted xs tail : List M} (fuel : Nat) (h : Builds xs tail)
    (small : tail.length ≤ fuel) (hall : ∀ a ∈ wanted, a ∈ xs ∨ a ∈ tail) :
    weCan wanted fuel xs = true := by
  induction tail generalizing fuel xs with
  | nil =>
    have empty : unseen xs wanted = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro a ha
      have hh := mem_unseen.mp ha
      simpa using (hall _ hh.1).resolve_left hh.2)
    cases fuel <;> simp [weCan, empty]
  | cons a tail ih =>
    obtain ⟨prod, run⟩ := h
    by_cases already : a ∈ xs
    · apply ih fuel (builds_mono (fun z hz => (List.mem_cons.mp hz).elim (fun e => e ▸ already) id) run) (by simpa using Nat.le_trans (Nat.le_succ _) small)
      intro z hz
      rcases hall z hz with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl already
        · exact Or.inr h
    · cases fuel with
      | zero => simp at small
      | succ k =>
        have le := (count_unseen hall).trans small
        rw [weCan]
        split
        · rfl
        · rw [if_neg (by omega)]
          apply List.any_eq_true.mpr
          have room : (unseen xs wanted).length < k+1 ∨ a ∈ unseen xs wanted := by
            by_contra! no
            have notWanted : a ∉ wanted := fun h => no.2 (mem_unseen.mpr ⟨h, already⟩)
            have shorter := count_unseen (xs := xs) (wanted := wanted) (tail := tail) (by
              intro z hz
              rcases hall z hz with h | h
              · exact Or.inl h
              · exact Or.inr ((List.mem_cons.mp h).resolve_left (fun e => notWanted (e ▸ hz))))
            simp only [List.length_cons] at small
            omega
          refine ⟨a, candidate_mem prod room, ?_⟩
          have rest := ih k run (by simpa using small) (by
            intro z hz
            rcases hall z hz with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl List.mem_cons_self
              · exact Or.inr h)
          simpa [already, rest] using room

def options (c : M × M) : List M :=
  match c.1.toNat, c.2.toNat with
  | 102, 1 => [1,9,17,25]
  | 102, 8 => [8,9,24,25]
  | 102, 16 => [16,17,24,25]
  | 74, 1 => [1,5,17,21,33,37,49,53]
  | 74, 4 => [4,5,20,21,36,37,52,53]
  | 74, 16 => [16,17,20,21,48,49,52,53]
  | 74, 32 => [32,33,36,37,48,49,52,53]
  | 84, 1 => [1,3,9,11,33,35,41,43]
  | 84, 2 => [2,3,10,11,34,35,42,43]
  | 84, 8 => [8,9,10,11,40,41,42,43]
  | 84, 32 => [32,33,34,35,40,41,42,43]
  | 56, 1 => [1,3,5,7,65,67,69,71]
  | 56, 2 => [2,3,6,7,66,67,70,71]
  | 56, 4 => [4,5,6,7,68,69,70,71]
  | 56, 64 => [64,65,66,67,68,69,70,71]
  | _, _ => []

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma every_option : ∀ c ∈ cells, ∀ z : M, hit c z = true → z ∈ options c := by
  have checked : cells.all (fun c => decide (∀ z : M, hit c z = true → z ∈ options c)) = true := by
    decide +kernel
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp checked c hc)

lemma member_head {xs : List α} {c : α} (h : xs.head? = some c) : c ∈ xs := by
  obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp h
  exact List.mem_cons_self

def remaining (chosen : List M) := cells.filter fun c => !(chosen.any (hit c))

def solve : Nat → List M → Bool
  | fuel, chosen =>
    let wanted := chosen.map key
    if 9 < chosen.length + (unseen seeds wanted).length then false else
      match (remaining chosen).head? with
      | none => weCan wanted (9-chosen.length) seeds
      | some c => match fuel with
        | 0 => false
        | k+1 => (options c).any fun z => solve k (z :: chosen)

lemma solve_ok (tail blocks : List M) (run : Builds seeds tail)
    (bound : tail.length + blocks.length ≤ 9)
    (attain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (cover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true)
    (fuel : Nat) (chosen : List M) (nd : chosen.Nodup)
    (sub : ∀ z ∈ chosen, z ∈ blocks) (enough : blocks.length ≤ fuel + chosen.length) :
    solve fuel chosen = true := by
  have size_of_chosen (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      ys.length ≤ blocks.length := by
    rw [← List.toFinset_card_of_nodup distinct]
    have subset : ys.toFinset ⊆ blocks.toFinset := by
      intro z hz; exact List.mem_toFinset.mpr (included _ (List.mem_toFinset.mp hz))
    exact (Finset.card_le_card subset).trans (List.toFinset_card_le _)
  have keys_of_chosen (ys : List M) (included : ∀ z ∈ ys, z ∈ blocks) :
      ∀ a ∈ ys.map key, a ∈ seeds ∨ a ∈ tail := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact attain _ (included _ hz)
  have cut (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      ¬ 9 < ys.length + (unseen seeds (ys.map key)).length := by
    have := size_of_chosen ys distinct included
    have := count_unseen (keys_of_chosen ys included)
    omega
  have done (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      weCan (ys.map key) (9-ys.length) seeds = true := by
    have := size_of_chosen ys distinct included
    exact weCan_ok_aux _ run (by omega) (keys_of_chosen ys included)
  have uncovered {ys : List M} {c} (hc : (remaining ys).head? = some c) :
      ∃ z ∈ blocks, hit c z = true ∧ z ∉ ys := by
    obtain ⟨hc1,hc2⟩ := List.mem_filter.mp (member_head hc)
    obtain ⟨z,hz,yes⟩ := cover _ hc1
    refine ⟨z,hz,yes,fun zz => ?_⟩
    have on : ys.any (hit c) = true := List.any_eq_true.mpr ⟨z,zz,yes⟩
    simp [on] at hc2
  induction fuel generalizing chosen with
  | zero =>
    rw [solve, if_neg (cut _ nd sub)]
    split
    · exact done _ nd sub
    · rename_i c hc
      obtain ⟨z,hz,yes,nz⟩ := uncovered hc
      have distinct := List.nodup_cons.mpr ⟨nz,nd⟩
      have big := size_of_chosen (z :: chosen) distinct (by
        intro x hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hz
        · exact sub _ hm)
      simp only [List.length_cons] at big
      omega
  | succ k ih =>
    rw [solve, if_neg (cut _ nd sub)]
    split
    · exact done _ nd sub
    · rename_i c hc
      obtain ⟨z,hz,yes,nz⟩ := uncovered hc
      apply List.any_eq_true.mpr
      refine ⟨z, every_option c (List.mem_filter.mp (member_head hc)).1 z yes, ?_⟩
      apply ih (z :: chosen) (List.nodup_cons.mpr ⟨nz,nd⟩)
      · intro x hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hz
        · exact sub _ hm
      · simp only [List.length_cons]
        omega

end CoverCheck

namespace Probes
open CoverCheck

abbrev Term := Fin 4
abbrev Row := Fin 9
abbrev V := Row → Fin 5 → Bool

def pick (t : Term) := t.succ
def active (v : V) : Finset Term := Finset.univ.filter fun t => v 7 (pick t)
def pack {n : Nat} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)
lemma pack_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) : (pack f).getLsbD i.val = f i := by
  simp only [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt] <;> simp
def regular (r : Fin 7) : Row := ⟨r.val, by omega⟩
def mask (v : V) : M := pack (fun i => v (regular i) 0)
def roots : List (Finset Term) := (List.finRange 4).map fun t => {t}
def joins (xs : List (Finset Term)) : List (Finset Term) :=
  xs.flatMap fun a => xs.map fun b => a ∪ b
def Joined : List (Finset Term) → List (Finset Term) → Prop
  | _, [] => True
  | xs, a :: tail => a ∈ joins xs ∧ Joined (a :: xs) tail
def twoOK : Bool :=
  (joins roots).all fun a =>
    (joins (a :: roots)).all fun b => !((b :: a :: roots).contains Finset.univ)
lemma two_checked : twoOK = true := by decide +kernel
lemma three_joins {js : List (Finset Term)} (h : Joined roots js)
    (mem : Finset.univ ∈ js.reverse ++ roots) : 3 ≤ js.length := by
  by_contra! small
  rcases js with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · exact (show Finset.univ ∉ roots by decide) (by simpa using mem)
  · obtain ⟨ha,_⟩ := h
    exact (show ∀ a ∈ joins roots, Finset.univ ∉ a :: roots by decide) a ha (by simpa using mem)
  · obtain ⟨ha,hb,_⟩ := h
    have checked := List.all_eq_true.mp (List.all_eq_true.mp two_checked a ha) b hb
    have yes : (b :: a :: roots).contains Finset.univ = true :=
      List.contains_iff_mem.mpr (by simpa using mem)
    change (!(List.contains (b :: a :: roots) Finset.univ)) = true at checked
    rw [yes] at checked
    contradiction
  · simp only [List.length_cons] at small
    omega

def Signed (ps : List M) (v : V) : Prop := key (mask v) ∈ ps.reverse ++ seeds

def Safe (ps bs : List M) (js : List (Finset Term)) (add : Bool) (v : V) : Prop :=
  (∀ t : Term, t ∉ active v → ∀ r : Row, v r (pick t) = v r 0) ∧
  (active v = ∅ → Signed ps v) ∧
  (active v ≠ ∅ → active v ∈ js.reverse ++ roots) ∧
  (active v ≠ ∅ → add = false → v 8 0 = false) ∧
  (∀ t ∈ active v, ∃ qs : List M, (∀ z ∈ qs, z ∈ bs) ∧ ∀ r : Fin 7,
    v (regular r) (pick t) =
      (v (regular r) 0 || !(qs.any fun z => z.getLsbD r.val)))

lemma safe_mono {ps bs js add v ps' bs' js' add'} (h : Safe ps bs js add v)
    (p : ∀ x ∈ ps, x ∈ ps') (b : ∀ x ∈ bs, x ∈ bs') (j : ∀ x ∈ js, x ∈ js')
    (a : add = true → add' = true) : Safe ps' bs' js' add' v := by
  obtain ⟨same,pure,mixed,noAdd,filters⟩ := h
  refine ⟨same,fun e => ?_,fun e => ?_,fun e h' => ?_,fun t ht => ?_⟩
  · have hp := pure e
    simp only [Signed, List.mem_append, List.mem_reverse] at hp ⊢
    exact hp.imp (p _) id
  · have hj := mixed e
    simp only [List.mem_append, List.mem_reverse] at hj ⊢
    exact hj.imp (j _) id
  · apply noAdd e
    cases he : add
    · rfl
    · have ah := a he
      simp [h'] at ah
  · obtain ⟨qs,hs,hq⟩ := filters t ht
    exact ⟨qs, fun z hz => b _ (hs z hz), hq⟩

def actOr (x y : V) : V := fun r t => x r t || y r t
def actFilter (x y : V) : V := fun r t => x r t && ! y r t

lemma mixed_join {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y ≠ ∅)
    (dis : Disjoint (active x) (active y)) :
    let z := actOr x y
    Safe ps bs (js ++ [active z]) d z := by
  let z := actOr x y
  have cap : active z = active x ∪ active y := by ext t; simp [active,z,actOr]
  have nz : active z ≠ ∅ := by rw [cap]; simp [nx]
  refine ⟨?_,fun e => (nz e).elim,fun _ => by simp,fun _ no => ?_,?_⟩
  · intro t ht r
    change t ∉ active z at ht
    rw [cap, Finset.mem_union, not_or] at ht
    simp [actOr,hx.1 _ ht.1 r,hy.1 _ ht.2 r]
  · simp [actOr, hx.2.2.2.1 nx no, hy.2.2.2.1 ny no]
  · intro t ht
    change t ∈ active z at ht
    rw [cap, Finset.mem_union] at ht
    rcases ht with ht | ht
    · obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
      have absent : t ∉ active y := Finset.disjoint_left.mp dis ht
      refine ⟨qs,ss, fun r => ?_⟩
      simp only [actOr,eq r,hy.1 _ absent _]
      ac_rfl
    · obtain ⟨qs,ss,eq⟩ := hy.2.2.2.2 t ht
      have absent : t ∉ active x := fun h => Finset.disjoint_left.mp dis h ht
      refine ⟨qs,ss, fun r => ?_⟩
      simp only [actOr,eq r,hx.1 _ absent _]
      ac_rfl

lemma add_pure {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    Safe ps bs js true (actOr x y) := by
  have cap : active (actOr x y) = active x := by
    ext t; have := Finset.notMem_empty t; rw [← ny] at this
    simp_all [active,actOr]
  refine ⟨?_,fun e => (nx (cap.symm.trans e)).elim,
    fun _ => cap ▸ hx.2.2.1 nx, fun _ no => by contradiction,?_⟩
  · intro t ht r
    rw [cap] at ht
    simp [actOr,hx.1 _ ht r,hy.1 t (by simp [ny]) r]
  · intro t ht
    rw [cap] at ht
    obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
    refine ⟨qs,ss, fun r => ?_⟩
    simp only [actOr,eq r,hy.1 t (by simp [ny]) _]
    ac_rfl

lemma filter_pure {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    Safe ps (mask y :: bs) js d (actFilter x y) := by
  have cap : active (actFilter x y) = active x := by
    ext t; have := Finset.notMem_empty t; rw [← ny] at this
    simp_all [active,actFilter]
  refine ⟨?_,fun e => (nx (cap.symm.trans e)).elim,
    fun _ => cap ▸ hx.2.2.1 nx, fun _ no => ?_,?_⟩
  · intro t ht r
    rw [cap] at ht
    simp [actFilter,hx.1 _ ht r,hy.1 t (by simp [ny]) r]
  · simp [actFilter,hx.2.2.2.1 nx no]
  · intro t ht
    rw [cap] at ht
    obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
    refine ⟨mask y :: qs, ?_, fun r => ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ss _ hz)
    simp only [actFilter,eq r,hy.1 t (by simp [ny]) _,List.any_cons,mask,pack_bit]
    cases x (regular r) 0 <;> cases y (regular r) 0 <;> cases qs.any (fun z => z.getLsbD r.val) <;> rfl

end Probes

namespace Probes
open CoverCheck

def negVal (a : Bool) (b : Bool) := xor a b
def gateB (o a b : Bool) := if o then a || b else a && b
def bin (o sa sb a b : Bool) := xor (gateB o (xor a sa) (xor b sb)) (gateB o sa sb)
def combine (o sa sb : Bool) (x y : V) : V := fun r t => bin o sa sb (x r t) (y r t)
lemma bin_cases : ∀ o sa sb : Bool,
    (∀ a b, bin o sa sb a b = (a || b)) ∨
    (∀ a b, bin o sa sb a b = (a && b)) ∨
    (∀ a b, bin o sa sb a b = (a && !b)) ∨
    (∀ a b, bin o sa sb a b = (b && !a)) := by decide
lemma bin_sym (o sa sb a b : Bool) : bin o sa sb a b = bin o sb sa b a := by
  cases o <;> cases sa <;> cases sb <;> cases a <;> cases b <;> rfl
lemma bin_two (o sa sb : Bool) (h1 : bin o sa sb true false = true)
    (h2 : bin o sa sb false true = true) : ∀ a b, bin o sa sb a b = (a || b) := by
  exact (show ∀ o sa sb, bin o sa sb true false = true → bin o sa sb false true = true →
    ∀ a b, bin o sa sb a b = (a || b) by decide) _ _ _ h1 h2
lemma bin_one (o sa sb : Bool) (h1 : bin o sa sb true false = true) :
    (∀ a b, bin o sa sb a b = (a || b)) ∨ (∀ a b, bin o sa sb a b = (a && !b)) := by
  exact (show ∀ o sa sb, bin o sa sb true false = true →
    (∀ a b, bin o sa sb a b = (a || b)) ∨ (∀ a b, bin o sa sb a b = (a && !b)) by decide) _ _ _ h1

lemma both_lits {u : M} {xs : List M} (h : key u ∈ xs) :
    u ∈ lits xs ∧ ~~~u ∈ lits xs := by
  have put (v : M) (hv : v ∈ xs) : v ∈ lits xs ∧ ~~~v ∈ lits xs :=
    ⟨List.mem_append_left _ hv, List.mem_append_right _ (List.mem_map.mpr ⟨v,hv,rfl⟩)⟩
  unfold key at h
  split at h
  · exact put _ h
  · obtain ⟨ht,hu⟩ := put _ h
    exact ⟨by simpa using hu,ht⟩

lemma pack_op {f : Bool → Bool → Bool} {op : M → M → M}
    (point : ∀ a b : M, ∀ i : Fin 7, (op a b).getLsbD i.val = f (a.getLsbD i.val) (b.getLsbD i.val))
    (x y : V) : mask (fun r t => f (x r t) (y r t)) = op (mask x) (mask y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 7 := ⟨i,hi⟩
  change (pack _).getLsbD r.val = (op _ _).getLsbD r.val
  simp only [point _ _ r, mask, pack_bit]

lemma bin_product {xs : List M} {x y : V} (o sa sb : Bool)
    (hx : key (mask x) ∈ xs) (hy : key (mask y) ∈ xs) :
    key (mask (combine o sa sb x y)) ∈ products xs := by
  obtain ⟨x1,x0⟩ := both_lits hx
  obtain ⟨y1,y0⟩ := both_lits hy
  have prod (a b : M) (ha : a ∈ lits xs) (hb : b ∈ lits xs) :
      key (a &&& b) ∈ products xs := by
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  rcases bin_cases o sa sb with h | h | h | h
  · have op : mask (combine o sa sb x y) = mask x ||| mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := (· || ·)) (op := (· ||| ·)) (by simp) x y
    rw [op, ← key_flip, BitVec.not_or]
    exact prod _ _ x0 y0
  · have op : mask (combine o sa sb x y) = mask x &&& mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := (· && ·)) (op := (· &&& ·)) (by simp) x y
    rw [op]
    exact prod _ _ x1 y1
  · have op : mask (combine o sa sb x y) = mask x &&& ~~~mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := fun a b => a && !b)
        (op := fun a b => a &&& ~~~b) (by simp) x y
    rw [op]
    exact prod _ _ x1 y0
  · have op : mask (combine o sa sb x y) = mask y &&& ~~~mask x := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := fun a b => b && !a)
        (op := fun a b => b &&& ~~~a) (by simp) x y
    rw [op]
    exact prod _ _ y1 x0

lemma builds_snoc {xs tail : List M} (h : Builds xs tail) (a : M)
    (ha : a ∈ products (tail.reverse ++ xs)) : Builds xs (tail ++ [a]) := by
  induction tail generalizing xs with
  | nil => exact ⟨by simpa using ha, trivial⟩
  | cons b tail ih => exact ⟨h.1, ih h.2 (by simpa using ha)⟩
lemma joined_snoc {xs tail : List (Finset Term)} (h : Joined xs tail) (a : Finset Term)
    (ha : a ∈ joins (tail.reverse ++ xs)) : Joined xs (tail ++ [a]) := by
  induction tail generalizing xs with
  | nil => exact ⟨by simpa using ha, trivial⟩
  | cons b tail ih => exact ⟨h.1, ih h.2 (by simpa using ha)⟩

abbrev Ledger := List M × List M × List (Finset Term) × Bool
def AllSafe (l : Ledger) (v : V) := Safe l.1 l.2.1 l.2.2.1 l.2.2.2 v
def Valid (l : Ledger) (n : Nat) : Prop :=
  Builds seeds l.1 ∧ Joined roots l.2.2.1 ∧
  (∀ z ∈ l.2.1, key z ∈ l.1.reverse ++ seeds) ∧
  l.1.length + l.2.1.length + l.2.2.1.length + l.2.2.2.toNat ≤ n

def StepOK (l : Ledger) (n : Nat) (z : V) : Prop :=
  ∃ l' : Ledger, Valid l' (n+1) ∧ AllSafe l' z ∧ ∀ v, AllSafe l v → AllSafe l' v

lemma pure_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x = ∅) (ny : active y = ∅) (o sa sb : Bool)
    (nz : active (combine o sa sb x y) = ∅) :
    StepOK (ps,bs,js,d) n (combine o sa sb x y) := by
  let z := combine o sa sb x y
  let m := key (mask z)
  have prod := bin_product o sa sb (hx.2.1 nx) (hy.2.1 ny)
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  refine ⟨(ps ++ [m],bs,js,d), ⟨builds_snoc build m prod,joined,?_,?_⟩,?_,?_⟩
  · intro a ha
    simpa [List.mem_append, or_assoc] using (show key a = m ∨ _ from Or.inr (attain a ha))
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Prod.fst, Prod.snd]
    omega
  · refine ⟨fun t _ r => ?_,fun _ => ?_,fun hn => (hn nz).elim,fun hn => (hn nz).elim,
      fun t ht => False.elim (by rw [nz] at ht; simpa using ht)⟩
    · simp [combine, hx.1 t (by simp [nx]) r, hy.1 t (by simp [ny]) r]
    · simp [Signed,m,z]
  · intro v h
    exact safe_mono h (fun _ ht => List.mem_append_left _ ht) (fun _ ht => ht) (fun _ ht => ht) id

lemma join_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y ≠ ∅) (dis : Disjoint (active x) (active y)) :
    StepOK (ps,bs,js,d) n (actOr x y) := by
  have cap : active (actOr x y) = active x ∪ active y := by ext t; simp [active,actOr]
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  refine ⟨(ps,bs,js ++ [active (actOr x y)],d), ⟨build,joined_snoc joined _ ?_,attain,?_⟩,
    mixed_join hx hy nx ny dis,?_⟩
  · rw [cap]
    exact List.mem_flatMap.mpr ⟨_,hx.2.2.1 nx,List.mem_map.mpr ⟨_,hy.2.2.1 ny,rfl⟩⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Prod.fst, Prod.snd]
    omega
  · intro v h
    exact safe_mono h (fun _ ht => ht) (fun _ ht => ht) (fun _ ht => List.mem_append_left _ ht) id

lemma unary_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    StepOK (ps,bs,js,d) n (actOr x y) ∧ StepOK (ps,bs,js,d) n (actFilter x y) := by
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  constructor
  · refine ⟨(ps,bs,js,true), ⟨build,joined,attain,?_⟩,add_pure hx hy nx ny,?_⟩
    · change ps.length + bs.length + js.length + 1 ≤ n + 1
      omega
    · intro v h
      exact safe_mono h (fun _ ht => ht) (fun _ ht => ht) (fun _ ht => ht) (fun _ => rfl)
  · refine ⟨(ps,mask y :: bs,js,d), ⟨build,joined,?_,?_⟩,filter_pure hx hy nx ny,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy.2.1 ny
      · exact attain z hz
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ cost
    · intro v h
      exact safe_mono h (fun _ ht => ht) (fun _ ht => List.mem_cons_of_mem _ ht) (fun _ ht => ht) id

lemma one_step {l n} (valid : Valid l n) {x y : V} (hx : AllSafe l x) (hy : AllSafe l y)
    (o sa sb : Bool) (nx : active x ≠ ∅) (ny : active y = ∅)
    (cap : active (combine o sa sb x y) = active x ∪ active y) :
    StepOK l n (combine o sa sb x y) := by
  obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr nx
  have hyt : t ∉ active y := by simp [ny]
  have hzt : t ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_left _ ht
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at ht hyt hzt
  have good : bin o sa sb true false = true := by simpa [combine,ht,hyt] using hzt
  rcases bin_one o sa sb good with h | h
  · have eq : combine o sa sb x y = actOr x y := by funext r t; exact h _ _
    rw [eq]
    exact (unary_step valid hx hy nx ny).1
  · have eq : combine o sa sb x y = actFilter x y := by funext r t; exact h _ _
    rw [eq]
    exact (unary_step valid hx hy nx ny).2

lemma binary_step {l n} (valid : Valid l n) {x y : V} (hx : AllSafe l x) (hy : AllSafe l y)
    (o sa sb : Bool) (dis : Disjoint (active x) (active y))
    (cap : active (combine o sa sb x y) = active x ∪ active y) :
    StepOK l n (combine o sa sb x y) := by
  by_cases nx : active x = ∅
  · by_cases ny : active y = ∅
    · exact pure_step valid hx hy nx ny o sa sb (by simpa [nx,ny] using cap)
    · have eq : combine o sa sb x y = combine o sb sa y x := by funext r t; exact bin_sym .. 
      rw [eq] at cap ⊢
      exact one_step valid hy hx o sb sa ny nx (cap.trans (Finset.union_comm ..))
  · by_cases ny : active y = ∅
    · exact one_step valid hx hy o sa sb nx ny cap
    obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr nx
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr ny
    have hyt := Finset.disjoint_left.mp dis ht
    have hxu := Finset.disjoint_right.mp dis hu
    have hzt : t ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_left _ ht
    have hzu : u ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_right _ hu
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at ht hu hyt hxu hzt hzu
    have h := bin_two o sa sb (by simpa [combine,ht,hyt] using hzt) (by simpa [combine,hu,hxu] using hzu)
    have eq : combine o sa sb x y = actOr x y := by funext r t; exact h _ _
    rw [eq]
    exact join_step valid hx hy nx ny dis

end Probes

namespace Probes
open CoverCheck PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenNine
open PetersenScratch (occurrences)
open PetersenCutFormula (wireFormula)

def perm (h : Fin 3) : Vertex → Vertex :=
  [![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2], ![1,0,5,8,6,2,4,7,3]].getD h.val id

def term (h : Fin 3) (t : Term) := perm h (![1,4,7,8] t)
def fixture (h : Fin 3) (r : Row) (u : Fin 5) (i : Vertex) : Bool :=
  let bits : Nat := ([0,1,4,8,32,64,5,69,33].getD r.val 0) ||| ([0,2,16,128,256].getD u.val 0)
  (List.finRange 9).any fun v => (perm h v == i) && bits.testBit v.val

def inp (h : Fin 3) (i : Vertex) : V := fun r u => xor (fixture h r u i) (fixture h 7 0 i)
def aim (h : Fin 3) : V := fun r u => xor (petersenF (fixture h r u)) (petersenF (fixture h 7 0))
def layoutOK (h : Fin 3) (s : Finset Vertex) : Prop := ∀ t, term h t ∈ s
lemma layout_exists (s : Finset Vertex) (hs : s ∈ cuts) : ∃ h, layoutOK h s := by
  simp only [cuts,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl <;> unfold layoutOK <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fixture_delta : ∀ h t i, (inp h i 7 (pick t)).toNat = if i = term h t then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma initial_safe (h : Fin 3) (i : Vertex) : AllSafe ([],[],[],false) (inp h i) := by
  let x := inp h i
  have samples : ∀ h i,
      (∀ t, t ∉ active (inp h i) → ∀ r, inp h i r (pick t) = inp h i r 0) ∧
      (active (inp h i) = ∅ → Signed [] (inp h i)) ∧
      (active (inp h i) ≠ ∅ → active (inp h i) ∈ roots ∧ inp h i 8 0 = false) ∧
      (∀ t ∈ active (inp h i), ∀ r : Fin 7, inp h i (regular r) (pick t) = true) := by
    unfold Signed
    decide +kernel
  obtain ⟨a,b,c,d⟩ := samples h i
  exact ⟨a,b,fun e => (c e).1,fun e _ => (c e).2,fun t ht =>
    ⟨[],by simp,fun r => by simp [d _ ht r]⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aim_samples : ∀ h, active (aim h) = Finset.univ ∧ aim h 8 0 = true ∧
    (∀ r : Fin 7, aim h (regular r) 0 = false) ∧
    (∀ t : Term, ∀ r : Fin 7, aim h (regular r) (pick t) = (profiles.getD t.val 0).getLsbD r.val) := by
  decide +kernel

def sense (gs : List Gate) (h : Fin 3) (w : Nat) : V := fun r u =>
  xor (vl gs (fixture h r u) w) (vl gs (fixture h 7 0) w)

lemma sense_input (gs : List Gate) (h : Fin 3) (w : Nat) (hw : w < 9) :
    sense gs h w = inp h ⟨w,hw⟩ := by
  funext r u; simp [sense,inp,vl_input _ _ _ hw]

lemma sense_not {gs : List Gate} (clean : CleanL 9 gs) (h : Fin 3)
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not) (args : g.inputs = [a]) :
    sense gs h (9+p) = sense gs h a := by
  funext r u
  simp only [sense,vl_gate gs clean _ _ g hg, op,args,List.map_cons,List.map_nil,GateOp.eval,List.head?_cons,Option.getD_some]
  cases vl gs (fixture h r u) a <;> cases vl gs (fixture h 7 0) a <;> rfl

lemma sense_bin {gs : List Gate} (clean : CleanL 9 gs) (h : Fin 3)
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and ∨ g.op = .or)
    (args : g.inputs = [a,b]) :
    ∃ o sa sb, sense gs h (9+p) = combine o sa sb (sense gs h a) (sense gs h b) := by
  let sa := vl gs (fixture h 7 0) a
  let sb := vl gs (fixture h 7 0) b
  rcases op with e | e
  · refine ⟨false,sa,sb,?_⟩
    funext r u
    simp only [sense,combine,bin,gateB,sa,sb,vl_gate gs clean _ _ g hg,e,args,List.map_cons,List.map_nil,GateOp.eval]
    cases vl gs (fixture h r u) a <;> cases vl gs (fixture h r u) b <;>
      cases vl gs (fixture h 7 0) a <;> cases vl gs (fixture h 7 0) b <;> rfl
  · refine ⟨true,sa,sb,?_⟩
    funext r u
    simp only [sense,combine,bin,gateB,sa,sb,vl_gate gs clean _ _ g hg,e,args,List.map_cons,List.map_nil,GateOp.eval]
    cases vl gs (fixture h r u) a <;> cases vl gs (fixture h r u) b <;>
      cases vl gs (fixture h 7 0) a <;> cases vl gs (fixture h 7 0) b <;> rfl

lemma local_flip (o sa sb a b : Bool) :
    (bin o sa sb a b).toNat ≤ a.toNat + b.toNat := by
  exact (show ∀ o sa sb a b : Bool, (bin o sa sb a b).toNat ≤ a.toNat + b.toNat by decide) o sa sb a b 

lemma sum_le {l : List Nat} {f g : Nat → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma sum_lt {l : List Nat} {f g : Nat → Nat} {a : Nat} (ha : a ∈ l)
    (h : ∀ b ∈ l, f b ≤ g b) (strict : f a < g a) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have tail (x) (hx : x ∈ l) := h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | later
    · exact Nat.add_lt_add_of_lt_of_le strict (sum_le tail)
    · exact Nat.add_lt_add_of_le_of_lt (h _ List.mem_cons_self) (ih later tail)

lemma exact_occ {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (t : Term) (single : occurrences (term h t) (wireFormula 0 gs o) ≤ 1) :
    ∀ w, w < 9 + gs.length →
      (sense gs h w 7 (pick t)).toNat = occurrences (term h t) (wireFormula 0 gs w) := by
  let f (w : Nat) := (sense gs h w 7 (pick t)).toNat
  let g (w : Nat) := occurrences (term h t) (wireFormula 0 gs w)
  have step {p : Nat} {G : Gate} (hg : gs[p]? = some G) : f (9+p) ≤ (G.inputs.map f).sum := by
    rcases L.hcl p G hg with ⟨op,a,_,args⟩ | ⟨op,a,b,_,_,args⟩
    · simp [f,sense_not L.hcl h hg op args, args]
    · obtain ⟨op',sa,sb,sz⟩ := sense_bin L.hcl h hg op args
      simpa [f,sz,args,combine] using local_flip op' sa sb
        (sense gs h a 7 (pick t)) (sense gs h b 7 (pick t))
  have count {p : Nat} {G : Gate} (hg : gs[p]? = some G) : g (9+p) = (G.inputs.map g).sum :=
    PetersenCutFormula.wireFormula_count_gate 0 L.hcl _ hg
  have upper (w : Nat) (hw : w < 9 + gs.length) : f w ≤ g w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases input : w < 9
      · change (sense gs h w 7 (pick t)).toNat ≤ _
        rw [sense_input _ _ _ input,fixture_delta]
        exact le_of_eq (PetersenCutFormula.wireFormula_count_input 0 gs _ ⟨w,input⟩).symm
      · obtain ⟨p,rfl⟩ : ∃ p, w = 9+p := ⟨w-9,by omega⟩
        have hp : p < gs.length := by omega
        have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
        rw [count hg]
        exact (step hg).trans (sum_le fun a ha => ih a ((L.hcl _ _ hg).lt _ ha) (by have := (L.hcl _ _ hg).lt _ ha; omega))
  have output : sense gs h o = aim h := by funext r u; simp [sense,aim,L.hev]
  have onset : t ∈ active (aim h) := by simp [(aim_samples h).1]
  have doneAt : f o = g o := by
    have on : aim h 7 (pick t) = true := (Finset.mem_filter.mp onset).2
    have yes : f o = 1 := by simp [f,output,on]
    have := upper o (least_petersen_output_valid L)
    change g o ≤ 1 at single
    omega
  have live := least_read_edge_live L petersen_nonconstant petersen_depends petersen_restrict_nonconstant
    (least_petersen_output_valid L)
  intro w hw
  change f w = g w
  induction rank : 9 + gs.length - w using Nat.strong_induction_on generalizing w with
  | ind m ih =>
    apply le_antisymm (upper w hw)
    by_contra! lower
    by_cases out : w = o
    · subst w; omega
    · let wire : Fin (9 + gs.length) := ⟨w,hw⟩
      obtain ⟨v,p,G,hg,eq,inside⟩ := live wire (fun e => out (congrArg Fin.val e))
      have before := (L.hcl p G hg).lt _ inside
      change w < 9+p at before
      have endBound : 9+p < 9+gs.length := by have := v.isLt; omega
      have next := ih (9+gs.length-(9+p)) (by omega) (9+p) endBound rfl
      have strict := sum_lt inside (fun a ha => upper a (by have := (L.hcl _ _ hg).lt _ ha; omega)) lower
      have := step hg
      rw [count hg] at next
      omega

lemma binary_caps {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (single : ∀ t, occurrences (term h t) (wireFormula 0 gs o) ≤ 1)
    {p a b : Nat} {G : Gate} (hg : gs[p]? = some G) (args : G.inputs = [a,b]) :
    Disjoint (active (sense gs h a)) (active (sense gs h b)) ∧
      active (sense gs h (9+p)) = active (sense gs h a) ∪ active (sense gs h b) := by
  have endBound : 9+p < 9+gs.length := by have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have ha : a < 9+p := (L.hcl p G hg).lt a (by simp [args])
  have hb : b < 9+p := (L.hcl p G hg).lt b (by simp [args])
  have cnt (t : Term) :
      (sense gs h (9+p) 7 (pick t)).toNat =
      (sense gs h a 7 (pick t)).toNat + (sense gs h b 7 (pick t)).toNat := by
    have matched := exact_occ L h t (single t)
    rw [matched _ endBound, matched _ (ha.trans endBound), matched _ (hb.trans endBound)]
    simpa [args] using PetersenCutFormula.wireFormula_count_gate 0 L.hcl (term h t) hg
  constructor
  · apply Finset.disjoint_left.mpr
    intro t ht hu
    have eq := cnt t
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and] at ht hu
    rw [ht,hu] at eq
    cases e : sense gs h (9+p) 7 (pick t) <;> simp [e] at eq
  · ext t
    have eq := cnt t
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    cases ea : sense gs h a 7 (pick t) <;> cases eb : sense gs h b 7 (pick t) <;>
      cases ec : sense gs h (9+p) 7 (pick t) <;> simp_all

lemma ledger_for_circuit {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (single : ∀ t, occurrences (term h t) (wireFormula 0 gs o) ≤ 1) :
    ∃ l, Valid l (nonNotCount gs) ∧ AllSafe l (aim h) := by
  have pref (p : Nat) (hp : p ≤ gs.length) : ∃ l, Valid l (nonNotCount (gs.take p)) ∧
      ∀ w < 9+p, AllSafe l (sense gs h w) := by
    induction p with
    | zero =>
      refine ⟨([],[],[],false), ⟨trivial,trivial,by simp,by simp [nonNotCount]⟩,?_⟩
      intro w hw
      rw [sense_input _ _ _ (by omega)]
      exact initial_safe h _
    | succ p ih =>
      have before : p < gs.length := by omega
      have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem before
      obtain ⟨l, valid, safe⟩ := ih (by omega)
      have takeEq : gs.take (p+1) = gs.take p ++ [gs[p]] := List.take_succ_eq_append_getElem before
      have size : nonNotCount (gs.take (p+1)) = nonNotCount (gs.take p) +
          (if isNotGate gs[p].op then 0 else 1) := by
        rw [takeEq]
        unfold nonNotCount
        rw [List.countP_append]
        congr 1
        cases hb : isNotGate gs[p].op <;> simp [hb]
      rcases L.hcl p gs[p] hg with ⟨op,a,ha,args⟩ | ⟨op,a,b,ha,hb,args⟩
      · refine ⟨l,?_,?_⟩
        · rw [size, op]
          simpa [isNotGate] using valid
        · intro w hw
          by_cases old : w < 9+p
          · exact safe w old
          · have eq : w = 9+p := by omega
            rw [eq,sense_not L.hcl h hg op args]
            exact safe a ha
      · obtain ⟨oo,sa,sb,sz⟩ := sense_bin L.hcl h hg op args
        obtain ⟨dis,cap⟩ := binary_caps L h single hg args
        rw [sz] at cap
        obtain ⟨l',valid',safe',keep⟩ := binary_step valid (safe _ ha) (safe _ hb) oo sa sb dis cap
        refine ⟨l',?_,?_⟩
        · rcases op with op | op <;> rw [size, op] <;> simpa [isNotGate] using valid'
        · intro w hw
          by_cases old : w < 9+p
          · exact keep _ (safe w old)
          · have eq : w = 9+p := by omega
            rwa [eq,sz]
  obtain ⟨l,valid,all⟩ := pref gs.length le_rfl
  refine ⟨l,by simpa using valid,?_⟩
  have output : sense gs h o = aim h := by funext r u; simp [sense,aim,L.hev]
  rw [←output]
  exact all _ (least_petersen_output_valid L)

end Probes

namespace Probes
open CoverCheck

set_option maxRecDepth 20000 in
lemma cell_witness : ∀ c ∈ cells, ∃ t : Term, ∃ r : Fin 7,
    c = (profiles.getD t.val 0, (1 : M) <<< r.val) ∧ c.1.getLsbD r.val = false := by
  have checked : cells.all (fun c => decide (∃ t : Term, ∃ r : Fin 7,
    c = (profiles.getD t.val 0, (1 : M) <<< r.val) ∧ c.1.getLsbD r.val = false)) = true := by
    decide +kernel
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp checked c hc)

lemma hit_spec : ∀ a z : M, ∀ r : Fin 7, z.getLsbD r.val = true →
    (∀ i : Fin 7, a.getLsbD i.val = true → z.getLsbD i.val = false) →
    hit (a,(1 : M) <<< r.val) z = true := by
  intro a z r yes good
  have zero : a &&& z = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := good ⟨i,hi⟩
    cases h : a.getLsbD i <;> simp_all
  unfold hit
  simp only [zero,beq_self_eq_true,true_and]
  have law : ∀ v : M, ∀ j : Fin 7, v.getLsbD j.val = true →
      (((1 : M) <<< j.val) &&& v != 0) = true := by decide +kernel
  exact law z r yes

lemma output_cover {ps bs js d} {h : Fin 3} (safe : Safe ps bs js d (aim h)) :
    ∀ c ∈ cells, ∃ z ∈ bs, hit c z = true := by
  intro c hc
  obtain ⟨t,r,eq,neg⟩ := cell_witness c hc
  obtain ⟨all,on,baseline,probe⟩ := aim_samples h
  obtain ⟨qs,inside,values⟩ := safe.2.2.2.2 t (by simp [all])
  have required (j : Fin 7) :
      (profiles.getD t.val 0).getLsbD j.val = !(qs.any fun z => z.getLsbD j.val) := by
    simpa [baseline j, probe t j] using values j
  rw [eq] at neg ⊢
  have has : (qs.any fun z => z.getLsbD r.val) = true := by
    have e := required r
    simp_all
  obtain ⟨z,zIn,yes⟩ := List.any_eq_true.mp has
  refine ⟨z,inside z zIn,hit_spec _ _ _ yes ?_⟩
  intro j one
  have eq := required j
  by_contra! nz
  have nz' : z.getLsbD j.val = true := Bool.ne_false_iff.mp nz
  have hit' := List.any_eq_true.mpr (show ∃ x ∈ qs, x.getLsbD j.val = true from ⟨z,zIn,nz'⟩)
  rw [one, hit'] at eq
  contradiction

set_option maxHeartbeats 2000000 in
lemma no_ledger {l n} {h : Fin 3} (bound : n ≤ 13) (valid : Valid l n)
    (safe : AllSafe l (aim h)) : solve 9 [] ≠ false := by
  obtain ⟨ps,bs,js,d⟩ := l
  obtain ⟨build,joined,outputs,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  change Builds seeds ps at build
  change Joined roots js at joined
  change ∀ z ∈ bs, key z ∈ ps.reverse ++ seeds at outputs
  change Safe ps bs js d (aim h) at safe
  have nonempty : active (aim h) ≠ ∅ := by
    rw [(aim_samples h).1]
    decide
  have mem := safe.2.2.1 nonempty
  rw [(aim_samples h).1] at mem
  have jc : 3 ≤ js.length := three_joins joined mem
  have dtrue : d = true := by
    cases h' : d
    · have no := safe.2.2.2.1 nonempty h'
      simp [(aim_samples h).2.1] at no
    · rfl
  rw [dtrue] at cost
  change ps.length + bs.length + js.length + 1 ≤ n at cost
  have witness : solve 9 [] = true := solve_ok ps bs build (by omega) (by
    intro z hz
    simpa [List.mem_append,or_comm] using outputs z hz) (output_cover safe) 9 []
      (by simp) (by simp) (by simp; omega)
  intro check
  exact Bool.false_ne_true (check.symm.trans witness)

end Probes

open CircuitProof PetersenNine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CoverCheck

lemma split_solve (k : Nat) (xs : List M) (c : M × M) (next : List M)
    (hc : (remaining xs).head? = some c) (eq : options c = next)
    (h : (next.any fun z => solve k (z :: xs)) = false) : solve (k+1) xs = false := by
  rw [solve]
  split
  · rfl
  · rw [hc]
    simpa only [eq] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_8_1 : solve 6 [16,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_8_1 : solve 6 [17,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_8_1 : solve 6 [24,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_8_1 : solve 6 [25,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_8_1 : solve 7 [8,1] = false := by
  apply split_solve 6 [8,1] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_8_1, reject_17_8_1, reject_24_8_1, reject_25_8_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_9_1 : solve 6 [16,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_9_1 : solve 6 [17,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_9_1 : solve 6 [24,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_9_1 : solve 6 [25,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_1 : solve 7 [9,1] = false := by
  apply split_solve 6 [9,1] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_9_1, reject_17_9_1, reject_24_9_1, reject_25_9_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_24_1 : solve 6 [4,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_1 : solve 6 [5,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_24_1 : solve 6 [20,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_1 : solve 6 [21,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_24_1 : solve 6 [36,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_1 : solve 6 [37,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_24_1 : solve 6 [52,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_1 : solve 6 [53,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_1 : solve 7 [24,1] = false := by
  apply split_solve 6 [24,1] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_24_1, reject_5_24_1, reject_20_24_1, reject_21_24_1, reject_36_24_1, reject_37_24_1, reject_52_24_1, reject_53_24_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_25_1 : solve 6 [4,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_1 : solve 6 [5,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_25_1 : solve 6 [20,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_1 : solve 6 [21,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_25_1 : solve 6 [36,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_1 : solve 6 [37,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_25_1 : solve 6 [52,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_1 : solve 6 [53,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_1 : solve 7 [25,1] = false := by
  apply split_solve 6 [25,1] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_25_1, reject_5_25_1, reject_20_25_1, reject_21_25_1, reject_36_25_1, reject_37_25_1, reject_52_25_1, reject_53_25_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1 : solve 8 [1] = false := by
  apply split_solve 7 [1] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_1, reject_9_1, reject_24_1, reject_25_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_16_9 : solve 6 [1,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_16_9 : solve 6 [5,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_16_9 : solve 6 [17,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_16_9 : solve 6 [21,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_16_9 : solve 6 [33,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_16_9 : solve 6 [37,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_16_9 : solve 6 [49,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_16_9 : solve 6 [53,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_9 : solve 7 [16,9] = false := by
  apply split_solve 6 [16,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_16_9, reject_5_16_9, reject_17_16_9, reject_21_16_9, reject_33_16_9, reject_37_16_9, reject_49_16_9, reject_53_16_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_17_9 : solve 6 [4,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_17_9 : solve 6 [5,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_17_9 : solve 6 [20,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_17_9 : solve 6 [21,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_17_9 : solve 6 [36,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_17_9 : solve 6 [37,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_17_9 : solve 6 [52,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_17_9 : solve 6 [53,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_9 : solve 7 [17,9] = false := by
  apply split_solve 6 [17,9] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_17_9, reject_5_17_9, reject_20_17_9, reject_21_17_9, reject_36_17_9, reject_37_17_9, reject_52_17_9, reject_53_17_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_24_9 : solve 6 [1,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_9 : solve 6 [5,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_24_9 : solve 6 [17,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_9 : solve 6 [21,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_24_9 : solve 6 [33,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_9 : solve 6 [37,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_24_9 : solve 6 [49,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_9 : solve 6 [53,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_9 : solve 7 [24,9] = false := by
  apply split_solve 6 [24,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_24_9, reject_5_24_9, reject_17_24_9, reject_21_24_9, reject_33_24_9, reject_37_24_9, reject_49_24_9, reject_53_24_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_25_9 : solve 6 [1,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_9 : solve 6 [5,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_25_9 : solve 6 [17,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_9 : solve 6 [21,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_25_9 : solve 6 [33,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_9 : solve 6 [37,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_25_9 : solve 6 [49,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_9 : solve 6 [53,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_9 : solve 7 [25,9] = false := by
  apply split_solve 6 [25,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_25_9, reject_5_25_9, reject_17_25_9, reject_21_25_9, reject_33_25_9, reject_37_25_9, reject_49_25_9, reject_53_25_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9 : solve 8 [9] = false := by
  apply split_solve 7 [9] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_9, reject_17_9, reject_24_9, reject_25_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_8_17 : solve 6 [4,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_8_17 : solve 6 [5,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_8_17 : solve 6 [20,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_8_17 : solve 6 [21,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_8_17 : solve 6 [36,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_8_17 : solve 6 [37,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_8_17 : solve 6 [52,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_8_17 : solve 6 [53,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_8_17 : solve 7 [8,17] = false := by
  apply split_solve 6 [8,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_8_17, reject_5_8_17, reject_20_8_17, reject_21_8_17, reject_36_8_17, reject_37_8_17, reject_52_8_17, reject_53_8_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_9_17 : solve 6 [4,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_9_17 : solve 6 [5,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_9_17 : solve 6 [20,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_9_17 : solve 6 [21,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_9_17 : solve 6 [36,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_9_17 : solve 6 [37,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_9_17 : solve 6 [52,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_9_17 : solve 6 [53,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_17 : solve 7 [9,17] = false := by
  apply split_solve 6 [9,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_9_17, reject_5_9_17, reject_20_9_17, reject_21_9_17, reject_36_9_17, reject_37_9_17, reject_52_9_17, reject_53_9_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_24_17 : solve 6 [4,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_17 : solve 6 [5,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_24_17 : solve 6 [20,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_17 : solve 6 [21,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_24_17 : solve 6 [36,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_17 : solve 6 [37,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_24_17 : solve 6 [52,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_17 : solve 6 [53,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_17 : solve 7 [24,17] = false := by
  apply split_solve 6 [24,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_24_17, reject_5_24_17, reject_20_24_17, reject_21_24_17, reject_36_24_17, reject_37_24_17, reject_52_24_17, reject_53_24_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_25_17 : solve 6 [4,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_17 : solve 6 [5,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_25_17 : solve 6 [20,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_17 : solve 6 [21,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_25_17 : solve 6 [36,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_17 : solve 6 [37,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_25_17 : solve 6 [52,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_17 : solve 6 [53,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_17 : solve 7 [25,17] = false := by
  apply split_solve 6 [25,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_25_17, reject_5_25_17, reject_20_25_17, reject_21_25_17, reject_36_25_17, reject_37_25_17, reject_52_25_17, reject_53_25_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17 : solve 8 [17] = false := by
  apply split_solve 7 [17] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_17, reject_9_17, reject_24_17, reject_25_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_1_25 : solve 6 [4,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_1_25 : solve 6 [5,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_1_25 : solve 6 [20,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_1_25 : solve 6 [21,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_1_25 : solve 6 [36,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_1_25 : solve 6 [37,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_1_25 : solve 6 [52,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_1_25 : solve 6 [53,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_25 : solve 7 [1,25] = false := by
  apply split_solve 6 [1,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_1_25, reject_5_1_25, reject_20_1_25, reject_21_1_25, reject_36_1_25, reject_37_1_25, reject_52_1_25, reject_53_1_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_5_25 : solve 6 [16,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_5_25 : solve 6 [17,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_5_25 : solve 6 [20,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_5_25 : solve 6 [21,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_5_25 : solve 6 [48,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_5_25 : solve 6 [49,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_5_25 : solve 6 [52,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_5_25 : solve 6 [53,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25 : solve 7 [5,25] = false := by
  apply split_solve 6 [5,25] (74,16) [16,17,20,21,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_5_25, reject_17_5_25, reject_20_5_25, reject_21_5_25, reject_48_5_25, reject_49_5_25, reject_52_5_25, reject_53_5_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_17_25 : solve 6 [4,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_17_25 : solve 6 [5,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_17_25 : solve 6 [20,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_17_25 : solve 6 [21,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_17_25 : solve 6 [36,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_17_25 : solve 6 [37,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_17_25 : solve 6 [52,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_17_25 : solve 6 [53,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_25 : solve 7 [17,25] = false := by
  apply split_solve 6 [17,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_17_25, reject_5_17_25, reject_20_17_25, reject_21_17_25, reject_36_17_25, reject_37_17_25, reject_52_17_25, reject_53_17_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_32_21_25 : solve 6 [32,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_21_25 : solve 6 [33,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_21_25 : solve 6 [36,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_21_25 : solve 6 [37,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_21_25 : solve 6 [48,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_21_25 : solve 6 [49,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_21_25 : solve 6 [52,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_21_25 : solve 6 [53,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25 : solve 7 [21,25] = false := by
  apply split_solve 6 [21,25] (74,32) [32,33,36,37,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_32_21_25, reject_33_21_25, reject_36_21_25, reject_37_21_25, reject_48_21_25, reject_49_21_25, reject_52_21_25, reject_53_21_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_33_25 : solve 6 [4,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_33_25 : solve 6 [5,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_33_25 : solve 6 [20,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_33_25 : solve 6 [21,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_33_25 : solve 6 [36,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_33_25 : solve 6 [37,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_33_25 : solve 6 [52,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_33_25 : solve 6 [53,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_25 : solve 7 [33,25] = false := by
  apply split_solve 6 [33,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_33_25, reject_5_33_25, reject_20_33_25, reject_21_33_25, reject_36_33_25, reject_37_33_25, reject_52_33_25, reject_53_33_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_37_25 : solve 6 [16,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_37_25 : solve 6 [17,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_37_25 : solve 6 [20,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_37_25 : solve 6 [21,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_37_25 : solve 6 [48,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_37_25 : solve 6 [49,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_37_25 : solve 6 [52,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_37_25 : solve 6 [53,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25 : solve 7 [37,25] = false := by
  apply split_solve 6 [37,25] (74,16) [16,17,20,21,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_37_25, reject_17_37_25, reject_20_37_25, reject_21_37_25, reject_48_37_25, reject_49_37_25, reject_52_37_25, reject_53_37_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_49_25 : solve 6 [4,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_49_25 : solve 6 [5,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_49_25 : solve 6 [20,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_49_25 : solve 6 [21,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_49_25 : solve 6 [36,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_49_25 : solve 6 [37,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_49_25 : solve 6 [52,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_49_25 : solve 6 [53,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_25 : solve 7 [49,25] = false := by
  apply split_solve 6 [49,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_49_25, reject_5_49_25, reject_20_49_25, reject_21_49_25, reject_36_49_25, reject_37_49_25, reject_52_49_25, reject_53_49_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_53_25 : solve 6 [1,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_3_53_25 : solve 6 [3,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_53_25 : solve 6 [9,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_11_53_25 : solve 6 [11,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_53_25 : solve 6 [33,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_35_53_25 : solve 6 [35,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_41_53_25 : solve 6 [41,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_43_53_25 : solve 6 [43,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25 : solve 7 [53,25] = false := by
  apply split_solve 6 [53,25] (84,1) [1,3,9,11,33,35,41,43] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_53_25, reject_3_53_25, reject_9_53_25, reject_11_53_25, reject_33_53_25, reject_35_53_25, reject_41_53_25, reject_43_53_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25 : solve 8 [25] = false := by
  apply split_solve 7 [25] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_25, reject_5_25, reject_17_25, reject_21_25, reject_33_25, reject_37_25, reject_49_25, reject_53_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checked : solve 9 [] = false := by
  apply split_solve 8 [] (102,1) [1,9,17,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1, reject_9, reject_17, reject_25]

end CoverCheck


def prependNots (pins : List ℕ) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, [0]⟩ :: ⟨GateOp.not, pins⟩ :: C.gates, C.output⟩

lemma prependNots_eval (pins : List ℕ) (C : Circuit) (x : Fin 9 → Bool) :
    (prependNots pins C).eval (List.ofFn x) =
      let w := List.ofFn x ++ [!x 0]
      C.eval (w ++ [GateOp.not.eval (pins.map fun i => w.getD i false)]) := by
  have hzero : (List.ofFn x).getD 0 false = x 0 := getD_ofFn 9 x false (0 : Fin 9)
  simp only [prependNots, Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons,
    List.map_nil, GateOp.eval, List.headD_cons, hzero]

lemma prependNots_fanInTwo (pins : List ℕ) (C : Circuit) (hlen : pins.length ≤ 2)
    (hfan : FanInTwo C) : FanInTwo (prependNots pins C) := by
  intro g hg
  change g ∈ (⟨GateOp.not, [0]⟩ : Gate) :: ⟨GateOp.not, pins⟩ :: C.gates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  rcases List.mem_cons.mp hg with rfl | hg
  · simpa using hlen
  · exact hfan g hg

lemma petersen_binary_bound (C : Circuit) (hfan : FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = petersenF x)
    (small : nonNotCount C.gates ≤ 13) : False := by
  obtain ⟨gs, o, L, budget⟩ := Readers.least_with_budget C hfan computes petersen_nonconstant
  have bound := budget.trans small
  obtain ⟨s, hs, once⟩ := terminal_class L bound
  obtain ⟨h, hh⟩ := Probes.layout_exists s hs
  obtain ⟨l, valid, safe⟩ := Probes.ledger_for_circuit L h (fun t => once _ (hh t))
  exact Probes.no_ledger bound valid safe CoverCheck.checked

end BinaryPart

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity BinaryPart

theorem fourteen : ∀ (D : Circuit), FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) := by
  intro C hf correct
  by_contra! small
  apply petersen_binary_bound C hf
  · intro x
    rw [correct x]
    simp only [petersenF, PetersenNine.edgeFun, PetersenNine.edges, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc]
  · let charged (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
    have eq : (fun g : Gate => !(CircuitProof.isNotGate g.op)) = charged := by
      funext g
      cases g with
      | mk op ins => cases op <;> rfl
    change C.gates.countP (fun g : Gate => !(CircuitProof.isNotGate g.op)) ≤ 13
    rw [eq]
    change C.gates.countP charged < 14 at small
    omega

namespace DummyCertificate

def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]

inductive Sol (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol m T q (insert (a ^^^ m) S) → Sol m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S →
      Sol m T q (insert (op d a b) S) → Sol m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) (Set.insert_subset_insert hs))

inductive Live (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live m T k t (insert (a ^^^ m) U) →
      Live m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Live m T k t (insert (op d a b) U) →
      Live m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Sol m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left

def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S') :
    Live m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S') :
    Live m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl⟩ := h; exact .bi hab hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d b a S S' := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm]⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]

def Min (m T k t : ℕ) (S : Finset ℕ) : Prop := Live m T k t S ∧ ∀ q < k, ¬ Sol m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'

lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega

def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h

lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol n (T &&& n) q (C n (Im n S'))) : Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩

def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hl : Live m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min m T k t (insert (op d a b) U) := by
  have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live m T k 0 S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect

structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
def NN : Nat := 1118
def AA : Nat := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fff0000000000000000
def HX : Nat := 0x2954955552924a49554a5494800092552500015494a9200029294a94925524a524a52800094a52a94800094a94929254a49252a8000a4955292500014a00024a0002900012800080000000000000000000
def HY : Nat := 0x2000082080001080001042000041041100002000082084108000104210900004100002084108210000210904000084000082082210904110444400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def tail (f : Nat → List W → Bool) (d : Bool) (l e n z : Nat) (r : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f z r) (Bool.rec (motive := fun _ => Bool) (f z r) false (rect d l (Nat.xor l (twice d l r)) r [])) (Nat.beq n e)
def child (f : Nat → List W → Bool) (d : Bool) (l g e n : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (tail f d l e n z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x => (st (y) (fun y => (st (Nat.lor x y) (fun w => ins ⟨s, x, y, w⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : Nat → ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c n (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f d l g e) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def nots (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e n (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f d l m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (fun n => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (ih (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s) v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) (true) (node (ih (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) n z 0 v v)) (true) (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) n z v pairs))) (true) (Nat.ble n 1))) v.length) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63,79), (79,95), (95,97), (97,100), (100,116), (116,119), (119,121), (121,137), (137,139), (139,142), (142,145), (145,161), (161,163), (163,166), (166,168), (168,184), (184,186), (186,189), (189,192), (192,195), (195,197), (197,200), (200,202), (202,204), (204,206), (206,208), (208,211), (211,214), (214,217), (217,219), (219,235), (235,237), (237,239), (239,241), (241,244), (244,246), (246,249), (249,252), (252,255), (255,258), (258,261), (261,263), (263,266), (266,268), (268,270), (270,273), (273,276), (276,279), (279,281), (281,284), (284,287), (287,290), (290,292), (292,295), (295,297), (297,299), (299,302), (302,304), (304,307), (307,323), (323,326), (326,328), (328,331), (331,333), (333,335), (335,337), (337,340), (340,342), (342,345), (345,347), (347,350), (350,352), (352,355), (355,371), (371,373), (373,376), (376,378), (378,381), (381,383), (383,386), (386,389), (389,392), (392,394), (394,397), (397,399), (399,402), (402,405), (405,408), (408,410), (410,412), (412,414), (414,417), (417,420), (420,423), (423,426), (426,428), (428,431), (431,433), (433,435), (435,438), (438,440), (440,443), (443,445), (445,448), (448,451), (451,453), (453,469), (469,472), (472,475), (475,477), (477,479), (479,482), (482,484), (484,487), (487,490), (490,492), (492,494), (494,496), (496,512), (512,514), (514,517), (517,520), (520,522), (522,524), (524,526), (526,529), (529,532), (532,535), (535,551), (551,554), (554,556), (556,559), (559,562), (562,564), (564,566), (566,569), (569,571), (571,574), (574,576), (576,578), (578,580), (580,582), (582,584), (584,587), (587,590), (590,593), (593,595), (595,598), (598,601), (601,604), (604,607), (607,609), (609,612), (612,614), (614,616), (616,618), (618,620), (620,622), (622,624), (624,626), (626,628), (628,631), (631,634), (634,636), (636,638), (638,640), (640,643), (643,645)]
def segsY : List (ℕ × ℕ) := [(645,658), (658,662), (662,666), (666,670), (670,676), (676,680), (680,686), (686,692), (692,695), (695,700), (700,705), (705,709), (709,715), (715,721), (721,727), (727,746), (746,751), (751,770), (770,776), (776,779), (779,784), (784,789), (789,808), (808,813), (813,819), (819,824), (824,830), (830,835), (835,841), (841,860), (860,866), (866,884), (884,887), (887,892), (892,897), (897,902), (902,908), (908,927), (927,932), (932,938), (938,943), (943,949), (949,955), (955,973), (973,992), (992,996), (996,1002), (1002,1008), (1008,1014), (1014,1033), (1033,1038), (1038,1044), (1044,1063), (1063,1068), (1068,1087), (1087,1093), (1093,1099), (1099,1117)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma tail_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : tail f d l e n z r = false) : f z r = false := by
  simp only [tail, bR] at h
  by_cases hne : n = e
  · have hb : Nat.beq n e = true := by simpa using hne
    rw [hb, cond_true] at h
    cases hrect : rect d l (Nat.xor l (twice d l r)) r [] with
    | false => rw [hrect] at h; simpa using h
    | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := Nat.xor l (twice d l r))] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp d l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : d = false := by rw [hd]; simp [pos']
          subst hd'
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : d = true := by rw [hd]; simp [pos', htp]
          subst hd'
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
  · have hb : Nat.beq n e = false := Bool.eq_false_iff.2 fun h => hne (Nat.eq_of_beq_eq_true h)
    rw [hb, cond_false] at h; exact h
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : child f d l g e n mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact tail_sound X hr hm hk hd hn he h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b)⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b)⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi d' a.s c.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f d l m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
lemma mid_false {f : ℕ → List W → Bool} {d : Bool} {l m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f d l m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f d l g e) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ℕ → ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch n (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch (n + 2) mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch n (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) = false
    cases ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f d l m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ S'.card ≤ e ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, by omega, this⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {n z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → n = r.length →
      child f (pos' t) l g e n mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' :=
    fun {n z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk rfl h3 he h4, h2⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 (by omega) ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {d : Bool} {l m g e n z q : ℕ} {v r : List W} (h : nots f d l m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f d l m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) d l g e n (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f d l m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f d l m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Un m a.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f d l m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk rfl (by omega) he h, hst⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk rfl (by omega) he h, hst⟩
end sound
def FM (m T k t : ℕ) (S : Finset ℕ) (KP : ℕ → ℕ → Prop) (KN : ℕ → Prop) : Prop :=
  (∃ k0 d a b S1, k = k0 + 1 ∧ KP a b ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
  (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ KN a ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
  (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ KN a ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
    Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3)
lemma FM_of {m T k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) (hc : 2 ≤ S.card) : FM m T k t S (fun _ _ => True) (fun _ => True) := by
  rcases first_move k t S h hc with ⟨k0, d, a, b, S1, e, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, trivial, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', trivial, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', trivial, h⟩)
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma look_succ (l m g fuel k t z : ℕ) (v : List W) (h : look l m g (fuel + 1) k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos s) l m g (k - 2 - s)
        v.length z v (pairsQ q q')) (pos s) l m g (k - 1 - s) v.length z (q + 1) v v)) true
        (node (look l m g fuel (k - 2) s) (pos s) l m g (k - 1 - s) v.length z v (pairsP q)))) (pos s) l m g (k - s) v.length z 0 v v)) true
      (node (look l m g fuel (k - 1) t) (pos t) l m g (k - t) v.length z v pairs)) true (Nat.ble v.length 1) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (DummyCertificate.X → DummyCertificate.X → Bool) → List DummyCertificate.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' x y S S') (hl : Live m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · exact gate_sound X hs hm hk hd hn he hb hl ha hc h
  · exact gate_sound X hs hm hk hd hn he hb.symm hl hc ha h
lemma step_sound {fuel : ℕ} (ih : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S) {k t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hlen : 2 ≤ v.length)
    {KP : ℕ → ℕ → Prop} {KN : ℕ → Prop}
    (hA : ∀ x y : ℕ, x ≠ y → KP x y → ∃ go : (DummyCertificate.X → DummyCertificate.X → Bool) → List DummyCertificate.X → Bool,
      node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false)
    (hN : ∀ s, t = s + 1 → ∀ a ∈ v, KN a.s → ∃ rr, a ∈ rr ∧ nots (fun q z v =>
      bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v rr = false) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S KP KN := by
  intro k' hk hm hfm
  rcases hfm with
    ⟨k0, d, a, b, S1, rfl, hkp, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hkn, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hkn, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨go, h1, hgo⟩ := hA a b hb.1 hkp
    obtain ⟨z', r, hf, hst⟩ := node_bi X hs hm (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact hgo h hp a c ha hc hax hcy) h1
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN t0 rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl rfl (by omega) hu hl1 hwa (by omega) hrr h2
    have hm1 := hu.min hl1 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN (t0 + 1) rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl rfl (by omega) hu hl2 hwa (by omega) hrr h2
    have hm1 := hu.min hl2 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl rfl (by omega) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs
    obtain ⟨hlen, h1, h2⟩ := look_succ _ _ _ _ _ _ _ _ h
    intro k' hk hm
    refine step_sound X (KP := fun _ _ => True) (KN := fun _ => True) ih hs hlen (fun x y hxy _ => ⟨pairs, h1, fun h hp a c ha hc hax hcy => ?_⟩)
      (fun s hs a ha _ => ⟨v, ha, h2 s hs⟩) k' hk hm (FM_of hm (by rw [hs.rep.card]; exact hlen))
    have hpw := pairs_false hp
    have : Std.Symm (fun a c : DummyCertificate.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
    refine (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_
    intro e
    have : a.s = c.s := congrArg DummyCertificate.X.s e
    exact hxy (by rw [← hax, ← hcy, this])
end sound
def rawP : List ℕ := [0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff2cb20284c2023205, 0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff605989290008a0c3, 0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff00004840d0f006c20810, 0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec00000000000004525d9ab670, 0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc000000000000004c32000238851dce, 0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe00000000000000000000000000940c0523a2600210, 0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000a180bb188920c1a4, 0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000130220c900310c00, 0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000092683e00754c0101]
def rawL : List ℕ := rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7ffffc7abffbffeabfd5
def kz (Z : ℕ) : ℕ := (List.range 9).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawL.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawL) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)))⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c⟩ :: r)) v
def anySub (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (ih h) true (ih fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def filt (H : ℕ) (v : List W) : List W := List.rec (motive := fun _ => List W) [] (fun w _ ih => Bool.rec (motive := fun _ => List W) ih (w :: ih) (hb H w.s)) v
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g fuel H HN k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s)
        v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) true
        (node (look l m g fuel (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) v.length z 0 v (filt HN v))) true
      (node (look l m g fuel (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) v.length z v (pairsC H))) true (Nat.ble v.length 1)
def startv (l m g B K t H HN : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H HN K t z r) (pos t) l g (Nat.sub (Nat.succ K) t) v.length (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (Nat.beq (cov (pos t) l v) l)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {v : List W} : ∀ {h : List W → Bool}, anySub v h = false → ∀ r, r.Sublist v → h r = false := by
  induction v with
  | nil => intro h hh r hr; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro h hh r hr
    change (Bool.rec (motive := fun _ => Bool) (anySub v h) true (anySub v fun r => h (w :: r)) : Bool) = false at hh
    rw [bR] at hh
    cases h1 : anySub v (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      cases hr with
      | cons _ hr => exact ih hh r hr
      | cons_cons _ hr => exact ih h1 _ hr
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma filt_mem {H : ℕ} {v : List W} {w : W} (hw : w ∈ v) (hH : hb H w.s = true) : w ∈ filt H v := by
  induction v with
  | nil => simp at hw
  | cons x v ih =>
    have e : filt H (x :: v) = bif hb H x.s then x :: filt H v else filt H v := by
      change Bool.rec (motive := fun _ => List W) (filt H v) (x :: filt H v) (hb H x.s) = _
      cases hb H x.s <;> rfl
    rw [e]
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · rw [hH]; simp
    · cases hb H x.s <;> simp [ih hw]
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
lemma topC_succ {l m g fuel H HN k t z : ℕ} {v : List W} (h : topC l m g fuel H HN k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v (pairsC H) = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v (filt HN v) = false := by
  simp only [topC, bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (Nat.sub k 1) t) (pos' t) l m g (Nat.sub k t) v.length z v (pairsC H) with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
def KP (M : List (ℕ × ℕ)) (x y : ℕ) : Prop := ∃ p ∈ M, hb p.1 (x + y) = true
def KN (M : List (ℕ × ℕ)) (x : ℕ) : Prop := ∃ p ∈ M, hb p.2 x = true
lemma topC_sound {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T) {fuel k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} (hlen : 2 ≤ v.length)
    (h : ∀ p ∈ M, topC l m g fuel p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S (KP M) (KN M) := by
  refine step_sound X (look_sound X fuel) hs hlen (fun x y hxy ⟨p, hpM, hpx⟩ => ⟨pairsC p.1, (topC_succ (h p hpM)).2.1, ?_⟩)
    (fun s hst a ha ⟨p, hpM, hpa⟩ => ⟨_, filt_mem ha hpa, (topC_succ (h p hpM)).2.2 s hst⟩)
  intro h hp a b ha hb' hax hby
  have hpw := pairsC_false hp
  have : Std.Symm (fun a b : DummyCertificate.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  refine (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb') ?_ ?_
  · intro e
    have : a.s = b.s := congrArg DummyCertificate.X.s e
    exact hxy (by rw [← hax, ← hby, this])
  · change hb p.1 (a.s + b.s) = true; rw [hax, hby]; exact hpx
def tab : List (ℕ × ℕ) := [(16,13), (64,13), (128,13), (1,12), (2,12), (4,12), (8,12), (32,12), (256,12), (17,11), (24,11), (66,11), (80,11), (132,11), (144,11), (160,11), (192,11), (320,11), (3,9), (6,9), (12,9), (18,9), (20,9), (33,9), (48,9), (65,9), (68,9), (72,9), (96,9), (129,9), (130,9), (136,9), (264,9), (272,9), (288,9), (384,9), (5,8), (9,8), (10,8), (34,8), (36,8), (40,8), (257,8), (258,8), (260,8), (19,8), (25,8), (28,8), (49,8), (67,8), (70,8), (81,8), (82,8), (88,8), (134,8), (140,8), (145,8), (148,8), (152,8), (161,8), (164,8), (176,8), (194,8), (196,8), (208,8), (224,8), (280,8), (322,8), (328,8), (336,8), (352,8), (416,8), (448,8), (7,7), (14,7), (21,7), (26,7), (35,7), (56,7), (74,7), (84,7), (98,7), (112,7), (133,7), (146,7), (162,7), (168,7), (193,7), (200,7), (268,7), (273,7), (289,7), (296,7), (321,7), (324,7), (388,7), (400,7), (22,6), (76,6), (97,6), (131,6), (304,6), (392,6), (11,5), (13,5), (37,5), (38,5), (41,5), (42,5), (44,5), (50,5), (52,5), (69,5), (73,5), (100,5), (104,5), (137,5), (138,5), (259,5), (261,5), (262,5), (265,5), (266,5), (274,5), (276,5), (290,5), (292,5), (385,5), (386,5)]
def pr (Z : ℕ) : List (ℕ × ℕ) := tab.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def WZ (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL, x = w &&& mz Z}
def Imp (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z))
def PZ (Z : ℕ) : List ℕ := (pr Z).map (fun e => mz e.1)
def pOk (Z : ℕ) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && (pr Z).all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
noncomputable def chk (Z K t H HN : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B =>
    frc (avl P m rawL) (fun v => anySub v (fun r => st l fun l => st m fun m => st g fun g => st B fun B => startv l m g B K t H HN r)))
    (pL ((pr Z).map fun e => 16 + (K - e.2)))) (pL ((pr Z).map fun _ => 16))) (PZ Z)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ Z) : Im (mz Z') S ⊆ WZ Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Z K : ℕ) : pL ((pr Z).map fun e => 16 + (K - e.2)) = pk (PZ Z).length (fun j => 16 + (K - ((pr Z).getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
theorem imp_of {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk Z (L - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M)) : Imp Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hex : ∃ q, Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ pr Z, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → ∀ e ∈ pr Z, ∀ q < e.2, ¬ Sol (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro S hSW e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno S hSW e he q' (by omega) hs'
  obtain ⟨M, hM, hchk, hsym⟩ := hb t (by omega)
  have key : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card ∧ ¬ FM (mz Z) (tz Z) k t S (KP M) (KN M) := by
    clear h0 h1 hbd hl hm hSW hCS hS S
    intro S hSW hm
    have hl := hm.1
    have hbd : ∀ x ∈ S, x &&& mz Z = x := by
      intro x hx
      obtain ⟨w, _, rfl⟩ := hSW hx
      rw [Nat.and_assoc, Nat.and_self]
    obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
    obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Z) (mz Z) rawL
    set v := (avl (PZ Z) (mz Z) rawL).filter (fun w => decide (w.s ∈ S)) with hv
    have hsub : v.Sublist (avl (PZ Z) (mz Z) rawL) := List.filter_sublist
    have hnd : (v.map W.s).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
    have hrep : Rep v S := by
      refine ⟨hnd, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hv, List.mem_filter] at hw; simpa using hw.2
      · intro hx
        obtain ⟨w, hw, rfl⟩ := hSW hx
        obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
        exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
    have hwok : ∀ w ∈ v, WOk (PZ Z) w := by
      intro w hw
      obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
    have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good hx Z
    have hPlen : (PZ Z).length = (pr Z).length := by simp [PZ]
    have hPget : ∀ j < (PZ Z).length, (PZ Z).getD j 0 = mz ((pr Z).getD j (0, L - 1)).1 ∧ (pr Z).getD j (0, L - 1) ∈ pr Z := by
      intro j hj
      rw [hPlen] at hj
      simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    have X : Ctx (PZ Z) (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (tz Z) := by
      refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
      · obtain ⟨e1, e2⟩ := hPget j hj
        have h3 := hproj _ e2
        rw [e1, tz_sub h3.1]; exact h3
      · rw [pL_pk, List.length_map, hPlen]
        refine pk_congr fun j hj => ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hcl : Cl (PZ Z) (tz Z) (L - 1) (fun j => L - 1 - ((pr Z).getD j (0, L - 1)).2) S := by
      intro j hj q hq
      obtain ⟨e1, e2⟩ := hPget j hj
      have hq' : q + (L - 1 - ((pr Z).getD j (0, L - 1)).2) < L - 1 := hq
      rw [e1]; exact hno S hSW _ e2 q (by omega)
    have hle := cnt_le X hrep hwok hcl hm (by omega)
    have hst : StOk (PZ Z) (tz Z) (lz Z) (L - 1) (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
      refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
      rw [sumc_eq hwok, pk16, pk_sub]
      intro j hj; have := hle j hj; omega
    have hcov : Nat.beq (cov (pos t) (lz Z) v) (lz Z) = true := by
      rw [Nat.beq_eq]
      apply Nat.eq_of_testBit_eq; intro i
      cases hli : (lz Z).testBit i with
      | false =>
        by_contra hc
        obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
        rw [sp_bit, hli] at hw; simp at hw
      | true =>
        rw [cov_bit]
        obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
        obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
        obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
        exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
    have hsz := hm.size.1
    have hcard := hrep.card
    have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
      change v.length ≤ L - 1 + 1 - t; omega)
    have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
      intro p hpM
      have h2 := hchk p hpM
      simp only [chk, frc_eq, st_eq] at h2
      have h3 := anySub_false h2 v hsub
      simp only [startv, bR, hcov, hble, Bool.cond_true] at h3
      exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) (pos_eq t) rfl rfl h3
    obtain ⟨p0, hp0M⟩ := List.exists_mem_of_ne_nil M hM
    have hlen := (topC_succ (all p0 hp0M)).1
    exact ⟨by rw [hcard]; exact hlen, topC_sound X hlen all hst k (by omega) hm⟩
  obtain ⟨S', hS', hm', hfm⟩ := hsym k S hSW hm (key S hSW hm).1
  exact (key S' hS' hm').2 hfm
def PIK : ℕ := 0x22ebc778cf31e43c5780ef9e4bc3788efddebcb784f29e0bbc896ee1dbbba772eda22b89710e2dc538787ee5dcb39a73ce65cab9171ee6dca398720e39ceb93738e49c6c2c706e09c2b8484ed5daa34e6a6d31adb516a4d61aab5669ad2dad3506b2d3da5414660cbd9933165d03995b2a658ca604ae55c0b716fada5c4ba1732de5c6b916dad95d2b8573add5b0fd96aad45a6b59693f0556aa956aac552fa958ab0564acd57be454ca9553be07b4f49e83dc7b2f7dedbd77b0f55eb3d179ef79ea3dd7a6f39e6c5a8a113a2ac598b916e2c4538a913e26c578a515a28c4c77712223c4a893119daba774cea5d43a575ee89d0ba3740ea9d93b1768ecdd83a4758eb9d6bab73f0ee18c2f86d0f21d43487d0f61cc358610ba1c43386f0ca16b8c88510622443880e1a14c288570a9c0b7a6f2dedbc37c6fce01bfb7d6eedd5bb3746d8d9db2b706dedb5b73736d4dadb33646e4da5b8b686c6d899db3c67ace59d35c8430660bc1e84d0720ec2584707e1041882d0920dc22835055a4b0560cc1d81b04686afd602bd57ccf9afb606c2d75af33866ccdd9a3356670460841382503d96c0b81b032053285f0bd1792fe5fabed7e2f75f4c017b2f35e2c057caff5eabc18aaec5dabb975b10574ae55dab8616ad95ab0868cd1da434468ac098d31e630c9191b21644c7d8cb27640c758bb26638c958db165dec4989b14622ba9fdc027f3006043fe7ff00dfd40780b001fc4067fb011fe3f75aefc9fabf47e6fc568ace59eb41662cd596a8151aa1544a7d62a9c53aa6d60b41684cfda02bc61ac3d8730c56ec2984ab47ccf9df4be87caab9f6bec7defb9f5aa87c2f8df12a4592b1d642ca58ca7961ac4584a694a295526a594c29952ea494528851ea354728950ea4546290516a19429ab5066a0d4a804d29f933a7c2be9e8b09624ee570aea7433a9c8cda7029c9b8a826c2989a93fa684fa998dba6436a6d1309994be65ccb25c4ae9612ca5a4b69592a2554a65f928981300938be17b496524a524825e91886a443de9086d24014e8f89612d47642d1c9082128d8f6a343d68c86b8d845e3506aa2c1448a8520a544e26c4d09812a24c4e0a013e2644f09612825c4e89242e484902141f63e9088f81ee838ef20c3b882864a0818e319028760ea8083c2000dc1b4358680ce1bc398720d81c43486a0e0198329f04867b91a9ec4667a88d91a3ce4788e9e41ea788798f23be834eea0b3b6758eb9d83b2768ea9ce39a72ce41c739e750e99cc3a4724e51d13a0718e28c4386308609c00c418cde9bc376698d29b84ca6d931a62366624d895a35e560ab9ac5086a940a8234e6e8dc9a434067cd09a33446793999c4e2669301984bc974ca98730c648c218331e554c69532a4628d918832864cc29913206092824f2fe948bea4d4985e8bc97828a510ba9472e64f49e13926c4f8a11412764e8a01372704fc9a9342c69e13c9604f65793aa762b66c0ac9ae35a558c715431862ca8a6d29e9bca6a6b296925251482e8518bb9762865b4b61692cc5b8b91712d65a8b81672d05bcb29642664c49913048e4b91e23d2564a09492a24e4108192420c4890b21523e798f291c3d27a08c8cf22e3486891411a2308889011e4392290c4744291ba3820e48c8292624a4087f0fd1fe404800fc4268487ca1041e3d8f18f43c2780788cd1de32c7688a1d620c410800fa210440871022183f07c0fe2143d87a1b69046ca3046235916a2e1a64588a8d0230338780cc1dc329048c840e818629c4186708e08c01782ec5e8bf17c2e8300b80b21602b0530b41782e8570b81502a85b0a4144280a847e299142291468ac50a2043e8750ca2144c8950f22443487111a1b4448604891021e238899121163b0448e51c83886f0e61d43a4718e81be384738e01ba3703ca010ee811018743f27e0fb1f33f47fcff1f73fa7d0fa9fc3f67c8f886437c6fc308b90be2c8588af1582cc5b8b61602d4568ae1682ac550a909e124240460861282704d08e130220450961042104002e07c1a0260500bc0a0100020240783d0220b8118220740c8050210180680303b0400f00c81d0620c01602707c04c120180100a81281c07e0100583903c0141983806a00c0002b02a0b41b01b0040a40901601c01c1b80d
def pi0 (i : ℕ) : ℕ := Nat.mod (Nat.shiftRight PIK (Nat.mul 11 i)) 2048
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pi0_ok : ∀ i < NN, pi0 i < NN ∧ pi0 (pi0 i) = i := by decide +kernel
def pi (i : ℕ) : ℕ := if i < NN then pi0 i else if i < NN + NN then NN + pi0 (i - NN) else i
lemma pi_pi (i : ℕ) : pi (pi i) = i := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1, this]
  · by_cases h2 : i < NN + NN
    · have := pi0_ok (i - NN) (by omega)
      simp [h1, h2, this]; omega
    · simp [h1, h2]
lemma pi_lt {i : ℕ} (h : i < NN + NN) : pi i < NN + NN := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1]; omega
  · have := pi0_ok (i - NN) (by omega); simp [h1, h]; omega
def rho (w : ℕ) : ℕ := (∑ i ∈ Finset.range (NN + NN), (w.testBit (pi i)).toNat * 2 ^ i) + 2 ^ (NN + NN) * (w >>> (NN + NN))
lemma bits_sum (n : ℕ) (f : ℕ → Bool) : (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i) < 2 ^ n ∧
    ∀ j, (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i).testBit j = (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm]
    have hb : (f n).toNat ≤ 1 := by cases f n <;> simp
    constructor
    · have := ih.1
      have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ hb
      rw [pow_succ]; omega
    · intro j
      rw [Nat.testBit_two_pow_mul_add _ ih.1, ih.2]
      split_ifs with h
      · simp [h, show j < n + 1 by omega]
      · rcases Nat.eq_or_lt_of_le (not_lt.1 h) with rfl | h2
        · cases f n <;> simp
        · have : (f n).toNat.testBit (j - n) = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hb (Nat.one_lt_two_pow (by omega)))
          rw [this]; simp [show ¬ j < n + 1 by omega]
lemma rho_bit (w i : ℕ) : (rho w).testBit i = w.testBit (pi i) := by
  unfold rho
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bits_sum _ _).1]
  split_ifs with h
  · rw [(bits_sum _ _).2]; simp [h]
  · rw [Nat.testBit_shiftRight, show NN + NN + (i - (NN + NN)) = i by omega]
    unfold pi; simp [h, show ¬ i < NN by omega]
lemma rho_ext {w w' : ℕ} (h : ∀ i, w.testBit (pi i) = w'.testBit i) : rho w = w' :=
  Nat.eq_of_testBit_eq fun i => by rw [rho_bit, h]
lemma rho_phi (w : ℕ) : rho (rho w) = w := rho_ext fun i => by rw [rho_bit, pi_pi]
lemma rho_op (d : Bool) (a b : ℕ) : rho (op d a b) = op d (rho a) (rho b) :=
  rho_ext fun i => by simp only [op_bit, rho_bit]
lemma rho_xor (a b : ℕ) : rho (a ^^^ b) = rho a ^^^ rho b := rho_ext fun i => by simp only [Nat.testBit_xor, rho_bit]
lemma rho_and (a b : ℕ) : rho (a &&& b) = rho a &&& rho b := rho_ext fun i => by simp only [Nat.testBit_and, rho_bit]
lemma rho_zero : rho 0 = 0 := rho_ext fun i => by simp
lemma rho_inj {a b : ℕ} (h : rho a = rho b) : a = b := by rw [← rho_phi a, h, rho_phi]
def eqv (w w' : ℕ) : Bool := decide (w < 2 ^ (NN + NN)) && decide (w' < 2 ^ (NN + NN)) && (List.range (NN + NN)).all (fun i => w.testBit (pi i) == w'.testBit i)
lemma eqv_phi {w w' : ℕ} (h : eqv w w' = true) : rho w = w' := by
  simp only [eqv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine rho_ext fun i => ?_
  by_cases hi : i < NN + NN
  · exact h.2 i hi
  · have : pi i = i := by unfold pi; simp [hi, show ¬ i < NN by omega]
    have hp : 2 ^ (NN + NN) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [this, Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
lemma Sol.rho {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) : Sol (rho m) (rho T) q (DummyCertificate.rho '' S) := by
  induction h with
  | done h => exact .done ⟨_, h, rfl⟩
  | un h _ ih =>
    refine .un (Set.mem_image_of_mem _ h) ?_
    rw [← rho_xor, ← Set.image_insert_eq]; exact ih
  | @bi _ _ d _ _ h1 h2 _ ih =>
    refine .bi (d := d) (Set.mem_image_of_mem _ h1) (Set.mem_image_of_mem _ h2) ?_
    rw [← rho_op, ← Set.image_insert_eq]; exact ih
lemma Live.rho {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Live (rho m) (rho T) k t (S.image DummyCertificate.rho) := by
  induction h with
  | stop => rw [Finset.image_singleton]; exact .stop
  | un _ ih =>
    rw [Finset.image_insert, rho_xor] at ih
    rw [Finset.image_insert]; exact .un ih
  | bi hab _ ih =>
    rw [Finset.image_insert, rho_op] at ih
    rw [Finset.image_insert, Finset.image_insert]
    exact .bi (fun e => hab (rho_inj e)) ih
lemma Un.rho {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : Un (rho m) (rho a) (S.image DummyCertificate.rho) (S'.image DummyCertificate.rho) := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨U.image _, by rw [Finset.image_insert], by rw [Finset.image_insert, rho_xor]⟩
lemma Bi.rho {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d (rho a) (rho b) (S.image DummyCertificate.rho) (S'.image DummyCertificate.rho) := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨fun e => hab (rho_inj e), U.image _, by rw [Finset.image_insert, Finset.image_insert], by rw [Finset.image_insert, rho_op]⟩
def rawS : List ℕ := (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).map (fun i => rawP.getD i 0)) ++ [rawP.getD 0 0 ||| rawP.getD 1 0]
def rawT : List (ℕ × ℕ) := rawL.zip rawS
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_ok : rawT.all (fun p => eqv p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_fst : rawT.map Prod.fst = rawL := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_snd : rawT.all (fun p => rawL.contains p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_phi : eqv TG TG = true := by decide +kernel
lemma raw_phi {w : ℕ} (hw : w ∈ rawL) : ∃ p ∈ rawT, p.1 = w ∧ rho w = p.2 ∧ p.2 ∈ rawL := by
  rw [← rawT_fst, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  refine ⟨p, hp, rfl, eqv_phi (List.all_eq_true.1 rawT_ok p hp), ?_⟩
  simpa using List.all_eq_true.1 rawT_snd p hp
lemma WZ_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) {x : ℕ} (hx : x ∈ WZ Z') : rho x ∈ WZ Z := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨p, _, _, e, hp⟩ := raw_phi hw
  exact ⟨p.2, hp, by rw [rho_and, h, e]⟩
lemma tz_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) : rho (tz Z') = tz Z := by
  simp only [tz, nl]; rw [rho_and, h, eqv_phi TG_phi]
theorem imp_sym {Z Z' L : ℕ} (h : Imp Z L) (he : eqv (mz Z') (mz Z) = true) : Imp Z' L := by
  intro q hq hs
  have h' := eqv_phi he
  have h2 := hs.rho
  rw [h', tz_phi h'] at h2
  refine h q hq (h2.mono le_rfl ?_)
  rintro _ ⟨x, hx | hx, rfl⟩
  · exact Or.inl (WZ_phi h' hx)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h']; exact Or.inr (Set.mem_insert_of_mem _ rfl)
def kOk (M : List (ℕ × ℕ)) : Bool := rawT.all (fun p => (M.any (fun x => hb x.2 p.1) || M.any (fun x => hb x.2 p.2)) &&
  rawT.all (fun q => Nat.beq p.1 q.1 || M.any (fun x => hb x.1 (p.1 + q.1)) || M.any (fun x => hb x.1 (p.2 + q.2))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_full : rawL.all (fun w => Nat.beq (Nat.land w (mz 0)) w) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_phi : eqv (mz 0) (mz 0) = true := by decide +kernel
lemma WZ0 {x : ℕ} (hx : x ∈ WZ 0) : x ∈ rawL := by
  obtain ⟨w, hw, rfl⟩ := hx
  have := List.all_eq_true.1 m0_full w hw
  rw [Nat.beq_eq, nl] at this; rwa [this]
lemma sym0 {M : List (ℕ × ℕ)} (hM : kOk M = true) (k t : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ 0) (hm : Min (mz 0) (tz 0) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 0 ∧ Min (mz 0) (tz 0) k t S' ∧ FM (mz 0) (tz 0) k t S' (KP M) (KN M) := by
  have pm := eqv_phi m0_phi
  have pt := tz_phi pm
  have hN : ∀ a ∈ S, KN M a ∨ KN M (rho a) := by
    intro a ha
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, ← e1]; exact this.1.imp id id
  have hP : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → KP M a b ∨ KP M (rho a) (rho b) := by
    intro a ha b hb hab
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    obtain ⟨q, hq, f1, f2, _⟩ := raw_phi (WZ0 (hS hb))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true] at this
    have := List.all_eq_true.1 this.2 q hq
    simp only [Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, f2, ← e1, ← f1]
    rcases this with (h | h) | h
    · exact absurd (e1.symm.trans ((Nat.eq_of_beq_eq_true h).trans f1)) hab
    · exact Or.inl h
    · exact Or.inr h
  have hS' : ((S.image DummyCertificate.rho : Finset ℕ) : Set ℕ) ⊆ WZ 0 := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact WZ_phi pm (hS hy)
  have hm' : Min (mz 0) (tz 0) k t (S.image DummyCertificate.rho) := by
    have h1 := hm.1.rho
    rw [pm, pt] at h1
    refine ⟨h1, fun q hq hs => hm.2 q hq ?_⟩
    have h2 := hs.rho
    rw [pm, pt] at h2
    refine h2.mono le_rfl ?_
    rintro _ ⟨x, hx | hx, rfl⟩
    · simp only [Finset.coe_image, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [rho_phi]; exact Or.inl hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx, rho_zero]; exact Or.inr (Set.mem_insert _ _)
      · rw [hx, pm]; exact Or.inr (Set.mem_insert_of_mem _ rfl)
  rcases first_move k t S hm hc with ⟨k0, d, a, b, S1, e, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, e, e', hu, hne, hu', hb, hl⟩
  · rcases hP a hb.sub.1 b hb.sub.2.1 hb.1 with h | h
    · exact ⟨S, hS, hm, Or.inl ⟨k0, d, a, b, S1, e, h, hb, hl⟩⟩
    · refine ⟨_, hS', hm', Or.inl ⟨k0, d, rho a, rho b, _, e, h, hb.rho, ?_⟩⟩
      have := hl.rho; rwa [pm, pt] at this
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h, hu, hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h2 := hb.rho; rw [rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      exact ⟨_, hS', hm', Or.inr (Or.inl ⟨k0, t0, rho a, d, rho c, _, _, e, e', h, h1, h2, h3⟩)⟩
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h, hu, hne, hu', hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h1' := hu'.rho; rw [pm] at h1'
      have h2 := hb.rho; rw [rho_xor, rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      refine ⟨_, hS', hm', Or.inr (Or.inr ⟨k0, t0, rho a, rho a', d, _, _, _, e, e', h, h1, fun e => hne ?_, h1', h2, h3⟩)⟩
      apply rho_inj; rw [e, rho_xor, pm]
def FF : ℕ := 2 ^ MM - 1
lemma hbF (x : ℕ) : hb FF x = true := by
  have h : x % MM < MM := Nat.mod_lt _ (by decide)
  have h2 : FF.testBit (x % MM) = true := by rw [FF, Nat.testBit_two_pow_sub_one]; simpa using h
  unfold hb
  rw [Nat.beq_eq]
  change (FF >>> (x % MM)) &&& 1 = 1
  rw [Nat.testBit] at h2
  rw [Nat.and_one_is_mod]
  simp only [Nat.one_and_eq_mod_two, bne_iff_ne, ne_eq] at h2
  omega
lemma FM_mono {m T k t : ℕ} {S : Finset ℕ} {A A' : ℕ → ℕ → Prop} {B B' : ℕ → Prop} (h : FM m T k t S A B) (h1 : ∀ x y, A x y → A' x y)
    (h2 : ∀ x, B x → B' x) : FM m T k t S A' B' := by
  rcases h with ⟨k0, d, a, b, S1, e, q, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', q, h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', q, h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, h1 _ _ q, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h2 _ q, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h2 _ q, h⟩)
theorem imp_full {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, chk Z (L - 1) t FF FF = false) : Imp Z L := by
  refine imp_of hp hL hI (hb.imp id fun h t ht => ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩)
  · simp only [List.mem_singleton] at hp; subst hp; exact h t ht
  · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
noncomputable def okT (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk Z (L - 1) t FF FF)
noncomputable def okE (e : ℕ × ℕ) : Bool := pOk e.1 && Nat.ble e.2 15 && ((pr e.1).any (fun x => Nat.ble e.2 x.2) || okT e.1 e.2 (List.range e.2))
def kFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r) && M.any (fun p => hb p.2 r))
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
lemma sym_full {Z t : ℕ} {M : List (ℕ × ℕ)} (hM : kFull M = true) (k : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ Z) (hm : Min (mz Z) (tz Z) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M) := by
  have h : ∀ x, (∃ p ∈ M, hb p.1 x = true) ∧ ∃ p ∈ M, hb p.2 x = true := by
    intro x
    have := List.all_eq_true.1 hM (x % MM) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
    simp only [Bool.and_eq_true, List.any_eq_true, ← hb_mod] at this
    exact this
  exact ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => (h (x + y)).1) (fun x _ => (h x).2)⟩
lemma imp_okE {e : ℕ × ℕ} (h : okE e = true) (hI : ∀ e' ∈ pr e.1, Imp e'.1 e'.2) : Imp e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_full h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) id)
def tab1 : List (ℕ × ℕ) := [(16, 13), (64, 13), (128, 13), (1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)]
def tab2 : List (ℕ × ℕ) := [(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11), (3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)]
def tab3 : List (ℕ × ℕ) := [(19, 8), (25, 8), (28, 8), (49, 8), (67, 8), (70, 8), (81, 8), (82, 8), (88, 8), (134, 8), (140, 8), (145, 8), (148, 8), (152, 8), (161, 8), (164, 8), (176, 8), (194, 8), (196, 8), (208, 8), (224, 8), (280, 8), (322, 8), (328, 8), (336, 8), (352, 8), (416, 8), (448, 8), (7, 7), (14, 7), (21, 7), (26, 7), (35, 7), (56, 7), (74, 7), (84, 7), (98, 7), (112, 7), (133, 7), (146, 7), (162, 7), (168, 7), (193, 7), (200, 7), (268, 7), (273, 7), (289, 7), (296, 7), (321, 7), (324, 7), (388, 7), (400, 7), (22, 6), (76, 6), (97, 6), (131, 6), (304, 6), (392, 6), (11, 5), (13, 5), (37, 5), (38, 5), (41, 5), (42, 5), (44, 5), (50, 5), (52, 5), (69, 5), (73, 5), (100, 5), (104, 5), (137, 5), (138, 5), (259, 5), (261, 5), (262, 5), (265, 5), (266, 5), (274, 5), (276, 5), (290, 5), (292, 5), (385, 5), (386, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr3 : tab3.all (fun e => (pr e.1).isEmpty) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr2 : tab2.all (fun e => (pr e.1).all (fun x => tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr1 : tab1.all (fun e => (pr e.1).all (fun x => tab2.contains x || tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr0 : (pr 0).all (fun x => tab1.contains x || tab2.contains x || tab3.contains x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : tab3.all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2l : ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ)).all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17 : okE (17, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24 : okE (24, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c80 : okE (80, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c132 : okE (132, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c144 : okE (144, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66 : eqv (mz 66) (mz 17) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s320 : eqv (mz 320) (mz 24) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s160 : eqv (mz 160) (mz 132) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s192 : eqv (mz 192) (mz 144) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1l : ([(1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)] : List (ℕ × ℕ)).all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16 : pOk 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_0 : chk 16 12 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_2 : chk 16 12 2 FF FF = false := by decide +kernel
def N16 : List (ℕ × ℕ) := [(0x3fffffffffffffdfffffffefffff7ffffffbffffdffffff7ffffff, 0x3fff7ffffffffffeffffffffffffffffffffeffffffff7ffffffff), (0x4000000000008000000, 0x80000000000000000000000000000000100000000800000000), (0x2000000010000080000000000020000000000000, 0x100000000000000000000000000000000000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16 : kFull N16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_0 : chk 16 12 1 0x3fffffffffffffdfffffffefffff7ffffffbffffdffffff7ffffff 0x3fff7ffffffffffeffffffffffffffffffffeffffffff7ffffffff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_1 : chk 16 12 1 0x4000000000008000000 0x80000000000000000000000000000000100000000800000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_2 : chk 16 12 1 0x2000000010000080000000000020000000000000 0x100000000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_r : okT 16 13 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p128 : pOk 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_0 : chk 128 12 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_2 : chk 128 12 2 FF FF = false := by decide +kernel
def N128 : List (ℕ × ℕ) := [(0x3fffffffbfffffbffffffffffdbfffffffffffffffffffffffffff, 0x3fffffffdfffffffffffffffffdfffffffffffffffffffffffffed), (0x4000004000000000004000000000000000000000000000, 0x2000000000000000000000000000000000000000000010), (0x20000000000000000020000000000000000000000000000, 0x2000000000000000000000000002)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k128 : kFull N128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_0 : chk 128 12 1 0x3fffffffbfffffbffffffffffdbfffffffffffffffffffffffffff 0x3fffffffdfffffffffffffffffdfffffffffffffffffffffffffed = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_1 : chk 128 12 1 0x4000004000000000004000000000000000000000000000 0x2000000000000000000000000000000000000000000010 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_2 : chk 128 12 1 0x20000000000000000020000000000000000000000000000 0x2000000000000000000000000002 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_r : okT 128 13 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64 : eqv (mz 64) (mz 16) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0 : pOk 0 = true := by decide +kernel
def M0 : List (ℕ × ℕ) := [(0x90000044088000021100000000102000400810000010000, 0x1020000000000000000000000000040000100200000004000000), (0x40000000000000000000000000000800000, 0x0), (0x800000000000000001000, 0x0), (0x8000000000000000000000000000000000008000000000200, 0x0), (0x1000000000000080000000400000000000000000000000, 0x0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : kOk M0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_0 : chk 0 14 0 0x90000044088000021100000000102000400810000010000 0x1020000000000000000000000000040000100200000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_1 : chk 0 14 0 0x40000000000000000000000000000800000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_2 : chk 0 14 0 0x800000000000000001000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_3 : chk 0 14 0 0x8000000000000000000000000000000000008000000000200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_4 : chk 0 14 0 0x1000000000000080000000400000000000000000000000 0x0 = false := by decide +kernel
def M1 : List (ℕ × ℕ) := [(0x90000044088000021100000000102000400810000010000, 0x1000000000000000000000000000040000000000000000000000), (0x40000000000000000000000000000000000, 0x0), (0x200, 0x0), (0x800000, 0x0), (0x1000, 0x0), (0x80000000000800000000000000000000, 0x0), (0x8000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000000100000000000000000), (0x400000000008000000000000, 0x0), (0x1000000000000000000000000000000000000000000000, 0x200000004000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1 : kOk M1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_0 : chk 0 14 1 0x90000044088000021100000000102000400810000010000 0x1000000000000000000000000000040000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_1 : chk 0 14 1 0x40000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_2 : chk 0 14 1 0x200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_3 : chk 0 14 1 0x800000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_4 : chk 0 14 1 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_5 : chk 0 14 1 0x80000000000800000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_6 : chk 0 14 1 0x8000000000000000000000000000000000000000000000000 0x20000000000000000000000000000000100000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_7 : chk 0 14 1 0x400000000008000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_8 : chk 0 14 1 0x1000000000000000000000000000000000000000000000 0x200000004000000 = false := by decide +kernel
def M2 : List (ℕ × ℕ) := [(0x90000044088040021100000000102000400810000010000, 0x1020000000000000000000000000040000100000000004000000), (0x8001000000000000000000000000000000008000000000200, 0x200000000000000), (0x80000000400800000000000000801000, 0x0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2 : kOk M2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_0 : chk 0 14 2 0x90000044088040021100000000102000400810000010000 0x1020000000000000000000000000040000100000000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_1 : chk 0 14 2 0x8001000000000000000000000000000000008000000000200 0x200000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_2 : chk 0 14 2 0x80000000400800000000000000801000 0x0 = false := by decide +kernel
def M3 : List (ℕ × ℕ) := [(0x80910000440880400a1100000400902000408810000811200, 0x1020000000000000000000000000040000100200000004000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k3 : kOk M3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3_0 : chk 0 14 3 0x80910000440880400a1100000400902000408810000811200 0x1020000000000000000000000000040000100200000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r_r : okT 0 15 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem i3 : ∀ e ∈ tab3, Imp e.1 e.2 := fun e he => imp_okE (List.all_eq_true.1 c3 e he) fun x hx => by
  have := List.all_eq_true.1 pr3 e he
  rw [List.isEmpty_iff] at this; rw [this] at hx; simp at hx
lemma up2 {e : ℕ × ℕ} (he : e ∈ tab2) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx =>
  i3 x (by simpa using List.all_eq_true.1 (List.all_eq_true.1 pr2 e he) x hx)
theorem i17 : Imp 17 11 := imp_okE (e := (17, 11)) c17 (up2 (by decide +kernel))
theorem i24 : Imp 24 11 := imp_okE (e := (24, 11)) c24 (up2 (by decide +kernel))
theorem i80 : Imp 80 11 := imp_okE (e := (80, 11)) c80 (up2 (by decide +kernel))
theorem i132 : Imp 132 11 := imp_okE (e := (132, 11)) c132 (up2 (by decide +kernel))
theorem i144 : Imp 144 11 := imp_okE (e := (144, 11)) c144 (up2 (by decide +kernel))
theorem i66 : Imp 66 11 := imp_sym i17 s66
theorem i320 : Imp 320 11 := imp_sym i24 s320
theorem i160 : Imp 160 11 := imp_sym i132 s160
theorem i192 : Imp 192 11 := imp_sym i144 s192
theorem i2 : ∀ e ∈ tab2, Imp e.1 e.2 := by
  intro e he
  by_cases hl : e ∈ ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ))
  · exact imp_okE (List.all_eq_true.1 c2l e hl) (up2 he)
  · have : e ∈ ([(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11)] : List (ℕ × ℕ)) := by
      have h : tab2.all (fun e => ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ)).contains e || ([(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11)] : List (ℕ × ℕ)).contains e) = true := by decide +kernel
      have := List.all_eq_true.1 h e he
      rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
      exact this.resolve_left hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact i17
    · exact i24
    · exact i66
    · exact i80
    · exact i132
    · exact i144
    · exact i160
    · exact i192
    · exact i320
lemma up1 {e : ℕ × ℕ} (he : e ∈ tab1) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx => by
  have := List.all_eq_true.1 (List.all_eq_true.1 pr1 e he) x hx
  rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
  exact this.elim (i2 x) (i3 x)
theorem i16 : Imp 16 13 := by
  refine imp_of p16 (by decide) (up1 (e := (16, 13)) (by decide +kernel)) (Or.inr fun t ht => ?_)
  have one : ∀ t, chk 16 12 t FF FF = false → ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk 16 (13 - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ 16 → Min (mz 16) (tz 16) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 16 ∧ Min (mz 16) (tz 16) k t S' ∧ FM (mz 16) (tz 16) k t S' (KP M) (KN M) := fun t h =>
    ⟨[(FF, FF)], by simp, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h,
      fun k S hS hm hc => ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)⟩⟩
  by_cases h3 : t < 3
  · interval_cases t
    · exact one 0 c16_0
    · refine ⟨N16, by simp [N16], fun p hp => ?_, sym_full k16⟩
      simp only [N16, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r16_0
      · exact r16_1
      · exact r16_2
    · exact one 2 c16_2
  · have h := List.all_eq_true.1 c16_r t (by simp; omega)
    rw [Bool.not_eq_true'] at h
    exact one t h
theorem i128 : Imp 128 13 := by
  refine imp_of p128 (by decide) (up1 (e := (128, 13)) (by decide +kernel)) (Or.inr fun t ht => ?_)
  have one : ∀ t, chk 128 12 t FF FF = false → ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk 128 (13 - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ 128 → Min (mz 128) (tz 128) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 128 ∧ Min (mz 128) (tz 128) k t S' ∧ FM (mz 128) (tz 128) k t S' (KP M) (KN M) := fun t h =>
    ⟨[(FF, FF)], by simp, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h,
      fun k S hS hm hc => ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)⟩⟩
  by_cases h3 : t < 3
  · interval_cases t
    · exact one 0 c128_0
    · refine ⟨N128, by simp [N128], fun p hp => ?_, sym_full k128⟩
      simp only [N128, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r128_0
      · exact r128_1
      · exact r128_2
    · exact one 2 c128_2
  · have h := List.all_eq_true.1 c128_r t (by simp; omega)
    rw [Bool.not_eq_true'] at h
    exact one t h
theorem i64 : Imp 64 13 := imp_sym i16 s64
theorem i1 : ∀ e ∈ tab1, Imp e.1 e.2 := by
  intro e he
  by_cases hl : e ∈ ([(1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)] : List (ℕ × ℕ))
  · exact imp_okE (List.all_eq_true.1 c1l e hl) (up1 he)
  · simp only [tab1, List.mem_cons, List.not_mem_nil, or_false] at he hl
    push Not at hl
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact i16
    · exact i64
    · exact i128
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
theorem i0 : Imp 0 15 := by
  refine imp_of p0 le_rfl (fun x hx => ?_) (Or.inr fun t ht => ?_)
  · have := List.all_eq_true.1 pr0 x hx
    rw [Bool.or_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem, List.contains_iff_mem] at this
    exact this.elim (fun h => h.elim (i1 x) (i2 x)) (i3 x)
  by_cases h4 : t < 4
  · interval_cases t
    · refine ⟨M0, by simp [M0], fun p hp => ?_, fun k S => sym0 k0 k 0 S⟩
      simp only [M0, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact r0_0
      · exact r0_1
      · exact r0_2
      · exact r0_3
      · exact r0_4
    · refine ⟨M1, by simp [M1], fun p hp => ?_, fun k S => sym0 k1 k 1 S⟩
      simp only [M1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact r1_0
      · exact r1_1
      · exact r1_2
      · exact r1_3
      · exact r1_4
      · exact r1_5
      · exact r1_6
      · exact r1_7
      · exact r1_8
    · refine ⟨M2, by simp [M2], fun p hp => ?_, fun k S => sym0 k2 k 2 S⟩
      simp only [M2, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r2_0
      · exact r2_1
      · exact r2_2
    · refine ⟨M3, by simp [M3], fun p hp => ?_, fun k S => sym0 k3 k 3 S⟩
      simp only [M3, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      · exact r3_0
  · refine ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩
    · simp only [List.mem_singleton] at hp; subst hp
      have h := List.all_eq_true.1 r_r t (by simp; omega)
      rwa [Bool.not_eq_true'] at h
    · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def EF : ℕ := (([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (ℕ × ℕ)).map
  (fun e => rawP.getD e.1 0 &&& rawP.getD e.2 0)).foldr (· ||| ·) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 9 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma rawL_mem (i : ℕ) (hi : i < 9) : rawP.getD i 0 ∈ rawL := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [rawP_len]; exact hi)]
  exact List.mem_append_left _ (List.getElem_mem _)
lemma or01_mem : rawP.getD 0 0 ||| rawP.getD 1 0 ∈ rawL := List.mem_append_right _ (by simp)
lemma raw_sub {x : ℕ} (hx : x ∈ rawL) : x &&& mz 0 = x := by
  have := List.all_eq_true.1 m0_full x hx
  rwa [Nat.beq_eq, nl] at this
theorem final : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hfun
  by_contra hsz
  obtain ⟨gates, out⟩ := C
  let row : ℕ → Fin 9 → Bool := fun b v => (rawP.getD v.val 0).testBit b
  have hrow : ∀ b, List.ofFn (row b) = rawP.map (fun x => x.testBit b) := row_list
  have hRP : ∀ x ∈ rawP, x &&& mz 0 = x := fun x hx => raw_sub (List.mem_append_left _ hx)
  match gates, hfan, hfirst, hfun, hsz with
  | [], _, hfirst, _, _ =>
    have := hfirst (fun _ => true)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires] at this
  | g :: gs, hfan, hfirst, hfun, hsz =>
    have hlen : gs.length ≤ 14 := by
      have : ¬ 16 ≤ gs.length + 1 := hsz
      omega
    have hg : ∀ x ∈ g :: gs, x.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ x.inputs.length ≤ 2 := hfan
    have hy : gv (mz 0) rawP g = rawP.getD 0 0 ||| rawP.getD 1 0 := by
      apply Nat.eq_of_testBit_eq; intro b
      cases hb : (mz 0).testBit b with
      | false =>
        have e1 := congrArg (fun x => x.testBit b) (gv_sub (mz 0) hRP g)
        have e2 := congrArg (fun x => x.testBit b) (raw_sub or01_mem)
        simp only [Nat.testBit_and, hb, Bool.and_false] at e1 e2
        rw [← e1, ← e2]
      | true =>
        have h := hfirst (row b)
        have e : (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b)) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)]) := by
          rw [hrow]; rfl
        rw [e, fold_keep _ _ _ (by simp [rawP_len]), ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self)] at h
        have h9 : (rawP.map (fun x => x.testBit b) ++ [(gv (mz 0) rawP g).testBit b]).getD 9 false = (gv (mz 0) rawP g).testBit b := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [rawP_len])]; simp [rawP_len]
        rw [h9] at h
        rw [h, Nat.testBit_or]; rfl
    have hsub : ∀ x ∈ rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0], x ∈ rawL := fun x hx => hx
    have hout : (ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0])).getD out 0 = tz 0 := by
      rw [← EF_ok]
      have hs : ∀ x ∈ ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]), x &&& mz 0 = x :=
        ex_sub (mz 0) fun x hx => raw_sub (hsub x hx)
      have hs' := getD_mem (S := {x | x &&& mz 0 = x}) hs (by simp) out
      apply Nat.eq_of_testBit_eq; intro b
      have e1 := congrArg (fun x => x.testBit b) hs'
      simp only [Nat.testBit_and] at e1
      rw [← e1, Nat.testBit_and]
      cases hb : (mz 0).testBit b with
      | false => simp
      | true =>
        simp only [Bool.and_true]
        rw [← getD_map, ex_bit (mz 0) hb gs _ (fun x hx => hg x (List.mem_cons_of_mem _ hx))]
        have h := congrFun hfun (row b)
        have e : PEqualNP.MetaComplexity.circuitFun 9 ⟨g :: gs, out⟩ (row b) =
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)])).getD out false := by
          change ((PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b))).getD out false = _
          rw [hrow]; rfl
        rw [e, ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self), hy] at h
        rw [List.map_append, List.map_singleton, h]
        simp only [EF, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.testBit_or, Nat.testBit_and, Nat.zero_testBit, Bool.or_false]
        simp only [Bool.or_assoc]; rfl
    have hsol := ex_sol (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]) (C (mz 0) (WZ 0))
      (fun x hx => Or.inl ⟨x, hsub x hx, (raw_sub (hsub x hx)).symm⟩) (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx)) ⟨out, hout⟩
    exact i0 _ (by omega) hsol
end DummyCertificate

namespace PetersenMemo

abbrev StatePool := List (BitVec 29)
abbrev Key := Nat × StatePool

inductive Cache where
  | empty
  | node (bucket : List Key) (left right : Cache)

namespace Cache

def keys : Cache → List Key
  | .empty => []
  | .node ks _ _ => ks

def lo : Cache → Cache
  | .empty => .empty
  | .node _ l _ => l

def hi : Cache → Cache
  | .empty => .empty
  | .node _ _ r => r

def entries : Cache → List Key
  | .empty => []
  | .node ks l r => ks ++ (entries l ++ entries r)

lemma components (m : Cache) : entries m = keys m ++ (entries (lo m) ++ entries (hi m)) := by cases m <;> rfl

def code (key : Key) : Nat :=
  key.2.foldl (fun h w => (h * 65599 + w.toNat + 1) % 131071) (key.1 + 11)

def containsAt : Nat → Nat → Key → Cache → Bool
  | _,_,_,.empty => false
  | 0,_,key,.node ks _ _ => ks.contains key
  | d+1,h,key,.node _ l r =>
    if h % 2 = 0 then containsAt d (h / 2) key l else containsAt d (h / 2) key r

def addAt : Nat → Nat → Key → Cache → Cache
  | 0,_,key,m => .node (key::keys m) (lo m) (hi m)
  | d+1,h,key,m => if h % 2 = 0 then .node (keys m) (addAt d (h / 2) key (lo m)) (hi m)
                     else .node (keys m) (lo m) (addAt d (h / 2) key (hi m))

def has (m : Cache) (key : Key) := containsAt 17 (code key) key m

def add (m : Cache) (key : Key) := addAt 17 (code key) key m

lemma contains_spec (d h : Nat) (key : Key) (m : Cache) :
    containsAt d h key m = true → key ∈ entries m := by
  induction d generalizing h m with
  | zero =>
    cases m with
    | empty => simp [containsAt]
    | node ks l r => intro found; exact List.mem_append_left _ (List.contains_iff_mem.mp found)
  | succ d ih =>
    cases m with
    | empty => simp [containsAt]
    | node ks l r =>
      intro found
      change (if h % 2 = 0 then containsAt d (h / 2) key l else containsAt d (h / 2) key r) = true at found
      apply List.mem_append_right
      split at found
      · exact List.mem_append_left _ (ih _ _ found)
      · exact List.mem_append_right _ (ih _ _ found)

lemma add_spec (d h : Nat) (key : Key) (m : Cache) (x : Key) :
    x ∈ entries (addAt d h key m) → x = key ∨ x ∈ entries m := by
  induction d generalizing h m with
  | zero =>
    rw [components m]
    simp only [addAt,entries,List.mem_append,List.mem_cons]
    tauto
  | succ d ih =>
    rw [components m]
    simp only [addAt]
    split
    · simp only [entries,List.mem_append]
      rintro (k | l | r)
      · exact Or.inr (Or.inl k)
      · rcases ih _ _ l with eq | old
        · exact Or.inl eq
        · exact Or.inr (Or.inr (Or.inl old))
      · exact Or.inr (Or.inr (Or.inr r))
    · simp only [entries,List.mem_append]
      rintro (k | l | r)
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr (Or.inl l))
      · rcases ih _ _ r with eq | old
        · exact Or.inl eq
        · exact Or.inr (Or.inr (Or.inr old))

end Cache


def reference (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) :
    Nat → StatePool → Bool
  | 0, xs => hit xs
  | k+1, xs => hit xs || (children (k+1) xs).any (reference hit children k)

def visit (step : StatePool → Cache → Bool × Cache) : List StatePool → Cache → Bool × Cache
  | [], memo => (false, memo)
  | x::xs, memo =>
    let result := step x memo
    if result.1 then result else visit step xs result.2

def memoized (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) :
    Nat → StatePool → Cache → Bool × Cache
  | 0, xs, table => (hit xs, table)
  | k+1, xs, table =>
    if hit xs then (true, table)
    else if table.has (k+1, xs) = true then (false, table)
    else
      let result := visit (memoized hit children k) (children (k+1) xs) table
      if result.1 then result else
        (false, if (children (k+1) xs).isEmpty = true then result.2 else result.2.add (k+1, xs))

def Invariant (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (memo : Cache) : Prop :=
  ∀ key ∈ memo.entries, reference hit children key.1 key.2 = false

lemma visit_spec (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (k : Nat)
    (step : StatePool → Cache → Bool × Cache)
    (hstep : ∀ x m, Invariant hit children m →
      (step x m).1 = reference hit children k x ∧ Invariant hit children (step x m).2)
    (xs : List StatePool) (m : Cache) (hm : Invariant hit children m) :
    (visit step xs m).1 = xs.any (reference hit children k) ∧
      Invariant hit children (visit step xs m).2 := by
  induction xs generalizing m with
  | nil => exact ⟨rfl, hm⟩
  | cons x xs ih =>
    obtain ⟨hx, hnew⟩ := hstep x m hm
    cases h : (step x m).1 with
    | false => simpa [visit,h,←hx] using ih _ hnew
    | true => simpa [visit,h,←hx] using hnew

lemma memoized_spec (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool)
    (k : Nat) (xs : StatePool) (m : Cache) (hm : Invariant hit children m) :
    (memoized hit children k xs m).1 = reference hit children k xs ∧
      Invariant hit children (memoized hit children k xs m).2 := by
  induction k generalizing xs m with
  | zero => exact ⟨rfl,hm⟩
  | succ k ih =>
    cases hx : hit xs with
    | true => simpa [memoized, reference, hx] using hm
    | false =>
      by_cases seen : m.has (k+1,xs) = true
      · have no := hm _ (Cache.contains_spec _ _ _ _ seen)
        simpa [memoized,hx,seen,no] using hm
      · obtain ⟨v, valid⟩ := visit_spec hit children k (memoized hit children k) ih (children (k+1) xs) m hm
        cases h : (visit (memoized hit children k) (children (k+1) xs) m).1 with
        | true => simpa [memoized,reference,hx,seen,h,←v] using valid
        | false =>
          have no : reference hit children (k+1) xs = false := by simp [reference,hx,←v,h]
          have extended : Invariant hit children ((visit (memoized hit children k) (children (k+1) xs) m).2.add (k+1,xs)) := by
            intro key hk
            rcases Cache.add_spec _ _ _ _ _ hk with eq | old
            · exact eq.symm ▸ no
            · exact valid key old
          by_cases empty : (children (k+1) xs).isEmpty = true
          · simpa [memoized,hx,seen,h,no,empty] using valid
          · simpa [memoized,hx,seen,h,no,empty] using extended

lemma from_empty (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (k : Nat) (xs : StatePool) :
    (memoized hit children k xs .empty).1 = reference hit children k xs := by
  apply (memoized_spec hit children k xs .empty ?_).1
  intro key h
  exact (List.not_mem_nil h).elim

end PetersenMemo

namespace PetersenPacked

abbrev W := BitVec 29

def rowCover (p : Nat) : List W → W
  | [] => 0
  | w::xs => if w.getLsbD p = true then ~~~w ||| rowCover p xs else rowCover p xs

lemma rowCover_bits (p n : Nat) (hn : n < 29) (xs : List W) :
    (rowCover p xs).getLsbD n = xs.any (fun w => w.getLsbD p && !(w.getLsbD n)) := by
  induction xs with
  | nil => exact BitVec.getLsbD_zero
  | cons w xs ih =>
    cases hv : w.getLsbD p <;>
      simp only [rowCover,hv,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_or,BitVec.getLsbD_not,hn,decide_true,
        Bool.true_and,Bool.false_and,Bool.false_or,List.any_cons,ih]

def covers (xs : List W) : Bool :=
  (List.range 16).all fun p => (rowCover p xs ||| 65535) == BitVec.allOnes 29

lemma coverage_full (xs : List W) (h : ∀ p : Fin 16, ∀ n : Fin 13,
    xs.any (fun w => w.getLsbD p.val && !(w.getLsbD (n.val + 16))) = true) : covers xs = true := by
  have low : ∀ i : Fin 16, (65535 : W).getLsbD i.val = true := by decide +kernel
  have high : ∀ i : Fin 13, (65535 : W).getLsbD (i.val+16) = false := by decide +kernel
  apply List.all_eq_true.mpr
  intro p hp
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or,BitVec.getLsbD_allOnes]
  simp only [hi,decide_true]
  by_cases below : i < 16
  · have yes := low ⟨i,below⟩
    rw [show (65535 : W).getLsbD i = true from yes, Bool.or_true]
  · let n : Fin 13 := ⟨i-16,by omega⟩
    have eq : i = n.val+16 := by dsimp [n]; omega
    rw [eq,high n,Bool.or_false,rowCover_bits p _ (by omega)]
    exact h ⟨p,List.mem_range.mp hp⟩ n

end PetersenPacked

namespace PetersenMask

abbrev W := BitVec 29

def combine (d : Bool) (a b : W) : W := if d then a ||| b else a &&& b

def next (U : List W) (x : W) : Prop :=
  x ∉ U ∧ ∃ a ∈ U, ∃ b ∈ U, x = a &&& b ∨ x = a ||| b

def Valid (U s : List W) : Prop :=
  ∀ j (hj : j < s.length), next (U ++ s.take j) s[j]

inductive Live (target : W) : ℕ → Finset W → Prop where
  | stop : Live target 0 {target}
  | step {k : ℕ} {R : Finset W} (d : Bool) (a b : W)
      (diff : a ≠ b) (fresh : combine d a b ∉ insert a (insert b R))
      (tail : Live target k (insert (combine d a b) R)) :
      Live target (k + 1) (insert a (insert b R))

lemma step_tail {U : List W} {x : W} {s : List W} (leg : Valid U (x :: s)) :
    next U x ∧ Valid (U ++ [x]) s := by
  constructor
  · have h := leg 0 (by simp)
    simpa using h
  · intro j hj
    have h := leg (j+1) (by simp; omega)
    simpa [List.append_assoc] using h

lemma compile {target : W} (U s : List W) (leg : Valid U s) (hit : target ∈ U ++ s) :
    ∃ k ≤ s.length, ∃ S : Finset W, (∀ w ∈ S, w ∈ U) ∧ Live target k S := by
  induction s generalizing U with
  | nil =>
    exact ⟨0, Nat.zero_le _, {target}, by simpa using hit, .stop⟩
  | cons x s ih =>
    obtain ⟨⟨new, a, ha, b, hb, op⟩, legal⟩ := step_tail leg
    have hit' : target ∈ (U ++ [x]) ++ s := by simpa [List.append_assoc] using hit
    obtain ⟨k, small, S, sub, tail⟩ := ih (U ++ [x]) legal hit'
    by_cases used : x ∈ S
    · let R := S.erase x
      have rest : ∀ w ∈ R, w ∈ U := by
        intro w hw
        have q := Finset.mem_erase.mp hw
        have h := sub w q.2
        exact (List.mem_append.mp h).resolve_right (fun eq => q.1 (List.mem_singleton.mp eq))
      have eqS : insert x R = S := Finset.insert_erase used
      have ab : a ≠ b := by
        rintro rfl
        rcases op with h | h
        · exact new (by simpa [h] using ha)
        · exact new (by simpa [h] using ha)
      have fresh : x ∉ insert a (insert b R) := by
        intro h
        rcases Finset.mem_insert.mp h with e | h
        · exact new (by simpa only [e] using ha)
        rcases Finset.mem_insert.mp h with e | h
        · exact new (by simpa only [e] using hb)
        exact (Finset.mem_erase.mp h).1 rfl
      have src : ∀ w ∈ insert a (insert b R), w ∈ U := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        exact rest w hw
      refine ⟨k+1, by simp; omega, insert a (insert b R), src, ?_⟩
      rcases op with h | h
      · apply Live.step false a b ab
        · simpa only [combine, Bool.false_eq_true, ↓reduceIte, ← h] using fresh
        · simpa only [combine, Bool.false_eq_true, ↓reduceIte, ← h, eqS] using tail
      · apply Live.step true a b ab
        · simpa only [combine, ↓reduceIte, ← h] using fresh
        · simpa only [combine, ↓reduceIte, ← h, eqS] using tail
    · refine ⟨k,by simp; omega,S,?_,tail⟩
      intro w hw
      rcases List.mem_append.mp (sub w hw) with old | e
      · exact old
      · exact False.elim (used (List.mem_singleton.mp e ▸ hw))

lemma live_card {target : W} {k : ℕ} {S : Finset W} (h : Live target k S) :
    S.card ≤ k + 1 := by
  induction h with
  | stop => simp
  | @step k R d a b diff fresh tail ih =>
    have hz : combine d a b ∉ R := fun h => fresh (by simp [h])
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b R)
    have h2 := Finset.card_insert_le b R
    omega

def sep (w : W) (p n : ℕ) : Prop :=
  w.getLsbD p = true ∧ w.getLsbD n = false

lemma sep_combine (d : Bool) (a b : W) (p n : ℕ) (h : sep (combine d a b) p n) :
    sep a p n ∨ sep b p n := by
  cases d <;> cases ha : a.getLsbD p <;> cases hb : a.getLsbD n <;>
    cases hc : b.getLsbD p <;> cases hd : b.getLsbD n <;>
    simp_all [combine, sep, BitVec.getLsbD_and, BitVec.getLsbD_or]

lemma live_sep {target : W} {k : ℕ} {S : Finset W} (h : Live target k S)
    (p n : ℕ) (test : sep target p n) : ∃ w ∈ S, sep w p n := by
  induction h with
  | stop => exact ⟨_,by simp,test⟩
  | @step k R d a b diff fresh tail ih =>
    obtain ⟨w,hw,hval⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | rest
    · rcases sep_combine d a b p n hval with ha | hb
      · exact ⟨a,by simp,ha⟩
      · exact ⟨b,by simp,hb⟩
    · exact ⟨w,by simp [rest],hval⟩


def base : List W :=
  [0,536870911,503381504,18022921,176694291,70599750,30017540,987296,107774216,
   359669808,427868608,33489407,18813609]

def raw : List W :=
  [503381504,18022921,176694291,70599750,30017540,987296,107774216,359669808,427868608]

def witnesses : List (ℕ × ℕ) :=
  [(9,16),(0,19),(0,16),(1,19),(2,16),(5,20),(3,16),(4,19),(6,16)]

lemma raw_witnesses : ∀ i : Fin 9, let p := witnesses.getD i.val (0,0)
    sep 65535 p.1 p.2 ∧ ∀ w ∈ base, sep w p.1 p.2 → w = raw.getD i.val 0 := by
  intro i
  fin_cases i <;> simp only [base, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, sep] <;> decide +kernel

lemma live_all_raw {k : ℕ} {S : Finset W} (h : Live 65535 k S) (sub : ∀ w ∈ S, w ∈ base) :
    ∀ x ∈ raw, x ∈ S := by
  intro x hx
  obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hx
  have jb : j < 9 := by simpa [raw] using hj
  have w := raw_witnesses ⟨j,jb⟩
  obtain ⟨a,ha,ok⟩ := live_sep h _ _ w.1
  have eq := w.2 a (sub a ha) ok
  rw [List.getD_eq_getElem _ _ hj] at eq
  simpa only [eq,e] using ha

lemma live_nonconstant {x : W} {k : ℕ} {S : Finset W} (live : Live x k S)
    (target : x ≠ 0 ∧ x ≠ BitVec.allOnes 29) :
    ∀ w ∈ S, w ≠ 0 ∧ w ≠ BitVec.allOnes 29 := by
  induction live with
  | stop => simpa using target
  | @step k R d a b diff fresh tail ih =>
    have hz : combine d a b ≠ a ∧ combine d a b ≠ b := by
      refine ⟨fun e => fresh (by simp [e]),fun e => fresh (by simp [e])⟩
    have properA : a ≠ 0 ∧ a ≠ BitVec.allOnes 29 := by
      constructor <;> intro eq <;> subst a <;> cases d <;>
        simp only [combine, Bool.false_eq_true, ite_false, ite_true, BitVec.allOnes_and,
          BitVec.allOnes_or, BitVec.and_allOnes, BitVec.or_allOnes, BitVec.zero_and,
          BitVec.zero_or, BitVec.and_zero, BitVec.or_zero] at hz <;> simp at hz
    have properB : b ≠ 0 ∧ b ≠ BitVec.allOnes 29 := by
      constructor <;> intro eq <;> subst b <;> cases d <;>
        simp only [combine, Bool.false_eq_true, ite_false, ite_true, BitVec.allOnes_and,
          BitVec.allOnes_or, BitVec.and_allOnes, BitVec.or_allOnes, BitVec.zero_and,
          BitVec.zero_or, BitVec.and_zero, BitVec.or_zero] at hz <;> simp at hz
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact properA
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact properB
    exact ih w (Finset.mem_insert_of_mem hw)

lemma root_shape {k : ℕ} {S : Finset W} (h : Live 65535 k S) (sub : ∀ w ∈ S, w ∈ base) :
    ∃ extra : List W, extra ∈ [[],[33489407],[18813609],[33489407,18813609]] ∧
      S = (raw ++ extra).toFinset := by
  have need := live_all_raw h sub
  have proper := live_nonconstant h (by decide)
  have src (w : W) (hw : w ∈ S) : w ∈ raw ∨ w = 33489407 ∨ w = 18813609 := by
    have mem := sub w hw
    change w ∈ 0 :: BitVec.allOnes 29 :: raw ++ [33489407,18813609] at mem
    have ne := proper w hw
    have h1 := (List.mem_cons.mp mem).resolve_left ne.1
    have h2 := (List.mem_cons.mp h1).resolve_left ne.2
    simpa using h2
  by_cases h1 : (33489407 : W) ∈ S <;> by_cases h2 : (18813609 : W) ∈ S
  · refine ⟨[33489407,18813609], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨src w, fun p => by rcases p with hw | rfl | rfl; exact need _ hw; exact h1; exact h2⟩
  · refine ⟨[33489407], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact Or.inl r
      · exact Or.inr rfl
      · exact (h2 hw).elim
    · rintro (r | rfl)
      · exact need _ r
      · exact h1
  · refine ⟨[18813609], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact Or.inl r
      · exact (h1 hw).elim
      · exact Or.inr rfl
    · rintro (r | rfl)
      · exact need _ r
      · exact h2
  · refine ⟨[], by simp, ?_⟩
    ext w
    simp only [List.append_nil,List.mem_toFinset]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact r
      · exact (h1 hw).elim
      · exact (h2 hw).elim
    · exact need w


def separates (xs : List W) : Bool :=
  (List.range 16).all fun p => (List.range 13).all fun q =>
    xs.any fun w => w.getLsbD p && !(w.getLsbD (q + 16))

lemma separates_live {k : ℕ} {xs : List W} (h : Live 65535 k xs.toFinset) :
    separates xs = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have hp' : p < 16 := List.mem_range.mp hp
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 13 := List.mem_range.mp hq
  have bits : ∀ (p : Fin 16) (q : Fin 13), sep 65535 p.val (q.val + 16) := by
    dsimp only [sep]
    decide +kernel
  obtain ⟨w,hw,yes,no⟩ := live_sep h p (q+16) (bits ⟨p,hp'⟩ ⟨q,hq'⟩)
  exact List.any_eq_true.mpr ⟨w,List.mem_toFinset.mp hw,by simp [yes,no]⟩

def orderedInsert (z : W) : List W → List W
  | [] => [z]
  | w::ws => if z < w then z::w::ws else w::orderedInsert z ws

lemma perm_orderedInsert (z : W) (xs : List W) : (orderedInsert z xs).Perm (z::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons w ws ih =>
    unfold orderedInsert
    split
    · exact List.Perm.refl _
    · exact (ih.cons w).trans (List.Perm.swap z w ws)

def updated (xs : List W) (a b z : W) (ka kb : Bool) : List W :=
  orderedInsert z (xs.filter (fun w => (ka || w != a) && (kb || w != b)))

def can (fuel : Nat) (xs : List W) : Bool :=
  match fuel with
  | 0 => xs.contains 65535
  | fuel + 1 =>
    xs.contains 65535 ||
      ((decide (xs.length ≤ fuel + 2) && separates xs) &&
       xs.any fun a => xs.any fun b =>
        decide (a < b) && [false,true].any fun d =>
          let z := combine d a b
          (!(xs.contains z) && decide (z ≠ 0 ∧ z ≠ BitVec.allOnes 29)) && [false,true].any fun ka => [false,true].any fun kb =>
            can fuel (updated xs a b z ka kb))

lemma act_lists {R : Finset W} {xs : List W} {d : Bool} {a b : W}
    (h : xs.toFinset = insert a (insert b R)) (nd : xs.Nodup)
    (fz : combine d a b ∉ insert a (insert b R)) :
    let y := updated xs a b (combine d a b) (decide (a ∈ R)) (decide (b ∈ R))
    y.Nodup ∧ y.toFinset = insert (combine d a b) R := by
  dsimp only
  let keep := fun w : W => (decide (a ∈ R) || w != a) && (decide (b ∈ R) || w != b)
  have mem (w : W) : w ∈ xs ↔ w = a ∨ w = b ∨ w ∈ R := by
    change w ∈ xs ↔ _
    rw [← List.mem_toFinset, h]
    simp
  have mf (w : W) : w ∈ xs.filter keep ↔ w ∈ R := by
    simp only [List.mem_filter, mem, keep, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, bne_iff_ne]
    by_cases wa : w = a <;> by_cases wb : w = b <;> simp_all
  have perm := perm_orderedInsert (combine d a b) (xs.filter keep)
  change (orderedInsert (combine d a b) (xs.filter keep)).Nodup ∧
    (orderedInsert (combine d a b) (xs.filter keep)).toFinset = insert (combine d a b) R
  constructor
  · apply perm.nodup_iff.mpr
    apply List.nodup_cons.mpr
    have nf : combine d a b ∉ R := fun hR => fz (by simp [hR])
    exact ⟨fun hz => nf ((mf _).mp hz), nd.filter _⟩
  · ext w
    simp only [List.mem_toFinset,perm.mem_iff,List.mem_cons,mf,Finset.mem_insert]

def hit (xs : List W) := xs.contains 65535

def branches (budget : Nat) (xs : List W) : List (List W) :=
  if xs.length ≤ budget + 1 ∧ PetersenPacked.covers xs = true then
    xs.flatMap fun c => xs.flatMap fun e =>
      if c < e then [false,true].flatMap fun d =>
        let z := combine d c e
        if z ∉ xs ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 29 then
          [false,true].flatMap fun ka => [false,true].map fun kb => updated xs c e z ka kb
        else []
      else []
  else []

lemma branch_mem {n budget : Nat} {xs : List W} {c e : W} {d : Bool}
    (bound : xs.length ≤ budget+1) (live : Live 65535 n xs.toFinset)
    (hc : c ∈ xs) (he : e ∈ xs) (order : c < e) (new : combine d c e ∉ xs)
    (proper : combine d c e ≠ 0 ∧ combine d c e ≠ BitVec.allOnes 29) (ka kb : Bool) :
    updated xs c e (combine d c e) ka kb ∈ branches budget xs := by
  have sep := separates_live live
  have coverage : PetersenPacked.covers xs = true := by
    apply PetersenPacked.coverage_full
    intro p n
    apply List.all_eq_true.mp (List.all_eq_true.mp sep p.val (List.mem_range.mpr p.isLt)) n.val
      (List.mem_range.mpr n.isLt)
  rw [branches, if_pos ⟨bound,coverage⟩]
  apply List.mem_flatMap.mpr ⟨c,hc,?_⟩
  apply List.mem_flatMap.mpr ⟨e,he,?_⟩
  rw [if_pos order]
  apply List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩
  dsimp only
  rw [if_pos ⟨new,proper⟩]
  apply List.mem_flatMap.mpr ⟨ka,by cases ka <;> simp,?_⟩
  exact List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩

lemma memo_complete {k : ℕ} {S : Finset W} (h : Live 65535 k S) :
    ∀ fuel (xs : List W), k ≤ fuel → xs.Nodup → xs.toFinset = S → PetersenMemo.reference hit branches fuel xs = true := by
  induction h with
  | stop =>
    intro fuel xs _ _ eq
    have ht : (65535 : W) ∈ xs := List.mem_toFinset.mp (by rw [eq]; simp)
    have hit : xs.contains (65535 : W) = true := List.contains_iff_mem.mpr ht
    cases fuel with
    | zero => exact hit
    | succ _ => exact Bool.or_eq_true_iff.mpr (Or.inl hit)
  | @step k R d a b diff fresh tail ih =>
    intro fuel xs small nd eq
    cases fuel with
    | zero => omega
    | succ fuel =>
      have live : Live 65535 (k+1) xs.toFinset := eq.symm ▸ Live.step d a b diff fresh tail
      have sz := live_card live
      have el : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup nd
      have bound : xs.length ≤ fuel + 2 := by omega
      obtain ⟨c,e,ordered,state,word⟩ : ∃ c e : W, c < e ∧
          xs.toFinset = insert c (insert e R) ∧ combine d c e = combine d a b := by
        by_cases ab : a.toNat < b.toNat
        · exact ⟨a,b,ab,eq,rfl⟩
        · have ne : a.toNat ≠ b.toNat := fun h => diff (BitVec.eq_of_toNat_eq h)
          have ba : b.toNat < a.toNat := by omega
          refine ⟨b,a,ba,?_,?_⟩
          · simpa only [Finset.insert_comm b a] using eq
          · cases d <;> simp only [combine, ↓reduceIte, BitVec.or_comm b a, BitVec.and_comm b a]
      have hc : c ∈ xs := List.mem_toFinset.mp (by rw [state]; simp)
      have he : e ∈ xs := List.mem_toFinset.mp (by rw [state]; simp)
      have fz : combine d c e ∉ insert c (insert e R) := by
        rw [←state,eq,word]
        exact fresh
      have hz : combine d c e ∉ xs := by simpa [←state] using fz
      have tail' : Live 65535 k (insert (combine d c e) R) := by rw [word]; exact tail
      have proper := live_nonconstant tail' (by decide) (combine d c e) (by simp)
      have close := act_lists state nd fz
      have accepted := ih fuel _ (by omega) close.1 (by simpa only [word] using close.2)
      apply Bool.or_eq_true_iff.mpr (Or.inr ?_)
      apply List.any_eq_true.mpr
      refine ⟨_,branch_mem (by omega) live hc he ordered hz proper _ _,accepted⟩

theorem memo_lower_bound
    (checks : ∀ extra ∈ ([[],[33489407],[18813609],[33489407,18813609]] : List (List W)),
      (PetersenMemo.memoized hit branches 13 (raw ++ extra) .empty).1 = false)
    (program : List W) (len : program.length ≤ 13) (legal : Valid base program) :
    (65535 : W) ∉ base ++ program := by
  intro occurs
  obtain ⟨k,hk,S,sub,live⟩ := compile base program legal occurs
  obtain ⟨extra,he,eq⟩ := root_shape live sub
  have nodup : (raw ++ extra).Nodup := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide +kernel
  have yes := memo_complete live 13 (raw ++ extra) (by omega) nodup eq.symm
  have no := checks extra he
  rw [PetersenMemo.from_empty] at no
  exact Bool.noConfusion (yes.symm.trans no)

end PetersenMask

namespace PetersenMask
namespace Reconstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 9 → Bool
abbrev Wire := X → Bool

def edge (x : X) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def rows : List Nat := [6,12,24,66,132,160,264,288,320,3,13,17,33,133,265,321,42,50,104,116,138,200,208,276,402,69,201,261,385]
def point (i : Fin 29) (j : Fin 9) := (rows.getD i.val 0).testBit j.val

def below (x y : X) : Prop := x 0 = y 0 ∧ ∀ j, x j = true → y j = true

def Good (w : W) (f : Wire) : Prop :=
  (∀ i : Fin 29, f (point i) = w.getLsbD i.val) ∧
  ∀ x y, below x y → f x = true → f y = true

lemma full {f : Wire} (h : Good 65535 f) (x : X) : f x = edge x := by
  have extrema : ∀ y : X,
      (edge y = true → ∃ i : Fin 29, (65535 : W).getLsbD i.val = true ∧ below (point i) y) ∧
      (edge y = false → ∃ i : Fin 29, (65535 : W).getLsbD i.val = false ∧ below y (point i)) := by
    dsimp only [below]
    decide +kernel
  cases e : edge x with
  | true =>
    obtain ⟨i,bit,le⟩ := (extrema x).1 e
    exact h.2 _ _ le ((h.1 i).trans bit)
  | false =>
    obtain ⟨i,bit,le⟩ := (extrema x).2 e
    cases ex : f x with
    | false => rfl
    | true => exact Bool.noConfusion ((h.2 _ _ le ex).symm.trans ((h.1 i).trans bit))

def readFn (bank : List Wire) (x : X) := bank.map fun f => f x

lemma location (bank : List Wire) (f : Wire) (hf : f ∈ bank) :
    ∃ j : Nat, ∀ x : X, (readFn bank x).getD j false = f x := by
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hf
  refine ⟨j,?_⟩
  intro x
  rw [List.getD_eq_getElem _ _ (by simpa [readFn] using hj)]
  simp only [readFn,List.getElem_map,eq]

def combFn (d : Bool) (f g : Wire) (x : X) := if d = true then f x || g x else f x && g x

lemma good_combine {a b : W} {f g : Wire} (ha : Good a f) (hb : Good b g) (d : Bool) :
    Good (combine d a b) (combFn d f g) := by
  constructor
  · intro i
    cases d <;> simp [combine,combFn,ha.1 i,hb.1 i,BitVec.getLsbD_or,BitVec.getLsbD_and]
  · intro x y hxy h
    cases d with
    | false => exact Bool.and_eq_true_iff.mpr ⟨ha.2 x y hxy (Bool.and_eq_true_iff.mp h).1,
          hb.2 x y hxy (Bool.and_eq_true_iff.mp h).2⟩
    | true =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ha.2 x y hxy h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (hb.2 x y hxy h))

def Represents (bank : List Wire) (S : Finset W) : Prop := ∀ w ∈ S, ∃ f ∈ bank, Good w f

lemma build {k : Nat} {S : Finset W} (live : Live 65535 k S) (bank : List Wire) (rep : Represents bank S) :
    ∃ (gs : List Gate) (out : Nat) (f : Wire), gs.length = k ∧ FanInTwo ⟨gs,out⟩ ∧
      Good 65535 f ∧ ∀ x : X, (Circuit.mk gs out).eval (readFn bank x) = f x := by
  induction live generalizing bank with
  | stop =>
    obtain ⟨f,mem,good⟩ := rep 65535 (by simp)
    obtain ⟨j,get⟩ := location bank f mem
    exact ⟨[],j,f,rfl,fun g h => (List.not_mem_nil h).elim,good,get⟩
  | @step k R d a b diff fresh tail ih =>
    obtain ⟨f,hf,gf⟩ := rep a (by simp)
    obtain ⟨g,hg,gg⟩ := rep b (by simp)
    obtain ⟨i,ri⟩ := location bank f hf
    obtain ⟨j,rj⟩ := location bank g hg
    let op : GateOp := if d = true then .or else .and
    let gate : Gate := ⟨op,[i,j]⟩
    let z := combFn d f g
    have rep' : Represents (bank ++ [z]) (insert (combine d a b) R) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact ⟨z,List.mem_append_right _ (by simp),good_combine gf gg d⟩
      obtain ⟨v,hv,ok⟩ := rep w (by simp [hr])
      exact ⟨v,List.mem_append_left _ hv,ok⟩
    obtain ⟨gs,out,fn,sz,fan,good,semantics⟩ := ih (bank ++ [z]) rep'
    refine ⟨gate::gs,out,fn,by simp [sz],?_,good,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hr
      · cases d <;> simp [gate,op]
      · exact fan t hr
    · intro x
      have nextVal : op.eval ([i,j].map (fun t => (readFn bank x).getD t false)) = z x := by
        simp only [List.map_cons,List.map_nil,ri x,rj x]
        cases d <;> simp [op,z,combFn,GateOp.eval]
      change (Circuit.mk gs out).eval (readFn bank x ++ [op.eval ([i,j].map (fun t => (readFn bank x).getD t false))]) = fn x
      rw [nextVal]
      simpa only [readFn,List.map_append,List.map_cons,List.map_nil] using semantics x

def prim : List Wire := List.ofFn fun j : Fin 9 => fun x : X => x j
def minus : Wire := fun x => !(x 0)

lemma initial : Represents (prim ++ [minus]) (raw ++ [33489407]).toFinset := by
  have coords : ∀ i : Fin 9, ∀ j : Fin 29, point j i = (raw.getD i.val 0).getLsbD j.val := by decide +kernel
  have negbits : ∀ j : Fin 29, minus (point j) = (33489407 : W).getLsbD j.val := by decide +kernel
  intro w hw
  rcases List.mem_append.mp (List.mem_toFinset.mp hw) with r | r
  · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp r
    have bound : j < 9 := by simpa [raw] using hj
    let idx : Fin 9 := ⟨j,bound⟩
    have mem : (fun x : X => x idx) ∈ prim := List.mem_ofFn.mpr ⟨idx,rfl⟩
    refine ⟨_,List.mem_append_left _ mem,?_,fun x y h => h.2 idx⟩
    intro i
    have c := coords idx i
    change point i idx = (raw.getD j 0).getLsbD i.val at c
    simpa only [List.getD_eq_getElem _ _ hj,eq] using c
  · have eq := List.mem_singleton.mp r
    subst w
    refine ⟨minus,List.mem_append_right _ (by simp),negbits,?_⟩
    intro x y h
    simp only [minus,h.1,imp_self]

lemma no_or
    (bound : ∀ D : Circuit, FanInTwo D → (∀ x : X, D.eval (List.ofFn x) = edge x) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    {k : Nat} {S : Finset W} (small : k ≤ 13) (live : Live 65535 k S)
    (source : S ⊆ (raw ++ [33489407]).toFinset) : False := by
  obtain ⟨gs,out,f,len,fan,good,sem⟩ := build live (prim ++ [minus]) (fun w hw => initial w (source hw))
  let negGate : Gate := ⟨.not,[0]⟩
  let D : Circuit := ⟨negGate::gs,out⟩
  have ok : FanInTwo D := by
    intro g hg
    change g ∈ negGate::gs at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl),by decide⟩
    · exact fan g hg
  have output (x : X) : D.eval (List.ofFn x) = edge x := by
    have read0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    change (Circuit.mk gs out).eval (List.ofFn x ++ [!(List.ofFn x).getD 0 false]) = edge x
    rw [read0]
    have init : readFn (prim ++ [minus]) x = List.ofFn x ++ [!x 0] := by
      simp [readFn,prim,minus,List.map_ofFn,Function.comp_def]
    rw [←init,sem x]
    exact full good x
  have lower := bound D ok output
  let charged (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  change 14 ≤ (negGate::gs).countP charged at lower
  have zero : charged negGate = false := rfl
  have maxC := List.countP_le_length (p := charged) (l := gs)
  simp [List.countP_cons,zero] at lower
  omega

end Reconstruction

namespace Reconstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dummy : Wire := fun x => x 0 || x 1
def useful : Wire := fun x => x 1 || x 5
def primOr := prim ++ [dummy,useful]

lemma initial_or : Represents primOr (raw ++ [18813609]).toFinset := by
  have coords : ∀ i : Fin 9, ∀ j : Fin 29, point j i = (raw.getD i.val 0).getLsbD j.val := by decide +kernel
  have extra : ∀ j : Fin 29, useful (point j) = (18813609 : W).getLsbD j.val := by decide +kernel
  intro w hw
  rcases List.mem_append.mp (List.mem_toFinset.mp hw) with r | r
  · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp r
    have bound : j < 9 := by simpa [raw] using hj
    let idx : Fin 9 := ⟨j,bound⟩
    have mem : (fun x : X => x idx) ∈ prim := List.mem_ofFn.mpr ⟨idx,rfl⟩
    refine ⟨_,List.mem_append_left _ mem,?_,fun x y h => h.2 idx⟩
    intro i
    have c := coords idx i
    change point i idx = (raw.getD j 0).getLsbD i.val at c
    simpa only [List.getD_eq_getElem _ _ hj,eq] using c
  · have eq := List.mem_singleton.mp r
    subst w
    refine ⟨useful,List.mem_append_right _ (by simp),extra,?_⟩
    intro x y h yes
    rcases Bool.or_eq_true_iff.mp yes with a | b
    · exact Bool.or_eq_true_iff.mpr (Or.inl (h.2 1 a))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (h.2 5 b))

def runGate (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma preserve_wire (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl runGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [runGate]; omega)]
    exact List.getD_append _ _ _ _ hi

def DummyBound := ∀ D : Circuit, FanInTwo D →
    (∀ x : X, (D.wires (List.ofFn x)).getD 9 false = dummy x) →
    (∀ x : X, D.eval (List.ofFn x) = edge x) → 16 ≤ D.size

lemma no_not (strong : DummyBound) {k : Nat} (small : k ≤ 13)
    (live : Live 65535 k (raw ++ [18813609]).toFinset) : False := by
  obtain ⟨gs,out,f,len,fan,good,sem⟩ := build live primOr initial_or
  let first : Gate := ⟨.or,[0,1]⟩
  let second : Gate := ⟨.or,[1,5]⟩
  let D : Circuit := ⟨first::second::gs,out⟩
  have data : ∀ x : X, let ws := runGate (runGate (List.ofFn x) first) second
      ws = readFn primOr x ∧ ws.getD 9 false = dummy x ∧ 9 < ws.length := by decide +kernel
  have ok : FanInTwo D := by
    intro g hg
    change g ∈ first::second::gs at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    exact fan g hg
  have firstWire (x : X) : (D.wires (List.ofFn x)).getD 9 false = dummy x := by
    change (gs.foldl runGate (runGate (runGate (List.ofFn x) first) second)).getD 9 false = dummy x
    exact (preserve_wire _ _ _ (data x).2.2).trans (data x).2.1
  have computes (x : X) : D.eval (List.ofFn x) = edge x := by
    change (Circuit.mk gs out).eval (runGate (runGate (List.ofFn x) first) second) = edge x
    rw [(data x).1,sem x]
    exact full good x
  have lower := strong D ok firstWire computes
  change 16 ≤ gs.length + 1 + 1 at lower
  omega

end Reconstruction

lemma dummy_bound : Reconstruction.DummyBound := by
  intro D fan wire good
  refine DummyCertificate.final D fan wire ?_
  funext x
  exact good x

namespace Reconstruction

abbrev IsConst (w : W) := w = 0 ∨ w = BitVec.allOnes 29

def countConst (p : W → W) (S : Finset W) := (S.filter fun w => IsConst (p w)).card

lemma count_insert (p : W → W) (w : W) (S : Finset W) :
    countConst p (insert w S) ≤ countConst p S + (if IsConst (p w) then 1 else 0) := by
  by_cases hc : IsConst (p w)
  · simp only [countConst,Finset.filter_insert,if_pos hc]
    exact Finset.card_insert_le _ _
  · simp [countConst,Finset.filter_insert,hc]

lemma count_fresh (p : W → W) (w : W) (S : Finset W) (fresh : w ∉ S) :
    countConst p (insert w S) = countConst p S + (if IsConst (p w) then 1 else 0) := by
  by_cases hc : IsConst (p w)
  · have no : w ∉ (S.filter fun u => IsConst (p u)) := fun h => fresh (Finset.mem_filter.mp h).1
    simp [countConst,Finset.filter_insert,hc,Finset.card_insert_of_notMem no]
  · simp [countConst,Finset.filter_insert,hc]

lemma const_rules (d : Bool) (a b : W) :
    (IsConst a ∨ IsConst b → combine d a b = a ∨ combine d a b = b) ∧
    (IsConst a → IsConst b → IsConst (combine d a b)) := by
  constructor
  · rintro ((rfl|rfl)|(rfl|rfl)) <;> cases d <;>
      simp only [combine,Bool.false_eq_true,ite_false,ite_true,BitVec.zero_or,BitVec.or_zero,
        BitVec.zero_and,BitVec.and_zero,BitVec.allOnes_and,BitVec.and_allOnes,BitVec.allOnes_or,BitVec.or_allOnes] <;> simp
  · rintro (rfl|rfl) (rfl|rfl) <;> cases d <;> decide +kernel

def faceRows : List Nat := [6,12,66,132,160,264,288,320,320,320,320,320,320,320,320,320,
    42,100,104,138,200,260,386,386,386,386,386,386,386]

def facePoint (i : Fin 29) (j : Fin 9) := (faceRows.getD i.val 0).testBit j.val

def face (f : Wire) : W := (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 29 => f (facePoint i)))).cast (by simp)

lemma face_bit (f : Wire) (i : Fin 29) : (face f).getLsbD i.val = f (facePoint i) := by
  simp only [face,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  fin_cases i <;> rfl

lemma face_combine (d : Bool) (f g : Wire) : face (combFn d f g) = combine d (face f) (face g) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 29 := ⟨i,hi⟩
  cases d <;> simp only [combine,combFn,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,
    BitVec.getLsbD_or,show (face f).getLsbD i = f (facePoint j) from face_bit f j,
    show (face g).getLsbD i = g (facePoint j) from face_bit g j] <;> apply face_bit _ j

lemma face_target {f : Wire} (hg : Good 65535 f) : face f = 65535 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 29 := ⟨i,hi⟩
  have chart : ∀ j : Fin 29, edge (facePoint j) = (65535 : W).getLsbD j.val := by decide +kernel
  exact (face_bit f j).trans ((full hg _).trans (chart j))

lemma pvalid_append {base log : List W} {v : W} (h : Valid base log) (hfresh : v ∉ base ++ log)
    (hv : ∃ a ∈ base ++ log, ∃ b ∈ base ++ log, v = a &&& b ∨ v = a ||| b) :
    Valid base (log ++ [v]) := by
  intro j hj
  by_cases hj' : j < log.length
  · simpa only [List.getElem_append_left hj', List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
  · have eq : j = log.length := by simp at hj; omega
    subst j
    simpa [next] using And.intro hfresh hv

lemma project_live {k : Nat} {S : Finset W} (live : Live 65535 k S) (base log : List W)
    (legal : Valid base log) (lab : W → Wire)
    (avail : ∀ w ∈ S, Good w (lab w) ∧ face (lab w) ∈ base ++ log) :
    ∃ out : List W, Valid base out ∧ 65535 ∈ base ++ out ∧
      out.length + countConst (fun w => face (lab w)) S ≤ log.length + k := by
  induction live generalizing log lab with
  | stop =>
    have a := avail 65535 (by simp)
    have tgt := face_target a.1
    have nonconst : ¬IsConst (65535 : W) := by decide +kernel
    refine ⟨log,legal,by simpa only [tgt] using a.2,?_⟩
    simp [countConst]
    change face (lab (65535 : W)) ≠ 0 ∧ face (lab (65535 : W)) ≠ BitVec.allOnes 29
    rw [tgt]
    decide +kernel
  | @step k R d a b diff fresh tail ih =>
    let z := combine d a b
    let p := fun w : W => face (lab w)
    let fz := combFn d (lab a) (lab b)
    let lab' (w : W) := if w = z then fz else lab w
    let p' := fun w : W => face (lab' w)
    have az := avail a (by simp)
    have bz := avail b (by simp)
    have fzGood : Good z fz := good_combine az.1 bz.1 d
    have znot : z ∉ R := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have pZ : p' z = combine d (p a) (p b) := by simpa [p',lab',fz,p] using face_combine d (lab a) (lab b)
    have agree (w : W) (hw : w ∈ R) : lab' w = lab w := by
      have ne : w ≠ z := fun e => znot (e ▸ hw)
      simp [lab',ne]
    have eqCount : countConst p' R = countConst p R := by
      unfold countConst
      congr 1
      ext w
      by_cases hw : w ∈ R <;> simp [hw,p',p,agree w]
    have ab := count_insert p a (insert b R)
    have br := count_insert p b R
    have zc := count_fresh p' z R znot
    rw [eqCount,pZ] at zc
    have lift_avail (more : List W) (old : base ++ log ⊆ base ++ more)
        (inZ : p' z ∈ base ++ more) :
        ∀ w ∈ insert z R, Good w (lab' w) ∧ face (lab' w) ∈ base ++ more := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact ⟨by simpa [lab'] using fzGood,inZ⟩
      have oldw := avail w (by simp [hr])
      exact ⟨by simpa only [agree w hr] using oldw.1,by simpa only [agree w hr] using old oldw.2⟩
    by_cases mem : p' z ∈ base ++ log
    · obtain ⟨out,ok,goal,size⟩ := ih log legal lab' (lift_avail log (fun _ h => h) mem)
      refine ⟨out,ok,goal,?_⟩
      change out.length + countConst p (insert a (insert b R)) ≤ log.length + (k+1)
      change out.length + countConst p' (insert z R) ≤ log.length + k at size
      by_cases ca : IsConst (p a) <;> by_cases cb : IsConst (p b)
      · have cz := (const_rules d (p a) (p b)).2 ca cb
        simp only [if_pos ca,if_pos cb,if_pos cz] at ab br zc
        omega
      · simp only [if_pos ca,if_neg cb] at ab br
        split at zc <;> omega
      · simp only [if_neg ca,if_pos cb] at ab br
        split at zc <;> omega
      · simp only [if_neg ca,if_neg cb] at ab br
        split at zc <;> omega
    · have clear : ¬IsConst (p a) ∧ ¬IsConst (p b) := by
        have h (c : IsConst (p a) ∨ IsConst (p b)) : False := by
          rcases (const_rules d (p a) (p b)).1 c with e | e
          · exact mem (by simpa only [pZ,e] using az.2)
          · exact mem (by simpa only [pZ,e] using bz.2)
        exact ⟨fun e => h (Or.inl e),fun e => h (Or.inr e)⟩
      have validGate : ∃ x ∈ base ++ log, ∃ y ∈ base ++ log, p' z = x &&& y ∨ p' z = x ||| y := by
        refine ⟨p a,az.2,p b,bz.2,?_⟩
        cases d <;> simp [pZ,combine]
      let more := log ++ [p' z]
      have extl : base ++ log ⊆ base ++ more := by
        dsimp [more]; rw [←List.append_assoc]; exact fun _ h => List.mem_append_left _ h
      have inz : p' z ∈ base ++ more := by simp [more]
      obtain ⟨out,ok,goal,size⟩ := ih more (pvalid_append legal mem validGate) lab' (lift_avail more extl inz)
      refine ⟨out,ok,goal,?_⟩
      change out.length + countConst p (insert a (insert b R)) ≤ log.length + (k+1)
      change out.length + countConst p' (insert z R) ≤ (log ++ [p' z]).length + k at size
      simp only [List.length_append,List.length_singleton,if_neg clear.1,if_neg clear.2] at size ab br
      split at zc <;> omega

end Reconstruction
namespace Reconstruction

def unsigned : List W := [533266437,2228235,1900578,458832,1507204,534249496,534839264]
def faceBase : List W := 0 :: BitVec.allOnes 29 :: unsigned ++ [533659733]
def faceWitnesses : List (Nat × Nat) := [(0,17),(0,16),(1,17),(4,19),(2,16),(3,17),(5,16)]

def origin (w : W) (x : X) : Bool :=
  if w = 503381504 then x 0 else if w = 18022921 then x 1 else if w = 176694291 then x 2 else
  if w = 70599750 then x 3 else if w = 30017540 then x 4 else if w = 987296 then x 5 else
  if w = 107774216 then x 6 else if w = 359669808 then x 7 else if w = 427868608 then x 8 else
  if w = 33489407 then !(x 0) else x 1 || x 5

lemma original_avail (w : W) (hw : w ∈ (raw ++ [33489407,18813609]).toFinset) :
    Good w (origin w) ∧ face (origin w) ∈ faceBase ++ [] := by
  have bits : ∀ u ∈ raw ++ [33489407,18813609], ∀ i : Fin 29, origin u (point i) = u.getLsbD i.val := by
    simp only [raw,List.cons_append,List.nil_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    decide +kernel
  have faceMem : ∀ u ∈ raw ++ [33489407,18813609], face (origin u) ∈ faceBase ++ [] := by
    simp only [raw,List.cons_append,List.nil_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have old := List.mem_toFinset.mp hw
  refine ⟨⟨bits w old,?_⟩,faceMem w old⟩
  intro x y h
  have primMono (i : Fin 9) : x i = true → y i = true := h.2 i
  have negMono : !(x 0) = true → !(y 0) = true := by rw [h.1]; exact id
  have orMono : (x 1 || x 5) = true → (y 1 || y 5) = true := by
    intro yes
    rcases Bool.or_eq_true_iff.mp yes with v | v
    · exact Bool.or_eq_true_iff.mpr (Or.inl (primMono 1 v))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (primMono 5 v))
  unfold origin
  repeat' first | split | assumption | exact primMono _

lemma chart_face_raw : ∀ i : Fin 7, let p := faceWitnesses.getD i.val (0,0)
    sep 65535 p.1 p.2 ∧ ∀ w ∈ faceBase, sep w p.1 p.2 → w = unsigned.getD i.val 0 := by
  intro i
  fin_cases i <;> simp only [faceBase,unsigned,List.cons_append,List.nil_append,List.forall_mem_cons,
    List.not_mem_nil,false_implies,implies_true,and_true,sep] <;> decide +kernel

lemma face_root {k : Nat} {S : Finset W} (live : Live 65535 k S)
    (sub : ∀ w ∈ S, w ∈ faceBase) : S = unsigned.toFinset ∨ S = (unsigned ++ [533659733]).toFinset := by
  have need (x : W) (mem : x ∈ unsigned) : x ∈ S := by
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp mem
    have jb : j < 7 := by simpa [unsigned] using hj
    have w := chart_face_raw ⟨j,jb⟩
    obtain ⟨a,ha,ok⟩ := live_sep live _ _ w.1
    have eq := w.2 a (sub a ha) ok
    rw [List.getD_eq_getElem _ _ hj] at eq
    simpa only [eq,e] using ha
  have proper := live_nonconstant live (by decide)
  have src (w : W) (hw : w ∈ S) : w ∈ unsigned ∨ w = 533659733 := by
    have m := sub w hw
    change w ∈ 0 :: BitVec.allOnes 29 :: unsigned ++ [533659733] at m
    have h1 := (List.mem_cons.mp m).resolve_left (proper w hw).1
    have h2 := (List.mem_cons.mp h1).resolve_left (proper w hw).2
    simpa using h2
  by_cases ex : (533659733 : W) ∈ S
  · right
    ext w
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton]
    refine ⟨src w,?_⟩
    rintro (r | rfl)
    · exact need _ r
    · exact ex
  · left
    ext w
    simp only [List.mem_toFinset]
    refine ⟨?_,need w⟩
    intro hw
    rcases src w hw with r | rfl
    · exact r
    · exact (ex hw).elim

lemma small_face {k : Nat} (small : k ≤ 13) (live : Live 65535 k (raw ++ [33489407,18813609]).toFinset)
    (check0 : (PetersenMemo.memoized hit branches 10 unsigned .empty).1 = false)
    (check1 : (PetersenMemo.memoized hit branches 10 (unsigned ++ [533659733]) .empty).1 = false) : False := by
  obtain ⟨p,valid,target,budget⟩ := project_live live faceBase [] (by intro j h; simp at h) origin original_avail
  have count : countConst (fun w => face (origin w)) (raw ++ [33489407,18813609]).toFinset = 3 := by decide +kernel
  rw [count] at budget
  obtain ⟨m,hm,S,sub,h⟩ := compile faceBase p valid target
  have tiny : m ≤ 10 := by simp only [List.length_nil,Nat.zero_add] at budget; omega
  rcases face_root h sub with eq | eq
  · have yes := memo_complete h 10 unsigned tiny (by decide +kernel) eq.symm
    rw [PetersenMemo.from_empty] at check0
    exact Bool.noConfusion (yes.symm.trans check0)
  · have yes := memo_complete h 10 (unsigned ++ [533659733]) tiny (by decide +kernel) eq.symm
    rw [PetersenMemo.from_empty] at check1
    exact Bool.noConfusion (yes.symm.trans check1)

end Reconstruction

theorem memo_lower_faces
    (bound : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Reconstruction.X, D.eval (List.ofFn x) = Reconstruction.edge x) →
      14 ≤ D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (check0 : (PetersenMemo.memoized hit branches 10 Reconstruction.unsigned .empty).1 = false)
    (check1 : (PetersenMemo.memoized hit branches 10 (Reconstruction.unsigned ++ [533659733]) .empty).1 = false)
    (program : List W) (len : program.length ≤ 13) (legal : Valid base program) :
    (65535 : W) ∉ base ++ program := by
  intro occurs
  obtain ⟨k,hk,S,sub,live⟩ := compile base program legal occurs
  obtain ⟨extra,he,eq⟩ := root_shape live sub
  have small : k ≤ 13 := hk.trans len
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Reconstruction.no_or bound small live (by rw [eq]; decide +kernel)
  · exact Reconstruction.no_or bound small live (by rw [eq])
  · rw [eq] at live
    exact Reconstruction.no_not dummy_bound small live
  · rw [eq] at live
    exact Reconstruction.small_face small live check0 check1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma closed_face0 : (PetersenMemo.memoized hit branches 10 Reconstruction.unsigned .empty).1 = false := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma closed_face1 : (PetersenMemo.memoized hit branches 10 (Reconstruction.unsigned ++ [533659733]) .empty).1 = false := by
  decide +kernel


end PetersenMask

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem from_children
    (binaryBound : ∀ (D : Circuit), FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (finite : let seeds : List (BitVec 29) := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18813609]
      ∀ program : List (BitVec 29), program.length ≤ 13 →
      (∀ j (hj : j < program.length), program[j] ∉ seeds ++ program.take j ∧
        ∃ a ∈ seeds ++ program.take j, ∃ b ∈ seeds ++ program.take j,
          program[j] = a &&& b ∨ program[j] = a ||| b) →
      (65535 : BitVec 29) ∉ seeds ++ program) :
∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         (1 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro pins len _ allowed hasOne C fan budget
  let F := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let input := fun (ls : List ℕ) (x : Fin 9 → Bool) =>
    let z := List.ofFn x ++ [!x 0]
    z ++ [GateOp.or.eval (ls.map fun i => z.getD i false)]
  by_contra missed
  have correct (x : Fin 9 → Bool) : C.eval (input pins x) = F x :=
    Classical.not_not.mp (fun wrong => missed ⟨x,wrong⟩)
  let first : Gate := ⟨.not,[0]⟩
  let second : Gate := ⟨.or,pins⟩
  let D : Circuit := ⟨first :: second :: C.gates,C.output⟩
  have dfan : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl),by decide⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),len.le⟩
    exact fan g hg
  have dcorrect (x : Fin 9 → Bool) : D.eval (List.ofFn x) = F x := by
    have read0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    change C.eval (((List.ofFn x) ++ [!(List.ofFn x).getD 0 false]) ++
      [GateOp.or.eval (pins.map fun j => ((List.ofFn x) ++ [!(List.ofFn x).getD 0 false]).getD j false)]) = F x
    rw [read0]
    exact correct x
  let charged (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  have n := binaryBound D dfan dcorrect
  change 14 ≤ (first :: second :: C.gates).countP charged at n
  have hn : charged first = false := rfl
  have ho : charged second = true := rfl
  simp [List.countP_cons,hn,ho] at n
  change C.gates.length ≤ 13 at budget
  have le := List.countP_le_length (p := charged) (l := C.gates)
  have allBinary : C.gates.countP charged = C.gates.length := by omega
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨basis,arity⟩ := fan g hg
    refine ⟨?_,arity⟩
    rcases basis with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have keep := List.countP_eq_length.mp allBinary g hg
      change g.op = .not at h
      simp [charged,h] at keep
  have shapes : pins ∈ ([[1,1],[1,5],[5,1]] : List (List ℕ)) := by
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
    · simp at len
    · simp at len
    · have ha := allowed a (by simp)
      have hb := allowed b (by simp)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · decide
      · decide
      · decide
      · exact False.elim ((by decide : (1 : ℕ) ∉ [5,5]) hasOne)
    · simp at len
  let bit (i : Fin 29) (v : BitVec 29) := v.getLsbD i.val
  have evalAnd : ∀ a, GateOp.and.eval a = a.all id := fun _ => rfl
  have evalOr : ∀ a, GateOp.or.eval a = a.any id := fun _ => rfl
  let gateWord (w : List (BitVec 29)) (g : Gate) : BitVec 29 :=
    let args := g.inputs.map fun j => w.getD j 0
    let a : BitVec 29 := args.getD 0 (BitVec.allOnes 29) &&& args.getD 1 (BitVec.allOnes 29)
    let b : BitVec 29 := args.getD 0 0 ||| args.getD 1 0
    GateOp.rec (motive := fun _ => BitVec 29) a b b (fun _ => b) b g.op

  let wordStep (w : List (BitVec 29)) (g : Gate) := w ++ [gateWord w g]

  let boolStep (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

  have zero_bit (i : Fin 29) : (0 : BitVec 29).getLsbD i.val = false :=
    BitVec.getLsbD_zero

  have read_bit (w : List (BitVec 29)) (i : Fin 29) (j : Nat) :
      (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
    simpa only [bit, zero_bit] using (List.getD_map w 0 (n := j) (bit i))

  have step_bits (w : List (BitVec 29)) (i : Fin 29) (g : Gate)
      (hg : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
      (wordStep w g).map (bit i) = boolStep (w.map (bit i)) g := by
    obtain ⟨op, args⟩ := g
    change op = .and ∨ op = .or at hg
    change args.length ≤ 2 at hlen
    have shapes : args = [] ∨ (∃ a, args = [a]) ∨ ∃ a b, args = [a, b] := by
      cases args with
      | nil => exact Or.inl rfl
      | cons a tail =>
        cases tail with
        | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
        | cons b tail =>
          cases tail with
          | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
          | cons _ _ => simp at hlen
    rcases hg with rfl | rfl <;>
      rcases shapes with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
      simp only [wordStep, boolStep, gateWord, evalAnd, evalOr, List.map_append, List.map_cons,
        List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, read_bit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, bit,
        BitVec.getLsbD_and, BitVec.getLsbD_or, zero_bit, BitVec.getLsbD_allOnes,
        i.isLt, decide_true, Bool.and_true, Bool.or_false]

  have run_bits (gs : List Gate) (w : List (BitVec 29)) (i : Fin 29)
      (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      obtain ⟨hop, hlen⟩ := hm g List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons, ih _ (fun k hk => hm k (List.mem_cons_of_mem g hk)),
        step_bits w i g hop hlen]

  let Binary (pool : List (BitVec 29)) (v : BitVec 29) : Prop :=
    ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

  let Valid (base values : List (BitVec 29)) : Prop :=
    ∀ j (hj : j < values.length), values[j] ∉ base ++ values.take j ∧
      Binary (base ++ values.take j) values[j]

  have valid_append {base program : List (BitVec 29)} {v : BitVec 29} (h : Valid base program)
      (hfresh : v ∉ base ++ program) (hv : Binary (base ++ program) v) :
      Valid base (program ++ [v]) := by
    intro j hj
    by_cases hj' : j < program.length
    · simpa only [List.getElem_append_left hj',
        List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
    · have heq : j = program.length := by simp at hj; omega
      subst j
      simpa using And.intro hfresh hv

  have read_mem {α : Type} {xs pool : List α} (h : xs ⊆ pool) {d : α} (hd : d ∈ pool)
      (i : Nat) : xs.getD i d ∈ pool := by
    rw [List.getD_eq_getElem?_getD]
    cases hv : xs[i]? with
    | none => exact hd
    | some v => exact h (List.mem_of_getElem? hv)

  have gate_binary {w pool : List (BitVec 29)} (g : Gate) (hw : w ⊆ pool)
      (hz : 0 ∈ pool) (ht : BitVec.allOnes 29 ∈ pool) : Binary pool (gateWord w g) := by
    have hargs : (g.inputs.map fun j => w.getD j 0) ⊆ pool := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
      exact read_mem hw hz j
    dsimp only [gateWord]
    cases h : g.op
    · exact ⟨_, read_mem hargs ht 0, _, read_mem hargs ht 1, Or.inl rfl⟩
    all_goals exact ⟨_, read_mem hargs hz 0, _, read_mem hargs hz 1, Or.inr rfl⟩

  have record_step {base program w : List (BitVec 29)} (g : Gate) (hz : 0 ∈ base)
      (ht : BitVec.allOnes 29 ∈ base) (h : Valid base program) (hw : w ⊆ base ++ program) :
      ∃ next : List (BitVec 29), next.length ≤ program.length + 1 ∧ Valid base next ∧
        wordStep w g ⊆ base ++ next := by
    let v := gateWord w g
    by_cases hmem : v ∈ base ++ program
    · refine ⟨program, by omega, h, ?_⟩
      exact List.append_subset.mpr ⟨hw, by simpa [v] using hmem⟩
    · have hv := gate_binary g hw (List.mem_append_left _ hz) (List.mem_append_left _ ht)
      refine ⟨program ++ [v], by simp, valid_append h hmem hv, ?_⟩
      rw [← List.append_assoc]
      exact List.append_subset.mpr ⟨fun _ ha => List.mem_append_left _ (hw ha),
        fun _ ha => List.mem_append_right _ ha⟩

  have record_run (gs : List Gate) (base program w : List (BitVec 29)) (hz : 0 ∈ base)
      (ht : BitVec.allOnes 29 ∈ base) (h : Valid base program) (hw : w ⊆ base ++ program) :
      ∃ final : List (BitVec 29), final.length ≤ program.length + gs.length ∧ Valid base final ∧
        gs.foldl wordStep w ⊆ base ++ final := by
    induction gs generalizing program w with
    | nil => exact ⟨program, by simp, h, hw⟩
    | cons g gs ih =>
      obtain ⟨next, hlen, hnext, hwires⟩ := record_step g hz ht h hw
      obtain ⟨final, hsize, hfinal, hout⟩ := ih next (wordStep w g) hnext hwires
      exact ⟨final, by simp; omega, hfinal, hout⟩

  let seeds : List (BitVec 29) := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18813609]
  let given := fun (ls : List ℕ) =>
    ([503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407] : List (BitVec 29)) ++ [if 5 ∈ ls then 18813609 else 18022921]
  let rows := ([6, 12, 24, 66, 132, 160, 264, 288, 320, 3, 13, 17, 33, 133, 265, 321, 42, 50, 104, 116, 138, 200, 208, 276, 402, 69, 201, 261, 385] : List ℕ)
  let point := fun (i : Fin 29) (k : Fin 9) => (rows.getD i.val 0).testBit k.val
  have rowData : ∀ ls ∈ ([[1,1],[1,5],[5,1]] : List (List ℕ)), ∀ i : Fin 29,
      (given ls).map (bit i) = input ls (point i) ∧ bit i 65535 = F (point i) := by
    intro ls hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide +kernel
  have hinit : given pins ⊆ seeds ++ [] := by
    rcases (show pins = [1,1] ∨ pins = [1,5] ∨ pins = [5,1] by simpa using shapes) with rfl | rfl | rfl
    all_goals decide
  obtain ⟨program, hlen, hvalid, hw⟩ := record_run C.gates seeds [] (given pins)
    (by decide) (by decide) (by intro j hj; simp at hj) hinit
  let wires := C.gates.foldl wordStep (given pins)
  have houtput : wires.getD C.output 0 = 65535 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 29 := ⟨j,hj⟩
    obtain ⟨hin,hout⟩ := rowData pins shapes i
    change bit i (wires.getD C.output 0) = bit i 65535
    rw [← read_bit, hout, ← correct (point i)]
    change ((C.gates.foldl wordStep (given pins)).map (bit i)).getD C.output false =
      (C.gates.foldl boolStep (input pins (point i))).getD C.output false
    rw [run_bits C.gates (given pins) i hm, hin]
  apply finite program (by simp only [List.length_nil, Nat.zero_add] at hlen; omega) hvalid
  change (65535 : BitVec 29) ∈ seeds ++ program
  rw [← houtput]
  exact read_mem hw (List.mem_append_left _ (by decide)) C.output

end PEqualNP.Outside.L_meta_3921

open PEqualNP.Outside.L_meta_3921

theorem PEqualNP.Outside.L_meta_3921 :
∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         (1 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  apply from_children fourteen
  exact PetersenMask.memo_lower_faces fourteen PetersenMask.closed_face0 PetersenMask.closed_face1
