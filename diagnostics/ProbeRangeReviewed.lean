import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23616.SampleBank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample : Fin 21 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def needed : Finset (Fin 21) := [0, 2, 3, 5, 6, 7, 8, 10, 12, 18].toFinset
def bank : Fin 13 → Circuit := ![⟨[⟨.or, [1,3]⟩, ⟨.or, [3,5]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,8]⟩, ⟨.not, [7]⟩, ⟨.or, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [9,12]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [5,7]⟩, ⟨.and, [9,6]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.or, [0,2]⟩, ⟨.not, [2]⟩, ⟨.or, [3,5]⟩, ⟨.or, [3,7]⟩, ⟨.and, [6,9]⟩, ⟨.not, [8]⟩, ⟨.and, [1,11]⟩, ⟨.or, [12,10]⟩], 13⟩,
⟨[⟨.or, [0,1]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,7]⟩, ⟨.or, [8,5]⟩, ⟨.not, [10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.and, [6,4]⟩, ⟨.or, [0,9]⟩, ⟨.not, [7]⟩, ⟨.and, [10,11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.or, [0,1]⟩, ⟨.and, [1,5]⟩, ⟨.or, [7,2]⟩, ⟨.and, [8,3]⟩, ⟨.or, [8,3]⟩, ⟨.not, [10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [2,3]⟩, ⟨.or, [1,6]⟩, ⟨.or, [2,3]⟩, ⟨.not, [8]⟩, ⟨.and, [0,9]⟩, ⟨.not, [5]⟩, ⟨.and, [7,11]⟩, ⟨.or, [10,12]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [2,6]⟩, ⟨.and, [7,9]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [2,6]⟩, ⟨.or, [5,7]⟩, ⟨.and, [9,8]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩], 12⟩,
⟨[⟨.not, [0]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,7]⟩, ⟨.and, [5,6]⟩, ⟨.or, [8,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [5,1]⟩, ⟨.or, [6,3]⟩, ⟨.or, [1,7]⟩, ⟨.or, [2,4]⟩, ⟨.or, [7,9]⟩, ⟨.and, [8,9]⟩, ⟨.not, [10]⟩, ⟨.or, [12,11]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.or, [5,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.and, [7,6]⟩, ⟨.or, [8,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [5,1]⟩, ⟨.or, [6,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [2,8]⟩, ⟨.or, [7,3]⟩, ⟨.or, [10,4]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩]
def missing : Fin 21 → Fin 13 := ![0, 0, 1, 2, 0, 3, 4, 5, 6, 0, 7, 0, 8, 0, 0, 0, 0, 0, 9, 0, 0]
def extra : Fin 21 → Fin 13 := ![10, 10, 10, 10, 11, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 10, 10, 10, 11]
def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢


def Check (C : Circuit) (k : Fin 21) : Prop :=
  let p := sample k
  C.eval (List.ofFn fun a : Fin 6 => decide (a=p.1 ∨ a=p.2)) =
    (34227 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

instance (C : Circuit) (k : Fin 21) : Decidable (Check C k) := by unfold Check; infer_instance

set_option maxRecDepth 10000 in
theorem fan (c) : FanInTwo (bank c) := by
  have pass : ∀ k, (bank k).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp (pass c) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using acceptedOpSound g h.1,h.2⟩

theorem price : ∀ c, (bank c).size ≤ 8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem whenMissing : ∀ i k : Fin 21, i ∈ needed → k ≠ i → Check (bank (missing i)) k := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem withExtra : ∀ i k : Fin 21, k ∈ needed ∨ k=i → Check (bank (extra i)) k := by decide +kernel

theorem everyEleven (S : Finset (Fin 21)) (small : S.card ≤ 11) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i ∈ S, Check C i := by
  classical
  by_cases absent : ∃ k, k∈needed ∧ k∉S
  · obtain ⟨k,hk,hno⟩ := absent
    exact ⟨bank (missing k),fan _,price _,fun i hi => whenMissing k i hk (by rintro rfl; exact hno hi)⟩
  have contained : needed ⊆ S := by
    intro x hx
    by_contra no
    exact absent ⟨x,hx,no⟩
  have ten : needed.card=10 := by decide +kernel
  have bound : (S \ needed).card ≤ 1 := by rw [Finset.card_sdiff_of_subset contained,ten]; omega
  by_cases rem : (S \ needed).Nonempty
  · obtain ⟨x,hx⟩ := rem
    refine ⟨bank (extra x),fan _,price _,?_⟩
    intro i hi
    apply withExtra
    by_cases h : i∈needed
    · exact Or.inl h
    · exact Or.inr (Finset.card_le_one.mp bound i (Finset.mem_sdiff.mpr ⟨hi,h⟩) x hx)
  · refine ⟨bank (extra 0),fan _,price _,?_⟩
    intro i hi
    apply withExtra
    left
    by_contra no
    exact rem ⟨i,Finset.mem_sdiff.mpr ⟨hi,no⟩⟩

end PEqualNP.Outside.L_meta_23616.SampleBank


namespace PEqualNP.Outside.L_meta_23616.Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents


abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
  · dsimp only
    split
    · rename_i hh
      exact Nat.ble_eq.mpr (probe_run h _ _ _ _ hh.1 hh.2)
    · rfl
def probeRoots : List (List Nat × Nat) := []
def urootHint (ws : List Nat) : Nat := (probeRoots.lookup (isort ws)).getD 0

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

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
        (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ucheck_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || !ucheck m y cap zs (urootHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

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
    have hd := via_sound hp hcap
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



def pairCode (p : Fin 6 × Fin 6) : Nat := 2 ^ p.1.val ||| 2 ^ p.2.val
def reference (x : Fin 6 → Bool) : Bool :=
  (x 0 && !(x 2 || x 3)) || (x 1 && !(x 3 || x 5)) || (x 2 && x 3)
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (34227 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 6 × Fin 6) := [(0, 0), (0, 2), (0, 3), (0, 5), (1, 1), (1, 2), (1, 3), (1, 5), (2, 2), (2, 3), (4, 4), (5, 5)]
def points := samplePairs.map pairCode

def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) =
  (34227 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 4095

def Y_ : ℕ := 569

def XS_ : List ℕ := [15, 240, 802, 580, 1024, 2184]

def PD_ : List (ℕ × ℕ) := [(1, 805), (2, 695), (3, 126), (4, 26), (5, 40), (6, 49), (7, 29), (8, 11), (10, 1), (11, 1)]

def PM_ : List (ℕ × ℕ) := [(1, 569), (2, 569), (6, 569), (7, 569), (8, 569), (10, 569), (11, 569)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,15,628,802,3225] BT.lf) [3,15,756,802,3097] BT.lf) [3,125,580] (BT.nd (BT.nd BT.lf [3,127,514,580] BT.lf) [3,127,582] BT.lf)) [3,253,708] (BT.nd (BT.nd (BT.nd BT.lf [3,255,514,708] BT.lf) [3,255,580,642] BT.lf) [3,255,710] (BT.nd BT.lf [3,580,3970] BT.lf))) [4,2,127,580] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2,255,708] BT.lf) [4,13,68,756,2184] BT.lf) [4,13,112,580] (BT.nd (BT.nd BT.lf [4,13,240,708] BT.lf) [4,13,580,3983] BT.lf)) [4,13,2296,2764] (BT.nd (BT.nd (BT.nd BT.lf [4,15,112,514,580] BT.lf) [4,15,112,580,802,3225] BT.lf) [4,15,112,582] (BT.nd BT.lf [4,15,114,580] BT.lf)))) [4,15,240,514,708] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,240,580,642] BT.lf) [4,15,240,580,802,3097] BT.lf) [4,15,240,708,802,3097] (BT.nd (BT.nd BT.lf [4,15,240,710] BT.lf) [4,15,242,708] BT.lf)) [4,15,514,580,3983] (BT.nd (BT.nd (BT.nd BT.lf [4,15,514,2296,2764] BT.lf) [4,15,544,870,3208] BT.lf) [4,15,544,1894,2184] (BT.nd BT.lf [4,15,580,802,1041,2296] BT.lf))) [4,15,580,2296,2698] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,580,3981] BT.lf) [4,15,582,3983] BT.lf) [4,15,628,802,870] (BT.nd (BT.nd BT.lf [4,15,756,802,998] BT.lf) [4,15,756,802,1041,2184] BT.lf)) [4,15,756,802,1911,3225] (BT.nd (BT.nd (BT.nd BT.lf [4,15,802,870,3467] BT.lf) [4,15,802,1041,2184,2812] BT.lf) [4,15,802,1041,2296,2764] (BT.nd BT.lf [4,15,2296,2766] BT.lf))))) [4,15,2298,2764] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,68,240,589,2184] BT.lf) [4,77,756,2184] BT.lf) [4,112,580,4082] (BT.nd (BT.nd BT.lf [4,127,580,591,802] BT.lf) [4,127,580,628,802] BT.lf)) [4,127,580,756,802] (BT.nd (BT.nd (BT.nd BT.lf [4,128,253,580] BT.lf) [4,128,255,514,580] BT.lf) [4,128,255,582] (BT.nd BT.lf [4,130,255,580] BT.lf))) [4,141,240,580] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,143,240,582] BT.lf) [4,143,242,580] BT.lf) [4,207,756,802] (BT.nd (BT.nd BT.lf [4,240,319,580,802] BT.lf) [4,240,580,802,3776] BT.lf)) [4,240,580,1343,1826] (BT.nd (BT.nd (BT.nd BT.lf [4,240,580,1826,2752] BT.lf) [4,240,580,3954] BT.lf) [4,240,708,4082] (BT.nd BT.lf [4,240,802,1343,1604] BT.lf)))) [4,240,802,1604,2752] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,240,802,3780] BT.lf) [4,240,810,3788] BT.lf) [4,240,1826,2756] (BT.nd (BT.nd BT.lf [4,240,1834,2764] BT.lf) [4,246,591,2184] BT.lf)) [4,255,590,2184] (BT.nd (BT.nd (BT.nd BT.lf [4,255,591,708,802] BT.lf) [4,255,708,719,802] BT.lf) [4,255,708,756,802] (BT.nd BT.lf [4,255,740,802] BT.lf))) [4,255,756,802,2767] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,580,3983,4082] BT.lf) [4,591,628,802] BT.lf) [4,591,802,3467] (BT.nd BT.lf [4,719,756,802] BT.lf)) [4,752,815,870,2184] (BT.nd (BT.nd (BT.nd BT.lf [4,756,815,870,2191] BT.lf) [4,756,2184,4018] BT.lf) [4,2296,2764,4082] (BT.nd BT.lf [5,2,15,112,580] BT.lf)))))) [5,2,15,240,708] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2,15,580,3983] BT.lf) [5,2,15,2296,2764] BT.lf) [5,2,128,255,580] (BT.nd (BT.nd BT.lf [5,2,143,240,580] BT.lf) [5,6,240,591,2184] BT.lf)) [5,8,240,802,3788] (BT.nd (BT.nd (BT.nd BT.lf [5,8,240,1826,2764] BT.lf) [5,10,255,580,2184] BT.lf) [5,11,240,802,2764] (BT.nd BT.lf [5,12,240,580,802,3788] BT.lf))) [5,12,240,580,1826,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12,240,802,1604,2764] BT.lf) [5,13,68,240,580,2184] BT.lf) [5,13,128,240,580] (BT.nd (BT.nd BT.lf [5,13,240,512,580,2184] BT.lf) [5,13,240,580,802,2764] BT.lf)) [5,13,240,580,1911] (BT.nd (BT.nd (BT.nd BT.lf [5,13,240,580,2184] BT.lf) [5,13,240,580,2189] BT.lf) [5,13,240,580,2191] (BT.nd BT.lf [5,13,240,580,2764] BT.lf)))) [5,13,240,580,2764,3293] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,13,240,580,3208] BT.lf) [5,13,240,2184,2764] BT.lf) [5,13,240,2184,3515] (BT.nd (BT.nd BT.lf [5,13,253,580,2184] BT.lf) [5,13,580,756,802,2184] BT.lf)) [5,13,580,756,2184,3293] (BT.nd (BT.nd (BT.nd BT.lf [5,13,580,2184,2296] BT.lf) [5,13,580,2184,3855] BT.lf) [5,15,48,580,802] (BT.nd BT.lf [5,15,68,756,802,2184] BT.lf))) [5,15,68,756,2184,3293] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,112,512,580,802] BT.lf) [5,15,112,580,580,802] BT.lf) [5,15,112,580,591,802] (BT.nd BT.lf [5,15,112,580,628,802] BT.lf)) [5,15,112,580,756,802] (BT.nd (BT.nd (BT.nd BT.lf [5,15,112,580,802] BT.lf) [5,15,112,580,802,870] BT.lf) [5,15,112,580,802,1604] (BT.nd BT.lf [5,15,112,580,802,2764] BT.lf))))) [5,15,112,580,802,3515] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,112,580,870] BT.lf) [5,15,112,580,882] BT.lf) [5,15,112,580,1010] (BT.nd (BT.nd BT.lf [5,15,112,580,1826] BT.lf) [5,15,112,580,3293] BT.lf)) [5,15,112,802,1604] (BT.nd (BT.nd (BT.nd BT.lf [5,15,112,802,3515] BT.lf) [5,15,119,580,802] BT.lf) [5,15,127,580,802] (BT.nd BT.lf [5,15,128,240,514,580] BT.lf))) [5,15,128,240,582] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,128,242,580] BT.lf) [5,15,128,756,802,870] BT.lf) [5,15,130,240,580] (BT.nd (BT.nd BT.lf [5,15,192,580,756,802] BT.lf) [5,15,192,756,802] BT.lf)) [5,15,240,307,580,802] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,512,582,2184] BT.lf) [5,15,240,512,708,802] BT.lf) [5,15,240,512,870,2764] (BT.nd BT.lf [5,15,240,514,580,1911] BT.lf)))) [5,15,240,514,580,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,514,580,2191] BT.lf) [5,15,240,514,580,2698] BT.lf) [5,15,240,514,580,2764] (BT.nd (BT.nd BT.lf [5,15,240,514,580,2767] BT.lf) [5,15,240,514,580,3208] BT.lf)) [5,15,240,514,2184,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,514,2184,3515] BT.lf) [5,15,240,516,802,2764] BT.lf) [5,15,240,544,870,2184] (BT.nd BT.lf [5,15,240,546,580,2184] BT.lf))) [5,15,240,580,628,802] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,640,802] BT.lf) [5,15,240,580,704,802] BT.lf) [5,15,240,580,708,802] (BT.nd BT.lf [5,15,240,580,708,930] BT.lf)) [5,15,240,580,708,1826] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,708,3293] BT.lf) [5,15,240,580,716,802] BT.lf) [5,15,240,580,719,802] (BT.nd BT.lf [5,15,240,580,754,2184] BT.lf))))))) [5,15,240,580,770,2764] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,802,998] BT.lf) [5,15,240,580,802,1041,2184] BT.lf) [5,15,240,580,802,1328] (BT.nd (BT.nd BT.lf [5,15,240,580,802,1331] BT.lf) [5,15,240,580,802,1343] BT.lf)) [5,15,240,580,802,1399] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,802,1732] BT.lf) [5,15,240,580,802,1911,3225] BT.lf) [5,15,240,580,802,2696] (BT.nd BT.lf [5,15,240,580,802,2698] BT.lf))) [5,15,240,580,802,2700] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,802,2703] BT.lf) [5,15,240,580,802,2752] BT.lf) [5,15,240,580,802,2756] (BT.nd (BT.nd BT.lf [5,15,240,580,802,2760] BT.lf) [5,15,240,580,802,2764] BT.lf)) [5,15,240,580,802,2766] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,802,2767] BT.lf) [5,15,240,580,802,3387] BT.lf) [5,15,240,580,802,3467] (BT.nd BT.lf [5,15,240,580,802,3720] BT.lf)))) [5,15,240,580,802,3788] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,802,3791] BT.lf) [5,15,240,580,870,930] BT.lf) [5,15,240,580,870,2696] (BT.nd (BT.nd BT.lf [5,15,240,580,882] BT.lf) [5,15,240,580,930,2764] BT.lf)) [5,15,240,580,1010,2696] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,1331,1826] BT.lf) [5,15,240,580,1331,3293] BT.lf) [5,15,240,580,1826,2696] (BT.nd BT.lf [5,15,240,580,1826,2764] BT.lf))) [5,15,240,580,1826,2767] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,1906] BT.lf) [5,15,240,580,2184,2698] BT.lf) [5,15,240,580,2184,3581] (BT.nd (BT.nd BT.lf [5,15,240,580,2189] BT.lf) [5,15,240,580,2269,2764] BT.lf)) [5,15,240,580,2696,3293] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,580,2764,3293] BT.lf) [5,15,240,580,2764,3325] BT.lf) [5,15,240,580,2767,3293] (BT.nd BT.lf [5,15,240,580,3213] BT.lf))))) [5,15,240,580,3293,3788] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,582,802,2764] BT.lf) [5,15,240,582,1911] BT.lf) [5,15,240,582,2184] (BT.nd (BT.nd BT.lf [5,15,240,582,2186] BT.lf) [5,15,240,582,2191] BT.lf)) [5,15,240,582,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,582,2766] BT.lf) [5,15,240,582,3208] BT.lf) [5,15,240,590,2184] (BT.nd BT.lf [5,15,240,591,708,802] BT.lf))) [5,15,240,612,802,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,708,708,802] BT.lf) [5,15,240,708,719,802] BT.lf) [5,15,240,708,756,802] (BT.nd (BT.nd BT.lf [5,15,240,708,802] BT.lf) [5,15,240,708,802,998] BT.lf)) [5,15,240,708,802,1604] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,708,802,1732] BT.lf) [5,15,240,708,802,2764] BT.lf) [5,15,240,708,802,3387] (BT.nd BT.lf [5,15,240,708,802,3515] BT.lf)))) [5,15,240,708,870] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,708,930] BT.lf) [5,15,240,708,998] BT.lf) [5,15,240,708,1010] (BT.nd (BT.nd BT.lf [5,15,240,708,1826] BT.lf) [5,15,240,708,3293] BT.lf)) [5,15,240,740,802] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,756,802,1331] BT.lf) [5,15,240,756,802,2764] BT.lf) [5,15,240,756,802,2767] (BT.nd BT.lf [5,15,240,756,802,3788] BT.lf))) [5,15,240,756,1010,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,756,1826,2764] BT.lf) [5,15,240,756,2764,3293] BT.lf) [5,15,240,802,1041,2184,2764] (BT.nd BT.lf [5,15,240,802,1331,1604] BT.lf)) [5,15,240,802,1331,3515] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,802,1604,2696] BT.lf) [5,15,240,802,1604,2764] BT.lf) [5,15,240,802,1604,2767] (BT.nd BT.lf [5,15,240,802,1732] BT.lf)))))) [5,15,240,802,1780,2764] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,802,2491,2764] BT.lf) [5,15,240,802,2696,3515] BT.lf) [5,15,240,802,2756] (BT.nd (BT.nd BT.lf [5,15,240,802,2764,3339] BT.lf) [5,15,240,802,2764,3515] BT.lf)) [5,15,240,802,2764,3579] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,802,2767,3515] BT.lf) [5,15,240,802,3387] BT.lf) [5,15,240,802,3515,3788] (BT.nd BT.lf [5,15,240,806,2764] BT.lf))) [5,15,240,810,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,870,1331] BT.lf) [5,15,240,870,2764] BT.lf) [5,15,240,870,2764,2986] (BT.nd (BT.nd BT.lf [5,15,240,870,2767] BT.lf) [5,15,240,870,3788] BT.lf)) [5,15,240,1014,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,1604,2764,3293] BT.lf) [5,15,240,1826,2764,3515] BT.lf) [5,15,240,1894,2764] (BT.nd BT.lf [5,15,240,2184,2766] BT.lf)))) [5,15,240,2184,3513] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,2186,2764] BT.lf) [5,15,240,2764,3225] BT.lf) [5,15,240,2764,3293,3515] (BT.nd (BT.nd BT.lf [5,15,242,580,1911] BT.lf) [5,15,242,580,2184] BT.lf)) [5,15,242,580,2186] (BT.nd (BT.nd (BT.nd BT.lf [5,15,242,580,2191] BT.lf) [5,15,242,580,2764] BT.lf) [5,15,242,580,3208] (BT.nd BT.lf [5,15,242,582,2184] BT.lf))) [5,15,242,2184,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,242,2184,3515] BT.lf) [5,15,244,580,802,2764] BT.lf) [5,15,244,802,2764] (BT.nd BT.lf [5,15,246,580,2184] BT.lf)) [5,15,248,580,802,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,248,802,2764] BT.lf) [5,15,250,580,2184] BT.lf) [5,15,252,580,802,2764] (BT.nd BT.lf [5,15,253,580,2184] BT.lf))))) [5,15,255,514,580,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,255,580,708,802] BT.lf) [5,15,255,580,802,2767] BT.lf) [5,15,255,582,2184] (BT.nd (BT.nd BT.lf [5,15,255,708,802] BT.lf) [5,15,255,756,802,2764] BT.lf)) [5,15,255,870,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,512,580,802,3983] BT.lf) [5,15,512,802,2296,2764] BT.lf) [5,15,514,580,754,2184] (BT.nd BT.lf [5,15,514,580,2184,2296] BT.lf))) [5,15,514,580,2184,3855] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,516,580,802,3983] BT.lf) [5,15,516,802,2764,3855] BT.lf) [5,15,544,580,802,3208] (BT.nd (BT.nd BT.lf [5,15,544,580,1826,2184] BT.lf) [5,15,544,756,870,2184] BT.lf)) [5,15,544,802,1604,2184] (BT.nd (BT.nd (BT.nd BT.lf [5,15,544,870,1024,2184] BT.lf) [5,15,580,580,802,3983] BT.lf) [5,15,580,591,802,3983] (BT.nd BT.lf [5,15,580,628,802] BT.lf)))) [5,15,580,708,802,3855] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,752,802,2696] BT.lf) [5,15,580,756,802,930] BT.lf) [5,15,580,756,802,2248] (BT.nd (BT.nd BT.lf [5,15,580,756,802,2696] BT.lf) [5,15,580,756,802,3983] BT.lf)) [5,15,580,770,2764,3855] (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,770,3208] BT.lf) [5,15,580,770,3983] BT.lf) [5,15,580,802,870,3983] (BT.nd BT.lf [5,15,580,802,1264,3788] BT.lf))) [5,15,580,802,1331,2296] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,802,1331,3855] BT.lf) [5,15,580,802,1604,3983] BT.lf) [5,15,580,802,1799,2764] (BT.nd BT.lf [5,15,580,802,2296,2696] BT.lf)) [5,15,580,802,2296,2764] (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,802,2296,2767] BT.lf) [5,15,580,802,2296,3054] BT.lf) [5,15,580,802,2296,3788] (BT.nd BT.lf [5,15,580,802,2303,2767] BT.lf)))))))) [5,15,580,802,2696,2808] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,802,2696,3855] BT.lf) [5,15,580,802,2700,3855] BT.lf) [5,15,580,802,2764,3855] (BT.nd (BT.nd BT.lf [5,15,580,802,2764,3983] BT.lf) [5,15,580,802,2767,3855] BT.lf)) [5,15,580,802,2812,2986] (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,802,2812,3054] BT.lf) [5,15,580,802,3240] BT.lf) [5,15,580,802,3320,3788] (BT.nd BT.lf [5,15,580,802,3467] BT.lf))) [5,15,580,802,3515,3983] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,802,3788,3855] BT.lf) [5,15,580,802,3976] BT.lf) [5,15,580,802,3983] (BT.nd (BT.nd BT.lf [5,15,580,802,4047] BT.lf) [5,15,580,870,2296,2986] BT.lf)) [5,15,580,870,3983] (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,1010,3983] BT.lf) [5,15,580,1794,2184] BT.lf) [5,15,580,1826,2216] (BT.nd BT.lf [5,15,580,1826,2296,2764] BT.lf)))) [5,15,580,1826,2764,3855] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,1826,3983] BT.lf) [5,15,580,2184,2298] BT.lf) [5,15,580,2184,2301] (BT.nd (BT.nd BT.lf [5,15,580,2184,3853] BT.lf) [5,15,580,2186,2296] BT.lf)) [5,15,580,2296,2764,2986] (BT.nd (BT.nd (BT.nd BT.lf [5,15,580,2296,2764,3293] BT.lf) [5,15,580,2764,3293,3855] BT.lf) [5,15,580,3208,3325] (BT.nd BT.lf [5,15,580,3293,3983] BT.lf))) [5,15,582,756,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,582,2184,2296] BT.lf) [5,15,582,2184,3855] BT.lf) [5,15,591,802,2296,2764] (BT.nd (BT.nd BT.lf [5,15,612,802,3208] BT.lf) [5,15,612,1826,2184] BT.lf)) [5,15,708,756,802] (BT.nd (BT.nd (BT.nd BT.lf [5,15,708,802,3855] BT.lf) [5,15,752,802,870,2184] BT.lf) [5,15,756,802,870,1911] (BT.nd BT.lf [5,15,756,802,870,2184] BT.lf))))) [5,15,756,802,870,2191] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,756,802,870,2764] BT.lf) [5,15,756,802,870,2986] BT.lf) [5,15,756,802,870,3054] (BT.nd (BT.nd BT.lf [5,15,756,802,870,3208] BT.lf) [5,15,756,802,1014,2764] BT.lf)) [5,15,756,802,1331] (BT.nd (BT.nd (BT.nd BT.lf [5,15,756,802,1894,2184] BT.lf) [5,15,756,802,2184,3054] BT.lf) [5,15,756,802,2184,3225] (BT.nd BT.lf [5,15,756,802,2184,4027] BT.lf))) [5,15,756,802,2248] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,756,802,2296,2764] BT.lf) [5,15,756,802,2764] BT.lf) [5,15,756,802,2764,2986] (BT.nd (BT.nd BT.lf [5,15,756,802,2764,3855] BT.lf) [5,15,756,802,2767] BT.lf)) [5,15,756,802,3054] (BT.nd (BT.nd (BT.nd BT.lf [5,15,756,802,3788] BT.lf) [5,15,756,815,870,2184] BT.lf) [5,15,756,870,1826,2184] (BT.nd BT.lf [5,15,756,870,2184,2986] BT.lf)))) [5,15,756,870,2184,3293] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,756,870,2986] BT.lf) [5,15,756,1826,1894,2184] BT.lf) [5,15,756,1826,2764] (BT.nd (BT.nd BT.lf [5,15,756,2764,3293] BT.lf) [5,15,770,1604,2184] BT.lf)) [5,15,802,870,2184,2812] (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,870,2184,3339] BT.lf) [5,15,802,870,2764,2812] BT.lf) [5,15,802,1264,1604,2764] (BT.nd BT.lf [5,15,802,1264,1604,3788] BT.lf))) [5,15,802,1331,2296] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,1331,2296,2764] BT.lf) [5,15,802,1604,2216] BT.lf) [5,15,802,1604,2296,2764] (BT.nd BT.lf [5,15,802,1604,2764,3855] BT.lf)) [5,15,802,1604,3983] (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,1636,2184] BT.lf) [5,15,802,1780,1894,2184] BT.lf) [5,15,802,1780,3788] (BT.nd BT.lf [5,15,802,1799,2764] BT.lf)))))) [5,15,802,2184,2812,3054] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,2296,2764] BT.lf) [5,15,802,2296,2764,2764] BT.lf) [5,15,802,2296,2764,2767] (BT.nd (BT.nd BT.lf [5,15,802,2296,2764,2812] BT.lf) [5,15,802,2296,2764,3054] BT.lf)) [5,15,802,2296,2764,3515] (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,2296,2764,3788] BT.lf) [5,15,802,2296,3788] BT.lf) [5,15,802,2764,2812,2986] (BT.nd BT.lf [5,15,802,2764,3339] BT.lf))) [5,15,802,2764,3515,3855] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,802,3320,3788] BT.lf) [5,15,802,3515,3983] BT.lf) [5,15,870,2296,2764] (BT.nd (BT.nd BT.lf [5,15,870,2764,3855] BT.lf) [5,15,1010,2296,2764] BT.lf)) [5,15,1604,2184,3325] (BT.nd (BT.nd (BT.nd BT.lf [5,15,1826,2296,2764] BT.lf) [5,15,2296,2764,2986] BT.lf) [5,15,2296,2764,3054] (BT.nd BT.lf [5,15,2296,2764,3066] BT.lf)))) [5,15,2296,2764,3293] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,47,240,580,802,2764] BT.lf) [5,77,240,580,2184] BT.lf) [5,79,240,580,802,2764] (BT.nd (BT.nd BT.lf [5,79,580,756,802,2184] BT.lf) [5,79,756,802,2184] BT.lf)) [5,112,127,580,802] (BT.nd (BT.nd (BT.nd BT.lf [5,112,580,591,802] BT.lf) [5,112,580,802,815] BT.lf) [5,112,580,802,4080] (BT.nd BT.lf [5,127,240,580,802] BT.lf))) [5,128,240,580,4082] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,128,255,580,591,802] BT.lf) [5,128,255,580,756,802] BT.lf) [5,128,591,756,802] (BT.nd BT.lf [5,143,240,580,591,802] BT.lf)) [5,143,240,580,708,802] (BT.nd (BT.nd (BT.nd BT.lf [5,143,240,580,802] BT.lf) [5,143,240,580,870] BT.lf) [5,143,240,580,930] (BT.nd BT.lf [5,143,240,580,1010] BT.lf))))) [5,143,240,580,1826] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,143,240,580,3293] BT.lf) [5,143,240,708,802] BT.lf) [5,143,240,802,1604] (BT.nd (BT.nd BT.lf [5,143,240,802,3515] BT.lf) [5,143,580,756,802] BT.lf)) [5,143,580,802,3855] (BT.nd (BT.nd (BT.nd BT.lf [5,160,255,580,802] BT.lf) [5,175,240,580,802] BT.lf) [5,207,240,580,802] (BT.nd BT.lf [5,221,240,580,2184] BT.lf))) [5,240,253,580,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,255,514,580,2184] BT.lf) [5,240,255,580,708,802] BT.lf) [5,240,255,580,802,2767] (BT.nd (BT.nd BT.lf [5,240,255,580,1010,2764] BT.lf) [5,240,255,582,2184] BT.lf)) [5,240,255,708,802] (BT.nd (BT.nd (BT.nd BT.lf [5,240,255,756,802,2764] BT.lf) [5,240,255,870,2764] BT.lf) [5,240,303,580,802,2184] (BT.nd BT.lf [5,240,303,802,2184,3515] BT.lf)))) [5,240,512,580,2184,4082] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,512,815,870,2184] BT.lf) [5,240,514,580,591,2191] BT.lf) [5,240,514,580,2184,4080] (BT.nd (BT.nd BT.lf [5,240,527,580,802,2191] BT.lf) [5,240,527,580,802,2696] BT.lf)) [5,240,580,589,802,2184] (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,589,2184,3293] BT.lf) [5,240,580,591,802,1904] BT.lf) [5,240,580,591,802,2191] (BT.nd BT.lf [5,240,580,591,802,2696] BT.lf))) [5,240,580,591,802,3215] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,591,1826,2191] BT.lf) [5,240,580,591,2191,3293] BT.lf) [5,240,580,708,802,4080] (BT.nd BT.lf [5,240,580,719,802] BT.lf)) [5,240,580,767,802,2191] (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,802,815,2696] BT.lf) [5,240,580,802,895] BT.lf) [5,240,580,802,943] (BT.nd BT.lf [5,240,580,802,1024,1343] BT.lf))))))) [5,240,580,802,1024,2752] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,802,1331,4080] BT.lf) [5,240,580,802,2191,3504] BT.lf) [5,240,580,802,2696,4080] (BT.nd (BT.nd BT.lf [5,240,580,802,2752,4080] BT.lf) [5,240,580,802,2756,4080] BT.lf)) [5,240,580,802,2760,4080] (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,802,2764,4080] BT.lf) [5,240,580,802,2764,4082] BT.lf) [5,240,580,802,2767,4080] (BT.nd BT.lf [5,240,580,802,3200] BT.lf))) [5,240,580,802,3788,4080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,802,3952] BT.lf) [5,240,580,810,3208] BT.lf) [5,240,580,815,870,2191] (BT.nd (BT.nd BT.lf [5,240,580,815,930] BT.lf) [5,240,580,1039,1826,2764] BT.lf)) [5,240,580,1826,1919] (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,1826,2176] BT.lf) [5,240,580,1826,2764,4080] BT.lf) [5,240,580,1834,2184] (BT.nd BT.lf [5,240,580,1911,4082] BT.lf)))) [5,240,580,2176,4082] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,2184,3874] BT.lf) [5,240,580,2184,4018] BT.lf) [5,240,580,2184,4082] (BT.nd (BT.nd BT.lf [5,240,580,2191,4082] BT.lf) [5,240,580,2764,3293,4080] BT.lf)) [5,240,580,2764,4082] (BT.nd (BT.nd (BT.nd BT.lf [5,240,580,3208,4082] BT.lf) [5,240,582,2184,4080] BT.lf) [5,240,588,802,3208] (BT.nd BT.lf [5,240,588,1826,2184] BT.lf))) [5,240,591,708,802] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,591,802,870,2191] BT.lf) [5,240,591,802,1604,2191] BT.lf) [5,240,591,802,2191,3515] (BT.nd BT.lf [5,240,591,870,2191] BT.lf)) [5,240,591,2764,2986] (BT.nd (BT.nd (BT.nd BT.lf [5,240,708,719,802] BT.lf) [5,240,708,802,815] BT.lf) [5,240,708,802,4080] (BT.nd BT.lf [5,240,756,802,2764,4080] BT.lf))))) [5,240,802,1024,2756] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,802,1032,2764] BT.lf) [5,240,802,1039,1604,2764] BT.lf) [5,240,802,1039,1604,3788] (BT.nd (BT.nd BT.lf [5,240,802,1604,1919] BT.lf) [5,240,802,1604,2176] BT.lf)) [5,240,802,1604,2764,4080] (BT.nd (BT.nd (BT.nd BT.lf [5,240,802,1612,2184] BT.lf) [5,240,802,2756,4080] BT.lf) [5,240,802,2764,3515,4080] (BT.nd BT.lf [5,240,802,2764,4084] BT.lf))) [5,240,810,1024,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,810,1604,2184] BT.lf) [5,240,815,2764,2986] BT.lf) [5,240,870,2764,4080] (BT.nd (BT.nd BT.lf [5,240,2184,2764,4082] BT.lf) [5,240,2184,3515,4082] BT.lf)) [5,242,580,2184,4080] (BT.nd (BT.nd (BT.nd BT.lf [5,244,580,591,802,2184] BT.lf) [5,255,514,580,591,2184] BT.lf) [5,255,580,591,802,2191] (BT.nd BT.lf [5,255,580,591,802,2767] BT.lf)))) [5,255,580,756,802,2191] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,255,580,1010,2191] BT.lf) [5,255,591,756,802,2184] BT.lf) [5,255,591,870,2184] (BT.nd (BT.nd BT.lf [5,255,756,802,2764] BT.lf) [5,514,591,756,2184] BT.lf)) [5,527,580,752,802,2184] (BT.nd (BT.nd (BT.nd BT.lf [5,580,591,802,2191,2296] BT.lf) [5,580,591,802,2191,2303] BT.lf) [5,580,591,802,2191,3855] (BT.nd BT.lf [5,580,591,802,3983] BT.lf))) [5,580,752,802,815,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,580,756,802,815,2191] BT.lf) [5,580,756,802,815,2986] BT.lf) [5,580,756,802,2184,4082] (BT.nd BT.lf [5,580,802,815,3983] BT.lf)) [5,580,802,2296,2764,4080] (BT.nd (BT.nd (BT.nd BT.lf [5,580,802,2764,3855,4080] BT.lf) [5,580,802,3983,4080] BT.lf) [5,580,815,2296,2986] (BT.nd BT.lf [5,580,2184,2296,4082] BT.lf)))))) [5,580,2184,3855,4082] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,591,756,802,870,2184] BT.lf) [5,591,756,802,1911] BT.lf) [5,591,756,802,2184] (BT.nd (BT.nd BT.lf [5,591,756,802,2191] BT.lf) [5,591,756,802,2764] BT.lf)) [5,591,756,802,2767] (BT.nd (BT.nd (BT.nd BT.lf [5,591,756,802,2986] BT.lf) [5,591,756,802,3208] BT.lf) [5,591,756,1826,2184] (BT.nd BT.lf [5,591,756,2184,2986] BT.lf))) [5,591,756,2184,3293] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,591,802,2184,2812] BT.lf) [5,591,802,2184,3339] BT.lf) [5,756,767,802,2764] (BT.nd (BT.nd BT.lf [5,756,802,815,870,2184] BT.lf) [5,756,802,815,2764] BT.lf)) [5,756,802,870,879,2184] (BT.nd (BT.nd (BT.nd BT.lf [5,756,802,870,2184,4080] BT.lf) [5,756,802,879,2184] BT.lf) [5,756,802,2184,3504] (BT.nd BT.lf [5,756,802,2764,4080] BT.lf)))) [5,802,815,2296,2764] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,802,1615,1780,2184] BT.lf) [5,802,2296,2764,4080] BT.lf) [6,0,15,240,580,802,2764] (BT.nd (BT.nd BT.lf [6,2,15,128,240,580] BT.lf) [6,2,15,240,512,580,2184] BT.lf)) [6,2,15,240,580,802,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,2,15,240,580,1911] BT.lf) [6,2,15,240,580,2184] BT.lf) [6,2,15,240,580,2186] (BT.nd BT.lf [6,2,15,240,580,2191] BT.lf))) [6,2,15,240,580,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2,15,240,580,3208] BT.lf) [6,2,15,240,582,2184] BT.lf) [6,2,15,240,2184,2764] (BT.nd BT.lf [6,2,15,240,2184,3515] BT.lf)) [6,2,15,242,580,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,2,15,255,580,2184] BT.lf) [6,2,15,580,756,802,2184] BT.lf) [6,2,15,580,2184,2296] (BT.nd BT.lf [6,2,15,580,2184,3855] BT.lf))))) [6,2,240,255,580,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2,240,580,591,802,2184] BT.lf) [6,2,240,580,2184,4080] BT.lf) [6,4,15,240,580,802,2764] (BT.nd (BT.nd BT.lf [6,4,15,240,802,2764] BT.lf) [6,4,240,580,591,802,2184] BT.lf)) [6,6,15,240,580,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,8,15,240,580,802,2764] BT.lf) [6,8,15,240,802,2764] BT.lf) [6,8,240,580,802,3208] (BT.nd BT.lf [6,8,240,580,1826,2184] BT.lf))) [6,8,240,802,1024,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,8,240,802,1604,2184] BT.lf) [6,10,15,240,580,2184] BT.lf) [6,11,240,580,802,2184] (BT.nd (BT.nd BT.lf [6,11,240,802,2184,3515] BT.lf) [6,12,15,240,580,802,2764] BT.lf)) [6,12,240,580,802,1024,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,13,15,240,580,2184] BT.lf) [6,13,240,580,802,2184] BT.lf) [6,13,240,580,1024,2184] (BT.nd BT.lf [6,13,240,580,2184] BT.lf)))) [6,13,240,580,2184,3293] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,15,240,580,802,2764] BT.lf) [6,15,32,240,580,802,2764] BT.lf) [6,15,32,580,802,3208] (BT.nd (BT.nd BT.lf [6,15,32,580,1826,2184] BT.lf) [6,15,32,802,1604,2184] BT.lf)) [6,15,34,240,580,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,34,255,580,2184] BT.lf) [6,15,64,240,580,802,2764] BT.lf) [6,15,64,580,756,802,2184] (BT.nd BT.lf [6,15,64,756,802,2184] BT.lf))) [6,15,68,240,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,68,240,580,2184,3293] BT.lf) [6,15,112,240,580,802] BT.lf) [6,15,112,580,802] (BT.nd BT.lf [6,15,112,580,802,1024] BT.lf)) [6,15,112,580,802,1911] (BT.nd (BT.nd (BT.nd BT.lf [6,15,112,580,802,2184] BT.lf) [6,15,128,240,512,580,802] BT.lf) [6,15,128,240,580,580,802] (BT.nd BT.lf [6,15,128,240,580,591,802] BT.lf))))))))) [6,15,128,240,580,708,802] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,128,240,580,756,802] BT.lf) [6,15,128,240,580,802] BT.lf) [6,15,128,240,580,802,870] (BT.nd (BT.nd BT.lf [6,15,128,240,580,802,1604] BT.lf) [6,15,128,240,580,802,2764] BT.lf)) [6,15,128,240,580,802,3515] (BT.nd (BT.nd (BT.nd BT.lf [6,15,128,240,580,870] BT.lf) [6,15,128,240,580,930] BT.lf) [6,15,128,240,580,1010] (BT.nd BT.lf [6,15,128,240,580,1826] BT.lf))) [6,15,128,240,580,3293] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,128,240,708,802] BT.lf) [6,15,128,240,802,1604] BT.lf) [6,15,128,240,802,3515] (BT.nd (BT.nd BT.lf [6,15,128,255,580,802] BT.lf) [6,15,128,580,756,802] BT.lf)) [6,15,128,580,802,3855] (BT.nd (BT.nd (BT.nd BT.lf [6,15,136,240,580,802] BT.lf) [6,15,136,255,580,802] BT.lf) [6,15,143,240,580,802] (BT.nd BT.lf [6,15,160,240,580,802] BT.lf)))) [6,15,176,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,176,802,2184,3515] BT.lf) [6,15,192,240,580,802] BT.lf) [6,15,192,240,580,802,2764] (BT.nd (BT.nd BT.lf [6,15,240,240,580,802,2764] BT.lf) [6,15,240,242,580,2184] BT.lf)) [6,15,240,255,580,802,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,290,580,802,2184] BT.lf) [6,15,240,290,580,2184] BT.lf) [6,15,240,290,802,2184,3515] (BT.nd BT.lf [6,15,240,290,2184,3515] BT.lf))) [6,15,240,512,580,802,1911] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,512,580,802,2184] BT.lf) [6,15,240,512,580,802,2191] BT.lf) [6,15,240,512,580,802,2696] (BT.nd (BT.nd BT.lf [6,15,240,512,580,802,2764] BT.lf) [6,15,240,512,580,802,3208] BT.lf)) [6,15,240,512,580,870,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,512,580,1010,2184] BT.lf) [6,15,240,512,580,1826,2184] BT.lf) [6,15,240,512,580,2184,3293] (BT.nd BT.lf [6,15,240,512,802,870,2184] BT.lf))))) [6,15,240,512,802,1604,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,512,802,2184,2764] BT.lf) [6,15,240,512,802,2184,3515] BT.lf) [6,15,240,514,580,591,2184] (BT.nd (BT.nd BT.lf [6,15,240,514,580,802,2184] BT.lf) [6,15,240,514,580,1024,2184] BT.lf)) [6,15,240,514,580,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,516,580,802,2184] BT.lf) [6,15,240,527,580,802,2184] BT.lf) [6,15,240,544,580,802,2184] (BT.nd BT.lf [6,15,240,576,580,802,2184] BT.lf))) [6,15,240,580,580,802,1911] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,580,802,2184] BT.lf) [6,15,240,580,580,802,2191] BT.lf) [6,15,240,580,580,802,2764] (BT.nd (BT.nd BT.lf [6,15,240,580,580,802,3208] BT.lf) [6,15,240,580,580,1826,2184] BT.lf)) [6,15,240,580,580,2184,3293] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,582,802,2184] BT.lf) [6,15,240,580,582,2184] BT.lf) [6,15,240,580,588,802,2184] (BT.nd BT.lf [6,15,240,580,591,802,1911] BT.lf)))) [6,15,240,580,591,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,591,802,2191] BT.lf) [6,15,240,580,591,802,2764] BT.lf) [6,15,240,580,591,802,2767] (BT.nd (BT.nd BT.lf [6,15,240,580,591,802,3208] BT.lf) [6,15,240,580,591,1826,2184] BT.lf)) [6,15,240,580,591,2184,3293] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,612,802,2184] BT.lf) [6,15,240,580,708,802] BT.lf) [6,15,240,580,708,802,1024] (BT.nd BT.lf [6,15,240,580,708,802,2184] BT.lf))) [6,15,240,580,752,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,756,802,1911] BT.lf) [6,15,240,580,756,802,2184] BT.lf) [6,15,240,580,756,802,2191] (BT.nd BT.lf [6,15,240,580,756,802,2764] BT.lf)) [6,15,240,580,756,802,3208] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,756,1010,2184] BT.lf) [6,15,240,580,756,1826,2184] BT.lf) [6,15,240,580,756,2184,3293] (BT.nd BT.lf [6,15,240,580,767,802,2184] BT.lf)))))) [6,15,240,580,770,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,802,2764] BT.lf) [6,15,240,580,802,815,2764] BT.lf) [6,15,240,580,802,870,1911] (BT.nd (BT.nd BT.lf [6,15,240,580,802,870,2184] BT.lf) [6,15,240,580,802,870,2191] BT.lf)) [6,15,240,580,802,870,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,870,2986] BT.lf) [6,15,240,580,802,870,3054] BT.lf) [6,15,240,580,802,870,3208] (BT.nd BT.lf [6,15,240,580,802,887] BT.lf))) [6,15,240,580,802,930] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1010,2764] BT.lf) [6,15,240,580,802,1024,1331] BT.lf) [6,15,240,580,802,1024,2696] (BT.nd (BT.nd BT.lf [6,15,240,580,802,1024,2764] BT.lf) [6,15,240,580,802,1024,2767] BT.lf)) [6,15,240,580,802,1024,3788] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1039,2764] BT.lf) [6,15,240,580,802,1109] BT.lf) [6,15,240,580,802,1152] (BT.nd BT.lf [6,15,240,580,802,1264,2764] BT.lf)))) [6,15,240,580,802,1331] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1331,2184] BT.lf) [6,15,240,580,802,1331,2764] BT.lf) [6,15,240,580,802,1536,2184] (BT.nd (BT.nd BT.lf [6,15,240,580,802,1604,1911] BT.lf) [6,15,240,580,802,1604,2184] BT.lf)) [6,15,240,580,802,1604,2191] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1604,2764] BT.lf) [6,15,240,580,802,1604,3208] BT.lf) [6,15,240,580,802,1604,3788] (BT.nd BT.lf [6,15,240,580,802,1615,2184] BT.lf))) [6,15,240,580,802,1780,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1826,2764] BT.lf) [6,15,240,580,802,1894,2184] BT.lf) [6,15,240,580,802,1904] (BT.nd BT.lf [6,15,240,580,802,1911] BT.lf)) [6,15,240,580,802,1911,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,1911,3515] BT.lf) [6,15,240,580,802,1919] BT.lf) [6,15,240,580,802,2176] (BT.nd BT.lf [6,15,240,580,802,2184] BT.lf))))) [6,15,240,580,802,2184,2491] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2184,2696] BT.lf) [6,15,240,580,802,2184,2764] BT.lf) [6,15,240,580,802,2184,2767] (BT.nd (BT.nd BT.lf [6,15,240,580,802,2184,2812] BT.lf) [6,15,240,580,802,2184,3054] BT.lf)) [6,15,240,580,802,2184,3225] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2184,3339] BT.lf) [6,15,240,580,802,2184,3504] BT.lf) [6,15,240,580,802,2184,3515] (BT.nd BT.lf [6,15,240,580,802,2184,3519] BT.lf))) [6,15,240,580,802,2184,3579] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2184,3583] BT.lf) [6,15,240,580,802,2184,3788] BT.lf) [6,15,240,580,802,2184,3805] (BT.nd (BT.nd BT.lf [6,15,240,580,802,2184,4027] BT.lf) [6,15,240,580,802,2186] BT.lf)) [6,15,240,580,802,2188] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2191] BT.lf) [6,15,240,580,802,2191,2764] BT.lf) [6,15,240,580,802,2191,2767] (BT.nd BT.lf [6,15,240,580,802,2191,3515] BT.lf)))) [6,15,240,580,802,2216] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2248] BT.lf) [6,15,240,580,802,2296,2764] BT.lf) [6,15,240,580,802,2696] (BT.nd (BT.nd BT.lf [6,15,240,580,802,2764] BT.lf) [6,15,240,580,802,2764,2764] BT.lf)) [6,15,240,580,802,2764,2767] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2764,2812] BT.lf) [6,15,240,580,802,2764,2986] BT.lf) [6,15,240,580,802,2764,3054] (BT.nd BT.lf [6,15,240,580,802,2764,3071] BT.lf))) [6,15,240,580,802,2764,3208] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2764,3293] BT.lf) [6,15,240,580,802,2764,3515] BT.lf) [6,15,240,580,802,2764,3788] (BT.nd BT.lf [6,15,240,580,802,2764,3855] BT.lf)) [6,15,240,580,802,2764,4080] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,2767] BT.lf) [6,15,240,580,802,2986] BT.lf) [6,15,240,580,802,2991] (BT.nd BT.lf [6,15,240,580,802,3054] BT.lf))))))) [6,15,240,580,802,3208] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,3208,3515] BT.lf) [6,15,240,580,802,3208,3788] BT.lf) [6,15,240,580,802,3215] (BT.nd (BT.nd BT.lf [6,15,240,580,802,3788] BT.lf) [6,15,240,580,802,3967] BT.lf)) [6,15,240,580,802,3983] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,802,4010] BT.lf) [6,15,240,580,806,2184] BT.lf) [6,15,240,580,810,2184] (BT.nd BT.lf [6,15,240,580,815,870,2184] BT.lf))) [6,15,240,580,866,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,870,1826,2184] BT.lf) [6,15,240,580,870,1911] BT.lf) [6,15,240,580,870,2184] (BT.nd (BT.nd BT.lf [6,15,240,580,870,2184,2986] BT.lf) [6,15,240,580,870,2184,3293] BT.lf)) [6,15,240,580,870,2191] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,870,2764] BT.lf) [6,15,240,580,870,2986] BT.lf) [6,15,240,580,870,3054] (BT.nd BT.lf [6,15,240,580,870,3208] BT.lf)))) [6,15,240,580,930,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,1010,1911] BT.lf) [6,15,240,580,1010,2184] BT.lf) [6,15,240,580,1010,2191] (BT.nd (BT.nd BT.lf [6,15,240,580,1010,2764] BT.lf) [6,15,240,580,1010,3208] BT.lf)) [6,15,240,580,1014,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,1024,1826,2764] BT.lf) [6,15,240,580,1024,2764,3293] BT.lf) [6,15,240,580,1026,2184] (BT.nd BT.lf [6,15,240,580,1109,2184] BT.lf))) [6,15,240,580,1604,1826,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,1604,2184,3293] BT.lf) [6,15,240,580,1826,1894,2184] BT.lf) [6,15,240,580,1826,1911] (BT.nd BT.lf [6,15,240,580,1826,2184] BT.lf)) [6,15,240,580,1826,2184,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,1826,2184,3515] BT.lf) [6,15,240,580,1826,2191] BT.lf) [6,15,240,580,1826,2764] (BT.nd BT.lf [6,15,240,580,1826,2986] BT.lf))))) [6,15,240,580,1826,3208] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,1826,4010] BT.lf) [6,15,240,580,1894,2184] BT.lf) [6,15,240,580,1911,2986] (BT.nd (BT.nd BT.lf [6,15,240,580,1911,3293] BT.lf) [6,15,240,580,2034,2184] BT.lf)) [6,15,240,580,2184,2186] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,2184,2269] BT.lf) [6,15,240,580,2184,2764,2986] BT.lf) [6,15,240,580,2184,2764,3293] (BT.nd BT.lf [6,15,240,580,2184,2986] BT.lf))) [6,15,240,580,2184,3054] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,2184,3066] BT.lf) [6,15,240,580,2184,3085] BT.lf) [6,15,240,580,2184,3225] (BT.nd (BT.nd BT.lf [6,15,240,580,2184,3293] BT.lf) [6,15,240,580,2184,3293,3515] BT.lf)) [6,15,240,580,2184,3293,3805] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,2184,3325] BT.lf) [6,15,240,580,2184,3805] BT.lf) [6,15,240,580,2184,4010] (BT.nd BT.lf [6,15,240,580,2184,4082] BT.lf)))) [6,15,240,580,2184,4093] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,2191,3293] BT.lf) [6,15,240,580,2764,2986] BT.lf) [6,15,240,580,2764,3054] (BT.nd (BT.nd BT.lf [6,15,240,580,2764,3293] BT.lf) [6,15,240,580,2986,3208] BT.lf)) [6,15,240,580,2986,3293] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,580,3208,3293] BT.lf) [6,15,240,580,3208,4010] BT.lf) [6,15,240,582,802,2184] (BT.nd BT.lf [6,15,240,582,1024,2184] BT.lf))) [6,15,240,582,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,588,802,2184] BT.lf) [6,15,240,591,756,802,2184] BT.lf) [6,15,240,591,802,870,2184] (BT.nd BT.lf [6,15,240,591,802,1604,2184] BT.lf)) [6,15,240,591,802,2184,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,591,802,2184,3515] BT.lf) [6,15,240,591,870,2184] BT.lf) [6,15,240,612,802,2184] (BT.nd BT.lf [6,15,240,708,802] BT.lf)))))) [6,15,240,708,802,1024] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,708,802,2184] BT.lf) [6,15,240,756,802,870,2184] BT.lf) [6,15,240,756,802,1024,2764] (BT.nd (BT.nd BT.lf [6,15,240,756,802,1604,2184] BT.lf) [6,15,240,756,802,2184,2764] BT.lf)) [6,15,240,756,802,2184,3515] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,756,802,2764] BT.lf) [6,15,240,802,870,1604,2184] BT.lf) [6,15,240,802,870,2184,2764] (BT.nd BT.lf [6,15,240,802,870,2184,3515] BT.lf))) [6,15,240,802,870,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,1024,1604,2764] BT.lf) [6,15,240,802,1024,1604,3788] BT.lf) [6,15,240,802,1024,2764,3515] (BT.nd (BT.nd BT.lf [6,15,240,802,1331,2184] BT.lf) [6,15,240,802,1331,2184,2764] BT.lf)) [6,15,240,802,1604,1894,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,1604,1911] BT.lf) [6,15,240,802,1604,2184] BT.lf) [6,15,240,802,1604,2184,2764] (BT.nd BT.lf [6,15,240,802,1604,2184,3515] BT.lf)))) [6,15,240,802,1604,2191] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,1604,2764] BT.lf) [6,15,240,802,1604,2986] BT.lf) [6,15,240,802,1604,3208] (BT.nd (BT.nd BT.lf [6,15,240,802,1604,3788] BT.lf) [6,15,240,802,1911,2764] BT.lf)) [6,15,240,802,1911,3515] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,2184,2491] BT.lf) [6,15,240,802,2184,2764] BT.lf) [6,15,240,802,2184,2764,2764] (BT.nd BT.lf [6,15,240,802,2184,2764,2767] BT.lf))) [6,15,240,802,2184,2764,2812] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,2184,2764,3054] BT.lf) [6,15,240,802,2184,2764,3515] BT.lf) [6,15,240,802,2184,2764,3788] (BT.nd BT.lf [6,15,240,802,2184,3515] BT.lf)) [6,15,240,802,2184,3515,3515] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,2184,3515,3519] BT.lf) [6,15,240,802,2184,3515,3579] BT.lf) [6,15,240,802,2184,3515,4027] (BT.nd BT.lf [6,15,240,802,2184,3788] BT.lf))))) [6,15,240,802,2191,3515] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,2296,2764] BT.lf) [6,15,240,802,2764,2986] BT.lf) [6,15,240,802,2764,3208] (BT.nd (BT.nd BT.lf [6,15,240,802,2764,3515] BT.lf) [6,15,240,802,2986,3515] BT.lf)) [6,15,240,802,3208,3515] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,802,3208,3788] BT.lf) [6,15,240,870,1024,2764] BT.lf) [6,15,240,870,1604,2184] (BT.nd BT.lf [6,15,240,870,2184,2764] BT.lf))) [6,15,240,870,2184,3515] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,870,2764] BT.lf) [6,15,240,1010,1604,2184] BT.lf) [6,15,240,1010,2184,2764] (BT.nd (BT.nd BT.lf [6,15,240,1010,2184,3515] BT.lf) [6,15,240,1604,2184,2986] BT.lf)) [6,15,240,1604,2184,3293] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,1826,2184,2764] BT.lf) [6,15,240,1826,2184,3515] BT.lf) [6,15,240,2184,2764,2986] (BT.nd BT.lf [6,15,240,2184,2764,3054] BT.lf)))) [6,15,240,2184,2764,3293] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,2184,2986,3515] BT.lf) [6,15,240,2184,3293,3515] BT.lf) [6,15,242,580,802,2184] (BT.nd (BT.nd BT.lf [6,15,242,580,1024,2184] BT.lf) [6,15,242,580,2184] BT.lf)) [6,15,244,580,802,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,248,580,802,2184] BT.lf) [6,15,255,580,591,802,2184] BT.lf) [6,15,255,580,756,802,2184] (BT.nd BT.lf [6,15,255,580,802,1911] BT.lf))) [6,15,255,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,255,580,802,2191] BT.lf) [6,15,255,580,802,2764] BT.lf) [6,15,255,580,802,2986] (BT.nd BT.lf [6,15,255,580,802,3208] BT.lf)) [6,15,255,580,870,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,255,580,1010,2184] BT.lf) [6,15,255,580,1826,2184] BT.lf) [6,15,255,580,2184,2986] (BT.nd BT.lf [6,15,255,580,2184,3293] BT.lf)))))))) [6,15,255,802,1604,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,255,802,2184,2764] BT.lf) [6,15,255,802,2184,3515] BT.lf) [6,15,512,580,752,802,2184] (BT.nd (BT.nd BT.lf [6,15,512,580,756,802,2184] BT.lf) [6,15,512,580,802,2184,2296] BT.lf)) [6,15,512,580,802,2184,3855] (BT.nd (BT.nd (BT.nd BT.lf [6,15,516,580,802,2184,3855] BT.lf) [6,15,544,580,756,802,2184] BT.lf) [6,15,544,580,802,1024,2184] (BT.nd BT.lf [6,15,580,580,802,2184,2296] BT.lf))) [6,15,580,580,802,2184,3855] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,591,802,2184,2296] BT.lf) [6,15,580,591,802,2184,3855] BT.lf) [6,15,580,752,802,2184] (BT.nd (BT.nd BT.lf [6,15,580,756,802,802,2184] BT.lf) [6,15,580,756,802,815,2184] BT.lf)) [6,15,580,756,802,870,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,756,802,1010,2184] BT.lf) [6,15,580,756,802,1014,2184] BT.lf) [6,15,580,756,802,1264,2184] (BT.nd BT.lf [6,15,580,756,802,1826,2184] BT.lf)))) [6,15,580,756,802,1911] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,756,802,2184] BT.lf) [6,15,580,756,802,2184,2296] BT.lf) [6,15,580,756,802,2184,2986] (BT.nd (BT.nd BT.lf [6,15,580,756,802,2184,3293] BT.lf) [6,15,580,756,802,2184,3855] BT.lf)) [6,15,580,756,802,2191] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,756,802,2764] BT.lf) [6,15,580,756,802,2986] BT.lf) [6,15,580,756,802,3208] (BT.nd BT.lf [6,15,580,756,1826,2184] BT.lf))) [6,15,580,756,2184,2986] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,756,2184,3293] BT.lf) [6,15,580,767,802,2184] BT.lf) [6,15,580,770,1024,2184] (BT.nd (BT.nd BT.lf [6,15,580,770,2184,3855] BT.lf) [6,15,580,802,870,2184,2296] BT.lf)) [6,15,580,802,870,2184,3855] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,1024,1264,2764] BT.lf) [6,15,580,802,1024,2216] BT.lf) [6,15,580,802,1024,2296,2764] (BT.nd BT.lf [6,15,580,802,1024,2764,3855] BT.lf))))) [6,15,580,802,1024,3983] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,1056,2184] BT.lf) [6,15,580,802,1264,1604,2184] BT.lf) [6,15,580,802,1264,3208] (BT.nd (BT.nd BT.lf [6,15,580,802,1604,2184,2296] BT.lf) [6,15,580,802,1604,2184,3855] BT.lf)) [6,15,580,802,1799,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,1911,2296] BT.lf) [6,15,580,802,1911,3855] BT.lf) [6,15,580,802,2184,2296] (BT.nd BT.lf [6,15,580,802,2184,2296,2764] BT.lf))) [6,15,580,802,2184,2296,2812] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,2184,2296,3515] BT.lf) [6,15,580,802,2184,2303] BT.lf) [6,15,580,802,2184,2764,3855] (BT.nd (BT.nd BT.lf [6,15,580,802,2184,2812] BT.lf) [6,15,580,802,2184,3339] BT.lf)) [6,15,580,802,2184,3515,3855] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,2184,3840] BT.lf) [6,15,580,802,2184,3855] BT.lf) [6,15,580,802,2184,3919] (BT.nd BT.lf [6,15,580,802,2184,3983] BT.lf)))) [6,15,580,802,2191,2296] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,2191,2303] BT.lf) [6,15,580,802,2191,3855] BT.lf) [6,15,580,802,2296,2764] (BT.nd (BT.nd BT.lf [6,15,580,802,2296,2986] BT.lf) [6,15,580,802,2296,3208] BT.lf)) [6,15,580,802,2764,2812] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,2764,3855] BT.lf) [6,15,580,802,2986,3855] BT.lf) [6,15,580,802,3208,3320] (BT.nd BT.lf [6,15,580,802,3208,3855] BT.lf))) [6,15,580,802,3855,3983] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,802,3983] BT.lf) [6,15,580,870,2184,2296] BT.lf) [6,15,580,870,2184,3855] (BT.nd BT.lf [6,15,580,1010,1264,2184] BT.lf)) [6,15,580,1010,2184,2296] (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,1010,2184,3855] BT.lf) [6,15,580,1024,2184,3325] BT.lf) [6,15,580,1826,2184,2296] (BT.nd BT.lf [6,15,580,1826,2184,3855] BT.lf)))))) [6,15,580,2184,2296,2986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,580,2184,2296,3066] BT.lf) [6,15,580,2184,2296,3293] BT.lf) [6,15,580,2184,2986,3855] (BT.nd (BT.nd BT.lf [6,15,580,2184,3293,3855] BT.lf) [6,15,591,756,802,2184] BT.lf)) [6,15,612,802,1024,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,15,756,802,870,1024,2184] BT.lf) [6,15,756,802,870,2184] BT.lf) [6,15,756,802,1024,2764] (BT.nd BT.lf [6,15,756,802,1604,2184] BT.lf))) [6,15,756,802,2184,2764] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,756,802,2184,3515] BT.lf) [6,15,756,802,2764] BT.lf) [6,15,802,1024,2296,2764] (BT.nd (BT.nd BT.lf [6,15,802,1264,1604,2184] BT.lf) [6,15,802,1604,1780,2184] BT.lf)) [6,15,802,1604,2184,2296] (BT.nd (BT.nd (BT.nd BT.lf [6,15,802,1604,2184,3855] BT.lf) [6,15,802,2184,2296,2764] BT.lf) [6,15,802,2184,2296,3515] (BT.nd BT.lf [6,15,802,2184,2764,2812] BT.lf)))) [6,15,802,2184,2764,3855] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,802,2184,3515,3855] BT.lf) [6,15,802,2296,2764] BT.lf) [6,34,240,255,580,2184] (BT.nd (BT.nd BT.lf [6,47,240,580,802,2184] BT.lf) [6,79,240,580,802,2184] BT.lf)) [6,128,143,240,580,802] (BT.nd (BT.nd (BT.nd BT.lf [6,128,240,255,580,802] BT.lf) [6,128,240,580,591,802] BT.lf) [6,128,240,580,802,815] (BT.nd BT.lf [6,128,240,580,802,4080] BT.lf))) [6,136,240,255,580,802] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,143,240,580,802] BT.lf) [6,143,240,580,802,1024] BT.lf) [6,143,240,580,802,2184] (BT.nd BT.lf [6,240,255,580,591,802,2184] BT.lf)) [6,240,255,580,756,802,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,240,255,580,802,1911] BT.lf) [6,240,255,580,802,2184] BT.lf) [6,240,255,580,802,2191] (BT.nd BT.lf [6,240,255,580,802,2764] BT.lf))))) [6,240,255,580,802,2986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,255,580,802,3208] BT.lf) [6,240,255,580,870,2184] BT.lf) [6,240,255,580,1010,2184] (BT.nd (BT.nd BT.lf [6,240,255,580,1826,2184] BT.lf) [6,240,255,580,2184,2986] BT.lf)) [6,240,255,580,2184,3293] (BT.nd (BT.nd (BT.nd BT.lf [6,240,255,802,1604,2184] BT.lf) [6,240,255,802,2184,2764] BT.lf) [6,240,255,802,2184,3515] (BT.nd BT.lf [6,240,512,527,580,802,2184] BT.lf))) [6,240,512,580,591,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,512,580,802,815,2184] BT.lf) [6,240,512,580,802,2184,4080] BT.lf) [6,240,514,580,591,2184] (BT.nd (BT.nd BT.lf [6,240,527,580,802,2184] BT.lf) [6,240,576,580,802,2184,4080] BT.lf)) [6,240,580,580,802,2184,4080] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,591,802,870,2184] BT.lf) [6,240,580,591,802,1024,2191] BT.lf) [6,240,580,591,802,1039,2184] (BT.nd BT.lf [6,240,580,591,802,1911] BT.lf)))) [6,240,580,591,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,591,802,2184,2191] BT.lf) [6,240,580,591,802,2184,4080] BT.lf) [6,240,580,591,802,2191] (BT.nd (BT.nd BT.lf [6,240,580,591,802,2764] BT.lf) [6,240,580,591,802,2767] BT.lf)) [6,240,580,591,802,2986] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,591,802,3208] BT.lf) [6,240,580,591,1010,2184] BT.lf) [6,240,580,591,1826,2184] (BT.nd BT.lf [6,240,580,591,2184,2986] BT.lf))) [6,240,580,591,2184,3293] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,756,802,2184,4080] BT.lf) [6,240,580,767,802,2184] BT.lf) [6,240,580,802,815,870,2184] (BT.nd BT.lf [6,240,580,802,815,1911] BT.lf)) [6,240,580,802,815,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,815,2191] BT.lf) [6,240,580,802,815,2764] BT.lf) [6,240,580,802,815,2986] (BT.nd BT.lf [6,240,580,802,815,2991] BT.lf))))))) [6,240,580,802,815,3208] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,870,879,2184] BT.lf) [6,240,580,802,870,2184,4080] BT.lf) [6,240,580,802,879,2184] (BT.nd (BT.nd BT.lf [6,240,580,802,1023,2184] BT.lf) [6,240,580,802,1024,1039,2764] BT.lf)) [6,240,580,802,1024,1919] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,1024,2176] BT.lf) [6,240,580,802,1024,2764,4080] BT.lf) [6,240,580,802,1032,2184] (BT.nd BT.lf [6,240,580,802,1039,1604,2184] BT.lf))) [6,240,580,802,1039,2191] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,1604,2184,4080] BT.lf) [6,240,580,802,1911,4080] BT.lf) [6,240,580,802,2176,4080] (BT.nd (BT.nd BT.lf [6,240,580,802,2184,2764,4080] BT.lf) [6,240,580,802,2184,3280] BT.lf)) [6,240,580,802,2184,3504] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,2184,3515,4080] BT.lf) [6,240,580,802,2184,3840] BT.lf) [6,240,580,802,2184,4080] (BT.nd BT.lf [6,240,580,802,2184,4082] BT.lf)))) [6,240,580,802,2184,4084] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,802,2191,4080] BT.lf) [6,240,580,802,2764,4080] BT.lf) [6,240,580,802,2986,4080] (BT.nd (BT.nd BT.lf [6,240,580,802,3208,4080] BT.lf) [6,240,580,810,1024,2184] BT.lf)) [6,240,580,815,1010,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,815,1826,2184] BT.lf) [6,240,580,815,2184,2986] BT.lf) [6,240,580,815,2184,3293] (BT.nd BT.lf [6,240,580,870,2184,4080] BT.lf))) [6,240,580,1010,1023,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,1010,2184,4080] BT.lf) [6,240,580,1024,2184,4082] BT.lf) [6,240,580,1039,1826,2184] (BT.nd BT.lf [6,240,580,1826,1839,2184] BT.lf)) [6,240,580,1826,2184,4080] (BT.nd (BT.nd (BT.nd BT.lf [6,240,580,2184,2986,4080] BT.lf) [6,240,580,2184,3293,4080] BT.lf) [6,240,580,2184,4080,4082] (BT.nd BT.lf [6,240,580,2184,4082] BT.lf))))) [6,240,588,802,1024,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,591,756,802,2184] BT.lf) [6,240,591,802,1604,2184] BT.lf) [6,240,591,802,2184,2764] (BT.nd (BT.nd BT.lf [6,240,591,802,2184,3515] BT.lf) [6,240,802,815,1604,2184] BT.lf)) [6,240,802,815,2184,2764] (BT.nd (BT.nd (BT.nd BT.lf [6,240,802,815,2184,3515] BT.lf) [6,240,802,1039,1604,2184] BT.lf) [6,240,802,1604,1615,2184] (BT.nd BT.lf [6,240,802,1604,2184,4080] BT.lf))) [6,240,802,2184,2764,4080] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,802,2184,3515,4080] BT.lf) [6,255,580,591,802,2184] BT.lf) [6,255,580,756,802,2184] (BT.nd (BT.nd BT.lf [6,255,580,802,1039,2184] BT.lf) [6,255,580,802,1264,2184] BT.lf)) [6,255,580,802,2184,3855] (BT.nd (BT.nd (BT.nd BT.lf [6,255,580,802,2184,4080] BT.lf) [6,580,591,756,802,2184] BT.lf) [6,580,591,767,802,2184] (BT.nd BT.lf [6,580,591,802,2184,2296] BT.lf)))) [6,580,591,802,2184,3855] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,580,756,767,802,2184] BT.lf) [6,580,756,802,815,2184] BT.lf) [6,580,756,802,2184,4080] (BT.nd (BT.nd BT.lf [6,580,802,815,2184,2296] BT.lf) [6,580,802,815,2184,3855] BT.lf)) [6,580,802,1039,1264,2184] (BT.nd (BT.nd (BT.nd BT.lf [6,580,802,2184,2296,4080] BT.lf) [6,580,802,2184,3855,4080] BT.lf) [6,591,756,802,1024,2184] (BT.nd BT.lf [6,591,756,802,2184] BT.lf))) [7,0,15,240,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2,15,240,580,802,2184] BT.lf) [7,2,15,240,580,1024,2184] BT.lf) [7,2,15,240,580,2184] (BT.nd BT.lf [7,4,15,240,580,802,2184] BT.lf)) [7,8,15,240,580,802,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,8,240,580,802,1024,2184] BT.lf) [7,15,15,240,580,802,2184] BT.lf) [7,15,32,240,580,802,2184] (BT.nd BT.lf [7,15,32,580,802,1024,2184] BT.lf)))))) [7,15,64,240,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,128,240,580,802] BT.lf) [7,15,128,240,580,802,1024] BT.lf) [7,15,128,240,580,802,2184] (BT.nd (BT.nd BT.lf [7,15,240,240,580,802,2184] BT.lf) [7,15,240,255,580,802,2184] BT.lf)) [7,15,240,512,580,802,1024,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,512,580,802,2184] BT.lf) [7,15,240,580,580,802,1024,2184] BT.lf) [7,15,240,580,580,802,2184] (BT.nd BT.lf [7,15,240,580,591,802,1024,2184] BT.lf))) [7,15,240,580,591,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,756,802,1024,2184] BT.lf) [7,15,240,580,756,802,2184] BT.lf) [7,15,240,580,802,802,2184] (BT.nd (BT.nd BT.lf [7,15,240,580,802,815,2184] BT.lf) [7,15,240,580,802,870,1024,2184] BT.lf)) [7,15,240,580,802,870,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,1010,2184] BT.lf) [7,15,240,580,802,1024,1604,2184] BT.lf) [7,15,240,580,802,1024,1911] (BT.nd BT.lf [7,15,240,580,802,1024,2184] BT.lf)))) [7,15,240,580,802,1024,2184,2764] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,1024,2184,3515] BT.lf) [7,15,240,580,802,1024,2191] BT.lf) [7,15,240,580,802,1024,2764] (BT.nd (BT.nd BT.lf [7,15,240,580,802,1024,2986] BT.lf) [7,15,240,580,802,1024,3208] BT.lf)) [7,15,240,580,802,1039,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,1264,2184] BT.lf) [7,15,240,580,802,1604,2184] BT.lf) [7,15,240,580,802,1826,2184] (BT.nd BT.lf [7,15,240,580,802,1911] BT.lf))) [7,15,240,580,802,1911,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,2184] BT.lf) [7,15,240,580,802,2184,2184] BT.lf) [7,15,240,580,802,2184,2191] (BT.nd BT.lf [7,15,240,580,802,2184,2296] BT.lf)) [7,15,240,580,802,2184,2764] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,2184,2986] BT.lf) [7,15,240,580,802,2184,3071] BT.lf) [7,15,240,580,802,2184,3208] (BT.nd BT.lf [7,15,240,580,802,2184,3293] BT.lf))))) [7,15,240,580,802,2184,3515] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,802,2184,3855] BT.lf) [7,15,240,580,802,2184,4080] BT.lf) [7,15,240,580,802,2191] (BT.nd (BT.nd BT.lf [7,15,240,580,802,2764] BT.lf) [7,15,240,580,802,2986] BT.lf)) [7,15,240,580,802,3208] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,870,1024,2184] BT.lf) [7,15,240,580,870,2184] BT.lf) [7,15,240,580,1010,1024,2184] (BT.nd BT.lf [7,15,240,580,1010,2184] BT.lf))) [7,15,240,580,1024,1826,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,580,1024,2184,2986] BT.lf) [7,15,240,580,1024,2184,3293] BT.lf) [7,15,240,580,1826,2184] (BT.nd (BT.nd BT.lf [7,15,240,580,2184,2986] BT.lf) [7,15,240,580,2184,3293] BT.lf)) [7,15,240,802,1024,1604,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,802,1024,2184,2764] BT.lf) [7,15,240,802,1024,2184,3515] BT.lf) [7,15,240,802,1604,2184] (BT.nd BT.lf [7,15,240,802,2184,2764] BT.lf)))) [7,15,240,802,2184,3515] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,255,580,802,1024,2184] BT.lf) [7,15,255,580,802,2184] BT.lf) [7,15,580,756,802,1024,2184] (BT.nd (BT.nd BT.lf [7,15,580,756,802,2184] BT.lf) [7,15,580,802,1024,1264,2184] BT.lf)) [7,15,580,802,1024,2184,2296] (BT.nd (BT.nd (BT.nd BT.lf [7,15,580,802,1024,2184,3855] BT.lf) [7,15,580,802,2184,2296] BT.lf) [7,15,580,802,2184,3855] (BT.nd BT.lf [7,240,255,580,802,1024,2184] BT.lf))) [7,240,255,580,802,2184] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,580,591,802,1024,2184] BT.lf) [7,240,580,591,802,2184] BT.lf) [7,240,580,802,815,1024,2184] (BT.nd BT.lf [7,240,580,802,815,2184] BT.lf)) [7,240,580,802,1024,1039,2184] (BT.nd (BT.nd (BT.nd BT.lf [7,240,580,802,1024,2184,4080] BT.lf) [7,240,580,802,2184,4080] BT.lf) [8,15,240,580,802,1024,2184] (BT.nd BT.lf [8,15,240,580,802,2184] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,15,628,802,3225],[]),([3,15,756,802,3097],[]),([3,125,580],[(0,295939),(2,296962),(4,295939),(6,2338)]),([3,127,514,580],[(80,302082)]),([3,127,582],[(0,302082),(2,295944),(4,302082),(6,1320)]),([3,253,708],[(0,295939),(2,296962),(4,295939),(6,2338)]),([3,255,514,708],[(80,303106)]),([3,255,580,642],[(80,303106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,255,710],[(0,303106),(2,295945),(4,303106),(6,1321)]),([3,580,3970],[(0,296962),(2,296962),(4,296962),(6,295939)]),([4,2,127,580],[(0,302083),(2,302083),(4,302083),(6,296968),(8,302083),(10,2344),(58,302083),(61,302083),(73,7459),(74,302083)]),([4,2,255,708],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,2345),(58,303107),(61,303107),(73,8483),(74,303107)]),([4,13,68,756,2184],[(56,132099),(104,132195)]),([4,13,112,580],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(57,295939),(58,295939)]),([4,13,240,708],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(57,295939),(58,295939)]),([4,13,580,3983],[(0,301186),(2,296962),(4,301186),(6,301186),(8,301186),(10,295939),(74,301186),(77,301186)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,13,2296,2764],[(0,295939),(2,296962),(4,295939),(6,295939),(8,295939),(10,100647)]),([4,15,112,514,580],[(112,302082)]),([4,15,112,580,802,3225],[]),([4,15,112,582],[(0,302082),(2,295944),(4,302082),(6,301192),(8,302082),(10,1320),(57,302082),(58,302082)]),([4,15,114,580],[(0,302083),(2,132104),(4,302083),(6,1160),(8,302083),(10,2344)]),([4,15,240,514,708],[(112,303106)]),([4,15,240,580,642],[(112,303106)]),([4,15,240,580,802,3097],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,240,708,802,3097],[]),([4,15,240,710],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,1321),(57,303106),(58,303106)]),([4,15,242,708],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345)]),([4,15,514,580,3983],[(80,301192)]),([4,15,514,2296,2764],[(104,303106)]),([4,15,544,870,3208],[(104,170120)]),([4,15,544,1894,2184],[(104,170120)]),([4,15,580,802,1041,2296],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,580,2296,2698],[(104,303106)]),([4,15,580,3981],[(0,1160),(2,132104),(4,1160),(6,1160),(8,1160),(10,302083)]),([4,15,582,3983],[(0,301192),(2,295944),(4,301192),(6,301192),(8,301192),(10,302082),(74,301192),(77,301192)]),([4,15,628,802,870],[(96,7299)]),([4,15,756,802,998],[(96,10371)]),([4,15,756,802,1041,2184],[]),([4,15,756,802,1911,3225],[]),([4,15,802,870,3467],[(72,2184)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,802,1041,2184,2812],[]),([4,15,802,1041,2296,2764],[]),([4,15,2296,2766],[(0,303106),(2,295945),(4,303106),(6,303106),(8,303106),(10,99623)]),([4,15,2298,2764],[(0,99331),(2,132105),(4,99331),(6,99331),(8,99331),(10,100354)]),([4,68,240,589,2184],[(56,1155)]),([4,77,756,2184],[(0,132099),(2,133122),(4,132099),(6,2178),(8,132099),(10,132099),(74,132099),(81,132099),(86,132099)]),([4,112,580,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,295939),(74,296962),(77,296962)]),([4,127,580,591,802],[(104,303266)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,127,580,628,802],[]),([4,127,580,756,802],[]),([4,128,253,580],[(0,295939),(2,295939),(4,295939),(6,296962),(8,295939),(10,2338),(58,295939),(61,295939),(73,1315),(74,295939)]),([4,128,255,514,580],[(112,303106)]),([4,128,255,582],[(0,303106),(2,303106),(4,303106),(6,295945),(8,303106),(10,1321),(58,303106),(61,303106),(73,8482),(74,303106)]),([4,130,255,580],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,2345),(58,303107),(61,303107),(73,8483),(74,303107)]),([4,141,240,580],[(0,295939),(2,138242),(4,295939),(6,7298),(8,295939),(10,2338)]),([4,143,240,582],[(0,303106),(2,138249),(4,303106),(6,7305),(8,303106),(10,1321)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,143,242,580],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345)]),([4,207,756,802],[(0,141315),(2,133131),(4,141315),(6,2187),(8,141315),(10,141315),(73,10371),(78,139267),(82,10371)]),([4,240,319,580,802],[(112,305154)]),([4,240,580,802,3776],[(80,295947),(104,295939)]),([4,240,580,1343,1826],[(104,306178)]),([4,240,580,1826,2752],[(80,295948),(104,295939)]),([4,240,580,3954],[(0,138242),(2,138242),(4,138242),(6,138242),(8,138242),(10,295939)]),([4,240,708,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,295939),(74,296962),(77,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([4,240,802,1343,1604],[(104,306178)]),([4,240,802,1604,2752],[(80,295948),(112,295939)]),([4,240,802,3780],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,296962),(58,295939),(61,295939),(73,296962)]),([4,240,810,3788],[(0,99331),(2,99331),(4,99331),(6,99331),(8,99331),(10,100354),(58,99331),(61,99331),(73,100354)]),([4,240,1826,2756],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,296962),(58,295939),(61,295939),(73,296962)]),([4,240,1834,2764],[(0,99331),(2,99331),(4,99331),(6,99331),(8,99331),(10,100354),(58,99331),(61,99331),(73,100354)]),([4,246,591,2184],[(0,8322),(2,1161),(4,8322),(6,132105),(8,8322),(10,8322),(73,139266),(78,8322),(82,139266)]),([4,255,590,2184],[(0,99336),(2,295945),(4,99336),(6,1128),(8,99336),(10,7266),(73,8482),(78,105474)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([4,255,591,708,802],[]),([4,255,708,719,802],[(104,303266)]),([4,255,708,756,802],[]),([4,255,740,802],[(0,165890),(2,165890),(4,165890),(6,2210),(8,165890),(10,1187),(57,165890),(73,165890),(78,164867)]),([4,255,756,802,2767],[(80,303234),(100,141315)]),([4,580,3983,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,301186),(85,301186),(86,296962)]),([4,591,628,802],[(0,296962),(2,133128),(4,296962),(6,2184),(8,296962),(10,1315),(73,7299),(78,138243)]),([4,591,802,3467],[(0,2184),(2,133128),(4,2184),(6,2184),(8,2184),(10,296962),(57,2184),(62,2184)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([4,719,756,802],[(0,296962),(2,133131),(4,296962),(6,2187),(8,296962),(10,1315),(73,10371),(78,139267)]),([4,752,815,870,2184],[]),([4,756,815,870,2191],[]),([4,756,2184,4018],[(0,133122),(2,133122),(4,133122),(6,133122),(8,133122),(10,132099),(57,133122),(62,133122),(85,133122)]),([4,2296,2764,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,295939)]),([5,2,15,112,580],[(0,302083),(2,302083),(4,302083),(6,296968),(8,302083),(10,301192),(12,302083),(14,2344),(58,302083),(61,302083),(73,302083),(74,302083),(81,302083),(82,302083),(97,138535),(98,302083)]),([5,2,15,240,708],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107)]),([5,2,15,580,3983],[(0,301192),(2,301192),(4,301192),(6,296968),(8,301192),(10,301192),(12,301192),(14,302083),(58,301192),(61,301192),(73,301192),(74,301192),(98,301192),(101,301192),(106,301192),(109,301192)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,2,15,2296,2764],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,303107),(12,303107),(14,100647),(58,303107),(61,303107),(73,303107),(74,303107),(97,100647),(98,303107)]),([5,2,128,255,580],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,296969),(12,303107),(14,2345),(57,303107),(58,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,8483),(98,303107),(105,8483),(106,303107)]),([5,2,143,240,580],[(0,303107),(2,303107),(4,303107),(6,138249),(8,303107),(10,7305),(12,303107),(14,2345),(58,303107),(61,303107),(73,303107),(74,303107),(97,139272),(98,303107)]),([5,6,240,591,2184],[(0,8327),(2,8327),(4,8327),(6,6281),(8,8327),(10,137225),(12,8327),(14,8327),(57,8327),(58,8327),(74,8327),(77,8327),(97,8327),(98,8327),(105,139271),(110,8327),(114,139271)]),([5,8,240,802,3788],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,295939),(12,295939),(14,296962),(57,295939),(58,295939),(73,295939),(74,295939),(82,295939),(85,295939),(98,295939),(101,295939),(105,296962)]),([5,8,240,1826,2764],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,295939),(12,295939),(14,296962),(57,295939),(58,295939),(73,295939),(74,295939),(82,295939),(85,295939),(98,295939),(101,295939),(105,296962)]),([5,10,255,580,2184],[(0,99336),(2,1128),(4,99336),(6,296969),(8,99336),(10,2345),(12,99336),(14,7266),(58,99336),(61,99336),(73,99336),(74,99336),(105,8483),(110,303107),(113,303107),(114,99336)]),([5,11,240,802,2764],[(0,303239),(2,303239),(4,303239),(6,303239),(8,303239),(10,1315),(12,303239),(14,137513),(57,303239),(58,303239),(73,296071),(82,303239),(98,303239),(105,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,12,240,580,802,3788],[(80,301058),(112,295947)]),([5,12,240,580,1826,2764],[(80,301058),(112,295948)]),([5,12,240,802,1604,2764],[(112,295948)]),([5,13,68,240,580,2184],[(56,295939),(80,296071),(104,295939),(136,296035)]),([5,13,128,240,580],[(0,295939),(2,296962),(4,295939),(6,295939),(8,295939),(10,301186),(12,295939),(14,2338),(57,295939),(58,295939),(73,295939),(74,295939),(82,295939),(85,295939),(105,132391),(106,295939)]),([5,13,240,512,580,2184],[(112,295939),(144,306179)]),([5,13,240,580,802,2764],[(80,141411),(112,296072)]),([5,13,240,580,1911],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(58,295939),(98,295939),(109,295939),(110,295939),(114,295939),(117,295939)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,13,240,580,2184],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(58,295939),(98,295939),(105,132391),(110,295939),(113,295939),(114,306275)]),([5,13,240,580,2189],[(0,295939),(2,295939),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(58,295939),(73,132391),(98,295939),(101,295939),(105,132391),(110,295939),(114,306179)]),([5,13,240,580,2191],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,139559),(98,303107),(101,303107),(105,139559),(110,295939),(114,295939)]),([5,13,240,580,2764],[(0,306275),(2,296962),(4,306275),(6,301186),(8,306275),(10,100652),(12,306275),(14,306275),(57,306275),(58,306275),(82,306275),(98,306179),(110,295939),(114,306275),(117,306275)]),([5,13,240,580,2764,3293],[(80,141411),(132,306275),(156,296035)]),([5,13,240,580,3208],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(58,295939),(98,295939),(105,132391),(110,295939),(113,295939),(114,305251)]),([5,13,240,2184,2764],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,295939),(12,295939),(14,100652),(57,295939),(58,295939),(81,295939),(82,295939),(114,295939),(117,295939)]),([5,13,240,2184,3515],[(0,2338),(2,296962),(4,2338),(6,301186),(8,2338),(10,2338),(12,2338),(14,295939),(57,2338),(58,2338),(74,2338),(81,2338),(86,2338),(114,2338),(117,2338)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,13,253,580,2184],[(0,295939),(2,295939),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(58,295939),(61,295939),(73,132387),(98,295939),(101,295939),(105,132391),(110,295939),(113,295939),(114,306275)]),([5,13,580,756,802,2184],[(56,141315),(136,141411)]),([5,13,580,756,2184,3293],[(56,141315),(104,141411)]),([5,13,580,2184,2296],[(0,132391),(2,296962),(4,132391),(6,2338),(8,132391),(10,132391),(12,132391),(14,301186),(74,132391),(81,295939),(82,132391),(98,132391),(114,132391),(117,132391)]),([5,13,580,2184,3855],[(0,301186),(2,296962),(4,301186),(6,301186),(8,301186),(10,301186),(12,301186),(14,295939),(74,301186),(81,301186),(82,301186),(98,301186),(101,301186),(113,295939),(114,301186)]),([5,15,48,580,802],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2345),(12,301058),(14,1319),(57,301058),(58,301058),(73,296962),(81,301058),(82,301058),(97,296962),(106,301058)]),([5,15,68,756,802,2184],[(56,141315),(136,141411)]),([5,15,68,756,2184,3293],[(56,141315),(104,141411)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,112,512,580,802],[(72,296962),(80,301058),(112,303107),(144,303107)]),([5,15,112,580,580,802],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271)]),([5,15,112,580,591,802],[(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271)]),([5,15,112,580,628,802],[(72,296962),(84,138243),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239)]),([5,15,112,580,756,802],[(72,296962),(108,303107),(116,303107),(152,302215)]),([5,15,112,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,302083),(106,303107),(114,303271)]),([5,15,112,580,802,870],[(128,296962),(148,303107),(152,303271),(156,303107)]),([5,15,112,580,802,1604],[(72,295939),(80,301058),(112,303271),(144,303107),(148,303107),(152,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,112,580,802,2764],[(80,301058),(112,303271),(148,303107)]),([5,15,112,580,802,3515],[(72,2338),(80,301058),(112,170281),(132,296962),(140,301058),(156,302083)]),([5,15,112,580,870],[(0,303271),(2,296968),(4,303271),(6,301192),(8,303271),(10,170281),(12,303271),(14,303271),(57,303271),(58,303271),(74,303271),(102,302215),(106,303239),(114,303271),(117,303271)]),([5,15,112,580,882],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,302083),(106,303107),(109,303107),(114,303239)]),([5,15,112,580,1010],[(0,302083),(2,302083),(4,302083),(6,301192),(8,302083),(10,2344),(12,302083),(14,302083),(57,302083),(58,302083),(73,296962),(97,296962),(102,302083),(106,302083),(109,302083),(114,302215)]),([5,15,112,580,1826],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,302083),(106,303107),(114,303271)]),([5,15,112,580,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,1315),(81,1319),(101,295939),(102,302083),(106,303107),(114,302083)]),([5,15,112,802,1604],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(57,303107),(58,303107),(73,295939),(82,303107),(97,295939),(105,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,112,802,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,303107),(57,2345),(58,2345),(73,2338),(78,2344),(82,2345),(101,137513),(109,2345),(117,2344)]),([5,15,119,580,802],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(73,105634),(81,301058),(102,302083),(110,302083),(114,303271)]),([5,15,127,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(61,303107),(81,301058),(101,303107),(102,302083),(110,302083),(114,303271)]),([5,15,128,240,514,580],[(56,139272),(152,303106)]),([5,15,128,240,582],[(0,303106),(2,295945),(4,303106),(6,303106),(8,303106),(10,301193),(12,303106),(14,1321),(57,303106),(58,303106),(73,303106),(74,303106),(82,303106),(85,303106),(105,139559),(106,303106)]),([5,15,128,242,580],[(0,303107),(2,132105),(4,303107),(6,303107),(8,303107),(10,1161),(12,303107),(14,2345),(57,303107),(58,303107),(82,303107),(85,303107),(105,139266),(106,303107)]),([5,15,128,756,802,870],[(56,141320),(104,170120),(128,10371)]),([5,15,130,240,580],[(0,303107),(2,296969),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(57,303107),(73,303107),(74,303107),(82,303107),(105,139559),(106,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,192,580,756,802],[(56,141320),(72,296962),(80,301058),(112,141315),(144,10403)]),([5,15,192,756,802],[(0,141315),(2,133131),(4,141315),(6,141315),(8,141315),(10,2187),(12,141315),(14,141315),(57,141315),(58,141315),(82,141315),(85,141315),(97,10371),(102,139267),(105,141315),(106,141315),(114,10371)]),([5,15,240,307,580,802],[(84,301058),(104,301058),(152,305154)]),([5,15,240,512,582,2184],[(112,303106),(144,306178)]),([5,15,240,512,708,802],[(72,296962),(80,301058),(112,303107),(144,303107)]),([5,15,240,512,870,2764],[(112,303240),(144,303240)]),([5,15,240,514,580,1911],[(112,303106)]),([5,15,240,514,580,2184],[(112,303106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,514,580,2191],[(112,303106)]),([5,15,240,514,580,2698],[(80,301192),(112,306179)]),([5,15,240,514,580,2764],[(104,139363),(112,306178)]),([5,15,240,514,580,2767],[(104,139267),(112,306178)]),([5,15,240,514,580,3208],[(112,303106)]),([5,15,240,514,2184,2764],[(144,303106)]),([5,15,240,514,2184,3515],[]),([5,15,240,516,802,2764],[(80,301058),(112,303239)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,544,870,2184],[(144,170120)]),([5,15,240,546,580,2184],[]),([5,15,240,580,628,802],[(72,296962),(84,138243),(96,296962),(108,303107),(152,138242)]),([5,15,240,580,640,802],[(96,296962),(112,303107)]),([5,15,240,580,704,802],[(80,301058),(96,296962),(112,303107),(144,303240)]),([5,15,240,580,708,802],[(72,296962),(80,301058),(96,296962),(112,303107),(144,303240)]),([5,15,240,580,708,930],[(72,296962),(96,296962),(112,303107),(144,303271)]),([5,15,240,580,708,1826],[(72,296962),(80,301058),(96,296962),(112,303107),(144,303240)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,708,3293],[(72,1315),(80,1319),(96,1315),(112,303107),(132,132391),(144,305155)]),([5,15,240,580,716,802],[(80,301058),(96,296962),(144,303240)]),([5,15,240,580,719,802],[(80,301058),(96,296962),(144,303240)]),([5,15,240,580,754,2184],[]),([5,15,240,580,770,2764],[(80,301058),(112,303240)]),([5,15,240,580,802,998],[(128,10376)]),([5,15,240,580,802,1041,2184],[]),([5,15,240,580,802,1328],[(80,301058),(112,138537),(140,301058),(152,138242)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,802,1331],[(80,301058),(112,138537),(140,301058)]),([5,15,240,580,802,1343],[(80,301058),(112,138537),(140,301058)]),([5,15,240,580,802,1399],[(140,303107)]),([5,15,240,580,802,1732],[(72,295939),(80,301058),(112,303240),(144,303107)]),([5,15,240,580,802,1911,3225],[]),([5,15,240,580,802,2696],[]),([5,15,240,580,802,2698],[]),([5,15,240,580,802,2700],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,802,2703],[]),([5,15,240,580,802,2752],[(80,301058),(112,303240),(144,303107)]),([5,15,240,580,802,2756],[(72,295939),(80,301058),(112,303240),(144,303107)]),([5,15,240,580,802,2760],[(80,301058),(112,303240)]),([5,15,240,580,802,2764],[(80,301058),(112,303240)]),([5,15,240,580,802,2766],[(80,301154),(112,303240)]),([5,15,240,580,802,2767],[(80,301058),(112,303240)]),([5,15,240,580,802,3387],[(72,2338),(80,301058),(112,138537),(140,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,802,3467],[(72,2184),(84,2184)]),([5,15,240,580,802,3720],[]),([5,15,240,580,802,3788],[(80,301058),(112,303240)]),([5,15,240,580,802,3791],[(80,301058),(112,303240)]),([5,15,240,580,870,930],[(80,170120),(96,296962)]),([5,15,240,580,870,2696],[(72,296072),(144,303240)]),([5,15,240,580,882],[(0,138242),(2,138242),(4,138242),(6,301193),(8,138242),(10,2345),(12,138242),(14,1160),(57,138242),(58,138242),(73,138242),(97,296962),(109,303107),(114,138242)]),([5,15,240,580,930,2764],[(112,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,1010,2696],[]),([5,15,240,580,1331,1826],[(80,301058),(108,301058),(144,306178)]),([5,15,240,580,1331,3293],[(80,1319),(108,1319),(132,306275)]),([5,15,240,580,1826,2696],[]),([5,15,240,580,1826,2764],[(80,301058),(112,303240)]),([5,15,240,580,1826,2767],[(80,301058),(112,303240)]),([5,15,240,580,1906],[(0,138242),(2,138242),(4,138242),(6,301193),(8,138242),(10,2345),(12,138242),(14,1160),(57,138242),(58,138242),(73,138242),(97,296962),(109,303107),(114,138242)]),([5,15,240,580,2184,2698],[(144,303106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,2184,3581],[(132,295939)]),([5,15,240,580,2189],[(0,1160),(2,1160),(4,1160),(6,301193),(8,1160),(10,2345),(12,1160),(14,138242),(57,1160),(58,1160),(73,1160),(101,295939),(105,139559),(114,1160)]),([5,15,240,580,2269,2764],[(80,1319),(100,306275),(104,1319)]),([5,15,240,580,2696,3293],[(132,306179)]),([5,15,240,580,2764,3293],[(80,1319),(132,306275)]),([5,15,240,580,2764,3325],[(80,1319),(132,306275)]),([5,15,240,580,2767,3293],[(80,1319),(132,295939),(156,1160)]),([5,15,240,580,3213],[(0,1160),(2,1160),(4,1160),(6,301193),(8,1160),(10,2345),(12,1160),(14,138242),(57,1160),(58,1160),(73,1160),(101,295939),(105,139559),(114,1160)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,580,3293,3788],[(80,1319),(100,305251),(104,1319)]),([5,15,240,582,802,2764],[(80,141411),(112,303240)]),([5,15,240,582,1911],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(57,303106),(58,303106),(98,303106),(109,303106),(110,303106),(114,303106),(117,303106)]),([5,15,240,582,2184],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(57,303106),(58,303106),(98,303106),(105,139559),(110,303106),(113,303106),(114,306274)]),([5,15,240,582,2186],[(0,303107),(2,296969),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(98,303106),(105,139559),(110,303106),(114,306274)]),([5,15,240,582,2191],[(0,303106),(2,303106),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(57,303106),(58,303106),(73,139559),(98,303106),(101,303106),(105,139559),(110,303106),(114,306178)]),([5,15,240,582,2764],[(0,306178),(2,296969),(4,306178),(6,301193),(8,306178),(10,1324),(12,306178),(14,306178),(57,306178),(58,306178),(82,306178),(98,306178),(110,303106),(114,306274)]),([5,15,240,582,2766],[(0,306274),(2,295945),(4,306274),(6,301193),(8,306274),(10,99628),(12,306274),(14,306274),(57,306274),(58,306274),(82,306274),(98,306178),(110,303106),(114,306274),(117,306274)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,582,3208],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(57,303106),(58,303106),(98,303106),(105,139559),(110,303106),(113,303106),(114,305250)]),([5,15,240,590,2184],[(0,99464),(2,295945),(4,99464),(6,301193),(8,99464),(10,1321),(12,99464),(14,138338),(57,99464),(58,99464),(97,8482),(105,139559),(113,303106)]),([5,15,240,591,708,802],[(72,296962),(76,303107),(80,301058)]),([5,15,240,612,802,2764],[(80,301058),(112,303240)]),([5,15,240,708,708,802],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271)]),([5,15,240,708,719,802],[(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271)]),([5,15,240,708,756,802],[(72,296962),(84,141315),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239)]),([5,15,240,708,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,708,802,998],[(128,296962),(148,303107),(152,303271),(156,303107)]),([5,15,240,708,802,1604],[(72,295939),(144,303107),(152,303240)]),([5,15,240,708,802,1732],[(72,295939),(80,301058),(112,303271),(144,303107),(148,303107),(152,303271)]),([5,15,240,708,802,2764],[(80,301058),(112,303271),(148,303107)]),([5,15,240,708,802,3387],[(72,2338),(80,301058),(112,170281),(132,296962),(140,301058),(156,305155)]),([5,15,240,708,802,3515],[(72,2338),(132,296962),(140,301058),(156,305155)]),([5,15,240,708,870],[(0,303240),(2,296971),(4,303240),(6,301195),(8,303240),(10,138537),(12,303240),(14,303240),(57,303240),(58,303240),(74,303240),(102,303239),(106,303239),(114,303271)]),([5,15,240,708,930],[(0,303107),(2,303107),(4,303107),(6,302219),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(114,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,708,998],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(114,303271),(117,303271)]),([5,15,240,708,1010],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239)]),([5,15,240,708,1826],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271)]),([5,15,240,708,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,1315),(81,1319),(101,295939),(102,303107),(106,303107),(114,305155)]),([5,15,240,740,802],[(0,169986),(2,169986),(4,169986),(6,169986),(8,169986),(10,2345),(12,169986),(14,1191),(57,169986),(58,169986),(73,169986),(81,169986),(97,296962),(105,170121)]),([5,15,240,756,802,1331],[(56,164963),(80,301058),(112,137513),(140,301058)]),([5,15,240,756,802,2764],[(56,164963),(80,301058),(112,303239),(140,141315),(148,303107)]),([5,15,240,756,802,2767],[(80,301058),(112,303239),(140,141315),(148,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,756,802,3788],[(56,164963),(80,301058),(112,303239),(140,141315),(148,303107)]),([5,15,240,756,1010,2764],[(56,132195),(112,303239),(140,139267),(148,303107)]),([5,15,240,756,1826,2764],[(56,164963),(80,301058),(112,303239),(140,142339),(148,303107)]),([5,15,240,756,2764,3293],[(56,164963),(80,1319),(108,141315),(116,303107),(132,306275),(136,1319)]),([5,15,240,802,1041,2184,2764],[]),([5,15,240,802,1331,1604],[(108,303107),(144,306178)]),([5,15,240,802,1331,3515],[(108,2345),(132,137513)]),([5,15,240,802,1604,2696],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,802,1604,2764],[(112,303240)]),([5,15,240,802,1604,2767],[(112,303240)]),([5,15,240,802,1732],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(57,303107),(58,303107),(73,295939),(82,303107),(97,295939),(105,301058)]),([5,15,240,802,1780,2764],[(56,164963),(112,303239),(156,303107)]),([5,15,240,802,2491,2764],[(100,303239)]),([5,15,240,802,2696,3515],[]),([5,15,240,802,2756],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1324),(12,303107),(14,2345),(57,303107),(58,303107),(73,295939),(82,303107),(97,295939),(105,301058)]),([5,15,240,802,2764,3339],[(56,100514),(108,2187),(132,303239)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,802,2764,3515],[(132,303239)]),([5,15,240,802,2764,3579],[(132,303239)]),([5,15,240,802,2767,3515],[(132,303239)]),([5,15,240,802,3387],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(101,137513),(109,2345),(117,2347)]),([5,15,240,802,3515,3788],[(100,303239)]),([5,15,240,806,2764],[(0,303239),(2,296971),(4,303239),(6,303239),(8,303239),(10,1324),(12,303239),(14,137513),(57,303239),(58,303239),(82,303239),(98,303239),(105,301058)]),([5,15,240,810,2764],[(0,99331),(2,99331),(4,99331),(6,99331),(8,99331),(10,1123),(12,99331),(14,2146),(57,99331),(58,99331),(73,99331),(82,99331),(97,99331),(105,100354)]),([5,15,240,870,1331],[(0,138537),(2,296971),(4,138537),(6,301195),(8,138537),(10,1324),(12,138537),(14,303240),(57,138537),(58,138537),(82,137513),(98,138537)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,870,2764],[(0,303240),(2,296971),(4,303240),(6,301195),(8,303240),(10,1324),(12,303240),(14,138537),(57,303240),(58,303240),(82,303239),(98,303240)]),([5,15,240,870,2764,2986],[(72,100354),(104,170120)]),([5,15,240,870,2767],[(0,303240),(2,295948),(4,303240),(6,301195),(8,303240),(10,1324),(12,303240),(14,138537),(57,303240),(58,303240),(82,303239),(98,303240),(101,303240),(117,306178)]),([5,15,240,870,3788],[(0,303240),(2,297067),(4,303240),(6,301225),(8,303240),(10,303240),(12,303240),(14,305154),(57,303240),(58,303240),(82,303239),(85,303240),(98,303240),(101,295947)]),([5,15,240,1014,2764],[(0,303239),(2,296971),(4,303239),(6,301193),(8,303239),(10,1324),(12,303239),(14,137513),(57,303239),(58,303239),(82,303239),(85,303239),(98,303239),(118,303239)]),([5,15,240,1604,2764,3293],[(132,305288),(136,1319)]),([5,15,240,1826,2764,3515],[(132,303239)]),([5,15,240,1894,2764],[(0,303240),(2,297068),(4,303240),(6,301225),(8,303240),(10,303240),(12,303240),(14,306178),(57,303240),(58,303240),(82,303239),(85,303240),(98,303240),(101,295948)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,2184,2766],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,303106),(12,303106),(14,99628),(57,303106),(58,303106),(81,303106),(82,303106),(114,303106),(117,303106)]),([5,15,240,2184,3513],[(0,1321),(2,295945),(4,1321),(6,301193),(8,1321),(10,1321),(12,1321),(14,303106),(57,1321),(58,1321),(74,1321),(81,1321),(86,1321),(114,1321),(117,1321)]),([5,15,240,2186,2764],[(0,99331),(2,296969),(4,99331),(6,301193),(8,99331),(10,99331),(12,99331),(14,100354),(57,99331),(58,99331),(81,99331),(82,99331)]),([5,15,240,2764,3225],[(0,1324),(2,296971),(4,1324),(6,301195),(8,1324),(10,1324),(12,1324),(14,303240),(57,1324),(58,1324),(74,1324),(106,1324)]),([5,15,240,2764,3293,3515],[(100,100652),(132,1315),(156,1324)]),([5,15,242,580,1911],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345),(12,303107),(14,303107),(98,303107),(109,303107),(110,303107),(114,303107),(117,303107)]),([5,15,242,580,2184],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345),(12,303107),(14,303107),(98,303107),(105,139266),(110,303107),(113,303107),(114,306275)]),([5,15,242,580,2186],[(0,303107),(2,296969),(4,303107),(6,99465),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(98,303107),(110,303107),(113,303107),(114,306275)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,242,580,2191],[(0,303107),(2,303107),(4,303107),(6,1161),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(73,139266),(98,303107),(101,303107),(110,303107),(114,306179)]),([5,15,242,580,2764],[(0,306275),(2,132105),(4,306275),(6,1161),(8,306275),(10,100652),(12,306275),(14,306275),(82,306275),(98,306179),(110,303107),(114,306275),(117,306275)]),([5,15,242,580,3208],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345),(12,303107),(14,303107),(98,303107),(105,139266),(110,303107),(113,303107),(114,305251)]),([5,15,242,582,2184],[(0,303107),(2,296969),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303106),(98,303107),(105,139559),(110,303107),(113,303107),(114,306275)]),([5,15,242,2184,2764],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,303107),(12,303107),(14,100652),(81,303107),(82,303107),(114,303107),(117,303107)]),([5,15,242,2184,3515],[(0,2345),(2,132105),(4,2345),(6,1161),(8,2345),(10,2345),(12,2345),(14,303107),(74,2345),(81,2345),(86,2345),(114,2345),(117,2345)]),([5,15,244,580,802,2764],[(72,296072),(80,301058),(112,303240),(144,303239)]),([5,15,244,802,2764],[(0,303239),(2,303239),(4,303239),(6,100491),(8,303239),(10,1324),(12,303239),(14,137513),(57,303235),(73,296071),(82,303239),(98,303239)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,246,580,2184],[(0,303239),(2,132105),(4,303239),(6,1161),(8,303239),(10,137513),(12,303239),(14,303239),(73,8322),(74,303239),(98,303239),(105,139266),(110,303239),(113,303239),(114,139266)]),([5,15,248,580,802,2764],[(112,303240),(144,303107)]),([5,15,248,802,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1324),(12,303107),(14,2345),(73,295939),(82,303107)]),([5,15,250,580,2184],[(0,99464),(2,132105),(4,99464),(6,1161),(8,99464),(10,2345),(12,99464),(14,138338),(105,139266),(110,303107),(113,303107),(114,99464)]),([5,15,252,580,802,2764],[(112,303240)]),([5,15,253,580,2184],[(0,303107),(2,303107),(4,303107),(6,301058),(8,303107),(10,2345),(12,303107),(14,303107),(61,295939),(73,295939),(98,303107),(101,295939),(105,1319),(110,303107),(113,303107),(114,306275)]),([5,15,255,514,580,2184],[(112,303106)]),([5,15,255,580,708,802],[(80,301058),(112,303107),(132,8483),(144,303240)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,255,580,802,2767],[(112,303240)]),([5,15,255,582,2184],[(0,303106),(2,303106),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(58,303106),(61,303106),(73,139554),(98,303106),(101,303106),(105,139559),(110,303106),(113,303106),(114,306274)]),([5,15,255,708,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(61,303107),(81,301058),(101,303107),(102,303107),(110,303107),(114,303271)]),([5,15,255,756,802,2764],[(56,164963),(60,301058),(84,303239),(100,306275),(112,303239),(140,141411),(148,303107)]),([5,15,255,870,2764],[(0,303240),(2,164968),(4,303240),(6,301195),(8,303240),(10,1324),(12,303240),(14,138537),(58,303240),(61,303240),(98,303240)]),([5,15,512,580,802,3983],[(56,296962),(80,303107),(104,303107),(136,303107)]),([5,15,512,802,2296,2764],[(56,295939),(80,303107),(104,301058),(136,303107)]),([5,15,514,580,754,2184],[(56,139266),(136,301192)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,514,580,2184,2296],[(80,139559)]),([5,15,514,580,2184,3855],[(80,301193)]),([5,15,516,580,802,3983],[(56,296962),(72,6280),(80,303107),(104,303239),(136,303107),(144,303107)]),([5,15,516,802,2764,3855],[(80,303239),(152,303107)]),([5,15,544,580,802,3208],[(80,169986),(136,172168)]),([5,15,544,580,1826,2184],[(80,169986),(136,172168)]),([5,15,544,756,870,2184],[(136,170120)]),([5,15,544,802,1604,2184],[(104,172035),(136,172168)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,544,870,1024,2184],[(104,170123),(136,170120)]),([5,15,580,580,802,3983],[(56,296962),(64,303107),(68,303107),(104,301192),(136,301058)]),([5,15,580,591,802,3983],[(72,296962),(76,303107),(84,303107),(104,301192),(128,296962),(144,301058)]),([5,15,580,628,802],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962)]),([5,15,580,708,802,3855],[(56,296962),(72,7307),(80,303107),(104,301195),(136,301058),(144,301058)]),([5,15,580,752,802,2696],[]),([5,15,580,756,802,930],[(56,141315),(96,296962),(104,170120),(128,10376)]),([5,15,580,756,802,2248],[(56,296962),(80,141315),(104,10403),(136,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,756,802,2696],[(56,141315),(136,301058)]),([5,15,580,756,802,3983],[(56,296962),(84,303107),(112,301192),(136,301058)]),([5,15,580,770,2764,3855],[(80,301195),(152,301058)]),([5,15,580,770,3208],[(0,301058),(2,301058),(4,301058),(6,2345),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,296962),(105,303107),(106,301058),(113,301058),(114,303107)]),([5,15,580,770,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,296962),(73,296962),(78,301192),(82,301192),(98,303107),(101,303107),(106,301058),(114,303107),(117,303107)]),([5,15,580,802,870,3983],[(96,296962),(108,303107),(112,301192),(116,303107)]),([5,15,580,802,1264,3788],[(80,303240),(104,172131)]),([5,15,580,802,1331,2296],[(80,141607),(156,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,802,1331,3855],[(80,301195)]),([5,15,580,802,1604,3983],[(56,295939),(80,301192),(104,303107),(108,303107),(112,301192),(136,303107),(152,301058)]),([5,15,580,802,1799,2764],[(80,303240),(104,303107),(136,303107),(152,301058)]),([5,15,580,802,2296,2696],[(136,303107)]),([5,15,580,802,2296,2764],[(80,303240),(136,303107)]),([5,15,580,802,2296,2767],[(80,303240)]),([5,15,580,802,2296,3054],[]),([5,15,580,802,2296,3788],[(80,303240),(136,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,802,2303,2767],[(80,303240)]),([5,15,580,802,2696,2808],[(104,301058)]),([5,15,580,802,2696,3855],[(152,303107)]),([5,15,580,802,2700,3855],[(152,303107)]),([5,15,580,802,2764,3855],[(80,301195),(152,301058)]),([5,15,580,802,2764,3983],[(80,301195),(108,303107),(152,301058)]),([5,15,580,802,2767,3855],[(80,301195),(152,301058)]),([5,15,580,802,2812,2986],[(56,100488),(72,296962),(80,170120)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,802,2812,3054],[]),([5,15,580,802,3240],[(0,172168),(2,172168),(4,172168),(6,2345),(8,172168),(10,1192),(12,172168),(14,138409),(57,172168),(73,165000),(98,172168),(101,164872),(105,303107),(106,172168)]),([5,15,580,802,3320,3788],[(80,303240),(136,303107)]),([5,15,580,802,3467],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(58,2184),(73,296962),(98,301058),(101,296962),(105,2345),(106,301058)]),([5,15,580,802,3515,3983],[(56,2338),(80,301192),(100,296962),(116,301192),(136,2345),(156,301058)]),([5,15,580,802,3788,3855],[(80,301225),(148,301058),(152,301058)]),([5,15,580,802,3976],[(0,303107),(2,164968),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,105634),(78,301192),(82,301192),(98,303107),(106,301058),(113,99496)]),([5,15,580,802,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,296962),(73,296962),(78,301192),(82,301192),(98,303107),(101,303107),(106,301058),(117,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,802,4047],[(0,301058),(2,301058),(4,301058),(6,2345),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,301058),(106,301058),(109,301058),(117,301058)]),([5,15,580,870,2296,2986],[(72,296962),(104,170120)]),([5,15,580,870,3983],[(0,301192),(2,296968),(4,301192),(6,301192),(8,301192),(10,301192),(12,301192),(14,303271),(58,301192),(78,301192),(82,301192),(85,301192),(98,301192),(101,301192),(117,303239)]),([5,15,580,1010,3983],[(0,301192),(2,301192),(4,301192),(6,301192),(8,301192),(10,301192),(12,301192),(14,302083),(57,301192),(73,301186),(78,301192),(82,301192),(98,301192),(101,301192),(117,302083),(118,301192)]),([5,15,580,1794,2184],[(0,301058),(2,301058),(4,301058),(6,2345),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,296962),(105,303107),(106,301058),(113,301058),(114,303107)]),([5,15,580,1826,2216],[(0,172168),(2,172168),(4,172168),(6,2345),(8,172168),(10,1192),(12,172168),(14,138409),(57,172168),(73,165000),(98,172168),(101,164872),(105,303107),(106,172168)]),([5,15,580,1826,2296,2764],[(80,303240),(136,303107)]),([5,15,580,1826,2764,3855],[(80,301225),(148,301058),(152,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,1826,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,296962),(73,296962),(78,301192),(82,301192),(98,303107),(101,303107),(106,301058),(117,303107)]),([5,15,580,2184,2298],[(0,139266),(2,132105),(4,139266),(6,2345),(8,139266),(10,139266),(12,139266),(14,99464),(81,303107),(82,99464),(114,139266),(117,139266)]),([5,15,580,2184,2301],[(0,1319),(2,1319),(4,1319),(6,2345),(8,1319),(10,1319),(12,1319),(14,301058),(57,1315),(74,1319),(77,1315),(81,303107),(82,1319),(101,132391),(114,1319),(117,1319)]),([5,15,580,2184,3853],[(0,1161),(2,132105),(4,1161),(6,1161),(8,1161),(10,1161),(12,1161),(14,303107),(74,1161),(81,1161),(82,1161),(113,303107),(114,1161)]),([5,15,580,2186,2296],[(0,99623),(2,296969),(4,99623),(6,2345),(8,99623),(10,99623),(12,99623),(14,301154),(81,303107),(82,99623)]),([5,15,580,2296,2764,2986],[(56,104450),(104,303107),(136,303271)]),([5,15,580,2296,2764,3293],[(104,303107),(132,132391),(136,305155)]),([5,15,580,2764,3293,3855],[(100,301186),(144,1319)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,580,3208,3325],[(0,1319),(2,1319),(4,1319),(6,2345),(8,1319),(10,1319),(12,1319),(14,301058),(57,1315),(74,1319),(77,1315),(81,303107),(82,1319),(101,132391),(114,1319),(117,1319)]),([5,15,580,3293,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,1315),(77,295939),(78,301192),(82,301192),(98,303107),(101,303107),(106,1319),(117,301193)]),([5,15,582,756,802,2184],[(56,296962),(136,301154)]),([5,15,582,2184,2296],[(0,139559),(2,295945),(4,139559),(6,1321),(8,139559),(10,139559),(12,139559),(14,301193),(74,139559),(81,303106),(82,139559),(98,139559),(114,139559),(117,139559)]),([5,15,582,2184,3855],[(0,301193),(2,295945),(4,301193),(6,301193),(8,301193),(10,301193),(12,301193),(14,303106),(74,301193),(81,301193),(82,301193),(98,301193),(101,301193),(113,303106),(114,301193)]),([5,15,591,802,2296,2764],[(60,303107)]),([5,15,612,802,3208],[(0,169986),(2,169986),(4,169986),(6,2217),(8,169986),(10,1191),(12,169986),(14,169986),(57,165890),(73,165890),(98,169986),(101,165890),(105,172035),(106,169986),(113,169986),(114,172035)]),([5,15,612,1826,2184],[(0,169986),(2,169986),(4,169986),(6,2217),(8,169986),(10,1191),(12,169986),(14,169986),(57,165890),(73,165890),(98,169986),(101,165890),(105,172035),(106,169986),(113,169986),(114,172035)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,708,756,802],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962)]),([5,15,708,802,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(101,303107),(106,301058),(117,303107)]),([5,15,752,802,870,2184],[(144,170120)]),([5,15,756,802,870,1911],[(96,10371)]),([5,15,756,802,870,2184],[(96,10371),(144,170120),(152,170082)]),([5,15,756,802,870,2191],[(96,11399),(144,170120),(152,169986)]),([5,15,756,802,870,2764],[(96,296962),(116,301058),(152,170082)]),([5,15,756,802,870,2986],[(72,166024),(96,10371),(112,170120),(144,170120),(152,170082)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,756,802,870,3054],[(96,165986),(116,170082),(152,170082)]),([5,15,756,802,870,3208],[(96,108675),(108,169986),(144,170120),(152,170082)]),([5,15,756,802,1014,2764],[(96,296962),(108,301058),(116,301058),(156,301058)]),([5,15,756,802,1331],[(0,301058),(2,301058),(4,301058),(6,100491),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(110,301058),(114,141411)]),([5,15,756,802,1894,2184],[(144,170120),(152,170082)]),([5,15,756,802,2184,3054],[(152,170082)]),([5,15,756,802,2184,3225],[(112,99496)]),([5,15,756,802,2184,4027],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,756,802,2248],[(0,141315),(2,133131),(4,141315),(6,2187),(8,141315),(10,141315),(12,141315),(14,141315),(73,10371),(78,139267),(82,10371),(98,141315),(105,141315),(110,141315),(113,99495),(114,170082)]),([5,15,756,802,2296,2764],[(80,303239),(156,141315)]),([5,15,756,802,2764],[(0,301058),(2,301058),(4,301058),(6,100491),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(110,301058),(114,170082)]),([5,15,756,802,2764,2986],[(72,296962),(148,301058),(152,170082)]),([5,15,756,802,2764,3855],[(80,301193),(108,303107),(132,301058),(148,301058),(152,301058)]),([5,15,756,802,2767],[(0,301058),(2,301058),(4,301058),(6,2187),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,301058),(110,301058),(114,169986),(117,139267)]),([5,15,756,802,3054],[(0,170082),(2,170082),(4,170082),(6,100491),(8,170082),(10,99495),(12,170082),(14,170082),(57,165986),(73,165986),(98,169986),(110,169986),(114,170082),(117,170082)]),([5,15,756,802,3788],[(0,301058),(2,301058),(4,301058),(6,100521),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,301058),(110,301058),(114,170082)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,756,815,870,2184],[(144,170120)]),([5,15,756,870,1826,2184],[(72,165890),(84,169986),(144,170082),(152,170120)]),([5,15,756,870,2184,2986],[(72,165890),(104,170120),(152,170120)]),([5,15,756,870,2184,3293],[(72,1187),(112,99495)]),([5,15,756,870,2986],[(0,170120),(2,170120),(4,170120),(6,170120),(8,170120),(10,99496),(12,170120),(14,138407),(57,166024),(58,170120),(73,166024),(98,170120),(110,171010)]),([5,15,756,1826,1894,2184],[(96,109699),(108,169986),(144,170120),(152,170082)]),([5,15,756,1826,2764],[(0,301058),(2,301058),(4,301058),(6,100521),(8,301058),(10,1319),(12,301058),(14,301058),(57,296962),(73,296962),(98,301058),(101,301058),(110,301058),(114,170082)]),([5,15,756,2764,3293],[(0,1319),(2,1319),(4,1319),(6,100491),(8,1319),(10,1319),(12,1319),(14,301058),(57,1315),(74,1319),(86,1319),(101,141411),(117,141411)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,770,1604,2184],[(0,303107),(2,303107),(4,303107),(6,1319),(8,303107),(10,2345),(12,303107),(14,303107),(57,295939),(73,295939),(98,303107),(101,295939),(105,301058),(106,303107),(113,303107),(114,301058)]),([5,15,802,870,2184,2812],[(72,141315),(104,170120)]),([5,15,802,870,2184,3339],[(72,2187),(104,170120),(112,100491)]),([5,15,802,870,2764,2812],[]),([5,15,802,1264,1604,2764],[]),([5,15,802,1264,1604,3788],[(104,303240),(112,172131)]),([5,15,802,1331,2296],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,303107),(12,2345),(14,2345),(57,2338),(62,100647),(85,100647),(105,139559)]),([5,15,802,1331,2296,2764],[(84,305155),(136,100647)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,802,1604,2216],[(0,172168),(2,172168),(4,172168),(6,1192),(8,172168),(10,2345),(12,172168),(14,138409),(57,165000),(73,172168),(98,172168),(101,164872),(113,303107),(114,172168)]),([5,15,802,1604,2296,2764],[(80,303240),(144,303107)]),([5,15,802,1604,2764,3855],[(80,301225),(140,301058),(152,303107)]),([5,15,802,1604,3983],[(0,303107),(2,303107),(4,303107),(6,1323),(8,303107),(10,2345),(12,303107),(14,303107),(57,295939),(73,295939),(98,303107),(101,303107),(109,303107),(114,303107)]),([5,15,802,1636,2184],[(0,172035),(2,172035),(4,172035),(6,1191),(8,172035),(10,2217),(12,172035),(14,172035),(57,164867),(73,164867),(98,172035),(101,164867),(105,169986),(106,172035),(113,172035),(114,169986)]),([5,15,802,1780,1894,2184],[(96,109699),(116,172035),(136,170120),(152,172131)]),([5,15,802,1780,3788],[(0,172131),(2,172131),(4,172131),(6,1319),(8,172131),(10,100521),(12,172131),(14,172131),(57,164963),(73,164963),(98,172035),(101,164963),(106,172131),(118,301058)]),([5,15,802,1799,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(57,295939),(62,303107),(85,303107),(105,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,802,2184,2812,3054],[]),([5,15,802,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(57,295939),(62,303107),(81,303107),(105,303271)]),([5,15,802,2296,2764,2764],[(104,303271),(120,303107),(124,303107)]),([5,15,802,2296,2764,2767],[(104,303271),(132,303107),(156,303107)]),([5,15,802,2296,2764,2812],[(116,141315),(136,303239),(148,303107),(156,303107)]),([5,15,802,2296,2764,3054],[(136,303271),(140,303107),(156,303107)]),([5,15,802,2296,2764,3515],[(132,303239),(140,305155),(148,303107)]),([5,15,802,2296,2764,3788],[(100,295947),(104,303271),(136,303271),(152,303107),(156,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,802,2296,3788],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,305154),(57,295939),(77,295939),(81,303107),(101,295947)]),([5,15,802,2764,2812,2986],[(56,100354)]),([5,15,802,2764,3339],[(0,100491),(2,100491),(4,100491),(6,100491),(8,100491),(10,100491),(12,100491),(14,301058),(57,100491),(74,2187),(82,100491),(101,296962),(113,2345)]),([5,15,802,2764,3515,3855],[(100,303239),(144,2345),(156,100491)]),([5,15,802,3320,3788],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(57,295939),(62,303107),(77,295939),(81,303107),(101,296071),(105,303271)]),([5,15,802,3515,3983],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,303107),(12,2345),(14,2345),(57,2338),(62,301192),(77,137513),(85,301192),(98,2345),(101,2345),(109,2345),(118,301058)]),([5,15,870,2296,2764],[(0,303240),(2,296971),(4,303240),(6,303240),(8,303240),(10,303240),(12,303240),(14,141607),(62,303239),(74,303240),(81,303239),(98,303240),(105,303271)]),([5,15,870,2764,3855],[(0,301195),(2,296971),(4,301195),(6,301195),(8,301195),(10,301195),(12,301195),(14,303240),(74,301195),(98,301195),(101,301195),(109,303239)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,1010,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,100647),(57,295939),(62,303107),(81,303107),(105,303239)]),([5,15,1604,2184,3325],[(0,1319),(2,1319),(4,1319),(6,1319),(8,1319),(10,1319),(12,1319),(14,303107),(57,1315),(74,1319),(77,1315),(81,303107),(82,1319),(101,132391),(114,1319),(117,1319)]),([5,15,1826,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(57,295939),(62,303107),(77,295939),(81,303107),(101,296071),(105,303271)]),([5,15,2296,2764,2986],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,141608),(12,303107),(14,303107),(58,100354),(102,303107),(106,303107),(114,303271)]),([5,15,2296,2764,3054],[(0,303271),(2,296971),(4,303271),(6,303271),(8,303271),(10,100647),(12,303271),(14,303271),(74,303271),(102,303239),(106,303239),(114,303271),(117,303271)]),([5,15,2296,2764,3066],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,139559),(12,303107),(14,303107),(58,100354),(102,303107),(106,303107),(109,303107),(114,303239)]),([5,15,2296,2764,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(101,295939),(102,303107),(106,303107),(114,305155)]),([5,47,240,580,802,2764],[(80,301058),(112,303240)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([5,77,240,580,2184],[(0,295939),(2,296962),(4,295939),(6,295939),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(58,295939),(81,1315),(82,295939),(98,295939),(105,295939),(110,295939),(113,295939),(114,306275)]),([5,79,240,580,802,2764],[(80,302082),(112,303240)]),([5,79,580,756,802,2184],[(56,296962),(80,141315),(104,10403),(136,302082)]),([5,79,756,802,2184],[(0,141315),(2,133131),(4,141315),(6,2187),(8,141315),(10,141315),(12,141315),(14,141315),(73,10371),(78,139267),(82,10371),(98,141315),(105,141315),(110,141315),(113,99496),(114,171106)]),([5,112,127,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(61,303107),(81,296962),(98,303107),(101,303107),(105,296962),(110,302083),(114,303271)]),([5,112,580,591,802],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939)]),([5,112,580,802,815],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(98,296962),(106,296962),(114,296962),(117,296962)]),([5,112,580,802,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,301058),(74,303107),(82,296968),(98,303107),(101,303107),(106,296962),(113,302083),(114,295939)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([5,127,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(62,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303271)]),([5,128,240,580,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(58,296962),(61,296962),(73,296962),(74,296962),(98,296962),(101,296962),(106,296962),(109,296962)]),([5,128,255,580,591,802],[(144,303266)]),([5,128,255,580,756,802],[]),([5,128,591,756,802],[(0,296962),(2,296962),(4,296962),(6,133131),(8,296962),(10,2187),(12,296962),(14,1315),(57,296962),(58,296962),(74,296962),(77,296962),(97,141315),(98,296962),(105,10371),(110,139267)]),([5,143,240,580,591,802],[(80,301058),(96,296962),(116,303107),(144,303271),(156,139272)]),([5,143,240,580,708,802],[(72,296962),(80,301058),(96,296962),(104,301058),(112,303107),(116,303107),(144,303271),(152,303271)]),([5,143,240,580,802],[(0,303107),(2,138251),(4,303107),(6,7307),(8,303107),(10,2345),(12,303107),(14,303107),(73,296962),(81,301058),(97,10376),(102,303107),(106,303107),(114,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([5,143,240,580,870],[(0,303271),(2,138251),(4,303271),(6,7307),(8,303271),(10,170281),(12,303271),(14,303271),(74,303271),(102,303239),(106,303239),(114,303271),(117,303271)]),([5,143,240,580,930],[(0,303107),(2,171019),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(73,296962),(81,301058),(102,303107),(106,303107),(114,303271)]),([5,143,240,580,1010],[(0,303107),(2,138251),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(73,296962),(102,303107),(106,303107),(109,303107),(114,303239)]),([5,143,240,580,1826],[(0,303107),(2,138252),(4,303107),(6,7308),(8,303107),(10,2345),(12,303107),(14,303107),(73,296962),(81,301058),(97,11400),(102,303107),(106,303107),(114,303271)]),([5,143,240,580,3293],[(0,303107),(2,138251),(4,303107),(6,7307),(8,303107),(10,2345),(12,303107),(14,303107),(73,1315),(81,1319),(101,295939),(102,303107),(106,303107),(114,305155)]),([5,143,240,708,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271)]),([5,143,240,802,1604],[(0,303107),(2,138252),(4,303107),(6,7308),(8,303107),(10,1323),(12,303107),(14,2345),(73,295939),(82,303107),(97,11400),(105,142344)]),([5,143,240,802,3515],[(0,2345),(2,138251),(4,2345),(6,7307),(8,2345),(10,2345),(12,2345),(14,303107),(73,2338),(78,2345),(82,2345),(101,137513),(109,2345),(117,2347)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([5,143,580,756,802],[(0,301058),(2,138251),(4,301058),(6,301058),(8,301058),(10,7307),(12,301058),(14,1319),(57,296962),(58,301058),(82,301058),(85,301058),(97,10376),(105,141320)]),([5,143,580,802,3855],[(0,7307),(2,138251),(4,7307),(6,7307),(8,7307),(10,7307),(12,7307),(14,303107),(57,7307),(73,7307),(78,7305),(82,7307),(106,7307),(117,7307)]),([5,160,255,580,802],[(0,171010),(2,7330),(4,171010),(6,171010),(8,171010),(10,2345),(12,171010),(14,1192),(58,171010),(61,171010),(73,171010),(74,171010),(81,171010),(105,171010),(110,303107),(114,171010)]),([5,175,240,580,802],[(0,171010),(2,138251),(4,171010),(6,7307),(8,171010),(10,2345),(12,171010),(14,1192),(73,171010),(81,171010),(97,10376),(102,303107),(114,171010)]),([5,207,240,580,802],[(0,303107),(2,138251),(4,303107),(6,7307),(8,303107),(10,2345),(12,303107),(14,303107),(73,296962),(81,141320),(82,303107),(97,10376),(102,303107),(106,303107),(114,141320)]),([5,221,240,580,2184],[(0,295939),(2,296962),(4,295939),(6,105634),(8,295939),(10,2338),(12,295939),(14,295939),(57,295939),(81,164968),(102,295939),(110,295939),(113,295939),(114,306275)]),([5,240,253,580,2184],[(0,295939),(2,295939),(4,295939),(6,296962),(8,295939),(10,2338),(12,295939),(14,295939),(58,295939),(61,295939),(73,1315),(101,295939),(102,295939),(110,295939),(113,295939),(114,306275)]),([5,240,255,514,580,2184],[(112,303106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,255,580,708,802],[(80,296962),(112,303107),(144,303240)]),([5,240,255,580,802,2767],[(96,11559),(112,303240),(140,303107)]),([5,240,255,580,1010,2764],[(72,132195),(112,303239)]),([5,240,255,582,2184],[(0,303106),(2,303106),(4,303106),(6,295945),(8,303106),(10,1321),(12,303106),(14,303106),(58,303106),(61,303106),(73,8482),(101,303106),(102,303106),(110,303106),(113,303106),(114,306274)]),([5,240,255,708,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(61,303107),(81,296962),(98,303107),(101,303107),(105,296962),(110,303107),(114,303271)]),([5,240,255,756,802,2764],[(56,164963),(72,164963),(96,132195),(112,303239),(148,303107)]),([5,240,255,870,2764],[(0,303240),(2,105634),(4,303240),(6,296971),(8,303240),(10,1324),(12,303240),(14,138537),(58,303240),(61,303240),(74,303239)]),([5,240,303,580,802,2184],[(112,305154)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,303,802,2184,3515],[]),([5,240,512,580,2184,4082],[(80,296962),(104,306179),(136,296962)]),([5,240,512,815,870,2184],[(136,296072)]),([5,240,514,580,591,2191],[(72,139267),(80,139559)]),([5,240,514,580,2184,4080],[(80,295945),(136,296962)]),([5,240,527,580,802,2191],[]),([5,240,527,580,802,2696],[]),([5,240,580,589,802,2184],[(56,141315)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,589,2184,3293],[(56,141315),(148,295939)]),([5,240,580,591,802,1904],[(56,301058),(104,11431),(132,296962),(136,138243),(152,138242)]),([5,240,580,591,802,2191],[(56,301058),(104,11431)]),([5,240,580,591,802,2696],[(56,141315),(104,296072)]),([5,240,580,591,802,3215],[(56,301058),(104,10407)]),([5,240,580,591,1826,2191],[(56,301058),(104,11431)]),([5,240,580,591,2191,3293],[(56,1319),(148,303107),(156,1160)]),([5,240,580,708,802,4080],[(56,301058),(80,303107),(104,296971),(136,296962),(152,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,719,802],[(0,296962),(2,7307),(4,296962),(6,2338),(8,296962),(10,138251),(12,296962),(14,1315),(57,296962),(58,296962),(82,296962),(85,296962),(98,296962),(113,10376),(118,8328)]),([5,240,580,767,802,2191],[(148,303107)]),([5,240,580,802,815,2696],[(80,296072)]),([5,240,580,802,895],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(77,296962),(101,296962),(106,296962),(109,296962),(114,296962),(117,296962)]),([5,240,580,802,943],[(0,10376),(2,7307),(4,10376),(6,2338),(8,10376),(10,1192),(12,10376),(14,138251),(57,10376),(106,10376),(114,10376),(117,10376)]),([5,240,580,802,1024,1343],[(80,11554)]),([5,240,580,802,1024,2752],[(80,295948),(136,295939)]),([5,240,580,802,1331,4080],[(56,301058),(80,296971),(100,301058),(136,137513),(144,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,802,2191,3504],[(56,137228),(80,169996),(144,303107)]),([5,240,580,802,2696,4080],[(144,306179)]),([5,240,580,802,2752,4080],[(56,133131),(80,303240),(104,303107),(136,303239),(144,306179)]),([5,240,580,802,2756,4080],[(56,301058),(80,296971),(104,303107),(136,303239),(144,296962)]),([5,240,580,802,2760,4080],[(56,133131),(80,303240),(136,303239),(144,306179)]),([5,240,580,802,2764,4080],[(56,301058),(80,296971),(136,303239),(144,296962)]),([5,240,580,802,2764,4082],[(56,141411),(80,296971),(136,296071),(144,296962)]),([5,240,580,802,2767,4080],[(56,301058),(80,295948),(136,295939),(144,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,802,3200],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(77,296962),(97,296962),(105,295939),(106,296962),(113,296962),(114,295939)]),([5,240,580,802,3788,4080],[(56,301058),(80,297067),(136,303239),(144,296962)]),([5,240,580,802,3952],[(0,138251),(2,138251),(4,138251),(6,138251),(8,138251),(10,138251),(12,138251),(14,303107),(57,138251),(74,138251),(82,138251),(106,138251),(113,303107),(114,138251)]),([5,240,580,810,3208],[(0,99339),(2,99339),(4,99339),(6,2338),(8,99339),(10,1131),(12,99339),(14,10338),(57,99339),(74,99339),(77,99336),(97,105474),(105,295939),(106,99339)]),([5,240,580,815,870,2191],[]),([5,240,580,815,930],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(57,296962),(82,296962)]),([5,240,580,1039,1826,2764],[(56,301058),(104,303240)]),([5,240,580,1826,1919],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(77,296962),(101,296962),(106,296962),(109,296962),(114,296962),(117,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,1826,2176],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(77,296962),(97,296962),(105,295939),(106,296962),(113,296962),(114,295939)]),([5,240,580,1826,2764,4080],[(56,301058),(80,297068),(136,303239),(144,296962)]),([5,240,580,1834,2184],[(0,99340),(2,99340),(4,99340),(6,2338),(8,99340),(10,1132),(12,99340),(14,11362),(57,99340),(74,99340),(77,99336),(97,105474),(105,295939),(106,99340)]),([5,240,580,1911,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(77,296962),(78,296962),(82,296962),(85,296962),(98,296962),(101,296962),(117,295939)]),([5,240,580,2176,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(73,296962),(78,296962),(81,296962),(82,296962),(98,296962),(101,296962),(114,296962),(117,296962)]),([5,240,580,2184,3874],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(57,296962),(78,296962),(81,296962),(82,296962),(98,296962),(113,171106)]),([5,240,580,2184,4018],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(57,296962),(58,137218),(73,296962),(78,296962),(81,296962),(82,296962),(98,296962),(101,296962),(117,296962)]),([5,240,580,2184,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(73,296962),(78,296962),(81,296962),(82,296962),(98,296962),(101,296962),(117,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,580,2191,4082],[(0,303107),(2,301193),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(73,139559),(78,296962),(82,296962),(98,303107),(101,303107),(106,303239),(117,296969),(118,8483)]),([5,240,580,2764,3293,4080],[(56,1319),(136,1315)]),([5,240,580,2764,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,306275),(58,296962),(78,296962),(82,296962),(85,296962),(98,296962),(101,296962),(117,306179)]),([5,240,580,3208,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(73,296962),(78,296962),(81,296962),(82,296962),(98,296962),(101,296962),(117,296962)]),([5,240,582,2184,4080],[(0,295945),(2,295945),(4,295945),(6,295945),(8,295945),(10,295945),(12,295945),(14,303106),(73,295945),(78,295945),(81,295945),(82,295945),(98,295945),(101,295945),(117,295945)]),([5,240,588,802,3208],[(0,100363),(2,100363),(4,100363),(6,2155),(8,100363),(10,1315),(12,100363),(14,10339),(57,100363),(74,100363),(77,100360),(97,104584),(113,296962),(114,100363)]),([5,240,588,1826,2184],[(0,100364),(2,100364),(4,100364),(6,2156),(8,100364),(10,1315),(12,100364),(14,11363),(57,100364),(74,100364),(77,100360),(97,104584),(113,296962),(114,100364)]),([5,240,591,708,802],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(57,296962),(58,296962),(73,296962),(81,296962),(98,296962),(105,296962),(110,295939)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,591,802,870,2191],[(112,11431)]),([5,240,591,802,1604,2191],[(112,11431)]),([5,240,591,802,2191,3515],[(156,2184)]),([5,240,591,870,2191],[(0,11431),(2,301195),(4,11431),(6,169996),(8,11431),(10,11431),(12,11431),(14,11431),(74,11399),(86,139559),(97,141607),(117,11399)]),([5,240,591,2764,2986],[(0,100354),(2,100354),(4,100354),(6,100354),(8,100354),(10,100354),(12,100354),(14,99331),(57,100354),(58,100354),(73,100354),(98,100354),(110,99331)]),([5,240,708,719,802],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939)]),([5,240,708,802,815],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(74,296962),(98,296962),(106,296962),(114,296962),(117,296962)]),([5,240,708,802,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(57,301058),(74,303107),(82,296971),(98,303107),(101,303107),(106,296962),(113,303107),(114,295939)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,756,802,2764,4080],[(56,301058),(80,296971),(100,133131),(108,303107),(128,301058),(136,303239),(144,296962)]),([5,240,802,1024,2756],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,295939),(12,295939),(14,2338),(58,295939),(61,295939),(73,295939),(74,295939),(81,295939),(82,295939),(97,296962),(113,296962),(114,295939)]),([5,240,802,1032,2764],[(0,108547),(2,108547),(4,108547),(6,1315),(8,108547),(10,10339),(12,108547),(14,2155),(58,108547),(61,108547),(73,108547),(74,108547),(81,108547),(82,108547),(97,100363)]),([5,240,802,1039,1604,2764],[(96,172043),(104,303240)]),([5,240,802,1039,1604,3788],[(96,172131),(104,303240)]),([5,240,802,1604,1919],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,2338),(12,295939),(14,295939),(58,295939),(61,295939),(73,296962),(101,295939),(106,295939),(109,295939),(114,295939),(117,295939)]),([5,240,802,1604,2176],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,2338),(12,295939),(14,295939),(58,295939),(61,295939),(73,296962),(97,295939),(105,296962),(106,295939),(113,295939),(114,296962)]),([5,240,802,1604,2764,4080],[(80,297068),(136,296962),(144,303239)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,802,1612,2184],[(0,100364),(2,100364),(4,100364),(6,1315),(8,100364),(10,2156),(12,100364),(14,11363),(58,100364),(61,100360),(73,100364),(97,104584),(105,296962),(106,100364)]),([5,240,802,2756,4080],[(0,303107),(2,303107),(4,303107),(6,1324),(8,303107),(10,2345),(12,303107),(14,303107),(58,303107),(73,301058),(98,303107),(101,303107),(106,295939),(114,303239)]),([5,240,802,2764,3515,4080],[(136,296962)]),([5,240,802,2764,4084],[(0,303239),(2,303239),(4,303239),(6,1315),(8,303239),(10,137513),(12,303239),(14,303239),(58,303239),(73,296962),(98,303239),(101,303239),(106,296071),(117,303239)]),([5,240,810,1024,2764],[(0,99331),(2,99331),(4,99331),(6,1123),(8,99331),(10,99331),(12,99331),(14,2146),(58,99331),(61,99331),(73,99331),(74,99331),(81,99331),(82,99331),(97,100354),(113,100354),(114,99331)]),([5,240,810,1604,2184],[(0,99340),(2,99340),(4,99340),(6,1132),(8,99340),(10,2338),(12,99340),(14,11362),(58,99340),(61,99336),(73,99340),(97,295939),(113,295939),(114,99340)]),([5,240,815,2764,2986],[(0,100354),(2,100354),(4,100354),(6,100354),(8,100354),(10,100354),(12,100354),(14,99331),(58,100354),(73,100354),(98,100354),(110,99331)]),([5,240,870,2764,4080],[(0,296971),(2,296971),(4,296971),(6,296971),(8,296971),(10,296971),(12,296971),(14,303240),(58,296971),(98,296971),(101,296971),(117,303240)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,2184,2764,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,295939),(57,296962),(58,296962),(82,296962),(85,296962),(98,296962),(101,296962)]),([5,240,2184,3515,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,2338),(57,296962),(62,296962),(82,296962),(85,296962),(98,296962),(101,296962),(109,296962)]),([5,242,580,2184,4080],[(0,132105),(2,132105),(4,132105),(6,132105),(8,132105),(10,132105),(12,132105),(14,303107),(73,132105),(78,132105),(81,132105),(82,132105),(117,132105)]),([5,244,580,591,802,2184],[(56,296962),(136,296072)]),([5,255,514,580,591,2184],[(80,139554)]),([5,255,580,591,802,2191],[(104,7335)]),([5,255,580,591,802,2767],[(104,141602)]),([5,255,580,756,802,2191],[(112,303239),(132,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,580,1010,2191],[(0,303107),(2,301068),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(78,303107),(82,303239),(102,303107),(106,11559),(117,303107),(118,303107)]),([5,255,591,756,802,2184],[(60,141315),(112,303234),(132,296962)]),([5,255,591,870,2184],[(0,105634),(2,296075),(4,105634),(6,164968),(8,105634),(10,105634),(12,105634),(14,105634),(78,105634),(86,139554),(97,141602),(102,105634),(106,141602),(113,99496),(114,171106)]),([5,255,756,802,2764],[(0,164963),(2,164963),(4,164963),(6,100514),(8,164963),(10,164963),(12,164963),(14,164963),(57,296962),(62,303235),(73,296962),(78,164963),(82,10531),(102,164963),(113,99491),(114,165986)]),([5,514,591,756,2184],[(0,139267),(2,1315),(4,139267),(6,133129),(8,139267),(10,2185),(12,139267),(14,139267),(58,139267),(61,139267),(97,296962),(98,139267),(106,139267),(113,139267),(118,139267)]),([5,527,580,752,802,2184],[]),([5,580,591,802,2191,2296],[(72,141607)]),([5,580,591,802,2191,2303],[(72,141607)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([5,580,591,802,2191,3855],[(72,301195),(152,296962)]),([5,580,591,802,3983],[(0,296962),(2,2338),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(58,296962),(61,296962),(81,296962),(86,295939),(98,296962),(101,6280),(106,296962),(109,296962),(117,296962)]),([5,580,752,802,815,2184],[]),([5,580,756,802,815,2191],[(96,11399),(128,296962)]),([5,580,756,802,815,2986],[(72,166024),(96,10371),(128,165986)]),([5,580,756,802,2184,4082],[(96,141411)]),([5,580,802,815,3983],[(0,296962),(2,2338),(4,296962),(6,1315),(8,296962),(10,296962),(12,296962),(14,296962),(74,296962),(82,296962),(85,296962),(98,296962),(109,296962),(117,296962)]),([5,580,802,2296,2764,4080],[(56,296971),(96,303107),(128,303239),(136,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([5,580,802,2764,3855,4080],[(56,296971),(112,301058),(128,303239),(136,296962)]),([5,580,802,3983,4080],[(0,303107),(2,2345),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(58,296968),(74,301058),(85,303107),(98,296962),(105,301192),(106,295939),(117,303107),(118,303107)]),([5,580,815,2296,2986],[(0,296962),(2,2338),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,1315),(58,296962),(74,296962)]),([5,580,2184,2296,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,132391),(57,296962),(58,296962),(82,296962),(85,296962),(109,296962),(117,296962)]),([5,580,2184,3855,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,301186),(57,296962),(58,296962),(81,296962),(82,296962),(109,296962),(117,301186),(118,296962)]),([5,591,756,802,870,2184],[(96,10371),(116,296962),(144,297096),(152,171106)]),([5,591,756,802,1911],[(0,296962),(2,133131),(4,296962),(6,2187),(8,296962),(10,1315),(12,296962),(14,296962),(73,10371),(78,139267),(98,296962),(109,296962),(110,296962),(114,296962),(117,296962)]),([5,591,756,802,2184],[(0,296962),(2,133131),(4,296962),(6,2187),(8,296962),(10,1315),(12,296962),(14,296962),(73,10371),(78,139267),(98,296962),(105,141315),(110,296962),(113,296962),(114,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([5,591,756,802,2191],[(0,301058),(2,137228),(4,301058),(6,2187),(8,301058),(10,1319),(12,301058),(14,301058),(73,11399),(78,139267),(98,296962),(110,301058),(114,171010)]),([5,591,756,802,2764],[(0,296962),(2,296962),(4,296962),(6,100491),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(73,296962),(78,139363),(98,296962),(110,296962),(114,171106)]),([5,591,756,802,2767],[(0,296962),(2,296962),(4,296962),(6,2187),(8,296962),(10,1315),(12,296962),(14,296962),(57,296962),(73,296962),(78,139267),(98,296962),(101,296962),(110,296962),(114,171010),(117,139267)]),([5,591,756,802,2986],[(0,171106),(2,133131),(4,171106),(6,2187),(8,171106),(10,99496),(12,171106),(14,171106),(73,10371),(98,171010),(110,171010),(114,171106),(117,171106)]),([5,591,756,802,3208],[(0,296962),(2,133227),(4,296962),(6,2217),(8,296962),(10,1315),(12,296962),(14,296962),(73,108675),(78,139267),(98,296962),(105,172035),(110,296962),(113,296962),(114,171106)]),([5,591,756,1826,2184],[(0,296962),(2,133228),(4,296962),(6,2217),(8,296962),(10,1315),(12,296962),(14,296962),(73,109699),(78,139267),(98,296962),(105,172035),(110,296962),(113,296962),(114,171106)]),([5,591,756,2184,2986],[(0,296962),(2,133131),(4,296962),(6,2187),(8,296962),(10,296962),(12,296962),(14,99496),(81,296962),(102,99464),(114,296962),(117,296962)]),([5,591,756,2184,3293],[(0,1315),(2,133131),(4,1315),(6,2187),(8,1315),(10,1315),(12,1315),(14,296962),(74,1315),(81,1315),(86,1315),(101,141315),(102,139267),(114,1315),(117,1315)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([5,591,802,2184,2812],[(0,141315),(2,133131),(4,141315),(6,1315),(8,141315),(10,141315),(12,141315),(14,100488),(57,141315),(62,139267),(81,296962),(82,100488),(114,141315),(117,141315)]),([5,591,802,2184,3339],[(0,2187),(2,133131),(4,2187),(6,2187),(8,2187),(10,2187),(12,2187),(14,296962),(57,2187),(62,2185),(74,2187),(81,2187),(82,2187),(113,296962),(114,2187)]),([5,756,767,802,2764],[(0,296962),(2,100514),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(58,296962),(61,296962),(81,296962),(86,164963),(102,296962),(110,296962),(114,165986)]),([5,756,802,815,870,2184],[(112,10371),(136,166024),(152,165986)]),([5,756,802,815,2764],[(0,296962),(2,100491),(4,296962),(6,1315),(8,296962),(10,296962),(12,296962),(14,296962),(74,296962),(82,296962),(85,296962),(102,296962),(106,165986),(114,165890)]),([5,756,802,870,879,2184],[(84,10371),(112,10371),(136,166024),(144,165986)]),([5,756,802,870,2184,4080],[(104,170120),(112,170082)]),([5,756,802,879,2184],[(0,10371),(2,2187),(4,10371),(6,1187),(8,10371),(10,133131),(12,10371),(14,10371),(82,10371),(85,10371),(97,141315),(102,10371),(105,165890),(106,10371),(114,165890)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([5,756,802,2184,3504],[(0,133131),(2,133131),(4,133131),(6,133131),(8,133131),(10,133131),(12,133131),(14,296962),(73,133131),(78,133131),(81,133131),(82,133131),(105,296962),(106,133131),(117,133131)]),([5,756,802,2764,4080],[(0,301058),(2,100491),(4,301058),(6,1319),(8,301058),(10,301058),(12,301058),(14,301058),(78,301058),(82,170082),(98,296962),(106,141411),(117,133131)]),([5,802,815,2296,2764],[(0,295939),(2,1315),(4,295939),(6,295939),(8,295939),(10,295939),(12,295939),(14,2338),(58,295939),(61,295939),(73,296962)]),([5,802,1615,1780,2184],[(0,172035),(2,1315),(4,172035),(6,133228),(8,172035),(10,2217),(12,172035),(14,172035),(58,109699),(61,139267),(97,296962),(98,172035),(106,172035),(113,172035),(118,142339)]),([5,802,2296,2764,4080],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(57,303107),(73,296971),(97,303107),(98,295939)]),([6,0,15,240,580,802,2764],[(112,301058),(152,303240)]),([6,2,15,128,240,580],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,303107),(12,303107),(14,301193),(16,303107),(18,2345),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,303107),(98,303107),(105,303107),(106,303107),(114,303107),(117,303107),(129,139559),(130,303107),(145,139559),(146,303107)]),([6,2,15,240,512,580,2184],[(72,139266),(152,303107),(192,306179)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([6,2,15,240,580,802,2764],[(72,10402),(112,141411),(132,306275),(152,303240)]),([6,2,15,240,580,1911],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(130,303107),(133,303107),(138,303107),(149,303107),(150,303107),(154,303107),(157,303107)]),([6,2,15,240,580,2184],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(129,303107),(130,303107),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,2,15,240,580,2186],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(130,303107),(133,303107),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,2,15,240,580,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(105,139559),(130,303107),(133,303107),(138,303107),(141,303107),(145,139559),(150,303107),(154,306179)]),([6,2,15,240,580,2764],[(0,306275),(2,306275),(4,306275),(6,296969),(8,306275),(10,301193),(12,306275),(14,100652),(16,306275),(18,306275),(58,306275),(61,306275),(73,306275),(74,306275),(81,306275),(82,306275),(97,139559),(98,306275),(114,306275),(129,306275),(130,306275),(138,306179),(150,303107),(154,306275),(157,306275)]),([6,2,15,240,580,3208],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(129,303107),(130,303107),(138,303107),(145,139559),(150,303107),(153,303107),(154,305251)]),([6,2,15,240,582,2184],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(57,303106),(58,303107),(61,303107),(73,303107),(74,303107),(77,303106),(81,303107),(82,303107),(97,139559),(98,303107),(101,303107),(129,303107),(130,303107),(133,303106),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([6,2,15,240,2184,2764],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,303107),(16,303107),(18,100652),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,303107),(98,303107),(113,303107),(114,303107),(129,100652),(130,303107),(154,303107),(157,303107)]),([6,2,15,240,2184,3515],[(0,2345),(2,2345),(4,2345),(6,296969),(8,2345),(10,301193),(12,2345),(14,2345),(16,2345),(18,303107),(58,2345),(61,2345),(73,2345),(74,2345),(81,2345),(82,2345),(97,2345),(98,2345),(106,2345),(113,2345),(118,2345),(130,2345),(133,2345),(154,2345),(157,2345)]),([6,2,15,242,580,2184],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(81,303107),(82,303107),(97,139559),(98,303107),(101,303107),(129,303107),(130,303107),(133,303107),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,2,15,255,580,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,139559),(98,303107),(105,139555),(129,303107),(130,303107),(138,303107),(141,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,2,15,580,756,802,2184],[(56,301058),(80,141315),(96,10402),(128,301058),(168,301154),(184,141411)]),([6,2,15,580,2184,2296],[(0,139559),(2,139559),(4,139559),(6,296969),(8,139559),(10,2345),(12,139559),(14,139559),(16,139559),(18,301193),(58,139559),(61,139559),(73,139559),(74,139559),(97,139559),(98,139559),(106,139559),(113,303107),(114,139559),(129,303107),(130,139559),(138,139559),(154,139559),(157,139559)]),([6,2,15,580,2184,3855],[(0,301193),(2,301193),(4,301193),(6,296969),(8,301193),(10,301193),(12,301193),(14,301193),(16,301193),(18,303107),(58,301193),(61,301193),(73,301193),(74,301193),(97,301193),(98,301193),(106,301193),(113,301193),(114,301193),(130,301193),(133,301193),(138,301193),(141,301193),(153,303107),(154,301193)]),([6,2,240,255,580,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,296969),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,8483),(98,303107),(105,8483),(129,303107),(130,303107),(141,303107),(142,303107),(150,303107),(153,303107),(154,306275)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([6,2,240,580,591,802,2184],[(56,10402),(80,141315),(96,296962),(128,296962),(168,297058)]),([6,2,240,580,2184,4080],[(0,296969),(2,296969),(4,296969),(6,296969),(8,296969),(10,296969),(12,296969),(14,296969),(16,296969),(18,303107),(57,296969),(58,296969),(73,296969),(74,296969),(97,296969),(98,296969),(105,296969),(110,296969),(113,296969),(114,296969),(129,303107),(130,296969),(138,296969),(141,296969),(157,296969)]),([6,4,15,240,580,802,2764],[(100,303239),(104,296072),(112,301058),(128,10531),(152,303240),(192,303239)]),([6,4,15,240,802,2764],[(0,303239),(2,303239),(4,303239),(6,303239),(8,303239),(10,303239),(12,303239),(14,1324),(16,303239),(18,137513),(58,303239),(61,303239),(73,303239),(74,303239),(81,303239),(82,303239),(97,303239),(98,303239),(105,296071),(114,303239),(130,303239),(133,303239),(138,303239),(145,301058)]),([6,4,240,580,591,802,2184],[(72,296962),(80,301058),(96,296962),(168,296035),(184,296072)]),([6,6,15,240,580,2184],[(0,303239),(2,303239),(4,303239),(6,303239),(8,303239),(10,301193),(12,303239),(14,137513),(16,303239),(18,303239),(58,303239),(61,303239),(73,303239),(74,303239),(81,303239),(82,303239),(97,139559),(98,303239),(105,139559),(106,303239),(129,303239),(130,303239),(138,303239),(145,139559),(150,303239),(153,303239),(154,139559)]),([6,8,15,240,580,802,2764],[(104,295939),(112,301058),(128,99464),(152,303240),(192,303107)]),([6,8,15,240,802,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,1324),(16,303107),(18,2345),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,303107),(98,303107),(105,295939),(114,303107),(130,303107),(133,303107),(137,295939),(145,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([6,8,240,580,802,3208],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(81,296962),(97,295939),(98,296962),(106,296962),(109,296962),(130,296962),(133,296962),(137,296962),(145,295939),(146,296962),(153,296962),(154,295939)]),([6,8,240,580,1826,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(81,296962),(97,295939),(98,296962),(106,296962),(109,296962),(130,296962),(133,296962),(137,296962),(145,295939),(146,296962),(153,296962),(154,295939)]),([6,8,240,802,1024,2764],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,1315),(12,295939),(14,295939),(16,295939),(18,2338),(57,295939),(58,295939),(73,295939),(74,295939),(82,295939),(85,295939),(97,295939),(98,295939),(105,295939),(106,295939),(113,295939),(114,295939),(130,295939),(133,295939),(137,296962),(153,296962),(154,295939)]),([6,8,240,802,1604,2184],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,1315),(12,295939),(14,2338),(16,295939),(18,295939),(57,295939),(58,295939),(73,295939),(74,295939),(82,295939),(85,295939),(97,296962),(98,295939),(105,296962),(130,295939),(133,295939),(137,295939),(145,296962),(146,295939),(153,295939),(154,296962)]),([6,10,15,240,580,2184],[(0,99464),(2,99464),(4,99464),(6,296969),(8,99464),(10,301193),(12,99464),(14,2345),(16,99464),(18,138338),(58,99464),(61,99464),(73,99464),(74,99464),(81,99464),(82,99464),(97,99464),(98,99464),(129,303107),(137,8483),(145,139559),(153,303107),(154,99464)]),([6,11,240,580,802,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,137513),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(81,296962),(97,296071),(106,296962),(130,296962),(137,296962),(142,296962),(145,303239),(146,296962),(153,296962),(154,171106)]),([6,11,240,802,2184,3515],[(0,137513),(2,137513),(4,137513),(6,137513),(8,137513),(10,137513),(12,137513),(14,137513),(16,137513),(18,296962),(57,137513),(58,137513),(73,137506),(82,137513),(98,137513),(105,137513),(110,137513),(113,137513),(114,137513),(130,137513),(133,137513),(141,296962),(154,137513),(157,137513)]),([6,12,15,240,580,802,2764],[(100,303239),(112,301058),(128,99464),(152,303240)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([6,12,240,580,802,1024,2764],[(80,301058),(112,295948),(128,108556)]),([6,13,15,240,580,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(62,295939),(73,303107),(74,303107),(81,303107),(82,303107),(85,295939),(97,139559),(105,295939),(109,296071),(129,303107),(130,303107),(137,303107),(138,303107),(141,295939),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,13,240,580,802,2184],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,2338),(12,295939),(14,295939),(16,295939),(18,295939),(57,295939),(58,295939),(97,296962),(98,295939),(102,295939),(106,295939),(110,295939),(114,296103),(130,295939),(137,295939),(142,295939),(145,295939),(153,295939),(154,295939),(157,295939)]),([6,13,240,580,1024,2184],[(0,295939),(2,296962),(4,295939),(6,301186),(8,295939),(10,2338),(12,295939),(14,295939),(16,295939),(18,295939),(57,295939),(58,295939),(97,1315),(98,295939),(102,295939),(105,132391),(106,295939),(110,295939),(113,295939),(114,132391),(118,295939),(130,295939),(137,132391),(142,295939),(145,295939),(146,306275),(153,295939),(154,295939),(157,295939)]),([6,13,240,580,2184],[(1,295939),(3,295939),(5,295939),(7,295939),(9,132391),(11,132391),(13,295939),(15,295939),(59,295939),(63,295939),(75,132391),(79,296071),(83,1315),(87,295939),(99,295939),(103,295939),(107,295939),(111,295939),(115,132391),(119,295939)]),([6,13,240,580,2184,3293],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,2338),(12,295939),(14,295939),(16,295939),(18,295939),(57,295939),(58,295939),(98,295939),(105,295939),(110,295939),(113,295939),(130,295939),(133,295939),(134,295939),(138,295939),(142,295939),(146,305155),(154,295939),(157,295939),(158,295939)]),([6,15,15,240,580,802,2764],[(72,105634),(100,303239),(112,301058),(132,306275),(152,303240)]),([6,15,32,240,580,802,2764],[(112,301058),(152,303240),(176,171010)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,32,580,802,3208],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2345),(12,301058),(14,1319),(16,301058),(18,301058),(57,301058),(58,301058),(73,296962),(81,301058),(82,301058),(97,296962),(106,301058),(109,301058),(130,301058),(133,296962),(137,301058),(138,301058),(145,303107),(146,301058),(153,301058),(154,303107)]),([6,15,32,580,1826,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2345),(12,301058),(14,1319),(16,301058),(18,301058),(57,301058),(58,301058),(73,296962),(81,301058),(82,301058),(97,296962),(106,301058),(109,301058),(130,301058),(133,296962),(137,301058),(138,301058),(145,303107),(146,301058),(153,301058),(154,303107)]),([6,15,32,802,1604,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1319),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(82,303107),(85,303107),(97,295939),(105,301058),(106,303107),(130,303107),(133,295939),(137,303107),(138,303107),(145,301058),(146,303107),(153,303107),(154,301058)]),([6,15,34,240,580,2184],[(0,303107),(2,296969),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(62,303107),(73,303107),(74,303107),(81,303107),(82,303107),(105,139559),(106,303107),(130,303107),(137,99496),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,15,34,255,580,2184],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(62,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,105634),(105,139559),(106,303107),(130,303107),(137,99496),(138,303107),(145,139559),(150,303107),(153,303107),(154,306275)]),([6,15,64,240,580,802,2764],[(112,302082),(136,141607),(152,303240)]),([6,15,64,580,756,802,2184],[(72,296962),(80,301058),(84,141315),(104,301058),(112,141315),(144,10403),(184,302082)]),([6,15,64,756,802,2184],[(0,141315),(2,133131),(4,141315),(6,141315),(8,141315),(10,2187),(12,141315),(14,141315),(16,141315),(18,141315),(57,141315),(58,141315),(82,141315),(85,141315),(97,10371),(102,139267),(105,141315),(106,141315),(114,10371),(130,141315),(137,141315),(138,141315),(145,141315),(150,141315),(153,99496),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,68,240,580,802,2184],[(56,303107),(80,303239),(104,303107),(136,303271),(176,303203),(192,303240)]),([6,15,68,240,580,2184,3293],[(56,303107),(80,303239),(104,303107),(136,303203),(152,1324),(176,303107)]),([6,15,112,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(78,303107),(82,303107),(85,303107),(86,303107),(97,296962),(117,303107),(129,296962),(134,303107),(137,303107),(138,303107),(145,303107),(146,303107),(149,303107),(154,303271)]),([6,15,112,580,802],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107)]),([6,15,112,580,802,1024],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,302083),(106,303107),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,15,112,580,802,1911],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(138,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107),(158,303107)]),([6,15,112,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,15,128,240,512,580,802],[(56,141320),(96,296962),(112,301058),(152,303107),(192,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,128,240,580,580,802],[(56,141320),(96,296962),(112,301058),(120,303107),(124,303107),(192,303271)]),([6,15,128,240,580,591,802],[(112,301058),(128,296962),(132,303107),(144,301058),(156,303107),(192,303271)]),([6,15,128,240,580,708,802],[(96,296962),(108,303107),(112,301058),(128,296962),(140,303107),(144,301058),(152,303107),(156,303107),(192,303271),(200,303271)]),([6,15,128,240,580,756,802],[(56,10376),(84,301058),(96,296962),(116,141315),(128,296962),(140,303107),(144,301058),(148,303107),(156,303107),(200,303239)]),([6,15,128,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(146,303107),(154,303271)]),([6,15,128,240,580,802,870],[(56,141320),(104,303240),(168,296962),(196,303107),(200,303271),(204,303107)]),([6,15,128,240,580,802,1604],[(56,142344),(96,295939),(112,301058),(152,303271),(192,303107),(196,303107),(200,303271)]),([6,15,128,240,580,802,2764],[(56,141416),(112,301058),(152,303271),(180,303107),(196,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,128,240,580,802,3515],[(56,141320),(96,2338),(112,301058),(152,170281),(172,296962),(180,303107),(188,301058),(204,305155)]),([6,15,128,240,580,870],[(0,303271),(2,296971),(4,303271),(6,303271),(8,303271),(10,301195),(12,303271),(14,170281),(16,303271),(18,303271),(57,303271),(58,303271),(73,303271),(74,303271),(82,303271),(85,303271),(98,303271),(105,141607),(106,303271),(134,303239),(137,303271),(138,303271),(146,303239),(154,303271),(157,303271)]),([6,15,128,240,580,930],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(113,301058),(129,296962),(134,303107),(138,303107),(141,303107),(146,303107),(154,303271)]),([6,15,128,240,580,1010],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(105,139559),(106,303107),(129,296962),(134,303107),(138,303107),(141,303107),(146,303107),(149,303107),(154,303239)]),([6,15,128,240,580,1826],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(146,303107),(154,303271)]),([6,15,128,240,580,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,1315),(106,303107),(113,1319),(133,295939),(134,303107),(138,303107),(141,303107),(146,303107),(154,305155)]),([6,15,128,240,708,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(62,303107),(73,303107),(74,303107),(81,303107),(82,303107),(85,303107),(97,296962),(106,303107),(109,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(141,303107),(146,303107),(154,303271)]),([6,15,128,240,802,1604],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,1323),(16,303107),(18,2345),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,295939),(105,303107),(106,303107),(114,303107),(129,295939),(137,305154),(138,303107),(145,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,128,240,802,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2345),(74,2345),(82,2345),(85,2345),(97,2338),(102,2345),(105,2345),(106,2345),(114,2345),(133,137513),(138,2345),(141,2345),(149,2345),(157,2347)]),([6,15,128,255,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(74,303107),(77,303107),(82,303107),(85,303107),(106,303107),(113,301058),(133,303107),(134,303107),(137,303107),(138,303107),(150,303107),(154,303271)]),([6,15,128,580,756,802],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,301058),(16,301058),(18,1319),(57,301058),(58,301058),(73,296962),(74,301058),(81,301058),(82,301058),(97,296962),(98,301058),(106,301058),(109,301058),(114,301058),(117,301058),(129,296962),(138,301058)]),([6,15,128,580,802,3855],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(82,303107),(97,296962),(102,301193),(105,303107),(106,303107),(114,301195),(130,303107),(133,303107),(137,303107),(138,303107),(146,301058),(157,303107)]),([6,15,136,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(113,301058),(129,296962),(134,303107),(137,171106),(138,303107),(146,303107),(154,303271)]),([6,15,136,255,580,802],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,105634),(105,105634),(106,303107),(113,301058),(134,303107),(137,171106),(138,303107),(150,303107),(154,303271)]),([6,15,143,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(82,303107),(85,303107),(101,303239),(113,301058),(129,303107),(133,303107),(134,303107),(137,171010),(142,303107),(146,303107),(154,303271)]),([6,15,160,240,580,802],[(0,171010),(2,171010),(4,171010),(6,171010),(8,171010),(10,171010),(12,171010),(14,2345),(16,171010),(18,1192),(57,171010),(58,171010),(73,171010),(74,171010),(82,171010),(85,171010),(97,171010),(105,171010),(106,171010),(113,171010),(129,296962),(137,303107),(145,171145),(154,171010)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,176,580,802,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2345),(12,301058),(14,1319),(16,301058),(18,301058),(57,301058),(58,301058),(73,296962),(81,301058),(82,301058),(97,296962),(106,301058),(130,301058),(137,301058),(142,301058),(145,303107),(146,301058),(153,301058),(154,171106)]),([6,15,176,802,2184,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,301058),(57,2345),(58,2345),(73,2338),(82,2345),(98,2345),(105,2345),(110,2345),(113,2345),(114,2345),(133,296962),(138,2345),(141,2345),(154,2345),(157,2345)]),([6,15,192,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(114,303107),(129,296962),(134,303107),(137,303107),(138,303107),(146,303107),(154,10531)]),([6,15,192,240,580,802,2764],[(56,141416),(112,141411),(136,141607),(152,306178),(180,303107),(196,303107)]),([6,15,240,240,580,802,2764],[(56,164968),(136,139559),(152,303240),(180,303107)]),([6,15,240,242,580,2184],[(0,303107),(2,296969),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(62,303107),(73,303107),(78,303107),(81,303107),(82,303107),(85,303107),(105,8483),(109,303107),(113,8483),(130,303107),(137,303107),(141,303107),(142,303107),(145,99464),(150,303107),(153,303107),(154,306275)]),([6,15,240,255,580,802,2764],[(72,164968),(80,105634),(100,303239),(116,303240),(132,306275),(136,139559),(148,306275),(152,303240),(180,303107),(188,303203)]),([6,15,240,290,580,802,2184],[(144,303107),(148,305155),(152,305155),(184,171106),(200,306179)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,290,580,2184],[(0,305155),(2,296971),(4,305155),(6,301195),(8,305155),(10,305155),(12,305155),(14,2347),(16,305155),(18,305155),(57,305155),(58,305155),(73,305155),(78,303107),(82,305155),(113,303271),(114,305155),(130,305155),(137,141607),(142,305155),(145,99496),(146,305155),(153,305155),(154,306275)]),([6,15,240,290,802,2184,3515],[(112,2345),(116,2347),(144,171106),(152,2348),(184,2345)]),([6,15,240,290,2184,3515],[(0,2347),(2,296971),(4,2347),(6,301195),(8,2347),(10,2347),(12,2347),(14,2347),(16,2347),(18,305155),(57,2347),(58,2347),(73,2347),(78,2345),(82,2347),(98,2347),(105,2347),(110,2347),(113,2347),(114,2347),(146,2347),(149,2347),(154,2347),(157,2347)]),([6,15,240,512,580,802,1911],[(72,296962),(80,301058),(112,303107),(144,303107),(184,303107)]),([6,15,240,512,580,802,2184],[(72,296962),(80,301058),(112,303107),(144,303107)]),([6,15,240,512,580,802,2191],[(80,301058),(112,303107),(144,303107)]),([6,15,240,512,580,802,2696],[]),([6,15,240,512,580,802,2764],[(72,296962),(80,301058),(104,141411)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,512,580,802,3208],[(72,296962),(80,301058),(112,303107),(144,303107)]),([6,15,240,512,580,870,2184],[(96,10407),(112,303271),(144,303271)]),([6,15,240,512,580,1010,2184],[(72,296962),(112,303107),(144,303107)]),([6,15,240,512,580,1826,2184],[(72,296962),(80,301058),(112,303107),(144,303107)]),([6,15,240,512,580,2184,3293],[(72,1315),(80,1319),(112,303107),(184,305155)]),([6,15,240,512,802,870,2184],[(184,303240),(192,170120)]),([6,15,240,512,802,1604,2184],[(72,295939),(80,301058),(112,303107),(144,303107)]),([6,15,240,512,802,2184,2764],[(72,295939),(80,301058),(112,303107),(144,306178),(152,100354),(184,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,512,802,2184,3515],[(72,2338),(80,301058),(112,2345)]),([6,15,240,514,580,591,2184],[(104,139267),(112,139559),(128,295939),(136,301058)]),([6,15,240,514,580,802,2184],[(72,296962),(80,10402),(112,303107),(144,303107)]),([6,15,240,514,580,1024,2184],[(112,303106),(144,305155),(152,305154)]),([6,15,240,514,580,2184],[(73,295939),(78,303107),(97,295939),(105,301058),(113,139559),(114,8482)]),([6,15,240,516,580,802,2184],[(72,296962),(80,301058),(96,296962),(112,303107),(144,303239)]),([6,15,240,527,580,802,2184],[(56,105634),(72,296962),(76,303107),(80,301058)]),([6,15,240,544,580,802,2184],[(72,296962),(80,301058),(112,169986),(144,303107),(184,171010)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,576,580,802,2184],[(72,296962),(80,301058),(104,301058),(112,303107),(144,303107),(152,303271)]),([6,15,240,580,580,802,1911],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271),(184,303107)]),([6,15,240,580,580,802,2184],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271)]),([6,15,240,580,580,802,2191],[(80,301058),(88,303107),(92,303107),(144,303271)]),([6,15,240,580,580,802,2764],[(72,296962),(80,301058),(144,141607)]),([6,15,240,580,580,802,3208],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271)]),([6,15,240,580,580,1826,2184],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271)]),([6,15,240,580,580,2184,3293],[(72,1315),(80,1319),(88,303107),(92,303107),(172,132391),(184,305155)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,582,802,2184],[(96,296962),(104,10402),(112,303107),(116,303107),(144,303271),(152,303271)]),([6,15,240,580,582,2184],[(0,139559),(2,296969),(4,139559),(6,301193),(8,139559),(10,139559),(12,139559),(14,139559),(16,139559),(18,139559),(57,8483),(58,139559),(74,139559),(78,303106),(82,8483),(86,303106),(102,303239),(106,8483),(113,139559),(114,139559),(117,139559),(130,139559),(137,139559),(142,139559),(145,139559),(146,139559),(149,303106),(153,139559),(154,139559)]),([6,15,240,580,588,802,2184],[(72,100488),(80,301058),(96,296962),(104,301058),(112,100488),(116,303107),(144,303271),(152,99464)]),([6,15,240,580,591,802,1911],[(56,105634),(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271),(168,296962),(192,303107)]),([6,15,240,580,591,802,2184],[(56,105634),(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271)]),([6,15,240,580,591,802,2191],[(76,11399),(80,301058),(100,303107),(104,301058),(116,303107),(132,139559),(144,303271)]),([6,15,240,580,591,802,2764],[(56,105634),(76,296072),(80,301058),(96,296962),(104,301058),(144,141607),(168,296962)]),([6,15,240,580,591,802,2767],[(80,301058),(96,296962),(104,301058),(144,141607),(168,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,591,802,3208],[(56,105634),(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271)]),([6,15,240,580,591,1826,2184],[(56,105634),(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271)]),([6,15,240,580,591,2184,3293],[(56,105634),(80,1319),(96,1315),(100,303107),(104,1319),(116,303107),(172,295939),(196,303107)]),([6,15,240,580,612,802,2184],[(72,296962),(80,169986),(96,296962),(104,301058),(112,169986),(116,303107),(152,303271),(192,171010)]),([6,15,240,580,708,802],[(73,296962),(78,303239),(81,301058),(86,303107),(97,296962),(105,301058),(110,303107),(129,296962),(134,139559),(138,139559),(145,303240),(146,141607),(154,141607)]),([6,15,240,580,708,802,1024],[(72,296962),(80,301058),(96,296962),(112,303107),(144,303240),(188,303107)]),([6,15,240,580,708,802,2184],[(72,296962),(80,301058),(96,296962),(104,301058),(112,303107),(116,303107),(144,303271),(152,303271),(188,303107),(196,303107)]),([6,15,240,580,752,802,2184],[(56,164968),(96,296962),(104,301058),(108,303107),(152,303107),(180,301058),(196,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,756,802,1911],[(56,164968),(72,296962),(84,141315),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239)]),([6,15,240,580,756,802,2184],[(56,164968),(72,296962),(84,141315),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239),(180,301058),(196,303107)]),([6,15,240,580,756,802,2191],[(72,11399),(84,141315),(104,301058),(108,303107),(116,303107),(152,303239),(180,301058),(196,303239)]),([6,15,240,580,756,802,2764],[(56,164968),(72,296962),(80,301058),(84,302082),(96,296962),(104,301058),(144,10531),(152,139559)]),([6,15,240,580,756,802,3208],[(56,164968),(72,296962),(84,172035),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239),(180,301058),(196,303107)]),([6,15,240,580,756,1010,2184],[(56,10535),(72,296962),(84,139267),(96,296962),(108,303107),(116,303107),(152,303239),(196,303107)]),([6,15,240,580,756,1826,2184],[(56,164968),(72,296962),(84,172035),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239),(180,301058),(196,303107)]),([6,15,240,580,756,2184,3293],[(56,164968),(72,1315),(84,141315),(96,1315),(104,1319),(108,303107),(116,303107),(140,1319),(156,303107),(172,1315),(176,1319),(192,305155)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,767,802,2184],[(96,296962),(100,303107),(104,301058),(108,303107),(116,303107),(180,301058),(196,303107)]),([6,15,240,580,770,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(105,301193),(106,303107),(114,141607),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107)]),([6,15,240,580,802,802,2764],[(80,141411),(96,296962),(112,303240),(192,171106)]),([6,15,240,580,802,815,2764],[(76,296071),(80,141411),(112,303240),(128,296962),(168,296962),(200,171010)]),([6,15,240,580,802,870,1911],[(128,296962),(148,303107),(152,303271),(156,303107),(192,303271),(200,303107)]),([6,15,240,580,802,870,2184],[(128,296962),(148,303107),(152,303271),(156,303107),(184,303240),(192,171106),(200,171106)]),([6,15,240,580,802,870,2191],[(128,303107),(148,303107),(152,303271),(156,303107),(184,303240),(192,171010),(200,171010)]),([6,15,240,580,802,870,2764],[(72,296072),(112,303240),(128,296962),(144,303240),(152,141607),(184,303240),(192,171106),(200,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,870,2986],[(96,297096),(116,170120),(128,295939),(148,171106),(152,171106),(156,171106),(192,171106),(200,171106)]),([6,15,240,580,802,870,3054],[(128,297058),(148,171106),(152,171106),(156,171106),(192,171106),(200,171106)]),([6,15,240,580,802,870,3208],[(128,296962),(140,303107),(148,303107),(152,303271),(156,303107),(184,303240),(192,171106),(200,171106)]),([6,15,240,580,802,887],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(129,296962),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,802,930],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(110,303107),(129,295939),(130,171010),(142,171010),(154,303107),(157,303107)]),([6,15,240,580,802,1010,2764],[(80,172131),(96,296962),(112,303240),(128,296962),(144,303239),(152,139559)]),([6,15,240,580,802,1024,1331],[(80,301058),(112,138537),(180,301058)]),([6,15,240,580,802,1024,2696],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_99 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,1024,2764],[(80,301058),(112,303240)]),([6,15,240,580,802,1024,2767],[(80,301058),(112,303240),(128,10376)]),([6,15,240,580,802,1024,3788],[(80,301058),(112,303240),(144,305154),(152,305251)]),([6,15,240,580,802,1039,2764],[(56,105634),(80,301058),(112,303240),(148,303239),(156,306275),(168,10376)]),([6,15,240,580,802,1109],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(114,171106),(130,171010),(142,171010),(146,171106),(153,171106),(154,303107)]),([6,15,240,580,802,1152],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(129,303107),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107)]),([6,15,240,580,802,1264,2764],[(56,164968),(80,141411),(104,139559),(112,303240),(152,139559),(204,303107)]),([6,15,240,580,802,1331],[(57,164968),(58,105634),(73,296962),(78,137513),(81,301058),(97,296962),(102,306275),(106,139559),(113,138537),(114,141607),(141,301058),(142,303107),(145,2345),(146,303107),(154,303203),(157,306275)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_99 : K_99.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_100 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,1331,2184],[(72,2338),(80,301058),(112,170281),(140,301058),(156,305155),(192,171106)]),([6,15,240,580,802,1331,2764],[(80,301058),(112,306178),(140,301058),(144,303107),(156,306275),(176,301058),(192,171106)]),([6,15,240,580,802,1536,2184],[(144,303107),(152,303107)]),([6,15,240,580,802,1604,1911],[(72,295939),(80,301058),(112,303271),(144,303107),(148,303107),(152,303271),(168,296962),(184,303107),(200,303107)]),([6,15,240,580,802,1604,2184],[(72,295939),(80,301058),(112,303271),(144,303107),(148,303107),(152,303271)]),([6,15,240,580,802,1604,2191],[(80,301058),(112,303271),(128,10376),(144,303107),(148,303107),(152,303271)]),([6,15,240,580,802,1604,2764],[(72,296962),(80,301058),(112,172327),(152,172327)]),([6,15,240,580,802,1604,3208],[(72,295939),(80,301058),(112,303271),(136,301058),(144,303107),(148,303107),(152,303271),(184,305154)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_100 : K_100.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_101 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,1604,3788],[(72,296962),(80,301058),(112,305154),(136,301058),(144,305154),(152,172327),(184,305154)]),([6,15,240,580,802,1615,2184],[(56,105634),(80,301058),(112,303271),(132,303107),(148,303107),(168,10376)]),([6,15,240,580,802,1780,2184],[(56,164968),(72,295939),(140,303107),(148,303107),(152,303239),(204,303107)]),([6,15,240,580,802,1826,2764],[(80,172131),(96,296962),(108,301058),(112,303240),(144,303240),(192,171106),(200,171106)]),([6,15,240,580,802,1894,2184],[(148,303107),(152,303271),(156,303107),(184,303240),(192,171106),(200,171106)]),([6,15,240,580,802,1904],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(114,303271),(129,303107),(130,303107),(141,303107),(142,303107),(146,303239),(153,303107),(154,303107)]),([6,15,240,580,802,1911],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,802,1911,2764],[(72,295939),(80,301058),(112,303271),(144,303107),(176,301058),(184,303107),(188,303107),(192,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_101 : K_101.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_102 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,1911,3515],[(72,2338),(80,301058),(112,170281),(144,2345),(172,296962),(180,301058),(196,305155)]),([6,15,240,580,802,1919],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(133,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,802,2176],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(129,303107),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107)]),([6,15,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106)]),([6,15,240,580,802,2184,2491],[(72,2338),(80,301058),(112,170281),(172,296962),(180,301058),(196,305155),(204,303107)]),([6,15,240,580,802,2184,2696],[(144,306178),(152,99496),(176,301058),(184,303107),(192,99496),(204,303107)]),([6,15,240,580,802,2184,2764],[(72,295939),(80,301058),(112,303271),(152,99496),(176,301058),(184,303107),(188,303107),(192,99496),(204,303107)]),([6,15,240,580,802,2184,2767],[(80,301058),(112,303271),(172,303107),(176,301058),(188,303107),(204,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_102 : K_102.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_103 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,2184,2812],[(72,295939),(84,141315),(176,301058),(180,303107),(188,303107),(192,99464),(204,303107)]),([6,15,240,580,802,2184,3054],[(188,303107),(192,99496),(196,303107),(200,171106),(204,303107)]),([6,15,240,580,802,2184,3225],[(144,303240),(152,99496),(172,296071),(204,303107)]),([6,15,240,580,802,2184,3339],[(56,105634),(72,2338),(84,2187),(140,301058),(172,296962),(196,305155)]),([6,15,240,580,802,2184,3504],[(56,164968),(80,301058),(112,170281),(180,301058),(192,303107),(204,303107)]),([6,15,240,580,802,2184,3515],[(72,2338),(80,301058),(112,170281),(172,296962),(180,301058),(196,305155),(204,303107)]),([6,15,240,580,802,2184,3519],[(80,301058),(112,170281),(172,303107),(180,301058),(196,305155),(204,303107)]),([6,15,240,580,802,2184,3579],[(72,2338),(172,296962),(180,303107),(196,305155),(204,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_103 : K_103.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_104 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,2184,3583],[(172,303107),(180,303107),(196,305155),(204,303107)]),([6,15,240,580,802,2184,3788],[(72,295939),(80,301058),(112,303271),(132,296962),(152,99496),(184,303107),(188,303107),(192,99496),(204,303107)]),([6,15,240,580,802,2184,3805],[(112,303271),(152,99496),(172,295939),(188,303107),(204,303107)]),([6,15,240,580,802,2184,4027],[(144,303240),(172,296962),(180,301058),(196,303107),(204,303107)]),([6,15,240,580,802,2186],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,297058),(81,301154),(97,296969),(102,303107),(106,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(154,171106),(157,303107)]),([6,15,240,580,802,2188],[(0,303203),(2,303203),(4,303203),(6,303203),(8,303203),(10,100649),(12,303203),(14,303203),(16,303203),(18,303203),(57,303203),(58,303203),(73,296035),(81,301058),(97,296035),(102,303203),(106,303203),(114,303271),(130,303107),(137,303203),(142,303107),(153,99496),(154,171106)]),([6,15,240,580,802,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(114,303271),(130,303107),(133,303107),(137,303107),(142,303107),(154,171010),(157,303107)]),([6,15,240,580,802,2191,2764],[(80,301058),(112,303271),(136,105634),(148,303239),(156,306275),(176,301058),(188,303107),(204,303203)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_104 : K_104.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_105 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,2191,2767],[(80,301058),(112,303271),(148,303239),(156,306179),(172,303107),(176,301058),(188,303107),(204,303107)]),([6,15,240,580,802,2191,3515],[(80,301058),(112,170281),(172,303239),(180,301058),(196,305155),(204,303239)]),([6,15,240,580,802,2216],[(0,171010),(2,171010),(4,171010),(6,171010),(8,171010),(10,2345),(12,171010),(14,1192),(16,171010),(18,171010),(57,171010),(58,171010),(73,171010),(81,171010),(97,296962),(105,172168),(114,171010),(130,171010),(137,171010),(142,171010),(145,303107),(146,171010),(154,171106)]),([6,15,240,580,802,2248],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(82,303107),(97,296962),(102,303107),(106,303107),(114,10531),(130,303107),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106)]),([6,15,240,580,802,2296,2764],[(72,295939),(84,303107),(104,139559),(112,303240),(152,99464),(184,303107),(204,303107)]),([6,15,240,580,802,2696],[(57,164968),(58,105634),(102,306179),(113,303240),(142,303107),(145,306178),(153,99496),(154,171106)]),([6,15,240,580,802,2764],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(97,296962),(102,306275),(106,139559),(113,303240),(114,141607),(137,301058),(142,303107),(153,99496),(154,171106)]),([6,15,240,580,802,2764,2764],[(80,301058),(112,306178),(136,301058),(152,99496)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_105 : K_105.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_106 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,2764,2767],[(80,301058),(112,306178),(136,301058),(176,301058)]),([6,15,240,580,802,2764,2812],[(80,301058),(112,306178),(176,301058),(192,99464)]),([6,15,240,580,802,2764,2986],[(72,295939),(96,296962),(116,100354),(144,303107),(148,171106),(192,99496),(200,171106)]),([6,15,240,580,802,2764,3054],[(80,141411),(112,303271),(148,171106),(192,99496),(200,171106)]),([6,15,240,580,802,2764,3071],[(80,301058),(112,303240)]),([6,15,240,580,802,2764,3208],[(72,295939),(80,301058),(112,303271),(132,296071),(136,301058),(144,303107),(148,303107),(152,99496),(192,99496),(204,303107)]),([6,15,240,580,802,2764,3293],[(80,141411),(96,1315),(112,303240),(152,99496),(188,303240),(204,303203)]),([6,15,240,580,802,2764,3515],[(72,296962),(80,301058),(112,141607),(172,296962),(180,301058),(196,306275),(204,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_106 : K_106.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_107 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,2764,3788],[(80,301058),(112,306178),(136,301058),(152,99496),(192,99496)]),([6,15,240,580,802,2764,3855],[(56,105634),(104,301193),(112,303240),(140,303107),(200,303107)]),([6,15,240,580,802,2764,4080],[(56,164968),(76,303239),(80,301058),(100,296969),(112,303240),(184,303239),(192,306275)]),([6,15,240,580,802,2767],[(73,296962),(78,303239),(81,301058),(97,296962),(102,306179),(106,139559),(113,303240),(114,141607),(137,301058),(142,303107),(154,171010)]),([6,15,240,580,802,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(114,171106),(130,171010),(142,171010),(146,171106),(154,171106),(157,171106)]),([6,15,240,580,802,2991],[(0,171010),(2,171010),(4,171010),(6,171010),(8,171010),(10,2345),(12,171010),(14,1192),(16,171010),(18,171010),(57,171010),(58,171010),(73,171010),(81,171010),(97,296962),(114,171010),(130,171010),(133,171010),(142,171010),(146,171010),(154,171010),(157,171010)]),([6,15,240,580,802,3054],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,100649),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(82,170082),(97,297058),(114,171106),(130,171010),(142,171010),(146,171106),(149,171106),(154,171106),(157,171106)]),([6,15,240,580,802,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,296962),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_107 : K_107.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_108 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,802,3208,3515],[(72,2338),(80,301058),(112,170281),(172,296962),(180,301058),(196,172327),(204,303107)]),([6,15,240,580,802,3208,3788],[(72,295939),(80,301058),(112,303271),(132,296962),(152,99496),(172,296071),(176,301058),(184,303107),(188,303107),(192,99496),(204,303107)]),([6,15,240,580,802,3215],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,303107),(137,303107),(142,303107),(154,171010),(157,303107)]),([6,15,240,580,802,3788],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(97,296962),(102,305251),(106,139559),(109,301058),(113,303240),(114,172327),(137,301058),(142,303107),(153,99496),(154,171106)]),([6,15,240,580,802,3967],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(133,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,802,3983],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(62,303107),(73,296962),(85,303107),(97,296962),(102,303107),(105,303107),(106,303107),(109,303107),(114,303271),(130,303107),(133,303107),(137,303107),(141,303107),(142,303107),(146,303107),(154,171010),(157,303107)]),([6,15,240,580,802,4010],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(109,303107),(114,171106),(130,171010),(133,171106),(141,171106),(142,171010),(146,171106),(154,171106),(157,171106)]),([6,15,240,580,806,2184],[(0,303239),(2,296971),(4,303239),(6,303239),(8,303239),(10,137513),(12,303239),(14,303239),(16,303239),(18,303239),(57,303239),(58,303239),(74,303239),(81,301058),(102,303239),(106,303239),(114,303271),(130,303239),(137,303239),(142,303239),(145,303239),(146,10531),(153,99496),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_108 : K_108.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_109 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,810,2184],[(0,99464),(2,99464),(4,99464),(6,99464),(8,99464),(10,2345),(12,99464),(14,99464),(16,99464),(18,138338),(57,99464),(58,99464),(73,99464),(81,99464),(97,99464),(102,99464),(106,99464),(114,99464),(129,99340),(137,303107),(145,303107),(146,99464),(153,99496)]),([6,15,240,580,815,870,2184],[(100,303271),(156,303239),(184,303240),(192,171010)]),([6,15,240,580,866,2184],[(0,303107),(2,303107),(4,303107),(6,301195),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(137,141607),(142,303107),(145,303107),(146,141607),(153,99496),(154,171106)]),([6,15,240,580,870,1826,2184],[(96,296962),(108,303107),(116,303107),(152,303271),(156,303107),(184,303240),(192,171106),(200,171106)]),([6,15,240,580,870,1911],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(114,303271),(117,303271),(130,303271),(141,303271),(142,303271),(146,303271),(149,303271),(154,303271),(157,303271)]),([6,15,240,580,870,2184],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(114,303271),(117,303271),(130,303271),(137,141607),(142,303271),(145,303271),(146,141607),(153,99496),(154,171106)]),([6,15,240,580,870,2184,2986],[(96,296962),(116,99496),(192,99496),(196,303107),(200,171106),(204,303271)]),([6,15,240,580,870,2184,3293],[(96,1315),(116,303107),(144,303240),(152,99496),(172,296103),(184,303271),(204,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_109 : K_109.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_110 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,870,2191],[(0,303271),(2,303271),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(73,141607),(74,303271),(97,303271),(102,303239),(106,303239),(114,303271),(117,303271),(130,303271),(133,303271),(137,141607),(142,303271),(145,303271),(146,141607),(154,171010),(157,303239)]),([6,15,240,580,870,2764],[(0,141607),(2,296971),(4,141607),(6,301195),(8,141607),(10,141607),(12,141607),(14,141607),(16,141607),(18,141607),(57,10531),(58,141607),(74,141607),(78,303240),(82,10531),(86,303240),(102,139559),(106,139559),(113,303240),(114,141607),(117,141607),(130,141607),(142,10531),(145,306178),(146,141607),(149,141607),(153,99496),(154,171106)]),([6,15,240,580,870,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,171106),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,297096),(74,171011),(81,301192),(82,170120),(97,297096),(114,171106),(117,171106),(130,171010),(142,171010),(146,171106),(149,170120),(154,171106),(157,171106)]),([6,15,240,580,870,3054],[(0,171106),(2,296971),(4,171106),(6,301195),(8,171106),(10,170281),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(74,171106),(114,171106),(117,171106),(130,171010),(142,171010),(146,171106),(149,171106),(154,171106),(157,171106)]),([6,15,240,580,870,3208],[(0,303271),(2,297067),(4,303271),(6,301225),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(109,303271),(114,303271),(117,303271),(130,303271),(137,172327),(142,303271),(145,303271),(146,172327),(153,99496),(154,171106)]),([6,15,240,580,930,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(153,99496),(158,303107)]),([6,15,240,580,1010,1911],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(157,303107),(158,303107)]),([6,15,240,580,1010,2184],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239),(130,303107),(137,139559),(142,303107),(145,303107),(146,139559),(153,99464),(158,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_110 : K_110.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_111 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,1010,2191],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,139559),(97,303107),(102,303107),(106,303107),(109,303107),(114,303239),(130,303107),(133,303107),(137,139559),(142,303107),(146,139559),(157,303107),(158,303107)]),([6,15,240,580,1010,2764],[(0,139559),(2,139559),(4,139559),(6,301193),(8,139559),(10,139559),(12,139559),(14,139559),(16,139559),(18,139559),(58,139559),(73,296962),(78,303239),(97,296962),(102,306275),(106,139559),(109,139559),(113,303239),(114,139559),(130,139559),(142,303107),(146,139559),(149,139559),(153,99464),(158,139559)]),([6,15,240,580,1010,3208],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239),(130,303107),(133,296962),(137,139559),(142,303107),(145,303107),(146,139559),(153,99464),(158,303107)]),([6,15,240,580,1014,2184],[(0,303239),(2,296971),(4,303239),(6,301193),(8,303239),(10,137513),(12,303239),(14,303239),(16,303239),(18,303239),(57,303239),(58,303239),(74,303239),(102,303239),(106,303239),(109,303239),(114,303239),(117,303239),(130,303239),(137,139559),(142,303239),(145,303239),(146,139559),(153,99464),(158,303239)]),([6,15,240,580,1024,1826,2764],[(80,301058),(112,305288),(144,303240),(192,305251)]),([6,15,240,580,1024,2764,3293],[(80,1319),(172,306275),(176,1319)]),([6,15,240,580,1026,2184],[(0,303107),(2,296969),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(97,8483),(102,303107),(105,139559),(106,303107),(113,303107),(114,139559),(130,303107),(137,139559),(142,303107),(145,303107),(146,306275),(153,303107),(154,303107)]),([6,15,240,580,1109,2184],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,99496),(16,99496),(18,171106),(57,99496),(58,99496),(73,99496),(81,99496),(102,99464),(106,99464),(114,99496),(137,303107),(145,303107),(146,99496),(153,303107),(154,99496)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_111 : K_111.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_112 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,1604,1826,2184],[(72,296962),(80,301058),(96,296962),(116,303107),(152,303271),(184,305288),(192,305251)]),([6,15,240,580,1604,2184,3293],[(72,1315),(80,1319),(112,1323),(116,303107),(172,132391),(176,1319),(192,305155)]),([6,15,240,580,1826,1894,2184],[(128,296962),(140,303107),(148,303107),(152,303271),(156,303107),(184,303240),(192,171106),(200,171106)]),([6,15,240,580,1826,1911],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(129,296962),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,1826,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,296962),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106)]),([6,15,240,580,1826,2184,2764],[(72,295939),(80,301058),(112,303271),(132,296962),(152,99496),(172,296071),(176,301058),(184,303107),(188,303107),(192,99496),(204,303107)]),([6,15,240,580,1826,2184,3515],[(72,2338),(80,301058),(112,170281),(172,296962),(180,301058),(196,172327),(204,303107)]),([6,15,240,580,1826,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,303107),(137,303107),(142,303107),(154,171010),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_112 : K_112.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_113 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,1826,2764],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(97,296962),(102,306275),(106,139559),(109,301058),(113,303240),(114,172327),(137,301058),(142,303107),(153,99496),(154,171106)]),([6,15,240,580,1826,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(109,303107),(114,171106),(130,171010),(133,171019),(141,171106),(142,171010),(146,171106),(154,171106),(157,171106)]),([6,15,240,580,1826,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,296962),(137,303107),(142,303107),(145,303107),(146,305251),(153,99496),(154,171106)]),([6,15,240,580,1826,4010],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(109,303107),(114,171106),(130,171010),(133,171106),(141,171106),(142,171010),(146,171106),(154,171106),(157,171106)]),([6,15,240,580,1894,2184],[(0,303271),(2,297068),(4,303271),(6,301225),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(109,303271),(114,303271),(117,303271),(130,303271),(137,172327),(142,303271),(145,303271),(146,172327),(153,99496),(154,171106)]),([6,15,240,580,1911,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,296962),(81,301058),(109,303107),(114,171106),(117,171106),(134,138338),(138,138338),(146,171106),(157,171106),(158,303107)]),([6,15,240,580,1911,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(81,1319),(98,303107),(109,303107),(110,303107),(114,303107),(117,303107),(133,295939),(134,303107),(138,303107),(146,305155),(157,99496),(158,171106)]),([6,15,240,580,2034,2184],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239),(130,303107),(133,296962),(137,139559),(142,303107),(145,303107),(146,139559),(153,99464),(158,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_113 : K_113.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_114 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,2184,2186],[(0,303107),(2,296969),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(102,303107),(105,139559),(106,303107),(113,303107),(114,139559),(134,99464),(137,139559),(138,99464),(145,303107),(146,139559),(154,303107),(157,303107)]),([6,15,240,580,2184,2269],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(81,1319),(98,303107),(101,1315),(105,303107),(110,303107),(113,303107),(133,295939),(134,303107),(137,303107),(138,303107),(146,172327),(154,303107),(157,303107)]),([6,15,240,580,2184,2764,2986],[(72,296962),(80,301058),(136,301058),(144,303107),(148,99496),(152,99496),(156,99496),(184,303271),(192,99496),(200,99496)]),([6,15,240,580,2184,2764,3293],[(72,1315),(80,1319),(136,1319),(144,303107),(148,303107),(156,303107),(172,132391),(184,305155),(200,305155)]),([6,15,240,580,2184,2986],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(73,296962),(81,301058),(105,303107),(113,303107),(114,99496),(134,99464),(138,99464),(146,99496),(154,99496),(157,99496)]),([6,15,240,580,2184,3054],[(0,99496),(2,296971),(4,99496),(6,301195),(8,99496),(10,170281),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(74,99496),(105,141607),(113,303271),(114,99496),(134,99464),(138,99464),(146,99496),(149,99496),(154,99496),(157,99496)]),([6,15,240,580,2184,3066],[(0,99464),(2,99464),(4,99464),(6,301193),(8,99464),(10,2345),(12,99464),(14,138338),(16,99464),(18,99464),(57,99464),(58,99464),(73,296962),(105,139559),(113,303107),(114,99464),(134,99464),(138,99464),(141,99464),(146,99464),(154,99464),(157,99464)]),([6,15,240,580,2184,3085],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(98,303107),(105,139559),(110,303107),(113,303107),(114,139559),(133,295939),(134,303107),(137,139559),(138,303107),(146,305155),(153,303107),(154,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_114 : K_114.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_115 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,2184,3225],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(98,303271),(105,141607),(110,303271),(113,303271),(114,141607),(134,303239),(138,303239),(145,303271),(146,305155),(154,303271),(157,303271)]),([6,15,240,580,2184,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(81,1319),(98,303107),(105,303107),(110,303107),(113,303107),(133,295939),(134,303107),(138,303107),(146,305155),(154,303107),(157,303107)]),([6,15,240,580,2184,3293,3515],[(72,2338),(80,1319),(132,132391),(144,2347),(172,1315),(180,1319),(196,303107),(204,303271)]),([6,15,240,580,2184,3293,3805],[(132,305155),(156,305155),(172,295939),(188,303107),(196,303107),(200,305155),(204,303107)]),([6,15,240,580,2184,3325],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(81,1319),(98,303107),(105,303107),(110,303107),(113,303107),(133,295939),(134,303107),(138,303107),(141,303107),(146,305155),(154,303107),(157,303107)]),([6,15,240,580,2184,3805],[(0,305155),(2,296971),(4,305155),(6,301195),(8,305155),(10,2347),(12,305155),(14,305155),(16,305155),(18,305155),(57,305155),(58,305155),(98,305155),(105,141607),(110,305155),(113,305155),(114,306275),(133,305155),(134,303107),(138,305155),(146,305155),(149,305155),(154,305155),(157,305155)]),([6,15,240,580,2184,4010],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(73,296962),(81,301058),(101,296962),(105,303107),(113,303107),(114,99496),(133,296969),(134,99464),(138,99464),(141,301058),(146,99496),(154,99496),(157,99496)]),([6,15,240,580,2184,4082],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(61,296962),(73,296962),(77,296071),(97,303107),(98,303107),(101,296962),(105,139559),(110,303107),(113,303107),(114,306275),(129,296962),(133,296969),(134,303107),(138,303107),(141,303107),(146,303239),(154,99464),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_115 : K_115.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_116 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,2184,4093],[(0,303107),(2,296969),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(98,303107),(105,139559),(110,303107),(113,303107),(114,306275),(133,303107),(134,303107),(138,303107),(141,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,240,580,2191,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,1319),(98,303107),(101,303107),(105,303107),(110,303107),(133,303107),(134,303107),(138,303107),(146,305155),(157,303107),(158,303107)]),([6,15,240,580,2764,2986],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,99496),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(73,296962),(74,100354),(81,301058),(82,99463),(105,301058),(114,99496),(117,99496),(134,99464),(138,99464),(146,99496),(149,100354),(154,99496),(157,99496)]),([6,15,240,580,2764,3054],[(0,99496),(2,296971),(4,99496),(6,301195),(8,99496),(10,100652),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(82,99495),(114,99496),(117,99496),(134,99464),(138,99464),(146,99496),(149,99496),(154,99496),(157,99496)]),([6,15,240,580,2764,3293],[(57,164968),(58,105634),(73,1315),(78,1324),(81,1319),(105,1319),(110,303107),(134,306275),(146,306275),(149,1324),(154,306275),(157,303203)]),([6,15,240,580,2986,3208],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,99496),(16,99496),(18,171106),(57,99496),(58,99496),(73,99496),(81,99496),(101,99339),(102,99464),(106,99464),(109,99467),(114,99496),(133,296962),(137,303107),(145,303107),(146,99496),(153,99496),(158,99496)]),([6,15,240,580,2986,3293],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,99496),(16,99496),(18,171106),(57,99496),(58,99496),(73,99496),(81,99496),(98,1192),(110,1192),(114,99496),(133,295939),(146,99496),(157,303107),(158,99496)]),([6,15,240,580,3208,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,1315),(81,1319),(98,303107),(101,1315),(105,303107),(110,303107),(113,303107),(133,295939),(134,303107),(137,303107),(138,303107),(146,172327),(154,303107),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_116 : K_116.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_117 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,580,3208,4010],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,171106),(16,99496),(18,99496),(57,99496),(58,99496),(73,296962),(81,301058),(101,296962),(105,303107),(113,303107),(114,99496),(133,296969),(134,99464),(138,99464),(141,301058),(146,99496),(154,99496),(157,99496)]),([6,15,240,582,802,2184],[(0,303107),(2,295947),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(81,10530),(98,303106),(102,303107),(106,303107),(110,303106),(114,303271),(118,8482),(130,303107),(137,303107),(142,303107),(145,303107),(146,10530),(153,303107),(154,303107),(157,303106)]),([6,15,240,582,1024,2184],[(0,303106),(2,295945),(4,303106),(6,301193),(8,303106),(10,1321),(12,303106),(14,303106),(16,303106),(18,303106),(57,303106),(58,303106),(97,8482),(98,303106),(102,303106),(105,139559),(106,303106),(110,303106),(113,303106),(114,139559),(118,303106),(130,303106),(137,139559),(142,303106),(145,303106),(146,306274),(153,303106),(154,303106),(157,303106)]),([6,15,240,582,2184],[(1,303106),(3,303106),(5,303106),(7,303106),(9,139559),(11,139559),(13,303106),(15,303106),(59,303106),(63,303106),(75,139559),(79,303239),(83,8482),(87,303106),(99,303106),(103,303106),(107,303106),(111,303106),(115,139559),(119,303106)]),([6,15,240,588,802,2184],[(0,100488),(2,100488),(4,100488),(6,100488),(8,100488),(10,2345),(12,100488),(14,100488),(16,100488),(18,138339),(57,100488),(58,100488),(73,100488),(81,100488),(97,100488),(102,100488),(106,100488),(114,100488),(129,100364),(137,303107),(145,303107),(153,303107),(154,100488)]),([6,15,240,591,756,802,2184],[(60,296962),(72,296962),(84,141315),(104,301058),(116,303107),(152,303239),(168,11399),(180,301058)]),([6,15,240,591,802,870,2184],[(56,105634),(80,105634),(132,10375),(148,303107),(152,303271),(184,303240),(192,171011)]),([6,15,240,591,802,1604,2184],[(56,105634),(72,295939),(76,303107),(80,301058),(116,305154),(148,303107),(152,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_117 : K_117.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_118 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,591,802,2184,2764],[(56,105634),(72,295939),(76,303107),(80,301058),(132,295939),(148,303107),(152,100354),(176,141315),(188,100488),(192,99496)]),([6,15,240,591,802,2184,3515],[(56,105634),(72,2338),(76,2345),(80,301058),(172,296962)]),([6,15,240,591,870,2184],[(0,303271),(2,303271),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(57,303271),(58,303271),(74,303271),(77,303271),(101,10407),(102,303239),(106,303239),(117,303271),(118,139559),(129,109735),(130,303271),(137,141607),(142,303271),(145,303271),(146,141607),(153,99496),(154,171106)]),([6,15,240,612,802,2184],[(0,169986),(2,169986),(4,169986),(6,169986),(8,169986),(10,2345),(12,169986),(14,1191),(16,169986),(18,169986),(57,169986),(58,169986),(73,169986),(81,169986),(97,296962),(105,170121),(130,169986),(137,169986),(142,169986),(145,303107),(146,169986),(153,169986),(154,303107)]),([6,15,240,708,802],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107)]),([6,15,240,708,802,1024],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,15,240,708,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,15,240,756,802,870,2184],[(56,164968),(128,10375),(140,169986),(148,169986),(192,170120),(200,170082)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_118 : K_118.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_119 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,756,802,1024,2764],[(56,164963),(80,301058),(112,303239),(136,141411),(140,301058),(180,142339),(188,303107)]),([6,15,240,756,802,1604,2184],[(56,164968),(72,295939),(80,301058),(84,303107),(112,303239),(140,141315),(148,303107),(180,301058),(188,303107)]),([6,15,240,756,802,2184,2764],[(56,164968),(72,295939),(80,301058),(84,303107),(112,303239),(140,301058),(152,99463),(180,141315),(188,303107)]),([6,15,240,756,802,2184,3515],[(56,164968),(72,2338),(80,301058),(84,2345),(112,137513),(140,301058),(148,2345),(180,301058)]),([6,15,240,756,802,2764],[(62,301058),(73,296962),(78,303239),(81,301058),(97,296962),(102,306275),(105,172131),(109,301058),(113,303239),(114,10531),(137,301058),(141,141411),(142,303107),(153,99495),(154,170082)]),([6,15,240,802,870,1604,2184],[(96,295939),(108,303107),(112,303271),(116,303107),(156,303107),(184,171106),(192,303203),(200,303240)]),([6,15,240,802,870,2184,2764],[(96,295939),(112,303271),(116,303107),(136,303240),(148,303240),(196,303107),(200,303240)]),([6,15,240,802,870,2184,3515],[(96,2338),(112,170281),(116,2345),(144,171106),(152,100649),(188,305155)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_119 : K_119.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_120 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,802,870,2764],[(0,303240),(2,303240),(4,303240),(6,303240),(8,303240),(10,303240),(12,303240),(14,303240),(16,303240),(18,138537),(57,303240),(58,303240),(73,296072),(74,303240),(78,303240),(82,303240),(86,303240),(97,296072),(102,303239),(106,303239),(113,303240),(114,303240),(117,303240),(130,303240),(145,303271)]),([6,15,240,802,1024,1604,2764],[(112,305288),(136,172131),(144,303240),(192,305154)]),([6,15,240,802,1024,1604,3788],[(136,172131),(144,303240),(152,305154),(192,305154)]),([6,15,240,802,1024,2764,3515],[(172,303239)]),([6,15,240,802,1331,2184],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,303107),(16,2345),(18,2345),(57,2345),(58,2345),(73,2338),(78,100652),(82,2345),(109,2345),(117,100652),(134,2345),(137,2345),(138,2345),(145,2345),(146,2345),(153,2345)]),([6,15,240,802,1331,2184,2764],[(108,303107),(116,305155),(176,301058),(184,100652),(204,2345)]),([6,15,240,802,1604,1894,2184],[(128,295939),(140,303107),(148,303107),(156,303107),(184,305288),(192,303240),(200,303203)]),([6,15,240,802,1604,1911],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(82,303107),(85,303107),(97,295939),(105,301058),(129,295939),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_120 : K_120.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_121 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,802,1604,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(82,303107),(85,303107),(97,295939),(105,301058),(130,303107),(133,295939),(137,303107),(142,303107),(145,305154),(146,303107),(153,303107),(154,305154)]),([6,15,240,802,1604,2184,2764],[(112,303271),(132,296962),(144,99496),(172,295947),(176,301058),(184,305154),(192,303107),(196,303107),(204,303107)]),([6,15,240,802,1604,2184,3515],[(112,170281),(172,303239),(180,303107),(204,303107)]),([6,15,240,802,1604,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,303107),(82,303107),(85,303107),(97,305154),(105,301058),(130,303107),(133,303107),(137,303107),(142,303107),(146,303107),(154,305154)]),([6,15,240,802,1604,2764],[(57,164968),(58,105634),(73,296962),(78,305288),(82,139559),(85,301058),(97,296962),(102,303239),(105,301058),(113,305288),(114,303240),(137,301058),(142,303107),(145,99496),(146,303203),(154,305154)]),([6,15,240,802,1604,2986],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,99496),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(85,303107),(97,295939),(105,171106),(113,305288),(130,303107),(133,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303203)]),([6,15,240,802,1604,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(97,295939),(105,301058),(113,303271),(130,303107),(133,295939),(137,303107),(142,303107),(145,99496),(146,303107),(153,303107),(154,305154)]),([6,15,240,802,1604,3788],[(0,305154),(2,305154),(4,305154),(6,305154),(8,305154),(10,1323),(12,305154),(14,305154),(16,305154),(18,305154),(57,305154),(58,305154),(73,296962),(82,305154),(85,301058),(97,296962),(102,303239),(105,301058),(106,305154),(114,303240),(130,305154),(133,305154),(137,301058),(142,303107),(146,303203),(154,305154),(157,305154)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_121 : K_121.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_122 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,802,1911,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(102,303107),(106,303107),(109,303107),(114,303107),(117,303107),(137,301058),(145,303271),(158,303107)]),([6,15,240,802,1911,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(98,2345),(109,2345),(110,2345),(114,2345),(117,2345),(133,137513),(141,2345),(149,2347),(158,2345)]),([6,15,240,802,2184,2491],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,1323),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(82,2345),(85,2345),(98,2345),(101,2338),(105,2345),(110,2345),(113,305154),(114,2345),(133,137513),(141,2345),(154,2345),(157,2345)]),([6,15,240,802,2184,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(102,303107),(105,303107),(106,303107),(113,303107),(114,303107),(137,301058),(145,303271),(154,303107),(157,303107)]),([6,15,240,802,2184,2764,2764],[(136,301058),(144,303271),(156,303107),(160,303107),(164,303107)]),([6,15,240,802,2184,2764,2767],[(100,295939),(136,141315),(144,303271),(172,303107),(176,301058),(196,303107),(204,303107)]),([6,15,240,802,2184,2764,2812],[(140,141315),(176,301058),(180,303107),(184,303239),(196,303107),(204,303107)]),([6,15,240,802,2184,2764,3054],[(184,303271),(188,303107),(196,303107),(204,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_122 : K_122.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_123 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,802,2184,2764,3515],[(112,99496),(136,301058),(144,170281),(156,2345),(172,303239),(180,303107),(188,305155),(196,303107)]),([6,15,240,802,2184,2764,3788],[(100,296962),(132,295947),(136,301058),(144,303271),(156,303107),(184,303271),(196,303107),(200,303107),(204,303107)]),([6,15,240,802,2184,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(98,2345),(105,2345),(110,2345),(113,2345),(114,2345),(133,137513),(141,2345),(149,2347),(154,2345),(157,2345)]),([6,15,240,802,2184,3515,3515],[(132,137513),(140,2345),(148,2347),(156,2345),(160,2345),(164,2345)]),([6,15,240,802,2184,3515,3519],[(132,137513),(172,2345),(180,2345),(188,2347),(196,2345),(204,2345)]),([6,15,240,802,2184,3515,3579],[(140,2345),(172,137513),(180,2345),(188,2347),(196,2345),(204,2345)]),([6,15,240,802,2184,3515,4027],[(172,137513),(180,2345),(188,2345),(196,2345),(204,2345)]),([6,15,240,802,2184,3788],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,305154),(57,303107),(58,303107),(73,295939),(82,303107),(85,303107),(101,295939),(102,303107),(105,303107),(106,303107),(113,303107),(114,303107),(133,295947),(137,301058),(154,303107),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_123 : K_123.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_124 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,802,2191,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2345),(78,2345),(82,2345),(98,2345),(101,2345),(105,2345),(110,2345),(114,2345),(117,2345),(133,137513),(141,2345),(149,2347),(157,137513)]),([6,15,240,802,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(62,303107),(73,295939),(78,303107),(81,303107),(82,303107),(85,303107),(102,303107),(105,303107),(106,303107),(109,303107),(113,303107),(114,303107),(141,303107),(145,303271),(157,303107)]),([6,15,240,802,2764,2986],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(74,100354),(82,303107),(117,100354),(134,303107),(138,303107),(146,303107),(149,303107),(158,306178)]),([6,15,240,802,2764,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(78,100652),(82,303107),(85,100491),(101,100363),(105,301058),(113,100652),(133,295939),(134,303107),(137,303107),(138,303107),(145,303107),(146,303107),(153,303107),(158,303107)]),([6,15,240,802,2764,3515],[(57,164968),(58,105634),(73,296962),(78,100652),(82,139559),(105,301058),(110,2345),(113,100652),(114,100649),(133,296962),(134,303239),(141,301058),(146,303240),(149,100652),(157,2345),(158,303107)]),([6,15,240,802,2986,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,171106),(57,2345),(58,2345),(73,2338),(98,2345),(110,2345),(114,2345),(117,2345),(133,137513),(141,2345),(149,2348),(157,171106)]),([6,15,240,802,3208,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(85,2345),(98,2345),(101,2338),(105,2345),(110,2345),(113,2345),(114,2345),(133,137513),(141,2345),(149,172327),(154,2345),(157,2345)]),([6,15,240,802,3208,3788],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(101,295939),(102,303107),(105,303107),(106,303107),(113,303107),(114,303107),(133,296071),(137,301058),(145,303271),(154,303107),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_124 : K_124.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_125 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,870,1024,2764],[(0,303240),(2,297068),(4,303240),(6,301225),(8,303240),(10,1324),(12,303240),(14,303240),(16,303240),(18,138537),(57,303240),(58,303240),(82,303239),(85,303240),(97,303240),(98,303240),(102,303240),(105,303240),(106,303240),(110,303240),(113,303240),(114,303240),(118,303240),(130,303240),(133,295948),(153,306178),(154,303240),(157,303240)]),([6,15,240,870,1604,2184],[(0,303271),(2,297068),(4,303271),(6,301225),(8,303271),(10,1323),(12,303271),(14,170281),(16,303271),(18,303271),(57,303271),(58,303271),(82,303239),(85,303243),(98,303271),(118,303271),(130,303271),(137,172327),(142,303271),(145,305154),(146,303271),(153,303271),(154,305154)]),([6,15,240,870,2184,2764],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,303271),(12,303271),(14,303271),(16,303271),(18,170281),(57,303271),(58,303271),(78,303239),(82,303239),(98,303271),(102,303240),(105,303271),(106,303240),(110,303271),(113,303271),(114,303271),(118,303240),(130,303271),(145,303271),(150,303271),(153,306178),(154,303271),(157,303271)]),([6,15,240,870,2184,3515],[(0,170281),(2,296971),(4,170281),(6,301195),(8,170281),(10,170281),(12,170281),(14,170281),(16,170281),(18,303271),(57,170281),(58,170281),(78,137513),(82,137513),(98,170281),(105,170281),(110,170281),(113,170281),(114,170281),(130,170281),(149,2347),(150,305155),(154,170281),(157,170281)]),([6,15,240,870,2764],[(1,303240),(3,303240),(5,303240),(7,303240),(9,303240),(11,303240),(13,306178),(15,306178),(59,303240),(63,303240),(75,303240),(79,303240),(83,303240),(87,303240),(99,306178),(103,303240),(107,306178),(111,306178),(115,303271),(119,141607)]),([6,15,240,1010,1604,2184],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(73,295939),(82,303107),(85,303107),(97,295939),(130,303107),(133,295939),(137,139559),(142,303107),(145,305154),(150,303107),(153,303107),(154,305154)]),([6,15,240,1010,2184,2764],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(102,303107),(105,303107),(106,303107),(113,303107),(114,303107),(145,303239),(154,303107),(157,303107)]),([6,15,240,1010,2184,3515],[(0,2345),(2,2345),(4,2345),(6,301193),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(85,2345),(98,2345),(105,2345),(110,2345),(113,2345),(118,2345),(133,137513),(149,2347),(154,2345),(157,2345)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_125 : K_125.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_126 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,1604,2184,2986],[(0,305154),(2,305154),(4,305154),(6,305154),(8,305154),(10,305154),(12,305154),(14,305154),(16,305154),(18,99496),(57,305154),(58,305154),(73,296962),(81,301058),(101,296962),(105,305154),(113,303107),(114,99496),(133,296969),(138,305154),(141,301058),(154,305154),(157,305154)]),([6,15,240,1604,2184,3293],[(0,1323),(2,1323),(4,1323),(6,1323),(8,1323),(10,1323),(12,1323),(14,1323),(16,1323),(18,303107),(57,1323),(58,1323),(73,1315),(81,1319),(98,1323),(101,1315),(105,1323),(110,1323),(113,303107),(114,1323),(133,295939),(137,303107),(138,1323),(154,1323),(157,1323)]),([6,15,240,1826,2184,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(101,295939),(102,303107),(105,303107),(106,303107),(113,303107),(114,303107),(133,296071),(137,301058),(145,303271),(154,303107),(157,303107)]),([6,15,240,1826,2184,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(85,2345),(98,2345),(101,2338),(105,2345),(110,2345),(113,2345),(114,2345),(133,137513),(141,2345),(149,172327),(154,2345),(157,2345)]),([6,15,240,2184,2764,2986],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(74,100354),(81,303107),(82,303107),(105,301058),(114,303107),(117,303107),(134,303107),(138,303107),(146,303107),(149,303107),(154,303271)]),([6,15,240,2184,2764,3054],[(0,303271),(2,296971),(4,303271),(6,301195),(8,303271),(10,303271),(12,303271),(14,100652),(16,303271),(18,303271),(57,303271),(58,303271),(81,303271),(82,303271),(98,303271),(114,303271),(117,303271),(134,303239),(138,303239),(146,303271),(149,303271),(154,303271),(157,303271)]),([6,15,240,2184,2764,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(78,1324),(81,303107),(82,303107),(105,1319),(114,303107),(117,303107),(133,295939),(134,303107),(138,303107),(146,303107),(149,303107),(154,305155)]),([6,15,240,2184,2986,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,99496),(57,2345),(58,2345),(81,2345),(102,2345),(106,2345),(114,2345),(117,2345),(133,137513),(141,2345),(146,2345),(149,2345),(157,2347)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_126 : K_126.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_127 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,2184,3293,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2345),(58,2345),(74,2345),(81,2345),(86,2345),(101,2338),(102,2345),(106,2345),(114,2345),(117,2345),(133,137513),(141,2345),(146,2345),(149,2345),(157,170281)]),([6,15,242,580,802,2184],[(0,303107),(2,164875),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(73,10402),(81,10402),(98,303107),(102,303107),(106,303107),(110,303107),(114,303271),(118,139266),(130,303107),(137,303107),(142,303107),(145,303107),(146,10402),(153,303107),(154,303107),(157,303107)]),([6,15,242,580,1024,2184],[(0,303107),(2,132105),(4,303107),(6,1161),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(97,8322),(98,303107),(102,303107),(105,139266),(106,303107),(110,303107),(113,303107),(114,139266),(118,303107),(130,303107),(137,139266),(142,303107),(145,303107),(146,306275),(153,303107),(154,303107),(157,303107)]),([6,15,242,580,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,139266),(11,139266),(13,303107),(15,303107),(59,303107),(63,303107),(75,139266),(79,303239),(83,8322),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(115,139266),(119,303107)]),([6,15,244,580,802,2184],[(0,303239),(2,303239),(4,303239),(6,303239),(8,303239),(10,137513),(12,303239),(14,303239),(16,303239),(18,303239),(57,303235),(58,303107),(74,303239),(81,301058),(97,296071),(102,303239),(106,303239),(114,303271),(130,303239),(137,303239),(142,303239),(145,303239),(153,99496),(154,171106)]),([6,15,248,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107)]),([6,15,255,580,591,802,2184],[(56,105634),(96,105634),(100,303107),(104,301058),(116,303107),(132,139555),(144,303271)]),([6,15,255,580,756,802,2184],[(56,164968),(60,301058),(104,301058),(108,303239),(116,303107),(132,8483),(152,303239),(180,301058),(196,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_127 : K_127.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_128 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,255,580,802,1911],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,105634),(81,301058),(102,303107),(110,303107),(114,303271),(130,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,15,255,580,802,2184],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,105634),(81,301058),(102,303107),(110,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(146,105634),(153,99496),(154,171106)]),([6,15,255,580,802,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(81,301058),(97,303107),(102,303107),(110,303107),(114,303271),(130,303107),(133,303107),(137,303107),(142,303107),(154,171010),(157,303107)]),([6,15,255,580,802,2764],[(0,105634),(2,164968),(4,105634),(6,105634),(8,105634),(10,105634),(12,105634),(14,105634),(16,105634),(18,105634),(58,105634),(61,105634),(73,105634),(78,303239),(81,301058),(86,303240),(102,306275),(110,306275),(113,303240),(114,141607),(137,301058),(142,303203),(146,105634),(149,105634),(153,99496),(154,171106)]),([6,15,255,580,802,2986],[(0,171106),(2,164968),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(58,171106),(61,171106),(73,171106),(81,171106),(110,303107),(114,171106),(130,171010),(133,171106),(142,171106),(146,171106),(154,171106),(157,171106)]),([6,15,255,580,802,3208],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,105634),(81,301058),(102,303107),(109,301193),(110,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(146,105634),(153,99496),(154,171106)]),([6,15,255,580,870,2184],[(0,303271),(2,164968),(4,303271),(6,301195),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(58,303271),(61,303271),(73,105634),(74,303271),(102,303239),(110,303271),(114,303271),(117,303271),(130,303271),(137,141607),(142,303271),(145,303271),(146,141607),(153,99496),(154,171106)]),([6,15,255,580,1010,2184],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,139559),(101,303107),(102,303107),(109,303107),(110,303107),(114,303239),(129,303107),(130,303107),(137,139559),(142,303107),(145,303107),(146,139559),(153,99464),(158,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_128 : K_128.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_129 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,255,580,1826,2184],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,105634),(81,301058),(102,303107),(109,301193),(110,303107),(114,303271),(130,303107),(137,303107),(142,303107),(145,303107),(146,105634),(153,99496),(154,171106)]),([6,15,255,580,2184,2986],[(0,99496),(2,164968),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,171106),(16,99496),(18,99496),(58,99496),(61,99496),(73,99496),(81,301058),(105,99496),(110,303107),(113,303107),(114,99496),(133,99496),(134,99464),(142,99496),(146,99496),(154,99496),(157,99496)]),([6,15,255,580,2184,3293],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,105634),(81,1319),(98,303107),(105,303107),(110,303107),(113,303107),(114,105634),(134,303107),(142,303107),(146,305155),(154,303107),(157,303107)]),([6,15,255,802,1604,2184],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(85,303107),(97,105634),(105,301058),(130,303107),(137,303107),(142,303107),(145,305154),(146,303107),(153,303107),(154,305154)]),([6,15,255,802,2184,2764],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(58,303107),(61,303107),(78,303107),(86,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(137,301058),(145,303271),(154,303107),(157,303107)]),([6,15,255,802,2184,3515],[(0,2345),(2,164968),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(58,2345),(61,2345),(78,2345),(86,2345),(98,2345),(105,2345),(110,2345),(113,2345),(114,2345),(133,133417),(141,301058),(149,2347),(154,2345),(157,2345)]),([6,15,512,580,752,802,2184],[(80,301058),(104,301058),(136,301058)]),([6,15,512,580,756,802,2184],[(56,296962),(72,141315),(80,301058),(104,301058),(136,301058),(184,141411)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_129 : K_129.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_130 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,512,580,802,2184,2296],[(56,296962),(80,303107),(104,303107),(176,301058)]),([6,15,512,580,802,2184,3855],[(56,296962),(80,303107),(104,303107),(176,303107)]),([6,15,516,580,802,2184,3855],[(56,296962),(72,6283),(80,303107),(104,303239),(176,303107),(184,303107)]),([6,15,544,580,756,802,2184],[(56,296962),(72,141315),(80,169986),(104,301058),(136,301058),(176,171010),(184,141411)]),([6,15,544,580,802,1024,2184],[(80,169986),(136,172171),(176,172168)]),([6,15,580,580,802,2184,2296],[(56,296962),(64,303107),(68,303107),(104,141607),(176,301058)]),([6,15,580,580,802,2184,3855],[(56,296962),(64,303107),(68,303107),(104,301195),(176,301058)]),([6,15,580,591,802,2184,2296],[(72,296962),(76,303107),(84,303107),(104,141607),(168,105634),(176,141315),(184,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_130 : K_130.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_131 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,591,802,2184,3855],[(72,296962),(76,303107),(84,303107),(104,301195),(168,296962),(184,301058)]),([6,15,580,752,802,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,301058),(73,301058),(74,301058),(82,301058),(130,301058),(137,301058),(138,301058),(145,301058),(150,301058),(153,301058),(154,171106)]),([6,15,580,756,802,802,2184],[(56,141315),(96,296962),(120,301058),(124,301058),(176,141411),(192,171106)]),([6,15,580,756,802,815,2184],[(56,296962),(128,296962),(132,301058),(136,169986),(156,301058),(176,141411),(200,171010)]),([6,15,580,756,802,870,2184],[(128,296962),(140,301058),(156,301058),(192,301192),(200,171106)]),([6,15,580,756,802,1010,2184],[(56,172035),(96,296962),(128,296962),(140,301058),(148,301058),(156,301058),(176,172131),(204,301058)]),([6,15,580,756,802,1014,2184],[(56,10371),(128,296962),(140,301058),(148,301058),(156,301058),(204,301058)]),([6,15,580,756,802,1264,2184],[(56,296962),(72,164968),(112,139559),(140,141315),(148,303107),(176,141411),(204,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_131 : K_131.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_132 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,756,802,1826,2184],[(56,172035),(96,296962),(152,301058),(156,301058),(176,172131),(192,171106),(200,171106)]),([6,15,580,756,802,1911],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962),(130,301058),(138,301058),(141,301058),(149,301058),(150,301058),(154,301058),(157,301058)]),([6,15,580,756,802,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962),(130,301058),(137,301058),(138,301058),(145,301058),(150,301058),(153,301058),(154,171106)]),([6,15,580,756,802,2184,2296],[(56,296962),(84,303107),(112,139559),(180,141315),(184,301058),(188,303107),(204,301058)]),([6,15,580,756,802,2184,2986],[(56,141315),(96,296962),(192,301058),(196,301058),(200,171106),(204,301058)]),([6,15,580,756,802,2184,3293],[(56,141315),(96,1315),(136,141411),(152,99496),(204,301058)]),([6,15,580,756,802,2184,3855],[(56,296962),(72,105634),(84,303107),(112,301193),(148,303107),(172,301058),(176,301058),(196,301058)]),([6,15,580,756,802,2191],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,301058),(58,301058),(73,301058),(74,301058),(82,301058),(85,301058),(130,301058),(133,301058),(137,301058),(138,301058),(145,301058),(150,301058),(154,171010)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_132 : K_132.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_133 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,756,802,2764],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(62,301058),(73,296962),(74,301058),(81,301058),(82,301058),(85,301058),(97,296962),(109,141411),(130,301058),(137,301058),(138,301058),(141,301058),(145,301058),(150,301058),(154,171106)]),([6,15,580,756,802,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,171106),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(74,171106),(82,171106),(85,171106),(106,301192),(130,171010),(137,171106),(138,171106),(150,171010),(154,171106),(157,171106)]),([6,15,580,756,802,3208],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962),(130,301058),(133,296962),(137,301058),(138,301058),(145,301058),(150,301058),(153,301058),(154,171106)]),([6,15,580,756,1826,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962),(130,301058),(133,296962),(137,301058),(138,301058),(145,301058),(150,301058),(153,301058),(154,171106)]),([6,15,580,756,2184,2986],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,301058),(16,301058),(18,99496),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(105,301058),(106,301058),(113,301058),(137,99496),(154,301058),(157,301058)]),([6,15,580,756,2184,3293],[(0,1319),(2,1319),(4,1319),(6,1319),(8,1319),(10,1319),(12,1319),(14,1319),(16,1319),(18,301058),(57,1315),(58,1319),(73,1315),(74,1319),(82,1319),(85,1319),(98,1319),(105,1319),(106,1319),(113,1319),(118,1319),(154,1319),(157,1319)]),([6,15,580,767,802,2184],[(0,301058),(2,164968),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(74,301058),(77,301058),(82,301058),(85,301058),(105,105634),(118,301058),(130,301058),(137,301058),(138,301058),(145,301058),(150,301058),(153,301058),(154,171106)]),([6,15,580,770,1024,2184],[(0,301058),(2,301058),(4,301058),(6,2345),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(73,296962),(97,301058),(98,301058),(105,303107),(106,301058),(113,301058),(114,303107),(130,301058),(133,296962),(137,303107),(138,301058),(145,301058),(146,303107),(153,301058),(154,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_133 : K_133.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_134 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,770,2184,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(105,303107),(113,303107),(114,303107),(130,303107),(133,303107),(138,301058),(146,303107),(149,303107),(153,303107),(154,303107)]),([6,15,580,802,870,2184,2296],[(96,296962),(108,303107),(112,141607),(116,303107),(136,303240)]),([6,15,580,802,870,2184,3855],[(96,296962),(108,303107),(112,301195),(116,303107),(136,303240),(144,171106),(152,171106)]),([6,15,580,802,1024,1264,2764],[(80,303240),(96,172043),(136,172131)]),([6,15,580,802,1024,2216],[(0,172168),(2,172168),(4,172168),(6,2345),(8,172168),(10,1192),(12,172168),(14,172168),(16,172168),(18,138409),(57,172168),(73,165000),(97,172168),(98,172168),(105,172168),(106,172168),(113,172168),(114,172168),(130,172168),(133,164872),(137,303107),(138,172168),(153,171010),(154,172168)]),([6,15,580,802,1024,2296,2764],[(80,303240),(108,303107),(176,303107)]),([6,15,580,802,1024,2764,3855],[(80,301225),(188,301058),(200,301058)]),([6,15,580,802,1024,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301192),(82,301192),(97,303107),(98,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(118,303107),(130,303107),(133,303107),(138,301058),(149,303107),(153,303107),(154,303107),(157,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_134 : K_134.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_135 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,802,1056,2184],[(0,172171),(2,172171),(4,172171),(6,2345),(8,172171),(10,1195),(12,172171),(14,141481),(16,172171),(18,172171),(57,172171),(73,165003),(97,164875),(98,172171),(105,303107),(106,172171),(130,172171),(133,164875),(137,303107),(138,172171),(145,174082),(146,172171),(153,172171),(154,174082)]),([6,15,580,802,1264,1604,2184],[(56,295939),(80,303243),(104,301058),(128,109707),(136,303107)]),([6,15,580,802,1264,3208],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,172327),(97,164968),(98,303107),(106,301058),(113,139559),(118,301058),(130,303107),(133,296962),(137,303107),(145,99496),(146,171106),(153,303107),(158,303107)]),([6,15,580,802,1604,2184,2296],[(56,295939),(80,172327),(104,303107),(108,303107),(112,172327),(176,301058)]),([6,15,580,802,1604,2184,3855],[(56,295939),(80,301225),(104,303107),(108,303107),(112,301225),(176,303107),(188,301058),(192,301058)]),([6,15,580,802,1799,2184],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(106,301058),(117,303107),(130,303107),(137,303107),(145,303107),(146,303107),(153,303107),(154,303107)]),([6,15,580,802,1911,2296],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,141607),(98,303107),(106,303107),(109,303107),(114,303107),(117,303107),(130,303107),(138,301058),(145,139559),(157,303107),(158,303107)]),([6,15,580,802,1911,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(106,303107),(109,303107),(114,303107),(117,303107),(130,303107),(133,303107),(138,301058),(149,303107),(153,303107),(158,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_135 : K_135.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_136 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,802,2184,2296],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,141607),(98,303107),(105,303107),(113,303107),(114,303107),(130,303107),(138,301058),(145,139559),(154,303107),(157,303107)]),([6,15,580,802,2184,2296,2764],[(56,295939),(80,303271),(108,303107),(136,301058),(176,303107),(180,303107),(184,141607),(196,303107),(200,301058)]),([6,15,580,802,2184,2296,2812],[(56,295939),(140,141315),(156,301058),(180,303107),(184,139559),(196,303107),(200,301058),(204,303107)]),([6,15,580,802,2184,2296,3515],[(56,2338),(80,170281),(136,301058),(172,296962),(188,141607),(196,303107),(204,301058)]),([6,15,580,802,2184,2303],[(0,303107),(2,164968),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,105634),(78,139559),(82,141607),(98,303107),(105,303107),(106,105634),(113,99496),(114,171106),(130,303107),(133,303107),(138,301058),(149,139559),(154,303107),(157,303107)]),([6,15,580,802,2184,2764,3855],[(56,295939),(80,301195),(112,99496),(136,303107),(140,303107),(144,301195),(156,303107),(176,303107),(200,301058)]),([6,15,580,802,2184,2812],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(58,141315),(73,296962),(98,301058),(105,301058),(106,301058),(113,301058),(130,301058),(138,301058),(141,301058),(154,301058),(157,301058)]),([6,15,580,802,2184,3339],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(58,2187),(73,296962),(98,301058),(105,301058),(106,301058),(113,301058),(114,171106),(130,301058),(133,296962),(137,2345),(138,301058),(153,301058),(154,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_136 : K_136.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_137 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,802,2184,3515,3855],[(56,2338),(80,301195),(132,296962),(148,301195),(156,303107),(176,2345),(204,301058)]),([6,15,580,802,2184,3840],[(0,303107),(2,164968),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,105634),(78,301193),(82,301195),(98,303107),(105,303107),(106,105634),(113,99496),(114,171106),(129,105634),(130,303107),(138,301058),(145,303107),(153,303107),(154,303107)]),([6,15,580,802,2184,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,301058),(149,303107),(153,303107),(154,303107)]),([6,15,580,802,2184,3919],[(0,301058),(2,301058),(4,301058),(6,2345),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(73,296962),(98,301058),(105,303107),(106,301058),(113,301058),(114,171106),(130,301058),(133,301058),(138,301058),(141,301058),(149,301058),(153,301058),(154,301058)]),([6,15,580,802,2184,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301195),(98,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(118,303107),(130,303107),(133,303107),(138,301058),(149,303107),(153,303107),(154,303107),(157,303107)]),([6,15,580,802,2191,2296],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(73,303107),(78,139559),(82,141607),(98,303107),(101,303107),(114,171010),(117,139559),(130,303107),(133,141320),(138,301058),(145,99623),(154,303107),(157,303107)]),([6,15,580,802,2191,2303],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(73,303107),(78,139559),(82,141607),(98,303107),(101,303107),(114,171010),(117,139559),(130,303107),(133,303107),(138,301058),(149,139559),(154,303107),(157,303107)]),([6,15,580,802,2191,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(73,303107),(78,301193),(82,301195),(98,303107),(101,303107),(114,171010),(117,301193),(130,303107),(133,303107),(138,301058),(149,303107),(153,303107),(154,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_137 : K_137.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_138 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,802,2296,2764],[(57,296962),(62,303239),(73,296962),(78,139559),(81,303240),(82,141607),(98,105634),(106,301058),(109,303107),(113,139559),(145,141607),(153,301058),(158,303107)]),([6,15,580,802,2296,2986],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,295939),(73,295939),(74,303107),(98,171106),(117,303107),(130,171010),(146,303107),(149,303107),(158,171010)]),([6,15,580,802,2296,3208],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,172327),(98,303107),(101,296962),(106,301058),(113,139559),(118,301058),(130,303107),(133,296962),(137,303107),(145,303107),(146,303107),(153,303107),(158,303107)]),([6,15,580,802,2764,2812],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(62,301058),(73,296962),(98,301058),(106,301058),(109,301058),(130,301058),(138,301058),(141,301058),(154,301058),(157,301058)]),([6,15,580,802,2764,3855],[(57,296962),(62,303239),(73,296962),(78,301193),(81,303240),(82,301195),(113,301195),(114,171106),(138,301058),(153,303107),(154,301058)]),([6,15,580,802,2986,3855],[(0,171106),(2,171106),(4,171106),(6,2345),(8,171106),(10,99496),(12,171106),(14,171106),(16,171106),(18,171106),(57,171106),(73,295939),(82,171106),(98,171010),(106,171106),(114,171106),(117,171106),(130,171106),(133,171106),(138,171106),(153,171010)]),([6,15,580,802,3208,3320],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,172327),(98,303107),(101,296962),(105,303107),(113,303107),(114,303107),(130,303107),(133,296962),(138,301058),(145,139559),(150,301058),(154,303107),(157,303107)]),([6,15,580,802,3208,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301225),(98,303107),(101,296962),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,301058),(149,303107),(150,303107),(153,303107),(154,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_138 : K_138.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_139 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,802,3855,3983],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,303107),(82,303271),(98,303107),(101,303107),(102,303107),(106,303107),(114,303107),(117,303107),(118,303107),(130,303107),(133,303107),(138,303107),(146,171010),(149,303107),(153,303107),(154,303107),(157,303107)]),([6,15,580,802,3983],[(1,303107),(3,303107),(9,303107),(11,303107),(13,303107),(15,303107),(63,303239),(75,303107),(79,303107),(99,303107),(103,303107),(107,303107),(115,303107),(119,303107)]),([6,15,580,870,2184,2296],[(0,141607),(2,296971),(4,141607),(6,170281),(8,141607),(10,141607),(12,141607),(14,141607),(16,141607),(18,301195),(58,141607),(78,139559),(82,141607),(85,141607),(98,141607),(105,303271),(106,141607),(113,141607),(114,141607),(130,141607),(145,139559),(154,141607),(157,141607)]),([6,15,580,870,2184,3855],[(0,301195),(2,296971),(4,301195),(6,301195),(8,301195),(10,301195),(12,301195),(14,301195),(16,301195),(18,303271),(58,301195),(78,301193),(82,301195),(85,301195),(98,301195),(105,301195),(106,301195),(113,301195),(114,301195),(130,301195),(133,301195),(149,303239),(153,303271),(154,301195)]),([6,15,580,1010,1264,2184],[(0,139559),(2,139559),(4,139559),(6,2345),(8,139559),(10,1163),(12,139559),(14,301193),(16,139559),(18,139559),(57,139559),(73,132391),(82,139559),(97,132107),(98,139559),(118,303107),(130,139559),(133,132107),(137,303107),(138,139559),(145,141314),(150,139559),(153,139559),(158,139559)]),([6,15,580,1010,2184,2296],[(0,139559),(2,139559),(4,139559),(6,2345),(8,139559),(10,139559),(12,139559),(14,139559),(16,139559),(18,301193),(57,139559),(73,132391),(78,139559),(82,139559),(98,139559),(105,303107),(106,139559),(113,139559),(118,139559),(130,139559),(145,139559),(150,303107),(154,139559),(157,139559)]),([6,15,580,1010,2184,3855],[(0,301193),(2,301193),(4,301193),(6,301193),(8,301193),(10,301193),(12,301193),(14,301193),(16,301193),(18,303107),(57,301193),(73,301186),(78,301193),(82,301193),(98,301193),(105,301193),(106,301193),(113,301193),(118,301193),(130,301193),(133,301193),(149,303107),(150,301193),(153,303107),(154,301193)]),([6,15,580,1024,2184,3325],[(0,1319),(2,1319),(4,1319),(6,2345),(8,1319),(10,1319),(12,1319),(14,1319),(16,1319),(18,301058),(57,1315),(73,1319),(74,1319),(81,1319),(82,1319),(98,1319),(101,1315),(105,1319),(106,1319),(113,1319),(114,1319),(133,132391),(146,1319),(149,1319),(154,1319),(157,1319)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_139 : K_139.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_140 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,580,1826,2184,2296],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,139559),(82,172327),(98,303107),(101,296962),(105,303107),(113,303107),(114,303107),(130,303107),(133,296962),(138,301058),(145,139559),(150,301058),(154,303107),(157,303107)]),([6,15,580,1826,2184,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(73,296962),(78,301193),(82,301225),(98,303107),(101,296962),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,301058),(149,303107),(150,303107),(153,303107),(154,303107)]),([6,15,580,2184,2296,2986],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,296962),(74,303107),(81,303107),(98,99496),(106,301058),(114,303107),(117,303107),(134,139559),(138,141607),(146,303107),(149,303107),(154,139559)]),([6,15,580,2184,2296,3066],[(0,139559),(2,139559),(4,139559),(6,2345),(8,139559),(10,139559),(12,139559),(14,301193),(16,139559),(18,139559),(57,296962),(74,99623),(81,303107),(82,139559),(98,139559),(114,139559),(117,139559),(134,139559),(138,139559),(146,139559),(149,139559),(154,139559),(157,139559)]),([6,15,580,2184,2296,3293],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,1315),(74,303107),(81,303107),(98,303107),(106,1319),(114,303107),(117,303107),(133,295939),(134,139559),(138,141607),(146,303107),(149,303107),(154,303107)]),([6,15,580,2184,2986,3855],[(0,99496),(2,99496),(4,99496),(6,2345),(8,99496),(10,171106),(12,99496),(14,99496),(16,99496),(18,99496),(57,296962),(81,303107),(82,99496),(102,301193),(106,301195),(114,99496),(117,99496),(130,99496),(133,99496),(138,301058),(146,303107),(157,99464)]),([6,15,580,2184,3293,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,1315),(74,303107),(81,303107),(101,295939),(102,301193),(106,301195),(114,303107),(117,303107),(130,303107),(133,303107),(138,1319),(145,303107),(146,303107),(157,301193)]),([6,15,591,756,802,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2187),(12,301058),(14,1319),(16,301058),(18,301058),(57,296962),(58,301058),(61,301058),(73,296962),(77,301058),(85,301058),(97,296962),(101,141315),(105,169986),(110,139267),(129,301058),(130,301058),(133,296962),(137,301058),(138,301058),(145,141315),(150,301058),(153,301058),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_140 : K_140.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_141 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,612,802,1024,2184],[(0,169986),(2,169986),(4,169986),(6,2217),(8,169986),(10,1191),(12,169986),(14,169986),(16,169986),(18,169986),(57,165890),(73,165890),(97,169986),(98,169986),(105,172035),(106,169986),(113,169986),(114,172035),(130,169986),(133,165890),(137,172035),(138,169986),(145,169986),(146,172035),(153,169986),(154,169986)]),([6,15,756,802,870,1024,2184],[(96,109699),(108,169986),(184,170120),(192,170082)]),([6,15,756,802,870,2184],[(57,164968),(58,105634),(98,169986),(110,169986)]),([6,15,756,802,1024,2764],[(0,301058),(2,301058),(4,301058),(6,100521),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(73,296962),(97,301058),(98,301058),(102,301058),(105,172131),(106,301058),(110,301058),(113,301058),(114,172131),(118,301058),(130,301058),(133,301058),(142,301058),(146,170082),(153,301058),(154,301058),(157,301058)]),([6,15,756,802,1604,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(97,296962),(98,301058),(105,301058),(110,301058),(130,301058),(133,296962),(137,301058),(142,301058),(145,301058),(146,171106),(153,301058),(154,301058)]),([6,15,756,802,2184,2764],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(98,301058),(102,301058),(105,301058),(106,301058),(110,301058),(113,301058),(118,301058),(130,301058),(137,301058),(142,301058),(153,301058),(154,301058),(157,301058)]),([6,15,756,802,2184,3515],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(58,301058),(73,296962),(98,301058),(105,301058),(110,301058),(113,301058),(114,171106),(130,301058),(133,296962),(141,2345),(142,301058),(154,301058),(157,301058)]),([6,15,756,802,2764],[(1,301058),(3,301058),(5,301058),(7,301058),(9,141411),(11,141411),(13,301058),(15,301058),(59,301058),(63,301058),(75,141411),(79,141411),(87,141411),(99,301058),(103,301058),(107,301058),(111,301058),(115,141411),(119,141411)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_141 : K_141.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_142 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,802,1024,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,295939),(62,303107),(73,303107),(74,303107),(78,303107),(81,303107),(82,303107),(86,303107),(101,295939),(105,303107),(113,303107),(114,303107),(117,303107),(133,296071),(137,303271),(146,303107),(149,303107)]),([6,15,802,1264,1604,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,295939),(62,303107),(73,303107),(74,303107),(81,303107),(86,303107),(97,295939),(105,303271),(113,301058),(130,303107),(133,295939),(137,99496),(138,303107),(145,303107),(150,303107),(153,303107)]),([6,15,802,1604,1780,2184],[(0,301058),(2,301058),(4,301058),(6,1319),(8,301058),(10,301058),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(73,296962),(74,172035),(97,164968),(98,301058),(114,301058),(117,301058),(130,301058),(133,296962),(137,301058),(138,171106),(145,301058),(146,301058),(153,301058),(158,301058)]),([6,15,802,1604,2184,2296],[(0,303107),(2,303107),(4,303107),(6,1323),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,295939),(73,295939),(98,303107),(101,295939),(105,305154),(106,303107),(113,303107),(114,305154),(130,303107),(133,295939),(137,305154),(142,303107),(146,301058),(154,303107),(157,303107)]),([6,15,802,1604,2184,3855],[(0,303107),(2,303107),(4,303107),(6,1323),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,295939),(73,295939),(98,303107),(101,295939),(105,305154),(106,303107),(113,303107),(114,305154),(130,303107),(133,303107),(141,303107),(142,303107),(146,303107),(153,303107),(154,303107)]),([6,15,802,2184,2296,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(57,295939),(62,303107),(74,303107),(78,303107),(81,303107),(82,303107),(86,303107),(98,303107),(105,303107),(113,303107),(114,303107),(117,303107),(137,303271),(146,303107),(149,303107),(153,301058)]),([6,15,802,2184,2296,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(57,2338),(62,2345),(74,2345),(81,2345),(82,2345),(98,2345),(105,2345),(114,2345),(117,2345),(133,137513),(141,2347),(146,2345),(149,2345),(157,2345)]),([6,15,802,2184,2764,2812],[(0,301058),(2,301058),(4,301058),(6,1319),(8,301058),(10,301058),(12,301058),(14,301058),(16,301058),(18,301058),(57,296962),(78,301058),(81,301058),(98,141315),(114,301058),(117,301058),(130,301058),(146,301058),(149,301058),(154,301058),(157,301058)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_142 : K_142.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_143 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,802,2184,2764,3855],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,295939),(62,301193),(78,303107),(81,303107),(82,303107),(105,301195),(114,303107),(117,303107),(130,303107),(133,303107),(141,303107),(146,303107),(149,303107),(154,303107)]),([6,15,802,2184,3515,3855],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,303107),(16,2345),(18,2345),(57,2338),(62,301193),(74,2345),(81,2345),(82,2345),(101,137513),(109,301195),(114,2345),(117,2345),(130,2345),(133,2345),(141,2345),(145,2345),(146,2345),(158,301058)]),([6,15,802,2296,2764],[(1,303107),(3,303107),(5,303107),(7,303107),(9,303107),(11,303107),(59,303107),(63,303107),(75,303107),(79,303107),(83,303107),(87,303107),(103,303239),(119,303107)]),([6,34,240,255,580,2184],[(0,303107),(2,303107),(4,303107),(6,105634),(8,303107),(10,296969),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,8483),(98,303107),(105,164968),(129,99496),(130,303107),(142,303107),(150,303107),(153,303107),(154,306275)]),([6,47,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,141607),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107)]),([6,79,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(82,303107),(97,296962),(102,303107),(106,303107),(114,10531),(130,303107),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106)]),([6,128,143,240,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(81,303107),(82,303107),(98,303107),(101,303107),(105,296962),(113,301058),(129,303107),(130,303107),(133,303107),(137,296962),(142,303107),(146,303107),(154,303271)]),([6,128,240,255,580,802],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(74,303107),(77,303107),(82,303107),(85,303107),(98,303107),(113,296962),(129,303107),(130,303107),(138,303107),(141,303107),(145,296962),(150,303107),(154,303271)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_143 : K_143.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_144 : List (List ℕ × List (ℕ × ℕ)) := [([6,128,240,580,591,802],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,296962),(16,296962),(18,1315),(58,296962),(61,296962),(73,296962),(74,296962),(81,296962),(82,296962),(97,296962),(98,296962),(105,296962),(106,296962),(114,296962),(117,296962),(129,295939),(130,296962),(138,296962),(153,296962),(158,295939)]),([6,128,240,580,802,815],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(58,296962),(61,296962),(73,296962),(74,296962),(81,296962),(97,295939),(98,296962),(106,296962),(129,296962),(130,296962),(138,296962),(146,296962),(154,296962),(157,296962)]),([6,128,240,580,802,4080],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(74,303107),(81,301058),(97,303107),(98,303107),(106,303107),(114,296971),(130,303107),(133,303107),(138,303107),(141,303107),(146,296962),(153,303107),(154,295939)]),([6,136,240,255,580,802],[(0,303107),(2,303107),(4,303107),(6,105634),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(61,303107),(74,303107),(77,303107),(82,303107),(85,303107),(97,164968),(98,303107),(105,164968),(113,296962),(129,171106),(130,303107),(138,303107),(145,296962),(150,303107),(154,303271)]),([6,143,240,580,802],[(1,303107),(3,303107),(5,303107),(7,303107),(9,141320),(11,141320),(13,303107),(15,303107),(59,303107),(63,303107),(75,141320),(79,303239),(83,10376),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(115,141320),(119,141320)]),([6,143,240,580,802,1024],[(0,303107),(2,138252),(4,303107),(6,7308),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(73,296962),(81,301058),(97,11400),(102,303107),(106,303107),(114,303271),(129,11400),(130,303107),(134,303107),(137,142344),(138,303107),(142,303107),(145,303107),(146,142344),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,143,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,105611),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(138,303107),(142,303107),(145,303107),(146,141416),(150,303107),(153,303107),(154,303107),(158,303107)]),([6,240,255,580,591,802,2184],[(56,105634),(60,296962),(104,296962),(108,303107),(116,303107),(128,139559),(144,303271),(180,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_144 : K_144.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_145 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,255,580,756,802,2184],[(56,164968),(96,164968),(100,303107),(104,296962),(116,303107),(128,10535),(152,303239),(196,303107)]),([6,240,255,580,802,1911],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,164968),(81,296962),(98,303107),(105,296962),(110,303107),(114,303271),(134,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107)]),([6,240,255,580,802,2184],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,164968),(81,296962),(98,303107),(105,296962),(110,303107),(114,303271),(134,303107),(142,303107),(145,303107),(146,164968),(153,99496),(154,171106)]),([6,240,255,580,802,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(97,303107),(98,303107),(105,303107),(110,303107),(114,303271),(133,303107),(134,303107),(141,303107),(142,303107),(154,171010),(157,303107)]),([6,240,255,580,802,2764],[(0,164968),(2,105634),(4,164968),(6,164968),(8,164968),(10,164968),(12,164968),(14,164968),(16,164968),(18,164968),(58,164968),(61,164968),(73,164968),(81,296962),(86,303240),(105,296962),(110,306275),(113,303240),(114,10531),(134,303107),(142,303203),(146,164968),(149,164968),(153,99496),(154,171106)]),([6,240,255,580,802,2986],[(0,171106),(2,105634),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(58,171106),(61,171106),(73,171106),(81,171106),(105,171106),(110,303107),(114,171106),(133,171106),(134,171010),(142,171106),(146,171106),(154,171106),(157,171106)]),([6,240,255,580,802,3208],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,164968),(81,296962),(98,303107),(105,296962),(110,303107),(114,303271),(134,303107),(141,296962),(142,303107),(145,303107),(146,164968),(153,99496),(154,171106)]),([6,240,255,580,870,2184],[(0,303271),(2,105634),(4,303271),(6,296971),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(58,303271),(61,303271),(73,164968),(98,303239),(110,303271),(114,303271),(117,303271),(134,303271),(142,303271),(145,303271),(146,10531),(153,99496),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_145 : K_145.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_146 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,255,580,1010,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,10535),(81,296962),(98,303107),(101,303107),(105,296962),(110,303107),(114,303239),(129,303107),(134,303107),(142,303107),(145,303107),(153,99464),(158,303107)]),([6,240,255,580,1826,2184],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,164968),(81,296962),(98,303107),(105,296962),(110,303107),(114,303271),(134,303107),(141,296962),(142,303107),(145,303107),(146,164968),(153,99496),(154,171106)]),([6,240,255,580,2184,2986],[(0,99496),(2,105634),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,171106),(16,99496),(18,99496),(58,99496),(61,99496),(73,99496),(81,296962),(110,303107),(113,303107),(114,99496),(130,99464),(133,99496),(142,99496),(146,99496),(154,99496),(157,99496)]),([6,240,255,580,2184,3293],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,164968),(81,1315),(102,303107),(110,303107),(113,303107),(114,164968),(130,303107),(141,295939),(142,303107),(146,305155),(154,303107),(157,303107)]),([6,240,255,802,1604,2184],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,1323),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(74,303107),(81,295939),(97,164968),(105,295939),(134,303107),(141,295939),(142,303107),(145,305154),(146,303107),(153,303107),(154,305154)]),([6,240,255,802,2184,2764],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(58,303107),(61,303107),(74,303107),(81,295939),(86,303107),(98,303107),(110,303107),(113,303107),(114,303107),(145,303271),(154,303107),(157,303107)]),([6,240,255,802,2184,3515],[(0,2345),(2,105634),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,303107),(58,2345),(61,2345),(74,2345),(81,2338),(86,2345),(102,2345),(110,2345),(113,2345),(114,2345),(133,2345),(141,296962),(149,2347),(154,2345),(157,2345)]),([6,240,512,527,580,802,2184],[(80,296962),(104,296962),(136,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_146 : K_146.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_147 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,512,580,591,802,2184],[(56,301058),(72,141315),(80,296962),(104,296962),(136,296962),(144,10407)]),([6,240,512,580,802,815,2184],[(80,296962),(104,296962),(136,296962)]),([6,240,512,580,802,2184,4080],[(56,301058),(80,303107),(104,303107),(176,303107)]),([6,240,514,580,591,2184],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,2338),(12,295939),(14,295939),(16,295939),(18,295939),(57,295939),(58,296962),(73,296962),(74,295939),(97,295939),(98,295939),(106,295939),(109,295939),(114,295939),(117,295939),(129,295939),(134,295939),(137,296962),(138,295939),(145,295939),(146,296962),(154,295939)]),([6,240,527,580,802,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(81,296962),(98,296962),(105,296962),(110,295939),(129,296962),(134,296962),(138,296962),(145,295939),(146,296962),(153,296962),(154,171106)]),([6,240,576,580,802,2184,4080],[(56,301058),(72,133131),(80,303107),(104,303107),(112,303271),(176,303107),(184,303239),(192,132391)]),([6,240,580,580,802,2184,4080],[(56,301058),(64,303107),(68,303107),(104,296971),(176,296962),(192,296962)]),([6,240,580,591,802,870,2184],[(108,10407),(140,296962),(144,296962),(156,296962),(176,296072),(192,297096),(200,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_147 : K_147.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_148 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,591,802,1024,2191],[(56,301058),(104,11431),(144,10376)]),([6,240,580,591,802,1039,2184],[(56,301058),(72,105634),(104,10407),(148,303107),(184,10376)]),([6,240,580,591,802,1911],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939),(133,296962),(134,296962),(138,296962),(141,296962),(146,296962),(154,296962),(157,296962)]),([6,240,580,591,802,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939),(129,296962),(134,296962),(137,295939),(138,296962),(146,296962),(153,296962),(154,171106)]),([6,240,580,591,802,2184,2191],[(56,301058),(104,109735),(168,105634),(188,303107),(204,296962)]),([6,240,580,591,802,2184,4080],[(56,301058),(72,164968),(84,303107),(104,303271),(172,296962),(176,295939),(192,296962),(204,296962)]),([6,240,580,591,802,2191],[(57,301058),(58,11399),(73,301058),(98,139559),(106,141607),(113,303107),(134,296962),(138,296962),(141,11399),(146,296962),(149,303107),(154,171010),(157,139559)]),([6,240,580,591,802,2764],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(105,296072),(113,296962),(118,296962),(129,296962),(134,296962),(138,296962),(141,296962),(146,296962),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_148 : K_148.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_149 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,591,802,2767],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939),(129,296962),(134,296962),(138,296962),(141,296962),(146,296962),(149,296962),(154,171010),(157,295939)]),([6,240,580,591,802,2986],[(0,171106),(2,171106),(4,171106),(6,2338),(8,171106),(10,171106),(12,171106),(14,99496),(16,171106),(18,171106),(57,171106),(58,171106),(73,171106),(74,171106),(82,171106),(85,171106),(106,297096),(113,295939),(134,171010),(138,171106),(146,171010),(154,171106),(157,171106)]),([6,240,580,591,802,3208],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(101,296962),(113,296962),(118,295939),(129,296962),(134,296962),(137,295939),(138,296962),(146,296962),(149,296962),(153,296962),(154,171106)]),([6,240,580,591,1010,2184],[(0,296962),(2,301193),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(58,296962),(74,296962),(82,296962),(85,296962),(98,296962),(101,296962),(113,296962),(118,295939),(129,139559),(134,296962),(137,295939),(138,296962),(146,296962),(153,296962),(158,296962)]),([6,240,580,591,1826,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(101,296962),(113,296962),(118,295939),(129,296962),(134,296962),(137,295939),(138,296962),(146,296962),(149,296962),(153,296962),(154,171106)]),([6,240,580,591,2184,2986],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,296962),(16,296962),(18,99496),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(97,296962),(105,296962),(106,296962),(130,296962),(150,99464),(154,296962),(157,296962)]),([6,240,580,591,2184,3293],[(0,1315),(2,1315),(4,1315),(6,2338),(8,1315),(10,1315),(12,1315),(14,1315),(16,1315),(18,296962),(57,1315),(58,1315),(73,1315),(74,1315),(82,1315),(85,1315),(97,1315),(102,1315),(105,1315),(106,1315),(114,1315),(130,1315),(149,295939),(150,295939),(154,1315),(157,1315)]),([6,240,580,756,802,2184,4080],[(60,133131),(72,301058),(76,303107),(84,303107),(112,296971),(132,301058),(148,303107),(168,301058),(184,296962),(192,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_149 : K_149.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_150 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,767,802,2184],[(0,296962),(2,105634),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(82,296962),(85,296962),(98,296962),(113,296962),(118,295939),(134,296962),(137,295939),(138,296962),(150,296962),(153,296962),(154,171106)]),([6,240,580,802,815,870,2184],[(140,296962),(148,296962),(152,296962),(176,296072),(184,297096),(200,297058)]),([6,240,580,802,815,1911],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(98,296962),(106,296962),(114,296962),(117,296962),(133,296962),(134,296962),(138,296962),(141,296962),(146,296962),(149,296962),(154,296962)]),([6,240,580,802,815,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(98,296962),(106,296962),(114,296962),(117,296962),(129,296962),(134,296962),(137,295939),(138,296962),(145,296962),(146,295939),(154,296962)]),([6,240,580,802,815,2191],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(74,303107),(98,303107),(106,303107),(114,303107),(117,303107),(129,303107),(134,296962),(138,296962),(146,296962),(149,8328),(154,296962),(157,303107)]),([6,240,580,802,815,2764],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(58,296962),(74,296962),(81,296072),(98,296962),(106,296962),(109,296962),(114,296962),(117,296962),(129,296962),(134,296962),(138,296962),(141,296962),(146,297058),(154,296962)]),([6,240,580,802,815,2986],[(0,295939),(2,295939),(4,295939),(6,2338),(8,295939),(10,295939),(12,295939),(14,295939),(16,295939),(18,295939),(74,295939),(82,297096),(98,171106),(106,295939),(114,295939),(117,295939),(134,296962),(138,297058),(146,295939),(149,295939),(154,296962)]),([6,240,580,802,815,2991],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(98,171010),(106,296962),(114,296962),(117,296962),(134,296962),(138,296962),(146,296962),(149,296962),(154,296962),(157,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_150 : K_150.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_151 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,802,815,3208],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(98,296962),(101,296962),(106,296962),(114,296962),(117,296962),(129,296962),(134,296962),(137,295939),(138,296962),(145,296962),(146,295939),(154,296962),(157,296962)]),([6,240,580,802,870,879,2184],[(108,296962),(116,296962),(152,296962),(176,296072),(184,297096),(192,297058)]),([6,240,580,802,870,2184,4080],[(108,303107),(112,296971),(116,303107),(136,303240),(144,171106),(152,171106),(184,296971),(192,296071)]),([6,240,580,802,879,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(58,10375),(74,296962),(98,296962),(106,296962),(109,296962),(114,296962),(117,296962),(129,296962),(134,296962),(137,295939),(138,296962),(145,296962),(146,295939),(154,296962)]),([6,240,580,802,1023,2184],[(0,296962),(2,105634),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(98,296962),(101,296962),(106,296962),(109,296962),(114,296962),(117,296962),(134,296962),(137,295939),(138,296962),(145,296962),(146,171106),(158,296962)]),([6,240,580,802,1024,1039,2764],[(56,301058),(80,303240),(96,172043)]),([6,240,580,802,1024,1919],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(97,296962),(98,296962),(105,295939),(106,296962),(113,296962),(114,295939),(133,296962),(138,296962),(141,296962),(146,296962),(149,296962),(154,296962),(157,296962)]),([6,240,580,802,1024,2176],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(97,296962),(98,296962),(105,295939),(106,296962),(113,296962),(114,295939),(129,296962),(137,295939),(138,296962),(145,296962),(146,295939),(153,296962),(154,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_151 : K_151.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_152 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,802,1024,2764,4080],[(56,301058),(80,297068),(176,303239),(184,296962)]),([6,240,580,802,1032,2184],[(0,108556),(2,108556),(4,108556),(6,2338),(8,108556),(10,1315),(12,108556),(14,10348),(16,108556),(18,11371),(57,108556),(74,108556),(77,108552),(97,108556),(98,108556),(105,108556),(106,108556),(113,108556),(114,108556),(129,105483),(137,295939),(138,108556),(145,296962),(146,108556)]),([6,240,580,802,1039,1604,2184],[(56,301058),(80,303115),(104,295939),(128,172043),(136,303107),(144,109859)]),([6,240,580,802,1039,2191],[(0,10376),(2,10376),(4,10376),(6,2345),(8,10376),(10,10376),(12,10376),(14,10376),(16,10376),(18,138251),(57,10376),(74,10376),(77,10376),(82,10376),(97,10376),(98,10376),(106,10376),(114,10376),(117,10376),(129,303107),(138,10376),(146,10376),(149,10376),(157,303107)]),([6,240,580,802,1604,2184,4080],[(56,301058),(80,297068),(104,303107),(108,303107),(112,297068),(176,303239),(184,296962),(192,296962),(204,296962)]),([6,240,580,802,1911,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(82,296971),(101,303107),(102,303107),(106,303107),(109,303107),(114,303107),(117,303107),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(157,303107)]),([6,240,580,802,2176,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(82,296971),(97,303107),(102,303107),(105,303107),(113,303107),(114,303107),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(154,303107),(157,303107)]),([6,240,580,802,2184,2764,4080],[(56,301058),(80,296971),(112,99496),(128,301058),(136,303107),(140,303107),(144,296971),(156,303107),(176,303239),(184,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_152 : K_152.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_153 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,802,2184,3280],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(97,296962),(102,296962),(105,295939),(106,296962),(113,296962),(114,295939),(130,296962),(138,296962),(145,296962),(146,295939),(157,296962)]),([6,240,580,802,2184,3504],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(58,137227),(74,296962),(97,296962),(102,296962),(105,295939),(106,296962),(113,296962),(114,171106),(130,296962),(133,296962),(137,295939),(138,296962),(145,296962),(146,295939),(157,296962)]),([6,240,580,802,2184,3515,4080],[(56,301058),(80,296971),(132,301058),(148,296971),(156,303107),(176,137513),(184,296962),(204,296962)]),([6,240,580,802,2184,3840],[(0,303107),(2,105634),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,164968),(74,303107),(82,296971),(102,303107),(105,303107),(106,164968),(113,99496),(114,171106),(129,164968),(130,303107),(138,296962),(145,303107),(146,295939),(153,303107)]),([6,240,580,802,2184,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(82,296971),(97,303107),(102,303107),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(157,303107)]),([6,240,580,802,2184,4082],[(0,295939),(2,295939),(4,295939),(6,2338),(8,295939),(10,295939),(12,295939),(14,295939),(16,295939),(18,295939),(74,295939),(78,296962),(82,296971),(97,295939),(102,295939),(105,295939),(113,295939),(114,295939),(117,296962),(130,295939),(133,295939),(138,296071),(145,295939),(146,295939),(149,295939),(157,295939)]),([6,240,580,802,2184,4084],[(0,296962),(2,296962),(4,296962),(6,137513),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(97,296962),(102,296962),(105,303239),(106,296962),(113,296962),(114,171106),(130,296962),(133,296962),(138,296962),(141,296962),(146,296071),(157,296962)]),([6,240,580,802,2191,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(82,303271),(97,303107),(102,303107),(114,171010),(117,303107),(130,303107),(133,303107),(138,303239),(145,303107),(146,303107),(157,303107),(158,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_153 : K_153.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_154 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,802,2764,4080],[(57,301058),(74,139559),(81,303240),(82,296971),(97,301058),(102,303107),(113,296971),(114,171106),(137,303239),(138,296962),(145,306275)]),([6,240,580,802,2986,4080],[(0,171106),(2,171106),(4,171106),(6,2345),(8,171106),(10,99496),(12,171106),(14,171106),(16,171106),(18,171106),(57,171106),(82,171106),(102,171010),(106,171106),(114,171106),(117,171106),(130,171106),(133,171106),(138,171106),(146,295939),(157,171010)]),([6,240,580,802,3208,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(77,301058),(82,297067),(97,303107),(102,303107),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(157,303107),(158,296962)]),([6,240,580,810,1024,2184],[(0,99340),(2,99340),(4,99340),(6,2338),(8,99340),(10,1132),(12,99340),(14,99340),(16,99340),(18,11362),(57,99340),(74,99340),(77,99336),(97,99340),(98,99340),(105,99340),(106,99340),(113,99340),(114,99340),(129,105474),(137,295939),(138,99340),(153,109570),(154,99340)]),([6,240,580,815,1010,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(74,296962),(77,141314),(82,296962),(98,296962),(101,296962),(113,296962),(118,296962),(129,296962),(134,296962),(137,295939),(138,296962),(146,296962),(153,296962),(158,296962)]),([6,240,580,815,1826,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(82,296962),(98,296962),(101,296962),(113,296962),(118,296962),(129,296962),(134,296962),(137,295939),(138,296962),(146,296962),(149,296962),(153,296962),(154,295939)]),([6,240,580,815,2184,2986],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,296962),(16,296962),(18,1315),(57,296962),(74,296962),(82,296962),(97,296962),(98,296962),(105,296962),(106,296962),(118,296962),(130,296962),(150,99464),(154,296962),(157,296962)]),([6,240,580,815,2184,3293],[(0,1315),(2,1315),(4,1315),(6,2338),(8,1315),(10,1315),(12,1315),(14,1315),(16,1315),(18,296962),(57,1315),(74,1315),(82,1315),(97,1315),(102,1315),(105,1315),(106,1315),(114,1315),(130,1315),(149,295939),(150,295939),(154,1315),(157,1315)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_154 : K_154.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_155 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,870,2184,4080],[(0,296971),(2,296971),(4,296971),(6,296971),(8,296971),(10,296971),(12,296971),(14,296971),(16,296971),(18,303271),(74,296971),(82,296971),(85,296971),(97,296971),(102,296971),(105,296971),(106,296971),(113,296971),(114,296971),(130,296971),(133,296971),(141,303271),(145,303239),(157,296971)]),([6,240,580,1010,1023,2184],[(0,296962),(2,301186),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(74,296962),(77,296962),(98,296962),(101,296962),(106,296962),(109,296962),(114,296962),(117,296962),(129,132391),(134,296962),(137,295939),(138,296962),(145,296962),(150,296962),(158,296962)]),([6,240,580,1010,2184,4080],[(0,303107),(2,301193),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(74,303107),(77,303107),(82,296971),(97,139559),(102,303107),(105,303107),(106,139559),(113,99464),(118,303107),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(157,303107)]),([6,240,580,1024,2184,4082],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,296962),(16,296962),(18,295939),(73,296962),(74,296962),(78,296962),(81,296962),(82,296962),(86,296962),(97,296962),(102,296962),(105,296962),(106,296962),(113,296962),(114,296962),(117,296962),(130,296962),(133,296962),(145,295939),(146,296962),(149,296962),(157,296962)]),([6,240,580,1039,1826,2184],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(73,105634),(74,303107),(82,296962),(98,303107),(101,301058),(106,109859),(113,296962),(118,8483),(129,303107),(134,303107),(137,303107),(146,303107),(149,296962),(153,99496),(154,171106)]),([6,240,580,1826,1839,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(57,296962),(74,296962),(77,296962),(98,296962),(101,296962),(106,296962),(114,296962),(117,296962),(129,296962),(134,296962),(137,295939),(138,296962),(145,296962),(146,295939),(154,296962),(157,296962)]),([6,240,580,1826,2184,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,301058),(74,303107),(77,301058),(82,297068),(97,303107),(102,303107),(105,303107),(113,99496),(114,171106),(130,303107),(133,303107),(138,296962),(145,303107),(146,295939),(157,303107),(158,296962)]),([6,240,580,2184,2986,4080],[(0,99496),(2,99496),(4,99496),(6,2345),(8,99496),(10,171106),(12,99496),(14,99496),(16,99496),(18,99496),(57,301058),(73,303107),(81,303107),(82,99496),(98,99464),(106,296971),(114,99496),(117,99496),(130,99496),(133,99496),(138,296962),(153,99464)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_155 : K_155.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_156 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,580,2184,3293,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(57,1319),(73,303107),(78,303107),(81,303107),(98,303107),(106,296971),(114,303107),(117,303107),(130,303107),(133,303107),(138,1315),(149,303107),(153,296969),(158,1315)]),([6,240,580,2184,4080,4082],[(0,303107),(2,301193),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(73,139559),(78,303107),(81,303107),(82,306275),(98,303107),(101,303107),(102,296962),(106,296962),(110,132391),(114,303107),(117,303107),(118,296962),(130,303107),(133,303107),(138,303239),(146,99464),(149,303107),(153,295939),(154,303107),(157,303107)]),([6,240,580,2184,4082],[(1,296962),(3,296962),(5,296962),(7,296962),(9,296962),(11,296962),(13,295939),(15,295939),(59,296962),(63,296962),(75,296962),(79,296962),(83,296962),(87,296962),(99,295939),(103,296962),(107,296071),(111,132391),(115,295939),(119,296962)]),([6,240,588,802,1024,2184],[(0,100364),(2,100364),(4,100364),(6,2156),(8,100364),(10,1315),(12,100364),(14,100364),(16,100364),(18,11363),(57,100364),(74,100364),(77,100360),(97,100364),(98,100364),(105,100364),(106,100364),(113,100364),(114,100364),(129,104584),(145,296962),(146,100364),(153,296962),(154,100364)]),([6,240,591,756,802,2184],[(0,296962),(2,296962),(4,296962),(6,137227),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(61,296962),(73,296962),(74,296962),(77,296962),(86,296962),(97,172035),(98,296962),(101,296962),(105,10375),(110,295939),(129,296962),(133,296962),(134,296962),(138,296962),(145,295939),(150,296962),(153,296962),(154,171106)]),([6,240,591,802,1604,2184],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,1315),(12,295939),(14,2338),(16,295939),(18,295939),(57,295939),(58,295939),(74,295939),(77,295939),(81,295939),(86,295939),(97,296962),(98,295939),(105,295939),(110,296962),(129,295939),(134,295939),(138,295939),(141,295939),(145,296962),(146,295939),(153,295939),(154,296962)]),([6,240,591,802,2184,2764],[(0,295939),(2,295939),(4,295939),(6,295939),(8,295939),(10,1315),(12,295939),(14,295939),(16,295939),(18,2338),(57,295939),(58,295939),(74,295939),(81,295939),(86,295939),(97,295939),(98,295939),(110,295939),(113,296962),(114,295939),(129,296962),(130,295939),(142,100488),(154,295939),(157,295939)]),([6,240,591,802,2184,3515],[(0,2338),(2,2338),(4,2338),(6,2338),(8,2338),(10,2338),(12,2338),(14,2338),(16,2338),(18,296962),(57,2338),(58,2338),(74,2338),(81,2338),(86,2338),(97,2338),(102,2338),(106,2338),(113,2338),(114,2338),(130,2338),(133,2338),(141,137513),(142,296962),(154,2338),(157,2338)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_156 : K_156.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_157 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,802,815,1604,2184],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,295939),(12,295939),(14,2338),(16,295939),(18,295939),(58,295939),(61,295939),(74,295939),(77,295939),(82,295939),(85,295939),(97,296962),(113,295939),(129,295939),(134,295939),(137,296962),(138,295939),(146,295939),(149,295939),(153,295939),(154,296962)]),([6,240,802,815,2184,2764],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,295939),(12,295939),(14,295939),(16,295939),(18,2338),(58,295939),(74,295939),(82,295939),(85,295939),(97,295939),(98,295939),(105,296962),(106,295939),(118,295939),(129,296962),(154,295939),(157,295939)]),([6,240,802,815,2184,3515],[(0,2338),(2,2338),(4,2338),(6,2338),(8,2338),(10,2338),(12,2338),(14,2338),(16,2338),(18,296962),(58,2338),(74,2338),(82,2338),(85,2338),(97,2338),(102,2338),(105,2338),(106,2338),(114,2338),(133,2338),(149,296962),(154,2338),(157,2338)]),([6,240,802,1039,1604,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(61,303107),(73,303107),(74,303107),(82,295939),(85,303107),(97,301058),(105,303271),(113,295939),(129,303107),(134,303107),(137,99496),(138,303107),(146,303107),(149,295939),(153,303107)]),([6,240,802,1604,1615,2184],[(0,295939),(2,295939),(4,295939),(6,1315),(8,295939),(10,2338),(12,295939),(14,295939),(16,295939),(18,295939),(58,295939),(61,295939),(73,296962),(74,295939),(97,105634),(98,295939),(106,295939),(109,295939),(114,295939),(117,295939),(129,295939),(134,295939),(137,296962),(138,295939),(145,295939),(146,296962),(154,295939),(157,295939)]),([6,240,802,1604,2184,4080],[(0,303107),(2,303107),(4,303107),(6,1323),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(58,303107),(61,303107),(73,301058),(97,303107),(102,303107),(105,305154),(106,303107),(113,303107),(114,305154),(130,303107),(133,303107),(138,295939),(146,303239),(157,303107),(158,295939)]),([6,240,802,2184,2764,4080],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(58,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,301058),(105,296971),(114,303107),(117,303107),(130,303107),(133,303107),(137,303107),(138,295939),(145,303107)]),([6,240,802,2184,3515,4080],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,303107),(16,2345),(18,2345),(58,2345),(73,2345),(78,2345),(81,2345),(82,2345),(101,2345),(109,296971),(114,2345),(117,2345),(130,2345),(133,2345),(137,2345),(138,2338),(149,2345),(158,2338)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_157 : K_157.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_158 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,580,591,802,2184],[(0,105634),(2,105634),(4,105634),(6,105634),(8,105634),(10,164968),(12,105634),(14,105634),(16,105634),(18,105634),(57,296962),(62,105634),(73,296962),(78,303107),(82,105634),(85,105634),(102,105634),(105,105634),(106,105634),(129,105634),(134,105634),(137,105634),(138,105634),(153,99496),(154,171106)]),([6,255,580,756,802,2184],[(0,164968),(2,164968),(4,164968),(6,164968),(8,164968),(10,105634),(12,164968),(14,164968),(16,164968),(18,164968),(57,296962),(62,164968),(73,296962),(78,303235),(82,164968),(85,164968),(97,296962),(102,164968),(105,164968),(106,164968),(114,10531),(134,164968),(137,164968),(138,164968),(153,99496),(154,171106)]),([6,255,580,802,1039,2184],[(0,105634),(2,105634),(4,105634),(6,2345),(8,105634),(10,105634),(12,105634),(14,164968),(16,105634),(18,105634),(57,105634),(78,105634),(82,105634),(102,303107),(106,105634),(117,303107),(129,105634),(134,105634),(137,303107),(138,105634),(145,99496),(146,105634),(154,303107)]),([6,255,580,802,1264,2184],[(0,164968),(2,164968),(4,164968),(6,2345),(8,164968),(10,164968),(12,164968),(14,105634),(16,164968),(18,164968),(57,164968),(73,164968),(78,164968),(82,164968),(102,303107),(106,164968),(113,303107),(134,164968),(137,303107),(138,164968),(145,99496),(146,164968),(158,303107)]),([6,255,580,802,2184,3855],[(0,105634),(2,105634),(4,105634),(6,105634),(8,105634),(10,105634),(12,105634),(14,105634),(16,105634),(18,303107),(57,105634),(73,105634),(78,105634),(82,105634),(102,105634),(105,105634),(106,105634),(113,105634),(114,105634),(133,303107),(134,303107),(138,105634),(149,303107),(153,303107)]),([6,255,580,802,2184,4080],[(0,164968),(2,164968),(4,164968),(6,164968),(8,164968),(10,164968),(12,164968),(14,164968),(16,164968),(18,303107),(57,164968),(78,164968),(82,164968),(97,164968),(102,164968),(105,164968),(106,164968),(113,164968),(114,164968),(133,303107),(134,303107),(138,164968),(145,303107),(157,303107)]),([6,580,591,756,802,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(57,296962),(58,296962),(61,296962),(73,296962),(74,296962),(77,296962),(81,296962),(82,296962),(101,141315),(105,296962),(110,296962),(129,296962),(130,296962),(133,296962),(138,296962),(145,296962),(150,296962),(153,296962),(154,171106)]),([6,580,591,767,802,2184],[(0,296962),(2,2338),(4,296962),(6,164968),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(58,296962),(61,296962),(74,296962),(77,296962),(82,296962),(85,296962),(110,295939),(118,105634),(129,295939),(130,296962),(138,296962),(145,296962),(150,296962),(153,296962),(154,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_158 : K_158.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_159 : List (List ℕ × List (ℕ × ℕ)) := [([6,580,591,802,2184,2296],[(0,296962),(2,2338),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(58,296962),(61,296962),(81,296962),(86,295939),(97,295939),(98,296962),(106,296962),(113,296962),(114,295939),(129,295939),(130,296962),(138,296962),(145,296962),(154,296962),(157,296962)]),([6,580,591,802,2184,3855],[(0,296962),(2,2338),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(58,296962),(61,296962),(81,296962),(86,295939),(97,295939),(98,296962),(106,296962),(113,296962),(114,171106),(130,296962),(133,6283),(138,296962),(141,296962),(149,296962),(153,296962),(154,296962)]),([6,580,756,767,802,2184],[(0,296962),(2,296962),(4,296962),(6,105634),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(58,296962),(61,296962),(74,296962),(77,296962),(82,296962),(85,296962),(97,164968),(113,296962),(118,164968),(129,296962),(130,296962),(142,296962),(150,296962),(153,296962),(154,171106)]),([6,580,756,802,815,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(58,296962),(61,296962),(97,165890),(98,296962),(106,296962),(114,296962),(117,296962),(129,296962),(130,296962),(137,296962),(142,296962),(145,296962),(154,296962)]),([6,580,756,802,2184,4080],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,1319),(12,301058),(14,301058),(16,301058),(18,301058),(58,301058),(61,301058),(97,301058),(98,301058),(105,301058),(110,301058),(113,301058),(114,171106),(130,296962),(133,133131),(138,296962),(141,301058),(157,301058)]),([6,580,802,815,2184,2296],[(0,296962),(2,2338),(4,296962),(6,1315),(8,296962),(10,296962),(12,296962),(14,296962),(16,296962),(18,296962),(74,296962),(82,296962),(85,296962),(97,295939),(98,296962),(105,296962),(106,295939),(114,296962),(130,296962),(137,296962),(154,296962),(157,296962)]),([6,580,802,815,2184,3855],[(0,296962),(2,2338),(4,296962),(6,1315),(8,296962),(10,296962),(12,296962),(14,296962),(16,296962),(18,296962),(74,296962),(82,296962),(85,296962),(97,295939),(98,296962),(105,296962),(106,295939),(114,296962),(130,296962),(141,296962),(149,296962),(153,296962),(154,296962)]),([6,580,802,1039,1264,2184],[(0,172043),(2,2345),(4,172043),(6,172043),(8,172043),(10,141420),(12,172043),(14,10409),(16,172043),(18,172043),(58,172043),(74,109707),(82,109707),(85,139275),(98,172043),(105,139559),(129,303107),(130,172043),(137,99496),(138,172043),(146,172043),(153,172043),(158,142347)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_159 : K_159.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_160 : List (List ℕ × List (ℕ × ℕ)) := [([6,580,802,2184,2296,4080],[(0,303107),(2,2345),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(58,296971),(73,303107),(81,303107),(82,303107),(98,301058),(105,139559),(114,303107),(117,303107),(130,296962),(137,139559),(138,295939),(149,303107),(157,303107)]),([6,580,802,2184,3855,4080],[(0,303107),(2,2345),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(58,296971),(73,303107),(81,99496),(82,171106),(98,301058),(109,303107),(113,303107),(114,303107),(130,296962),(137,301193),(138,295939),(149,303107),(157,164968),(158,105634)]),([6,591,756,802,1024,2184],[(0,296962),(2,133228),(4,296962),(6,2217),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(73,109699),(78,139267),(97,109699),(98,296962),(102,296962),(105,172035),(106,296962),(110,296962),(113,296962),(114,172035),(118,296962),(130,296962),(137,172035),(142,296962),(145,296962),(146,171106),(153,296962),(154,296962),(157,296962)]),([6,591,756,802,2184],[(1,296962),(3,296962),(5,296962),(7,296962),(9,141315),(11,141315),(13,296962),(15,296962),(59,296962),(63,296962),(75,296962),(79,141315),(83,10371),(87,141315),(99,296962),(103,296962),(107,296962),(111,296962),(115,141315),(119,296962)]),([7,0,15,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(81,303107),(82,303107),(98,303107),(101,303107),(105,296962),(113,301058),(129,303107),(130,303107),(133,303107),(137,296962),(142,303107),(146,303107),(154,303271),(169,303107),(170,303107),(173,303107),(178,303107),(185,303107),(190,303107),(193,303107),(201,99496),(202,171106)]),([7,2,15,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(81,303107),(82,303107),(98,303107),(101,303107),(129,303107),(130,303107),(133,303107),(134,303107),(137,296969),(138,303107),(142,303107),(146,303107),(150,303107),(154,303271),(169,303107),(170,303107),(173,303107),(178,303107),(185,303107),(190,303107),(193,303107),(201,303107),(202,303107),(205,303107)]),([7,2,15,240,580,1024,2184],[(0,303107),(2,303107),(4,303107),(6,296969),(8,303107),(10,301193),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(58,303107),(61,303107),(73,303107),(74,303107),(81,303107),(82,303107),(97,139559),(98,303107),(129,303107),(130,303107),(134,303107),(137,8483),(138,303107),(142,303107),(145,139559),(146,303107),(150,303107),(153,303107),(154,139559),(158,303107),(169,303107),(170,303107),(178,303107),(185,139559),(190,303107),(193,303107),(194,306275),(201,303107),(202,303107),(205,303107)]),([7,2,15,240,580,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,303107),(11,303107),(13,139559),(15,139559),(17,303107),(19,303107),(59,303107),(63,303107),(75,303107),(79,303107),(83,303107),(87,303107),(99,139559),(103,303107),(107,139559),(111,303239),(115,8483),(119,303107),(131,303107),(135,303107),(139,303107),(143,303107),(147,303107),(151,303107),(155,139559),(159,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_160 : K_160.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_161 : List (List ℕ × List (ℕ × ℕ)) := [([7,4,15,240,580,802,2184],[(0,303239),(2,303239),(4,303239),(6,303239),(8,303239),(10,303239),(12,303239),(14,137513),(16,303239),(18,303239),(20,303239),(22,303239),(57,303107),(58,303239),(61,303239),(73,303239),(74,303239),(77,303107),(81,303239),(82,303239),(98,303239),(101,303239),(106,303239),(113,301058),(129,303239),(130,303239),(133,303107),(137,296071),(142,303239),(146,303239),(154,303271),(169,303239),(170,303239),(173,303107),(178,303239),(185,303239),(190,303239),(193,303239),(201,99496),(202,171106)]),([7,8,15,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,303107),(73,303107),(74,303107),(77,303107),(81,303107),(82,303107),(98,303107),(101,303107),(105,296962),(113,301058),(129,303107),(130,303107),(133,303107),(137,296962),(142,303107),(146,303107),(154,303271),(169,303107),(170,303107),(173,303107),(177,303107),(178,303107),(185,303107),(190,303107),(193,303107),(201,303107),(202,303107)]),([7,8,240,580,802,1024,2184],[(0,296962),(2,296962),(4,296962),(6,296962),(8,296962),(10,2338),(12,296962),(14,1315),(16,296962),(18,296962),(20,296962),(22,296962),(57,296962),(58,296962),(73,296962),(74,296962),(81,296962),(97,295939),(98,296962),(106,296962),(109,296962),(129,296962),(130,296962),(137,296962),(138,296962),(145,295939),(146,296962),(153,296962),(154,295939),(170,296962),(173,296962),(177,296962),(185,295939),(186,296962),(193,296962),(194,295939),(201,296962),(202,296962)]),([7,15,15,240,580,802,2184],[(0,303107),(2,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(49,303107),(50,303107),(53,303107),(54,303107),(73,303107),(74,303107),(77,303107),(101,303239),(113,301058),(129,303107),(133,303107),(134,303107),(146,303107),(154,303271),(169,303107),(170,303107),(173,303107),(185,303107),(190,303107),(193,303107),(201,99496),(202,171106)]),([7,15,32,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(73,303107),(74,303107),(81,303107),(82,303107),(85,303107),(97,296962),(106,303107),(109,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(141,303107),(145,301193),(146,303107),(154,141607),(170,303107),(177,303107),(178,303107),(181,303107),(185,303107),(190,303107),(193,303107),(201,303107),(202,303107)]),([7,15,32,580,802,1024,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,2345),(12,301058),(14,1319),(16,301058),(18,301058),(20,301058),(22,301058),(57,301058),(58,301058),(73,296962),(81,301058),(82,301058),(97,296962),(106,301058),(109,301058),(129,301058),(130,301058),(137,301058),(138,301058),(145,303107),(146,301058),(153,301058),(154,303107),(170,301058),(173,296962),(177,301058),(178,301058),(185,303107),(186,301058),(193,301058),(194,303107),(201,301058),(202,301058)]),([7,15,64,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(73,303107),(74,303107),(81,303107),(82,303107),(85,303107),(97,296962),(106,303107),(109,303107),(114,303107),(129,296962),(134,303107),(137,303107),(138,303107),(141,303107),(146,303107),(154,10531),(170,303107),(177,303107),(178,303107),(181,303107),(185,303107),(190,303107),(193,303107),(201,99496),(202,171106)]),([7,15,128,240,580,802],[(1,303107),(3,303107),(5,303107),(7,303107),(9,303107),(11,303107),(17,303107),(19,303107),(59,303107),(63,303107),(75,303107),(79,303107),(83,303107),(87,303107),(103,303239),(111,303107),(119,303107),(131,303107),(135,303107),(139,303107),(143,303107),(147,303107),(151,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_161 : K_161.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_162 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,128,240,580,802,1024],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,303107),(74,303107),(82,303107),(85,303107),(97,296962),(106,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(146,303107),(154,303271),(169,303107),(170,303107),(174,303107),(177,303107),(178,303107),(182,303107),(185,303107),(186,303107),(190,303107),(193,303107),(198,303107),(201,303107),(202,303107),(206,303107)]),([7,15,128,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(73,303107),(74,303107),(81,303107),(82,303107),(85,303107),(97,296962),(106,303107),(109,303107),(113,301058),(129,296962),(134,303107),(137,303107),(138,303107),(141,303107),(146,303107),(154,303271),(170,303107),(174,303107),(177,303107),(178,303107),(181,303107),(182,303107),(185,303107),(186,303107),(190,303107),(193,303107),(198,303107),(201,303107),(202,303107),(206,303107)]),([7,15,240,240,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(65,303107),(66,303107),(69,303107),(70,303107),(97,296962),(109,303107),(129,296962),(134,303107),(137,303107),(138,303107),(141,303107),(154,303271),(170,303107),(177,303107),(181,303107),(182,303107),(193,303107),(201,99496),(202,171106)]),([7,15,240,255,580,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,2345),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,303107),(62,303107),(73,303107),(74,303107),(77,303107),(78,303107),(81,303107),(82,303107),(85,303107),(86,303107),(101,303239),(109,303107),(129,303107),(133,303107),(134,303107),(137,303107),(138,303107),(141,303107),(145,303107),(149,303107),(150,303107),(154,303271),(169,303107),(170,303107),(173,303107),(177,303107),(181,303107),(182,303107),(185,303107),(189,303107),(190,303107),(193,303107),(201,99496),(202,171106)]),([7,15,240,512,580,802,1024,2184],[(72,296962),(80,301058),(112,303107),(144,303107),(188,303107)]),([7,15,240,512,580,802,2184],[(57,164968),(58,105634),(78,303107),(86,303107),(145,303107),(189,303107),(201,99496),(202,171106)]),([7,15,240,580,580,802,1024,2184],[(72,296962),(80,301058),(88,303107),(92,303107),(144,303271),(188,303107)]),([7,15,240,580,580,802,2184],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(86,303107),(129,296962),(134,139559),(138,139559),(146,141607),(189,303107),(201,99496),(202,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_162 : K_162.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_163 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,591,802,1024,2184],[(56,105634),(80,301058),(96,296962),(100,303107),(104,301058),(116,303107),(144,303271),(172,296962),(196,303107)]),([7,15,240,580,591,802,2184],[(61,296962),(73,296962),(78,303239),(81,301058),(97,296962),(102,303107),(105,301058),(110,303107),(129,296962),(134,139559),(138,139559),(146,141607),(153,303107),(173,296962),(197,303107),(201,99496),(202,171106)]),([7,15,240,580,756,802,1024,2184],[(56,164968),(72,296962),(84,172035),(96,296962),(104,301058),(108,303107),(116,303107),(152,303239),(180,301058),(196,303107),(228,301058),(244,303107)]),([7,15,240,580,756,802,2184],[(62,301058),(73,296962),(81,301058),(86,303107),(97,296962),(102,303239),(105,301058),(110,303107),(129,296962),(134,8483),(141,301058),(146,10531),(153,303239),(154,10531),(181,301058),(197,303107),(201,99496),(202,171106)]),([7,15,240,580,802,802,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(102,303107),(106,303107),(110,303107),(121,303107),(122,303107),(125,303107),(126,303107),(170,303107),(177,303107),(182,303107),(185,303107),(193,303107),(194,303107),(197,303107)]),([7,15,240,580,802,815,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,296962),(73,296962),(77,296071),(97,296962),(101,296969),(102,303107),(106,303107),(129,296962),(130,303107),(133,303107),(134,303107),(138,303107),(142,303107),(146,303107),(154,303107),(157,303107),(158,303107),(169,303107),(170,303107),(173,296962),(177,303107),(182,303107),(185,303107),(193,303107),(194,303107),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,870,1024,2184],[(128,296962),(140,303107),(148,303107),(152,303271),(156,303107),(196,303271),(204,303107),(232,303240),(240,171106),(248,171106)]),([7,15,240,580,802,870,2184],[(57,164968),(58,105634),(102,303271),(106,303271),(110,141607),(114,303271),(130,303107),(134,303239),(138,303239),(142,303107),(153,303271),(158,303107),(197,303271),(205,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_163 : K_163.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_164 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,802,1010,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(102,303107),(106,303107),(109,301193),(110,303107),(114,303271),(129,295939),(130,303107),(134,303107),(138,303107),(141,303107),(142,303107),(146,303239),(153,303107),(154,303107),(157,303107),(158,303107),(170,303107),(177,303107),(182,303107),(185,303107),(193,303107),(194,303107),(197,303107),(201,303107),(205,303107),(206,303107)]),([7,15,240,580,802,1024,1604,2184],[(72,295939),(80,301058),(112,303271),(144,305154),(148,303107),(168,296962),(176,301058),(184,303107),(188,303107),(192,303271),(204,303107)]),([7,15,240,580,802,1024,1911],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(169,296962),(170,303107),(181,303107),(182,303107),(186,303107),(189,303107),(194,303107),(197,303107),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1024,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,296962),(177,303107),(182,303107),(185,303107),(193,99496),(194,171106),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1024,2184,2764],[(72,295939),(80,301058),(112,303271),(148,303107),(172,296962),(192,99496),(220,296071),(224,301058),(232,303107),(236,303107),(240,99496),(252,303107),(260,303107)]),([7,15,240,580,802,1024,2184,3515],[(72,2338),(80,301058),(112,170281),(148,2345),(220,296962),(228,301058),(244,172327),(252,303107),(260,303107)]),([7,15,240,580,802,1024,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(109,301058),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,303107),(177,303107),(182,303107),(194,171010),(197,303107),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1024,2764],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(97,296962),(102,306275),(106,139559),(109,301058),(113,303240),(114,172327),(177,301058),(182,303107),(193,99496),(194,171106)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_164 : K_164.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_165 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,802,1024,2986],[(0,171106),(2,171106),(4,171106),(6,171106),(8,171106),(10,2345),(12,171106),(14,99496),(16,171106),(18,171106),(20,171106),(22,171106),(57,171106),(58,171106),(73,171106),(81,171106),(97,295939),(109,303107),(114,171106),(129,171106),(130,171106),(134,171106),(137,171106),(138,171106),(142,171106),(145,303107),(146,171106),(150,171106),(153,171106),(154,303107),(158,171106),(170,171010),(173,171106),(181,171106),(182,171010),(186,171106),(194,171106),(197,171106),(201,171106),(202,171106),(205,171106)]),([7,15,240,580,802,1024,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(129,303107),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,296962),(177,303107),(182,303107),(185,303107),(193,99496),(194,171106),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1039,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,303107),(134,303107),(137,303107),(138,303107),(142,303107),(150,303239),(154,303107),(157,303107),(158,303107),(169,303107),(170,303107),(177,303107),(182,303107),(185,303107),(193,99496),(194,171106),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1264,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(105,303107),(106,303107),(114,303271),(129,303107),(130,303107),(134,303107),(138,303107),(141,303107),(142,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,296962),(177,303107),(182,303107),(185,303107),(193,99496),(194,171106),(201,303107),(205,303107),(206,303107)]),([7,15,240,580,802,1604,2184],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(86,303107),(97,296962),(102,139559),(106,139559),(109,301058),(114,172327),(129,296962),(134,303239),(137,301058),(142,303107),(145,305154),(153,172327),(173,296962),(189,303107),(193,99496),(194,171106),(205,303107)]),([7,15,240,580,802,1826,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(102,303107),(106,303107),(109,303107),(110,303107),(129,295939),(130,303107),(134,303107),(138,303107),(141,303107),(142,303107),(153,303107),(154,303107),(157,303107),(158,303107),(170,303107),(173,295939),(177,303107),(182,303107),(185,303107),(193,303107),(194,303107),(197,303107),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,802,1911],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(147,303107),(155,303107),(159,303107)]),([7,15,240,580,802,1911,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(138,303107),(141,303107),(142,303107),(146,303107),(149,303107),(154,303107),(157,303107),(158,303107),(170,303107),(174,303107),(177,303107),(178,303107),(182,303107),(185,303107),(190,303107),(193,303107),(194,303107),(198,303107),(201,303107),(202,303107),(205,303107),(206,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_165 : K_165.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_166 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,802,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(151,303107),(155,303107),(159,303107)]),([7,15,240,580,802,2184,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(114,303271),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(161,303107),(162,303107),(165,303107),(166,303107)]),([7,15,240,580,802,2184,2191],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(81,301058),(97,303107),(102,303107),(106,303107),(114,303271),(130,303107),(133,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,303107),(174,303107),(177,303107),(178,303107),(182,303107),(190,303239),(194,303107),(197,303107),(198,303107),(201,303107),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2184,2296],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(73,296962),(85,303107),(97,296962),(102,303107),(105,303107),(106,303107),(109,303107),(114,303271),(130,303107),(137,303107),(141,303107),(142,303107),(145,303107),(153,303107),(154,303107),(170,303107),(174,303107),(177,303107),(178,303107),(181,303107),(182,303107),(190,303107),(193,303107),(194,303107),(198,303107),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2184,2764],[(57,164968),(58,105634),(73,296962),(78,303239),(81,301058),(86,303107),(97,296962),(102,139559),(106,139559),(114,141607),(149,303107),(174,303239),(177,301058),(182,303107),(193,141607),(206,303107)]),([7,15,240,580,802,2184,2986],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(102,303107),(106,303107),(110,303107),(118,99496),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,171106),(153,99496),(154,171106),(157,99496),(158,171106),(170,303107),(174,303107),(178,303107),(182,303107),(193,99496),(194,303107),(197,303107),(198,303107),(201,171106),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2184,3071],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,296962),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106),(170,303107),(173,303107),(174,303107),(178,303107),(181,303107),(182,303107),(186,303107),(189,303107),(194,303107),(197,303107),(198,303107),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2184,3208],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,296962),(102,303107),(106,303107),(109,301058),(114,303271),(130,303107),(133,296962),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,296962),(174,303107),(177,303107),(178,303107),(182,303107),(185,303107),(190,303107),(193,303107),(194,303107),(198,303107),(201,303107),(202,303107),(205,303107),(206,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_166 : K_166.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_167 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,802,2184,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(97,295939),(98,303107),(102,303107),(106,303107),(110,303107),(130,303107),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107),(157,303107),(170,303107),(173,295939),(174,303107),(178,303107),(182,303107),(193,303107),(194,303107),(197,303107),(198,303107),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2184,3515],[(57,164968),(58,105634),(73,296962),(78,137513),(81,301058),(86,2345),(97,296962),(102,139559),(106,139559),(114,141607),(149,2345),(153,99496),(154,171106),(173,296962),(174,303239),(181,301058),(182,303107),(185,2345),(186,303107),(189,2345),(190,303107),(197,141607),(206,303107)]),([7,15,240,580,802,2184,3855],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(62,303107),(73,296962),(85,303107),(97,296962),(102,303107),(105,303107),(106,303107),(109,303107),(114,303271),(130,303107),(137,303107),(141,303107),(142,303107),(145,303107),(153,99496),(154,171106),(170,303107),(173,303107),(174,303107),(177,303107),(178,303107),(181,303107),(182,303107),(186,303107),(194,303107),(197,303107),(198,303107),(201,303107),(202,303107),(206,303107)]),([7,15,240,580,802,2184,4080],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(61,303107),(77,303239),(81,301058),(97,303107),(101,303107),(102,303107),(106,303107),(114,303271),(129,303107),(130,303107),(133,303107),(137,303107),(142,303107),(145,303107),(153,99496),(154,171106),(169,303107),(170,303107),(173,303107),(174,303107),(178,303107),(181,303107),(182,303107),(186,303239),(193,303107),(194,303107),(198,303107),(202,303107),(205,303107),(206,303107)]),([7,15,240,580,802,2191],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(151,303239),(155,303107),(159,303107)]),([7,15,240,580,802,2764],[]),([7,15,240,580,802,2986],[(1,171106),(3,171106),(5,171106),(7,171106),(9,171106),(11,171106),(13,303107),(15,303107),(17,171106),(19,171106),(59,171106),(63,171106),(75,171106),(79,171106),(83,171106),(87,171106),(99,303107),(103,303107),(107,303107),(111,303107),(119,171106),(131,171106),(135,171106),(139,171106),(143,171106),(147,171106),(151,171106),(155,171106),(159,303107)]),([7,15,240,580,802,3208],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(151,303107),(155,303107),(159,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_167 : K_167.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_168 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,870,1024,2184],[(0,303271),(2,297068),(4,303271),(6,301225),(8,303271),(10,170281),(12,303271),(14,303271),(16,303271),(18,303271),(20,303271),(22,303271),(57,303271),(58,303271),(74,303271),(102,303239),(106,303239),(109,303271),(114,303271),(117,303271),(129,109859),(130,303271),(134,303271),(137,172327),(138,303271),(142,303271),(145,303271),(146,172327),(150,303271),(153,303271),(154,303271),(158,303271),(170,303271),(177,172327),(182,303271),(185,303271),(186,172327),(193,99496),(194,171106),(201,303271),(202,303271),(205,303271)]),([7,15,240,580,870,2184],[(1,303271),(3,303271),(5,303271),(7,303271),(9,141607),(11,141607),(13,303271),(15,303271),(17,303271),(19,303271),(59,303271),(63,303271),(75,141607),(79,303271),(83,10531),(87,10531),(99,303271),(103,303271),(107,303271),(111,303271),(115,303271),(119,141607),(131,303271),(135,303271),(139,303271),(143,303271),(147,141607),(151,303271),(155,303271),(159,303271)]),([7,15,240,580,1010,1024,2184],[(0,303107),(2,303107),(4,303107),(6,301193),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(97,296962),(102,303107),(106,303107),(109,303107),(114,303239),(129,303107),(130,303107),(134,303107),(137,139559),(138,303107),(142,303107),(145,303107),(146,139559),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(173,296962),(177,139559),(182,303107),(185,303107),(186,139559),(193,99464),(198,303107),(201,303107),(202,303107),(205,303107)]),([7,15,240,580,1010,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,139559),(11,139559),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(75,139559),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(115,303239),(119,139559),(131,303107),(135,303107),(139,303107),(143,303107),(147,139559),(151,303107),(155,303107),(159,303107)]),([7,15,240,580,1024,1826,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,296962),(81,301058),(97,303107),(98,303107),(102,303107),(105,303107),(106,303107),(110,303107),(113,303107),(118,303107),(129,296962),(134,303107),(138,303107),(141,301058),(146,303271),(153,303107),(154,303107),(157,303107),(170,303107),(173,296962),(177,303107),(182,303107),(185,303107),(193,303107),(194,303107),(197,303107),(201,99496),(202,171106)]),([7,15,240,580,1024,2184,2986],[(0,99496),(2,99496),(4,99496),(6,99496),(8,99496),(10,2345),(12,99496),(14,99496),(16,99496),(18,171106),(20,99496),(22,99496),(57,99496),(58,99496),(73,296962),(81,301058),(97,99496),(98,99496),(102,99496),(105,99496),(106,99496),(110,99496),(113,99496),(114,99496),(118,99496),(133,296962),(137,303107),(145,303107),(146,99496),(153,303107),(154,99496),(157,99496),(173,296969),(174,99464),(178,99464),(181,301058),(186,99496),(193,99496),(194,99496),(197,99496),(202,99496),(205,99496)]),([7,15,240,580,1024,2184,3293],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,303107),(58,303107),(73,1315),(81,1319),(97,303107),(98,303107),(102,303107),(105,303107),(106,303107),(110,303107),(113,303107),(118,303107),(130,303107),(133,1315),(137,303107),(142,303107),(145,303107),(153,303107),(154,303107),(157,303107),(173,295939),(174,303107),(177,303107),(178,303107),(186,172327),(193,303107),(194,303107),(197,303107),(202,303107),(205,303107)]),([7,15,240,580,1826,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(151,303107),(155,303107),(159,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_168 : K_168.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_169 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,580,2184,2986],[(1,99496),(3,99496),(5,99496),(7,99496),(9,99496),(11,99496),(13,303107),(15,303107),(17,99496),(19,99496),(59,99496),(63,99496),(75,99496),(79,99496),(83,99496),(87,99496),(99,303107),(103,303107),(107,303107),(111,303107),(119,99496),(131,99496),(135,99496),(139,99496),(143,99496),(147,99496),(151,99496),(155,99496),(159,303107)]),([7,15,240,580,2184,3293],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(119,303107),(131,303107),(135,303107),(139,303107),(143,303107),(155,303107),(159,303107)]),([7,15,240,802,1024,1604,2184],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,2345),(20,303107),(22,303107),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(97,303107),(98,303107),(102,303107),(105,303107),(106,303107),(110,303107),(113,303107),(114,303107),(118,303107),(129,295939),(137,301058),(145,303271),(153,305154),(154,303107),(157,303107),(170,303107),(173,295939),(177,303107),(182,303107),(185,99496),(186,303107),(193,303107),(194,303107),(197,303107),(201,303107)]),([7,15,240,802,1024,2184,2764],[(0,303107),(2,303107),(4,303107),(6,303107),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,2345),(57,303107),(58,303107),(73,295939),(78,303107),(82,303107),(85,303107),(97,303107),(98,303107),(102,303107),(105,303107),(106,303107),(110,303107),(113,303107),(114,303107),(118,303107),(133,295939),(134,303107),(137,303107),(138,303107),(145,303107),(146,303107),(153,303107),(154,303107),(157,303107),(173,296071),(177,301058),(185,303271),(194,303107),(197,303107),(202,303107),(205,303107)]),([7,15,240,802,1024,2184,3515],[(0,2345),(2,2345),(4,2345),(6,2345),(8,2345),(10,2345),(12,2345),(14,2345),(16,2345),(18,2345),(20,2345),(22,303107),(57,2345),(58,2345),(73,2338),(78,2345),(82,2345),(85,2345),(97,2345),(98,2345),(102,2345),(105,2345),(106,2345),(110,2345),(113,2345),(114,2345),(118,2345),(130,2345),(133,2338),(137,2345),(142,2345),(145,2345),(146,2345),(153,2345),(154,2345),(157,2345),(173,137513),(181,2345),(189,172327),(194,2345),(197,2345),(202,2345),(205,2345)]),([7,15,240,802,1604,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,303107),(11,303107),(13,305154),(15,305154),(17,303107),(19,303107),(59,303107),(63,303107),(75,303107),(79,303107),(83,303107),(87,303107),(99,305154),(103,303239),(107,305154),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(147,303107),(151,303107),(155,305154),(159,303107)]),([7,15,240,802,2184,2764],[(1,303107),(3,303107),(5,303107),(7,303107),(9,303107),(11,303107),(13,303107),(15,303107),(59,303107),(63,303107),(75,303107),(79,303107),(83,303107),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(115,303107),(119,303107),(135,303239),(143,303107),(159,303107)]),([7,15,240,802,2184,3515],[(1,2345),(3,2345),(5,2345),(7,2345),(9,2345),(11,2345),(13,2345),(15,2345),(59,2345),(63,2345),(75,2345),(79,2345),(83,2345),(87,2345),(99,2345),(103,2345),(107,2345),(111,2345),(115,2345),(119,2345),(135,137513),(143,2345),(159,2345)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_169 : K_169.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_170 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,255,580,802,1024,2184],[(0,303107),(2,164968),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(58,303107),(61,303107),(73,105634),(81,301058),(102,303107),(109,301193),(110,303107),(114,303271),(129,105634),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(146,105634),(150,303107),(153,303107),(154,303107),(158,303107),(170,303107),(177,303107),(182,303107),(185,303107),(186,105634),(193,99496),(194,171106),(201,303107),(202,303107),(205,303107)]),([7,15,255,580,802,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,105634),(11,105634),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303239),(83,105634),(87,105634),(99,303107),(103,303107),(107,303107),(111,303107),(115,105634),(119,105634),(131,303107),(135,303107),(139,303107),(143,303107),(147,105634),(151,303107),(155,303107),(159,303107)]),([7,15,580,756,802,1024,2184],[(0,301058),(2,301058),(4,301058),(6,301058),(8,301058),(10,301058),(12,301058),(14,1319),(16,301058),(18,301058),(20,301058),(22,301058),(57,296962),(58,301058),(73,296962),(74,301058),(82,301058),(85,301058),(97,296962),(129,301058),(130,301058),(134,301058),(137,301058),(138,301058),(142,301058),(145,301058),(146,301058),(150,301058),(153,301058),(158,301058),(170,301058),(173,296962),(177,301058),(178,301058),(185,301058),(190,301058),(193,301058),(194,171106),(201,301058),(202,301058),(205,301058)]),([7,15,580,756,802,2184],[(1,301058),(3,301058),(5,301058),(7,301058),(9,301058),(11,301058),(17,301058),(19,301058),(59,301058),(63,301058),(75,301058),(79,301058),(83,301058),(87,301058),(131,301058),(135,301058),(139,301058),(143,301058),(147,301058),(151,301058),(159,301058)]),([7,15,580,802,1024,1264,2184],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,296962),(73,296962),(78,139559),(82,172327),(97,303107),(98,303107),(105,303107),(113,303107),(114,303107),(129,164968),(130,303107),(138,301058),(145,139559),(150,301058),(154,303107),(157,303107),(170,303107),(173,296962),(177,303107),(185,99496),(186,171106),(193,303107),(194,303107),(201,303107),(206,303107)]),([7,15,580,802,1024,2184,2296],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,296962),(73,296962),(78,139559),(82,172327),(97,303107),(98,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(118,303107),(130,303107),(133,296962),(137,303107),(145,303107),(146,303107),(153,303107),(154,303107),(157,303107),(170,303107),(173,296962),(178,301058),(185,139559),(190,301058),(193,303107),(194,303107),(197,303107),(202,303107),(205,303107)]),([7,15,580,802,1024,2184,3855],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,296962),(73,296962),(78,301193),(82,301225),(97,303107),(98,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(118,303107),(130,303107),(133,296962),(137,303107),(145,99496),(146,171106),(153,303107),(154,303107),(157,303107),(170,303107),(173,303107),(178,301058),(189,303107),(190,303107),(193,303107),(194,303107),(197,303107),(201,303107),(202,303107)]),([7,15,580,802,2184,2296],[(1,303107),(3,303107),(9,303107),(11,303107),(13,303107),(15,303107),(17,303107),(19,303107),(63,303239),(75,303107),(79,303107),(99,303107),(103,303107),(111,303107),(115,303107),(119,303107),(131,303107),(135,303107),(143,303107),(147,303107),(151,303107),(155,303107),(159,303107)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_170 : K_170.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_171 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,580,802,2184,3855],[(1,303107),(3,303107),(9,303107),(11,303107),(13,303107),(15,303107),(17,303107),(19,303107),(63,303239),(75,303107),(79,303107),(99,303107),(103,303107),(111,303107),(115,303107),(119,303107),(131,303107),(135,303107),(139,303107),(147,303107),(151,303107),(155,303107),(159,303107)]),([7,240,255,580,802,1024,2184],[(0,303107),(2,105634),(4,303107),(6,303107),(8,303107),(10,2345),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(58,303107),(61,303107),(73,164968),(81,296962),(98,303107),(105,296962),(110,303107),(114,303271),(129,164968),(130,303107),(134,303107),(137,303107),(138,303107),(142,303107),(145,303107),(146,164968),(150,303107),(153,303107),(154,303107),(158,303107),(174,303107),(181,296962),(182,303107),(185,303107),(186,164968),(193,99496),(194,171106),(201,303107),(202,303107),(205,303107)]),([7,240,255,580,802,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(9,164968),(11,164968),(13,303107),(15,303107),(17,303107),(19,303107),(59,303107),(63,303107),(79,303107),(83,164968),(87,164968),(99,303107),(103,303107),(107,303107),(111,303107),(115,164968),(119,164968),(131,303107),(135,303107),(139,303107),(143,303107),(147,164968),(151,303107),(155,303107),(159,303107)]),([7,240,580,591,802,1024,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,296962),(12,296962),(14,1315),(16,296962),(18,296962),(20,296962),(22,296962),(57,296962),(58,296962),(73,296962),(74,296962),(82,296962),(85,296962),(98,296962),(101,296962),(113,296962),(118,295939),(129,296962),(130,296962),(134,296962),(137,295939),(138,296962),(142,296962),(145,296962),(146,296962),(150,296962),(153,296962),(154,295939),(158,296962),(169,296962),(174,296962),(177,295939),(178,296962),(186,296962),(189,296962),(193,296962),(194,171106),(201,296962),(202,296962),(205,296962)]),([7,240,580,591,802,2184],[(1,296962),(3,296962),(5,296962),(7,296962),(9,296962),(11,296962),(13,295939),(15,295939),(17,296962),(19,296962),(59,296962),(63,296962),(75,296962),(79,296962),(83,296962),(87,296962),(99,295939),(103,296962),(115,296962),(119,295939),(131,296962),(135,296962),(139,296962),(143,296962),(147,296962),(151,296962),(155,295939),(159,296962)]),([7,240,580,802,815,1024,2184],[(0,296962),(2,296962),(4,296962),(6,2338),(8,296962),(10,1315),(12,296962),(14,296962),(16,296962),(18,296962),(20,296962),(22,296962),(57,296962),(74,296962),(77,296962),(98,296962),(101,296962),(106,296962),(114,296962),(117,296962),(129,296962),(130,296962),(134,296962),(137,295939),(138,296962),(142,296962),(145,296962),(146,295939),(150,296962),(153,296962),(154,296962),(158,296962),(169,296962),(174,296962),(177,295939),(178,296962),(185,296962),(186,295939),(194,296962),(197,296962),(201,296962),(202,296962),(205,296962)]),([7,240,580,802,815,2184],[(1,296962),(3,296962),(5,296962),(7,296962),(9,295939),(11,295939),(13,296962),(15,296962),(17,296962),(19,296962),(59,296962),(63,296962),(75,295939),(79,296962),(99,296962),(103,296962),(107,296962),(111,296962),(115,296962),(119,295939),(131,296962),(135,296962),(139,296962),(143,296962),(147,295939),(151,296962),(155,296962),(159,296962)]),([7,240,580,802,1024,1039,2184],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,301058),(74,303107),(77,301058),(82,109859),(97,303107),(98,303107),(105,303107),(113,303107),(114,303107),(129,105634),(130,303107),(138,296962),(146,296962),(149,8483),(154,303107),(157,303107),(169,303107),(174,303107),(177,303107),(185,99496),(186,171106),(193,303107),(194,303107),(202,303107),(205,296962)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_171 : K_171.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_172 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,580,802,1024,2184,4080],[(0,303107),(2,303107),(4,303107),(6,2345),(8,303107),(10,303107),(12,303107),(14,303107),(16,303107),(18,303107),(20,303107),(22,303107),(57,301058),(74,303107),(77,301058),(82,297068),(97,303107),(98,303107),(102,303107),(105,303107),(110,303107),(113,303107),(114,303107),(118,303107),(129,303107),(134,303107),(137,303107),(145,99496),(146,171106),(153,303107),(154,303107),(157,303107),(170,303107),(173,303107),(178,296962),(185,303107),(186,295939),(193,303107),(194,303107),(197,303107),(205,303107),(206,296962)]),([7,240,580,802,2184,4080],[(1,303107),(3,303107),(9,303107),(11,303107),(13,303107),(15,303107),(17,303107),(19,303107),(63,303107),(75,303107),(79,303107),(99,303107),(103,303107),(111,303107),(115,303107),(119,303107),(131,303107),(135,303107),(139,303239),(147,303107),(151,303107),(155,303107),(159,303107)]),([8,15,240,580,802,1024,2184],[(1,303107),(3,303107),(5,303107),(7,303107),(13,303107),(15,303107),(17,303107),(19,303107),(21,303107),(23,303107),(59,303107),(63,303107),(79,303239),(87,303107),(99,303107),(103,303107),(107,303107),(111,303107),(131,303107),(135,303107),(139,303107),(143,303107),(151,303107),(155,303107),(159,303107),(171,303107),(175,303107),(179,303107),(183,303107),(191,303107),(195,303107),(199,303107),(203,303107),(207,303107)]),([8,15,240,580,802,2184],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_172 : K_172.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((((((((K_0 ++ K_1) ++ (K_2 ++ (K_3 ++ K_4))) ++ ((K_5 ++ K_6) ++ (K_7 ++ (K_8 ++ K_9)))) ++ (((K_10 ++ K_11) ++ (K_12 ++ (K_13 ++ K_14))) ++ ((K_15 ++ (K_16 ++ K_17)) ++ (K_18 ++ (K_19 ++ K_20))))) ++ ((((K_21 ++ K_22) ++ (K_23 ++ (K_24 ++ K_25))) ++ ((K_26 ++ (K_27 ++ K_28)) ++ (K_29 ++ (K_30 ++ K_31)))) ++ (((K_32 ++ K_33) ++ (K_34 ++ (K_35 ++ K_36))) ++ ((K_37 ++ (K_38 ++ K_39)) ++ (K_40 ++ (K_41 ++ K_42)))))) ++ (((((K_43 ++ K_44) ++ (K_45 ++ (K_46 ++ K_47))) ++ ((K_48 ++ K_49) ++ (K_50 ++ (K_51 ++ K_52)))) ++ (((K_53 ++ K_54) ++ (K_55 ++ (K_56 ++ K_57))) ++ ((K_58 ++ (K_59 ++ K_60)) ++ (K_61 ++ (K_62 ++ K_63))))) ++ ((((K_64 ++ K_65) ++ (K_66 ++ (K_67 ++ K_68))) ++ ((K_69 ++ (K_70 ++ K_71)) ++ (K_72 ++ (K_73 ++ K_74)))) ++ (((K_75 ++ K_76) ++ (K_77 ++ (K_78 ++ K_79))) ++ ((K_80 ++ (K_81 ++ K_82)) ++ (K_83 ++ (K_84 ++ K_85))))))) ++ ((((((K_86 ++ K_87) ++ (K_88 ++ (K_89 ++ K_90))) ++ ((K_91 ++ K_92) ++ (K_93 ++ (K_94 ++ K_95)))) ++ (((K_96 ++ K_97) ++ (K_98 ++ (K_99 ++ K_100))) ++ ((K_101 ++ (K_102 ++ K_103)) ++ (K_104 ++ (K_105 ++ K_106))))) ++ ((((K_107 ++ K_108) ++ (K_109 ++ (K_110 ++ K_111))) ++ ((K_112 ++ (K_113 ++ K_114)) ++ (K_115 ++ (K_116 ++ K_117)))) ++ (((K_118 ++ K_119) ++ (K_120 ++ (K_121 ++ K_122))) ++ ((K_123 ++ (K_124 ++ K_125)) ++ (K_126 ++ (K_127 ++ K_128)))))) ++ (((((K_129 ++ K_130) ++ (K_131 ++ (K_132 ++ K_133))) ++ ((K_134 ++ (K_135 ++ K_136)) ++ (K_137 ++ (K_138 ++ K_139)))) ++ (((K_140 ++ K_141) ++ (K_142 ++ (K_143 ++ K_144))) ++ ((K_145 ++ (K_146 ++ K_147)) ++ (K_148 ++ (K_149 ++ K_150))))) ++ ((((K_151 ++ K_152) ++ (K_153 ++ (K_154 ++ K_155))) ++ ((K_156 ++ (K_157 ++ K_158)) ++ (K_159 ++ (K_160 ++ K_161)))) ++ (((K_162 ++ K_163) ++ (K_164 ++ (K_165 ++ K_166))) ++ ((K_167 ++ (K_168 ++ K_169)) ++ (K_170 ++ (K_171 ++ K_172))))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 (all_app c_3 c_4))) (all_app (all_app c_5 c_6) (all_app c_7 (all_app c_8 c_9)))) (all_app (all_app (all_app c_10 c_11) (all_app c_12 (all_app c_13 c_14))) (all_app (all_app c_15 (all_app c_16 c_17)) (all_app c_18 (all_app c_19 c_20))))) (all_app (all_app (all_app (all_app c_21 c_22) (all_app c_23 (all_app c_24 c_25))) (all_app (all_app c_26 (all_app c_27 c_28)) (all_app c_29 (all_app c_30 c_31)))) (all_app (all_app (all_app c_32 c_33) (all_app c_34 (all_app c_35 c_36))) (all_app (all_app c_37 (all_app c_38 c_39)) (all_app c_40 (all_app c_41 c_42)))))) (all_app (all_app (all_app (all_app (all_app c_43 c_44) (all_app c_45 (all_app c_46 c_47))) (all_app (all_app c_48 c_49) (all_app c_50 (all_app c_51 c_52)))) (all_app (all_app (all_app c_53 c_54) (all_app c_55 (all_app c_56 c_57))) (all_app (all_app c_58 (all_app c_59 c_60)) (all_app c_61 (all_app c_62 c_63))))) (all_app (all_app (all_app (all_app c_64 c_65) (all_app c_66 (all_app c_67 c_68))) (all_app (all_app c_69 (all_app c_70 c_71)) (all_app c_72 (all_app c_73 c_74)))) (all_app (all_app (all_app c_75 c_76) (all_app c_77 (all_app c_78 c_79))) (all_app (all_app c_80 (all_app c_81 c_82)) (all_app c_83 (all_app c_84 c_85))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_86 c_87) (all_app c_88 (all_app c_89 c_90))) (all_app (all_app c_91 c_92) (all_app c_93 (all_app c_94 c_95)))) (all_app (all_app (all_app c_96 c_97) (all_app c_98 (all_app c_99 c_100))) (all_app (all_app c_101 (all_app c_102 c_103)) (all_app c_104 (all_app c_105 c_106))))) (all_app (all_app (all_app (all_app c_107 c_108) (all_app c_109 (all_app c_110 c_111))) (all_app (all_app c_112 (all_app c_113 c_114)) (all_app c_115 (all_app c_116 c_117)))) (all_app (all_app (all_app c_118 c_119) (all_app c_120 (all_app c_121 c_122))) (all_app (all_app c_123 (all_app c_124 c_125)) (all_app c_126 (all_app c_127 c_128)))))) (all_app (all_app (all_app (all_app (all_app c_129 c_130) (all_app c_131 (all_app c_132 c_133))) (all_app (all_app c_134 (all_app c_135 c_136)) (all_app c_137 (all_app c_138 c_139)))) (all_app (all_app (all_app c_140 c_141) (all_app c_142 (all_app c_143 c_144))) (all_app (all_app c_145 (all_app c_146 c_147)) (all_app c_148 (all_app c_149 c_150))))) (all_app (all_app (all_app (all_app c_151 c_152) (all_app c_153 (all_app c_154 c_155))) (all_app (all_app c_156 (all_app c_157 c_158)) (all_app c_159 (all_app c_160 c_161)))) (all_app (all_app (all_app c_162 c_163) (all_app c_164 (all_app c_165 c_166))) (all_app (all_app c_167 (all_app c_168 c_169)) (all_app c_170 (all_app c_171 c_172))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 8) (hr : Matches C) : False := by
  let f : BFn 6 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 6 × Fin 6) (hp : p ∈ samplePairs) : f (pt 6 (pairCode p)) = reference (pt 6 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 6 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 6 → Bool, f x ≠ f y := by
    refine ⟨pt 6 (pairCode (0,0)),pt 6 (pairCode (0,2)),?_⟩
    rw [he (0,0) (by decide +kernel),he (0,2) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_23616.Core


namespace PEqualNP.Outside.L_meta_23616.SampleBank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_23616

def chosen : Finset (Fin 21) := [0, 2, 3, 5, 6, 7, 8, 10, 11, 12, 18, 20].toFinset

theorem chosen_card : chosen.card = 12 := by decide +kernel
theorem coverChosen : ∀ p ∈ Core.samplePairs, ∃ k ∈ chosen, sample k=p := by decide +kernel
theorem failsChosen (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 8) :
    ¬ ∀ i ∈ chosen, Check C i := by
  intro hsample
  apply Core.coreLower C fan size
  intro p hp
  obtain ⟨i,hi,ev⟩ := coverChosen p hp
  simpa only [Check,ev,Core.pairInput] using hsample i hi

end PEqualNP.Outside.L_meta_23616.SampleBank

open PEqualNP.Outside.L_meta_23616.SampleBank PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_23616 :
    (∀ S : Finset (Fin 21), S.card ≤ 11 →
      ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i ∈ S, Check C i) ∧
    (∃ S : Finset (Fin 21), S.card=12 ∧
      ∀ C : Circuit, FanInTwo C → C.size ≤ 8 → ¬ ∀ i ∈ S, Check C i) :=
  ⟨everyEleven,chosen,chosen_card,failsChosen⟩
