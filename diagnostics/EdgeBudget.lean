import PEqualNP.Defs
import Mathlib
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_lib_912_aux

open scoped Classical

abbrev F2 := ZMod 2
abbrev V2 := Fin 2 → F2
abbrev V4 := Fin 4 → F2

section Graph

variable {X : Type*} [DecidableEq X]
variable (f : X → X) (S : Finset X)

def edge (x y : X) : Prop := x ∈ S ∧ y ∈ S ∧ (f x = y ∨ f y = x)

noncomputable def cc (x : X) : Finset X := S.filter (Relation.ReflTransGen (edge f S) x)
noncomputable def pcs : Finset (Finset X) := S.image (cc f S)
def halo (C : Finset X) : Finset X := C ∪ C.image f

omit [DecidableEq X] in
lemma selfMem {x : X} (hx : x ∈ S) : x ∈ cc f S x :=
  Finset.mem_filter.mpr ⟨hx, .refl⟩

omit [DecidableEq X] in
lemma same {x y : X} (h : Relation.ReflTransGen (edge f S) x y) :
    cc f S x = cc f S y := by
  let : Std.Symm (edge f S) := ⟨fun _ _ e => ⟨e.2.1, e.1, e.2.2.symm⟩⟩
  have back := Std.Symm.symm (r := Relation.ReflTransGen (edge f S)) _ _ h
  ext z
  simp only [cc, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun p => back.trans p, fun p => h.trans p⟩

lemma center {C : Finset X} (hC : C ∈ pcs f S) {x : X} (hx : x ∈ C) :
    x ∈ S ∧ cc f S x = C := by
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hx, p⟩ := Finset.mem_filter.mp hx
  exact ⟨hx, (same f S p).symm⟩

lemma populated {C : Finset X} (hC : C ∈ pcs f S) : C.Nonempty := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨w, selfMem f S hw⟩

lemma joined {C D : Finset X} (hc : C ∈ pcs f S) (hd : D ∈ pcs f S)
    {x y : X} (hx : x ∈ C) (hy : y ∈ D) (h : x = y ∨ f x = y ∨ f y = x) : C = D := by
  obtain ⟨xs, xc⟩ := center f S hc hx
  obtain ⟨ys, yc⟩ := center f S hd hy
  rw [← xc, ← yc]
  rcases h with rfl | h
  · rfl
  · exact same f S (.single ⟨xs, ys, h⟩)

lemma separate (inj : Function.Injective f) :
    (↑(pcs f S) : Set (Finset X)).PairwiseDisjoint (halo f) := by
  intro C hc D hd ne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [halo, Finset.mem_union, Finset.mem_image] at hz hz'
  rcases hz with h | ⟨x, h, rfl⟩ <;> rcases hz' with h' | ⟨y, h', eq⟩
  · exact ne (joined f S hc hd h h' (Or.inl rfl))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inr eq)))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inl rfl)))
  · exact ne (joined f S hc hd h h' (Or.inl (inj eq).symm))

lemma pcs_pairwiseDisjoint :
    (↑(pcs f S) : Set (Finset X)).PairwiseDisjoint id := by
  intro C hc D hd ne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact ne (joined f S hc hd hz hz' (Or.inl rfl))

lemma pcs_biUnion_eq : (pcs f S).biUnion id = S := by
  ext x
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨C, hC, hx⟩
    exact (center f S hC hx).1
  · intro hx
    exact ⟨cc f S x, Finset.mem_image_of_mem _ hx, selfMem f S hx⟩

end Graph

section Cycle

variable {t : ℕ} (ht : 0 < t)

def idx (k : ℕ) : Fin (6 * t) := ⟨k % (6 * t), Nat.mod_lt _ (by omega)⟩
def nxt (i : Fin (6 * t)) : Fin (6 * t) := ⟨(i.val + 1) % (6 * t), Nat.mod_lt _ (by omega)⟩
def prv (i : Fin (6 * t)) : Fin (6 * t) := ⟨(i.val + 6 * t - 1) % (6 * t), Nat.mod_lt _ (by omega)⟩

lemma mod_eq_sub_of_lt2 {a m : ℕ} (h1 : m ≤ a) (h2 : a < 2 * m) : a % m = a - m := by
  have e : a = (a - m) + m := by omega
  conv_lhs => rw [e]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma idx_val (k : ℕ) : (idx ht k).val = k % (6 * t) := rfl

lemma idx_self (i : Fin (6 * t)) : idx ht i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma nxt_val (i : Fin (6 * t)) :
    (nxt ht i).val = if i.val + 1 < 6 * t then i.val + 1 else 0 := by
  have hi := i.isLt
  unfold nxt
  dsimp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have e : i.val + 1 = 6 * t := by omega
    simp [e]

lemma prv_val (i : Fin (6 * t)) :
    (prv ht i).val = if i.val = 0 then 6 * t - 1 else i.val - 1 := by
  have hi := i.isLt
  unfold prv
  dsimp only
  split_ifs with h
  · simp [h, Nat.mod_eq_of_lt (by omega : 6 * t - 1 < 6 * t)]
  · have e : i.val + 6 * t - 1 = (i.val - 1) + 6 * t := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma nxt_idx (k : ℕ) : nxt ht (idx ht k) = idx ht (k + 1) := by
  apply Fin.ext
  change (k % (6 * t) + 1) % (6 * t) = (k + 1) % (6 * t)
  rw [Nat.mod_add_mod]

lemma nxt_prv (i : Fin (6 * t)) : nxt ht (prv ht i) = i := by
  have hi := i.isLt
  apply Fin.ext
  by_cases h : i.val = 0
  · rw [nxt_val, prv_val, if_pos h, if_neg (by omega)]; omega
  · rw [nxt_val, prv_val, if_neg h, if_pos (by omega)]; omega

lemma prv_nxt (i : Fin (6 * t)) : prv ht (nxt ht i) = i := by
  have hi := i.isLt
  apply Fin.ext
  by_cases h : i.val + 1 < 6 * t
  · rw [prv_val, nxt_val, if_pos h, if_neg (by omega)]; omega
  · rw [prv_val, nxt_val, if_neg h, if_pos rfl]; omega

lemma ninj : Function.Injective (nxt ht) := by
  intro i j h
  have := congrArg (prv ht) h
  simpa [prv_nxt] using this

lemma nxt_parity (i : Fin (6 * t)) : (nxt ht i).val % 2 = (i.val + 1) % 2 := by
  have hi := i.isLt
  rw [nxt_val]
  split_ifs <;> omega

lemma idx_mod6 (k : ℕ) : (idx ht k).val % 6 = k % 6 := by
  change (k % (6 * t)) % 6 = k % 6
  exact Nat.mod_mod_of_dvd k ⟨t, rfl⟩

lemma idx_mod2 (k : ℕ) : (idx ht k).val % 2 = k % 2 := by
  change (k % (6 * t)) % 2 = k % 2
  exact Nat.mod_mod_of_dvd k ⟨3 * t, by ring⟩

lemma idx_div2_mod3 (k : ℕ) : (idx ht k).val / 2 % 3 = k / 2 % 3 := by
  have h6 := idx_mod6 ht k
  omega

lemma idx_add_dist (x y : Fin (6 * t)) :
    idx ht (x.val + (y.val + 6 * t - x.val) % (6 * t)) = y := by
  apply Fin.ext
  change (x.val + (y.val + 6 * t - x.val) % (6 * t)) % (6 * t) = y.val
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h1 : x.val + (y.val + 6 * t - x.val) = y.val + 6 * t := by have := x.isLt; omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

lemma idx_inj_range (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t)
    {j₁ j₂ : ℕ} (h1 : j₁ < m) (h2 : j₂ < m)
    (heq : idx ht (s.val + j₁) = idx ht (s.val + j₂)) : j₁ = j₂ := by
  have hv := congrArg Fin.val heq
  change (s.val + j₁) % (6 * t) = (s.val + j₂) % (6 * t) at hv
  have hs := s.isLt
  by_cases c1 : s.val + j₁ < 6 * t <;> by_cases c2 : s.val + j₂ < 6 * t
  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
  · rw [Nat.mod_eq_of_lt c1, mod_eq_sub_of_lt2 (by omega) (by omega)] at hv; omega
  · rw [mod_eq_sub_of_lt2 (by omega) (by omega), Nat.mod_eq_of_lt c2] at hv; omega
  · rw [mod_eq_sub_of_lt2 (by omega) (by omega), mod_eq_sub_of_lt2 (by omega) (by omega)] at hv; omega

def arc (s : Fin (6 * t)) (m : ℕ) : Finset (Fin (6 * t)) :=
  (Finset.range m).image (fun k => idx ht (s.val + k))

lemma card_arc (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t) : (arc ht s m).card = m := by
  unfold arc
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j₁ hj₁ j₂ hj₂ heq
  exact idx_inj_range ht s hm (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂) heq

lemma mem_arc_iff (s : Fin (6 * t)) (m : ℕ) (x : Fin (6 * t)) :
    x ∈ arc ht s m ↔ ∃ k < m, idx ht (s.val + k) = x := by
  simp [arc]

lemma start_of_proper {C : Finset (Fin (6 * t))} (ne : C.Nonempty) (pr : C ≠ Finset.univ) :
    ∃ s ∈ C, prv ht s ∉ C := by
  by_contra! h
  obtain ⟨w, hw⟩ : ∃ w : Fin (6 * t), w ∉ C := by
    by_contra! hall
    exact pr (Finset.eq_univ_of_forall hall)
  have hstep : ∀ x : Fin (6 * t), x ∉ C → nxt ht x ∉ C := by
    intro x hx hnx
    exact hx (prv_nxt ht x ▸ h (nxt ht x) hnx)
  have go (k : ℕ) : idx ht (w.val + k) ∉ C := by
    induction k with
    | zero => simpa [idx_self] using hw
    | succ k ih =>
      rw [← add_assoc, ← nxt_idx]
      exact hstep _ ih
  obtain ⟨y, hy⟩ := ne
  have e : idx ht (w.val + (6 * t - w.val + y.val)) = y := by
    apply Fin.ext
    change (w.val + (6 * t - w.val + y.val)) % (6 * t) = y.val
    have h1 : w.val + (6 * t - w.val + y.val) = y.val + 6 * t := by have := w.isLt; omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
  exact go (6 * t - w.val + y.val) (e.symm ▸ hy)

lemma comp_arc_of_start {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {s : Fin (6 * t)} (hs : s ∈ S) (hp : prv ht s ∉ S) :
    cc (nxt ht) S s = arc ht s (cc (nxt ht) S s).card ∧
      (cc (nxt ht) S s).card < 6 * t ∧
      idx ht (s.val + (cc (nxt ht) S s).card) ∉ S := by
  have hex : ∃ k : ℕ, idx ht (s.val + k) ∉ S := by
    have ⟨y, hy⟩ : ∃ y : Fin (6 * t), y ∉ S := by
      by_contra! hall
      exact hS (Finset.eq_univ_of_forall hall)
    refine ⟨6 * t - s.val + y.val, ?_⟩
    have e : idx ht (s.val + (6 * t - s.val + y.val)) = y := by
      apply Fin.ext
      change (s.val + (6 * t - s.val + y.val)) % (6 * t) = y.val
      have h1 : s.val + (6 * t - s.val + y.val) = y.val + 6 * t := by have := s.isLt; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
    rwa [e]
  let k0 := Nat.find hex
  have hk0_out : idx ht (s.val + k0) ∉ S := Nat.find_spec hex
  have hk0_pos : 0 < k0 := by
    by_contra h0
    have : k0 = 0 := by omega
    rw [this, add_zero, idx_self] at hk0_out
    exact hk0_out hs
  have hk0_lt : k0 < 6 * t := by
    by_contra hge
    have hprev : 6 * t - 1 < k0 := by omega
    have hin : idx ht (s.val + (6 * t - 1)) ∈ S := by
      by_contra hout
      exact Nat.find_min hex hprev hout
    have e : idx ht (s.val + (6 * t - 1)) = prv ht s := by
      apply Fin.ext
      change (s.val + (6 * t - 1)) % (6 * t) = (s.val + 6 * t - 1) % (6 * t)
      congr 1; omega
    rw [e] at hin
    exact hp hin
  have hsub1 : arc ht s k0 ⊆ cc (nxt ht) S s := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_arc_iff ht s k0 x).mp hx
    clear hx
    induction k with
    | zero =>
      rw [add_zero, idx_self]
      exact selfMem (nxt ht) S hs
    | succ k ih =>
      have hk' : k < k0 := by omega
      have hprev := ih hk'
      obtain ⟨hprevS, hpath⟩ := Finset.mem_filter.mp hprev
      have hcurS : idx ht (s.val + (k + 1)) ∈ S := by
        by_contra hout
        exact Nat.find_min hex hk hout
      refine Finset.mem_filter.mpr ⟨hcurS, hpath.tail ⟨hprevS, hcurS, Or.inl ?_⟩⟩
      rw [← add_assoc, nxt_idx]
  have hsub2 : cc (nxt ht) S s ⊆ arc ht s k0 := by
    intro x hx
    obtain ⟨hxS, hpath⟩ := Finset.mem_filter.mp hx
    clear hx hxS
    induction hpath with
    | refl =>
      exact (mem_arc_iff ht s k0 s).mpr ⟨0, hk0_pos, by rw [add_zero, idx_self]⟩
    | @tail y z _ he ih =>
      obtain ⟨k, hk, hka⟩ := (mem_arc_iff ht s k0 y).mp ih
      rcases he.2.2 with hf | hb
      · have hy : idx ht (s.val + (k + 1)) = z := by
          rw [← add_assoc, ← nxt_idx, hka, hf]
        have hne : k + 1 ≠ k0 := by
          intro eq
          rw [eq] at hy
          exact hk0_out (hy.symm ▸ he.2.1)
        exact (mem_arc_iff ht s k0 z).mpr ⟨k + 1, by omega, hy⟩
      · have hprev_eq : z = prv ht (idx ht (s.val + k)) := by
          rw [hka, ← hb, prv_nxt]
        cases k with
        | zero =>
          rw [add_zero, idx_self] at hprev_eq
          exact (hp (hprev_eq ▸ he.2.1)).elim
        | succ k =>
          have hz : idx ht (s.val + k) = z := by
            rw [hprev_eq, ← add_assoc, ← nxt_idx, prv_nxt]
          exact (mem_arc_iff ht s k0 z).mpr ⟨k, by omega, hz⟩
  have heq : cc (nxt ht) S s = arc ht s k0 := Finset.Subset.antisymm hsub2 hsub1
  have hcard : (cc (nxt ht) S s).card = k0 := by
    rw [heq, card_arc ht s (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact heq
  · rw [hcard]; exact hk0_lt
  · rw [hcard]; exact hk0_out

lemma comp_arc {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) S) :
    ∃ s ∈ C, prv ht s ∉ S ∧ C = arc ht s C.card ∧
      0 < C.card ∧ C.card < 6 * t ∧ idx ht (s.val + C.card) ∉ S := by
  have hne := populated (nxt ht) S hC
  have hpr : C ≠ Finset.univ := by
    intro eq
    apply hS
    apply Finset.eq_univ_of_forall
    intro x
    exact (center (nxt ht) S hC (eq.symm ▸ Finset.mem_univ x)).1
  obtain ⟨s, hsC, hpsC⟩ := start_of_proper ht hne hpr
  obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
  have hpsS : prv ht s ∉ S := by
    intro hpS
    apply hpsC
    rw [← hcs]
    exact Finset.mem_filter.mpr ⟨hpS, .single ⟨hsS, hpS, Or.inr (nxt_prv ht s)⟩⟩
  obtain ⟨harc, hlt, hout⟩ := comp_arc_of_start ht hS hsS hpsS
  rw [hcs] at harc hlt hout
  exact ⟨s, hsC, hpsS, harc, Finset.card_pos.mpr hne, hlt, hout⟩

lemma halo_arc (s : Fin (6 * t)) {m : ℕ} (hm : 0 < m) :
    halo (nxt ht) (arc ht s m) = arc ht s (m + 1) := by
  ext x
  simp only [halo, Finset.mem_union, Finset.mem_image, mem_arc_iff]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨y, ⟨k, hk, rfl⟩, rfl⟩)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨k + 1, by omega, by rw [← add_assoc, nxt_idx]⟩
  · rintro ⟨k, hk, rfl⟩
    by_cases hk' : k < m
    · exact Or.inl ⟨k, hk', rfl⟩
    · have hk1 : k = m := by omega
      rw [hk1]
      refine Or.inr ⟨idx ht (s.val + (m - 1)), ⟨m - 1, by omega, rfl⟩, ?_⟩
      rw [nxt_idx]; congr 1; omega

lemma halo_card_eq {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) S) :
    (halo (nxt ht) C).card = C.card + 1 := by
  obtain ⟨s, _, _, harc, hpos, hlt, _⟩ := comp_arc ht hS hC
  conv_lhs => rw [harc, halo_arc ht s hpos, card_arc ht s (by omega)]

lemma sum_halo_le {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ) :
    ∑ C ∈ pcs (nxt ht) S, (C.card + 1) ≤ 6 * t := by
  have h1 : ∑ C ∈ pcs (nxt ht) S, (C.card + 1) =
      ∑ C ∈ pcs (nxt ht) S, (halo (nxt ht) C).card :=
    Finset.sum_congr rfl fun C hC => (halo_card_eq ht hS hC).symm
  rw [h1, ← Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
  simpa using Finset.card_le_univ ((pcs (nxt ht) S).biUnion (halo (nxt ht)))

lemma mem_biUnion_halo_iff {S : Finset (Fin (6 * t))} (x : Fin (6 * t)) :
    x ∈ (pcs (nxt ht) S).biUnion (halo (nxt ht)) ↔ x ∈ S ∨ prv ht x ∈ S := by
  simp only [Finset.mem_biUnion, halo, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨C, hC, hx | ⟨y, hy, rfl⟩⟩
    · exact Or.inl (center (nxt ht) S hC hx).1
    · rw [prv_nxt]
      exact Or.inr (center (nxt ht) S hC hy).1
  · rintro (hx | hpx)
    · exact ⟨cc (nxt ht) S x, Finset.mem_image_of_mem _ hx, Or.inl (selfMem (nxt ht) S hx)⟩
    · exact ⟨cc (nxt ht) S (prv ht x), Finset.mem_image_of_mem _ hpx,
        Or.inr ⟨prv ht x, selfMem (nxt ht) S hpx, nxt_prv ht x⟩⟩

end Cycle

section Columns

def col2 (r : ℕ) : V2 :=
  if r % 3 = 0 then ![1, 0] else if r % 3 = 1 then ![0, 1] else ![1, 1]

def hPat (k : ℕ) : V4 :=
  fun b => if k % 2 = b.val / 2 ∧ (k / 2 % 3 = b.val % 2 ∨ k / 2 % 3 = 2) then 1 else 0

def hVec {t : ℕ} (i : Fin (6 * t)) : V4 :=
  fun b => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then 1 else 0

def hSum {t : ℕ} (C : Finset (Fin (6 * t))) : V4 := ∑ i ∈ C, hVec i

def evenProj : V4 →ₗ[F2] V2 where
  toFun v b := v ⟨b.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def oddProj : V4 →ₗ[F2] V2 where
  toFun v b := v ⟨b.val + 2, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def incEven : V2 →ₗ[F2] V4 where
  toFun u b := if h : b.val < 2 then u ⟨b.val, h⟩ else 0
  map_add' u v := by ext b; dsimp; split_ifs <;> simp
  map_smul' c u := by ext b; dsimp; split_ifs <;> simp

def incOdd : V2 →ₗ[F2] V4 where
  toFun u b := if h : 2 ≤ b.val then u ⟨b.val - 2, by omega⟩ else 0
  map_add' u v := by ext b; dsimp; split_ifs <;> simp
  map_smul' c u := by ext b; dsimp; split_ifs <;> simp

lemma evenProj_incEven (u : V2) : evenProj (incEven u) = u := by
  ext b; fin_cases b <;> rfl

lemma oddProj_incEven (u : V2) : oddProj (incEven u) = 0 := by
  ext b; fin_cases b <;> rfl

lemma evenProj_incOdd (u : V2) : evenProj (incOdd u) = 0 := by
  ext b; fin_cases b <;> rfl

lemma oddProj_incOdd (u : V2) : oddProj (incOdd u) = u := by
  ext b; fin_cases b <;> rfl

lemma incEven_inj : Function.Injective incEven := fun u v h => by
  have := congrArg evenProj h
  simpa [evenProj_incEven] using this

lemma incOdd_inj : Function.Injective incOdd := fun u v h => by
  have := congrArg oddProj h
  simpa [oddProj_incOdd] using this

lemma v4_decomp (v : V4) : v = incEven (evenProj v) + incOdd (oddProj v) := by
  ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj]

lemma v4_eq_zero_iff (v : V4) : v = 0 ↔ evenProj v = 0 ∧ oddProj v = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨he, ho⟩
    rw [v4_decomp v, he, ho]
    simp

lemma range_incEven_inf_incOdd :
    LinearMap.range incEven ⊓ LinearMap.range incOdd = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨u, hu⟩ := hv.1
  obtain ⟨w, hw⟩ := hv.2
  have he : evenProj v = 0 := by rw [← hw, evenProj_incOdd]
  have ho : oddProj v = 0 := by rw [← hu, oddProj_incEven]
  exact (v4_eq_zero_iff v).mpr ⟨he, ho⟩

lemma range_incEven_sup_incOdd :
    LinearMap.range incEven ⊔ LinearMap.range incOdd = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [v4_decomp v]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self incEven _) (LinearMap.mem_range_self incOdd _)

lemma zmod2_cases (c : F2) : c = 0 ∨ c = 1 := by
  rcases c with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

lemma zmod2_ne_zero_iff (c : F2) : c ≠ 0 ↔ c = 1 := by
  rcases zmod2_cases c with rfl | rfl <;> simp

lemma v2_add_self (u : V2) : u + u = 0 := by
  ext b; simp [CharTwo.add_self_eq_zero]

lemma v4_add_self (v : V4) : v + v = 0 := by
  ext b; simp [CharTwo.add_self_eq_zero]

lemma col2_mod3 (r : ℕ) : col2 (r % 3) = col2 r := by
  simp [col2]

lemma col2_ne_zero (r : ℕ) : col2 r ≠ 0 := by
  rw [← col2_mod3]
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (r % 3) <;> decide

lemma col2_consec_li (r : ℕ) : LinearIndependent F2 ![col2 r, col2 (r + 1)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 : g 0 • col2 (r % 3) + g 1 • col2 ((r + 1) % 3) = 0 := by
    simpa [Fin.sum_univ_two, col2_mod3] using hg
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  have hr : (r + 1) % 3 = (r % 3 + 1) % 3 := by omega
  rw [hr] at h0
  rcases zmod2_cases (g 0) with h00 | h01 <;> rcases zmod2_cases (g 1) with h10 | h11
  · fin_cases i <;> assumption
  · rw [h00, h11, zero_smul, one_smul, zero_add] at h0
    exact (col2_ne_zero _ h0).elim
  · rw [h01, h10, one_smul, zero_smul, add_zero] at h0
    exact (col2_ne_zero _ h0).elim
  · rw [h01, h11, one_smul, one_smul] at h0
    exfalso
    interval_cases (r % 3) <;> revert h0 <;> decide

lemma span_col2_consec (r : ℕ) : Submodule.span F2 {col2 r, col2 (r + 1)} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hset : ({col2 r, col2 (r + 1)} : Set V2) = Set.range ![col2 r, col2 (r + 1)] := by
    ext x; simp [Fin.exists_fin_two, or_comm]
  rw [hset, finrank_span_eq_card (col2_consec_li r)]
  simp [Module.finrank_fin_fun]

lemma col2_eq_iff (r₁ r₂ : ℕ) : col2 r₁ = col2 r₂ ↔ r₁ % 3 = r₂ % 3 := by
  rw [← col2_mod3 r₁, ← col2_mod3 r₂]
  have h1 : r₁ % 3 < 3 := Nat.mod_lt _ (by decide)
  have h2 : r₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (r₁ % 3) <;> interval_cases (r₂ % 3) <;> decide

lemma exists_col2_eq (u : V2) (hu : u ≠ 0) : ∃ c : ℕ, c < 3 ∧ col2 c = u := by
  have h0 : u 0 = 0 ∨ u 0 = 1 := zmod2_cases (u 0)
  have h1 : u 1 = 0 ∨ u 1 = 1 := zmod2_cases (u 1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exfalso; apply hu; ext b; fin_cases b <;> assumption
  · refine ⟨1, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]
  · refine ⟨0, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]
  · refine ⟨2, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]

lemma hPat_mod6 (k : ℕ) : hPat (k % 6) = hPat k := by
  ext b
  have h1 : k % 6 % 2 = k % 2 := by omega
  have h2 : k % 6 / 2 % 3 = k / 2 % 3 := by omega
  simp [hPat, h1, h2]

lemma hVec_idx {t : ℕ} (ht : 0 < t) (k : ℕ) : hVec (idx ht k) = hPat k := by
  ext b
  simp [hVec, hPat, idx_mod2 ht k, idx_div2_mod3 ht k]

lemma hVec_eq_incEven {t : ℕ} {i : Fin (6 * t)} (he : i.val % 2 = 0) :
    hVec i = incEven (col2 (i.val / 2)) := by
  ext b
  have hq : i.val / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hVec, incEven, col2, he] <;> interval_cases (i.val / 2 % 3) <;> decide

lemma hVec_eq_incOdd {t : ℕ} {i : Fin (6 * t)} (ho : i.val % 2 = 1) :
    hVec i = incOdd (col2 (i.val / 2)) := by
  ext b
  have hq : i.val / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hVec, incOdd, col2, ho] <;> interval_cases (i.val / 2 % 3) <;> decide

lemma hPat_eq_incEven {k : ℕ} (he : k % 2 = 0) :
    hPat k = incEven (col2 (k / 2)) := by
  ext b
  have hq : k / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hPat, incEven, col2, he] <;> interval_cases (k / 2 % 3) <;> decide

lemma hPat_eq_incOdd {k : ℕ} (ho : k % 2 = 1) :
    hPat k = incOdd (col2 (k / 2)) := by
  ext b
  have hq : k / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hPat, incOdd, col2, ho] <;> interval_cases (k / 2 % 3) <;> decide

lemma hVec_ne_zero {t : ℕ} (i : Fin (6 * t)) : hVec i ≠ 0 := by
  by_cases h : i.val % 2 = 0
  · rw [hVec_eq_incEven h]
    intro hz
    exact col2_ne_zero _ (by simpa [evenProj_incEven] using congrArg evenProj hz)
  · have ho : i.val % 2 = 1 := by omega
    rw [hVec_eq_incOdd ho]
    intro hz
    exact col2_ne_zero _ (by simpa [oddProj_incOdd] using congrArg oddProj hz)

def arcSum (s m : ℕ) : V4 := ∑ j ∈ Finset.range m, hPat (s + j)

lemma sum_hPat_six (s : ℕ) : ∑ j ∈ Finset.range 6, hPat (s + j) = 0 := by
  have hstep : ∀ j, hPat (s + j) = hPat (s % 6 + j) := fun j => by
    rw [← hPat_mod6 (s + j), ← hPat_mod6 (s % 6 + j)]
    congr 1; omega
  have heq : ∑ j ∈ Finset.range 6, hPat (s + j) = ∑ j ∈ Finset.range 6, hPat (s % 6 + j) :=
    Finset.sum_congr rfl fun j _ => hstep j
  rw [heq]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (s % 6) <;> decide

lemma arcSum_add_six (s m : ℕ) : arcSum s (m + 6) = arcSum s m := by
  unfold arcSum
  rw [Finset.sum_range_add, show ∑ x ∈ Finset.range 6, hPat (s + (m + x)) =
      ∑ x ∈ Finset.range 6, hPat ((s + m) + x) from
    Finset.sum_congr rfl fun x _ => by rw [add_assoc], sum_hPat_six, add_zero]

lemma arcSum_mod6 (s m : ℕ) : arcSum s m = arcSum (s % 6) (m % 6) := by
  have hm : ∀ q, arcSum s (m % 6 + 6 * q) = arcSum s (m % 6) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show m % 6 + 6 * (q + 1) = (m % 6 + 6 * q) + 6 by ring, arcSum_add_six, ih]
  have h1 : arcSum s m = arcSum s (m % 6) := by
    conv_lhs => rw [← Nat.mod_add_div m 6, add_comm]
    rw [add_comm]
    exact hm (m / 6)
  rw [h1]
  unfold arcSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← hPat_mod6 (s + j), ← hPat_mod6 (s % 6 + j)]
  congr 1; omega

lemma hSum_arc {t : ℕ} (ht : 0 < t) (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t) :
    hSum (arc ht s m) = arcSum s.val m := by
  unfold hSum arc arcSum
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl fun k _ => hVec_idx ht (s.val + k)
  · intro j₁ hj₁ j₂ hj₂ heq
    exact idx_inj_range ht s hm (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂) heq

lemma arcSum_eq_zero_iff (s m : ℕ) : arcSum s m = 0 ↔ m % 6 = 0 := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_oddProj_zero_iff (s m : ℕ) :
    oddProj (arcSum s m) = 0 ↔ m % 6 = 0 ∨ (m % 6 = 1 ∧ s % 2 = 0) ∨ (m % 6 = 5 ∧ s % 2 = 1) := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  have h2 : s % 2 = s % 6 % 2 := by omega
  rw [h2]
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_evenProj_zero_iff (s m : ℕ) :
    evenProj (arcSum s m) = 0 ↔ m % 6 = 0 ∨ (m % 6 = 1 ∧ s % 2 = 1) ∨ (m % 6 = 5 ∧ s % 2 = 0) := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  have h2 : s % 2 = s % 6 % 2 := by omega
  rw [h2]
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_two (s : ℕ) :
    arcSum s 2 = hPat s + hPat (s + 1) := by
  simp [arcSum, Finset.sum_range_succ]

lemma arcSum_three (s : ℕ) :
    arcSum s 3 = hPat s + hPat (s + 1) + hPat (s + 2) := by
  simp [arcSum, Finset.sum_range_succ]

lemma card_lane_col_eq {t : ℕ} (ht : 0 < t) (p : ℕ) (hp : p < 2) (u : V2) (hu : u ≠ 0) :
    (Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = p ∧ col2 (i.val / 2) = u)).card = t := by
  obtain ⟨c, hc, rfl⟩ := exists_col2_eq u hu
  let f : Fin t → Fin (6 * t) := fun q => ⟨6 * q.val + 2 * c + p, by have := q.isLt; omega⟩
  have hset : Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = p ∧ col2 (i.val / 2) = col2 c) =
      Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, col2_eq_iff]
    constructor
    · rintro ⟨hp', hc'⟩
      refine ⟨⟨i.val / 6, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      have : c % 3 = c := Nat.mod_eq_of_lt hc
      omega
    · rintro ⟨q, rfl⟩
      dsimp [f]
      have : c % 3 = c := Nat.mod_eq_of_lt hc
      omega
  rw [hset, Finset.card_image_of_injective]
  · simp
  · intro q₁ q₂ h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    exact Fin.ext (by omega)

lemma card_six_window_hits {t : ℕ} (ht : 0 < t) (s : Fin (6 * t))
    (we wo : V2) (hwe : we ≠ 0) (hwo : wo ≠ 0) :
    ((arc ht s 6).filter (fun i : Fin (6 * t) =>
      (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo))).card = 2 := by
  obtain ⟨ce, hce, rfl⟩ := exists_col2_eq we hwe
  obtain ⟨co, hco, rfl⟩ := exists_col2_eq wo hwo
  let re := (2 * ce + 6 - s.val % 6) % 6
  let ro := (2 * co + 1 + 6 - s.val % 6) % 6
  have hre : re < 6 := Nat.mod_lt _ (by decide)
  have hro : ro < 6 := Nat.mod_lt _ (by decide)
  have hne : re ≠ ro := by omega
  let xe := idx ht (s.val + re)
  let xo := idx ht (s.val + ro)
  have hxne : xe ≠ xo := fun h => hne (idx_inj_range ht s (by omega) hre hro h)
  have hsub : (arc ht s 6).filter (fun i : Fin (6 * t) =>
      (i.val % 2 = 0 ∧ col2 (i.val / 2) = col2 ce) ∨
      (i.val % 2 = 1 ∧ col2 (i.val / 2) = col2 co)) = {xe, xo} := by
    ext x
    simp only [Finset.mem_filter, mem_arc_iff, Finset.mem_insert, Finset.mem_singleton, col2_eq_iff]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hcond⟩
      simp only [idx_mod2, idx_div2_mod3] at hcond
      rcases hcond with ⟨hp, hc⟩ | ⟨hp, hc⟩
      · left; congr 1
        have : ce % 3 = ce := Nat.mod_eq_of_lt hce
        have : k = re := by dsimp [re]; omega
        rw [this]
      · right; congr 1
        have : co % 3 = co := Nat.mod_eq_of_lt hco
        have : k = ro := by dsimp [ro]; omega
        rw [this]
    · rintro (rfl | rfl)
      · refine ⟨⟨re, hre, rfl⟩, Or.inl ?_⟩
        rw [idx_mod2, idx_div2_mod3]
        have : ce % 3 = ce := Nat.mod_eq_of_lt hce
        dsimp [re]; omega
      · refine ⟨⟨ro, hro, rfl⟩, Or.inr ?_⟩
        rw [idx_mod2, idx_div2_mod3]
        have : co % 3 = co := Nat.mod_eq_of_lt hco
        dsimp [ro]; omega
  rw [hsub, Finset.card_pair hxne]

end Columns

section RunKernel

variable {t : ℕ} (ht : 0 < t)

abbrev W (t : ℕ) := Fin (6 * t) → F2

def goodU (U : Submodule F2 (W t)) : Prop :=
  (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hVec i b * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nxt ht i) = x (nxt ht i) * y i)

noncomputable def suppU (U : Submodule F2 (W t)) : Finset (Fin (6 * t)) :=
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

def sitesOf (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  (S.filter (fun i => i.val % 2 = p)).card

noncomputable def hSpace (S : Finset (Fin (6 * t))) : Submodule F2 V4 :=
  Submodule.span F2 (↑((pcs (nxt ht) S).image hSum) : Set V4)

noncomputable def rk (S : Finset (Fin (6 * t))) : ℕ :=
  Module.finrank F2 (hSpace ht S)

lemma mem_hSpace {S : Finset (Fin (6 * t))} {C : Finset (Fin (6 * t))}
    (hC : C ∈ pcs (nxt ht) S) : hSum C ∈ hSpace ht S :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem hSum hC))

lemma zero_of_not_mem_supp {U : Submodule F2 (W t)} {x : W t} (hx : x ∈ U)
    {i : Fin (6 * t)} (hi : i ∉ suppU U) : x i = 0 := by
  by_contra hne
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩)

lemma const_on_adj {U : Submodule F2 (W t)} (hg : goodU ht U)
    {i : Fin (6 * t)} (hi : i ∈ suppU U) (hni : nxt ht i ∈ suppU U)
    {x : W t} (hx : x ∈ U) : x i = x (nxt ht i) := by
  obtain ⟨u, hu, hui⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨v, hv, hvni⟩ := (Finset.mem_filter.mp hni).2
  have hui1 : u i = 1 := (zmod2_ne_zero_iff _).mp hui
  have hvni1 : v (nxt ht i) = 1 := (zmod2_ne_zero_iff _).mp hvni
  have hw : ∃ w ∈ U, w i = 1 ∧ w (nxt ht i) = 1 := by
    rcases zmod2_cases (u (nxt ht i)) with hu0 | hu1
    · rcases zmod2_cases (v i) with hv0 | hv1
      · refine ⟨u + v, U.add_mem hu hv, ?_, ?_⟩
        · simp [hui1, hv0]
        · simp [hu0, hvni1]
      · exact ⟨v, hv, hv1, hvni1⟩
    · exact ⟨u, hu, hui1, hu1⟩
  obtain ⟨w, hwU, hwi, hwni⟩ := hw
  have hmul := hg.2 x hx w hwU i
  simpa [hwi, hwni] using hmul

lemma const_on_edge {U : Submodule F2 (W t)} (hg : goodU ht U)
    {i j : Fin (6 * t)} (he : edge (nxt ht) (suppU U) i j)
    {x : W t} (hx : x ∈ U) : x i = x j := by
  rcases he.2.2 with rfl | rfl
  · exact const_on_adj ht hg he.1 he.2.1 hx
  · exact (const_on_adj ht hg he.2.1 he.1 hx).symm

lemma const_on_comp {U : Submodule F2 (W t)} (hg : goodU ht U)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U))
    {i j : Fin (6 * t)} (hi : i ∈ C) (hj : j ∈ C)
    {x : W t} (hx : x ∈ U) : x i = x j := by
  obtain ⟨_, hci⟩ := center (nxt ht) (suppU U) hC hi
  rw [← hci] at hj
  obtain ⟨hjS, hpath⟩ := Finset.mem_filter.mp hj
  clear hj hjS
  induction hpath with
  | refl => rfl
  | tail _ he ih => exact ih.trans (const_on_edge ht hg he hx)

lemma finrank_le_one_of_supp_univ {U : Submodule F2 (W t)} (hg : goodU ht U)
    (huniv : suppU U = Finset.univ) : Module.finrank F2 U ≤ 1 := by
  let ones : W t := fun _ => 1
  have hle : U ≤ Submodule.span F2 {ones} := by
    intro x hx
    have hconst : ∀ i : Fin (6 * t), x i = x ⟨0, by omega⟩ := by
      intro i
      have go (k : ℕ) : x (idx ht k) = x ⟨0, by omega⟩ := by
        induction k with
        | zero =>
          have : idx ht 0 = ⟨0, by omega⟩ := by apply Fin.ext; simp [idx]
          rw [this]
        | succ k ih =>
          have h1 : idx ht k ∈ suppU U := huniv.symm ▸ Finset.mem_univ _
          have h2 : nxt ht (idx ht k) ∈ suppU U := huniv.symm ▸ Finset.mem_univ _
          have hc := const_on_adj ht hg h1 h2 hx
          rw [nxt_idx] at hc
          exact hc.symm.trans ih
      simpa [idx_self] using go i.val
    rw [Submodule.mem_span_singleton]
    refine ⟨x ⟨0, by omega⟩, ?_⟩
    ext i
    simp [ones, hconst i]
  have hm := Submodule.finrank_mono hle
  have h1 : ones ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [ones] at this
  rwa [finrank_span_singleton h1] at hm

lemma finrank_add_rk_le_runs {U : Submodule F2 (W t)} (hg : goodU ht U) :
    Module.finrank F2 U + rk ht (suppU U) ≤ (pcs (nxt ht) (suppU U)).card := by
  set S := suppU U
  set P := pcs (nxt ht) S
  let rep : ↥P → Fin (6 * t) := fun C => Classical.choose (populated (nxt ht) S C.2)
  have hrep : ∀ C : ↥P, rep C ∈ C.1 := fun C => Classical.choose_spec (populated (nxt ht) S C.2)
  let ρ : U →ₗ[F2] (↥P → F2) :=
    { toFun := fun x C => x.1 (rep C)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · let C : ↥P := ⟨cc (nxt ht) S i, Finset.mem_image_of_mem _ hi⟩
      have hiC : i ∈ C.1 := selfMem (nxt ht) S hi
      have h1 := const_on_comp ht hg C.2 hiC (hrep C) x.2
      have h2 := const_on_comp ht hg C.2 hiC (hrep C) y.2
      have h3 := congrFun hxy C
      exact h1.trans (h3.trans h2.symm)
    · rw [zero_of_not_mem_supp x.2 hi, zero_of_not_mem_supp y.2 hi]
  let Φ : (↥P → F2) →ₗ[F2] V4 :=
    { toFun := fun c => ∑ C : ↥P, c C • hSum C.1
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hker : LinearMap.range ρ ≤ LinearMap.ker Φ := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    ext b
    dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, ρ, Pi.zero_apply]
    rw [Finset.sum_apply]
    have hsum1 : (∑ C : ↥P, (x.1 (rep C) • hSum C.1) b) =
        ∑ C ∈ P, ∑ i ∈ id C, hVec i b * x.1 i := by
      rw [← Finset.sum_coe_sort P (fun C => ∑ i ∈ id C, hVec i b * x.1 i)]
      apply Finset.sum_congr rfl
      intro C _
      simp only [id_eq, Pi.smul_apply, smul_eq_mul, hSum, Finset.sum_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [const_on_comp ht hg C.2 hi (hrep C) x.2, mul_comm]
    rw [hsum1, ← Finset.sum_biUnion (pcs_pairwiseDisjoint (nxt ht) S), pcs_biUnion_eq]
    have hsum2 : (∑ i ∈ S, hVec i b * x.1 i) = ∑ i : Fin (6 * t), hVec i b * x.1 i := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      rw [zero_of_not_mem_supp x.2 hi, mul_zero]
    rw [hsum2]
    exact hg.1 x.1 x.2 b
  have hrange : LinearMap.range Φ = hSpace ht S := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      apply Submodule.sum_mem
      intro C _
      exact Submodule.smul_mem _ _ (mem_hSpace ht C.2)
    · apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      refine ⟨Pi.single ⟨C, hC⟩ 1, ?_⟩
      dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single (⟨C, hC⟩ : ↥P)]
      · simp
      · intro D _ hne
        simp [Pi.single_eq_of_ne hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
  have h1 : Module.finrank F2 U = Module.finrank F2 (LinearMap.range ρ) :=
    (LinearMap.finrank_range_of_inj hρ_inj).symm
  have h2 : Module.finrank F2 (LinearMap.range ρ) ≤ Module.finrank F2 (LinearMap.ker Φ) :=
    Submodule.finrank_mono hker
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, Module.finrank_pi, Fintype.card_coe] at h3
  change rk ht S + Module.finrank F2 (LinearMap.ker Φ) = P.card at h3
  omega

end RunKernel

section Defect
open Finset

theorem few_equal_edges {t : ℕ} (ht : 0 < t) {U : Submodule F2 (W t)}
    (hg : goodU ht U) (hbig : 1 < Module.finrank F2 U) :
    (univ.filter (fun i : Fin (6*t) => i ∈ suppU U ↔ nxt ht i ∈ suppU U)).card +
      2 * Module.finrank F2 U ≤ 6*t := by
  classical
  set S := suppU U
  let P := pcs (nxt ht) S
  have hS : S ≠ univ := fun h => (Nat.not_le_of_gt hbig) (finrank_le_one_of_supp_univ ht hg h)
  have starts (C : ↥P) := comp_arc ht hS C.property
  choose first hfC hp hArc hlen hlt hend using starts
  let last (C : ↥P) := idx ht ((first C).val + (C.val.card-1))
  have hlC (C : ↥P) : last C ∈ C.val := by
    rw [hArc C]
    apply (mem_arc_iff ht _ _ _).mpr
    exact ⟨C.val.card-1,by have := hlen C; omega,rfl⟩
  have hlout (C : ↥P) : nxt ht (last C) ∉ S := by
    have hk : (first C).val + (C.val.card - 1) + 1 = (first C).val + C.val.card := by
      have := hlen C
      omega
    simpa only [last, nxt_idx, hk] using hend C
  let entering := univ.filter (fun i : Fin (6*t) => i ∉ S ∧ nxt ht i ∈ S)
  let leaving := univ.filter (fun i : Fin (6*t) => i ∈ S ∧ nxt ht i ∉ S)
  let equal := univ.filter (fun i : Fin (6*t) => i ∈ S ↔ nxt ht i ∈ S)
  have he (C : ↥P) : prv ht (first C) ∈ entering := by
    refine mem_filter.mpr ⟨mem_univ _,hp C,?_⟩
    rw [nxt_prv]
    exact (center (nxt ht) S C.property (hfC C)).1
  have hl (C : ↥P) : last C ∈ leaving :=
    mem_filter.mpr ⟨mem_univ _, (center (nxt ht) S C.property (hlC C)).1, hlout C⟩
  have he' := Fintype.card_le_of_injective
    (fun C : ↥P => (⟨prv ht (first C), he C⟩ : ↥entering)) (by
      intro C D hh
      have hh' := congrArg (fun i : ↥entering => nxt ht i.val) hh
      change nxt ht (prv ht (first C)) = nxt ht (prv ht (first D)) at hh'
      simp only [nxt_prv] at hh'
      exact Subtype.ext (joined (nxt ht) S C.property D.property (hfC C) (hfC D) (Or.inl hh')))
  have hl' := Fintype.card_le_of_injective
    (fun C : ↥P => (⟨last C, hl C⟩ : ↥leaving)) (by
      intro C D hh
      exact Subtype.ext (joined (nxt ht) S C.property D.property (hlC C) (hlC D)
        (Or.inl (congrArg Subtype.val hh))))
  simp only [Fintype.card_coe] at he' hl'
  have hed : Disjoint entering leaving := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_filter.mp hx).2.1 (mem_filter.mp hy).2.1
  have hd : Disjoint equal (entering ∪ leaving) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hiff := (mem_filter.mp hx).2
    rcases mem_union.mp hy with he | hl
    · exact (mem_filter.mp he).2.1 (hiff.mpr (mem_filter.mp he).2.2)
    · exact (mem_filter.mp hl).2.2 (hiff.mp (mem_filter.mp hl).2.1)
  have hc := card_le_univ (equal ∪ (entering ∪ leaving))
  rw [card_union_of_disjoint hd, card_union_of_disjoint hed, Fintype.card_fin] at hc
  have hr := finrank_add_rk_le_runs ht hg
  change Module.finrank F2 U + _ ≤ P.card at hr
  change equal.card + _ ≤ _
  omega

end Defect
end PEqualNP.Outside.L_lib_912_aux
