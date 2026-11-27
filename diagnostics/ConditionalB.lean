import PEqualNP.Defs
import Mathlib
namespace PEqualNP.Outside.L_lib_912_aux
namespace Old

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

lemma active_run {U : Submodule F2 (W t)} (hg : goodU ht U)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U)) :
    hSum C ∈ Submodule.span F2 (↑(((pcs (nxt ht) (suppU U)).erase C).image hSum) : Set V4) := by
  set S := suppU U
  set P := pcs (nxt ht) S
  obtain ⟨i0, hi0C⟩ := populated (nxt ht) S hC
  have hi0S : i0 ∈ S := (center (nxt ht) S hC hi0C).1
  obtain ⟨x, hxU, hxi0⟩ := (Finset.mem_filter.mp hi0S).2
  have hxi01 : x i0 = 1 := (zmod2_ne_zero_iff _).mp hxi0
  let rep : Finset (Fin (6 * t)) → Fin (6 * t) := fun D =>
    if hD : D ∈ P then Classical.choose (populated (nxt ht) S hD) else i0
  have hrep : ∀ D, ∀ hD : D ∈ P, rep D ∈ D := fun D hD => by
    simp only [rep, dif_pos hD]
    exact Classical.choose_spec (populated (nxt ht) S hD)
  have htot : ∑ D ∈ P, x (rep D) • hSum D = 0 := by
    ext b
    rw [Finset.sum_apply, Pi.zero_apply]
    have h1 : (∑ D ∈ P, (x (rep D) • hSum D) b) = ∑ D ∈ P, ∑ i ∈ id D, hVec i b * x i := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [id_eq, Pi.smul_apply, smul_eq_mul, hSum, Finset.sum_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [const_on_comp ht hg hD hi (hrep D hD) hxU, mul_comm]
    rw [h1, ← Finset.sum_biUnion (pcs_pairwiseDisjoint (nxt ht) S), pcs_biUnion_eq]
    have h2 : (∑ i ∈ S, hVec i b * x i) = ∑ i : Fin (6 * t), hVec i b * x i := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      rw [zero_of_not_mem_supp hxU hi, mul_zero]
    rw [h2]
    exact hg.1 x hxU b
  have hsplit := Finset.add_sum_erase P (fun D => x (rep D) • hSum D) hC
  rw [htot] at hsplit
  have hxC : x (rep C) = 1 :=
    (const_on_comp ht hg hC (hrep C hC) hi0C hxU).trans hxi01
  rw [hxC, one_smul] at hsplit
  have heq : hSum C = ∑ D ∈ P.erase C, x (rep D) • hSum D := by
    have hadd := congrArg (fun v => v + hSum C) hsplit
    simp only [zero_add] at hadd
    rw [add_comm (hSum C), add_assoc, v4_add_self, add_zero] at hadd
    exact hadd.symm
  rw [heq]
  apply Submodule.sum_mem
  intro D hD
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem hSum hD)))

lemma active_proj {U : Submodule F2 (W t)} (hg : goodU ht U)
    (proj : V4 →ₗ[F2] V2) {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U))
    (hne : proj (hSum C) ≠ 0) :
    ∃ D ∈ pcs (nxt ht) (suppU U), D ≠ C ∧ proj (hSum D) ≠ 0 := by
  by_contra! hall
  have hle : Submodule.span F2 (↑(((pcs (nxt ht) (suppU U)).erase C).image hSum) : Set V4) ≤
      LinearMap.ker proj := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hall D (Finset.mem_of_mem_erase hD) (Finset.ne_of_mem_erase hD)
  exact hne (hle (active_run ht hg hC))

end RunKernel

section UpperBounds

variable {t : ℕ} (ht : 0 < t)

lemma submodule_le_one_eq_zero_or_w {M : Type*} [AddCommGroup M] [Module F2 M]
    [FiniteDimensional F2 M] {V : Submodule F2 M} (hV : Module.finrank F2 V ≤ 1) :
    ∃ w : M, ∀ v ∈ V, v = 0 ∨ v = w := by
  by_cases h0 : Module.finrank F2 V = 0
  · refine ⟨0, fun v hv => Or.inl ?_⟩
    exact congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0) ⟨v, hv⟩)
  · have h1 : Module.finrank F2 V = 1 := by omega
    have hne : V ≠ ⊥ := by
      intro eb
      rw [eb, finrank_bot] at h1
      omega
    obtain ⟨w, hwV, hw0⟩ : ∃ w ∈ V, w ≠ 0 := by
      by_contra! hall
      exact hne ((Submodule.eq_bot_iff V).mpr hall)
    have hle : Submodule.span F2 {w} ≤ V := (Submodule.span_singleton_le_iff_mem w V).mpr hwV
    have heq : Submodule.span F2 {w} = V :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hw0, h1])
    refine ⟨w, fun v hv => ?_⟩
    rw [← heq, Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rcases zmod2_cases c with rfl | rfl
    · left; simp
    · right; simp

lemma rk_zero_runs {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (hrk : rk ht S = 0) : 7 * (pcs (nxt ht) S).card ≤ 6 * t := by
  have hseven : ∀ C ∈ pcs (nxt ht) S, 7 ≤ C.card + 1 := by
    intro C hC
    obtain ⟨s, _, _, harc, hpos, hlt, _⟩ := comp_arc ht hS hC
    have hz : hSum C = 0 := congrArg Subtype.val
      ((finrank_zero_iff_forall_zero.mp hrk) ⟨hSum C, mem_hSpace ht hC⟩)
    rw [harc, hSum_arc ht s (by omega), arcSum_eq_zero_iff] at hz
    omega
  have hsum := Finset.sum_le_sum hseven
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hle := sum_halo_le ht hS
  omega

lemma rk_le_one_runs {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (hrk : rk ht S ≤ 1) : (pcs (nxt ht) S).card < 2 * t := by
  obtain ⟨w, hw⟩ := submodule_le_one_eq_zero_or_w hrk
  set P := pcs (nxt ht) S
  by_cases hwe : evenProj w = 0
  · by_cases hwo : oddProj w = 0
    · have hw0 : w = 0 := (v4_eq_zero_iff w).mpr ⟨hwe, hwo⟩
      have hrk0 : rk ht S = 0 := by
        rw [rk, finrank_zero_iff_forall_zero]
        intro ⟨v, hv⟩
        apply Subtype.ext
        rcases hw v hv with h | h
        · exact h
        · exact h.trans hw0
      have h7 : 7 * P.card ≤ 6 * t := rk_zero_runs ht hS hrk0
      omega
    · let P1 := P.filter (fun C => C.card = 1)
      let P2 := P.filter (fun C => 2 ≤ C.card)
      have hdis : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P1 ∪ P2 = P := by
        ext C; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
          by_cases hc1 : C.card = 1
          · exact Or.inl ⟨hC, hc1⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P1.card + P2.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP1 : P1.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = oddProj w)
        have hT : T.card = t := card_lane_col_eq ht 1 (by decide) (oddProj w) hwo
        have hsub : P1.biUnion id ⊆ T := by
          intro i hi
          obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
          obtain ⟨hCP, hcard1⟩ := Finset.mem_filter.mp hC1
          have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hcard1.le hj hiC⟩
          have hsumW : hVec i = w := by
            have hm := mem_hSpace ht hCP
            rw [hCeq, hSum, Finset.sum_singleton] at hm
            rcases hw _ hm with h0 | h1
            · exact (hVec_ne_zero i h0).elim
            · exact h1
          have hpar : i.val % 2 = 1 := by
            by_contra hne
            have he : i.val % 2 = 0 := by omega
            have := congrArg oddProj hsumW
            rw [hVec_eq_incEven he, oddProj_incEven] at this
            exact hwo this.symm
          have hcol : col2 (i.val / 2) = oddProj w := by
            have := congrArg oddProj hsumW
            rwa [hVec_eq_incOdd hpar, oddProj_incOdd] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar, hcol⟩
        have hcard_bi : (P1.biUnion id).card = P1.card := by
          rw [Finset.card_biUnion]
          · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
              Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
            simpa using this
          · intro C hC D hD hne
            exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
              (Finset.mem_filter.mp hD).1 hne
        calc P1.card = (P1.biUnion id).card := hcard_bi.symm
          _ ≤ T.card := Finset.card_le_card hsub
          _ = t := hT
      have hP2 : ∀ C ∈ P2, 6 ≤ C.card + 1 := by
        intro C hC2
        obtain ⟨hCP, hge2⟩ := Finset.mem_filter.mp hC2
        obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
        have hev : evenProj (hSum C) = 0 := by
          rcases hw _ (mem_hSpace ht hCP) with h0 | h1
          · rw [h0, map_zero]
          · rw [h1, hwe]
        rw [harc, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev
        omega
      have hsum_le : 2 * P1.card + 6 * P2.card ≤ 6 * t := by
        have h1 : 2 * P1.card ≤ ∑ C ∈ P1, (C.card + 1) := by
          have : ∑ C ∈ P1, (C.card + 1) = ∑ _ ∈ P1, 2 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h2 : 6 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have := Finset.sum_le_sum hP2
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega
  · by_cases hwo : oddProj w = 0
    · let P1 := P.filter (fun C => C.card = 1)
      let P2 := P.filter (fun C => 2 ≤ C.card)
      have hdis : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P1 ∪ P2 = P := by
        ext C; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
          by_cases hc1 : C.card = 1
          · exact Or.inl ⟨hC, hc1⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P1.card + P2.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP1 : P1.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = evenProj w)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) (evenProj w) hwe
        have hsub : P1.biUnion id ⊆ T := by
          intro i hi
          obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
          obtain ⟨hCP, hcard1⟩ := Finset.mem_filter.mp hC1
          have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hcard1.le hj hiC⟩
          have hsumW : hVec i = w := by
            have hm := mem_hSpace ht hCP
            rw [hCeq, hSum, Finset.sum_singleton] at hm
            rcases hw _ hm with h0 | h1
            · exact (hVec_ne_zero i h0).elim
            · exact h1
          have hpar : i.val % 2 = 0 := by
            by_contra hne
            have ho : i.val % 2 = 1 := by omega
            have := congrArg evenProj hsumW
            rw [hVec_eq_incOdd ho, evenProj_incOdd] at this
            exact hwe this.symm
          have hcol : col2 (i.val / 2) = evenProj w := by
            have := congrArg evenProj hsumW
            rwa [hVec_eq_incEven hpar, evenProj_incEven] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar, hcol⟩
        have hcard_bi : (P1.biUnion id).card = P1.card := by
          rw [Finset.card_biUnion]
          · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
              Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
            simpa using this
          · intro C hC D hD hne
            exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
              (Finset.mem_filter.mp hD).1 hne
        calc P1.card = (P1.biUnion id).card := hcard_bi.symm
          _ ≤ T.card := Finset.card_le_card hsub
          _ = t := hT
      have hP2 : ∀ C ∈ P2, 6 ≤ C.card + 1 := by
        intro C hC2
        obtain ⟨hCP, hge2⟩ := Finset.mem_filter.mp hC2
        obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
        have hod : oddProj (hSum C) = 0 := by
          rcases hw _ (mem_hSpace ht hCP) with h0 | h1
          · rw [h0, map_zero]
          · rw [h1, hwo]
        rw [harc, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod
        omega
      have hsum_le : 2 * P1.card + 6 * P2.card ≤ 6 * t := by
        have h1 : 2 * P1.card ≤ ∑ C ∈ P1, (C.card + 1) := by
          have : ∑ C ∈ P1, (C.card + 1) = ∑ _ ∈ P1, 2 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h2 : 6 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have := Finset.sum_le_sum hP2
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega
    · have hno1 : ∀ C ∈ P, 2 ≤ C.card := by
        intro C hC
        have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
        by_contra hlt2
        have h1 : C.card = 1 := by omega
        obtain ⟨i, hiC⟩ := populated (nxt ht) S hC
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp h1.le hj hiC⟩
        have hsumW : hVec i = w := by
          have hm := mem_hSpace ht hC
          rw [hCeq, hSum, Finset.sum_singleton] at hm
          rcases hw _ hm with h0 | h1'
          · exact (hVec_ne_zero i h0).elim
          · exact h1'
        by_cases hp : i.val % 2 = 0
        · have := congrArg oddProj hsumW
          rw [hVec_eq_incEven hp, oddProj_incEven] at this
          exact hwo this.symm
        · have ho : i.val % 2 = 1 := by omega
          have := congrArg evenProj hsumW
          rw [hVec_eq_incOdd ho, evenProj_incOdd] at this
          exact hwe this.symm
      let P2 := P.filter (fun C => C.card = 2)
      let P3 := P.filter (fun C => 3 ≤ C.card)
      have hdis : Disjoint P2 P3 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P2 ∪ P3 = P := by
        ext C; simp only [P2, P3, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hge2 := hno1 C hC
          by_cases hc2 : C.card = 2
          · exact Or.inl ⟨hC, hc2⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P2.card + P3.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP2 : P2.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = evenProj w)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) (evenProj w) hwe
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hsumW : hSum C.1 = w := by
            rcases hw _ (mem_hSpace ht hCP) with h0 | h1
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_eq_zero_iff] at h0; omega
            · exact h1
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 0
          · have hsp1 : (s.val + 1) % 2 = 1 := by omega
            have hev : evenProj w = col2 (s.val / 2) := by
              rw [← hsumW, hs2, hPat_eq_incEven hsp, hPat_eq_incOdd hsp1, map_add,
                evenProj_incEven, evenProj_incOdd, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hev.symm⟩
          · have hsp1 : s.val % 2 = 1 := by omega
            have hsp2 : (s.val + 1) % 2 = 0 := by omega
            have hev : evenProj w = col2 ((s.val + 1) / 2) := by
              rw [← hsumW, hs2, hPat_eq_incOdd hsp1, hPat_eq_incEven hsp2, map_add,
                evenProj_incOdd, evenProj_incEven, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; exact hsp2
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hev.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
      have hsum_le : 3 * P2.card + 4 * P3.card ≤ 6 * t := by
        have h2 : 3 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have : ∑ C ∈ P2, (C.card + 1) = ∑ _ ∈ P2, 3 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h3 : 4 * P3.card ≤ ∑ C ∈ P3, (C.card + 1) := by
          have : ∑ _ ∈ P3, 4 ≤ ∑ C ∈ P3, (C.card + 1) :=
            Finset.sum_le_sum fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega

lemma runs_lt_a {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (h1 : 0 < sitesOf S 1) : (pcs (nxt ht) S).card < 3 * t := by
  set P := pcs (nxt ht) S
  have hle : 2 * P.card ≤ 6 * t := by
    have h2 : ∑ _ ∈ P, 2 ≤ ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_le_sum fun C hC => by have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  by_contra hge
  have heq : P.card = 3 * t := by omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h2 : 2 * P.card ≤ ∑ C ∈ P, (C.card + 1) := by
      have := Finset.sum_le_sum fun C (hC : C ∈ P) =>
        show 2 ≤ C.card + 1 by have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C.card = 1 := by
    intro C hC
    by_contra hne
    have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
    have hge3 : 3 ≤ C.card + 1 := by omega
    have hrest : 2 * (P.erase C).card ≤ ∑ D ∈ P.erase C, (D.card + 1) := by
      have := Finset.sum_le_sum fun D (hD : D ∈ P.erase C) =>
        show 2 ≤ D.card + 1 by
          have := Finset.card_pos.mpr (populated (nxt ht) S (Finset.mem_of_mem_erase hD)); omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have hsplit := Finset.add_sum_erase P (fun D => D.card + 1) hC
    have her : (P.erase C).card = P.card - 1 := Finset.card_erase_of_mem hC
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  have halt : ∀ x : Fin (6 * t), x ∈ S ↔ nxt ht x ∉ S := by
    intro x
    constructor
    · intro hx hnx
      let C := cc (nxt ht) S x
      have hCP : C ∈ P := Finset.mem_image_of_mem _ hx
      have hxC : x ∈ C := selfMem (nxt ht) S hx
      have hnxC : nxt ht x ∈ C := Finset.mem_filter.mpr ⟨hnx, .single ⟨hx, hnx, Or.inl rfl⟩⟩
      have hne : x ≠ nxt ht x := by
        intro eq
        have hp := nxt_parity ht x
        rw [← eq] at hp; omega
      have h2 : 2 ≤ C.card := by
        calc 2 = ({x, nxt ht x} : Finset _).card := (Finset.card_pair hne).symm
          _ ≤ C.card := Finset.card_le_card (Finset.insert_subset hxC (Finset.singleton_subset_iff.mpr hnxC))
      have := hall1 C hCP
      omega
    · intro hnx
      have hmem : nxt ht x ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
      rw [mem_biUnion_halo_iff, prv_nxt] at hmem
      rcases hmem with h | h
      · exact (hnx h).elim
      · exact h
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp h0
  obtain ⟨hi0S, hi0p⟩ := Finset.mem_filter.mp hi0
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp h1
  obtain ⟨hi1S, hi1p⟩ := Finset.mem_filter.mp hi1
  have go (k : ℕ) : idx ht (i0.val + k) ∈ S ↔ k % 2 = 0 := by
    induction k with
    | zero =>
      rw [add_zero, idx_self]
      simp [hi0S]
    | succ k ih =>
      rw [← add_assoc, ← nxt_idx]
      have hstep := halt (idx ht (i0.val + k))
      constructor
      · intro h'; have hnot := hstep.not.mpr (not_not.mpr h'); have := ih.not.mp hnot; omega
      · intro h'; exact hstep.not.mp (ih.not.mpr (by omega)) |> of_not_not
  let k := 6 * t - i0.val + i1.val
  have heqi1 : idx ht (i0.val + k) = i1 := by
    apply Fin.ext
    change (i0.val + (6 * t - i0.val + i1.val)) % (6 * t) = i1.val
    have : i0.val + (6 * t - i0.val + i1.val) = i1.val + 6 * t := by have := i0.isLt; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i1.isLt]
  have hk := (go k).mp (heqi1.symm ▸ hi1S)
  dsimp only [k] at hk
  have := i0.isLt
  omega

lemma range_incEven_le_of_consec {V : Submodule F2 V4} {r : ℕ}
    (h1 : incEven (col2 r) ∈ V) (h2 : incEven (col2 (r + 1)) ∈ V) :
    LinearMap.range incEven ≤ V := by
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Submodule.span F2 {col2 r, col2 (r + 1)} := by
    rw [span_col2_consec]; trivial
  have hle : Submodule.span F2 {col2 r, col2 (r + 1)} ≤ V.comap incEven := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  exact hle hu

lemma range_incOdd_le_of_consec {V : Submodule F2 V4} {r : ℕ}
    (h1 : incOdd (col2 r) ∈ V) (h2 : incOdd (col2 (r + 1)) ∈ V) :
    LinearMap.range incOdd ≤ V := by
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Submodule.span F2 {col2 r, col2 (r + 1)} := by
    rw [span_col2_consec]; trivial
  have hle : Submodule.span F2 {col2 r, col2 (r + 1)} ≤ V.comap incOdd := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  exact hle hu

lemma range_incOdd_le_of_even_and_consec {V : Submodule F2 V4}
    (hev : LinearMap.range incEven ≤ V) {v₁ v₂ : V4} (hv1 : v₁ ∈ V) (hv2 : v₂ ∈ V) {r : ℕ}
    (ho1 : oddProj v₁ = col2 r) (ho2 : oddProj v₂ = col2 (r + 1)) :
    LinearMap.range incOdd ≤ V := by
  have hsub : ∀ v : V4, incOdd (oddProj v) = v + incEven (evenProj v) := fun v => by
    ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj, CharTwo.add_self_eq_zero]
  have h1 : incOdd (col2 r) ∈ V := by
    rw [← ho1, hsub v₁]
    exact V.add_mem hv1 (hev (LinearMap.mem_range_self incEven _))
  have h2 : incOdd (col2 (r + 1)) ∈ V := by
    rw [← ho2, hsub v₂]
    exact V.add_mem hv2 (hev (LinearMap.mem_range_self incEven _))
  exact range_incOdd_le_of_consec h1 h2

lemma range_incEven_le_of_odd_and_consec {V : Submodule F2 V4}
    (hod : LinearMap.range incOdd ≤ V) {v₁ v₂ : V4} (hv1 : v₁ ∈ V) (hv2 : v₂ ∈ V) {r : ℕ}
    (he1 : evenProj v₁ = col2 r) (he2 : evenProj v₂ = col2 (r + 1)) :
    LinearMap.range incEven ≤ V := by
  have hsub : ∀ v : V4, incEven (evenProj v) = v + incOdd (oddProj v) := fun v => by
    ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj, CharTwo.add_self_eq_zero]
  have h1 : incEven (col2 r) ∈ V := by
    rw [← he1, hsub v₁]
    exact V.add_mem hv1 (hod (LinearMap.mem_range_self incOdd _))
  have h2 : incEven (col2 (r + 1)) ∈ V := by
    rw [← he2, hsub v₂]
    exact V.add_mem hv2 (hod (LinearMap.mem_range_self incOdd _))
  exact range_incEven_le_of_consec h1 h2

lemma finrank_eq_four_of_both_lanes {V : Submodule F2 V4}
    (hev : LinearMap.range incEven ≤ V) (hod : LinearMap.range incOdd ≤ V) :
    Module.finrank F2 V = 4 := by
  have htop : V = ⊤ := by
    rw [eq_top_iff, ← range_incEven_sup_incOdd]
    exact sup_le hev hod
  rw [htop, finrank_top, Module.finrank_fin_fun]

lemma solo_mem_hSpace {S : Finset (Fin (6 * t))} {x : Fin (6 * t)}
    (hx : x ∈ S) (hp : prv ht x ∉ S) (hn : nxt ht x ∉ S) :
    ({x} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) S ∧ hVec x ∈ hSpace ht S := by
  have hcc : cc (nxt ht) S x = {x} := by
    ext y
    simp only [cc, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyS, hpath⟩
      clear hyS
      induction hpath with
      | refl => rfl
      | @tail a b _ he ih =>
        rw [ih] at he
        rcases he.2.2 with hf | hb
        · exact (hn (hf ▸ he.2.1)).elim
        · have hb' : b = prv ht x := by rw [← hb, prv_nxt]
          exact (hp (hb' ▸ he.2.1)).elim
    · rintro rfl
      exact ⟨hx, .refl⟩
  have hmem : ({x} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) S := by
    rw [← hcc]
    exact Finset.mem_image_of_mem _ hx
  have hsp := mem_hSpace ht hmem
  rw [hSum, Finset.sum_singleton] at hsp
  exact ⟨hmem, hsp⟩

lemma span_of_consec_solos {S : Finset (Fin (6 * t))} (b k : ℕ) (hk : 2 ≤ k)
    (hmem : ∀ j < k, hVec (idx ht (b + 2 * j)) ∈ hSpace ht S) :
    (b % 2 = 0 → LinearMap.range incEven ≤ hSpace ht S) ∧
    (b % 2 = 1 → LinearMap.range incOdd ≤ hSpace ht S) := by
  have hm0 := hmem 0 (by omega)
  have hm1 := hmem 1 (by omega)
  constructor
  · intro he
    have hp0 : (idx ht (b + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
    have hp1 : (idx ht (b + 2 * 1)).val % 2 = 0 := by rw [idx_mod2]; omega
    rw [hVec_eq_incEven hp0, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm0
    rw [hVec_eq_incEven hp1, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm1
    have eq1 : (b + 2 * 1) / 2 = (b + 2 * 0) / 2 + 1 := by omega
    rw [eq1] at hm1
    exact range_incEven_le_of_consec hm0 hm1
  · intro ho
    have hp0 : (idx ht (b + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
    have hp1 : (idx ht (b + 2 * 1)).val % 2 = 1 := by rw [idx_mod2]; omega
    rw [hVec_eq_incOdd hp0, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm0
    rw [hVec_eq_incOdd hp1, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm1
    have eq1 : (b + 2 * 1) / 2 = (b + 2 * 0) / 2 + 1 := by omega
    rw [eq1] at hm1
    exact range_incOdd_le_of_consec hm0 hm1

lemma runs_sub1_two_gaps {U : Submodule F2 (W t)} (hg : goodU ht U)
    (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1)
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (hpar : a2.val % 2 = (a1.val + 1) % 2)
    (hsolo1 : ∀ k < k1, ({idx ht (a1.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a1.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hsolo2 : ∀ k < k2, ({idx ht (a2.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a2.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hdecomp : ∀ C ∈ pcs (nxt ht) (suppU U),
      (∃ k < k1, C = {idx ht (a1.val + 1 + 2 * k)}) ∨
      (∃ k < k2, C = {idx ht (a2.val + 1 + 2 * k)})) :
    LinearMap.range incEven ≤ hSpace ht (suppU U) ∧ LinearMap.range incOdd ≤ hSpace ht (suppU U) := by
  have hge2 : ∀ (x y : Fin (6 * t)) (kx ky : ℕ),
      y.val % 2 = (x.val + 1) % 2 →
      (∀ k < kx, ({idx ht (x.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U)) →
      (∀ C ∈ pcs (nxt ht) (suppU U),
        (∃ k < kx, C = {idx ht (x.val + 1 + 2 * k)}) ∨
        (∃ k < ky, C = {idx ht (y.val + 1 + 2 * k)})) →
      2 ≤ kx := by
    intro x y kx ky hxy hsx hdec
    by_contra hlt2
    have h01 : kx = 0 ∨ kx = 1 := by omega
    rcases h01 with rfl | rfl
    · by_cases hp : (x.val + 1) % 2 = 0
      · obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
        obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
        rcases hdec _ (Finset.mem_image_of_mem _ hiS) with ⟨k, hk, _⟩ | ⟨k, _, hceq⟩
        · omega
        · have hiin : i ∈ ({idx ht (y.val + 1 + 2 * k)} : Finset _) :=
            hceq ▸ selfMem (nxt ht) (suppU U) hiS
          rw [Finset.mem_singleton] at hiin
          have := congrArg (fun z : Fin (6 * t) => z.val % 2) hiin
          rw [idx_mod2] at this; omega
      · obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
        obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
        rcases hdec _ (Finset.mem_image_of_mem _ hiS) with ⟨k, hk, _⟩ | ⟨k, _, hceq⟩
        · omega
        · have hiin : i ∈ ({idx ht (y.val + 1 + 2 * k)} : Finset _) :=
            hceq ▸ selfMem (nxt ht) (suppU U) hiS
          rw [Finset.mem_singleton] at hiin
          have := congrArg (fun z : Fin (6 * t) => z.val % 2) hiin
          rw [idx_mod2] at this; omega
    · let x0 := idx ht (x.val + 1 + 2 * 0)
      have hx0P := hsx 0 (by omega)
      by_cases hp : (x.val + 1) % 2 = 0
      · have hp0 : x0.val % 2 = 0 := by dsimp [x0]; rw [idx_mod2]; omega
        have hne : evenProj (hSum {x0}) ≠ 0 := by
          rw [hSum, Finset.sum_singleton, hVec_eq_incEven hp0, evenProj_incEven]
          exact col2_ne_zero _
        obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hx0P hne
        rcases hdec D hDP with ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
        · have hk0 : k = 0 := by omega
          exact hDne (by subst hk0; rfl)
        · have hpD : (idx ht (y.val + 1 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
          exact hDev rfl
      · have hp0 : x0.val % 2 = 1 := by dsimp [x0]; rw [idx_mod2]; omega
        have hne : oddProj (hSum {x0}) ≠ 0 := by
          rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hp0, oddProj_incOdd]
          exact col2_ne_zero _
        obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hx0P hne
        rcases hdec D hDP with ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
        · have hk0 : k = 0 := by omega
          exact hDne (by subst hk0; rfl)
        · have hpD : (idx ht (y.val + 1 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
          exact hDod rfl
  have hk1 : 2 ≤ k1 := hge2 a1 a2 k1 k2 hpar (fun k hk => (hsolo1 k hk).1) hdecomp
  have hk2 : 2 ≤ k2 := hge2 a2 a1 k2 k1 (by omega) (fun k hk => (hsolo2 k hk).1)
    (fun C hC => (hdecomp C hC).symm)
  have hs1 := span_of_consec_solos ht (a1.val + 1) k1 hk1 (fun j hj => (hsolo1 j hj).2)
  have hs2 := span_of_consec_solos ht (a2.val + 1) k2 hk2 (fun j hj => (hsolo2 j hj).2)
  by_cases hp : (a1.val + 1) % 2 = 0
  · exact ⟨hs1.1 hp, hs2.2 (by omega)⟩
  · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩

lemma runs_sub1_run_gap {U : Submodule F2 (W t)} (ht2 : 2 ≤ t) (hg : goodU ht U)
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (ha1S : a1 ∈ suppU U) (harc1 : cc (nxt ht) (suppU U) a1 = arc ht a1 2)
    (hpar : a2.val % 2 = (a1.val + 3) % 2)
    (hk12 : k1 + k2 = 3 * t - 2)
    (ha1_from_a2 : k2 = 1 → idx ht (a2.val + 3) = a1)
    (hsolo1 : ∀ k < k1, ({idx ht (a1.val + 3 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a1.val + 3 + 2 * k)) ∈ hSpace ht (suppU U))
    (hsolo2 : ∀ k < k2, ({idx ht (a2.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a2.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hdecomp : ∀ C ∈ pcs (nxt ht) (suppU U),
      C = cc (nxt ht) (suppU U) a1 ∨
      (∃ k < k1, C = {idx ht (a1.val + 3 + 2 * k)}) ∨
      (∃ k < k2, C = {idx ht (a2.val + 1 + 2 * k)})) :
    LinearMap.range incEven ≤ hSpace ht (suppU U) ∧ LinearMap.range incOdd ≤ hSpace ht (suppU U) := by
  have hC1P : cc (nxt ht) (suppU U) a1 ∈ pcs (nxt ht) (suppU U) := Finset.mem_image_of_mem _ ha1S
  have hC1sum : hSum (cc (nxt ht) (suppU U) a1) = hPat a1.val + hPat (a1.val + 1) := by
    rw [harc1, hSum_arc ht a1 (by omega), arcSum_two]
  have hk1_pos : 1 ≤ k1 := by
    by_contra hk0
    by_cases hp : a1.val % 2 = 0
    · have hod : oddProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          oddProj_incEven, oddProj_incOdd, zero_add]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      rcases hdecomp D hDP with rfl | ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
      · exact hDne rfl
      · omega
      · have hpD : (idx ht (a2.val + 1 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
        exact hDod rfl
    · have hev : evenProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          evenProj_incOdd, evenProj_incEven, zero_add]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      rcases hdecomp D hDP with rfl | ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
      · exact hDne rfl
      · omega
      · have hpD : (idx ht (a2.val + 1 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
        exact hDev rfl
  have hk2_pos : 1 ≤ k2 := by
    by_contra hk0
    by_cases hp : a1.val % 2 = 0
    · have hev : evenProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          evenProj_incEven, evenProj_incOdd, add_zero]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      rcases hdecomp D hDP with rfl | ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
      · exact hDne rfl
      · have hpD : (idx ht (a1.val + 3 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
        exact hDev rfl
      · omega
    · have hod : oddProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          oddProj_incOdd, oddProj_incEven, add_zero]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      rcases hdecomp D hDP with rfl | ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
      · exact hDne rfl
      · have hpD : (idx ht (a1.val + 3 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
        exact hDod rfl
      · omega
  by_cases hk2_2 : 2 ≤ k2
  · have hs2 := span_of_consec_solos ht (a2.val + 1) k2 hk2_2 (fun j hj => (hsolo2 j hj).2)
    by_cases hk1_2 : 2 ≤ k1
    · have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 (fun j hj => (hsolo1 j hj).2)
      by_cases hp : a1.val % 2 = 0
      · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩
      · exact ⟨hs1.1 (by omega), hs2.2 (by omega)⟩
    · have hm_s := (hsolo1 0 (by omega)).2
      have hm_c := mem_hSpace ht hC1P
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht (suppU U) := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm_c hm_s (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht (suppU U) := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm_c hm_s (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
  · have hk2_eq : k2 = 1 := by omega
    have hk1_2 : 2 ≤ k1 := by omega
    have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 (fun j hj => (hsolo1 j hj).2)
    have hm_s := (hsolo2 0 (by omega)).2
    have hm_c := mem_hSpace ht hC1P
    have ha1_rel : idx ht (a2.val + 3) = a1 := ha1_from_a2 hk2_eq
    by_cases hp : a1.val % 2 = 0
    · have hod : LinearMap.range incOdd ≤ hSpace ht (suppU U) := hs1.2 (by omega)
      refine ⟨range_incEven_le_of_odd_and_consec hod hm_s hm_c (r := (a2.val + 1) / 2) ?_ ?_, hod⟩
      · have hp' : (idx ht (a2.val + 1 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
      · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          evenProj_incEven, evenProj_incOdd, add_zero, ← col2_mod3, ← ha1_rel, idx_div2_mod3, col2_mod3]
        congr 1; omega
    · have hev : LinearMap.range incEven ≤ hSpace ht (suppU U) := hs1.1 (by omega)
      refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm_s hm_c (r := (a2.val + 1) / 2) ?_ ?_⟩
      · have hp' : (idx ht (a2.val + 1 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
      · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          oddProj_incOdd, oddProj_incEven, add_zero, ← col2_mod3, ← ha1_rel, idx_div2_mod3, col2_mod3]
        congr 1; omega

lemma runs_sub1_two_runs_half {S : Finset (Fin (6 * t))}
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (ha1S : a1 ∈ S) (ha2S : a2 ∈ S)
    (harc1 : cc (nxt ht) S a1 = arc ht a1 2) (harc2 : cc (nxt ht) S a2 = arc ht a2 2)
    (hpar : a2.val % 2 = (a1.val + 3) % 2)
    (hk2_2 : 2 ≤ k2)
    (ha2_of_0 : k1 = 0 → idx ht (a1.val + 3) = a2)
    (hsolo1 : ∀ k < k1, hVec (idx ht (a1.val + 3 + 2 * k)) ∈ hSpace ht S)
    (hsolo2 : ∀ k < k2, hVec (idx ht (a2.val + 3 + 2 * k)) ∈ hSpace ht S) :
    LinearMap.range incEven ≤ hSpace ht S ∧ LinearMap.range incOdd ≤ hSpace ht S := by
  have hm1 : hSum (cc (nxt ht) S a1) ∈ hSpace ht S := mem_hSpace ht (Finset.mem_image_of_mem _ ha1S)
  have hm2 : hSum (cc (nxt ht) S a2) ∈ hSpace ht S := mem_hSpace ht (Finset.mem_image_of_mem _ ha2S)
  have hC1sum : hSum (cc (nxt ht) S a1) = hPat a1.val + hPat (a1.val + 1) := by
    rw [harc1, hSum_arc ht a1 (by omega), arcSum_two]
  have hC2sum : hSum (cc (nxt ht) S a2) = hPat a2.val + hPat (a2.val + 1) := by
    rw [harc2, hSum_arc ht a2 (by omega), arcSum_two]
  have hs2 := span_of_consec_solos ht (a2.val + 3) k2 hk2_2 hsolo2
  by_cases hk1_2 : 2 ≤ k1
  · have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 hsolo1
    by_cases hp : a1.val % 2 = 0
    · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩
    · exact ⟨hs1.1 (by omega), hs2.2 (by omega)⟩
  · by_cases hk1_1 : k1 = 1
    · have hm_s := hsolo1 0 (by omega)
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht S := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm1 hm_s (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht S := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm1 hm_s (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
    · have hk1_0 : k1 = 0 := by omega
      have ha2_rel : idx ht (a1.val + 3) = a2 := ha2_of_0 hk1_0
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht S := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm1 hm2 (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · rw [hC2sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            oddProj_incOdd, oddProj_incEven, add_zero, ← col2_mod3, ← ha2_rel, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht S := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm1 hm2 (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · rw [hC2sum, hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega), map_add,
            evenProj_incEven, evenProj_incOdd, add_zero, ← col2_mod3, ← ha2_rel, idx_div2_mod3, col2_mod3]
          congr 1; omega

lemma runs_eq_a_sub_one {U : Submodule F2 (W t)} (ht2 : 2 ≤ t) (hg : goodU ht U)
    (hS : suppU U ≠ Finset.univ) (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1)
    (hr : (pcs (nxt ht) (suppU U)).card = 3 * t - 1) : rk ht (suppU U) = 4 := by
  set S := suppU U
  set P := pcs (nxt ht) S
  let RunStarts := Finset.univ.filter (fun x : Fin (6 * t) => x ∈ S ∧ prv ht x ∉ S)
  let Gaps := Finset.univ.filter (fun x : Fin (6 * t) => x ∉ S ∧ prv ht x ∉ S)
  let Starts := Finset.univ.filter (fun x : Fin (6 * t) => prv ht x ∉ S)
  have hdisRG : Disjoint RunStarts Gaps :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.1 h1.1
  have hunRG : RunStarts ∪ Gaps = Starts := by
    ext x; simp only [RunStarts, Gaps, Starts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hbijRS : Finset.image (cc (nxt ht) S) RunStarts = P := by
    ext C
    simp only [Finset.mem_image, RunStarts, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, ⟨hs, _⟩, rfl⟩
      exact Finset.mem_image_of_mem _ hs
    · intro hC
      obtain ⟨s, hsC, hps, _, _, _, _⟩ := comp_arc ht hS hC
      obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
      exact ⟨s, ⟨hsS, hps⟩, hcs⟩
  have hinjRS : Set.InjOn (cc (nxt ht) S) (RunStarts : Set (Fin (6 * t))) := by
    intro s₁ hs₁ s₂ hs₂ heq
    obtain ⟨h1S, h1p⟩ := (Finset.mem_filter.mp hs₁).2
    obtain ⟨h2S, h2p⟩ := (Finset.mem_filter.mp hs₂).2
    obtain ⟨harc1, hlt1, _⟩ := comp_arc_of_start ht hS h1S h1p
    have h2in : s₂ ∈ cc (nxt ht) S s₁ := heq.symm ▸ selfMem (nxt ht) S h2S
    rw [harc1, mem_arc_iff] at h2in
    obtain ⟨k, hk, hkeq⟩ := h2in
    cases k with
    | zero => rw [add_zero, idx_self] at hkeq; exact hkeq
    | succ k =>
      exfalso; apply h2p
      have : prv ht s₂ = idx ht (s₁.val + k) := by
        rw [← hkeq, ← add_assoc, ← nxt_idx, prv_nxt]
      rw [this]
      have hmem : idx ht (s₁.val + k) ∈ cc (nxt ht) S s₁ := by
        rw [harc1, mem_arc_iff]; exact ⟨k, by omega, rfl⟩
      exact (Finset.mem_filter.mp hmem).1
  have hGaps_eq : Gaps = Finset.univ \ P.biUnion (halo (nxt ht)) := by
    ext x
    simp only [Gaps, P, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_biUnion_halo_iff, not_or]
  have hsum_halo : ∑ C ∈ P, (C.card + 1) + Gaps.card = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = (P.biUnion (halo (nxt ht))).card := by
      rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
      exact Finset.sum_congr rfl fun C hC => (halo_card_eq ht hS hC).symm
    rw [h1', hGaps_eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_le_univ (P.biUnion (halo (nxt ht)))
    simp only [Fintype.card_fin] at hle
    omega
  have hsum_def : ∑ C ∈ P, (C.card - 1) + Gaps.card = 2 := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      ring
    omega
  let dwt : Fin (6 * t) → ℕ := fun x => if x ∈ S then (cc (nxt ht) S x).card - 1 else 1
  let Defects := Starts.filter (fun x => 0 < dwt x)
  have hsum_dwt : ∑ x ∈ Defects, dwt x = 2 := by
    have h1' : ∑ x ∈ Defects, dwt x = ∑ x ∈ Starts, dwt x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hnd
      simp only [Defects, Finset.mem_filter, not_and, not_lt, Nat.le_zero] at hnd
      exact hnd hx
    rw [h1', ← hunRG, Finset.sum_union hdisRG]
    have hG : ∑ x ∈ Gaps, dwt x = Gaps.card := by
      have : ∑ x ∈ Gaps, dwt x = ∑ _ ∈ Gaps, 1 :=
        Finset.sum_congr rfl fun x hx => by
          have hxS := (Finset.mem_filter.mp hx).2.1
          simp [dwt, hxS]
      simp [this]
    have hR : ∑ x ∈ RunStarts, dwt x = ∑ C ∈ P, (C.card - 1) := by
      rw [← hbijRS, Finset.sum_image hinjRS]
      apply Finset.sum_congr rfl
      intro x hx
      have hxS := (Finset.mem_filter.mp hx).2.1
      simp [dwt, hxS]
    rw [hG, hR, hsum_def]
  have hSolo : ∀ x ∈ Starts, x ∉ Defects → x ∈ S ∧ nxt ht x ∉ S ∧ (cc (nxt ht) S x).card = 1 := by
    intro x hx hnd
    have hpx : prv ht x ∉ S := (Finset.mem_filter.mp hx).2
    have hdw0 : dwt x = 0 := by
      by_contra hne
      exact hnd (Finset.mem_filter.mpr ⟨hx, by omega⟩)
    have hxS : x ∈ S := by
      by_contra hns
      simp [dwt, hns] at hdw0
    have hpos : 0 < (cc (nxt ht) S x).card :=
      Finset.card_pos.mpr ⟨x, selfMem (nxt ht) S hxS⟩
    have hc1 : (cc (nxt ht) S x).card = 1 := by simp [dwt, hxS] at hdw0; omega
    have hnx : nxt ht x ∉ S := by
      obtain ⟨_, _, hout⟩ := comp_arc_of_start ht hS hxS hpx
      rw [hc1] at hout
      simpa [← nxt_idx, idx_self] using hout
    exact ⟨hxS, hnx, hc1⟩
  have hDef_card_le : Defects.card ≤ 2 := by
    have hge : Defects.card ≤ ∑ x ∈ Defects, dwt x := by
      have : ∑ _ ∈ Defects, 1 ≤ ∑ x ∈ Defects, dwt x :=
        Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      simpa using this
    omega
  have hDef_card_pos : 0 < Defects.card := by
    by_contra h0'
    have he : Defects = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he, Finset.sum_empty] at hsum_dwt
    omega
  have hwalk : ∀ (b : Fin (6 * t)) (len : ℕ), b ∈ Starts → len ≤ 6 * t →
      (∀ j < len, idx ht (b.val + j) ∉ Defects) →
      ∀ k, 2 * k < len →
        idx ht (b.val + 2 * k) ∈ S ∧
        prv ht (idx ht (b.val + 2 * k)) ∉ S ∧
        nxt ht (idx ht (b.val + 2 * k)) ∉ S := by
    intro b len hb hlen hnoDef
    have hgo : ∀ k, 2 * k ≤ len → idx ht (b.val + 2 * k) ∈ Starts := by
      intro k
      induction k with
      | zero => intro _; simpa [idx_self] using hb
      | succ k ih =>
        intro hk
        have hst : idx ht (b.val + 2 * k) ∈ Starts := ih (by omega)
        have hnd : idx ht (b.val + 2 * k) ∉ Defects := hnoDef (2 * k) (by omega)
        obtain ⟨_, hnx, _⟩ := hSolo _ hst hnd
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have e : prv ht (idx ht (b.val + 2 * (k + 1))) = nxt ht (idx ht (b.val + 2 * k)) := by
          rw [nxt_idx, show b.val + 2 * (k + 1) = (b.val + 2 * k + 1) + 1 by omega,
            ← nxt_idx, prv_nxt]
        rwa [e]
    intro k hk
    have hst := hgo k (by omega)
    have hnd := hnoDef (2 * k) hk
    obtain ⟨hs, hnx, _⟩ := hSolo _ hst hnd
    exact ⟨hs, (Finset.mem_filter.mp hst).2, hnx⟩
  by_cases hcard1 : Defects.card = 1
  · obtain ⟨a1, hDefEq⟩ := Finset.card_eq_one.mp hcard1
    have ha1Def : a1 ∈ Defects := hDefEq.symm ▸ Finset.mem_singleton_self a1
    have hdw2 : dwt a1 = 2 := by rw [hDefEq, Finset.sum_singleton] at hsum_dwt; exact hsum_dwt
    have ha1S : a1 ∈ S := by by_contra hns; simp [dwt, hns] at hdw2
    have ha1p : prv ht a1 ∉ S := (Finset.mem_filter.mp (Finset.mem_filter.mp ha1Def).1).2
    have ha1c : (cc (nxt ht) S a1).card = 3 := by
      have hpos := Finset.card_pos.mpr ⟨a1, selfMem (nxt ht) S ha1S⟩
      simp [dwt, ha1S] at hdw2; omega
    obtain ⟨harc1, _, hout1⟩ := comp_arc_of_start ht hS ha1S ha1p
    rw [ha1c] at harc1 hout1
    let b := idx ht (a1.val + 4)
    have hb2 : b.val % 2 = a1.val % 2 := by dsimp [b]; rw [idx_mod2]; omega
    have hbSt : b ∈ Starts := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have : prv ht b = idx ht (a1.val + 3) := by
        dsimp only [b]
        rw [show a1.val + 4 = (a1.val + 3) + 1 by omega, ← nxt_idx, prv_nxt]
      rwa [this]
    have hnoDef : ∀ j < 6 * t - 4, idx ht (b.val + j) ∉ Defects := by
      intro j hj hmem
      rw [hDefEq, Finset.mem_singleton] at hmem
      have heq : idx ht (a1.val + (4 + j)) = idx ht (a1.val + 0) := by
        have hb1 : idx ht (b.val + j) = idx ht (a1.val + (4 + j)) := by
          apply Fin.ext; dsimp only [b]
          change ((a1.val + 4) % (6 * t) + j) % (6 * t) = (a1.val + (4 + j)) % (6 * t)
          rw [Nat.mod_add_mod, add_assoc]
        rw [← hb1, hmem, add_zero, idx_self]
      have := idx_inj_range ht a1 (le_refl _) (by omega) (by omega) heq
      omega
    have hw := hwalk b (6 * t - 4) hbSt (by omega) hnoDef
    let Q := (Finset.range (3 * t - 2)).image (fun k => ({idx ht (b.val + 2 * k)} : Finset (Fin (6 * t))))
    have hC1P : cc (nxt ht) S a1 ∈ P := Finset.mem_image_of_mem _ ha1S
    have hQsub : Q ⊆ P.erase (cc (nxt ht) S a1) := by
      intro C hC
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hC
      have hklt : k < 3 * t - 2 := Finset.mem_range.mp hk
      obtain ⟨hs, hp, hn⟩ := hw k (by omega)
      have hmemP := (solo_mem_hSpace ht hs hp hn).1
      refine Finset.mem_erase.mpr ⟨?_, hmemP⟩
      intro heq
      have := congrArg Finset.card heq
      rw [Finset.card_singleton, ha1c] at this
      omega
    have hQcard : Q.card = 3 * t - 2 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro k₁ hk₁ k₂ hk₂ heq
      have hfeq : idx ht (b.val + 2 * k₁) = idx ht (b.val + 2 * k₂) :=
        Finset.singleton_injective heq
      have := idx_inj_range ht b (le_refl _) (by have := Finset.mem_range.mp hk₁; omega)
        (by have := Finset.mem_range.mp hk₂; omega) hfeq
      omega
    have hQeq : P.erase (cc (nxt ht) S a1) = Q := by
      apply (Finset.eq_of_subset_of_card_le hQsub _).symm
      rw [hQcard, Finset.card_erase_of_mem hC1P]
      omega
    exfalso
    by_cases hap : a1.val % 2 = 0
    · have hod : oddProj (hSum (cc (nxt ht) S a1)) ≠ 0 := by
        rw [harc1, hSum_arc ht a1 (by omega)]
        intro hz; rw [arcSum_oddProj_zero_iff] at hz; omega
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      have hDQ : D ∈ Q := hQeq ▸ Finset.mem_erase.mpr ⟨hDne, hDP⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hDQ
      have hpar : (idx ht (b.val + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
      rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpar, oddProj_incEven] at hDod
      exact hDod rfl
    · have hev : evenProj (hSum (cc (nxt ht) S a1)) ≠ 0 := by
        rw [harc1, hSum_arc ht a1 (by omega)]
        intro hz; rw [arcSum_evenProj_zero_iff] at hz; omega
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      have hDQ : D ∈ Q := hQeq ▸ Finset.mem_erase.mpr ⟨hDne, hDP⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hDQ
      have hpar : (idx ht (b.val + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
      rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpar, evenProj_incOdd] at hDev
      exact hDev rfl
  · have hcard2 : Defects.card = 2 := by omega
    obtain ⟨a1, a2, hne12, hDefEq⟩ := Finset.card_eq_two.mp hcard2
    have ha1Def : a1 ∈ Defects := by rw [hDefEq]; simp
    have ha2Def : a2 ∈ Defects := by rw [hDefEq]; simp
    have hdw12 : dwt a1 + dwt a2 = 2 := by
      rw [hDefEq, Finset.sum_pair hne12] at hsum_dwt; exact hsum_dwt
    have hdw1 : dwt a1 = 1 := by
      have p1 := (Finset.mem_filter.mp ha1Def).2
      have p2 := (Finset.mem_filter.mp ha2Def).2
      omega
    have hdw2 : dwt a2 = 1 := by omega
    let L : Fin (6 * t) → ℕ := fun a => if a ∈ S then 3 else 1
    have hL_spec : ∀ a ∈ Defects, dwt a = 1 →
        (L a = 1 ∧ a ∉ S ∧ prv ht a ∉ S ∧ idx ht (a.val + 1) ∈ Starts) ∨
        (L a = 3 ∧ a ∈ S ∧ prv ht a ∉ S ∧ cc (nxt ht) S a = arc ht a 2 ∧
          idx ht (a.val + 2) ∉ S ∧ idx ht (a.val + 3) ∈ Starts ∧
          idx ht (a.val + 1) ∈ S ∧ idx ht (a.val + 1) ∉ Starts ∧ idx ht (a.val + 2) ∉ Starts) := by
      intro a ha hdw
      have hap : prv ht a ∉ S := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      by_cases haS : a ∈ S
      · right
        have hpos := Finset.card_pos.mpr ⟨a, selfMem (nxt ht) S haS⟩
        have hc2 : (cc (nxt ht) S a).card = 2 := by simp [dwt, haS] at hdw; omega
        obtain ⟨harc, _, hout⟩ := comp_arc_of_start ht hS haS hap
        rw [hc2] at harc hout
        have h1S : idx ht (a.val + 1) ∈ S := by
          have : idx ht (a.val + 1) ∈ cc (nxt ht) S a := by
            rw [harc, mem_arc_iff]; exact ⟨1, by decide, rfl⟩
          exact (Finset.mem_filter.mp this).1
        have h1nSt : idx ht (a.val + 1) ∉ Starts := by
          simp only [Starts, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          have : prv ht (idx ht (a.val + 1)) = a := by rw [← nxt_idx, idx_self, prv_nxt]
          rwa [this]
        have h2nSt : idx ht (a.val + 2) ∉ Starts := by
          simp only [Starts, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          have : prv ht (idx ht (a.val + 2)) = idx ht (a.val + 1) := by
            rw [show a.val + 2 = (a.val + 1) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [this]
        have h3St : idx ht (a.val + 3) ∈ Starts := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : prv ht (idx ht (a.val + 3)) = idx ht (a.val + 2) := by
            rw [show a.val + 3 = (a.val + 2) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [this]
        exact ⟨by simp [L, haS], haS, hap, harc, hout, h3St, h1S, h1nSt, h2nSt⟩
      · left
        have h1St : idx ht (a.val + 1) ∈ Starts := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : prv ht (idx ht (a.val + 1)) = a := by rw [← nxt_idx, idx_self, prv_nxt]
          rwa [this]
        exact ⟨by simp [L, haS], haS, hap, h1St⟩
    have hseg : ∀ (x y : Fin (6 * t)), x ∈ Defects → y ∈ Defects → x ≠ y → dwt x = 1 →
        Defects = {x, y} →
        let dist := (y.val + 6 * t - x.val) % (6 * t)
        L x ≤ dist ∧ (dist - L x) % 2 = 0 ∧
        (∀ k < (dist - L x) / 2,
          idx ht (x.val + L x + 2 * k) ∈ S ∧
          prv ht (idx ht (x.val + L x + 2 * k)) ∉ S ∧
          nxt ht (idx ht (x.val + L x + 2 * k)) ∉ S) := by
      intro x y hxD hyD hxy hdwx hDeq dist
      have hdist_pos : 0 < dist := by
        by_contra h0'
        have h0'' : dist = 0 := by omega
        apply hxy; apply Fin.ext
        dsimp only [dist] at h0''
        have hxlt := x.isLt; have hylt := y.isLt
        by_cases c : y.val + 6 * t - x.val < 6 * t
        · rw [Nat.mod_eq_of_lt c] at h0''; omega
        · rw [mod_eq_sub_of_lt2 (by omega) (by omega)] at h0''; omega
      have hdist_lt : dist < 6 * t := Nat.mod_lt _ (by omega)
      have hy_eq : idx ht (x.val + dist) = y := idx_add_dist ht x y
      have hLx_le : L x ≤ dist := by
        rcases hL_spec x hxD hdwx with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
        · omega
        · rw [hL3]
          by_contra hlt3
          have hySt : y ∈ Starts := (Finset.mem_filter.mp hyD).1
          have hd12 : dist = 1 ∨ dist = 2 := by omega
          rcases hd12 with hd1 | hd2
          · rw [hd1] at hy_eq; exact h1n (hy_eq ▸ hySt)
          · rw [hd2] at hy_eq; exact h2n (hy_eq ▸ hySt)
      have hbSt : idx ht (x.val + L x) ∈ Starts := by
        rcases hL_spec x hxD hdwx with ⟨hL1, _, _, h1St⟩ | ⟨hL3, _, _, _, _, h3St, _, _, _⟩
        · rw [hL1]; exact h1St
        · rw [hL3]; exact h3St
      let b := idx ht (x.val + L x)
      have hnoD : ∀ j < dist - L x, idx ht (b.val + j) ∉ Defects := by
        intro j hj hmem
        rw [hDeq, Finset.mem_insert, Finset.mem_singleton] at hmem
        have hb1 : idx ht (b.val + j) = idx ht (x.val + (L x + j)) := by
          apply Fin.ext; dsimp only [b]
          change ((x.val + L x) % (6 * t) + j) % (6 * t) = (x.val + (L x + j)) % (6 * t)
          rw [Nat.mod_add_mod, add_assoc]
        rw [hb1] at hmem
        rcases hmem with h1' | h2'
        · have : idx ht (x.val + (L x + j)) = idx ht (x.val + 0) := by rw [h1', add_zero, idx_self]
          have := idx_inj_range ht x (le_refl _) (by omega) (by omega) this
          have : 0 < L x := by dsimp [L]; split_ifs <;> omega
          omega
        · rw [← hy_eq] at h2'
          have := idx_inj_range ht x (le_refl _) (by omega) hdist_lt h2'
          omega
      have hw := hwalk b (dist - L x) hbSt (by omega) hnoD
      have heven : (dist - L x) % 2 = 0 := by
        by_contra hodd
        let q := (dist - L x) / 2
        obtain ⟨hs, _, _⟩ := hw q (by omega)
        have hpy : prv ht y ∈ S := by
          have e : prv ht y = idx ht (b.val + 2 * q) := by
            rw [← hy_eq]
            have e1 : idx ht (b.val + 2 * q) = idx ht (x.val + (L x + 2 * q)) := by
              apply Fin.ext; dsimp only [b]
              change ((x.val + L x) % (6 * t) + 2 * q) % (6 * t) = (x.val + (L x + 2 * q)) % (6 * t)
              rw [Nat.mod_add_mod, add_assoc]
            rw [e1, show x.val + dist = (x.val + (L x + 2 * q)) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [e]
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hyD).1).2 hpy
      refine ⟨hLx_le, heven, fun k hk => ?_⟩
      have hb1 : idx ht (b.val + 2 * k) = idx ht (x.val + L x + 2 * k) := by
        apply Fin.ext; dsimp only [b]
        change ((x.val + L x) % (6 * t) + 2 * k) % (6 * t) = (x.val + L x + 2 * k) % (6 * t)
        rw [Nat.mod_add_mod]
      simpa [hb1] using hw k (by omega)
    have hseg1 := hseg a1 a2 ha1Def ha2Def hne12 hdw1 hDefEq
    have hseg2 := hseg a2 a1 ha2Def ha1Def hne12.symm hdw2 (by rw [hDefEq, Finset.pair_comm])
    let d1 := (a2.val + 6 * t - a1.val) % (6 * t)
    let d2 := (a1.val + 6 * t - a2.val) % (6 * t)
    have hd12_sum : d1 + d2 = 6 * t := by
      dsimp only [d1, d2]
      have h1lt := a1.isLt; have h2lt := a2.isLt
      by_cases c : a1.val < a2.val
      · rw [mod_eq_sub_of_lt2 (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · have hgt : a2.val < a1.val := by
          have : a1.val ≠ a2.val := fun e => hne12 (Fin.ext e)
          omega
        rw [Nat.mod_eq_of_lt (by omega), mod_eq_sub_of_lt2 (by omega) (by omega)]; omega
    let k1 := (d1 - L a1) / 2
    let k2 := (d2 - L a2) / 2
    have hL1_le : L a1 ≤ d1 := hseg1.1
    have hL2_le : L a2 ≤ d2 := hseg2.1
    have h2k1 : 2 * k1 = d1 - L a1 := by have := hseg1.2.1; omega
    have h2k2 : 2 * k2 = d2 - L a2 := by have := hseg2.2.1; omega
    have hsolo1 : ∀ k < k1, ({idx ht (a1.val + L a1 + 2 * k)} : Finset (Fin (6 * t))) ∈ P ∧
        hVec (idx ht (a1.val + L a1 + 2 * k)) ∈ hSpace ht S := fun k hk => by
      obtain ⟨hs, hp, hn⟩ := hseg1.2.2 k hk
      exact solo_mem_hSpace ht hs hp hn
    have hsolo2 : ∀ k < k2, ({idx ht (a2.val + L a2 + 2 * k)} : Finset (Fin (6 * t))) ∈ P ∧
        hVec (idx ht (a2.val + L a2 + 2 * k)) ∈ hSpace ht S := fun k hk => by
      obtain ⟨hs, hp, hn⟩ := hseg2.2.2 k hk
      exact solo_mem_hSpace ht hs hp hn
    have hpar_rel : a2.val % 2 = (a1.val + L a1) % 2 := by
      have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
      have := congrArg (fun z : Fin (6 * t) => z.val % 2) hy
      rw [idx_mod2] at this; omega
    have hP_decomp : ∀ C ∈ P,
        (a1 ∈ S ∧ C = cc (nxt ht) S a1) ∨
        (a2 ∈ S ∧ C = cc (nxt ht) S a2) ∨
        (∃ k < k1, C = {idx ht (a1.val + L a1 + 2 * k)}) ∨
        (∃ k < k2, C = {idx ht (a2.val + L a2 + 2 * k)}) := by
      intro C hC
      obtain ⟨s, hsC, hps, _, _, _, _⟩ := comp_arc ht hS hC
      obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
      by_cases hs1 : s = a1
      · left; exact ⟨hs1 ▸ hsS, (hs1 ▸ hcs).symm⟩
      by_cases hs2 : s = a2
      · right; left; exact ⟨hs2 ▸ hsS, (hs2 ▸ hcs).symm⟩
      have hsSt : s ∈ Starts := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hps⟩
      have hsNotDef : s ∉ Defects := by rw [hDefEq]; simp [hs1, hs2]
      obtain ⟨_, hns, _⟩ := hSolo s hsSt hsNotDef
      have hCeq : C = {s} := by
        rw [← hcs]
        have := (solo_mem_hSpace ht hsS hps hns).1
        exact joined (nxt ht) S (Finset.mem_image_of_mem _ hsS) this (selfMem (nxt ht) S hsS)
          (Finset.mem_singleton_self s) (Or.inl rfl)
      let ds := (s.val + 6 * t - a1.val) % (6 * t)
      have hds_lt : ds < 6 * t := Nat.mod_lt _ (by omega)
      have hs_eq : idx ht (a1.val + ds) = s := idx_add_dist ht a1 s
      have hds_ge : L a1 ≤ ds := by
        rcases hL_spec a1 ha1Def hdw1 with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
        · rw [hL1]; by_contra h0'; have hd0 : ds = 0 := by omega
          rw [hd0, add_zero, idx_self] at hs_eq; exact hs1 hs_eq.symm
        · rw [hL3]; by_contra hlt3
          have hcases : ds = 0 ∨ ds = 1 ∨ ds = 2 := by omega
          rcases hcases with hd0 | hd1 | hd2
          · rw [hd0, add_zero, idx_self] at hs_eq; exact hs1 hs_eq.symm
          · rw [hd1] at hs_eq; exact h1n (hs_eq ▸ hsSt)
          · rw [hd2] at hs_eq; exact h2n (hs_eq ▸ hsSt)
      by_cases hlt_d1 : ds < d1
      · right; right; left
        have hev_ds : (ds - L a1) % 2 = 0 := by
          by_contra hodd
          let q := (ds - L a1) / 2
          obtain ⟨hs', _, _⟩ := hseg1.2.2 q (by omega)
          have hps' : prv ht s ∈ S := by
            have : prv ht s = idx ht (a1.val + L a1 + 2 * q) := by
              rw [← hs_eq, show a1.val + ds = (a1.val + L a1 + 2 * q) + 1 by omega, ← nxt_idx, prv_nxt]
            rwa [this]
          exact hps hps'
        refine ⟨(ds - L a1) / 2, by omega, ?_⟩
        rw [hCeq, ← hs_eq]; congr 2; omega
      · right; right; right
        let ds2 := (s.val + 6 * t - a2.val) % (6 * t)
        have hs2_eq : idx ht (a2.val + ds2) = s := idx_add_dist ht a2 s
        have hds2_eq : ds2 = ds - d1 := by
          have ha2_eq : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
          have hidx2 : idx ht (a2.val + (ds - d1)) = s := by
            rw [← hs_eq]
            apply Fin.ext; rw [← ha2_eq]
            change ((a1.val + d1) % (6 * t) + (ds - d1)) % (6 * t) = (a1.val + ds) % (6 * t)
            rw [Nat.mod_add_mod]; congr 1; omega
          exact idx_inj_range ht a2 (le_refl _) (Nat.mod_lt _ (by omega)) (by omega) (hs2_eq.trans hidx2.symm)
        have hds2_ge : L a2 ≤ ds2 := by
          rcases hL_spec a2 ha2Def hdw2 with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
          · rw [hL1]; by_contra h0'; have hd0 : ds2 = 0 := by omega
            rw [hd0, add_zero, idx_self] at hs2_eq; exact hs2 hs2_eq.symm
          · rw [hL3]; by_contra hlt3
            have hcases : ds2 = 0 ∨ ds2 = 1 ∨ ds2 = 2 := by omega
            rcases hcases with hd0 | hd1 | hd2
            · rw [hd0, add_zero, idx_self] at hs2_eq; exact hs2 hs2_eq.symm
            · rw [hd1] at hs2_eq; exact h1n (hs2_eq ▸ hsSt)
            · rw [hd2] at hs2_eq; exact h2n (hs2_eq ▸ hsSt)
        have hev_ds2 : (ds2 - L a2) % 2 = 0 := by
          by_contra hodd
          let q := (ds2 - L a2) / 2
          obtain ⟨hs', _, _⟩ := hseg2.2.2 q (by omega)
          have hps' : prv ht s ∈ S := by
            have : prv ht s = idx ht (a2.val + L a2 + 2 * q) := by
              rw [← hs2_eq, show a2.val + ds2 = (a2.val + L a2 + 2 * q) + 1 by omega, ← nxt_idx, prv_nxt]
            rwa [this]
          exact hps hps'
        refine ⟨(ds2 - L a2) / 2, by omega, ?_⟩
        rw [hCeq, ← hs2_eq]; congr 2; omega
    have hboth : LinearMap.range incEven ≤ hSpace ht S ∧ LinearMap.range incOdd ≤ hSpace ht S := by
      rcases hL_spec a1 ha1Def hdw1 with ⟨hL1, ha1nS, _, _⟩ | ⟨hL1, ha1S, _, harc1, _, _, _, _, _⟩ <;>
      rcases hL_spec a2 ha2Def hdw2 with ⟨hL2, ha2nS, _, _⟩ | ⟨hL2, ha2S, _, harc2, _, _, _, _, _⟩
      · refine runs_sub1_two_gaps ht hg h0 h1 (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2)
          (by rw [hL1] at hpar_rel; omega)
          (by simpa [hL1] using hsolo1) (by simpa [hL2] using hsolo2) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨h, _⟩ | ⟨h, _⟩ | h | h
        · exact (ha1nS h).elim
        · exact (ha2nS h).elim
        · left; simpa [hL1] using h
        · right; simpa [hL2] using h
      · refine runs_sub1_run_gap ht ht2 hg (a1 := a2) (a2 := a1) (k1 := k2) (k2 := k1) ha2S harc2
          (by rw [hL1] at hpar_rel; omega)
          (by rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega)
          (fun hk1 => by
            have hd1_eq : d1 = 3 := by rw [hL1] at h2k1 hL1_le; omega
            have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
            rwa [hd1_eq] at hy)
          (by simpa [hL2] using hsolo2) (by simpa [hL1] using hsolo1) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨h, _⟩ | ⟨_, h⟩ | h | h
        · exact (ha1nS h).elim
        · exact Or.inl h
        · right; right; simpa [hL1] using h
        · right; left; simpa [hL2] using h
      · refine runs_sub1_run_gap ht ht2 hg (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2) ha1S harc1
          (by rw [hL1] at hpar_rel; omega)
          (by rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega)
          (fun hk2 => by
            have hd2_eq : d2 = 3 := by rw [hL2] at h2k2 hL2_le; omega
            have hy : idx ht (a2.val + d2) = a1 := idx_add_dist ht a2 a1
            rwa [hd2_eq] at hy)
          (by simpa [hL1] using hsolo1) (by simpa [hL2] using hsolo2) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨_, h⟩ | ⟨h, _⟩ | h | h
        · exact Or.inl h
        · exact (ha2nS h).elim
        · right; left; simpa [hL1] using h
        · right; right; simpa [hL2] using h
      · have hk12 : k1 + k2 = 3 * t - 3 := by
          rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega
        by_cases hk2_2 : 2 ≤ k2
        · exact runs_sub1_two_runs_half ht (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2) ha1S ha2S harc1 harc2
            (by rw [hL1] at hpar_rel; omega) hk2_2
            (fun hk0 => by
              have hd1_eq : d1 = 3 := by rw [hL1] at h2k1 hL1_le; omega
              have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
              rwa [hd1_eq] at hy)
            (fun k hk => by simpa [hL1] using (hsolo1 k hk).2)
            (fun k hk => by simpa [hL2] using (hsolo2 k hk).2)
        · have hk1_2 : 2 ≤ k1 := by omega
          exact runs_sub1_two_runs_half ht (a1 := a2) (a2 := a1) (k1 := k2) (k2 := k1) ha2S ha1S harc2 harc1
            (by rw [hL1] at hpar_rel; omega) hk1_2
            (fun hk0 => by
              have hd2_eq : d2 = 3 := by rw [hL2] at h2k2 hL2_le; omega
              have hy : idx ht (a2.val + d2) = a1 := idx_add_dist ht a2 a1
              rwa [hd2_eq] at hy)
            (fun k hk => by simpa [hL2] using (hsolo2 k hk).2)
            (fun k hk => by simpa [hL1] using (hsolo1 k hk).2)
    exact finrank_eq_four_of_both_lanes hboth.1 hboth.2

lemma runs_a2_case_pure_even {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h1 : 0 < sitesOf S 1) (hr : (pcs (nxt ht) S).card = 3 * t - 2)
    (hVeq : hSpace ht S = LinearMap.range incEven)
    (hdef : ∑ C ∈ pcs (nxt ht) S, (C.card - 1) ≤ 4) : False := by
  set P := pcs (nxt ht) S
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp h1
  obtain ⟨hi1S, hi1p⟩ := Finset.mem_filter.mp hi1
  let Cstar := cc (nxt ht) S i1
  have hCstarP : Cstar ∈ P := Finset.mem_image_of_mem _ hi1S
  obtain ⟨s, _, _, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
  have hod0 : oddProj (hSum Cstar) = 0 := by
    have hmem : hSum Cstar ∈ LinearMap.range incEven := hVeq ▸ mem_hSpace ht hCstarP
    obtain ⟨u, hu⟩ := hmem
    rw [← hu, oddProj_incEven]
  have hge5 : 5 ≤ Cstar.card := by
    have hne1 : Cstar.card ≠ 1 := by
      intro hc1
      have hCeq : Cstar = {i1} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨selfMem (nxt ht) S hi1S, fun j hj => Finset.card_le_one_iff.mp hc1.le hj (selfMem (nxt ht) S hi1S)⟩
      rw [hCeq, hSum, Finset.sum_singleton, hVec_eq_incOdd hi1p, oddProj_incOdd] at hod0
      exact col2_ne_zero _ hod0
    rw [harc, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod0
    omega
  have hcard5 : Cstar.card = 5 := by
    have h1' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    omega
  have hsp : s.val % 2 = 1 := by
    rw [harc, hcard5, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod0
    omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have h2' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C ≠ Cstar → C.card = 1 := by
    intro C hCP hne
    have hsplit := Finset.add_sum_erase P (fun D => D.card - 1) hCstarP
    have hle' := Finset.single_le_sum (fun D _ => Nat.zero_le (D.card - 1))
      (Finset.mem_erase.mpr ⟨hne, hCP⟩)
    have hpos' := Finset.card_pos.mpr (populated (nxt ht) S hCP)
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  let y := idx ht (s.val + 6)
  have hpy : prv ht y ∉ S := by
    have e : prv ht y = idx ht (s.val + 5) := by
      dsimp only [y]
      rw [show s.val + 6 = (s.val + 5) + 1 by omega, ← nxt_idx, prv_nxt]
    rw [e, ← hcard5]; exact hout
  have hyS : y ∈ S := by
    have hm : y ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
    rw [mem_biUnion_halo_iff] at hm
    rcases hm with h | h
    · exact h
    · exact (hpy h).elim
  let D := cc (nxt ht) S y
  have hDP : D ∈ P := Finset.mem_image_of_mem _ hyS
  have hDne : D ≠ Cstar := by
    intro heq
    have hyC : y ∈ Cstar := heq ▸ selfMem (nxt ht) S hyS
    rw [harc, hcard5, mem_arc_iff] at hyC
    obtain ⟨k, hk, hkeq⟩ := hyC
    have := idx_inj_range ht s (le_refl _) (by omega) (by omega) hkeq
    omega
  have hD1 : D.card = 1 := hall1 D hDP hDne
  have hDeq : D = {y} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨selfMem (nxt ht) S hyS, fun j hj => Finset.card_le_one_iff.mp hD1.le hj (selfMem (nxt ht) S hyS)⟩
  have hyp : y.val % 2 = 1 := by dsimp only [y]; rw [idx_mod2]; omega
  have hmem : hSum D ∈ LinearMap.range incEven := hVeq ▸ mem_hSpace ht hDP
  obtain ⟨u, hu⟩ := hmem
  have := congrArg oddProj hu
  rw [oddProj_incEven, hDeq, hSum, Finset.sum_singleton, hVec_eq_incOdd hyp, oddProj_incOdd] at this
  exact col2_ne_zero _ this.symm

lemma runs_a2_case_pure_odd {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (hr : (pcs (nxt ht) S).card = 3 * t - 2)
    (hVeq : hSpace ht S = LinearMap.range incOdd)
    (hdef : ∑ C ∈ pcs (nxt ht) S, (C.card - 1) ≤ 4) : False := by
  set P := pcs (nxt ht) S
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp h0
  obtain ⟨hi0S, hi0p⟩ := Finset.mem_filter.mp hi0
  let Cstar := cc (nxt ht) S i0
  have hCstarP : Cstar ∈ P := Finset.mem_image_of_mem _ hi0S
  obtain ⟨s, _, _, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
  have hev0 : evenProj (hSum Cstar) = 0 := by
    have hmem : hSum Cstar ∈ LinearMap.range incOdd := hVeq ▸ mem_hSpace ht hCstarP
    obtain ⟨u, hu⟩ := hmem
    rw [← hu, evenProj_incOdd]
  have hge5 : 5 ≤ Cstar.card := by
    have hne1 : Cstar.card ≠ 1 := by
      intro hc1
      have hCeq : Cstar = {i0} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨selfMem (nxt ht) S hi0S, fun j hj => Finset.card_le_one_iff.mp hc1.le hj (selfMem (nxt ht) S hi0S)⟩
      rw [hCeq, hSum, Finset.sum_singleton, hVec_eq_incEven hi0p, evenProj_incEven] at hev0
      exact col2_ne_zero _ hev0
    rw [harc, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev0
    omega
  have hcard5 : Cstar.card = 5 := by
    have h1' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    omega
  have hsp : s.val % 2 = 0 := by
    rw [harc, hcard5, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev0
    omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have h2' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C ≠ Cstar → C.card = 1 := by
    intro C hCP hne
    have hsplit := Finset.add_sum_erase P (fun D => D.card - 1) hCstarP
    have hle' := Finset.single_le_sum (fun D _ => Nat.zero_le (D.card - 1))
      (Finset.mem_erase.mpr ⟨hne, hCP⟩)
    have hpos' := Finset.card_pos.mpr (populated (nxt ht) S hCP)
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  let y := idx ht (s.val + 6)
  have hpy : prv ht y ∉ S := by
    have e : prv ht y = idx ht (s.val + 5) := by
      dsimp only [y]
      rw [show s.val + 6 = (s.val + 5) + 1 by omega, ← nxt_idx, prv_nxt]
    rw [e, ← hcard5]; exact hout
  have hyS : y ∈ S := by
    have hm : y ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
    rw [mem_biUnion_halo_iff] at hm
    rcases hm with h | h
    · exact h
    · exact (hpy h).elim
  let D := cc (nxt ht) S y
  have hDP : D ∈ P := Finset.mem_image_of_mem _ hyS
  have hDne : D ≠ Cstar := by
    intro heq
    have hyC : y ∈ Cstar := heq ▸ selfMem (nxt ht) S hyS
    rw [harc, hcard5, mem_arc_iff] at hyC
    obtain ⟨k, hk, hkeq⟩ := hyC
    have := idx_inj_range ht s (le_refl _) (by omega) (by omega) hkeq
    omega
  have hD1 : D.card = 1 := hall1 D hDP hDne
  have hDeq : D = {y} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨selfMem (nxt ht) S hyS, fun j hj => Finset.card_le_one_iff.mp hD1.le hj (selfMem (nxt ht) S hyS)⟩
  have hyp : y.val % 2 = 0 := by dsimp only [y]; rw [idx_mod2]; omega
  have hmem : hSum D ∈ LinearMap.range incOdd := hVeq ▸ mem_hSpace ht hDP
  obtain ⟨u, hu⟩ := hmem
  have := congrArg evenProj hu
  rw [evenProj_incOdd, hDeq, hSum, Finset.sum_singleton, hVec_eq_incEven hyp, evenProj_incEven] at this
  exact col2_ne_zero _ this.symm

lemma runs_a2_case_11 {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    {we wo : V2} (hwe0 : we ≠ 0) (hwo0 : wo ≠ 0)
    (hV_proj : ∀ v ∈ hSpace ht S, (evenProj v = 0 ∨ evenProj v = we) ∧ (oddProj v = 0 ∨ oddProj v = wo))
    (hP_part : (pcs (nxt ht) S |>.filter (·.card = 1)).card +
      (pcs (nxt ht) S |>.filter (·.card = 2)).card +
      (pcs (nxt ht) S |>.filter (·.card = 3)).card +
      (pcs (nxt ht) S |>.filter (4 ≤ ·.card)).card = 3 * t - 2)
    (hP_def : (pcs (nxt ht) S |>.filter (·.card = 2)).card +
      2 * (pcs (nxt ht) S |>.filter (·.card = 3)).card +
      3 * (pcs (nxt ht) S |>.filter (4 ≤ ·.card)).card ≤ 4) : False := by
  set P := pcs (nxt ht) S
  set P1 := P.filter (fun C => C.card = 1)
  set P2 := P.filter (fun C => C.card = 2)
  set P3 := P.filter (fun C => C.card = 3)
  set P4 := P.filter (fun C => 4 ≤ C.card)
  let G := Finset.univ.filter (fun i : Fin (6 * t) =>
    (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo))
  have hG_card : G.card = 2 * t := by
    let Ge := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
    let Go := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
    have hdis : Disjoint Ge Go := Finset.disjoint_filter.mpr fun _ _ a b => by omega
    have hun : Ge ∪ Go = G := by ext i; simp [Ge, Go, G]
    rw [← hun, Finset.card_union_of_disjoint hdis,
      card_lane_col_eq ht 0 (by decide) we hwe0,
      card_lane_col_eq ht 1 (by decide) wo hwo0]
    omega
  have hch1 : ∀ C ∈ P1, 1 ≤ (C ∩ G).card := by
    intro C hC1
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    obtain ⟨i, hiC⟩ := populated (nxt ht) S hCP
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    rw [hCeq, hSum, Finset.sum_singleton] at hpv
    have hiG : i ∈ G := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_cases hp : i.val % 2 = 0
      · left; refine ⟨hp, ?_⟩
        rw [hVec_eq_incEven hp, evenProj_incEven] at hpv
        rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
      · right; have ho : i.val % 2 = 1 := by omega
        refine ⟨ho, ?_⟩
        rw [hVec_eq_incOdd ho, oddProj_incOdd] at hpv
        rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
    exact Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hiC, hiG⟩⟩
  have hch2 : ∀ C ∈ P2, 2 ≤ (C ∩ G).card := by
    intro C hC2
    obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
    obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    have hs2 : hSum C = hPat s.val + hPat (s.val + 1) := by
      rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
    have h0in : idx ht (s.val + 0) ∈ C := by
      rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
    have h1in : idx ht (s.val + 1) ∈ C := by
      rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
    have hne01 : idx ht (s.val + 0) ≠ idx ht (s.val + 1) := fun h => by
      have := idx_inj_range ht s (by omega) (by decide : 0 < 2) (by decide : 1 < 2) h; omega
    have hbothG : idx ht (s.val + 0) ∈ G ∧ idx ht (s.val + 1) ∈ G := by
      rw [hs2] at hpv
      by_cases hsp : s.val % 2 = 0
      · rw [hPat_eq_incEven hsp, hPat_eq_incOdd (by omega)] at hpv
        simp only [map_add, evenProj_incEven, evenProj_incOdd, oddProj_incEven, oddProj_incOdd, add_zero, zero_add] at hpv
        have h0G : idx ht (s.val + 0) ∈ G := by
          rw [add_zero, idx_self]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hsp, ?_⟩⟩
          rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        have h1G : idx ht (s.val + 1) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by rw [idx_mod2]; omega, ?_⟩⟩
          rw [← col2_mod3, idx_div2_mod3, col2_mod3]
          rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        exact ⟨h0G, h1G⟩
      · rw [hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega)] at hpv
        simp only [map_add, evenProj_incEven, evenProj_incOdd, oddProj_incEven, oddProj_incOdd, add_zero, zero_add] at hpv
        have h0G : idx ht (s.val + 0) ∈ G := by
          rw [add_zero, idx_self]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, ?_⟩⟩
          rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        have h1G : idx ht (s.val + 1) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by rw [idx_mod2]; omega, ?_⟩⟩
          rw [← col2_mod3, idx_div2_mod3, col2_mod3]
          rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        exact ⟨h0G, h1G⟩
    calc 2 = ({idx ht (s.val + 0), idx ht (s.val + 1)} : Finset _).card := (Finset.card_pair hne01).symm
      _ ≤ (C ∩ G).card := Finset.card_le_card (Finset.insert_subset (Finset.mem_inter.mpr ⟨h0in, hbothG.1⟩)
          (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨h1in, hbothG.2⟩)))
  have hch3 : ∀ C ∈ P3, 1 ≤ (C ∩ G).card := by
    intro C hC3
    obtain ⟨hCP, hc3⟩ := Finset.mem_filter.mp hC3
    obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    have hs3 : hSum C = hPat s.val + hPat (s.val + 1) + hPat (s.val + 2) := by
      rw [harc, hc3, hSum_arc ht s (by omega), arcSum_three]
    have h1in : idx ht (s.val + 1) ∈ C := by
      rw [harc, hc3]; exact (mem_arc_iff ht s 3 _).mpr ⟨1, by decide, rfl⟩
    have h1G : idx ht (s.val + 1) ∈ G := by
      rw [hs3] at hpv
      by_cases hsp : s.val % 2 = 0
      · rw [hPat_eq_incEven hsp, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega)] at hpv
        simp only [map_add, oddProj_incEven, oddProj_incOdd, zero_add, add_zero] at hpv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by rw [idx_mod2]; omega, ?_⟩⟩
        rw [← col2_mod3, idx_div2_mod3, col2_mod3]
        rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
      · rw [hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega)] at hpv
        simp only [map_add, evenProj_incOdd, evenProj_incEven, zero_add, add_zero] at hpv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by rw [idx_mod2]; omega, ?_⟩⟩
        rw [← col2_mod3, idx_div2_mod3, col2_mod3]
        rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
    exact Finset.card_pos.mpr ⟨idx ht (s.val + 1), Finset.mem_inter.mpr ⟨h1in, h1G⟩⟩
  let P123 := P1 ∪ P2 ∪ P3
  have hd12 : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ a b => by omega
  have hd123 : Disjoint (P1 ∪ P2) P3 :=
    Finset.disjoint_left.mpr fun C h12 h3 => by
      simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter] at h12 h3; omega
  have hP123_dis : (↑P123 : Set (Finset (Fin (6 * t)))).PairwiseDisjoint (fun C => C ∩ G) := by
    intro C hC D hD hne
    have hCP : C ∈ P := by
      simp only [P123, P1, P2, P3, Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at hC
      rcases hC with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
    have hDP : D ∈ P := by
      simp only [P123, P1, P2, P3, Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at hD
      rcases hD with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (pcs_pairwiseDisjoint (nxt ht) S hCP hDP hne)
  have hsum123 : P1.card + 2 * P2.card + P3.card ≤ (P123.biUnion (fun C => C ∩ G)).card := by
    rw [Finset.card_biUnion hP123_dis]
    dsimp only [P123]
    rw [Finset.sum_union hd123, Finset.sum_union hd12]
    have s1 : P1.card ≤ ∑ C ∈ P1, (C ∩ G).card := by
      have := Finset.sum_le_sum hch1; simpa using this
    have s2 : 2 * P2.card ≤ ∑ C ∈ P2, (C ∩ G).card := by
      have := Finset.sum_le_sum hch2; simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have s3 : P3.card ≤ ∑ C ∈ P3, (C ∩ G).card := by
      have := Finset.sum_le_sum hch3; simpa using this
    omega
  have hbi_sub : P123.biUnion (fun C => C ∩ G) ⊆ G := by
    intro x hx
    obtain ⟨_, _, hx'⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx').2
  by_cases hP4_0 : P4.card = 0
  · have hleG := Finset.card_le_card hbi_sub
    omega
  · have hP4_1 : P4.card = 1 := by omega
    obtain ⟨Cstar, hCstar4⟩ := Finset.card_pos.mp (by omega : 0 < P4.card)
    obtain ⟨hCstarP, hge4⟩ := Finset.mem_filter.mp hCstar4
    obtain ⟨s, _, hps, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
    let B := arc ht (prv ht s) 6
    have hBG_card : (B ∩ G).card = 2 := by
      have heq : B ∩ G = B.filter (fun i : Fin (6 * t) =>
          (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)) := by
        ext i; simp [G]
      rw [heq]
      exact card_six_window_hits ht (prv ht s) we wo hwe0 hwo0
    have hB_dis : Disjoint (P123.biUnion (fun C => C ∩ G)) (B ∩ G) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      obtain ⟨C, hC123, hxCG⟩ := Finset.mem_biUnion.mp hx1
      have hxC : x ∈ C := (Finset.mem_inter.mp hxCG).1
      have hxB : x ∈ B := (Finset.mem_inter.mp hx2).1
      have hCP : C ∈ P := by
        simp only [P123, P1, P2, P3, Finset.mem_union, Finset.mem_filter] at hC123
        rcases hC123 with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
      have hCne : C ≠ Cstar := by
        intro eq
        rw [eq] at hC123
        simp only [P123, P1, P2, P3, Finset.mem_union, Finset.mem_filter] at hC123
        omega
      have hxS : x ∈ S := (center (nxt ht) S hCP hxC).1
      have hxnCs : x ∉ Cstar := Finset.disjoint_left.mp
        (pcs_pairwiseDisjoint (nxt ht) S hCP hCstarP hCne) hxC
      obtain ⟨k, hk, hkx⟩ := (mem_arc_iff ht (prv ht s) 6 x).mp hxB
      have hshift : ∀ j, idx ht ((prv ht s).val + (j + 1)) = idx ht (s.val + j) := fun j => by
        apply Fin.ext
        change ((prv ht s).val + (j + 1)) % (6 * t) = (s.val + j) % (6 * t)
        rw [prv_val]
        have hs := s.isLt
        split_ifs with h0
        · rw [h0, zero_add]
          have e : 6 * t - 1 + (j + 1) = j + 6 * t := by omega
          rw [e, Nat.add_mod_right]
        · congr 1; omega
      cases k with
      | zero =>
        rw [add_zero, idx_self] at hkx
        exact hps (hkx ▸ hxS)
      | succ k =>
        rw [hshift k] at hkx
        by_cases hk4 : k < Cstar.card
        · apply hxnCs
          rw [harc, mem_arc_iff]
          exact ⟨k, hk4, hkx⟩
        · have hk4eq : k = 4 := by omega
          have hcs4 : Cstar.card = 4 := by omega
          rw [hk4eq, ← hcs4] at hkx
          exact hout (hkx ▸ hxS)
    have hun_sub : P123.biUnion (fun C => C ∩ G) ∪ (B ∩ G) ⊆ G :=
      Finset.union_subset hbi_sub Finset.inter_subset_right
    have hleG := Finset.card_le_card hun_sub
    rw [Finset.card_union_of_disjoint hB_dis, hBG_card] at hleG
    omega

lemma runs_eq_a_sub_two {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (h1 : 0 < sitesOf S 1)
    (hr : (pcs (nxt ht) S).card = 3 * t - 2) : 3 ≤ rk ht S := by
  by_contra hlt3
  have hrk2 : rk ht S ≤ 2 := by omega
  set V := hSpace ht S
  set P := pcs (nxt ht) S
  let Ve : Submodule F2 V2 := V.comap incEven
  let Vo : Submodule F2 V2 := V.comap incOdd
  have hVe_map : Ve.map incEven = V ⊓ LinearMap.range incEven := by
    ext v; simp [Ve, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u, rfl⟩
    · rintro ⟨hv, u, rfl⟩; exact ⟨u, hv, rfl⟩
  have hVo_map : Vo.map incOdd = V ⊓ LinearMap.range incOdd := by
    ext v; simp [Vo, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u, rfl⟩
    · rintro ⟨hv, u, rfl⟩; exact ⟨u, hv, rfl⟩
  have hVe_rk : Module.finrank F2 Ve = Module.finrank F2 (Ve.map incEven) := by
    have hrng : LinearMap.range (incEven.comp Ve.subtype) = Ve.map incEven := by
      ext v; simp [LinearMap.mem_range, Submodule.mem_map]
    rw [← hrng]
    exact (LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (incEven_inj h))).symm
  have hVo_rk : Module.finrank F2 Vo = Module.finrank F2 (Vo.map incOdd) := by
    have hrng : LinearMap.range (incOdd.comp Vo.subtype) = Vo.map incOdd := by
      ext v; simp [LinearMap.mem_range, Submodule.mem_map]
    rw [← hrng]
    exact (LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (incOdd_inj h))).symm
  have hinf : Ve.map incEven ⊓ Vo.map incOdd = ⊥ := by
    rw [hVe_map, hVo_map, Submodule.eq_bot_iff]
    intro v hv
    have : v ∈ LinearMap.range incEven ⊓ LinearMap.range incOdd := ⟨hv.1.2, hv.2.2⟩
    rwa [range_incEven_inf_incOdd] at this
  have hsup_le : Ve.map incEven ⊔ Vo.map incOdd ≤ V := by
    rw [hVe_map, hVo_map]
    exact sup_le inf_le_left inf_le_left
  have hde_do : Module.finrank F2 Ve + Module.finrank F2 Vo ≤ 2 := by
    have h1' := Submodule.finrank_sup_add_finrank_inf_eq (Ve.map incEven) (Vo.map incOdd)
    rw [hinf, finrank_bot, add_zero, ← hVe_rk, ← hVo_rk] at h1'
    have h2' : Module.finrank F2 ↥(Ve.map incEven ⊔ Vo.map incOdd) ≤ Module.finrank F2 V :=
      Submodule.finrank_mono hsup_le
    change Module.finrank F2 V ≤ 2 at hrk2
    omega
  set P1 := P.filter (fun C => C.card = 1)
  set P2 := P.filter (fun C => C.card = 2)
  set P3 := P.filter (fun C => C.card = 3)
  set P4 := P.filter (fun C => 4 ≤ C.card)
  have hdef_budget : ∑ C ∈ P, (C.card - 1) ≤ 4 := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hd12 : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ a b => by omega
  have hd123 : Disjoint (P1 ∪ P2) P3 :=
    Finset.disjoint_left.mpr fun C h12 h3 => by
      simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter] at h12 h3; omega
  have hd1234 : Disjoint (P1 ∪ P2 ∪ P3) P4 :=
    Finset.disjoint_left.mpr fun C h123 h4 => by
      simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_filter] at h123 h4; omega
  have hunP : P1 ∪ P2 ∪ P3 ∪ P4 = P := by
    ext C; simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hC
      have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
      by_cases c1 : C.card = 1
      · exact Or.inl (Or.inl (Or.inl ⟨hC, c1⟩))
      by_cases c2 : C.card = 2
      · exact Or.inl (Or.inl (Or.inr ⟨hC, c2⟩))
      by_cases c3 : C.card = 3
      · exact Or.inl (Or.inr ⟨hC, c3⟩)
      exact Or.inr ⟨hC, by omega⟩
  have hP_part : P1.card + P2.card + P3.card + P4.card = 3 * t - 2 := by
    rw [← hr, ← hunP, Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12]
  have hP_def : P2.card + 2 * P3.card + 3 * P4.card ≤ 4 := by
    have hsum := hdef_budget
    rw [← hunP, Finset.sum_union hd1234, Finset.sum_union hd123, Finset.sum_union hd12] at hsum
    have s2 : ∑ C ∈ P2, (C.card - 1) = P2.card := by
      have : ∑ C ∈ P2, (C.card - 1) = ∑ _ ∈ P2, 1 :=
        Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp [this]
    have s3 : ∑ C ∈ P3, (C.card - 1) = 2 * P3.card := by
      have : ∑ C ∈ P3, (C.card - 1) = ∑ _ ∈ P3, 2 :=
        Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp [this, mul_comm]
    have s4 : 3 * P4.card ≤ ∑ C ∈ P4, (C.card - 1) := by
      have : ∑ _ ∈ P4, 3 ≤ ∑ C ∈ P4, (C.card - 1) :=
        Finset.sum_le_sum fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    omega
  have hno_even1 : Module.finrank F2 Ve = 0 → ∀ C ∈ P1, ∀ i ∈ C, i.val % 2 ≠ 0 := by
    intro h0e C hC1 i hiC hp0
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hmem : col2 (i.val / 2) ∈ Ve := by
      show incEven (col2 (i.val / 2)) ∈ V
      rw [← hVec_eq_incEven hp0]
      simpa [hCeq, hSum] using mem_hSpace ht hCP
    exact col2_ne_zero _ (congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0e) ⟨_, hmem⟩))
  have hno_odd1 : Module.finrank F2 Vo = 0 → ∀ C ∈ P1, ∀ i ∈ C, i.val % 2 ≠ 1 := by
    intro h0o C hC1 i hiC hp1
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hmem : col2 (i.val / 2) ∈ Vo := by
      show incOdd (col2 (i.val / 2)) ∈ V
      rw [← hVec_eq_incOdd hp1]
      simpa [hCeq, hSum] using mem_hSpace ht hCP
    exact col2_ne_zero _ (congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0o) ⟨_, hmem⟩))
  have hde_cases : Module.finrank F2 Ve = 0 ∨ Module.finrank F2 Ve = 1 ∨ Module.finrank F2 Ve = 2 := by omega
  have hdo_cases : Module.finrank F2 Vo = 0 ∨ Module.finrank F2 Vo = 1 ∨ Module.finrank F2 Vo = 2 := by omega
  rcases hde_cases with hde_eq | hde_eq | hde_eq <;> rcases hdo_cases with hdo_eq | hdo_eq | hdo_eq
  · have hP10 : P1 = ∅ := by
      ext C; simp only [Finset.notMem_empty, iff_false]
      intro hC1
      obtain ⟨i, hiC⟩ := populated (nxt ht) S (Finset.mem_filter.mp hC1).1
      by_cases hp : i.val % 2 = 0
      · exact hno_even1 hde_eq C hC1 i hiC hp
      · exact hno_odd1 hdo_eq C hC1 i hiC (by omega)
    rw [hP10, Finset.card_empty] at hP_part
    omega
  · have hP1_le : P1.card ≤ t := by
      obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Vo ≤ 1 by omega)
      have hwo0 : wo ≠ 0 := by
        intro hz
        have hbot : Vo = ⊥ := (Submodule.eq_bot_iff Vo).mpr fun u hu => by
          rcases hwo u hu with h | h; exact h; exact h.trans hz
        rw [hbot, finrank_bot] at hdo_eq; omega
      let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
      have hT : T.card = t := card_lane_col_eq ht 1 (by decide) wo hwo0
      have hsub : P1.biUnion id ⊆ T := by
        intro i hi
        obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
        have hp1 : i.val % 2 = 1 := by have := hno_even1 hde_eq C hC1 i hiC; omega
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
        have hmem : col2 (i.val / 2) ∈ Vo := by
          show incOdd (col2 (i.val / 2)) ∈ V
          rw [← hVec_eq_incOdd hp1]
          simpa [hCeq, hSum] using mem_hSpace ht hCP
        rcases hwo _ hmem with hz | heq
        · exact (col2_ne_zero _ hz).elim
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1, heq⟩
      have hcard_bi : (P1.biUnion id).card = P1.card := by
        rw [Finset.card_biUnion]
        · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
            Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
          simpa using this
        · intro C hC D hD hne
          exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
            (Finset.mem_filter.mp hD).1 hne
      calc P1.card = (P1.biUnion id).card := hcard_bi.symm
        _ ≤ T.card := Finset.card_le_card hsub
        _ = t := hT
    have hP2_le : P2.card ≤ t := by
      let evV : V →ₗ[F2] V2 := evenProj.comp V.subtype
      have hker_ev : LinearMap.ker evV = (Vo.map incOdd).comap V.subtype := by
        ext ⟨v, hv⟩
        simp only [LinearMap.mem_ker, evV, LinearMap.comp_apply, Submodule.coe_subtype,
          Submodule.mem_comap, hVo_map, Submodule.mem_inf, LinearMap.mem_range]
        constructor
        · intro he0
          refine ⟨hv, oddProj v, ?_⟩
          have hd := v4_decomp v
          rw [he0, map_zero, zero_add] at hd
          exact hd.symm
        · rintro ⟨_, u, hu⟩
          rw [← hu, evenProj_incOdd]
      have hker_rk : Module.finrank F2 (LinearMap.ker evV) = 1 := by
        have hsub : Vo.map incOdd ≤ LinearMap.range V.subtype := by
          rw [Submodule.range_subtype, hVo_map]; exact inf_le_left
        have hrng : ((Vo.map incOdd).comap V.subtype).map V.subtype = Vo.map incOdd :=
          Submodule.map_comap_eq_of_le hsub
        rw [hker_ev]
        have := Submodule.finrank_map_subtype_eq V ((Vo.map incOdd).comap V.subtype)
        rw [hrng] at this
        have : Module.finrank F2 (Vo.map incOdd) = 1 := hVo_rk.symm.trans hdo_eq
        omega
      have hrng_rk : Module.finrank F2 (LinearMap.range evV) ≤ 1 := by
        have h3 := LinearMap.finrank_range_add_finrank_ker evV
        rw [hker_rk] at h3
        change Module.finrank F2 (LinearMap.range evV) + 1 = rk ht S at h3
        omega
      obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w hrng_rk
      by_cases hwe0 : we = 0
      · have hP20 : P2 = ∅ := by
          ext C; simp only [Finset.notMem_empty, iff_false]
          intro hC2
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : evenProj (hSum C) ∈ LinearMap.range evV := ⟨⟨hSum C, mem_hSpace ht hCP⟩, rfl⟩
          have he0 : evenProj (hSum C) = 0 := by
            rcases hwe _ hmem with h | h; exact h; exact h.trans hwe0
          rw [harc, hc2, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at he0; omega
        rw [hP20, Finset.card_empty]; omega
      · let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) we hwe0
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : evenProj (hSum C.1) ∈ LinearMap.range evV := ⟨⟨hSum C.1, mem_hSpace ht hCP⟩, rfl⟩
          have heqW : evenProj (hSum C.1) = we := by
            rcases hwe _ hmem with h0' | h1'
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at h0'; omega
            · exact h1'
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 0
          · have hev : we = col2 (s.val / 2) := by
              rw [← heqW, hs2, hPat_eq_incEven hsp, hPat_eq_incOdd (by omega), map_add,
                evenProj_incEven, evenProj_incOdd, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hev.symm⟩
          · have hev : we = col2 ((s.val + 1) / 2) := by
              rw [← heqW, hs2, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
                evenProj_incOdd, evenProj_incEven, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; omega
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hev.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
    omega
  · have hVeq : V = LinearMap.range incOdd := by
      have hle : Vo.map incOdd ≤ V := by rw [hVo_map]; exact inf_le_left
      have hVo2 : Module.finrank F2 (Vo.map incOdd) = 2 := hVo_rk.symm.trans hdo_eq
      have hrkV : Module.finrank F2 V = 2 := by
        have := Submodule.finrank_mono hle
        change Module.finrank F2 V ≤ 2 at hrk2
        omega
      have heq1 : Vo.map incOdd = V := Submodule.eq_of_le_of_finrank_eq hle (by omega)
      have hVoTop : Vo = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hdo_eq, Module.finrank_fin_fun])
      rw [← heq1, hVoTop, Submodule.map_top]
    exact runs_a2_case_pure_odd ht ht3 hS h0 hr hVeq hdef_budget
  · have hP1_le : P1.card ≤ t := by
      obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Ve ≤ 1 by omega)
      have hwe0 : we ≠ 0 := by
        intro hz
        have hbot : Ve = ⊥ := (Submodule.eq_bot_iff Ve).mpr fun u hu => by
          rcases hwe u hu with h | h; exact h; exact h.trans hz
        rw [hbot, finrank_bot] at hde_eq; omega
      let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
      have hT : T.card = t := card_lane_col_eq ht 0 (by decide) we hwe0
      have hsub : P1.biUnion id ⊆ T := by
        intro i hi
        obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
        have hp0 : i.val % 2 = 0 := by have := hno_odd1 hdo_eq C hC1 i hiC; omega
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
        have hmem : col2 (i.val / 2) ∈ Ve := by
          show incEven (col2 (i.val / 2)) ∈ V
          rw [← hVec_eq_incEven hp0]
          simpa [hCeq, hSum] using mem_hSpace ht hCP
        rcases hwe _ hmem with hz | heq
        · exact (col2_ne_zero _ hz).elim
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0, heq⟩
      have hcard_bi : (P1.biUnion id).card = P1.card := by
        rw [Finset.card_biUnion]
        · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
            Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
          simpa using this
        · intro C hC D hD hne
          exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
            (Finset.mem_filter.mp hD).1 hne
      calc P1.card = (P1.biUnion id).card := hcard_bi.symm
        _ ≤ T.card := Finset.card_le_card hsub
        _ = t := hT
    have hP2_le : P2.card ≤ t := by
      let odV : V →ₗ[F2] V2 := oddProj.comp V.subtype
      have hker_od : LinearMap.ker odV = (Ve.map incEven).comap V.subtype := by
        ext ⟨v, hv⟩
        simp only [LinearMap.mem_ker, odV, LinearMap.comp_apply, Submodule.coe_subtype,
          Submodule.mem_comap, hVe_map, Submodule.mem_inf, LinearMap.mem_range]
        constructor
        · intro ho0
          refine ⟨hv, evenProj v, ?_⟩
          have hd := v4_decomp v
          rw [ho0, map_zero, add_zero] at hd
          exact hd.symm
        · rintro ⟨_, u, hu⟩
          rw [← hu, oddProj_incEven]
      have hker_rk : Module.finrank F2 (LinearMap.ker odV) = 1 := by
        have hsub : Ve.map incEven ≤ LinearMap.range V.subtype := by
          rw [Submodule.range_subtype, hVe_map]; exact inf_le_left
        have hrng : ((Ve.map incEven).comap V.subtype).map V.subtype = Ve.map incEven :=
          Submodule.map_comap_eq_of_le hsub
        rw [hker_od]
        have := Submodule.finrank_map_subtype_eq V ((Ve.map incEven).comap V.subtype)
        rw [hrng] at this
        have : Module.finrank F2 (Ve.map incEven) = 1 := hVe_rk.symm.trans hde_eq
        omega
      have hrng_rk : Module.finrank F2 (LinearMap.range odV) ≤ 1 := by
        have h3 := LinearMap.finrank_range_add_finrank_ker odV
        rw [hker_rk] at h3
        change Module.finrank F2 (LinearMap.range odV) + 1 = rk ht S at h3
        omega
      obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w hrng_rk
      by_cases hwo0 : wo = 0
      · have hP20 : P2 = ∅ := by
          ext C; simp only [Finset.notMem_empty, iff_false]
          intro hC2
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : oddProj (hSum C) ∈ LinearMap.range odV := ⟨⟨hSum C, mem_hSpace ht hCP⟩, rfl⟩
          have ho0 : oddProj (hSum C) = 0 := by
            rcases hwo _ hmem with h | h; exact h; exact h.trans hwo0
          rw [harc, hc2, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at ho0; omega
        rw [hP20, Finset.card_empty]; omega
      · let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
        have hT : T.card = t := card_lane_col_eq ht 1 (by decide) wo hwo0
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : oddProj (hSum C.1) ∈ LinearMap.range odV := ⟨⟨hSum C.1, mem_hSpace ht hCP⟩, rfl⟩
          have heqW : oddProj (hSum C.1) = wo := by
            rcases hwo _ hmem with h0' | h1'
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at h0'; omega
            · exact h1'
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 1
          · have hod : wo = col2 (s.val / 2) := by
              rw [← heqW, hs2, hPat_eq_incOdd hsp, hPat_eq_incEven (by omega), map_add,
                oddProj_incOdd, oddProj_incEven, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hod.symm⟩
          · have hod : wo = col2 ((s.val + 1) / 2) := by
              rw [← heqW, hs2, hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega), map_add,
                oddProj_incEven, oddProj_incOdd, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; omega
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hod.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
    omega
  · have hVeq : Ve.map incEven ⊔ Vo.map incOdd = V := by
      have h1' := Submodule.finrank_sup_add_finrank_inf_eq (Ve.map incEven) (Vo.map incOdd)
      have hVe1 : Module.finrank F2 (Ve.map incEven) = 1 := hVe_rk.symm.trans hde_eq
      have hVo1 : Module.finrank F2 (Vo.map incOdd) = 1 := hVo_rk.symm.trans hdo_eq
      rw [hinf, finrank_bot, add_zero, hVe1, hVo1] at h1'
      have h2' := Submodule.finrank_mono hsup_le
      change Module.finrank F2 V ≤ 2 at hrk2
      exact Submodule.eq_of_le_of_finrank_eq hsup_le (by omega)
    obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Ve ≤ 1 by omega)
    obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Vo ≤ 1 by omega)
    have hwe0 : we ≠ 0 := by
      intro hz
      have hbot : Ve = ⊥ := (Submodule.eq_bot_iff Ve).mpr fun u hu => by
        rcases hwe u hu with h | h; exact h; exact h.trans hz
      rw [hbot, finrank_bot] at hde_eq; omega
    have hwo0 : wo ≠ 0 := by
      intro hz
      have hbot : Vo = ⊥ := (Submodule.eq_bot_iff Vo).mpr fun u hu => by
        rcases hwo u hu with h | h; exact h; exact h.trans hz
      rw [hbot, finrank_bot] at hdo_eq; omega
    have hV_proj : ∀ v ∈ V, (evenProj v = 0 ∨ evenProj v = we) ∧ (oddProj v = 0 ∨ oddProj v = wo) := by
      intro v hv
      rw [← hVeq, Submodule.mem_sup] at hv
      obtain ⟨_, ⟨ue, hue, rfl⟩, _, ⟨uo, huo, rfl⟩, rfl⟩ := hv
      rw [map_add, evenProj_incEven, evenProj_incOdd, add_zero,
        map_add, oddProj_incEven, oddProj_incOdd, zero_add]
      exact ⟨hwe ue hue, hwo uo huo⟩
    exact runs_a2_case_11 ht ht3 hS hwe0 hwo0 hV_proj hP_part hP_def
  · omega
  · have hVeq : V = LinearMap.range incEven := by
      have hle : Ve.map incEven ≤ V := by rw [hVe_map]; exact inf_le_left
      have hVe2 : Module.finrank F2 (Ve.map incEven) = 2 := hVe_rk.symm.trans hde_eq
      have hrkV : Module.finrank F2 V = 2 := by
        have := Submodule.finrank_mono hle
        change Module.finrank F2 V ≤ 2 at hrk2
        omega
      have heq1 : Ve.map incEven = V := Submodule.eq_of_le_of_finrank_eq hle (by omega)
      have hVeTop : Ve = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hde_eq, Module.finrank_fin_fun])
      rw [← heq1, hVeTop, Submodule.map_top]
    exact runs_a2_case_pure_even ht ht3 hS h1 hr hVeq hdef_budget
  · omega
  · omega

def thresh (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 2 else 3 * t - 5

lemma mixed_finrank_le {U : Submodule F2 (W t)} (hg : goodU ht U)
    (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1) :
    Module.finrank F2 U ≤ thresh t := by
  by_cases hS : suppU U = Finset.univ
  · have hle := finrank_le_one_of_supp_univ ht hg hS
    unfold thresh; split_ifs <;> omega
  · have hbound := finrank_add_rk_le_runs ht hg
    have hlt := runs_lt_a ht hS h0 h1
    set r := (pcs (nxt ht) (suppU U)).card
    set k := rk ht (suppU U)
    unfold thresh
    split_ifs with ht1 ht2
    · subst ht1
      by_cases hr2 : r = 2
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      · omega
    · subst ht2
      by_cases hr5 : r = 5
      · have hk4 := runs_eq_a_sub_one ht (by decide) hg hS h0 h1 hr5; omega
      by_cases hr4 : r = 4
      · have hk2 : ¬ k ≤ 1 := fun hk => by have := rk_le_one_runs ht hS hk; omega
        omega
      by_cases hr3 : r = 3
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      omega
    · have ht3 : 3 ≤ t := by omega
      by_cases hr1 : r = 3 * t - 1
      · have hk4 := runs_eq_a_sub_one ht (by omega) hg hS h0 h1 hr1; omega
      by_cases hr2 : r = 3 * t - 2
      · have hk3 := runs_eq_a_sub_two ht ht3 hS h0 h1 hr2; omega
      by_cases hr3 : r = 3 * t - 3
      · have hk2 : ¬ k ≤ 1 := fun hk => by have := rk_le_one_runs ht hS hk; omega
        omega
      by_cases hr4 : r = 3 * t - 4
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      omega

end UpperBounds
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
end Old
namespace Geometry

open scoped Classical
abbrev F := ZMod 2
abbrev W (ι : Type*) := ι → F

variable {ι κ : Type*} [Fintype ι]
variable (next : ι → ι) (h : ι → κ → F)

def Good (U : Submodule F (W ι)) : Prop :=
  (∀ x ∈ U, ∀ b, ∑ i, h i b * x i = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)

noncomputable def support (U : Submodule F (W ι)) : Finset ι :=
  Finset.univ.filter fun i => ∃ x ∈ U, x i ≠ 0

lemma mem_support (U : Submodule F (W ι)) (i : ι) :
    i ∈ support U ↔ ∃ x ∈ U, x i ≠ 0 := by simp [support]

lemma support_mono {U V : Submodule F (W ι)} (huv : U ≤ V) : support U ⊆ support V := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_support U i).mp hi
  exact (mem_support V i).mpr ⟨x,huv hx,hxi⟩

lemma bit_one {z : F} (hz : z ≠ 0) : z = 1 := by
  fin_cases z <;> first | rfl | contradiction

lemma adjacent_equal {U : Submodule F (W ι)} (hg : Good next h U)
    {i : ι} (hi : i ∈ support U) (hn : next i ∈ support U)
    {x : W ι} (hx : x ∈ U) : x i = x (next i) := by
  obtain ⟨u, hu, hui⟩ := (mem_support _ _).mp hi
  obtain ⟨v, hv, hvn⟩ := (mem_support _ _).mp hn
  have hu1 := bit_one hui
  have hv1 := bit_one hvn
  have hcheck := hg.2 u hu v hv i
  have hun : u (next i) ≠ 0 := by
    intro hz
    simp [hu1, hv1, hz] at hcheck
  have hu2 := bit_one hun
  simpa [hu1, hu2] using hg.2 x hx u hu i

def kernel (S : Finset ι) : Submodule F (W ι) where
  carrier := {x | (∀ b, ∑ i, h i b * x i = 0) ∧
    (∀ i, i ∉ S → x i = 0) ∧ (∀ i, i ∈ S → next i ∈ S → x i = x (next i))}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro b
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx.1 b, hy.1 b, zero_add]
    · intro i hi
      simp [hx.2.1 i hi, hy.2.1 i hi]
    · intro i hi hn
      simp [hx.2.2 i hi hn, hy.2.2 i hi hn]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro b
      calc
        (∑ i, h i b * (c • x) i) = ∑ i, c * (h i b * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          change h i b * (c * x i) = c * (h i b * x i)
          ring
        _ = 0 := by rw [← Finset.mul_sum, hx.1 b, mul_zero]
    · intro i hi
      simp [hx.2.1 i hi]
    · intro i hi hn
      simp [hx.2.2 i hi hn]

lemma good_kernel (S : Finset ι) : Good next h (kernel next h S) := by
  constructor
  · intro x hx
    exact hx.1
  · intro x hx y hy i
    by_cases hi : i ∈ S
    · by_cases hn : next i ∈ S
      · rw [hx.2.2 i hi hn, hy.2.2 i hi hn]
      · rw [hx.2.1 _ hn, hy.2.1 _ hn, mul_zero, zero_mul]
    · rw [hx.2.1 _ hi, hy.2.1 _ hi, zero_mul, mul_zero]

lemma le_kernel {U : Submodule F (W ι)} (hg : Good next h U) :
    U ≤ kernel next h (support U) := by
  intro x hx
  refine ⟨hg.1 x hx, ?_, ?_⟩
  · intro i hi
    by_contra hne
    exact hi ((mem_support _ _).mpr ⟨x,hx,hne⟩)
  · intro i hi hn
    exact adjacent_equal next h hg hi hn hx

lemma support_kernel_subset (S : Finset ι) : support (kernel next h S) ⊆ S := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_support _ _).mp hi
  by_contra hn
  exact hxi (hx.2.1 i hn)

lemma support_kernel {U : Submodule F (W ι)} (hg : Good next h U) :
    support (kernel next h (support U)) = support U :=
  Finset.Subset.antisymm (support_kernel_subset next h _) (support_mono (le_kernel next h hg))

theorem unique_at_max {U : Submodule F (W ι)} (hg : Good next h U)
    (maximal : ∀ V, Good next h V → support V = support U →
      Module.finrank F V ≤ Module.finrank F U) :
    kernel next h (support U) = U := by
  have hle := le_kernel next h hg
  have hdim := maximal _ (good_kernel next h _) (support_kernel next h hg)
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (Nat.le_antisymm (Submodule.finrank_mono hle) hdim)).symm

theorem common_max {U V : Submodule F (W ι)} (hu : Good next h U) (hv : Good next h V)
    (hs : support V = support U) (hr : Module.finrank F V = Module.finrank F U)
    (maximal : ∀ E, Good next h E → support E = support U →
      Module.finrank F E ≤ Module.finrank F U) : V = U := by
  have hle := le_kernel next h hv
  rw [hs, unique_at_max next h hu maximal] at hle
  exact Submodule.eq_of_le_of_finrank_eq hle hr

end Geometry

open Finset
open scoped Classical

def singleHost {α β : Type*} (P : Finset (α × β)) (same : α → β → Prop) (p : α × β) : Prop :=
  same p.1 p.2 ∧ ∀ a, (a,p.2) ∈ P → a = p.1

theorem incidence_mass {α β : Type*} (P : Finset (α × β)) (L : Finset β)
    (same : α → β → Prop)
    (valid : ∀ a b, (a,b) ∈ P → same a b → b ∈ L) :
    let exceptional := L.filter (fun b => ¬ ∃ a, (a,b) ∈ P ∧ singleHost P same (a,b))
    let bad := P.filter (fun p => ¬ singleHost P same p)
    let withoutHost := L.filter (fun b => ¬ ∃ a, (a,b) ∈ P)
    Nat.dist L.card P.card + exceptional.card ≤ 3*bad.card + 2*withoutHost.card := by
  classical
  intro exceptional bad withoutHost
  let G := P.filter (singleHost P same)
  let normal := L.filter (fun b => ∃ a, (a,b) ∈ P ∧ singleHost P same (a,b))
  have hn : normal = G.image Prod.snd := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,hab,hg⟩ := (mem_filter.mp hb).2
      exact mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨hab,hg⟩,rfl⟩
    · intro hb
      obtain ⟨⟨a,y⟩,hp,rfl⟩ := mem_image.mp hb
      obtain ⟨hab,hg⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨valid a y hab hg.1, a, hab, hg⟩
  have hni : Set.InjOn Prod.snd (↑G : Set (α × β)) := by
    rintro ⟨a,x⟩ hx ⟨a',y⟩ hy he
    dsimp only at he
    subst y
    have hax := (mem_filter.mp hx).2.2 a' (mem_filter.mp hy).1
    exact Prod.ext hax.symm rfl
  have hncard : normal.card = G.card := by rw [hn, card_image_of_injOn hni]
  have hl : normal.card + exceptional.card = L.card :=
    card_filter_add_card_filter_not (s := L) _
  have hp : G.card + bad.card = P.card := card_filter_add_card_filter_not (s := P) _
  have hs : exceptional ⊆ bad.image Prod.snd ∪ withoutHost := by
    intro b hb
    obtain ⟨hbL,ex⟩ := mem_filter.mp hb
    by_cases h : ∃ a, (a,b) ∈ P
    · obtain ⟨a,ha⟩ := h
      exact mem_union_left _ (mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨ha,fun g => ex ⟨a,ha,g⟩⟩,rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hbL,h⟩)
  have hbad : exceptional.card ≤ bad.card + withoutHost.card :=
    (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _))
  unfold Nat.dist
  omega

theorem twice_tail (s : ℕ → ℕ) (N : ℕ) (h : ∀ i < N, 2*s (i+1) ≤ s i) :
    (∑ i ∈ range (N+1), s i) + s N ≤ 2 * s 0 := by
  induction N with
  | zero => simp; omega
  | succ N ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h N (by omega)
    rw [sum_range_succ]
    omega

theorem weighted_tail (g : ℕ → ℕ) {z q N : ℕ} (hz : 2*z ≤ q)
    (hg : ∀ i ≤ N, q*g (i+1) ≤ g i) :
    q * (∑ i ∈ range (N+1), z^(i+1)*g (i+1)) ≤ 2*z*g 0 := by
  let s := fun i => z^(i+1)*g (i+1)
  have hs (i : ℕ) (hi : i < N) : 2*s (i+1) ≤ s i := by
    have hh := (Nat.mul_le_mul_right (g (i+1+1)) hz).trans (hg (i+1) (by omega))
    calc
      2*s (i+1) = z^(i+1) * ((2*z)*g (i+1+1)) := by dsimp [s]; rw [pow_succ z (i+1)]; ring
      _ ≤ z^(i+1) * g (i+1) := Nat.mul_le_mul_left _ hh
      _ = s i := rfl
  have ht := twice_tail s N hs
  have hsum : (∑ i ∈ range (N+1), s i) ≤ 2*s 0 := by omega
  calc
    _ ≤ q*(2*s 0) := Nat.mul_le_mul_left _ hsum
    _ = 2*z*(q*g 1) := by simp [s]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (hg 0 (by omega))

open Finset

def nextSite {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def equalEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i => (i ∈ S ↔ nextSite i ∈ S))

def encode {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Bool × Finset (Fin n) :=
  (decide ((⟨0,hn⟩ : Fin n) ∈ S), equalEdges S)

theorem encode_injective {n : ℕ} (hn : 0 < n) : Function.Injective (encode hn) := by
  intro S T he
  have h0 : ((⟨0,hn⟩ : Fin n) ∈ S) ↔ (⟨0,hn⟩ : Fin n) ∈ T := by
    have h := congrArg Prod.fst he
    simpa [encode] using h
  have hd : equalEdges S = equalEdges T := congrArg Prod.snd he
  have step (i : Fin n) (h : i ∈ S ↔ i ∈ T) : nextSite i ∈ S ↔ nextSite i ∈ T := by
    have hh : (i ∈ S ↔ nextSite i ∈ S) ↔ (i ∈ T ↔ nextSite i ∈ T) := by
      have hm : i ∈ equalEdges S ↔ i ∈ equalEdges T := by rw [hd]
      simpa [equalEdges] using hm
    tauto
  have go (k : ℕ) (hk : k < n) : (⟨k,hk⟩ : Fin n) ∈ S ↔ (⟨k,hk⟩ : Fin n) ∈ T := by
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < n := by omega
      have hs := step ⟨k,hk'⟩ (ih hk')
      have heq : nextSite (⟨k,hk'⟩ : Fin n) = ⟨k+1,hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rwa [heq] at hs
  ext i
  exact go i.val i.isLt

lemma small_subsets (n k : ℕ) (hn : 2 ≤ n) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)).card ≤ 2*n^k := by
  let sets := fun j => (univ : Finset (Fin n)).powersetCard j
  have hsub : (univ.filter (fun S : Finset (Fin n) => S.card ≤ k)) ⊆
      (range (k+1)).biUnion sets := by
    intro S hS
    exact mem_biUnion.mpr ⟨S.card, mem_range.mpr (by have := (mem_filter.mp hS).2; omega),
      mem_powersetCard.mpr ⟨subset_univ _,rfl⟩⟩
  have hsum : ∀ m : ℕ, (∑ j ∈ range (m+1), n^j) ≤ 2*n^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hpow : 2*n^m ≤ n^(m+1) := by
        rw [pow_succ, Nat.mul_comm (n^m)]
        exact Nat.mul_le_mul_right _ hn
      omega
  calc
    _ ≤ ((range (k+1)).biUnion sets).card := card_le_card hsub
    _ ≤ ∑ j ∈ range (k+1), (sets j).card := card_biUnion_le
    _ ≤ ∑ j ∈ range (k+1), n^j := by
      apply sum_le_sum
      intro j _
      simpa [sets] using Nat.choose_le_pow n j
    _ ≤ _ := hsum _

theorem count_supports {n k : ℕ} (hn : 2 ≤ n) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => (equalEdges S).card ≤ k)).card ≤
      4*n^k := by
  have hp : 0 < n := by omega
  let small := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)
  have hle : ((univ : Finset (Finset (Fin n))).filter
      (fun S => (equalEdges S).card ≤ k)).card ≤ ((univ : Finset Bool).product small).card := by
    apply card_le_card_of_injOn (encode hp)
    · intro S hS
      exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hS).2⟩⟩
    · exact (encode_injective hp).injOn
  have hs := small_subsets n k hn
  calc
    _ ≤ ((univ : Finset Bool).product small).card := hle
    _ = (univ : Finset Bool).card * small.card := card_product _ _
    _ = 2*small.card := by simp
    _ ≤ 2*(2*n^k) := Nat.mul_le_mul_left 2 hs
    _ = _ := by ring


abbrev Bin := ZMod 2
abbrev Plane (A : Type*) [AddCommGroup A] [Module Bin A] (d : ℕ) :=
  { U : Submodule Bin A // Module.finrank Bin U = d }

variable {A B : Type*} [AddCommGroup A] [Module Bin A] [FiniteDimensional Bin A]
variable [AddCommGroup B] [Module Bin B] [FiniteDimensional Bin B]

def pairMap (U : Submodule Bin A) (f : U →ₗ[Bin] B) : U →ₗ[Bin] A × B := U.subtype.prod f

lemma pairMap_inj (U : Submodule Bin A) (f : U →ₗ[Bin] B) :
    Function.Injective (pairMap U f) := by
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

def toPlane {d : ℕ} (p : (U : Plane A d) × (U.val →ₗ[Bin] B)) : Plane (A × B) d :=
  ⟨LinearMap.range (pairMap p.1.val p.2),
    (LinearMap.finrank_range_of_inj (pairMap_inj p.1.val p.2)).trans p.1.property⟩

lemma pair_le {U V : Submodule Bin A} (f : U →ₗ[Bin] B) (g : V →ₗ[Bin] B)
    (hle : LinearMap.range (pairMap U f) ≤ LinearMap.range (pairMap V g)) : U ≤ V := by
  intro x hx
  obtain ⟨v,hv⟩ := hle (LinearMap.mem_range_self (pairMap U f) ⟨x,hx⟩)
  have he : (v : A) = x := congrArg Prod.fst hv
  exact he ▸ v.property

lemma toPlane_injective (d : ℕ) :
    Function.Injective (toPlane (A := A) (B := B) (d := d)) := by
  rintro ⟨U,f⟩ ⟨V,g⟩ hh
  have hr : LinearMap.range (pairMap U.val f) = LinearMap.range (pairMap V.val g) :=
    congrArg Subtype.val hh
  have huv : U = V := Subtype.ext (le_antisymm (pair_le f g hr.le) (pair_le g f hr.ge))
  subst V
  suffices fe : f = g by subst g; rfl
  ext u
  obtain ⟨v,hv⟩ := hr.le (LinearMap.mem_range_self (pairMap U.val f) u)
  have he : v = u := Subtype.ext (congrArg Prod.fst hv)
  subst v
  exact (congrArg Prod.snd hv).symm

theorem grass_product (A B : Type*) [AddCommGroup A] [Module Bin A] [FiniteDimensional Bin A]
    [Finite A] [AddCommGroup B] [Module Bin B] [FiniteDimensional Bin B] [Finite B] (d : ℕ) :
    Nat.card (Plane A d) * 2 ^ (d * Module.finrank Bin B) ≤ Nat.card (Plane (A × B) d) := by
  classical
  letI : Fintype (Plane A d) := Fintype.ofFinite _
  letI (U : Plane A d) : Finite (U.val →ₗ[Bin] B) :=
    Finite.of_injective (fun f : U.val →ₗ[Bin] B => (f : U.val → B)) DFunLike.coe_injective
  have hf (U : Plane A d) : Nat.card (U.val →ₗ[Bin] B) = 2 ^ (d * Module.finrank Bin B) := by
    letI : Fintype (U.val →ₗ[Bin] B) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bin), ZMod.card,
      Module.finrank_linearMap, U.property]
  have hi := Nat.card_le_card_of_injective _ (toPlane_injective (A := A) (B := B) d)
  rw [Nat.card_sigma] at hi
  simpa [hf, Nat.card_eq_fintype_card] using hi

section Transport
open Finset
open scoped Classical

variable {X Y : Type*} [AddCommGroup X] [Module Bin X] [FiniteDimensional Bin X]
  [AddCommGroup Y] [Module Bin Y] [FiniteDimensional Bin Y]

lemma map_rank (f : X →ₗ[Bin] Y) (hi : Function.Injective f) (U : Submodule Bin X) :
    Module.finrank Bin (U.map f) = Module.finrank Bin U := by
  have hr : (f.comp U.subtype).range = U.map f := by
    ext x
    simp [LinearMap.mem_range, Submodule.mem_map]
  rw [←hr,LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (hi h))]

def plane_push (f : X →ₗ[Bin] Y) (hi : Function.Injective f) {d : ℕ} :
    Plane X d → Plane Y d :=
  fun U => ⟨U.val.map f,(map_rank f hi _).trans U.property⟩

lemma plane_push_inj (f : X →ₗ[Bin] Y) (hi : Function.Injective f) (d : ℕ) :
    Function.Injective (plane_push f hi (d := d)) := by
  intro U V hh
  have hm : U.val.map f = V.val.map f := congrArg Subtype.val hh
  apply Subtype.ext
  simpa only [Submodule.comap_map_eq_of_injective hi] using congrArg (Submodule.comap f) hm

lemma plane_card_congr [Finite X] [Finite Y] (h : Module.finrank Bin X = Module.finrank Bin Y) (d : ℕ) :
    Nat.card (Plane X d) = Nat.card (Plane Y d) := by
  let e : X ≃ₗ[Bin] Y := LinearEquiv.ofFinrankEq _ _ h
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_injective _ (plane_push_inj e.toLinearMap e.injective d)
  · exact Nat.card_le_card_of_injective _ (plane_push_inj e.symm.toLinearMap e.symm.injective d)

abbrev G (k d : ℕ) := Nat.card (Plane (Fin k → Bin) d)

theorem grass_gap {k D : ℕ} (h : k ≤ D) (d : ℕ) : G k d * (2^d)^(D-k) ≤ G D d := by
  let X := Fin k → Bin
  let Y := Fin (D-k) → Bin
  have hh : Module.finrank Bin (X × Y) = Module.finrank Bin (Fin D → Bin) := by
    simp only [X,Y,Module.finrank_prod,Module.finrank_fin_fun]
    omega
  have hi := grass_product X Y d
  rw [plane_card_congr hh d] at hi
  simpa only [G,X,Y,Module.finrank_fin_fun,←pow_mul] using hi

noncomputable def slice [Finite X] (E : Submodule Bin X) (d : ℕ) : Finset (Submodule Bin X) :=
  letI : Fintype (Submodule Bin X) := Fintype.ofFinite _
  univ.filter fun U : Submodule Bin X => Module.finrank Bin U = d ∧ U ≤ E

lemma mem_slice [Finite X] {U E : Submodule Bin X} {d : ℕ} :
    U ∈ slice E d ↔ Module.finrank Bin U = d ∧ U ≤ E := by simp [slice]

theorem slice_card [Finite X] (E : Submodule Bin X) (d : ℕ) :
    (slice E d).card = G (Module.finrank Bin E) d := by
  classical
  let f := E.subtype
  have hi : Function.Injective f := Subtype.val_injective
  let e : Plane E d ≃ ↥(slice E d) :=
    { toFun := fun U => ⟨U.val.map f, mem_slice.mpr ⟨(map_rank f hi _).trans U.property, by
        rintro _ ⟨x, _, rfl⟩
        exact x.property⟩⟩
      invFun := fun U => ⟨U.val.comap f, by
        have hle : U.val ≤ f.range := by
          intro x hx
          exact ⟨⟨x,(mem_slice.mp U.property).2 hx⟩,rfl⟩
        have hr := map_rank f hi (U.val.comap f)
        rw [Submodule.map_comap_eq_of_le hle, (mem_slice.mp U.property).1] at hr
        exact hr.symm⟩
      left_inv := fun U => Subtype.ext (Submodule.comap_map_eq_of_injective hi _)
      right_inv := fun U => Subtype.ext (Submodule.map_comap_eq_of_le (by
        intro x hx
        exact ⟨⟨x,(mem_slice.mp U.property).2 hx⟩,rfl⟩)) }
  calc
    (slice E d).card = Nat.card ↥(slice E d) := by simp
    _ = Nat.card (Plane E d) := Nat.card_congr e.symm
    _ = _ := plane_card_congr (by rw [Module.finrank_fin_fun]) d

theorem proper_slice [Finite X] {E F : Submodule Bin X} (h : E < F) (d : ℕ) :
    2^d * (slice E d).card ≤ (slice F d).card := by
  have hr : Module.finrank Bin E < Module.finrank Bin F :=
    lt_of_le_of_ne (Submodule.finrank_mono h.le) (fun e => h.ne (Submodule.eq_of_le_of_finrank_eq h.le e))
  rw [slice_card,slice_card,mul_comm]
  refine (Nat.mul_le_mul_left _ ?_).trans (grass_gap hr.le d)
  calc
    2^d = (2^d)^1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by omega)
end Transport


section BadInc
open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι]
abbrev Ambient (ι : Type*) := ι → Bin
noncomputable def suppB (E : Submodule Bin (Ambient ι)) : Finset ι :=
  univ.filter (fun i => ∃ x ∈ E, x i ≠ 0)
lemma suppB_mono {E V : Submodule Bin (Ambient ι)} (hle : V ≤ E) : suppB V ⊆ suppB E := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _,x,hle hx,hxi⟩

def silent (i : ι) : Submodule Bin (Ambient ι) where
  carrier := {x | x i = 0}
  zero_mem' := rfl
  add_mem' := fun {x y} hx hy => by change x i + y i = 0; rw [hx,hy,add_zero]
  smul_mem' := fun c x hx => by change c * x i = 0; rw [hx,mul_zero]

lemma joint_cost {α β : Type*} [DecidableEq β] (T : Finset α) (g : α → Finset β) (q C : ℕ)
    (h : ∀ x ∈ T, q*(g x).card ≤ C) : q*(T.biUnion g).card ≤ T.card*C := by
  calc
    _ ≤ q*(∑ x ∈ T,(g x).card) := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ x ∈ T,q*(g x).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _x ∈ T,C := sum_le_sum h
    _ = _ := by simp

noncomputable def badInside (T : Finset (Submodule Bin (Ambient ι)))
    (E : Submodule Bin (Ambient ι)) (d : ℕ) : Finset (Submodule Bin (Ambient ι)) :=
  (slice E d).filter (fun U => suppB U ≠ suppB E ∨ ∃ F ∈ T, F ≠ E ∧ U ≤ F)

theorem cost_badInside (T : Finset (Submodule Bin (Ambient ι))) (E : Submodule Bin (Ambient ι))
    (d : ℕ) (ht : ∀ F ∈ T, Module.finrank Bin F = Module.finrank Bin E) :
    2^d*(badInside T E d).card ≤ (Fintype.card ι+T.card)*(slice E d).card := by
  classical
  let S := suppB E
  let C := fun i => slice (E ⊓ silent i) d
  let V := fun F => slice (E ⊓ F) d
  have hc (i : ι) (hi : i ∈ S) : 2^d*(C i).card ≤ (slice E d).card := by
    apply proper_slice
    apply lt_of_le_of_ne inf_le_left
    intro eq
    obtain ⟨x,hx,hxi⟩ := (mem_filter.mp hi).2
    have hmem : x ∈ E ⊓ silent i := eq.symm ▸ hx
    exact hxi hmem.2
  have hv (F : Submodule Bin (Ambient ι)) (hF : F ∈ T.erase E) :
      2^d*(V F).card ≤ (slice E d).card := by
    apply proper_slice
    apply lt_of_le_of_ne inf_le_left
    intro eq
    have hle : E ≤ F := eq ▸ (inf_le_right : E ⊓ F ≤ F)
    exact (mem_erase.mp hF).1 (Submodule.eq_of_le_of_finrank_eq hle (ht F (mem_erase.mp hF).2).symm).symm
  have sub : badInside T E d ⊆ S.biUnion C ∪ (T.erase E).biUnion V := by
    intro U hU
    obtain ⟨hs,hbad⟩ := mem_filter.mp hU
    obtain ⟨hd,hle⟩ := mem_slice.mp hs
    rcases hbad with h | ⟨F,hFT,hFE,hUF⟩
    · have hw : ∃ i ∈ S, i ∉ suppB U := by
        by_contra! hh
        exact h (Finset.Subset.antisymm (suppB_mono hle) hh)
      obtain ⟨i,hi,hn⟩ := hw
      apply mem_union_left
      refine mem_biUnion.mpr ⟨i,hi,mem_slice.mpr ⟨hd,le_inf hle ?_⟩⟩
      intro x hx
      change x i = 0
      by_contra hne
      exact hn (mem_filter.mpr ⟨mem_univ _,x,hx,hne⟩)
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨F,mem_erase.mpr ⟨hFE,hFT⟩,mem_slice.mpr ⟨hd,le_inf hle hUF⟩⟩
  have h1 := joint_cost S C (2^d) _ hc
  have h2 := joint_cost (T.erase E) V (2^d) _ hv
  have hcard1 : S.card ≤ Fintype.card ι := card_le_univ S
  have hcard2 : (T.erase E).card ≤ T.card := card_le_card (erase_subset _ _)
  calc
    _ ≤ 2^d*((S.biUnion C).card+((T.erase E).biUnion V).card) :=
      Nat.mul_le_mul_left _ ((card_le_card sub).trans (card_union_le _ _))
    _ ≤ (S.card+(T.erase E).card)*(slice E d).card := by
      rw [Nat.mul_add,Nat.add_mul]
      exact Nat.add_le_add h1 h2
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add hcard1 hcard2)
end BadInc

section DeepBound
open Finset
open scoped Classical

theorem deep_count {n D d : ℕ} (hn : 2 ≤ n) (hwidth : 2*n^2 ≤ 2^d)
    (K : Finset (Fin n) → Submodule Bin (Fin n → Bin)) (L : Finset (Submodule Bin (Fin n → Bin)))
    (cover : ∀ U ∈ L, ∃ j < D, ∃ S : Finset (Fin n),
      (equalEdges S).card ≤ 10 + 2*(j+1) ∧
      Module.finrank Bin (K S) = D-(j+1) ∧ U ∈ slice (K S) d) :
    2^d * L.card ≤ 8*n^12*G D d := by
  classical
  let sources := fun j => (univ : Finset (Finset (Fin n))).filter (fun S =>
      (equalEdges S).card ≤ 10+2*(j+1) ∧ Module.finrank Bin (K S) = D-(j+1))
  let bucket := fun j => (sources j).biUnion (fun S => slice (K S) d)
  have hsub : L ⊆ (range D).biUnion bucket := by
    intro U hU
    obtain ⟨j,hj,S,he,hr,hmem⟩ := cover U hU
    exact mem_biUnion.mpr ⟨j,mem_range.mpr hj, mem_biUnion.mpr
      ⟨S,mem_filter.mpr ⟨mem_univ _,he,hr⟩,hmem⟩⟩
  have hsource (j : ℕ) : (sources j).card ≤ 4*n^(10+2*(j+1)) := by
    refine (card_le_card ?_).trans (count_supports (k := 10+2*(j+1)) hn)
    intro S hS
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hS).2.1⟩
  let g := fun j => G (D-j) d
  have hbucket (j : ℕ) : (bucket j).card ≤ 4*n^10 * ((n^2)^(j+1)*g (j+1)) := by
    calc
      _ ≤ ∑ S ∈ sources j, (slice (K S) d).card := card_biUnion_le
      _ = ∑ _S ∈ sources j, g (j+1) := by
        apply sum_congr rfl
        intro S hs
        rw [slice_card,(mem_filter.mp hs).2.2]
      _ = (sources j).card * g (j+1) := by simp
      _ ≤ (4*n^(10+2*(j+1))) * g (j+1) := Nat.mul_le_mul_right _ (hsource j)
      _ = _ := by rw [pow_add,pow_mul]; ring
  have hsum : L.card ≤ (4*n^10) * ∑ j ∈ range D,(n^2)^(j+1)*g (j+1) := by
    rw [Finset.mul_sum]
    exact (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum (fun j _ => hbucket j)))
  have hsteps (j : ℕ) (hj : j < D) : 2^d * g (j+1) ≤ g j := by
    have hgap := grass_gap (k := D-(j+1)) (D := D-j) (by omega) d
    have hone : D-j-(D-(j+1)) = 1 := by omega
    simpa only [g,hone,pow_one,mul_comm] using hgap
  have hsmall : 2^d * (∑ j ∈ range D,(n^2)^(j+1)*g (j+1)) ≤ 2*n^2*g 0 := by
    cases D with
    | zero => simp
    | succ m =>
      exact weighted_tail g hwidth (fun j hj => hsteps j (by omega))
  calc
    _ ≤ 2^d*((4*n^10)*∑ j ∈ range D,(n^2)^(j+1)*g (j+1)) := Nat.mul_le_mul_left _ hsum
    _ = (4*n^10)*(2^d*∑ j ∈ range D,(n^2)^(j+1)*g (j+1)) := by ring
    _ ≤ (4*n^10)*(2*n^2*g 0) := Nat.mul_le_mul_left _ hsmall
    _ = _ := by simp only [g,Nat.sub_zero]; ring

end DeepBound

section Pairs
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]
abbrev ModSpace (ι : Type*) := Submodule Bin (Ambient ι)

noncomputable def pairs (T : Finset (ModSpace ι)) (d : ℕ) : Finset (ModSpace ι × ModSpace ι) :=
  T.biUnion fun E => (slice E d).image (Prod.mk E)

lemma mem_pairs (T : Finset (ModSpace ι)) {d : ℕ} {E U : ModSpace ι} :
    (E,U) ∈ pairs T d ↔ E ∈ T ∧ U ∈ slice E d := by simp [pairs]

theorem pairs_card (T : Finset (ModSpace ι)) {D d : ℕ}
    (ht : ∀ E ∈ T, Module.finrank Bin E = D) :
    (pairs T d).card = T.card * G D d := by
  classical
  unfold pairs
  rw [card_biUnion]
  · calc
      _ = ∑ _E ∈ T,G D d := by
        apply sum_congr rfl
        intro E he
        rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),slice_card,ht E he]
      _ = _ := by simp
  · intro E _ F _ hne
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨U,_,rfl⟩ := mem_image.mp hp
    obtain ⟨V,_,hh⟩ := mem_image.mp hq
    exact hne (congrArg Prod.fst hh).symm

theorem pairs_bad_cost (T : Finset (ModSpace ι)) {D d : ℕ}
    (ht : ∀ E ∈ T, Module.finrank Bin E = D) :
    2^d * ((pairs T d).filter
        (fun p => ¬singleHost (pairs T d) (fun E U => suppB U = suppB E) p)).card ≤
      T.card*((Fintype.card ι+T.card)*G D d) := by
  classical
  let b := fun E : ModSpace ι => (badInside T E d).image (Prod.mk E)
  have hcost (E : ModSpace ι) (hE : E ∈ T) :
      2^d*(b E).card ≤ (Fintype.card ι+T.card)*G D d := by
    have h := cost_badInside T E d (fun F hf => (ht F hf).trans (ht E hE).symm)
    simpa only [b,card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),slice_card,ht E hE] using h
  refine (Nat.mul_le_mul_left _ (card_le_card ?_)).trans (joint_cost T b (2^d) _ hcost)
  rintro ⟨E,U⟩ hp
  obtain ⟨hpair,hbad⟩ := mem_filter.mp hp
  obtain ⟨hE,hU⟩ := (mem_pairs T).mp hpair
  refine mem_biUnion.mpr ⟨E,hE,mem_image.mpr ⟨U,mem_filter.mpr ⟨hU,?_⟩,rfl⟩⟩
  by_cases hs : suppB U = suppB E
  · right
    by_contra! hall
    apply hbad
    refine ⟨hs,?_⟩
    intro F hF
    by_contra hne
    obtain ⟨hFT,hFU⟩ := (mem_pairs T).mp hF
    exact hall F hFT hne (mem_slice.mp hFU).2
  · exact Or.inl hs
end Pairs
section MainCount
open Finset
open scoped Classical

theorem concentration_of_cover {n D d C : ℕ} (hn : 2 ≤ n) (hwide : 2*n^2 ≤ 2^d)
    (K : Finset (Fin n) → ModSpace (Fin n)) (T L : Finset (ModSpace (Fin n)))
    (hcard : T.card = C) (hdim : ∀ E ∈ T, Module.finrank Bin E = D)
    (valid : ∀ E U, E ∈ T → U ∈ slice E d → suppB U = suppB E → U ∈ L)
    (cover : ∀ U ∈ L, (∀ E ∈ T, ¬ U ≤ E) → ∃ j < D, ∃ S : Finset (Fin n),
      (equalEdges S).card ≤ 10+2*(j+1) ∧ Module.finrank Bin (K S) = D-(j+1) ∧ U ∈ slice (K S) d)
    (hL : ∀ U ∈ L, Module.finrank Bin U = d)
    (hcst : 3*(C*((n+C)*G D d))+2*(8*n^12*G D d) ≤ 32*n^10*(C*G D d)) :
    let ex := L.filter (fun U => ¬∃ E ∈ T, U ≤ E ∧ suppB U = suppB E ∧
      ∀ E' ∈ T, U ≤ E' → E' = E)
    (Nat.dist L.card (C*G D d) + ex.card)*2^d ≤ 32*n^10*(C*G D d) := by
  classical
  intro ex
  let P := pairs T d
  let same := fun E U : ModSpace (Fin n) => suppB U = suppB E
  let X := L.filter (fun U => ¬ ∃ E, (E,U) ∈ P ∧ singleHost P same (E,U))
  let B := P.filter (fun p => ¬singleHost P same p)
  let Z := L.filter (fun U => ¬∃ E, (E,U) ∈ P)
  have hmass : Nat.dist L.card P.card + X.card ≤ 3*B.card+2*Z.card :=
    incidence_mass P L same (fun E U hp hs => valid E U ((mem_pairs T).mp hp).1
      ((mem_pairs T).mp hp).2 hs)
  have hxe : X = ex := by
    ext U
    simp only [X,ex,mem_filter]
    apply and_congr_right
    intro hU
    have hdimU := hL U hU
    have hp (E : ModSpace (Fin n)) : (E,U) ∈ P ↔ E ∈ T ∧ U ≤ E := by
      rw [mem_pairs,mem_slice]
      tauto
    change (¬∃ E, (E,U) ∈ P ∧ (same E U ∧ ∀ F, (F,U) ∈ P → F = E)) ↔ _
    simp only [hp,same]
    tauto
  have hsize : P.card = C*G D d := (pairs_card T hdim).trans (by rw [hcard])
  rw [hxe,hsize] at hmass
  have hb : 2^d*B.card ≤ C*((n+C)*G D d) := by
    simpa only [B,P,same,hcard,Fintype.card_fin] using pairs_bad_cost T (d := d) hdim
  have hz : 2^d*Z.card ≤ 8*n^12*G D d := by
    apply deep_count hn hwide K Z
    intro U hu
    obtain ⟨hU,hz⟩ := mem_filter.mp hu
    apply cover U hU
    intro E he hle
    exact hz ⟨E,(mem_pairs T).mpr ⟨he,mem_slice.mpr ⟨hL U hU,hle⟩⟩⟩
  calc
    _ ≤ (3*B.card+2*Z.card)*2^d := Nat.mul_le_mul_right _ hmass
    _ = 3*(2^d*B.card)+2*(2^d*Z.card) := by ring
    _ ≤ _ := (Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hz)).trans hcst

theorem mixer_constants (t m : ℕ) (ht : 4 ≤ t) :
    let n := 6*t
    let C := 12*t*(7*t-1)
    3*(C*((n+C)*m))+2*(8*n^12*m) ≤ 32*n^10*(C*m) := by
  intro n C
  have hlo : n^2 ≤ C := by
    have hh : 6*t ≤ 7*t-1 := by omega
    have hp := Nat.mul_le_mul_left (12*t) hh
    dsimp only [n,C]
    nlinarith
  have hhi : C ≤ 3*n^2 := by
    have hp := Nat.mul_le_mul_left (12*t) (Nat.sub_le (7*t) 1)
    dsimp only [n,C]
    nlinarith
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hn2 : n ≤ n^2 := by nlinarith
  have hn10 : n^2 ≤ n^10 := Nat.pow_le_pow_right hn (by decide)
  have hNC : n+C ≤ 4*n^10 := by omega
  have h1 := Nat.mul_le_mul_right (3*C*m) hNC
  have h2 := Nat.mul_le_mul_left (16*n^10*m) hlo
  nlinarith

end MainCount
open Finset
theorem conditional_concentration :
∀ (t d : ℕ), 4 ≤ t →
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let D := a-5
  let top := mixed.filter (fun E : Submodule F W => Module.finrank F E = D)
  let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = d)
  let exceptional := layer.filter (fun U =>
    ¬ ∃ E ∈ top, U ≤ E ∧ supp U = supp E ∧
      ∀ E' ∈ top, U ≤ E' → E' = E)
  let model := 12*t*(7*t-1) *
    Nat.card {V : Submodule F (Fin D → F) // Module.finrank F V = d}
  top.card = 12*t*(7*t-1) → d ≤ D → 2*n^2 ≤ 2^d →
    (Nat.dist layer.card model + exceptional.card) * 2^d ≤ 32*n^10*model := by
  intro t d ht F n a W next h good supp sites spaces mixed D top layer exceptional model htop hd hwide
  classical
  have hp : 0 < t := by omega
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hbig : 1 < d := by
    by_contra! hh
    have hq := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    have hn2 : 2 ≤ n^2 := by nlinarith
    simp only [pow_one] at hq
    omega
  have hsucc : ∀ i : Fin n, next i = Old.nxt hp i := fun _ => rfl
  have hcoef : ∀ (i : Fin n) b, h i b = Old.hVec i b := by
    intro i b
    dsimp only [h,Old.hVec]
    split_ifs <;> rfl
  have hold (U : ModSpace (Fin n)) : good U ↔ Old.goodU hp U := by
    dsimp only [good,Old.goodU]
    simp only [hcoef,hsucc]
  have hsup (U : ModSpace (Fin n)) : supp U = suppB U := by
    ext i
    simp only [supp,suppB,Finset.mem_filter,Finset.mem_univ,true_and]
  have holdS (U : ModSpace (Fin n)) : Old.suppU U = suppB U := by
    ext i
    simp only [Old.suppU,suppB,Finset.mem_filter,Finset.mem_univ,true_and]
  have hgeomS (U : ModSpace (Fin n)) : Geometry.support U = suppB U := by
    ext i
    simp only [Geometry.support,suppB,Finset.mem_filter,Finset.mem_univ,true_and]
  have hsites (S : Finset (Fin n)) (p : ℕ) : sites S p = Old.sitesOf S p := by
    dsimp only [sites,Old.sitesOf]
    congr 1
    ext i
    simp
  have hmix (U : ModSpace (Fin n)) : U ∈ mixed ↔ good U ∧
      0 < sites (suppB U) 0 ∧ 0 < sites (suppB U) 1 := by
    simp only [mixed,spaces,mem_filter,mem_univ,true_and,hsup]
  have hmax (U : ModSpace (Fin n)) (hu : U ∈ mixed) : Module.finrank Bin U ≤ D := by
    obtain ⟨hg,h0,h1⟩ := (hmix U).mp hu
    have hmax := Old.mixed_finrank_le hp ((hold U).mp hg)
    rw [holdS,←hsites,←hsites] at hmax
    have hdmax := hmax h0 h1
    simpa only [Old.thresh,if_neg (show t ≠ 1 by omega),if_neg (show t ≠ 2 by omega),D,a] using hdmax
  let K := Geometry.kernel next h
  have hgood (U : ModSpace (Fin n)) : good U ↔ Geometry.Good next h U := Iff.rfl
  have hK (U : ModSpace (Fin n)) (hU : U ∈ mixed) :
      U ≤ K (suppB U) ∧ suppB (K (suppB U)) = suppB U ∧ K (suppB U) ∈ mixed := by
    obtain ⟨hg,h0,h1⟩ := (hmix U).mp hU
    have hgg := (hgood U).mp hg
    have hle := Geometry.le_kernel next h hgg
    have hs := Geometry.support_kernel next h hgg
    simp only [hgeomS] at hle hs
    exact ⟨hle,hs,(hmix _).mpr ⟨(hgood _).mpr (Geometry.good_kernel _ _ _),hs.symm ▸ h0,hs.symm ▸ h1⟩⟩
  have htmem (E : ModSpace (Fin n)) : E ∈ top ↔ E ∈ mixed ∧ Module.finrank Bin E = D := mem_filter
  have hlmem (U : ModSpace (Fin n)) : U ∈ layer ↔ U ∈ mixed ∧ Module.finrank Bin U = d := mem_filter
  have hcount := concentration_of_cover (D := D) (d := d) hn hwide K top layer htop
    (fun E he => ((htmem E).mp he).2)
  have hvalid (E U : ModSpace (Fin n)) (hE : E ∈ top) (hU : U ∈ slice E d)
      (hs : suppB U = suppB E) : U ∈ layer := by
    obtain ⟨hg,h0,h1⟩ := (hmix E).mp ((htmem E).mp hE).1
    obtain ⟨hr,hle⟩ := mem_slice.mp hU
    have hgu : good U :=
      ⟨fun x hx => hg.1 x (hle hx),fun x hx y hy => hg.2 x (hle hx) y (hle hy)⟩
    exact (hlmem U).mpr ⟨(hmix U).mpr ⟨hgu,hs ▸ h0,hs ▸ h1⟩,hr⟩
  have hcover (U : ModSpace (Fin n)) (hU : U ∈ layer) (nh : ∀ E ∈ top, ¬U ≤ E) :
      ∃ j < D, ∃ S : Finset (Fin n), (equalEdges S).card ≤ 10+2*(j+1) ∧
      Module.finrank Bin (K S) = D-(j+1) ∧ U ∈ slice (K S) d := by
    obtain ⟨hm,hr⟩ := (hlmem U).mp hU
    obtain ⟨hle,heq,hmK⟩ := hK U hm
    set M := K (suppB U)
    set k := Module.finrank Bin M
    have hkd : k ≤ D := hmax M hmK
    have hlt : k < D := lt_of_le_of_ne hkd (fun eq => nh M ((htmem M).mpr ⟨hmK,eq⟩) hle)
    have hdim : d ≤ k := hr ▸ Submodule.finrank_mono hle
    have hedge := Old.few_equal_edges hp ((hold M).mp ((hmix M).mp hmK).1) (show 1 < k by omega)
    have hDef (S : Finset (Fin n)) :
        (univ.filter (fun i : Fin n => i ∈ S ↔ Old.nxt hp i ∈ S)) = equalEdges S := by
      ext i
      simp only [equalEdges,mem_filter,mem_univ,true_and]
      rfl
    rw [holdS,hDef,heq] at hedge
    change (equalEdges (suppB U)).card + 2*k ≤ 6*t at hedge
    refine ⟨D-k-1,by omega,suppB U,?_,?_,mem_slice.mpr ⟨hr,hle⟩⟩
    · dsimp only [D,a] at hkd hlt ⊢
      omega
    · change k = D - (D-k-1+1)
      omega
  have hfinal := hcount hvalid hcover (fun U hu => ((hlmem U).mp hu).2) (mixer_constants t (G D d) ht)
  simpa only [exceptional,model,G,Plane,hsup] using hfinal

end PEqualNP.Outside.L_lib_912_aux
