import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_30642_aux.PivotFinish

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem bit_gate_pair :
    ∀ a b : F,
    let ba := decide (a = 1)
    let bb := decide (b = 1)
    PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba,bb] = decide (a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba,bb] = decide (a+b+a*b = 1) ∧
    PEqualNP.CircuitLowerBounds.GateOp.not.eval
      [PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [ba,bb]] =
      decide (a+b = 1) := by
  decide +kernel

theorem no_free_after_elimination {p k t : ℕ} (A : Vec p →ₗ[F] Vec k)
    (hA : Function.Injective A) (b : Vec k → Vec t → Vec k)
    (g h : Vec k → Vec t → F) (l : Vec p → F)
    (heval : ∀ q y z, dotProduct (A q + b y z) y + g y z = l q + h y z) :
    p = 0 := by
  have hconst : ∀ q, l q = l 0 := by
    intro q
    have hq := heval q 0 0
    have h0 := heval 0 0 0
    simp only [dotProduct_zero] at hq h0
    exact add_right_cancel (hq.symm.trans h0)
  have hvanish : ∀ q, A q = 0 := by
    intro q
    ext i
    let y : Vec k := fun j => if i = j then 1 else 0
    have hq := heval q y 0
    have h0 := heval 0 y 0
    rw [hconst q] at hq
    have hd : dotProduct (A q + b y 0) y = dotProduct (b y 0) y := by
      apply add_right_cancel (b := g y 0)
      simpa only [map_zero, zero_add] using hq.trans h0.symm
    have hdot : ∀ v : Vec k, dotProduct v y = v i := by
      intro v
      simp [dotProduct,y,Finset.sum_ite_eq]
    rw [hdot, hdot] at hd
    have hz : A q i + b y 0 i = 0 + b y 0 i := hd.trans (zero_add _).symm
    exact add_right_cancel hz
  by_contra hp
  let i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
  let q : Vec p := fun _ => 1
  have he : q = 0 := hA ((hvanish q).trans (map_zero A).symm)
  have hm : (1 : F) = 0 := congrFun he i
  exact one_ne_zero hm

end PEqualNP.Outside.L_meta_30642_aux.PivotFinish

namespace PEqualNP.Outside.L_meta_30642_aux.PivotStep
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

theorem solve_one {p : ℕ} (a : Vec (p+1) →ₗ[F] F) (ha : a ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ a v = 1 ∧
      (∀ q, a (R q) = 0) ∧ (∀ q c, a (R q + c • v) + c = 0) := by
  classical
  have hsurj : Function.Surjective a := LinearMap.surjective_of_ne_zero ha
  obtain ⟨v,hv⟩ := hsurj 1
  have hkdim : Module.finrank F a.ker = p := by
    have h := LinearMap.finrank_range_add_finrank_ker a
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega
  let E : Vec p ≃ₗ[F] a.ker := LinearEquiv.ofFinrankEq _ _ (by rw [hkdim, Module.finrank_fin_fun])
  let R : Vec p →ₗ[F] Vec (p+1) := a.ker.subtype.comp E.toLinearMap
  have hR : ∀ q, a (R q) = 0 := fun q => LinearMap.mem_ker.mp (E q).property
  refine ⟨R, v, a.ker.subtype_injective.comp E.injective, hv, hR, ?_⟩
  intro q c
  simp [hR, hv, CharTwo.add_self_eq_zero]

end PEqualNP.Outside.L_meta_30642_aux.PivotStep

namespace PEqualNP.Outside.L_meta_30642_aux.CubeParity

open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def toggle {d : ℕ} (i : Fin d) (w : Vec d) : Vec d :=
  Function.update w i (w i + 1)

theorem toggle_involutive {d : ℕ} (i : Fin d) : Function.Involutive (toggle i) := by
  intro w
  ext j
  by_cases h : j = i
  · subst j
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  · simp [toggle, Function.update_of_ne h]

theorem sum_zero_of_toggle {d : ℕ} (i : Fin d) (f : Vec d → F)
    (hf : ∀ w, f (toggle i w) = f w) : (∑ w, f w) = 0 := by
  let E : Vec d ≃ Vec d := ⟨toggle i, toggle i, toggle_involutive i, toggle_involutive i⟩
  have h : (∑ w : Vec d, f w * w i) = ∑ w : Vec d, f w * (w i + 1) := by
    apply Fintype.sum_equiv E
    intro w
    change f w * w i = f (toggle i w) * (toggle i w i + 1)
    rw [hf]
    simp [toggle, add_assoc, CharTwo.add_self_eq_zero]
  calc
    (∑ w, f w) = ∑ w : Vec d, (f w * w i + f w * (w i + 1)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_add]
      simp [add_assoc, ← add_assoc (w i), CharTwo.add_self_eq_zero]
    _ = (∑ w : Vec d, f w * w i) + (∑ w : Vec d, f w * (w i + 1)) :=
      Finset.sum_add_distrib
    _ = 0 := h ▸ CharTwo.add_self_eq_zero _

theorem sum_monomial_eq_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.card < d) (c : F) :
    (∑ w : Vec d, c * ∏ i ∈ S, w i) = 0 := by
  classical
  have hmiss : ∃ i : Fin d, i ∉ S := by
    by_contra h
    push Not at h
    have hu : S = Finset.univ := Finset.eq_univ_of_forall h
    simp [hu] at hS
  obtain ⟨i, hi⟩ := hmiss
  apply sum_zero_of_toggle i
  intro w
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  simp [toggle, Function.update_of_ne hji]

end PEqualNP.Outside.L_meta_30642_aux.CubeParity

namespace PEqualNP.Outside.L_meta_30642_aux.MonoSpan
open scoped BigOperators
abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Fn (n : ℕ) := Vec n → F

def mono {n : ℕ} (S : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ S, x i

def degree (n q : ℕ) : Submodule F (Fn n) :=
  Submodule.span F { f | ∃ S : Finset (Fin n), S.card ≤ q ∧ mono S = f }

theorem mono_mem {n q} (S : Finset (Fin n)) (hS : S.card ≤ q) : mono S ∈ degree n q :=
  Submodule.subset_span ⟨S,hS,rfl⟩

theorem degree_mono {n a b : ℕ} (hab : a ≤ b) : degree n a ≤ degree n b := by
  apply Submodule.span_mono
  rintro x ⟨S,hS,rfl⟩
  exact ⟨S,hS.trans hab,rfl⟩

theorem constant {n q : ℕ} (c : F) : (fun _ : Vec n => c) ∈ degree n q := by
  have h := (degree n q).smul_mem c (mono_mem ∅ (Nat.zero_le q) : mono (∅ : Finset (Fin n)) ∈ degree n q)
  have he : c • mono (∅ : Finset (Fin n)) = (fun _ : Vec n => c) := by
    funext w
    simp [mono]
  rwa [he] at h

theorem coordinate {n : ℕ} (i : Fin n) : (fun w : Vec n => w i) ∈ degree n 1 := by
  have he : mono ({i} : Finset (Fin n)) = (fun w : Vec n => w i) := by
    funext w
    simp [mono]
  rw [← he]
  exact mono_mem {i} (by simp)

private theorem char_idem (q : F) : q*q=q := (by decide : ∀ q : F, q*q=q) q

theorem mono_mul {n : ℕ} (S T : Finset (Fin n)) : mono S * mono T = mono (S ∪ T) := by
  classical
  funext x
  induction T using Finset.induction_on with
  | empty => simp [mono]
  | insert a T ha ih =>
    by_cases hs : a ∈ S
    · have hu : a ∈ S ∪ T := Finset.mem_union_left T hs
      have hdup : x a * (∏ i ∈ S ∪ T, x i) = ∏ i ∈ S ∪ T, x i := by
        rw [← Finset.insert_erase hu, Finset.prod_insert (Finset.notMem_erase _ _), ← mul_assoc,
          char_idem]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih]
      rw [show S ∪ insert a T = S ∪ T by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h.symm ▸ hs)
          · exact Or.inr h
        · tauto]
      exact hdup
    · have hn : a ∉ S ∪ T := by simp [hs,ha]
      change (∏ i ∈ S, x i) * (∏ i ∈ insert a T, x i) = ∏ i ∈ S ∪ insert a T, x i
      change (∏ i ∈ S, x i) * (∏ i ∈ T, x i) = ∏ i ∈ S ∪ T, x i at ih
      rw [Finset.prod_insert ha, ← mul_left_comm, ih, Finset.union_insert, Finset.prod_insert hn]


theorem degree_mul {n a b : ℕ} {f g : Fn n}
    (hf : f ∈ degree n a) (hg : g ∈ degree n b) :
    f * g ∈ degree n (a+b) := by
  let W := degree n (a+b)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => f * g ∈ W) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    change g ∈ Submodule.span F _ at hg
    refine Submodule.span_induction (p := fun g _ => mono S * g ∈ W) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨T,hT,rfl⟩
      rw [mono_mul]
      exact mono_mem _ ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
    · simpa using W.zero_mem
    · intro f g _ _ hf hg
      rw [mul_add]
      exact W.add_mem hf hg
    · intro c x _ hx
      have he : mono S * (c • x) = c • (mono S * x) := by
        funext y
        change (mono S y) * (c * x y) = c * (mono S y * x y)
        exact mul_left_comm _ _ _
      rw [he]
      exact W.smul_mem c hx
  · simpa using W.zero_mem
  · intro f g _ _ hf hg
    rw [add_mul]
    exact W.add_mem hf hg
  · intro c x _ hx
    have he : (c • x) * g = c • (x*g) := by
      funext y
      change (c * x y) * g y = c * (x y * g y)
      exact mul_assoc _ _ _
    rw [he]
    exact W.smul_mem c hx

theorem parity {n q : ℕ} {f : Fn n} (hf : f ∈ degree n q) (hqn : q < n) :
    (∑ w, f w) = 0 := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (∑ w, f w) = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    simpa [mono] using PEqualNP.Outside.L_meta_30642_aux.CubeParity.sum_monomial_eq_zero S (hS.trans_lt hqn) 1
  · simp
  · intro a b _ _ ha hb
    simp [Pi.add_apply, Finset.sum_add_distrib, ha, hb]
  · intro c a _ ha
    simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha]

end PEqualNP.Outside.L_meta_30642_aux.MonoSpan

namespace PEqualNP.Outside.L_meta_30642_aux.ParityBudget
open scoped BigOperators
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan

private theorem linear_mem {d : ℕ} (L : Vec d →ₗ[F] F) : (fun w => L w) ∈ degree d 1 := by
  classical
  have he (w : Vec d) : w = ∑ j : Fin d, w j • (Pi.single j 1 : Vec d) := by
    funext i
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_ite_eq']
  have hL (w : Vec d) : L w = ∑ j : Fin d, L (Pi.single j 1) * w j := by
    conv_lhs => rw [he w]
    simp [map_sum, smul_eq_mul, mul_comm]
  let g : Fin d → Fn d := fun j => L (Pi.single j 1) • (fun w => w j)
  have hL' : (fun w => L w) = ∑ j : Fin d, g j := by
    funext w
    simpa [g, Finset.sum_apply] using hL w
  rw [hL']
  apply Submodule.sum_mem
  intro j _
  exact (degree d 1).smul_mem _ (coordinate j)

theorem affine_mem {d : ℕ} (c : F) (L : Vec d →ₗ[F] F) :
    (fun w => c + L w) ∈ degree d 1 :=
  (degree d 1).add_mem (constant c) (linear_mem L)

theorem affine_cube_budget {d k r : ℕ} (A : Vec d →ₗ[F] Vec k)
    (y₀ : Vec k) (b : Fin k → Fn d) (h : Fn d)
    (hb : ∀ i, b i ∈ degree d (r+1))
    (hh : h ∈ degree d (r+1))
    (hsum : (∑ w : Vec d, (h w + ∑ i : Fin k, (y₀ i + A w i) * b i w)) = 1) :
    d ≤ r + (if A = 0 then 1 else 2) := by
  classical
  let q : ℕ := if A = 0 then 0 else 1
  have hy : ∀ i : Fin k, (fun w : Vec d => y₀ i + A w i) ∈ degree d q := by
    intro i
    by_cases ha : A = 0
    · simpa [q,ha] using (constant (n := d) (q := 0) (y₀ i))
    · have hp := affine_mem (y₀ i) ((LinearMap.proj i).comp A)
      simpa [q,ha] using hp
  let u : Fin k → Fn d := fun i => (fun w => y₀ i + A w i) * b i
  have hprod : ∀ i, u i ∈ degree d (r+1+q) := by
    intro i
    have hi := degree_mul (hb i) (hy i)
    simpa [u, mul_comm] using hi
  have hu : (∑ i : Fin k, u i) ∈ degree d (r+1+q) := by
    apply Submodule.sum_mem
    intro i _
    exact hprod i
  have hde := (degree d (r+1+q)).add_mem (degree_mono (Nat.le_add_right _ _) hh) hu
  have he : h + (∑ i : Fin k, u i) = (fun w : Vec d =>
      h w + ∑ i : Fin k, (y₀ i + A w i) * b i w) := by
    funext w
    simp [u,Finset.sum_apply]
  rw [he] at hde
  have hn : d ≤ r+1+q := by
    by_contra ht
    push Not at ht
    have hz := parity hde ht
    rw [hsum] at hz
    contradiction
  by_cases e : A = 0
  · simpa [q,e] using hn
  · simpa [q,e, Nat.add_assoc] using hn

end PEqualNP.Outside.L_meta_30642_aux.ParityBudget

namespace PEqualNP.Outside.L_meta_30642_aux.Substitute
open scoped BigOperators
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan

def front {n : ℕ} (H : Fn n) (w : Vec n) : Vec (n+1) :=
  Fin.cases (H w) w

theorem substitute {n q : ℕ} (H : Fn n) (hH : H ∈ degree n 2)
    {f : Fn (n+1)} (hf : f ∈ degree (n+1) q) :
    (fun w => f (front H w)) ∈ degree n (q+1) := by
  classical
  let W := degree n (q+1)
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (fun w => f (front H w)) ∈ W)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    let U : Finset (Fin n) := (S.erase 0).preimage Fin.succ (Fin.succ_injective n).injOn
    have huI : U.image Fin.succ = S.erase 0 := by
      ext i
      cases i using Fin.cases with
      | zero => simp [U]
      | succ i => simp [U]
    have huC : U.card = (S.erase 0).card := by
      rw [← huI, Finset.card_image_of_injective U (Fin.succ_injective n)]
    have huP (w : Vec n) : (∏ i ∈ S.erase 0, front H w i) = mono U w := by
      rw [← huI, Finset.prod_image (Fin.succ_injective n).injOn]
      rfl
    by_cases hz : 0 ∈ S
    · have hU : U.card + 1 ≤ q := by
        rw [huC, Finset.card_erase_of_mem hz]
        have hp : 0 < S.card := Finset.card_pos.mpr ⟨0,hz⟩
        omega
      have hform : (fun w => mono S (front H w)) = mono U * H := by
        funext w
        change (∏ i ∈ S, front H w i) = mono U w * H w
        rw [← Finset.prod_erase_mul S (fun i => front H w i) hz, huP]
        rfl
      rw [hform]
      exact degree_mono (by omega) (degree_mul (mono_mem U (le_refl _)) hH)
    · have hU : U.card ≤ q := by
        rwa [huC, Finset.erase_eq_of_notMem hz]
      have hform : (fun w => mono S (front H w)) = mono U := by
        funext w
        simpa only [mono, Finset.erase_eq_of_notMem hz] using huP w
      rw [hform]
      exact mono_mem U (by omega)
  · exact W.zero_mem
  · intro a b _ _ ha hb
    exact W.add_mem ha hb
  · intro c a _ ha
    exact W.smul_mem c ha

end PEqualNP.Outside.L_meta_30642_aux.Substitute

namespace PEqualNP.Outside.L_meta_30642_aux.ProgramDegree
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.Substitute PEqualNP.Outside.L_meta_30642_aux.ParityBudget

inductive Run (n : ℕ) : ∀ r : ℕ, (Vec n → Vec (n+r)) → Prop
  | nil : Run n 0 id
  | cons {r : ℕ} {f : Vec n → Vec (n+r)} (hf : Run n r f)
      (a b : Fn (n+r)) (ha : a ∈ degree (n+r) 1) (hb : b ∈ degree (n+r) 1) :
      Run n (r+1) (fun w => front (a*b) (f w))

theorem degree_run {n r : ℕ} {g : Vec n → Vec (n+r)} (hg : Run n r g) :
    ∀ q, ∀ f : Fn (n+r), f ∈ degree (n+r) q → (fun w => f (g w)) ∈ degree n (q+r) := by
  induction hg with
  | nil =>
    intro q f hf
    simpa using hf
  | @cons r f h a b ha hb ih =>
    intro q fi hi
    have hp := degree_mul ha hb
    have h₀ := substitute (a*b) hp hi
    have h₁ := ih (q+1) (fun w => fi (front (a*b) w)) h₀
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁

end PEqualNP.Outside.L_meta_30642_aux.ProgramDegree

namespace PEqualNP.Outside.L_meta_30642_aux.SpanExact
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan

theorem as_affine {n : ℕ} {f : Fn n} (hf : f ∈ degree n 1) :
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ =>
    ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    by_cases he : S = ∅
    · refine ⟨1,0,?_⟩
      intro w
      simp [mono,he]
    · have hcard : S.card = 1 := by
        have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨0, LinearMap.proj j, by intro w; simp [mono]⟩
  · exact ⟨0,0,by simp⟩
  · rintro f g _ _ ⟨c,L,h⟩ ⟨d,K,hk⟩
    refine ⟨c+d,L+K,?_⟩
    intro w
    simp only [Pi.add_apply, LinearMap.add_apply, h, hk]
    abel
  · rintro c f _ ⟨d,L,h⟩
    refine ⟨c*d,c • L,?_⟩
    intro w
    simp [h, mul_add]

theorem iff_affine {n : ℕ} {f : Fn n} :
    f ∈ degree n 1 ↔ ∃ (c : F) (L : Vec n →ₗ[F] F), ∀ w, f w = c + L w := by
  refine ⟨as_affine, ?_⟩
  rintro ⟨c,L,h⟩
  rw [show f = (fun w => c + L w) from funext h]
  exact PEqualNP.Outside.L_meta_30642_aux.ParityBudget.affine_mem c L

end PEqualNP.Outside.L_meta_30642_aux.SpanExact

namespace PEqualNP.Outside.L_meta_30642_aux.Wire
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.SpanExact PEqualNP.Outside.L_meta_30642_aux.Substitute

structure Wire (p n : ℕ) where
  x : Vec p →ₗ[F] F
  tail : Fn n
  tail_aff : tail ∈ degree n 1

def eval {p n : ℕ} (a : Wire p n) (q : Vec p) (w : Vec n) : F :=
  a.x q + a.tail w

def shift {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n) : Wire p n :=
  ⟨a.x.comp R, a.tail + (a.x v) • pivot,
    (degree n 1).add_mem a.tail_aff ((degree n 1).smul_mem _ hp)⟩

theorem shift_eval {p n : ℕ} (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1))
    (pivot : Fn n) (hp : pivot ∈ degree n 1) (a : Wire (p+1) n)
    (q : Vec p) (w : Vec n) :
    eval (shift R v pivot hp a) q w = eval a (R q + pivot w • v) w := by
  simp [eval, shift, smul_eq_mul, mul_comm]
  abel

theorem kill_factor {p n : ℕ} (a : Wire (p+1) n) (ha : a.x ≠ 0) :
    ∃ (R : Vec p →ₗ[F] Vec (p+1)) (v : Vec (p+1)),
      Function.Injective R ∧ ∀ q w,
        eval (shift R v a.tail a.tail_aff a) q w = 0 := by
  obtain ⟨R,v,hR,_,_,hp⟩ := PEqualNP.Outside.L_meta_30642_aux.PivotStep.solve_one a.x ha
  refine ⟨R,v,hR,?_⟩
  intro q w
  rw [shift_eval]
  exact hp q (a.tail w)

private def tailLinear (n : ℕ) : Vec (n+1) →ₗ[F] Vec n :=
  LinearMap.pi (fun i => LinearMap.proj i.succ)

def extend {p n : ℕ} (a : Wire p n) : Wire p (n+1) where
  x := a.x
  tail := fun w => a.tail (tailLinear n w)
  tail_aff := by
    obtain ⟨c,L,h⟩ := as_affine a.tail_aff
    apply iff_affine.mpr
    exact ⟨c, L.comp (tailLinear n), fun w => h _⟩

theorem extend_eval {p n : ℕ} (a : Wire p n) (H : Fn n) (q : Vec p) (w : Vec n) :
    eval (extend a) q (front H w) = eval a q w := by
  rfl

def retained {p n : ℕ} : Wire p (n+1) :=
  ⟨0, (fun w => w 0), coordinate 0⟩

theorem retained_eval {p n : ℕ} (H : Fn n) (q : Vec p) (w : Vec n) :
    eval retained q (front H w) = H w := by
  simp [eval, retained, front]

end PEqualNP.Outside.L_meta_30642_aux.Wire

namespace PEqualNP.Outside.L_meta_30642_aux.GateDecode
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2

def bit (x : F) : Bool := decide (x = 1)

def costly (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def legal (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

-- At most two affine input terms and a product term, whose presence is exactly the budget.
def ops (g : Gate) (a b : F) : F :=
  match g.op, g.inputs with
  | .and, [] => 1
  | .and, [_] => a
  | .and, _ :: _ :: _ => a*b
  | .or, [] => 0
  | .or, [_] => a
  | .or, _ :: _ :: _ => a+b+a*b
  | .mod _, [] => 1
  | .mod _, [_] => 1+a
  | .mod _, _ :: _ :: _ => 1+a+b
  | .not, _ => 1+a
  | .maj, _ => 0

private theorem and1 : ∀ a : F, GateOp.and.eval [bit a] = bit a := by decide +kernel
private theorem or1 : ∀ a : F, GateOp.or.eval [bit a] = bit a := by decide +kernel
private theorem and2 : ∀ a b : F, GateOp.and.eval [bit a,bit b] = bit (a*b) := by decide +kernel
private theorem or2 : ∀ a b : F, GateOp.or.eval [bit a,bit b] = bit (a+b+a*b) := by decide +kernel
private theorem mod1 : ∀ a : F, (GateOp.mod 2).eval [bit a] = bit (1+a) := by decide +kernel
private theorem mod2 : ∀ a b : F, (GateOp.mod 2).eval [bit a,bit b] = bit (1+a+b) := by decide +kernel
private theorem not1 : ∀ a : F, GateOp.not.eval [bit a] = bit (1+a) := by decide +kernel

theorem decode (g : Gate) (u : ℕ → F) (h : legal g) :
    g.op.eval (g.inputs.map fun i => bit (u i)) =
      bit (ops g (u (g.inputs.getD 0 0)) (u (g.inputs.getD 1 0))) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := h
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩
    · exact and1 (u i)
    · exact or1 (u i)
    · exact mod1 (u i)
    · exact not1 (u i)
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · exact and2 (u i) (u j)
    · exact or2 (u i) (u j)
    · exact mod2 (u i) (u j)
    · simp at h
  · simp at hs

end PEqualNP.Outside.L_meta_30642_aux.GateDecode

namespace PEqualNP.Outside.L_meta_30642_aux.WireOps
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.Wire

def zeroCostConst {p n : ℕ} (c : F) : Wire p n :=
  ⟨0, fun _ => c, constant c⟩

def plus {p n : ℕ} (a b : Wire p n) : Wire p n :=
  ⟨a.x+b.x, a.tail+b.tail, (degree n 1).add_mem a.tail_aff b.tail_aff⟩

theorem const_eval {p n} (c : F) (q : Vec p) (w : Vec n) :
    eval (zeroCostConst c) q w = c := by simp [eval,zeroCostConst]

theorem plus_eval {p n} (a b : Wire p n) (q : Vec p) (w : Vec n) :
    eval (plus a b) q w = eval a q w + eval b q w := by
  simp [plus, eval]
  abel

theorem factor_value_of_zero {p n} (a : Wire p n) (h : a.x = 0) (q : Vec p) (w : Vec n) :
    eval a q w = a.tail w := by simp [eval,h]

theorem retain_product {p n} (a b : Wire p n) (ha : a.x = 0) (hb : b.x = 0)
    (q : Vec p) (w : Vec n) :
    eval retained q (PEqualNP.Outside.L_meta_30642_aux.Substitute.front (a.tail*b.tail) w) = eval a q w * eval b q w := by
  rw [retained_eval, factor_value_of_zero a ha, factor_value_of_zero b hb]
  rfl

end PEqualNP.Outside.L_meta_30642_aux.WireOps

namespace PEqualNP.Outside.L_meta_30642_aux.Normalized
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.Wire PEqualNP.Outside.L_meta_30642_aux.WireOps PEqualNP.Outside.L_meta_30642_aux.Substitute
open PEqualNP.Outside.L_meta_30642_aux.ProgramDegree

inductive Expr where
  | cn : F → Expr
  | rd : ℕ → Expr
  | add : Expr → Expr → Expr

def Expr.val (w : List F) : Expr → F
  | .cn c => c
  | .rd i => w.getD i 0
  | .add a b => a.val w + b.val w

def Expr.compile {p n : ℕ} (w : List (Wire p n)) : Expr → Wire p n
  | .cn c => zeroCostConst c
  | .rd i => w.getD i (zeroCostConst 0)
  | .add a b => plus (a.compile w) (b.compile w)

theorem list_getD_eval {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (i : ℕ) :
    eval (w.getD i (zeroCostConst 0)) q u =
      (w.map fun z => eval z q u).getD i 0 := by
  induction w generalizing i with
  | nil => simp [const_eval]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Expr.compile_val {p n : ℕ} (w : List (Wire p n)) (q : Vec p) (u : Vec n) (e : Expr) :
    eval (e.compile w) q u = e.val (w.map fun z => eval z q u) := by
  induction e with
  | cn c => exact const_eval c q u
  | rd i => exact list_getD_eval w q u i
  | add a b ha hb => simp [Expr.compile, Expr.val, plus_eval, ha, hb]

inductive Ins where
  | free : Expr → Ins
  | paid : Expr → Expr → Expr → Ins

def Ins.cost : Ins → ℕ
  | .free _ => 0
  | .paid _ _ _ => 1

def Ins.val (w : List F) : Ins → F
  | .free e => e.val w
  | .paid e a b => e.val w + a.val w * b.val w

def Ins.step (w : List F) (g : Ins) : List F := w ++ [g.val w]

def embed {k p n : ℕ} (x : Fin k → Wire p n) : Vec p →ₗ[F] Vec k :=
  LinearMap.pi fun i => (x i).x

structure State (b k p r : ℕ) where
  env : Vec b → Vec (b+r)
  hEnv : Run b r env
  orig : Fin k → Wire p (b+r)
  hOrig : Function.Injective (embed orig)
  regs : List (Wire p (b+r))

def State.args {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : Vec k :=
  fun i => eval (S.orig i) q (S.env u)

def State.values {b k p r} (S : State b k p r) (q : Vec p) (u : Vec b) : List F :=
  S.regs.map fun z => eval z q (S.env u)

def State.free {b k p r} (S : State b k p r) (e : Expr) : State b k p r :=
  { S with regs := S.regs ++ [e.compile S.regs] }

theorem State.free_ok {b k p r} (S : State b k p r) (e : Expr) (q : Vec p) (u : Vec b) :
    (S.free e).args q u = S.args q u ∧
    (S.free e).values q u = Ins.step (S.values q u) (.free e) := by
  refine ⟨rfl, ?_⟩
  simp [State.free, State.values, Ins.step, Ins.val, Expr.compile_val]

def State.retain {b k p r} (S : State b k p r) (e a c : Expr) : State b k p (r+1) :=
  let a' := a.compile S.regs
  let c' := c.compile S.regs
  ⟨fun u => front (a'.tail*c'.tail) (S.env u),
    .cons S.hEnv a'.tail c'.tail a'.tail_aff c'.tail_aff,
    fun i => extend (S.orig i), S.hOrig,
    (S.regs.map extend) ++ [plus (extend (e.compile S.regs)) retained]⟩

theorem State.retain_ok {b k p r} (S : State b k p r) (e a c : Expr)
    (ha : (a.compile S.regs).x = 0) (hc : (c.compile S.regs).x = 0)
    (q : Vec p) (u : Vec b) :
    (S.retain e a c).args q u = S.args q u ∧
    (S.retain e a c).values q u = Ins.step (S.values q u) (.paid e a c) := by
  constructor
  · funext i
    exact extend_eval (S.orig i) _ q (S.env u)
  · unfold State.retain State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      plus_eval, extend_eval]
    rw [retain_product _ _ ha hc]
    simp [Expr.compile_val, extend_eval]

def State.discard {b k p r} (S : State b k (p+1) r) (e : Expr)
  (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
  (pivot : Wire (p+1) (b+r)) : State b k p r :=
  let f := shift R v pivot.tail pivot.tail_aff
  ⟨S.env, S.hEnv, fun i => f (S.orig i), S.hOrig.comp hR,
    (S.regs.map f) ++ [f (e.compile S.regs)]⟩


theorem State.discard_ok {b k p r} (S : State b k (p+1) r) (e a c : Expr)
    (R : Vec p →ₗ[F] Vec (p+1)) (hR : Function.Injective R) (v : Vec (p+1))
    (pivot : Wire (p+1) (b+r)) (q : Vec p) (u : Vec b)
    (hz : eval (shift R v pivot.tail pivot.tail_aff (a.compile S.regs)) q (S.env u) *
          eval (shift R v pivot.tail pivot.tail_aff (c.compile S.regs)) q (S.env u) = 0) :
    let q₀ := R q + pivot.tail (S.env u) • v
    (S.discard e R hR v pivot).args q u = S.args q₀ u ∧
    (S.discard e R hR v pivot).values q u = Ins.step (S.values q₀ u) (.paid e a c) := by
  dsimp only
  constructor
  · funext i
    exact shift_eval R v pivot.tail pivot.tail_aff (S.orig i) q (S.env u)
  · unfold State.discard State.values Ins.step Ins.val
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      shift_eval]
    simp only [shift_eval] at hz
    simp [← Expr.compile_val, hz, shift_eval]

theorem zero_direction {n} (a : Wire 0 n) : a.x = 0 := by
  apply LinearMap.ext
  intro q
  have hq : q = 0 := Subsingleton.elim _ _
  rw [hq]
  exact map_zero a.x

theorem advance {b k p r} (S : State b k p r) (g : Ins) :
    ∃ (p' r' : ℕ) (S' : State b k p' r'),
      p+r' = p'+r+g.cost ∧
      ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧ S'.values q u = g.step (S.values q₀ u) := by
  cases g with
  | free e =>
    exact ⟨p,r,S.free e,by simp [Ins.cost],fun q u => ⟨q,S.free_ok e q u⟩⟩
  | paid e a c =>
    let aa := a.compile S.regs
    let cc := c.compile S.regs
    by_cases both : aa.x = 0 ∧ cc.x = 0
    · refine ⟨p,r+1,S.retain e a c,by simp [Ins.cost, Nat.add_assoc],?_⟩
      intro q u
      exact ⟨q,S.retain_ok e a c both.1 both.2 q u⟩
    · cases p with
      | zero => exact False.elim (both ⟨zero_direction aa,zero_direction cc⟩)
      | succ p =>
        have usePivot (z : Wire (p+1) (b+r)) (hz : z.x ≠ 0) (hz' : z = aa ∨ z = cc) :
            ∃ (p' r' : ℕ) (S' : State b k p' r'),
              (p+1)+r' = p'+r+(.paid e a c : Ins).cost ∧
              ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
                S'.values q u = (.paid e a c : Ins).step (S.values q₀ u) := by
          obtain ⟨R,v,hR,hkill⟩ := kill_factor z hz
          refine ⟨p,r,S.discard e R hR v z,by simp only [Ins.cost]; omega,?_⟩
          intro q u
          have hh := hkill q (S.env u)
          refine ⟨_,S.discard_ok e a c R hR v z q u ?_⟩
          rcases hz' with h | h
          · subst z
            change _ at hh
            change eval (shift R v aa.tail aa.tail_aff aa) q (S.env u) *
              eval (shift R v aa.tail aa.tail_aff cc) q (S.env u) = 0
            rw [hh,zero_mul]
          · subst z
            change eval (shift R v cc.tail cc.tail_aff aa) q (S.env u) *
              eval (shift R v cc.tail cc.tail_aff cc) q (S.env u) = 0
            rw [hh,mul_zero]
        by_cases h : aa.x = 0
        · exact usePivot cc (fun z => both ⟨h,z⟩) (Or.inr rfl)
        · exact usePivot aa h (Or.inl rfl)

def paidCount (gs : List Ins) : ℕ := (gs.map Ins.cost).sum

theorem advance_all {b k : ℕ} (gs : List Ins) :
    ∀ p r (S : State b k p r),
      ∃ (p' r' : ℕ) (S' : State b k p' r'),
        p+r' = p'+r+paidCount gs ∧
        ∀ q u, ∃ q₀, S'.args q u = S.args q₀ u ∧
          S'.values q u = gs.foldl Ins.step (S.values q₀ u) := by
  induction gs with
  | nil =>
    intro p r S
    exact ⟨p,r,S,by simp [paidCount],fun q _ => ⟨q,rfl,rfl⟩⟩
  | cons g t ih =>
    intro p r S
    obtain ⟨p₁,r₁,S₁,h₁,e₁⟩ := advance S g
    obtain ⟨p₂,r₂,S₂,h₂,e₂⟩ := ih p₁ r₁ S₁
    refine ⟨p₂,r₂,S₂,?_ ,?_⟩
    · simp only [paidCount,List.map_cons,List.sum_cons] at *
      omega
    · intro q u
      obtain ⟨q₁,ha,hw⟩ := e₂ q u
      obtain ⟨q₀,ha₀,hw₀⟩ := e₁ q₁ u
      exact ⟨q₀,ha.trans ha₀,by rw [List.foldl_cons,hw,hw₀]⟩

end PEqualNP.Outside.L_meta_30642_aux.Normalized

namespace PEqualNP.Outside.L_meta_30642_aux.CircuitBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_30642_aux.Normalized PEqualNP.Outside.L_meta_30642_aux.GateDecode

private def free0 (x : F) : Ins := .free (.cn x)
private def read (i : ℕ) : Ins := .free (.rd i)
private def neg (i : ℕ) : Ins := .free (.add (.cn 1) (.rd i))

def lower (g : Gate) : Ins :=
  match g.op, g.inputs with
  | .and, [] => free0 1
  | .or, [] => free0 0
  | .and, [i] | .or, [i] => read i
  | .and, i :: j :: _ => .paid (.cn 0) (.rd i) (.rd j)
  | .or, i :: j :: _ => .paid (.add (.rd i) (.rd j)) (.rd i) (.rd j)
  | .mod _, [] => free0 1
  | .mod _, [i] => neg i
  | .mod _, i :: j :: _ => .free (.add (.add (.cn 1) (.rd i)) (.rd j))
  | .not, i :: _ => neg i
  | _, _ => free0 0

theorem lower_ops (g : Gate) (w : List F) (hg : legal g) :
    (lower g).val w =
      ops g (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | rfl | simp at h
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> rfl
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩
    · simp [lower, ops, Ins.val, Expr.val]
    · rfl
    · rfl
    · simp at h
  · simp at hs

private theorem bit_zero : bit 0 = false := by decide

private theorem getD_map_bit (w : List F) (i : ℕ) :
    (w.map bit).getD i false = bit (w.getD i 0) := by
  induction w generalizing i with
  | nil => simp [bit_zero]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_bridge (g : Gate) (w : List F) (h : legal g) :
    stepBool (w.map bit) g = ((lower g).step w).map bit := by
  unfold stepBool Ins.step
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq]
  simp only [getD_map_bit]
  rw [decode g _ h, lower_ops g w h]

theorem fold_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List F) :
    gs.foldl stepBool (w.map bit) = ((gs.map lower).foldl Ins.step w).map bit := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [step_bridge g w (hg g (by simp))]
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) _

theorem eval_bridge (C : Circuit) (hg : ∀ g ∈ C.gates, legal g) (w : List F) :
    C.eval (w.map bit) = bit (((C.gates.map lower).foldl Ins.step w).getD C.output 0) := by
  change (C.gates.foldl stepBool (w.map bit)).getD C.output false = _
  rw [fold_bridge C.gates hg, getD_map_bit]

noncomputable def paid (g : Gate) : Bool := @decide (costly g) (Classical.propDecidable _)

theorem cost_one (g : Gate) (hg : legal g) :
    (lower g).cost = @ite ℕ (costly g) (Classical.propDecidable _) 1 0 := by
  classical
  obtain ⟨op,ins⟩ := g
  obtain ⟨hs,ho⟩ := hg
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ ins.length = 1) at ho
  change ins.length ≤ 2 at hs
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,is⟩⟩⟩
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost,free0] at *
  · rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;> simp [lower,costly,Ins.cost,read,neg]
  · rcases ho with rfl | rfl | rfl | ⟨rfl,h⟩ <;> simp [lower,costly,Ins.cost] at *
  · simp at hs

theorem cost_bridge (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
    paidCount (gs.map lower) = gs.countP paid := by
  classical
  induction gs with
  | nil => rfl
  | cons g t ih =>
    have ht := ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    simp only [paidCount,List.map_cons,List.sum_cons,List.countP_cons]
    change (lower g).cost + paidCount (t.map lower) = _
    rw [cost_one g (hg g (by simp)), ht]
    by_cases h : costly g <;> simp [paid,h,Nat.add_comm]

end PEqualNP.Outside.L_meta_30642_aux.CircuitBridge

namespace PEqualNP.Outside.L_meta_30642_aux.Pullback
open scoped BigOperators
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.ParityBudget

theorem pullback {d n q : ℕ} (Y : Vec d →ₗ[F] Vec n) (y₀ : Vec n)
    {f : Fn n} (hf : f ∈ degree n q) :
    (fun w => f (y₀ + Y w)) ∈ degree d q := by
  change f ∈ Submodule.span F _ at hf
  refine Submodule.span_induction (p := fun f _ => (fun w => f (y₀ + Y w)) ∈ degree d q)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S,hS,rfl⟩
    apply degree_mono hS
    clear hS
    induction S using Finset.induction_on with
    | empty =>
      have eq : (fun w => mono (∅ : Finset (Fin n)) (y₀ + Y w)) = (fun _ : Vec d => (1:F)) := by
        funext w
        simp [mono]
      rw [eq]
      exact constant 1
    | insert i s hi ih =>
      have he : (fun w => mono (insert i s) (y₀ + Y w)) =
          (fun w => y₀ i + Y w i) * (fun w => mono s (y₀ + Y w)) := by
        funext w
        simp [mono, Finset.prod_insert hi,Pi.mul_apply]
      rw [he,Finset.card_insert_of_notMem hi, Nat.add_comm]
      exact degree_mul (affine_mem (y₀ i) ((LinearMap.proj i).comp Y)) ih
  · exact (degree d q).zero_mem
  · intro a b _ _ ha hb
    exact (degree d q).add_mem ha hb
  · intro c a _ ha
    exact (degree d q).smul_mem c ha

def appendLinear {d k t : ℕ} (B : Vec d →ₗ[F] Vec k) (T : Vec d →ₗ[F] Vec t) :
    Vec d →ₗ[F] Vec (k+t) :=
  LinearMap.pi (Fin.addCases (fun i => (LinearMap.proj i).comp B)
    (fun j => (LinearMap.proj j).comp T))

theorem append_affine {d k t : ℕ} (B : Vec d →ₗ[F] Vec k) (T : Vec d →ₗ[F] Vec t)
    (y₀ : Vec k) (z₀ : Vec t) (w : Vec d) :
    Fin.append (y₀ + B w) (z₀ + T w) = Fin.append y₀ z₀ + appendLinear B T w := by
  funext i
  cases i using Fin.addCases with
  | left i => simp [appendLinear]
  | right i => simp [appendLinear]

end PEqualNP.Outside.L_meta_30642_aux.Pullback

namespace PEqualNP.Outside.L_meta_30642_aux.Lower

open scoped BigOperators
open PEqualNP.Outside.L_meta_30642_aux.MonoSpan PEqualNP.Outside.L_meta_30642_aux.Wire PEqualNP.Outside.L_meta_30642_aux.WireOps
open PEqualNP.Outside.L_meta_30642_aux.Normalized PEqualNP.Outside.L_meta_30642_aux.ProgramDegree PEqualNP.Outside.L_meta_30642_aux.Pullback
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_30642_aux.CircuitBridge
open PEqualNP.Outside.L_meta_30642_aux.GateDecode (bit legal)

private def xreg {k b : ℕ} (i : Fin k) : Wire k b :=
  ⟨LinearMap.proj i, fun _ => 0, constant 0⟩

private def baseReg {k b : ℕ} (i : Fin b) : Wire k b :=
  ⟨0, fun w => w i, coordinate i⟩

private def start (k b : ℕ) : State b k k 0 :=
  ⟨id, .nil, fun i => xreg i, by
    intro q s h
    funext i
    exact congrFun h i,
    (List.ofFn fun i : Fin k => xreg i) ++ (List.ofFn fun i : Fin b => baseReg i)⟩

private theorem args_start {k b : ℕ} (q : Vec k) (u : Vec b) :
    (start k b).args q u = q := by
  funext i
  simp [start,State.args,eval,xreg]

private theorem regs_start {k b : ℕ} (q : Vec k) (u : Vec b) :
    (start k b).values q u = List.ofFn q ++ List.ofFn u := by
  simp [start,State.values,eval,xreg,baseReg,List.map_ofFn,Function.comp_def]

private theorem ofFn_append {k t : ℕ} (y : Vec k) (z : Vec t) :
    List.ofFn (Fin.append y z) = List.ofFn y ++ List.ofFn z := by
  rw [List.ofFn_add]
  simp only [Fin.append_left', Fin.append_right]

private def areg {b k p r : ℕ} (S : State b k p r) (i : ℕ) : Wire p (b+r) :=
  S.regs.getD i (zeroCostConst 0)

theorem bit_inj : Function.Injective bit := by
  exact (by decide : ∀ a b : F, bit a = bit b → a = b)

def bits {n : ℕ} (x : Vec n) : List Bool := List.ofFn (fun i => bit (x i))

set_option maxHeartbeats 1500000 in
theorem normalized_readout {n : Nat} (g : Vec n → F) (c : Nat)
    (C : Circuit) (hlegal : ∀ a ∈ C.gates, legal a)
    (hcost : C.gates.countP paid ≤ n+c)
    (hfit : ∀ x y : Vec n, C.eval (bits x ++ bits y) = bit (dotProduct x y + g y)) :
    ∃ (r : Nat) (env : Vec n → Vec (n+r))
      (o : Fn (n+r)) (p : Fin n → Fn (n+r)), r ≤ c ∧ Run n r env ∧
      o∈degree (n+r) 1 ∧ (∀ i, p i∈degree (n+r) 1) ∧
      ∀ y, g y = o (env y)+ ∑ i, y i * p i (env y) := by
  classical
  let gs := C.gates.map lower
  have hFld (x y : Vec n) :
      (gs.foldl Ins.step (List.ofFn x ++ List.ofFn y)).getD C.output 0 = dotProduct x y + g y := by
    apply bit_inj
    rw [← eval_bridge C hlegal]
    simpa [bits,List.map_ofFn,Function.comp_def] using hfit x y
  obtain ⟨p,r,S,hs,hstate⟩ := advance_all gs n 0 (start n n)
  let O := areg S C.output
  let A := embed S.orig
  let b : Vec n → Vec n := fun u i => (S.orig i).tail (S.env u)
  let h : Vec n → F := fun u => O.tail (S.env u)
  have hv (q : Vec p) (y : Vec n) :
      dotProduct (A q+b y) y + g y=O.x q+h y := by
    obtain ⟨q₀,hq,hrs⟩ := hstate q y
    have ha : A q+b y=q₀ := by
      change S.args q y=q₀
      simpa only [args_start] using hq
    have hO : eval O q (S.env y)=(S.values q y).getD C.output 0 :=
      list_getD_eval S.regs q (S.env y) _
    change dotProduct (A q+b y) y+g y=eval O q (S.env y)
    rw [ha,hO,hrs,regs_start]
    exact (hFld q₀ y).symm
  have hp : p=0 := PEqualNP.Outside.L_meta_30642_aux.PivotFinish.no_free_after_elimination (t:=0) A S.hOrig
    (fun y _ => b y) (fun y _ => g y) (fun y _ => h y) O.x (fun q y _ => hv q y)
  have hc : paidCount gs ≤ n+c := by simpa only [gs,cost_bridge C.gates hlegal] using hcost
  refine ⟨r,S.env,O.tail,(fun i => (S.orig i).tail),by omega,S.hEnv,O.tail_aff,
    (fun i => (S.orig i).tail_aff),?_⟩
  intro y
  have hf := hv 0 y
  simp only [map_zero,zero_add] at hf
  change dotProduct (b y) y + g y=h y at hf
  have he : g y=h y+dotProduct (b y) y := by
    rw [←hf]
    conv_rhs => rw [add_comm (dotProduct (b y) y) (g y)]
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
  simpa [h,b,dotProduct,mul_comm] using he
end PEqualNP.Outside.L_meta_30642_aux.Lower

namespace PEqualNP.Outside.L_meta_30642_aux
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
def D {n} (g : V n → F) (a x : V n) : F := g (x+a)-g x
def T {n} (g : V n → F) (a b c : V n) := D (D (D g a) b) c 0
def Cubic {n} (g : V n → F) := ∀ a b c d x, D (D (D (D g a) b) c) d x=0
def Quad {n} (q : V n → F) := ∃ (s : F) (h : V n) (M : Fin n → V n),
    ∀ x, q x=s+dotProduct h x+∑ i,∑ j, M i j*x i*x j

set_option maxHeartbeats 600000 in
theorem quad_diff {n} {q : V n → F} (hq : Quad q) (u v w x : V n) :
    D (D (D q u) v) w x=0 := by
  obtain ⟨s,h,M,hq⟩ := hq
  simp only [D,hq,dotProduct,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
  ring

theorem map_dot {n} (h x u : V n) : dotProduct h (x+u)=dotProduct h x + dotProduct h u := by
  simp only [dotProduct, Pi.add_apply, mul_add,Finset.sum_add_distrib]

structure Features {n : ℕ} (g : V n → F) (r : ℕ) where
  A : Fin r × Fin 3 → V n
  q : V n → F
  hq : Quad q
  H : Fin r → V n → F
  co : Fin r → F
  start : Fin r → Fin 2 → F
  earlier : Fin r → Fin 2 → Fin r → F
  strict : ∀ i k j, i.val ≤ j.val → earlier i k j=0
  gate : ∀ i x, H i x =
    (start i 0+dotProduct (A (i,0)) x+∑ j, earlier i 0 j * H j x) *
    (start i 1+dotProduct (A (i,1)) x+∑ j, earlier i 1 j * H j x)
  out : ∀ x, g x=q x+∑ i, (co i+dotProduct (A (i,2)) x)*H i x

theorem same_prefix {n r} {g : V n → F} (S : Features g r) (u : V n) (m : ℕ)
    (zero : ∀ (i : Fin r), i.val<m → ∀ k : Fin 2, dotProduct (S.A (i,k.castSucc)) u=0) :
    ∀ (i : Fin r), i.val<m → ∀ x, S.H i (x+u)=S.H i x := by
  intro i
  refine Fin.strong_induction_on (motive := fun i => i.val<m → ∀ x, S.H i (x+u)=S.H i x) ?_ i
  intro i ih
  all_goals
    intro hi x
    have prev (k : Fin 2) : (∑ j, S.earlier i k j*S.H j (x+u)) = ∑ j, S.earlier i k j*S.H j x := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases lt : j.val<i.val
      · rw [ih j lt (by omega) x]
      · rw [S.strict i k j (by omega),zero_mul,zero_mul]
    rw [S.gate i (x+u),S.gate i x,map_dot,map_dot,prev,prev]
    have z₀ : dotProduct (S.A (i,0)) u=0 := zero i hi 0
    have z₁ : dotProduct (S.A (i,1)) u=0 := zero i hi 1
    rw [z₀,z₁,add_zero,add_zero]

def featureMap {n r} (A : Fin r × Fin 3 → V n) : V n →ₗ[F] (Fin r × Fin 3 → F) :=
  Matrix.mulVecLin (Matrix.of A)

theorem ker_in_rad {n r} {g : V n → F} (S : Features g r) (R : Submodule F (V n))
    (rad : ∀ u, u∈R ↔ ∀ v w, T g u v w=0) : LinearMap.ker (featureMap S.A) ≤ R := by
  intro u hu
  have zero (j) : dotProduct (S.A j) u=0 := congrFun (show featureMap S.A u=0 from hu) j
  have hH (i : Fin r) (x : V n) : S.H i (x+u)=S.H i x :=
    same_prefix S u r (fun i _ k => zero _) i i.isLt x
  have de : D g u = D S.q u := by
    funext x
    unfold D
    rw [S.out (x+u),S.out x]
    simp_rw [map_dot,zero,add_zero,hH]
    ring
  apply (rad u).mpr
  intro v w
  unfold T
  rw [de]
  exact quad_diff S.hq _ _ _ _

theorem feature_bound {n r} {g : V n → F} (S : Features g r) (R : Submodule F (V n))
    (rad : ∀ u, u∈R ↔ ∀ v w, T g u v w=0) :
    n-Module.finrank F R ≤ 3*r ∧
     (n-Module.finrank F R=3*r → Function.Surjective (featureMap S.A)) := by
  let P := featureMap S.A
  have hk := Submodule.finrank_mono (ker_in_rad S R rad)
  have hd := P.finrank_range_add_finrank_ker
  have hc := (LinearMap.range P).finrank_le
  have domain : Module.finrank F (V n)=n := Module.finrank_fin_fun ..
  have cod : Module.finrank F (Fin r × Fin 3 → F)=r*3 := by
    simp [Module.finrank_fintype_fun_eq_card]
  rw [domain] at hd
  rw [cod] at hc
  change Module.finrank F (LinearMap.ker P) ≤ _ at hk
  constructor
  · omega
  · intro hh
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [cod]
    change Module.finrank F (LinearMap.range P)=r*3
    omega

theorem independent_of_surjective {n r} {A : Fin r × Fin 3 → V n}
    (hA : Function.Surjective (featureMap A)) : LinearIndependent F A := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨u,hu⟩ := hA (Pi.single j 1)
  have E (k) : dotProduct (A k) u = (Pi.single j 1 : Fin r × Fin 3 → F) k := congrFun hu k
  let L : V n →ₗ[F] F := (LinearMap.proj (0 : Fin 1)).comp
    (Matrix.mulVecLin (Matrix.of (fun _ : Fin 1 => u)))
  have h (k) : L (A k) = (Pi.single j 1 : Fin r × Fin 3 → F) k :=
    (dotProduct_comm u (A k)).trans (E k)
  have he := congrArg L hc
  simp only [map_sum,map_smul,map_zero,h,smul_eq_mul] at he
  simpa [Pi.single_apply] using he

end PEqualNP.Outside.L_meta_30642_aux

namespace PEqualNP.Outside.L_meta_30642_aux
open MonoSpan (degree Fn) ProgramDegree (Run)
open scoped BigOperators

structure WRep (n r : Nat) where
  s : F
  raw : V n
  h : V r

def WRep.val {n r} (w : WRep n r) (H : Fin r → V n → F) (x : V n) :=
  w.s+dotProduct w.raw x+∑ j, w.h j*H j x

def WRep.plus {n r} (w v : WRep n r) : WRep n r := ⟨w.s+v.s,w.raw+v.raw,w.h+v.h⟩
def WRep.scale {n r} (c : F) (w : WRep n r) : WRep n r := ⟨c*w.s,c • w.raw,c • w.h⟩
def WRep.const {n r} (c : F) : WRep n r := ⟨c,0,0⟩
def WRep.extend {n r} (w : WRep n r) : WRep n (r+1) := ⟨w.s,w.raw,Fin.snoc w.h 0⟩
def WRep.top (n r : Nat) : WRep n (r+1) := ⟨0,0,Fin.snoc (fun _ => 0) 1⟩

theorem WRep.plus_val {n r} (w v : WRep n r) (H x) :
    (w.plus v).val H x=w.val H x+v.val H x := by
  simp only [plus,val,dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring
theorem WRep.scale_val {n r} (w : WRep n r) (c : F) (H x) :
    (w.scale c).val H x=c*w.val H x := by
  simp [scale,val,dotProduct,Finset.mul_sum,mul_add,mul_assoc]
theorem WRep.const_val {n r} (c : F) (H x) : (const (n:=n) (r:=r) c).val H x=c := by simp [const,val]
theorem WRep.extend_val {n r} (w : WRep n r) (H : Fin r → V n → F) (h : V n → F) (x) :
    w.extend.val (Fin.snoc H h) x=w.val H x := by
  simp only [extend,val,Fin.sum_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,zero_mul,add_zero]
theorem WRep.top_val {n r} (H : Fin r → V n → F) (h : V n → F) (x) :
    (top n r).val (Fin.snoc H h) x=h x := by
  simp [top,val,Fin.sum_univ_castSucc]

structure Bank (n r : Nat) where
  H : Fin r → V n → F
  w : Fin r → Fin 2 → WRep n r
  bound : ∀ i k j, i.val≤j.val → (w i k).h j=0
  gates : ∀ i x, H i x=(w i 0).val H x * (w i 1).val H x

def Bank.empty (n) : Bank n 0 := ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0⟩

def Bank.snoc {n r} (B : Bank n r) (a b : WRep n r) : Bank n (r+1) where
  H := Fin.snoc B.H (fun x => a.val B.H x*b.val B.H x)
  w := Fin.snoc (fun i k => (B.w i k).extend) (fun k => if k=0 then a.extend else b.extend)
  bound := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro k j hj
      have e : j=Fin.last r := Fin.ext (by have := j.isLt;change r≤j.val at hj;change j.val=r;omega)
      subst j
      simp [WRep.extend]
    · intro k j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [WRep.extend]
      · intro le
        simpa [WRep.extend] using B.bound i k j le
  gates := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro x
      simp [WRep.extend_val]
    · intro x
      simpa [WRep.extend_val] using B.gates i x

def Real {n r} (B : Bank n r) (f : V n → F) := ∃ w : WRep n r, ∀ x, f x=w.val B.H x

theorem real_const {n r} (B : Bank n r) (c : F) : Real B (fun _ => c) :=
  ⟨WRep.const c, fun x => (WRep.const_val ..).symm⟩
theorem real_plus {n r} {B : Bank n r} {f g : V n → F} (a : Real B f) (b : Real B g) :
    Real B (fun x => f x+g x) := by
  obtain ⟨w,hw⟩ := a;obtain ⟨v,hv⟩ := b
  exact ⟨w.plus v,fun x => by rw [WRep.plus_val,hw,hv]⟩
theorem real_scale {n r} {B : Bank n r} {f : V n → F} (c : F) (a : Real B f) :
    Real B (fun x => c*f x) := by
  obtain ⟨w,hw⟩ := a
  exact ⟨WRep.scale c w,fun x => by rw [WRep.scale_val,hw]⟩
theorem real_sum {n r} {B : Bank n r} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {f : ι → V n → F} (h : ∀ i∈S, Real B (f i)) : Real B (fun x => ∑ i∈S, f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using real_const B 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact real_plus (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem real_linear {n r t} {B : Bank n r} {env : V n → V t}
    (hs : ∀ j, Real B (fun x => env x j)) {f : Fn t} (hf : f∈degree t 1) :
    Real B (fun x => f (env x)) := by
  classical
  obtain ⟨c,L,he⟩ := SpanExact.as_affine hf
  have basis (v : V t) : v=∑ j : Fin t, v j • (Pi.single j 1 : V t) := by
    funext i
    simp [Pi.single_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_ite_eq']
  have calcL (v : V t) : L v=∑ j, L (Pi.single j 1) * v j := by
    conv_lhs => rw [basis v]
    simp [map_sum,smul_eq_mul,mul_comm]
  simp_rw [he,calcL]
  exact real_plus (real_const B c) (real_sum Finset.univ (fun j _ => real_scale _ (hs j)))

theorem bank_run {n r} {env : V n → V (n+r)} (run : Run n r env) :
    ∃ B : Bank n r, ∀ i, Real B (fun x => env x i) := by
  induction run with
  | nil =>
    refine ⟨Bank.empty n,?_⟩
    intro j
    exact ⟨⟨0,Pi.single j 1,0⟩,fun x => by simp [WRep.val,dotProduct,Pi.single_apply]⟩
  | @cons r f hf a b ha hb ih =>
    obtain ⟨B,hB⟩ := ih
    obtain ⟨ca,ea⟩ := real_linear hB ha
    obtain ⟨cb,eb⟩ := real_linear hB hb
    refine ⟨B.snoc ca cb,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨WRep.top n r,?_⟩
      intro x
      change a (f x)*b (f x) = (WRep.top n r).val (Fin.snoc B.H _) x
      rw [WRep.top_val,ea,eb]
    · obtain ⟨w,hw⟩ := hB j
      refine ⟨w.extend,?_⟩
      intro x
      change f x j=w.extend.val (Fin.snoc B.H _) x
      rw [WRep.extend_val,hw]

def arrA {n r} (B : Bank n r) (ww : Fin n → WRep n r) (p : Fin r × Fin 3) : V n :=
  if p.2=0 then (B.w p.1 0).raw else if p.2=1 then (B.w p.1 1).raw else fun i => (ww i).h p.1

def writeQ {n r} (o : WRep n r) (ww : Fin n → WRep n r) (x : V n) :=
  o.s+dotProduct (o.raw + fun i => (ww i).s) x+∑ i,∑ j, (ww i).raw j*x i*x j

theorem agg {n r} (B : Bank n r) (o : WRep n r) (ww : Fin n → WRep n r) (x : V n) :
    o.val B.H x + ∑ i, x i*(ww i).val B.H x =
      writeQ o ww x + ∑ i, (o.h i+dotProduct (arrA B ww (i,2)) x)*B.H i x := by
  simp only [WRep.val,writeQ,arrA,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    if_false,dotProduct, Pi.add_apply, add_mul,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum,Finset.sum_mul]
  have h₁ : (∑ i, x i*(ww i).s)=∑ i, (ww i).s*x i := by
    apply Finset.sum_congr rfl;intro i _;ring
  have h₂ : (∑ i,∑ j, x i*((ww i).raw j*x j))= ∑ i,∑ j, (ww i).raw j*x i*x j := by
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
  have h₃ : (∑ i,∑ j, x i*((ww i).h j*B.H j x))=∑ j,∑ i, ((ww i).h j*x i)*B.H j x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
  rw [h₁,h₂,h₃]
  ring

theorem assemble {n r} {g : V n → F} {env : V n → V (n+r)}
    (run : Run n r env) {o : Fn (n+r)} {p : Fin n → Fn (n+r)}
    (ho : o∈degree (n+r) 1) (hp : ∀ i,p i∈degree (n+r) 1)
    (h : ∀ y,g y=o (env y)+∑ i, y i*p i (env y)) : Nonempty (Features g r) := by
  classical
  obtain ⟨B,hB⟩ := bank_run run
  obtain ⟨out,eo⟩ := real_linear hB ho
  choose ww ew using fun i => real_linear hB (hp i)
  refine ⟨⟨arrA B ww,writeQ out ww,⟨_,_,_,fun _ => rfl⟩,B.H,out.h,
    (fun i k => (B.w i k).s),(fun i k => (B.w i k).h),B.bound,?_,?_⟩⟩
  · intro i x
    simpa [arrA,WRep.val] using B.gates i x
  · intro x
    rw [h,eo]
    simp_rw [ew]
    exact agg B out ww x

theorem fit_bound {n c} {g : V n → F} (R : Submodule F (V n))
    (rad : ∀ u, u∈R ↔ ∀ v w, T g u v w=0)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : ∀ a∈C.gates, GateDecode.legal a)
    (cost : C.gates.countP CircuitBridge.paid ≤ n+c)
    (ev : ∀ x y, C.eval (Lower.bits x++Lower.bits y)=GateDecode.bit (dotProduct x y+g y)) :
    n-Module.finrank F R ≤ 3*c ∧
      (n-Module.finrank F R=3*c → ∃ S : Features g c, Function.Surjective (featureMap S.A)) := by
  obtain ⟨r,env,o,p,le,hr,ho,hp,h⟩ := Lower.normalized_readout g c C legal cost ev
  obtain ⟨S⟩ := assemble hr ho hp h
  obtain ⟨bd,eq⟩ := feature_bound S R rad
  refine ⟨by omega,?_⟩
  intro hh
  have e : r=c := by omega
  subst r
  exact ⟨S,eq hh⟩
end PEqualNP.Outside.L_meta_30642_aux
