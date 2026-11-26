import PEqualNP.Defs
namespace Research9350.StrictRank
open Finset
abbrev V := Fin 21
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (r c : V) : Bool := !((board.getD r.val 0).testBit c.val)
def column (c r : V) : ℚ := if zeroCell r c then 1 else 0
def dual (c r : V) : ℚ := if zeroCell r c then 1 else -3
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem evaluate : ∀ i j : V, (∑ r : V, dual i r * column j r) =
    if i=j then 16 else 0 := by decide +kernel

theorem independent : LinearIndependent ℚ column := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff rel i
  have coord (r : V) : (∑ j : V, coeff j * column j r)=0 := by
    simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun rel r
  have dot : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r))=0 := by
    simp [coord]
  have swap : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r)) =
      ∑ j : V, coeff j * (∑ r : V, dual i r * column j r) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    ring
  rw [swap] at dot
  simp_rw [evaluate] at dot
  have atI : (∑ j : V, coeff j * (if i=j then 16 else 0))=coeff i * 16 := by
    rw [sum_eq_single_of_mem i (mem_univ i)]
    · simp
    · intro j _ ne
      simp [Ne.symm ne]
  rw [atI] at dot
  linarith

abbrev Box := Finset V × Finset V
def rv (b : Box) (r : V) : ℚ := if r ∈ b.1 then 1 else 0
def cv (b : Box) (c : V) : ℚ := if c ∈ b.2 then 1 else 0
def unitRow (s r : V) : ℚ := if s = r then 1 else 0


def pair (c : V) (f : V → ℚ) := ∑ r : V, dual c r * f r
def actual {m : Nat} (B : Fin m → Box) (c : V) : V → ℚ :=
  ∑ i : Fin m, cv (B i) c • rv (B i)

theorem existsMinor (T : Fin 3 → Fin 3 → ℚ)
    (pos : ∀ j, 0 < T j j)
    (peaks : ∀ i j, i ≠ j → T i j < T j j) :
    ∃ (u v x y : Fin 3), T u x * T v y ≠ T u y * T v x := by
  by_contra! none
  have h (r j : Fin 3) : T 0 0 * T r j = T 0 j * T r 0 := none 0 r 0 j
  have neg (j : Fin 3) (nz : j ≠ 0) : T 0 j < 0 := by
    by_contra! nonneg
    have le := mul_le_mul_of_nonneg_left (peaks j 0 nz).le nonneg
    have lt := mul_lt_mul_of_pos_left (peaks 0 j (Ne.symm nz)) (pos 0)
    nlinarith only [le, lt, h j j]
  have n1 : T 0 1 < 0 := neg 1 (by decide)
  have n2 : T 0 2 < 0 := neg 2 (by decide)
  have a := mul_lt_mul_of_pos_left (peaks 2 1 (by decide)) (pos 0)
  have b := mul_lt_mul_of_pos_left (peaks 1 2 (by decide)) (pos 0)
  rw [h 2 1,h 1 1] at a
  rw [h 1 2,h 2 2] at b
  rcases le_total (T 2 0) (T 1 0) with le | le
  · exact (not_lt_of_ge (mul_le_mul_of_nonpos_left le n1.le)) a
  · exact (not_lt_of_ge (mul_le_mul_of_nonpos_left le n2.le)) b

def pair_lin (d : V) : (V → ℚ) →ₗ[ℚ] ℚ := 
  { toFun := pair d
    map_add' := by
      intro a b
      simp [pair,mul_add,sum_add_distrib]
    map_smul' := by
      intro a b
      simp only [pair,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring }

theorem pairingPeak {m : Nat} (B : Fin m → Box)
    (law : ∀ r c, zeroCell r c = false → actual B c r = 0)
    (lower : ∀ r c, column c r ≤ actual B c r) (i j : V) (ne : i ≠ j) :
    pair i (actual B j) + 16 ≤ pair j (actual B j) := by
  have each (r : V) : (dual j r - dual i r) * column j r ≤
      (dual j r - dual i r) * actual B j r := by
    cases hz : zeroCell r j with
    | false => simp [column,hz,law r j hz]
    | true =>
      apply mul_le_mul_of_nonneg_left (lower r j)
      cases hi : zeroCell r i <;> norm_num [dual,hz,hi]
  have q := sum_le_sum (s := (univ : Finset V)) (fun r _ => each r)
  simp only [sub_mul,sum_sub_distrib] at q
  rw [evaluate,evaluate] at q
  simp [ne] at q
  change (∑ r : V, dual i r * actual B j r) + 16 ≤ ∑ r : V, dual j r * actual B j r
  linarith

theorem pairingPos {m : Nat} (B : Fin m → Box)
    (law : ∀ r c, zeroCell r c = false → actual B c r = 0)
    (lower : ∀ r c, column c r ≤ actual B c r) (j : V) : 0 < pair j (actual B j) := by
  have term (r : V) : dual j r * column j r ≤ dual j r * actual B j r := by
    cases z : zeroCell r j with
    | true => simpa [dual,z] using lower r j
    | false => simp [dual,column,z,law r j z]
  have H := sum_le_sum (s := (univ : Finset V)) (fun r _ => term r)
  rw [evaluate] at H
  simp only [ite_true] at H
  change 0 < ∑ r : V, dual j r * actual B j r
  linarith

theorem doubleRank {m : Nat} (B : Fin m → Box) (S : Finset V)
    (d : Fin 3 → V) (inj : Function.Injective d) (outside : ∀ i, d i ∉ S)
    (W : Submodule ℚ (V → ℚ)) [Module.Finite ℚ W]
    (colIn : ∀ c ∈ S, column c ∈ W) (represented : ∀ c, actual B c ∈ W)
    (law : ∀ r c, zeroCell r c = false → actual B c r = 0)
    (lower : ∀ r c, column c r ≤ actual B c r) : S.card + 2 ≤ Module.finrank ℚ W := by
  classical
  let T (i j : Fin 3) := pair (d i) (actual B (d j))
  have pos (i : Fin 3) : 0 < T i i := pairingPos B law lower _
  have peaks (i j : Fin 3) (ne : i ≠ j) : T i j < T j j := by
    have q := pairingPeak B law lower (d i) (d j) (fun eq => ne (inj eq))
    change pair (d i) (actual B (d j)) < pair (d j) (actual B (d j))
    linarith
  obtain ⟨u,v,x,y,det⟩ := existsMinor T pos peaks
  let f (i : ↥S ⊕ Fin 2) : V → ℚ :=
    Sum.elim (fun s : ↥S => column s.val)
      (fun j : Fin 2 => if j = 0 then actual B (d x) else actual B (d y)) i
  have li : LinearIndependent ℚ f := by
    rw [Fintype.linearIndependent_iff]
    intro a rel i
    have sums : (∑ j : ↥S, a (.inl j) • column j.val) +
        (a (.inr 0) • actual B (d x) + a (.inr 1) • actual B (d y)) = 0 := by
      simpa [Fintype.sum_sum_type,Fin.sum_univ_two,f] using rel
    have eqn (w : Fin 3) : a (.inr 0) * T w x + a (.inr 1) * T w y = 0 := by
      let L := pair_lin (d w)
      have annihilates (s : ↥S) : L (column s.val) = 0 := by
        change ∑ r : V, dual (d w) r * column s.val r = 0
        rw [evaluate,if_neg (fun h => outside w (h.symm ▸ s.property))]
      have ev := congrArg (fun z => L z) sums
      simp only [map_add,map_sum,map_smul,annihilates,map_zero,smul_eq_mul,mul_zero,
        Finset.sum_const_zero,zero_add] at ev
      exact ev
    have e0 := eqn u
    have e1 := eqn v
    have z0 : a (.inr 0) = 0 := by
      apply (mul_eq_zero.mp (show a (.inr 0) * (T u x * T v y - T u y * T v x) = 0 by
        linear_combination T v y * e0 - T u y * e1)).resolve_right (sub_ne_zero.mpr det)
    have z1 : a (.inr 1) = 0 := by
      apply (mul_eq_zero.mp (show a (.inr 1) * (T u x * T v y - T u y * T v x) = 0 by
        linear_combination T u x * e1 - T v x * e0)).resolve_right (sub_ne_zero.mpr det)
    cases i with
    | inl j =>
      have rest : ∑ j : ↥S, a (.inl j) • column j.val = 0 := by
        simpa only [z0,z1,zero_smul,add_zero] using sums
      exact Fintype.linearIndependent_iff.mp (independent.comp Subtype.val Subtype.val_injective)
        (fun j : ↥S => a (.inl j)) rest j
    | inr j => fin_cases j <;> assumption
  have inside (i : ↥S ⊕ Fin 2) : f i ∈ W := by
    cases i with
    | inl j => exact colIn j.val j.property
    | inr j => by_cases h : j = 0 <;> simp [f,h,represented]
  let lifted (i : ↥S ⊕ Fin 2) : ↥W := ⟨f i,inside i⟩
  have li' : LinearIndependent ℚ lifted := LinearIndependent.of_comp W.subtype li
  simpa using li'.fintype_card_le_finrank

theorem strongMixedOne {m : Nat} (B : Fin m → Box) (badRows badCols : Finset V)
    (many : 3 ≤ badCols.card)
    (law : ∀ r c, zeroCell r c = false → actual B c r = 0)
    (lower : ∀ r c, column c r ≤ actual B c r)
    (agree : ∀ r ∉ badRows, ∀ c ∉ badCols,
      (∑ i : Fin m, cv (B i) c * rv (B i) r) = column c r) :
    23 ≤ m + badRows.card + badCols.card := by
  classical
  let vec : Fin m ⊕ ↥badRows → V → ℚ :=
    Sum.elim (fun i => rv (B i)) (fun s => unitRow s.val)
  let W := Submodule.span ℚ (Set.range vec)
  have member (i : Fin m ⊕ ↥badRows) : vec i ∈ W :=
    Submodule.subset_span ⟨i,rfl⟩
  let main (c : V) : V → ℚ := ∑ i : Fin m, cv (B i) c • rv (B i)
  have mainIn (c : V) : main c ∈ W := by
    apply Submodule.sum_mem
    intro i _
    exact W.smul_mem _ (member (Sum.inl i))
  let clean := (Finset.univ : Finset V) \ badCols
  have colIn (c : ↥clean) : column c.val ∈ W := by
    have hc : c.val ∉ badCols := (Finset.mem_sdiff.mp c.property).2
    let delta (s : ↥badRows) := column c.val s.val - main c.val s.val
    have eq : column c.val = main c.val +
        ∑ s : ↥badRows, delta s • unitRow s.val := by
      funext r
      simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hr : r ∈ badRows
      · let s : ↥badRows := ⟨r,hr⟩
        rw [Finset.sum_eq_single s]
        · simp [s,unitRow,delta]
        · intro b _ ne
          have nd : b.val ≠ r := fun eq => ne (Subtype.ext eq)
          simp [unitRow,nd]
        · simp
      · have vanish (s : ↥badRows) : unitRow s.val r = 0 := by
          have ne : s.val ≠ r := fun e => hr (e ▸ s.property)
          simp [unitRow,ne]
        simp only [vanish, mul_zero, Finset.sum_const_zero, add_zero]
        simpa only [main,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
          using (agree r hr c.val hc).symm
    rw [eq]
    apply W.add_mem (mainIn _)
    apply Submodule.sum_mem
    intro s _
    exact W.smul_mem _ (member (Sum.inr s))
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range vec)
  obtain ⟨K,ks,hk⟩ := Finset.exists_subset_card_eq many
  let e : ↥K ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hk)
  let d (i : Fin 3) : V := (e.symm i).val
  have di : Function.Injective d := Subtype.val_injective.comp e.symm.injective
  have out (i : Fin 3) : d i ∉ clean := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 (ks (e.symm i).property)
  have lo := doubleRank B clean d di out W (fun c hc => colIn ⟨c,hc⟩) mainIn law lower
  have hi : Module.finrank ℚ W ≤ m + badRows.card := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range vec)) ≤ _
    refine (finrank_span_le_card (Set.range vec)).trans ?_
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le vec
  have all : (Finset.univ : Finset V).card = 21 := by decide +kernel
  have cleanCard : clean.card = 21 - badCols.card := by
    dsimp [clean]
    rw [card_sdiff,inter_univ,all]
  have le : badCols.card ≤ 21 := all ▸ Finset.card_le_univ badCols
  omega

def flip (s : Finset V) : Finset V := s.image (fun p => -p)
def transpose (b : Box) : Box := (flip b.2,flip b.1)
theorem flipCard (s : Finset V) : (flip s).card=s.card := by
  apply card_image_of_injective
  exact neg_injective
theorem flipMem (s : Finset V) (p : V) : p∈flip s ↔ -p∈s := by
  constructor
  · intro h
    obtain ⟨v,hv,eq⟩ := mem_image.mp h
    rw [←eq,neg_neg]
    exact hv
  · intro h
    exact mem_image.mpr ⟨-p,h,neg_neg p⟩
theorem mixed_rank {m : Nat} (B : Fin m → Box) (badRows badCols : Finset V)
    (agree : ∀ r ∉ badRows, ∀ c ∉ badCols,
      (∑ i : Fin m, cv (B i) c * rv (B i) r) = column c r) :
    21 ≤ m + badRows.card + badCols.card := by
  classical
  let vec : Fin m ⊕ ↥badRows → V → ℚ :=
    Sum.elim (fun i => rv (B i)) (fun s => unitRow s.val)
  let W := Submodule.span ℚ (Set.range vec)
  have member (i : Fin m ⊕ ↥badRows) : vec i ∈ W :=
    Submodule.subset_span ⟨i,rfl⟩
  let main (c : V) : V → ℚ := ∑ i : Fin m, cv (B i) c • rv (B i)
  have mainIn (c : V) : main c ∈ W := by
    apply Submodule.sum_mem
    intro i _
    exact W.smul_mem _ (member (Sum.inl i))
  let clean := (Finset.univ : Finset V) \ badCols
  have colIn (c : ↥clean) : column c.val ∈ W := by
    have hc : c.val ∉ badCols := (Finset.mem_sdiff.mp c.property).2
    let delta (s : ↥badRows) := column c.val s.val - main c.val s.val
    have eq : column c.val = main c.val +
        ∑ s : ↥badRows, delta s • unitRow s.val := by
      funext r
      simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hr : r ∈ badRows
      · let s : ↥badRows := ⟨r,hr⟩
        rw [Finset.sum_eq_single s]
        · simp [s,unitRow,delta]
        · intro b _ ne
          have nd : b.val ≠ r := fun eq => ne (Subtype.ext eq)
          simp [unitRow,nd]
        · simp
      · have vanish (s : ↥badRows) : unitRow s.val r = 0 := by
          have ne : s.val ≠ r := fun e => hr (e ▸ s.property)
          simp [unitRow,ne]
        simp only [vanish, mul_zero, Finset.sum_const_zero, add_zero]
        simpa only [main,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
          using (agree r hr c.val hc).symm
    rw [eq]
    apply W.add_mem (mainIn _)
    apply Submodule.sum_mem
    intro s _
    exact W.smul_mem _ (member (Sum.inr s))
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range vec)
  let lifted (c : ↥clean) : ↥W := ⟨column c.val,colIn c⟩
  have li : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    exact independent.comp Subtype.val Subtype.val_injective
  have lo : clean.card ≤ Module.finrank ℚ W := by simpa using li.fintype_card_le_finrank
  have hi : Module.finrank ℚ W ≤ m + badRows.card := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range vec)) ≤ _
    refine (finrank_span_le_card (Set.range vec)).trans ?_
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le vec
  have all : (Finset.univ : Finset V).card = 21 := by decide +kernel
  have cleanCard : clean.card = 21 - badCols.card := by
    dsimp [clean]
    rw [card_sdiff,inter_univ,all]
  have le : badCols.card ≤ 21 := all ▸ Finset.card_le_univ badCols
  omega

theorem flipActual {m : Nat} (B : Fin m → Box) (r c : V) :
    actual (fun b => transpose (B b)) c r = actual B (-r) (-c) := by
  simp only [actual,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro b _
  simp only [cv,rv,transpose,flipMem]
  exact mul_comm _ _

theorem reflZero : ∀ r c : V, zeroCell r c = zeroCell (-c) (-r) := by decide +kernel

theorem nineMixed {m : Nat} (B : Fin m → Box) (bound : m ≤ 14)
    (badRows badCols : Finset V)
    (law : ∀ r c, zeroCell r c = false → actual B c r = 0)
    (lower : ∀ r c, column c r ≤ actual B c r)
    (agree : ∀ r ∉ badRows, ∀ c ∉ badCols, actual B c r = column c r) :
    9 ≤ badRows.card + badCols.card := by
  classical
  have expand (D : Fin m → Box) (r c : V) : actual D c r =
      ∑ i, cv (D i) c * rv (D i) r := by
    simp [actual,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases cols : 3 ≤ badCols.card
  · have h := strongMixedOne B badRows badCols cols law lower
        (fun r hr c hc => (expand B r c).symm.trans (agree r hr c hc))
    omega
  by_cases rows : 3 ≤ badRows.card
  · let D (i : Fin m) := transpose (B i)
    have g (r c : V) : actual D c r = actual B (-r) (-c) := flipActual B r c
    have cc (r c : V) : column c r = column (-r) (-c) := by
      unfold column
      rw [reflZero r c]
    have l (r c : V) (z : zeroCell r c = false) : actual D c r = 0 := by
      rw [g]
      exact law (-c) (-r) ((reflZero r c).symm.trans z)
    have low (r c : V) : column c r ≤ actual D c r := by
      rw [g,cc r c]
      exact lower _ _
    have a (r : V) (hr : r ∉ flip badCols) (c : V) (hc : c ∉ flip badRows) :
        (∑ i, cv (D i) c * rv (D i) r) = column c r := by
      rw [← expand D,g,cc r c]
      exact agree (-c) (fun h => hc ((flipMem badRows c).mpr h))
        (-r) (fun h => hr ((flipMem badCols r).mpr h))
    have h := strongMixedOne D (flip badCols) (flip badRows) (by simpa [flipCard] using rows)
        l low a
    simp only [flipCard] at h
    omega
  · have h := mixed_rank B badRows badCols
        (fun r hr c hc => (expand B r c).symm.trans (agree r hr c hc))
    omega

end Research9350.StrictRank
