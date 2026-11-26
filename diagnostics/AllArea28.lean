import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9345.Rank
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

theorem budget {n m : Nat} (cols : Fin n → V) (distinct : Function.Injective cols)
    (rows : Fin m → Finset V) (used : Fin n → Finset (Fin m))
    (exactly : ∀ j r, (∑ b ∈ used j, (if r∈rows b then (1:ℚ) else 0)) = column (cols j) r) :
    n≤m := by
  classical
  let R (b : Fin m) (r : V) : ℚ := if r∈rows b then 1 else 0
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (j : Fin n) : column (cols j) ∈ W := by
    have eq : column (cols j) = ∑ b ∈ used j, R b := by
      funext r
      simpa only [Finset.sum_apply,R] using (exactly j r).symm
    rw [eq]
    exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b,rfl⟩
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (j : Fin n) : ↥W := ⟨column (cols j),inSpan j⟩
  have li : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    exact independent.comp cols distinct
  have lo : n ≤ Module.finrank ℚ W := by simpa using li.fintype_card_le_finrank
  have hi : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lo.trans hi

theorem sevenNotSix (cols : Fin 7 → V) (distinct : Function.Injective cols)
    (rows : Fin 6 → Finset V) (used : Fin 7 → Finset (Fin 6)) :
    ¬ (∀ j r, (∑ b ∈ used j, (if r∈rows b then (1:ℚ) else 0)) = column (cols j) r) := by
  intro exactCover
  have impossible := budget cols distinct rows used exactCover
  omega
abbrev Box := Finset V × Finset V
def flag (s : Finset V) (p : V) : Nat := if p∈s then 1 else 0
def zn (p j : V) : Nat := if zeroCell p j then 1 else 0
theorem znCount : ∀ j, (∑ p : V, zn p j)=16 := by decide +kernel
theorem flags (s : Finset V) : (∑ p : V, flag s p)=s.card := by classical simp [flag]
def count {m} (B : Fin m → Box) (j : V) := ∑ b : Fin m, flag (B b).2 j
def load {m} (B : Fin m → Box) (r j : V) := ∑ b : Fin m, flag (B b).1 r * flag (B b).2 j
theorem countTotal {m w} (B : Fin m → Box) (hw : ∀ b, (B b).2.card=w) :
    (∑ j : V, count B j)=m*w := by
  unfold count
  rw [sum_comm]
  simp only [flags,hw]
  simp
theorem loadTotal {m h} (B : Fin m → Box) (hh : ∀ b, (B b).1.card=h) (j : V) :
    (∑ r : V, load B r j)=h*count B j := by
  unfold load count
  rw [sum_comm]
  simp only [←sum_mul,flags,hh,mul_sum]
theorem tightSums {α : Type} [Fintype α] {f g : α → Nat}
    (point : ∀ i, f i≤g i) (eq : (∑ i, f i)=(∑ i, g i)) (i : α) : f i=g i := by
  by_contra ne
  have lt := Finset.sum_lt_sum (fun j (_ : j∈univ) => point j)
    ⟨i,mem_univ i,lt_of_le_of_ne (point i) ne⟩
  omega

theorem noSixFourBySeven (A : Fin 6 → Box) (B : Fin 7 → Box)
    (ar : ∀ b, (A b).1.card=4) (ac : ∀ b, (A b).2.card=7)
    (br : ∀ b, (B b).1.card=7) (bc : ∀ b, (B b).2.card=4)
    (cover : ∀ r j, zn r j ≤ load A r j + load B r j) : False := by
  classical
  have Ay := countTotal A ac
  have Bx := countTotal B bc
  have need (j : V) : 16 ≤ 4*count A j+7*count B j := by
    have s := sum_le_sum (fun (r : V) (_ : r∈univ) => cover r j)
    simpa only [znCount,sum_add_distrib,loadTotal A ar,loadTotal B br] using s
  have lower (j : V) : 8 ≤ 3*count B j + 2*count A j := by
    have h := need j
    by_cases z : count B j=0
    · omega
    by_cases one : count B j=1
    · omega
    by_cases two : count B j=2 <;> omega
  have tight (j : V) : 8 = 3*count B j + 2*count A j := by
    apply tightSums lower _ j
    simp only [sum_add_distrib,←mul_sum,Bx,Ay]
    decide
  have binary (j : V) : count B j=0 ∨ count B j=2 := by have := tight j; omega
  let T : Finset V := univ.filter (fun j => count B j=0)
  have lab (j : V) : j∈T ↔ count B j=0 := by simp [T]
  have eq2 (j : V) : count B j + 2*flag T j=2 := by
    rcases binary j with z|tw
    · simp [flag,(lab j).2 z,z]
    · have outside : j∉T := fun h => by have := (lab j).1 h; omega
      simp [flag,outside,tw]
  have Tsize : T.card=7 := by
    have tot := sum_congr (s₁:=univ) rfl (fun (j : V) (_ : j∈univ) => eq2 j)
    simp only [sum_add_distrib,←mul_sum,flags,Bx] at tot
    have c : (∑ _ : V, (2:Nat))=42 := by decide +kernel
    rw [c] at tot
    omega
  let e : ↥T ≃ Fin 7 := Fintype.equivFinOfCardEq (by simpa using Tsize)
  let cols (j : Fin 7) : V := (e.symm j).val
  have good (j : Fin 7) : count B (cols j)=0 := (lab _).1 (e.symm j).property
  have a4 (j : Fin 7) : count A (cols j)=4 := by have := tight (cols j); rw [good] at this; omega
  have zeroLoad (j : Fin 7) (r : V) : load B r (cols j)=0 := by
    have pool := loadTotal B br (cols j)
    rw [good, Nat.mul_zero] at pool
    have le := Finset.single_le_sum (f:=fun p : V => load B p (cols j))
      (fun _ _ => Nat.zero_le _) (mem_univ r)
    omega
  have exactA (j : Fin 7) (r : V) : zn r (cols j)=load A r (cols j) := by
    apply tightSums (fun p => by simpa [zeroLoad] using cover p (cols j)) _ r
    rw [znCount,loadTotal A ar,a4]
  let useBox (j : Fin 7) := univ.filter (fun b : Fin 6 => cols j∈(A b).2)
  apply sevenNotSix cols (fun i j eq => e.symm.injective (Subtype.ext eq)) (fun b => (A b).1) useBox
  intro j r
  have countEq : (∑ b∈useBox j, flag (A b).1 r)=zn r (cols j) := by
    rw [exactA,load]
    unfold useBox
    rw [sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases h : cols j∈(A b).2 <;> simp [flag,h]
  have casted := congrArg (fun n : Nat => (n:ℚ)) countEq
  simpa [Nat.cast_sum,flag,zn,column] using casted

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
theorem swapped {m} (B : Fin m → Box) (r j : V) :
    load (fun i => transpose (B i)) r j=load B (-j) (-r) := by
  unfold load
  apply sum_congr rfl
  intro i _
  simp only [transpose,flag,flipMem]
  exact Nat.mul_comm _ _
theorem reflection : ∀ r j : V, zn r j=zn (-j) (-r) := by decide +kernel
theorem noSevenFourBySeven (A : Fin 7 → Box) (B : Fin 6 → Box)
    (ar : ∀ b, (A b).1.card=4) (ac : ∀ b, (A b).2.card=7)
    (br : ∀ b, (B b).1.card=7) (bc : ∀ b, (B b).2.card=4)
    (cover : ∀ r j, zn r j ≤ load A r j + load B r j) : False := by
  apply noSixFourBySeven (fun i => transpose (B i)) (fun i => transpose (A i))
  · intro i
    exact (flipCard _).trans (bc i)
  · intro i
    exact (flipCard _).trans (br i)
  · intro i
    exact (flipCard _).trans (ac i)
  · intro i
    exact (flipCard _).trans (ar i)
  · intro r j
    rw [swapped,swapped,reflection r j,Nat.add_comm]
    exact cover (-j) (-r)

theorem allocation {m n} (A : Fin m → Box) (B : Fin n → Box)
    (ar : ∀ b, (A b).1.card=4) (ac : ∀ b, (A b).2.card=7)
    (br : ∀ b, (B b).1.card=7) (bc : ∀ b, (B b).2.card=4)
    (cover : ∀ r j, zn r j ≤ load A r j + load B r j) :
    168 ≤ 14*m+12*n := by
  have price (j : V) : 8 ≤ 3*count B j + 2*count A j := by
    have s := sum_le_sum (fun (r : V) (_ : r∈univ) => cover r j)
    simp only [znCount,sum_add_distrib,loadTotal A ar,loadTotal B br] at s
    by_cases z : count B j=0
    · omega
    by_cases one : count B j=1
    · omega
    by_cases two : count B j=2 <;> omega
  have total := sum_le_sum (fun (j : V) (_ : j∈univ) => price j)
  have eight : (∑ _ : V, (8:Nat))=168 := by decide +kernel
  simp only [eight,sum_add_distrib,←mul_sum,countTotal A ac,countTotal B bc] at total
  omega

theorem noOrdinaryMaximum {m n} (cap : m+n≤13) (A : Fin m → Box) (B : Fin n → Box)
    (ar : ∀ b, (A b).1.card=4) (ac : ∀ b, (A b).2.card=7)
    (br : ∀ b, (B b).1.card=7) (bc : ∀ b, (B b).2.card=4)
    (cover : ∀ r j, zn r j ≤ load A r j + load B r j) : False := by
  have first := allocation A B ar ac br bc cover
  have alt (r j : V) : zn r j ≤ load (fun i => transpose (B i)) r j +
      load (fun i => transpose (A i)) r j := by
    rw [swapped,swapped,reflection r j,Nat.add_comm]
    exact cover (-j) (-r)
  have second := allocation (fun i => transpose (B i)) (fun i => transpose (A i))
    (fun i => (flipCard _).trans (bc i)) (fun i => (flipCard _).trans (br i))
    (fun i => (flipCard _).trans (ac i)) (fun i => (flipCard _).trans (ar i)) alt
  have orient : (m=6 ∧ n=7) ∨ (m=7 ∧ n=6) := by omega
  rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact noSixFourBySeven A B ar ac br bc cover
  · exact noSevenFourBySeven A B ar ac br bc cover

end PEqualNP.Outside.L_meta_9345.Rank
