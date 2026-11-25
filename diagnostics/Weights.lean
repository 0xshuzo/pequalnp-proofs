import Mathlib
namespace Rectangle4603
open scoped BigOperators
inductive Formula (X : Type) where
  | input (x : X)
  | meet (a b : Formula X)
  | join (a b : Formula X)
def Formula.eval {X} (x : X → Bool) : Formula X → Bool
  | .input v => x v
  | .meet a b => a.eval x && b.eval x
  | .join a b => a.eval x || b.eval x
def Formula.leaves {X} : Formula X → Nat
  | .input _ => 1
  | .meet a b | .join a b => a.leaves+b.leaves
abbrev P := Fin 21
abbrev N := Fin 37
def mass (w : P → N → ℤ) (R : Finset P) (C : Finset N) :=
  ∑ i ∈ R, ∑ j ∈ C, w i j
theorem formulaBound {X} (w : P → N → ℤ) (U : P → X → Bool) (V : N → X → Bool)
    (d : ℤ) (leaf : ∀ x R C, (∀ i∈R,U i x=true) → (∀ j∈C,V j x=false) → mass w R C ≤ d)
    (f : Formula X) (R : Finset P) (C : Finset N)
    (on : ∀i∈R,f.eval (U i)=true) (off : ∀j∈C,f.eval (V j)=false) :
    mass w R C ≤ d * f.leaves := by
  induction f generalizing R C with
  | input x => simpa [Formula.leaves] using leaf x R C on off
  | join x y ix iy =>
    let p (i : P) := x.eval (U i)=true
    have l := ix (R.filter p) C
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (off j hj)).1)
    have r := iy (R.filter (fun i => ¬p i)) C (by
      intro i hi
      have e := Finset.mem_filter.mp hi
      exact (Bool.or_eq_true.mp (on i e.1)).resolve_left e.2)
      (fun j hj => (Bool.or_eq_false_iff.mp (off j hj)).2)
    have part : mass w (R.filter p) C + mass w (R.filter (fun i=>¬p i)) C = mass w R C :=
      Finset.sum_filter_add_sum_filter_not R p _
    simpa only [Formula.leaves,Nat.cast_add,mul_add,part] using add_le_add l r
  | meet x y ix iy =>
    let p (j : N) := x.eval (V j)=false
    have l := ix R (C.filter p)
      (fun i hi => (Bool.and_eq_true.mp (on i hi)).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have r := iy R (C.filter (fun j=>¬p j))
      (fun i hi => (Bool.and_eq_true.mp (on i hi)).2) (by
        intro j hj
        have e := Finset.mem_filter.mp hj
        have both := off j e.1
        change (x.eval (V j) && y.eval (V j))=false at both
        cases v : x.eval (V j)
        · exact (e.2 v).elim
        · simpa [v] using both)
    have part : mass w R (C.filter p) + mass w R (C.filter (fun j=>¬p j)) = mass w R C := by
      unfold mass
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_filter_add_sum_filter_not C p _
    simpa only [Formula.leaves,Nat.cast_add,mul_add,part] using add_le_add l r

def choose {m : Nat} (ids : Fin m → P) (legal : P → Bool) (marks : Fin m → Bool) : Finset P :=
  (Finset.univ.filter fun t => legal (ids t) && marks t).image ids
theorem certifiedLeaf {X} {m : Nat} (w : P → N → ℤ) (U : P → X → Bool) (V : N → X → Bool)
    (d : ℤ) (ids : X → Fin m → P)
    (coverage : ∀ x i, U i x=true → ∃t,ids x t=i)
    (small : ∀ x marks, let A := choose (ids x) (fun i => U i x) marks;
      (∑ j : N, if V j x then (0:ℤ) else max 0 (∑ i∈A,w i j)) ≤ d) :
    ∀ x R C, (∀ i∈R,U i x=true) → (∀ j∈C,V j x=false) → mass w R C ≤ d := by
  intro x R C on off
  let marks (t : Fin m) := decide (ids x t ∈ R)
  have eq : choose (ids x) (fun i=>U i x) marks = R := by
    ext i
    simp only [choose,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
      Bool.and_eq_true,marks,decide_eq_true_eq]
    constructor
    · rintro ⟨t,⟨_,ht⟩,rfl⟩
      exact ht
    · intro hi
      obtain ⟨t,ht⟩ := coverage x i (on i hi)
      exact ⟨t,⟨ht ▸ on i hi,ht ▸ hi⟩,ht⟩
  have lim := small x marks
  dsimp only at lim
  rw [eq] at lim
  unfold mass
  rw [Finset.sum_comm]
  apply le_trans _ lim
  trans ∑ j∈C, if V j x then (0:ℤ) else max 0 (∑ i∈R,w i j)
  · apply Finset.sum_le_sum
    intro j hj
    rw [off j hj]
    exact le_max_right _ _
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j _ _
    split <;> simp
def posRows : Array Nat := #[129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208]
def negRows : Array Nat := #[127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
def pos (i : P) (x : Fin 14) := (posRows[i.val]?.getD 0).testBit x.val
def neg (j : N) (x : Fin 14) := (negRows[j.val]?.getD 0).testBit x.val
def matrix : Array (Array ℤ) := #[#[0,2,-1,0,1,0,0,-1,0,0,0,1,0,0,0,0,1,1,0,0,0,1,0,0,-1,1,0,0,0,0,-1,0,1,0,1,2,0],#[0,2,1,0,-1,0,0,1,0,0,0,1,0,0,0,0,1,1,0,0,0,1,0,0,2,-1,0,0,0,0,-1,0,1,0,1,-1,0],#[0,2,1,0,1,0,0,1,0,0,0,-1,0,0,0,0,1,-1,0,0,0,1,0,0,-1,1,0,0,0,0,2,0,1,0,1,-1,0],#[0,-1,2,0,1,0,0,-1,0,0,0,1,0,0,0,0,-1,1,0,0,0,1,0,0,1,1,0,0,0,0,1,0,1,0,-1,2,0],#[0,1,2,0,1,0,0,1,0,0,0,1,0,0,0,0,2,-1,0,0,0,1,0,0,1,-1,0,0,0,0,1,0,1,0,-1,-1,0],#[0,1,2,0,-1,0,0,1,0,0,0,-1,0,0,0,0,-1,1,0,0,0,1,0,0,1,1,0,0,0,0,1,0,1,0,2,-1,0],#[0,-1,1,0,2,0,0,1,0,0,0,1,0,0,0,0,1,1,0,0,0,1,0,0,2,-1,0,0,0,0,1,0,-1,0,-1,1,0],#[0,1,1,0,2,0,0,-1,0,0,0,1,0,0,0,0,1,-1,0,0,0,1,0,0,-1,1,0,0,0,0,1,0,2,0,-1,1,0],#[0,1,-1,0,2,0,0,1,0,0,0,-1,0,0,0,0,1,1,0,0,0,1,0,0,-1,1,0,0,0,0,1,0,-1,0,2,1,0],#[0,-1,-1,0,1,0,0,2,0,0,0,1,0,0,0,0,1,1,0,0,0,-1,0,0,1,1,0,0,0,0,1,0,-1,0,1,2,0],#[0,1,1,0,1,0,0,2,0,0,0,-1,0,0,0,0,1,1,0,0,0,2,0,0,1,-1,0,0,0,0,1,0,-1,0,1,-1,0],#[0,1,1,0,-1,0,0,2,0,0,0,1,0,0,0,0,1,-1,0,0,0,-1,0,0,1,1,0,0,0,0,1,0,2,0,1,-1,0],#[0,-1,1,0,1,0,0,1,0,0,0,2,0,0,0,0,1,-1,0,0,0,-1,0,0,1,1,0,0,0,0,2,0,1,0,-1,1,0],#[0,1,1,0,1,0,0,-1,0,0,0,2,0,0,0,0,1,1,0,0,0,2,0,0,1,-1,0,0,0,0,-1,0,1,0,-1,1,0],#[0,1,-1,0,-1,0,0,1,0,0,0,2,0,0,0,0,1,1,0,0,0,-1,0,0,1,1,0,0,0,0,-1,0,1,0,2,1,0],#[0,1,-1,0,1,0,0,1,0,0,0,1,0,0,0,0,2,2,0,0,0,1,0,0,1,-1,0,0,0,0,-1,0,-1,0,1,1,0],#[0,-1,1,0,1,0,0,1,0,0,0,-1,0,0,0,0,-1,2,0,0,0,1,0,0,1,1,0,0,0,0,2,0,-1,0,1,1,0],#[0,1,1,0,-1,0,0,-1,0,0,0,1,0,0,0,0,-1,2,0,0,0,1,0,0,1,1,0,0,0,0,-1,0,2,0,1,1,0],#[0,-1,1,0,-1,0,0,1,0,0,0,1,0,0,0,0,-1,1,0,0,0,-1,0,0,2,2,0,0,0,0,1,0,1,0,1,1,0],#[0,1,-1,0,1,0,0,1,0,0,0,1,0,0,0,0,2,-1,0,0,0,-1,0,0,-1,2,0,0,0,0,1,0,1,0,1,1,0],#[0,1,1,0,1,0,0,-1,0,0,0,-1,0,0,0,0,-1,1,0,0,0,2,0,0,-1,2,0,0,0,0,1,0,1,0,1,1,0]]
def weight (i : P) (j : N) := (((matrix[i.val]?).getD #[])[j.val]?.getD 0
def support : Array (Array Nat) := #[#[0,3,9],#[1,6,18],#[4,15,19],#[2,12,16],#[10,13,20],#[7,11,17],#[5,8,14],#[0,1,2],#[3,4,5],#[6,7,8],#[9,10,11],#[12,13,14],#[15,16,17],#[18,19,20]]
def ids (x : Fin 14) (t : Fin 3) : P := Fin.ofNat 21 ((((support[x.val]?).getD #[])[t.val]?).getD 0)
set_option maxHeartbeats 0 in
theorem boundBase (f : Formula (Fin 14)) (h₁ : ∀ i, f.eval (pos i)=true) (h₀ : ∀ j, f.eval (neg j)=false) : 28 ≤ f.leaves := by
  have cover : ∀ x i, pos i x=true → ∃t,ids x t=i := by decide +kernel
  have limit : ∀ x (marks : Fin 3 → Bool), let A := choose (ids x) (fun i => pos i x) marks;
      (∑ j : N, if neg j x then (0:ℤ) else max 0 (∑ i∈A,weight i j)) ≤ 6 := by decide +kernel
  have total : mass weight Finset.univ Finset.univ = 168 := by decide +kernel
  have q := formulaBound weight pos neg 6 (certifiedLeaf weight pos neg 6 ids cover limit)
    f Finset.univ Finset.univ (fun i _ => h₁ i) (fun j _ => h₀ j)
  rw [total] at q
  omega
end Rectangle4603
