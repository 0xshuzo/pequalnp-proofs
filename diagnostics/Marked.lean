import Mathlib
namespace Marked4603
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
abbrev P := Fin 22
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
      exact (Bool.or_eq_true_iff.mp (on i e.1)).resolve_left e.2)
      (fun j hj => (Bool.or_eq_false_iff.mp (off j hj)).2)
    have part : mass w (R.filter p) C + mass w (R.filter (fun i=>¬p i)) C = mass w R C :=
      Finset.sum_filter_add_sum_filter_not R p _
    simpa only [Formula.leaves,Nat.cast_add,mul_add,part] using add_le_add l r
  | meet x y ix iy =>
    let p (j : N) := x.eval (V j)=false
    have l := ix R (C.filter p)
      (fun i hi => (Bool.and_eq_true_iff.mp (on i hi)).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have r := iy R (C.filter (fun j=>¬p j))
      (fun i hi => (Bool.and_eq_true_iff.mp (on i hi)).2) (by
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
def pos (i : Fin 21) (x : Fin 14) := (posRows[i.val]?.getD 0).testBit x.val
def neg (j : N) (x : Fin 14) := (negRows[j.val]?.getD 0).testBit x.val
def u0 (i : P) (x : Fin 14) := if h : i.val<21 then pos ⟨i.val,h⟩ x else neg 36 x
def matrix0 : Array (Array ℤ) := #[#[56,0,0,56,0,14,-7,0,56,-56,-7,0,14,-7,7,-7,0,0,14,-7,7,0,-7,28,0,0,14,-7,28,-7,0,7,0,7,0,0,0],#[56,0,0,14,0,56,-7,0,14,28,-7,0,14,7,-7,7,0,0,14,7,-7,0,7,28,0,0,56,-7,-56,-7,0,-7,0,-7,0,0,0],#[56,0,0,14,0,14,7,0,14,28,7,0,56,-7,-7,-7,0,0,56,-7,-7,0,-7,-56,0,0,14,7,28,7,0,-7,0,-7,0,0,0],#[56,0,0,56,0,-7,14,0,-56,56,-7,0,-7,14,28,-7,0,0,-7,14,7,0,-7,7,0,0,-7,14,7,-7,0,7,0,28,0,0,0],#[56,0,0,14,0,7,14,0,28,14,7,0,7,14,28,7,0,0,-7,56,-7,0,-7,-7,0,0,-7,56,-7,-7,0,-7,0,-56,0,0,0],#[56,0,0,14,0,-7,56,0,28,14,-7,0,-7,56,-56,-7,0,0,7,14,-7,0,7,-7,0,0,7,14,-7,7,0,-7,0,28,0,0,0],#[56,0,0,-7,0,56,14,0,-7,7,14,0,-7,28,14,7,0,0,-7,7,14,0,28,7,0,0,-56,-7,56,-7,0,-7,0,-7,0,0,0],#[56,0,0,7,0,14,14,0,-7,-7,56,0,7,28,14,-7,0,0,-7,-7,56,0,-56,-7,0,0,28,7,14,-7,0,7,0,-7,0,0,0],#[56,0,0,-7,0,14,56,0,7,-7,14,0,-7,-56,56,-7,0,0,7,-7,14,0,28,-7,0,0,28,-7,14,7,0,-7,0,7,0,0,0],#[56,0,0,-56,0,-7,-7,0,56,56,14,0,-7,-7,7,14,0,0,-7,-7,28,0,14,7,0,0,-7,-7,7,14,0,28,0,7,0,0,0],#[56,0,0,28,0,7,7,0,14,14,14,0,-7,-7,-7,56,0,0,7,7,28,0,14,-7,0,0,-7,-7,-7,56,0,-56,0,-7,0,0,0],#[56,0,0,28,0,-7,-7,0,14,14,56,0,7,7,-7,14,0,0,-7,-7,-56,0,56,-7,0,0,7,7,-7,14,0,28,0,-7,0,0,0],#[56,0,0,-7,0,-7,28,0,-7,7,7,0,56,14,14,14,0,0,-56,-7,-7,0,-7,56,0,0,-7,7,7,28,0,14,0,-7,0,0,0],#[56,0,0,7,0,7,28,0,-7,-7,-7,0,14,14,14,56,0,0,28,7,7,0,-7,14,0,0,-7,-7,-7,-56,0,56,0,-7,0,0,0],#[56,0,0,-7,0,-7,-56,0,7,-7,-7,0,14,56,56,14,0,0,28,-7,-7,0,7,14,0,0,7,-7,-7,28,0,14,0,7,0,0,0],#[56,0,0,-7,0,7,-7,0,7,-7,28,0,28,-7,7,7,0,0,14,56,14,0,14,14,0,0,-7,-56,-7,-7,0,-7,0,56,0,0,0],#[56,0,0,-7,0,-7,7,0,-7,7,28,0,-56,-7,-7,-7,0,0,56,14,14,0,14,56,0,0,-7,28,7,7,0,-7,0,14,0,0,0],#[56,0,0,7,0,-7,-7,0,-7,-7,-56,0,28,7,-7,-7,0,0,14,14,56,0,56,14,0,0,7,28,-7,-7,0,7,0,14,0,0,0],#[56,0,0,-7,0,-56,-7,0,-7,7,-7,0,-7,7,-7,28,0,0,-7,28,-7,0,7,7,0,0,56,14,56,14,0,14,0,14,0,0,0],#[56,0,0,-7,0,28,-7,0,7,-7,7,0,7,-7,7,28,0,0,-7,-56,-7,0,-7,-7,0,0,14,56,14,14,0,14,0,56,0,0,0],#[56,0,0,7,0,28,7,0,-7,-7,-7,0,-7,-7,-7,-56,0,0,7,28,7,0,-7,-7,0,0,14,14,14,56,0,56,0,14,0,0,0],#[-90,0,0,10,0,10,10,0,10,10,10,0,10,10,10,10,0,0,10,10,10,0,10,10,0,0,10,10,10,10,0,10,0,10,0,0,0]]
def w0 (i : P) (j : N) := (((matrix0[i.val]?).getD #[])[j.val]?).getD 0
def support0 : Array (Array Nat) := #[#[0,3,9,0],#[1,6,18,1],#[4,15,19,4],#[2,12,16,2],#[10,13,20,10],#[7,11,17,7],#[5,8,14,5],#[0,1,2,21],#[3,4,5,21],#[6,7,8,21],#[9,10,11,21],#[12,13,14,21],#[15,16,17,21],#[18,19,20,21]]
def t0 (x : Fin 14) (t : Fin 4) : P := Fin.ofNat 22 ((((support0[x.val]?).getD #[])[t.val]?).getD 0)
def col0 (j : N) := ∑ i,w0 i j
set_option maxHeartbeats 0 in
theorem leftLeaf : ∀ x R C, (∀i∈R,u0 i x=true) → (∀j∈C,neg j x=false) → mass w0 R C ≤168 := by
  have cover : ∀ x i, u0 i x=true → ∃t,t0 x t=i := by decide +kernel
  have limit : ∀ x (marks : Fin 4 → Bool), let A := choose (t0 x) (fun i => u0 i x) marks;
      (∑ j : N, if neg j x then (0:ℤ) else max 0 (∑ i∈A,w0 i j)) ≤168 := by decide +kernel
  exact certifiedLeaf w0 u0 neg 168 t0 cover limit
def u1 (i : P) (x : Fin 14) := if h : i.val<21 then pos ⟨i.val,h⟩ x else neg 0 x
def matrix1 : Array (Array ℤ) := #[#[0,0,0,28,0,7,-7,0,28,-56,-7,0,7,-7,14,-7,0,0,7,-7,14,0,-7,56,0,0,7,-7,56,-7,0,14,0,14,0,0,56],#[0,0,0,7,0,28,-7,0,7,56,-7,0,7,14,-7,14,0,0,7,14,-7,0,14,56,0,0,28,-7,-56,-7,0,-7,0,-7,0,0,56],#[0,0,0,7,0,7,14,0,7,56,14,0,28,-7,-7,-7,0,0,28,-7,-7,0,-7,-56,0,0,7,14,56,14,0,-7,0,-7,0,0,56],#[0,0,0,28,0,-7,7,0,-56,28,-7,0,-7,7,56,-7,0,0,-7,7,14,0,-7,14,0,0,-7,7,14,-7,0,14,0,56,0,0,56],#[0,0,0,7,0,14,7,0,56,7,14,0,14,7,56,14,0,0,-7,28,-7,0,-7,-7,0,0,-7,28,-7,-7,0,-7,0,-56,0,0,56],#[0,0,0,7,0,-7,28,0,56,7,-7,0,-7,28,-56,-7,0,0,14,7,-7,0,14,-7,0,0,14,7,-7,14,0,-7,0,56,0,0,56],#[0,0,0,-7,0,28,7,0,-7,14,7,0,-7,56,7,14,0,0,-7,14,7,0,56,14,0,0,-56,-7,28,-7,0,-7,0,-7,0,0,56],#[0,0,0,14,0,7,7,0,-7,-7,28,0,14,56,7,-7,0,0,-7,-7,28,0,-56,-7,0,0,56,14,7,-7,0,14,0,-7,0,0,56],#[0,0,0,-7,0,7,28,0,14,-7,7,0,-7,-56,28,-7,0,0,14,-7,7,0,56,-7,0,0,56,-7,7,14,0,-7,0,14,0,0,56],#[0,0,0,-56,0,-7,-7,0,28,28,7,0,-7,-7,14,7,0,0,-7,-7,56,0,7,14,0,0,-7,-7,14,7,0,56,0,14,0,0,56],#[0,0,0,56,0,14,14,0,7,7,7,0,-7,-7,-7,28,0,0,14,14,56,0,7,-7,0,0,-7,-7,-7,28,0,-56,0,-7,0,0,56],#[0,0,0,56,0,-7,-7,0,7,7,28,0,14,14,-7,7,0,0,-7,-7,-56,0,28,-7,0,0,14,14,-7,7,0,56,0,-7,0,0,56],#[0,0,0,-7,0,-7,56,0,-7,14,14,0,28,7,7,7,0,0,-56,-7,-7,0,-7,28,0,0,-7,14,14,56,0,7,0,-7,0,0,56],#[0,0,0,14,0,14,56,0,-7,-7,-7,0,7,7,7,28,0,0,56,14,14,0,-7,7,0,0,-7,-7,-7,-56,0,28,0,-7,0,0,56],#[0,0,0,-7,0,-7,-56,0,14,-7,-7,0,7,28,28,7,0,0,56,-7,-7,0,14,7,0,0,14,-7,-7,56,0,7,0,14,0,0,56],#[0,0,0,-7,0,14,-7,0,14,-7,56,0,56,-7,14,14,0,0,7,28,7,0,7,7,0,0,-7,-56,-7,-7,0,-7,0,28,0,0,56],#[0,0,0,-7,0,-7,14,0,-7,14,56,0,-56,-7,-7,-7,0,0,28,7,7,0,7,28,0,0,-7,56,14,14,0,-7,0,7,0,0,56],#[0,0,0,14,0,-7,-7,0,-7,-7,-56,0,56,14,-7,-7,0,0,7,7,28,0,28,7,0,0,14,56,-7,-7,0,14,0,7,0,0,56],#[0,0,0,-7,0,-56,-7,0,-7,14,-7,0,-7,14,-7,56,0,0,-7,56,-7,0,14,14,0,0,28,7,28,7,0,7,0,7,0,0,56],#[0,0,0,-7,0,56,-7,0,14,-7,14,0,14,-7,14,56,0,0,-7,-56,-7,0,-7,-7,0,0,7,28,7,7,0,7,0,28,0,0,56],#[0,0,0,14,0,56,14,0,-7,-7,-7,0,-7,-7,-7,-56,0,0,14,56,14,0,-7,-7,0,0,7,7,7,28,0,28,0,7,0,0,56],#[0,0,0,10,0,10,10,0,10,10,10,0,10,10,10,10,0,0,10,10,10,0,10,10,0,0,10,10,10,10,0,10,0,10,0,0,-90]]
def w1 (i : P) (j : N) := (((matrix1[i.val]?).getD #[])[j.val]?).getD 0
def support1 : Array (Array Nat) := #[#[0,3,9,21],#[1,6,18,21],#[4,15,19,21],#[2,12,16,21],#[10,13,20,21],#[7,11,17,21],#[5,8,14,21],#[0,1,2,0],#[3,4,5,3],#[6,7,8,6],#[9,10,11,9],#[12,13,14,12],#[15,16,17,15],#[18,19,20,18]]
def t1 (x : Fin 14) (t : Fin 4) : P := Fin.ofNat 22 ((((support1[x.val]?).getD #[])[t.val]?).getD 0)
def col1 (j : N) := ∑ i,w1 i j
set_option maxHeartbeats 0 in
theorem rightLeaf : ∀ x R C, (∀i∈R,u1 i x=true) → (∀j∈C,neg j x=false) → mass w1 R C ≤168 := by
  have cover : ∀ x i, u1 i x=true → ∃t,t1 x t=i := by decide +kernel
  have limit : ∀ x (marks : Fin 4 → Bool), let A := choose (t1 x) (fun i => u1 i x) marks;
      (∑ j : N, if neg j x then (0:ℤ) else max 0 (∑ i∈A,w1 i j)) ≤168 := by decide +kernel
  exact certifiedLeaf w1 u1 neg 168 t1 cover limit

def mincol (j : N) := if j=0 then col0 j else if j=36 then col1 j else min (col0 j) (col1 j)
set_option maxHeartbeats 0 in
theorem markedAND (f g : Formula (Fin 14))
    (on : ∀ i, f.eval (pos i)=true ∧ g.eval (pos i)=true)
    (off : ∀ j, f.eval (neg j)=false ∨ g.eval (neg j)=false)
    (p : f.eval (neg 0)=false ∧ g.eval (neg 0)=true)
    (q : f.eval (neg 36)=true ∧ g.eval (neg 36)=false) : 32 ≤ f.leaves+g.leaves := by
  let cut (j : N) := f.eval (neg j)=false
  let C := Finset.univ.filter cut
  let D := Finset.univ.filter (fun j=>¬cut j)
  have fc : ∀i∈(Finset.univ : Finset P), f.eval (u0 i)=true := by
    intro i _
    by_cases h : i.val<21
    · have e : u0 i = pos ⟨i.val,h⟩ := by funext x; simp [u0,h]
      rw [e]; exact (on ⟨i.val,h⟩).1
    · have e : u0 i = neg 36 := by funext x; simp [u0,h]
      rw [e]; exact q.1
  have gc : ∀i∈(Finset.univ : Finset P), g.eval (u1 i)=true := by
    intro i _
    by_cases h : i.val<21
    · have e : u1 i = pos ⟨i.val,h⟩ := by funext x; simp [u1,h]
      rw [e]; exact (on ⟨i.val,h⟩).2
    · have e : u1 i = neg 0 := by funext x; simp [u1,h]
      rw [e]; exact p.2
  have l := formulaBound w0 u0 neg 168 leftLeaf f Finset.univ C fc
    (fun j hj => (Finset.mem_filter.mp hj).2)
  have r := formulaBound w1 u1 neg 168 rightLeaf g Finset.univ D gc
    (fun j hj => (off j).resolve_left (Finset.mem_filter.mp hj).2)
  have a : (∑j∈C,mincol j) ≤ mass w0 Finset.univ C := by
    unfold mass
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    have hs : cut j := (Finset.mem_filter.mp hj).2
    have hq : j≠36 := by intro e; subst j; change f.eval (neg 36)=false at hs; simp [q.1] at hs
    by_cases hp : j=0
    · simp [mincol,hp,col0]
    · simpa only [mincol,if_neg hp,if_neg hq,col0] using min_le_left (col0 j) (col1 j)
  have b : (∑j∈D,mincol j) ≤ mass w1 Finset.univ D := by
    unfold mass
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    have hs : ¬cut j := (Finset.mem_filter.mp hj).2
    have hp : j≠0 := by intro e; subst j; exact hs p.1
    by_cases hq : j=36
    · simp [mincol,hq,col1]
    · simpa only [mincol,if_neg hp,if_neg hq,col1] using min_le_right (col0 j) (col1 j)
  have total : (∑j,mincol j)=5322 := by decide +kernel
  have part : (∑j∈C,mincol j)+(∑j∈D,mincol j)=∑j,mincol j := Finset.sum_filter_add_sum_filter_not Finset.univ cut mincol
  have h := add_le_add (a.trans l) (b.trans r)
  rw [part,total] at h
  omega
end Marked4603
