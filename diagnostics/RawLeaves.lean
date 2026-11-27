import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9809.RawLeaf
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
abbrev P := Fin 19
abbrev N := Fin 39
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
def posRows : Array Nat := #[257, 1025, 130, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
def negRows : Array Nat := #[127, 245, 314, 432, 543, 661, 794, 1102, 1220, 1550, 1802, 2087, 2213, 2338, 2567, 2693, 3590, 3716, 4179, 4305, 4627, 4753, 4882, 5008, 5186, 6659, 7938, 8297, 8417, 8488, 8713, 9288, 9992, 10401, 10656, 12481, 13504, 14977, 16256]
def pos (i : P) (x : Fin 14) := (posRows[i.val]?.getD 0).testBit x.val
def neg (j : N) (x : Fin 14) := (negRows[j.val]?.getD 0).testBit x.val

def extra (row : Fin 14 → Bool) (pivot : Fin 14) (t : Fin 15) : Bool :=
  if t.val<14 then row (Fin.ofNat 14 t.val) else !row pivot

def selected {m} (ids : Fin m → N) (marks : Fin m → Bool) : Finset N :=
  (Finset.univ.filter (fun t => marks t=true)).image ids

theorem sparseColumns {m : Nat} (w : P → N → ℤ) (U : P → Bool) (V : N → Bool)
    (d : ℤ) (ids : Fin m → N)
    (zero : ∀ i j, U i=true → V j=false → 0<w i j → ∃t,ids t=j)
    (small : ∀ marks,let A:=selected ids marks;
      (∑ i : P,if U i then max 0 (∑j∈A,w i j) else (0:ℤ))≤d)
    (R : Finset P) (C : Finset N) (u : ∀i∈R,U i=true) (v : ∀j∈C,V j=false) :
    mass w R C≤d := by
  classical
  let marks (t : Fin m) := decide (ids t∈C)
  let A := selected ids marks
  have mem (j : N) : j∈A ↔ ∃t,ids t∈C ∧ ids t=j := by
    simp [A,selected,marks]
  have sub : A⊆C := by
    intro j hj
    obtain ⟨t,ht,rfl⟩ := (mem j).1 hj
    exact ht
  have filt : C.filter (fun j => j∈A)=A := by
    ext j
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have bound (i : P) (hi : i∈R) : (∑j∈C,w i j)≤∑j∈A,w i j := by
    have part := Finset.sum_filter_add_sum_filter_not C (fun j => j∈A) (fun j => w i j)
    rw [filt] at part
    have neg : (∑j∈C.filter (fun j => ¬j∈A),w i j)≤0 := by
      apply Finset.sum_nonpos
      intro j hj
      obtain ⟨hc,miss⟩ := Finset.mem_filter.mp hj
      by_contra! pos
      obtain ⟨t,eq⟩ := zero i j (u i hi) (v j hc) pos
      exact miss ((mem j).2 ⟨t,eq ▸ hc,eq⟩)
    omega
  have cert := small marks
  dsimp only at cert
  apply le_trans _ cert
  unfold mass
  trans ∑i∈R,if U i then max 0 (∑j∈A,w i j) else (0:ℤ)
  · apply Finset.sum_le_sum
    intro i hi
    rw [u i hi]
    exact (bound i hi).trans (le_max_right _ _)
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    split <;> simp
namespace X2
def matrix : Array (Array ℤ) := #[#[0,0,11,0,0,0,0,-3,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,4,-3,2,0],#[0,0,-6,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,3,2,6],#[0,0,0,9,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,6,0,0,0,0,-5,0,0,0,0,0,0,0],#[0,0,4,-5,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,-1,0,0,6,0,0,0,0,5,0,0,0,0,6,0,0],#[0,0,4,0,0,0,0,6,0,0,1,4,0,0,0,0,0,0,-2,0,0,0,0,1,0,0,2,0,0,4,0,0,0,0,0,-4,0,-1,0],#[0,0,0,0,0,0,0,6,0,0,-1,1,0,0,1,0,0,0,4,0,0,0,0,1,0,0,2,0,-1,-6,0,0,0,0,0,4,0,1,0],#[0,0,-4,0,0,1,0,0,0,6,0,0,0,0,0,0,2,0,-2,0,0,0,0,-1,0,0,-2,0,1,6,0,0,0,0,0,4,0,1,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,-6,0,1,0,0,5,6,3,0,0,0,0,0],#[0,0,2,0,0,0,2,0,0,0,0,1,0,2,0,0,0,0,0,-7,0,0,0,0,0,0,5,0,0,0,0,4,4,3,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,1,-1,0,-2,0,0,0,0,0,4,0,0,0,0,0,0,6,0,-1,6,0,0,5,-3,0,0,0,0,0],#[0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,4,0,0,4,-2,-2,0,0,4,4,-2,0,0,0,-2,0],#[0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,4,0,0,4,0,0,0,6,0,0,0,0,-4,-4,2,0,0,0,2,0],#[0,0,4,5,0,0,0,0,0,0,0,0,0,0,0,0,-2,0,2,0,0,0,0,1,0,0,-6,2,2,0,0,0,4,2,0,0,0,2,0],#[0,0,0,0,0,0,0,0,0,0,1,0,0,5,1,0,0,0,0,0,3,0,0,2,0,0,0,0,0,0,0,0,5,6,0,0,-6,0,0],#[0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-6,0,0,-4,0,0,0,2,2,0,0,0,5,2,0,0,6,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,0,0,2,-1,0,0,0,0,0,3,0,0,4,0,0,0,0,1,6,0,0,-5,3,0,0,5,0,0],#[0,0,2,0,0,0,0,3,0,0,0,-4,0,5,0,0,0,0,2,0,0,0,4,0,0,0,1,0,0,0,-4,0,0,0,0,4,3,-2,0],#[0,0,0,0,0,0,2,0,0,0,0,0,0,-5,0,0,0,0,0,0,0,0,4,0,0,0,-1,0,0,0,4,0,0,0,0,0,11,2,0],#[0,0,-2,0,0,0,-2,0,0,0,0,4,0,5,0,0,0,0,0,7,0,0,-4,0,0,0,1,0,0,0,0,4,0,0,0,0,0,2,0]]
def weight (i : P) (j : N) := (((matrix[i.val]?).getD #[])[j.val]?).getD 0
def support : Array (Array Nat) := #[#[0,1,0],#[2,3,0],#[4,5,6],#[7,8,9],#[10,11,12],#[13,14,15],#[16,17,18],#[2,7,0],#[0,4,16],#[13,17,0],#[1,10,14],#[8,11,18],#[5,9,15],#[3,6,12]]
def ids (x : Fin 14) (t : Fin 3) : P := Fin.ofNat 19 ((((support[x.val]?).getD #[])[t.val]?).getD 0)
def cols : Fin 5 → N := ![5,7,11,14,16]
set_option maxHeartbeats 0 in
theorem bound (f : Formula (Fin 15))
    (hon : ∀ i,f.eval (extra (pos i) 2)=true) (hoff : ∀ j,f.eval (extra (neg j) 2)=false) :
    25≤f.leaves := by
  have cover : ∀ x i,pos i x=true → ∃t,ids x t=i := by decide +kernel
  have lim : ∀ x (marks : Fin 3 → Bool),let A:=choose (ids x) (fun i=>pos i x) marks;
    (∑j : N,if neg j x then (0:ℤ) else max 0 (∑i∈A,weight i j))≤12 := by decide +kernel
  have raw := certifiedLeaf weight pos neg 12 ids cover lim
  have zero : ∀ i j, (!pos i 2)=true → (!neg j 2)=false → 0<weight i j → ∃t,cols t=j := by decide +kernel
  have sm : ∀ marks : Fin 5 → Bool, let A:=selected cols marks;
    (∑i : P,if !pos i 2 then max 0 (∑j∈A,weight i j) else (0:ℤ))≤12 := by decide +kernel
  have sign := sparseColumns weight (fun i=> !pos i 2) (fun j=> !neg j 2) 12 cols zero sm
  have q := formulaBound weight (fun i=>extra (pos i) 2) (fun j=>extra (neg j) 2) 12 (by
    intro t R C hp hn
    by_cases lt : t.val<14
    · exact raw (Fin.ofNat 14 t.val) R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn)
    · exact sign R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn))
    f Finset.univ Finset.univ (fun i _=>hon i) (fun j _=>hoff j)
  have total : mass weight Finset.univ Finset.univ=295 := by decide +kernel
  rw [total] at q
  omega
end X2
namespace X3
def matrix : Array (Array ℤ) := #[#[0,0,0,7,1,0,0,0,-7,0,0,0,0,0,0,6,0,0,0,0,0,0,0,8,-1,1,0,0,0,0,0,0,0,3,0,2,0,2,0],#[0,0,0,-7,0,0,0,0,7,0,0,0,5,0,0,0,0,0,0,1,0,1,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,8,0],#[0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,3,4,0,0,3,0,0,0,9,0,0,0,0,0,-3,3,0,0,0,0,0],#[0,-3,0,0,0,0,0,0,0,0,0,0,0,0,0,-5,5,0,0,-4,0,0,7,0,0,0,3,0,0,0,0,0,3,12,0,0,0,0,0],#[0,0,0,0,0,0,2,0,7,0,0,2,0,0,0,6,0,0,-5,0,0,0,8,0,0,-1,0,0,0,0,0,0,0,-3,6,-2,0,-2,0],#[0,0,0,0,0,0,-2,0,0,0,0,0,8,0,0,0,7,0,5,0,0,0,7,0,0,1,0,0,0,0,0,0,0,-1,-6,0,0,2,0],#[0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,2,0,0,0,0,-8,0,0,0,0,0,0,0,0,0,0,5,6,2,0,2,0],#[0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,5,0,0,-3,0,0,0,-9,0,0,0,0,0,15,1,0,0,1,0,0],#[0,0,5,0,3,0,0,0,0,0,0,0,5,0,0,0,0,0,-3,-5,0,0,0,0,0,0,9,0,0,0,0,5,0,1,0,0,-1,0,0],#[0,0,0,0,0,0,2,0,0,0,0,0,-8,0,0,0,0,0,3,5,0,0,3,0,0,0,3,0,0,0,7,0,0,-1,0,0,1,0,0],#[0,0,0,7,0,0,0,0,0,0,0,0,-5,0,0,0,5,2,0,7,0,1,0,0,0,0,3,0,0,0,0,0,0,0,-2,0,5,-3,0],#[0,0,1,1,0,0,0,0,0,0,0,0,5,0,0,0,0,2,3,5,0,1,5,0,0,0,3,0,0,0,0,-5,0,0,2,0,-5,3,0],#[0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-5,-2,0,4,0,0,8,0,0,0,-3,0,0,0,0,5,0,0,2,0,5,3,0],#[0,0,0,4,0,0,0,0,0,0,0,10,0,0,0,0,7,0,0,0,0,1,0,0,-8,0,0,0,0,0,0,0,0,0,1,0,0,6,0],#[0,0,0,7,0,0,0,0,0,0,0,0,6,0,0,0,7,0,0,-7,0,-1,0,0,8,0,0,0,0,0,0,0,0,0,2,0,0,-6,0],#[0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,-7,0,0,7,0,0,0,0,8,0,0,0,0,0,0,0,0,1,6,0,0,0,0],#[0,0,1,5,-1,0,0,0,7,0,0,-2,0,0,0,-6,0,0,5,0,0,0,5,0,1,0,0,0,0,0,0,0,0,0,1,2,0,0,3],#[0,0,0,-4,4,0,0,0,0,0,0,-3,0,0,0,6,0,0,0,0,0,1,5,0,8,0,0,0,0,0,0,0,0,0,-1,8,0,0,-3],#[0,0,-1,-1,-3,0,0,0,0,0,0,5,0,0,0,6,0,0,3,5,0,-1,-5,0,0,0,0,0,0,0,0,3,0,0,1,0,5,0,3]]
def weight (i : P) (j : N) := (((matrix[i.val]?).getD #[])[j.val]?).getD 0
def support : Array (Array Nat) := #[#[0,1,0],#[2,3,0],#[4,5,6],#[7,8,9],#[10,11,12],#[13,14,15],#[16,17,18],#[2,7,0],#[0,4,16],#[13,17,0],#[1,10,14],#[8,11,18],#[5,9,15],#[3,6,12]]
def ids (x : Fin 14) (t : Fin 3) : P := Fin.ofNat 19 ((((support[x.val]?).getD #[])[t.val]?).getD 0)
def cols : Fin 5 → N := ![2,4,6,31,32]
set_option maxHeartbeats 0 in
theorem bound (f : Formula (Fin 15))
    (hon : ∀ i,f.eval (extra (pos i) 3)=true) (hoff : ∀ j,f.eval (extra (neg j) 3)=false) :
    25≤f.leaves := by
  have cover : ∀ x i,pos i x=true → ∃t,ids x t=i := by decide +kernel
  have lim : ∀ x (marks : Fin 3 → Bool),let A:=choose (ids x) (fun i=>pos i x) marks;
    (∑j : N,if neg j x then (0:ℤ) else max 0 (∑i∈A,weight i j))≤16 := by decide +kernel
  have raw := certifiedLeaf weight pos neg 16 ids cover lim
  have zero : ∀ i j, (!pos i 3)=true → (!neg j 3)=false → 0<weight i j → ∃t,cols t=j := by decide +kernel
  have sm : ∀ marks : Fin 5 → Bool, let A:=selected cols marks;
    (∑i : P,if !pos i 3 then max 0 (∑j∈A,weight i j) else (0:ℤ))≤16 := by decide +kernel
  have sign := sparseColumns weight (fun i=> !pos i 3) (fun j=> !neg j 3) 16 cols zero sm
  have q := formulaBound weight (fun i=>extra (pos i) 3) (fun j=>extra (neg j) 3) 16 (by
    intro t R C hp hn
    by_cases lt : t.val<14
    · exact raw (Fin.ofNat 14 t.val) R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn)
    · exact sign R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn))
    f Finset.univ Finset.univ (fun i _=>hon i) (fun j _=>hoff j)
  have total : mass weight Finset.univ Finset.univ=386 := by decide +kernel
  rw [total] at q
  omega
end X3
namespace X5
def matrix : Array (Array ℤ) := #[#[0,0,1,0,0,0,0,0,-5,0,0,0,0,0,2,0,0,0,2,0,0,0,4,0,0,0,5,0,0,0,2,0,0,0,0,0,0,2,0],#[0,0,-1,0,0,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,5,0,-4,0,0,0,0,0,0,0,1,0,0,0,0,0,0,4,0],#[0,0,0,0,0,8,0,0,2,0,0,0,0,0,3,0,2,0,0,0,0,0,3,0,0,2,0,0,0,0,0,-2,0,0,0,0,0,0,0],#[0,0,0,0,0,-8,1,0,0,0,0,0,0,0,1,0,4,0,0,0,0,0,3,0,0,0,1,0,0,0,0,10,0,0,0,0,0,0,0],#[0,0,0,0,0,0,1,0,5,0,0,0,0,0,5,0,0,0,-3,0,0,0,3,0,0,0,1,0,0,1,0,-2,3,0,0,0,0,-2,0],#[0,0,0,0,0,0,0,0,0,5,0,2,0,0,0,3,0,0,3,0,0,0,3,0,0,0,1,0,0,-4,0,0,-3,0,0,0,0,2,0],#[0,0,0,0,0,4,-1,0,0,0,0,0,0,0,2,0,3,0,0,0,0,0,-3,0,0,0,-1,0,0,2,0,2,3,0,0,0,0,2,0],#[0,0,0,0,0,0,8,0,0,0,0,0,2,0,-3,3,0,0,0,5,0,0,-3,0,0,-2,0,0,0,0,0,2,0,0,0,0,0,0,0],#[0,0,0,0,0,0,2,0,0,0,2,2,0,0,3,3,0,0,0,-5,0,0,0,0,0,2,0,0,0,0,0,2,2,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,5,0,-2,-2,0,0,-3,0,0,0,5,0,0,3,0,0,2,0,0,0,2,0,0,3,0,0,0,0,0,0],#[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,5,0,4,0,0,0,0,0,0,-1,-1,4,2,0,0,0,0,-4,0],#[0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,4,0,0,5,0,0,2,0,0,0,0,0,0,0,0,-5,-2,0,0,0,0,4,0],#[0,0,0,0,0,6,1,0,0,0,0,0,0,0,-2,0,-4,0,0,0,0,0,3,0,0,0,0,0,0,1,1,1,2,0,0,0,0,4,0],#[0,0,0,0,0,0,0,0,-5,5,0,0,10,0,0,0,0,0,0,-5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,5,0,0,0,0,0,5,5,0,0,0,0,0,0,0,0,0,0,-5,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,-5,0,2,3,0,0,0,0,0,0,5,5,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,0,2,0,0,0,-5,0,0,0,3,0,0,0,2,0,0,0,5,0,0,0,-2,2,0,0,0,0,0,0,0],#[0,0,0,0,0,0,2,0,5,0,2,0,0,0,2,0,0,0,0,5,0,0,0,0,0,0,-5,0,0,0,2,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,-2,0,0,0,-2,0,0,0,5,0,0,0,0,5,0,0,-2,0,0,0,5,0,0,0,0,5,0,0,0,0,0,0,0]]
def weight (i : P) (j : N) := (((matrix[i.val]?).getD #[])[j.val]?).getD 0
def support : Array (Array Nat) := #[#[0,1,0],#[2,3,0],#[4,5,6],#[7,8,9],#[10,11,12],#[13,14,15],#[16,17,18],#[2,7,0],#[0,4,16],#[13,17,0],#[1,10,14],#[8,11,18],#[5,9,15],#[3,6,12]]
def ids (x : Fin 14) (t : Fin 3) : P := Fin.ofNat 19 ((((support[x.val]?).getD #[])[t.val]?).getD 0)
def cols : Fin 4 → N := ![2,11,12,29]
set_option maxHeartbeats 0 in
theorem bound (f : Formula (Fin 15))
    (hon : ∀ i,f.eval (extra (pos i) 5)=true) (hoff : ∀ j,f.eval (extra (neg j) 5)=false) :
    25≤f.leaves := by
  have cover : ∀ x i,pos i x=true → ∃t,ids x t=i := by decide +kernel
  have lim : ∀ x (marks : Fin 3 → Bool),let A:=choose (ids x) (fun i=>pos i x) marks;
    (∑j : N,if neg j x then (0:ℤ) else max 0 (∑i∈A,weight i j))≤10 := by decide +kernel
  have raw := certifiedLeaf weight pos neg 10 ids cover lim
  have zero : ∀ i j, (!pos i 5)=true → (!neg j 5)=false → 0<weight i j → ∃t,cols t=j := by decide +kernel
  have sm : ∀ marks : Fin 4 → Bool, let A:=selected cols marks;
    (∑i : P,if !pos i 5 then max 0 (∑j∈A,weight i j) else (0:ℤ))≤10 := by decide +kernel
  have sign := sparseColumns weight (fun i=> !pos i 5) (fun j=> !neg j 5) 10 cols zero sm
  have q := formulaBound weight (fun i=>extra (pos i) 5) (fun j=>extra (neg j) 5) 10 (by
    intro t R C hp hn
    by_cases lt : t.val<14
    · exact raw (Fin.ofNat 14 t.val) R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn)
    · exact sign R C (by simpa [extra,lt] using hp) (by simpa [extra,lt] using hn))
    f Finset.univ Finset.univ (fun i _=>hon i) (fun j _=>hoff j)
  have total : mass weight Finset.univ Finset.univ=246 := by decide +kernel
  rw [total] at q
  omega
end X5
end PEqualNP.Outside.L_meta_9809.RawLeaf
