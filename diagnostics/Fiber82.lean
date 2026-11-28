import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.Fixed75
open Finset
abbrev Five := Fin 5
abbrev Count := Fin 7

-- Orient a fixed rectangle so its moving shore consists of whole affine fibers.
-- h = number of such fibers; b = size of the opposite fixed shore.
-- a counts fixed elements on the same shore.  The exceptional axis/center case has a=0.
def allowed (h a b : Count) : Prop :=
  h.val≤5 ∧ a.val≤5 ∧ ((h.val+b.val≤5) ∨ (a.val=0 ∧ h.val+b.val≤6)) 
instance (h a b : Count) : Decidable (allowed h a b) := by unfold allowed; infer_instance

def weight (h a b : Count) := (4*h.val+a.val)*b.val
theorem prices : ∀ (h a b : Count), allowed h a b →
    weight h a b≤36 ∨ (weight h a b=39 ∧ h.val=2 ∧ a.val=5 ∧ b.val=3) := by
  decide +kernel

theorem intersect (A B : Finset Five) : A.card+B.card≤5+(A∩B).card := by
  have h := card_union_add_card_inter A B
  have small : (A∪B).card≤5 := (A∪B).card_le_univ
  omega

theorem overlap (A B C D : Finset Five)
    (one : A.card=5 ∧ B.card=3 ∨ A.card=3 ∧ B.card=5)
    (two : C.card=5 ∧ D.card=3 ∨ C.card=3 ∧ D.card=5) :
    5≤(A∩C).card*(B∩D).card := by
  have x := intersect A C
  have y := intersect B D
  rcases one with h|h <;> rcases two with j|j
  all_goals obtain ⟨a,b⟩ := h
  all_goals obtain ⟨c,d⟩ := j
  all_goals rw [a,c] at x
  all_goals rw [b,d] at y
  all_goals first
    | exact (show 5≤5*1 by decide).trans (Nat.mul_le_mul (by omega : 5≤(A∩C).card) (by omega : 1≤(B∩D).card))
    | exact (show 5≤1*5 by decide).trans (Nat.mul_le_mul (by omega : 1≤(A∩C).card) (by omega : 5≤(B∩D).card))
    | exact (show 5≤3*3 by decide).trans (Nat.mul_le_mul (by omega : 3≤(A∩C).card) (by omega : 3≤(B∩D).card))

theorem unionPrice (h a b h' a' b' : Count) (ok : allowed h a b) (ok' : allowed h' a' b')
    (A B C D : Finset Five)
    (corners : a.val=5 → b.val=3 → A.card=5 ∧ B.card=3 ∨ A.card=3 ∧ B.card=5)
    (corners' : a'.val=5 → b'.val=3 → C.card=5 ∧ D.card=3 ∨ C.card=3 ∧ D.card=5)
    (u : Nat) (both : u+(A∩C).card*(B∩D).card≤weight h a b+weight h' a' b') :
    u≤75 := by
  rcases prices h a b ok with x | ⟨x,hh,aa,bb⟩ <;>
    rcases prices h' a' b' ok' with y | ⟨y,hh',aa',bb'⟩
  · omega
  · omega
  · omega
  · have cnt := overlap A B C D (corners aa bb) (corners' aa' bb')
    omega
end PEqualNP.Outside.L_meta_10007.Fixed75

namespace PEqualNP.Outside.L_meta_10007.Fiber82
abbrev Idx := Fin 252
def shapes : Array (List Nat) := #[[0,0,0,0,0],[0,0,0,0,1],[0,0,0,0,2],[0,0,0,0,3],[0,0,0,0,4],[0,0,0,0,5],[0,0,0,1,1],[0,0,0,1,2],[0,0,0,1,3],[0,0,0,1,4],[0,0,0,1,5],[0,0,0,2,2],[0,0,0,2,3],[0,0,0,2,4],[0,0,0,2,5],[0,0,0,3,3],[0,0,0,3,4],[0,0,0,3,5],[0,0,0,4,4],[0,0,0,4,5],[0,0,0,5,5],[0,0,1,1,1],[0,0,1,1,2],[0,0,1,1,3],[0,0,1,1,4],[0,0,1,1,5],[0,0,1,2,2],[0,0,1,2,3],[0,0,1,2,4],[0,0,1,2,5],[0,0,1,3,3],[0,0,1,3,4],[0,0,1,3,5],[0,0,1,4,4],[0,0,1,4,5],[0,0,1,5,5],[0,0,2,2,2],[0,0,2,2,3],[0,0,2,2,4],[0,0,2,2,5],[0,0,2,3,3],[0,0,2,3,4],[0,0,2,3,5],[0,0,2,4,4],[0,0,2,4,5],[0,0,2,5,5],[0,0,3,3,3],[0,0,3,3,4],[0,0,3,3,5],[0,0,3,4,4],[0,0,3,4,5],[0,0,3,5,5],[0,0,4,4,4],[0,0,4,4,5],[0,0,4,5,5],[0,0,5,5,5],[0,1,1,1,1],[0,1,1,1,2],[0,1,1,1,3],[0,1,1,1,4],[0,1,1,1,5],[0,1,1,2,2],[0,1,1,2,3],[0,1,1,2,4],[0,1,1,2,5],[0,1,1,3,3],[0,1,1,3,4],[0,1,1,3,5],[0,1,1,4,4],[0,1,1,4,5],[0,1,1,5,5],[0,1,2,2,2],[0,1,2,2,3],[0,1,2,2,4],[0,1,2,2,5],[0,1,2,3,3],[0,1,2,3,4],[0,1,2,3,5],[0,1,2,4,4],[0,1,2,4,5],[0,1,2,5,5],[0,1,3,3,3],[0,1,3,3,4],[0,1,3,3,5],[0,1,3,4,4],[0,1,3,4,5],[0,1,3,5,5],[0,1,4,4,4],[0,1,4,4,5],[0,1,4,5,5],[0,1,5,5,5],[0,2,2,2,2],[0,2,2,2,3],[0,2,2,2,4],[0,2,2,2,5],[0,2,2,3,3],[0,2,2,3,4],[0,2,2,3,5],[0,2,2,4,4],[0,2,2,4,5],[0,2,2,5,5],[0,2,3,3,3],[0,2,3,3,4],[0,2,3,3,5],[0,2,3,4,4],[0,2,3,4,5],[0,2,3,5,5],[0,2,4,4,4],[0,2,4,4,5],[0,2,4,5,5],[0,2,5,5,5],[0,3,3,3,3],[0,3,3,3,4],[0,3,3,3,5],[0,3,3,4,4],[0,3,3,4,5],[0,3,3,5,5],[0,3,4,4,4],[0,3,4,4,5],[0,3,4,5,5],[0,3,5,5,5],[0,4,4,4,4],[0,4,4,4,5],[0,4,4,5,5],[0,4,5,5,5],[0,5,5,5,5],[1,1,1,1,1],[1,1,1,1,2],[1,1,1,1,3],[1,1,1,1,4],[1,1,1,1,5],[1,1,1,2,2],[1,1,1,2,3],[1,1,1,2,4],[1,1,1,2,5],[1,1,1,3,3],[1,1,1,3,4],[1,1,1,3,5],[1,1,1,4,4],[1,1,1,4,5],[1,1,1,5,5],[1,1,2,2,2],[1,1,2,2,3],[1,1,2,2,4],[1,1,2,2,5],[1,1,2,3,3],[1,1,2,3,4],[1,1,2,3,5],[1,1,2,4,4],[1,1,2,4,5],[1,1,2,5,5],[1,1,3,3,3],[1,1,3,3,4],[1,1,3,3,5],[1,1,3,4,4],[1,1,3,4,5],[1,1,3,5,5],[1,1,4,4,4],[1,1,4,4,5],[1,1,4,5,5],[1,1,5,5,5],[1,2,2,2,2],[1,2,2,2,3],[1,2,2,2,4],[1,2,2,2,5],[1,2,2,3,3],[1,2,2,3,4],[1,2,2,3,5],[1,2,2,4,4],[1,2,2,4,5],[1,2,2,5,5],[1,2,3,3,3],[1,2,3,3,4],[1,2,3,3,5],[1,2,3,4,4],[1,2,3,4,5],[1,2,3,5,5],[1,2,4,4,4],[1,2,4,4,5],[1,2,4,5,5],[1,2,5,5,5],[1,3,3,3,3],[1,3,3,3,4],[1,3,3,3,5],[1,3,3,4,4],[1,3,3,4,5],[1,3,3,5,5],[1,3,4,4,4],[1,3,4,4,5],[1,3,4,5,5],[1,3,5,5,5],[1,4,4,4,4],[1,4,4,4,5],[1,4,4,5,5],[1,4,5,5,5],[1,5,5,5,5],[2,2,2,2,2],[2,2,2,2,3],[2,2,2,2,4],[2,2,2,2,5],[2,2,2,3,3],[2,2,2,3,4],[2,2,2,3,5],[2,2,2,4,4],[2,2,2,4,5],[2,2,2,5,5],[2,2,3,3,3],[2,2,3,3,4],[2,2,3,3,5],[2,2,3,4,4],[2,2,3,4,5],[2,2,3,5,5],[2,2,4,4,4],[2,2,4,4,5],[2,2,4,5,5],[2,2,5,5,5],[2,3,3,3,3],[2,3,3,3,4],[2,3,3,3,5],[2,3,3,4,4],[2,3,3,4,5],[2,3,3,5,5],[2,3,4,4,4],[2,3,4,4,5],[2,3,4,5,5],[2,3,5,5,5],[2,4,4,4,4],[2,4,4,4,5],[2,4,4,5,5],[2,4,5,5,5],[2,5,5,5,5],[3,3,3,3,3],[3,3,3,3,4],[3,3,3,3,5],[3,3,3,4,4],[3,3,3,4,5],[3,3,3,5,5],[3,3,4,4,4],[3,3,4,4,5],[3,3,4,5,5],[3,3,5,5,5],[3,4,4,4,4],[3,4,4,4,5],[3,4,4,5,5],[3,4,5,5,5],[3,5,5,5,5],[4,4,4,4,4],[4,4,4,4,5],[4,4,4,5,5],[4,4,5,5,5],[4,5,5,5,5],[5,5,5,5,5]]
def shape (a : Idx) := shapes[a.val]!
def top (a : List Nat) := a.foldl max 0
def used (a : List Nat) := (a.filter (fun i => i!=0)).length
def cap (a : Nat) := (#[31,25,20,16,13,11,10,8,7,6,6,5,4,4,3,3,3,2,2,2,2,1,1,1,1,1,0,0,0,0,0,0] : Array Nat)[a]?.getD 0
def moment (a b : Nat) : Bool := decide (a*b≤60) && (List.range 7).all (fun k =>
  decide ((2*k+1)*6*a≤a*(a+5)+(31-b)*k*(k+1)) && decide ((2*k+1)*6*b≤b*(b+5)+(31-a)*k*(k+1)))
set_option maxRecDepth 8192 in
theorem envelope : ∀ a b : Fin 32,moment a.val b.val=true → b.val≤cap a.val := by decide +kernel

def core (a b : List Nat) := (a.map (fun x => (b.map (fun y => min 4 (x*y))).sum)).sum
def inspect (a b : List Nat) : Bool :=
  if 5 < top a+top b then true else
  let u := used a
  let v := used b
  let af := a.sum
  let bf := b.sum
  let kernelMass := core a b
  (List.range (7-v)).all (fun x =>
    (List.range (7-u)).all (fun y =>
      !(decide (bf+y≤cap (af+x)) &&
        (decide (x=0) || decide (y=0) || (decide (x+v≤5) && decide (y+u≤5)))) ||
      decide (kernelMass+4*(x*v+y*u)+x*y≤82)))
def priced (a : Idx) : Prop := ∀ b : Idx,inspect (shape a) (shape b)=true
instance (a : Idx) : Decidable (priced a) := by unfold priced; infer_instance
def atPage (q : Fin 28) (i : Fin 9) : Idx := ⟨q.val*9+i.val,by have := q.isLt; have := i.isLt; omega⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page0 : ∀ j,priced (atPage 0 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page1 : ∀ j,priced (atPage 1 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page2 : ∀ j,priced (atPage 2 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page3 : ∀ j,priced (atPage 3 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page4 : ∀ j,priced (atPage 4 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page5 : ∀ j,priced (atPage 5 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page6 : ∀ j,priced (atPage 6 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page7 : ∀ j,priced (atPage 7 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page8 : ∀ j,priced (atPage 8 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page9 : ∀ j,priced (atPage 9 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page10 : ∀ j,priced (atPage 10 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page11 : ∀ j,priced (atPage 11 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page12 : ∀ j,priced (atPage 12 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page13 : ∀ j,priced (atPage 13 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page14 : ∀ j,priced (atPage 14 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page15 : ∀ j,priced (atPage 15 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page16 : ∀ j,priced (atPage 16 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page17 : ∀ j,priced (atPage 17 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page18 : ∀ j,priced (atPage 18 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page19 : ∀ j,priced (atPage 19 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page20 : ∀ j,priced (atPage 20 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page21 : ∀ j,priced (atPage 21 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page22 : ∀ j,priced (atPage 22 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page23 : ∀ j,priced (atPage 23 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page24 : ∀ j,priced (atPage 24 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page25 : ∀ j,priced (atPage 25 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page26 : ∀ j,priced (atPage 26 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem page27 : ∀ j,priced (atPage 27 j) := by decide +kernel
theorem pages (q : Fin 28) (i : Fin 9) : priced (atPage q i) := by
  fin_cases q
  · exact page0 i
  · exact page1 i
  · exact page2 i
  · exact page3 i
  · exact page4 i
  · exact page5 i
  · exact page6 i
  · exact page7 i
  · exact page8 i
  · exact page9 i
  · exact page10 i
  · exact page11 i
  · exact page12 i
  · exact page13 i
  · exact page14 i
  · exact page15 i
  · exact page16 i
  · exact page17 i
  · exact page18 i
  · exact page19 i
  · exact page20 i
  · exact page21 i
  · exact page22 i
  · exact page23 i
  · exact page24 i
  · exact page25 i
  · exact page26 i
  · exact page27 i

theorem allChecked (a b : Idx) : inspect (shape a) (shape b)=true := by
  let q : Fin 28 := ⟨a.val/9,by have := a.isLt; omega⟩
  let j : Fin 9 := ⟨a.val%9,Nat.mod_lt _ (by decide)⟩
  have eq : atPage q j=a := by apply Fin.ext; change a.val/9*9+a.val%9=a.val; omega
  exact eq ▸ pages q j b

theorem price (a b : Idx) (x y : Nat) (maxs : top (shape a)+top (shape b)≤5)
    (row : x+used (shape b)≤6) (col : y+used (shape a)≤6)
    (fit : (shape b).sum+y≤cap ((shape a).sum+x))
    (corner : x=0 ∨ y=0 ∨ x+used (shape b)≤5 ∧ y+used (shape a)≤5) :
    core (shape a) (shape b)+4*(x*used (shape b)+y*used (shape a))+x*y≤82 := by
  have paid := allChecked a b
  simp only [inspect,show ¬ 5 < top (shape a)+top (shape b) from by omega, if_false] at paid
  have p := List.all_eq_true.mp paid x (List.mem_range.mpr (by omega))
  have w := List.all_eq_true.mp p y (List.mem_range.mpr (by omega))
  simp [fit,corner] at w
  exact w

theorem threeFail (x a b c : Nat) (fixed : x≤75) (ha : a≤82) (hb : b≤82) (hc : c≤82) :
    x+a+b+c<325 := by omega
end PEqualNP.Outside.L_meta_10007.Fiber82
