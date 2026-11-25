import Mathlib
import PEqualNP.Outside.L_meta_3008
import PEqualNP.Outside.L_meta_4385
import PEqualNP.Outside.L_meta_1983
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4385
namespace Structural4603
abbrev Entry := Bool × Fin 40 × Fin 40
def base : List (BitVec 59) := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
def codes : List Nat := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
def target : BitVec 59 := 2097151
abbrev Rel := PEqualNP.Outside.L_meta_3008_aux.edges
abbrev Old := PEqualNP.Outside.L_meta_3008_aux.nums
def price (w : List (BitVec 59)) (e : Entry) :=
  w ++ [if e.1 then w.getD e.2.1.val 0 ||| w.getD e.2.2.val 0 else w.getD e.2.1.val 0 &&& w.getD e.2.2.val 0]

def gate (n : Nat) (e : Entry) : Gate :=
  let a := e.2.1.val; let b := e.2.2.val
  if e.1 then
    if a<n then (if b<n then ⟨.or,[a,b]⟩ else ⟨.or,[a]⟩)
    else if b<n then ⟨.or,[b]⟩ else ⟨.or,[]⟩
  else if a<n ∧ b<n then ⟨.and,[a,b]⟩ else ⟨.or,[]⟩
lemma gate_ok (e : Entry) (n : Nat) :
    ((gate n e).op = .and ∨ (gate n e).op = .or) ∧ (gate n e).inputs.length ≤ 2 ∧
    ∀ i∈(gate n e).inputs, i<n := by
  rcases e with ⟨k,a,b⟩
  cases k <;> by_cases ha : a.val<n <;> by_cases hb : b.val<n <;> simp [gate,ha,hb]
lemma step (e : Entry) (w : List (BitVec 59)) :
    wordStep w (gate w.length e)=price w e := by
  rcases e with ⟨k,a,b⟩
  by_cases ha : a.val<w.length <;> by_cases hb : b.val<w.length
  all_goals
    first | have na : w.getD a.val 0 = 0 := List.getD_eq_default _ _ (Nat.le_of_not_gt ha) | skip
    first | have nb : w.getD b.val 0 = 0 := List.getD_eq_default _ _ (Nat.le_of_not_gt hb) | skip
    cases k <;> simp only [price,gate,wordStep,gateWord,ha,hb,if_true,if_false,
      and_self,false_and,true_and,and_true,and_false, Bool.false_eq_true, List.map_cons,List.map_nil,
      List.getD_cons_zero,List.getD_cons_succ,List.getD_nil] <;> simp_all [gateWord]
def compile (n : Nat) : List Entry → List Gate
  | [] => []
  | g::gs => gate n g :: compile (n+1) gs
lemma count (n : Nat) (gs : List Entry) : (compile n gs).length=gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [compile,ih]
lemma legal (n : Nat) (l : List Entry) (g : Gate) (hg : g∈compile n l) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length≤2 := by
  induction l generalizing n with
  | nil => cases hg
  | cons e l ih =>
    rcases List.mem_cons.mp hg with rfl|next
    · exact ⟨(gate_ok e n).1,(gate_ok e n).2.1⟩
    · exact ih _ next
lemma back (n : Nat) (l : List Entry) (j : Nat) (g : Gate) (h : (compile n l)[j]?=some g) :
    ∀ i∈g.inputs, i<n+j := by
  induction l generalizing n j with
  | nil => simp [compile] at h
  | cons a l ih =>
    cases j with
    | zero =>
      have eq : gate n a=g := Option.some.inj h
      exact eq ▸ (gate_ok a n).2.2
    | succ j =>
      intro i hi
      have q := ih (n+1) j h i hi
      omega
lemma same (w : List (BitVec 59)) (l : List Entry) :
    (compile w.length l).foldl wordStep w = l.foldl price w := by
  induction l generalizing w with
  | nil => rfl
  | cons e es ih =>
    rw [compile,List.foldl_cons,step,List.foldl_cons]
    have len : (price w e).length=w.length+1 := by simp [price]
    rw [←len]
    exact ih _
def routing : List Nat := [0, 3, 9, 1, 6, 18, 4, 15, 19, 2, 12, 16, 10, 13, 20, 7, 11, 17, 5, 8, 14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
set_option maxHeartbeats 1000000 in
lemma rows (n : Nat) : ∃ z : Fin 59, Old.map (·.testBit n)=base.map (bit z) ∧
    (2097151 : Nat).testBit n=bit z target := by
  by_cases small : n<59
  · have chk : ∀ i : Fin 59,
        let z : Fin 59 := Fin.ofNat 59 (routing.getD i.val 58);
        Old.map (·.testBit i.val)=base.map (bit z) ∧
        (2097151 : Nat).testBit i.val=bit z target := by decide +kernel
    exact ⟨_,chk ⟨n,small⟩⟩
  · have hi : 2^58 ≤ (2^n : Nat) := Nat.pow_le_pow_right (by decide) (by omega)
    have sm : ∀ w∈Old, w < 2^58 := by decide
    have eq : Old.map (·.testBit n)=Old.map (fun _ => false) := by
      apply List.map_congr_left
      intro w hw; exact Nat.testBit_lt_two_pow ((sm w hw).trans_le hi)
    refine ⟨58,?_,?_⟩
    · rw [eq]; decide +kernel
    · rw [Nat.testBit_lt_two_pow ((show (2097151 : Nat)<2^58 by decide).trans_le hi)]
      rfl
lemma lift (gs : List Entry) (h : (gs.foldl price base).getD (13+gs.length) 0 = target) :
    let C : Circuit := ⟨compile 14 gs,13+gs.length⟩
    Monotone2 C ∧ NestedCover.ReadsBack 14 C ∧ (∀ x : Fin 14 → Bool,
    C.eval (List.ofFn x)=true ↔ ∃ u v : Fin 14, (u.val,v.val)∈Rel ∧ x u=true ∧ x v=true) := by
  intro C
  have mono : Monotone2 C := by
    intro g hg
    have q := legal 14 gs g hg
    exact ⟨q.1,q.2⟩
  refine ⟨mono,?_,?_⟩
  · intro j hj i hi
    let g := C.gates[j]
    have hg : NestedCover.gateAt C j=g := by
      exact List.getD_eq_getElem _ _ hj
    apply back 14 gs j g (List.getElem?_eq_getElem hj)
    exact hg ▸ hi
  · apply PEqualNP.Outside.L_meta_3008 C mono
    intro n
    obtain ⟨z,eq,tar⟩ := rows n
    change C.eval (Old.map (·.testBit n))=_
    rw [eq,tar]
    change (C.gates.foldl boolStep (base.map (bit z))).getD C.output false=_
    rw [← run_bits C.gates base z (fun g hg => legal 14 gs _ hg),read_bit]
    change bit z (((compile base.length gs).foldl wordStep base).getD (13+gs.length) 0)=_
    rw [same,h]
set_option maxHeartbeats 1200000 in
theorem nested_of_witness (witness : have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (39 : ℕ)) (x5 : Fin (39 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (25 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9) :
    ∃ C : Circuit, C.size=26 ∧ Monotone2 C ∧ NestedCover.ReadsBack 14 C ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
      ∃ u v : Fin 14, (u.val,v.val)∈Rel ∧ x u=true ∧ x v=true) ∧
    ∃ i j, (NestedCover.gateAt C i).op=.and ∧ (NestedCover.gateAt C j).op=.and ∧
      PEqualNP.EdgeOwnership.InCone 14 C i j := by
  obtain ⟨gs,a,b,k,len,lo,lt,res,ne,c1,c2⟩ := witness
  let isOr := decide ((codes.getD k.val 0)%64<21)
  let e : Entry := ⟨isOr,Fin.castLE (by decide) a,Fin.castLE (by decide) b⟩
  let all := gs ++ [e]
  let C : Circuit := ⟨compile 14 all,13+all.length⟩
  have al : all.length=26 := by simp [all,len]
  have wl : ∀ (l : List Entry) (w : List (BitVec 59)), (l.foldl price w).length = w.length+l.length := by
    intro l
    induction l with
    | nil => simp
    | cons h t ih => intro w; rw [List.foldl_cons,ih];simp [price] <;> omega
  have last : (all.foldl price base).getD (13+all.length) 0 = target := by
    let v := gs.foldl price base
    have vl : v.length=39 := by rw [wl]; change 14+gs.length=39;omega
    have out : 13+all.length=v.length := by omega
    rw [out]
    change ((gs ++ [e]).foldl price base).getD v.length 0 = _
    rw [List.foldl_append]
    change (v ++ [_]).getD v.length 0=_
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    have hr : (if (codes.getD k.val 0)%64<21 then v.getD a.val 0 ||| v.getD b.val 0 else v.getD a.val 0 &&& v.getD b.val 0)=target := res
    change (if isOr then v.getD a.val 0 ||| v.getD b.val 0 else v.getD a.val 0 &&& v.getD b.val 0)=target
    simpa only [isOr,decide_eq_true_eq] using hr
  obtain ⟨mono,backC,correct⟩ := lift all last
  have size : C.size=26 := (count 14 all).trans al
  refine ⟨C,size,mono,backC,correct,?_⟩
  by_contra flat
  have h := PEqualNP.Outside.L_meta_1983 C mono backC flat correct
  omega
end Structural4603
