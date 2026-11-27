import PEqualNP.Defs
namespace Grid1018
abbrev Seq := ℕ → ℤ
def diff (f : Seq) (i : ℕ) := f (i+1)-f i
def order : ℕ → Seq → Prop
  | 0,f => ∀ x, f x=f 0
  | d+1,f => order d (diff f)

theorem add_order (d : ℕ) (f g : Seq) (hf : order d f) (hg : order d g) :
    order d (fun x => f x+g x) := by
  induction d generalizing f g with
  | zero => exact fun x => congrArg₂ (·+·) (hf x) (hg x)
  | succ d ih =>
    change order d (diff (fun x => f x+g x))
    rw [show diff (fun x => f x+g x)=(fun x => diff f x+diff g x) by funext x; simp [diff]; ring]
    exact ih _ _ hf hg

theorem shift_order (d : ℕ) (f : Seq) (hf : order d f) : order d (fun x => f (x+1)) := by
  induction d generalizing f with
  | zero => exact fun x => (hf (x+1)).trans (hf 1).symm
  | succ d ih => exact ih (diff f) hf

theorem mul_linear_order (d : ℕ) (f : Seq) (a : ℤ) (hf : order d f) :
    order (d+1) (fun x => ((x:ℤ)-a)*f x) := by
  have rule (g : Seq) : diff (fun x => ((x:ℤ)-a)*g x)=fun x => g (x+1)+((x:ℤ)-a)*diff g x := by
    funext i
    simp [diff]
    ring
  induction d generalizing f with
  | zero =>
    change ∀ x, diff (fun i => ((i:ℤ)-a)*f i) x=diff (fun i => ((i:ℤ)-a)*f i) 0
    rw [rule]
    intro x
    simp only [diff]
    rw [hf (x+1),hf x,hf (0+1)]
    ring
  | succ d ih =>
    change order (d+1) (diff (fun x => ((x:ℤ)-a)*f x))
    rw [rule]
    exact add_order (d+1) _ _ (shift_order (d+1) f hf) (ih _ hf)

theorem characteristic_order {n : ℕ} (V : Finset (Fin n)) :
    order (2*V.card) (fun x : ℕ => ∏ i∈V, ((x:ℤ)-i.val)^2) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [order]
  | @insert i V hi ih =>
    rw [Finset.card_insert_of_notMem hi,Nat.mul_succ]
    simp only [Finset.prod_insert hi]
    have one := mul_linear_order (2*V.card) _ (i.val:ℤ) ih
    have two := mul_linear_order (2*V.card+1) _ (i.val:ℤ) one
    convert two using 1 <;> first | rfl | (funext x; ring)

def recover : ℕ → Seq → Seq
  | 0,f,_ => f 0
  | d+1,f,x => f 0 + ∑ i∈Finset.range x, recover d (diff f) i

theorem telescopes (f : Seq) (n : ℕ) : f 0 + ∑ i∈Finset.range n, diff f i = f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←add_assoc,ih]
    simp [diff]

theorem reconstruction (d : ℕ) (f : Seq) (h : order d f) (x : ℕ) : recover d f x=f x := by
  induction d generalizing f x with
  | zero => exact (h x).symm
  | succ d ih =>
    simp only [recover]
    have eq : ∀ i, recover d (diff f) i=diff f i := fun i => ih _ h i
    simp only [eq,telescopes]

theorem on_grid (d : ℕ) (f g : Seq) (agree : ∀ i≤d, f i=g i) (x : ℕ) :
    recover d f x=recover d g x := by
  induction d generalizing f g x with
  | zero => exact agree 0 le_rfl
  | succ d ih =>
    simp only [recover,agree 0 (Nat.zero_le _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply ih
    intro j hj
    simp only [diff,agree (j+1) (by omega),agree j (by omega)]

theorem linear {α : Type*} (S : Finset α) (a : α → ℤ) (F : α → Seq) (d x : ℕ) :
    recover d (fun i => ∑ j∈S,a j*F j i) x = ∑ j∈S,a j*recover d (F j) x := by
  induction d generalizing F x with
  | zero => rfl
  | succ d ih =>
    have delta : diff (fun i => ∑ j∈S,a j*F j i)=(fun i => ∑ j∈S,a j*diff (F j) i) := by
      funext i
      simp [diff,Finset.sum_sub_distrib,mul_sub]
    simp only [recover,delta]
    simp_rw [ih]
    rw [Finset.sum_comm (s:=Finset.range x) (t:=S)]
    simp [Finset.mul_sum,mul_add,Finset.sum_add_distrib]

def coeff (d x j : ℕ) : ℤ := recover d (fun i => if i=j then 1 else 0) x

theorem interpolation (d : ℕ) (f : Seq) (h : order d f) (x : ℕ) :
    f x = ∑ j∈Finset.range (d+1), f j*coeff d x j := by
  classical
  simp only [coeff]
  rw [←reconstruction d f h x,←linear (Finset.range (d+1)) f (fun j i => if i=j then 1 else 0) d x]
  apply on_grid
  intro i hi
  have hmem : i∈Finset.range (d+1) := Finset.mem_range.mpr (by omega)
  simp [mul_ite,hmem]

end Grid1018

namespace Grid1018
theorem recover_step (d : ℕ) (f : Seq) (x : ℕ) :
    recover (d+1) f (x+1)=recover (d+1) f x+recover d (diff f) x := by
  simp only [recover,Finset.sum_range_succ,add_assoc]

theorem recover_bdd (x d : ℕ) (f : Seq) (B : ℕ) (h : ∀ i,(f i).natAbs≤B) :
    (recover d f x).natAbs ≤ 3^x * B := by
  induction x generalizing d f B with
  | zero => cases d <;> simpa [recover] using h 0
  | succ x ih =>
    cases d with
    | zero =>
      change (f 0).natAbs≤_
      exact (h 0).trans (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<3) _))
    | succ d =>
      have hd : ∀ i,(diff f i).natAbs≤2*B := by
        intro i
        rw [diff,sub_eq_add_neg]
        have m := Int.natAbs_add_le (f (i+1)) (-f i)
        simp only [Int.natAbs_neg] at m
        have := h (i+1)
        have := h i
        omega
      rw [recover_step]
      calc
        _ ≤ _ := Int.natAbs_add_le _ _
        _ ≤ 3^x*B + 3^x*(2*B) := Nat.add_le_add (ih _ f B h) (ih _ (diff f) _ hd)
        _ = _ := by rw [pow_succ]; ring

theorem coeff_bdd (d x j : ℕ) : (coeff d x j).natAbs≤3^x := by
  simpa [coeff] using recover_bdd x d (fun i => if i=j then 1 else 0) 1 (fun i => by split <;> decide)

theorem zero_recover (d x : ℕ) : recover d (fun _ => 0) x=0 := by
  have := recover_bdd x d (fun _ => 0) 0 (fun i => by decide)
  simpa using this

theorem sub_recover (d x : ℕ) (f g : Seq) :
    recover d (fun i=>f i-g i) x = recover d f x-recover d g x := by
  induction d generalizing f g x with
  | zero => rfl
  | succ d ih =>
    have point : diff (fun i => f i-g i)=fun i => diff f i-diff g i := by
      funext i
      simp only [diff]
      ring
    simp only [recover,point,ih,Finset.sum_sub_distrib]
    ring

theorem coeff_step (d x j : ℕ) :
    coeff (d+1) (x+1) j =
      coeff (d+1) x j + (if j=0 then 0 else coeff d x (j-1)) - coeff d x j := by
  unfold coeff
  rw [recover_step]
  by_cases z : j=0
  · subst j
    have e : diff (fun i : ℕ => if i=0 then (1:ℤ) else 0) = fun i => 0 - (if i=0 then 1 else 0) := by
      funext i
      simp [diff]
    rw [e,sub_recover,zero_recover]
    simp
  · have e : diff (fun i : ℕ => if i=j then (1:ℤ) else 0)=
        fun i => (if i=j-1 then 1 else 0) - (if i=j then 1 else 0) := by
      funext i
      simp only [diff,show (i+1=j ↔ i=j-1) by omega]
    rw [e,sub_recover,if_neg z]
    ring

end Grid1018
