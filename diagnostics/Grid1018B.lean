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
