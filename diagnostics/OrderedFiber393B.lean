import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

def tag (o : Option Bool) : Nat := if o.isSome then 1+(o.getD false).toNat else 0
def number {n : Nat} (x : Fin n→Nat) : Nat := ∑ i, x i * 3^i.val
def key {n : Nat} (p : Bool × Fin n → Option Bool) : Nat :=
  ∑ v, tag (p v) * 3^(v.2.val + (if v.1 then n else 0))

lemma tag_inj : Function.Injective tag := by
  intro a b
  cases a with
  | none => cases b with
            | none => simp
            | some b => cases b <;> decide
  | some a =>
    cases b with
    | none => cases a <;> decide
    | some b => cases a <;> cases b <;> decide

lemma tag_bound (a : Option Bool) : tag a < 3 := by cases a with
  | none => decide
  | some v => cases v <;> decide

lemma number_succ {n : Nat} (x : Fin (n+1)→Nat) :
    number x = x 0 + 3*number (fun i : Fin n => x i.succ) := by
  unfold number
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma number_bound {n : Nat} (x : Fin n→Nat) (h : ∀ i,x i<3) : number x<3^n := by
  induction n with
  | zero => simp [number]
  | succ n ih =>
    have z := h 0
    have t := ih (fun i => x i.succ) (fun i => h i.succ)
    rw [number_succ,pow_succ]
    omega

lemma number_inj {n : Nat} {x y : Fin n→Nat} (hx : ∀ i,x i<3) (hy : ∀ i,y i<3)
    (eq : number x=number y) : x=y := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    rw [number_succ,number_succ] at eq
    have zx := hx 0
    have zy := hy 0
    have heads : x 0=y 0 := by omega
    have tails := ih (x:=fun i => x i.succ) (y:=fun i => y i.succ)
      (fun i => hx i.succ) (fun i => hy i.succ) (by omega)
    funext i
    exact Fin.cases heads (fun j => congrFun tails j) i

lemma key_split {n : Nat} (p : Bool × Fin n → Option Bool) :
    key p = number (fun i => tag (p (false,i))) + number (fun i => tag (p (true,i)))*3^n := by
  unfold key number
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  simp [pow_add,Finset.sum_mul,Nat.mul_assoc,Nat.add_comm]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma key_injective {n : Nat} : Function.Injective (@key n) := by
  intro x y eq
  rw [key_split,key_split] at eq
  let low := fun (p : Bool × Fin n→Option Bool) => number (fun i => tag (p (false,i)))
  let high := fun (p : Bool × Fin n→Option Bool) => number (fun i => tag (p (true,i)))
  have lowlim (p) : low p<3^n := number_bound _ (fun _ => tag_bound _)
  change low x+high x*3^n=low y+high y*3^n at eq
  have leq : low x=low y := by
    have h := congrArg (fun z => z % 3^n) eq
    simpa [Nat.add_mod,Nat.mod_eq_of_lt (lowlim x),Nat.mod_eq_of_lt (lowlim y)] using h
  have heq : high x=high y := by
    rw [leq] at eq
    have u := Nat.add_left_cancel eq
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0<3^n) u
  have xl := number_inj (x:=fun i => tag (x (false,i))) (y:=fun i => tag (y (false,i)))
    (fun _ => tag_bound _) (fun _ => tag_bound _) leq
  have xh := number_inj (x:=fun i => tag (x (true,i))) (y:=fun i => tag (y (true,i)))
    (fun _ => tag_bound _) (fun _ => tag_bound _) heq
  funext v
  obtain ⟨b,i⟩ := v
  cases b
  · exact tag_inj (congrFun xl i)
  · exact tag_inj (congrFun xh i)

theorem ordered_fiber {n : Nat} (S : Finset (Bool × Fin n→Option Bool)) :
    ∃ e : Fin S.card ≃ {p // p ∈ S}, ∀ i j, i<j → key (e i).val < key (e j).val := by
  classical
  letI : LinearOrder (Bool × Fin n→Option Bool) := LinearOrder.lift' key key_injective
  let o := S.orderIsoOfFin rfl
  exact ⟨o.toEquiv,fun i j h => o.strictMono h⟩

theorem count_fits {n : Nat} (hn : 0<n) (S : Finset (Bool × Fin n→Option Bool)) :
    S.card < 2^(4*n) := by
  have c := Finset.card_le_univ S
  have cap : Fintype.card (Bool × Fin n→Option Bool) = 9^n := by
    simp [Fintype.card_fun,Fintype.card_prod,Fintype.card_option,Fintype.card_bool,
      show (9:Nat)=3^2 by decide,pow_mul]
  rw [cap] at c
  calc
    S.card ≤ 9^n := c
    _ < 16^n := Nat.pow_lt_pow_left (by decide) hn.ne'
    _ = 2^(4*n) := by rw [pow_mul]; norm_num

end PEqualNP.Outside.L_pcx_393_aux
