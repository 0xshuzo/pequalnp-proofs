import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_363

abbrev Role := Fin 4 × Bool
abbrev Inc := Bool × Fin 9 × Bool

def ends (j : Fin 9) (b : Bool) : Role :=
  let table : Fin 9 → Fin 2 → Role :=
  ![![((0,true) : Role),(1,true)],![(1,true),(2,true)],![(2,true),(0,true)],
    ![(0,false),(2,false)],![(2,false),(3,false)],![(3,false),(0,false)],
    ![(1,false),(2,false)],![(2,false),(3,false)],![(3,false),(1,false)]]
  table j (if b then 1 else 0)

def localPin (r : Inc) : Role :=
  let p := ends r.2.1 r.2.2
  (p.1, if r.1 then !p.2 else p.2)

def turn (r : Inc) : Inc := (r.1, r.2.1, if r.1 then r.2.2 else !r.2.2)

theorem turn_inv : Function.Involutive turn := by
  rintro ⟨b,j,t⟩
  cases b <;> simp [turn]

def loc (h : Role → Bool) : ℕ :=
  (Finset.univ.filter fun r : Inc => h (localPin r) ≠ h (localPin (turn r))).card

def evalRole (A B Z : Bool) (p : Role) : Bool :=
  let t := ![A,B,Z,false] p.1
  if p.2 then !t else t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_le : ∀ h : Role → Bool, loc h ≤ 12 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_top : ∀ A B Z : Bool, loc (evalRole A B Z) = 12 ↔ Z = !(A && B) := by decide +kernel

def pairCost (h : Bool → Bool) : ℕ :=
  (Finset.univ.filter fun t : Bool => h t ≠ h (!t)).card

theorem pair_le : ∀ h, pairCost h ≤ 2 := by decide +kernel

theorem pair_top : ∀ h, pairCost h = 2 ↔ h true = !(h false) := by decide +kernel

theorem cyc (m : ℕ) (g : Fin m → Bool) (h : ∀ i, g (finRotate m i) = g i) (i j : Fin m) :
    g i = g j := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    have : ∀ i : Fin (m+1), g i = g 0 := fun i => by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [← ih, ← h i.castSucc, finRotate_apply, Fin.coeSucc_eq_succ]
    rw [this i, this j]

theorem rot {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) :
    ∃ σ : Equiv.Perm α, (∀ a, f (σ a) = f a) ∧
      ∀ g : α → Bool, (∀ a, g (σ a) = g a) → ∀ a b, f a = f b → g a = g b := by
  classical
  let F := Equiv.sigmaFiberEquiv f
  let φ : ∀ b, {a // f a = b} ≃ Fin (Fintype.card {a // f a = b}) := fun b => Fintype.equivFin _
  let τ : ∀ b, Equiv.Perm {a // f a = b} := fun b => (φ b).trans ((finRotate _).trans (φ b).symm)
  let σ : Equiv.Perm α := F.symm.trans ((Equiv.sigmaCongrRight τ).trans F)
  have hσ : ∀ b (a : {a // f a = b}), σ a.1 = (τ b a).1 := by
    rintro b ⟨a, rfl⟩
    rfl
  refine ⟨σ, fun a => ?_, fun g hg a b hab => ?_⟩
  · rw [hσ (f a) ⟨a, rfl⟩]
    exact (τ (f a) ⟨a, rfl⟩).2
  · have := cyc _ (fun i => g ((φ (f b)).symm i).1) (fun i => by
      have := hg ((φ (f b)).symm i).1
      rw [hσ (f b)] at this
      simpa [τ] using this) (φ (f b) ⟨a, hab⟩) (φ (f b) ⟨b, rfl⟩)
    simpa using this


abbrev Key (v : ℕ) := Option (Fin v)
abbrev Wire (v : ℕ) := Key v × Bool
abbrev Slot (v g : ℕ) := Wire v ⊕ (Fin g × Inc)

variable {v g : ℕ}

def nameAt (a b z : Fin g → Fin v) (j : Fin g) : Fin 4 → Key v :=
  ![some (a j), some (b j), some (z j), none]

def keyAt (a b z : Fin g → Fin v) : Slot v g → Wire v
  | .inl w => w
  | .inr (j,r) => (nameAt a b z j (localPin r).1, (localPin r).2)

def matchEnd : Slot v g → Slot v g
  | .inl (q,b) => .inl (q,!b)
  | .inr (j,r) => .inr (j,turn r)

theorem match_inv : Function.Involutive (@matchEnd v g) := by
  rintro (⟨q,b⟩ | ⟨j,r⟩)
  · simp [matchEnd]
  · simp [matchEnd,turn_inv r]

def changeSign : Slot v g → Slot v g
  | .inl (q,b) => .inl (q,!b)
  | .inr (j,(d,k,b)) => .inr (j,(!d,k,b))

theorem sign_inv : Function.Involutive (@changeSign v g) := by
  rintro (⟨q,b⟩ | ⟨j,d,k,b⟩) <;> simp [changeSign]

theorem sign_key (a b z : Fin g → Fin v) (s : Slot v g) :
    keyAt a b z (changeSign s) = ((keyAt a b z s).1, !(keyAt a b z s).2) := by
  rcases s with ⟨q,c⟩ | ⟨j,d,k,c⟩
  · rfl
  · cases d <;> simp [keyAt, changeSign, localPin]

def gateView (a b z : Fin g → Fin v) (h : Wire v → Bool) (j : Fin g) (p : Role) :=
  h (nameAt a b z j p.1, p.2)

def score (a b z : Fin g → Fin v) (h : Wire v → Bool) :=
  (∑ q : Key v, pairCost (fun t => h (q,t))) +
    ∑ j : Fin g, loc (gateView a b z h j)

theorem cost_form (a b z : Fin g → Fin v) (h : Wire v → Bool) :
    (Finset.univ.filter (fun s : Slot v g =>
      h (keyAt a b z s) ≠ h (keyAt a b z (matchEnd s)))).card = score a b z h := by
  classical
  simp only [score, pairCost, loc, Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  rfl

theorem cost_bound (a b z : Fin g → Fin v) (h : Wire v → Bool) :
    score a b z h ≤ 2*(v+1+6*g) ∧
    (score a b z h = 2*(v+1+6*g) ↔
      (∀ q, h (q,true) = !(h (q,false))) ∧
      (∀ j, loc (gateView a b z h j) = 12)) := by
  classical
  let p := fun q : Key v => pairCost (fun t => h (q,t))
  let s := fun j : Fin g => loc (gateView a b z h j)
  have hp : ∀ q, p q ≤ 2 := fun q => pair_le _
  have hs : ∀ j, s j ≤ 12 := fun j => loc_le _
  have cp : (∑ _ : Key v, (2:ℕ)) = 2*(v+1) := by simp [Key, Nat.mul_comm, Nat.add_comm]
  have cs : (∑ _ : Fin g, (12:ℕ)) = 12*g := by simp [Nat.mul_comm]
  have ep := Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun q _ => hp q)
  have es := Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun j _ => hs j)
  have lp := Finset.sum_le_sum (s:=Finset.univ) (fun q _ => hp q)
  have ls := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hs j)
  rw [cp] at lp ep
  rw [cs] at ls es
  change (∑ q, p q) + (∑ j, s j) ≤ _ ∧ ((∑ q, p q) + (∑ j, s j) = _ ↔ _)
  refine ⟨by omega, ?_⟩
  constructor
  · intro hh
    exact ⟨fun q => (pair_top _).1 ((ep.1 (by omega)) q (Finset.mem_univ _)),
      fun j => (es.1 (by omega)) j (Finset.mem_univ _)⟩
  · rintro ⟨h1,h2⟩
    have h3 := ep.2 (fun q _ => (pair_top _).2 (h1 q))
    have h4 := es.2 (fun j _ => h2 j)
    omega

def baseVal (x : Fin v → Bool) : Key v → Bool
  | none => false
  | some i => x i

def enc (x : Fin v → Bool) (w : Wire v) : Bool :=
  if w.2 then !(baseVal x w.1) else baseVal x w.1

theorem enc_gate (a b z : Fin g → Fin v) (x : Fin v → Bool) (j : Fin g) :
    gateView a b z (enc x) j = evalRole (x (a j)) (x (b j)) (x (z j)) := by
  funext p
  rcases p with ⟨k,t⟩
  fin_cases k <;> cases t <;> rfl

theorem enc_top (a b z : Fin g → Fin v) (x : Fin v → Bool) :
    score a b z (enc x) = 2*(v+1+6*g) ↔
      ∀ j, x (z j) = !(x (a j) && x (b j)) := by
  rw [(cost_bound a b z (enc x)).2]
  simp only [enc_gate,loc_top]
  exact and_iff_right (fun q => rfl)

theorem negate_half {A : Type} [Fintype A] (f : A → Bool) (e : Equiv.Perm A)
    (h : ∀ x, f (e x) = !(f x)) :
    2 * (Finset.univ.filter (fun x => f x = true)).card = Fintype.card A := by
  classical
  have eq : (Finset.univ.filter (fun x => f x = true)).card =
      (Finset.univ.filter (fun x => f x = false)).card := by
    apply Finset.card_equiv e
    intro x
    cases hh : f x <;> simp [h,hh]
  have add : (Finset.univ.filter (fun x => f x = true)).card +
      (Finset.univ.filter (fun x => f x = false)).card = Fintype.card A := by
    rw [Finset.card_filter,Finset.card_filter,← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : A, (1:ℕ) := Finset.sum_congr rfl (fun x _ => by cases hh : f x <;> simp [hh])
      _ = _ := by simp
  omega

end PEqualNP.Outside.L_pcx_363
