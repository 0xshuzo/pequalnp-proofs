import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

abbrev Sites (n : Nat) := Bool × Fin n
abbrev Pin (n : Nat) := Sites n → Option Bool
def honors {n : Nat} (p : Pin n) (x : Sites n→Bool) : Prop :=
  ∀ v, p v=none ∨ p v=some (x v)
def red {n : Nat} (x : Sites n→Bool) (i : Fin n) := Bool.xor (x (false,i)) (x (true,i))
def blue {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Sites n→Bool) (i : Fin n) :=
  Bool.xor (x (false,i)) (x (true,σ i))
abbrev Exact {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin n→Bool) :=
  {x : Sites n→Bool // honors p x ∧ red x=r ∧ blue σ x=b}

abbrev Orb {n : Nat} (σ : Equiv.Perm (Fin n)) := Quot (fun i j : Fin n => σ i=j)
def label {n : Nat} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Orb σ := Quot.mk _ i
def loose {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (o : Orb σ) : Prop :=
  ∀ i, label σ i=o → ∀ a : Bool, p (a,i)=none

noncomputable instance orbFinite {n : Nat} (σ : Equiv.Perm (Fin n)) : Fintype (Orb σ) :=
  Fintype.ofSurjective (label σ) (fun o => Quot.inductionOn o (fun i => ⟨i,rfl⟩))

lemma label_step {n : Nat} (σ : Equiv.Perm (Fin n)) (i : Fin n) : label σ i=label σ (σ i) :=
  Quot.sound rfl

noncomputable def shift {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n}
    (d : {o : Orb σ // loose σ p o}→Bool) (i : Fin n) : Bool := by
  classical
  exact if h : loose σ p (label σ i) then d ⟨label σ i,h⟩ else false

lemma shift_step {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n}
    (d : {o : Orb σ // loose σ p o}→Bool) (i : Fin n) : shift d i=shift d (σ i) := by
  unfold shift
  rw [label_step σ i]

lemma hxorb : ∀ a b c : Bool, Bool.xor (Bool.xor a c) (Bool.xor b c) = Bool.xor a b := by decide
lemma xor_deltas : ∀ a b c d : Bool, Bool.xor a b = Bool.xor c d →
    Bool.xor a c = Bool.xor b d := by decide
lemma xor_inverse : ∀ a b : Bool, Bool.xor a (Bool.xor a b) = b := by decide

noncomputable def flipAlong {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x : Exact σ p r b) (d : {o : Orb σ // loose σ p o}→Bool) : Exact σ p r b := by
  classical
  let y := fun v : Sites n => Bool.xor (x.val v) (shift d v.2)
  refine ⟨y,?_,?_,?_⟩
  · rintro ⟨a,i⟩
    obtain free|on := x.property.1 (a,i)
    · exact Or.inl free
    · right
      have notLoose : ¬loose σ p (label σ i) := by
        intro h
        have off := h i rfl a
        rw [on] at off
        contradiction
      simpa [y,shift,notLoose] using on
  · funext i
    exact (hxorb _ _ _).trans (congrFun x.property.2.1 i)
  · funext i
    change Bool.xor (Bool.xor _ (shift d i)) (Bool.xor _ (shift d (σ i)))=_
    rw [←shift_step d i,hxorb]
    exact congrFun x.property.2.2 i

def diffAt {n : Nat} (x y : Sites n→Bool) (i : Fin n) := Bool.xor (x (false,i)) (y (false,i))

lemma diff_side {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x y : Exact σ p r b) (a : Bool) (i : Fin n) :
    diffAt x.val y.val i = Bool.xor (x.val (a,i)) (y.val (a,i)) := by
  cases a
  · rfl
  · exact xor_deltas _ _ _ _ (congrFun (x.property.2.1.trans y.property.2.1.symm) i)

lemma diff_step {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x y : Exact σ p r b) (i : Fin n) : diffAt x.val y.val i=diffAt x.val y.val (σ i) := by
  rw [diff_side x y true (σ i)]
  exact xor_deltas _ _ _ _ (congrFun (x.property.2.2.trans y.property.2.2.symm) i)

def orbitDiff {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x y : Exact σ p r b) : Orb σ→Bool :=
  Quot.lift (diffAt x.val y.val) (by intro i j eq; obtain rfl := eq; exact diff_step x y i)

lemma closed_diff {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x y : Exact σ p r b) (o : Orb σ) (h : ¬loose σ p o) : orbitDiff x y o = false := by
  classical
  unfold loose at h
  push_neg at h
  obtain ⟨i,hi,a,locked⟩ := h
  obtain px := (x.property.1 (a,i)).resolve_left locked
  obtain py := (y.property.1 (a,i)).resolve_left locked
  have same := Option.some.inj (px.symm.trans py)
  rw [←hi]
  change diffAt x.val y.val i = false
  rw [diff_side x y a i,same]
  cases y.val (a,i) <;> rfl

noncomputable def gaugeEquiv {n : Nat} {σ : Equiv.Perm (Fin n)} {p : Pin n} {r b : Fin n→Bool}
    (x : Exact σ p r b) : ({o : Orb σ // loose σ p o}→Bool) ≃ Exact σ p r b where
  toFun := flipAlong x
  invFun y o := orbitDiff x y o.val
  left_inv d := by
    classical
    funext o
    obtain ⟨i,hi⟩ : ∃ i,label σ i=o.val := Quot.inductionOn o.val (fun i => ⟨i,rfl⟩)
    change orbitDiff x (flipAlong x d) o.val = d o
    rw [←hi]
    change Bool.xor (x.val (false,i)) (Bool.xor (x.val (false,i)) (shift d i)) = d o
    rw [xor_inverse]
    have h : loose σ p (label σ i) := hi ▸ o.property
    simp only [shift,dif_pos h]
    exact congrArg d (Subtype.ext hi)
  right_inv y := by
    classical
    apply Subtype.ext
    funext v
    obtain ⟨a,i⟩ := v
    let d := fun o : {o : Orb σ // loose σ p o} => orbitDiff x y o.val
    change Bool.xor (x.val (a,i)) (shift d i)=y.val (a,i)
    have hh : shift d i=diffAt x.val y.val i := by
      by_cases openO : loose σ p (label σ i)
      · simp [shift,openO,d,orbitDiff,label]
      · rw [show shift d i=false by simp [shift,openO]]
        exact (closed_diff x y (label σ i) openO).symm
    rw [hh,diff_side x y a i,xor_inverse]

theorem exact_card {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin n→Bool) :
    letI := Classical.propDecidable
    Fintype.card (Exact σ p r b) = if Nonempty (Exact σ p r b)
      then 2^(Fintype.card {o : Orb σ // loose σ p o}) else 0 := by
  classical
  dsimp only
  split_ifs with h
  · obtain ⟨x⟩ := h
    rw [← Fintype.card_congr (gaugeEquiv x),Fintype.card_fun,Fintype.card_bool]
  · exact Fintype.card_eq_zero_iff.mpr ⟨fun x => h ⟨x⟩⟩

end PEqualNP.Outside.L_pcx_393_aux
