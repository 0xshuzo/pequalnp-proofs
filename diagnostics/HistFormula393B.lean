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

noncomputable instance orbFinite {n : Nat} (σ : Equiv.Perm (Fin n)) : Fintype (Orb σ) := by
  classical
  exact Fintype.ofSurjective (label σ) (fun o => Quot.inductionOn o (fun i => ⟨i,rfl⟩))

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
      · unfold shift
        rw [dif_pos openO]
        rfl
      · rw [show shift d i=false by simp [shift,openO]]
        exact (closed_diff x y (label σ i) openO).symm
    rw [hh,diff_side x y a i,xor_inverse]

theorem exact_card {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin n→Bool) :
    letI := Classical.propDecidable
    Nat.card (Exact σ p r b) = if Nonempty (Exact σ p r b)
      then 2^(Nat.card {o : Orb σ // loose σ p o}) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨x⟩ := h
    calc
      Nat.card (Exact σ p r b) = Nat.card ({o : Orb σ // loose σ p o}→Bool) := Nat.card_congr (gaugeEquiv x).symm
      _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_fun]
  · letI : IsEmpty (Exact σ p r b) := ⟨fun x => h ⟨x⟩⟩
    simp

def weight {n : Nat} (f : Fin n→Bool) := (Finset.univ.filter fun i => f i=true).card

def liveHist {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :=
  ((Finset.univ : Finset (Sites n→Bool)).filter (fun x =>
    (∀ v, p v=none ∨ p v=some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,i))).card=r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,σ i))).card=b.val)).card

abbrev Row {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Nat) :=
  {x : Sites n→Bool // honors p x ∧ weight (red x)=r ∧ weight (blue σ x)=b}

abbrev Admissible {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Nat) :=
  {v : (Fin n→Bool) × (Fin n→Bool) // weight v.1=r ∧ weight v.2=b ∧ Nonempty (Exact σ p v.1 v.2)}

lemma hist_is_row {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :
    liveHist σ p r b = Nat.card (Row σ p r.val b.val) := by
  classical
  have xor_iff : ∀ a b : Bool, Bool.xor a b=true ↔ a≠b := by decide
  unfold liveHist
  rw [Nat.card_eq_fintype_card,← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp [honors,weight,red,blue,xor_iff]

def flagsEquiv {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Nat) :
    Row σ p r b ≃ (Σ f : Admissible σ p r b, Exact σ p f.val.1 f.val.2) where
  toFun x :=
    let f : (Fin n→Bool)×(Fin n→Bool) := (red x.val, blue σ x.val)
    let ef : Exact σ p f.1 f.2 := ⟨x.val,x.property.1,rfl,rfl⟩
    ⟨⟨f,x.property.2.1,x.property.2.2,⟨ef⟩⟩,ef⟩
  invFun z := ⟨z.2.val,z.2.property.1, by rw [z.2.property.2.1]; exact z.1.property.1,
     by rw [z.2.property.2.2]; exact z.1.property.2.1⟩
  left_inv _ := rfl
  right_inv z := by
    obtain ⟨⟨⟨R,B⟩,hh⟩,⟨v,hp,hR,hB⟩⟩ := z
    dsimp at hR hB
    subst R; subst B
    rfl

theorem live_hist_formula {n : Nat} (σ : Equiv.Perm (Fin n)) (p : Pin n) (r b : Fin (n+1)) :
    liveHist σ p r b = Nat.card (Admissible σ p r.val b.val) *
      2 ^ Nat.card {o : Orb σ // loose σ p o} := by
  classical
  let A := Admissible σ p r.val b.val
  let Free := {o : Orb σ // loose σ p o}
  let e : (Σ f : A, Exact σ p f.val.1 f.val.2) ≃ (A × (Free→Bool)) :=
    { toFun := fun z => (z.1, (gaugeEquiv (Classical.choice z.1.property.2.2)).symm z.2)
      invFun := fun z => ⟨z.1, gaugeEquiv (Classical.choice z.1.property.2.2) z.2⟩
      left_inv := by rintro ⟨f,x⟩; simp
      right_inv := by rintro ⟨f,x⟩; simp }
  rw [hist_is_row,Nat.card_congr ((flagsEquiv σ p r.val b.val).trans e)]
  simp [Nat.card_eq_fintype_card,Fintype.card_fun,A,Free]

end PEqualNP.Outside.L_pcx_393_aux
