import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9815.Phase

structure Node where
  left : Nat
  right : Nat
  leftNeg : Bool
  rightNeg : Bool

def need (phase sign : Bool) : Bool := xor phase sign

def compatible (pivot : Nat) (phase : Nat → Bool) (g : Node) (q : Bool) : Prop :=
  (g.left ≠ pivot → q = need (phase g.left) g.leftNeg) ∧
  (g.right ≠ pivot → q = need (phase g.right) g.rightNeg)

def passes (pivot : Nat) (phase : Nat → Bool) (g : Node) : Bool :=
  decide (g.left = pivot) || decide (g.right = pivot) ||
    (need (phase g.left) g.leftNeg == need (phase g.right) g.rightNeg)

def chosen (pivot : Nat) (phase : Nat → Bool) (g : Node) : Bool :=
  if g.left = pivot then need (phase g.right) g.rightNeg else need (phase g.left) g.leftNeg

theorem phase_step (r : Nat) (p : Nat → Bool) (g : Node) (h : g.left ≠ g.right)
    (q : Bool) :
    compatible r p g q ↔ passes r p g = true ∧ q = chosen r p g := by
  by_cases ha : g.left = r
  · have hb : g.right ≠ r := fun e => h (ha.trans e.symm)
    simp [compatible,passes,chosen,ha,hb]
  · by_cases hb : g.right = r
    · simp [compatible,passes,chosen,ha,hb]
    · simp [compatible,passes,chosen,ha,hb]
      constructor
      · rintro ⟨a,b⟩
        exact ⟨a.symm.trans b,a⟩
      · rintro ⟨eq,a⟩
        exact ⟨a,a.trans eq⟩

def data (sign value : Bool) : Bool := xor sign value
def realize (op a b : Bool) : Bool := if op then a || b else a && b

theorem gate_value (q sa sb a b : Bool) :
    realize q (data (need q sa) a) (data (need q sb) b) =
      data q (data sa a && data sb b) := by
  cases q <;> cases sa <;> cases sb <;> cases a <;> cases b <;> rfl

theorem existing_rail {q p s : Bool} (h : q = need p s) : need q s = p := by
  subst q
  cases p <;> cases s <;> rfl

theorem source_agrees {r p g q} (h : compatible r p g q) :
    (g.left ≠ r → need q g.leftNeg = p g.left) ∧
    (g.right ≠ r → need q g.rightNeg = p g.right) :=
  ⟨fun e => existing_rail (h.1 e),fun e => existing_rail (h.2 e)⟩

def extend (p : Nat → Bool) (idx : Nat) (q : Bool) : Nat → Bool :=
  fun j => if j = idx then q else p j

def tracks (r : Nat) : Nat → (Nat → Bool) → List Node → Prop
  | _, _, [] => True
  | k, p, g :: gs => ∃ q, compatible r p g q ∧ tracks r (k+1) (extend p k q) gs

def accepts (r : Nat) : Nat → (Nat → Bool) → List Node → Bool
  | _, _, [] => true
  | k, p, g :: gs => passes r p g && accepts r (k+1) (extend p k (chosen r p g)) gs

theorem exact_phases (r k : Nat) (p : Nat → Bool) (gs : List Node)
    (distinct : ∀ g ∈ gs, g.left ≠ g.right) :
    tracks r k p gs ↔ accepts r k p gs = true := by
  induction gs generalizing k p with
  | nil => simp [tracks,accepts]
  | cons g gs ih =>
    have hd := distinct g (by simp)
    have ht : ∀ t ∈ gs, t.left ≠ t.right := fun t h => distinct t (by simp [h])
    simp only [tracks,accepts,Bool.and_eq_true]
    constructor
    · rintro ⟨q,hc,hrest⟩
      obtain ⟨pass,rfl⟩ := (phase_step r p g hd q).mp hc
      exact ⟨pass,(ih _ _ ht).mp hrest⟩
    · rintro ⟨pass,hrest⟩
      exact ⟨_,(phase_step r p g hd _).mpr ⟨pass,rfl⟩,(ih _ _ ht).mpr hrest⟩

end PEqualNP.Outside.L_meta_9815.Phase
