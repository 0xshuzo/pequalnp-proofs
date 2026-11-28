import PEqualNP.Defs
namespace Research9755.FirstPulse
open PEqualNP.CircuitLowerBounds
abbrev Val (X : Type) := X → Bool
def fixed (v : Val X) := (v,v)
def lo : Val X := fun _ => false
def hi : Val X := fun _ => true
def pivot : Val X × Val X := (lo,hi)
def evaluate (op : GateOp) (p : List (Val X × Val X)) : Val X × Val X :=
  (fun x => op.eval (p.map fun a => a.1 x),fun x => op.eval (p.map fun a => a.2 x))
def source (S : Set (Val X)) (v : Val X × Val X) := (∃ b∈S, v = fixed b) ∨ v=pivot
def pulse (S : Set (Val X)) (v : Val X × Val X) :=
  v.1=v.2 ∨ v=pivot ∨ v=(hi,lo) ∨ (∃ b∈S, v=(lo,b)) ∨ (∃ b∈S, v=(b,hi))
theorem classify (S : Set (Val X)) (op : GateOp) (args : List (Val X × Val X))
    (legal : op=.and ∨ op=.or ∨ op=.not) (small : args.length≤2)
    (old : ∀ a∈args, source S a) : pulse S (evaluate op args) := by
  classical
  cases args with
  | nil => exact Or.inl rfl
  | cons a tail =>
    have ha := old a (by simp)
    cases tail with
    | nil =>
      rcases ha with ⟨v,hv,rfl⟩ | rfl
      · exact Or.inl rfl
      · rcases legal with rfl | rfl | rfl
        · exact Or.inr (Or.inl (by rfl))
        · exact Or.inr (Or.inl (by rfl))
        · exact Or.inr (Or.inr (Or.inl (by rfl)))
    | cons b rest =>
      have hb := old b (by simp)
      have er : rest=[] := by cases rest <;> simp_all
      subst rest
      rcases ha with ⟨u,hu,rfl⟩ | rfl <;> rcases hb with ⟨v,hv,rfl⟩ | rfl
      · exact Or.inl rfl
      · rcases legal with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u,hu,by
            apply Prod.ext <;> funext x <;> simp [evaluate,fixed,pivot,lo,hi,GateOp.eval]⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u,hu,by
            apply Prod.ext <;> funext x <;> simp [evaluate,fixed,pivot,lo,hi,GateOp.eval]⟩)))
        · exact Or.inl rfl
      · rcases legal with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v,hv,by
            apply Prod.ext <;> funext x <;> simp [evaluate,fixed,pivot,lo,hi,GateOp.eval]⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v,hv,by
            apply Prod.ext <;> funext x <;> simp [evaluate,fixed,pivot,lo,hi,GateOp.eval]⟩)))
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases legal with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
theorem changing_zero_face (S : Set (Val X)) (v : Val X × Val X) (p : pulse S v)
    (change : v.1 ≠ v.2) : v.1=lo ∨ v.1=hi ∨ v.1 ∈ S := by
  rcases p with e | rfl | rfl | ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
  · exact (change e).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr hu)
end Research9755.FirstPulse
