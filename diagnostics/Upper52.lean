import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9682.Build
open PEqualNP.Search PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Ln := CPLine V
abbrev Fe := PHP 4 3
def pigeon (p : Fin 4) : Clause V := Finset.univ.image (fun h : Fin 3 => ((p,h),true))
def pair (p q : Fin 4) (h : Fin 3) : Clause V := {((p,h),false),((q,h),false)}
inductive Op where
  | beg (p : Fin 4)
  | coll (p q : Fin 4) (h : Fin 3)
  | add (a b : Nat)
  | scale (a m : Nat)
  | cut (a d : Nat)
def goal : Ln := (0,1)
def lookup (B : List Ln) (i : Nat) : Ln := B.getD i goal
def eqv (x y : Ln) : Prop := (∀ v, x.1 v=y.1 v) ∧ x.2=y.2
instance {x y} : Decidable (eqv x y) := by unfold eqv; infer_instance
theorem equal {x y} (eq : eqv x y) : x=y := Prod.ext (funext eq.1) eq.2
theorem found {B : List Ln} {i : Nat} (bound : i<B.length) : lookup B i ∈ B := by
  simp only [lookup,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some]
  exact List.getElem_mem bound
def good (B : List Ln) (e : Ln) : Op → Prop
  | .beg p => eqv e (clauseCP (pigeon p))
  | .coll p q h => p≠q ∧ eqv e (clauseCP (pair p q h))
  | .add i j =>
    i<B.length ∧ j<B.length ∧ eqv e ((lookup B i).1 + (lookup B j).1,(lookup B i).2+(lookup B j).2)
  | .scale i m => i<B.length ∧ eqv e ((m:ℤ) • (lookup B i).1,(m:ℤ)*(lookup B i).2)
  | .cut i d => i<B.length ∧ 0<d ∧ (∀ v, (d:ℤ) ∣ (lookup B i).1 v) ∧
    eqv e (fun v => (lookup B i).1 v/(d:ℤ), -((-(lookup B i).2)/(d:ℤ)))
instance (B e op) : Decidable (good B e op) := by cases op <;> unfold good <;> infer_instance
theorem sound {B e op} (der : IsCPDerivation Fe B) (ok : good B e op) : IsCPDerivation Fe (e::B) := by
  cases op with
  | beg p => rw [equal ok]; exact .ax (pigeon p) der (Or.inl ⟨p,rfl⟩)
  | coll p q h =>
    obtain ⟨ne,eq⟩ := ok
    rw [equal eq]
    exact .ax (pair p q h) der (Or.inr ⟨p,q,h,ne,rfl⟩)
  | add i j =>
    obtain ⟨bi,bj,eq⟩ := ok
    rw [equal eq]
    exact .add der (found bi) (found bj)
  | scale i m =>
    obtain ⟨bi,eq⟩ := ok
    rw [equal eq]
    exact .mul m der (found bi)
  | cut i d =>
    obtain ⟨bi,pos,divs,eq⟩ := ok
    rw [equal eq]
    exact .div d der (found bi) pos divs
abbrev Step := Ln × Op
def accept (B : List Ln) : List Step → Bool
  | [] => true
  | (e,op)::ss => decide (good B e op) && accept (e::B) ss
def finish (B : List Ln) : List Step → List Ln
  | [] => B
  | (e,_)::ss => finish (e::B) ss
theorem replay {steps B} (hb : IsCPDerivation Fe B) (pass : accept B steps=true) :
    IsCPDerivation Fe (finish B steps) := by
  induction steps generalizing B with
  | nil => exact hb
  | cons hd tail ih =>
    obtain ⟨e,op⟩ := hd
    simp only [accept,Bool.and_eq_true,decide_eq_true_eq] at pass
    exact ih (sound hb pass.1) pass.2
def coeffs (a : Array Int) (b : Int) : Ln := (fun v => a[3*v.1.val+v.2.val]!,b)
set_option maxRecDepth 12000
set_option maxHeartbeats 0
def certificate : List Step := [
  (coeffs #[-1,0,0,-1,0,0,0,0,0,0,0,0] (-1), .coll 0 1 0),
  (coeffs #[-1,0,0,0,0,0,-1,0,0,0,0,0] (-1), .coll 0 2 0),
  (coeffs #[0,0,0,-1,0,0,-1,0,0,0,0,0] (-1), .coll 1 2 0),
  (coeffs #[-2,0,0,-1,0,0,-1,0,0,0,0,0] (-2), .add 2 1),
  (coeffs #[-2,0,0,-2,0,0,-2,0,0,0,0,0] (-3), .add 0 1),
  (coeffs #[-1,0,0,-1,0,0,-1,0,0,0,0,0] (-1), .cut 0 2),
  (coeffs #[-2,0,0,-2,0,0,-2,0,0,0,0,0] (-2), .scale 0 2),
  (coeffs #[-1,0,0,0,0,0,0,0,0,-1,0,0] (-1), .coll 0 3 0),
  (coeffs #[0,0,0,-1,0,0,0,0,0,-1,0,0] (-1), .coll 1 3 0),
  (coeffs #[0,0,0,0,0,0,-1,0,0,-1,0,0] (-1), .coll 2 3 0),
  (coeffs #[-3,0,0,-2,0,0,-2,0,0,-1,0,0] (-3), .add 3 2),
  (coeffs #[-3,0,0,-3,0,0,-2,0,0,-2,0,0] (-4), .add 0 2),
  (coeffs #[-3,0,0,-3,0,0,-3,0,0,-3,0,0] (-5), .add 0 2),
  (coeffs #[-1,0,0,-1,0,0,-1,0,0,-1,0,0] (-1), .cut 0 3),
  (coeffs #[0,-1,0,0,-1,0,0,0,0,0,0,0] (-1), .coll 0 1 1),
  (coeffs #[0,-1,0,0,0,0,0,-1,0,0,0,0] (-1), .coll 0 2 1),
  (coeffs #[0,0,0,0,-1,0,0,-1,0,0,0,0] (-1), .coll 1 2 1),
  (coeffs #[0,-2,0,0,-1,0,0,-1,0,0,0,0] (-2), .add 2 1),
  (coeffs #[0,-2,0,0,-2,0,0,-2,0,0,0,0] (-3), .add 0 1),
  (coeffs #[0,-1,0,0,-1,0,0,-1,0,0,0,0] (-1), .cut 0 2),
  (coeffs #[0,-2,0,0,-2,0,0,-2,0,0,0,0] (-2), .scale 0 2),
  (coeffs #[0,-1,0,0,0,0,0,0,0,0,-1,0] (-1), .coll 0 3 1),
  (coeffs #[0,0,0,0,-1,0,0,0,0,0,-1,0] (-1), .coll 1 3 1),
  (coeffs #[0,0,0,0,0,0,0,-1,0,0,-1,0] (-1), .coll 2 3 1),
  (coeffs #[0,-3,0,0,-2,0,0,-2,0,0,-1,0] (-3), .add 3 2),
  (coeffs #[0,-3,0,0,-3,0,0,-2,0,0,-2,0] (-4), .add 0 2),
  (coeffs #[0,-3,0,0,-3,0,0,-3,0,0,-3,0] (-5), .add 0 2),
  (coeffs #[0,-1,0,0,-1,0,0,-1,0,0,-1,0] (-1), .cut 0 3),
  (coeffs #[0,0,-1,0,0,-1,0,0,0,0,0,0] (-1), .coll 0 1 2),
  (coeffs #[0,0,-1,0,0,0,0,0,-1,0,0,0] (-1), .coll 0 2 2),
  (coeffs #[0,0,0,0,0,-1,0,0,-1,0,0,0] (-1), .coll 1 2 2),
  (coeffs #[0,0,-2,0,0,-1,0,0,-1,0,0,0] (-2), .add 2 1),
  (coeffs #[0,0,-2,0,0,-2,0,0,-2,0,0,0] (-3), .add 0 1),
  (coeffs #[0,0,-1,0,0,-1,0,0,-1,0,0,0] (-1), .cut 0 2),
  (coeffs #[0,0,-2,0,0,-2,0,0,-2,0,0,0] (-2), .scale 0 2),
  (coeffs #[0,0,-1,0,0,0,0,0,0,0,0,-1] (-1), .coll 0 3 2),
  (coeffs #[0,0,0,0,0,-1,0,0,0,0,0,-1] (-1), .coll 1 3 2),
  (coeffs #[0,0,0,0,0,0,0,0,-1,0,0,-1] (-1), .coll 2 3 2),
  (coeffs #[0,0,-3,0,0,-2,0,0,-2,0,0,-1] (-3), .add 3 2),
  (coeffs #[0,0,-3,0,0,-3,0,0,-2,0,0,-2] (-4), .add 0 2),
  (coeffs #[0,0,-3,0,0,-3,0,0,-3,0,0,-3] (-5), .add 0 2),
  (coeffs #[0,0,-1,0,0,-1,0,0,-1,0,0,-1] (-1), .cut 0 3),
  (coeffs #[1,1,1,0,0,0,0,0,0,0,0,0] (1), .beg 0),
  (coeffs #[0,0,0,1,1,1,0,0,0,0,0,0] (1), .beg 1),
  (coeffs #[0,0,0,0,0,0,1,1,1,0,0,0] (1), .beg 2),
  (coeffs #[0,0,0,0,0,0,0,0,0,1,1,1] (1), .beg 3),
  (coeffs #[-1,-1,0,-1,-1,0,-1,-1,0,-1,-1,0] (-2), .add 32 18),
  (coeffs #[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1] (-3), .add 0 5),
  (coeffs #[0,0,0,-1,-1,-1,-1,-1,-1,-1,-1,-1] (-2), .add 0 5),
  (coeffs #[0,0,0,0,0,0,-1,-1,-1,-1,-1,-1] (-1), .add 0 5),
  (coeffs #[0,0,0,0,0,0,0,0,0,-1,-1,-1] (0), .add 0 5),
  (goal, .add 0 5)]
theorem valid : accept [] certificate=true := by decide +kernel
theorem result : ∃ π : List (CPLine (Fin (3+1) × Fin 3)), IsCPRefutation (PHP (3+1) 3) π ∧ π.length ≤ 52 := by
  refine ⟨finish [] certificate,⟨replay .nil valid,?_⟩,?_⟩
  · exact List.mem_cons_self
  · decide +kernel
end PEqualNP.Outside.L_meta_9682.Build
