import PEqualNP.Defs
namespace Research9815.ShadowCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := BitVec 8
def norm (a : V) := if a.getLsbD 7 then (~~~a).toNat else a.toNat
def bits (k a b : Nat) := match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def typ (andGate x y : Bool) : Nat :=
  if x=y then (if andGate != x then 0 else 1) else if andGate != x then 2 else 3
theorem bounded : ∀a : V,norm a<128 := by decide +kernel
theorem invert : ∀a : V,norm (~~~a)=norm a := by decide +kernel
theorem small : ∀g x y : Bool,typ g x y<4 := by decide

def limb (a b : Fin 16) : V := BitVec.ofNat 8 (a.val*16+b.val)
def valid (a b : V) : Bool :=
  bits (typ true (a.getLsbD 7) (b.getLsbD 7)) (norm a) (norm b) == norm (a &&& b) &&
  bits (typ false (a.getLsbD 7) (b.getLsbD 7)) (norm a) (norm b) == norm (a ||| b)
set_option maxRecDepth 12000 in
private theorem row0 : ∀i : Fin 16,∀b : V,valid (limb 0 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row1 : ∀i : Fin 16,∀b : V,valid (limb 1 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row2 : ∀i : Fin 16,∀b : V,valid (limb 2 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row3 : ∀i : Fin 16,∀b : V,valid (limb 3 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row4 : ∀i : Fin 16,∀b : V,valid (limb 4 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row5 : ∀i : Fin 16,∀b : V,valid (limb 5 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row6 : ∀i : Fin 16,∀b : V,valid (limb 6 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row7 : ∀i : Fin 16,∀b : V,valid (limb 7 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row8 : ∀i : Fin 16,∀b : V,valid (limb 8 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row9 : ∀i : Fin 16,∀b : V,valid (limb 9 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row10 : ∀i : Fin 16,∀b : V,valid (limb 10 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row11 : ∀i : Fin 16,∀b : V,valid (limb 11 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row12 : ∀i : Fin 16,∀b : V,valid (limb 12 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row13 : ∀i : Fin 16,∀b : V,valid (limb 13 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row14 : ∀i : Fin 16,∀b : V,valid (limb 14 i) b=true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem row15 : ∀i : Fin 16,∀b : V,valid (limb 15 i) b=true := by decide +kernel
theorem pair (a b : V) : valid a b=true := by
  have reps : ∀v : V, ∃i j : Fin 16,limb i j=v := by decide +kernel
  obtain ⟨i,j,rfl⟩ := reps a
  fin_cases i
  · exact row0 j b
  · exact row1 j b
  · exact row2 j b
  · exact row3 j b
  · exact row4 j b
  · exact row5 j b
  · exact row6 j b
  · exact row7 j b
  · exact row8 j b
  · exact row9 j b
  · exact row10 j b
  · exact row11 j b
  · exact row12 j b
  · exact row13 j b
  · exact row14 j b
  · exact row15 j b
def compute (op : GateOp) (qs : List V) : V := match op with
  | .and => qs.foldr (fun a b => a &&& b) 255
  | .or => qs.foldr (fun a b => a ||| b) 0
  | .not => ~~~(qs.headD 0)
  | _ => 0
def allowed (op : GateOp) := op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not
def encStep (g : Gate) (qs : List V) := compute g.op (g.inputs.map (fun i => qs.getD i 0))
def trace (raw : Finset Nat) : List Nat → Prop
  | [] => True
  | t::s => trace raw s ∧ ∃k<4,∃a∈raw∪s.toFinset,∃b∈raw∪s.toFinset,bits k a b=t
theorem step (op : GateOp) (good : allowed op) (a : List V) (len : a.length≤2)
    (U : Finset Nat) (has0 : 0∈U) (av : ∀w∈a,norm w∈U) :
    norm (compute op a)∈U ∨ ∃k<4,∃x∈U,∃y∈U,bits k x y=norm (compute op a) := by
  have zero : norm 0=0 := by decide
  have ones : norm 255=0 := by decide
  have idA : ∀z : V,z &&& 255=z := by decide +kernel
  have idO : ∀z : V,z ||| 0=z := by decide +kernel
  rcases good with rfl|rfl|rfl
  · cases a with
    | nil => exact Or.inl (by simpa [compute,ones] using has0)
    | cons a more =>
      cases more with
      | nil => exact Or.inl (by simpa [compute,idA] using av a (by simp))
      | cons b tail =>
        have nil : tail=[] := by have := List.length_eq_zero_iff.mp (show tail.length=0 by simp at len; omega); assumption
        subst tail
        have val := (Bool.and_eq_true_iff.mp (pair a b)).1
        refine Or.inr ⟨_,small true _ _,_,av a (by simp),_,av b (by simp),?_⟩
        simpa [compute,idA] using val
  · cases a with
    | nil => exact Or.inl (by simpa [compute,zero] using has0)
    | cons a more =>
      cases more with
      | nil => exact Or.inl (by simpa [compute,idO] using av a (by simp))
      | cons b tail =>
        have nil : tail=[] := by have := List.length_eq_zero_iff.mp (show tail.length=0 by simp at len; omega); assumption
        subst tail
        have val := (Bool.and_eq_true_iff.mp (pair a b)).2
        refine Or.inr ⟨_,small false _ _,_,av a (by simp),_,av b (by simp),?_⟩
        simpa [compute,idO] using val
  · cases a with
    | nil => exact Or.inl (by simpa [compute,invert,zero] using has0)
    | cons a l => exact Or.inl (by simpa [compute,invert] using av a (by simp))
end Research9815.ShadowCircuit
