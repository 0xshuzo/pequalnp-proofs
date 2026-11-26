import PEqualNP.Defs

namespace L237Mod19

set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev Shape := Nat × Nat × Nat
def shapeKey (v : Shape) : Nat := 361*v.1 + 19*v.2.1 + v.2.2
def allShapes : List Shape :=
  (List.range 19).flatMap fun a => (List.range (19-a)).flatMap fun db =>
    (List.range (19-a-db)).map fun dc => (a,a+db,a+db+dc)
def reps : List Shape := [(0,0,0),(0,0,1),(0,1,2),(0,1,3),(0,1,4),(0,1,8)]
def sortedKey (a b c : Nat) : Nat :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  shapeKey (lo,a+b+c-lo-hi,hi)
def orbit (v : Shape) : List Nat :=
  (List.range 18).flatMap fun l => (List.range 19).map fun b =>
    sortedKey (((l+1)*v.1+b)%19) (((l+1)*v.2.1+b)%19) (((l+1)*v.2.2+b)%19)
def coverage : Bool :=
  let all := reps.flatMap orbit
  allShapes.all fun x => all.contains (shapeKey x)
theorem covered : coverage = true := by decide +kernel

def elementary1 (u v w : Nat) : Nat := (u) % 19
def elementary2 (u v w : Nat) : Nat := (14*v + 18*u^2) % 19
def elementary3 (u v w : Nat) : Nat := (w + u*v + 10*u^3) % 19
def coordinate4 (u v w : Nat) : Nat := (3*v^2 + u*w + 6*u^2*v + 8*u^4) % 19
def coordinate5 (u v w : Nat) : Nat := (9*v*w + 13*u*v^2 + 15*u^2*w + u^3*v + 9*u^5) % 19
def coordinate6 (u v w : Nat) : Nat := (16*w^2 + v^3 + 15*u*v*w + 7*u^2*v^2 + 11*u^4*v + 6*u^6) % 19
def coordinate7 (u v w : Nat) : Nat := (15*v^2*w + 16*u*w^2 + 5*u*v^3 + 5*u^2*v*w + 2*u^3*v^2 + 13*u^4*w + 14*u^5*v + 7*u^7) % 19
def coords (a : Shape) : List Nat :=
  let u := (a.1+a.2.1+a.2.2)%19
  let v := (a.1*a.2.1+a.1*a.2.2+a.2.1*a.2.2)%19
  let w := (a.1*a.2.1*a.2.2)%19
  let x := elementary1 u v w
  let y := elementary2 u v w
  let z := elementary3 u v w
  [x,y,z,coordinate4 x y z,coordinate5 x y z,coordinate6 x y z,coordinate7 x y z]
def subtract (a b : Nat) : Nat := (a+19-b)%19
def inverse (v : Nat) : Nat := ([0, 1, 10, 13, 5, 4, 16, 11, 12, 17, 2, 7, 8, 3, 15, 14, 6, 9, 18] : List Nat).getD v 0
def projectiveKey (x : List Nat) : Nat :=
  let s := inverse ((x.find? (fun a => a != 0)).getD 0)
  x.foldl (fun v z => v*19+z*s%19) 0
def sortedFrom : Nat → List Nat → Bool
  | _, [] => true
  | a, b :: t => decide (a<b) && sortedFrom b t
def distinct (b : Shape) : Bool :=
  let x := coords b
  let ks := ((allShapes.filter (fun v => v != b)).map fun v =>
    projectiveKey (List.zipWith subtract (coords v) x)).mergeSort (fun i j => decide (i ≤ j))
  sortedFrom 0 ks

def linear (z : List Nat) (a b c : Nat) : List Nat :=
  let u := z.getD 0 0
  let v := z.getD 1 0
  let w := z.getD 2 0
  [(((w + 12*u*v + 13*u^3) % 19)*a+((6*v + 6*u^2) % 19)*b+((u) % 19)*c)%19,
  (((13*v^2 + 11*u*w + 3*u^2*v + 7*u^4) % 19)*a+((9*w + 7*u*v + u^3) % 19)*b+((9*v + 15*u^2) % 19)*c)%19,
  (((15*v*w + 14*u*v^2 + 6*u^3*v + 17*u^5) % 19)*a+((3*v^2 + 15*u*w + 14*u^2*v + 11*u^4) % 19)*b+((13*w + 15*u*v) % 19)*c)%19,
  (((16*w^2 + 5*v^3 + 10*u*v*w + 6*u^2*v^2 + 14*u^3*w + 13*u^4*v + 11*u^6) % 19)*a+((11*v*w + 15*u*v^2 + 5*u^2*w + 4*u^3*v + 14*u^5) % 19)*b+((15*v^2 + 13*u*w + 5*u^2*v + 13*u^4) % 19)*c)%19]
def second (z : List Nat) (a b c : Nat) : List Nat :=
  let u := z.getD 0 0
  let v := z.getD 1 0
  let w := z.getD 2 0
  [(((6*v + 10*u^2) % 19)*a^2+((12*u) % 19)*a*b+((1) % 19)*a*c+((3) % 19)*b^2)%19,
  (((15*w + 3*u*v + 14*u^3) % 19)*a^2+((7*v + 3*u^2) % 19)*a*b+((11*u) % 19)*a*c+((13*u) % 19)*b^2+((9) % 19)*b*c)%19,
  (((7*v^2 + 9*u^2*v + 14*u^4) % 19)*a^2+((15*w + 9*u*v + 6*u^3) % 19)*a*b+((15*v) % 19)*a*c+((3*v + 7*u^2) % 19)*b^2+((15*u) % 19)*b*c+((16) % 19)*c^2)%19,
  (((5*v*w + 6*u*v^2 + 2*u^2*w + 7*u^3*v + 14*u^5) % 19)*a^2+((15*v^2 + 10*u*w + 12*u^2*v + 13*u^4) % 19)*a*b+((13*w + 10*u*v + 14*u^3) % 19)*a*c+((15*w + 15*u*v + 2*u^3) % 19)*b^2+((11*v + 5*u^2) % 19)*b*c+((16*u) % 19)*c^2)%19]
def tangents (b : Shape) : Bool :=
  let x := coords b
  (allShapes.filter (fun v => v != b)).all fun v =>
    let d := List.zipWith subtract (coords v) x
    linear x (d.getD 0 0) (d.getD 1 0) (d.getD 2 0) != d.drop 3
def directions : List Shape :=
  ([(0,0,1)] ++ (List.range 19).map (fun c => (0,1,c))) ++
    (List.range 19).flatMap (fun b => (List.range 19).map (fun c => (1,b,c)))
def flexes (b : Shape) : Bool :=
  let x := coords b
  directions.all fun t =>
    ((second x t.1 t.2.1 t.2.2).all (fun z => z == 0)) ==
      ((b == (0,0,0)) && (t == (1,0,0)))
theorem base0 : distinct (0,0,0) = true ∧ tangents (0,0,0) = true ∧ flexes (0,0,0) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem base1 : distinct (0,0,1) = true ∧ tangents (0,0,1) = true ∧ flexes (0,0,1) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem base2 : distinct (0,1,2) = true ∧ tangents (0,1,2) = true ∧ flexes (0,1,2) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem base3 : distinct (0,1,3) = true ∧ tangents (0,1,3) = true ∧ flexes (0,1,3) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem base4 : distinct (0,1,4) = true ∧ tangents (0,1,4) = true ∧ flexes (0,1,4) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem base5 : distinct (0,1,8) = true ∧ tangents (0,1,8) = true ∧ flexes (0,1,8) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end L237Mod19
