import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_166_CommonFive
def sub (x y : Nat) := x &&& y == x
def axis (n x h : Nat) := (x >>> (n*h)) &&& (2^n-1)
def allCols (n k x : Nat) := (List.range k).all (fun h => axis n x h != 0)
def ground (n k x : Nat) := ((List.range k).foldl (fun a h => a ||| axis n x h) 0) != 2^n-1
def cut (n x v : Nat) : Nat × Nat :=
  let b := 2^v
  let h := v/n
  (x ^^^ b,(x ^^^ (axis n x h <<< (n*h))) ||| b)
def splitOK (n x v : Nat) :=
  let b := 2^v
  x &&& b == b && axis n x (v/n) != 2^(v%n)
def next (s : List Nat) (v u : Nat) : Option (List Nat) := do
  let use := s.filter (fun x => sub x u)
  if use.foldl (fun a x => a ||| x) 0 != u || !splitOK 5 u v then return ← none
  let (a,b) := cut 5 u v
  let t := (a::b::s.filter (fun x => !sub x u)).filter (fun x => !ground 5 4 x)
  return t.filter (fun x => !(t.any (fun y => x != y && sub x y)))
def roots : List (Nat × Nat) := [(1,1048575),(5,1048543),(6,1048511),(7,1046463),(4,980927)]
def capacity : List Nat := [2,2,2,1,2,1,1,2,1,1,1,1,1,1,1,1,0,1,1,1]
def programs : List (List (Nat × Nat)) := [[(8,1450),(3,1325),(7,1522),(5,1533),(1,1535),(10,4027),(9,3925),(2,3870),(6,4081)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871)],[(4,2650),(3,605),(11,3922),(9,3933),(1,3935),(6,3067),(5,1525),(2,510),(10,4081),(4,3838),(8,4094),(0,4095)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871),(0,3823),(8,4079),(4,4095)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871),(0,3823),(8,4079),(4,4095)],[(0,2725),(7,725),(11,3877),(9,4053),(5,4085),(2,3007),(1,1375),(6,495),(10,3871),(0,3823),(8,4079),(4,4095)],[(9,1689),(3,1566),(7,1777),(4,1790),(0,1791),(10,4027),(8,3942),(2,3885),(6,4082)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(9,1689),(3,1566),(7,1777),(4,1790),(0,1791),(10,4027),(8,3942),(2,3885),(6,4082)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)],[(9,1689),(3,1566),(7,1777),(4,1790),(0,1791),(10,4027),(8,3942),(2,3885),(6,4082)],[(4,1686),(1,1179),(9,3988),(10,3995),(2,3999),(7,2039),(6,2553),(3,510),(11,4081),(4,3838),(8,4094),(0,4095)],[(9,1689),(7,1761),(3,1567),(0,1775),(4,1791),(10,4027),(8,3942),(6,4050),(2,3887)],[(1,2454),(7,486),(11,3862),(8,4070),(4,4086),(2,3007),(0,1647),(6,735),(10,3887)]]
def physical (p h j : Nat) :=
  let r := j%4
  let c := j/4
  4*(if r<p then r else r+1)+(if c<h then c else c+1)
def projection (p h u : Nat) :=
  (List.range 12).foldl (fun out j =>
    let z := physical p h j
    if u.testBit (5*(z%4)+z/4) then out ||| 2^j else out) 0
def built (basis : List Nat) : List (Nat × Nat) → Option (List Nat)
  | [] => some basis
  | (v,u)::s => do
    let (a,b) := cut 4 u v
    if v>=12 || !splitOK 4 u v || !(basis.any (sub a)) || !(basis.any (sub b)) then return ← none
    built (u::basis) s
def checkFace (s : List Nat) (i : Nat) := Id.run do
  let p := i/4
  let h := i%4
  let prog := programs.getD i []
  let raw := (List.range 4).map (fun r => 4095 ^^^ (273 <<< r))
  let some basis := built raw prog | return false
  let fits := (List.range 12).all (fun j =>
    let big := physical p h j
    (prog.countP (fun x => x.1==j))+(roots.countP (fun x => x.1==big))≤capacity.getD big 0)
  return fits && s.all (fun u =>
    let q := projection p h u
    !(u.testBit (5*h+p)) || !(allCols 4 3 q) || basis.any (sub q))
def checkCommon := Id.run do
  let some s := roots.foldlM (fun t e => next t (5*(e.1%4)+e.1/4) e.2) [1048575] | return false
  return capacity.sum == 24 && roots.length == 5 && (List.range 20).all (checkFace s)
set_option maxHeartbeats 0 in
theorem certificate : checkCommon=true := by decide +kernel
end PEqualNP.Outside.L_pcx_166_CommonFive
