import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9757.SingerThree

-- Each thirteen-bit lane gives the active translates of one cyclic signal
-- when point 0 and exactly one line are on.
def lanes (f : Nat → Nat) : Nat :=
  (List.range 13).foldl (fun z d => z ||| (f d <<< (13*d))) 0

def full : Nat := (1 <<< 169)-1
def p : Nat := lanes (fun _ => 1)
def l : Nat := lanes (fun d => 1 <<< d)
def points : List Nat := [0,4,10,12]
def allowed : Nat := lanes (fun d => if d ∈ points then 8191 else 0)
def masks : List Nat := points.map (fun d => 8191 <<< (13*d))
def band (z : Nat) : Bool :=
  (z &&& (full ^^^ allowed)) == 0 && masks.all (fun m => (z &&& m) != 0)

def leftMask (s : Nat) : Nat := lanes (fun _ => 8191 ^^^ ((1 <<< s)-1))
def rightMask (s : Nat) : Nat := lanes (fun _ => (1 <<< s)-1)
def rotations : List (Nat × Nat × Nat) :=
  (List.range 13).map (fun s => (s,leftMask s,rightMask s))
def orbit (z : Nat) : List Nat := rotations.map (fun ⟨s,hi,lo⟩ =>
  ((z <<< s) &&& hi) ||| ((z >>> (13-s)) &&& lo))
abbrev Rail := Nat × List Nat
def rail (z : Nat) : Rail := (z,orbit z)

-- Translation of either rail is absorbed by the arbitrary displacement on
-- each subsequent use. In a self-pair, t and 13-t yield translated outputs.
def binary (a : Nat) (bs : List Nat) : List Nat :=
  bs.flatMap (fun b => [a &&& b,a ||| b])
def withFirst (a : Rail) (bs : List Rail) : List Nat :=
  [full ^^^ a.1] ++ binary a.1 ((a.2.drop 1).take 6) ++
    bs.flatMap (fun b => binary a.1 b.2)
def extend : List Rail → List Nat
  | [] => []
  | a::bs => withFirst a bs ++ extend bs
def seeds : List Rail := [rail p,rail l]

-- The last operation may use either raw rail and either previous result,
-- with its most recently produced argument at phase zero.
def finish (depth : Nat) (state : List Rail) : Bool :=
  match depth with
  | 0 => state.head?.any (fun a => band a.1)
  | d+1 => (extend state).any (fun z =>
      if d=0 then band z else finish d (rail z :: state))

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
theorem threeLayersFail : finish 3 seeds = false := by decide +kernel

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
theorem shorterLayersFail : finish 2 seeds = false ∧ finish 1 seeds = false ∧
    band p=false ∧ band l=false := by decide +kernel

theorem required (z : Nat) (off : z &&& (full ^^^ allowed)=0)
    (on : ∀ m ∈ masks, z &&& m ≠ 0) : band z=true := by
  simpa [band, off, List.all_eq_true] using on

theorem threeStepsIncompatible {a b c : Nat} (ha : a ∈ extend seeds)
    (hb : b ∈ extend (rail a :: seeds)) (hc : c ∈ extend (rail b :: rail a :: seeds))
    (off : c &&& (full ^^^ allowed)=0) (on : ∀ m ∈ masks, c &&& m ≠ 0) : False := by
  have good := required c off on
  have inner : finish 1 (rail b :: rail a :: seeds)=true := by
    apply List.any_eq_true.mpr
    exact ⟨c,hc,good⟩
  have middle : finish 2 (rail a :: seeds)=true := by
    apply List.any_eq_true.mpr
    exact ⟨b,hb,inner⟩
  have top : finish 3 seeds=true := by
    apply List.any_eq_true.mpr
    exact ⟨a,ha,middle⟩
  rw [threeLayersFail] at top
  contradiction

end PEqualNP.Outside.L_meta_9757.SingerThree
