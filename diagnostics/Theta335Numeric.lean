import PEqualNP.Defs
namespace Pilot
abbrev V (r : Nat) := BitVec r
def full (r : Nat) := BitVec.allOnes r
def on {r} (a : V r) (i : Fin r) := a.getLsbD i.val
def support {r} (a : V r) : Finset (Fin r) := Finset.univ.filter (fun i => on a i)
def pop {r} (a : V r) := (support a).card
def Extend {r} (p : List (V r)) (a : V r) : List (V r) := (p ++ p.map (fun v => v &&& a)).eraseDups
def halves {r} (cells : List (V r)) (a : V r) : List (V r) :=
  cells.flatMap (fun z => [z &&& a,z &&& ~~~a])
def fits {r} (cells : List (V r)) (a : V r) (cap : ℕ) : Bool :=
  (halves cells a).all (fun z => decide (pop z ≤ cap))

def possible {r} (tail : ℕ) : ℕ → List (V r) → List (V r) → Bool
  | 0, _, cells => cells.all (fun z => decide (pop z ≤ 2^tail))
  | d+1, p, cells =>
    let pool := p.filter (fun a => fits cells a (2^(d+tail)))
    pool.any (fun a => pool.any (fun b =>
      possible tail d (Extend p (a ||| b)) ((halves cells a)++(halves cells b))))
def seed {r} : List (V r) → List (V r)
  | [] => [0,full r]
  | a::rest => Extend (seed rest) a
def cols : Fin 10 → V 16 := ![47870,54220,58352,65280,64682,18261,27955,23823,15615,1023]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem obstruction : possible 1 3 (seed (List.ofFn cols)) [full 16]=false := by decide +kernel
end Pilot
