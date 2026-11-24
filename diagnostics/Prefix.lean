import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Prefix2567
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem semantic (x : Fin 26 → Bool) :
    (⟨([10309,12627,2813,10509,11012,13031,3217,10408,10911,13435,3618,10307,10810,13839,4019,10206,10709,14243,4420,10004,10507,14647,4822,10304,10612,15051,5223,10203,10511,15455,5624,10102,10410,15859,6025,12933,16237,16341,16445,16549,16653,16757,16861] : List ℕ).map (fun e => ⟨if e < 10000 then .and else .or, [(e / 100) % 100,e % 100]⟩),69⟩ : Circuit).eval (List.ofFn x ++ [x 0 || x 1]) = (((((((((((x 0 || x 1) || (x 3 || x 9)) && x 13) || (((x 5 || x 9) || (x 10 || x 12)) && x 17)) || (((x 4 || x 8) || (x 9 || x 11)) && x 18)) || (((x 3 || x 7) || (x 8 || x 10)) && x 19)) || (((x 2 || x 6) || (x 7 || x 9)) && x 20)) || (((x 0 || x 4) || (x 5 || x 7)) && x 22)) || (((x 3 || x 4) || (x 6 || x 12)) && x 23)) || (((x 2 || x 3) || (x 5 || x 11)) && x 24)) || (((x 1 || x 2) || (x 4 || x 10)) && x 25)) := by
  have init : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25] := rfl
  rw [init]
  change (((((((((((x 0 || x 1) || ((x 3 || (x 9 || false)) || false)) && (x 13 && true)) || ((((x 5 || (x 9 || false)) || ((x 10 || (x 12 || false)) || false)) && (x 17 && true)) || false)) || ((((x 4 || (x 8 || false)) || ((x 9 || (x 11 || false)) || false)) && (x 18 && true)) || false)) || ((((x 3 || (x 7 || false)) || ((x 8 || (x 10 || false)) || false)) && (x 19 && true)) || false)) || ((((x 2 || (x 6 || false)) || ((x 7 || (x 9 || false)) || false)) && (x 20 && true)) || false)) || ((((x 0 || (x 4 || false)) || ((x 5 || (x 7 || false)) || false)) && (x 22 && true)) || false)) || ((((x 3 || (x 4 || false)) || ((x 6 || (x 12 || false)) || false)) && (x 23 && true)) || false)) || ((((x 2 || (x 3 || false)) || ((x 5 || (x 11 || false)) || false)) && (x 24 && true)) || false)) || ((((x 1 || (x 2 || false)) || ((x 4 || (x 10 || false)) || false)) && (x 25 && true)) || false)) = _
  simp only [Bool.or_false,Bool.and_true]
end Prefix2567
