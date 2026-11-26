import PEqualNP.Defs

namespace L9765Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def C : Circuit := ⟨[
  ⟨.or,[1,2]⟩,
  ⟨.or,[41,5]⟩,
  ⟨.or,[42,15]⟩,
  ⟨.or,[43,17]⟩,
  ⟨.and,[44,21]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[46,6]⟩,
  ⟨.or,[47,16]⟩,
  ⟨.or,[48,18]⟩,
  ⟨.and,[49,22]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[51,7]⟩,
  ⟨.or,[52,17]⟩,
  ⟨.or,[53,19]⟩,
  ⟨.and,[54,23]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[56,8]⟩,
  ⟨.or,[57,18]⟩,
  ⟨.or,[58,20]⟩,
  ⟨.and,[59,24]⟩,
  ⟨.or,[0,5]⟩,
  ⟨.or,[61,6]⟩,
  ⟨.or,[62,9]⟩,
  ⟨.or,[63,19]⟩,
  ⟨.and,[64,25]⟩,
  ⟨.or,[1,6]⟩,
  ⟨.or,[66,7]⟩,
  ⟨.or,[67,10]⟩,
  ⟨.or,[68,20]⟩,
  ⟨.and,[69,26]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.or,[71,7]⟩,
  ⟨.or,[72,8]⟩,
  ⟨.or,[73,11]⟩,
  ⟨.and,[74,27]⟩,
  ⟨.or,[1,3]⟩,
  ⟨.or,[76,8]⟩,
  ⟨.or,[77,9]⟩,
  ⟨.or,[78,12]⟩,
  ⟨.and,[79,28]⟩,
  ⟨.or,[2,4]⟩,
  ⟨.or,[81,9]⟩,
  ⟨.or,[82,10]⟩,
  ⟨.or,[83,13]⟩,
  ⟨.and,[84,29]⟩,
  ⟨.or,[3,5]⟩,
  ⟨.or,[86,10]⟩,
  ⟨.or,[87,11]⟩,
  ⟨.or,[88,14]⟩,
  ⟨.and,[89,30]⟩,
  ⟨.or,[4,6]⟩,
  ⟨.or,[91,11]⟩,
  ⟨.or,[92,12]⟩,
  ⟨.or,[93,15]⟩,
  ⟨.and,[94,31]⟩,
  ⟨.or,[5,7]⟩,
  ⟨.or,[96,12]⟩,
  ⟨.or,[97,13]⟩,
  ⟨.or,[98,16]⟩,
  ⟨.and,[99,32]⟩,
  ⟨.or,[6,8]⟩,
  ⟨.or,[101,13]⟩,
  ⟨.or,[102,14]⟩,
  ⟨.or,[103,17]⟩,
  ⟨.and,[104,33]⟩,
  ⟨.or,[7,9]⟩,
  ⟨.or,[106,14]⟩,
  ⟨.or,[107,15]⟩,
  ⟨.or,[108,18]⟩,
  ⟨.and,[109,34]⟩,
  ⟨.or,[8,10]⟩,
  ⟨.or,[111,15]⟩,
  ⟨.or,[112,16]⟩,
  ⟨.or,[113,19]⟩,
  ⟨.and,[114,35]⟩,
  ⟨.or,[9,11]⟩,
  ⟨.or,[116,16]⟩,
  ⟨.or,[117,17]⟩,
  ⟨.or,[118,20]⟩,
  ⟨.and,[119,36]⟩,
  ⟨.or,[0,10]⟩,
  ⟨.or,[121,12]⟩,
  ⟨.or,[122,17]⟩,
  ⟨.or,[123,18]⟩,
  ⟨.and,[124,37]⟩,
  ⟨.or,[1,11]⟩,
  ⟨.or,[126,13]⟩,
  ⟨.or,[127,18]⟩,
  ⟨.or,[128,19]⟩,
  ⟨.and,[129,38]⟩,
  ⟨.or,[2,12]⟩,
  ⟨.or,[131,14]⟩,
  ⟨.or,[132,19]⟩,
  ⟨.or,[133,20]⟩,
  ⟨.and,[134,39]⟩,
  ⟨.or,[0,3]⟩,
  ⟨.or,[136,13]⟩,
  ⟨.or,[137,15]⟩,
  ⟨.or,[138,20]⟩,
  ⟨.and,[139,40]⟩,
  ⟨.or,[45,50]⟩,
  ⟨.or,[141,55]⟩,
  ⟨.or,[142,60]⟩,
  ⟨.or,[143,65]⟩,
  ⟨.or,[144,70]⟩,
  ⟨.or,[145,75]⟩,
  ⟨.or,[146,80]⟩,
  ⟨.or,[147,85]⟩,
  ⟨.or,[148,90]⟩,
  ⟨.or,[149,95]⟩,
  ⟨.or,[150,100]⟩,
  ⟨.or,[151,105]⟩,
  ⟨.or,[152,110]⟩,
  ⟨.or,[153,115]⟩,
  ⟨.or,[154,120]⟩,
  ⟨.or,[155,125]⟩,
  ⟨.or,[156,130]⟩,
  ⟨.or,[157,135]⟩,
  ⟨.or,[158,140]⟩],159⟩

def legal (g : Gate) : Bool :=
  decide (g.op = .and ∨ g.op = .or ∨ g.op = .not) && decide (g.inputs.length ≤ 2)

theorem fanin : FanInTwo C := by
  have hall : C.gates.all legal = true := by decide +kernel
  intro g hg
  have h := (List.all_eq_true.1 hall) g hg
  simpa only [legal, Bool.and_eq_true, decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem size_eq : C.size = 119 := by decide +kernel

theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 41 (fun x : Fin 41 → Bool => (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 0 && x 40) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 3 && x 40) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 13 && x 40) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 15 && x 40) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39) || (x 20 && x 24) || (x 20 && x 26) || (x 20 && x 36) || (x 20 && x 39) || (x 20 && x 40)) 119 := by
  refine ⟨C, fanin, by rw [size_eq], fun x => ?_⟩
  change ((((((((((((((((((((((((x 1 || (x 2 || false)) || (x 5 || false)) || (x 15 || false)) || (x 17 || false)) && (x 21 && true)) || ((((((x 2 || (x 3 || false)) || (x 6 || false)) || (x 16 || false)) || (x 18 || false)) && (x 22 && true)) || false)) || ((((((x 3 || (x 4 || false)) || (x 7 || false)) || (x 17 || false)) || (x 19 || false)) && (x 23 && true)) || false)) || ((((((x 4 || (x 5 || false)) || (x 8 || false)) || (x 18 || false)) || (x 20 || false)) && (x 24 && true)) || false)) || ((((((x 0 || (x 5 || false)) || (x 6 || false)) || (x 9 || false)) || (x 19 || false)) && (x 25 && true)) || false)) || ((((((x 1 || (x 6 || false)) || (x 7 || false)) || (x 10 || false)) || (x 20 || false)) && (x 26 && true)) || false)) || ((((((x 0 || (x 2 || false)) || (x 7 || false)) || (x 8 || false)) || (x 11 || false)) && (x 27 && true)) || false)) || ((((((x 1 || (x 3 || false)) || (x 8 || false)) || (x 9 || false)) || (x 12 || false)) && (x 28 && true)) || false)) || ((((((x 2 || (x 4 || false)) || (x 9 || false)) || (x 10 || false)) || (x 13 || false)) && (x 29 && true)) || false)) || ((((((x 3 || (x 5 || false)) || (x 10 || false)) || (x 11 || false)) || (x 14 || false)) && (x 30 && true)) || false)) || ((((((x 4 || (x 6 || false)) || (x 11 || false)) || (x 12 || false)) || (x 15 || false)) && (x 31 && true)) || false)) || ((((((x 5 || (x 7 || false)) || (x 12 || false)) || (x 13 || false)) || (x 16 || false)) && (x 32 && true)) || false)) || ((((((x 6 || (x 8 || false)) || (x 13 || false)) || (x 14 || false)) || (x 17 || false)) && (x 33 && true)) || false)) || ((((((x 7 || (x 9 || false)) || (x 14 || false)) || (x 15 || false)) || (x 18 || false)) && (x 34 && true)) || false)) || ((((((x 8 || (x 10 || false)) || (x 15 || false)) || (x 16 || false)) || (x 19 || false)) && (x 35 && true)) || false)) || ((((((x 9 || (x 11 || false)) || (x 16 || false)) || (x 17 || false)) || (x 20 || false)) && (x 36 && true)) || false)) || ((((((x 0 || (x 10 || false)) || (x 12 || false)) || (x 17 || false)) || (x 18 || false)) && (x 37 && true)) || false)) || ((((((x 1 || (x 11 || false)) || (x 13 || false)) || (x 18 || false)) || (x 19 || false)) && (x 38 && true)) || false)) || ((((((x 2 || (x 12 || false)) || (x 14 || false)) || (x 19 || false)) || (x 20 || false)) && (x 39 && true)) || false)) || ((((((x 0 || (x 3 || false)) || (x 13 || false)) || (x 15 || false)) || (x 20 || false)) && (x 40 && true)) || false)) = _
  simp only [Bool.or_false, Bool.and_true, Bool.and_or_distrib_right]
  ac_rfl

end L9765Upper
