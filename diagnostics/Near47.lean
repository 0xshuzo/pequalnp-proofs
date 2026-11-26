import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9809.Near
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
deriving instance DecidableEq for GateOp
set_option maxHeartbeats 0
set_option maxRecDepth 16000
def legal (g : Gate) : Bool :=
  decide (g.op = .and ∨ g.op = .or ∨ g.op = .not) && decide (g.inputs.length ≤ 2)

def target (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def reduced (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def full : Circuit := ⟨[⟨.or,[11,8]⟩,⟨.or,[9,14]⟩,⟨.and,[6,15]⟩,⟨.or,[12,10]⟩,⟨.or,[17,9]⟩,⟨.and,[5,18]⟩,⟨.or,[13,11]⟩,⟨.or,[20,10]⟩,⟨.and,[4,21]⟩,⟨.or,[11,7]⟩,⟨.or,[23,12]⟩,⟨.and,[3,24]⟩,⟨.or,[7,13]⟩,⟨.and,[1,26]⟩,⟨.or,[12,13]⟩,⟨.or,[8,28]⟩,⟨.and,[2,29]⟩,⟨.or,[10,8]⟩,⟨.and,[0,31]⟩,⟨.or,[19,25]⟩,⟨.or,[16,30]⟩,⟨.or,[27,32]⟩,⟨.or,[33,35]⟩,⟨.or,[36,34]⟩,⟨.or,[37,22]⟩],38⟩
theorem legal_full : FanInTwo full := by
  have hall : full.gates.all legal = true := by decide +kernel
  intro g hg
  have h := (List.all_eq_true.1 hall) g hg
  simpa only [legal, Bool.and_eq_true, decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using h


theorem correctness_full (x : Fin 14 → Bool) : full.eval (List.ofFn x)=target x := by
  change (((((x 5 && (((x 12 || (x 10 || false)) || (x 9 || false)) && true)) || ((x 3 && (((x 11 || (x 7 || false)) || (x 12 || false)) && true)) || false)) || (((x 1 && ((x 7 || (x 13 || false)) && true)) || ((x 0 && ((x 10 || (x 8 || false)) && true)) || false)) || false)) || (((x 6 && ((x 9 || ((x 11 || (x 8 || false)) || false)) && true)) || ((x 2 && ((x 8 || ((x 12 || (x 13 || false)) || false)) && true)) || false)) || false)) || ((x 4 && (((x 13 || (x 11 || false)) || (x 10 || false)) && true)) || false)) = _
  simp only [target,Bool.and_true,Bool.or_false]
  bv_decide
theorem size_full : full.size=25 := by decide +kernel
def close : Circuit := ⟨[⟨.or,[7,13]⟩,⟨.and,[1,14]⟩,⟨.or,[10,8]⟩,⟨.and,[0,16]⟩,⟨.or,[10,11]⟩,⟨.or,[13,18]⟩,⟨.and,[4,19]⟩,⟨.or,[9,12]⟩,⟨.and,[5,21]⟩,⟨.or,[8,12]⟩,⟨.or,[23,13]⟩,⟨.and,[2,24]⟩,⟨.or,[9,11]⟩,⟨.or,[26,8]⟩,⟨.and,[6,27]⟩,⟨.or,[7,11]⟩,⟨.or,[29,12]⟩,⟨.and,[3,30]⟩,⟨.or,[22,15]⟩,⟨.or,[20,32]⟩,⟨.or,[31,28]⟩,⟨.or,[25,17]⟩,⟨.or,[34,35]⟩,⟨.or,[36,33]⟩],37⟩
theorem legal_close : FanInTwo close := by
  have hall : close.gates.all legal = true := by decide +kernel
  intro g hg
  have h := (List.all_eq_true.1 hall) g hg
  simpa only [legal, Bool.and_eq_true, decide_eq_true_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using h


theorem correctness_close (x : Fin 14 → Bool) : close.eval (List.ofFn x)=reduced x := by
  change ((((x 3 && (((x 7 || (x 11 || false)) || (x 12 || false)) && true)) || ((x 6 && (((x 9 || (x 11 || false)) || (x 8 || false)) && true)) || false)) || (((x 2 && (((x 8 || (x 12 || false)) || (x 13 || false)) && true)) || ((x 0 && ((x 10 || (x 8 || false)) && true)) || false)) || false)) || (((x 4 && ((x 13 || ((x 10 || (x 11 || false)) || false)) && true)) || (((x 5 && ((x 9 || (x 12 || false)) && true)) || ((x 1 && ((x 7 || (x 13 || false)) && true)) || false)) || false)) || false)) = _
  simp only [reduced,Bool.and_true,Bool.or_false]
  bv_decide
theorem size_close : close.size=24 := by decide +kernel

theorem upper25 : HasCircuitSize 14 target 25 :=
  ⟨full,legal_full,by decide +kernel,correctness_full⟩
theorem missed (x : Fin 14 → Bool) : (target x && !(close.eval (List.ofFn x))) =
    ((x 5 && x 10) && !(reduced x)) := by
  rw [correctness_close]
  unfold target reduced
  bv_decide
def bad (m : Nat) : Bool :=
  (m.testBit 5 && m.testBit 10) && !(reduced (fun i => m.testBit i.val))
def page (n : Nat) := ((List.range 64).filter (fun k => bad (64*n+k))).length
def p0 : Nat := ((List.range 16).map (fun j => page (0+j))).sum
theorem h0 : p0=0 := by decide +kernel
def p1 : Nat := ((List.range 16).map (fun j => page (16+j))).sum
theorem h1 : p1=25 := by decide +kernel
def p2 : Nat := ((List.range 16).map (fun j => page (32+j))).sum
theorem h2 : p2=0 := by decide +kernel
def p3 : Nat := ((List.range 16).map (fun j => page (48+j))).sum
theorem h3 : p3=9 := by decide +kernel
def p4 : Nat := ((List.range 16).map (fun j => page (64+j))).sum
theorem h4 : p4=0 := by decide +kernel
def p5 : Nat := ((List.range 16).map (fun j => page (80+j))).sum
theorem h5 : p5=0 := by decide +kernel
def p6 : Nat := ((List.range 16).map (fun j => page (96+j))).sum
theorem h6 : p6=0 := by decide +kernel
def p7 : Nat := ((List.range 16).map (fun j => page (112+j))).sum
theorem h7 : p7=0 := by decide +kernel
def p8 : Nat := ((List.range 16).map (fun j => page (128+j))).sum
theorem h8 : p8=0 := by decide +kernel
def p9 : Nat := ((List.range 16).map (fun j => page (144+j))).sum
theorem h9 : p9=9 := by decide +kernel
def p10 : Nat := ((List.range 16).map (fun j => page (160+j))).sum
theorem h10 : p10=0 := by decide +kernel
def p11 : Nat := ((List.range 16).map (fun j => page (176+j))).sum
theorem h11 : p11=4 := by decide +kernel
def p12 : Nat := ((List.range 16).map (fun j => page (192+j))).sum
theorem h12 : p12=0 := by decide +kernel
def p13 : Nat := ((List.range 16).map (fun j => page (208+j))).sum
theorem h13 : p13=0 := by decide +kernel
def p14 : Nat := ((List.range 16).map (fun j => page (224+j))).sum
theorem h14 : p14=0 := by decide +kernel
def p15 : Nat := ((List.range 16).map (fun j => page (240+j))).sum
theorem h15 : p15=0 := by decide +kernel
theorem fortySeven : p0+p1+p2+p3+p4+p5+p6+p7+p8+p9+p10+p11+p12+p13+p14+p15=47 := by
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15]
end PEqualNP.Outside.L_meta_9809.Near
