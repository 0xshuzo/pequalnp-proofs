import PEqualNP.Defs
namespace Research9755.MixedMinor
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def h (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def eraser (side : Bool) : Fin 10 → Option (Fin 9) :=
  if side then ![some 4,none,some 7,some 5,some 0,some 3,some 6,some 2,some 8,some 1]
  else ![none,some 4,some 0,some 1,some 6,some 7,some 3,some 5,some 2,some 8]
def pull (s : Bool) (x : Fin 9 → Bool) (j : Fin 10) := (eraser s j).elim false x

def net : Circuit := ⟨[⟨.or,[6,2]⟩,
⟨.or,[9,0]⟩,
⟨.and,[1,10]⟩,
⟨.or,[7,3]⟩,
⟨.and,[2,12]⟩,
⟨.or,[3,0]⟩,
⟨.and,[4,14]⟩,
⟨.or,[7,0]⟩,
⟨.and,[5,16]⟩,
⟨.or,[6,5]⟩,
⟨.or,[18,3]⟩,
⟨.or,[17,8]⟩,
⟨.and,[20,19]⟩,
⟨.or,[21,15]⟩,
⟨.or,[22,13]⟩,
⟨.or,[23,11]⟩],24⟩

theorem fits : FanInTwo net := by
  intro g hg
  simp only [net,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def mixed (x : Fin 9 → Bool) := x 8 || (x 5 && (x 0 || x 7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem trace_table : ∀ s (x : Fin 9 → Bool),
    net.eval (List.ofFn x) = target (pull s x) ∧
    (net.wires (List.ofFn x)).getD 20 false = mixed x := by decide +kernel

-- A singleton and an incomparable pair both set the same interior gate.
def point (i : Fin 9) (j : Fin 9) := decide (j=i)
def couple (i k : Fin 9) (j : Fin 9) := decide (j=i ∨ j=k)
theorem two_term_sizes :
    mixed (point 8) = true ∧ mixed (point 0) = false ∧ mixed (point 5) = false ∧
    mixed (couple 0 5) = true ∧ mixed (fun _ => false) = false := by decide

theorem physical_control (side : Bool) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = 16 ∧
       (∀ x, C.eval (List.ofFn x) = target (pull side x)) ∧
       (∀ x, (C.wires (List.ofFn x)).getD 20 false = mixed x) :=
  ⟨net,fits,rfl,fun x => (trace_table side x).1,fun x => (trace_table side x).2⟩
end Research9755.MixedMinor
