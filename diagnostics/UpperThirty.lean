import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18910.Boundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev P := Fin 17
def E (p q : P) := ([33216,36352,61440,70208,74880,84224] : List Nat).getD p.val 0 |>.testBit q.val
def V (c : Circuit) (k : Nat) (x : P → Bool) := (c.wires (List.ofFn x)).getD k false
def c : Circuit := ⟨[⟨.or,[6,7]⟩,⟨.or,[17,8]⟩,⟨.or,[18,15]⟩,⟨.and,[0,19]⟩,⟨.or,[9,10]⟩,⟨.or,[21,11]⟩,⟨.or,[22,15]⟩,⟨.and,[1,23]⟩,⟨.or,[12,13]⟩,⟨.or,[25,14]⟩,⟨.or,[26,15]⟩,⟨.and,[2,27]⟩,⟨.or,[6,9]⟩,⟨.or,[29,12]⟩,⟨.or,[30,16]⟩,⟨.and,[3,31]⟩,⟨.or,[7,10]⟩,⟨.or,[33,13]⟩,⟨.or,[34,16]⟩,⟨.and,[4,35]⟩,⟨.or,[8,11]⟩,⟨.or,[37,14]⟩,⟨.or,[38,16]⟩,⟨.and,[5,39]⟩,⟨.or,[20,24]⟩,⟨.or,[41,28]⟩,⟨.or,[42,32]⟩,⟨.or,[43,36]⟩,⟨.or,[44,40]⟩,⟨.or,[15,16]⟩],45⟩
theorem legal : Monotone2 c := by decide +kernel
theorem edges : ∀ p q : P, E p q=true → c.eval (List.ofFn fun i => decide (i=p ∨ i=q))=true := by decide +kernel
theorem scalar (x : P → Bool) : V c 45 x = ((((((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) || (x 3 && (((x 6 || x 9) || x 12) || x 16))) || (x 4 && (((x 7 || x 10) || x 13) || x 16))) || (x 5 && (((x 8 || x 11) || x 14) || x 16))) := by
  change GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [GateOp.eval .and [x 0, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 6, x 7], x 8], x 15]], GateOp.eval .and [x 1, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 9, x 10], x 11], x 15]]], GateOp.eval .and [x 2, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 12, x 13], x 14], x 15]]], GateOp.eval .and [x 3, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 6, x 9], x 12], x 16]]], GateOp.eval .and [x 4, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 7, x 10], x 13], x 16]]], GateOp.eval .and [x 5, GateOp.eval .or [GateOp.eval .or [GateOp.eval .or [x 8, x 11], x 14], x 16]]] = _
  simp [GateOp.eval]
theorem mark (x : P → Bool) : V c 46 x = (x 15 || x 16) := by
  change GateOp.eval .or [x 15, x 16] = _
  simp [GateOp.eval]
theorem safe (x : P → Bool) (h : ∀ p q : P, E p q=true → x p=true → x q=false) : V c 45 x=false := by
  rw [scalar]
  have f0 : (x 0 && (((x 6 || x 7) || x 8) || x 15))=false := by
    cases b : x 0 with
    | false => simp
    | true => simp [h 0 6 (by decide) b,h 0 7 (by decide) b,h 0 8 (by decide) b,h 0 15 (by decide) b]
  have f1 : (x 1 && (((x 9 || x 10) || x 11) || x 15))=false := by
    cases b : x 1 with
    | false => simp
    | true => simp [h 1 9 (by decide) b,h 1 10 (by decide) b,h 1 11 (by decide) b,h 1 15 (by decide) b]
  have f2 : (x 2 && (((x 12 || x 13) || x 14) || x 15))=false := by
    cases b : x 2 with
    | false => simp
    | true => simp [h 2 12 (by decide) b,h 2 13 (by decide) b,h 2 14 (by decide) b,h 2 15 (by decide) b]
  have f3 : (x 3 && (((x 6 || x 9) || x 12) || x 16))=false := by
    cases b : x 3 with
    | false => simp
    | true => simp [h 3 6 (by decide) b,h 3 9 (by decide) b,h 3 12 (by decide) b,h 3 16 (by decide) b]
  have f4 : (x 4 && (((x 7 || x 10) || x 13) || x 16))=false := by
    cases b : x 4 with
    | false => simp
    | true => simp [h 4 7 (by decide) b,h 4 10 (by decide) b,h 4 13 (by decide) b,h 4 16 (by decide) b]
  have f5 : (x 5 && (((x 8 || x 11) || x 14) || x 16))=false := by
    cases b : x 5 with
    | false => simp
    | true => simp [h 5 8 (by decide) b,h 5 11 (by decide) b,h 5 14 (by decide) b,h 5 16 (by decide) b]
  simp only [f0,f1,f2,f3,f4,f5,Bool.false_or]
theorem boundary : (have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (30 : ℕ) ∧       x2.output < (17 : ℕ) + x2.size ∧         x3 < (17 : ℕ) + x2.size ∧           (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧             (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧               ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),                 (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →                   have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;                   ∀ (x8 : Fin (17 : ℕ) → Bool), (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) → (x2.wires (List.ofFn x8)).getD (if x4 = Bool.true then x3 else x2.output) Bool.false = Bool.false) := by
  refine ⟨c,46,legal,by decide,by decide,by decide,edges,?_,?_⟩
  · intro p hp
    have hh : p=(15 : P) ∨ p=(16 : P) := by simpa using hp
    rcases hh with rfl|rfl <;> decide +kernel
  · intro b S _ x hx
    let L (i : P) := (b=false ∨ i.val<15) ∧ ∀ p∈S, E p i=false
    have h (i : P) : x i=true ↔ if i.val<6 then ∀ j, E i j=true → ¬ L j else L i := hx i
    cases hb : b with
    | false =>
      change V c 45 x=false
      apply safe
      intro p q he hp
      have side : ∀ u v : P, E u v=true → u.val<6 ∧ 6≤v.val := by decide +kernel
      obtain ⟨a,d⟩ := side _ _ he
      have live := (h p).mp hp
      rw [if_pos a] at live
      apply Bool.eq_false_iff.mpr
      intro hq
      have off := (h q).mp hq
      rw [if_neg (Nat.not_lt.mpr d)] at off
      exact live q he off
    | true =>
      change V c 46 x=false
      rw [mark]
      have ff (i : P) (hi : 15≤i.val) : x i=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        have m := (h i).mp yes
        rw [if_neg (by omega)] at m
        rcases m.1 with no|bad
        · simp [hb] at no
        · omega
      simp [ff 15 (by decide),ff 16 (by decide)]

end PEqualNP.Outside.L_meta_18910.Boundary
