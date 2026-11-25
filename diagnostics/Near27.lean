import Mathlib
import PEqualNP.Outside.L_meta_3008
import PEqualNP.Outside.L_meta_3537
namespace Near2733
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev edges := PEqualNP.Outside.L_meta_3008_aux.edges
abbrev vec := PEqualNP.Outside.L_meta_3008_aux.nums
def target (x : Fin 14 → Bool) := decide (∃ a b : Fin 14, (a.val,b.val)∈edges ∧ x a=true ∧ x b=true)
def tail : Circuit := ⟨[⟨.and,[7,15]⟩,⟨.or,[0,2]⟩,⟨.or,[6,17]⟩,⟨.and,[8,18]⟩,⟨.or,[1,5]⟩,⟨.or,[6,20]⟩,⟨.and,[9,21]⟩,⟨.or,[0,4]⟩,⟨.or,[5,23]⟩,⟨.and,[10,24]⟩,⟨.or,[3,4]⟩,⟨.or,[6,26]⟩,⟨.and,[11,27]⟩,⟨.or,[2,3]⟩,⟨.or,[5,29]⟩,⟨.and,[12,30]⟩,⟨.or,[1,2]⟩,⟨.or,[4,32]⟩,⟨.and,[13,33]⟩,⟨.or,[16,19]⟩,⟨.or,[35,22]⟩,⟨.or,[36,25]⟩,⟨.or,[37,28]⟩,⟨.or,[38,31]⟩,⟨.or,[39,34]⟩],40⟩
def whole : Circuit := ⟨⟨.or,[0,1]⟩ :: ⟨.or,[3,14]⟩ :: tail.gates,tail.output⟩

private theorem monoTail : Monotone2 tail := by
  intro g hg
  simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,le_rfl⟩ | exact ⟨Or.inr rfl,le_rfl⟩
private theorem monoWhole : Monotone2 whole := by
  intro g hg
  change g∈_ :: _ :: tail.gates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨Or.inr rfl,le_rfl⟩
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨Or.inr rfl,le_rfl⟩
  exact monoTail _ hg
theorem correct (x : Fin 14 → Bool) : whole.eval (List.ofFn x)=target x := by
  apply Bool.eq_iff_iff.mpr
  change (whole.eval (List.ofFn x)=true ↔ decide _=true)
  rw [decide_eq_true_eq]
  apply PEqualNP.Outside.L_meta_3008 whole monoWhole _ x
  intro n
  change whole.eval (vec.map (·.testBit n))=(2097151:Nat).testBit n
  by_cases lt : n<58
  · have chk : ∀ i : Fin 58, whole.eval (vec.map (·.testBit i.val))=(2097151:Nat).testBit i.val := by decide +kernel
    exact chk ⟨n,lt⟩
  · have hi : 2^58 ≤ (2^n : Nat) := Nat.pow_le_pow_right (by decide) (by omega)
    have sm : ∀ w∈vec, w<2^58 := by decide
    have eq : vec.map (·.testBit n) = vec.map (fun _ => false) :=
      List.map_congr_left fun w hw => Nat.testBit_lt_two_pow ((sm w hw).trans_le hi)
    rw [eq,Nat.testBit_lt_two_pow ((show (2097151:Nat)<2^58 by decide).trans_le hi)]
    decide
theorem actualPrefix : (have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (25 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12) := by
  dsimp only
  refine ⟨0,1,3,14,.or,.or,tail,by decide,by decide,Or.inr rfl,Or.inr rfl,?_,monoTail,by decide,?_⟩
  · let F := PEqualNP.Outside.L_meta_3537.heawood
    have pairs : ∀ a b : Fin 14, ((a.val,b.val)∈edges) ↔
      (PEqualNP.Outside.L_meta_3537.rows.getD a.val 0).testBit b.val=true := by decide
    have same (x : Fin 14 → Bool) : target x=F x := by
      simp only [target,F,PEqualNP.Outside.L_meta_3537.heawood,pairs]
    intro σ auto
    have hσ : ∀ x,F (x ∘ σ)=F x := fun x => (same _).symm.trans ((auto x).trans (same x))
    simpa only [Nat.add_assoc] using (PEqualNP.Outside.L_meta_3537 (20 : Fin 65)).2.2 σ hσ
  · intro x
    have raw (i : Fin 14) : (List.ofFn x).getD i.val false=x i := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact i.isLt),List.getElem_ofFn]
    have zero : (List.ofFn x).getD 0 false=x 0 := raw 0
    have one : (List.ofFn x).getD 1 false=x 1 := raw 1
    have h := correct x
    change (whole.eval (List.ofFn x))=target x at h
    simp only [whole,Circuit.eval,Circuit.wires,List.foldl_cons,List.map_cons,List.map_nil,zero,one] at h
    exact h
end Near2733
