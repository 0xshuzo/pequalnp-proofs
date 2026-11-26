import PEqualNP.Outside.L_meta_17581
import PEqualNP.Outside.L_meta_18007

namespace PetersenMonotoneHint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17581
open SeedCompress Petersen7217
open PEqualNP.Outside.L_meta_18007.Monotonicity

abbrev Point := V → Bool
def frame (x : Point) (b : Bool) := List.ofFn x ++ [b]

private theorem oneRel {a b : Bool} (h : a ≤ b) : R [a] [b] := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i with
  | zero => exact h
  | succ i =>
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)] <;> exact le_refl _

private theorem smaller (C : Circuit) (hm : Monotone2 C) {x y : Point} {a b : Bool}
    (xy : ∀ i, x i ≤ y i) (ab : a ≤ b) :
    C.eval (frame x a) ≤ C.eval (frame y b) :=
  eval_mono C hm _ _ (R_append (R_ofFn x y xy) (oneRel ab))

private def ends (e : ℕ) (i : V) :=
  decide (i = Fin.ofNat 10 (e/10) ∨ i = Fin.ofNat 10 (e%10))

private theorem edgeFacts : ∀ i : Fin nums.length,
    pet (ends (nums.get i)) = true ∧
      (ends (nums.get i) 0 && ends (nums.get i) 2) = false := by
  decide +kernel

/-- Every minimal positive assignment is an edge, so the free product
can be fixed to false throughout a monotone circuit for Petersen. -/
theorem remove_product (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Point, C.eval (frame x (x 0 && x 2)) = pet x) :
    ∀ x : Point, C.eval (frame x false) = pet x := by
  intro x
  cases hp : pet x with
  | false =>
    have order := smaller C hm (x:=x) (y:=x) (a:=false) (b:=x 0 && x 2)
      (fun _ => le_refl _) (Bool.false_le _)
    rw [hc,hp] at order
    exact le_antisymm order (Bool.false_le _)
  | true =>
    obtain ⟨e,he,hon⟩ := List.any_eq_true.mp hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    obtain ⟨hy,hz⟩ := edgeFacts i
    have hxy : ∀ k, ends (nums.get i) k ≤ x k := by
      intro k
      obtain ⟨ha,hb⟩ := Bool.and_eq_true.mp hon
      unfold ends
      by_cases h : k = Fin.ofNat 10 (nums.get i/10) ∨ k = Fin.ofNat 10 (nums.get i%10)
      · rcases h with rfl | rfl <;> simp [ha,hb]
      · simp [h]
    have low := hc (ends (nums.get i))
    rw [hz,hy] at low
    have order := smaller C hm (a:=false) (b:=false) hxy (le_refl _)
    rw [low] at order
    exact Bool.eq_true_of_true_le order

private def bank : List Stat := List.ofFn (fun i : V => (.inr i.val : Stat)) ++ [.inl false]

/-- An effective read of the free hint in a monotone circuit forces its
size to be at least nineteen. -/
theorem charged_hint (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Point, C.eval (frame x (x 0 && x 2)) = pet x)
    (read : ∃ j : Fin C.gates.length, 10 ∈ (normGate (C.gates.get j)).inputs) :
    19 ≤ C.size := by
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨op,sz⟩ := hm g hg
    exact ⟨by rcases op with ha|hb; exact Or.inl ha; exact Or.inr (Or.inl hb),sz⟩
  have good := remove_product C hm hc
  have valid : ∀ s ∈ bank, s.Valid 10 := by
    intro s hs
    simp only [bank,List.mem_append,List.mem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with ⟨i,rfl⟩ | rfl
    · exact i.isLt
    · trivial
  have layout (x : Point) : row bank [] x = frame x false := by
    simp only [bank,row,frame,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
      Stat.val,wiresFrom,List.foldl_nil]
    congr 1
  have fits (x) := (congrArg C.eval (layout x)).trans (good x)
  obtain ⟨D,hD,sz,ev⟩ := compile_bank bank [] C fan (by simp) valid
    ⟨fun _ => false,(fits _).trans (by decide : pet (fun _ => false)=false)⟩
  have lo := plain18 nine_bound D hD (fun x => (ev x).trans (fits x))
  obtain ⟨j,hj⟩ := read
  have contact : hits bank (C.gates.get j) = true := by
    apply List.any_eq_true.mpr
    exact ⟨10,hj,by simp [bank,List.getD_append_right,constant]⟩
  have pay : 0 < count bank C := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,contact⟩⟩
  simp only [List.length_nil,Nat.add_zero] at sz
  omega

end PetersenMonotoneHint
