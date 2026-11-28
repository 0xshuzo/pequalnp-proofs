import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17721
open PEqualNP.CircuitLowerBounds
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]
theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]
theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true
theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht
def allowed (C : Circuit) := ∀ g∈C.gates, g.op=GateOp.and ∨ g.op=GateOp.or
def zeroGate : Gate := ⟨.or,[]⟩
def oneGate : Gate := ⟨.and,[]⟩
theorem zeros (k : Nat) (a : List Bool) : W (List.replicate k zeroGate) a = a++List.replicate k false := by
  induction k generalizing a with
  | zero => simp [W]
  | succ k ih =>
    rw [List.replicate_succ]
    change W (List.replicate k zeroGate) (a++[false])=_
    rw [ih,List.append_assoc]
    rfl
def test (x y : List Bool) : Circuit := ⟨List.replicate y.length zeroGate ++ [oneGate], x.length+y.length⟩
theorem legal (x y) : allowed (test x y) := by
  intro g hg
  change g∈List.replicate y.length zeroGate ++ [oneGate] at hg
  rcases List.mem_append.mp hg with hl|hr
  · have eq : g=zeroGate := (List.mem_replicate.mp hl).2
    exact .inr (eq ▸ rfl)
  · obtain rfl : g=oneGate := List.mem_singleton.mp hr
    exact .inl rfl
theorem test_eval (x y a : List Bool) (enough : a.length≤x.length+y.length) :
    (test x y).eval a=decide (a.length=x.length) := by
  change (W (List.replicate y.length zeroGate++[oneGate]) a).getD (x.length+y.length) false=_
  rw [W_snoc,zeros]
  change ((a++List.replicate y.length false)++[true]).getD _ false=_
  rw [getD_snoc]
  simp only [List.length_append,List.length_replicate]
  by_cases eq : a.length=x.length
  · simp [eq]
  · rw [if_neg (by omega : ¬x.length+y.length=a.length+y.length)] <;> try assumption
    rw [decide_eq_false eq]
    split
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right enough,List.getElem?_replicate]
      split <;> rfl
    · rfl

theorem exact_order (x y : List Bool) :
    (∀ C : Circuit, allowed C → C.eval x=true → C.eval y=true) ↔ x.length=y.length ∧ Le x y := by
  constructor
  · intro all
    have h := all (test x y) (legal x y)
    rw [test_eval x y x (by omega),test_eval x y y (by omega)] at h
    have eq : y.length=x.length := of_decide_eq_true (h (by simp))
    refine ⟨eq.symm,?_⟩
    intro i hi
    exact all ⟨[],i⟩ (by intro g hg;cases hg) hi
  · rintro ⟨len,le⟩ C hm
    exact W_mono C.gates hm x y len le C.output
end PEqualNP.Outside.L_meta_17721
