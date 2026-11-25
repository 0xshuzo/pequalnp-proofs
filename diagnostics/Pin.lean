import Mathlib
import PEqualNP.Outside.L_meta_3336
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3336
namespace Pin3338
abbrev pos (h : Gate) := h.op.eval [true]

lemma localPrice (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    (simplifyGate op m ins).1.toList.countP pos ≤ (if op.eval [true] then 1 else 0) := by
  have cap : (simplifyGate op m ins).1.toList.countP pos ≤ 1 :=
    List.countP_le_length.trans (toList_opt_len_le _)
  cases op with
  | and => exact cap
  | or => exact cap
  | not =>
    rcases ins with _ | ⟨a,as⟩
    · exact Nat.zero_le _
    · cases a <;> simp [simplifyGate,simpNot,pos,GateOp.eval]
  | mod n => simp [simplifyGate]
  | maj => exact cap

lemma costs (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass 8 gs acc).2.length ≤ acc.2.length + gs.length ∧
    (elimPass 8 gs acc).2.countP pos ≤ acc.2.countP pos + gs.countP pos := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    let q := simplifyGate g.op (8+acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))
    obtain ⟨len,price⟩ := ih (elimStep 8 acc g)
    change _ ≤ (acc.2 ++ q.1.toList).length + gs.length at len
    change _ ≤ (acc.2 ++ q.1.toList).countP pos + gs.countP pos at price
    rw [List.length_append] at len
    rw [List.countP_append] at price
    have cap := toList_opt_len_le q.1
    have cp : q.1.toList.countP pos ≤ (if pos g then 1 else 0) := localPrice _ _ _
    simp only [List.length_cons,List.countP_cons]
    constructor
    · omega
    · cases test : pos g <;> simp only [test,Bool.false_eq_true,if_false,if_true] at cp ⊢ <;> omega

set_option maxHeartbeats 1600000 in
theorem pin : let I (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b];
    let T (x : Fin 8 → Bool) := let n := tableIndex x; ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64);
    ∀ (p s : List Gate) (g : Gate) (o : ℕ), let C : Circuit := ⟨p ++ g::s,o⟩;
    FanInTwo C → g.op=GateOp.or → 6∈g.inputs → (∀ x, C.eval (I false x)=T x) →
    ∃ D : Circuit, FanInTwo D ∧ D.size≤p.length+s.length ∧
      D.gates.countP (fun h => h.op.eval [true]) ≤ (p++s).countP (fun h => h.op.eval [true]) ∧
      ∀ x, D.eval (List.ofFn x)=T x := by
  intro I T p s g o C fan op hit low
  let a := elimPass 8 p start
  let b := elimStep 8 a g
  let c := elimPass 8 s b
  have hp (h : Gate) (hh : h ∈ p) : OkGate h := fan h (List.mem_append_left _ hh)
  have hg : OkGate g := fan g (List.mem_append_right _ List.mem_cons_self)
  have hs (h : Gate) (hh : h ∈ s) : OkGate h :=
    fan h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  have fixed : a.1.getD 6 (.inl false) = .inl false := by
    rw [pass_old _ _ _ (by decide)]; rfl
  have skip : (simplifyGate g.op (8+a.2.length)
      (g.inputs.map fun i => a.1.getD i (.inl false))).1 = none := by
    apply simplifyGate_none_of_const _ _ _ hg.1
    · simpa using hg.2
    · intro bad; rw [op] at bad; contradiction
    · exact ⟨false,List.mem_map.mpr ⟨6,hit,fixed⟩⟩
  have saved : b.2=a.2 := by simp only [b,elimStep,skip,Option.toList_none,List.append_nil]
  have good : ∀h∈c.2, OkGate h := by
    apply elimPass_ok
    rw [saved]
    exact elimPass_ok _ _ _ (by simp [start])
  have ca := costs p start
  have cb := costs s b
  change a.2.length ≤ _ ∧ a.2.countP pos ≤ _ at ca
  change c.2.length ≤ _ ∧ c.2.countP pos ≤ _ at cb
  rw [saved] at cb
  simp [start] at ca
  have value (x : Fin 8 → Bool) :
      statVal (wiresFrom c.2 (List.ofFn x)) (c.1.getD o (.inl false)) = T x := by
    have ea := elimInv_pass 8 (List.ofFn x) p (inputs false x) start hp (start_sound x)
    have eb := elimInv_step 8 (List.ofFn x) (wiresFrom p (inputs false x)) a g hg ea
    have ec := elimInv_pass 8 (List.ofFn x) s _ b hs eb
    apply ((ec.2.2 o).2).trans
    have correct := low x
    change (wiresFrom (p ++ g :: s) (inputs false x)).getD o false = _ at correct
    rwa [wiresFrom_append,wiresFrom_cons] at correct
  cases wire : c.1.getD o (.inl false) with
  | inl u =>
    let edge (i : Fin 8) := decide (i=0 ∨ i=1)
    have off := value (fun _ => false)
    have on := value edge
    rw [wire] at off on
    have no : T (fun _ => false)=false := by decide
    have yes : T edge=true := by decide
    exact (Bool.false_ne_true (no.symm.trans (off.symm.trans (on.trans yes)))).elim
  | inr i =>
    refine ⟨⟨c.2,i⟩,good,?_,?_,?_⟩
    · change c.2.length ≤ _; omega
    · change c.2.countP pos ≤ (p++s).countP pos
      rw [List.countP_append]; omega
    · intro x
      have correct := value x
      rw [wire] at correct
      exact correct
end Pin3338
