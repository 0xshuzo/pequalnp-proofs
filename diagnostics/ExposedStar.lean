import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit (step, val, val_snoc, val_ge, val_lt) copied from the L_meta_2986 / L_meta_1406 files

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = val ([] : List Gate) x i := by
  rw [val_lt gs x i hi, val_lt [] x i hi]

/-- re-indexing of the wires: the first `a` inputs stay, everything else moves up by `n`. -/
def phi (a n : ℕ) (w : ℕ) : ℕ := if w < a then w else w + n

def rho (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi a n)⟩

lemma phi_lt (a n : ℕ) (ha : a ≤ n) (i : ℕ) (hi : i < n) : phi a n i < n + n := by
  unfold phi
  split_ifs <;> omega

def zof (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) : Fin n → Bool :=
  fun i => x ⟨phi a n i.val, phi_lt a n ha i.val i.isLt⟩

lemma reidx (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) (z : Fin n → Bool)
    (hz : ∀ (i : ℕ) (hi : i < n) (h2 : phi a n i < n + n), z ⟨i, hi⟩ = x ⟨phi a n i, h2⟩) :
    ∀ (gs : List Gate) (w : ℕ), val (gs.map (rho a n)) x (phi a n w) = val gs z w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil]
    rw [val_nil, val_nil]
    by_cases hw : w < n
    · have hp := phi_lt a n ha w hw
      rw [dif_pos hp, dif_pos hw]
      exact (hz w hw hp).symm
    · have hp : ¬ phi a n w < n + n := by
        unfold phi
        split_ifs <;> omega
      rw [dif_neg hp, dif_neg hw]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_cons, List.map_nil, val_snoc, val_snoc, List.length_map]
    have key : phi a n w = n + n + gs.length ↔ w = n + gs.length := by
      unfold phi
      split_ifs <;> omega
    by_cases hw : w = n + gs.length
    · rw [if_pos (key.2 hw), if_pos hw]
      show g.op.eval (List.map (fun j => val (gs.map (rho a n)) x j) (g.inputs.map (phi a n))) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hw (key.1 h)), if_neg hw]
      exact ih w

/-- well-formed gate lists: AND/OR, two inputs, each input earlier. -/
def WF (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m + j

lemma wf_two (m : ℕ) (gs : List Gate) (a b c : ℕ) (hwf : WF m gs)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    WF m (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h | h
  · rw [List.getElem?_append_left h] at hj
    exact hwf j g hj
  · rw [List.getElem?_append_right h] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = gs.length + k := ⟨j - gs.length, by omega⟩
    rw [Nat.add_sub_cancel_left] at hj
    match k, hj with
    | 0, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inl rfl, rfl, by intro i hi; simp at hi; omega⟩
    | 1, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
    | k + 2, hj => simp at hj

lemma val_two_new {m : ℕ} (gs : List Gate) (a b c : ℕ) (x : Fin m → Bool)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    val (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) x (m + gs.length + 1)
      = (val gs x c || (val gs x a && val gs x b)) := by
  have happ : gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [c, m + gs.length]⟩]
      = (gs ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [c, m + gs.length]⟩] := by simp
  have hl1 : (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
  rw [happ, val_snoc, if_pos (by omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [val_snoc, if_neg (by omega), val_snoc, if_pos rfl]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]

lemma isAO2_of_wf (m : ℕ) (gs : List Gate) (out : ℕ) (hwf : WF m gs) :
    PEqualNP.TopForm.IsAO2 m (⟨gs, out⟩ : Circuit) := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hi' : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact (hwf j _ (List.getElem?_eq_getElem hj')).2.2 i hi'
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).2.1

end PEqualNP.Outside.L_meta_3264_aux
namespace PEqualNP.Outside.L_meta_2585.Run
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3264_aux

def rem {n m : Nat} (f : Fin n → Fin m) (w : Nat) : Nat :=
  if h : w < n then (f ⟨w,h⟩).val else m+(w-n)
def gate {n m : Nat} (f : Fin n → Fin m) (g : Gate) : Gate := ⟨g.op,g.inputs.map (rem f)⟩

private theorem rem_lt {n m : Nat} (f : Fin n → Fin m) {w j : Nat} (hw : w < n+j) :
    rem f w < m+j := by
  unfold rem
  split
  next h => have := (f ⟨w,h⟩).isLt; omega
  next => omega

private theorem rem_gate {n m : Nat} (f : Fin n → Fin m) (w j : Nat) :
    rem f w=m+j ↔ w=n+j := by
  unfold rem
  split
  next h => have := (f ⟨w,h⟩).isLt; omega
  next => omega

private theorem sim {n m : Nat} (f : Fin n → Fin m) (x : Fin m → Bool) :
    ∀ (gs : List Gate) (w : Nat),
      L_meta_3264_aux.val (gs.map (gate f)) x (rem f w) = L_meta_3264_aux.val gs (x ∘ f) w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil]
    rw [val_nil,val_nil]
    by_cases hw : w < n
    · have hm : rem f w < m := by simpa using rem_lt f (j:=0) (by simpa using hw)
      rw [dif_pos hm,dif_pos hw]
      congr 1
      apply Fin.ext
      simp [rem,hw]
    · have hm : ¬ rem f w < m := by simp [rem,hw]
      rw [dif_neg hm,dif_neg hw]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append,List.map_cons,List.map_nil,val_snoc,val_snoc,List.length_map]
    by_cases hw : w=n+gs.length
    · rw [if_pos ((rem_gate f w _).2 hw),if_pos hw]
      change g.op.eval ((g.inputs.map (rem f)).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hw ((rem_gate f w _).1 h)),if_neg hw]
      exact ih w

private theorem good {n m : Nat} (f : Fin n → Fin m) (C : Circuit) (ao : IsAO2 n C) :
    WF m (C.gates.map (gate f)) := by
  intro j g hg
  rw [List.getElem?_map] at hg
  cases h : C.gates[j]? with
  | none => simp [h] at hg
  | some a =>
    simp [h] at hg
    subst g
    have ha := List.mem_of_getElem? h
    have hj : j < C.gates.length := by
      by_contra! bad
      rw [List.getElem?_eq_none bad] at h
      contradiction
    refine ⟨ao.1 a ha,by simpa [gate] using ao.2.2 a ha,?_⟩
    intro k hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    apply rem_lt f (ao.2.1 j hj i ?_)
    change i ∈ (C.gates.getD j _).inputs
    simpa [List.getD_eq_getElem?_getD,h] using hi


private theorem wfOr {n : Nat} (gs : List Gate) {u v : Nat} (hag : WF n gs)
    (hu : u<n+gs.length) (hv : v<n+gs.length) : WF n (gs++[⟨.or,[u,v]⟩]) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h|h
  · rw [List.getElem?_append_left h] at hj
    exact hag j g hj
  · rw [List.getElem?_append_right h] at hj
    cases eq : j-gs.length with
    | zero =>
      rw [eq] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst g
      exact ⟨Or.inr rfl,rfl,by intro i hi; simp at hi; omega⟩
    | succ d => simp [eq] at hj

theorem exposedWire {k n : Nat} (C : Circuit) (ao : IsAO2 k C) (w : Nat)
    (ho : C.output < k+C.size) (hw : w < k+C.size) (f : Fin k → Fin n) (u z : Fin n) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size=C.size+3 ∧
      ∀ x : Fin n → Bool, circuitFun n D x =
        (circuitFun k C (x ∘ f) || (x z && (x u || val C.gates (x ∘ f) w))) := by
  let gs := C.gates.map (gate f)
  let v := rem f w
  let o := rem f C.output
  let start := n+gs.length
  let g : Gate := ⟨.or,[u.val,v]⟩
  let mid := gs++[g]
  let tail : List Gate := [⟨.and,[z.val,start]⟩,⟨.or,[o,n+mid.length]⟩]
  let final := n+mid.length+1
  have lv : v < n+gs.length := by simpa [v,gs,Circuit.size] using rem_lt f hw
  have lo : o < n+gs.length := by simpa [o,gs,Circuit.size] using rem_lt f ho
  have lu := u.isLt
  have lz := z.isLt
  have lm : mid.length=gs.length+1 := by simp [mid]
  have ls : start < n+mid.length := by dsimp [start]; omega
  have lo' : o<n+mid.length := by omega
  have lz' : z.val<n+mid.length := by omega
  have legal := wfOr gs (u:=u.val) (v:=v) (good f C ao) (by omega) lv
  have leg2 := wf_two n mid z.val start o legal lz' ls lo'
  refine ⟨⟨mid++tail,final⟩,isAO2_of_wf _ _ _ leg2,?_,?_⟩
  · simp [Circuit.size,mid,gs,tail]
  intro x
  change val (mid++tail) x final = _
  rw [show val (mid++tail) x final = (val mid x o || (val mid x z.val && val mid x start)) from
    val_two_new mid z.val start o x lz' ls lo']
  have vom : val mid x o=val gs x o := by rw [show mid=gs++[g] from rfl,val_snoc,if_neg (by omega)]
  have vz : val mid x z.val=x z := val_lt mid x z.val z.isLt
  have vs : val mid x start=(x u || val C.gates (x ∘ f) w) := by
    rw [show mid=gs++[g] from rfl,val_snoc,if_pos rfl]
    simp only [g,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
    rw [val_lt gs x u.val u.isLt]
    exact congrArg (fun b=>x u || b) (sim f x C.gates w)
  rw [vom,vz,vs]
  exact congrArg (fun b=>b || (x z && (x u || val C.gates (x ∘ f) w))) (sim f x C.gates C.output)

end PEqualNP.Outside.L_meta_2585.Run

namespace PEqualNP.Outside.L_meta_2585.Star
variable {P L : Type*} [Fintype P] [Fintype L]
def graph (r : P → L → Prop) (S : Finset P) : P ⊕ Unit → L ⊕ Unit → Prop
  | .inl p,.inl l => r p l
  | .inl p,.inr _ => p∈S
  | .inr _,.inl _ => False
  | .inr _,.inr _ => True

def NoRect (r : P → L → Prop) := ∀ p q l k, r p l → r p k → r q l → r q k → p=q ∨ l=k

theorem noRect {r : P → L → Prop} (S : Finset P) (base : NoRect r)
    (apart : ∀ p∈S,∀ q∈S,∀ l, r p l → r q l → p=q) : NoRect (graph r S) := by
  intro p q l k
  rcases p with p|⟨⟩ <;> rcases q with q|⟨⟩ <;> rcases l with l|⟨⟩ <;> rcases k with k|⟨⟩ <;>
    simp only [graph,Sum.inl.injEq,Sum.inr.injEq] <;> grind [NoRect]

def mate (s : P ≃ L) : (P ⊕ Unit) ≃ (L ⊕ Unit) := Equiv.sumCongr s (Equiv.refl _)
theorem perfect {r : P → L → Prop} (S : Finset P) (s : P ≃ L) (mat : ∀ p, r p (s p)) :
    ∀ p, graph r S p (mate s p) := by
  rintro (p|⟨⟩)
  · exact mat p
  · trivial

noncomputable def wt (b : Prop) := @ite Nat b (Classical.propDecidable b) 1 0
noncomputable def edges (r : P → L → Prop) := ∑ p : P, ∑ l : L, wt (r p l)
theorem count (r : P → L → Prop) (S : Finset P) : edges (graph r S) = edges r+S.card+1 := by
  classical
  have old (p : P) : (∑ l : L ⊕ Unit, wt (graph r S (.inl p) l)) =
      (∑ l : L, wt (r p l)) + wt (p∈S) := by rw [Fintype.sum_sum_type]; simp [graph]
  have new : (∑ l : L ⊕ Unit, wt (graph r S (.inr ()) l)) = 1 := by
    rw [Fintype.sum_sum_type]; simp [graph,wt]
  have mem : (∑ p : P, wt (p∈S))=S.card := by simp [wt]
  unfold edges
  rw [Fintype.sum_sum_type]
  simp [old,new,Finset.sum_add_distrib,mem]

noncomputable def hit (r : P → L → Prop) (p : P → Bool) (l : L → Bool) : Bool :=
  @decide (∃ a b,r a b ∧ p a=true ∧ l b=true) (Classical.propDecidable _)
noncomputable def member (S : Finset P) (p : P → Bool) : Bool :=
  @decide (∃ a∈S, p a=true) (Classical.propDecidable _)

theorem hit_extend (r : P → L → Prop) (S : Finset P) (p : P ⊕ Unit → Bool) (l : L ⊕ Unit → Bool)
    (w : Bool) (safe : hit r (p ∘ Sum.inl) (l ∘ Sum.inl)=false → w=member S (p ∘ Sum.inl)) :
    hit (graph r S) p l =
      (hit r (p ∘ Sum.inl) (l ∘ Sum.inl) || (l (.inr ()) && (p (.inr ()) || w))) := by
  classical
  have hit_eq : hit (graph r S) p l =
      (hit r (p ∘ Sum.inl) (l ∘ Sum.inl) || (l (.inr ()) && (p (.inr ()) || member S (p ∘ Sum.inl)))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [hit,member,decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true,Function.comp_apply]
    constructor
    · rintro ⟨(a|⟨⟩),(b|⟨⟩),h,one,two⟩
      · exact Or.inl ⟨a,b,h,one,two⟩
      · exact Or.inr ⟨two,Or.inr ⟨a,h,one⟩⟩
      · exact False.elim h
      · exact Or.inr ⟨two,Or.inl one⟩
    · rintro (⟨a,b,h,one,two⟩|⟨two,(one|⟨a,h,one⟩)⟩)
      · exact ⟨.inl a,.inl b,h,one,two⟩
      · exact ⟨.inr (),.inr (),trivial,one,two⟩
      · exact ⟨.inl a,.inr (),h,one,two⟩
  rw [hit_eq]
  cases e : hit r (p ∘ Sum.inl) (l ∘ Sum.inl) with
  | false => rw [safe e]
  | true => simp

end PEqualNP.Outside.L_meta_2585.Star
