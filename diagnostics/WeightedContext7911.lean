import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_7911
namespace Hole7911
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
inductive Expr (α : Type) where
  | atom (v : α)
  | zero | one
  | join (a b : Expr α)
  | meet (a b : Expr α)
namespace Expr
variable {α : Type}
def val (x : α → Bool) : Expr α → Bool
  | .atom v => x v | .zero => false | .one => true
  | .join a b => val x a || val x b | .meet a b => val x a && val x b
def degree (c : α → ℕ) : Expr α → ℕ
  | .atom v => c v | .zero | .one => 0
  | .join a b => max (degree c a) (degree c b) | .meet a b => degree c a+degree c b
lemma parse (f : Expr α) (x : α → Bool) (on : val x f=true) : ∃ T : List α,
    (∀ t∈T,x t=true) ∧ (∀ y, (∀ t∈T,y t=true) → val y f=true) ∧
    ∀ c : α → ℕ, (T.map c).sum≤degree c f := by
  induction f with
  | atom v => exact ⟨[v],by simp_all [val],by simp [val],by simp [degree]⟩
  | zero => contradiction
  | one => exact ⟨[],by simp,by simp [val],by simp⟩
  | join a b ha hb =>
    rcases Bool.or_eq_true_iff.mp on with h|h
    · obtain ⟨T,yes,v,c⟩ := ha h
      exact ⟨T,yes,fun y h => Bool.or_eq_true_iff.mpr (Or.inl (v y h)),fun w => (c w).trans (le_max_left ..)⟩
    · obtain ⟨T,yes,v,c⟩ := hb h
      exact ⟨T,yes,fun y h => Bool.or_eq_true_iff.mpr (Or.inr (v y h)),fun w => (c w).trans (le_max_right ..)⟩
  | meet a b ha hb =>
    have both := Bool.and_eq_true_iff.mp on
    obtain ⟨T,ht,vt,ct⟩ := ha both.1
    obtain ⟨U,hu,vu,cu⟩ := hb both.2
    refine ⟨T++U,?_,?_,?_⟩
    · intro v hv; exact (List.mem_append.mp hv).elim (ht v) (hu v)
    · intro y hy; exact Bool.and_eq_true_iff.mpr ⟨vt y (fun t h => hy t (List.mem_append_left _ h)),vu y (fun t h => hy t (List.mem_append_right _ h))⟩
    · intro w; simpa only [List.map_append,List.sum_append,degree] using Nat.add_le_add (ct w) (cu w)
end Expr
variable {α : Type}
def fill (b : Bool) (x : α → Bool) : Option α → Bool | none => b | some i => x i
lemma projected (T : List (Option α)) (c : Option α → ℕ) :
    ((T.filterMap id).map (fun i => c (some i))).sum ≤ (T.map c).sum := by
  induction T with
  | nil => simp
  | cons a t ih => cases a <;> simp_all [List.filterMap_cons] <;> omega
lemma charge_marker (T : List (Option α)) (h : none∈T) (c : Option α → ℕ) :
    c none+((T.filterMap id).map (fun i => c (some i))).sum ≤ (T.map c).sum := by
  induction T with
  | nil => simp at h
  | cons a t ih =>
    cases a with
    | none => simpa using Nat.add_le_add_left (projected t c) (c none)
    | some i => have m : none∈t := by simpa using h
                have hi := ih m
                simp only [List.filterMap_cons,id_eq,List.map_cons,List.sum_cons]
                omega
lemma context (f : Expr (Option α)) (x : α → Bool) (on : f.val (fill true x)=true) (off : f.val (fill false x)=false) :
    ∃ S : List α, (∀ i∈S,x i=true) ∧ (∀ y, (∀ i∈S,y i=true) → f.val (fill true y)=true) ∧
    ∀ c : Option α → ℕ, c none+(S.map (fun i => c (some i))).sum≤f.degree c := by
  obtain ⟨T,member,covers,price⟩ := f.parse (fill true x) on
  have mark : none∈T := by
    by_contra z
    have h := covers (fill false x) (by rintro (_|i) hi; exact (z hi).elim; exact member _ hi)
    exact Bool.noConfusion (off.symm.trans h)
  refine ⟨T.filterMap id,?_,?_,fun c => (charge_marker T mark c).trans (price c)⟩
  · intro i hi
    obtain ⟨t,ht,e⟩ := List.mem_filterMap.mp hi
    change t=some i at e; subst t; exact member _ ht
  · intro y hy
    apply covers
    rintro (_|i) hi
    · rfl
    · exact hy i (List.mem_filterMap.mpr ⟨some i,hi,rfl⟩)

attribute [local instance] PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
def blend {α} (g : Gate) (bank : List (Expr α)) : Expr α :=
  if g.op = .and then (g.inputs.map (fun i => bank.getD i .zero)).foldr .meet .one
  else (g.inputs.map (fun i => bank.getD i .zero)).foldr .join .zero
def run {α} (gs : List Gate) (bank : List (Expr α)) := gs.foldl (fun L g => L++[blend g L]) bank
def values (gs : List Gate) (bank : List Bool) := gs.foldl (fun L g => L++[g.op.eval (g.inputs.map fun i => L.getD i false)]) bank
def degrees (gs : List Gate) (bank : List ℕ) := gs.foldl (fun L g => L++[g.lineDegree L]) bank
lemma mapAt {α β : Type} (f : α → β) (d : α) (L : List α) (i : ℕ) : f (L.getD i d)=(L.map f).getD i (f d) := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_map,Option.map_getD]
lemma val_meet {α} (x : α → Bool) (L : List (Expr α)) : Expr.val x (L.foldr .meet .one)=(L.map (Expr.val x)).all id := by
  induction L with
  | nil => rfl
  | cons a L ih => change _ && _ = _; simp [ih,Expr.val]
lemma val_join {α} (x : α → Bool) (L : List (Expr α)) : Expr.val x (L.foldr .join .zero)=(L.map (Expr.val x)).any id := by
  induction L with
  | nil => rfl
  | cons a L ih => change _ || _ = _; simp [ih,Expr.val]
lemma deg_meet {α} (c : α → ℕ) (L : List (Expr α)) : Expr.degree c (L.foldr .meet .one)=(L.map (Expr.degree c)).sum := by
  induction L with | nil => rfl | cons a L ih => simp [Expr.degree,ih]
lemma deg_join {α} (c : α → ℕ) (L : List (Expr α)) : Expr.degree c (L.foldr .join .zero)=(L.map (Expr.degree c)).foldr max 0 := by
  induction L with | nil => rfl | cons a L ih => simp [Expr.degree,ih]
lemma val_blend {α} (x : α → Bool) (L : List (Expr α)) (g : Gate) (h : g.op=.and ∨ g.op=.or) :
    Expr.val x (blend g L)=g.op.eval (g.inputs.map fun i => (L.map (Expr.val x)).getD i false) := by
  rcases h with h|h <;> simp [blend,h,val_meet,val_join,GateOp.eval,List.map_map,Function.comp_def, mapAt (Expr.val x) .zero L]
lemma deg_blend {α} (c : α → ℕ) (L : List (Expr α)) (g : Gate) :
    Expr.degree c (blend g L)=g.lineDegree (L.map (Expr.degree c)) := by
  by_cases h : g.op=.and <;> simp [blend,Gate.lineDegree,h,deg_meet,deg_join,List.map_map,Function.comp_def,mapAt (Expr.degree c) .zero L]
lemma val_run {α} (x : α → Bool) (gs : List Gate) (L : List (Expr α)) (hm : ∀ g∈gs,g.op=.and ∨ g.op=.or) :
    (run gs L).map (Expr.val x)=values gs (L.map (Expr.val x)) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (L++[blend g L])).map _=values gs _
    rw [ih _ (fun i hi => hm i (by simp [hi]))]; simp only [List.map_append,List.map_cons,List.map_nil,val_blend x L g (hm g (by simp))]
lemma deg_run {α} (c : α → ℕ) (gs : List Gate) (L : List (Expr α)) :
    (run gs L).map (Expr.degree c)=degrees gs (L.map (Expr.degree c)) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (L++[blend g L])).map _=degrees gs _
    rw [ih]; simp only [List.map_append,List.map_cons,List.map_nil,deg_blend]
end Hole7911
end PEqualNP.Outside.L_meta_7911
