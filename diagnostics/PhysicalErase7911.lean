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
                simp only [id_eq] at hi
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
lemma mapDefault {α β : Type} (f : α → β) (d : α) (v : Option α) : f (v.getD d)=(v.map f).getD (f d) := by cases v <;> rfl
lemma mapAt {α β : Type} (f : α → β) (d : α) (L : List α) (i : ℕ) : f (L.getD i d)=(L.map f).getD i (f d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; exact mapDefault f d _
lemma val_meet {α} (x : α → Bool) (L : List (Expr α)) : Expr.val x (L.foldr .meet .one)=(L.map (Expr.val x)).all id := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [Expr.val,ih]
lemma val_join {α} (x : α → Bool) (L : List (Expr α)) : Expr.val x (L.foldr .join .zero)=(L.map (Expr.val x)).any id := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [Expr.val,ih]
lemma deg_meet {α} (c : α → ℕ) (L : List (Expr α)) : Expr.degree c (L.foldr .meet .one)=(L.map (Expr.degree c)).sum := by
  induction L with | nil => rfl | cons a L ih => simp [Expr.degree,ih]
lemma deg_join {α} (c : α → ℕ) (L : List (Expr α)) : Expr.degree c (L.foldr .join .zero)=(L.map (Expr.degree c)).foldr max 0 := by
  induction L with | nil => rfl | cons a L ih => simp [Expr.degree,ih]
lemma val_blend {α} (x : α → Bool) (L : List (Expr α)) (g : Gate) (h : g.op=.and ∨ g.op=.or) :
    Expr.val x (blend g L)=g.op.eval (g.inputs.map fun i => (L.map (Expr.val x)).getD i false) := by
  rcases h with h|h <;> simp [blend,h,val_meet,val_join,GateOp.eval,List.map_map,Function.comp_def, mapDefault (Expr.val x) .zero, Expr.val]
lemma deg_blend {α} (c : α → ℕ) (L : List (Expr α)) (g : Gate) :
    Expr.degree c (blend g L)=g.lineDegree (L.map (Expr.degree c)) := by
  by_cases h : g.op=.and <;> simp [blend,Gate.lineDegree,h,deg_meet,deg_join,List.map_map,Function.comp_def,mapDefault (Expr.degree c) .zero, Expr.degree]
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
namespace Physical7911
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Hole7911
abbrev Frame := Expr (Option ℕ)
def raw (n : ℕ) : List Frame := (List.range n).map fun i => .atom (some i)
def input (n : ℕ) (x : ℕ → Bool) := (List.range n).map x
def price (M : Finset ℕ) (i : ℕ) := if i∈M then 1 else 0
def weights (M : Finset ℕ) (v : ℕ) : Option ℕ → ℕ | none => v | some i => price M i
def split (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) : Circuit := ⟨pre++g::post,o⟩
def gateCost (n : ℕ) (pre : List Gate) (g : Gate) (M : Finset ℕ) := g.lineDegree (degrees pre ((List.range n).map (price M)))
def gateVal (n : ℕ) (pre : List Gate) (g : Gate) (x : ℕ → Bool) :=
  g.op.eval (g.inputs.map fun i => (values pre (input n x)).getD i false)
def cutVal (n : ℕ) (pre post : List Gate) (o : ℕ) (x : ℕ → Bool) (b : Bool) :=
  (values post (values pre (input n x) ++ [b])).getD o false
def root (n : ℕ) (pre post : List Gate) (o : ℕ) : Frame :=
  (run post (run pre (raw n) ++ [.atom none])).getD o .zero
lemma intact (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (x : ℕ → Bool) :
    (split pre g post o).eval (input n x)=cutVal n pre post o x (gateVal n pre g x) := by
  simp [split,Circuit.eval,Circuit.wires,cutVal,gateVal,values,List.foldl_append]
lemma expression {n pre g post o} (hm : Monotone2 (split pre g post o)) (x : ℕ → Bool) (b : Bool) :
    (root n pre post o).val (fill b x)=cutVal n pre post o x b := by
  have hp : ∀ a∈pre, a.op=.and ∨ a.op=.or := fun a h => (hm a (by simp [split,h])).1
  have hs : ∀ a∈post, a.op=.and ∨ a.op=.or := fun a h => (hm a (by simp [split,h])).1
  unfold root
  rw [mapAt (Expr.val (fill b x)) .zero, val_run _ _ _ hs,List.map_append,val_run _ _ _ hp]
  simp [raw,cutVal,input,List.map_map,Function.comp_def,Expr.val,fill]
lemma charge (n pre g post o M) : (root n pre post o).degree (weights M (gateCost n pre g M))=(split pre g post o).lineDeg n M := by
  unfold root
  rw [mapAt (Expr.degree _) .zero,deg_run,List.map_append,deg_run]
  simp [raw,Expr.degree,weights,price,gateCost,split,Circuit.lineDeg,Circuit.lineDegrees,degrees,List.foldl_append,List.map_map,Function.comp_def] <;> rfl

theorem physical_context (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (hm : Monotone2 (split pre g post o))
    (x : ℕ → Bool) (sensitive : cutVal n pre post o x true=true ∧ cutVal n pre post o x false=false) :
    ∃ S : List ℕ, (∀ i∈S,x i=true) ∧ (∀ y, (∀ i∈S,y i=true) → gateVal n pre g y=true → (split pre g post o).eval (input n y)=true) ∧
      ∀ M : Finset ℕ, gateCost n pre g M+(S.map (price M)).sum≤(split pre g post o).lineDeg n M := by
  obtain ⟨S,inS,forces,cost⟩ := context (root n pre post o) x ((expression hm x true).trans sensitive.1) ((expression hm x false).trans sensitive.2)
  refine ⟨S,inS,?_,?_⟩
  · intro y hy actual
    rw [intact,actual,←expression hm]
    exact forces y hy
  · intro M
    have c := cost (weights M (gateCost n pre g M))
    rw [charge] at c
    exact c

theorem free_coords (S : List ℕ) (M : Finset ℕ) (z : (S.map (price M)).sum=0) : ∀ i∈S, i∉M := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons,List.sum_cons] at z
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · intro h; simp [price,h] at z
    · exact ih (by omega) i hi

theorem no_marked_context {n pre g post o M} (hm : Monotone2 (split pre g post o))
    (saturated : (split pre g post o).lineDeg n M≤gateCost n pre g M) (x : ℕ → Bool)
    (sens : cutVal n pre post o x true=true ∧ cutVal n pre post o x false=false) :
    ∀ y, (∀ i, i∉M → x i=true → y i=true) → gateVal n pre g y=true → (split pre g post o).eval (input n y)=true := by
  obtain ⟨S,active,forces,priceS⟩ := physical_context n pre g post o hm x sens
  have cost := priceS M
  have outside := free_coords S M (by omega)
  exact fun y keep => forces y (fun i hi => keep i (outside i hi) (active i hi))
end Physical7911
namespace Drop7911
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Hole7911 Physical7911
def index (m z i : ℕ) := if i<m then i else if i=m then z else i-1
def adjust (m z : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (index m z)⟩
def erase (n : ℕ) (pre post : List Gate) (o : ℕ) : Circuit :=
  let m := n+pre.length
  let z := m+post.length
  ⟨pre++post.map (adjust m z),index m z o⟩

lemma read (A B : List Bool) (z i : ℕ) (hz : A.length+B.length≤z) :
    (A++false::B).getD i false=(A++B).getD (index A.length z i) false := by
  by_cases h : i<A.length
  · rw [show index A.length z i=i by simp [index,h],List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
  by_cases he : i=A.length
  · subst i
    have bound : (A++B).length≤z := by simpa using hz
    rw [show index A.length z A.length=z by simp [index],List.getD_eq_default _ _ bound,List.getD_append_right _ _ _ _ le_rfl]
    simp
  have hgt : A.length<i := by omega
  have drop : i-A.length=(i-1-A.length)+1 := by omega
  rw [show index A.length z i=i-1 by simp [index,h,he],List.getD_append_right _ _ _ _ (by omega),
    List.getD_append_right _ _ _ _ (by omega),drop]
  rfl

lemma through (gs : List Gate) (A B : List Bool) (z : ℕ) (hz : A.length+B.length+gs.length≤z) :
    ∀ i, (values gs (A++false::B)).getD i false=(values (gs.map (adjust A.length z)) (A++B)).getD (index A.length z i) false := by
  induction gs generalizing B with
  | nil => exact fun i => read A B z i (by simpa using hz)
  | cons g gs ih =>
    let t := g.op.eval (g.inputs.map fun i => (A++false::B).getD i false)
    have e : t = (adjust A.length z g).op.eval ((adjust A.length z g).inputs.map fun i => (A++B).getD i false) := by
      unfold t
      simp only [adjust,List.map_map,Function.comp_def]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _
      exact read A B z i (by simp at hz; omega)
    intro i
    change (values gs ((A++false::B)++[t])).getD i false = (values (gs.map (adjust A.length z)) ((A++B)++[_])).getD _ false
    rw [←e]
    have step := ih (B++[t]) (by simp at hz ⊢; omega) i
    simpa only [List.append_assoc,List.cons_append] using step

lemma len_values (gs : List Gate) (A : List Bool) : (values gs A).length=A.length+gs.length := by
  induction gs generalizing A with
  | nil => simp [values]
  | cons g gs ih =>
    change (values gs (A++[_])).length=_
    rw [ih]; simp; omega

theorem implements (n : ℕ) (pre post : List Gate) (o : ℕ) (x : ℕ → Bool) :
    (erase n pre post o).eval (input n x)=cutVal n pre post o x false := by
  let A := values pre (input n x)
  have lenA : A.length=n+pre.length := by simp [A,len_values,input]
  have eq := through post A [] (n+pre.length+post.length) (by simp [lenA]) o
  simpa [erase,Circuit.eval,Circuit.wires,List.foldl_append,cutVal,values,A,lenA] using eq.symm

theorem erase_mono {n pre g post o} (hm : Monotone2 (split pre g post o)) : Monotone2 (erase n pre post o) := by
  intro a ha
  change a∈pre++post.map (adjust (n+pre.length) (n+pre.length+post.length)) at ha
  rcases List.mem_append.mp ha with h|h
  · exact hm a (by simp [split,h])
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    have hb' := hm b (by simp [split,hb])
    simpa [adjust] using hb'

theorem erase_size (n : ℕ) (pre post : List Gate) (o : ℕ) : (erase n pre post o).size=pre.length+post.length := by simp [erase,Circuit.size]
end Drop7911
end PEqualNP.Outside.L_meta_7911
