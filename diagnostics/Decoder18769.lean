import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18769.Suffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp


def sep (A B : List Bool) (w : Nat) := A.getD w false=true ∧ B.getD w false=false
def separates {J : Type} (X Y : J→List Bool) (S : Finset Nat) := ∀ i,∃ w∈S,sep (X i) (Y i) w

theorem gate_step (g : Gate) (h : g.op=.and ∨ g.op=.or) (A B : List Bool)
    (ha : g.op.eval (g.inputs.map fun i => A.getD i false)=true)
    (hb : g.op.eval (g.inputs.map fun i => B.getD i false)=false) :
    ∃ t∈g.inputs,sep A B t := by
  by_contra! bad
  have lift (t : Nat) (ht : t∈g.inputs) (on : A.getD t false=true) : B.getD t false=true := by
    cases e : B.getD t false with
    | true => rfl
    | false => exact (bad t ht ⟨on,e⟩).elim
  rcases h with h|h
  · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at ha
    have all : (g.inputs.map fun i => B.getD i false).all id=true := List.all_eq_true.mpr (by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
      exact lift i hi (ha i hi))
    simp [h,GateOp.eval,all] at hb
  · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at ha
    obtain ⟨i,hi,v⟩ := ha
    have any : (g.inputs.map fun j => B.getD j false).any id=true := List.any_eq_true.mpr
      ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,lift i hi v⟩
    simp [h,GateOp.eval,any] at hb

theorem sources {J : Type} (m : Nat) (X Y : J→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m) (gs : List Gate)
    (legal : ∀g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (S : Finset Nat) (h : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+gs.length := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,h,by simp⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : J) (w : Nat) (ne : w≠last) :
        sep (run (gs++[g]) (X i)) (run (gs++[g]) (Y i)) w → sep (V i) (W i) w := by
      rw [run_snoc,run_snoc]
      change ((V i++[_]).getD w false=true ∧ (W i++[_]).getD w false=false) → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have gl := legal g (by simp)
    have old := fun a (ha : a∈gs) => legal a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ g.inputs.toFinset
      have ok : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := h i
        by_cases eq : w=last
        · subst w
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false=true ∧ (W i++[g.op.eval _]).getD last false=false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          obtain ⟨t,ht,sep⟩ := gate_step g gl.1 (V i) (W i) diff.1 diff.2
          exact ⟨t,Finset.mem_union_right _ (List.mem_toFinset.mpr ht),sep⟩
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,ht,sz⟩ := ih old R ok
      have u : R.card ≤ (S.erase last).card + g.inputs.toFinset.card := Finset.card_union_le _ _
      have e := Finset.card_erase_add_one mem
      have k := List.toFinset_card_le g.inputs
      refine ⟨T,ht,?_⟩
      simp only [List.length_append,List.length_singleton]
      omega
    · have ok : separates V W S := by
        intro i
        obtain ⟨w,ws,diff⟩ := h i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) diff⟩
      obtain ⟨T,ht,sz⟩ := ih old S ok
      exact ⟨T,ht,by simp; omega⟩

open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel

theorem crosses : ∀ p q : I,p≠q → idx p∉nbr q ∨ idx q∉nbr p := by decide +kernel
abbrev Index := I × Bool
def posP (i : Index) : Finset I := {i.1}
def negP (i : Index) : Finset I := if i.2 then {i.1} else ∅
def posL (i : Index) : Finset L := {idx i.1}
def negL (i : Index) : Finset L := if i.2 then (nbr i.1)ᶜ else {idx i.1}
def initial (X Y : Index→List Bool) := ∀w,
  (∃p : I,∀i, (X i).getD w false=decide (p∈posP i) ∧ (Y i).getD w false=decide (p∈negP i)) ∨
  (∃ f : Finset L → Bool,(∀ a b,a⊆b → f a=true → f b=true) ∧
     ∀ i,(X i).getD w false=f (posL i) ∧ (Y i).getD w false=f (negL i))
theorem exclusive {X Y w} (bank : initial X Y) (i j : Index)
    (hi : sep (X i) (Y i) w) (hj : sep (X j) (Y j) w) : i=j := by
  rcases i with ⟨i,b⟩
  rcases j with ⟨j,c⟩
  rcases bank w with ⟨p,spec⟩ | ⟨f,mono,spec⟩
  · rw [sep,(spec _).1,(spec _).2] at hi hj
    cases b <;> cases c <;> simp_all [posP,negP]
  · rw [sep,(spec _).1,(spec _).2] at hi hj
    cases b <;> cases c <;> simp only [posL,negL,Bool.false_eq_true,if_false,if_true] at hi hj
    all_goals try grind
    by_contra ne
    have ij : i≠j := fun e => ne (congrArg (fun p : I => (p,true)) e)
    rcases crosses i j ij with m|m
    · have a := mono _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr m)) hi.1
      exact Bool.noConfusion (a.symm.trans hj.2)
    · have a := mono _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr m)) hj.1
      exact Bool.noConfusion (a.symm.trans hi.2)
theorem decoder (m : Nat) (X Y : Index→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m) (bank : initial X Y)
    (gs : List Gate) (legal : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (o : Nat) (correct : ∀i,sep (run gs (X i)) (run gs (Y i)) o) : 23≤gs.length := by
  classical
  obtain ⟨T,ht,lim⟩ := sources m X Y lens gs legal {o} (fun i=>⟨o,mem_singleton_self _,correct i⟩)
  choose f hf hv using ht
  have inj : Set.InjOn f (univ : Finset Index) := fun i _ j _ eq =>
    exclusive bank i j (eq ▸ hv i) (hv j)
  have card := card_le_card_of_injOn f (fun i _ => hf i) inj
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at card
  simp only [card_singleton] at lim
  omega
end PEqualNP.Outside.L_meta_18769.Suffix
