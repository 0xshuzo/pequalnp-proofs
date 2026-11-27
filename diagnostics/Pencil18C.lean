import PEqualNP.Defs

namespace PencilControl
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
abbrev V := Fin 42
abbrev I := Fin 18
abbrev S := Fin 21
def armL : Array Nat := #[5419040770,214756769792,81938,21617442848,1718003696128,524896,43100667908,693637218560,2436,1112933401600,584157626368,398336,576599359496,1237118386176,1089544,1,2097151,4398044413952]
def armR : Array Nat := #[550431096848,1153198784512,2097152,10775167040,173409828864,67108864,1100597952640,86469773312,268435456,72074924032,154640056320,274877906944,2709528576,107379425280,2199023255552,2474238803968,0,0]
def left (i : I) := armL[i.val]?.getD 0
def right (i : I) := armR[i.val]?.getD 0
def vertices (m : Nat) : Finset V := Finset.univ.filter fun v => m.testBit v.val = true
def prev (i : I) : Finset I := if i.val=16 then Finset.univ.filter (fun j => j.val<16)
  else if i.val=17 then {16} else ∅
abbrev C : AndCountCircuit 42 where
  size := 18
  leftVars i := vertices (left i)
  rightVars i := vertices (right i)
  leftGates _ := ∅
  rightGates := prev
  outVars := ∅
  outGates := {17}

def hit (m : Nat) (U : Finset V) := ∃ v ∈ U, m.testBit v.val=true
lemma meet (m : Nat) (U : Finset V) : (∃v ∈ vertices m, v∈U) ↔ hit m U := by
  simp only [vertices,Finset.mem_filter,Finset.mem_univ,true_and,hit]
  exact exists_congr (fun _ => and_comm)

lemma step (U : Finset V) (d : Nat) (i : I) : C.gateValFuel U (d+1) i=true ↔
    hit (left i) U ∧ (hit (right i) U ∨ ∃ j∈prev i, j < i ∧ C.gateValFuel U d j=true) := by
  rw [gateValFuel,Bool.and_eq_true]
  simp only [sideTrue,decide_eq_true_eq]
  change ((∃v∈vertices (left i),v∈U) ∨ ∃ j ∈ (∅:Finset I), j < i ∧ C.gateValFuel U d j=true) ∧
      ((∃v∈vertices (right i),v∈U) ∨ ∃j∈prev i,j < i ∧ C.gateValFuel U d j=true) ↔ _
  simp only [meet,Finset.notMem_empty,false_and,exists_false,or_false]

lemma primitive (i : I) (hi : i.val<16) (U : Finset V) (d : Nat) :
    C.gateValFuel U (d+1) i = true ↔ hit (left i) U ∧ hit (right i) U := by
  have n16 : i.val≠16 := by omega
  have n17 : i.val≠17 := by omega
  rw [step]
  simp only [prev,if_neg n16,if_neg n17,Finset.notMem_empty,false_and,exists_false,or_false]

lemma pre (U : Finset V) (d : Nat) : C.gateValFuel U (d+2) 16 = true ↔
    hit (left 16) U ∧ (∃i : I,i.val<16 ∧ hit (left i) U ∧ hit (right i) U) := by
  rw [step]
  have zero : ¬hit (right 16) U := by
    intro h
    obtain ⟨v,_,hv⟩ := h
    exact (by decide +kernel : ∀v:V, ¬(right 16).testBit v.val=true) v hv
  simp only [zero,false_or]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨j,hj,_,h⟩
    have v : j.val<16 := (Finset.mem_filter.mp (show j∈Finset.univ.filter (fun i : I => i.val<16) from hj)).2
    exact ⟨j,v,(primitive j v U d).mp h⟩
  · rintro ⟨j,hj,h⟩
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,hj,(primitive j hj U d).mpr h⟩

def accepts (U : Finset V) := hit (left 17) U ∧ hit (left 16) U ∧
  ∃i : I,i.val<16 ∧ hit (left i) U ∧ hit (right i) U
lemma eval_iff (U : Finset V) : C.eval U=true ↔ accepts U := by
  rw [AndCountCircuit.eval,decide_eq_true_eq]
  change ((∃v∈(∅ : Finset V), v∈U) ∨ ∃j∈({17}:Finset I), C.gateVal U j=true) ↔ _
  simp only [Finset.notMem_empty,false_and,exists_false,false_or,Finset.mem_singleton,exists_eq_left]
  change C.gateValFuel U (17+1) (17:I)=true ↔ _
  rw [step]
  have zero : ¬hit (right 17) U := by
    rintro ⟨v,_,hv⟩
    exact (by decide +kernel : ∀v:V, ¬(right 17).testBit v.val=true) v hv
  have last : prev 17 = {16} := by decide +kernel
  simp only [zero,false_or,last,Finset.mem_singleton,exists_eq_left,show (16:I)<17 by decide,true_and,accepts]
  exact and_congr_right fun _ => pre U 15

def ori (a b : V) : Prop := a.val<21 ∧ 21≤b.val ∧
    (b.val+21-a.val)%21∈([0,5,7,17,20]:List Nat)
instance (a b:V) : Decidable (ori a b) := by unfold ori; infer_instance
def G := SimpleGraph.fromRel ori
lemma hemi (a b : V) : G.Adj a b ↔ ori a b ∨ ori b a := by
  rw [G, SimpleGraph.fromRel_adj]
  refine and_iff_right_of_imp ?_
  rintro (h | h) rfl <;> unfold ori at h <;> omega

def hits (m : Nat) (a b : V) := m.testBit a.val=true ∨ m.testBit b.val=true
instance (m:Nat) (a b:V) : Decidable (hits m a b) := by unfold hits; infer_instance
def acceptsPair (a b : V) := hits (left 17) a b ∧ hits (left 16) a b ∧
    ∃i:I,i.val<16 ∧ hits (left i) a b ∧ hits (right i) a b
instance (a b:V) : Decidable (acceptsPair a b) := by unfold acceptsPair; infer_instance
lemma hitPair (m : Nat) (a b : V) : hit m {a,b} ↔ hits m a b := by simp [hit,hits]
set_option maxHeartbeats 3500000 in
set_option maxRecDepth 10000 in
lemma table : ∀a b:V, acceptsPair a b ↔ ori a b ∨ ori b a := by decide +kernel
theorem allPairs (a b : V) : C.eval {a,b}=true ↔ G.Adj a b := by
  simpa only [eval_iff,accepts,hitPair,hemi,acceptsPair] using table a b

def dyad (d p : S) : Finset V := {Fin.castAdd 21 p,Fin.natAdd 21 (p+d)}
def cross (i : I) (d p : S) : Prop :=
  (∃v∈C.leftVars i,v∈dyad d p) ∧ ∃v∈C.rightVars i,v∈dyad d p
def owner (i : I) (d p : S) := cross i d p ∧ ∀ j < i, ¬cross j d p
def double (i : I) := ∃d∈({0,5,7,17,20}:Finset S),∃p q:S,p≠q ∧ owner i d p ∧ owner i d q
def raw (i : I) (d p : S) :=
  hits (left i) (Fin.castAdd 21 p) (Fin.natAdd 21 (p+d)) ∧
  hits (right i) (Fin.castAdd 21 p) (Fin.natAdd 21 (p+d))
instance (i:I) (d p:S) : Decidable (raw i d p) := by unfold raw; infer_instance
lemma raw_iff (i:I) (d p:S) : raw i d p ↔ cross i d p := by
  change _ ↔ (∃v∈vertices (left i),v∈dyad d p) ∧ ∃v∈vertices (right i),v∈dyad d p
  rw [meet,meet]
  change _ ↔ hit _ {_,_} ∧ hit _ {_,_}
  simp only [dyad,hitPair,raw]
def records : Array (I × S × S × S) := #[(0,0,1,4),(12,0,3,13),(7,0,8,11),(4,0,9,19),(9,0,10,12),(1,0,14,16),(3,5,5,6),(10,5,17,18),(6,7,2,7),(13,7,15,20)]
def cert (j:Fin 10) := records[j.val]?.getD (0,0,0,0)
set_option maxRecDepth 10000 in
lemma records_ok : ∀ j:Fin 10, let (i,d,p,q) := cert j
    d∈({0,5,7,17,20}:Finset S) ∧ p≠q ∧ (raw i d p ∧ ∀ k < i,¬raw k d p) ∧ (raw i d q ∧ ∀ k < i,¬raw k d q) := by
  decide +kernel
theorem repeats (j:Fin 10) : double (cert j).1 := by
  generalize h : cert j = t at *
  obtain ⟨i,d,p,q⟩ := t
  change double i
  have v := records_ok j
  rw [h] at v
  dsimp only at v
  exact ⟨d,v.1,p,q,v.2.1,⟨(raw_iff _ _ _).mp v.2.2.1.1,
    fun k hk ck => v.2.2.1.2 k hk ((raw_iff _ _ _).mpr ck)⟩,
    (raw_iff _ _ _).mp v.2.2.2.1,fun k hk ck => v.2.2.2.2 k hk ((raw_iff _ _ _).mpr ck)⟩
theorem tenDouble : 10 ≤ {i:I | double i}.ncard := by
  classical
  let R := (Finset.univ : Finset (Fin 10)).image (fun j => (cert j).1)
  have card : R.card=10 := by decide +kernel
  have sub : (R : Set I) ⊆ {i:I | double i} := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact repeats j
  simpa only [Set.ncard_coe_finset,card] using Set.ncard_le_ncard sub

theorem size_wf : C.size=18 ∧ C.WellFormed ∧ ∀ i, Disjoint (C.leftVars i) (C.rightVars i) := by
  refine ⟨rfl,?_,?_⟩
  · unfold WellFormed
    decide +kernel
  · decide +kernel

theorem error : C.eval {0,22,23}=true ∧ ¬∃a∈({0,22,23}:Finset V),∃b∈({0,22,23}:Finset V), G.Adj a b := by
  rw [eval_iff]
  change accepts _ ∧ _
  constructor
  · unfold accepts hit
    decide +kernel
  · simp only [hemi]
    decide +kernel
end PencilControl
