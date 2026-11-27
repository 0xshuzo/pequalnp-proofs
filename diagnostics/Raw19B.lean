import PEqualNP.Defs

namespace RawBank
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
abbrev V := Fin 42
abbrev I := Fin 19
abbrev S := Fin 21
def armL : Array Nat := #[16513,33026,66052,132104,264208,528416,1056832,2097151,34359738369,137438953476,549755813904,2199023255616,4194560,16778240,67112960,268451840,1073807360,4295229440,17180917760]
def armR : Array Nat := #[34630270976,69260541952,138521083904,277042167808,554084335616,1108168671232,2216337342464,4398044413952,68719476738,274877906952,1099511627808,2097280,8389120,33556480,134225920,536903680,2147614720,8590458880,0]
def left (i : I) := armL[i.val]?.getD 0
def right (i : I) := armR[i.val]?.getD 0
def vertices (m : Nat) : Finset V := Finset.univ.filter fun v => m.testBit v.val = true

abbrev C : AndCountCircuit 42 where
  size := 19
  leftVars i := vertices (left i)
  rightVars i := vertices (right i)
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := {7}
def arm (i:I) (s:Bool) := if s then vertices (right i) else vertices (left i)
def read (v:V) := Finset.univ.filter (fun i:I => v∈C.leftVars i ∨ v∈C.rightVars i)
private def pairSlot : Array (I × Bool) := #[(8,false),(8,true),(9,false),(9,true),(10,false),(10,true),(11,false),(11,true),(12,false),(12,true),(13,false),(13,true),(14,false),(14,true),(15,false),(15,true),(16,false),(16,true),(17,false),(17,true),(18,false),(11,true),(12,false),(12,true),(13,false),(13,true),(14,false),(14,true),(15,false),(15,true),(16,false),(16,true),(17,false),(17,true),(18,false),(8,false),(8,true),(9,false),(9,true),(10,false),(10,true),(11,false)]
private def blockSlot : Array (I × Bool) := #[(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(0,false),(1,false),(2,false),(3,false),(4,false),(5,false),(6,false),(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(6,true)]
private def mates : Array V := #[35,36,37,38,39,40,41,21,22,23,24,25,26,27,28,29,30,31,32,33,34,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0,1,2,3,4,5,6]
def A (v:V) := pairSlot[v.val]?.getD (0,false)
def B (v:V) := blockSlot[v.val]?.getD (0,false)
def mate (v:V) := mates[v.val]?.getD 0
def S1 (v:V) := arm (A v).1 (A v).2
def S2 (v:V) := arm (B v).1 (B v).2
def ori (a b : V) : Prop := a.val<21 ∧ 21≤b.val ∧
    (b.val+21-a.val)%21∈([0,5,7,17,20]:List Nat)
instance (a b:V) : Decidable (ori a b) := by unfold ori; infer_instance
def G := SimpleGraph.fromRel ori
lemma hemi (a b : V) : G.Adj a b ↔ ori a b ∨ ori b a := by
  rw [G, SimpleGraph.fromRel_adj]
  refine and_iff_right_of_imp ?_
  rintro (h | h) rfl <;> unfold ori at h <;> omega


set_option maxRecDepth 10000 in
lemma geom : ∀v:V,v∈S1 v ∧ v∈S2 v ∧
    (∀w∈S1 v,w=v ∨ w=mate v) ∧ (∀w∈S2 v,w=v ∨ ori w (mate v) ∨ ori (mate v) w) := by decide +kernel
theorem separates (U:Finset V) (independent : ∀a∈U,∀b∈U,¬G.Adj a b) (v:V) (absent:v∉U) :
    ∃i:I,∃s:Bool,v∈arm i s ∧ Disjoint (arm i s) U := by
  obtain ⟨one,two,mem,adj⟩ := geom v
  by_cases h : mate v ∈ U
  · refine ⟨(B v).1,(B v).2,two,Finset.disjoint_left.mpr ?_⟩
    intro w hw hi
    rcases adj w hw with rfl|e
    · exact absent hi
    · exact independent w hi (mate v) h ((hemi _ _).mpr e)
  · refine ⟨(A v).1,(A v).2,one,Finset.disjoint_left.mpr ?_⟩
    intro w hw hi
    rcases mem w hw with rfl|rfl
    · exact absent hi
    · exact h hi

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem readers : (∀v:V,(read v).card=3) ∧
    ∀ p l:V, p.val<21 → 21≤l.val → ¬ori p l → (read p ∪ read l).card≤5 := by decide +kernel

def pt (p:Fin 21):V := Fin.castAdd 21 p
def ln (d p:Fin 21):V := Fin.natAdd 21 (p+d)
def maskHit (m:Nat) (d p:Fin 21) := m.testBit (pt p).val=true ∨ m.testBit (ln d p).val=true
instance (m:Nat)(d p:Fin 21):Decidable (maskHit m d p) := by unfold maskHit;infer_instance
def direct (i:I) (d p:Fin 21) := maskHit (left i) d p ∧ maskHit (right i) d p
instance (i:I)(d p:Fin 21):Decidable (direct i d p) := by unfold direct;infer_instance
def physical (i:I) (d p:Fin 21) :=
    (∃v∈C.leftVars i,v∈({pt p,ln d p}:Finset V)) ∧ ∃v∈C.rightVars i,v∈({pt p,ln d p}:Finset V)
lemma direct_iff (i:I) (d p:Fin 21) : direct i d p ↔ physical i d p := by
  simp only [physical,C,vertices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton,direct,maskHit]
  aesop
def D : Finset (Fin 21) := {0,5,7,17,20}
def owner (i:I) (d p:Fin 21) := physical i d p ∧ ∀j < i, ¬physical j d p
def repeated (i:I) := ∃d∈D,∃p q:Fin 21,p≠q ∧ owner i d p ∧ owner i d q
set_option maxRecDepth 10000 in
lemma complete : ∀d∈D,∀p:Fin 21,∃i:I,direct i d p := by decide +kernel
private def tuples : Array (Fin 21 × Fin 21 × Fin 21) := #[(7,0,7),(7,1,8),(7,2,9),(7,3,10),(7,4,11),(7,5,12),(7,6,13),(20,0,1)]
def triple (i:Fin 8) := tuples[i.val]?.getD (0,0,0)
lemma check : ∀j:Fin 8,let (d,p,q):=triple j
    d∈D ∧ p≠q ∧ (direct (Fin.castLE (by decide) j) d p ∧ ∀k < (Fin.castLE (show 8≤19 by decide) j),¬direct k d p)
      ∧ (direct (Fin.castLE (by decide) j) d q ∧ ∀k < (Fin.castLE (show 8≤19 by decide) j),¬direct k d q) := by decide +kernel
theorem eight (j:Fin 8) : repeated (Fin.castLE (by decide) j) := by
  have h := check j
  generalize triple j = a at h
  obtain ⟨d,p,q⟩ := a
  change d∈D ∧ p≠q ∧ _ ∧ _ at h
  exact ⟨d,h.1,p,q,h.2.1,⟨(direct_iff _ _ _).mp h.2.2.1.1,
    fun k hk ck => h.2.2.1.2 k hk ((direct_iff _ _ _).mpr ck)⟩,
    (direct_iff _ _ _).mp h.2.2.2.1,fun k hk ck => h.2.2.2.2 k hk ((direct_iff _ _ _).mpr ck)⟩
theorem wf : C.WellFormed ∧ ∀i,Disjoint (C.leftVars i) (C.rightVars i) := by
  constructor
  · unfold WellFormed
    decide +kernel
  · decide +kernel
end RawBank
