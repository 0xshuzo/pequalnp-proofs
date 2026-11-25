import PEqualNP.Outside.L_meta_4897
import PEqualNP.Outside.L_meta_7684

namespace Price9804
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
abbrev V := Fin 20
def listed : List (ℕ × ℕ) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]
def masks : Array Nat := #[0x200a1,0x40142,0x80286,0x50d,0xa18,0x1432,0x2864,0x50c8,0xa190,0x14320,0x28640,0x50c80,0xa1900,0x43201,0x86400,0xc803,0x19004,0x3200a,0x64014,0xc8028]
def incident (a b : V) := ((masks[a.val]?).getD 0).testBit b.val
def edges : Finset (V × V) := Finset.univ.filter (fun e => incident e.1 e.2)
def spec (x : Fin 40 → Bool) := ∃ u v : Fin 40, (u.val,v.val)∈listed ∧ x u=true ∧ x v=true

theorem incidence (a b : V) : (a,b)∈edges ↔ incident a b=true := by simp [edges]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem data : (∀ a b : V, incident a b=true ↔ (a.val,20+b.val)∈listed) ∧
    (∀ u v : Fin 40, (u.val,v.val)∈listed → u.val<20 ∧ 20≤v.val) ∧
    (∀ i : V, incident i i=true) ∧ edges.card=95 := by decide +kernel

def common (a c : V) : Finset V := Finset.univ.filter (fun b => incident a b && incident c b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem uniqueCard : ∀ a c : V, a≠c → (common a c).card≤1 := by decide +kernel

theorem linear (a c b d : V) (ac : a≠c) (bd : b≠d) :
    ¬((a,b)∈edges ∧ (a,d)∈edges ∧ (c,b)∈edges ∧ (c,d)∈edges) := by
  rintro ⟨ab,ad,cb,cd⟩
  have mem {j : V} (h1 : (a,j)∈edges) (h2 : (c,j)∈edges) : j∈common a c := by
    simp [common,(incidence _ _).mp h1,(incidence _ _).mp h2]
  exact bd (Finset.card_le_one.mp (uniqueCard a c ac) b (mem ab cb) d (mem ad cd))

theorem specEq (x : Fin 40 → Bool) :
    (∃ a b : V, (a,b)∈edges ∧ x (Fin.castAdd 20 a)=true ∧ x (Fin.natAdd 20 b)=true) ↔ spec x := by
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨Fin.castAdd 20 a, Fin.natAdd 20 b,(data.1 a b).mp ((incidence a b).mp ab),xa,xb⟩
  · rintro ⟨u,v,uv,xu,xv⟩
    obtain ⟨hu,hv⟩ := data.2.1 u v uv
    let a : V := ⟨u.val,hu⟩
    let b : V := ⟨v.val-20,by have := v.isLt; omega⟩
    have eqv : 20+(v.val-20)=v.val := by omega
    have eb : Fin.natAdd 20 b=v := Fin.ext eqv
    have mem : (a.val,20+b.val)∈listed := by
      change (u.val,20+(v.val-20))∈listed
      rwa [eqv]
    exact ⟨a,b,(incidence a b).mpr ((data.1 a b).mpr mem),xu,eb.symm ▸ xv⟩

theorem coverSize (A M : Finset V) (cover : ∀ e∈edges,e.1∈A ∨ e.2∈M) : 20≤A.card+M.card := by
  have sub : (Finset.univ : Finset V) ⊆ A∪M := by
    intro i _
    exact Finset.mem_union.mpr (cover (i,i) ((incidence i i).mpr (data.2.2.1 i)))
  simpa using (Finset.card_le_card sub).trans (Finset.card_union_le A M)

theorem lower (C : Circuit) (ao : IsAO2 40 C) (read : IsReadK 40 C 1)
    (correct : ∀ x : Fin 40 → Bool, C.eval (List.ofFn x)=true ↔ spec x) : 114≤C.size := by
  have eqn (x : Fin 40 → Bool) : circuitFun 40 C x = decide
      (∃ a b : V, (a,b)∈edges ∧ x (Fin.castAdd 20 a)=true ∧ x (Fin.natAdd 20 b)=true) := by
    apply Bool.eq_iff_iff.mpr
    change (C.eval (List.ofFn x)=true) ↔ _
    rw [decide_eq_true_eq]
    exact (correct x).trans (specEq x).symm
  obtain ⟨A,M,cover,cost⟩ := PEqualNP.Outside.L_meta_4897 20 20 edges C linear ao eqn read
  have matchSize := coverSize A M cover
  have ec := data.2.2.2
  omega

theorem upper : ∃ C : Circuit, Monotone2 C ∧ C.size≤114 ∧
    (∀ x : Fin 40 → Bool, C.eval (List.ofFn x)=true ↔ spec x) ∧ IsReadK 40 C 1 := by
  obtain ⟨C,ao,size,computed,read⟩ := PEqualNP.Outside.L_meta_7684 20 20 edges Finset.univ ∅
    (fun e _ => Or.inl (Finset.mem_univ e.1))
  refine ⟨C,?_,?_,?_,read⟩
  · intro g hg
    exact ⟨by simpa using ao.1 g hg, le_of_eq (ao.2.2 g hg)⟩
  · simpa [data.2.2.2] using size
  · intro x
    change circuitFun 40 C x=true ↔ _
    rw [computed x, decide_eq_true_eq]
    exact specEq x
end Price9804
