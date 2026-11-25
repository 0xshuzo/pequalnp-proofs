import PEqualNP.Outside.L_meta_4897
import PEqualNP.Outside.L_meta_7684

namespace Price9796
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
abbrev V := Fin 12
def listed : List (ℕ × ℕ) := [(0,12),(0,16),(0,22),(1,13),(1,17),(1,23),(2,12),(2,13),(2,14),(2,18),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,12),(8,17),(8,19),(8,20),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23)]
def masks : Array Nat := #[0x411,0x822,0x47,0x8c,0x11a,0x234,0x468,0x8d0,0x1a1,0x340,0x682,0xd04]
def incident (a b : V) := ((masks[a.val]?).getD 0).testBit b.val
def edges : Finset (V × V) := Finset.univ.filter (fun e => incident e.1 e.2)
def spec (x : Fin 24 → Bool) := ∃ u v : Fin 24, (u.val,v.val)∈listed ∧ x u=true ∧ x v=true

theorem incidence (a b : V) : (a,b)∈edges ↔ incident a b=true := by simp [edges]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem data : (∀ a b : V, incident a b=true ↔ (a.val,12+b.val)∈listed) ∧
    (∀ u v : Fin 24, (u.val,v.val)∈listed → u.val<12 ∧ 12≤v.val) ∧
    (∀ i : V, incident i i=true) ∧ edges.card=44 := by decide +kernel

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

theorem specEq (x : Fin 24 → Bool) :
    (∃ a b : V, (a,b)∈edges ∧ x (Fin.castAdd 12 a)=true ∧ x (Fin.natAdd 12 b)=true) ↔ spec x := by
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨Fin.castAdd 12 a, Fin.natAdd 12 b,(data.1 a b).mp ((incidence a b).mp ab),xa,xb⟩
  · rintro ⟨u,v,uv,xu,xv⟩
    obtain ⟨hu,hv⟩ := data.2.1 u v uv
    let a : V := ⟨u.val,hu⟩
    let b : V := ⟨v.val-12,by have := v.isLt; omega⟩
    have eqv : 12+(v.val-12)=v.val := by omega
    have eb : Fin.natAdd 12 b=v := Fin.ext eqv
    have mem : (a.val,12+b.val)∈listed := by
      change (u.val,12+(v.val-12))∈listed
      rwa [eqv]
    exact ⟨a,b,(incidence a b).mpr ((data.1 a b).mpr mem),xu,eb.symm ▸ xv⟩

theorem coverSize (A M : Finset V) (cover : ∀ e∈edges,e.1∈A ∨ e.2∈M) : 12≤A.card+M.card := by
  have sub : (Finset.univ : Finset V) ⊆ A∪M := by
    intro i _
    exact Finset.mem_union.mpr (cover (i,i) ((incidence i i).mpr (data.2.2.1 i)))
  simpa using (Finset.card_le_card sub).trans (Finset.card_union_le A M)

theorem lower (C : Circuit) (ao : IsAO2 24 C) (read : IsReadK 24 C 1)
    (correct : ∀ x : Fin 24 → Bool, C.eval (List.ofFn x)=true ↔ spec x) : 55≤C.size := by
  have eqn (x : Fin 24 → Bool) : circuitFun 24 C x = decide
      (∃ a b : V, (a,b)∈edges ∧ x (Fin.castAdd 12 a)=true ∧ x (Fin.natAdd 12 b)=true) := by
    apply Bool.eq_iff_iff.mpr
    change (C.eval (List.ofFn x)=true) ↔ _
    rw [decide_eq_true_eq]
    exact (correct x).trans (specEq x).symm
  obtain ⟨A,M,cover,cost⟩ := PEqualNP.Outside.L_meta_4897 12 12 edges C linear ao eqn read
  have matchSize := coverSize A M cover
  have ec := data.2.2.2
  omega

theorem upper : ∃ C : Circuit, Monotone2 C ∧ C.size≤55 ∧
    (∀ x : Fin 24 → Bool, C.eval (List.ofFn x)=true ↔ spec x) ∧ IsReadK 24 C 1 := by
  obtain ⟨C,ao,size,computed,read⟩ := PEqualNP.Outside.L_meta_7684 12 12 edges Finset.univ ∅
    (fun e _ => Or.inl (Finset.mem_univ e.1))
  refine ⟨C,?_,?_,?_,read⟩
  · intro g hg
    exact ⟨by simpa using ao.1 g hg, le_of_eq (ao.2.2 g hg)⟩
  · simpa [data.2.2.2] using size
  · intro x
    change circuitFun 24 C x=true ↔ _
    rw [computed x, decide_eq_true_eq]
    exact specEq x
end Price9796
