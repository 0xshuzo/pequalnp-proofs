import PEqualNP.Outside.L_meta_4897
import PEqualNP.Outside.L_meta_7684

namespace Price9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
abbrev P := Fin 13
abbrev L := Fin 13
def listed : List (ℕ × ℕ) := [(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
def masks : Array Nat := #[0x1410,0x823,0x1046,0x8d,0x11a,0x234,0x468,0x8d0,0x11a0,0x341,0x682,0xd04,0x1a08]
def matchPoint (i : L) : P := ![9,1,2,3,4,5,6,8,11,12,10,7,0] i
def incident (a : P) (b : L) := ((masks[a.val]?).getD 0).testBit b.val
def edges : Finset (P × L) := Finset.univ.filter (fun e => incident e.1 e.2)
def spec (x : Fin 26 → Bool) := ∃ u v : Fin 26, (u.val,v.val)∈listed ∧ x u=true ∧ x v=true

theorem incidence (a : P) (b : L) : (a,b)∈edges ↔ incident a b=true := by simp [edges]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem data : (∀ (a : P) (b : L), incident a b=true ↔ (a.val,13+b.val)∈listed) ∧
    (∀ u v : Fin 26, (u.val,v.val)∈listed → u.val<13 ∧ 13≤v.val) ∧
    (∀ i : L, incident (matchPoint i) i=true) ∧ edges.card=51 := by decide +kernel

def common (a c : P) : Finset L := Finset.univ.filter (fun b => incident a b && incident c b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem uniqueCard : ∀ a c : P, a≠c → (common a c).card≤1 := by decide +kernel

theorem linear (a c : P) (b d : L) (ac : a≠c) (bd : b≠d) :
    ¬((a,b)∈edges ∧ (a,d)∈edges ∧ (c,b)∈edges ∧ (c,d)∈edges) := by
  rintro ⟨ab,ad,cb,cd⟩
  have mem {j : L} (h1 : (a,j)∈edges) (h2 : (c,j)∈edges) : j∈common a c := by
    simp [common,(incidence _ _).mp h1,(incidence _ _).mp h2]
  exact bd (Finset.card_le_one.mp (uniqueCard a c ac) b (mem ab cb) d (mem ad cd))

theorem specEq (x : Fin 26 → Bool) :
    (∃ (a : P) (b : L), (a,b)∈edges ∧ x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true) ↔ spec x := by
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨Fin.castAdd 13 a, Fin.natAdd 13 b,(data.1 a b).mp ((incidence a b).mp ab),xa,xb⟩
  · rintro ⟨u,v,uv,xu,xv⟩
    obtain ⟨hu,hv⟩ := data.2.1 u v uv
    let a : P := ⟨u.val,hu⟩
    let b : L := ⟨v.val-13,by have := v.isLt; omega⟩
    have eqv : 13+(v.val-13)=v.val := by omega
    have eb : Fin.natAdd 13 b=v := Fin.ext eqv
    have mem : (a.val,13+b.val)∈listed := by
      change (u.val,13+(v.val-13))∈listed
      rwa [eqv]
    exact ⟨a,b,(incidence a b).mpr ((data.1 a b).mpr mem),xu,eb.symm ▸ xv⟩

theorem coverSize (A : Finset P) (M : Finset L) (cover : ∀ e∈edges,e.1∈A ∨ e.2∈M) :
    13≤A.card+M.card := by
  let S : Finset L := Finset.univ.filter (fun i => matchPoint i ∈ A)
  have sub : (Finset.univ : Finset L) ⊆ S∪M := by
    intro i _
    have hi := cover (matchPoint i,i) ((incidence _ _).mpr (data.2.2.1 i))
    rcases hi with h|h
    · exact Finset.mem_union_left M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right S h
  have inj : ∀ i j : L, matchPoint i=matchPoint j → i=j := by decide +kernel
  have nS : S.card≤A.card := Finset.card_le_card_of_injOn matchPoint
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun i _ j _ h => inj i j h)
  have size : 13≤S.card+M.card := by
    simpa using (Finset.card_le_card sub).trans (Finset.card_union_le S M)
  omega

theorem lower (C : Circuit) (ao : IsAO2 26 C) (read : IsReadK 26 C 1)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ spec x) : 63≤C.size := by
  have eqn (x : Fin 26 → Bool) : circuitFun 26 C x = decide
      (∃ (a : P) (b : L), (a,b)∈edges ∧ x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true) := by
    apply Bool.eq_iff_iff.mpr
    change (C.eval (List.ofFn x)=true) ↔ _
    rw [decide_eq_true_eq]
    exact (correct x).trans (specEq x).symm
  obtain ⟨A,M,cover,cost⟩ := PEqualNP.Outside.L_meta_4897 13 13 edges C linear ao eqn read
  have matchSize := coverSize A M cover
  have ec := data.2.2.2
  omega

theorem upper : ∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ spec x) ∧ IsReadK 26 C 1 := by
  obtain ⟨C,ao,size,computed,read⟩ := PEqualNP.Outside.L_meta_7684 13 13 edges ∅ Finset.univ
    (fun e _ => Or.inr (Finset.mem_univ e.2))
  refine ⟨C,?_,?_,?_,read⟩
  · intro g hg
    exact ⟨by simpa using ao.1 g hg, le_of_eq (ao.2.2 g hg)⟩
  · simpa [data.2.2.2] using size
  · intro x
    change circuitFun 26 C x=true ↔ _
    rw [computed x, decide_eq_true_eq]
    exact specEq x
end Price9742
