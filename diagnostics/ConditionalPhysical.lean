import PEqualNP.Outside.L_meta_9825
import PEqualNP.Outside.L_meta_9785
namespace PEqualNP.Outside.L_meta_9822.ExactBridge
open PEqualNP.Outside.L_meta_9825.Engine
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def natPack : List Nat → Nat
  | [] => 0
  | x::xs => x + (natPack xs <<< 56)
def goal : Sig := (BitVec.ofNat 1024 (natPack [66123439587115200,67253827447606527,72057572310450158,72056481591066623,66146348944064511,72057594037927935,67835469387268095,72057594037926655,72057594037927935,66123529778675967,72057594037927935,72057594037927935,72057594037927935,71988324805378047,72057594037927935,72057594037927935,72057594037927935,72057594037927935,65535]))
open PEqualNP.CircuitLowerBounds
def graphFn (x : Fin 10 → Bool) := (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem goal_eq : ∀ r : Row, bit r goal=graphFn (sample r) := by decide +kernel
theorem proper_goal : proper goal := by unfold proper; decide +kernel
def neighbor (i : Fin 10) : Nat := [4,2,1,4,0,0,1,2,3,4].getD i.val 0
def absent (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor i)
def present (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< neighbor i) ||| (1 <<< i.val))
theorem required :
    (∀ i : Fin 10, bit (absent i) goal ≠ bit (present i) goal) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absent i) (inputs.getD j.val zero)=bit (present i) (inputs.getD j.val zero)) := by
  decide +kernel
def edges : List (Nat × Nat) := [(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
theorem listSpec (x : Fin 10 → Bool) :
    graphFn x = true ↔ ∃ u v : Fin 10, (u.val,v.val) ∈ edges ∧ x u=true ∧ x v=true := by
  constructor
  · intro h
    simp only [graphFn,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
    · exact ⟨1,2,by decide,h.1,h.2⟩
    · exact ⟨3,4,by decide,h.1,h.2⟩
    · exact ⟨0,4,by decide,h.1,h.2⟩
    · exact ⟨0,5,by decide,h.1,h.2⟩
    · exact ⟨1,6,by decide,h.1,h.2⟩
    · exact ⟨2,7,by decide,h.1,h.2⟩
    · exact ⟨3,8,by decide,h.1,h.2⟩
    · exact ⟨4,9,by decide,h.1,h.2⟩
    · exact ⟨5,7,by decide,h.1,h.2⟩
    · exact ⟨7,9,by decide,h.1,h.2⟩
    · exact ⟨6,9,by decide,h.1,h.2⟩
    · exact ⟨6,8,by decide,h.1,h.2⟩
    · exact ⟨5,8,by decide,h.1,h.2⟩
  · rintro ⟨u,v,hm,hu,hv⟩
    simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h
    · have a : u=(1:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(2:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(3:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(4:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(0:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(4:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(0:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(5:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(1:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(6:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(2:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(7:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(3:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(8:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(4:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(9:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(5:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(7:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(7:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(9:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(6:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(9:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(6:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(8:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
    · have a : u=(5:Fin 10) := Fin.ext (congrArg Prod.fst h)
      have b : v=(8:Fin 10) := Fin.ext (congrArg Prod.snd h)
      subst u; subst v
      simp [graphFn,hu,hv]
theorem physical (root : Impossible true goal 16 inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 graphFn 17 := by
  rintro ⟨C,legal,small,computes⟩
  by_cases all : ∀ g ∈ C.gates, isNot g = false
  · apply PEqualNP.Outside.L_meta_9785
    refine ⟨C,?_,small,?_⟩
    · intro g hg
      have hp := (legal g hg).1
      have hn := all g hg
      refine ⟨?_,(legal g hg).2⟩
      cases h : g.op <;> simp_all [isNot]
    · intro x
      rw [computes x]
      exact listSpec x
  · have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      by_contra! n
      apply all
      intro g hg
      have h := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length n) g hg
      simpa using h
    have goalEq : (execute C.gates inputs).getD C.output zero = goal := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      let r : Row := ⟨j,hj⟩
      exact (table_eval C legal C.output r).trans ((computes (sample r)).trans (goal_eq r).symm)
    have out := get_rep (u:=true) (execute C.gates inputs) C.output
    rw [goalEq] at out
    unfold Repr at out
    have pg : bit 0 goal = false := by decide +kernel
    rw [nrm_id pg] at out
    obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal (u:=true) (by simp) proper_goal
      (out.resolve_right (fun h => h proper_goal))
    have ns : inputs.all plainWord = true := by decide +kernel
    rw [nrm_map ns] at sub
    have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
      rw [←input_list] at ha
      exact List.mem_ofFn.mp ha
    have eq : S = inputs.toFinset := by
      ext a
      constructor
      · exact fun h => List.mem_toFinset.mpr (sub a h)
      · intro ha
        obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
        apply raw_required run inputs (inputs.getD i.val zero) sub (absent i) (present i) (required.1 i)
        intro v hv hn
        obtain ⟨j,rfl⟩ := idx v hv
        apply required.2 i j
        rintro rfl
        exact hn rfl
    have len : C.gates.length ≤ 17 := small
    exact root k (by omega) (eq ▸ run)
end PEqualNP.Outside.L_meta_9822.ExactBridge
