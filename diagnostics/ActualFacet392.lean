import PEqualNP.Outside.L_meta_9825
namespace PEqualNP.Outside.L_meta_9822.FoldedSample
open PEqualNP.Outside.L_meta_9825.Engine
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def natPack : List Nat → Nat
  | [] => 0
  | x::xs => x + (natPack xs <<< 56)
def goal : Sig := (BitVec.ofNat 1024 (natPack [66123439587115200,67253827447606527,72057572310450158,72056481591066623,66146348944064511,72057594037927935,67835469387268095,72057594037926655,72057594037927935,66123529778675967,72057594037927935,72057594037927935,72057594037927935,71988324805378047,72057594037927935,72057594037927935,72057594037927935,72057594037927935,65535]))
def aliasRows (j i : Nat) (phase : Bool) : Move :=
  let a := inputs.getD j zero
  let b := if phase then neg (inputs.getD i zero) else inputs.getD i zero
  (b &&& ~~~a,a &&& ~~~b,Fin.ofNat 1024 (1 <<< j))
def dom : Sig := subcube 256 0 &&& ~~~((inputs.getD 6 zero) ^^^ (inputs.getD 4 zero))
def into : List Move := fixRows 256 0 ++ [aliasRows 6 4 false]
def folded : Sig := movedWord into goal
theorem signedFree {base : List Sig} {w : Sig}
    (h : (freeWord base w || freeWord base (neg w)) = true) :
    Available true (base.map observe) (observe w) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact freeWord_ok h
  · have negAvail : Available true (base.map observe) (observe (neg w)) := freeWord_ok h
    have h' := avail_inv rfl negAvail
    rw [←obs_neg,neg_neg'] at h'
    exact h'
def paidMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a) || freeWord base (neg (movedWord ms a)))
theorem paidSlice {ms raw T base G L d} (ok : paidMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower true base G L) :
    Slice true raw T d L := by
  simp only [paidMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe ok.1)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact signedFree (ok.2 a ha)
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL
def toDonor : List Move := [49].map swapRows ++ fixRows 8 0
def ess : List (Sig × Row × Row) := [(inputs.getD 3 zero,16,24)]
theorem foldLower : Lower true (varsX 703) folded 12 := by
  have h := lift_ok (u:=true) (ms:=toDonor) (T:=folded) (raw:=varsX 703) (base:=varsX 701) (G:=graphGoal 701) (xs:=ess)
      (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) h701_11
  exact lowerHint h (by decide +kernel)
theorem actual392 : Slice true inputs goal dom 12 :=
  paidSlice (ms:=into) (base:=varsX 703) (G:=folded) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide +kernel)) foldLower
end PEqualNP.Outside.L_meta_9822.FoldedSample
