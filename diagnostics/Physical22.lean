import PEqualNP.Outside.L_meta_5670
import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9753.Paid
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_5670
open PEqualNP.Outside.L_meta_5670.Heawood
open PEqualNP.Outside.L_meta_9752.Engine

def packet : (Fin 14 → Bool) → Bool := fun x : Fin 14 → Bool => (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def assignmentMap : Fin 14 → Fin 14 := ![0, 1, 4, 3, 2, 6, 5, 7, 11, 12, 13, 9, 10, 8]
def deleteMap : Fin 14 → Fin 12 := ![0, 0, 2, 1, 0, 4, 3, 5, 11, 9, 10, 6, 7, 8]
def coreMap : Fin 14 → Fin 11 := ![0, 5, 9, 7, 10, 6, 8, 0, 0, 3, 2, 0, 4, 0]
theorem packetMap (x) : packet (x ∘ assignmentMap) = f x := by
  change (x 0 && x 7) || (x 0 && x 11) || (x 0 && x 13) || (x 1 && x 7) || (x 1 && x 12) || (x 1 && x 8) || (x 4 && x 11) || (x 4 && x 10) || (x 4 && x 8) || (x 3 && x 7) || (x 3 && x 9) || (x 3 && x 10) || (x 2 && x 13) || (x 2 && x 9) || (x 2 && x 8) || (x 6 && x 12) || (x 6 && x 13) || (x 6 && x 10) || (x 5 && x 11) || (x 5 && x 12) || (x 5 && x 9) = (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 5 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 6 && x 10) || (x 0 && x 11) || (x 4 && x 11) || (x 5 && x 11) || (x 1 && x 12) || (x 5 && x 12) || (x 6 && x 12) || (x 0 && x 13) || (x 2 && x 13) || (x 6 && x 13)
  ac_rfl

abbrev cut0 := pinF f 0 false
abbrev cut01 := pinF cut0 1 false
theorem deleted (x) : cut01 (x ∘ deleteMap)=PEqualNP.Outside.L_meta_9752.Physical.f x := by
  change (false && x 5) || (false && x 5) || (x 1 && x 5) || (false && x 11) || (x 2 && x 11) || (x 0 && x 11) || (x 2 && x 9) || (x 1 && x 9) || (x 4 && x 9) || (x 1 && x 10) || (x 0 && x 10) || (x 3 && x 10) || (false && x 6) || (x 0 && x 6) || (x 4 && x 6) || (false && x 7) || (x 4 && x 7) || (x 3 && x 7) || (false && x 8) || (x 2 && x 8) || (x 3 && x 8) = (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
  simp only [Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
theorem zeroLower : LB cut0 20 := by
  refine payOne _ 1 false 18 ⟨one 7,by decide⟩ ⟨fun _ => false,leafEdge 2 8,by decide⟩ ?_
  intro n h
  have lower := Base.PermInputs.relabel_size deleteMap cut01 n h
  have mapped : (fun x => cut01 (x ∘ deleteMap))=PEqualNP.Outside.L_meta_9752.Physical.f := funext deleted
  rw [mapped] at lower
  by_contra! bad
  obtain ⟨C,legal,size,ev⟩ := lower
  exact PEqualNP.Outside.L_meta_9752 ⟨C,legal,by omega,ev⟩
abbrev cut1 := pinF f 0 true
abbrev fix1 := pinF cut1 7 false
abbrev fix2 := pinF fix1 11 false
abbrev fix3 := pinF fix2 13 false

def screen : List Sig := List.ofFn (fun i : Fin 14 => inputs.getD (coreMap i).val zero)
def inputAt (r : Row) (i : Fin 14) : Bool := bit r (inputs.getD (coreMap i).val zero)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem mainRows : ∀r, fix3 (inputAt r)=bit r (graphGoal 2045) := by decide +kernel
theorem availableScreen : ∀ a ∈ screen.map (nrm true), a∈varsX 2045 := by
  have checked : (screen.map (nrm true)).all (fun a => (varsX 2045).contains a)=true := by decide +kernel
  intro a ha
  simpa using (List.all_eq_true.mp checked a ha)
theorem coreLower : LB fix3 15 := by
  classical
  rintro n ⟨C,legal,size,ev⟩
  have pg : proper (graphGoal 2045) := by unfold proper; decide +kernel
  have outEq : (execute C.gates screen).getD C.output zero=graphGoal 2045 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates screen).getD C.output zero) = bit r (graphGoal 2045)
    have sampleEq : screen.map (bit r) = List.ofFn (inputAt r) := by
      rw [screen,List.map_ofFn]
      rfl
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),sampleEq]
    exact (ev (inputAt r)).trans (mainRows r)
  have represented := get_rep (u:=true) (execute C.gates screen) C.output
  rw [outEq] at represented
  unfold PEqualNP.Outside.L_meta_9752.Engine.Repr at represented
  rw [nrm_id (by decide +kernel : bit 0 (graphGoal 2045)=false)] at represented
  obtain ⟨k,S,le,live,sub⟩ := extract C.gates screen legal (fun bad => Bool.noConfusion bad) pg (represented.resolve_right (fun h => h pg))
  have run := list_run live S.toList (Finset.nodup_toList _) (by simp)
  have supp : supply true ((varsX 2045).map observe) (S.toList.map observe) := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact Or.inl (List.mem_map.mpr ⟨a,availableScreen a (sub a (Finset.mem_toList.mp ha)),rfl⟩)
  obtain ⟨t,ws,reachable,goal,score⟩ := contraction (observe_proper pg) run _ (p:=0) Reach.start supp
  have bound : 15≤t := h4061_15 t ws reachable goal
  have cnt : C.gates.countP (fun g => !isNot g) ≤ C.gates.length := List.countP_le_length
  change C.gates.length ≤ n at size
  omega
theorem oneLower : LB cut1 18 := by
  refine payOne _ 7 false 16 ⟨fun _ => false,by decide⟩ ⟨fun _ => false,leafEdge 1 8,by decide⟩ ?_
  refine payOne _ 11 false 15 ⟨fun _ => false,by decide⟩ ⟨fun _ => false,leafEdge 1 8,by decide⟩ ?_
  refine payOne _ 13 false 14 ⟨fun _ => false,by decide⟩ ⟨fun _ => false,leafEdge 1 8,by decide⟩ ?_
  exact coreLower
theorem donor22 : LB f 22 := by
  intro n h
  rcases Base.readerTheorem 13 f n depends_some (fun p _ b => fixing_nonconstant p b)
      (fun p q hpq _ _ => no_funnel p q hpq) h with ⟨p,t,ht,hc⟩ | ⟨p,t,ht,hc⟩
  · have bound := zeroLower t (normalizePin p false t hc)
    omega
  · have bound := oneLower t (normalizePin p true t hc)
    omega
theorem physical22 (n : Nat) (h : HasCircuitSize 14 packet n) : 22≤n := by
  have other := Base.PermInputs.relabel_size assignmentMap packet n h
  have eq : (fun x => packet (x ∘ assignmentMap))=f := funext packetMap
  rw [eq] at other
  exact donor22 n other
end PEqualNP.Outside.L_meta_9753.Paid
