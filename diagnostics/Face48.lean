import PEqualNP.Outside.L_meta_5670
import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9753.Paid
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_5670
open PEqualNP.Outside.L_meta_5670.Heawood
open PEqualNP.Outside.L_meta_9752.Engine

private def leafEdge (p q : Fin 14) : Fin 14 → Bool := fun i => decide (i=p ∨ i=q)

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

def packet : (Fin 14 → Bool) → Bool := fun x : Fin 14 → Bool => (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def assignmentMap : Fin 14 → Fin 14 := ![0, 1, 4, 3, 2, 6, 5, 7, 11, 12, 13, 9, 10, 8]
def deleteMap : Fin 14 → Fin 12 := ![0, 0, 2, 1, 0, 4, 3, 5, 11, 9, 10, 6, 7, 8]
def coreMap : Fin 14 → Fin 11 := ![0, 5, 9, 7, 10, 6, 8, 0, 0, 3, 2, 0, 4, 0]
theorem packetMap (x) : packet (x ∘ assignmentMap) = f x := by
  change ((x 0 && x 7) || (x 0 && x 11) || (x 0 && x 13) || (x 1 && x 7) || (x 1 && x 12) || (x 1 && x 8) || (x 4 && x 11) || (x 4 && x 10) || (x 4 && x 8) || (x 3 && x 7) || (x 3 && x 9) || (x 3 && x 10) || (x 2 && x 13) || (x 2 && x 9) || (x 2 && x 8) || (x 6 && x 12) || (x 6 && x 13) || (x 6 && x 10) || (x 5 && x 11) || (x 5 && x 12) || (x 5 && x 9)) = ((x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 5 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 6 && x 10) || (x 0 && x 11) || (x 4 && x 11) || (x 5 && x 11) || (x 1 && x 12) || (x 5 && x 12) || (x 6 && x 12) || (x 0 && x 13) || (x 2 && x 13) || (x 6 && x 13))
  ac_rfl

abbrev cut0 := pinF f 0 false
abbrev cut01 := pinF cut0 1 false
theorem deleted (x) : cut01 (x ∘ deleteMap)=PEqualNP.Outside.L_meta_9752.Physical.f x := by
  change ((false && x 5) || (false && x 5) || (x 1 && x 5) || (false && x 11) || (x 2 && x 11) || (x 0 && x 11) || (x 2 && x 9) || (x 1 && x 9) || (x 4 && x 9) || (x 1 && x 10) || (x 0 && x 10) || (x 3 && x 10) || (false && x 6) || (x 0 && x 6) || (x 4 && x 6) || (false && x 7) || (x 4 && x 7) || (x 3 && x 7) || (false && x 8) || (x 2 && x 8) || (x 3 && x 8)) = ((x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9))
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

namespace Fano9838


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9752.Physical
private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => w.getD j false)
private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value g w]
private def AgreeAway (a b : List Bool) : Prop :=
  a.length = b.length ∧ 0 < b.length ∧
    ∀ j, j ≠ 0 → a.getD j false = b.getD j false
private theorem unread_value (g : Gate) (a b : List Bool) (near : AgreeAway a b)
    (_legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h : reads 0 g = false) : value g a = value g b := by
  unfold value
  rw [← normGate_eval g (fun i => a.getD i false), ← normGate_eval g (fun i => b.getD i false)]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply near.2.2 j
  rintro rfl
  have yes : reads 0 g = true := List.contains_iff_mem.mpr hj
  simp [h] at yes
private theorem step_agree (a b : List Bool) (g : Gate) (near : AgreeAway a b)
    (same : value g a = value g b) : AgreeAway (step a g) (step b g) := by
  obtain ⟨length, bound, eq⟩ := near
  refine ⟨by simp [step,length], by simp [step], ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [step, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),length,same]
private theorem fold_agree (p : List Gate) (a b : List Bool)
    (near : AgreeAway a b) (fan : FanInTwo ⟨p, 0⟩) (silent : ∀ g ∈ p, reads 0 g = false) :
    AgreeAway (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact near
  | cons g p ih =>
    exact ih _ _ (step_agree a b g near (unread_value g a b near (fan g (by simp)).1 (silent g (by simp))))
      (fun k hk => fan k (by simp [hk])) (fun k hk => silent k (by simp [hk]))
set_option maxRecDepth 16000

private theorem paid_pin {n m k : ℕ} (f : (Fin n → Bool) → Bool)
    (g : (Fin m → Bool) → Bool) (bank : List (Option (Fin m)))
    (probe : Bool → Fin n → Bool) (raw : Fin n → Bool)
    (positive : 0 < n) (different : (List.ofFn raw).getD 0 false ≠ f raw)
    (separate : f (probe false) ≠ f (probe true))
    (agree : ∀ i : Fin n, i.val ≠ 0 →
      (List.ofFn (probe false)).getD i.val false = (List.ofFn (probe true)).getD i.val false)
    (absent : bank[0]? = some none)
    (lift : (Fin m → Bool) → Fin n → Bool)
    (layoutEq : ∀ y, restrict bank y = List.ofFn (lift y))
    (restricted : ∀ y, f (lift y) = g y)
    (hasFalse : g (fun _ => false) = false)
    (core : ¬ HasCircuitSize m g k) : ¬ HasCircuitSize n f (k+1) := by
  rintro ⟨C,fan,small,ev⟩
  have rawOut : C.output ≠ 0 := by
    intro eq
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn raw)
    have h := ev raw
    change (wiresFrom C.gates (List.ofFn raw)).getD C.output false = f raw at h
    rw [eq, ht, List.getD_append _ _ _ _ (by simpa using positive : 0 < (List.ofFn raw).length)] at h
    exact different h
  have positiveUse : 0 < C.gates.countP (reads 0) := by
    by_contra! no
    have silent : ∀ a ∈ C.gates, reads 0 a = false := by
      intro a ha
      by_contra! h
      have yes : reads 0 a = true := by cases e : reads 0 a <;> simp_all
      have pos : 0 < C.gates.countP (reads 0) := List.countP_pos_iff.mpr ⟨a,ha,yes⟩
      omega
    have near : AgreeAway (List.ofFn (probe false)) (List.ofFn (probe true)) := by
      refine ⟨by simp, by simpa using positive, ?_⟩
      intro j diff
      by_cases h : j < n
      · exact agree ⟨j,h⟩ diff
      · have past (b : Bool) : (List.ofFn (probe b)).length ≤ j := by rw [List.length_ofFn]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
    have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output rawOut
    change C.eval (List.ofFn (probe false)) = C.eval (List.ofFn (probe true)) at same
    rw [ev,ev] at same
    exact separate same
  have rest (y) : C.eval (restrict bank y) = g y :=
    (layoutEq y) ▸ ((ev (lift y)).trans (restricted y))
  obtain ⟨D,legal,cost,table⟩ := eliminate_pin bank 0 C fan absent
    ⟨fun _ => false, (rest _).trans hasFalse⟩
  exact core ⟨D,legal,by omega,fun y => (table y).trans (rest y)⟩

def f14 (x : Fin 14 → Bool) : Bool := (x 0 && x 7) || (x 0 && x 10) || (x 0 && x 8) || (x 1 && x 7) || (x 1 && x 13) || (x 1 && x 9) || (x 2 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 13) || (x 4 && x 11) || (x 4 && x 10) || (x 6 && x 11) || (x 6 && x 8) || (x 6 && x 9) || (x 5 && x 10) || (x 5 && x 9) || (x 5 && x 12)
def f15 (x : Fin 15 → Bool) : Bool := (x 1 && x 8) || (x 1 && x 11) || (x 1 && x 9) || (x 2 && x 8) || (x 2 && x 14) || (x 2 && x 10) || (x 3 && x 14) || (x 3 && x 9) || (x 3 && x 13) || (x 0 && x 10) || (x 4 && x 8) || (x 4 && x 12) || (x 4 && x 13) || (x 5 && x 14) || (x 5 && x 12) || (x 5 && x 11) || (x 7 && x 12) || (x 7 && x 9) || (x 7 && x 10) || (x 6 && x 11) || (x 6 && x 10) || (x 6 && x 13)
def f16 (x : Fin 16 → Bool) : Bool := (x 2 && x 9) || (x 2 && x 12) || (x 2 && x 10) || (x 3 && x 9) || (x 3 && x 15) || (x 3 && x 11) || (x 4 && x 15) || (x 4 && x 10) || (x 4 && x 14) || (x 1 && x 11) || (x 5 && x 9) || (x 5 && x 13) || (x 5 && x 14) || (x 6 && x 15) || (x 6 && x 13) || (x 6 && x 12) || (x 0 && x 12) || (x 8 && x 13) || (x 8 && x 10) || (x 8 && x 11) || (x 7 && x 12) || (x 7 && x 11) || (x 7 && x 14)
def f17 (x : Fin 17 → Bool) : Bool := (x 3 && x 10) || (x 3 && x 13) || (x 3 && x 11) || (x 4 && x 10) || (x 4 && x 16) || (x 4 && x 12) || (x 5 && x 16) || (x 5 && x 11) || (x 5 && x 15) || (x 2 && x 12) || (x 6 && x 10) || (x 6 && x 14) || (x 6 && x 15) || (x 7 && x 16) || (x 7 && x 14) || (x 7 && x 13) || (x 1 && x 13) || (x 0 && x 11) || (x 9 && x 14) || (x 9 && x 11) || (x 9 && x 12) || (x 8 && x 13) || (x 8 && x 12) || (x 8 && x 15)
def f18 (x : Fin 18 → Bool) : Bool := (x 4 && x 11) || (x 4 && x 14) || (x 4 && x 12) || (x 5 && x 11) || (x 5 && x 17) || (x 5 && x 13) || (x 6 && x 17) || (x 6 && x 12) || (x 6 && x 16) || (x 3 && x 13) || (x 7 && x 11) || (x 7 && x 15) || (x 7 && x 16) || (x 8 && x 17) || (x 8 && x 15) || (x 8 && x 14) || (x 2 && x 14) || (x 1 && x 12) || (x 10 && x 15) || (x 10 && x 12) || (x 10 && x 13) || (x 9 && x 14) || (x 9 && x 13) || (x 9 && x 16) || (x 0 && x 16)
def f19 (x : Fin 19 → Bool) : Bool := (x 5 && x 12) || (x 5 && x 15) || (x 5 && x 13) || (x 6 && x 12) || (x 6 && x 18) || (x 6 && x 14) || (x 7 && x 18) || (x 7 && x 13) || (x 7 && x 17) || (x 4 && x 14) || (x 8 && x 12) || (x 8 && x 16) || (x 8 && x 17) || (x 9 && x 18) || (x 9 && x 16) || (x 9 && x 15) || (x 3 && x 15) || (x 2 && x 13) || (x 11 && x 16) || (x 11 && x 13) || (x 11 && x 14) || (x 10 && x 15) || (x 10 && x 14) || (x 10 && x 17) || (x 1 && x 17) || (x 0 && x 13)
def f20 (x : Fin 20 → Bool) : Bool := (x 6 && x 13) || (x 6 && x 16) || (x 6 && x 14) || (x 7 && x 13) || (x 7 && x 19) || (x 7 && x 15) || (x 8 && x 19) || (x 8 && x 14) || (x 8 && x 18) || (x 5 && x 15) || (x 9 && x 13) || (x 9 && x 17) || (x 9 && x 18) || (x 10 && x 19) || (x 10 && x 17) || (x 10 && x 16) || (x 4 && x 16) || (x 3 && x 14) || (x 12 && x 17) || (x 12 && x 14) || (x 12 && x 15) || (x 11 && x 16) || (x 11 && x 15) || (x 11 && x 18) || (x 2 && x 18) || (x 1 && x 14) || (x 0 && x 15)
def f21 (x : Fin 21 → Bool) : Bool := (x 7 && x 14) || (x 7 && x 17) || (x 7 && x 15) || (x 8 && x 14) || (x 8 && x 20) || (x 8 && x 16) || (x 9 && x 20) || (x 9 && x 15) || (x 9 && x 19) || (x 6 && x 16) || (x 10 && x 14) || (x 10 && x 18) || (x 10 && x 19) || (x 11 && x 20) || (x 11 && x 18) || (x 11 && x 17) || (x 5 && x 17) || (x 4 && x 15) || (x 13 && x 18) || (x 13 && x 15) || (x 13 && x 16) || (x 12 && x 17) || (x 12 && x 16) || (x 12 && x 19) || (x 3 && x 19) || (x 2 && x 15) || (x 1 && x 16) || (x 0 && x 19)
def f22 (x : Fin 22 → Bool) : Bool := (x 8 && x 15) || (x 8 && x 18) || (x 8 && x 16) || (x 9 && x 15) || (x 9 && x 21) || (x 9 && x 17) || (x 10 && x 21) || (x 10 && x 16) || (x 10 && x 20) || (x 7 && x 17) || (x 11 && x 15) || (x 11 && x 19) || (x 11 && x 20) || (x 12 && x 21) || (x 12 && x 19) || (x 12 && x 18) || (x 6 && x 18) || (x 5 && x 16) || (x 14 && x 19) || (x 14 && x 16) || (x 14 && x 17) || (x 13 && x 18) || (x 13 && x 17) || (x 13 && x 20) || (x 4 && x 20) || (x 3 && x 16) || (x 2 && x 17) || (x 1 && x 20) || (x 0 && x 15)
def f23 (x : Fin 23 → Bool) : Bool := (x 9 && x 16) || (x 9 && x 19) || (x 9 && x 17) || (x 10 && x 16) || (x 10 && x 22) || (x 10 && x 18) || (x 11 && x 22) || (x 11 && x 17) || (x 11 && x 21) || (x 8 && x 18) || (x 12 && x 16) || (x 12 && x 20) || (x 12 && x 21) || (x 13 && x 22) || (x 13 && x 20) || (x 13 && x 19) || (x 7 && x 19) || (x 6 && x 17) || (x 15 && x 20) || (x 15 && x 17) || (x 15 && x 18) || (x 14 && x 19) || (x 14 && x 18) || (x 14 && x 21) || (x 5 && x 21) || (x 4 && x 17) || (x 3 && x 18) || (x 2 && x 21) || (x 1 && x 16) || (x 0 && x 22)
def f24 (x : Fin 24 → Bool) : Bool := (x 10 && x 17) || (x 10 && x 20) || (x 10 && x 18) || (x 11 && x 17) || (x 11 && x 23) || (x 11 && x 19) || (x 12 && x 23) || (x 12 && x 18) || (x 12 && x 22) || (x 9 && x 19) || (x 13 && x 17) || (x 13 && x 21) || (x 13 && x 22) || (x 14 && x 23) || (x 14 && x 21) || (x 14 && x 20) || (x 8 && x 20) || (x 7 && x 18) || (x 16 && x 21) || (x 16 && x 18) || (x 16 && x 19) || (x 15 && x 20) || (x 15 && x 19) || (x 15 && x 22) || (x 6 && x 22) || (x 5 && x 18) || (x 4 && x 19) || (x 3 && x 22) || (x 2 && x 17) || (x 1 && x 23) || (x 0 && x 17)
def f25 (x : Fin 25 → Bool) : Bool := (x 11 && x 18) || (x 11 && x 21) || (x 11 && x 19) || (x 12 && x 18) || (x 12 && x 24) || (x 12 && x 20) || (x 13 && x 24) || (x 13 && x 19) || (x 13 && x 23) || (x 10 && x 20) || (x 14 && x 18) || (x 14 && x 22) || (x 14 && x 23) || (x 15 && x 24) || (x 15 && x 22) || (x 15 && x 21) || (x 9 && x 21) || (x 8 && x 19) || (x 17 && x 22) || (x 17 && x 19) || (x 17 && x 20) || (x 16 && x 21) || (x 16 && x 20) || (x 16 && x 23) || (x 7 && x 23) || (x 6 && x 19) || (x 5 && x 20) || (x 4 && x 23) || (x 3 && x 18) || (x 2 && x 24) || (x 1 && x 18) || (x 0 && x 24)
def f26 (x : Fin 26 → Bool) : Bool := (x 12 && x 19) || (x 12 && x 22) || (x 12 && x 20) || (x 13 && x 19) || (x 13 && x 25) || (x 13 && x 21) || (x 14 && x 25) || (x 14 && x 20) || (x 14 && x 24) || (x 11 && x 21) || (x 15 && x 19) || (x 15 && x 23) || (x 15 && x 24) || (x 16 && x 25) || (x 16 && x 23) || (x 16 && x 22) || (x 10 && x 22) || (x 9 && x 20) || (x 18 && x 23) || (x 18 && x 20) || (x 18 && x 21) || (x 17 && x 22) || (x 17 && x 21) || (x 17 && x 24) || (x 8 && x 24) || (x 7 && x 20) || (x 6 && x 21) || (x 5 && x 24) || (x 4 && x 19) || (x 3 && x 25) || (x 2 && x 19) || (x 1 && x 25) || (x 0 && x 23)
def f27 (x : Fin 27 → Bool) : Bool := (x 13 && x 20) || (x 13 && x 23) || (x 13 && x 21) || (x 14 && x 20) || (x 14 && x 26) || (x 14 && x 22) || (x 15 && x 0) || (x 15 && x 26) || (x 15 && x 21) || (x 15 && x 25) || (x 12 && x 22) || (x 16 && x 20) || (x 16 && x 24) || (x 16 && x 25) || (x 17 && x 26) || (x 17 && x 24) || (x 17 && x 23) || (x 11 && x 23) || (x 10 && x 21) || (x 19 && x 24) || (x 19 && x 21) || (x 19 && x 22) || (x 18 && x 23) || (x 18 && x 22) || (x 18 && x 25) || (x 9 && x 25) || (x 8 && x 21) || (x 7 && x 0) || (x 7 && x 22) || (x 6 && x 25) || (x 5 && x 0) || (x 5 && x 20) || (x 4 && x 26) || (x 3 && x 20) || (x 2 && x 26) || (x 1 && x 24)
def f28 (x : Fin 28 → Bool) : Bool := (x 14 && x 21) || (x 14 && x 24) || (x 14 && x 22) || (x 15 && x 21) || (x 15 && x 27) || (x 15 && x 23) || (x 16 && x 1) || (x 16 && x 27) || (x 16 && x 0) || (x 16 && x 22) || (x 16 && x 26) || (x 13 && x 0) || (x 13 && x 23) || (x 17 && x 21) || (x 17 && x 25) || (x 17 && x 26) || (x 18 && x 27) || (x 18 && x 25) || (x 18 && x 24) || (x 12 && x 0) || (x 12 && x 24) || (x 11 && x 22) || (x 20 && x 25) || (x 20 && x 22) || (x 20 && x 23) || (x 19 && x 24) || (x 19 && x 23) || (x 19 && x 26) || (x 10 && x 26) || (x 9 && x 22) || (x 8 && x 1) || (x 8 && x 23) || (x 7 && x 26) || (x 6 && x 1) || (x 6 && x 21) || (x 5 && x 27) || (x 4 && x 21) || (x 4 && x 0) || (x 3 && x 27) || (x 2 && x 0) || (x 2 && x 25)
def f29 (x : Fin 29 → Bool) : Bool := (x 15 && x 22) || (x 15 && x 25) || (x 15 && x 23) || (x 16 && x 22) || (x 16 && x 28) || (x 16 && x 24) || (x 17 && x 2) || (x 17 && x 28) || (x 17 && x 1) || (x 17 && x 23) || (x 17 && x 27) || (x 14 && x 1) || (x 14 && x 0) || (x 14 && x 24) || (x 18 && x 22) || (x 18 && x 0) || (x 18 && x 26) || (x 18 && x 27) || (x 19 && x 28) || (x 19 && x 26) || (x 19 && x 25) || (x 13 && x 1) || (x 13 && x 25) || (x 12 && x 0) || (x 12 && x 23) || (x 21 && x 26) || (x 21 && x 23) || (x 21 && x 24) || (x 20 && x 25) || (x 20 && x 24) || (x 20 && x 27) || (x 11 && x 27) || (x 10 && x 23) || (x 9 && x 2) || (x 9 && x 24) || (x 8 && x 27) || (x 7 && x 2) || (x 7 && x 22) || (x 6 && x 28) || (x 5 && x 22) || (x 5 && x 1) || (x 4 && x 28) || (x 4 && x 0) || (x 3 && x 1) || (x 3 && x 26)
def f30 (x : Fin 30 → Bool) : Bool := (x 16 && x 23) || (x 16 && x 26) || (x 16 && x 24) || (x 17 && x 23) || (x 17 && x 29) || (x 17 && x 0) || (x 17 && x 25) || (x 18 && x 3) || (x 18 && x 29) || (x 18 && x 2) || (x 18 && x 24) || (x 18 && x 28) || (x 15 && x 2) || (x 15 && x 1) || (x 15 && x 25) || (x 19 && x 23) || (x 19 && x 1) || (x 19 && x 27) || (x 19 && x 28) || (x 20 && x 29) || (x 20 && x 27) || (x 20 && x 26) || (x 14 && x 2) || (x 14 && x 26) || (x 14 && x 0) || (x 13 && x 1) || (x 13 && x 0) || (x 13 && x 24) || (x 22 && x 27) || (x 22 && x 24) || (x 22 && x 25) || (x 21 && x 26) || (x 21 && x 25) || (x 21 && x 28) || (x 12 && x 0) || (x 12 && x 28) || (x 11 && x 24) || (x 10 && x 3) || (x 10 && x 25) || (x 9 && x 28) || (x 8 && x 3) || (x 8 && x 23) || (x 7 && x 29) || (x 6 && x 23) || (x 6 && x 2) || (x 5 && x 29) || (x 5 && x 1) || (x 4 && x 2) || (x 4 && x 27)
def f31 (x : Fin 31 → Bool) : Bool := (x 17 && x 24) || (x 17 && x 27) || (x 17 && x 25) || (x 18 && x 24) || (x 18 && x 30) || (x 18 && x 1) || (x 18 && x 26) || (x 19 && x 4) || (x 19 && x 30) || (x 19 && x 3) || (x 19 && x 25) || (x 19 && x 29) || (x 16 && x 3) || (x 16 && x 2) || (x 16 && x 26) || (x 16 && x 0) || (x 20 && x 24) || (x 20 && x 2) || (x 20 && x 28) || (x 20 && x 29) || (x 21 && x 30) || (x 21 && x 28) || (x 21 && x 27) || (x 21 && x 0) || (x 15 && x 3) || (x 15 && x 27) || (x 15 && x 1) || (x 14 && x 2) || (x 14 && x 1) || (x 14 && x 25) || (x 23 && x 28) || (x 23 && x 25) || (x 23 && x 26) || (x 22 && x 27) || (x 22 && x 26) || (x 22 && x 29) || (x 13 && x 1) || (x 13 && x 29) || (x 13 && x 0) || (x 12 && x 25) || (x 12 && x 0) || (x 11 && x 4) || (x 11 && x 26) || (x 10 && x 29) || (x 9 && x 4) || (x 9 && x 24) || (x 9 && x 0) || (x 8 && x 30) || (x 7 && x 24) || (x 7 && x 3) || (x 6 && x 30) || (x 6 && x 2) || (x 5 && x 3) || (x 5 && x 28)
def f32 (x : Fin 32 → Bool) : Bool := (x 18 && x 25) || (x 18 && x 28) || (x 18 && x 26) || (x 19 && x 25) || (x 19 && x 31) || (x 19 && x 2) || (x 19 && x 27) || (x 20 && x 5) || (x 20 && x 31) || (x 20 && x 4) || (x 20 && x 26) || (x 20 && x 30) || (x 17 && x 4) || (x 17 && x 3) || (x 17 && x 27) || (x 17 && x 1) || (x 21 && x 25) || (x 21 && x 3) || (x 21 && x 29) || (x 21 && x 30) || (x 21 && x 0) || (x 22 && x 31) || (x 22 && x 29) || (x 22 && x 28) || (x 22 && x 1) || (x 16 && x 4) || (x 16 && x 28) || (x 16 && x 2) || (x 16 && x 0) || (x 15 && x 3) || (x 15 && x 2) || (x 15 && x 26) || (x 24 && x 29) || (x 24 && x 26) || (x 24 && x 27) || (x 23 && x 28) || (x 23 && x 27) || (x 23 && x 30) || (x 14 && x 2) || (x 14 && x 30) || (x 14 && x 1) || (x 13 && x 26) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 5) || (x 12 && x 27) || (x 12 && x 0) || (x 11 && x 30) || (x 10 && x 5) || (x 10 && x 25) || (x 10 && x 1) || (x 9 && x 31) || (x 9 && x 0) || (x 8 && x 25) || (x 8 && x 4) || (x 7 && x 31) || (x 7 && x 3) || (x 6 && x 4) || (x 6 && x 29)
def f33 (x : Fin 33 → Bool) : Bool := (x 19 && x 26) || (x 19 && x 29) || (x 19 && x 27) || (x 20 && x 26) || (x 20 && x 32) || (x 20 && x 3) || (x 20 && x 28) || (x 21 && x 6) || (x 21 && x 32) || (x 21 && x 5) || (x 21 && x 27) || (x 21 && x 31) || (x 18 && x 5) || (x 18 && x 4) || (x 18 && x 28) || (x 18 && x 2) || (x 22 && x 26) || (x 22 && x 4) || (x 22 && x 30) || (x 22 && x 31) || (x 22 && x 1) || (x 23 && x 32) || (x 23 && x 30) || (x 23 && x 29) || (x 23 && x 2) || (x 23 && x 0) || (x 17 && x 5) || (x 17 && x 29) || (x 17 && x 3) || (x 17 && x 1) || (x 16 && x 4) || (x 16 && x 3) || (x 16 && x 27) || (x 16 && x 0) || (x 25 && x 30) || (x 25 && x 27) || (x 25 && x 28) || (x 24 && x 29) || (x 24 && x 28) || (x 24 && x 31) || (x 15 && x 3) || (x 15 && x 31) || (x 15 && x 2) || (x 14 && x 27) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 6) || (x 13 && x 28) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 31) || (x 12 && x 0) || (x 11 && x 6) || (x 11 && x 26) || (x 11 && x 2) || (x 10 && x 32) || (x 10 && x 1) || (x 9 && x 26) || (x 9 && x 5) || (x 9 && x 0) || (x 8 && x 32) || (x 8 && x 4) || (x 7 && x 5) || (x 7 && x 30)
def f34 (x : Fin 34 → Bool) : Bool := (x 20 && x 27) || (x 20 && x 30) || (x 20 && x 28) || (x 21 && x 27) || (x 21 && x 33) || (x 21 && x 4) || (x 21 && x 29) || (x 22 && x 7) || (x 22 && x 33) || (x 22 && x 6) || (x 22 && x 28) || (x 22 && x 32) || (x 19 && x 6) || (x 19 && x 5) || (x 19 && x 29) || (x 19 && x 3) || (x 23 && x 27) || (x 23 && x 5) || (x 23 && x 31) || (x 23 && x 32) || (x 23 && x 2) || (x 24 && x 33) || (x 24 && x 31) || (x 24 && x 30) || (x 24 && x 3) || (x 24 && x 1) || (x 18 && x 6) || (x 18 && x 30) || (x 18 && x 4) || (x 18 && x 2) || (x 18 && x 0) || (x 17 && x 5) || (x 17 && x 4) || (x 17 && x 28) || (x 17 && x 1) || (x 26 && x 31) || (x 26 && x 28) || (x 26 && x 29) || (x 26 && x 0) || (x 25 && x 30) || (x 25 && x 29) || (x 25 && x 32) || (x 16 && x 4) || (x 16 && x 32) || (x 16 && x 3) || (x 15 && x 28) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 7) || (x 14 && x 29) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 32) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 7) || (x 12 && x 27) || (x 12 && x 3) || (x 12 && x 0) || (x 11 && x 33) || (x 11 && x 2) || (x 10 && x 27) || (x 10 && x 6) || (x 10 && x 1) || (x 9 && x 33) || (x 9 && x 5) || (x 9 && x 0) || (x 8 && x 6) || (x 8 && x 31)
def f35 (x : Fin 35 → Bool) : Bool := (x 21 && x 28) || (x 21 && x 31) || (x 21 && x 29) || (x 22 && x 28) || (x 22 && x 34) || (x 22 && x 5) || (x 22 && x 30) || (x 23 && x 8) || (x 23 && x 34) || (x 23 && x 7) || (x 23 && x 29) || (x 23 && x 33) || (x 20 && x 7) || (x 20 && x 6) || (x 20 && x 30) || (x 20 && x 4) || (x 24 && x 28) || (x 24 && x 6) || (x 24 && x 32) || (x 24 && x 33) || (x 24 && x 3) || (x 25 && x 34) || (x 25 && x 32) || (x 25 && x 31) || (x 25 && x 4) || (x 25 && x 2) || (x 19 && x 7) || (x 19 && x 31) || (x 19 && x 5) || (x 19 && x 3) || (x 19 && x 1) || (x 18 && x 6) || (x 18 && x 5) || (x 18 && x 29) || (x 18 && x 2) || (x 18 && x 0) || (x 27 && x 32) || (x 27 && x 29) || (x 27 && x 30) || (x 27 && x 1) || (x 26 && x 31) || (x 26 && x 30) || (x 26 && x 33) || (x 26 && x 0) || (x 17 && x 5) || (x 17 && x 33) || (x 17 && x 4) || (x 16 && x 29) || (x 16 && x 4) || (x 16 && x 3) || (x 15 && x 8) || (x 15 && x 30) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 33) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 8) || (x 13 && x 28) || (x 13 && x 4) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 34) || (x 12 && x 3) || (x 12 && x 0) || (x 11 && x 28) || (x 11 && x 7) || (x 11 && x 2) || (x 10 && x 34) || (x 10 && x 6) || (x 10 && x 1) || (x 9 && x 7) || (x 9 && x 32) || (x 9 && x 0)
def f36 (x : Fin 36 → Bool) : Bool := (x 22 && x 29) || (x 22 && x 32) || (x 22 && x 30) || (x 23 && x 29) || (x 23 && x 35) || (x 23 && x 6) || (x 23 && x 31) || (x 24 && x 9) || (x 24 && x 35) || (x 24 && x 8) || (x 24 && x 30) || (x 24 && x 34) || (x 21 && x 8) || (x 21 && x 7) || (x 21 && x 31) || (x 21 && x 5) || (x 25 && x 29) || (x 25 && x 7) || (x 25 && x 33) || (x 25 && x 34) || (x 25 && x 4) || (x 26 && x 35) || (x 26 && x 33) || (x 26 && x 32) || (x 26 && x 5) || (x 26 && x 3) || (x 20 && x 8) || (x 20 && x 32) || (x 20 && x 6) || (x 20 && x 4) || (x 20 && x 2) || (x 19 && x 7) || (x 19 && x 6) || (x 19 && x 30) || (x 19 && x 3) || (x 19 && x 1) || (x 28 && x 33) || (x 28 && x 30) || (x 28 && x 31) || (x 28 && x 2) || (x 28 && x 0) || (x 27 && x 32) || (x 27 && x 31) || (x 27 && x 34) || (x 27 && x 1) || (x 18 && x 6) || (x 18 && x 34) || (x 18 && x 5) || (x 18 && x 0) || (x 17 && x 30) || (x 17 && x 5) || (x 17 && x 4) || (x 16 && x 9) || (x 16 && x 31) || (x 16 && x 4) || (x 16 && x 3) || (x 15 && x 34) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 9) || (x 14 && x 29) || (x 14 && x 5) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 35) || (x 13 && x 4) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 29) || (x 12 && x 8) || (x 12 && x 3) || (x 12 && x 0) || (x 11 && x 35) || (x 11 && x 7) || (x 11 && x 2) || (x 10 && x 8) || (x 10 && x 33) || (x 10 && x 1)
def f37 (x : Fin 37 → Bool) : Bool := (x 23 && x 30) || (x 23 && x 33) || (x 23 && x 31) || (x 24 && x 30) || (x 24 && x 36) || (x 24 && x 7) || (x 24 && x 32) || (x 25 && x 10) || (x 25 && x 36) || (x 25 && x 9) || (x 25 && x 31) || (x 25 && x 35) || (x 22 && x 9) || (x 22 && x 8) || (x 22 && x 32) || (x 22 && x 6) || (x 26 && x 30) || (x 26 && x 8) || (x 26 && x 34) || (x 26 && x 35) || (x 26 && x 5) || (x 27 && x 36) || (x 27 && x 34) || (x 27 && x 33) || (x 27 && x 6) || (x 27 && x 4) || (x 21 && x 9) || (x 21 && x 33) || (x 21 && x 7) || (x 21 && x 5) || (x 21 && x 3) || (x 20 && x 8) || (x 20 && x 7) || (x 20 && x 31) || (x 20 && x 4) || (x 20 && x 2) || (x 29 && x 34) || (x 29 && x 31) || (x 29 && x 32) || (x 29 && x 3) || (x 29 && x 1) || (x 28 && x 33) || (x 28 && x 32) || (x 28 && x 35) || (x 28 && x 2) || (x 28 && x 0) || (x 19 && x 7) || (x 19 && x 35) || (x 19 && x 6) || (x 19 && x 1) || (x 18 && x 31) || (x 18 && x 6) || (x 18 && x 5) || (x 18 && x 0) || (x 17 && x 10) || (x 17 && x 32) || (x 17 && x 5) || (x 17 && x 4) || (x 16 && x 35) || (x 16 && x 4) || (x 16 && x 3) || (x 15 && x 10) || (x 15 && x 30) || (x 15 && x 6) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 36) || (x 14 && x 5) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 30) || (x 13 && x 9) || (x 13 && x 4) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 36) || (x 12 && x 8) || (x 12 && x 3) || (x 12 && x 0) || (x 11 && x 9) || (x 11 && x 34) || (x 11 && x 2)
def f38 (x : Fin 38 → Bool) : Bool := (x 24 && x 31) || (x 24 && x 34) || (x 24 && x 32) || (x 24 && x 0) || (x 25 && x 31) || (x 25 && x 37) || (x 25 && x 8) || (x 25 && x 33) || (x 26 && x 11) || (x 26 && x 37) || (x 26 && x 10) || (x 26 && x 32) || (x 26 && x 36) || (x 23 && x 10) || (x 23 && x 9) || (x 23 && x 33) || (x 23 && x 7) || (x 27 && x 31) || (x 27 && x 9) || (x 27 && x 35) || (x 27 && x 36) || (x 27 && x 6) || (x 28 && x 37) || (x 28 && x 35) || (x 28 && x 34) || (x 28 && x 7) || (x 28 && x 5) || (x 22 && x 10) || (x 22 && x 34) || (x 22 && x 8) || (x 22 && x 6) || (x 22 && x 4) || (x 21 && x 9) || (x 21 && x 8) || (x 21 && x 32) || (x 21 && x 5) || (x 21 && x 3) || (x 30 && x 35) || (x 30 && x 32) || (x 30 && x 33) || (x 30 && x 4) || (x 30 && x 2) || (x 29 && x 34) || (x 29 && x 33) || (x 29 && x 36) || (x 29 && x 3) || (x 29 && x 1) || (x 20 && x 8) || (x 20 && x 36) || (x 20 && x 7) || (x 20 && x 2) || (x 20 && x 0) || (x 19 && x 32) || (x 19 && x 7) || (x 19 && x 6) || (x 19 && x 1) || (x 18 && x 11) || (x 18 && x 33) || (x 18 && x 6) || (x 18 && x 5) || (x 18 && x 0) || (x 17 && x 36) || (x 17 && x 5) || (x 17 && x 4) || (x 16 && x 11) || (x 16 && x 31) || (x 16 && x 7) || (x 16 && x 4) || (x 16 && x 3) || (x 15 && x 37) || (x 15 && x 6) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 31) || (x 14 && x 10) || (x 14 && x 5) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 37) || (x 13 && x 9) || (x 13 && x 4) || (x 13 && x 1) || (x 13 && x 0) || (x 12 && x 10) || (x 12 && x 35) || (x 12 && x 3) || (x 12 && x 0)
def f39 (x : Fin 39 → Bool) : Bool := (x 25 && x 32) || (x 25 && x 35) || (x 25 && x 33) || (x 25 && x 1) || (x 26 && x 32) || (x 26 && x 38) || (x 26 && x 9) || (x 26 && x 34) || (x 26 && x 0) || (x 27 && x 12) || (x 27 && x 38) || (x 27 && x 11) || (x 27 && x 33) || (x 27 && x 37) || (x 24 && x 11) || (x 24 && x 10) || (x 24 && x 34) || (x 24 && x 8) || (x 28 && x 32) || (x 28 && x 10) || (x 28 && x 36) || (x 28 && x 37) || (x 28 && x 7) || (x 29 && x 38) || (x 29 && x 36) || (x 29 && x 35) || (x 29 && x 8) || (x 29 && x 6) || (x 23 && x 11) || (x 23 && x 35) || (x 23 && x 9) || (x 23 && x 7) || (x 23 && x 5) || (x 22 && x 10) || (x 22 && x 9) || (x 22 && x 33) || (x 22 && x 6) || (x 22 && x 4) || (x 31 && x 36) || (x 31 && x 33) || (x 31 && x 34) || (x 31 && x 5) || (x 31 && x 3) || (x 30 && x 35) || (x 30 && x 34) || (x 30 && x 37) || (x 30 && x 4) || (x 30 && x 2) || (x 21 && x 9) || (x 21 && x 37) || (x 21 && x 8) || (x 21 && x 3) || (x 21 && x 1) || (x 20 && x 33) || (x 20 && x 8) || (x 20 && x 7) || (x 20 && x 2) || (x 20 && x 0) || (x 19 && x 12) || (x 19 && x 34) || (x 19 && x 7) || (x 19 && x 6) || (x 19 && x 1) || (x 18 && x 37) || (x 18 && x 6) || (x 18 && x 5) || (x 18 && x 0) || (x 17 && x 12) || (x 17 && x 32) || (x 17 && x 8) || (x 17 && x 5) || (x 17 && x 4) || (x 16 && x 38) || (x 16 && x 7) || (x 16 && x 4) || (x 16 && x 3) || (x 15 && x 32) || (x 15 && x 11) || (x 15 && x 6) || (x 15 && x 3) || (x 15 && x 2) || (x 14 && x 38) || (x 14 && x 10) || (x 14 && x 5) || (x 14 && x 2) || (x 14 && x 1) || (x 13 && x 11) || (x 13 && x 36) || (x 13 && x 4) || (x 13 && x 1) || (x 13 && x 0)
def f40 (x : Fin 40 → Bool) : Bool := (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)

theorem base : ¬ HasCircuitSize 14 f14 21 := by
  intro h
  have eq : f14 = PEqualNP.Outside.L_meta_9753.Paid.packet := by
    funext x
    unfold f14 PEqualNP.Outside.L_meta_9753.Paid.packet
    ac_rfl
  rw [eq] at h
  have := PEqualNP.Outside.L_meta_9753.Paid.physical22 21 h
  omega

private def bank15 : List (Option (Fin 14)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13]
private def lift15 (y : Fin 14 → Bool) : Fin 15 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13]
private def probe15 (b : Bool) : Fin 15 → Bool := ![b,false,false,false,false,false,false,false,false,false,true,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower15 : ¬ HasCircuitSize 15 f15 22 := by
  apply paid_pin f15 f14 bank15 probe15 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift15 (fun y => by rfl) (fun y => by simp [f15,lift15,f14]) (by decide)
    base

private def bank16 : List (Option (Fin 15)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14]
private def lift16 (y : Fin 15 → Bool) : Fin 16 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14]
private def probe16 (b : Bool) : Fin 16 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower16 : ¬ HasCircuitSize 16 f16 23 := by
  apply paid_pin f16 f15 bank16 probe16 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift16 (fun y => by rfl) (fun y => by simp [f16,lift16,f15]) (by decide)
    lower15

private def bank17 : List (Option (Fin 16)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15]
private def lift17 (y : Fin 16 → Bool) : Fin 17 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15]
private def probe17 (b : Bool) : Fin 17 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower17 : ¬ HasCircuitSize 17 f17 24 := by
  apply paid_pin f17 f16 bank17 probe17 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift17 (fun y => by rfl) (fun y => by simp [f17,lift17,f16]) (by decide)
    lower16

private def bank18 : List (Option (Fin 17)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16]
private def lift18 (y : Fin 17 → Bool) : Fin 18 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16]
private def probe18 (b : Bool) : Fin 18 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false]

set_option maxHeartbeats 2000000 in
theorem lower18 : ¬ HasCircuitSize 18 f18 25 := by
  apply paid_pin f18 f17 bank18 probe18 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift18 (fun y => by rfl) (fun y => by simp [f18,lift18,f17]) (by decide)
    lower17

private def bank19 : List (Option (Fin 18)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17]
private def lift19 (y : Fin 18 → Bool) : Fin 19 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17]
private def probe19 (b : Bool) : Fin 19 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower19 : ¬ HasCircuitSize 19 f19 26 := by
  apply paid_pin f19 f18 bank19 probe19 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift19 (fun y => by rfl) (fun y => by simp [f19,lift19,f18]) (by decide)
    lower18

private def bank20 : List (Option (Fin 19)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18]
private def lift20 (y : Fin 19 → Bool) : Fin 20 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18]
private def probe20 (b : Bool) : Fin 20 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower20 : ¬ HasCircuitSize 20 f20 27 := by
  apply paid_pin f20 f19 bank20 probe20 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift20 (fun y => by rfl) (fun y => by simp [f20,lift20,f19]) (by decide)
    lower19

private def bank21 : List (Option (Fin 20)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19]
private def lift21 (y : Fin 20 → Bool) : Fin 21 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19]
private def probe21 (b : Bool) : Fin 21 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false]

set_option maxHeartbeats 2000000 in
theorem lower21 : ¬ HasCircuitSize 21 f21 28 := by
  apply paid_pin f21 f20 bank21 probe21 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift21 (fun y => by rfl) (fun y => by simp [f21,lift21,f20]) (by decide)
    lower20

private def bank22 : List (Option (Fin 21)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20]
private def lift22 (y : Fin 21 → Bool) : Fin 22 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20]
private def probe22 (b : Bool) : Fin 22 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower22 : ¬ HasCircuitSize 22 f22 29 := by
  apply paid_pin f22 f21 bank22 probe22 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift22 (fun y => by rfl) (fun y => by simp [f22,lift22,f21]) (by decide)
    lower21

private def bank23 : List (Option (Fin 22)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21]
private def lift23 (y : Fin 22 → Bool) : Fin 23 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21]
private def probe23 (b : Bool) : Fin 23 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true]

set_option maxHeartbeats 2000000 in
theorem lower23 : ¬ HasCircuitSize 23 f23 30 := by
  apply paid_pin f23 f22 bank23 probe23 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift23 (fun y => by rfl) (fun y => by simp [f23,lift23,f22]) (by decide)
    lower22

private def bank24 : List (Option (Fin 23)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22]
private def lift24 (y : Fin 23 → Bool) : Fin 24 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22]
private def probe24 (b : Bool) : Fin 24 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower24 : ¬ HasCircuitSize 24 f24 31 := by
  apply paid_pin f24 f23 bank24 probe24 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift24 (fun y => by rfl) (fun y => by simp [f24,lift24,f23]) (by decide)
    lower23

private def bank25 : List (Option (Fin 24)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23]
private def lift25 (y : Fin 24 → Bool) : Fin 25 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23]
private def probe25 (b : Bool) : Fin 25 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true]

set_option maxHeartbeats 2000000 in
theorem lower25 : ¬ HasCircuitSize 25 f25 32 := by
  apply paid_pin f25 f24 bank25 probe25 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift25 (fun y => by rfl) (fun y => by simp [f25,lift25,f24]) (by decide)
    lower24

private def bank26 : List (Option (Fin 25)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24]
private def lift26 (y : Fin 25 → Bool) : Fin 26 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24]
private def probe26 (b : Bool) : Fin 26 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false]

set_option maxHeartbeats 2000000 in
theorem lower26 : ¬ HasCircuitSize 26 f26 33 := by
  apply paid_pin f26 f25 bank26 probe26 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift26 (fun y => by rfl) (fun y => by simp [f26,lift26,f25]) (by decide)
    lower25

private def bank27 : List (Option (Fin 26)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25]
private def lift27 (y : Fin 26 → Bool) : Fin 27 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25]
private def probe27 (b : Bool) : Fin 27 → Bool := ![b,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower27 : ¬ HasCircuitSize 27 f27 34 := by
  apply paid_pin f27 f26 bank27 probe27 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift27 (fun y => by rfl) (fun y => by simp [f27,lift27,f26]) (by decide)
    lower26

private def bank28 : List (Option (Fin 27)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26]
private def lift28 (y : Fin 27 → Bool) : Fin 28 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26]
private def probe28 (b : Bool) : Fin 28 → Bool := ![b,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower28 : ¬ HasCircuitSize 28 f28 35 := by
  apply paid_pin f28 f27 bank28 probe28 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift28 (fun y => by rfl) (fun y => by simp [f28,lift28,f27]) (by decide)
    lower27

private def bank29 : List (Option (Fin 28)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27]
private def lift29 (y : Fin 28 → Bool) : Fin 29 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27]
private def probe29 (b : Bool) : Fin 29 → Bool := ![b,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower29 : ¬ HasCircuitSize 29 f29 36 := by
  apply paid_pin f29 f28 bank29 probe29 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift29 (fun y => by rfl) (fun y => by simp [f29,lift29,f28]) (by decide)
    lower28

private def bank30 : List (Option (Fin 29)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28]
private def lift30 (y : Fin 29 → Bool) : Fin 30 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28]
private def probe30 (b : Bool) : Fin 30 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower30 : ¬ HasCircuitSize 30 f30 37 := by
  apply paid_pin f30 f29 bank30 probe30 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift30 (fun y => by rfl) (fun y => by simp [f30,lift30,f29]) (by decide)
    lower29

private def bank31 : List (Option (Fin 30)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29]
private def lift31 (y : Fin 30 → Bool) : Fin 31 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29]
private def probe31 (b : Bool) : Fin 31 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower31 : ¬ HasCircuitSize 31 f31 38 := by
  apply paid_pin f31 f30 bank31 probe31 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift31 (fun y => by rfl) (fun y => by simp [f31,lift31,f30]) (by decide)
    lower30

private def bank32 : List (Option (Fin 31)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30]
private def lift32 (y : Fin 31 → Bool) : Fin 32 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30]
private def probe32 (b : Bool) : Fin 32 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower32 : ¬ HasCircuitSize 32 f32 39 := by
  apply paid_pin f32 f31 bank32 probe32 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift32 (fun y => by rfl) (fun y => by simp [f32,lift32,f31]) (by decide)
    lower31

private def bank33 : List (Option (Fin 32)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31]
private def lift33 (y : Fin 32 → Bool) : Fin 33 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31]
private def probe33 (b : Bool) : Fin 33 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower33 : ¬ HasCircuitSize 33 f33 40 := by
  apply paid_pin f33 f32 bank33 probe33 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift33 (fun y => by rfl) (fun y => by simp [f33,lift33,f32]) (by decide)
    lower32

private def bank34 : List (Option (Fin 33)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32]
private def lift34 (y : Fin 33 → Bool) : Fin 34 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32]
private def probe34 (b : Bool) : Fin 34 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower34 : ¬ HasCircuitSize 34 f34 41 := by
  apply paid_pin f34 f33 bank34 probe34 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift34 (fun y => by rfl) (fun y => by simp [f34,lift34,f33]) (by decide)
    lower33

private def bank35 : List (Option (Fin 34)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33]
private def lift35 (y : Fin 34 → Bool) : Fin 35 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33]
private def probe35 (b : Bool) : Fin 35 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower35 : ¬ HasCircuitSize 35 f35 42 := by
  apply paid_pin f35 f34 bank35 probe35 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift35 (fun y => by rfl) (fun y => by simp [f35,lift35,f34]) (by decide)
    lower34

private def bank36 : List (Option (Fin 35)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34]
private def lift36 (y : Fin 35 → Bool) : Fin 36 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34]
private def probe36 (b : Bool) : Fin 36 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower36 : ¬ HasCircuitSize 36 f36 43 := by
  apply paid_pin f36 f35 bank36 probe36 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift36 (fun y => by rfl) (fun y => by simp [f36,lift36,f35]) (by decide)
    lower35

private def bank37 : List (Option (Fin 36)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35]
private def lift37 (y : Fin 36 → Bool) : Fin 37 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35]
private def probe37 (b : Bool) : Fin 37 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower37 : ¬ HasCircuitSize 37 f37 44 := by
  apply paid_pin f37 f36 bank37 probe37 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift37 (fun y => by rfl) (fun y => by simp [f37,lift37,f36]) (by decide)
    lower36

private def bank38 : List (Option (Fin 37)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35,some 36]
private def lift38 (y : Fin 37 → Bool) : Fin 38 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35,y 36]
private def probe38 (b : Bool) : Fin 38 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower38 : ¬ HasCircuitSize 38 f38 45 := by
  apply paid_pin f38 f37 bank38 probe38 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift38 (fun y => by rfl) (fun y => by simp [f38,lift38,f37]) (by decide)
    lower37

private def bank39 : List (Option (Fin 38)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35,some 36,some 37]
private def lift39 (y : Fin 38 → Bool) : Fin 39 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35,y 36,y 37]
private def probe39 (b : Bool) : Fin 39 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower39 : ¬ HasCircuitSize 39 f39 46 := by
  apply paid_pin f39 f38 bank39 probe39 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift39 (fun y => by rfl) (fun y => by simp [f39,lift39,f38]) (by decide)
    lower38

private def bank40 : List (Option (Fin 39)) := [none,some 25,some 26,some 27,some 24,some 28,some 29,some 23,some 22,some 31,some 30,some 21,some 20,some 19,some 18,some 17,some 16,some 15,some 14,some 13,some 12,some 32,some 38,some 11,some 10,some 36,some 35,some 9,some 33,some 34,some 37,some 8,some 7,some 6,some 5,some 4,some 3,some 2,some 1,some 0]
private def lift40 (y : Fin 39 → Bool) : Fin 40 → Bool := ![false,y 25,y 26,y 27,y 24,y 28,y 29,y 23,y 22,y 31,y 30,y 21,y 20,y 19,y 18,y 17,y 16,y 15,y 14,y 13,y 12,y 32,y 38,y 11,y 10,y 36,y 35,y 9,y 33,y 34,y 37,y 8,y 7,y 6,y 5,y 4,y 3,y 2,y 1,y 0]
private def probe40 (b : Bool) : Fin 40 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower40 : ¬ HasCircuitSize 40 f40 47 := by
  apply paid_pin f40 f39 bank40 probe40 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift40 (fun y => by rfl) (fun y => by simp [f40,lift40,f39]) (by decide)
    lower39

end Fano9838
