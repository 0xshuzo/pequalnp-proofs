import PEqualNP.Outside.L_meta_18284

namespace PetersenProductFloor
open PEqualNP.Outside.L_meta_18284_aux.Certificate
open PEqualNP.Outside.L_meta_18284_aux.Bound

def tap (i : Fin 3) : Sig :=
  let a := if i.val=2 then 4 else 0
  let b := if i.val=0 then 2 else 6
  inputs.getD a zero &&& inputs.getD b zero

def rep (i : Fin 3) := inputs ++ [tap i]
def projectedInputs (v : Fin 10) := inputs ++ [dest v 0 &&& dest v 2]
def swaps : List (List Nat) := [[], [81, 130, 118], [16, 82, 131, 100], [16, 32, 48, 128, 100, 80, 116], [32, 83, 116], [32, 49, 128, 81, 116, 100], [48, 33, 133, 118], [48, 129, 82], [80, 16, 33, 50, 116, 131, 100], [80, 129, 50, 116], [128, 49, 100], [128, 81, 32, 49, 100, 116]]
def moves (p : Fin 12) := ((swaps.getD p.val []).map swapRows)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem projectedMaps : ∀ v : Fin 10, v≠6 → ∃ j : Fin 3, ∃ p : Fin 12,
    checkMap (moves p) (projectedInputs v) graph (rep j) graph = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem easilyCut (i : Fin 3) (nonzero : i ≠ 0) : Impossible true graph 14 (rep i).toFinset := by
  have h (j : Fin 3) (hj : j ≠ 0) : Impossible true (graphGoal 511) 14 (rep j).toFinset := by
    apply cut_root (m:=511) (cap:=14) (before_sound known383 valid383) (64,0,447,0,13)
    · decide +kernel
    · revert hj j
      decide +kernel
  exact (show graphGoal 511 = graph by decide +kernel) ▸ h i nonzero

def neighbors : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 8, 2, 1, 2, 4, 1, 1, 2, 4, 8, 2, 1, 2, 4, 1, 1, 2, 4, 8]

def tests (i : Fin 3) : List (Sig × Row × Row) := List.ofFn fun j : Fin 9 =>
  let low := neighbors.getD (9*i.val+j.val) 0
  (inputs.getD j.val zero,Fin.ofNat 512 low,Fin.ofNat 512 (low+2^j.val))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem testsOK : ∀ i : Fin 3, checkEssential graph (rep i) (tests i) = true ∧
    (tests i).map Prod.fst = inputs := by decide +kernel

theorem repFloor (i : Fin 3) (difficult : Impossible true graph 14 (rep 0).toFinset) :
    Lower true (rep i) graph 15 := by
  intro p bank path hit
  have ct : plainWord graph = true := by decide +kernel
  have rt : ∀ t : Fin 3, (rep t).all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := reach_live graph_proper ct (rt i) path hit
  have pick : ∀ a ∈ inputs, a ∈ S := by
    intro a ha
    have member : a ∈ ((tests i).map Prod.fst).toFinset := by
      rw [(testsOK i).2]
      exact List.mem_toFinset.mpr ha
    obtain ⟨r,s,neq,iso⟩ := essential_ok (testsOK i).1 a member
    exact raw_required run (rep i) a sub r s neq iso
  by_contra! small
  by_cases used : tap i ∈ S
  · have same : S = (rep i).toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨sub a,?_⟩
      intro h
      rcases List.mem_append.mp h with before|extra
      · exact pick a before
      · have ha : a = tap i := by simpa using extra
        exact ha.symm ▸ used
    rw [same] at run
    by_cases z : i=0
    · subst i
      exact difficult k (by omega) run
    · exact easilyCut i z k (by omega) run
  · have raw : ∀ w ∈ S, w ∈ inputs := by
      intro w hw
      rcases List.mem_append.mp (sub w hw) with h|h
      · exact h
      · have eq : w=tap i := by simpa using h
        exact (used (eq ▸ hw)).elim
    rw [orbitAllInputs run raw] at run
    exact rootSImpossible k (by omega) run

theorem projectedFloor (v : Fin 10) (avoid : v ≠ 6)
    (difficult : Impossible true graph 14 (rep 0).toFinset) :
    Lower true (projectedInputs v) graph 15 := by
  obtain ⟨j,p,ok⟩ := projectedMaps v avoid
  have plain : ∀ w : Fin 10, (projectedInputs w).all plainWord = true := by decide +kernel
  exact lower_map ok graph_proper (by decide +kernel) (plain v) graph_proper (repFloor j difficult)

end PetersenProductFloor
namespace PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds
private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

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


def supplied := PEqualNP.Outside.L_meta_18284_aux.Bound.pin 0 &&&
  PEqualNP.Outside.L_meta_18284_aux.Bound.pin 2
def extraInitial := initial ++ [supplied]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem realizeExtra (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = f10 x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ a ∈ S, a ∈ extraInitial := by
  have he : (execute C.gates extraInitial).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (extraInitial.map (bit r))).getD C.output false = _
    have hrows : extraInitial.map (bit r) = List.ofFn (assign r) ++ [assign r 0 && assign r 2] := by
      rw [extraInitial,List.map_append,rowInputs]
      simp [supplied,PEqualNP.Outside.L_meta_18284_aux.Bound.pin,assign,bit,initial]
    rw [hrows]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates extraInitial) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates extraInitial legal (u:=true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have ns : extraInitial.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k,S,hk,run,hs⟩

end PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended

namespace PetersenSignedHint
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_18284_aux.Certificate
open PEqualNP.Outside.L_meta_18284_aux.Bound

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem binary_bound {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.extraInitial) : 17 ≤ k := by
  classical
  by_cases hh : Extended.supplied ∈ S
  · have diff : Extended.bit 128 Extended.target ≠ Extended.bit 640 Extended.target := by decide +kernel
    obtain ⟨a,ha,ne⟩ := Extended.live_row_difference run diff
    have checked : Extended.extraInitial.all (fun a =>
        (Extended.bit 128 a == Extended.bit 640 a) || (a == pin 0)) = true := by decide +kernel
    have h := List.all_eq_true.mp checked a (raw a ha)
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    have eq := h.resolve_left ne
    have h0 : pin 0 ∈ S := eq ▸ ha
    have different : pin 0 ≠ Extended.supplied := by decide +kernel
    let rest := (S.erase (pin 0)).erase Extended.supplied
    let front := pin 0 :: Extended.supplied :: rest.toList
    have nd : front.Nodup := by
      simp [front,rest,different,Finset.nodup_toList]
    have hs : front.toFinset = S := by
      ext z
      simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
      by_cases h₀ : z = pin 0
      · simpa [h₀] using h0
      · by_cases h₁ : z = Extended.supplied
        · simpa [h₁] using hh
        · simp [h₀,h₁]
    have hrun := Extended.list_run run front nd hs
    have same : restrictRows (morph 0) (Extended.observe Extended.target) = observe graph := funext (morphGoal 0)
    have hzero : restrictRows (morph 0) (Extended.observe Extended.supplied) = fun _ => false := by
      funext r
      change Extended.bit (morph 0 r) Extended.supplied = false
      have bf := morphPin 0 0 r
      rw [destSelf] at bf
      have b : Extended.bit (morph 0 r) (pin 0) = false := by simpa [bit,zero] using bf
      have hbit : (Extended.bit (morph 0 r) (pin 0) && Extended.bit (morph 0 r) (pin 2)) = false := by simp [b]
      simpa [Extended.supplied,Extended.bit] using hbit
    have supplyRoots : supply true (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph 0))) := by
      intro z hz
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hz
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      have hr := raw w (hs ▸ List.mem_toFinset.mpr hw)
      change w ∈ Extended.initial ++ [Extended.supplied] at hr
      rcases List.mem_append.mp hr with un | bonus
      · obtain ⟨l,rfl⟩ := pinOfMem un
        exact availPin 0 l
      · obtain rfl : w = Extended.supplied := by simpa using bonus
        exact Or.inr (Or.inl ⟨false,hzero⟩)
    have need := projected_bound (morph 0) hrun (same ▸ observe_proper graph_proper)
      Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
    have c₁ := restrictSelf (0 : Fin 10)
    have c₂ : Constant (restrictRows (morph 0) (Extended.observe Extended.supplied)) := ⟨false,hzero⟩
    have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph 0))) := by
      change 2 ≤ mass (restrictRows (morph 0) (Extended.observe (pin 0)) ::
        restrictRows (morph 0) (Extended.observe Extended.supplied) :: _)
      simp only [mass_cons,cost,if_pos c₁,if_pos c₂]
      omega
    omega
  · apply binaryFloor run
    intro a ha
    have h := raw a ha
    change a ∈ Extended.initial ++ [Extended.supplied] at h
    rcases List.mem_append.mp h with h | h
    · exact h
    · have eq : a = Extended.supplied := by simpa using h
      exact (hh (eq ▸ ha)).elim

/-- The free nonedge product leaves the signed binary-gate lower bound
at seventeen, so an eighteen-gate realization has at most one NOT. -/
theorem seeded_binary (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k,S,hk,run,raw⟩ := Extended.realizeExtra C legal hC
  have lo := binary_bound run raw
  have eq : PEqualNP.NotBracket.notCount C = C.gates.countP Extended.isNot := by
    unfold PEqualNP.NotBracket.notCount
    rw [List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro g _
    cases g with
    | mk op ins => cases op <;> rfl
  have total : C.gates.length = C.gates.countP Extended.isNot + C.gates.countP (fun g => !Extended.isNot g) := by
    simpa using List.length_eq_countP_add_countP (l:=C.gates) Extended.isNot
  change 17 + PEqualNP.NotBracket.notCount C ≤ C.gates.length
  omega

end PetersenSignedHint
namespace PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_18284_aux.Bound

def tapVal (p : Fin 13) : Sig :=
  if h : p.val < 10 then pin ⟨p.val,h⟩
  else if p.val = 10 then supplied else if p.val = 11 then zero else one

def product (p q : Fin 13) := tapVal p &&& tapVal q
def normProduct (p q : Fin 13) := nrm true (product p q)

def physicalBank (p q : Fin 13) := extraInitial ++ [product p q]
def liveBank (p q : Fin 13) := extraInitial ++ [normProduct p q]

theorem physicalRun (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (p q : Fin 13) (correct : ∀ r : Row, C.eval ((physicalBank p q).map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ w ∈ S, w ∈ liveBank p q := by
  have he : (execute C.gates (physicalBank p q)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact correct r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates (physicalBank p q)) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates (physicalBank p q) legal (u:=true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have plain : extraInitial.all plainWord = true := by decide +kernel
  simp only [physicalBank,List.map_append,List.map_cons,List.map_nil,nrm_map plain] at sub
  exact ⟨k,S,hk,run,sub⟩

theorem nonzeroLive {k S} (run : Live true target k S) : zero ∉ S := by
  intro h
  exact (live_proper run zero h).1 rfl

end PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended

namespace PetersenProduct4813Full
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_18284_aux.Certificate
open PEqualNP.Outside.L_meta_18284_aux.Bound
open PetersenProductFloor

def nineTap (v : Fin 10) (p : Fin 13) : Sig :=
  if h : p.val < 10 then dest v ⟨p.val,h⟩
  else if p.val = 10 then dest v 0 &&& dest v 2 else if p.val = 11 then zero else one

theorem tapBit (v : Fin 10) (p : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.tapVal p) = bit r (nineTap v p) := by
  by_cases h : p.val < 10
  · simpa [Extended.tapVal,nineTap,h] using morphPin v ⟨p.val,h⟩ r
  · by_cases hs : p.val = 10
    · simp only [Extended.tapVal,nineTap,dif_neg h,if_pos hs,Extended.supplied,
        Extended.bit,bit,BitVec.getLsbD_and]
      change (Extended.bit (morph v r) (pin 0) && Extended.bit (morph v r) (pin 2)) =
        (bit r (dest v 0) && bit r (dest v 2))
      rw [morphPin,morphPin]
    · by_cases hx : p.val=11
      · simp [Extended.tapVal,nineTap,h,hs,hx,Extended.bit,bit,Extended.zero,zero]
      · simp [Extended.tapVal,nineTap,h,hs,hx,Extended.bit,bit,Extended.one,one,(morph v r).isLt,r.isLt]

def projectedProduct (v : Fin 10) (p q : Fin 13) :=
  let word := nineTap v p &&& nineTap v q
  if Extended.bit 0 (Extended.product p q) then ~~~word else word

theorem productBit (v : Fin 10) (p q : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.normProduct p q) = bit r (projectedProduct v p q) := by
  have eq : Extended.bit (morph v r) (Extended.product p q) = bit r (nineTap v p &&& nineTap v q) := by
    change ((Extended.tapVal p &&& Extended.tapVal q).getLsbD (morph v r).val) = _
    simp only [bit,BitVec.getLsbD_and]
    exact congrArg₂ Bool.and (tapBit v p r) (tapBit v q r)
  cases h : Extended.bit 0 (Extended.product p q) with
  | false => simpa [Extended.normProduct,Extended.nrm,projectedProduct,h] using eq
  | true => simpa [Extended.normProduct,Extended.nrm,projectedProduct,h,Extended.neg,
      Extended.bit,bit,BitVec.getLsbD_not,(morph v r).isLt,r.isLt] using congrArg Bool.not eq

def anchorData : Array (Nat × Nat × Nat) := #[(0,0,0),(0,64,576),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,64,576),(0,0,0),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(0,0,0),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(0,0,0),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(0,0,0),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(0,0,0),(4,512,576),(4,512,576),(4,512,576),(4,512,576),(4,512,576),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(0,0,0),(5,512,528),(5,512,528),(5,512,528),(5,512,528),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(0,0,0),(7,32,33),(8,256,264),(9,64,66),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(7,32,33),(0,0,0),(7,32,33),(7,32,33),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(8,256,264),(7,32,33),(0,0,0),(8,256,264),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(9,64,66),(7,32,33),(8,256,264),(0,0,0),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,128,640),(0,0,0),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0)]
def data (p q : Fin 13) := anchorData.getD (13*p.val+q.val) (0,0,0)
def vertex (p q : Fin 13) : Fin 10 := Fin.ofNat 10 (data p q).1
def rowLo (p q : Fin 13) : Extended.Row := Fin.ofNat 1024 (data p q).2.1
def rowHi (p q : Fin 13) : Extended.Row := Fin.ofNat 1024 (data p q).2.2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem anchorFacts : ∀ p q : Fin 13,
    Extended.normProduct p q ∈ Extended.extraInitial ∨ Extended.normProduct p q = Extended.zero ∨
    (vertex p q ≠ 6 ∧ pin (vertex p q) ≠ Extended.normProduct p q ∧
     projectedProduct (vertex p q) p q = zero ∧
     Extended.bit (rowLo p q) Extended.target ≠ Extended.bit (rowHi p q) Extended.target ∧
     (Extended.liveBank p q).all (fun a =>
       (Extended.bit (rowLo p q) a == Extended.bit (rowHi p q) a) || (a == pin (vertex p q))) = true) := by
  decide +kernel

theorem twoProductFloor (p q : Fin 13) {k S} (run : Extended.Live true Extended.target k S)
    (sub : ∀ a ∈ S, a ∈ Extended.liveBank p q)
    (difficult : Impossible true graph 14 (rep 0).toFinset) : 17 ≤ k := by
  classical
  let b := Extended.normProduct p q
  have base (notnew : b ∉ S ∨ b ∈ Extended.extraInitial) : 17 ≤ k := by
    apply PetersenSignedHint.binary_bound run
    intro a ha
    rcases List.mem_append.mp (sub a ha) with l|r
    · exact l
    · have e : a=b := by simpa [b] using r
      subst a
      exact notnew.resolve_left (fun h => h ha)
  by_cases live : b ∈ S
  · rcases anchorFacts p q with duplicate|z|facts
    · exact base (Or.inr duplicate)
    · exact (Extended.nonzeroLive run (z ▸ live)).elim
    · obtain ⟨avoid,distinct,dead,diff,check⟩ := facts
      let v := vertex p q
      obtain ⟨a,ha,neq⟩ := Extended.live_row_difference run diff
      have h := List.all_eq_true.mp check a (sub a ha)
      simp only [Bool.or_eq_true,beq_iff_eq] at h
      have hv : pin v ∈ S := (h.resolve_left neq) ▸ ha
      let rest := (S.erase (pin v)).erase b
      let front := pin v :: b :: rest.toList
      have nd : front.Nodup := by simp [front,rest,distinct,v,b]
      have hs : front.toFinset = S := by
        ext w
        simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
        by_cases h0 : w=pin v
        · simpa [h0] using hv
        · by_cases h1 : w=b
          · simpa [h1] using live
          · simp [h0,h1]
      have hrun := Extended.list_run run front nd hs
      have same : restrictRows (morph v) (Extended.observe Extended.target) = observe graph := funext (morphGoal v)
      have zeroB : restrictRows (morph v) (Extended.observe b) = fun _ => false := by
        funext r
        change Extended.bit (morph v r) (Extended.normProduct p q) = false
        rw [productBit,dead]
        simp [bit,zero]
      have avail : supply true ((projectedInputs v).map observe)
          ((front.map Extended.observe).map (restrictRows (morph v))) := by
        intro x hx
        obtain ⟨_,hw,rfl⟩ := List.mem_map.mp hx
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hw
        have mem := sub w (hs ▸ List.mem_toFinset.mpr hw)
        change w ∈ (Extended.initial ++ [Extended.supplied]) ++ [b] at mem
        rcases List.mem_append.mp mem with before|last
        · rcases List.mem_append.mp before with raw|bonus
          · obtain ⟨j,rfl⟩ := pinOfMem raw
            rw [restrictPin]
            rcases destMem v j with z|r
            · rw [z]
              exact Or.inr (Or.inl ⟨false,funext fun a => by simp [observe,bit,zero]⟩)
            · exact Or.inl (List.mem_map.mpr ⟨_,List.mem_append_left _ r,rfl⟩)
          · obtain rfl : w=Extended.supplied := by simpa using bonus
            have e : restrictRows (morph v) (Extended.observe Extended.supplied) =
                observe (dest v 0 &&& dest v 2) := by
              funext r
              exact (tapBit v 10 r)
            rw [e]
            exact Or.inl (List.mem_map.mpr ⟨_,List.mem_append_right _ (by simp),rfl⟩)
        · obtain rfl : w=b := by simpa using last
          exact Or.inr (Or.inl ⟨false,zeroB⟩)
      have bound := projected_bound (morph v) hrun (same ▸ observe_proper graph_proper)
        Reach.start avail (L:=15) (same ▸ projectedFloor v avoid difficult)
      have c1 := restrictSelf v
      have c2 : Constant (restrictRows (morph v) (Extended.observe b)) := ⟨false,zeroB⟩
      have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph v))) := by
        change 2 ≤ mass (restrictRows (morph v) (Extended.observe (pin v)) ::
          restrictRows (morph v) (Extended.observe b) :: _)
        simp only [mass_cons,cost,if_pos c1,if_pos c2]
        omega
      omega
  · exact base (Or.inl live)

end PetersenProduct4813Full
namespace PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18284_aux.Bound

def quietTap (p : Fin 13) : Sig :=
  if h : p.val < 10 then pin ⟨p.val,h⟩ else if p.val=12 then one else zero

def quietProduct (p q : Fin 13) := quietTap p &&& quietTap q
def quietBank (p q : Fin 13) := initial ++ [zero,quietProduct p q]

theorem quietRun (C : Circuit) (legal : FanInTwo C) (mono : Monotone2 C)
    (p q : Fin 13) (correct : ∀ r, C.eval ((quietBank p q).map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live false target k S ∧
      ∀ w ∈ S, w ∈ quietBank p q := by
  have he : (execute C.gates (quietBank p q)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact correct r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=false) (execute C.gates (quietBank p q)) C.output
  rw [he] at out
  have hn : ∀ g ∈ C.gates, isNot g=false := by
    intro g hg
    have op := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with h|h <;> simp [isNot,h]
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates (quietBank p q) legal (u:=false) (fun _ => hn) hp
    (out.resolve_right (fun h => h hp))
  exact ⟨k,S,hk,run,fun w hw => by simpa [nrm] using sub w hw⟩

theorem excludesConstants {k S} (run : Live false target k S) (w) (hw : w ∈ S) : w ≠ zero ∧ w ≠ one := live_proper run w hw
end PEqualNP.Outside.L_meta_18284_aux.Certificate.Extended

namespace PEqualNP.Outside.L_meta_18284_aux.Bound
open PEqualNP.Outside.L_meta_18284_aux.Certificate
theorem availMono (i j : Fin 10) :
    Available false (inputs.map observe) (restrictRows (morph i) (Extended.observe (pin j))) := by
  rw [restrictPin]
  rcases destMem i j with h|h
  · rw [h]; exact Or.inr (Or.inl ⟨false, funext fun r => by simp [observe,bit,zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_,h,rfl⟩)
theorem binaryMonoFloor (floor : Lower false inputs graph 16) {k S} (run : Extended.Live false Extended.target k S) (raw : ∀ w ∈ S, w ∈ Extended.initial) :
    18 ≤ k := by
  classical
  cases k with
  | zero =>
    obtain ⟨eq,_⟩ := run
    have h := raw Extended.target (eq.symm ▸ Finset.mem_singleton_self _)
    exact False.elim ((by decide +kernel : Extended.target ∉ Extended.initial) h)
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hne,_,ht⟩ := run
    obtain ⟨i,rfl⟩ := pinOfMem (raw a (by simp))
    obtain ⟨j,rfl⟩ := pinOfMem (raw b (by simp))
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    have hdl : d < 4 := by rcases hd with h|⟨_,h⟩ <;> omega
    let p := separating i j ⟨d,hdl⟩
    have wh := separates i j ⟨d,hdl⟩ hij
    obtain ⟨w,hw,hchange⟩ := Extended.live_row_difference ht wh.1
    have member : pin i ∈ U := by
      rcases Finset.mem_insert.mp hw with rfl|hu
      · exact False.elim (hchange wh.2.1)
      · obtain ⟨l,rfl⟩ := pinOfMem (raw w (by simp [hu]))
        by_cases he : l = i
        · simpa [he] using hu
        · exact False.elim (hchange (wh.2.2 l he))
    let V := insert (Extended.bin d (pin i) (pin j)) U
    have ha : pin i ∈ V := Finset.mem_insert_of_mem member
    let front := pin i :: (V.erase (pin i)).toList
    have nd : front.Nodup := List.nodup_cons.mpr ⟨by simp,Finset.nodup_toList _⟩
    have eqV : front.toFinset = V := by
      simp only [front,List.toFinset_cons,Finset.toList_toFinset,Finset.insert_erase ha]
    have hr := Extended.list_run ht front nd eqV
    have goalEq : restrictRows (morph i) (Extended.observe Extended.target) = observe graph := funext (morphGoal i)
    have supplyRoots : supply false (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph i))) := by
      intro z hz
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hz
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      have hm : w ∈ V := eqV ▸ List.mem_toFinset.mpr hw
      rcases Finset.mem_insert.mp hm with rfl|hm
      · rw [Extended.obs_bin, restrict_comb]
        obtain ⟨op,x,y,eq,hx,hy,hcx,_⟩ := comb_prime (u:=false) (a:=restrictRows (morph i) (Extended.observe (pin i))) (b:=restrictRows (morph i) (Extended.observe (pin j))) hd (availMono i i) (availMono i j)
        rw [eq]
        apply from_constant op (Or.inl ?_) hx hy
        by_contra hn
        have hc := restrictSelf i
        simp only [cost, ite_eq_right hn, ite_eq_left hc] at hcx
        omega
      · obtain ⟨l,rfl⟩ := pinOfMem (raw w (by simp [hm]))
        exact availMono i l
    have need := projected_bound (morph i) hr (goalEq ▸ observe_proper graph_proper) Reach.start supplyRoots (L:=16) (goalEq ▸ floor)
    have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (morph i))) := by
      change 1 ≤ mass (restrictRows (morph i) (Extended.observe (pin i)) :: _)
      rw [mass_cons]
      simp only [cost, ite_eq_left (restrictSelf i)]
      omega
    omega
end PEqualNP.Outside.L_meta_18284_aux.Bound

namespace PetersenQuiet4813
open PEqualNP.Outside.L_meta_18284_aux.Certificate PEqualNP.Outside.L_meta_18284_aux.Bound
open PetersenProduct4813Full

def quietProjectedTap (v : Fin 10) (p : Fin 13) : Sig :=
  if h : p.val < 10 then dest v ⟨p.val,h⟩ else if p.val=12 then one else zero

theorem quietBit (v : Fin 10) (p : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.quietTap p) = bit r (quietProjectedTap v p) := by
  by_cases h : p.val < 10
  · simpa [Extended.quietTap,quietProjectedTap,h] using morphPin v ⟨p.val,h⟩ r
  · by_cases h1 : p.val=12 <;> simp [Extended.quietTap,quietProjectedTap,h,h1,Extended.bit,bit,
      Extended.one,one,Extended.zero,zero,(morph v r).isLt,r.isLt]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem quietFacts : ∀ p q : Fin 13,
    Extended.quietProduct p q ∈ Extended.initial ∨ Extended.quietProduct p q = Extended.zero ∨
    Extended.quietProduct p q = Extended.one ∨
    (pin (vertex p q) ≠ Extended.quietProduct p q ∧
     quietProjectedTap (vertex p q) p &&& quietProjectedTap (vertex p q) q = zero ∧
     Extended.bit (rowLo p q) Extended.target ≠ Extended.bit (rowHi p q) Extended.target ∧
     (Extended.quietBank p q).all (fun a =>
       (Extended.bit (rowLo p q) a == Extended.bit (rowHi p q) a) || (a == pin (vertex p q))) = true) := by
  decide +kernel

theorem quietFloor (p q : Fin 13) {k S} (run : Extended.Live false Extended.target k S)
    (sub : ∀ a ∈ S, a ∈ Extended.quietBank p q) (floor : Lower false inputs graph 16) : 18 ≤ k := by
  classical
  let b := Extended.quietProduct p q
  have base (absent : b ∉ S ∨ b ∈ Extended.initial) : 18 ≤ k := by
    apply binaryMonoFloor floor run
    intro w hw
    rcases List.mem_append.mp (sub w hw) with raw|last
    · exact raw
    · have e : w=Extended.zero ∨ w=b := by simpa [b] using last
      rcases e with rfl|rfl
      · exact ((Extended.excludesConstants run _ hw).1 rfl).elim
      · exact absent.resolve_left (fun h => h hw)
  by_cases live : b ∈ S
  · rcases quietFacts p q with dup|z|one|facts
    · exact base (Or.inr dup)
    · exact ((Extended.excludesConstants run b live).1 z).elim
    · exact ((Extended.excludesConstants run b live).2 one).elim
    · obtain ⟨distinct,dead,diff,check⟩ := facts
      let v := vertex p q
      obtain ⟨a,ha,neq⟩ := Extended.live_row_difference run diff
      have h := List.all_eq_true.mp check a (sub a ha)
      simp only [Bool.or_eq_true,beq_iff_eq] at h
      have hv : pin v ∈ S := (h.resolve_left neq) ▸ ha
      let rest := (S.erase (pin v)).erase b
      let front := pin v :: b :: rest.toList
      have nd : front.Nodup := by simp [front,rest,distinct,v,b]
      have hs : front.toFinset = S := by
        ext w
        simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
        by_cases h0 : w=pin v
        · simpa [h0] using hv
        · by_cases h1 : w=b
          · simpa [h1] using live
          · simp [h0,h1]
      have hrun := Extended.list_run run front nd hs
      have same : restrictRows (morph v) (Extended.observe Extended.target) = observe graph := funext (morphGoal v)
      have zeroB : restrictRows (morph v) (Extended.observe b) = fun _ => false := by
        funext r
        change (Extended.quietTap p &&& Extended.quietTap q).getLsbD (morph v r).val = false
        rw [BitVec.getLsbD_and]
        change (Extended.bit (morph v r) (Extended.quietTap p) && Extended.bit (morph v r) (Extended.quietTap q)) = false
        rw [quietBit,quietBit]
        change ((quietProjectedTap v p).getLsbD r.val && (quietProjectedTap v q).getLsbD r.val) = false
        rw [←BitVec.getLsbD_and,dead]
        simp [zero]
      have avail : supply false (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph v))) := by
        intro t ht
        obtain ⟨_,hw,rfl⟩ := List.mem_map.mp ht
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hw
        have member := hs ▸ List.mem_toFinset.mpr hw
        rcases List.mem_append.mp (sub w member) with raw|last
        · obtain ⟨j,rfl⟩ := pinOfMem raw
          exact availMono v j
        · have e : w=Extended.zero ∨ w=b := by simpa [b] using last
          rcases e with rfl|rfl
          · exact ((Extended.excludesConstants run _ member).1 rfl).elim
          · exact Or.inr (Or.inl ⟨false,zeroB⟩)
      have bound := projected_bound (morph v) hrun (same ▸ observe_proper graph_proper)
        Reach.start avail (L:=16) (same ▸ floor)
      have c1 := restrictSelf v
      have c2 : Constant (restrictRows (morph v) (Extended.observe b)) := ⟨false,zeroB⟩
      have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph v))) := by
        change 2 ≤ mass (restrictRows (morph v) (Extended.observe (pin v)) ::
          restrictRows (morph v) (Extended.observe b) :: _)
        simp only [mass_cons,cost,if_pos c1,if_pos c2]
        omega
      omega
  · exact base (Or.inl live)

end PetersenQuiet4813
namespace Monotonicity

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (l l' : List Bool)
    (h : R l l') : C.eval l ≤ C.eval l' := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
  rw [wires_eq, wires_eq]
  exact (fold_R C.gates hops _ _ h).2 C.output

end Monotonicity
namespace Petersen7217
abbrev V := Fin 10
def nums : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
def pet (x : V → Bool) := nums.any fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10))
end Petersen7217
namespace PetersenMonotoneHint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Petersen7217
open Monotonicity

abbrev Point := V → Bool
def frame (x : Point) (b : Bool) := List.ofFn x ++ [b]

private theorem oneRel {a b : Bool} (h : a ≤ b) : R [a] [b] := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i with
  | zero => exact h
  | succ i =>
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)] <;> exact le_refl _

private theorem smaller (C : Circuit) (hm : Monotone2 C) {x y : Point} {a b : Bool}
    (xy : ∀ i, x i ≤ y i) (ab : a ≤ b) :
    C.eval (frame x a) ≤ C.eval (frame y b) :=
  eval_mono C hm _ _ (R_append (R_ofFn x y xy) (oneRel ab))

private def ends (e : ℕ) (i : V) :=
  decide (i = Fin.ofNat 10 (e/10) ∨ i = Fin.ofNat 10 (e%10))

private theorem edgeFacts : ∀ i : Fin nums.length,
    pet (ends (nums.get i)) = true ∧
      (ends (nums.get i) 0 && ends (nums.get i) 2) = false := by
  decide +kernel

/-- Every minimal positive assignment is an edge, so the free product
can be fixed to false throughout a monotone circuit for Petersen. -/
theorem remove_product (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Point, C.eval (frame x (x 0 && x 2)) = pet x) :
    ∀ x : Point, C.eval (frame x false) = pet x := by
  intro x
  cases hp : pet x with
  | false =>
    have order := smaller C hm (x:=x) (y:=x) (a:=false) (b:=x 0 && x 2)
      (fun _ => le_refl _) (Bool.false_le _)
    rw [hc,hp] at order
    exact le_antisymm order (Bool.false_le _)
  | true =>
    obtain ⟨e,he,hon⟩ := List.any_eq_true.mp hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    obtain ⟨hy,hz⟩ := edgeFacts i
    have hxy : ∀ k, ends (nums.get i) k ≤ x k := by
      intro k
      simp only [Bool.and_eq_true] at hon
      obtain ⟨ha,hb⟩ := hon
      unfold ends
      by_cases h : k = Fin.ofNat 10 (nums.get i/10) ∨ k = Fin.ofNat 10 (nums.get i%10)
      · rcases h with rfl | rfl <;> simp [ha,hb]
      · simp [h]
    have low := hc (ends (nums.get i))
    rw [hz,hy] at low
    have order := smaller C hm (a:=false) (b:=false) hxy (le_refl _)
    rw [low] at order
    exact Bool.eq_true_of_true_le order

end PetersenMonotoneHint

namespace PetersenProductMono4813
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Petersen7217
open PEqualNP.Outside.L_meta_18284_aux.Certificate
def base (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
def extra (ls : List (Fin 12)) (x : Fin 10 → Bool) :=
  GateOp.and.eval (ls.map fun a => (base x).getD a.val false)

def quietBase (x : Fin 10 → Bool) := List.ofFn x ++ [false]
def quietExtra (ls : List (Fin 12)) (x : Fin 10 → Bool) :=
  GateOp.and.eval (ls.map fun a => (quietBase x).getD a.val false)

def quietPort (p : Fin 12) : Fin 13 := ⟨p.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem portValue : ∀ j : Fin 12, ∀ r : Extended.Row,
    Extended.bit r (Extended.quietTap (quietPort j)) = (quietBase (Extended.assign r)).getD j.val false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullBank : ∀ r : Extended.Row, (Extended.initial ++ [Extended.zero]).map (Extended.bit r) =
    quietBase (Extended.assign r) := by decide +kernel

theorem quietLayout (ls : List (Fin 12)) (sz : ls.length ≤ 2) : ∃ p q : Fin 13, ∀ r : Extended.Row,
    (Extended.quietBank p q).map (Extended.bit r) = quietBase (Extended.assign r) ++ [quietExtra ls (Extended.assign r)] := by
  have glue (p q : Fin 13) (r : Extended.Row) :
      (Extended.quietBank p q).map (Extended.bit r) =
        quietBase (Extended.assign r) ++ [Extended.bit r (Extended.quietTap p) && Extended.bit r (Extended.quietTap q)] := by
    change ((Extended.initial ++ [Extended.zero]) ++ [Extended.quietProduct p q]).map (Extended.bit r) = _
    simp only [List.map_append,fullBank,List.map_cons,List.map_nil,
      Extended.quietProduct,Extended.bit,BitVec.getLsbD_and]
  have neutral (r : Extended.Row) : Extended.bit r (Extended.quietTap 12) = true := by
    simp [Extended.quietTap,Extended.bit,Extended.one,r.isLt]
  cases ls with
  | nil =>
    refine ⟨12,12,fun r => ?_⟩
    rw [glue,neutral]
    rfl
  | cons a l =>
    cases l with
    | nil =>
      refine ⟨quietPort a,12,fun r => ?_⟩
      rw [glue,portValue,neutral]
      simp [quietExtra,GateOp.eval]
    | cons b l =>
      have empty : l=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at sz
        omega
      subst l
      refine ⟨quietPort a,quietPort b,fun r => ?_⟩
      rw [glue,portValue,portValue]
      simp [quietExtra,GateOp.eval]

theorem afterMonotone (floor : Lower false inputs graph 16) (C : Circuit) (ls : List (Fin 12)) (hlen : ls.length ≤ 2)
    (hm : Monotone2 C) (legal : FanInTwo C) (small : C.size ≤ 17)
    (correct : ∀ x, C.eval (base x ++ [extra ls x]) = pet x) : False := by
  let g : Gate := ⟨.and,ls.map Fin.val⟩
  let B : Circuit := ⟨g::C.gates,C.output⟩
  have mono : Monotone2 B := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact ⟨by simp [g],by simpa [g] using hlen⟩
    · exact hm a ha
  have original (x) : B.eval (PetersenMonotoneHint.frame x (x 0 && x 2)) = pet x := by
    change C.eval (base x ++ [g.op.eval (g.inputs.map fun i => (base x).getD i false)]) = _
    simpa only [g,extra,List.map_map,Function.comp_def] using correct x
  have reduced := PetersenMonotoneHint.remove_product B mono original
  have after (x : Fin 10 → Bool) : C.eval (quietBase x ++ [quietExtra ls x]) = pet x := by
    have hh := reduced x
    change C.eval (quietBase x ++ [g.op.eval (g.inputs.map fun i => (quietBase x).getD i false)]) = _ at hh
    simpa only [g,quietExtra,List.map_map,Function.comp_def] using hh
  have agrees (x : Fin 10 → Bool) : pet x = Extended.f10 x := by
    simp [pet,nums,Extended.f10,List.any_cons,Bool.or_assoc]
  obtain ⟨p,q,hrow⟩ := quietLayout ls hlen
  have correctRows (r : Extended.Row) : C.eval ((Extended.quietBank p q).map (Extended.bit r)) = Extended.bit r Extended.target := by
    rw [hrow,after,agrees,Extended.rowTarget]
  obtain ⟨k,S,cap,run,sub⟩ := Extended.quietRun C legal hm p q correctRows
  have bound := PetersenQuiet4813.quietFloor p q run sub floor
  have len : C.gates.countP (fun g => !Extended.isNot g) ≤ C.gates.length := List.countP_le_length
  change C.gates.length ≤ 17 at small
  omega

end PetersenProductMono4813
namespace PetersenProduct4813Finish

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18284_aux.Certificate
open PetersenProductMono4813

def port (p : Fin 12) : Fin 13 := ⟨p.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem portValue : ∀ j : Fin 12, ∀ r : Extended.Row,
    Extended.bit r (Extended.tapVal (port j)) = (base (Extended.assign r)).getD j.val false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullBank : ∀ r : Extended.Row, Extended.extraInitial.map (Extended.bit r) =
    base (Extended.assign r) := by decide +kernel

theorem layout (ls : List (Fin 12)) (sz : ls.length ≤ 2) : ∃ p q : Fin 13, ∀ r : Extended.Row,
    (Extended.physicalBank p q).map (Extended.bit r) = base (Extended.assign r) ++ [extra ls (Extended.assign r)] := by
  have glue (p q : Fin 13) (r : Extended.Row) :
      (Extended.physicalBank p q).map (Extended.bit r) =
        base (Extended.assign r) ++ [Extended.bit r (Extended.tapVal p) && Extended.bit r (Extended.tapVal q)] := by
    simp only [Extended.physicalBank,List.map_append,fullBank,List.map_cons,List.map_nil,
      Extended.product,Extended.bit,BitVec.getLsbD_and]
  have neutral (r : Extended.Row) : Extended.bit r (Extended.tapVal 12) = true := by
    simp [Extended.tapVal,Extended.bit,Extended.one,r.isLt]
  cases ls with
  | nil =>
    refine ⟨12,12,fun r => ?_⟩
    rw [glue,neutral]
    rfl
  | cons a l =>
    cases l with
    | nil =>
      refine ⟨port a,12,fun r => ?_⟩
      rw [glue,portValue,neutral]
      simp [extra,GateOp.eval]
    | cons b l =>
      have empty : l=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at sz
        omega
      subst l
      refine ⟨port a,port b,fun r => ?_⟩
      rw [glue,portValue,portValue]
      simp [extra,GateOp.eval]

theorem compulsoryMono (C : Circuit) (ls : List (Fin 12)) (legal : FanInTwo C) (small : C.size ≤ 17)
    (sz : ls.length ≤ 2) (correct : ∀ x, C.eval (base x ++ [extra ls x]) = Extended.f10 x)
    (difficult : Impossible true graph 14 (PetersenProductFloor.rep 0).toFinset) : Monotone2 C := by
  obtain ⟨p,q,rows⟩ := layout ls sz
  have works (r : Extended.Row) : C.eval ((Extended.physicalBank p q).map (Extended.bit r)) =
      Extended.bit r Extended.target := by rw [rows,correct,Extended.rowTarget]
  obtain ⟨k,S,budget,run,sub⟩ := Extended.physicalRun C legal p q works
  have floor := PetersenProduct4813Full.twoProductFloor p q run sub difficult
  have split := List.length_eq_countP_add_countP (l:=C.gates) Extended.isNot
  change C.gates.length ≤ 17 at small
  have z : C.gates.countP Extended.isNot = 0 := by omega
  intro g hg
  obtain ⟨op,arity⟩ := legal g hg
  refine ⟨?_,arity⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  rcases op with h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · have pos : 0 < C.gates.countP Extended.isNot :=
      List.countP_pos_iff.2 ⟨g,hg,by simp [Extended.isNot,h]⟩
    omega

theorem contradiction (nineMonotone : Lower false inputs graph 16) (C : Circuit) (ls : List (Fin 12)) (legal : FanInTwo C) (small : C.size ≤ 17)
    (sz : ls.length ≤ 2) (correct : ∀ x, C.eval (base x ++ [extra ls x]) = Extended.f10 x)
    (difficult : Impossible true graph 14 (PetersenProductFloor.rep 0).toFinset) : False := by
  have mono := compulsoryMono C ls legal small sz correct difficult
  apply PetersenProductMono4813.afterMonotone nineMonotone C ls sz mono legal small
  intro x
  rw [correct]
  simp [Extended.f10, Petersen7217.pet,
    Petersen7217.nums,List.any_cons,Bool.or_assoc]

end PetersenProduct4813Finish

open PEqualNP.Outside.L_meta_18284_aux.Certificate
theorem petersenTwoBonusBridge (signed02 : Impossible true graph 14 (PetersenProductFloor.rep 0).toFinset) (ordinaryMono : Lower false inputs graph 16) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  classical
  intro C ls legal small sz
  by_contra! correct
  exact PetersenProduct4813Finish.contradiction ordinaryMono C ls legal small sz correct
    signed02
