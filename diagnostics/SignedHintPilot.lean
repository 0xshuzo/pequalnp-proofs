import PEqualNP.Outside.L_meta_18284

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
      simp [supplied,PEqualNP.Outside.L_meta_18284_aux.Bound.pin,assign,bit]
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
      simp [front,rest,different]
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
