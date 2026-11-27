import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_816

open PEqualNP.CircuitLowerBounds
abbrev K := ZMod 2
abbrev X (n : ℕ) := Fin n → K

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

theorem z_not (A : K) : (!decide (A = 1)) = decide (A + 1 = 1) := by revert A; decide
theorem z_one (A : K) :
    decide (List.count true [decide (A = 1)] % 2 = 0) = decide (A + 1 = 1) := by revert A; decide
theorem z_two (A B : K) :
    decide (List.count true [decide (A = 1), decide (B = 1)] % 2 = 0) = decide (A + B + 1 = 1) := by
  revert A B; decide
theorem z_eq (a b : K) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by revert a b; decide

/-- The weight of a wire as a linear form. -/
def phi {n : ℕ} (w : X n) : X n →ₗ[K] K where
  toFun x := dotProduct w x
  map_add' := dotProduct_add w
  map_smul' c x := by simp [dotProduct_smul]

theorem finrank_cut {n : ℕ} (D : Submodule K (X n)) (w : X n) :
    Module.finrank K D ≤ Module.finrank K ↥(D ⊓ LinearMap.ker (phi w)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D (LinearMap.ker (phi w))
  have h2 := LinearMap.finrank_range_add_finrank_ker (phi w)
  have h3 : Module.finrank K ↥(LinearMap.range (phi w)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (phi w))
    simpa using this
  have h4 := Submodule.finrank_le (D ⊔ LinearMap.ker (phi w))
  omega


abbrev Z (t : Nat) := Fin t → Bool

structure Leaf (k t : Nat) where
  U : Submodule K (X k)
  p : Z t → X k

def Leaf.Here {k t} (L : Leaf k t) (z : Z t) (x : X k) := x - L.p z ∈ L.U

def inp {k t} (x : X k) (z : Z t) :=
  List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z

abbrev Val {k t} (gs : List Gate) (x : X k) (z : Z t) (w : Nat) :=
  (W gs (inp x z)).getD w false

def HasForm {k t} (L : Leaf k t) (f : X k → Z t → Bool) :=
  ∃ (a : X k) (c : Z t → K), ∀ z x, L.Here z x →
    f x z = decide (dotProduct a x + c z = 1)

def Aff {k t} (gs : List Gate) (L : Leaf k t) :=
  ∀ w : Nat, HasForm L (fun x z => Val gs x z w)

def gateFun {k t} (gs : List Gate) (g : Gate) (x : X k) (z : Z t) :=
  g.op.eval (g.inputs.map fun i => Val gs x z i)

theorem restrictF {k t} {L Q : Leaf k t} {f} (h : HasForm L f)
    (sub : ∀ z x, Q.Here z x → L.Here z x) : HasForm Q f := by
  obtain ⟨a,c,h⟩ := h
  exact ⟨a,c,fun z x hx => h z x (sub z x hx)⟩

theorem liftAff {k t} {gs : List Gate} {g : Gate} {L : Leaf k t}
    (h : Aff gs L) (hg : HasForm L (gateFun gs g)) : Aff (gs++[g]) L := by
  intro w
  by_cases hw : w=k+t+gs.length
  · obtain ⟨a,c,rep⟩ := hg
    refine ⟨a,c,fun z x hx => ?_⟩
    have eq := new_wire gs g (inp x z)
    rw [show (inp x z).length=k+t by simp [inp], ←hw] at eq
    exact eq.trans (rep z x hx)
  · obtain ⟨a,c,rep⟩ := h w
    refine ⟨a,c,fun z x hx => ?_⟩
    exact (old_wire gs g (inp x z) w (by simpa [inp] using hw)).trans (rep z x hx)

theorem zeroRow {k t} (L : Leaf k t) (f : X k → Z t → Bool) (v : Z t → Bool)
    (eq : ∀ z x, L.Here z x → f x z = v z) : HasForm L f := by
  refine ⟨0,fun z => if v z then 1 else 0,fun z x hx => ?_⟩
  rw [eq z x hx]
  cases e : v z <;> simp [e]

theorem baseAff (k t : Nat) (L : Leaf k t) : Aff [] L := by
  intro w
  by_cases hw : w<k
  · refine ⟨Pi.single ⟨w,hw⟩ 1,0,fun z x _ => ?_⟩
    change (inp x z).getD w false = _
    unfold inp
    rw [List.getD_append _ _ _ _ (by simpa using hw),List.getD_eq_getElem _ _ (by simpa using hw)]
    simp only [List.getElem_ofFn,single_dotProduct,one_mul,Pi.zero_apply,add_zero]
  · apply zeroRow L _ (fun z => (List.ofFn z).getD (w-k) false)
    intro z x _
    change (inp x z).getD w false = _
    simp [inp,List.getD_eq_getElem?_getD,List.getElem?_append_right,hw,Nat.le_of_not_gt hw]

def Good (g : Gate) := g.inputs.length≤2 ∧
    (g.op=.and ∨ g.op=.or ∨ g.op=.mod 2 ∨ (g.op=.not ∧ g.inputs.length=1))
def Paid (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2
noncomputable def cost (gs : List Gate) := gs.countP (fun g => @decide
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) (Classical.propDecidable _))

theorem freeForm {k t} (gs : List Gate) (g : Gate) (L : Leaf k t)
    (h : Aff gs L) (good : Good g) (free : ¬Paid g) : HasForm L (gateFun gs g) := by
  obtain ⟨hl,ops⟩ := good
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨m,r⟩⟩⟩
  · apply zeroRow L _ (fun _ => g.op.eval [])
    intro z x _; simp [gateFun,hin]
  · obtain ⟨a,c,eq⟩ := h i
    change ∀ z x, L.Here z x → Val gs x z i = decide (dotProduct a x+c z=1) at eq
    rcases ops with op | op | op | ⟨op,_⟩
    · exact ⟨a,c,fun z x hx => by simpa [gateFun,op,hin,GateOp.eval] using eq z x hx⟩
    · exact ⟨a,c,fun z x hx => by simpa [gateFun,op,hin,GateOp.eval] using eq z x hx⟩
    · refine ⟨a,fun z => c z+1,fun z x hx => ?_⟩
      unfold gateFun; rw [op,hin]
      change decide (List.count true [Val gs x z i] % 2 = 0) = _
      rw [eq z x hx,z_one,add_assoc]
    · refine ⟨a,fun z => c z+1,fun z x hx => ?_⟩
      unfold gateFun; rw [op,hin]
      change (!Val gs x z i) = _
      rw [eq z x hx,z_not,add_assoc]
  · rcases ops with op | op | op | ⟨_,bad⟩
    · exact (free ⟨Or.inl op,by simp [hin]⟩).elim
    · exact (free ⟨Or.inr op,by simp [hin]⟩).elim
    · obtain ⟨a,c,ha⟩ := h i
      obtain ⟨b,e,hb⟩ := h j
      change ∀ z x, L.Here z x → Val gs x z i = decide (dotProduct a x+c z=1) at ha
      change ∀ z x, L.Here z x → Val gs x z j = decide (dotProduct b x+e z=1) at hb
      refine ⟨a+b,fun z => c z+e z+1,fun z x hx => ?_⟩
      unfold gateFun; rw [op,hin]
      change decide (List.count true [Val gs x z i,Val gs x z j] % 2 = 0) = _
      rw [ha z x hx,hb z x hx,z_two,add_dotProduct]
      congr 2 <;> ring
    · simp [hin] at bad
  · simp [hin] at hl

theorem scalar_bits (v : K) : v=0 ∨ v=1 := by revert v; decide

theorem find_direction {k t} (L : Leaf k t) (pos : 0<Module.finrank K L.U) :
    ∃ (a v : X k), v∈L.U ∧ dotProduct a v=1 := by
  classical
  have ne : L.U ≠ ⊥ := fun e => (Nat.ne_of_gt pos) (Submodule.finrank_eq_zero.mpr e)
  obtain ⟨v,hv,hn⟩ : ∃ v ∈ L.U, v ≠ 0 := by
    by_contra! no
    apply ne
    apply le_antisymm _ bot_le
    intro x hx; simpa using no x hx
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  exact ⟨Pi.single i 1,v,hv,by simpa [single_dotProduct] using (scalar_bits (v i)).resolve_left hi⟩

theorem halves {k t} (L : Leaf k t) (a : X k) (c : Z t → K)
    (v : X k) (hv : v∈L.U) (ha : dotProduct a v=1) :
    ∃ Q : K → Leaf k t, (∀ d,Module.finrank K (Q d).U+1=Module.finrank K L.U) ∧
      ∀ d z x,(Q d).Here z x ↔ L.Here z x ∧ dotProduct a x+c z=d := by
  classical
  let D := L.U ⊓ LinearMap.ker (phi a)
  let sh (d : K) (z : Z t) := (d-(dotProduct a (L.p z)+c z)) • v
  let Q (d : K) : Leaf k t := ⟨D,fun z => L.p z+sh d z⟩
  have less : D < L.U := by
    apply lt_of_le_of_ne inf_le_left
    intro e
    have vd : v∈D := by change v ∈ L.U ⊓ LinearMap.ker (phi a); rw [e]; exact hv
    have h : dotProduct a v=0 := vd.2
    rw [ha] at h; exact one_ne_zero h
  have lt := Submodule.finrank_lt_finrank_of_lt less
  have lb := finrank_cut L.U a
  change Module.finrank K L.U ≤ Module.finrank K D + 1 at lb
  refine ⟨Q,fun d => by change Module.finrank K D+1=_; omega,?_⟩
  intro d z x
  have shift : sh d z∈L.U := L.U.smul_mem _ hv
  have sd : dotProduct a (sh d z)=d-(dotProduct a (L.p z)+c z) := by simp [sh,dotProduct_smul,ha]
  change x-(L.p z+sh d z)∈ D ↔ x-L.p z∈L.U ∧ _
  have ee : x-(L.p z+sh d z)=x-L.p z-sh d z := by abel
  rw [ee]
  constructor
  · intro h
    have hh := L.U.add_mem h.1 shift
    have hk : dotProduct a (x-L.p z-sh d z)=0 := h.2
    rw [dotProduct_sub,dotProduct_sub,sd] at hk
    exact ⟨by simpa using hh,by linear_combination hk⟩
  · rintro ⟨h,e⟩
    refine ⟨L.U.sub_mem h shift,?_⟩
    change dotProduct a (x-L.p z-sh d z)=0
    rw [dotProduct_sub,dotProduct_sub,sd]
    linear_combination e

def Splits {k t} (L : Leaf k t) (gs : List Gate) :=
  ∃ (Q : K → Leaf k t) (a : X k) (c : Z t → K),
    (∀ d,Module.finrank K (Q d).U + 1 = Module.finrank K L.U) ∧
    (∀ d z x,(Q d).Here z x ↔ L.Here z x ∧ dotProduct a x+c z=d) ∧
    ∀ d, Aff gs (Q d)

theorem fixedForm {k t} {Q : Leaf k t} {gs : List Gate} {g : Gate} {i j : Nat} {b : Bool}
    (hop : g.op=.and ∨ g.op=.or) (hin : g.inputs=[i,j] ∨ g.inputs=[j,i])
    (fixed : ∀ z x, Q.Here z x → Val gs x z i = b) (h : Aff gs Q) :
    HasForm Q (gateFun gs g) := by
  obtain ⟨a,c,rep⟩ := h j
  have commute (x y : Bool) : g.op.eval [x,y]=g.op.eval [y,x] := by
    rcases hop with op|op <;> rw [op] <;> cases x <;> cases y <;> rfl
  have step (z : Z t) (x : X k) (hx : Q.Here z x) :
      gateFun gs g x z=g.op.eval [b, Val gs x z j] := by
    unfold gateFun
    rcases hin with ins|ins <;> rw [ins]
    · change g.op.eval [Val gs x z i,Val gs x z j]=_
      rw [fixed z x hx]
    · change g.op.eval [Val gs x z j,Val gs x z i]=_
      rw [fixed z x hx]; exact commute _ _
  rcases hop with op|op <;> cases b
  · apply zeroRow Q _ (fun _ => false)
    intro z x hx; rw [step z x hx,op]; simp [GateOp.eval]
  · refine ⟨a,c,fun z x hx => ?_⟩
    rw [step z x hx,op]
    simpa only [GateOp.eval,List.all_cons,List.all_nil,Bool.true_and,Bool.and_true] using rep z x hx
  · refine ⟨a,c,fun z x hx => ?_⟩
    rw [step z x hx,op]
    simpa only [GateOp.eval,List.any_cons,List.any_nil,Bool.false_or,Bool.or_false] using rep z x hx
  · apply zeroRow Q _ (fun _ => true)
    intro z x hx; rw [step z x hx,op]; simp [GateOp.eval]

theorem split_wire {k t} (L : Leaf k t) (gs : List Gate) (g : Gate) (i j : Nat)
    (hop : g.op=.and ∨ g.op=.or) (hin : g.inputs=[i,j] ∨ g.inputs=[j,i])
    (h : Aff gs L) (a : X k) (c : Z t → K)
    (rep : ∀ z x,L.Here z x → Val gs x z i=decide (dotProduct a x+c z=1))
    (v : X k) (hv : v∈L.U) (ha : dotProduct a v=1) : Splits L (gs++[g]) := by
  obtain ⟨Q,dim,mem⟩ := halves L a c v hv ha
  refine ⟨Q,a,c,dim,mem,?_⟩
  intro d
  have sub : ∀ z x,(Q d).Here z x → L.Here z x := fun z x hx => ((mem d z x).mp hx).1
  have hh : Aff gs (Q d) := fun w => restrictF (h w) sub
  apply liftAff hh
  apply fixedForm (b:=decide (d=1)) hop hin _ hh
  intro z x hx
  rw [rep z x (sub z x hx),((mem d z x).mp hx).2]

theorem splitGate {k t} (gs : List Gate) (g : Gate) (L : Leaf k t)
    (paid : Paid g) (dim : 0<Module.finrank K L.U) (h : Aff gs L) : Splits L (gs++[g]) := by
  classical
  obtain ⟨op,len⟩ := paid
  obtain ⟨i,j,ins⟩ := List.length_eq_two.mp len
  obtain ⟨a,c,ha⟩ := h i
  obtain ⟨b,e,hb⟩ := h j
  by_cases va : ∃ v∈L.U,dotProduct a v=1
  · obtain ⟨v,vin,one⟩ := va
    exact split_wire L gs g i j op (Or.inl ins) h a c ha v vin one
  by_cases vb : ∃ v∈L.U,dotProduct b v=1
  · obtain ⟨v,vin,one⟩ := vb
    exact split_wire L gs g j i op (Or.inr ins) h b e hb v vin one
  have flat (w : Nat) (a : X k) (c : Z t → K)
      (rep : ∀ z x,L.Here z x → Val gs x z w=decide (dotProduct a x+c z=1))
      (zero : ¬∃ v∈L.U,dotProduct a v=1) :
      ∀ z x,L.Here z x → Val gs x z w=Val gs (L.p z) z w := by
    intro z x hx
    have d0 : dotProduct a (x-L.p z)=0 := (scalar_bits _).resolve_right (fun one => zero ⟨_,hx,one⟩)
    rw [dotProduct_sub,sub_eq_zero] at d0
    rw [rep z x hx,rep z (L.p z) (by simp [Leaf.Here]),d0]
  have same : HasForm L (gateFun gs g) := by
    apply zeroRow L _ (fun z => gateFun gs g (L.p z) z)
    intro z x hx
    simp only [gateFun,ins,List.map_cons,List.map_nil,flat i a c ha va z x hx,flat j b e hb vb z x hx]
  obtain ⟨w,v,vin,one⟩ := find_direction L dim
  obtain ⟨Q,rank,mem⟩ := halves L w 0 v vin one
  refine ⟨Q,w,0,rank,mem,?_⟩
  intro d j
  exact restrictF (liftAff h same j) (fun z x hx => ((mem d z x).mp hx).1)

def Family (k t : Nat) (gs : List Gate) :=
  ∃ P : Fin (2^cost gs) → Leaf k t,
    (∀ i,Module.finrank K (P i).U = k - cost gs) ∧
    (∀ z x, ∃! i,(P i).Here z x) ∧ ∀ i, Aff gs (P i)

theorem families (k t : Nat) (gs : List Gate) (ok : ∀g∈gs,Good g) (bound : cost gs ≤ k) : Family k t gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    let L : Leaf k t := ⟨⊤,0⟩
    refine ⟨fun _ => L,fun _ => by simp [L,cost,Module.finrank_pi],?_,fun _ => baseAff _ _ L⟩
    intro z x
    refine ⟨⟨0,by simp [cost]⟩,by simp [Leaf.Here,L],?_⟩
    intro j _
    apply Fin.ext
    change j.val=0
    have h : j.val<1 := by simpa [cost] using j.isLt
    omega
  | append_singleton gs g IH =>
    have og := ok g (by simp)
    have ogs : ∀g'∈gs,Good g' := fun g' hg' => ok g' (List.mem_append_left _ hg')
    by_cases pay : Paid g
    · have cc : cost (gs++[g]) = cost gs+1 := by
        unfold cost; rw [List.countP_append]; simp [show (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 from pay]
      obtain ⟨P,rank,partition,aff⟩ := IH ogs (by omega)
      have hh (i) : Splits (P i) (gs++[g]) :=
        splitGate gs g (P i) pay (by rw [rank]; omega) (aff i)
      choose Q a c nextRank here nextAff using hh
      let E : Fin (2^cost (gs++[g])) ≃ Fin (2^cost gs) × K :=
        Fintype.equivOfCardEq (by simp [cc,pow_succ,ZMod.card])
      refine ⟨fun j => Q (E j).1 (E j).2,?_,?_,fun j => nextAff _ _⟩
      · intro j
        have h1 := nextRank (E j).1 (E j).2
        rw [rank] at h1
        change Module.finrank K (Q (E j).1 (E j).2).U = k-cost (gs++[g])
        have cap : cost gs+1≤k := by simpa only [cc] using bound
        rw [cc]
        omega
      · intro z x
        obtain ⟨i,hi,ui⟩ := partition z x
        let d := dotProduct (a i) x+c i z
        refine ⟨E.symm (i,d),?_,?_⟩
        · simp only [Equiv.apply_symm_apply]
          exact (here i d z x).mpr ⟨hi,rfl⟩
        · intro j hj
          obtain ⟨hp,hv⟩ := (here (E j).1 (E j).2 z x).mp hj
          have h1 := ui _ hp
          apply E.injective
          rw [Equiv.apply_symm_apply]
          apply Prod.ext h1
          simpa [d,h1] using hv.symm
    · have cc : cost (gs++[g])=cost gs := by
        unfold cost; rw [List.countP_append]; simp [show ¬((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) from pay]
      obtain ⟨P,rank,partition,aff⟩ := IH ogs (by omega)
      unfold Family
      rw [cc]
      exact ⟨P,rank,partition,fun i => liftAff (aff i) (freeForm gs g (P i) (aff i) og pay)⟩

def Answer (k t : Nat) (C : Circuit) (b : Nat) :=
    ∃ (U : Fin (2^b) → Submodule K (X k)) (a : Fin (2^b) → X k)
      (p : Fin (2^b) → Z t → X k) (c : Fin (2^b) → Z t → K),
      (∀ i, Module.finrank K (U i) = k-b) ∧
      (∀ z x,∃! i,x-p i z∈U i) ∧
      ∀ i z u,u∈U i → C.eval (inp (p i z+u) z) = decide (dotProduct (a i) u+c i z=1)

theorem terminal (k t : Nat) (C : Circuit) : Answer k t C k := by
  classical
  let E : Fin (2^k) ≃ X k := Fintype.equivOfCardEq (by simp [X,K,ZMod.card])
  let c (i : Fin (2^k)) (z : Z t) : K := if C.eval (inp (E i) z) then 1 else 0
  refine ⟨fun _ => ⊥,fun _ => 0,fun i _ => E i,c,by simp,?_,?_⟩
  · intro z x
    refine ⟨E.symm x,by simp,?_⟩
    intro i hi
    apply E.injective
    have he : x-E i=0 := hi
    rw [Equiv.apply_symm_apply]
    exact (sub_eq_zero.mp he).symm
  · intro i z u hu
    have zu : u=0 := hu
    subst u
    cases e : C.eval (inp (E i) z) <;> simp [c,e]

theorem solution (k t : Nat) (C : Circuit) (ok : ∀g∈C.gates,Good g) :
    Answer k t C (min (cost C.gates) k) := by
  classical
  by_cases small : cost C.gates≤k
  · rw [Nat.min_eq_left small]
    obtain ⟨P,dim,part,aff⟩ := families k t C.gates ok small
    choose a c rep using fun i => aff i C.output
    refine ⟨fun i => (P i).U,a,fun i => (P i).p,
      fun i z => dotProduct (a i) ((P i).p z)+c i z,dim,part,?_⟩
    intro i z u hu
    change Val C.gates ((P i).p z+u) z C.output = _
    have inside : (P i).Here z ((P i).p z+u) := by simpa [Leaf.Here] using hu
    have e : Val C.gates ((P i).p z+u) z C.output = decide (dotProduct (a i) ((P i).p z+u)+c i z=1) := rep i z _ inside
    rw [e,dotProduct_add]
    simp only [add_assoc,add_left_comm,add_comm]
  · rw [Nat.min_eq_right (by omega)]
    exact terminal k t C
end PEqualNP.Outside.L_lib_816

theorem PEqualNP.Outside.L_lib_816 : ∀ (k t : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  let Z := Fin t → Bool
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) →
    let s := C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let b := min s k
    let I := Fin (2^b)
    ∃ (U : I → Submodule F V) (a : I → V) (p : I → Z → V) (c : I → Z → F),
      (∀ i, Module.finrank F (U i) = k-b) ∧
      (∀ (z : Z) (x : V), ∃! i : I, x-p i z ∈ U i) ∧
      ∀ (i : I) (z : Z) (u : V), u ∈ U i →
        C.eval (List.ofFn (fun j : Fin k => decide ((p i z + u) j = 1)) ++ List.ofFn z) =
          decide (dotProduct (a i) u + c i z = 1) := by
  intro k t
  dsimp only
  intro C _ ok
  exact PEqualNP.Outside.L_lib_816.solution k t C ok
