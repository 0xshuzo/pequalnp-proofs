import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_865_aux

abbrev N (a : Nat) := 2*a+1
def site {a : Nat} (s : Fin (N a)) (d : Nat) : Fin (N a) :=
  ⟨(s.val+d) % N a, Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem site_zero {a} (s : Fin (N a)) : site s 0 = s := by
  apply Fin.ext; simp [site,Nat.mod_eq_of_lt s.isLt]

theorem site_comp {a} (s : Fin (N a)) (i j : Nat) : site (site s i) j = site s (i+j) := by
  apply Fin.ext
  simp [site, Nat.mod_add_mod, Nat.add_assoc]

theorem site_full {a} (s : Fin (N a)) : site s (N a) = s := by
  apply Fin.ext
  simp [site,Nat.mod_eq_of_lt s.isLt]

theorem offsets {a} (s t : Fin (N a)) :
    ∃ d < N a, site s d = t := by
  have hs := s.isLt
  have ht := t.isLt
  by_cases st : s.val ≤ t.val
  · refine ⟨t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(t.val-s.val)) % N a = t.val
    rw [show s.val+(t.val-s.val)=t.val by omega,Nat.mod_eq_of_lt ht]
  · refine ⟨N a+t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(N a+t.val-s.val)) % N a = t.val
    rw [show s.val+(N a+t.val-s.val)=t.val+N a by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

def Mark {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) : Prop :=
  h s ≠ 0 ∧ (∀ d : Nat, 0 < d → d < a → h (site s d) = 0) ∧
    (h (site s a) = 0 ∨ h (site s a) = h s)

def Canon {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) :=
  Mark h s ∧ ¬ Mark h (site s a)

theorem mark_spacing {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s : Fin (N a)} {d : Nat} (pos : 0<d) (lt : d<N a)
    (hs : Mark h s) (ht : Mark h (site s d)) : d=a ∨ d=a+1 := by
  have fwd : a≤d := by
    by_contra! small
    exact ht.1 (hs.2.1 d pos small)
  have rt : site (site s d) (N a-d) = s := by
    rw [site_comp,show d+(N a-d)=N a by omega,site_full]
  have rev : a≤N a-d := by
    by_contra! small
    exact hs.1 (rt ▸ (ht.2.1 _ (by omega) small))
  dsimp [N] at rev lt
  omega

theorem has_canon {a : Nat} {A : Type*} [Zero A] (ha : 2≤a) {h : Fin (N a) → A}
    {s : Fin (N a)} (hs : Mark h s) : ∃ t, Canon h t := by
  by_cases ht : Mark h (site s a)
  · refine ⟨site s a,ht,?_⟩
    intro bad
    rw [site_comp] at bad
    have eq := mark_spacing (d:=a+a) (by omega) (by dsimp [N];omega) hs bad
    omega
  · exact ⟨s,hs,ht⟩

theorem canon_unique {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s t : Fin (N a)} (hs : Canon h s) (ht : Canon h t) : s=t := by
  obtain ⟨d,lt,eq⟩ := offsets s t
  subst t
  by_cases zero : d=0
  · subst d; exact (site_zero s).symm
  have split := mark_spacing (d:=d) (by omega) lt hs.1 ht.1
  rcases split with e | e
  · subst d; exact (hs.2 ht.1).elim
  · subst d
    apply False.elim
    apply ht.2
    rw [site_comp,show a+1+a=N a by dsimp [N];omega,site_full]
    exact hs.1


def slot {a : Nat} (i : Fin a) : Fin (N a) := ⟨a+1+i.val,by dsimp [N];have := i.isLt;omega⟩
def pivot (a : Nat) : Fin (N a) := ⟨a,by dsimp [N];omega⟩
def srcZero (a : Nat) : Fin (N a) := ⟨0,Nat.succ_pos _⟩
abbrev Code (A : Type*) [Zero A] (a : Nat) := {c : A // c ≠ 0} × Bool × (Fin a → A)

def pack {a : Nat} {A : Type*} [Zero A] (x : Code A a) (i : Fin (N a)) : A :=
  if z : i.val=0 then x.1.val else if sm : i.val<a then 0 else if eq : i.val=a then (if x.2.1 then x.1.val else 0)
  else x.2.2 ⟨i.val-(a+1),by have := i.isLt;dsimp [N] at this;omega⟩

theorem pack_zero {a} {A : Type*} [Zero A] (x : Code A a) :
    pack x (srcZero a)=x.1.val := by simp [pack,srcZero]
theorem pack_pivot {a} {A : Type*} [Zero A] (ha : 0<a) (x : Code A a) :
    pack x (pivot a)=(if x.2.1 then x.1.val else 0) := by simp [pack,pivot,Nat.ne_of_gt ha]
theorem pack_slot {a} {A : Type*} [Zero A] (x : Code A a) (j : Fin a) :
    pack x (slot j)=x.2.2 j := by
  have z : a+1+j.val ≠ 0 := by omega
  have sm : ¬ a+1+j.val < a := by omega
  have eq : a+1+j.val ≠ a := by omega
  simp [pack,slot,z,sm,eq]

def normMark {a : Nat} {A : Type*} [Zero A] (w : Fin (N a) → A) : Prop :=
  w (srcZero a) ≠ 0 ∧ (∀ (i : Fin (N a)), ((0 : ℕ) < (Fin.val i)) → ((Fin.val i) < a) → w i = (0 : A)) ∧
    (w (pivot a)=0 ∨ w (pivot a)=w (srcZero a))

theorem pack_normal {a} {A : Type*} [Zero A] (ha : 0<a) (x : Code A a) : normMark (pack x) := by
  refine ⟨by rw [pack_zero];exact x.1.property,?_,?_⟩
  · intro i pos small
    unfold pack
    rw [dif_neg (Nat.ne_of_gt pos),dif_pos small]
  · rw [pack_pivot ha,pack_zero]
    cases x.2.1 <;> simp

noncomputable def unpack {a} {A : Type*} [Zero A] (w : Fin (N a) → A) (ok : normMark w) : Code A a := by
  classical
  exact (⟨w (srcZero a),ok.1⟩,decide (w (pivot a)=w (srcZero a)),fun i => w (slot i))

theorem unpack_pack {a} {A : Type*} [Zero A] (ha : 0<a) (x : Code A a) :
    unpack (pack x) (pack_normal ha x)=x := by
  classical
  rcases x with ⟨⟨c,hc⟩,b,v⟩
  apply Prod.ext
  · exact Subtype.ext (pack_zero _)
  · apply Prod.ext
    · change decide (pack _ (pivot _) = pack _ (srcZero _)) = b
      rw [pack_pivot ha,pack_zero]
      cases b <;> simp [Ne.symm hc]
    · funext i;exact pack_slot _ _

theorem pack_unpack {a} {A : Type*} [Zero A] (ha : 0<a) (w : Fin (N a) → A) (ok : normMark w) :
    pack (unpack w ok)=w := by
  classical
  funext i
  by_cases z : i.val=0
  · have e : i=srcZero a := Fin.ext z
    rw [e,pack_zero];rfl
  by_cases sm : i.val<a
  · unfold pack
    rw [dif_neg z,dif_pos sm]
    exact (ok.2.1 i (Nat.pos_of_ne_zero z) sm).symm
  by_cases eq : i.val=a
  · have e : i=pivot a := Fin.ext eq
    rw [e,pack_pivot ha]
    rcases ok.2.2 with h|h
    · simp [unpack,h,Ne.symm ok.1] <;> exact Eq.symm
    · simp [unpack,h]
  let j : Fin a := ⟨i.val-(a+1),by have := i.isLt;dsimp [N] at this;omega⟩
  have e : i=slot j := Fin.ext (by dsimp [j,slot];omega)
  rw [e,pack_slot];rfl

noncomputable def codeEquiv {a : Nat} {A : Type*} [Zero A] (ha : 0<a) :
    Code A a ≃ {w : Fin (N a) → A // normMark w} where
  toFun x := ⟨pack x,pack_normal ha x⟩
  invFun w := unpack w.val w.property
  left_inv := unpack_pack ha
  right_inv w := Subtype.ext (pack_unpack ha _ _)

theorem shift_zero {a} (s : Fin (N a)) : s+srcZero a=s := add_zero s
theorem shift_idx {a} (s i : Fin (N a)) : s+i=site s i.val := rfl

noncomputable def shiftEquiv {a : Nat} {A : Type*} [Zero A] (s : Fin (N a)) :
    {h : Fin (N a) → A // Mark h s} ≃ {w : Fin (N a) → A // normMark w} := by
  classical
  let e := Equiv.addLeft s
  have eqv (h : Fin (N a) → A) : Mark h s ↔ normMark (h ∘ e) := by
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    have ez : e (srcZero a)=s := shift_zero _
    have ea : e (pivot a)=site s a := rfl
    simp only [Function.comp_apply,ez,ea]
    constructor
    · rintro ⟨nz,zeros,tail⟩
      exact ⟨nz,fun (j : Fin (N a)) pos sm => zeros j.val pos sm,tail⟩
    · rintro ⟨nz,zeros,tail⟩
      refine ⟨nz,?_,tail⟩
      intro d pos sm
      exact zeros ⟨d,by dsimp [N];omega⟩ pos sm
  exact {
    toFun := fun h => ⟨h.val ∘ e,(eqv h.val).mp h.property⟩
    invFun := fun w => ⟨w.val ∘ e.symm,(eqv _).mpr (by simpa [Function.comp_def] using w.property)⟩
    left_inv := fun h => Subtype.ext (by funext j; simp [Function.comp_def])
    right_inv := fun w => Subtype.ext (by funext j; simp [Function.comp_def]) }

def lastI {a} (ha : 0<a) : Fin a := ⟨a-1,by omega⟩

theorem site_slot {a} (j : Fin a) : site (pivot a) (j.val+1)=slot j := by
  apply Fin.ext
  change (a+(j.val+1))%N a=a+1+j.val
  rw [Nat.mod_eq_of_lt (by have := j.isLt;dsimp [N];omega)]
  omega

def lastTail {a : Nat} {A : Type*} [Zero A] (c : A) (on : Bool) (j : Fin a) : A :=
  if j.val+1=a then (if on then c else 0) else 0

theorem lastTail_last {a} {A : Type*} [Zero A] (ha : 0<a) (c : A) (on : Bool) :
    lastTail c on (lastI ha) = (if on then c else 0) := by
  simp only [lastTail,lastI,show a-1+1=a by omega,if_true]

theorem other_pivot {a} {A : Type*} [Zero A] (ha : 0<a) (c : {u : A // u ≠ 0})
    (b : Bool) (v : Fin a → A) :
    Mark (pack (a:=a) (c,b,v)) (pivot a) ↔
      b=true ∧ ∃ t, v=lastTail c.val t := by
  classical
  let x : Code A a := (c,b,v)
  change Mark (pack x) (pivot a) ↔ _
  have center : pack x (pivot a) = if b then c.val else 0 := pack_pivot ha x
  have atSlot (j : Fin a) : pack x (site (pivot a) (j.val+1))=v j := by
    rw [site_slot,pack_slot]
  have endpoint : pack x (site (pivot a) a)=v (lastI ha) := by
    have h := atSlot (lastI ha)
    simpa only [lastI,show a-1+1=a by omega] using h
  constructor
  · intro hm
    have be : b=true := by
      rcases b with _|_
      · exact (hm.1 (by simpa using center)).elim
      · rfl
    have edge := hm.2.2
    rw [endpoint,center,be] at edge
    simp only [ite_true] at edge
    refine ⟨be,decide (v (lastI ha)=c.val),?_⟩
    funext j
    by_cases e : j.val+1=a
    · have je : j=lastI ha := Fin.ext (by dsimp [lastI];omega)
      subst j
      rw [lastTail_last ha]
      rcases edge with z | z <;> simp [z,Ne.symm c.property]
    · have z := hm.2.1 (j.val+1) (by omega) (by have := j.isLt;omega)
      rw [atSlot] at z
      simpa [lastTail,e] using z
  · rintro ⟨be,t,vv⟩
    have cc : pack x (pivot a)=c.val := by simpa [be] using center
    refine ⟨by rw [cc];exact c.property,?_,?_⟩
    · intro d pos sm
      let j : Fin a := ⟨d-1,by omega⟩
      have je : j.val+1=d := by dsimp [j];omega
      have ar := atSlot j
      rw [je,vv] at ar
      simpa [lastTail,je,Nat.ne_of_lt sm] using ar
    · rw [endpoint,vv,lastTail_last ha,cc]
      cases t <;> simp

abbrev DoubleCode (A : Type*) [Zero A] := {c : A // c ≠ 0} × Bool

noncomputable def doubleEquiv {a} {A : Type*} [Zero A] (ha : 0<a) :
    DoubleCode A ≃ {x : Code A a // Mark (pack x) (pivot a)} := by
  classical
  let f (x : DoubleCode A) : {x : Code A a // Mark (pack x) (pivot a)} :=
    ⟨(x.1,true,lastTail x.1.val x.2),(other_pivot ha _ _ _).mpr ⟨rfl,x.2,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨c,b⟩ ⟨d,t⟩ eq
    have ce : c=d := congrArg (fun z => z.val.1) eq
    subst d
    have endEq := congrArg (fun z => z.val.2.2 (lastI ha)) eq
    change lastTail c.val b (lastI ha)=lastTail c.val t (lastI ha) at endEq
    rw [lastTail_last ha,lastTail_last ha] at endEq
    cases b <;> cases t <;> simp_all [c.property,Ne.symm c.property] <;> rfl
  · rintro ⟨⟨c,b,v⟩,h⟩
    obtain ⟨rfl,t,rfl⟩ := (other_pivot ha c b v).mp h
    exact ⟨(c,t),rfl⟩

theorem site_shift {a} (s i : Fin (N a)) (d : Nat) : s+site i d=site (s+i) d := by
  apply Fin.ext
  change (s.val+((i.val+d)%N a))%N a = (((s.val+i.val)%N a)+d)%N a
  simp [Nat.add_mod_mod,Nat.mod_add_mod,Nat.add_assoc]

theorem mark_rot {a} {A : Type*} [Zero A] (h : Fin (N a) → A) (s i : Fin (N a)) :
    Mark (h ∘ Equiv.addLeft s) i ↔ Mark h (s+i) := by
  have ap (z : Fin (N a)) : Equiv.addLeft s z=s+z := rfl
  simp only [Mark,Function.comp_apply,ap,site_shift]

def restrictEquiv {X Y : Type*} (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (rel : ∀ x, p x ↔ q (e x)) : {x // p x} ≃ {y // q y} where
  toFun x := ⟨e x.val,(rel x.val).mp x.property⟩
  invFun y := ⟨e.symm y.val,(rel _).mpr (by simpa using y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)

abbrev Marked {a} (A : Type*) [Zero A] (s : Fin (N a)) := {h : Fin (N a) → A // Mark h s}
abbrev Kept {a} (A : Type*) [Zero A] (s : Fin (N a)) :=
  {w : Marked A s // ¬ Mark w.val (site s a)}

private theorem filterChange {X : Type*} (p : X → Prop) {I J : Fintype X} {d e : DecidablePred p} :
    (@Finset.filter X p d (@Finset.univ X I)).card = (@Finset.filter X p e (@Finset.univ X J)).card := by
  cases Subsingleton.elim I J
  cases Subsingleton.elim d e
  rfl

private theorem cardChange {X : Type*} {I J : Fintype X} : @Fintype.card X I = @Fintype.card X J := by
  cases Subsingleton.elim I J
  rfl

theorem kept_count {a} (A : Type*) [Fintype A] [Zero A] (ha : 0<a) (s : Fin (N a)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    Fintype.card (Kept A s) = 2*(Fintype.card A-1)*((Fintype.card A)^a-1) := by
  classical
  let e : Marked A s ≃ Code A a := (shiftEquiv s).trans (codeEquiv ha).symm
  let q := Fintype.card A
  let occ := fun x : Marked A s => Mark x.val (site s a)
  have rot (w : Marked A s) : pack (e w)=w.val ∘ Equiv.addLeft s := pack_unpack ha _ ((shiftEquiv s) w).property
  have rel (w : Marked A s) : occ w ↔ Mark (pack (e w)) (pivot a) := by
    rw [rot,mark_rot];rfl
  let cut := restrictEquiv e occ (fun x => Mark (pack x) (pivot a)) rel
  have pos : 0<q := Fintype.card_pos_iff.mpr ⟨0⟩
  have nonzero : Fintype.card {c : A // c ≠ 0}=q-1 := by
    rw [Fintype.card_subtype_compl]
    simp [q]
  have allc : Fintype.card (Marked A s) = (q-1)*(2*q^a) := by
    rw [Fintype.card_congr e]
    simp [Code,Fintype.card_prod,Fintype.card_fun,nonzero,q]
  have both : Fintype.card {x : Marked A s // occ x}=(q-1)*2 := by
    rw [Fintype.card_congr cut,←Fintype.card_congr (doubleEquiv (A:=A) ha)]
    simp [DoubleCode,Fintype.card_prod,nonzero]
  have numeric : Fintype.card {x : Marked A s // ¬occ x}=2*(q-1)*(q^a-1) := by
    rw [Fintype.card_subtype_compl,allc,both]
    rw [Nat.mul_sub_left_distrib,Nat.mul_one]
    congr 1 <;> ring
  exact cardChange.trans numeric

def WordHit {a} {A : Type*} [Zero A] (h : Fin (N a) → A) :=
  h=0 ∨ ∃ s, Mark h s

noncomputable def wordsEquiv {a} (A : Type*) [Zero A] (ha : 2 ≤ a) :
    Option (Σ s : Fin (N a), Kept A s) ≃ {h : Fin (N a) → A // WordHit h} := by
  classical
  let f : Option (Σ s : Fin (N a), Kept A s) → {h : Fin (N a) → A // WordHit h}
    | none => ⟨0,Or.inl rfl⟩
    | some ⟨s,w⟩ => ⟨w.val.val,Or.inr ⟨s,w.val.property⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro (_|⟨s,x⟩) (_|⟨t,y⟩) e
    · rfl
    · have h : (0 : Fin (N a) → A)=y.val.val := congrArg Subtype.val e
      exact (y.val.property.1 (congrFun h.symm t)).elim
    · have h : x.val.val=(0 : Fin (N a) → A) := congrArg Subtype.val e
      exact (x.val.property.1 (congrFun h s)).elim
    · have h : x.val.val=y.val.val := congrArg Subtype.val e
      have cy : Canon x.val.val t := h ▸ (show Canon y.val.val t from ⟨y.val.property,y.property⟩)
      have st := canon_unique (show Canon x.val.val s from ⟨x.val.property,x.property⟩) cy
      subst t
      have xy : x=y := Subtype.ext (Subtype.ext h)
      rw [xy]
  · rintro ⟨w,z|⟨s,h⟩⟩
    · exact ⟨none,Subtype.ext z.symm⟩
    · obtain ⟨t,hm,un⟩ := has_canon ha h
      exact ⟨some ⟨t,⟨⟨w,hm⟩,un⟩⟩,rfl⟩

theorem word_count {a} (A : Type*) [Zero A] [Fintype A] (ha : 2≤a) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ((Finset.univ : Finset (Fin (N a) → A)).filter WordHit).card =
       1 + 2*N a*(Fintype.card A-1)*((Fintype.card A)^a-1) := by
  classical
  let q := Fintype.card A
  let r := 2*(q-1)*(q^a-1)
  have f (s : Fin (N a)) : Fintype.card (Kept A s)=r :=
    (cardChange (X:=Kept A s)).trans (kept_count A (by omega) s)
  calc
    _ = Fintype.card {w : Fin (N a) → A // WordHit w} := by rw [Fintype.card_subtype];exact filterChange WordHit
    _ = Fintype.card (Option (Σ s : Fin (N a), Kept A s)) := (Fintype.card_congr (wordsEquiv A ha)).symm
    _ = (∑ s : Fin (N a), Fintype.card (Kept A s))+1 := by rw [Fintype.card_option,Fintype.card_sigma]
    _ = (∑ _s : Fin (N a), r)+1 := congrArg (·+1) (Finset.sum_congr rfl (fun s _ => f s))
    _ = _ := by simp [r,q,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,Nat.add_comm]




open scoped BigOperators
abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F
def coord {n : Nat} (U : Submodule F (W n)) (i : Fin n) : U →ₗ[F] F :=
  (LinearMap.proj i).comp U.subtype
noncomputable def colors {n : Nat} (U : Submodule F (W n)) : Finset (U →ₗ[F] F) := by
  classical
  exact (Finset.univ.image (coord U)).erase 0

theorem mem_colors {n} {U : Submodule F (W n)} {c : U →ₗ[F] F} :
    c ∈ colors U ↔ c ≠ 0 ∧ ∃ i, coord U i=c := by
  classical
  simp [colors]

def encode {n : Nat} (U : Submodule F (W n)) : U →ₗ[F] (↥(colors U) → F) where
  toFun u c := c.val u
  map_add' u v := by funext c; exact map_add c.val u v
  map_smul' b u := by funext c; exact map_smul c.val b u

theorem encode_inj {n : Nat} (U : Submodule F (W n)) : Function.Injective (encode U) := by
  intro x y h
  apply Subtype.ext; funext i
  change coord U i x=coord U i y
  by_cases z : coord U i=0
  · rw [z];rfl
  · exact congrFun h ⟨coord U i,mem_colors.mpr ⟨z,i,rfl⟩⟩

theorem rank_le_colors {n : Nat} (U : Submodule F (W n)) :
    Module.finrank F U ≤ (colors U).card := by
  have rank := LinearMap.finrank_le_finrank_of_injective (encode_inj U)
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using rank

theorem isotropic_labels {n : Nat} (U : Submodule F (W n)) {i j : Fin n}
    (ortho : ∀ x ∈ U, ∀ y ∈ U, x i*y j=x j*y i) :
    coord U i=0 ∨ coord U j=0 ∨ coord U i=coord U j := by
  let L := coord U i
  let R := coord U j
  have bin : ∀ b : F, b=0 ∨ b=1 := by decide +kernel
  have det (u v : U) : L u * R v=R u * L v := ortho u u.property v v.property
  by_cases hL : L=0
  · exact Or.inl hL
  · have ex : ∃ u, L u ≠ 0 := by
      by_contra! h
      exact hL (LinearMap.ext fun u => h u)
    obtain ⟨u,hu⟩ := ex
    have Lu := (bin (L u)).resolve_left hu
    rcases bin (R u) with z | e
    · right;left;ext v
      exact (by simpa [Lu,z] using det u v : R v=0)
    · right;right;ext v
      exact (by simpa [Lu,e] using (det u v).symm : L v=R v)


theorem site_one_inj {a} : Function.Injective (fun s : Fin (N a) => site s 1) := by
  intro s t he
  have eq : site (site s 1) (N a-1)=site (site t 1) (N a-1) := congrArg (fun i => site i (N a-1)) he
  simpa only [site_comp,show 1+(N a-1)=N a by dsimp [N];omega,site_full] using eq

theorem site_offsets_inj {a} (s : Fin (N a)) {i j : Nat} (hi : i<N a) (hj : j<N a)
    (eq : site s i=site s j) : i=j := by
  have e : s+(⟨i,hi⟩ : Fin (N a))=s+(⟨j,hj⟩ : Fin (N a)) := eq
  exact congrArg Fin.val (add_left_cancel e)

theorem domino {a : Nat} (D : Finset (Fin (N a))) (large : a≤D.card)
    (apart : ∀ i ∈ D, site i 1 ∉ D) :
    D.card=a ∧ ∃ u : Fin (N a), ∀ j : Fin a,
      site u (2*j.val+1)∈D ∧ site u (2*j.val+2)∉D := by
  classical
  let E := D.image (fun i => site i 1)
  have dis : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro x hx he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact apart p hp hx
  have count : E.card=D.card := Finset.card_image_of_injective _ site_one_inj
  have union := Finset.card_union_of_disjoint dis
  have room : (D∪E).card≤N a := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have dc : D.card=a := by dsimp [N] at room;omega
  refine ⟨dc,?_⟩
  have one : ((D∪E)ᶜ).card=1 := by
    rw [Finset.card_compl,Fintype.card_fin,union,count,dc]
    dsimp [N];omega
  obtain ⟨u,eq⟩ := Finset.card_eq_one.mp one
  have out : u∉D∪E := by
    have : u∈(D∪E)ᶜ := by rw [eq];simp
    exact Finset.mem_compl.mp this
  have comp {i : Fin (N a)} (ne : i≠u) : i∈D∪E := by
    by_contra h
    have ic := Finset.mem_compl.mpr h
    rw [eq] at ic
    exact ne (Finset.mem_singleton.mp ic)
  have after (d : Nat) (hl : d+1<N a) (pre : site u d∉D) : site u (d+1)∈D := by
    have ne : site u (d+1) ≠ u := by
      intro h
      have bad := site_offsets_inj u hl (Nat.succ_pos _) (h.trans (site_zero u).symm)
      omega
    rcases Finset.mem_union.mp (comp ne) with yes|no
    · exact yes
    · obtain ⟨p,hp,hq⟩ := Finset.mem_image.mp no
      have h := site_one_inj (hq.trans (site_comp u d 1).symm)
      exact (pre (h ▸ hp)).elim
  have odds (j : Nat) (hj : j<a) : site u (2*j+1)∈D := by
    induction j with
    | zero =>
      apply after 0 (by dsimp [N];omega)
      simpa only [site_zero] using (fun hu => out (Finset.mem_union_left _ hu) : u∉D)
    | succ j ih =>
      have hi := ih (by omega)
      have hn := apart _ hi
      rw [site_comp] at hn
      have sub := after (2*j+1+1) (by dsimp [N];omega) hn
      convert sub using 1 <;> congr 2 <;> omega
  refine ⟨u,fun j => ⟨odds j.val j.isLt,?_⟩⟩
  simpa only [site_comp,show 2*j.val+1+1=2*j.val+2 by omega] using apart _ (odds j.val j.isLt)
def oddSite {a} (u : Fin (N a)) (j : Fin a) := site u (2*j.val+1)
def evenSite {a} (u : Fin (N a)) (j : Fin a) := site u (2*j.val+2)

def loc {a} (u : Fin (N a)) : Option (Fin a × Bool) → Fin (N a)
  | none => u
  | some (j,false) => oddSite u j
  | some (j,true) => evenSite u j

noncomputable def chart {a} (u : Fin (N a)) : Option (Fin a × Bool) ≃ Fin (N a) := by
  classical
  apply Equiv.ofBijective (loc u)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro i
    obtain ⟨d,lt,rfl⟩ := offsets u i
    cases d with
    | zero => exact ⟨none,(site_zero u).symm⟩
    | succ j =>
      dsimp [N] at lt
      let k : Fin a := ⟨j/2,by omega⟩
      by_cases e : j%2=0
      · refine ⟨some (k,false),?_⟩
        change site u (2*(j/2)+1)=site u (j+1)
        congr 1;omega
      · refine ⟨some (k,true),?_⟩
        change site u (2*(j/2)+2)=site u (j+1)
        congr 1;omega
  · simp [N,Fintype.card_option,Fintype.card_prod,Nat.mul_comm]

theorem next_odd {a} (u : Fin (N a)) (j : Fin a) : site (oddSite u j) 1=evenSite u j := by
  unfold oddSite evenSite
  rw [site_comp]
theorem next_even {a} (u : Fin (N a)) (j : Fin a) (lt : j.val+1<a) :
    site (evenSite u j) 1=oddSite u ⟨j.val+1,lt⟩ := by
  unfold evenSite oddSite; rw [site_comp] <;> congr 1 <;> omega
theorem last_even {a} (ha : 0<a) (u : Fin (N a)) :
    site (evenSite u (lastI ha)) 1=u := by
  unfold evenSite lastI;rw [site_comp,show 2*(a-1)+2+1=N a by dsimp [N];omega,site_full]

def rawValue {a} (ha : 0<a) (b : Bool) (x : Fin a → F) : Option (Fin a × Bool) → F
  | none => if b then x (lastI ha) else 0
  | some (j,false) => 0
  | some (j,true) => x j

noncomputable def model {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) :
    (Fin a → F) →ₗ[F] W (N a) where
  toFun x i := rawValue ha b x ((chart u).symm i)
  map_add' x y := by
    funext i
    change rawValue ha b (x+y) ((chart u).symm i)=rawValue ha b x ((chart u).symm i)+rawValue ha b y ((chart u).symm i)
    rcases (chart u).symm i with _|⟨j,c⟩
    · cases b <;> simp [rawValue]
    · cases c <;> simp [rawValue]
  map_smul' r x := by
    funext i
    change rawValue ha b (r • x) ((chart u).symm i)=r • rawValue ha b x ((chart u).symm i)
    rcases (chart u).symm i with _|⟨j,c⟩
    · cases b <;> simp [rawValue]
    · cases c <;> simp [rawValue]

theorem at_chart {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (p) :
    model ha u b x (chart u p)=rawValue ha b x p := by
  change rawValue ha b x ((chart u).symm (chart u p))=_
  rw [Equiv.symm_apply_apply]
theorem at_even {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (j) :
    model ha u b x (evenSite u j)=x j := at_chart ha u b x (some (j,true))
theorem at_odd {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) (j) :
    model ha u b x (oddSite u j)=0 := at_chart ha u b x (some (j,false))
theorem at_root {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x : Fin a → F) :
    model ha u b x u=(if b then x (lastI ha) else 0) := at_chart ha u b x none

theorem model_inj {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) : Function.Injective (model ha u b) := by
  intro x y h;funext i
  simpa only [at_even] using congrFun h (evenSite u i)

theorem model_iso {a} (ha : 0<a) (u : Fin (N a)) (b : Bool) (x y : Fin a → F) (i) :
    model ha u b x i * model ha u b y (site i 1)=model ha u b x (site i 1)*model ha u b y i := by
  obtain ⟨w,rfl⟩ := (chart u).surjective i
  rcases w with _|⟨j,c⟩
  · change model ha u b x u * model ha u b y (oddSite u ⟨0,ha⟩)=
        model ha u b x (oddSite u ⟨0,ha⟩)*model ha u b y u
    simp [at_odd]
  · cases c
    · change model ha u b x (oddSite u j)*model ha u b y (site (oddSite u j) 1)=_
      change _=model ha u b x (site (oddSite u j) 1)*model ha u b y (oddSite u j)
      simp [at_odd]
    · change model ha u b x (evenSite u j)*model ha u b y (site (evenSite u j) 1)=
          model ha u b x (site (evenSite u j) 1)*model ha u b y (evenSite u j)
      by_cases lt : j.val+1<a
      · rw [next_even u j lt];simp [at_odd]
      · have e : j=lastI ha := Fin.ext (by have := j.isLt; dsimp [lastI];omega)
        subst j
        rw [last_even ha,at_even,at_even,at_root,at_root]
        cases b <;> simp

def allowed {a m : Nat} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u : Fin (N a)) (b : Bool) :=
  ∀ j : Fin a, h (evenSite u j) = (if j=lastI ha ∧ b=true then h u else 0)

theorem model_sum {a m : Nat} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u : Fin (N a)) (b : Bool)
    (x : Fin a → F) (k : Fin m) :
    (∑ i, h i k * model ha u b x i) =
     h u k*(if b then x (lastI ha) else 0) + ∑ j, h (evenSite u j) k*x j := by
  rw [←Equiv.sum_comp (chart u) (fun i => h i k * model ha u b x i)]
  simp only [at_chart,Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool]
  change h u k*(if b then x (lastI ha) else 0)+_ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [rawValue,chart,loc,mul_zero]

theorem model_checked {a m} (ha : 0<a) (h : Fin (N a) → Fin m → F) (u) (b) :
    (∀ x k, ∑ i, h i k * model ha u b x i=0) ↔ allowed ha h u b := by
  classical
  constructor
  · intro checks j
    funext k
    have e := checks (fun t => if t=j then 1 else 0) k
    rw [model_sum] at e
    by_cases last : j = lastI ha
    · subst j
      cases b <;> simp [mul_ite] at e ⊢
      · exact e
      · exact (show ∀ p q : F, p+q=0 → q=p by decide +kernel) _ _ e
    · cases b <;> simpa [mul_ite,last,Ne.symm last] using e
  · intro ok x k
    rw [model_sum]
    simp_rw [fun j => congrFun (ok j) k]
    cases b <;> simp [ite_apply,ite_mul]
    exact (show ∀ p : F, p+p=0 by decide +kernel) _

def Success {a m} (h : Fin (N a) → Fin m → F) : Prop :=
  ∃ U : Submodule F (W (N a)), Module.finrank F U=a ∧
    (∀ x ∈ U, ∀ k, ∑ i, h i k*x i=0) ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ i, x i*y (site i 1)=x (site i 1)*y i

theorem success_shape {a m} (ha : 2≤a) (h : Fin (N a) → Fin m → F) :
    Success h ↔ ∃ u b, allowed (by omega : 0<a) h u b := by
  classical
  have hp : 0<a := by omega
  constructor
  · rintro ⟨U,dim,checks,iso⟩
    let f := coord U
    have adj (i : Fin (N a)) : f i=0 ∨ f (site i 1)=0 ∨ f i=f (site i 1) :=
      isotropic_labels U (fun x hx y hy => iso x hx y hy i)
    let D := Finset.univ.filter (fun i => f i=0 ∧ f (site i 1)≠0)
    have mem (i) : i∈D ↔ f i=0 ∧ f (site i 1)≠0 := by simp [D]
    have colsz := rank_le_colors U
    rw [dim] at colsz
    have cover : colors U ⊆ D.image (fun v => f (site v 1)) := by
      intro c hc
      obtain ⟨nz,i,atI⟩ := mem_colors.mp hc
      have diff : ∃ j, f j≠c := by
        by_contra! all
        have sub : colors U ⊆ {c} := by
          intro z hz
          obtain ⟨_,i,e⟩ := mem_colors.mp hz
          simpa using e.symm.trans (all i)
        have sz := Finset.card_le_card sub
        rw [Finset.card_singleton] at sz
        omega
      obtain ⟨j,hj⟩ := diff
      obtain ⟨d,_,eq⟩ := offsets j i
      have walk (d : Nat) (hit : f (site j d)=c) : c∈D.image (fun v => f (site v 1)) := by
        induction d with
        | zero => exact (hj (by simpa [site_zero] using hit)).elim
        | succ p ih =>
          by_cases pre : f (site j p)=c
          · exact ih pre
          · have nt : f (site (site j p) 1)=c := by simpa only [site_comp] using hit
            have z : f (site j p)=0 := (adj (site j p)).resolve_right (by
              rintro (e|e)
              · exact nz (nt.symm.trans e)
              · exact pre (e.trans nt))
            exact Finset.mem_image.mpr ⟨site j p,(mem _).mpr ⟨z,fun e => nz (nt.symm.trans e)⟩,nt⟩
      exact walk d (eq ▸ atI)
    have large := colsz.trans ((Finset.card_le_card cover).trans Finset.card_image_le)
    obtain ⟨_,u,tiling⟩ := domino D large (fun i hi bad => ((mem i).mp hi).2 ((mem _).mp bad).1)
    have zeros (j : Fin a) : f (oddSite u j)=0 := ((mem _).mp (tiling j).1).1
    have alive (j : Fin a) : f (evenSite u j)≠0 := by
      have v := ((mem _).mp (tiling j).1).2
      change f (site (oddSite u j) 1) ≠ 0 at v
      rwa [next_odd] at v
    have edge := adj (evenSite u (lastI hp))
    rw [last_even hp] at edge
    obtain hroot | hroot := edge.resolve_left (alive _)
    all_goals
      have rootChoice : ∃ b : Bool, ∀ x : U, x.val u =
          (if b then x.val (evenSite u (lastI hp)) else 0) := by
        first
        | exact ⟨false,fun x => LinearMap.congr_fun hroot x⟩
        | exact ⟨true,fun x => (LinearMap.congr_fun hroot x).symm⟩
      obtain ⟨b,root⟩ := rootChoice
      let ev : U →ₗ[F] (Fin a → F) :=
        {toFun := fun x j => x.val (evenSite u j)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl}
      have modelEq (x : U) : model hp u b (ev x)=x.val := by
        funext i
        obtain ⟨p,rfl⟩ := (chart u).surjective i
        rcases p with _|⟨j,c⟩
        · exact (at_root hp u b (ev x)).trans (root x).symm
        · cases c
          · exact (at_odd hp u b (ev x) j).trans (LinearMap.congr_fun (zeros j) x).symm
          · exact at_even hp u b (ev x) j
      have inj : Function.Injective ev := fun x y eq => Subtype.ext
        ((modelEq x).symm.trans ((congrArg (model hp u b) eq).trans (modelEq y)))
      have onto : Function.Surjective ev := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [dim,Module.finrank_fin_fun])).mp inj
      refine ⟨u,b,(model_checked hp h u b).mp ?_⟩
      intro x k
      obtain ⟨y,rfl⟩ := onto x
      simpa only [modelEq y] using checks y.val y.property k
  · rintro ⟨u,b,ok⟩
    refine ⟨LinearMap.range (model hp u b),?_,?_,?_⟩
    · rw [LinearMap.finrank_range_of_inj (model_inj hp u b),Module.finrank_fin_fun]
    · rintro _ ⟨x,rfl⟩ k
      exact (model_checked hp h u b).mpr ok x k
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ i
      exact model_iso hp u b x y i
def Window {a : Nat} {A : Type*} [Zero A] (w : Fin (N a) → A) (s : Fin (N a)) : Prop :=
  (∀ d : Nat, 0<d → d<a → w (site s d)=0) ∧
    (w (site s a)=0 ∨ w (site s a)=w s)

theorem window_hit {a : Nat} {A : Type*} [Zero A] (ha : 0<a) (w : Fin (N a) → A) :
    (∃ s, Window w s) ↔ WordHit w := by
  classical
  constructor
  · rintro ⟨s,mid,endpoint⟩
    by_cases z : w=0
    · exact Or.inl z
    right
    by_cases nz : w s≠0
    · exact ⟨s,nz,mid,endpoint⟩
    have zero : w s=0 := not_not.mp nz
    have window : ∀ d, d<a → w (site s d)=0 := by
      intro d lt
      cases d with
      | zero => simpa only [site_zero] using zero
      | succ d => exact mid _ (by omega) lt
    obtain ⟨p,hp⟩ : ∃ p, w p≠0 := by
      by_contra! all
      exact z (funext all)
    obtain ⟨d,_,e⟩ := offsets p s
    have retreat (k : Nat) : (∀ j, j<a → w (site (site p k) j)=0) → ∃ r, Mark w r := by
      induction k with
      | zero =>
        intro win
        exact (hp (by simpa only [site_zero] using win 0 ha)).elim
      | succ k ih =>
        intro win
        by_cases prev : w (site p k)=0
        · apply ih
          intro j hj
          cases j with
          | zero => simpa only [site_zero] using prev
          | succ j =>
            have h := win j (by omega)
            simpa only [site_comp,show k.succ+j=k+j.succ by omega] using h
        · refine ⟨site p k,prev,?_,Or.inl ?_⟩
          · intro j pos lt
            have h := win (j-1) (by omega)
            simpa only [site_comp,show k.succ+(j-1)=k+j by omega] using h
          · have h := win (a-1) (by omega)
            simpa only [site_comp,show k.succ+(a-1)=k+a by omega] using h
    exact retreat d (e ▸ window)
  · rintro (rfl|⟨s,_,mid,ep⟩)
    · exact ⟨srcZero a,fun _ _ _ => rfl,Or.inl rfl⟩
    · exact ⟨s,mid,ep⟩

def spin {a : Nat} (i : Fin (N a)) : Fin (N a) := ⟨(2*i.val)%N a,Nat.mod_lt _ (Nat.succ_pos _)⟩
def unspin {a : Nat} (i : Fin (N a)) : Fin (N a) := ⟨((a+1)*i.val)%N a,Nat.mod_lt _ (Nat.succ_pos _)⟩
private theorem mul_drop (c b n : Nat) : (c*(b%n))%n = (c*b)%n := by
  calc
    _ = ((c%n)*(b%n))%n := by rw [Nat.mul_mod c (b%n),Nat.mod_mod]
    _ = (c*b)%n := (Nat.mul_mod c b n).symm

private theorem spin_inv {a} (i : Fin (N a)) : ((2*(a+1))*i.val)%N a=i.val := by
  rw [show (2*(a+1))=N a+1 by dsimp [N];omega,Nat.add_mul,Nat.one_mul,
      Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt i.isLt]

def spinEq (a : Nat) : Fin (N a) ≃ Fin (N a) where
  toFun := spin
  invFun := unspin
  left_inv i := by
    apply Fin.ext
    change ((a+1)*((2*i.val)%N a))%N a=i.val
    rw [mul_drop,←Nat.mul_assoc,Nat.mul_comm (a+1) 2,spin_inv]
  right_inv i := by
    apply Fin.ext
    change (2*(((a+1)*i.val)%N a))%N a=i.val
    rw [mul_drop,←Nat.mul_assoc,spin_inv]

theorem spin_site {a} (s : Fin (N a)) (d) : spin (site s d)=site (spin s) (2*d) := by
  apply Fin.ext
  change (2*((s.val+d)%N a))%N a = ((2*s.val)%N a+2*d)%N a
  rw [mul_drop,Nat.mul_add,Nat.mod_add_mod]

theorem allow_hit {a m} (ha : 0<a) (h : Fin (N a) → Fin m → F) :
   (∃ u b, allowed ha h u b) ↔ WordHit (h ∘ spin) := by
  rw [←window_hit ha]
  constructor
  · rintro ⟨u,b,ok⟩
    obtain ⟨s,es⟩ := (spinEq a).surjective u
    change spin s=u at es
    have atW (d) : (h ∘ spin) (site s d)=h (site u (2*d)) := by rw [Function.comp_apply,spin_site,es]
    refine ⟨s,?_,?_⟩
    · intro d pos lt
      let j : Fin a := ⟨d-1,by omega⟩
      have neq : j≠lastI ha := by intro eq; have := congrArg Fin.val eq; dsimp [j,lastI] at this;omega
      have eq : 2*d=2*j.val+2 := by dsimp [j];omega
      rw [atW,eq];simpa only [evenSite,neq,false_and,if_false] using ok j
    · have eq : 2*a=2*(lastI ha).val+2 := by dsimp [lastI];omega
      rw [atW,eq]
      have e := ok (lastI ha)
      cases b
      · left;simpa [evenSite] using e
      · right;simpa [evenSite,Function.comp_apply,es] using e
  · rintro ⟨s,hzero,he⟩
    let u := spin s
    have atW (d) : (h ∘ spin) (site s d)=h (site u (2*d)) := by rw [Function.comp_apply,spin_site]
    rcases he with he|he
    · refine ⟨u,false,?_⟩
      intro j
      have val : evenSite u j=site u (2*(j.val+1)) := by unfold evenSite;congr 1 <;> omega
      rw [val,←atW];simp only [Bool.false_eq_true,and_false,if_false]
      by_cases last : j.val+1=a
      · rw [last];exact he
      · exact hzero _ (by omega) (by have := j.isLt;omega)
    · refine ⟨u,true,?_⟩
      intro j
      have val : evenSite u j=site u (2*(j.val+1)) := by unfold evenSite;congr 1 <;> omega
      rw [val,←atW]
      by_cases last : j=lastI ha
      · subst j
        rw [show (lastI ha).val+1=a by dsimp [lastI];omega]
        simpa [u] using he
      · have sm : j.val+1<a := by
          have := j.isLt
          by_contra! big
          exact last (Fin.ext (by dsimp [lastI];omega))
        simpa only [last,false_and,if_false] using hzero _ (by omega) sm


theorem main_count (a m : Nat) (ha : 2≤a) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ((Finset.univ : Finset (Fin (N a) → Fin m → F)).filter Success).card =
      1+2*N a*(2^m-1)*((2^m)^a-1) := by
  classical
  let A := Fin m → F
  let e := Equiv.arrowCongr (spinEq a).symm (Equiv.refl A)
  have rel (h : Fin (N a) → A) : Success h ↔ WordHit (e h) :=
    (success_shape ha h).trans (allow_hit (by omega) h)
  let r := restrictEquiv e Success WordHit rel
  have c := Fintype.card_congr r
  simp only [Fintype.card_subtype] at c
  have q : Fintype.card A=2^m := by simp [A,F,Fintype.card_fun,ZMod.card]
  have w := word_count A ha
  rw [q] at w
  exact (filterChange Success).trans (c.trans ((filterChange WordHit).trans w))
end PEqualNP.Outside.L_lib_865_aux

open PEqualNP.Outside.L_lib_865_aux in
theorem PEqualNP.Outside.L_lib_865 : ∀ (a m : ℕ), 2 ≤ a →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 2*a+1
  let A := Fin m → F
  let W := Fin n → F
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.succ_pos (2*a))⟩ : Fin n)
  let succeeds := fun h : Fin n → A =>
    ∃ U : Submodule F W, Module.finrank F U = a ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let q := 2^m
  ((Finset.univ : Finset (Fin n → A)).filter succeeds).card =
    1 + 2*n*(q-1)*(q^a-1) := by
  intro a m ha
  exact main_count a m ha
