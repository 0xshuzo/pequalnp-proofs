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
  w (srcZero a) ≠ 0 ∧ (∀ i : Fin (N a), 0<i.val → i.val<a → w i=0) ∧
    (w (pivot a)=0 ∨ w (pivot a)=w (srcZero a))

theorem pack_normal {a} {A : Type*} [Zero A] (ha : 0<a) (x : Code A a) : normMark (pack x) := by
  refine ⟨by rw [pack_zero];exact x.1.property,?_,?_⟩
  · intro i pos small
    simp [pack,Nat.ne_of_gt pos,small]
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
  · simpa only [pack,z,dif_neg,sm,dif_pos] using (ok.2.1 i (by omega) sm).symm
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
      exact ⟨nz,fun j pos sm => zeros j.val pos sm,tail⟩
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
  change Fintype.card {x : Marked A s // ¬occ x}=2*(q-1)*(q^a-1)
  rw [Fintype.card_subtype_compl,allc,both]
  rw [Nat.mul_sub_left_distrib,Nat.mul_one]
  congr 1 <;> ring

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
    (Fintype.card_congr (Equiv.refl (Kept A s))).trans (kept_count A (by omega) s)
  calc
    _ = Fintype.card {w : Fin (N a) → A // WordHit w} := by rw [Fintype.card_subtype]
    _ = Fintype.card (Option (Σ s : Fin (N a), Kept A s)) := (Fintype.card_congr (wordsEquiv A ha)).symm
    _ = (∑ s : Fin (N a), Fintype.card (Kept A s))+1 := by rw [Fintype.card_option,Fintype.card_sigma]
    _ = (∑ _s : Fin (N a), r)+1 := congrArg (·+1) (Finset.sum_congr rfl (fun s _ => f s))
    _ = _ := by simp [r,q,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,Nat.add_comm]


end PEqualNP.Outside.L_lib_865_aux
