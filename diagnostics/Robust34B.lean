import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8321_robust
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false
private theorem isOr_spec (g : Gate) : g.op = .or ↔ isOr g = true := by
  rcases g with ⟨op,ins⟩
  cases op <;> simp [isOr]

private def valid (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
private def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def step (w : List Bool) (g : Gate) := w ++ [val g w]
private def extra (g : Gate) : ℕ := if isOr g then 1 else 0

private theorem operandSet (g : Gate) (b : List Bool) (hg : valid g) (hn : val g b = false) :
    ∃ T : Finset ℕ, T.card ≤ 1 + extra g ∧ (∀ i ∈ T, b.getD i false = false) ∧
      ∀ w : List Bool, val g w = true → ∃ i ∈ T, w.getD i false = true := by
  rcases hg with ⟨hand | hor, hlen⟩
  · have hbad : ¬ ∀ i ∈ g.inputs, b.getD i false = true := by
      intro h
      have hyes : val g b = true := by simpa [val,hand,GateOp.eval,List.all_eq_true] using h
      rw [hn] at hyes
      contradiction
    push_neg at hbad
    obtain ⟨i, hi, hb⟩ := hbad
    refine ⟨{i},by simp [extra,isOr,hand],?_,?_⟩
    · simpa using hb
    · intro w hw
      have hh : ∀ j ∈ g.inputs, w.getD j false = true := by
        simpa [val,hand,GateOp.eval,List.all_eq_true] using hw
      exact ⟨i,by simp,hh i hi⟩
  · refine ⟨g.inputs.toFinset,?_,?_,?_⟩
    · simpa [extra,isOr,hor] using (List.toFinset_card_le _).trans hlen
    · simpa [val,hor,GateOp.eval,List.any_eq_false] using hn
    · intro w hw
      simpa [val,hor,GateOp.eval,List.any_eq_true] using hw

private theorem atEnd (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = val g w := by
  simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_right]

private theorem offEnd (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
  · have h1 : w.length ≤ i := by omega
    have h2 : (step w g).length ≤ i := by simp [step]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2]

private def covered {K : Type} (S : Finset ℕ) (b : List Bool) (v : K → List Bool) : Prop :=
  (∀ i ∈ S, b.getD i false = false) ∧ ∀ t : K, ∃ i ∈ S, (v t).getD i false = true

private theorem backOne {K : Type} (g : Gate) (b : List Bool) (v : K → List Bool)
    (len : ∀ t, (v t).length = b.length) (hg : valid g) (S : Finset ℕ)
    (hc : covered S (step b g) (fun t => step (v t) g)) :
    ∃ T : Finset ℕ, T.card ≤ S.card + extra g ∧ covered T b v := by
  by_cases hit : b.length ∈ S
  · have hz := hc.1 b.length hit
    rw [atEnd] at hz
    obtain ⟨P,hP,hno,hyes⟩ := operandSet g b hg hz
    refine ⟨S.erase b.length ∪ P,?_,?_,?_⟩
    · have s := Finset.card_union_le (S.erase b.length) P
      have h := Finset.card_erase_add_one hit
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
        simpa only [offEnd b g i ne] using hc.1 i mem
      · exact hno i h
    · intro t
      obtain ⟨i,hi,ht⟩ := hc.2 t
      by_cases ei : i = b.length
      · have eqv : i = (v t).length := ei.trans (len t).symm
        rw [eqv,atEnd] at ht
        obtain ⟨j,hj,hjt⟩ := hyes _ ht
        exact ⟨j,Finset.mem_union_right _ hj,hjt⟩
      · have ei' : i ≠ (v t).length := by rwa [len t]
        exact ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ei,hi⟩),
          (offEnd (v t) g i ei').symm.trans ht⟩
  · refine ⟨S,by omega,?_,?_⟩
    · intro i hi
      have ne : i ≠ b.length := fun e => hit (e ▸ hi)
      simpa only [offEnd b g i ne] using hc.1 i hi
    · intro t
      obtain ⟨i,hi,ht⟩ := hc.2 t
      have ne : i ≠ (v t).length := fun e => hit ((e.trans (len t)) ▸ hi)
      exact ⟨i,hi,(offEnd (v t) g i ne).symm.trans ht⟩

private theorem certificate {K : Type} (gs : List Gate) (b : List Bool) (v : K → List Bool)
    (len : ∀ t, (v t).length = b.length) (hg : ∀ g ∈ gs, valid g) (S : Finset ℕ)
    (hc : covered S (gs.foldl step b) (fun t => gs.foldl step (v t))) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.countP isOr ∧ covered T b v := by
  induction gs generalizing b v with
  | nil => exact ⟨S,by simp,hc⟩
  | cons g gs ih =>
    have lg (t : K) : (step (v t) g).length = (step b g).length := by simp [step,len t]
    obtain ⟨U,hU,hcU⟩ := ih (step b g) (fun t => step (v t) g) lg
      (fun a h => hg a (by simp [h])) hc
    obtain ⟨T,hT,hcT⟩ := backOne g b v len (hg g (by simp)) U hcU
    refine ⟨T,?_,hcT⟩
    cases h : isOr g <;> simp [List.countP_cons,h,extra] at * <;> omega


abbrev V := Fin 42
abbrev X := V → Bool
abbrev T := Fin 21
abbrev A := Fin 34

private def rot (t : T) (i : V) : V :=
  ⟨(if i.val<21 then 0 else 21) + (i.val+t.val)%21, by split <;> omega⟩
private def core (t : T) (v : V) :=
  decide (((if v.val<21 then 0 else 21)+(v.val+21-t.val)%21) ∈ ([0,2,7,8,31,32,37,39] : List Nat))
private def freePin (a : Fin 34) : V := (#[1,3,4,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,33,34,35,36,38,40,41] : Array V)[a.val]!
private def pWitness (a : Fin 34) : V := (#[1,3,4,5,6,9,10,11,12,13,14,15,16,17,18,19,20,0,2,2,7,8,0,7,0,8,2,7,8,7,8,0,2,0] : Array V)[a.val]!
private def lWitness (a : Fin 34) : V := (#[39,31,32,31,32,37,31,32,32,39,31,32,37,37,39,39,37,21,22,23,24,25,26,27,28,29,30,33,34,35,36,38,40,41] : Array V)[a.val]!

private def moved (t : T) (a : A) := rot t (freePin a)
private def spike (t : T) (a : A) (v : V) := core t v || decide (v=moved t a)
private def adj (p l : V) := p.val<21 ∧ 21≤l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List Nat)
private instance (p l : V) : Decidable (adj p l) := by unfold adj; infer_instance
private def accept (x : X) := ∃p l, adj p l ∧ x p=true ∧ x l=true
private instance (x : X) : Decidable (accept x) := by unfold accept; infer_instance
private theorem injectMoved : ∀t a b, moved t a=moved t b → a=b := by decide +kernel
private theorem someCore : ∀v,∃t,core t v=true := by decide +kernel
private theorem omitTwo : ∀v w : V,∃t,core t v=false ∧ core t w=false := by decide +kernel
private theorem noCore : ∀t,¬ accept (core t) := by decide +kernel
private theorem spikes (t : T) (a : A) : accept (spike t a) := by
  refine ⟨rot t (pWitness a),rot t (lWitness a),?_⟩
  revert t a
  decide +kernel

private def atom (f : X→Bool) : Prop :=
  (∀x,f x=false) ∨ ∃s : Finset V,∀x,f x=true ↔ ∀i∈s,x i=true

private def thin (t : T) (f : X→Bool) :=
  f (core t)=false → ∀a b : A,f (spike t a)=true → f (spike t b)=true → a=b

private def quiet (t : T) (f : X→Bool) :=
  f (core t)=true ∨ ∀a : A,f (spike t a)=false

private theorem thin_atom {f : X→Bool} (h : atom f) (t : T) : thin t f := by
  intro hn a b ha hb
  rcases h with hz | ⟨s,hs⟩
  · rw [hz] at ha
    contradiction
  · have miss : ¬∀i∈s,core t i=true := fun yes => by
      have ht := (hs _).2 yes
      rw [hn] at ht
      contradiction
    push_neg at miss
    obtain ⟨i,hi,h0⟩ := miss
    have h1 := (hs _).1 ha i hi
    have h2 := (hs _).1 hb i hi
    have h1' : i=moved t a := by simpa [spike,h0] using h1
    have h2' : i=moved t b := by simpa [spike,h0] using h2
    exact injectMoved t a b (h1'.symm.trans h2')

private theorem quiet_atom {f : X→Bool} (h : atom f) : ∃t, quiet t f := by
  classical
  rcases h with hz | ⟨s,hs⟩
  · exact ⟨0,Or.inr (fun _ => hz _)⟩
  by_cases empty : s.Nonempty
  · obtain ⟨i,hi⟩ := empty
    by_cases two : ∃j∈s,j≠i
    · obtain ⟨j,hj,ne⟩ := two
      obtain ⟨t,h0,h1⟩ := omitTwo i j
      refine ⟨t,Or.inr ?_⟩
      intro a
      apply Bool.eq_false_iff.mpr
      intro hy
      have eq1 : i=moved t a := by simpa [spike,h0] using (hs _).1 hy i hi
      have eq2 : j=moved t a := by simpa [spike,h1] using (hs _).1 hy j hj
      exact ne (eq2.trans eq1.symm)
    · obtain ⟨t,ht⟩ := someCore i
      refine ⟨t,Or.inl ((hs _).2 ?_)⟩
      intro j hj
      have e : j=i := by by_contra hn; exact two ⟨j,hj,hn⟩
      exact e ▸ ht
  · refine ⟨0,Or.inl ((hs _).2 ?_)⟩
    intro i hi
    exact False.elim (empty ⟨i,hi⟩)

private theorem constFalse : atom (fun _ => false) := Or.inl (fun _ => rfl)
private theorem constTrue : atom (fun _ => true) := Or.inr ⟨∅,by simp⟩

private theorem atom_and {f g : X→Bool} (hf : atom f) (hg : atom g) :
    atom (fun x=>f x && g x) := by
  rcases hf with z | ⟨s,hs⟩
  · exact Or.inl (fun x => by simp [z x])
  rcases hg with z | ⟨u,hu⟩
  · exact Or.inl (fun x => by simp [z x])
  refine Or.inr ⟨s∪u,?_⟩
  intro x
  simp only [Bool.and_eq_true,hs,hu,Finset.mem_union]
  grind

private theorem atom_all (w : X→List Bool) (hw : ∀i,atom (fun x=>(w x).getD i false))
    (ins : List Nat) :
    atom (fun x => (ins.map (fun i=>(w x).getD i false)).all id) := by
  induction ins with
  | nil => exact constTrue
  | cons a as ih => exact atom_and (hw a) ih

private def bank (w : X→List Bool) : Prop := ∀i,atom (fun x=>(w x).getD i false)
private def thinBank (t : T) (w : X→List Bool) := ∀i,thin t (fun x=>(w x).getD i false)
private def uniform (w : X→List Bool) := ∀ x y,(w x).length=(w y).length

private theorem keep {w : X→List Bool} (hlen : uniform w) {P : (X→Bool)→Prop}
    (old : ∀i,P (fun x=>(w x).getD i false)) (g : Gate) (new : P (fun x=>val g (w x))) :
    ∀i,P (fun x=>(step (w x) g).getD i false) := by
  intro i
  by_cases e : i=(w (fun _=>false)).length
  · have eq : (fun x=>(step (w x) g).getD i false)=(fun x=>val g (w x)) := by
      funext x
      rw [e,hlen _ x,atEnd]
    exact eq ▸ new
  · have eq : (fun x=>(step (w x) g).getD i false)=(fun x=>(w x).getD i false) := by
      funext x
      exact offEnd _ _ _ (fun eq=> e (eq.trans (hlen x _)))
    exact eq ▸ old i

private theorem newUniform {w : X→List Bool} (h : uniform w) (g : Gate) :
    uniform (fun x=>step (w x) g) := by
  intro x y
  simp [step,h x y]

private theorem oneOr {w : X→List Bool} (hw : bank w) (len : uniform w) (g : Gate)
    (hop : g.op=.or) (size : g.inputs.length≤2) :
    ∃t, thinBank t (fun x=>step (w x) g) := by
  cases ins : g.inputs with
  | nil =>
    refine ⟨0,keep len (fun i=>thin_atom (hw i) _) g ?_⟩
    simpa [val,hop,ins,GateOp.eval] using thin_atom constFalse (0:T)
  | cons i rest =>
    obtain ⟨t,qt⟩ := quiet_atom (hw i)
    refine ⟨t,keep len (fun k=>thin_atom (hw k) _) g ?_⟩
    cases rest with
    | nil => simpa [val,hop,ins,GateOp.eval] using thin_atom (hw i) t
    | cons j ss =>
      have z : ss=[] := by
        simp only [ins,List.length_cons] at size
        exact List.length_eq_zero_iff.mp (by omega)
      subst ss
      intro hz a b ha hb
      simp only [val,hop,ins,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,
        List.any_nil,Bool.or_false,id_eq] at hz ha hb
      rcases qt with on | off
      · change (w (core t)).getD i false = true at on
        rw [on] at hz
        simp at hz
      · change ∀a : A,(w (spike t a)).getD i false=false at off
        have heq : (w (core t)).getD i false=false ∧ (w (core t)).getD j false=false := by simpa only [Bool.or_eq_false_iff] using hz
        have hzb := heq.2
        rw [off a,Bool.false_or] at ha
        rw [off b,Bool.false_or] at hb
        have ha' := ha
        have hb' := hb
        exact thin_atom (hw j) t hzb a b ha' hb'

private theorem thinCount {w : X→List Bool} {t : T} (hw : thinBank t w) {S : Finset Nat}
    (hs : covered S (w (core t)) (fun a=>w (spike t a))) : 34 ≤ S.card := by
  classical
  choose f inside yes using hs.2
  let h (a : A) : S := ⟨f a,inside a⟩
  have inj : Function.Injective h := by
    intro a b hab
    have eq : f a=f b := congrArg Subtype.val hab
    have yb : (w (spike t b)).getD (f a) false=true := eq ▸ yes b
    exact hw (f a) (hs.1 _ (inside a)) a b (yes a) yb
  simpa using Fintype.card_le_of_injective h inj

private theorem countFrom (gs : List Gate) (out : Nat) (w : X→List Bool)
    (len : uniform w) (hw : bank w) (legal : ∀g∈gs,valid g)
    (rightF : ∀x,(gs.foldl step (w x)).getD out false=true ↔ accept x) :
    34 ≤ gs.countP isOr := by
  induction gs generalizing w with
  | nil =>
    have hs : covered {out} (w (core 0)) (fun a=>w (spike 0 a)) := by
      constructor
      · intro i hi
        obtain rfl := Finset.mem_singleton.mp hi
        exact Bool.eq_false_iff.mpr (fun ht=>noCore _ ((rightF _).1 ht))
      · intro a
        exact ⟨out,by simp,(rightF _).2 (spikes _ _)⟩
    have hh := thinCount (fun i=>thin_atom (hw i) 0) hs
    simp at hh
  | cons g gs ih =>
    have lg := legal g List.mem_cons_self
    have tailValid : ∀k∈gs,valid k := fun k hk=>legal k (List.mem_cons_of_mem _ hk)
    have newlen := newUniform len g
    rcases lg.1 with ha | ho
    · have new : atom (fun x=>val g (w x)) := by
        simpa only [val,ha,GateOp.eval] using atom_all w hw g.inputs
      have next := ih (fun x=>step (w x) g) newlen (keep len hw g new) tailValid rightF
      simpa [List.countP_cons,isOr,ha] using next
    · obtain ⟨t,thinW⟩ := oneOr hw len g ho lg.2
      let post (x : X) := step (w x) g
      have hc : covered {out} (gs.foldl step (post (core t)))
          (fun a=>gs.foldl step (post (spike t a))) := by
        constructor
        · intro i hi
          obtain rfl := Finset.mem_singleton.mp hi
          exact Bool.eq_false_iff.mpr (fun ht=>noCore _ ((rightF _).1 ht))
        · intro a
          exact ⟨out,by simp,(rightF _).2 (spikes _ _)⟩
      obtain ⟨S,hsize,hcover⟩ := certificate gs (post (core t)) (fun a=>post (spike t a))
        (fun a=>newlen _ _) tailValid {out} hc
      have hh := thinCount thinW hcover
      simp only [Finset.card_singleton] at hsize
      simp [List.countP_cons,isOr,ho]
      omega

theorem unrestricted34 (C : Circuit) (m : Monotone2 C)
    (correct : ∀x,C.eval (List.ofFn x)=true ↔ accept x) : 34≤ C.gates.countP isOr := by
  apply countFrom C.gates C.output (fun x=>List.ofFn x) (fun x y => by simp) _ _ correct
  · intro i
    by_cases h : i<42
    · refine Or.inr ⟨{⟨i,h⟩},?_⟩
      intro x
      change ((List.ofFn x)[i]?).getD false=true ↔ _
      rw [List.getElem?_eq_getElem (by simpa using h)]
      simp only [Option.getD_some,List.getElem_ofFn,Finset.mem_singleton,forall_eq]
    · refine Or.inl ?_
      intro x
      change ((List.ofFn x)[i]?).getD false=false
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)]
      rfl
  · intro g hg
    obtain ⟨a,b⟩ := m g hg
    exact ⟨by simpa using a,b⟩

end PEqualNP.Outside.L_meta_8321_robust
