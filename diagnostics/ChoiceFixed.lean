import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.Physical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def andB (g : Gate) : Bool := match g.op with | .and => true | _ => false
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def relation (a b c : List Bool) : Prop :=
  a.length=b.length ∧ b.length=c.length ∧
    ∀ i, a.getD i false=false → b.getD i false=false → c.getD i false=false

lemma append_relation {a b c : List Bool} (hr : relation a b c) {a' b' c' : Bool}
    (h : a'=false → b'=false → c'=false) : relation (a++[a']) (b++[b']) (c++[c']) := by
  obtain ⟨hab,hbc,pointwise⟩ := hr
  refine ⟨by simp [hab],by simp [hbc],?_⟩
  intro i
  by_cases hi : i<a.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
    exact pointwise i
  · by_cases he : i=a.length
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
      simpa [he,hab,hbc] using h
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
      simp

lemma or_false {a b c : List Bool} (r : relation a b c) (ins : List Nat)
    (ha : (ins.map (fun i => a.getD i false)).any id=false)
    (hb : (ins.map (fun i => b.getD i false)).any id=false) :
    (ins.map (fun i => c.getD i false)).any id=false := by
  simp only [List.any_map,List.any_eq_false,Function.comp_apply,id_eq] at ha hb ⊢
  intro i hi
  exact Bool.eq_false_iff.mp (r.2.2 i (Bool.eq_false_iff.mpr (ha i hi)) (Bool.eq_false_iff.mpr (hb i hi)))

def pickIdx (g : Gate) (s : Bool) := g.inputs[if s then 1 else 0]?
def picked (g : Gate) (s : Bool) (w : List Bool) : Bool :=
  match pickIdx g s with
  | none => true
  | some i => w.getD i false

lemma two_and (g : Gate) (w : List Bool) (op : g.op=.and) (fan : g.inputs.length≤2) :
    g.op.eval (g.inputs.map (fun i => w.getD i false))=(picked g false w && picked g true w) := by
  cases g with
  | mk o ins =>
    simp only at op fan
    subst o
    cases ins with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => simp [GateOp.eval,picked,pickIdx]
      | cons b xs =>
        have nil : xs=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at fan; omega)
        subst xs
        simp [GateOp.eval,picked,pickIdx]

def admitted : List Gate → List Bool → List Bool → Prop
  | [],_,s => s=[]
  | g::gs,w,s =>
    if andB g then ∃ c rest, s=c::rest ∧
      picked g c w=g.op.eval (g.inputs.map (fun i => w.getD i false)) ∧ admitted gs (step w g) rest
    else admitted gs (step w g) s

lemma length_admitted {gs : List Gate} {w : List Bool} {s : List Bool} (h : admitted gs w s) :
    s.length=gs.countP andB := by
  induction gs generalizing w s with
  | nil =>
    change s=[] at h
    simp [h]
  | cons g gs ih =>
    cases op : andB g with
    | false =>
      exact (ih (by simpa [admitted,op] using h)).trans (by simp [List.countP_cons,op])
    | true =>
      simp only [admitted,op,ite_true] at h
      obtain ⟨v,t,rfl,_,tail⟩ := h
      simp [List.countP_cons,op,ih tail]

lemma has_admitted (gs : List Gate) (w : List Bool)
    (legs : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    ∃ c, admitted gs w c := by
  induction gs generalizing w with
  | nil => exact ⟨[],rfl⟩
  | cons g gs ih =>
    obtain ⟨tail,ht⟩ := ih (step w g) (fun z hz => legs z (List.mem_cons_of_mem _ hz))
    have legal := legs g (by simp)
    rcases legal.1 with op|op
    · have eq := two_and g w op legal.2
      have yes : andB g=true := by simp [andB,op]
      by_cases h : picked g false w=true
      · refine ⟨true::tail,?_⟩
        simp only [admitted,yes,ite_true]
        exact ⟨true,tail,rfl,by simp only [eq,h,Bool.true_and],ht⟩
      · refine ⟨false::tail,?_⟩
        simp only [admitted,yes,ite_true]
        exact ⟨false,tail,rfl,by simp only [eq,Bool.eq_false_iff.mpr h,Bool.false_and],ht⟩
    · exact ⟨tail,by simpa [admitted,andB,op] using ht⟩

lemma admitted_relation (gs : List Gate)
    (fan : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (a b c : List Bool) (rel : relation a b c) (s : List Bool)
    (ha : admitted gs a s) (hb : admitted gs b s) :
    relation (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c s with
  | nil => exact rel
  | cons g gs ih =>
    have legal := fan g (by simp)
    have smaller := fun t (ht : t∈gs) => fan t (List.mem_cons_of_mem _ ht)
    rcases legal.1 with op|op
    · have yes : andB g=true := by simp [andB,op]
      simp only [admitted,yes,ite_true] at ha hb
      obtain ⟨m,t,rfl,xa,sa⟩ := ha
      obtain ⟨m',t',eq,xb,sb⟩ := hb
      obtain ⟨rfl,rfl⟩ := List.cons.inj eq
      apply ih smaller _ _ _ (append_relation rel ?_) _ sa sb
      intro ya yb
      have f1 := xa.trans ya
      have f2 := xb.trans yb
      have z : picked g m c=false := by
        cases h : pickIdx g m with
        | none => simp [picked,h] at f1
        | some i =>
          have zz := rel.2.2 i (by simpa only [picked,h] using f1) (by simpa only [picked,h] using f2)
          simpa only [picked,h] using zz
      rw [two_and g c op legal.2]
      cases m <;> simp_all only [Bool.false_and,Bool.and_false]
    · simp only [admitted,andB,op,Bool.false_eq_true,ite_false] at ha hb
      apply ih smaller _ _ _ (append_relation rel ?_) _ ha hb
      simpa [op,GateOp.eval] using or_false rel g.inputs

theorem price {n N : Nat} (C : Circuit) (fan : Monotone2 C)
    (rows : Fin N → Fin n → Bool)
    (off : ∀ i, C.eval (List.ofFn (rows i))=false)
    (cross : ∀ i j, i≠j → C.eval (List.ofFn (fun v => rows i v || rows j v))=true)
    (stem : List Bool) (survive : ∀ i, ∃ s, admitted C.gates (List.ofFn (rows i)) (stem++s)) :
    N≤2^(C.gates.countP andB-stem.length) := by
  classical
  choose tail yes using survive
  let k := C.gates.countP andB-stem.length
  have len (i : Fin N) : (tail i).length=k := by
    have h := length_admitted (yes i)
    rw [List.length_append] at h
    dsimp [k]; omega
  let enc (i : Fin N) (p : Fin k) := (tail i).getD p.val false
  have inj : Function.Injective enc := by
    intro i j heq
    by_contra hne
    have same : tail i=tail j := by
      apply List.ext_getElem
      · rw [len,len]
      · intro p hi hj
        have op := congrFun heq ⟨p,by rwa [len] at hi⟩
        change (tail i).getD p false=(tail j).getD p false at op
        simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] using op
    have raw : relation (List.ofFn (rows i)) (List.ofFn (rows j))
        (List.ofFn (fun v => rows i v || rows j v)) := by
      refine ⟨by simp,by simp,?_⟩
      intro p
      by_cases hp : p<n
      · have get (z : Fin n → Bool) : (List.ofFn z).getD p false=z ⟨p,hp⟩ := by
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hp)]
          simp only [List.getElem_ofFn]
        rw [get,get,get]; intro a b; simp [a,b]
      · have get (z : Fin n → Bool) : (List.ofFn z).getD p false=false :=
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
        rw [get,get,get]; simp
    have fj := yes j
    rw [← same] at fj
    have hr := admitted_relation C.gates (fun g hg => ⟨by simpa using (fan g hg).1,(fan g hg).2⟩)
      _ _ _ raw _ (yes i) fj
    exact Bool.noConfusion ((cross i j hne).symm.trans (hr.2.2 C.output (off i) (off j)))
  have count := Fintype.card_le_of_injective enc inj
  simpa [Fintype.card_fun,k] using count

end PEqualNP.Outside.L_meta_9792.Physical
