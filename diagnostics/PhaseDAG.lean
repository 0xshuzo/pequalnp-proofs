import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9762_Phase
open PEqualNP.CircuitLowerBounds

def flip (s x : Bool) : Bool := if s then !x else x
def op (a : Bool) : GateOp := if a then .and else .or
def bin (a x y : Bool) : Bool := if a then x && y else x || y
def go (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]

-- One global phase may be shared arbitrarily. A NOT reverses its input phase.
inductive Step (p : Nat → Bool) (k : Nat) : Gate → Gate → Prop where
  | bin (d : Bool) (a b : Nat) (av : a<k) (bv : b<k)
      (ea : p a=p k) (eb : p b=p k) :
    Step p k ⟨op d,[a,b]⟩ ⟨op (flip (p k) d),[a,b]⟩
  | inv (a : Nat) (av : a<k) (ea : p a= !(p k)) :
    Step p k ⟨.not,[a]⟩ ⟨.or,[a]⟩

inductive Chain (p : Nat → Bool) : Nat → List Gate → List Gate → Prop where
  | nil (k : Nat) : Chain p k [] []
  | cons {k g m gs ms} (a : Step p k g m) (b : Chain p (k+1) gs ms) :
    Chain p k (g::gs) (m::ms)

def linked (p : Nat → Bool) (k : Nat) (w v : List Bool) : Prop :=
  w.length=k ∧ v.length=k ∧ ∀ j<k, v.getD j false=flip (p j) (w.getD j false)

theorem snoc' (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by
  simp [List.getD_eq_getElem?_getD]

theorem old' (w : List Bool) (v : Bool) {i : Nat} (h : i<w.length) :
    (w++[v]).getD i false=w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem linked_push {p k w v} (h : linked p k w v) (x : Bool) :
    linked p (k+1) (w++[x]) (v++[flip (p k) x]) := by
  obtain ⟨hw,hv,hs⟩ := h
  refine ⟨by simp [hw],by simp [hv],?_⟩
  intro j hj
  by_cases prev : j<k
  · rw [old' v _ (by omega),old' w _ (by omega)]
    exact hs j prev
  · have ej : j=k := by omega
    subst j
    rw [← hv, snoc']
    rw [hv,← hw,snoc']

theorem op_eval (d a b : Bool) : (op d).eval [a,b]=bin d a b := by
  cases d <;> simp [op,bin,GateOp.eval]

theorem demorgan (s d a b : Bool) :
    bin (flip s d) (flip s a) (flip s b)=flip s (bin d a b) := by
  cases s <;> cases d <;> cases a <;> cases b <;> rfl

theorem step_link {p k g m w v} (h : Step p k g m) (z : linked p k w v) :
    linked p (k+1) (go w g) (go v m) := by
  cases h with
  | bin d a b av bv ea eb =>
    simp only [go,List.map_cons,List.map_nil,op_eval,z.2.2 a av,z.2.2 b bv,ea,eb,demorgan]
    exact linked_push z _
  | inv a av ea =>
    have neg : flip (!(p k)) (w.getD a false)=flip (p k) (!(w.getD a false)) := by
      cases p k <;> cases w.getD a false <;> rfl
    simpa [go,GateOp.eval,z.2.2 a av,ea,neg] using (linked_push z (!(w.getD a false)))

theorem steps_link {p k gs ms} (h : Chain p k gs ms) {w v} (z : linked p k w v) :
    linked p (k+gs.length) (gs.foldl go w) (ms.foldl go v) := by
  induction h generalizing w v with
  | nil => simpa using z
  | cons a b ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step_link a z)

theorem init_link (p : Nat → Bool) {n} (x : Fin n → Bool) :
    linked p n (List.ofFn x) (List.ofFn (fun i => flip (p i) (x i))) := by
  refine ⟨by simp,by simp,?_⟩
  intro j hj
  simp [List.getD_eq_getElem?_getD,hj]

theorem chain_edges {p k gs ms} (h : Chain p k gs ms) :
    gs.length=ms.length ∧ ∀ m∈ms,
      m.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ m.inputs.length≤2 := by
  induction h with
  | nil => simp
  | cons a b ih =>
    refine ⟨by simp [ih.1],?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | tail
    · cases a with
      | bin d a b av bv ea eb =>
        cases flip _ d <;> simp [op]
      | inv => simp
    · exact ih.2 m tail

theorem physical {p n} {C M : Circuit} (h : Chain p n C.gates M.gates)
    (port : C.output<n+C.gates.length) (out : M.output=C.output)
    (pos : p C.output=false) :
    M.size=C.size ∧ PEqualNP.MetaComplexity.Monotone2 M ∧
    ∀ x : Fin n → Bool,
      M.eval (List.ofFn (fun i => flip (p i) (x i)))=C.eval (List.ofFn x) := by
  refine ⟨(chain_edges h).1.symm,(chain_edges h).2,?_⟩
  intro x
  have hx := (steps_link h (init_link p x)).2.2 C.output port
  simpa [Circuit.eval,Circuit.wires,go,out,pos,flip] using hx

def below {V : Type} (x y : V → Bool) : Prop := ∀ i, x i=true → y i=true
def increasing {V : Type} (h : (V → Bool) → Bool) : Prop := ∀ x y, below x y → h x=true → h y=true
def zeroNeg {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) (i : Fin n) :=
  if p i then false else x i
def posBits {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) (i : Fin n) :=
  if p i then true else x i

theorem clamp_order {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) :
    below (zeroNeg p x) x ∧ below (fun i => flip (p i) (x i)) (posBits p x) ∧
    (fun i => flip (p i) (zeroNeg p x i))=posBits p x := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    cases h : p i <;> simp_all [zeroNeg]
  · intro i hi
    cases h : p i <;> simp_all [flip,posBits]
  · funext i
    cases h : p i <;> simp [flip,zeroNeg,posBits,h]

theorem clamp_splice {n : Nat} (p : Nat → Bool)
    (f r m : (Fin n → Bool) → Bool) (mf : increasing f) (mm : increasing m)
    (eqn : ∀ x, (r x || m (fun i => flip (p i) (x i)))=f x) :
    ∀ x, (r x || m (posBits p x))=f x := by
  intro x
  obtain ⟨down,up,norm⟩ := clamp_order p x
  cases h : f x with
  | false =>
    have rr : r x=false := by
      have z := (eqn x).trans h
      cases hr : r x <;> simp_all
    have rm : m (posBits p x)=false := by
      cases hm : m (posBits p x) with
      | false => rfl
      | true =>
        have t : f (zeroNeg p x)=true := by rw [← eqn,norm,hm]; simp
        exact Bool.noConfusion ((mf _ _ down t).symm.trans h)
    simp [rr,rm]
  | true =>
    have z := (eqn x).trans h
    cases hr : r x with
    | true => simp [hr]
    | false =>
      have hm : m (fun i => flip (p i) (x i))=true := by simpa [hr] using z
      simp [hr,mm _ _ up hm]

end PEqualNP.Outside.L_meta_9762_Phase
