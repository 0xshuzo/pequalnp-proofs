import PEqualNP.Defs

namespace LineZero7832

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxHeartbeats 0
set_option maxRecDepth 32768

def move (w : Nat) : Nat := if w < 13 then w else w+1

theorem move_inj : Function.Injective move := by
  intro i j h
  unfold move at h
  split at h <;> split at h <;> omega

theorem move_bound {w k : Nat} (h : w < 25+k) : move w < 26+k := by
  unfold move
  split <;> omega

theorem move_not_center (w : Nat) : move w ≠ 13 := by
  unfold move
  split <;> omega

def emb (i : Fin 25) : Fin 26 := ⟨move i.val, move_bound (k:=0) i.isLt⟩
def pull (x : Fin 26 → Bool) : Fin 25 → Bool := fun i => x (emb i)
def renamed (g : Gate) : Gate := ⟨g.op,g.inputs.map move⟩
def lifted (D : Circuit) : Circuit := ⟨D.gates.map renamed,move D.output⟩

theorem liftForm (D : Circuit) (hf : IsAO2 25 D) :
    IsAO2 26 (lifted D) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    exact hf.1 h hh
  · intro j hj w hw
    have hj' : j < D.gates.length := by simpa [lifted] using hj
    have eq : gateAt (lifted D) j = renamed (gateAt D j) := by
      simp [gateAt,lifted,List.getD_eq_getElem?_getD,hj']
    rw [eq] at hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact move_bound (hf.2.1 j hj' i hi)
  · intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    simpa [renamed] using hf.2.2 h hh

theorem liftDistinct (D : Circuit) (hn : ∀ g ∈ D.gates, g.inputs.Nodup) :
    ∀ g ∈ (lifted D).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  exact (hn h hh).map move_inj

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def aligned (old new : List Bool) : Prop :=
  13 ≤ old.length ∧ new.length = old.length+1 ∧
    ∀ i, old.getD i false = new.getD (move i) false

theorem aligned_inputs (x : Fin 26 → Bool) : aligned (List.ofFn (pull x)) (List.ofFn x) := by
  refine ⟨by simp,by simp,?_⟩
  intro i
  by_cases h : i<25
  · have h' := move_bound (k:=0) h
    simp [List.getD_eq_getElem?_getD,h,h',pull,emb]
  · have hh : 26 ≤ move i := by unfold move; split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem aligned_step {old new : List Bool} (rel : aligned old new) (g : Gate) :
    aligned (step old g) (step new (renamed g)) := by
  obtain ⟨lo,len,eq⟩ := rel
  have values : g.inputs.map (fun i => old.getD i false) =
      (renamed g).inputs.map (fun i => new.getD i false) := by
    simp only [renamed,List.map_map]
    apply List.map_congr_left
    exact fun i _ => eq i
  refine ⟨by simp [step]; omega,by simp [step,len],?_⟩
  intro i
  rcases lt_trichotomy i old.length with hi | hi | hi
  · have mv : move i < new.length := by unfold move; split <;> omega
    simpa only [step,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ mv] using eq i
  · subst i
    have mv : move old.length = new.length := by unfold move; split <;> omega
    simp [step,mv,values,renamed]
  · have mv : new.length < move i := by unfold move; split <;> omega
    rw [List.getD_eq_default _ _ (by simp [step]; omega),
        List.getD_eq_default _ _ (by simp [step]; omega)]

theorem aligned_run (gs : List Gate) {old new : List Bool} (rel : aligned old new) :
    aligned (gs.foldl step old) ((gs.map renamed).foldl step new) := by
  induction gs generalizing old new with
  | nil => exact rel
  | cons g gs ih => exact ih (aligned_step rel g)

theorem lift_wire (D : Circuit) (x : Fin 26 → Bool) (i : Nat) :
    wireValue (lifted D) 26 x (move i) = wireValue D 25 (pull x) i :=
  ((aligned_run D.gates (aligned_inputs x)).2.2 i).symm

theorem wlen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_singleton,List.length_cons]; omega

theorem keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem primary (D : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wireValue D n x i.val = x i := by
  change (D.gates.foldl step (List.ofFn x)).getD i.val false = _
  rw [keep _ _ _ (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD,i.isLt]

def addGate (D : Circuit) (op : GateOp) (u v : Nat) : Circuit :=
  ⟨D.gates ++ [⟨op,[u,v]⟩],26+D.size⟩

@[simp] theorem add_size (D : Circuit) (op : GateOp) (u v : Nat) :
    (addGate D op u v).size = D.size+1 := by simp [addGate,Circuit.size]
@[simp] theorem lift_size (D : Circuit) : (lifted D).size = D.size := by simp [lifted,Circuit.size]

theorem add_form (D : Circuit) (hf : IsAO2 26 D) (op : GateOp) (hop : op=.and ∨ op=.or)
    (u v : Nat) (hu : u<26+D.size) (hv : v<26+D.size) :
    IsAO2 26 (addGate D op u v) := by
  let g : Gate := ⟨op,[u,v]⟩
  let C := addGate D op u v
  change IsAO2 26 C
  refine ⟨?_,?_,?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hf.1 z hz
    · obtain rfl : z=g := List.mem_singleton.mp hz
      exact hop
  · intro i hi j hj
    by_cases hl : i<D.gates.length
    · have eq : gateAt C i = gateAt D i := List.getD_append _ _ _ _ hl
      exact hf.2.1 i hl j (eq ▸ hj)
    · have upper : i<D.gates.length+1 := by simpa [C,addGate] using hi
      obtain rfl : i = D.gates.length := by omega
      have last : gateAt C D.gates.length = g := by simp [gateAt,C,addGate,g,List.getD_eq_getElem?_getD]
      rw [last] at hj
      change j ∈ [u,v] at hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl <;> assumption
  · intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact hf.2.2 z hz
    · obtain rfl : z=g := List.mem_singleton.mp hz
      rfl

theorem add_distinct (D : Circuit) (hn : ∀ g ∈ D.gates, g.inputs.Nodup)
    (op : GateOp) (u v : Nat) (ne : u ≠ v) :
    ∀ g ∈ (addGate D op u v).gates, g.inputs.Nodup := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hn _ h
  · obtain rfl := List.mem_singleton.mp h
    simpa using ne

theorem add_wires (D : Circuit) (op : GateOp) (x : Fin 26 → Bool) (u v : Nat) :
    (addGate D op u v).wires (List.ofFn x) =
      D.wires (List.ofFn x) ++ [op.eval [wireValue D 26 x u,wireValue D 26 x v]] := by
  simp [Circuit.wires,addGate,List.foldl_append,wireValue]

theorem add_old (D : Circuit) (op : GateOp) (x : Fin 26 → Bool) (u v i : Nat) (bound : i<26+D.size) :
    wireValue (addGate D op u v) 26 x i = wireValue D 26 x i := by
  unfold wireValue
  rw [add_wires]
  apply List.getD_append
  change i < (D.gates.foldl step (List.ofFn x)).length
  simpa only [wlen,List.length_ofFn] using bound

theorem add_new (D : Circuit) (op : GateOp) (x : Fin 26 → Bool) (u v : Nat) :
    wireValue (addGate D op u v) 26 x (26+D.size) = op.eval [wireValue D 26 x u,wireValue D 26 x v] := by
  have len : (D.wires (List.ofFn x)).length=26+D.size := by
    change (D.gates.foldl step (List.ofFn x)).length=_
    simp [wlen,Circuit.size]
  unfold wireValue
  rw [add_wires,←len]
  simp

abbrev V := Fin 13
def Adj (p l : V) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
def opp (x : V → Bool) (l : V) := !(x l || x (l+1) || x (l+3) || x (l+9))
def ixP (p : V) : Fin 25 := ⟨p.val,by omega⟩
def ixL (l : Fin 12) : Fin 25 := ⟨13+l.val,by omega⟩
def flag (x : Fin 25 → Bool) := ∃ p : V, ∃ l : Fin 12, Adj p l.succ ∧ x (ixP p)=true ∧ x (ixL l)=true
def center (x : Fin 25 → Bool) := ∃ p : V, Adj p 0 ∧ x (ixP p)=true
instance (p l : V) : Decidable (Adj p l) := by unfold Adj; infer_instance
instance (x : Fin 25 → Bool) : Decidable (flag x) := by unfold flag; infer_instance
instance (x : Fin 25 → Bool) : Decidable (center x) := by unfold center; infer_instance
def pair (p l : V) (i : Fin 26) := decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)

theorem positives : ∀ p l : V, Adj p l →
    (flag (pull (pair p l)) ∨ center (pull (pair p l))) ∧
    (flag (pull (pair p l)) ∨ pair p l 13=true) := by decide +kernel

theorem point_index : ∀ p, emb (ixP p) = Fin.castAdd 13 p := by decide
theorem line_index : ∀ l, emb (ixL l) = Fin.natAdd 13 l.succ := by decide
theorem point_read (x y : V → Bool) (p : V) :
    pull (Fin.append x y) (ixP p) = x p := by simp [pull,point_index,Fin.append_left]
theorem line_read (x y : V → Bool) (l : Fin 12) :
    pull (Fin.append x y) (ixL l) = y l.succ := by simp [pull,line_index,Fin.append_right]

theorem opp_excludes {x : V → Bool} {p l : V} (hit : Adj p l) (neg : opp x l=true) :
    x p=false := by
  simp only [opp,Bool.not_eq_true',Bool.or_eq_false_iff] at neg
  rcases hit with rfl|rfl|rfl|rfl <;> tauto

theorem no_flag (x : V → Bool) : ¬ flag (pull (Fin.append x (opp x))) := by
  rintro ⟨p,l,inc,hp,hl⟩
  rw [point_read] at hp
  rw [line_read] at hl
  exact Bool.false_ne_true ((opp_excludes inc hl).symm.trans hp)

theorem no_center (x : V → Bool) (h : opp x 0=true) : ¬ center (pull (Fin.append x (opp x))) := by
  rintro ⟨p,inc,hp⟩
  rw [point_read] at hp
  exact Bool.false_ne_true ((opp_excludes inc h).symm.trans hp)

def Child : Prop :=
  ∃ (D : Circuit) (h a : Nat), D.size≤62 ∧ IsAO2 25 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
    h<25+D.size ∧ a<25+D.size ∧
    ∀ x : Fin 25 → Bool, (wireValue D 25 x h=true ↔ flag x) ∧
      (wireValue D 25 x a=true ↔ flag x ∨ center x)

theorem build (child : Child) : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (13 : ℕ) → Bool), (∀ (x8 : Fin (13 : ℕ)), x7 x8 = Bool.false → ∃ (x10 : Fin (13 : ℕ)), x1 x8 x10 ∧ x2 x7 x10 = Bool.true) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (Fin.append x7 (x2 x7)) (if x2 x7 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  dsimp only
  obtain ⟨D,h,a,sz,legal,distinct,hh,ha,corr⟩ := child
  let P := lifted D
  let A := move a
  let H := move h
  let B := 26 + P.size
  let Q := addGate P .or H 13
  let C := addGate Q .and A B
  have formP : IsAO2 26 P := liftForm D legal
  have boundH : H < 26+P.size := by simpa [H,P] using move_bound hh
  have boundA : A < 26+P.size := by simpa [A,P] using move_bound ha
  have formQ : IsAO2 26 Q := add_form P formP _ (Or.inr rfl) _ _ boundH (by omega)
  have sizeQ : Q.size = P.size+1 := add_size _ _ _ _
  have boundB : B < 26+Q.size := by dsimp [B]; omega
  have formC : IsAO2 26 C := add_form Q formQ _ (Or.inl rfl) _ _ (by omega) boundB
  have ndQ : ∀ g ∈ Q.gates, g.inputs.Nodup :=
    add_distinct _ (liftDistinct D distinct) _ _ _ (move_not_center h)
  have ndC : ∀ g ∈ C.gates, g.inputs.Nodup :=
    add_distinct _ ndQ _ _ _ (by change A ≠ 26+P.size; omega)
  have lhs (x : Fin 26 → Bool) : wireValue C 26 x A=true ↔ flag (pull x) ∨ center (pull x) := by
    change wireValue (addGate Q .and A B) 26 x A = true ↔ _
    rw [add_old _ _ _ _ _ _ (by omega),show Q = addGate P .or H 13 from rfl,
      add_old _ _ _ _ _ _ boundA]
    change wireValue (lifted D) 26 x (move a)=true ↔ _
    rw [lift_wire]
    exact (corr (pull x)).2
  have rhs (x : Fin 26 → Bool) : wireValue C 26 x B=true ↔ flag (pull x) ∨ x 13=true := by
    change wireValue (addGate Q .and A B) 26 x B=true ↔ _
    rw [add_old _ _ _ _ _ _ boundB]
    change wireValue (addGate P .or H 13) 26 x (26+P.size)=true ↔ _
    rw [add_new,lift_wire D x h,primary P x (13 : Fin 26)]
    simp [GateOp.eval,(corr (pull x)).1]
  refine ⟨C,Q.size,A,B,?_,formC,ndC,rfl,?_,?_,?_⟩
  · simp [C,Q,P]; omega
  · simp [C,addGate,Circuit.size]
  · intro p l inc
    obtain ⟨left,right⟩ := positives p l inc
    exact ⟨(lhs (pair p l)).mpr left,(rhs (pair p l)).mpr right⟩
  · intro x _
    change wireValue C 26 (Fin.append x (opp x)) (if opp x 0=true then A else B)=false
    by_cases e : opp x 0=true
    · rw [if_pos e]
      apply Bool.eq_false_iff.mpr
      rw [lhs]
      exact fun h => h.elim (no_flag x) (no_center x e)
    · rw [if_neg e]
      apply Bool.eq_false_iff.mpr
      rw [rhs]
      exact fun h => h.elim (no_flag x) (fun t => e (by simpa only [show (13 : Fin 26) = Fin.natAdd 13 (0 : V) from rfl,Fin.append_right] using t))

end LineZero7832

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate in
theorem PEqualNP.Outside.R_meta_7832_affine
    (child :
      let flags (x : Fin 25 → Bool) : Prop := ∃ p : Fin 13, ∃ l : Fin 12,
        (p=l.succ ∨ p=l.succ+1 ∨ p=l.succ+3 ∨ p=l.succ+9) ∧
        x ⟨p.val,by omega⟩=true ∧ x ⟨13+l.val,by omega⟩=true
      let central (x : Fin 25 → Bool) : Prop := ∃ p : Fin 13,
        (p=0 ∨ p=0+1 ∨ p=0+3 ∨ p=0+9) ∧ x ⟨p.val,by omega⟩=true
      ∃ (D : Circuit) (h a : Nat), D.size≤62 ∧ IsAO2 25 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        h<25+D.size ∧ a<25+D.size ∧
        ∀ x : Fin 25 → Bool, (wireValue D 25 x h=true ↔ flags x) ∧
          (wireValue D 25 x a=true ↔ flags x ∨ central x)) : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (13 : ℕ) → Bool), (∀ (x8 : Fin (13 : ℕ)), x7 x8 = Bool.false → ∃ (x10 : Fin (13 : ℕ)), x1 x8 x10 ∧ x2 x7 x10 = Bool.true) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (Fin.append x7 (x2 x7)) (if x2 x7 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false :=
  LineZero7832.build child
