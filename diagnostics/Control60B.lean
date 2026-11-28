import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18670
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Term := List (Fin 24)
abbrev Form := List Term
abbrev Instr := Bool × Nat × Nat
def prod (a b : Form) : Form := a.flatMap (fun u => b.map (u++·))
def value (x : Fin 24 → Bool) (a : Form) := a.any (fun u => u.all x)
theorem prod_value (x : Fin 24 → Bool) (a b : Form) :
    value x (prod a b) = (value x a && value x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [value,prod,List.any_eq_true,List.mem_flatMap,List.mem_map,List.all_append,Bool.and_eq_true]
  constructor
  · rintro ⟨t,⟨u,hu,v,hv,rfl⟩,h⟩
    have both : u.all x = true ∧ v.all x = true := by simpa only [List.all_append,Bool.and_eq_true] using h
    obtain ⟨h1,h2⟩ := both
    exact ⟨⟨u,hu,h1⟩,v,hv,h2⟩
  · rintro ⟨⟨u,hu,h1⟩,v,hv,h2⟩
    exact ⟨u++v,⟨u,hu,v,hv,rfl⟩,by simp [h1,h2]⟩

def gate (i : Instr) : Gate := ⟨if i.1 then .or else .and,[i.2.1,i.2.2]⟩
def produce (A : List Form) (i : Instr) : List Form :=
  let a := A.getD i.2.1 []
  let b := A.getD i.2.2 []
  A ++ [if i.1 then a++b else prod a b]
def sem (x : Fin 24 → Bool) (A : List Form) := A.map (value x)
theorem get_sem (x : Fin 24 → Bool) (A : List Form) (k : Nat) :
    (sem x A).getD k false = value x (A.getD k []) := by
  simp only [sem,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases A[k]? <;> rfl
theorem eval_fold (x : Fin 24 → Bool) (s : List Instr) (A : List Form) :
    (s.map gate).foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
       (sem x A) = sem x (s.foldl produce A) := by
  induction s generalizing A with
  | nil => rfl
  | cons i s ih =>
    rcases i with ⟨b,a,c⟩
    rw [List.map_cons,List.foldl_cons,List.foldl_cons,←ih (produce A (b,a,c))]
    congr 1
    cases b <;> simp [produce,gate,sem,List.map_append,GateOp.eval,value,prod_value,List.any_append,get_sem]
    · change ((A[a]?.map (value x)).getD false && (A[c]?.map (value x)).getD false) =
          value x (prod (A[a]?.getD []) (A[c]?.getD []))
      rw [prod_value]
      cases A[a]? <;> cases A[c]? <;> rfl
    · change ((A[a]?.map (value x)).getD false || (A[c]?.map (value x)).getD false) =
          (value x (A[a]?.getD []) || value x (A[c]?.getD []))
      cases A[a]? <;> cases A[c]? <;> rfl
def layout : List Instr := [(true,0,1),(true,24,3),(true,15,16),(true,26,18),(true,12,14),(true,20,28),(true,13,19),(true,30,23),(true,22,12),(true,18,32),(true,33,23),(true,21,22),(true,17,35),(true,21,23),(true,20,37),(true,38,16),(true,20,22),(true,19,40),(true,41,15),(true,14,18),(true,21,19),(true,43,44),(true,18,13),(true,17,46),(true,47,20),(true,19,12),(true,17,16),(true,49,50),(true,15,23),(true,52,14),(true,17,53),(true,16,14),(true,55,13),(true,56,22),(true,13,21),(true,15,12),(true,59,58),(false,0,29),(false,1,31),(false,2,34),(false,3,36),(false,4,39),(false,5,42),(false,6,45),(false,7,48),(false,8,51),(false,9,54),(false,10,57),(false,11,60),(true,61,62),(true,73,63),(true,74,64),(true,75,65),(true,76,66),(true,77,67),(true,78,68),(true,79,69),(true,80,70),(true,81,71),(true,82,72)]
def C : Circuit := ⟨layout.map gate,83⟩
def raw : List Form := (List.finRange 24).map (fun i => [[i]])
def form (k : Nat) := (layout.foldl produce raw).getD k []
theorem read_form (x : Fin 24 → Bool) (k : Nat) :
    (C.wires (List.ofFn x)).getD k false = value x (form k) := by
  have h : sem x raw = List.ofFn x := by simp [sem,raw,value,List.finRange,List.map_ofFn]
  unfold Circuit.wires C
  rw [←h,eval_fold]
  exact get_sem x _ k

def link (a b : Fin 12) : Prop := (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈ ({0,1,3,9} : Finset (Fin 13))
instance (a b : Fin 12) : Decidable (link a b) := by unfold link;infer_instance
def marks (b : Bool) : Finset (Fin 24) := if b=true then {15,16,18} else {0,1,3}
def mark (b : Bool) : Nat := if b=true then 27 else 25
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem flags (t : Term) : t ∈ form 83 ↔ ∃ a b : Fin 12, link a b ∧ t=[a.castAdd 12,b.natAdd 12] := by
  have h : (form 83).all (fun t => decide (∃ a b : Fin 12, link a b ∧ t=[a.castAdd 12,b.natAdd 12]))=true := by decide +kernel
  have back : ∀ a b : Fin 12,link a b → [a.castAdd 12,b.natAdd 12] ∈ form 83 := by decide +kernel
  constructor
  · intro ht;exact of_decide_eq_true (List.all_eq_true.mp h t ht)
  · rintro ⟨a,b,edge,rfl⟩;exact back a b edge

theorem correct (x : Fin 24 → Bool) :
    C.eval (List.ofFn x)=true ↔ ∃ a b : Fin 12, link a b ∧ x (a.castAdd 12)=true ∧ x (b.natAdd 12)=true := by
  change (C.wires (List.ofFn x)).getD 83 false=true ↔ _
  rw [read_form]
  change (form 83).any (fun t => t.all x)=true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t,ht,hx⟩
    obtain ⟨a,b,edge,rfl⟩ := (flags t).mp ht
    exact ⟨a,b,edge,by simpa using hx⟩
  · rintro ⟨a,b,edge,h1,h2⟩
    exact ⟨_,(flags _).mpr ⟨a,b,edge,rfl⟩,by simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true];exact ⟨h1,h2⟩⟩

theorem marked (x : Fin 24 → Bool) (b : Bool) :
    (C.wires (List.ofFn x)).getD (mark b) false=true ↔ ∃ i ∈ marks b, x i=true := by
  rw [read_form]
  have h1 : form 25 = [[0],[1],[3]] := by decide +kernel
  have h2 : form 27 = [[15],[16],[18]] := by decide +kernel
  cases b <;> simp [mark,marks,value,h1,h2]

theorem control60 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (x2 x3 : Fin (12 : ℕ)) => Fin.succAbove (9 : Fin (13 : ℕ)) x2 + Fin.succAbove (0 : Fin (13 : ℕ)) x3 ∈ x1; have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x2 x5 x4 → x3 x5 = Bool.false); have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x2 x5 x6 → x4 x6 = Bool.false); have x5 : Bool → Finset (Fin (24 : ℕ)) := fun (x5 : Bool) => if x5 = Bool.true then {(15 : Fin (24 : ℕ)), (16 : Fin (24 : ℕ)), (18 : Fin (24 : ℕ))} else {(0 : Fin (24 : ℕ)), (1 : Fin (24 : ℕ)), (3 : Fin (24 : ℕ))}; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x6 ∧     x6.size ≤ (60 : ℕ) ∧       x6.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧         Max.max x6.output (Max.max x7 x8) < (24 : ℕ) + x6.size ∧           (∀ (x9 x10 : Fin (12 : ℕ)), x2 x9 x10 → x6.eval (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (12 : ℕ) x9 ∨ x12 = Fin.natAdd (12 : ℕ) x10)) = Bool.true) ∧             (∀ (x9 : Bool), ∀ x10 ∈ x5 x9, (x6.wires (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = x10))).getD (if x9 = Bool.true then x8 else x7) Bool.false = Bool.true) ∧               ∀ (x9 : Fin (12 : ℕ) → Bool),                 x4 (x3 x9) = x9 →                   have x11 : Fin (24 : ℕ) → Bool := Fin.append x9 (x3 x9);                   x6.eval (List.ofFn x11) = Bool.false ∧ ∀ (x12 : Bool), (x6.wires (List.ofFn fun (x13 : Fin (24 : ℕ)) => if x13 ∈ x5 x12 then Bool.false else x11 x13)).getD (if x12 = Bool.true then x8 else x7) Bool.false = Bool.false := by
  dsimp only
  refine ⟨C,25,27,?_,by decide +kernel,rfl,by decide +kernel,?_,?_,?_⟩
  · intro g hg
    change g ∈ layout.map gate at hg
    obtain ⟨⟨b,a,c⟩,_,rfl⟩ := List.mem_map.mp hg
    cases b <;> simp [gate]
  · intro a b edge
    apply (correct _).mpr
    exact ⟨a,b,edge,by simp,by simp⟩
  · intro b i hi
    exact (marked _ b).mpr ⟨i,hi,by simp⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a,b,edge,ha,hb⟩ := (correct _).mp h
      simp only [Fin.append_left,Fin.append_right] at ha hb
      exact Bool.noConfusion (ha.symm.trans ((of_decide_eq_true hb) a edge))
    · intro b
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨i,hi,hv⟩ := (marked _ b).mp h
      change (if i ∈ marks b then false else _) = true at hv
      simp [hi] at hv
end PEqualNP.Outside.L_meta_18670
