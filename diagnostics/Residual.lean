import PEqualNP.Defs

namespace FanoVertex18627
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev I := Fin 7
abbrev V := Fin 14
def next (C : Circuit) : Nat := 14+C.gates.length
def val (C : Circuit) (x : V → Bool) (w : Nat) : Bool := (C.wires (List.ofFn x)).getD w false
def app (C : Circuit) (op : GateOp) (a b : Nat) : Circuit := ⟨C.gates++[⟨op,[a,b]⟩],next C⟩
@[simp] theorem next_app (C : Circuit) (op : GateOp) (a b : Nat) :
    next (app C op a b) = next C+1 := by simp [next,app,Nat.add_assoc]
@[simp] theorem out_app (C : Circuit) (op : GateOp) (a b : Nat) :
    (app C op a b).output=next C := rfl
@[simp] theorem size_app (C : Circuit) (op : GateOp) (a b : Nat) :
    (app C op a b).size=C.size+1 := by simp [app,Circuit.size]
lemma wires_app (C : Circuit) (op : GateOp) (a b : Nat) (x : V → Bool) :
    (app C op a b).wires (List.ofFn x) = C.wires (List.ofFn x) ++
      [op.eval [val C x a,val C x b]] := by
  simp [Circuit.wires,app,val,List.foldl_append]
lemma wires_len (C : Circuit) (x : V → Bool) :
    (C.wires (List.ofFn x)).length = next C := by
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length = _
  have hl (gs : List Gate) (l : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length = l.length+gs.length := by
    induction gs generalizing l with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,List.length_append,List.length_singleton,List.length_cons];omega
  rw [hl,List.length_ofFn];rfl
theorem newVal (C : Circuit) (op : GateOp) (a b : Nat) (x : V → Bool) :
    val (app C op a b) x (next C) = op.eval [val C x a,val C x b] := by
  unfold val
  rw [wires_app,← wires_len C x]
  simp [List.getD_eq_getElem?_getD,val]
theorem oldVal (C : Circuit) (op : GateOp) (a b w : Nat) (x : V → Bool) (h : w<next C) :
    val (app C op a b) x w = val C x w := by
  rw [← wires_len C x] at h
  simp only [val,wires_app,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
theorem inputVal (C : Circuit) (x : V → Bool) (r : V) : val C x r.val = x r := by
  have keep (gs : List Gate) (l : List Bool) (r : Nat) (hr : r<l.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD r false = l.getD r false := by
    induction gs generalizing l with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp;omega)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hr]
  change (C.gates.foldl _ (List.ofFn x)).getD r.val false = _
  rw [keep _ _ _ (by simpa using r.isLt),List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]
theorem app_mono (C : Circuit) (hm : Monotone2 C) (op : GateOp) (ho : op=.and ∨ op=.or)
    (a b : Nat) : Monotone2 (app C op a b) := by
  intro g hg
  change g ∈ C.gates++[_] at hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with h|rfl
  · exact hm g h
  · rcases ho with rfl|rfl <;> simp
def star (C : Circuit) (r a b c : V) : Circuit :=
  let A := app C .or a.val b.val
  let B := app A .or A.output c.val
  let D := app B .and r.val B.output
  app D .or C.output D.output
theorem starFacts (C : Circuit) (r a b c : V) (hm : Monotone2 C) (ho : C.output<next C) :
    let D := star C r a b c
    Monotone2 D ∧ D.output<next D ∧ D.size=C.size+4 ∧
    ∀ x : V → Bool, D.eval (List.ofFn x) = (C.eval (List.ofFn x) || (x r && (x a || x b || x c))) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · unfold star
    repeat first | apply app_mono | exact hm | exact Or.inl rfl | exact Or.inr rfl
  · simp [star]
  · simp [star,Nat.add_assoc]
  · intro x
    change val (star C r a b c) x (star C r a b c).output = (val C x C.output || _)
    have raw (t : V) : t.val<next C := by have := t.isLt;unfold next;omega
    have hR := raw r
    have hA := raw a
    have hB := raw b
    have hL := raw c
    simp (disch := (simp only [next_app]; omega)) only [star,out_app,newVal,oldVal,inputVal,GateOp.eval,
      List.map_cons,List.map_nil,List.any_cons,List.all_cons,List.any_nil,List.all_nil,Bool.or_false,Bool.and_true]
def edge (p l : I) : Prop := p=l ∨ p=l+1 ∨ p=l+3
def row (p : I) (x : V→Bool) : Prop := ∃l : I,edge p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
def layer (U : Finset I) (x : V→Bool) : Prop := ∃p∈U,row p x
theorem row_iff (p : I) (x : V→Bool) : row p x ↔ x (Fin.castAdd 7 p)=true ∧
    (x (Fin.natAdd 7 p)=true ∨ x (Fin.natAdd 7 (p-1))=true ∨ x (Fin.natAdd 7 (p-3))=true) := by
  have choices : ∀ u v : I,edge u v ↔ v=u ∨ v=u-1 ∨ v=u-3 := by decide +kernel
  constructor
  · rintro ⟨l,h,hp,hl⟩
    refine ⟨hp,?_⟩
    rcases (choices p l).1 h with rfl|rfl|rfl <;> simp_all
  · rintro ⟨hp,hl|hl|hl⟩
    · exact ⟨p,(choices _ _).2 (Or.inl rfl),hp,hl⟩
    · exact ⟨p-1,(choices _ _).2 (Or.inr (Or.inl rfl)),hp,hl⟩
    · exact ⟨p-3,(choices _ _).2 (Or.inr (Or.inr rfl)),hp,hl⟩
theorem restore (S : Finset I) (C : Circuit) (hm : Monotone2 C) (ho : C.output<next C) :
    ∃ D : Circuit, Monotone2 D ∧ D.output<next D ∧ D.size=C.size+4*S.card ∧
      ∀ x : V → Bool, D.eval (List.ofFn x)=true ↔ C.eval (List.ofFn x)=true ∨ layer S x := by
  induction S using Finset.induction_on with
  | empty => exact ⟨C,hm,ho,by simp,by simp [layer]⟩
  | @insert p S h ih =>
    obtain ⟨D,dm,dok,sz,ev⟩ := ih
    obtain ⟨em,eok,esz,ee⟩ := starFacts D (Fin.castAdd 7 p) (Fin.natAdd 7 p)
      (Fin.natAdd 7 (p-1)) (Fin.natAdd 7 (p-3)) dm dok
    refine ⟨_,em,eok,?_,?_⟩
    · rw [esz,sz,Finset.card_insert_of_notMem h];omega
    · intro x
      have ins : layer (insert p S) x ↔ row p x ∨ layer S x := by simp [layer]
      rw [ee, Bool.or_eq_true_iff, Bool.and_eq_true_iff, Bool.or_eq_true_iff,Bool.or_eq_true_iff,ev,ins,row_iff p x]
      tauto
theorem priced (floor : ∀ D : Circuit, Monotone2 D →
    (∀ x : V→Bool,D.eval (List.ofFn x)=true ↔ layer Finset.univ x) → 27≤D.size)
    (U : Finset I) (C : Circuit) (hm : Monotone2 C) (ho : C.output<next C)
    (rep : ∀ x : V→Bool,C.eval (List.ofFn x)=true ↔ layer U x) : 4*U.card ≤ C.size+1 := by
  obtain ⟨D,dm,_,sz,ev⟩ := restore (Finset.univ \ U) C hm ho
  have good (x : V→Bool) : D.eval (List.ofFn x)=true ↔ layer Finset.univ x := by
    rw [ev,rep]
    simp only [layer]
    constructor
    · rintro (⟨p,_,h⟩|⟨p,_,h⟩) <;> exact ⟨p,Finset.mem_univ _,h⟩
    · rintro ⟨p,_,hp⟩
      by_cases h:p∈U
      · exact Or.inl ⟨p,h,hp⟩
      · exact Or.inr ⟨p,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩,hp⟩
  have lb := floor D dm good
  have hc : ∀ S : Finset I, (Finset.univ \ S).card+S.card=7 := by decide +kernel
  have card := hc U
  omega
end FanoVertex18627
