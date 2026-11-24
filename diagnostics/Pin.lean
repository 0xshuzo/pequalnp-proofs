import Mathlib
import PEqualNP.Defs

namespace Pin3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def good (m : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
    gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < m+j

def rawReads (z : Nat) (gs : List Gate) := gs.countP (fun g => g.inputs.contains z)

def atWire (w : List Bool) (o : Option Nat) := o.elim false (fun i => w.getD i false)

theorem atWire_append (w : List Bool) (b : Bool) (o : Option Nat) (h : ∀ i ∈ o, i < w.length) :
    atWire (w++[b]) o = atWire w o := by
  cases o with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (h i (by simp))

theorem getD_snoc (xs : List Bool) (b : Bool) (i : Nat) :
    (xs ++ [b]).getD i false = if i=xs.length then b else xs.getD i false := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
  · by_cases eq : i=xs.length
    · subst i; simp
    · rw [List.getD_eq_default _ _ (by simp; omega), ite_eq_right eq, List.getD_eq_default _ _ (by omega)]

theorem run_len (gs : List Gate) (xs : List Bool) : (run gs xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (xs++[_])).length=_
    rw [ih];simp;omega

theorem good_snoc {m : Nat} {gs : List Gate} (h : good m gs) (g : Gate)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length=2) (back : ∀ i ∈ g.inputs, i < m + gs.length) :
    good m (gs++[g]) := by
  intro j hj
  by_cases lt : j < gs.length
  · rw [List.getElem_append_left lt]
    exact h j lt
  · have eq : j=gs.length := by simp at hj; omega
    subst j
    simpa using And.intro op (And.intro arity back)

theorem good_left {m : Nat} {gs : List Gate} {g : Gate} (h : good m (gs++[g])) : good m gs := by
  intro j hj
  have v := h j (by simp;omega)
  simpa only [List.getElem_append_left hj] using v

theorem good_last {m : Nat} {gs : List Gate} {g : Gate} (h : good m (gs++[g])) :
    (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ ∀ i ∈ g.inputs, i < m + gs.length := by
  simpa using h gs.length (by simp)

theorem binary {g : Gate} (h : g.inputs.length=2) : ∃ a b, g.inputs=[a,b] := by
  exact List.length_eq_two.mp h

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w = run gs w ++ [g.op.eval (g.inputs.map fun j => (run gs w).getD j false)] := by
  simp [run,List.foldl_append]

theorem translate {n : Nat} (z : Fin n) (gs : List Gate) (hg : good n gs) :
    ∃ (ds : List Gate) (tab : Nat → Option Nat), good n ds ∧
      ds.length + rawReads z.val gs ≤ gs.length ∧ tab z.val = none ∧
      (∀ i, ∀ j ∈ tab i, j < n + ds.length) ∧
      ∀ (x : Fin n → Bool) (i : Nat),
        (run gs (List.ofFn (Function.update x z false))).getD i false =
          atWire (run ds (List.ofFn x)) (tab i) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    let tab : Nat → Option Nat := fun i => if i<n ∧ i≠z.val then some i else none
    refine ⟨[], tab, by simp [good], by simp [rawReads], by simp [tab], ?_, ?_⟩
    · intro i j hj
      by_cases hi : i<n ∧ i≠z.val <;> simp [tab,hi] at hj
      subst j
      simpa using hi.1
    · intro x i
      by_cases hi : i<n
      · let k : Fin n := ⟨i,hi⟩
        by_cases eq : i=z.val
        · have ke : k=z := Fin.ext eq
          subst i
          simp [run,tab,atWire]
        · have kdiff : k ≠ z := fun e => eq (congrArg Fin.val e)
          have on : i<n ∧ i≠z.val := ⟨hi,eq⟩
          change (List.ofFn (Function.update x z false)).getD k.val false = atWire (List.ofFn x) (tab i)
          simp [tab,on,atWire,List.getD_eq_getElem?_getD,hi,k,Function.update_of_ne kdiff]
      · have stop : ¬(i<n ∧ i≠z.val) := fun h => hi h.1
        change (List.ofFn (Function.update x z false)).getD i false = atWire (List.ofFn x) (tab i)
        rw [List.getD_eq_default _ _ (by simp;omega)]
        simp [tab,stop,atWire]
  | append_singleton gs g ih =>
    obtain ⟨ds,tab,gd,sz,tz,live,sim⟩ := ih (good_left hg)
    obtain ⟨op,arity,back⟩ := good_last hg
    obtain ⟨a,b,ab⟩ := binary arity
    let old := n+gs.length
    let new := n+ds.length
    have adjust (added : List Gate) (o : Option Nat)
        (valid : good n (ds++added))
        (cost : (ds++added).length + rawReads z.val (gs++[g]) ≤ (gs++[g]).length)
        (ob : ∀ j ∈ o, j < n + (ds++added).length)
        (carry : ∀ (x : Fin n → Bool) i, atWire (run (ds++added) (List.ofFn x)) (tab i)=atWire (run ds (List.ofFn x)) (tab i))
        (eval : ∀ (x : Fin n → Bool), g.op.eval [atWire (run ds (List.ofFn x)) (tab a),atWire (run ds (List.ofFn x)) (tab b)] =
            atWire (run (ds++added) (List.ofFn x)) o) :
        ∃ (ds : List Gate) (tab : Nat → Option Nat), good n ds ∧
          ds.length + rawReads z.val (gs++[g]) ≤ (gs++[g]).length ∧ tab z.val = none ∧
          (∀ i, ∀ j ∈ tab i, j < n + ds.length) ∧
          ∀ (x : Fin n → Bool) i, (run (gs++[g]) (List.ofFn (Function.update x z false))).getD i false =
            atWire (run ds (List.ofFn x)) (tab i) := by
      let nxt i := if i=old then o else tab i
      have zlt : z.val<old := by dsimp [old];omega
      refine ⟨ds++added,nxt,valid,cost,by simpa [nxt,Nat.ne_of_lt zlt] using tz,?_,?_⟩
      · intro i j h
        by_cases eq : i=old
        · exact ob j (by simpa [nxt,eq] using h)
        · have := live i j (by simpa [nxt,eq] using h)
          simp;omega
      · intro x i
        let xs := List.ofFn (Function.update x z false)
        have len : (run gs xs).length=old := by simp [xs,run_len,old]
        change (run (gs++[g]) xs).getD i false=_
        rw [run_snoc,getD_snoc,len]
        by_cases eq : i=old
        · simp only [ite_eq_left eq,nxt,ab,List.map_cons,List.map_nil]
          rw [show (run gs xs).getD a false=_ from sim x a,
              show (run gs xs).getD b false=_ from sim x b]
          exact eval x
        · simp only [ite_eq_right eq,nxt]
          exact (sim x i).trans (carry x i).symm
    have one : rawReads z.val (gs++[g]) ≤ rawReads z.val gs + 1 := by
      simp [rawReads,List.countP_append];split <;> omega
    have keep (o : Option Nat) (ob : ∀ j ∈ o,j < new)
        (eval : ∀ x : Fin n → Bool, g.op.eval [atWire (run ds (List.ofFn x)) (tab a),atWire (run ds (List.ofFn x)) (tab b)]
          = atWire (run ds (List.ofFn x)) o) := adjust [] o (by simpa using gd)
      (by simp; omega) (by simpa [new] using ob) (by simp) (by simpa using eval)
    cases ea : tab a with
    | none =>
      rcases op with op|op
      · apply keep none (by simp)
        intro x; simp [ea,op,atWire,GateOp.eval]
      · apply keep (tab b) (live b)
        intro x; simp [ea,op,atWire,GateOp.eval]
    | some a' =>
      cases eb : tab b with
      | none =>
        rcases op with op|op
        · apply keep none (by simp)
          intro x; simp [eb,op,atWire,GateOp.eval]
        · apply keep (tab a) (live a)
          intro x; simp [eb,op,atWire,GateOp.eval]
      | some b' =>
        let g' : Gate := ⟨g.op,[a',b']⟩
        have ha : a'<new := live a a' (by simp [ea])
        have hb : b'<new := live b b' (by simp [eb])
        have az : a≠z.val := by rintro rfl; rw [tz] at ea; contradiction
        have bz : b≠z.val := by rintro rfl; rw [tz] at eb; contradiction
        have no : g.inputs.contains z.val=false := by simp [ab,az,bz,Ne.symm az,Ne.symm bz]
        apply adjust [g'] (some new)
        · apply good_snoc gd g' op rfl
          intro i hi
          rcases (by simpa [g'] using hi : i=a' ∨ i=b') with rfl|rfl
          · exact ha
          · exact hb
        · simpa [rawReads,List.countP_append,no] using sz
        · intro j hj; have eq : new=j := by simpa using hj
          subst j; simp [new]
        · intro x i
          rw [run_snoc]
          apply atWire_append
          intro j hj;simpa [run_len] using live i j hj
        · intro x
          rw [run_snoc]
          have len : (run ds (List.ofFn x)).length=new := by simp [run_len,new]
          simp [g',atWire,getD_snoc,len,ea,eb]
end Pin3566
