import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804.FalseCodes
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def andB (g : Gate) : Bool := match g.op with | .and => true | _ => false
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def flag (w : List Bool) (g : Gate) := (g.inputs.map fun i => w.getD i false).headD false
def code : List Gate → List Bool → List Bool
  | [],_ => []
  | g::gs,w => if andB g then flag w g :: code gs (step w g) else code gs (step w g)

lemma length_code (gs : List Gate) (w : List Bool) : (code gs w).length=gs.countP andB := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => cases h : andB g <;> simp [code,h,ih,List.countP_cons]

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
  exact r.2.2 i (ha i hi) (hb i hi)

lemma and_false {a b c : List Bool} (r : relation a b c) (ins : List Nat)
    (len : ins.length≤2)
    (same : (ins.map (fun i => a.getD i false)).headD false=(ins.map (fun i => b.getD i false)).headD false)
    (ha : (ins.map (fun i => a.getD i false)).all id=false)
    (hb : (ins.map (fun i => b.getD i false)).all id=false) :
    (ins.map (fun i => c.getD i false)).all id=false := by
  cases ins with
  | nil => simp at ha
  | cons u us =>
    cases us with
    | nil => simpa using r.2.2 u (by simpa using ha) (by simpa using hb)
    | cons v vs =>
      have empty : vs=[] := List.length_eq_zero_iff.mp (by simp at len; omega)
      subst vs
      change a.getD u false=b.getD u false at same
      cases xu : a.getD u false with
      | false =>
        have yy := same.symm.trans xu
        have zz := r.2.2 u xu yy
        simp [zz]
      | true =>
        have yy := same.symm.trans xu
        have zz := r.2.2 v (by simpa [xu] using ha) (by simpa [yy] using hb)
        simp [zz]

theorem code_relation (gs : List Gate)
    (fan : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (a b c : List Bool) (rel : relation a b c) (same : code gs a=code gs b) :
    relation (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact rel
  | cons g gs ih =>
    have legal := fan g (by simp)
    have tail := fun s (hs : s∈gs) => fan s (List.mem_cons_of_mem _ hs)
    rcases legal.1 with op|op
    · have h := same
      simp only [code,andB,op,if_true,List.cons.injEq] at h
      apply ih tail _ _ _ (append_relation rel ?_) h.2
      simpa [op,GateOp.eval] using and_false rel g.inputs legal.2 (by simpa [flag] using h.1)
    · have h := same
      simp only [code,andB,op,Bool.false_eq_true,if_false] at h
      apply ih tail _ _ _ (append_relation rel ?_) h
      simpa [op,GateOp.eval] using or_false rel g.inputs

theorem count_ands {n N : Nat} (C : Circuit) (fan : Monotone2 C)
    (rows : Fin N → Fin n → Bool)
    (off : ∀ t, C.eval (List.ofFn (rows t))=false)
    (cross : ∀ i j, i≠j → C.eval (List.ofFn (fun v => rows i v || rows j v))=true) :
    N ≤ 2^(C.gates.countP andB) := by
  classical
  let enc (t : Fin N) (i : Fin (C.gates.countP andB)) :=
    (code C.gates (List.ofFn (rows t))).getD i.val false
  have injection : Function.Injective enc := by
    intro i j eq
    by_contra neq
    have same : code C.gates (List.ofFn (rows i))=code C.gates (List.ofFn (rows j)) := by
      apply List.ext_getElem
      · simp [length_code]
      · intro k hk hl
        have ky : k<C.gates.countP andB := by simpa [length_code] using hk
        have h := congrFun eq ⟨k,ky⟩
        change (code C.gates _).getD k false = (code C.gates _).getD k false at h
        simpa only [List.getD_eq_getElem _ _ hk,List.getD_eq_getElem _ _ hl] using h
    have raw : relation (List.ofFn (rows i)) (List.ofFn (rows j))
        (List.ofFn (fun v => rows i v || rows j v)) := by
      refine ⟨by simp,by simp,?_⟩
      intro k
      by_cases hk : k<n
      · simp only [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_ofFn]
        intro a b; simp [a,b]
      · simp only [List.getD_eq_default _ _ (by simp; omega)]
        simp
    have cert := code_relation C.gates (fun g h => ⟨by simpa using (fan g h).1,(fan g h).2⟩)
      _ _ _ raw same
    have z := cert.2.2 C.output (off i) (off j)
    exact Bool.noConfusion ((cross i j neq).symm.trans z)
  have cnt := Fintype.card_le_of_injective enc injection
  simpa [Fintype.card_fun] using cnt

end PEqualNP.Outside.L_meta_9804.FalseCodes
