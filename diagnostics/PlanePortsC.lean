import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3310

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩


end Circ2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def input {N : ℕ} (P L : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p∈P)) (fun l => decide (l∈L))

def Hit {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Finset (Fin N)) : Prop :=
  ∃ p ∈ P, ∃ l ∈ L, I p l

theorem input_l {N} (P L : Finset (Fin N)) (p : Fin N) :
    input P L (Fin.castAdd N p) = decide (p∈P) := Fin.addCases_left ..
theorem input_r {N} (P L : Finset (Fin N)) (l : Fin N) :
    input P L (Fin.natAdd N l) = decide (l∈L) := Fin.addCases_right ..

theorem wire_mono {N} {C : Circuit} (hm : Monotone2 C) {P P' L L' : Finset (Fin N)}
    (hp : P ⊆ P') (hl : L ⊆ L') (w : ℕ) :
    val C (input P L) w = true → val C (input P' L') w = true := by
  apply acts_mono hm
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp only [input_l,decide_eq_true_eq]
    exact fun h => hp h
  · intro l
    simp only [input_r,decide_eq_true_eq]
    exact fun h => hl h

theorem and_parents {n : ℕ} (C : Circuit) (ho : n ≤ C.output)
    (hop : ∃ g : Gate, C.gates[C.output-n]? = some g ∧ g.op = GateOp.and)
    (hs : ∀ j (g : Gate), C.gates[j]? = some g →
      ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j) :
    ∃ a b : ℕ, a<b ∧ b<C.output ∧ ∀ x : Fin n → Bool,
      circuitFun n C x = (val C x a && val C x b) := by
  obtain ⟨g,hg,op⟩ := hop
  obtain ⟨a,b,ins,ab,bo⟩ := hs _ _ hg
  have eq : n+(C.output-n)=C.output := by omega
  rw [eq] at bo
  refine ⟨a,b,ab,bo,?_⟩
  intro x
  change val C x C.output = _
  have hh := val_gate C x hg
  rw [eq,ins,op] at hh
  simpa [operand,ab.trans bo,bo,GateOp.eval] using hh

def PairOK {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ p l, I p l → circuitFun (N+N) C
    (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true

def Rejects {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
    (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false

theorem sets_exact {N q} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hm : Monotone2 C) (hpos : PairOK I C) (hneg : Rejects q I C)
    (P L : Finset (Fin N)) (small : L.card ≤ q) :
    circuitFun (N+N) C (input P L) = true ↔ Hit I P L := by
  constructor
  · intro h
    by_contra bad
    have card : Fintype.card {l : Fin N // input P L (Fin.natAdd N l) = true} = L.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,input_r,decide_eq_true_eq]
    have err := hneg (input P L) (card.trans_le small) (by
      rintro ⟨p,l,pl,hp,hl⟩
      exact bad ⟨p,by simpa only [input_l,decide_eq_true_eq] using hp,l,
        by simpa only [input_r,decide_eq_true_eq] using hl,pl⟩)
    simp [h] at err
  · rintro ⟨p,hp,l,hl,pl⟩
    have good := hpos p l pl
    apply acts_mono (C:=C) hm (x:=fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l))
      (y:=input P L) _ C.output good
    rintro i h
    rcases of_decide_eq_true h with rfl | rfl
    · rw [input_l]; exact decide_eq_true hp
    · rw [input_r]; exact decide_eq_true hl


def outside {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (L : Finset (Fin N)) : Finset (Fin N) := Finset.univ.filter fun p => ∀ l ∈ L, ¬ I p l

theorem outside_miss {N} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (L : Finset (Fin N)) : ¬Hit I (outside I L) L := by
  rintro ⟨p,hp,l,hl,h⟩
  exact (Finset.mem_filter.mp hp).2 l hl h

theorem escape_line {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {L : Finset (Fin N)} (small : L.card≤q) {b : Fin N} (out : b∉L) :
    ∃ p ∈ outside I L, I p b := by
  classical
  by_contra fail
  let S := Finset.univ.filter (fun p : Fin N => I p b)
  have chooseLine (p : Fin N) (hp : p ∈ S) : ∃ l ∈ L, I p l := by
    by_contra none
    have po : p ∈ outside I L := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l hl h => none ⟨l,hl,h⟩⟩
    exact fail ⟨p,po,(Finset.mem_filter.mp hp).2⟩
  choose! f hf using chooseLine
  have bound : S.card ≤ L.card := by
    apply Finset.card_le_card_of_injOn f (fun p hp => (hf p hp).1)
    intro p hp p' hp' same
    by_contra ne
    have one := unique p p' ne
    have shared : I p (f p) ∧ I p' (f p) := ⟨(hf p hp).2,same ▸ (hf p' hp').2⟩
    have eq := one.unique shared ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hp').2⟩
    exact out (eq ▸ (hf p hp).1)
  have card : S.card = q+1 := by simpa only [S,Fintype.card_subtype] using hdeg b
  omega

theorem incomparable_inputs {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {L M : Finset (Fin N)} (ls : L.card≤q) (ms : M.card≤q) (ne : L≠M) :
    Hit I (outside I L ∪ outside I M) (L∪M) := by
  classical
  by_cases sub : M ⊆ L
  · obtain ⟨b,bl,bm⟩ := Finset.not_subset.mp (fun rev : L ⊆ M => ne (Finset.Subset.antisymm rev sub))
    obtain ⟨p,hp,hit⟩ := escape_line I hdeg unique ms bm
    exact ⟨p,Finset.mem_union_right _ hp,b,Finset.mem_union_left _ bl,hit⟩
  · obtain ⟨b,bm,bl⟩ := Finset.not_subset.mp sub
    obtain ⟨p,hp,hit⟩ := escape_line I hdeg unique ls bl
    exact ⟨p,Finset.mem_union_left _ hp,b,Finset.mem_union_right _ bm,hit⟩

theorem true_of_incidence {N} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hm : Monotone2 C) (accept : PairOK I C) (P L : Finset (Fin N)) (hit : Hit I P L) :
    circuitFun (N+N) C (input P L) = true := by
  obtain ⟨p,hp,l,hl,pl⟩ := hit
  apply acts_mono (C:=C) hm (x:=fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l))
    (y:=input P L) _ C.output (accept p l pl)
  rintro i h
  rcases of_decide_eq_true h with rfl | rfl
  · rw [input_l]; exact decide_eq_true hp
  · rw [input_r]; exact decide_eq_true hl

theorem root_separates {N q} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    {L M : Finset (Fin N)} (ls : L.card≤q) (ms : M.card≤q) (ne : L≠M) :
    circuitFun (N+N) C (input (outside I L) L) = false ∧
    circuitFun (N+N) C (input (outside I M) M) = false ∧
    circuitFun (N+N) C (input (outside I L ∪ outside I M) (L∪M)) = true := by
  have off (X : Finset (Fin N)) (small : X.card≤q) :
      circuitFun (N+N) C (input (outside I X) X) = false := by
    have contra := (sets_exact hm accept reject (outside I X) X small).not.mpr (outside_miss I X)
    cases h : circuitFun (N+N) C (input (outside I X) X) <;> simp_all
  exact ⟨off L ls,off M ms,true_of_incidence hm accept _ _ (incomparable_inputs I hdeg unique ls ms ne)⟩


theorem input_union {N} (P Q L M : Finset (Fin N)) (i : Fin (N+N)) :
    input (P∪Q) (L∪M) i = (input P L i || input Q M i) := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [input_l,Finset.mem_union]
  · intro l
    rw [input_r,input_r,input_r]; simp [Finset.mem_union]

section
variable {α : Type} [DecidableEq α]

private instance gateOpDec (a : GateOp) : Decidable (a=GateOp.or) := by
  cases a <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)


private def readSets (w : List (Finset α)) (g : Gate) :=
  g.inputs.map (fun i => w.getD i ∅)

private def outSet (w : List (Finset α)) (g : Gate) : Finset α :=
  if g.op = GateOp.or then g.inputs.toFinset.biUnion (fun i => w.getD i ∅) else ∅

def ports (o : ℕ) : List Gate → List (Finset α) → List (Finset α)
  | [], w => [w.getD o ∅]
  | g::gs, w =>
    (if g.op = GateOp.or then [] else readSets w g) ++ ports o gs (w++[outSet w g])

theorem ports_length (o : ℕ) (gs : List Gate)
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (w : List (Finset α)) :
    (ports o gs w).length ≤ 2*(gs.filter (fun g => !(g.op.eval [true,false]))).length+1 := by
  induction gs generalizing w with
  | nil => simp [ports]
  | cons g gs ih =>
    have tail := ih (fun k h => hm k (List.mem_cons_of_mem g h)) (w++[outSet w g])
    obtain ⟨op,ar⟩ := hm g (by simp)
    rcases op with h|h <;> simp [ports,h,GateOp.eval,readSets] at * <;> omega

private theorem at_append {β : Type} (w : List β) (x d : β) (i : ℕ) :
    (w++[x]).getD i d = if i<w.length then w.getD i d else if i=w.length then x else d := by
  rcases lt_trichotomy i w.length with hi|hi|hi
  · rw [List.getD_append _ _ _ _ hi, if_pos hi]
  · subst i
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k,hk⟩ : ∃ k, i-w.length=k+1 := ⟨i-w.length-1,by omega⟩
    simp [hk,show ¬i<w.length by omega,show i≠w.length by omega]

private def evG (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun vs g => vs++[g.op.eval (g.inputs.map fun i => vs.getD i false)]) w

private def Invariant (p : α) (L : Finset α) (w : List (Finset α)) (a b : List Bool) :=
  ∀ i, (b.getD i false=false → w.getD i ∅ ⊆ L) ∧
    (a.getD i false=true → b.getD i false=false → p ∈ w.getD i ∅)

private theorem forward (o : ℕ) (p : α) (L : Finset α) (gs : List Gate)
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (w : List (Finset α)) (a b : List Bool) (ha : a.length=w.length) (hb : b.length=w.length)
    (inv : Invariant p L w a b)
    (on : (evG gs a).getD o false=true) (off : (evG gs b).getD o false=false) :
    ∃ S ∈ ports o gs w, p∈S ∧ S⊆L := by
  induction gs generalizing w a b with
  | nil => exact ⟨w.getD o ∅,by simp [ports],(inv o).2 on off,(inv o).1 off⟩
  | cons g gs ih =>
    classical
    let rd (v : List Bool) := g.op.eval (g.inputs.map fun i => v.getD i false)
    let S := outSet w g
    let here := if g.op = GateOp.or then [] else readSets w g
    by_cases hit : ∃ s ∈ here, p∈s ∧ s⊆L
    · obtain ⟨s,hs,hp,hl⟩ := hit
      exact ⟨s,List.mem_append_left _ hs,hp,hl⟩
    have hstep : (rd b=false → S⊆L) ∧ (rd a=true → rd b=false → p∈S) := by
      obtain ⟨op,_⟩ := hm g (by simp)
      rcases op with hand | hor
      · constructor
        · simp [S,outSet,hand]
        · intro oa ob
          have allA : ∀ i ∈ g.inputs, a.getD i false=true := by
            simpa [rd,hand,GateOp.eval,List.all_map,Function.comp_def] using oa
          have exB : ∃ i ∈ g.inputs, b.getD i false=false := by
            by_contra! h
            have allB : ∀ i ∈ g.inputs, b.getD i false=true := by
              intro i hi
              cases v : b.getD i false <;> simp_all
            have eb : rd b=true := by
              simpa [rd,hand,GateOp.eval,List.all_map,Function.comp_def] using allB
            simp [eb] at ob
          obtain ⟨i,hi,hb'⟩ := exB
          exact (hit ⟨w.getD i ∅, by simp [here,hand,readSets]; exact ⟨i,hi,rfl⟩,
            (inv i).2 (allA i hi) hb',(inv i).1 hb'⟩).elim
      · have noB (h : rd b=false) (i) (hi : i ∈ g.inputs) : b.getD i false=false := by
          by_contra! bad
          have v : b.getD i false=true := by cases v : b.getD i false <;> simp_all
          have anyB : rd b=true := by
            simpa [rd,hor,GateOp.eval,List.any_map,Function.comp_def] using
              (show ∃ j ∈ g.inputs, b.getD j false=true from ⟨i,hi,v⟩)
          simp [anyB] at h
        constructor
        · intro f r hr
          have h : ∃ i ∈ g.inputs, r∈w.getD i ∅ := by simpa [S,outSet,hor] using hr
          obtain ⟨i,hi,mem⟩ := h
          exact (inv i).1 (noB f i hi) mem
        · intro oa ob
          have h : ∃ i ∈ g.inputs, a.getD i false=true := by
            simpa [rd,hor,GateOp.eval,List.any_map,Function.comp_def] using oa
          obtain ⟨i,hi,va⟩ := h
          have hp := (inv i).2 va (noB ob i hi)
          simpa [S,outSet,hor] using (show ∃ j ∈ g.inputs, p∈w.getD j ∅ from ⟨i,hi,hp⟩)
    have next : Invariant p L (w++[S]) (a++[rd a]) (b++[rd b]) := by
      intro i
      simp only [at_append,ha,hb]
      by_cases lo : i < w.length
      · simpa [lo] using inv i
      by_cases eq : i=w.length
      · simpa [lo,eq] using hstep
      · simp [lo,eq]
    obtain ⟨s,hs,hp,hl⟩ := ih (fun k h => hm k (List.mem_cons_of_mem g h))
      (w++[S]) (a++[rd a]) (b++[rd b]) (by simp [ha]) (by simp [hb]) next on off
    exact ⟨s,List.mem_append_right _ hs,hp,hl⟩
end

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem port_geometry (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (T : Finset (Finset (Fin N))) (covers : ∀ p l, I p l →
      ∃ S∈T, p∈S ∧ ∀ r∈S, I r l) : N ≤ T.card := by
  classical
  let P := fun l : Fin N => Finset.univ.filter (fun p => I p l)
  let lines := fun S : Finset (Fin N) => Finset.univ.filter (fun l => S ⊆ P l)
  have hc (l : Fin N) : (P l).card=q+1 := by simpa [P,Fintype.card_subtype] using degree l
  have row := lines_through q N I hq order hc unique
  have val (S : Finset (Fin N)) : S.card*(lines S).card ≤ q+1 := by
    by_cases zero : S=∅
    · simp [zero]
    obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    by_cases one : S={p}
    · simpa [one,lines,P] using (row p).le
    have existsOther : ∃ r∈S, r≠p := by
      by_contra! no
      apply one
      ext a
      constructor
      · intro ha; simpa using no a ha
      · intro ha; have eq : a=p := by simpa using ha
        simpa [eq] using hp
    obtain ⟨r,hr,ne⟩ := existsOther
    have sub : ∀ l∈lines S, S⊆P l := fun l hl => (Finset.mem_filter.mp hl).2
    have oneLine : (lines S).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro l hl m hm
      apply (unique p r ne.symm).unique
      · exact ⟨(Finset.mem_filter.mp (sub l hl hp)).2,(Finset.mem_filter.mp (sub l hl hr)).2⟩
      · exact ⟨(Finset.mem_filter.mp (sub m hm hp)).2,(Finset.mem_filter.mp (sub m hm hr)).2⟩
    by_cases empty : lines S=∅
    · simp [empty]
    obtain ⟨l,hl⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have h1 := (Finset.card_le_card (sub l hl)).trans (hc l).le
    simpa using Nat.mul_le_mul h1 oneLine
  have pointBound (l : Fin N) :
      (P l).card ≤ ∑ S∈T, if l∈lines S then S.card else 0 := by
    let fam := T.filter fun S => l∈lines S
    have covered : P l ⊆ fam.biUnion id := by
      intro p hp
      obtain ⟨S,hS,hp',hsub⟩ := covers p l (Finset.mem_filter.mp hp).2
      refine Finset.mem_biUnion.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,?_⟩,hp'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub r hr⟩⟩
    have small := (Finset.card_le_card covered).trans Finset.card_biUnion_le
    simpa [fam,Finset.sum_filter] using small
  have tot : N*(q+1) ≤ T.card*(q+1) := calc
    N*(q+1) = ∑ l : Fin N, (P l).card := by simp [hc]
    _ ≤ ∑ l : Fin N, ∑ S∈T, if l∈lines S then S.card else 0 := Finset.sum_le_sum (fun l _ => pointBound l)
    _ = ∑ S∈T, S.card*(lines S).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      rw [←Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ ∑ _S∈T, (q+1) := Finset.sum_le_sum (fun S _ => val S)
    _ = T.card*(q+1) := by simp
  exact Nat.le_of_mul_le_mul_right tot (by omega)
private def labels (N : ℕ) : Fin (N+N) → Finset (Fin N) :=
  Fin.addCases (fun p => {p}) (fun _ => ∅)

private theorem physical_ports {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 1 ≤ q) (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (p l : Fin N) (flag : I p l) :
    ∃ S ∈ ports C.output C.gates (List.ofFn (labels N)), p∈S ∧ ∀ r∈S, I r l := by
  classical
  let X := outside I {l}
  let L := Finset.univ.filter fun r => I r l
  let a := input {p} {l}
  let b := input X {l}
  have hp : Hit I {p} {l} := ⟨p,by simp,l,by simp,flag⟩
  have act := true_of_incidence hm accept _ _ hp
  have quiet : circuitFun (N+N) C b=false := by
    have no := (sets_exact hm accept reject X {l} (by simpa using hq)).not.mpr (outside_miss I {l})
    cases ht : circuitFun (N+N) C b <;> simp_all [b]
  have mons : ∀ g ∈ C.gates, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm g hg
  have inv0 (v : Fin (N+N)) : (b v=false → labels N v⊆L) ∧
      (a v=true → b v=false → p∈labels N v) := by
    refine Fin.addCases (fun r => ?_) (fun t => ?_) v
    · have z : labels N (Fin.castAdd N r) = {r} := Fin.addCases_left ..
      simp [a,b,input_l,z,X,L,outside] <;> tauto
    · have z : labels N (Fin.natAdd N t) = ∅ := Fin.addCases_right ..
      dsimp only [a,b]
      rw [z,input_r,input_r]
      simp
  have inv : Invariant p L (List.ofFn (labels N)) (List.ofFn a) (List.ofFn b) := by
    intro i
    by_cases hi : i < N+N
    · have get {β : Type} (f : Fin (N+N) → β) (d : β) :
          (List.ofFn f).getD i d=f ⟨i,hi⟩ := by rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
      simpa only [get] using inv0 ⟨i,hi⟩
    · have h0 : N+N ≤ i := by omega
      have get {β : Type} (f : Fin (N+N) → β) (d : β) :
          (List.ofFn f).getD i d=d := List.getD_eq_default _ _ (by simpa using h0)
      simp only [get]
      simp
  obtain ⟨S,hs,hp',hsub⟩ := forward C.output p L C.gates mons
    (List.ofFn (labels N)) (List.ofFn a) (List.ofFn b) (by simp) (by simp) inv act quiet
  exact ⟨S,hs,hp',fun r hr => (Finset.mem_filter.mp (hsub hr)).2⟩

theorem plane_and_price (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C) :
    N ≤ 2*(C.gates.filter (fun g => !(g.op.eval [true,false]))).length+1 := by
  classical
  let T := ports C.output C.gates (List.ofFn (labels N))
  have cover (p l : Fin N) (flag : I p l) :
      ∃ S∈T.toFinset, p∈S ∧ ∀ r∈S, I r l := by
    simpa only [List.mem_toFinset] using physical_ports I C (by omega : 1≤q) hm accept reject p l flag
  have geom := port_geometry q N I hq order degree unique T.toFinset cover
  have sz := ports_length C.output C.gates (fun g hg => by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm g hg) (List.ofFn (labels N))
  exact geom.trans ((List.toFinset_card_le T).trans sz)

theorem close_deficit (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (gap : N*q ≤ 100*((C.gates.filter (fun g => g.op.eval [true,false])).length + N/2)) :
    N*q-100*(C.gates.filter (fun g => g.op.eval [true,false])).length ≤
      100*(C.gates.filter (fun g => !(g.op.eval [true,false]))).length := by
  have := plane_and_price q N I C hq order degree unique hm accept reject
  omega

end PEqualNP.Outside.L_meta_3310
