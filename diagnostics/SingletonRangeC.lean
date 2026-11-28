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


section
variable {α : Type} [DecidableEq α]
private noncomputable def onePair (U V : Finset α) : Option (α × α) := by
  classical
  exact if h : ∃ z : α × α, U={z.1} ∧ z.2∈V ∧ z.2≠z.1 then some h.choose else none

private theorem onePair_spec (U V : Finset α) (p r : α) (u : U={p}) (hr : r∈V) (ne : r≠p) :
    ∃ t∈V, t≠p ∧ onePair U V = some (p,t) := by
  classical
  have ex : ∃ z : α × α, U={z.1} ∧ z.2∈V ∧ z.2≠z.1 := ⟨(p,r),u,hr,ne⟩
  let z := ex.choose
  have hz : U={z.1} ∧ z.2∈V ∧ z.2≠z.1 := ex.choose_spec
  have ep : z.1=p := by
    have inc : z.1∈U := hz.1 ▸ Finset.mem_singleton_self _
    simpa [u] using inc
  refine ⟨z.2,hz.2.1,by simpa [←ep] using hz.2.2,?_⟩
  rw [onePair,dif_pos ex]
  apply congrArg some
  exact Prod.ext ep rfl

noncomputable def earned (w : List (Finset α)) (g : Gate) : List (α × α) :=
  if g.op = GateOp.or then (readSets w g).filterMap (fun U => onePair U (outSet w g)) else []

noncomputable def partners : List Gate → List (Finset α) → List (α × α)
  | [], _ => []
  | g::gs,w => earned w g ++ partners gs (w++[outSet w g])

private def Signs (E : List (α × α)) (U : Finset α) :=
    ∀ p∈U, U={p} ∨ ∃ r∈U, r≠p ∧ (p,r)∈E

private theorem signs_mono {E F : List (α × α)} (h : ∀ e∈E, e∈F) {U : Finset α}
    (s : Signs E U) : Signs F U := by
  intro p hp
  rcases s p hp with done | ⟨r,hr,ne,he⟩
  · exact Or.inl done
  · exact Or.inr ⟨r,hr,ne,h _ he⟩

private theorem signs_new (E : List (α × α)) (w : List (Finset α)) (g : Gate)
    (sw : ∀ U∈w, Signs E U) : Signs (E++earned w g) (outSet w g) := by
  classical
  intro p hp
  by_cases op : g.op=GateOp.or
  · have ins : ∃ i∈g.inputs, p∈w.getD i ∅ := by simpa [outSet,op] using hp
    obtain ⟨i,hi,pi⟩ := ins
    let U := w.getD i ∅
    have goodU : Signs E U := by
      by_cases h : i<w.length
      · rw [show U=w[i] by exact List.getD_eq_getElem _ _ h]
        exact sw _ (List.getElem_mem _)
      · have none : U=∅ := List.getD_eq_default _ _ (by omega)
        simp [none,Signs]
    have sub : U⊆outSet w g := by
      intro r hr
      simpa [outSet,op] using (show ∃ j∈g.inputs, r∈w.getD j ∅ from ⟨i,hi,hr⟩)
    rcases goodU p pi with lone | ⟨r,hr,ne,he⟩
    · by_cases done : outSet w g={p}
      · exact Or.inl done
      have extra : ∃ r∈outSet w g, r≠p := by
        by_contra! fail
        apply done
        ext r
        constructor
        · intro hr; simpa using fail r hr
        · intro hr
          have ep : r=p := by simpa using hr
          simpa [ep] using hp
      obtain ⟨r,hr,ne⟩ := extra
      obtain ⟨t,ht,nt,chosen⟩ := onePair_spec U (outSet w g) p r lone hr ne
      refine Or.inr ⟨t,ht,nt,List.mem_append_right _ ?_⟩
      simp only [earned,if_pos op,List.mem_filterMap]
      exact ⟨U,List.mem_map.mpr ⟨i,hi,rfl⟩,chosen⟩
    · exact Or.inr ⟨r,sub hr,ne,List.mem_append_left _ he⟩
  · simp [outSet,op] at hp

theorem partner_ports (o : ℕ) (gs : List Gate) (w : List (Finset α)) (E : List (α × α))
    (sw : ∀ U∈w, Signs E U) :
    ∀ U∈ports o gs w, Signs (E++partners gs w) U := by
  induction gs generalizing w E with
  | nil =>
    intro U hu
    have ep : U=w.getD o ∅ := by simpa [ports] using hu
    by_cases h : o<w.length
    · rw [ep,List.getD_eq_getElem _ _ h]
      simpa [partners] using sw w[o] (List.getElem_mem _)
    · rw [ep, List.getD_eq_default _ _ (by omega : w.length ≤ o)]; simp [Signs]
  | cons g gs ih =>
    let fresh := E++earned w g
    have enlarged (a) (h : a∈E) : a∈fresh := List.mem_append_left _ h
    have next : ∀ U∈ w++[outSet w g], Signs fresh U := by
      intro U h
      rcases List.mem_append.mp h with old | new
      · exact signs_mono enlarged (sw _ old)
      · have eq : U=outSet w g := by simpa using new
        exact eq ▸ signs_new E w g sw
    intro U h
    rcases List.mem_append.mp h with first | rest
    · by_cases hor : g.op=GateOp.or
      · simp [hor] at first
      have hmem : U∈readSets w g := by simpa [hor] using first
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
      by_cases j : i<w.length
      · rw [List.getD_eq_getElem _ _ j]
        exact signs_mono (fun e he => List.mem_append_left _ he) (sw w[i] (List.getElem_mem _))
      · rw [List.getD_eq_default _ _ (by omega : w.length ≤ i)]; simp [Signs]
    · simpa [fresh,partners,List.append_assoc] using ih (w++[outSet w g]) fresh next U rest

theorem partners_length (gs : List Gate) (w : List (Finset α))
    (hm : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) :
    (partners gs w).length ≤ 2*(gs.filter (fun g => g.op.eval [true,false])).length := by
  induction gs generalizing w with
  | nil => simp [partners]
  | cons g gs ih =>
    have tail := ih (w++[outSet w g]) (fun k h => hm k (List.mem_cons_of_mem g h))
    obtain ⟨op,ar⟩ := hm g (by simp)
    have le : ((readSets w g).filterMap (fun U => onePair U (outSet w g))).length ≤ g.inputs.length :=
      (List.length_filterMap_le _ _).trans (by simp [readSets])
    rcases op with h | h <;> simp [partners,earned,h,GateOp.eval] at * <;> omega


end
section
variable {α : Type} [DecidableEq α] [Fintype α]

noncomputable def guardSet (E : List (α × α)) (p : α) : Finset α :=
  ((E.toFinset.filter fun z => z.1=p ∧ z.2≠p).image Prod.snd)

theorem guard_mass (E : List (α × α)) : ∑ p : α, (guardSet E p).card ≤ E.length := by
  classical
  have localBound (p : α) : (guardSet E p).card ≤ (E.toFinset.filter (fun z => z.1=p)).card := by
    apply Finset.card_image_le.trans
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.1⟩
  calc
    _ ≤ ∑ p : α, (E.toFinset.filter (fun z => z.1=p)).card := Finset.sum_le_sum (fun p _ => localBound p)
    _ = E.toFinset.card := (Finset.card_eq_sum_card_fiberwise (s:=E.toFinset) (t:=Finset.univ)
          (f:=Prod.fst) (fun _ _ => Finset.mem_univ _)).symm
    _ ≤ E.length := List.toFinset_card_le _

theorem guard_hits {E : List (α × α)} {U : Finset α} (sig : Signs E U) (p : α) (hp : p∈U) :
    U={p} ∨ ∃ r∈U, r∈guardSet E p := by
  rcases sig p hp with single | ⟨r,hr,ne,he⟩
  · exact Or.inl single
  · refine Or.inr ⟨r,hr,Finset.mem_image.mpr ⟨(p,r),?_,rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨by simpa using he,rfl,ne⟩

theorem guard_omits (E : List (α × α)) (p : α) : p∉guardSet E p := by
  classical
  intro hp
  obtain ⟨z,hz,zp⟩ := Finset.mem_image.mp hp
  exact (Finset.mem_filter.mp hz).2.2 zp
end

theorem physical_guards (N : ℕ) (C : Circuit) (hm : Monotone2 C) :
    ∃ G : Fin N → Finset (Fin N), (∀ p, p∉G p) ∧
      (∑ p, (G p).card) ≤ 2*(C.gates.filter (fun g => g.op.eval [true,false])).length ∧
      ∀ U∈ports C.output C.gates (List.ofFn (labels N)), ∀ p∈U, U={p} ∨ ∃ r∈U, r∈G p := by
  classical
  let w := List.ofFn (labels N)
  let E := partners C.gates w
  have sw : ∀ U∈w, Signs [] U := by
    intro U h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · rw [show labels N (Fin.castAdd N p)={p} from Fin.addCases_left ..]
      intro r hr
      have eq : r=p := by simpa using hr
      exact Or.inl (by rw [eq])
    · rw [show labels N (Fin.natAdd N l)=∅ from Fin.addCases_right ..]
      simp [Signs]
  refine ⟨guardSet E,guard_omits E,(guard_mass E).trans ?_,?_⟩
  · apply partners_length
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm g hg
  · intro U hU p hp
    have sig := partner_ports C.output C.gates w [] sw U hU
    apply guard_hits (E:=E) _ p hp
    simpa [E] using sig

theorem strict_sparse_guards (N q : ℕ) (C : Circuit) (hm : Monotone2 C)
    (h : 100*(C.gates.filter (fun g => g.op.eval [true,false])).length < N*q) :
    ∃ G : Fin N → Finset (Fin N), (∀ p, p∉G p) ∧
      50*(∑ p, (G p).card)<N*q ∧
      ∀ U∈ports C.output C.gates (List.ofFn (labels N)), ∀ p∈U, U={p} ∨ ∃ r∈U, r∈G p := by
  obtain ⟨G,avoid,budget,hit⟩ := physical_guards N C hm
  exact ⟨G,avoid,by omega,hit⟩

theorem missing_point_price (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C) :
    let T := ports C.output C.gates (List.ofFn (labels N))
    let bad := Finset.univ.filter (fun p : Fin N => ({p} : Finset (Fin N))∉T)
    bad.card*(q+1) ≤ 2*(C.gates.filter (fun g => g.op.eval [true,false])).length := by
  classical
  dsimp only
  let T := ports C.output C.gates (List.ofFn (labels N))
  let bad := Finset.univ.filter (fun p : Fin N => ({p} : Finset (Fin N))∉T)
  obtain ⟨G,avoid,mass,all⟩ := physical_guards N C hm
  have missing (p : Fin N) (hn : p∈bad) : q+1≤(G p).card := by
    let name (r : Fin N) := if e : p=r then (⟨0,(by omega : 0<N)⟩ : Fin N)
      else (unique p r e).choose
    let pencil := Finset.univ.filter (fun l => I p l)
    have sub : pencil ⊆ (G p).image name := by
      intro l hl
      obtain ⟨U,hu,hp,hsub⟩ := physical_ports I C (by omega : 1≤q) hm accept reject p l (Finset.mem_filter.mp hl).2
      rcases all U hu p hp with eq|⟨r,hr,hg⟩
      · exact ((Finset.mem_filter.mp hn).2 (eq ▸ hu)).elim
      · have ne : p≠r := by rintro rfl; exact avoid p hg
        apply Finset.mem_image.mpr
        refine ⟨r,hg,?_⟩
        simp only [name,dif_neg ne]
        exact (unique p r ne).unique (unique p r ne).choose_spec.1
          ⟨(Finset.mem_filter.mp hl).2,hsub r hr⟩
    have col (l : Fin N) : (Finset.univ.filter (fun r => I r l)).card=q+1 := by
      simpa [Fintype.card_subtype] using degree l
    have size : pencil.card=q+1 := lines_through q N I hq order col unique p
    rw [←size]
    exact (Finset.card_le_card sub).trans Finset.card_image_le
  change bad.card*(q+1) ≤ _
  calc
    bad.card*(q+1) = ∑ _p∈bad, (q+1) := by simp
    _ ≤ ∑ p∈bad, (G p).card := Finset.sum_le_sum (fun p h => missing p h)
    _ ≤ ∑ p : Fin N, (G p).card := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (by intros; omega)
    _ ≤ _ := mass

theorem missing_point_case (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (strict : 100*(C.gates.filter (fun g => g.op.eval [true,false])).length < N*q) :
    let T := ports C.output C.gates (List.ofFn (labels N))
    50*(Finset.univ.filter (fun p : Fin N => ({p} : Finset (Fin N))∉T)).card < N := by
  classical
  have bound := missing_point_price q N I C hq order degree unique hm accept reject
  dsimp only at bound ⊢
  by_contra! nope
  have mult := Nat.mul_le_mul_right q nope
  nlinarith only [bound,strict,mult]

end PEqualNP.Outside.L_meta_3310
