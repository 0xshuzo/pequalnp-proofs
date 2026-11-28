import PEqualNP.Defs

namespace Advice9059

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


def andOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def ands (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun j => andOp C.gates[j.val].op = true

def choices {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Finset (Fin C.gates.length) :=
  (ands C).filter fun j => val C x (C.gates[j.val].inputs.getD 0 0) = true

def Admits {n} (C : Circuit) (x : Fin n → Bool) (T : Finset (Fin C.gates.length)) : Prop :=
  ∀ j : Fin C.gates.length, C.gates[j.val].op = GateOp.and →
    val C x (n+j.val) = false →
    val C x (C.gates[j.val].inputs.getD (if j ∈ T then 1 else 0) 0) = false

def equalInputs {n} (C : Circuit) (x : Fin n → Bool) : Finset (Fin C.gates.length) :=
  (ands C).filter fun j => val C x (C.gates[j.val].inputs.getD 0 0) =
    val C x (C.gates[j.val].inputs.getD 1 0)

theorem advised_union {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j)
    (x y z : Fin n → Bool) (hz : ∀ i, z i = (x i || y i))
    (T : Finset (Fin C.gates.length)) (sx : Admits C x T) (sy : Admits C y T) :
    ∀ i, val C x i=false → val C y i=false → val C z i=false := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hx hy
    by_cases raw : i<n
    · let j : Fin n := ⟨i,raw⟩
      change val C z j.val = false
      rw [val_input, hz, ←val_input C x, ←val_input C y]
      simp [j,hx,hy]
    by_cases gone : n + C.gates.length ≤ i
    · exact val_beyond _ _ gone
    let k := i-n
    have hk : k<C.gates.length := by dsimp [k]; omega
    let j : Fin C.gates.length := ⟨k,hk⟩
    let g : Gate := C.gates[j.val]
    have hg : C.gates[k]?=some g := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
    obtain ⟨a,b,ins,ab,bk⟩ := hs k g hg
    have node : n+k=i := by dsimp [k]; omega
    have ai : a < i := by omega
    have bi : b < i := by omega
    have ev (t : Fin n → Bool) : val C t i=g.op.eval [val C t a,val C t b] := by
      have h := val_gate C t hg
      rw [node,ins] at h
      simpa [operand,ai,bi] using h
    rw [ev] at hx hy ⊢
    have hop := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with hand | hor
    · have applyAdvice (t : Fin n → Bool) (ht : Admits C t T)
          (ho : g.op.eval [val C t a,val C t b]=false) :
          val C t (if j ∈ T then b else a) = false := by
        have atGate : val C t (n+j.val)=false := by change val C t (n+k)=false; rw [node, ev]; exact ho
        have h := ht j hand atGate
        rw [show C.gates[j.val].inputs=[a,b] from ins] at h
        by_cases hj : j ∈ T <;> simpa [hj] using h
      have left := applyAdvice x sx hx
      have right := applyAdvice y sy hy
      rw [hand]
      by_cases hj : j ∈ T
      · simp only [hj,if_true] at left right
        simp [GateOp.eval, ih b bi left right]
      · simp only [hj,if_false] at left right
        simp [GateOp.eval, ih a ai left right]
    · rw [hor] at hx hy ⊢
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_false_iff] at hx hy ⊢
      exact ⟨ih a ai hx.1 hy.1,ih b bi hx.2 hy.2⟩

theorem input_union {N} (P Q L M : Finset (Fin N)) (i : Fin (N+N)) :
    input (P∪Q) (L∪M) i = (input P L i || input Q M i) := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [input_l,Finset.mem_union]
  · intro l
    rw [input_r,input_r,input_r]; simp [Finset.mem_union]

theorem free_advice {n} (C : Circuit)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j)
    (x : Fin n → Bool) (S : Finset (Fin C.gates.length)) (hS : S ⊆ equalInputs C x) :
    Admits C x ((choices C x \ equalInputs C x) ∪ S) := by
  classical
  intro j hand ho
  let g := C.gates[j.val]
  have hg : C.gates[j.val]?=some g := List.getElem?_eq_some_iff.mpr ⟨j.isLt,rfl⟩
  obtain ⟨a,b,ins,ab,bj⟩ := hs j.val g hg
  have ai : a < n+j.val := by omega
  have ev := val_gate C x hg
  change g.op=GateOp.and at hand
  rw [ins,hand] at ev
  have off : (val C x a && val C x b)=false := by
    simpa [operand,ai,bj,GateOp.eval] using ev.symm.trans ho
  have active : j ∈ ands C := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, show andOp g.op = true by rw [hand]; rfl⟩
  have i2 : C.gates[j.val].inputs=[a,b] := ins
  have ech : j ∈ equalInputs C x ↔ val C x a=val C x b := by
    simp [equalInputs, active,i2]
  have choice : j ∈ choices C x ↔ val C x a=true := by
    simp [choices,active,i2]
  rw [i2]
  by_cases eq : val C x a = val C x b
  · have za : val C x a=false := by cases ha : val C x a <;> simp_all
    have zb := eq.symm.trans za
    split <;> simpa [za,zb]
  · have nj := mt ech.mp eq
    have ns : j ∉ S := fun h => nj (hS h)
    cases ha : val C x a <;> cases hb : val C x b <;>
      simp_all [Finset.mem_union, Finset.mem_sdiff]

def adviceCube {n} (C : Circuit) (x : Fin n → Bool) : Finset (Finset (Fin C.gates.length)) :=
  (equalInputs C x).powerset.image fun S => (choices C x \ equalInputs C x) ∪ S

theorem advice_card {n} (C : Circuit) (x : Fin n → Bool) :
    (adviceCube C x).card = 2^(equalInputs C x).card := by
  classical
  rw [adviceCube, Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS T hT eq
  have s := Finset.mem_powerset.mp hS
  have t := Finset.mem_powerset.mp hT
  ext j
  by_cases hj : j ∈ equalInputs C x
  · have h := Finset.ext_iff.mp eq j
    simpa [hj] using h
  · exact ⟨fun h => False.elim (hj (s h)), fun h => False.elim (hj (t h))⟩

theorem advice_mass {N q} (C : Circuit) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g →
      ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j)
    (F : Finset (Finset (Fin N))) (small : ∀ L ∈ F, L.card ≤ q) :
    ∑ L ∈ F, 2^(equalInputs C (input (outside I L) L)).card ≤ 2^(ands C).card := by
  classical
  let row := fun L : Finset (Fin N) => input (outside I L) L
  let cubes := fun L => adviceCube C (row L)
  have valid (L : Finset (Fin N)) {T} (h : T ∈ cubes L) : Admits C (row L) T := by
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    exact free_advice C hs _ _ (Finset.mem_powerset.mp hS)
  have disj : (F : Set (Finset (Fin N))).PairwiseDisjoint cubes := by
    intro L hL M hM ne
    apply Finset.disjoint_left.mpr
    intro T tL tM
    obtain ⟨a,b,c⟩ := root_separates I hdeg unique hm accept reject (small L hL) (small M hM) ne
    have err := advised_union C hm hs _ _ _ (input_union (outside I L) (outside I M) L M)
      T (valid L tL) (valid M tM) C.output a b
    change circuitFun (N+N) C (input (outside I L ∪ outside I M) (L∪M))=false at err
    simp [c] at err
  have sub : F.biUnion cubes ⊆ (ands C).powerset := by
    intro T hT
    obtain ⟨L,_,hl⟩ := Finset.mem_biUnion.mp hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hl
    have he := Finset.mem_powerset.mp hS
    apply Finset.mem_powerset.mpr
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1
    · exact (Finset.mem_filter.mp (he hj)).1
  have bound := Finset.card_le_card sub
  rw [Finset.card_biUnion disj, Finset.card_powerset] at bound
  simpa only [cubes,row,advice_card] using bound

end Advice9059
