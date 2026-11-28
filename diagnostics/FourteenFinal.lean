import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17132

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

lemma frontier {β : Type} [Fintype β] [DecidableEq β] (n m : Nat) (S : Nat → Finset β) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<n, cold w → (S w).card≤1)
    (step : ∀ j < m, cold (n+j) → ∃ K : Finset Nat,
      (∀ i∈K, i<n+j ∧ cold i) ∧ S (n+j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0)) :
    ∀ q ≤ m, ∀ F : Finset Nat, (∀ i∈F, i<n+q ∧ cold i) →
      (F.biUnion S).card≤ F.card + ((Finset.range q).filter charged).card := by
  classical
  intro q
  induction q with
  | zero =>
    intro _ F good
    apply Finset.card_biUnion_le.trans
    have bound := Finset.sum_le_sum (fun w (h : w∈F) => raw w (by simpa using (good w h).1) (good w h).2)
    simpa using bound
  | succ q ih =>
    intro lim F good
    have lt := Nat.lt_of_succ_le lim
    have lim' := Nat.le_of_lt lt
    have cf : ((Finset.range (q+1)).filter charged).card =
        ((Finset.range q).filter charged).card + (if charged q then 1 else 0) := by
      have re : Finset.range (q+1)=insert q (Finset.range q) := by ext n; simp; omega
      rw [re,Finset.filter_insert]
      split_ifs with h <;> simp [h]
    rw [cf]
    by_cases h : (n+q)∈F
    · obtain ⟨K,prior,sub,kc⟩ := step q lt (good _ h).2
      let P := F.erase (n+q) ∪ K
      have hp : ∀ i∈P, i<n+q ∧ cold i := by
        intro i hi
        rcases Finset.mem_union.mp hi with he|hk
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp he
          have g := good i mem
          exact ⟨by  omega,g.2⟩
        · exact prior i hk
      have hs : F.biUnion S ⊆ P.biUnion S := by
        intro u hu
        obtain ⟨i,hi,ui⟩ := Finset.mem_biUnion.mp hu
        by_cases e : i=(n+q)
        · subst i
          obtain ⟨k,hk,uk⟩ := Finset.mem_biUnion.mp (sub ui)
          exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,uk⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩),ui⟩
      have e := Finset.card_erase_add_one h
      have upper : P.card≤(F.erase (n+q)).card+K.card := Finset.card_union_le _ _
      have bd := (Finset.card_le_card hs).trans (ih lim' P hp)
      omega
    · have bd := ih lim' F (fun i hi => ⟨by
          have ne : i≠(n+q) := fun e => h (e ▸ hi)
          have g := (good i hi).1
          change i<n+q
          omega,(good i hi).2⟩)
      omega

theorem coldCount {n : Nat} {β : Type} [Fintype β] [DecidableEq β]
    (C : Circuit) (hm : Monotone2 C) (xs : β → Fin n → Bool) (y : Fin n → Bool)
    (raw : ∀ i : Fin n, y i=false → (Finset.univ.filter (fun b => xs b i=true)).card≤1)
    {o : Nat} (coldOut : val C y o=false) (rangeOut : o<n+C.gates.length) :
    let S := fun w => Finset.univ.filter (fun b => val C (xs b) w=true)
    let charged := fun j => (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true ∧
      val C y (n+j)=false ∧ 2≤(S (n+j)).card
    (S o).card ≤ 1+((Finset.range C.gates.length).filter charged).card := by
  classical
  dsimp only
  let S := fun w => Finset.univ.filter (fun b => val C (xs b) w=true)
  let cold := fun w => val C y w=false
  let charged := fun j => (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true ∧
      cold (n+j) ∧ 2≤(S (n+j)).card
  have inputs (w : Nat) (hw : w<n) (off : cold w) : (S w).card≤1 := by
    let i : Fin n := ⟨w,hw⟩
    change val C y i.val=false at off
    rw [val_input] at off
    have eq : S w=Finset.univ.filter (fun b => xs b i=true) := by
      ext b
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      change (val C (xs b) i.val = true ↔ xs b i=true)
      rw [val_input]
    rw [eq]
    exact raw i off
  have steps (j : Nat) (hj : j<C.gates.length) (off : cold (n+j)) :
      ∃ K : Finset Nat, (∀ i∈K, i<n+j ∧ cold i) ∧
        S (n+j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0) := by
    let g := C.gates[j]
    have hg : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    obtain ⟨op,ar⟩ := hm g (List.mem_of_getElem? hg)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    have eq : (C.gates.getD j ⟨.or,[]⟩)=g := List.getD_eq_getElem _ _ hj
    have ev := val_gate C y hg
    change val C y (n+j)=false at off
    have no (empty : S (n+j)=∅) : ∃ K : Finset Nat, (∀ i∈K, i<n+j ∧ cold i) ∧
        S (n+j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0) := by
      exact ⟨∅,by simp,by simp [empty],by simp⟩
    by_cases non : (S (n+j)).Nonempty
    swap
    · exact no (Finset.not_nonempty_iff_eq_empty.mp non)
    obtain ⟨b,hb⟩ := non
    have pos (t) (ht : t∈S (n+j)) := (Finset.mem_filter.mp ht).2
    have one (i : Nat) (hi : i<n+j) (hc : cold i) (hs : S (n+j)⊆S i) :
        ∃ K : Finset Nat, (∀ i∈K, i<n+j ∧ cold i) ∧
        S (n+j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0) :=
      ⟨{i},by simpa using And.intro hi hc,by simpa using hs,by simp⟩
    rcases op with hand|hor
    · have yes (t) (ht : t∈S (n+j)) (i) (hi : i∈g.inputs) : operand C (xs t) (n+j) i=true := by
        have on := pos t ht
        rw [val_gate C (xs t) hg] at on
        exact (show ∀ i∈g.inputs, operand C (xs t) (n+j) i=true from by
            simpa only [hand,GateOp.eval,List.all_map,Function.comp_apply,id,List.all_eq_true] using on) i hi
      have zero : ∃ i∈g.inputs, operand C y (n+j) i=false := by
        by_contra! h
        have on : val C y (n+j)=true := by
          rw [ev]
          simp only [hand,GateOp.eval,List.all_map,Function.comp_apply,id,List.all_eq_true]
          exact fun i hi => Bool.eq_true_of_not_eq_false (h i hi)
        exact Bool.noConfusion (on.symm.trans off)
      obtain ⟨i,hi,hz⟩ := zero
      have lt : i<n+j := by
        by_contra e
        simpa [operand,e] using yes b hb i hi
      apply one i lt (by simpa [cold,operand,lt] using hz)
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [operand,lt] using yes t ht i hi⟩
    · let K := g.inputs.toFinset.filter (fun i => i<n+j)
      have prior : ∀ i∈K, i<n+j ∧ cold i := by
        intro i hi
        obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hi
        refine ⟨lt,?_⟩
        apply Bool.eq_false_iff.mpr
        intro on
        have on' : val C y (n+j)=true := by
          rw [ev]
          simp only [hor,GateOp.eval,List.any_map,Function.comp_apply,id,List.any_eq_true]
          exact ⟨i,List.mem_toFinset.mp mem,by simpa [operand,lt] using on⟩
        exact Bool.noConfusion (on'.symm.trans off)
      have cover : S (n+j) ⊆ K.biUnion S := by
        intro t ht
        have on := pos t ht
        rw [val_gate C (xs t) hg] at on
        simp only [hor,GateOp.eval,List.any_map,Function.comp_apply,id,List.any_eq_true] at on
        obtain ⟨i,hi,act⟩ := on
        have lt : i<n+j := by
          by_contra e
          simpa [operand,e] using act
        refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi,lt⟩,?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [operand,lt] using act⟩
      by_cases cost : 2≤(S (n+j)).card
      · have paid : charged j := ⟨by rw [eq,hor]; rfl,off,cost⟩
        have kc : K.card≤g.inputs.length := (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
        exact ⟨K,prior,cover,by rw [if_pos paid]; omega⟩
      · obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp (cover hb)
        apply one i (prior i hi).1 (prior i hi).2
        intro t ht
        have e : t=b := Finset.card_le_one.mp (by omega : (S (n+j)).card≤1) _ ht _ hb
        exact e.symm ▸ hit
  have bd := frontier n C.gates.length S cold charged inputs steps C.gates.length le_rfl {o}
    (by simpa using And.intro rangeOut coldOut)
  simpa [S,charged,cold] using bd


def flagSig {N : Nat} (C : Circuit) (l : Fin N) (w : Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun p => val C (input {p} {l}) w=true)

def lineCharge {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (l : Fin N) (j : Nat) : Prop :=
  (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true ∧
  val C (input (outside I {l}) {l}) (N+N+j)=false ∧ 2≤(flagSig C l (N+N+j)).card

open Classical in
theorem perColumn {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C) (l : Fin N) :
    q ≤ ((Finset.range C.gates.length).filter (lineCharge I C l)).card := by
  classical
  let y := input (outside I {l}) {l}
  let xs := fun p : Fin N => input {p} {l}
  have cold : val C y C.output=false := by
    have h := (sets_exact hm accept reject (outside I {l}) {l} (by simpa using hq)).not.mpr
      (outside_miss I {l})
    exact Bool.eq_false_iff.mpr h
  have root : flagSig C l C.output = Finset.univ.filter (fun p => I p l) := by
    ext p
    simp only [flagSig,Finset.mem_filter,Finset.mem_univ,true_and]
    change circuitFun (N+N) C (input {p} {l}) = true ↔ I p l
    rw [sets_exact hm accept reject _ _ (by simpa using hq)]
    simp [Hit]
  have size : (flagSig C l C.output).card = q+1 := by
    rw [root]
    simpa only [Fintype.card_subtype] using degree l
  have within : C.output < N+N+C.gates.length := by
    by_contra! out
    have emp : flagSig C l C.output=∅ := by
      ext p
      simp [flagSig,val_beyond C _ out]
    rw [emp,Finset.card_empty] at size
    omega
  have raw : ∀ i : Fin (N+N), y i=false → (Finset.univ.filter (fun p => xs p i=true)).card≤1 := by
    intro i
    refine Fin.addCases (fun p off => ?_) (fun r off => ?_) i
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      have h (s : Fin N) (hs : xs s (Fin.castAdd N p)=true) : p=s := by
        simpa [xs,input_l] using hs
      exact (h a (Finset.mem_filter.mp ha).2).symm.trans (h b (Finset.mem_filter.mp hb).2)
    · have off' : r≠l := by
        change input (outside I {l}) {l} (Fin.natAdd N r)=false at off
        rw [input_r] at off
        simpa using off
      have hz (p : Fin N) : xs p (Fin.natAdd N r)=false := by
        change input {p} {l} (Fin.natAdd N r)=false
        rw [input_r]
        simp [off']
      simp only [hz,Bool.false_eq_true,Finset.filter_false,Finset.card_empty,Nat.zero_le]
  have bd := coldCount C hm xs y raw cold within
  dsimp only at bd
  let T := (Finset.range C.gates.length).filter (lineCharge I C l)
  have lift {F : Finset (Fin N)} {J : Finset Nat} (h : F.card ≤ 1+J.card)
      (e : F=flagSig C l C.output) (sub : J⊆T) : q≤T.card := by
    have lt := Finset.card_le_card sub
    rw [e,size] at h
    omega
  apply lift bd
  · ext p
    simp only [flagSig,Finset.mem_filter,Finset.mem_univ,true_and,xs]
  · intro j hj
    obtain ⟨lim,paid,quiet,hits⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨lim,paid,quiet,?_⟩
    have eqj : (Finset.univ.filter (fun p => val C (xs p) (N+N+j)=true)) =
        flagSig C l (N+N+j) := by
      ext p
      simp only [flagSig,Finset.mem_filter,Finset.mem_univ,true_and,xs]
    rw [←eqj]
    exact hits

noncomputable def multiplicity {N} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (j : Nat) : Nat := by
  classical
  exact (Finset.univ.filter (fun l => lineCharge I C l j)).card

theorem sumCharges {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C) :
    N*q ≤ ∑j∈Finset.range C.gates.length, multiplicity I C j := by
  classical
  have eq {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
      (s.filter p).card=∑ x∈s, if p x then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  calc
    N*q = ∑ _ : Fin N, q := by simp
    _ ≤ ∑ l : Fin N, ((Finset.range C.gates.length).filter (lineCharge I C l)).card :=
      Finset.sum_le_sum (fun l _ => perColumn I C hq degree hm accept reject l)
    _ = ∑ l : Fin N, ∑ j ∈ Finset.range C.gates.length, if lineCharge I C l j then 1 else 0 :=
      Finset.sum_congr rfl (fun l _ => eq _ _)
    _ = ∑ j ∈ Finset.range C.gates.length, ∑ l : Fin N, if lineCharge I C l j then 1 else 0 :=
      Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (eq _ _).symm)

theorem rectLineCap {N k : Nat} (I : Fin N → Fin N → Prop)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (L : Finset (Fin N)) (P Y : Fin k → Finset (Fin N))
    (safe : ∀ i, ∀ p∈P i, ∀ l∈L, l∈Y i → I p l)
    (wide : ∀ l∈L, ∃ p r : Fin N, p≠r ∧ (∃ i, p∈P i ∧ l∈Y i) ∧ (∃ j, r∈P j ∧ l∈Y j)) :
    L.card ≤ (Finset.univ.filter (fun z : Fin k × Fin k => z.1≤z.2)).card := by
  classical
  let ok (l : Fin N) (z : Fin k × Fin k) :=
    z.1 ≤ z.2 ∧ l∈Y z.1 ∧ l∈Y z.2 ∧ ∃ p∈P z.1, ∃ r∈P z.2, p≠r
  by_cases h0 : L.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp h0]
    simp
  obtain ⟨l0,h0⟩ := h0
  obtain ⟨p0,r0,ne0,⟨i0,_,_⟩,⟨j0,_,_⟩⟩ := wide l0 h0
  letI : Nonempty (Fin k × Fin k) := ⟨(i0,j0)⟩
  have tags (l : Fin N) (h : l∈L) : ∃ z, ok l z := by
    obtain ⟨p,r,ne,⟨i,pi,li⟩,⟨j,rj,lj⟩⟩ := wide l h
    rcases le_total i j with le|le
    · exact ⟨(i,j),le,li,lj,p,pi,r,rj,ne⟩
    · exact ⟨(j,i),le,lj,li,r,rj,p,pi,ne.symm⟩
  choose! f hf using tags
  apply Finset.card_le_card_of_injOn f (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hf l hl).1⟩)
  intro l hl m hm e
  obtain ⟨_,li,lj,p,pp,r,rr,ne⟩ := hf l hl
  have mq : ok m (f l) := e.symm ▸ hf m hm
  exact (uniq p r ne).unique
    ⟨safe _ _ pp l hl li,safe _ _ rr l hl lj⟩
    ⟨safe _ _ pp m hm mq.2.1,safe _ _ rr m hm mq.2.2.1⟩

theorem thirteenCap (L : Finset (Fin N)) (I : Fin N → Fin N → Prop)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (P Y : Fin 13 → Finset (Fin N))
    (safe : ∀ i, ∀ p∈P i, ∀ l∈L, l∈Y i → I p l)
    (wide : ∀ l∈L, ∃ p r : Fin N, p≠r ∧ (∃ i, p∈P i ∧ l∈Y i) ∧ (∃ j, r∈P j ∧ l∈Y j)) :
    L.card ≤ 91 := by
  exact (rectLineCap I uniq L P Y safe wide).trans_eq (by decide +kernel)
open Classical in
theorem safeFlag {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) {l : Fin N} {j : Nat} (paid : lineCharge I C l j) :
    ∀ p ∈ flagSig C l (N+N+j), I p l := by
  intro p hp
  by_contra off
  have cmp : ({p}:Finset (Fin N)) ⊆ outside I {l} := by
    intro a ha
    obtain rfl := Finset.mem_singleton.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using off⟩
  have on := wire_mono (C:=C) hm cmp (show ({l}:Finset (Fin N)) ⊆ {l} from fun _ h => h)
    (N+N+j) (Finset.mem_filter.mp hp).2
  exact Bool.noConfusion (on.symm.trans paid.2.1)

theorem smallRank {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) (j : Nat)
    (P Y : Fin 13 → Finset (Fin N))
    (rep : ∀ l, lineCharge I C l j → ∀ p, p ∈ flagSig C l (N+N+j) ↔ ∃ i, p∈P i ∧ l∈Y i) :
    multiplicity I C j ≤ 91 := by
  classical
  apply thirteenCap _ I uniq P Y
  · intro i p hp l hl hy
    have ch : lineCharge I C l j := (Finset.mem_filter.mp hl).2
    exact safeFlag I C hm ch p ((rep l ch p).2 ⟨i,hp,hy⟩)
  · intro l hl
    have ch : lineCharge I C l j := (Finset.mem_filter.mp hl).2
    obtain ⟨p,hp,r,hr,ne⟩ := Finset.one_lt_card.mp (show 1 < (flagSig C l (N+N+j)).card from ch.2.2)
    exact ⟨p,r,ne,(rep l ch p).1 hp,(rep l ch r).1 hr⟩

theorem rangeTally {α : Type} (d : α) (p : α → Bool) (L : List α) :
    (∑ j∈Finset.range L.length, if p (L.getD j d)=true then 1 else 0)=(L.filter p).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    change (∑ j∈Finset.range L.length, if p (L.getD j d)=true then 1 else 0) +
      (if p a=true then 1 else 0) = ((a::L).filter p).length
    rw [ih]
    cases h : p a <;> simp [List.filter_cons,h]

theorem wideOR {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (strict : 100*(C.gates.filter (fun g => g.op.eval [true,false])).length < N*q) :
    ∃ j<C.gates.length, (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true ∧
       100<multiplicity I C j := by
  classical
  let op := fun j => (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]
  by_contra! h
  have bound (j : Nat) (lt : j<C.gates.length) :
      multiplicity I C j ≤ 100*(if op j=true then 1 else 0) := by
    by_cases paid : op j=true
    · simpa [paid] using h j lt paid
    · have nil : (Finset.univ.filter (fun l => lineCharge I C l j))=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact paid ((Finset.mem_filter.mp hl).2.1)
      rw [multiplicity,nil,Finset.card_empty]
      exact Nat.zero_le _
  have cap := (sumCharges I C hq degree hm accept reject).trans (Finset.sum_le_sum (fun j h => bound j (Finset.mem_range.mp h)))
  rw [←Finset.mul_sum] at cap
  change N*q ≤ 100*(∑ j∈Finset.range C.gates.length, if (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true then 1 else 0) at cap
  rw [rangeTally (⟨.or,[]⟩:Gate) (fun g => g.op.eval [true,false]) C.gates] at cap
  omega

theorem fourteenRequired {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (strict : 100*(C.gates.filter (fun g => g.op.eval [true,false])).length < N*q) :
    ∃ j<C.gates.length, (C.gates.getD j ⟨.or,[]⟩).op.eval [true,false]=true ∧
      100<multiplicity I C j ∧
      ¬ ∃ P Y : Fin 13 → Finset (Fin N), ∀ l, lineCharge I C l j → ∀ p,
        p∈flagSig C l (N+N+j) ↔ ∃ i, p∈P i ∧ l∈Y i := by
  obtain ⟨j,lt,paid,large⟩ := wideOR I C hq degree hm accept reject strict
  refine ⟨j,lt,paid,large,?_⟩
  rintro ⟨P,Y,rep⟩
  have cap := smallRank I C hm uniq j P Y rep
  omega

end PEqualNP.Outside.L_meta_17132
