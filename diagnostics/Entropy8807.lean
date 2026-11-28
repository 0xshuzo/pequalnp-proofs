import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8807.Entropy

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

theorem union_false {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<n+j ∧ b<n+j)
    (x y z : Fin n → Bool) (hz : ∀ i, z i = (x i || y i))
    (same : choices C x = choices C y) :
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
    · have eq : val C x a = val C y a := by
        have h : j ∈ choices C x ↔ j ∈ choices C y := by rw [same]
        have h' : val C x a=true ↔ val C y a=true := by
          have active : j∈ands C := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,show andOp g.op=true by rw [hand]; rfl⟩
          simp only [choices,Finset.mem_filter,active,true_and] at h
          rw [show C.gates[j.val].inputs=[a,b] from ins] at h
          exact h
        cases ax : val C x a <;> cases ay : val C y a <;> simp_all
      rw [hand] at hx hy ⊢
      simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] at hx hy ⊢
      cases ax : val C x a with
      | false =>
        have ay : val C y a=false := eq.symm.trans ax
        simp [ih a ai ax ay]
      | true =>
        have ay : val C y a=true := eq.symm.trans ax
        have bx : val C x b=false := by simpa [ax] using hx
        have by' : val C y b=false := by simpa [ay] using hy
        simp [ih b bi bx by']
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

theorem many_and_choices {N q} (C : Circuit) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g →
      ∃ a b : ℕ, g.inputs=[a,b] ∧ a<N+N+j ∧ b<N+N+j) :
    (Finset.univ.powersetCard q : Finset (Finset (Fin N))).card ≤ 2^(ands C).card := by
  classical
  let tag := fun L : Finset (Fin N) => choices C (input (outside I L) L)
  rw [←Finset.card_powerset]
  apply Finset.card_le_card_of_injOn tag
  · intro L _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro L hL M hM eq
    by_contra ne
    have ls := (Finset.mem_powersetCard.mp hL).2.le
    have ms := (Finset.mem_powersetCard.mp hM).2.le
    obtain ⟨a,b,c⟩ := root_separates I hdeg unique hm accept reject ls ms ne
    have err := union_false C hm hs _ _ _
      (input_union (outside I L) (outside I M) L M) eq C.output a b
    change circuitFun (N+N) C (input (outside I L ∪ outside I M) (L∪M))=false at err
    simp [c] at err

theorem separate {N} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro eq
  have e := congrArg Fin.val eq
  have := p.isLt
  change p.val=N+l.val at e
  omega
open Finset PEqualNP.TopForm PEqualNP.GenericRejection
theorem family_encode {N q b : Nat} (cap : q*b≤N) :
    b^q ≤ (univ.powersetCard q : Finset (Finset (Fin N))).card := by
  classical
  let embed : Fin q × Fin b ↪ Fin N :=
    ⟨fun z => Fin.castLE cap (finProdFinEquiv z),fun x y h =>
      finProdFinEquiv.injective (Fin.ext (congrArg Fin.val h))⟩
  let graph (f : Fin q → Fin b) := univ.image (fun i => embed (i,f i))
  have image (f : Fin q → Fin b) : (graph f).card=q := by
    have inj : Function.Injective (fun i => embed (i,f i)) :=
      fun i j eq => congrArg Prod.fst (embed.injective eq)
    simp [graph,card_image_of_injective _ inj]
  let tag (f : Fin q → Fin b) : ↑(univ.powersetCard q : Finset (Finset (Fin N))) :=
    ⟨graph f,mem_powersetCard.mpr ⟨subset_univ _,image f⟩⟩
  have inj : Function.Injective tag := by
    intro f g h
    have sets : graph f=graph g := congrArg Subtype.val h
    funext i
    have hi : embed (i,f i)∈graph f := mem_image_of_mem _ (mem_univ i)
    rw [sets] at hi
    obtain ⟨j,_,eq⟩ := mem_image.mp hi
    have ee := embed.injective eq
    have ji : j=i := congrArg Prod.fst ee
    subst j
    exact (congrArg Prod.snd ee).symm
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective tag inj

theorem and_bit_floor {N q : Nat} (C : Circuit) (S : Fin N → Finset (Fin N))
    (col : ∀ l,(S l).card=q+1) (uniq : ∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (e : Nat) (cap : q*2^e≤N) : e*q ≤ (ands C).card := by
  classical
  let I := fun p l : Fin N => p ∈ S l
  have deg (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa [I,Fintype.card_subtype] using col l
  have hit (p l : Fin N) (h : I p l) : circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true := by
    let x : Fin (N+N) → Bool := Fin.addCases (fun a => decide (a∈({p}:Finset (Fin N)))) (fun b => decide (b∈({l}:Finset (Fin N))))
    have raw : List.ofFn x = incidenceInput {p} {l} := List.ofFn_fin_append _ _
    have fn : x = (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · change x (Fin.castAdd N a) = _
        rw [show x (Fin.castAdd N a) = decide (a∈({p}:Finset (Fin N))) from Fin.addCases_left ..]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,separate a l,or_false]
      · change x (Fin.natAdd N b) = _
        rw [show x (Fin.natAdd N b) = decide (b∈({l}:Finset (Fin N))) from Fin.addCases_right ..]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (separate p b),false_or]
    rw [←fn]
    change C.eval (List.ofFn x)=true
    rw [raw]
    exact pos l p h
  have off (x : Fin (N+N) → Bool) (lim : Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q)
      (none : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) : circuitFun (N+N) C x=false := by
    let X := Finset.univ.filter (fun p => x (Fin.castAdd N p)=true)
    let Y := Finset.univ.filter (fun l => x (Fin.natAdd N l)=true)
    have eq : x = Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y)) := by
      funext i
      refine Fin.addCases (fun p => ?_) (fun l => ?_) i
      · rw [Fin.addCases_left]; simp [X]
      · rw [Fin.addCases_right]; simp [Y]
    have raw : List.ofFn x = incidenceInput X Y := by rw [eq]; exact List.ofFn_fin_append _ _
    change C.eval (List.ofFn x)=false
    rw [raw]
    apply sound X Y
    · simpa [Y,Fintype.card_subtype] using lim
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact none ⟨p,l,hp,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have shape (j : Nat) (g : Gate) (hg : C.gates[j]?=some g) :
      ∃ a b : Nat, g.inputs=[a,b] ∧ a<N+N+j ∧ b<N+N+j := by
    obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
    have gg : PEqualNP.MetaComplexity.NestedCover.gateAt C j=g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hg]
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hg))
    have pre := ao.2.1 j hj
    rw [gg,ab] at pre
    exact ⟨a,b,ab,pre a (by simp),pre b (by simp)⟩
  have ub := many_and_choices C I deg uniq mon hit off shape
  have lo := (family_encode cap).trans ub
  rw [←pow_mul] at lo
  by_contra! bad
  have err := Nat.pow_lt_pow_right (by decide : 1<2) bad
  omega
end PEqualNP.Outside.L_meta_8807.Entropy
