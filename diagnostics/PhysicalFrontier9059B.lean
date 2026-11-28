import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9059.Pencil

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

theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega


def Points {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (p l : Fin N) : Finset (Fin N) :=
  (Finset.univ.filter (fun u => I u l)).erase p
def Lines {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (p l : Fin N) : Finset (Fin N) :=
  (Finset.univ.filter (fun v => I p v)).erase l

theorem pencil_support {N} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {p l p' l' : Fin N} (pl : I p l) (pl' : I p' l')
    (W Z : Finset (Fin N))
    (wp : W ⊆ Points I p l) (wp' : W ⊆ Points I p' l')
    (zl : Z ⊆ Lines I p l) (zl' : Z ⊆ Lines I p' l')
    (three : (1<W.card ∧ Z.Nonempty) ∨ (W.Nonempty ∧ 1<Z.card)) :
    p=p' ∧ l=l' := by
  classical
  have point {u} (h : u∈W) : (u≠p ∧ I u l) ∧ (u≠p' ∧ I u l') := by
    obtain ⟨a,b⟩ := Finset.mem_erase.mp (wp h)
    obtain ⟨c,d⟩ := Finset.mem_erase.mp (wp' h)
    exact ⟨⟨a,(Finset.mem_filter.mp b).2⟩,c,(Finset.mem_filter.mp d).2⟩
  have line {v} (h : v∈Z) : (v≠l ∧ I p v) ∧ (v≠l' ∧ I p' v) := by
    obtain ⟨a,b⟩ := Finset.mem_erase.mp (zl h)
    obtain ⟨c,d⟩ := Finset.mem_erase.mp (zl' h)
    exact ⟨⟨a,(Finset.mem_filter.mp b).2⟩,c,(Finset.mem_filter.mp d).2⟩
  rcases three with ⟨wc,⟨v,hv⟩⟩ | ⟨⟨u,hu⟩,zc⟩
  · obtain ⟨u,hu,w,hw,uw⟩ := Finset.one_lt_card.mp wc
    have same := (unique u w uw).unique ⟨(point hu).1.2,(point hw).1.2⟩ ⟨(point hu).2.2,(point hw).2.2⟩
    refine ⟨?_,same⟩
    by_contra ne
    exact (line hv).1.1 ((unique p p' ne).unique ⟨(line hv).1.2,(line hv).2.2⟩ ⟨pl,same ▸ pl'⟩)
  · obtain ⟨v,hv,s,hs,vs⟩ := Finset.one_lt_card.mp zc
    have pe : p=p' := by
      by_contra ne
      exact vs ((unique p p' ne).unique ⟨(line hv).1.2,(line hv).2.2⟩ ⟨(line hs).1.2,(line hs).2.2⟩)
    exact ⟨pe,(unique u p (point hu).1.1).unique ⟨(point hu).1.2,pl⟩ ⟨(point hu).2.2,pe ▸ pl'⟩⟩

theorem pencil_frontier {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (deg : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (K : Finset Nat) (P L : Nat → Finset (Fin N))
    (three : ∀ k∈K,(1<(P k).card ∧ (L k).Nonempty) ∨ ((P k).Nonempty ∧ 1<(L k).card))
    (supply : ∀ p l,I p l → ∃ k∈K,P k ⊆ Points I p l ∧ L k ⊆ Lines I p l) :
    N*(q+1) ≤ K.card := by
  classical
  let F := (Finset.univ : Finset (Fin N)).sigma (fun l => Finset.univ.filter (fun p => I p l))
  have fcard : F.card=N*(q+1) := by
    dsimp [F]
    rw [Finset.card_sigma]
    simp only [← Fintype.card_subtype,deg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> simp
  have pick (z : Sigma (fun _ : Fin N => Fin N)) (hz : z∈F) :
      ∃ k∈K,P k ⊆ Points I z.2 z.1 ∧ L k ⊆ Lines I z.2 z.1 :=
    supply z.2 z.1 (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).2
  choose! f hf using pick
  rw [←fcard]
  apply Finset.card_le_card_of_injOn f (fun a ha => (hf a ha).1)
  rintro ⟨l,p⟩ hp ⟨m,t⟩ ht eq
  have h := hf _ hp
  have h' := hf _ ht
  rw [←eq] at h'
  obtain ⟨pe,le⟩ := pencil_support I unique
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
    (Finset.mem_filter.mp (Finset.mem_sigma.mp ht).2).2
    _ _ h.2.1 h'.2.1 h.2.2 h'.2.2 (three _ h.1)
  subst pe
  subst le
  rfl

theorem pencil_exact {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (order : N=q^2+q+1)
    (col : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {p t : Fin N} (pt : I p t) :
    (Lines I p t).card=q ∧ outside I (Lines I p t)=Points I p t := by
  classical
  let S := Finset.univ.filter fun l => I p l
  have cf (l : Fin N) : (Finset.univ.filter fun x => I x l).card=q+1 := by
    simpa only [Fintype.card_subtype] using col l
  have cs : S.card=q+1 := lines_through q N I hq order cf unique p
  have ht : t∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pt⟩
  let L := S.erase t
  have cl : L.card=q := by dsimp [L]; rw [Finset.card_erase_of_mem ht,cs]; omega
  have someLine : L.Nonempty := Finset.card_pos.mp (by omega)
  have eq : outside I L = (Finset.univ.filter fun x => I x t).erase p := by
    ext v
    simp only [outside,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
    constructor
    · intro no
      have ne : v≠p := by
        rintro rfl
        obtain ⟨l,hl⟩ := someLine
        exact no l hl (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2
      obtain ⟨l,⟨pv,vv⟩,_⟩ := unique p v ne.symm
      have ls : l∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pv⟩
      have lt : l=t := by
        by_contra neq
        exact no l (Finset.mem_erase.mpr ⟨neq,ls⟩) vv
      exact ⟨ne,lt ▸ vv⟩
    · rintro ⟨ne,vt⟩ l hl vl
      have pl := (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2
      exact (Finset.mem_erase.mp hl).1 ((unique p v ne.symm).unique ⟨pl,vl⟩ ⟨pt,vt⟩)
  exact ⟨cl,eq⟩
def Omits {n} (C : Circuit) (w : Nat) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool, (∀ j,j≠i → x j=y j) → val C x w=val C y w

theorem missed_at_false {N q} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (accept : PairOK I C)
    (col : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N,p≠p' → ∃! l,I p l ∧ I p' l)
    (L : Finset (Fin N)) (small : L.card≤q) (w : Nat)
    (hw : ∀ y : Fin (N+N) → Bool, circuitFun (N+N) C y=true → val C y w=true)
    (off : val C (input (outside I L) L) w=false) :
    (∀ p, Omits C w (Fin.castAdd N p) → p∈outside I L) ∧
    (∀ l, Omits C w (Fin.natAdd N l) → l∈L) := by
  classical
  let P := outside I L
  constructor
  · intro p omitP
    by_contra miss
    have hit : ∃ l∈L,I p l := by
      by_contra fail
      exact miss (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl pl => fail ⟨l,hl,pl⟩⟩)
    obtain ⟨l,hl,pl⟩ := hit
    have on := hw (input (insert p P) L)
      (true_of_incidence hm accept _ _ ⟨p,Finset.mem_insert_self _ _,l,hl,pl⟩)
    have e := omitP (input P L) (input (insert p P) L) (by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro p' ne
        have np : p'≠p := fun eq => ne (congrArg (Fin.castAdd N) eq)
        simp only [input_l,Finset.mem_insert,np,false_or]
      · intro l' _
        simp only [input_r])
    change val C (input P L) w=false at off
    rw [off,on] at e
    cases e
  · intro l omitL
    by_contra miss
    obtain ⟨p,hp,pl⟩ := escape_line I col unique small miss
    have on := hw (input P (insert l L))
      (true_of_incidence hm accept _ _ ⟨p,hp,l,Finset.mem_insert_self _ _,pl⟩)
    have e := omitL (input P L) (input P (insert l L)) (by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro p' _
        simp only [input_l]
      · intro l' ne
        have nl : l'≠l := fun eq => ne (congrArg (Fin.natAdd N) eq)
        simp only [input_r,Finset.mem_insert,nl,false_or])
    change val C (input P L) w=false at off
    rw [off,on] at e
    cases e

theorem factor_price {N q} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (order : N=q^2+q+1)
    (col : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N,p≠p' → ∃! l,I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (K : Finset Nat) (P L : Nat → Finset (Fin N))
    (front : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z=true ↔ ∀ k∈K,val C z k=true)
    (lostP : ∀ k∈K,∀ p∈P k, Omits C k (Fin.castAdd N p))
    (lostL : ∀ k∈K,∀ l∈L k, Omits C k (Fin.natAdd N l))
    (three : ∀ k∈K,(1<(P k).card ∧ (L k).Nonempty) ∨ ((P k).Nonempty ∧ 1<(L k).card)) :
    N*(q+1) ≤ K.card := by
  classical
  apply pencil_frontier I col unique K P L three
  intro p t pt
  obtain ⟨small,zone⟩ := pencil_exact I hq order col unique pt
  let X := input (outside I (Lines I p t)) (Lines I p t)
  have off : circuitFun (N+N) C X≠true :=
    (sets_exact hm accept reject _ _ small.le).not.mpr (outside_miss I _)
  have bad : ∃ k∈K,val C X k=false := by
    by_contra fail
    apply off
    apply (front X).mpr
    intro k hk
    cases v : val C X k with
    | false => exact False.elim (fail ⟨k,hk,v⟩)
    | true => rfl
  obtain ⟨k,hk,cold⟩ := bad
  obtain ⟨p0,l0⟩ := missed_at_false I C hm accept col unique _ small.le k
    (fun y hy => (front y).mp hy k hk) cold
  refine ⟨k,hk,?_,?_⟩
  · intro a ha
    rw [←zone]
    exact p0 a (lostP k hk a ha)
  · intro a ha
    exact l0 a (lostL k hk a ha)

end PEqualNP.Outside.L_meta_9059.Pencil
