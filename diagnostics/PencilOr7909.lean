import PEqualNP.Defs

namespace Fibers7909

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


def isOr : GateOp → Bool
  | .or => true
  | _ => false

def orCost (C : Circuit) : ℕ → ℕ
  | 0 => 0
  | t+1 => orCost C t + (if (C.gates[t]?).any (fun g => isOr g.op) then 1 else 0)

theorem at_zero_cut {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j)
    (x : Fin n → Bool) (t : ℕ) (limit : t≤C.gates.length) (S : Finset ℕ)
    (low : ∀ w∈S, w<n+t) (off : ∀ w∈S, val C x w=false) :
    ∃ R : Finset ℕ, R ⊆ Finset.range n ∧ R.card ≤ S.card + orCost C t ∧
      (∀ r∈R, val C x r=false) ∧ ∀ y : Fin n → Bool, (∀ r∈R, val C y r=false) → ∀ w∈S, val C y w=false := by
  classical
  induction t generalizing S with
  | zero =>
    exact ⟨S,fun w hw => Finset.mem_range.mpr (by simpa using low w hw),by simp [orCost],off,fun _ h => h⟩
  | succ k ih =>
    have hk : k<C.gates.length := by omega
    let v := n+k
    have earlier (w : ℕ) (hw : w∈S) (ne : w≠v) : w<n+k := by
      have h := low w hw
      dsimp [v] at ne
      omega
    by_cases keep : v∈S
    · let g := C.gates[k]
      have get : C.gates[k]?=some g := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
      obtain ⟨a,b,inputs,ab,bv⟩ := hs k g get
      have av : a<n+k := ab.trans bv
      have ev (z : Fin n → Bool) : val C z v = g.op.eval [val C z a,val C z b] := by
        have e := val_gate C z get
        rw [inputs] at e
        simpa [v,operand,av,bv] using e
      have old := off v keep
      rw [ev] at old
      have op := (hm g (List.mem_of_getElem? get)).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      have clause : ∃ B : Finset ℕ, B.card≤1+(if isOr g.op then 1 else 0) ∧
        (∀ w∈B, w<n+k) ∧ (∀ w∈B, val C x w=false) ∧
        ∀ y : Fin n → Bool, (∀ w∈B, val C y w=false) → val C y v=false := by
        rcases op with ha | ho
        · rw [ha] at old
          simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] at old
          by_cases ax : val C x a=false
          · refine ⟨{a},by simp [ha,isOr],by simpa using av,by simpa using ax,?_⟩
            intro y h
            simp [ev,ha,GateOp.eval,h a (by simp)]
          · have bx : val C x b=false := by cases t : val C x a <;> simp_all
            refine ⟨{b},by simp [ha,isOr],by simpa using bv,by simpa using bx,?_⟩
            intro y h
            simp [ev,ha,GateOp.eval,h b (by simp)]
        · rw [ho] at old
          simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_false_iff] at old
          refine ⟨{a,b},?_,?_,?_,?_⟩
          · have pp := Finset.card_insert_le (a:=a) (s:=({b}:Finset ℕ))
            simpa [ho,isOr] using pp
          · simpa only [Finset.forall_mem_insert,Finset.forall_mem_singleton] using (And.intro av bv)
          · simpa only [Finset.forall_mem_insert,Finset.forall_mem_singleton] using old
          · intro y h
            simp [ev,ho,GateOp.eval,h a (by simp),h b (by simp)]
      obtain ⟨B,cb,lb,ob,cl⟩ := clause
      let Q := S.erase v ∪ B
      have qlow : ∀ w∈Q, w<n+k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact earlier _ (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1
        · exact lb _ hw
      have qoff : ∀ w∈Q, val C x w=false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact off _ (Finset.mem_erase.mp hw).2
        · exact ob _ hw
      obtain ⟨R,rr,cr,orr,cert⟩ := ih (by omega) Q qlow qoff
      have qu := Finset.card_union_le (S.erase v) B
      have sv := Finset.card_erase_add_one keep
      have cost : orCost C (k+1)=orCost C k+(if isOr g.op then 1 else 0) := by simp [orCost,get]
      refine ⟨R,rr,?_,orr,?_⟩
      · rw [cost]
        dsimp [Q] at cr
        omega
      · intro y hy w hw
        have hh := cert y hy
        by_cases eq : w=v
        · exact eq ▸ cl y (fun z hz => hh _ (Finset.mem_union_right _ hz))
        · exact hh _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · have lo' : ∀ w∈S, w<n+k := fun w hw => earlier _ hw (fun eq => keep (eq ▸ hw))
      obtain ⟨R,rr,cr,ofr,cert⟩ := ih (by omega) S lo' off
      exact ⟨R,rr,cr.trans (by simp [orCost]),ofr,cert⟩

theorem or_floor_at {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j)
    (x : Fin n → Bool) (w : ℕ) (valid : w<n+C.gates.length) (off : val C x w=false)
    (F : Finset (Fin n)) (sens : ∀ i∈F, ∃ y : Fin n → Bool,
       (∀ j, j≠i → x j=y j) ∧ val C y w=true) :
    F.card≤orCost C C.gates.length+1 := by
  classical
  obtain ⟨R,rr,cr,orr,cert⟩ := at_zero_cut C hm hs x C.gates.length le_rfl {w}
    (by simpa using valid) (by simpa using off)
  have sub : F.card≤R.card := by
    refine Finset.card_le_card_of_injOn Fin.val ?_ (fun _ _ _ _ e => Fin.ext e)
    intro i hi
    by_contra miss
    obtain ⟨y,agree,on⟩ := sens i hi
    have roots : ∀ r∈R, val C y r=false := by
      intro r hr
      let j : Fin n := ⟨r,Finset.mem_range.mp (rr hr)⟩
      have ne : j≠i := fun eq => miss (congrArg Fin.val eq ▸ hr)
      change val C y j.val=false
      rw [val_input,←agree j ne,←val_input C x]
      exact orr r hr
    have c := cert y roots w (by simp)
    simp [on] at c
  simp only [Finset.card_singleton] at cr
  omega
theorem identifies_complement {N q} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {C : Circuit} (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (col : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (L M : Finset (Fin N)) (small : L.card≤q) :
    circuitFun (N+N) C (input (outside I L) M)=true ↔ ¬ M⊆L := by
  constructor
  · intro on sub
    have h := (sets_exact hm accept reject (outside I L) M ((Finset.card_le_card sub).trans small)).mp on
    obtain ⟨p,hp,l,hl,pl⟩ := h
    exact (Finset.mem_filter.mp hp).2 l (sub hl) pl
  · intro diff
    obtain ⟨l,hl,miss⟩ := Finset.not_subset.mp diff
    obtain ⟨p,hp,pl⟩ := escape_line I col unique small miss
    exact true_of_incidence hm accept _ _ ⟨p,hp,l,hl,pl⟩

theorem thin_pencil {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (order : N=q^2+q+1)
    (col : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l) :
    ∃ L : Finset (Fin N), L.card=q ∧ (outside I L).card=q := by
  classical
  have hn : 0<N := by omega
  let p : Fin N := ⟨0,hn⟩
  let S := Finset.univ.filter fun l => I p l
  have cf (l : Fin N) : (Finset.univ.filter fun x => I x l).card=q+1 := by
    simpa only [Fintype.card_subtype] using col l
  have cs : S.card=q+1 := lines_through q N I hq order cf unique p
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  have pt := (Finset.mem_filter.mp ht).2
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
  refine ⟨L,cl,?_⟩
  rw [eq,Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pt⟩),cf]
  omega

theorem sensitive_lower {N q} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (C : Circuit) (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (col : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j)
    (valid : C.output<N+N+C.gates.length) (L : Finset (Fin N)) (small : L.card≤q) :
    (N-(outside I L).card)+(N-L.card)≤orCost C C.gates.length+1 := by
  classical
  let P := outside I L
  let x := input P L
  let e : Fin N ↪ Fin (N+N) := ⟨Fin.castAdd N,fun _ _ h => Fin.castAdd_inj.mp h⟩
  let f : Fin N ↪ Fin (N+N) := ⟨Fin.natAdd N,fun _ _ h => (Fin.natAdd_inj N).mp h⟩
  let F := (Finset.univ \ P).map e ∪ (Finset.univ \ L).map f
  have dis : Disjoint ((Finset.univ \ P).map e) ((Finset.univ \ L).map f) := by
    apply Finset.disjoint_left.mpr
    rintro z hz h
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨l,_,eq⟩ := Finset.mem_map.mp h
    exact left_ne_right p l eq.symm
  have card : F.card = (N-P.card)+(N-L.card) := by
    rw [show F.card=_ from Finset.card_union_of_disjoint dis]
    simp [Finset.card_sdiff_of_subset]
  have off : val C x C.output=false := by
    change circuitFun (N+N) C (input P L)=false
    have noton := (sets_exact hm accept reject P L small).not.mpr (outside_miss I L)
    cases res : circuitFun (N+N) C (input P L) <;> simp_all
  have sens (i : Fin (N+N)) (hi : i∈F) : ∃ y : Fin (N+N) → Bool,
      (∀ j, j≠i → x j=y j) ∧ val C y C.output=true := by
    rcases Finset.mem_union.mp hi with left | right
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp left
      have miss := (Finset.mem_sdiff.mp hp).2
      have hit : ∃ l∈L, I p l := by
        by_contra fail
        exact miss (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl pl => fail ⟨l,hl,pl⟩⟩)
      obtain ⟨l,hl,pl⟩ := hit
      refine ⟨input (insert p P) L,?_,true_of_incidence hm accept _ _ ⟨p,Finset.mem_insert_self _ _,l,hl,pl⟩⟩
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro p' ne
        have np : p'≠p := fun eq => ne (congrArg (Fin.castAdd N) eq)
        simp only [x,input_l,Finset.mem_insert,np,false_or]
      · intro l' _
        simp only [x,input_r]
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp right
      obtain ⟨p,hp,pl⟩ := escape_line I col unique small (Finset.mem_sdiff.mp hl).2
      refine ⟨input P (insert l L),?_,true_of_incidence hm accept _ _ ⟨p,hp,l,Finset.mem_insert_self _ _,pl⟩⟩
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro p' _
        simp only [x,input_l]
      · intro l' ne
        have nl : l'≠l := fun eq => ne (congrArg (Fin.natAdd N) eq)
        simp only [x,input_r,Finset.mem_insert,nl,false_or]
  exact card ▸ or_floor_at C hm hs x C.output valid off F sens

theorem pencil_or_floor {N q} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (C : Circuit) (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (hq : 2≤q) (order : N=q^2+q+1) (col : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j)
    (valid : C.output<N+N+C.gates.length) : 2*q^2+1≤orCost C C.gates.length := by
  obtain ⟨L,cl,cp⟩ := thin_pencil I hq order col unique
  have le := sensitive_lower C hm accept reject col unique hs valid L cl.le
  rw [cp,cl,order] at le
  omega

end Fibers7909
