import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

abbrev Support := Finset (Fin 20)
def W (j : Nat) := 40+j

/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<40, cold w → (S w).card≤1)
    (step : ∀ j < m, cold (W j) → ∃ K : Finset Nat,
      (∀ i∈K, i<W j ∧ cold i) ∧ S (W j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0)) :
    ∀ q ≤ m, ∀ F : Finset Nat, (∀ i∈F, i<W q ∧ cold i) →
      (F.biUnion S).card≤ F.card + ((Finset.range q).filter charged).card := by
  classical
  intro q
  induction q with
  | zero =>
    intro _ F good
    apply Finset.card_biUnion_le.trans
    have bound := Finset.sum_le_sum (fun w (h : w∈F) => raw w (good w h).1 (good w h).2)
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
    by_cases h : W q∈F
    · obtain ⟨K,prior,sub,kc⟩ := step q lt (good _ h).2
      let P := F.erase (W q) ∪ K
      have hp : ∀ i∈P, i<W q ∧ cold i := by
        intro i hi
        rcases Finset.mem_union.mp hi with he|hk
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp he
          have g := good i mem
          exact ⟨by dsimp [W] at g ne ⊢; omega,g.2⟩
        · exact prior i hk
      have hs : F.biUnion S ⊆ P.biUnion S := by
        intro u hu
        obtain ⟨i,hi,ui⟩ := Finset.mem_biUnion.mp hu
        by_cases e : i=W q
        · subst i
          obtain ⟨k,hk,uk⟩ := Finset.mem_biUnion.mp (sub ui)
          exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,uk⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩),ui⟩
      have e := Finset.card_erase_add_one h
      have upper : P.card≤(F.erase (W q)).card+K.card := Finset.card_union_le _ _
      have bd := (Finset.card_le_card hs).trans (ih lim' P hp)
      omega
    · have bd := ih lim' F (fun i hi => ⟨by
          have ne : i≠W q := fun e => h (e ▸ hi)
          have g := (good i hi).1
          dsimp [W] at g ne ⊢
          omega,(good i hi).2⟩)
      omega


abbrev Port := Fin 20
abbrev Tag := Fin 21
abbrev Raw := Fin 40

def rowMasks : List Nat := [131233,262466,524934,1293,2584,5170,10340,20680,41360,82720,
   165440,330880,661760,274945,549888,51203,102404,204810,409620,819240]
def target (t : Tag) : Finset Port := if t.val=20 then Finset.univ else
  Finset.univ.filter fun i => (rowMasks.getD t.val 0).testBit i.val

def sample (t : Tag) (i : Port) : Nat :=
  if t.val=20 then (1048575 <<< 20) ||| (1 <<< i.val) else 1 <<< (20+i.val)
def challenge (t : Tag) : Nat :=
  if t.val=20 then 1048575 <<< 20 else (1048575 ^^^ (rowMasks.getD t.val 0)) <<< 20
def assign (m : Nat) : Raw → Bool := fun i => m.testBit i.val
def possible (t u : Tag) : Finset Port := Finset.univ.filter fun i =>
  sample t i &&& challenge t ≠ sample t i ∧ sample t i &&& challenge u ≠ sample t i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geometry :
    (∀ t : Tag, ∀ v : Raw, (challenge t).testBit v.val=false →
      (Finset.univ.filter (fun i : Port => (sample t i).testBit v.val)).card ≤ 1) ∧
    (∀ t u : Tag, t≠u → (possible t u).card≤1 ∨ (possible u t).card≤1) ∧
    (∑ t : Tag, (target t).card) = 115 := by decide +kernel

lemma dominates {a b : Nat} (rel : a &&& b = a) : ∀ v : Raw, assign a v=true → assign b v=true := by
  intro v hv
  have vv := congrArg (fun k : Nat => k.testBit v.val) rel
  change a.testBit v.val = true at hv
  simpa [assign,Nat.testBit_and,hv] using vv

set_option maxHeartbeats 4000000 in
open Classical in
theorem bank_ors (C : Circuit) (fan : Monotone2 C) (out : Tag → Nat)
    (bound : ∀ t, out t < 40+C.gates.length)
    (on : ∀ t i, i∈target t → val C.gates (out t) (assign (sample t i))=true)
    (off : ∀ t, val C.gates (out t) (assign (challenge t))=false) :
    94 ≤ ((Finset.range C.gates.length).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op=GateOp.or).card := by
  classical
  let m := C.gates.length
  let op (j : Nat) := (C.gates.getD j ⟨.or,[]⟩).op
  let S (t : Tag) (w : Nat) : Support := Finset.univ.filter fun i => val C.gates w (assign (sample t i))=true
  let cold (t : Tag) (w : Nat) := val C.gates w (assign (challenge t))=false
  let charged (t : Tag) (j : Nat) := op j=.or ∧ cold t (W j) ∧ 2≤(S t (W j)).card
  let P (t : Tag) := (Finset.range m).filter (charged t)
  have mono : ∀ g∈C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨h,l⟩ := fan g hg; exact ⟨by simpa using h,l⟩
  have raw (t : Tag) (w : Nat) (hw : w<40) (hc : cold t w) : (S t w).card≤1 := by
    have hi := val_input C.gates (assign (challenge t)) w hw
    have zero : (challenge t).testBit w=false := hi.symm.trans hc
    have eq : S t w = Finset.univ.filter fun i : Port => (sample t i).testBit w := by
      ext i; simp [S,val_input C.gates _ w hw,assign]
    rw [eq]
    exact geometry.1 t ⟨w,hw⟩ zero
  have subset (t u : Tag) (w : Nat) (ht : cold t w) (hu : cold u w) : S t w ⊆ possible t u := by
    intro i hi
    have onw := (Finset.mem_filter.mp hi).2
    have bad (v : Tag) (h : cold v w) : sample t i &&& challenge v ≠ sample t i := by
      intro hle
      have yes := val_mono C.gates mono _ _ (dominates hle) w onw
      exact Bool.noConfusion (yes.symm.trans h)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad t ht,bad u hu⟩
  have dis : (↑(Finset.univ : Finset Tag) : Set Tag).PairwiseDisjoint P := by
    intro t _ u _ ne
    apply Finset.disjoint_left.mpr
    intro j ht hu
    have a := (Finset.mem_filter.mp ht).2
    have b := (Finset.mem_filter.mp hu).2
    rcases geometry.2.1 t u ne with small|small
    · have lo := a.2.2; have le := Finset.card_le_card (subset t u (W j) a.2.1 b.2.1); omega
    · have lo := b.2.2; have le := Finset.card_le_card (subset u t (W j) b.2.1 a.2.1); omega
  have steps (t : Tag) (j : Nat) (hj : j < m) (frozen : cold t (W j)) :
      ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧ S t (W j)⊆K.biUnion (S t) ∧
          K.card≤1+(if charged t j then 1 else 0) := by
    let g := C.gates[j]
    obtain ⟨alt,arity⟩ := mono g (List.getElem_mem hj)
    have og : op j=g.op := by
      change (C.gates.getD j _).op=C.gates[j].op
      rw [List.getD_eq_getElem _ _ hj]
    have empty (h : S t (W j)=∅) : ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧
        S t (W j)⊆K.biUnion (S t) ∧ K.card≤1+(if charged t j then 1 else 0) :=
      ⟨∅,by simp,by simp [h],by simp⟩
    have one (i : Nat) (pr : i<W j ∧ cold t i) (su : S t (W j)⊆S t i) :
        ∃ K : Finset Nat, (∀ k∈K, k<W j ∧ cold t k) ∧ S t (W j)⊆K.biUnion (S t) ∧
          K.card≤1+(if charged t j then 1 else 0) :=
      ⟨{i},by simpa using pr,by simpa using su,by simp⟩
    rcases alt with aa|oo
    · have zero : ¬∀ i ∈ g.inputs, i < W j ∧ val C.gates i (assign (challenge t))=true := by
        intro all
        have q := (val_and C.gates (assign (challenge t)) j hj aa).2 all
        exact Bool.noConfusion (q.symm.trans frozen)
      push_neg at zero
      obtain ⟨i,hi,no⟩ := zero
      by_cases lt : i<W j
      · have coldI : cold t i := by
          unfold cold; cases e : val C.gates i (assign (challenge t)) <;> simp_all
        apply one i ⟨lt,coldI⟩
        intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((val_and C.gates _ j hj aa).1
          (Finset.mem_filter.mp hz).2 i hi).2⟩
      · apply empty; apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact lt (((val_and C.gates _ j hj aa).1 (Finset.mem_filter.mp hz).2 i hi).1)
    · let K := g.inputs.toFinset.filter (fun i => i < W j)
      have kp (i : Nat) (hi : i∈K) : i<W j ∧ cold t i := by
        obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hi
        refine ⟨lt,Bool.eq_false_iff.mpr (fun hc => ?_)⟩
        have q := (val_or C.gates _ j hj oo).2 ⟨i,List.mem_toFinset.mp mem,lt,hc⟩
        exact Bool.noConfusion (q.symm.trans frozen)
      have su : S t (W j)⊆K.biUnion (S t) := by
        intro z hz
        obtain ⟨i,hi,lt,yes⟩ := (val_or C.gates _ j hj oo).1 (Finset.mem_filter.mp hz).2
        exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi,lt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩⟩
      by_cases ch : 2 ≤ (S t (W j)).card
      · have active : charged t j := ⟨og.trans oo,frozen,ch⟩
        refine ⟨K,kp,su,?_⟩
        have card := (Finset.card_filter_le g.inputs.toFinset _).trans (List.toFinset_card_le g.inputs)
        simpa [K,active] using card.trans arity
      · rcases (S t (W j)).eq_empty_or_nonempty with e|⟨v,hv⟩
        · exact empty e
        · obtain ⟨i,hi,vv⟩ := Finset.mem_biUnion.mp (su hv)
          apply one i (kp i hi)
          intro z hz
          have eq : z=v := Finset.card_le_one.mp (by omega : (S t (W j)).card≤1) z hz v hv
          exact eq ▸ vv
  have one (t : Tag) : (target t).card ≤ 1+(P t).card := by
    have inc : target t ⊆ S t (out t) := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,on t i hi⟩
    have z := frontier m (S t) (cold t) (charged t) (raw t) (steps t) m le_rfl {out t}
      (by simpa [W,m] using And.intro (bound t) (off t))
    exact (Finset.card_le_card inc).trans (by simpa [P] using z)
  have total := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset Tag)) => one t)
  rw [geometry.2.2,Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at total
  have un : (Finset.univ.biUnion P).card=∑ t,(P t).card := Finset.card_biUnion dis
  have inc : Finset.univ.biUnion P ⊆ (Finset.range m).filter fun j => op j=.or := by
    intro j hj; obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2.1⟩
  have card := Finset.card_le_card inc
  change 94≤((Finset.range m).filter fun j => op j=.or).card
  omega

def listed : List (ℕ × ℕ) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]

def assigned (x : Raw → Bool) := ∃ u v : Raw, (u.val,v.val)∈listed ∧ x u=true ∧ x v=true

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem output_data :
    (∀ i : Port, assigned (assign (sample 20 i))) ∧ ¬ assigned (assign (challenge 20)) := by
  unfold assigned; decide +kernel

open Classical in
theorem threshold (C : Circuit) (mono : Monotone2 C)
    (spec : ∀ x : Raw → Bool, C.eval (List.ofFn x)=true ↔ assigned x)
    (bank : Port → Nat) (bound : ∀ p, bank p<40+C.size)
    (yes : ∀ p : Port, ∀ i∈target (p.castLE (by decide)), val C.gates (bank p) (assign (sample (p.castLE (by decide)) i))=true)
    (no : ∀ p : Port, val C.gates (bank p) (assign (challenge (p.castLE (by decide))))=false)
    (ands : 20≤((Finset.range C.size).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op=GateOp.and).card) :
    114≤C.size := by
  classical
  let out (t : Tag) : Nat := if h : t.val<20 then bank ⟨t.val,h⟩ else C.output
  have output_on (i : Port) : val C.gates C.output (assign (sample 20 i))=true :=
    (spec _).2 (output_data.1 i)
  have output_off : val C.gates C.output (assign (challenge 20))=false :=
    Bool.eq_false_iff.mpr (fun h => output_data.2 ((spec _).1 h))
  have oc : C.output<40+C.size := by
    by_contra! bg
    have z := val_big C.gates (assign (sample 20 0)) C.output bg
    exact Bool.noConfusion ((output_on 0).symm.trans z)
  have price := bank_ors C mono out (by
    intro t
    dsimp [out]; split
    · exact bound _
    · exact oc) (by
    intro t i hi
    by_cases h : t.val<20
    · let p : Port := ⟨t.val,h⟩
      have eq : p.castLE (show 20≤21 by decide) = t := Fin.ext rfl
      simpa [out,h,eq,p] using yes p i (eq.symm ▸ hi)
    · have eq : t=20 := Fin.ext (by have ht:=t.isLt; change t.val=20; omega)
      subst t; exact output_on i) (by
    intro t
    by_cases h : t.val<20
    · let p : Port := ⟨t.val,h⟩
      have eq : p.castLE (show 20≤21 by decide) = t := Fin.ext rfl
      simpa [out,h,eq,p] using no p
    · have eq : t=20 := Fin.ext (by have ht:=t.isLt; change t.val=20; omega)
      subst t; exact output_off)
  let A := (Finset.range C.size).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op=GateOp.and
  let O := (Finset.range C.size).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op=GateOp.or
  have dis : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro j ha ho
    exact GateOp.noConfusion ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp ho).2)
  have inc : A∪O ⊆ Finset.range C.size := by
    intro j hj; rcases Finset.mem_union.mp hj with h|h <;> exact (Finset.mem_filter.mp h).1
  have cp := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis,Finset.card_range] at cp
  change 94≤O.card at price
  change 20≤A.card at ands
  omega

end PEqualNP.Outside.L_meta_9804.Research
