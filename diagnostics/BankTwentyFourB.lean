import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18910.Price
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
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

abbrev Port := Fin 17
abbrev Support := Finset Port
def W (j : Nat) := 17+j

/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<17, cold w → (S w).card≤1)
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


abbrev T := Fin 8
def lists : List (List Nat) := [[6,7,8,15],[9,10,11,15],[12,13,14,15],[6,9,12,16],[7,10,13,16],[8,11,14,16],[15,16],[0,1,2,3,4,5]]
def target (t : T) : Support := Finset.univ.filter (fun i => i.val∈lists.getD t.val [])
def hot (t : T) (i v : Port) := decide (v=i ∨ t.val=7 ∧ 6≤v.val)
def ambient (t : T) (v : Port) := decide (6≤v.val ∧ (t.val=7 ∨ v∉target t))
def dom (t : T) (i : Port) (s : T) := ∀ v,hot t i v=true → ambient s v=true
instance (t : T) (i : Port) (s : T) : Decidable (dom t i s) := by unfold dom; infer_instance
def overlap (t s : T) := (target t).filter (fun i => ¬dom t i s)
theorem geometry : ∀ t s : T, t≠s → (overlap t s).card≤1 ∨ (overlap s t).card≤1 := by decide +kernel
theorem raw_geometry : ∀ t v,ambient t v=false → ((target t).filter fun i => hot t i v=true).card≤1 := by decide +kernel
theorem volume : ∑ t : T, (target t).card = 32 := by decide +kernel

open Classical in
theorem bank (C : Circuit) (leg : Monotone2 C) (out : T → Nat)
    (bd : ∀ t, out t<17+C.gates.length)
    (off : ∀ t, val C.gates (out t) (ambient t)=false)
    (on : ∀ t i, i∈target t → val C.gates (out t) (hot t i)=true) :
    24≤((Finset.range C.gates.length).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op = GateOp.or).card := by
  classical
  let m := C.gates.length
  let op (j : Nat) := (C.gates.getD j ⟨.or,[]⟩).op
  let S (t : T) (w : Nat) : Support := (target t).filter fun i => val C.gates w (hot t i)=true
  let cold (t : T) (w : Nat) := val C.gates w (ambient t)=false
  let charged (t : T) (j : Nat) := op j=.or ∧ cold t (W j) ∧ 2≤(S t (W j)).card
  let P (t : T) := (Finset.range m).filter (charged t)
  have raw (t : T) (w : Nat) (h : w<17) (off : cold t w) : (S t w).card≤1 := by
    have atInput : ambient t ⟨w,h⟩=false := (val_input C.gates _ w h).symm.trans off
    have v := raw_geometry t ⟨w,h⟩ atInput
    simpa only [S,val_input C.gates _ w h] using v
  have mono := val_mono (n:=17) C.gates (fun g hg => ⟨by simpa using (leg g hg).1,(leg g hg).2⟩)
  have overlap_bound (t s:T) (w:Nat) (h:cold s w) : (S t w).card≤(overlap t s).card := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hm,fun d => Bool.noConfusion ((mono (hot t i) (ambient s) d w hy).symm.trans h)⟩
  have dis : (↑(Finset.univ : Finset T) : Set T).PairwiseDisjoint P := by
    intro t _ s _ ne
    apply Finset.disjoint_left.mpr
    intro j ht hs
    obtain ⟨_,_,ct,zt⟩ := Finset.mem_filter.mp ht
    obtain ⟨_,_,cs,zs⟩ := Finset.mem_filter.mp hs
    have lt := overlap_bound t s (W j) cs
    have ls := overlap_bound s t (W j) ct
    rcases geometry t s ne with q|q <;> omega
  have steps (t : T) (j : Nat) (hj : j < m) (off : cold t (W j)) :
      ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧ S t (W j)⊆K.biUnion (S t) ∧
          K.card≤1+(if charged t j then 1 else 0) := by
    let g := C.gates[j]
    have ops : g.op=.and ∨ g.op=.or := (leg g (List.getElem_mem hj)).1
    have fan := (leg g (List.getElem_mem hj)).2
    have opg : op j=g.op := by
      change (C.gates.getD j ⟨.or,[]⟩).op=C.gates[j].op
      rw [List.getD_eq_getElem _ _ hj]
    have empty (he : S t (W j)=∅) : ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧ S t (W j)⊆K.biUnion (S t) ∧ K.card≤1+(if charged t j then 1 else 0) := ⟨∅,by simp,by simp [he],by simp⟩
    rcases ops with ha|ho
    · have ng : ¬∀ a∈g.inputs,a<W j ∧ val C.gates a (ambient t)=true := by
        intro all
        exact Bool.noConfusion (((val_and C.gates _ j hj ha).mpr all).symm.trans off)
      push_neg at ng
      obtain ⟨a,mem,neg⟩ := ng
      by_cases prior : a<W j
      · have ca : cold t a := Bool.eq_false_iff.mpr (by intro z; exact (by simpa [prior,z] using neg : False))
        refine ⟨{a},by simpa using And.intro prior ca,?_,by simp⟩
        simp only [Finset.singleton_biUnion]
        intro i hi
        obtain ⟨mi,yes⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨mi,((val_and C.gates _ j hj ha).mp yes a mem).2⟩
      · apply empty
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact prior (((val_and C.gates _ j hj ha).mp (Finset.mem_filter.mp hi).2 a mem).1)
    · let K := g.inputs.toFinset.filter (· < W j)
      have pred : ∀ a∈K,a<W j ∧ cold t a := by
        intro a mem
        obtain ⟨ma,lt⟩ := Finset.mem_filter.mp mem
        exact ⟨lt,Bool.eq_false_iff.mpr fun yes => Bool.noConfusion (((val_or C.gates _ j hj ho).mpr ⟨a,List.mem_toFinset.mp ma,lt,yes⟩).symm.trans off)⟩
      have sub : S t (W j)⊆K.biUnion (S t) := by
        intro i hi
        obtain ⟨mi,yes⟩ := Finset.mem_filter.mp hi
        obtain ⟨a,ma,lt,hy⟩ := (val_or C.gates _ j hj ho).mp yes
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ma,lt⟩,Finset.mem_filter.mpr ⟨mi,hy⟩⟩
      by_cases large : 2≤(S t (W j)).card
      · have ch : charged t j := ⟨opg.trans ho,off,large⟩
        have lim : K.card≤2 := (Finset.card_filter_le _ _).trans (g.inputs.toFinset_card_le.trans fan)
        exact ⟨K,pred,sub,by simpa [ch] using lim⟩
      · by_cases hex : (S t (W j)).Nonempty
        · obtain ⟨i,hi⟩ := hex
          obtain ⟨a,ma,ia⟩ := Finset.mem_biUnion.mp (sub hi)
          refine ⟨{a},by simpa using pred a ma,?_,by simp⟩
          simp only [Finset.singleton_biUnion]
          intro v hv
          have eq := Finset.card_le_one.mp (by omega : (S t (W j)).card≤1) v hv i hi
          simpa [eq] using ia
        · exact empty (Finset.not_nonempty_iff_eq_empty.mp hex)
  have one (t : T) : (target t).card≤1+(P t).card := by
    have eq : S t (out t)=target t := by
      ext i
      exact Finset.mem_filter.trans ⟨And.left,fun hi => ⟨hi,on t i hi⟩⟩
    have b := frontier m (S t) (cold t) (charged t) (raw t) (steps t) m le_rfl {out t} (by simpa [W,m] using And.intro (bd t) (off t))
    simpa [eq,P] using b
  have total := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset T)) => one t)
  rw [volume,Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at total
  have union : (Finset.univ.biUnion P).card=∑ t, (P t).card := Finset.card_biUnion dis
  have incl : Finset.univ.biUnion P ⊆ (Finset.range m).filter (fun j => op j=.or) := by
    intro j hj
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨lt,ch⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨lt,ch.1⟩
  have size := Finset.card_le_card incl
  rw [union] at size
  change 24≤((Finset.range m).filter (fun j => op j=.or)).card
  omega
end PEqualNP.Outside.L_meta_18910.Price
