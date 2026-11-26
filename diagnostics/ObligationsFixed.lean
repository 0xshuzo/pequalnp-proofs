import PEqualNP.Outside.L_meta_2069
import PEqualNP.Defs
namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

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

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

end PlaneOrdered

namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := Fin 13
abbrev W := Fin 26
abbrev pt (p : V) : W := Fin.castAdd 13 p
abbrev ln (l : V) : W := Fin.natAdd 13 l
def offs : Finset V := {0,1,3,9}
def Inc (p l : V) : Prop := ∃ a ∈ offs, p = l+a
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def Avoid (S : Finset V) (l : V) := ∀ p ∈ S, ¬ Inc p l
instance (S : Finset V) (l : V) : Decidable (Avoid S l) := by unfold Avoid; infer_instance
def Closed (S : Finset V) := ∀ p ∉ S, ∃ l, Avoid S l ∧ Inc p l
def frame (S : Finset V) (i : W) : Bool :=
  decide ((∃ p ∈ S, i=pt p) ∨ ∃ l, i=ln l ∧ Avoid S l)
def pos (p l : V) (i : W) : Bool := decide (i=pt p ∨ i=ln l)
def Hit (x : W → Bool) := ∃ p l, Inc p l ∧ x (pt p)=true ∧ x (ln l)=true
def Tests (C : Circuit) : Prop :=
  (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) ∧
  ∀ S, Closed S → circuitFun 26 C (frame S)=false
def Exact (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ Hit x

theorem parts : ∀ i : W, (∃ p, i=pt p) ∨ ∃ l, i=ln l := by decide
theorem disj : ∀ p l : V, pt p ≠ ln l := by decide
theorem pp : ∀ p q : V, pt p=pt q → p=q := by decide
theorem ll : ∀ p q : V, ln p=ln q → p=q := by decide

theorem frame_pt (S : Finset V) (p : V) : frame S (pt p)=true ↔ p∈S := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨q,hq,e⟩|⟨l,e,_⟩)
    · exact (pp _ _ e) ▸ hq
    · exact (disj _ _ e).elim
  · exact fun h => Or.inl ⟨p,h,rfl⟩
theorem frame_ln (S : Finset V) (l : V) : frame S (ln l)=true ↔ Avoid S l := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨p,_,e⟩|⟨k,e,h⟩)
    · exact (disj _ _ e.symm).elim
    · exact (ll _ _ e) ▸ h
  · exact fun h => Or.inr ⟨l,rfl,h⟩
theorem complete {C : Circuit} (hm : Monotone2 C) : Tests C ↔ Exact C := by
  constructor
  · intro h x
    constructor
    · intro live
      by_contra empty
      let S := Finset.univ.filter fun p : V => ∀ l : V, x (ln l)=true → ¬ Inc p l
      have mem (p : V) : p∈S ↔ ∀ l, x (ln l)=true → ¬Inc p l := by simp [S]
      have avoid (l : V) (selected : x (ln l)=true) : Avoid S l :=
        fun p hp => (mem p).mp hp l selected
      have closed : Closed S := by
        intro p hp
        rw [mem] at hp
        push_neg at hp
        obtain ⟨l,hl,edge⟩ := hp
        exact ⟨l,avoid l hl,edge⟩
      have below : x≤frame S := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        rcases parts i with ⟨p,rfl⟩|⟨l,rfl⟩
        · exact (frame_pt S p).mpr ((mem p).mpr (fun l hl edge => empty ⟨p,l,edge,hi,hl⟩))
        · exact (frame_ln S l).mpr (avoid l hi)
      have bad : circuitFun 26 C (frame S)=true := PlaneOrdered.cmono C hm 26 _ _ below live
      rw [h.2 S closed] at bad
      contradiction
    · rintro ⟨p,l,edge,hp,hl⟩
      apply PlaneOrdered.cmono C hm 26 (pos p l) x _ (h.1 p l edge)
      intro i
      apply Bool.le_iff_imp.mpr
      simp only [pos,decide_eq_true_eq]
      rintro (rfl|rfl)
      · exact hp
      · exact hl
  · intro h
    constructor
    · intro p l edge
      exact (h _).mpr ⟨p,l,edge,by simp [pos],by simp [pos]⟩
    · intro S _
      cases hv : circuitFun 26 C (frame S) with
      | false => rfl
      | true =>
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp hv
        exact ((frame_ln S l).mp hl p ((frame_pt S p).mp hp) edge).elim

theorem exact_lower_iff :
    (∀ C : Circuit, Monotone2 C → C.size≤63 →
      (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) →
      (∀ S, Closed S → circuitFun 26 C (frame S)=false) → False) ↔
    ∀ C : Circuit, Monotone2 C → Exact C → 64≤C.size := by
  constructor
  · intro h C hm exactC
    obtain ⟨hp,hn⟩ := (complete hm).mpr exactC
    by_contra! small
    exact h C hm (by omega) hp hn
  · intro h C hm small hp hn
    have := h C hm ((complete hm).mp ⟨hp,hn⟩)
    omega
end Full5741

namespace Oblig5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2069
abbrev Port := Fin 26
abbrev Support := Finset Port
def wire (j : Nat) := 26+j
/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<26, cold w → (S w).card≤1)
    (step : ∀ j < m, cold (wire j) → ∃ K : Finset Nat,
      (∀ i∈K, i<wire j ∧ cold i) ∧ S (wire j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0)) :
    ∀ q ≤ m, ∀ F : Finset Nat, (∀ i∈F, i<wire q ∧ cold i) →
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
    by_cases h : wire q∈F
    · obtain ⟨K,prior,sub,kc⟩ := step q lt (good _ h).2
      let P := F.erase (wire q) ∪ K
      have hp : ∀ i∈P, i<wire q ∧ cold i := by
        intro i hi
        rcases Finset.mem_union.mp hi with he|hk
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp he
          have g := good i mem
          exact ⟨by dsimp [wire] at g ne ⊢; omega,g.2⟩
        · exact prior i hk
      have hs : F.biUnion S ⊆ P.biUnion S := by
        intro u hu
        obtain ⟨i,hi,ui⟩ := Finset.mem_biUnion.mp hu
        by_cases e : i=wire q
        · subst i
          obtain ⟨k,hk,uk⟩ := Finset.mem_biUnion.mp (sub ui)
          exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,uk⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩),ui⟩
      have e := Finset.card_erase_add_one h
      have upper : P.card≤(F.erase (wire q)).card+K.card := Finset.card_union_le _ _
      have bd := (Finset.card_le_card hs).trans (ih lim' P hp)
      omega
    · have bd := ih lim' F (fun i hi => ⟨by
          have ne : i≠wire q := fun e => h (e ▸ hi)
          have g := (good i hi).1
          dsimp [wire] at g ne ⊢
          omega,(good i hi).2⟩)
      omega

def off (v i : Port) : Bool :=
  decide (i=v ∨ ((v.val < (13 : Nat) ↔ (13 : Nat) ≤ i.val) ∧ adjb v i=false))
instance (x : Port → Bool) : Decidable (Full5741.Hit x) := by unfold Full5741.Hit; infer_instance
theorem off_false : ∀ v : Port, ¬Full5741.Hit (off v) := by decide +kernel
theorem incident_true : ∀ v i : Port, i∈N v → Full5741.Hit (pr v i) := by decide +kernel
theorem raw_split : ∀ v u p q : Port, off v u=false → pr v p u=true → pr v q u=true → p=q := by
  intro v u p q hu hp hq
  have ne : u≠v := by
    intro eq
    rw [eq] at hu
    simp [off] at hu
  exact ((of_decide_eq_true hp : u=v ∨ u=p).resolve_left ne).symm.trans
    ((of_decide_eq_true hq : u=v ∨ u=q).resolve_left ne)

def supp (C : Circuit) (v : Port) (w : Nat) : Support :=
  (N v).filter fun i => val C.gates w (pr v i)=true
def cold (C : Circuit) (v : Port) (w : Nat) := val C.gates w (off v)=false
def splits (C : Circuit) (v : Port) (j : Nat) :=
  (C.gates.getD j ⟨.and,[]⟩).op=.or ∧ cold C v (wire j) ∧
  ∀ u∈(C.gates.getD j ⟨.and,[]⟩).inputs, u<wire j → ¬supp C v (wire j)⊆supp C v u
noncomputable instance (C : Circuit) (v : Port) : DecidablePred (splits C v) := Classical.decPred _
noncomputable def fees (C : Circuit) (v : Port) := (Finset.range C.size).filter (splits C v)

theorem fanout_free {C : Circuit} (leg : Monotone2 C) (spec : Full5741.Exact C) (v : Port) :
    3 ≤ (fees C v).card := by
  classical
  let S := supp C v
  let c := cold C v
  have raw (w : Nat) (hw : w<26) (hc : c w) : (S w).card≤1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨_,h1⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,h2⟩ := Finset.mem_filter.mp hq
    change val C.gates w (off v)=false at hc
    rw [val_input _ _ _ hw] at hc h1 h2
    exact raw_split v ⟨w,hw⟩ p q hc h1 h2
  have step (j : Nat) (hj : j<C.size) (hc : c (wire j)) :
      ∃ K : Finset Nat, (∀ i∈K,i<wire j ∧ c i) ∧ S (wire j) ⊆ K.biUnion S ∧
         K.card≤1+(if splits C v j then 1 else 0) := by
    let g := C.gates[j]
    have legal := leg g (List.getElem_mem hj)
    have get : C.gates.getD j ⟨.and,[]⟩=g := List.getD_eq_getElem _ _ hj
    have emptyK (he : S (wire j)=∅) : ∃ K : Finset Nat, (∀ i∈K,i<wire j ∧ c i) ∧
        S (wire j) ⊆ K.biUnion S ∧ K.card≤1+(if splits C v j then 1 else 0) :=
      ⟨∅,by simp,by simp [he],by simp⟩
    have oneK (i : Nat) (hi : i<wire j) (cc : c i) (sub : S (wire j)⊆S i) :
        ∃ K : Finset Nat, (∀ i∈K,i<wire j ∧ c i) ∧ S (wire j) ⊆ K.biUnion S ∧
            K.card≤1+(if splits C v j then 1 else 0) :=
      ⟨{i},by simpa using And.intro hi cc,by simpa using sub,by simp⟩
    rcases legal.1 with ha|ho
    · have low : ¬∀ i∈g.inputs, i<wire j ∧ val C.gates i (off v)=true := by
        intro all
        have bad := (val_and C.gates (off v) j hj ha).mpr all
        exact Bool.noConfusion (bad.symm.trans hc)
      push_neg at low
      obtain ⟨i,hi,notGood⟩ := low
      by_cases prior : i<wire j
      · apply oneK i prior (Bool.eq_false_iff.mpr fun hh => by
          have nq := notGood prior
          simp_all)
        intro u hu
        obtain ⟨near,hot⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨near,((val_and C.gates _ j hj ha).mp hot i hi).2⟩
      · apply emptyK
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact prior (((val_and C.gates _ j hj ha).mp (Finset.mem_filter.mp hu).2 i hi).1)
    · let K := g.inputs.toFinset.filter fun i => i<wire j
      have eligible {i : Nat} : i∈K ↔ i∈g.inputs ∧ i<wire j := by simp [K]
      have cc (i : Nat) (hi : i∈K) : i<wire j ∧ c i := by
        obtain ⟨mem,lt⟩ := eligible.mp hi
        refine ⟨lt,Bool.eq_false_iff.mpr fun h => ?_⟩
        have bad := (val_or C.gates _ j hj ho).mpr ⟨i,mem,lt,h⟩
        exact Bool.noConfusion (bad.symm.trans hc)
      have sub : S (wire j)⊆K.biUnion S := by
        intro u hu
        obtain ⟨near,hot⟩ := Finset.mem_filter.mp hu
        obtain ⟨i,hi,lt,on⟩ := (val_or C.gates _ j hj ho).mp hot
        exact Finset.mem_biUnion.mpr ⟨i,eligible.mpr ⟨hi,lt⟩,Finset.mem_filter.mpr ⟨near,on⟩⟩
      by_cases one : ∃i∈K,S (wire j)⊆S i
      · obtain ⟨i,hi,inc⟩ := one
        exact oneK i (cc i hi).1 (cc i hi).2 inc
      · have sp : splits C v j := by
          refine ⟨by rw [get]; exact ho,hc,?_⟩
          rw [get]
          exact fun i hi lt inc => one ⟨i,eligible.mpr ⟨hi,lt⟩,inc⟩
        have card : K.card≤g.inputs.length :=
          (Finset.card_filter_le (fun i : Nat => i<wire j) g.inputs.toFinset).trans g.inputs.toFinset_card_le
        refine ⟨K,cc,sub,?_⟩
        rw [if_pos sp]
        exact (show K.card≤g.inputs.length from card).trans legal.2
  have out : S C.output=N v := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro i hi
    exact Finset.mem_filter.mpr ⟨hi,(spec _).mpr (incident_true v i hi)⟩
  have nothot : c C.output := Bool.eq_false_iff.mpr fun on => off_false v ((spec _).mp on)
  have bound : C.output<wire C.size := by
    by_contra! h
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(N v).card by rw [degN]; decide)
    have good : val C.gates C.output (pr v i)=true := (spec _).mpr (incident_true v i hi)
    rw [val_big _ _ _ h] at good
    contradiction
  have b := frontier C.size S c (splits C v) raw step C.size le_rfl {C.output}
    (by simpa using And.intro bound nothot)
  simp only [Finset.singleton_biUnion,Finset.card_singleton,out,degN] at b
  change 3≤((Finset.range C.size).filter (splits C v)).card
  omega

theorem total {C : Circuit} (hm : Monotone2 C) (ht : Full5741.Tests C) :
    78 ≤ ∑ v : Port, (fees C v).card := by
  have t := Finset.sum_le_sum (fun v (_ : v∈(Finset.univ : Finset Port)) =>
    fanout_free hm ((Full5741.complete hm).mp ht) v)
  simpa using t
end Oblig5741
