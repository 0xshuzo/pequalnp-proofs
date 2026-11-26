import PEqualNP.Outside.L_meta_2069

namespace RawBank9766
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2069
abbrev Port := Fin 13
abbrev Support := Finset Port
def W (j : Nat) := 14+j

/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<14, cold w → (S w).card≤1)
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

def outputs : List (List Nat) := [[1,3,9],[1,2,4,10],[2,3,5,11],[3,4,6,12],
  [0,4,5,7],[1,5,6,8],[2,6,7,9],[3,7,8,10],[4,8,9,11],[5,9,10,12],
  [0,6,10,11],[1,7,11,12],[0,2,8,12]]
def target (t : Port) : Support := Finset.univ.filter (fun i => i.val∈outputs.getD t.val [])
lemma separation : ∀ a b : Port, a≠b → (target a∩target b).card≤1 := by decide +kernel
lemma price : ∑ t : Port, (target t).card = 51 := by decide +kernel
def single (i : Port) (x : Port) := decide (x=i)
def outside (r t : Port) (x : Port) := decide (x≠r ∧ x∉target t)
def extend (r : Port) (x : Port → Bool) (k : Fin 14) :=
  if h : k.val<13 then x ⟨k.val,h⟩ else !(x r)

set_option maxHeartbeats 2000000 in
open Classical in
theorem bank_raw_signed (r : Port) (C : Circuit) (out : Port → Nat)
    (bound : ∀ t, out t<14+C.gates.length)
    (gates : ∀ j g, C.gates[j]?=some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a<14+j ∧ b<14+j)
    (spec : ∀ t x, val C.gates (out t) (extend r x)=true ↔ ∃ i∈target t, x i=true) :
    38≤((Finset.range C.gates.length).filter fun j => (C.gates.getD j ⟨.or,[]⟩).op = GateOp.or).card := by
  classical
  let m := C.gates.length
  let op (j : Nat) := (C.gates.getD j ⟨.or,[]⟩).op
  let S (t : Port) (w : Nat) : Support := Finset.univ.filter (fun i => (i≠r ∨ i∈target t) ∧ val C.gates w (extend r (single i))=true)
  let cold (t : Port) (w : Nat) := val C.gates w (extend r (outside r t))=false
  let charged (t : Port) (j : Nat) := op j=.or ∧ cold t (W j) ∧ 2≤(S t (W j)).card
  let P (t : Port) := (Finset.range m).filter (charged t)
  have mono := val_mono (n:=14) C.gates (by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨go,a,b,ins,_,_⟩ := gates j _ (List.getElem?_eq_getElem hj)
    exact ⟨go,by simp [ins]⟩)
  have raw (t : Port) (w : Nat) (h : w<14) (off : cold t w) : (S t w).card≤1 := by
    by_cases q : w<13
    · have sub : S t w⊆{(⟨w,q⟩ : Port)} := by
        intro i hi
        have v := (Finset.mem_filter.mp hi).2.2
        rw [val_input _ _ _ h] at v
        change i ∈ ({⟨w,q⟩} : Support)
        simpa [extend,q,single,eq_comm] using v
      exact (Finset.card_le_card sub).trans (by simp)
    · change val C.gates w (extend r (outside r t))=false at off
      rw [val_input _ _ _ h] at off
      simp [extend,q,outside] at off
  have subset (t : Port) (w : Nat) (off : cold t w) : S t w⊆target t := by
    intro i hi
    obtain ⟨inc,on⟩ := (Finset.mem_filter.mp hi).2
    rcases inc with h | good
    · by_contra neg
      have yes := mono (extend r (single i)) (extend r (outside r t)) (fun v in0 => by
        by_cases q : v.val<13
        · simp only [extend,dif_pos q] at in0 ⊢
          have eq : (⟨v.val,q⟩ : Port)=i := of_decide_eq_true in0
          exact decide_eq_true (eq.symm ▸ And.intro h neg)
        · simp [extend,q,outside]) w on
      exact Bool.noConfusion (yes.symm.trans off)
    · exact good
  have comp (t s : Port) (w : Nat) : S t w⊆S s w ∨ S s w⊆S t w := by
    by_cases ht : r∈target t
    · right
      intro i hi
      obtain ⟨_,on⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by by_cases h : i=r <;> simp_all,on⟩
    · left
      intro i hi
      obtain ⟨inc,on⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (fun e => ht (e ▸ (inc.resolve_left (not_not.mpr e)))),on⟩
  have dis : (↑(Finset.univ : Finset Port) : Set Port).PairwiseDisjoint P := by
    intro t _ s _ ne
    apply Finset.disjoint_left.mpr
    intro j ht hs
    have ht' := (Finset.mem_filter.mp ht).2
    have hs' := (Finset.mem_filter.mp hs).2
    have r0 := separation t s ne
    have st := subset t _ ht'.2.1
    have ss := subset s _ hs'.2.1
    rcases comp t s (W j) with incl|incl
    · have low := ht'.2.2
      have q := Finset.card_le_card (Finset.subset_inter st (incl.trans ss))
      omega
    · have low := hs'.2.2
      have q := Finset.card_le_card (Finset.subset_inter (incl.trans st) ss)
      omega
  have steps (t : Port) (j : Nat) (hj : j < m) (off : cold t (W j)) :
      ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧ S t (W j)⊆K.biUnion (S t) ∧
          K.card≤1+(if charged t j then 1 else 0) := by
    let g := C.gates[j]
    have get := List.getElem?_eq_getElem (l:=C.gates) hj
    obtain ⟨ops,a,b,ins,ha,hb⟩ := gates j g get
    have opg : op j=g.op := by
      change (C.gates.getD j ⟨.or,[]⟩).op=C.gates[j].op
      rw [List.getD_eq_getElem _ _ hj]
    have singleK (u : Nat) (lt : u<W j) (hc : cold t u) (incl : S t (W j)⊆S t u) :
        ∃ K : Finset Nat, (∀ i∈K, i<W j ∧ cold t i) ∧ S t (W j)⊆K.biUnion (S t) ∧
          K.card≤1+(if charged t j then 1 else 0) := by
      refine ⟨{u},by simpa using And.intro lt hc,by simpa using incl,by simp⟩
    rcases ops with andOp|orOp
    · have binary (x : Fin 14 → Bool) : val C.gates (W j) x=true ↔ val C.gates a x=true ∧ val C.gates b x=true := by
        simpa [W,show C.gates[j].inputs=[a,b] from ins,ha,hb] using val_and C.gates x j hj andOp
      have af : cold t a ∨ cold t b := by
        change val C.gates a (extend r (outside r t))=false ∨ val C.gates b (extend r (outside r t))=false
        by_contra! h
        have both := (binary (extend r (outside r t))).mpr ⟨Bool.eq_true_of_not_eq_false h.1,Bool.eq_true_of_not_eq_false h.2⟩
        exact Bool.noConfusion (both.symm.trans off)
      rcases af with af|bf
      · apply singleK a ha af
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1,((binary _).mp ((Finset.mem_filter.mp hi).2.2)).1⟩
      · apply singleK b hb bf
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1,((binary _).mp ((Finset.mem_filter.mp hi).2.2)).2⟩
    · have binary (x : Fin 14 → Bool) : val C.gates (W j) x=true ↔ val C.gates a x=true ∨ val C.gates b x=true := by
        simpa [W,show C.gates[j].inputs=[a,b] from ins,ha,hb] using val_or C.gates x j hj orOp
      have af : cold t a := Bool.eq_false_iff.mpr fun h => Bool.noConfusion (((binary _).mpr (.inl h)).symm.trans off)
      have bf : cold t b := Bool.eq_false_iff.mpr fun h => Bool.noConfusion (((binary _).mpr (.inr h)).symm.trans off)
      have eq : S t (W j)=S t a∪S t b := by
        ext i
        simp [S,binary,and_or_left]
      by_cases use : 2≤(S t (W j)).card
      · have count : charged t j := ⟨opg.trans orOp,off,use⟩
        refine ⟨{a,b},?_,by simp [eq],?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl|hi
          · exact ⟨ha,af⟩
          obtain rfl := Finset.mem_singleton.mp hi
          exact ⟨hb,bf⟩
        · have q := Finset.card_insert_le a ({b} : Finset Nat)
          simpa [count] using q
      · by_cases ab : S t (W j)⊆S t a
        · exact singleK a ha af ab
        · apply singleK b hb bf
          intro i hi
          obtain ⟨v,hv,nva⟩ := Finset.not_subset.mp ab
          have iv : i=v := Finset.card_le_one.mp (by omega : (S t (W j)).card≤1) i hi v hv
          subst i
          rw [eq] at hv
          exact (Finset.mem_union.mp hv).resolve_left nva
  have one (t : Port) : (target t).card≤1+(P t).card := by
    have yes : S t (out t)=target t := by
      ext i
      simp [S,spec,single]
    have no : cold t (out t) := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨i,mem,act⟩ := (spec t _).mp on
      exact (of_decide_eq_true act).2 mem
    have b := frontier m (S t) (cold t) (charged t) (raw t) (steps t) m le_rfl {out t} (by simpa [W,m] using And.intro (bound t) no)
    simpa [yes,P] using b
  have total := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset Port)) => one t)
  rw [price,Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at total
  have union : (Finset.univ.biUnion P).card=∑ t, (P t).card := Finset.card_biUnion dis
  have incl : Finset.univ.biUnion P ⊆ (Finset.range m).filter (fun j => op j=.or) := by
    intro j hj
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨lt,ch⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨lt,ch.1⟩
  have size := Finset.card_le_card incl
  rw [union] at size
  change 38≤((Finset.range m).filter (fun j => op j=.or)).card
  omega
end RawBank9766
