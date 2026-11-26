import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2377_sensitivity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false
private def valid (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
private def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def step (w : List Bool) (g : Gate) := w ++ [val g w]
private def extra (g : Gate) : ℕ := if isOr g then 1 else 0

private theorem operandSet (g : Gate) (b : List Bool) (hg : valid g) (hn : val g b = false) :
    ∃ T : Finset ℕ, T.card ≤ 1 + extra g ∧ (∀ i ∈ T, b.getD i false = false) ∧
      ∀ w : List Bool, val g w = true → ∃ i ∈ T, w.getD i false = true := by
  rcases hg with ⟨hand | hor, hlen⟩
  · have hbad : ¬ ∀ i ∈ g.inputs, b.getD i false = true := by
      intro h
      have hyes : val g b = true := by simpa [val,hand,GateOp.eval,List.all_eq_true] using h
      rw [hn] at hyes
      contradiction
    push_neg at hbad
    obtain ⟨i, hi, hb⟩ := hbad
    refine ⟨{i},by simp [extra,isOr,hand],?_,?_⟩
    · simpa using hb
    · intro w hw
      have hh : ∀ j ∈ g.inputs, w.getD j false = true := by
        simpa [val,hand,GateOp.eval,List.all_eq_true] using hw
      exact ⟨i,by simp,hh i hi⟩
  · refine ⟨g.inputs.toFinset,?_,?_,?_⟩
    · simpa [extra,isOr,hor] using (List.toFinset_card_le _).trans hlen
    · simpa [val,hor,GateOp.eval,List.any_eq_false] using hn
    · intro w hw
      simpa [val,hor,GateOp.eval,List.any_eq_true] using hw

private theorem atEnd (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = val g w := by
  simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_right]

private theorem offEnd (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
  · have h1 : w.length ≤ i := by omega
    have h2 : (step w g).length ≤ i := by simp [step]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2]

private def covered {K : Type} (S : Finset ℕ) (b : List Bool) (v : K → List Bool) : Prop :=
  (∀ i ∈ S, b.getD i false = false) ∧ ∀ t : K, ∃ i ∈ S, (v t).getD i false = true

private theorem backOne {K : Type} (g : Gate) (b : List Bool) (v : K → List Bool)
    (len : ∀ t, (v t).length = b.length) (hg : valid g) (S : Finset ℕ)
    (hc : covered S (step b g) (fun t => step (v t) g)) :
    ∃ T : Finset ℕ, T.card ≤ S.card + extra g ∧ covered T b v := by
  by_cases hit : b.length ∈ S
  · have hz := hc.1 b.length hit
    rw [atEnd] at hz
    obtain ⟨P,hP,hno,hyes⟩ := operandSet g b hg hz
    refine ⟨S.erase b.length ∪ P,?_,?_,?_⟩
    · have s := Finset.card_union_le (S.erase b.length) P
      have h := Finset.card_erase_add_one hit
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
        simpa only [offEnd b g i ne] using hc.1 i mem
      · exact hno i h
    · intro t
      obtain ⟨i,hi,ht⟩ := hc.2 t
      by_cases ei : i = b.length
      · have eqv : i = (v t).length := ei.trans (len t).symm
        rw [eqv,atEnd] at ht
        obtain ⟨j,hj,hjt⟩ := hyes _ ht
        exact ⟨j,Finset.mem_union_right _ hj,hjt⟩
      · have ei' : i ≠ (v t).length := by rwa [len t]
        exact ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ei,hi⟩),
          (offEnd (v t) g i ei').symm.trans ht⟩
  · refine ⟨S,by omega,?_,?_⟩
    · intro i hi
      have ne : i ≠ b.length := fun e => hit (e ▸ hi)
      simpa only [offEnd b g i ne] using hc.1 i hi
    · intro t
      obtain ⟨i,hi,ht⟩ := hc.2 t
      have ne : i ≠ (v t).length := fun e => hit ((e.trans (len t)) ▸ hi)
      exact ⟨i,hi,(offEnd (v t) g i ne).symm.trans ht⟩

private theorem certificate {K : Type} (gs : List Gate) (b : List Bool) (v : K → List Bool)
    (len : ∀ t, (v t).length = b.length) (hg : ∀ g ∈ gs, valid g) (S : Finset ℕ)
    (hc : covered S (gs.foldl step b) (fun t => gs.foldl step (v t))) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.countP isOr ∧ covered T b v := by
  induction gs generalizing b v with
  | nil => exact ⟨S,by simp,hc⟩
  | cons g gs ih =>
    have lg (t : K) : (step (v t) g).length = (step b g).length := by simp [step,len t]
    obtain ⟨U,hU,hcU⟩ := ih (step b g) (fun t => step (v t) g) lg
      (fun a h => hg a (by simp [h])) hc
    obtain ⟨T,hT,hcT⟩ := backOne g b v len (hg g (by simp)) U hcU
    refine ⟨T,?_,hcT⟩
    cases h : isOr g <;> simp [List.countP_cons,h,extra] at * <;> omega

abbrev V := Fin 42
private def edges : List (Nat × Nat) := (List.range 21).flatMap fun i =>
  [(i,21+(i+20)%21),(i,21+i),(i,21+(i+5)%21),(i,21+(i+7)%21),(i,21+(i+17)%21)]
private def base (i : V) := decide (i.val ∈ ([0,2,7,8,31,32,37,39] : List Nat))
private def free : Finset V := Finset.univ.filter fun i => base i = false
private def flip (a i : V) := base i || decide (i = a)
private def accepts (x : V → Bool) := ∃ a b : V, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true
private instance (x : V → Bool) : Decidable (accepts x) := by unfold accepts; infer_instance
private theorem baseNo : ¬accepts base := by decide +kernel
private theorem flipYes : ∀ a ∈ free, accepts (flip a) := by decide +kernel
private theorem freeCard : free.card = 34 := by decide +kernel

private theorem offFlip (a : V) (i : ℕ) (hi : i ≠ a.val) :
    (List.ofFn (flip a)).getD i false = (List.ofFn base).getD i false := by
  by_cases h : i < 42
  · have h1 : i < (List.ofFn (flip a)).length := by simpa using h
    have h2 : i < (List.ofFn base).length := by simpa using h
    have h3 : (⟨i,h⟩ : V) ≠ a := fun eq => hi (congrArg Fin.val eq)
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,flip,h3]
  · have h1 : (List.ofFn (flip a)).length ≤ i := by simp; omega
    have h2 : (List.ofFn base).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2]

theorem planeUnrestricted (C : Circuit) (mono : Monotone2 C)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : V, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true) :
    33 ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard := by
  classical
  let K := {a : V // a ∈ free}
  let vars (t : K) := List.ofFn (flip t.val)
  have hv : ∀ g ∈ C.gates, valid g := by
    intro g hg
    obtain ⟨ho,hlen⟩ := mono g hg
    exact ⟨by simpa using ho,hlen⟩
  have c : covered {C.output} (C.gates.foldl step (List.ofFn base)) (fun t : K => C.gates.foldl step (vars t)) := by
    constructor
    · intro i hi
      obtain rfl := Finset.mem_singleton.mp hi
      change C.eval (List.ofFn base) = false
      exact Bool.eq_false_iff.mpr (fun ht => baseNo ((ok _).mp ht))
    · intro t
      exact ⟨C.output,by simp,(ok _).mpr (flipYes _ t.property)⟩
  obtain ⟨T,hT,hc⟩ := certificate C.gates (List.ofFn base) vars (fun t => by simp [vars]) hv {C.output} c
  have sub : free.image Fin.val ⊆ T := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,htrue⟩ := hc.2 (⟨a,ha⟩ : K)
    by_contra hnot
    have ne : j ≠ a.val := fun eq => hnot (eq ▸ hj)
    change (List.ofFn (flip a)).getD j false = true at htrue
    rw [offFlip a j ne,hc.1 j hj] at htrue
    contradiction
  have hmany := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective, freeCard] at hmany
  have count : C.gates.countP isOr = (Finset.univ.filter (fun i : Fin C.gates.length => isOr (C.gates.get i))).card := by
    simpa using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) isOr
  rw [Finset.card_singleton,count] at hT
  rw [Set.ncard_eq_toFinset_card']
  have eq : ({i : Fin C.gates.length | (C.gates.get i).op = GateOp.or} : Set _).toFinset =
      Finset.univ.filter (fun i : Fin C.gates.length => isOr (C.gates.get i)) := by
    ext i
    simp only [Set.mem_toFinset,Set.mem_setOf_eq,Finset.mem_filter,Finset.mem_univ,true_and]
    cases h : (C.gates.get i).op <;> simp [isOr,h]
  rw [eq]
  omega

end PEqualNP.Outside.L_meta_2377_sensitivity
