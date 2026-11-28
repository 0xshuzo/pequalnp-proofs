import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8869.Certificate

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

open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Finset
theorem induced_cost {N q d : Nat} (I : Fin N → Fin N → Prop) (C : Circuit) (ao : IsAO2 (N+N) C)
    (a b : Fin d → Fin N) (lim : d≤q) (ind : ∀ i j,I (a i) (b j) → i=j)
    (on : ∀ i,wireVal (N+N) C C.output (fun r => decide (r=Fin.castAdd N (a i) ∨ r=Fin.natAdd N (b i)))=true)
    (off : ∀ x : Fin (N+N) → Bool,Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
      (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → wireVal (N+N) C C.output x=false) :
    d ≤ (ands C).card := by
  classical
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have shape (j : Nat) (g : Gate) (hg : C.gates[j]?=some g) :
      ∃ r s : Nat, g.inputs=[r,s] ∧ r<N+N+j ∧ s<N+N+j := by
    obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
    have gg : gateAt C j=g := by simp [gateAt,List.getD,hg]
    obtain ⟨r,s,ab⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hg))
    have pre := ao.2.1 j hj
    rw [gg,ab] at pre
    exact ⟨r,s,ab,pre r (by simp),pre s (by simp)⟩
  let P (t : Finset (Fin d)) := t.image a
  let L (t : Finset (Fin d)) := (univ\t).image b
  let row (t : Finset (Fin d)) := input (P t) (L t)
  have neg (t : Finset (Fin d)) : val C (row t) C.output=false := by
    apply off
    · have sz : (L t).card≤d := card_image_le.trans ((card_le_card (subset_univ _)).trans_eq (by simp))
      simpa [row,input_r,Fintype.card_subtype] using sz.trans lim
    · rintro ⟨p,l,hit,px,lx⟩
      rw [show row t (Fin.castAdd N p)=_ from input_l (P t) (L t) p] at px
      rw [show row t (Fin.natAdd N l)=_ from input_r (P t) (L t) l] at lx
      obtain ⟨i,it,rfl⟩ := mem_image.mp (of_decide_eq_true px)
      obtain ⟨j,jt,rfl⟩ := mem_image.mp (of_decide_eq_true lx)
      exact (mem_sdiff.mp jt).2 ((ind i j hit) ▸ it)
  let tag (t : Finset (Fin d)) : Finset (Fin C.gates.length) := choices C (row t)
  have encode : (univ : Finset (Fin d)).powerset.card≤(ands C).powerset.card := by
    apply card_le_card_of_injOn tag
    · intro t _
      exact mem_powerset.mpr (filter_subset _ _)
    · intro s _ t _ same
      have zero := union_false C mon shape (row s) (row t) (input (P s ∪ P t) (L s ∪ L t))
        (input_union ..) same C.output (neg s) (neg t)
      have impossible (i : Fin d) (inP : i∈s ∨ i∈t) (inL : i∉s ∨ i∉t) : False := by
        have pin : a i ∈ P s ∪ P t := mem_union.mpr (inP.imp (mem_image_of_mem _) (mem_image_of_mem _))
        have ln {k : Finset (Fin d)} (no : i∉k) : b i∈L k := mem_image_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,no⟩)
        have lin : b i∈L s ∪ L t := mem_union.mpr (inL.imp ln ln)
        have yes : val C (input (P s ∪ P t) (L s ∪ L t)) C.output=true := by
          apply acts_mono mon _ _ (on i)
          intro z h
          rcases of_decide_eq_true h with rfl|rfl
          · exact (input_l ..).trans (decide_eq_true pin)
          · exact (input_r ..).trans (decide_eq_true lin)
        rw [zero] at yes
        cases yes
      ext i
      constructor
      · intro is
        by_contra no
        exact impossible i (.inl is) (.inr no)
      · intro it
        by_contra no
        exact impossible i (.inr it) (.inl no)
  simp only [card_powerset,card_univ,Fintype.card_fin] at encode
  by_contra! bad
  have strict := Nat.pow_lt_pow_right (by decide : 1<2) bad
  omega
end PEqualNP.Outside.L_meta_8869.Certificate
