import PEqualNP.Defs

namespace SparseGateCount

theorem frontier {α : Type} [DecidableEq α] (n s : ℕ) (A : ℕ → Finset α) (O : Finset ℕ)
    (raw : ∀ i < n, (A i).card ≤ 1)
    (gate : ∀ j < s, ∃ U : Finset ℕ, (∀ i ∈ U, i < n+j) ∧
      U.card ≤ 1+(if j ∈ O then 1 else 0) ∧ A (n+j) ⊆ U.biUnion A)
    (F : Finset ℕ) (bound : ∀ i ∈ F, i < n+s) :
    (F.biUnion A).card ≤ F.card + (O.filter (· < s)).card := by
  classical
  induction s generalizing F with
  | zero =>
    have h := Finset.card_biUnion_le_card_mul F A 1 (fun i hi => raw i (by simpa using bound i hi))
    simpa using h
  | succ s ih =>
    have cutoff : O.filter (· < s+1) = if s ∈ O then insert s (O.filter (· < s)) else O.filter (· < s) := by
      ext i
      by_cases hs : s∈O
      · simp only [if_pos hs, Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro h
          by_cases he : i=s
          · exact Or.inl he
          · exact Or.inr ⟨h.1,by omega⟩
        · rintro (rfl | h)
          · exact ⟨hs,by omega⟩
          · exact ⟨h.1,by omega⟩
      · simp only [if_neg hs,Finset.mem_filter]
        constructor
        · rintro ⟨h,hi⟩
          have hne : i ≠ s := fun he => hs (he ▸ h)
          exact ⟨h,by omega⟩
        · rintro ⟨h,hi⟩; exact ⟨h,by omega⟩
    have hcount : (O.filter (· < s+1)).card =
        (O.filter (· < s)).card + (if s∈O then 1 else 0) := by
      rw [cutoff]
      by_cases h : s∈O <;> simp [h]
    have prefix := fun j (hj : j<s) => gate j (by omega)
    by_cases mem : n+s ∈ F
    · obtain ⟨U,early,fan,cover⟩ := gate s (by omega)
      let F' := F.erase (n+s) ∪ U
      have within : ∀ i ∈ F', i < n+s := by
        intro i hi
        rcases Finset.mem_union.mp hi with h | h
        · have h1 := (Finset.mem_erase.mp h).1
          have h2 := bound i (Finset.mem_erase.mp h).2
          omega
        · exact early i h
      have contain : F.biUnion A ⊆ F'.biUnion A := by
        intro z hz
        obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp hz
        by_cases he : i=n+s
        · obtain ⟨v,hv,haveZ⟩ := Finset.mem_biUnion.mp (cover (he ▸ hit))
          exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_union_right _ hv,haveZ⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hi⟩),hit⟩
      have counts := (Finset.card_le_card contain).trans (ih prefix F' within)
      have cu := Finset.card_union_le (F.erase (n+s)) U
      change F'.card ≤ _ at cu
      have ce := Finset.card_erase_add_one mem
      omega
    · have within : ∀ i ∈ F, i < n+s := by
        intro i hi
        have hi' := bound i hi
        have ne : i ≠ n+s := fun e => mem (e ▸ hi)
        omega
      have hb := ih prefix F within
      omega

theorem sensitivity {α : Type} [Fintype α] [DecidableEq α] (n s out : ℕ)
    (O : Finset ℕ) (v : ℕ → Bool) (V : ℕ → α → Bool)
    (ready : out < n+s) (reject : v out = false) (flips : ∀ a, V out a = true)
    (raw : ∀ i < n, (Finset.univ.filter fun a : α => v i = false ∧ V i a = true).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧
      v (n+j) = (if j∈O then v a || v b else v a && v b) ∧
      ∀ h, V (n+j) h = (if j∈O then V a h || V b h else V a h && V b h)) :
    Fintype.card α ≤ (O.filter (· < s)).card+1 := by
  classical
  let A (i : ℕ) := Finset.univ.filter fun h : α => v i = false ∧ V i h = true
  have step (j : ℕ) (hj : j < s) : ∃ U : Finset ℕ, (∀ i ∈ U, i < n+j) ∧
      U.card ≤ 1+(if j ∈ O then 1 else 0) ∧ A (n+j) ⊆ U.biUnion A := by
    obtain ⟨a,b,ha,hb,base,pert⟩ := gate j hj
    by_cases hor : j∈O
    · refine ⟨{a,b},?_,?_,?_⟩
      · intro i hi; rcases (show i=a ∨ i=b by simpa using hi) with rfl | rfl <;> assumption
      · simpa [hor] using Finset.card_insert_le a ({b} : Finset ℕ)
      · intro h hit
        obtain ⟨hn,htrue⟩ := (Finset.mem_filter.mp hit).2
        rw [base,if_pos hor] at hn
        rw [pert,if_pos hor] at htrue
        cases h₁ : v a <;> cases h₂ : v b <;> simp_all [A]
    · by_cases yes : v a = true
      · refine ⟨{b},by simpa using hb,by simp [hor],?_⟩
        intro h hit
        obtain ⟨hn,ht⟩ := (Finset.mem_filter.mp hit).2
        simp [base,hor,yes] at hn
        simp [pert,hor] at ht
        simpa [A] using (show v b=false ∧ V b h=true from ⟨hn,ht.2⟩)
      · refine ⟨{a},by simpa using ha,by simp [hor],?_⟩
        intro h hit
        obtain ⟨_,ht⟩ := (Finset.mem_filter.mp hit).2
        simp [pert,hor] at ht
        simpa [A,yes] using ht.1
  have h := frontier n s A O raw step {out} (by simpa using ready)
  have all : A out = Finset.univ := by ext a; simp [A,reject,flips]
  simpa [all,Nat.add_comm] using h

end SparseGateCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
namespace SparsePhysical
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

theorem physicalCost {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (C : Circuit) (O : Finset ℕ) (bits : Fin n → Bool) (tests : α → Fin n → Bool)
    (ao : IsAO2 n C) (ready : C.output < n+C.size)
    (mark : ∀ j < C.size, j∈O ↔ (gateAt C j).op=.or)
    (reject : C.eval (List.ofFn bits) = false) (flips : ∀ a, C.eval (List.ofFn (tests a))=true)
    (single : ∀ i : Fin n, (Finset.univ.filter fun a => bits i=false ∧ tests a i=true).card ≤ 1) :
    Fintype.card α ≤ (O.filter (· < C.size)).card+1 := by
  classical
  apply SparseGateCount.sensitivity n C.size C.output O (val C bits) (fun i a => val C (tests a) i)
    ready reject flips
  · intro i hi
    let v : Fin n := ⟨i,hi⟩
    change (Finset.univ.filter fun a => val C bits v.val = false ∧ val C (tests a) v.val = true).card ≤ 1
    simpa only [val_input] using single v
  · intro j hj
    have hj' : j < C.gates.length := hj
    let g := C.gates[j]'hj'
    have hg : g ∈ C.gates := List.getElem_mem hj
    have atg : gateAt C j = g := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
    obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (ao.2.2 _ hg)
    have ea : a<n+j := ao.2.1 j hj a (by rw [atg,inputs]; simp)
    have eb : b<n+j := ao.2.1 j hj b (by rw [atg,inputs]; simp)
    have law (x : Fin n → Bool) : val C x (n+j) =
        if j∈O then val C x a || val C x b else val C x a && val C x b := by
      have hgate : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      rw [val_gate C x hgate,inputs]
      rcases ao.1 g hg with ha | ho
      · have notOr : j ∉ O := by
          intro hm
          have bad := (mark j hj).1 hm
          rw [atg,ha] at bad
          contradiction
        simp [ha,GateOp.eval,operand,ea,eb,notOr]
      · have isOr : j ∈ O := (mark j hj).2 (atg ▸ ho)
        simp [ho,GateOp.eval,operand,ea,eb,isOr]
    exact ⟨a,b,ea,eb,law bits,fun t => law (tests t)⟩

end SparsePhysical



open PEqualNP.GenericRejection PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace SparsePlane

theorem overlap {N : ℕ} (S : Fin N → Finset (Fin N))
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    {l m : Fin N} (hne : l ≠ m) : (S l ∩ S m).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro p hp r hr
  by_contra e
  obtain ⟨u, _, hu⟩ := join p r e
  exact hne ((hu l ⟨(Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hr).1⟩).trans
    (hu m ⟨(Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hr).2⟩).symm)

theorem privateCount {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y : Finset (Fin N)) {l : Fin N} (hl : l ∉ Y) :
    q+1 ≤ Y.card + (S l ∩ zeroSet S Y).card := by
  classical
  let cap := Y.biUnion fun m => S l ∩ S m
  have hc : cap.card ≤ Y.card := by
    simpa [cap] using Finset.card_biUnion_le_card_mul Y (fun m => S l ∩ S m) 1
      (fun m hm => overlap S join (fun h => hl (h ▸ hm)))
  have incl : S l ⊆ cap ∪ (S l ∩ zeroSet S Y) := by
    intro p hp
    by_cases h : ∃ m ∈ Y, p ∈ S m
    · obtain ⟨m, hm, hpm⟩ := h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hp,hpm⟩⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hp' => h ⟨m,hm,hp'⟩⟩
  have hb := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  rw [weight] at hb
  omega

theorem testGeometry {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y Z : Finset (Fin N)) (small : Y.card ≤ q) :
    IsFalseInput S (zeroSet S Y) Z ↔ Z ⊆ Y := by
  constructor
  · intro hf l hl
    by_contra h
    have hc := privateCount S weight join Y h
    have he := Finset.disjoint_iff_inter_eq_empty.mp (hf l hl)
    rw [he] at hc
    simp only [Finset.card_empty, Nat.add_zero] at hc
    omega
  · intro inc l hl
    exact Finset.disjoint_left.mpr fun p hp hpz => (Finset.mem_filter.mp hpz).2 l (inc hl) hp


def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem inputMono {N : ℕ} (C : Circuit) (ao : IsAO2 (N+N) C)
    {X X' Y Y' : Finset (Fin N)} (hx : X ⊆ X') (hy : Y ⊆ Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  refine W_mono C.gates ao.1 (incidenceInput X Y) (incidenceInput X' Y') (by simp [incidenceInput]) ?_ C.output
  intro i
  unfold incidenceInput
  by_cases hi : i < N
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi), ofFn_getD, ofFn_getD]
    simpa [hi] using (show (⟨i,hi⟩ : Fin N) ∈ X → (⟨i,hi⟩ : Fin N) ∈ X' from fun h => hx h)
  · have hle : N ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ (by simpa using hle),
      List.getD_append_right _ _ _ _ (by simpa using hle), ofFn_getD, ofFn_getD]
    by_cases hj : i-N < N
    · simpa [hj] using (show (⟨i-N,hj⟩ : Fin N) ∈ Y → (⟨i-N,hj⟩ : Fin N) ∈ Y' from fun h => hy h)
    · simp [hj]

theorem pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (positive : 0 < q) (order : N = q^2+q+1)
      (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
    classical
    let through := Finset.univ.filter (fun l : Fin N => I p l)
    let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
    have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
      let full := Finset.univ.filter (fun r : Fin N => I r l)
      have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
      have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
      have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
      rw [same,Finset.card_erase_of_mem inFull,cardFull]
      omega
    have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
      intro l other k more different
      refine Finset.disjoint_left.mpr ?_
      intro r here there
      have throughL : I p l := (Finset.mem_filter.mp other).2
      have throughK : I p k := (Finset.mem_filter.mp more).2
      obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
      have rk := (Finset.mem_filter.mp there).2.1
      exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
    have together : through.biUnion rest = Finset.univ.erase p := by
      ext r
      constructor
      · intro seen
        obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
      · intro seen
        have diff := (Finset.mem_erase.mp seen).1
        obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
        exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
    have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
      rw [Nat.add_sub_cancel]
      ring
    have scale : through.card*q = (q+1)*q := by
      calc
        through.card*q = ∑ l ∈ through, q := by simp
        _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
        _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
        _ = (q+1)*q := by rw [together,rightSize]
    exact Nat.eq_of_mul_eq_mul_right positive scale

theorem pencilTest {q N : ℕ} (S : Fin N → Finset (Fin N)) (positive : 0 < q)
    (order : N = q^2+q+1) (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (l : Fin N) {p : Fin N} (on : p ∈ S l) :
    ∃ Y : Finset (Fin N), Y.card = q ∧ zeroSet S Y = (S l).erase p := by
  classical
  let H := Finset.univ.filter (fun m : Fin N => p ∈ S m)
  let Y := H.erase l
  have hc : H.card = q+1 := by
    apply pointDegree q N (fun r k => r ∈ S k) positive order _ join p
    intro k
    simpa [Fintype.card_subtype, Finset.filter_mem_eq_inter] using weight k
  have hl : l ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩
  have count : Y.card = q := by
    have h := Finset.card_erase_add_one hl
    dsimp only [Y]
    omega
  obtain ⟨m,hm⟩ : ∃ m, m ∈ Y := Finset.card_pos.mp (count ▸ positive)
  refine ⟨Y,count,?_⟩
  ext r
  constructor
  · intro hr
    have clear := (Finset.mem_filter.mp hr).2
    have rp : r ≠ p := by
      intro e
      exact clear m hm (e ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2)
    obtain ⟨k,⟨pk,rk⟩,_⟩ := join p r rp.symm
    have kl : k = l := by
      by_contra ne
      exact clear k (Finset.mem_erase.mpr ⟨ne, Finset.mem_filter.mpr ⟨Finset.mem_univ _,pk⟩⟩) rk
    exact Finset.mem_erase.mpr ⟨rp,kl ▸ rk⟩
  · intro hr
    obtain ⟨rp,rl⟩ := Finset.mem_erase.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro k hk rk
    have pr := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
    exact (Finset.mem_erase.mp hk).1 ((join p r rp.symm).unique ⟨pr,rk⟩ ⟨on,rl⟩)

theorem allFlips {q N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (ao : IsAO2 (N+N) C) (flags : RightOnIncidentPairs S C)
    (Y : Finset (Fin N)) (small : Y.card ≤ q) :
    (∀ p ∉ zeroSet S Y, C.eval (incidenceInput (insert p (zeroSet S Y)) Y) = true) ∧
    ∀ l ∉ Y, C.eval (incidenceInput (zeroSet S Y) (insert l Y)) = true := by
  constructor
  · intro p hp
    have hp' : ∃ l ∈ Y, p ∈ S l := by
      by_contra! h
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    obtain ⟨l,hl,hpl⟩ := hp'
    exact inputMono C ao (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_subset_iff.mpr hl) (flags l p hpl)
  · intro l hl
    have hc := privateCount S weight join Y hl
    have pos : 0 < (S l ∩ zeroSet S Y).card := by omega
    obtain ⟨p,hp⟩ := Finset.card_pos.mp pos
    have both := Finset.mem_inter.mp hp
    exact inputMono C ao (Finset.singleton_subset_iff.mpr both.2)
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) (flags l p both.1)

theorem manyFlips {q N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (positive : 0 < q) (order : N = q^2+q+1) (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (ao : IsAO2 (N+N) C) (flags : RightOnIncidentPairs S C)
    (reject : ∀ Y : Finset (Fin N), Y.card ≤ q → C.eval (incidenceInput (zeroSet S Y) Y) = false) :
    ∃ X Y : Finset (Fin N), X.card=q ∧ Y.card=q ∧ C.eval (incidenceInput X Y)=false ∧
      (∀ p ∉ X, C.eval (incidenceInput (insert p X) Y)=true) ∧
      (∀ l ∉ Y, C.eval (incidenceInput X (insert l Y))=true) := by
  let l : Fin N := ⟨0,by omega⟩
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (S l).card by rw [weight]; omega)
  obtain ⟨Y,cY,eY⟩ := pencilTest S positive order weight join l hp
  have cX : (zeroSet S Y).card=q := by
    rw [eY]
    have h := Finset.card_erase_add_one hp
    rw [weight] at h
    omega
  exact ⟨_,Y,cX,cY,reject Y cY.le,allFlips S C weight join ao flags Y cY.le⟩

end SparsePlane

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover

namespace SparsePencilCost

def packed {N : ℕ} (X Y : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => decide (p∈X)) (fun l => decide (l∈Y))

theorem packed_list {N : ℕ} (X Y : Finset (Fin N)) :
    List.ofFn (packed X Y) = incidenceInput X Y :=
  List.ofFn_fin_append _ _

theorem bothSides {N : ℕ} (X Y : Finset (Fin N)) (C : Circuit) (O : Finset ℕ)
    (ao : IsAO2 (N+N) C) (ready : C.output<N+N+C.size)
    (mark : ∀ j < C.size, j∈O ↔ (gateAt C j).op=.or)
    (reject : C.eval (incidenceInput X Y) = false)
    (points : ∀ p ∉ X, C.eval (incidenceInput (insert p X) Y)=true)
    (lines : ∀ l ∉ Y, C.eval (incidenceInput X (insert l Y))=true) :
    (N-X.card)+(N-Y.card) ≤ (O.filter (·<C.size)).card + 1 := by
  classical
  let T := (↑(Xᶜ) ⊕ ↑(Yᶜ))
  let tests : T → Fin (N+N) → Bool := Sum.elim (fun p => packed (insert p.val X) Y)
    (fun l => packed X (insert l.val Y))
  have hc : Fintype.card T = (N-X.card)+(N-Y.card) := by
    simp [T,Finset.card_compl]
  rw [←hc]
  apply SparsePhysical.physicalCost C O (packed X Y) tests ao ready mark
  · simpa only [packed_list] using reject
  · intro t
    rcases t with p | l
    · change C.eval (List.ofFn (packed (insert p.val X) Y)) = true
      rw [packed_list]
      exact points _ (Finset.mem_compl.mp p.property)
    · change C.eval (List.ofFn (packed X (insert l.val Y))) = true
      rw [packed_list]
      exact lines _ (Finset.mem_compl.mp l.property)
  · intro i
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    have hh₁ := (Finset.mem_filter.mp ha).2
    have hh₂ := (Finset.mem_filter.mp hb).2
    revert hh₁ hh₂
    refine Fin.addCases (motive := fun j => (packed X Y j = false ∧ tests a j = true) →
      (packed X Y j = false ∧ tests b j = true) → a = b) ?_ ?_ i
    · intro v
      rcases a with a | a <;> rcases b with b | b <;> simp [packed,tests]
      all_goals
        intros
        first | contradiction | congr 1; apply Subtype.ext; grind
    · intro v
      rcases a with a | a <;> rcases b with b | b <;> simp [packed,tests]
      all_goals
        intros
        first | contradiction | congr 1; apply Subtype.ext; grind

theorem pencilCost {q N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (O : Finset ℕ)
    (positive : 0<q) (order : N=q^2+q+1) (weight : ∀ l, (S l).card=q+1)
    (join : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (ready : C.output<N+N+C.size)
    (mark : ∀ j < C.size, j∈O ↔ (gateAt C j).op=.or)
    (flags : RightOnIncidentPairs S C)
    (reject : ∀ Y : Finset (Fin N), Y.card≤q → C.eval (incidenceInput (zeroSet S Y) Y) = false) :
    2*(N-q) ≤ (O.filter (·<C.size)).card+1 := by
  obtain ⟨X,Y,cX,cY,off,hp,hl⟩ := SparsePlane.manyFlips S C positive order weight join ao flags reject
  simpa [cX,cY,two_mul] using bothSides X Y C O ao ready mark off hp hl

end SparsePencilCost
