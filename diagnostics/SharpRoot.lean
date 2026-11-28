import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8089.Grid
abbrev V := Fin 26
abbrev P := Fin 13
abbrev X := V → Bool
abbrev pt (p : P) : V := Fin.castAdd 13 p
abbrev ln (l : P) : V := Fin.natAdd 13 l
def I (p l : P) : Prop := (p-l)^4=p-l
instance (p l : P) : Decidable (I p l) := inferInstanceAs (Decidable ((p-l)^4=p-l))
def F (x : X) : Prop := ∃ p l : P, I p l ∧ x (pt p)=true ∧ x (ln l)=true
def adj (u v : V) : Prop := ((u.val<13 ∧ 13≤v.val ∧ I (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val)) ∨
  (v.val<13 ∧ 13≤u.val ∧ I (Fin.ofNat 13 v.val) (Fin.ofNat 13 u.val)))
instance (u v : V) : Decidable (adj u v) := by unfold adj; infer_instance
def independent (x : X) := ∀u v, x u=true → x v=true → ¬adj u v
def active (x : X) : Finset V := Finset.univ.filter (fun i => x i=true)
def colors (d : P) : List (Fin 9) := 
  if d=0 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,6,0,8,0,3,4,5,1,2,0,7,0] else
  if d=1 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,0,0,8,1,0,3,4,7,2,6,0,5] else
  if d=3 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,6,0,0,1,2,4,0,5,8,3,7,0] else
  [0,0,0,0,1,2,3,4,5,0,6,7,8,0,1,2,8,4,3,0,5,0,0,6,7,0]
def color (p l : P) (v : V) : Fin 9 :=
  let t : P := (Fin.ofNat 13 v.val)-l
  (colors (p-l)).getD (if v.val<13 then t.val else 13+t.val) 0
theorem unbits (u v : V) (h : adj u v) :
    ∃ p l, I p l ∧ ((u=pt p ∧ v=ln l) ∨ (u=ln l ∧ v=pt p)) := by
  have raw (u v : V) : u.val<13 → 13≤v.val →
    u=pt (Fin.ofNat 13 u.val) ∧ v=ln (Fin.ofNat 13 v.val) :=
    (by decide +kernel : ∀ u v : V, u.val<13 → 13≤v.val →
      u=pt (Fin.ofNat 13 u.val) ∧ v=ln (Fin.ofNat 13 v.val)) u v
  rcases h with ⟨hu,hv,edge⟩|⟨hv,hu,edge⟩
  · exact ⟨_,_,edge,Or.inl (raw u v hu hv)⟩
  · exact ⟨_,_,edge,Or.inr ⟨(raw v u hv hu).2,(raw v u hv hu).1⟩⟩
theorem disjoint (x : X) (no : ¬F x) : independent x := by
  intro u v hu hv adj
  obtain ⟨p,l,pl,⟨a,b⟩|⟨a,b⟩⟩ := unbits _ _ adj
  · exact no ⟨p,l,pl,a ▸ hu,b ▸ hv⟩
  · exact no ⟨p,l,pl,b ▸ hv,a ▸ hu⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem color_law : ∀ p l : P, I p l → ∀ u v : V,
    ¬adj u (pt p) → ¬adj u (ln l) → ¬adj v (pt p) → ¬adj v (ln l) →
    color p l u=color p l v → u=v ∨ adj u v := by decide +kernel

theorem common {x y : X} (no : ¬F x) (ny : ¬F y) (cross : F (fun i => x i || y i)) :
    (active x∩active y).card ≤ 9 := by
  obtain ⟨p,l,pl,pbit,lbit⟩ := cross
  simp only [Bool.or_eq_true] at pbit lbit
  have one (i : V) (h : i∈active x∩active y) : x i=true ∧ y i=true :=
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2,
     (Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2⟩
  have avoid (i : V) (h : i∈active x∩active y) : ¬adj i (pt p) ∧ ¬adj i (ln l) :=
    ⟨pbit.elim (fun t => disjoint x no i _ (one i h).1 t) (fun t => disjoint y ny i _ (one i h).2 t),
     lbit.elim (fun t => disjoint x no i _ (one i h).1 t) (fun t => disjoint y ny i _ (one i h).2 t)⟩
  have sz : (active x∩active y).card ≤ (Finset.univ : Finset (Fin 9)).card := by
    apply Finset.card_le_card_of_injOn (color p l) (fun _ _ => Finset.mem_univ _)
    intro u hu v hv eq
    exact (color_law p l pl u v (avoid u hu).1 (avoid u hu).2 (avoid v hv).1 (avoid v hv).2 eq).resolve_right
      (disjoint x no u v (one u hu).1 (one v hv).1)
  simpa using sz

theorem distinctMax {x y : X} (hx : Maximal (fun z => ¬F z) x)
    (hy : Maximal (fun z => ¬F z) y) (ne : x≠y) : (active x∩active y).card≤9 := by
  apply common hx.prop hy.prop
  by_contra no
  let z : X := fun i => x i || y i
  have xz : x≤z := fun i => Bool.le_iff_imp.mpr (fun h => by simp [z,h])
  have yz : y≤z := fun i => Bool.le_iff_imp.mpr (fun h => by simp [z,h])
  have zx : z≤x := hx.2 no xz
  have zy : z≤y := hy.2 no yz
  exact ne (le_antisymm (xz.trans zy) (yz.trans zx))

noncomputable def missed (f : X → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => ∀ x : X, f (Function.update x i true)=f x)
theorem contain {f g : X → Bool} (correct : ∀ x, (f x && g x)=true ↔ F x)
    (gmono : ∀ x y : X, x≤y → g x=true → g y=true)
    {x : X} (hx : Maximal (fun z => ¬F z) x) (on : g x=true) : missed f ⊆ active x := by
  classical
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_contra bad
  let z := Function.update x i true
  have above : x≤z := by
    intro a
    by_cases eq : a=i
    · subst a; simp [z]
    · simp [z,eq]
  have bit : z i=true := by simp [z]
  have nz : F z := by
    by_contra off
    have zx := hx.2 off above i
    exact bad (Bool.le_iff_imp.mp zx bit)
  have fz : f z=true := (show f z=true ∧ g z=true by simpa only [Bool.and_eq_true] using (correct z).mpr nz).1
  have fx : f x=true := ((Finset.mem_filter.mp hi).2 x) ▸ fz
  exact hx.prop ((correct x).mp (by simp [fx,on]))

theorem oneError {f g : X → Bool} (correct : ∀ x, (f x && g x)=true ↔ F x)
    (gmono : ∀ x y : X, x≤y → g x=true → g y=true)
    (omitCount : 10≤(missed f).card) :
    ∀ x y : X, Maximal (fun z => ¬F z) x → Maximal (fun z => ¬F z) y →
      g x=true → g y=true → x=y := by
  intro x y hx hy gx gy
  by_contra ne
  have inclusion : missed f⊆active x∩active y := fun i hi => Finset.mem_inter.mpr ⟨contain correct gmono hx gx hi,contain correct gmono hy gy hi⟩
  have sub := Finset.card_le_card inclusion
  have lim := distinctMax hx hy ne
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
open PEqualNP.CleanedNonEdge
theorem leafCertificate {α : Type*} (n s : ℕ) (M : Finset ℕ)
    (A : ℕ → Prop) (H : α → ℕ → Prop)
    (rule : ∀ j<s, A (n+j) → ∃ B : Finset ℕ, B.card≤1+(if j∈M then 1 else 0) ∧
      (∀ i∈B,i<n+j) ∧ (∀ i∈B,A i) ∧ ∀ y : α, (∀ i∈B,H y i) → H y (n+j))
    (k : ℕ) (hk : k≤s) (S : Finset ℕ) (lo : ∀ w∈S,w<n+k) (off : ∀ w∈S,A w) :
    ∃ R : Finset ℕ, R ⊆ Finset.range n ∧ R.card ≤ S.card+(M∩Finset.range k).card ∧
      (∀ r∈R,A r) ∧ ∀ y : α, (∀ r∈R,H y r) → ∀ w∈S,H y w := by
  classical
  induction k generalizing S with
  | zero =>
    exact ⟨S,fun i hi => Finset.mem_range.mpr (by simpa using lo i hi),by simp,off,fun _ h => h⟩
  | succ k ih =>
    let v := n+k
    have below (i : ℕ) (hi : i∈S) (ne : i≠v) : i<n+k := by
      have := lo i hi
      dsimp [v] at ne
      omega
    have older : M∩Finset.range k ⊆ M∩Finset.range (k+1) :=
      fun i hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (Finset.mem_inter.mp hi).2))⟩
    by_cases active : v∈S
    · have old := off v active
      have clause := rule k (by omega) old
      obtain ⟨B,bs,bl,bo,bc⟩ := clause
      let Q := S.erase v ∪ B
      have ql : ∀ i∈Q,i<n+k := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact below i (Finset.mem_erase.mp a).2 (Finset.mem_erase.mp a).1
        · exact bl i b
      have qo : ∀ i∈Q,A i := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact off i (Finset.mem_erase.mp a).2
        · exact bo i b
      obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) Q ql qo
      refine ⟨R,rr,?_,ro,?_⟩
      · have merge := Finset.card_union_le (S.erase v) B
        have er := Finset.card_erase_add_one active
        dsimp [Q] at cr
        by_cases inM : k∈M
        · have strict : M∩Finset.range k ⊂ M∩Finset.range (k+1) := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨older,?_⟩
            intro eq
            have mem : k∈M∩Finset.range (k+1) := by simp [inM]
            rw [←eq] at mem
            simpa using mem
          have := Finset.card_lt_card strict
          simp [inM] at bs
          omega
        · have := Finset.card_le_card older
          simp [inM] at bs
          omega
      · intro y yr w hw
        have h := rc y yr
        by_cases eq : w=v
        · exact eq ▸ bc y (fun b hb => h b (Finset.mem_union_right _ hb))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) S (fun w hw => below w hw (fun eq => active (eq ▸ hw))) off
      exact ⟨R,rr,cr.trans (Nat.add_le_add_left (Finset.card_le_card older) _),ro,rc⟩

abbrev W (C : Circuit) (i : ℕ) : X → Bool := wireVal 26 C i
theorem omissions (C : Circuit) (ao : IsAO2 26 C) (u t : ℕ)
    (early : u<26+t) (budget : t≤C.gates.length) : 26≤(missed (W C u)).card+(1+t) := by
  classical
  let M := Finset.range C.gates.length
  let H (y : X×X) (i : ℕ) := W C i y.1=W C i y.2
  have rule (j : ℕ) (hj : j<C.gates.length) (_ : True) :
      ∃ B : Finset ℕ, B.card≤1+(if j∈M then 1 else 0) ∧
        (∀ i∈B,i<26+j) ∧ (∀ _i∈B,True) ∧ ∀ y : X×X, (∀ i∈B,H y i) → H y (26+j) := by
    let B := (gateAt C j).inputs.toFinset
    have length := ao.2.2 _ (gateAt_mem hj)
    have mem : j∈M := Finset.mem_range.mpr hj
    refine ⟨B,?_,?_,fun _ _ => trivial,?_⟩
    · have hl := List.toFinset_card_le (gateAt C j).inputs
      simpa only [B,if_pos mem,length] using hl
    · intro i hi
      exact ao.2.1 j hj i (List.mem_toFinset.mp hi)
    · intro y same
      change val C (List.ofFn y.1) (26+j)=val C (List.ofFn y.2) (26+j)
      rw [val_gate (n:=26) (by simp) hj, val_gate (n:=26) (by simp) hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      have eq := same i (List.mem_toFinset.mpr hi)
      simp only [if_pos (ao.2.1 j hj i hi)]
      exact eq
  obtain ⟨R,rr,cr,_,rc⟩ := leafCertificate 26 C.gates.length M (fun _ => True) H rule t budget {u}
    (by simpa using early) (by simp)
  have rcost : R.card≤1+t := by
    have h : (M∩Finset.range t).card≤(Finset.range t).card := Finset.card_le_card (fun _ h => (Finset.mem_inter.mp h).2)
    simpa using (cr.trans (Nat.add_le_add_left h _))
  let D : Finset V := Finset.univ.filter (fun i => i.val∈R)
  have dc : D.card≤R.card := by
    apply Finset.card_le_card_of_injOn Fin.val (fun i hi => (Finset.mem_filter.mp hi).2)
    intro i _ j _ eq
    exact Fin.ext eq
  have subset : Dᶜ⊆missed (W C u) := by
    intro i hi
    have notIn : i.val∉R := by simpa [D] using hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro x
    refine rc (Function.update x i true,x) ?_ u (by simp)
    intro r hr
    let a : V := ⟨r,Finset.mem_range.mp (rr hr)⟩
    have ne : a≠i := by
      intro eq
      exact notIn (congrArg Fin.val eq ▸ (show a.val∈R from hr))
    change val C (List.ofFn (Function.update x i true)) a.val=val C (List.ofFn x) a.val
    rw [val_ofFn,val_ofFn,Function.update_of_ne ne]
  have ca := Finset.card_compl_add_card D
  have cm := Finset.card_le_card subset
  simp only [Fintype.card_fin] at ca
  omega
theorem mono {C : Circuit} (hshape : IsAO2 26 C) (i : ℕ) (x y : X) (le : x≤y) : W C i x=true → W C i y=true := by
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true
  -- Wire monotonicity follows the gate induction in LowMergeWires.
  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      op.eval (l.map f) = true → op.eval (l.map f') = true := by
    rcases hop with rfl | rfl
    · change (l.map f).all id = true → (l.map f').all id = true
      simp only [List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i (H (f i) ⟨i, hi, rfl⟩)
    · change (l.map f).any id = true → (l.map f').any id = true
      simp only [List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

  have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ a b : List Bool, a.length = b.length → LeL a b →
        LeL (gs.foldl wstep a) (gs.foldl wstep b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [wstep, hl]
      · intro i hi
        unfold wstep at hi ⊢
        by_cases hia : i < a.length
        · rw [List.getD_append _ _ _ _ hia] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega)]
          rw [← hl]
          by_cases he : i - a.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
          · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
            rw [hm] at hi; simp at hi
  have rise (i : ℕ) {x y : Fin 26 → Bool} (h : x ≤ y) :
      wireVal 26 C i x = true → wireVal 26 C i y = true := by
    apply fold_mono C.gates hshape.1 _ _ (by simp) _ i
    intro j hj
    by_cases hlt : j < 26
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hj ⊢
      simp only [List.getElem_ofFn] at hj ⊢
      exact Bool.le_iff_imp.mp (h ⟨j,hlt⟩) hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      contradiction
  exact rise i le
theorem boundary (C : Circuit) (ao : IsAO2 26 C) (u v : ℕ)
    (pos : ∀ x, Minimal F x → W C u x=true ∧ W C v x=true)
    (neg : ∀ x, Maximal (fun z => ¬F z) x → (W C u x && W C v x)=false) :
    ∀ x, (W C u x && W C v x)=true ↔ F x := by
  intro x
  constructor
  · intro h
    by_contra no
    obtain ⟨y,le,hy⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ F z) x no
    have on : W C u x=true ∧ W C v x=true := by simpa only [Bool.and_eq_true] using h
    have au := mono ao u x y le on.1
    have av := mono ao v x y le on.2
    have := neg y hy
    simp [au,av] at this
  · intro yes
    obtain ⟨y,le,hy⟩ := exists_minimal_le_of_wellFoundedLT F x yes
    obtain ⟨au,av⟩ := pos y hy
    simp [mono ao u y x le au,mono ao v y x le av]
theorem earlyUnique (C : Circuit) (ao : IsAO2 26 C) (u v : ℕ)
    (early : u≤40) (long : 15≤C.gates.length)
    (pos : ∀ x, Minimal F x → W C u x=true ∧ W C v x=true)
    (neg : ∀ x, Maximal (fun z => ¬F z) x → (W C u x && W C v x)=false)
    (nontrivial : ∃ x, Maximal (fun z => ¬F z) x ∧ W C v x=true) :
    ∃! x, Maximal (fun z => ¬F z) x ∧ W C v x=true := by
  obtain ⟨x,hx,on⟩ := nontrivial
  have price := omissions C ao u 15 (by omega) long
  refine ⟨x,⟨hx,on⟩,?_⟩
  intro y hy
  exact oneError (boundary C ao u v pos neg) (mono ao v) (by omega) y x hy.1 hx hy.2 on

theorem clause {g : X → Bool}
    (gmono : ∀ x y : X, x≤y → g x=true → g y=true)
    (accept : ∀ x, F x → g x=true)
    {z : X} (nz : ¬F z)
    (unique : ∀ y, Maximal (fun w => ¬F w) y → g y=true → y=z) (x : X) :
    F x ↔ g x=true ∧ ¬x≤z := by
  constructor
  · intro fx
    refine ⟨accept x fx,?_⟩
    intro xz
    obtain ⟨p,l,e,pa,la⟩ := fx
    exact nz ⟨p,l,e,Bool.le_iff_imp.mp (xz _) pa,Bool.le_iff_imp.mp (xz _) la⟩
  · rintro ⟨gx,out⟩
    by_contra no
    obtain ⟨y,le,hy⟩ := exists_maximal_ge_of_wellFoundedGT (fun w => ¬F w) x no
    exact out (unique y hy (gmono x y le gx) ▸ le)

def mixedColors (d : P) : List (Fin 10) :=
  if d=2 then [8,8,8,8,0,1,2,3,4,8,5,6,7,9,9,9,7,3,2,9,4,0,1,5,6,9] else
  if d=4 then [8,8,0,8,8,1,2,3,4,8,5,6,7,9,9,0,9,9,1,3,5,9,7,2,6,4] else
  if d=5 then [8,8,0,8,1,8,2,3,4,8,5,6,7,9,1,9,7,9,9,2,5,4,9,6,3,0] else
  if d=6 then [8,8,0,8,1,2,8,3,4,8,5,6,7,9,0,2,9,1,9,9,5,6,7,9,3,4] else
  if d=7 then [8,8,0,8,1,2,3,8,4,8,5,6,7,9,1,0,7,9,2,9,9,6,5,3,9,4] else
  if d=8 then [8,8,0,8,1,2,3,4,8,8,5,6,7,9,1,0,7,2,9,3,9,9,5,6,4,9] else
  if d=10 then [8,8,0,8,1,2,3,4,5,8,8,6,7,9,9,2,7,1,5,3,9,6,9,9,4,0] else
  if d=11 then [8,8,0,8,1,2,3,4,5,8,6,8,7,9,1,9,7,4,5,3,6,9,2,9,9,0] else
  [8,8,0,8,1,2,3,4,5,8,6,7,8,9,0,7,9,2,5,4,6,1,9,3,9,9]
def mixColor (p l : P) (v : V) : Fin 10 :=
  let t : P := (Fin.ofNat 13 v.val)-l
  (mixedColors (p-l)).getD (if v.val<13 then t.val else 13+t.val) 0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem mix_law : ∀ p l : P, ¬I p l → ∀ u v : V,
    ¬adj u (pt p) → ¬adj u (ln l) → ¬adj v (pt p) → ¬adj v (ln l) →
    mixColor p l u=mixColor p l v → u=v ∨ adj u v := by decide +kernel
theorem mixedPrice {x : X} (nx : ¬F x) {p l : P} (hp : x (pt p)=true) (hl : x (ln l)=true) :
    (active x).card≤10 := by
  have non : ¬I p l := fun e => nx ⟨p,l,e,hp,hl⟩
  have bit (u : V) (h : u∈active x) : x u=true := (Finset.mem_filter.mp h).2
  have sz : (active x).card ≤ (Finset.univ : Finset (Fin 10)).card := by
    apply Finset.card_le_card_of_injOn (mixColor p l) (fun _ _ => Finset.mem_univ _)
    intro u hu v hv eq
    exact (mix_law p l non u v (disjoint x nx u _ (bit u hu) hp) (disjoint x nx u _ (bit u hu) hl)
      (disjoint x nx v _ (bit v hv) hp) (disjoint x nx v _ (bit v hv) hl) eq).resolve_right
      (disjoint x nx u v (bit u hu) (bit v hv))
  simpa using sz
def diagonal (v : V) : P := Fin.ofNat 13 v.val
theorem indep13 {x : X} (nx : ¬F x) : (active x).card≤13 := by
  have law : ∀ u v : V, diagonal u=diagonal v → u=v ∨ adj u v := by decide +kernel
  have sz : (active x).card ≤ (Finset.univ : Finset P).card := by
    apply Finset.card_le_card_of_injOn diagonal (fun _ _ => Finset.mem_univ _)
    intro u hu v hv eq
    exact (law u v eq).resolve_right (disjoint x nx u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2)
  simpa using sz
def shore (b : Bool) (i : V) := if i.val<13 then b else !b
theorem shoreNo (b : Bool) : ¬F (shore b) := by
  rintro ⟨p,l,_,hp,hl⟩
  simp [shore,p.isLt] at hp
  simp [shore] at hl
  cases b <;> simp_all
theorem pureOfLarge {x : X} (hx : Maximal (fun z => ¬F z) x) (large : 11≤(active x).card) :
    ∃ b, x=shore b := by
  by_cases yes : ∃ p, x (pt p)=true
  · obtain ⟨p,hp⟩ := yes
    have zero (l : P) : x (ln l)=false := by
      cases h : x (ln l)
      · rfl
      · have := mixedPrice hx.prop hp h
        omega
    have le : x≤shore true := by
      intro i
      refine @Fin.addCases 13 13 (fun i => x i≤shore true i) ?_ ?_ i
      · intro p
        simp [shore,p.isLt]
      · intro l
        rw [show x (Fin.natAdd 13 l)=false from zero l]
        simp
    exact ⟨true,le_antisymm le (hx.2 (shoreNo _) le)⟩
  · have le : x≤shore false := by
      intro i
      refine @Fin.addCases 13 13 (fun i => x i≤shore false i) ?_ ?_ i
      · intro p
        have h : x (pt p)=false := Bool.eq_false_iff.mpr (fun h => yes ⟨p,h⟩)
        rw [show x (Fin.castAdd 13 p)=false from h]
        simp
      · intro l
        simp [shore]
    exact ⟨false,le_antisymm le (hx.2 (shoreNo _) le)⟩
def single (i : V) : X := fun a => decide (a=i)
def pair (i j : V) : X := fun a => decide (a=i ∨ a=j)
theorem pairFlags (i j : V) : F (pair i j) ↔ adj i j := by
  have split (p l : P) : pt p≠ln l := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    simp only [pair,decide_eq_true_eq] at hp hl
    rcases hp with hp|hp <;> rcases hl with hl|hl
    · exact (split p l (hp.trans hl.symm)).elim
    · rw [←hp,←hl]
      exact (by decide +kernel : ∀ p l : P, I p l → adj (pt p) (ln l)) p l e
    · rw [←hp,←hl]
      exact (by decide +kernel : ∀ p l : P, I p l → adj (ln l) (pt p)) p l e
    · exact (split p l (hp.trans hl.symm)).elim
  · intro h
    obtain ⟨p,l,e,⟨a,b⟩|⟨a,b⟩⟩ := unbits _ _ h
    · exact ⟨p,l,e,by simp [pair,a],by simp [pair,b]⟩
    · exact ⟨p,l,e,by simp [pair,b],by simp [pair,a]⟩
theorem forceSingle {f : X → Bool} (accept : ∀x,F x → f x=true)
    {i a : V} (mi : i∈missed f) (ad : adj i a) : f (single a)=true := by
  have eq : Function.update (single a) i true=pair i a := by
    funext v
    by_cases vi : v=i
    · subst v; simp [pair]
    · simp [Function.update_of_ne vi,pair,single,vi]
  have mem : ∀ x : X, f (Function.update x i true)=f x := (Finset.mem_filter.mp mi).2
  have h := mem (single a)
  rw [eq] at h
  exact h ▸ accept _ ((pairFlags i a).mpr ad)
set_option maxRecDepth 10000 in
theorem separated : ∀ i j : V, ∃ a b : V, adj i a ∧ adj j b ∧ ¬adj a b := by decide +kernel
theorem someFull {f g : X → Bool} (correct : ∀x,(f x && g x)=true ↔ F x)
    (fm : ∀ x y : X, x≤y → f x=true → f y=true)
    (gm : ∀ x y : X, x≤y → g x=true → g y=true) : missed f=∅ ∨ missed g=∅ := by
  by_contra deny
  push_neg at deny
  obtain ⟨i,mi⟩ := Finset.nonempty_iff_ne_empty.mpr deny.1
  obtain ⟨j,mj⟩ := Finset.nonempty_iff_ne_empty.mpr deny.2
  obtain ⟨a,b,ia,jb,ab⟩ := separated i j
  have on (x : X) (yes : F x) : f x=true ∧ g x=true := by
    simpa only [Bool.and_eq_true] using (correct x).mpr yes
  have fa := forceSingle (fun x h => (on x h).1) mi ia
  have gb := forceSingle (fun x h => (on x h).2) mj jb
  have left : single a≤pair a b := fun v => Bool.le_iff_imp.mpr (by
    intro h
    have va : v=a := of_decide_eq_true h
    simp [pair,va])
  have right : single b≤pair a b := fun v => Bool.le_iff_imp.mpr (by
    intro h
    have vb : v=b := of_decide_eq_true h
    simp [pair,vb])
  exact ab ((pairFlags a b).mp ((correct _).mp (by simp [fm _ _ left fa,gm _ _ right gb])))
theorem factorLower (C : Circuit) (ao : IsAO2 26 C) (u v : ℕ)
    (long : 11≤C.gates.length) (correct : ∀x,(W C u x && W C v x)=true ↔ F x)
    (nontrivial : ∃ x, Maximal (fun z => ¬F z) x ∧ W C v x=true) : 37≤u := by
  by_contra low
  obtain ⟨x,hx,on⟩ := nontrivial
  have price := omissions C ao u 11 (by omega) long
  have sub := Finset.card_le_card (contain correct (mono ao v) hx on)
  have lim := indep13 hx.prop
  omega
theorem oneLate (C : Circuit) (ao : IsAO2 26 C) (u v : ℕ)
    (long : 24≤C.gates.length) (correct : ∀x,(W C u x && W C v x)=true ↔ F x) :
    50≤u ∨ 50≤v := by
  rcases someFull correct (mono ao u) (mono ao v) with a|b
  · left
    by_contra h
    have t := omissions C ao u 24 (by omega) long
    simp [a] at t
  · right
    by_contra h
    have t := omissions C ao v 24 (by omega) long
    simp [b] at t
theorem earlyShore (C : Circuit) (ao : IsAO2 26 C) (u v : ℕ)
    (early : u≤39) (long : 14≤C.gates.length) (correct : ∀x,(W C u x && W C v x)=true ↔ F x)
    {x : X} (mx : Maximal (fun z => ¬F z) x) (on : W C v x=true) : ∃ b, x=shore b := by
  have price := omissions C ao u 14 (by omega) long
  have sub := Finset.card_le_card (contain correct (mono ao v) mx on)
  apply pureOfLarge mx
  omega

end PEqualNP.Outside.L_meta_8089.Grid
