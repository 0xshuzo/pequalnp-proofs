import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7911
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def DG (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) ((List.range n).map fun i => if i ∈ marked then 1 else 0)

def inp (n : ℕ) (z : ℕ → Bool) : List Bool := (List.range n).map z

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma DG_snoc (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (g : Gate) : DG n marked (gs ++ [g]) = DG n marked gs ++ [g.lineDegree (DG n marked gs)] := by
  simp [DG, List.foldl_append]

lemma W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma DG_len (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : (DG n marked gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [DG]
  | append_singleton gs g ih => rw [DG_snoc]; simp [ih]; omega

def Cert (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (k : ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  ∃ S : Finset ℕ, S.card ≤ k ∧ (∀ i ∈ S, i < n ∧ i ∈ marked ∧ z i = true) ∧
    ∀ z' : ℕ → Bool, (∀ i ∈ S, z' i = true) → (∀ i, i < n → i ∉ marked → z i = true → z' i = true) → P z'

lemma Cert.mono {n : ℕ} {marked : Finset ℕ} {z : ℕ → Bool} {k k' : ℕ} {P Q : (ℕ → Bool) → Prop} (h : Cert n marked z k P) (hk : k ≤ k') (hPQ : ∀ z', P z' → Q z') : Cert n marked z k' Q := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1.trans hk, h2, fun z' a b => hPQ z' (h3 z' a b)⟩

lemma Cert.and {n : ℕ} {marked : Finset ℕ} {z : ℕ → Bool} {k k' : ℕ} {P Q : (ℕ → Bool) → Prop} (h : Cert n marked z k P) (h' : Cert n marked z k' Q) : Cert n marked z (k + k') (fun z' => P z' ∧ Q z') := by
  obtain ⟨S, h1, h2, h3⟩ := h
  obtain ⟨T, g1, g2, g3⟩ := h'
  refine ⟨S ∪ T, (Finset.card_union_le S T).trans (by omega), ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h2 i hi
    · exact g2 i hi
  · intro z' a b
    exact ⟨h3 z' (fun i hi => a i (Finset.mem_union_left _ hi)) b, g3 z' (fun i hi => a i (Finset.mem_union_right _ hi)) b⟩

lemma Cert.true (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) : Cert n marked z 0 (fun _ => True) :=
  ⟨∅, by simp, by simp, fun _ _ _ => trivial⟩

lemma certAll (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (d : ℕ → ℕ) (R : ℕ → (ℕ → Bool) → Prop) (is : List ℕ) (h : ∀ i ∈ is, Cert n marked z (d i) (R i)) : Cert n marked z (is.map d).sum (fun z' => ∀ i ∈ is, R i z') := by
  induction is with
  | nil => exact (Cert.true n marked z).mono (by simp) (by simp)
  | cons a is ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun i hi => h i (by simp [hi]))
    exact (h1.and h2).mono (by simp) (by
      intro z' hz i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hz.1
      · exact hz.2 i hi)

lemma le_foldr_max (d : ℕ → ℕ) (is : List ℕ) (i : ℕ) (hi : i ∈ is) : d i ≤ (is.map d).foldr max 0 := by
  induction is with
  | nil => simp at hi
  | cons a is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · have := ih hi
      simp only [List.map_cons, List.foldr_cons]
      omega

lemma key (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : ∀ t, (W gs (inp n z)).getD t false = true → Cert n marked z ((DG n marked gs).getD t 0) (fun z' => (W gs (inp n z')).getD t false = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    have htn : t < n := by
      by_contra hc
      simp [W, inp, List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := (List.range n).map z) (i := t) (by simp; omega)] at ht
    have hz : z t = true := by
      simpa [W, inp, List.getD_eq_getElem?_getD, htn] using ht
    by_cases hmk : t ∈ marked
    · refine ⟨{t}, ?_, ?_, ?_⟩
      · simp [DG, List.getD_eq_getElem?_getD, htn, hmk]
      · simp [htn, hmk, hz]
      · intro z' a _
        simpa [W, inp, List.getD_eq_getElem?_getD, htn] using a t (by simp)
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro z' _ b
      simpa [W, inp, List.getD_eq_getElem?_getD, htn] using b t htn hmk hz
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : ∀ z'', (W gs (inp n z'')).length = n + gs.length := by
      intro z''
      rw [W_len]
      simp [inp]
    have hdl := DG_len n marked gs
    rcases Nat.lt_trichotomy t (n + gs.length) with hlt | heq | hgt
    · have e1 : ∀ z'', (W (gs ++ [g]) (inp n z'')).getD t false = (W gs (inp n z'')).getD t false := by
        intro z''
        rw [W_snoc, List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      have e2 : (DG n marked (gs ++ [g])).getD t 0 = (DG n marked gs).getD t 0 := by
        rw [DG_snoc, List.getD_append _ _ _ _ (by rw [hdl]; exact hlt)]
      rw [e1] at ht
      rw [e2]
      exact (ih' t ht).mono le_rfl (fun z' h => by rw [e1]; exact h)
    · subst heq
      have e1 : ∀ z'', (W (gs ++ [g]) (inp n z'')).getD (n + gs.length) false = g.op.eval (g.inputs.map fun i => (W gs (inp n z'')).getD i false) := by
        intro z''
        rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [hlen])]
        simp [hlen]
      have e2 : (DG n marked (gs ++ [g])).getD (n + gs.length) 0 = g.lineDegree (DG n marked gs) := by
        rw [DG_snoc, List.getD_append_right _ _ _ _ (by rw [hdl])]
        simp [hdl]
      rw [e1] at ht
      rw [e2]
      rcases hm g (by simp) with hop | hop
      · rw [hop] at ht
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at ht
        have hc := certAll n marked z (fun i => (DG n marked gs).getD i 0) (fun i z' => (W gs (inp n z')).getD i false = true) g.inputs (fun i hi => ih' i (ht i hi))
        refine hc.mono ?_ ?_
        · unfold Gate.lineDegree
          rw [if_pos hop]
        · intro z' hz
          rw [e1, hop]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
          exact hz
      · rw [hop] at ht
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at ht
        obtain ⟨i, hi, hti⟩ := ht
        refine (ih' i hti).mono ?_ ?_
        · unfold Gate.lineDegree
          rw [if_neg (by rw [hop]; intro h; cases h)]
          exact le_foldr_max (fun i => (DG n marked gs).getD i 0) g.inputs i hi
        · intro z' hz
          rw [e1, hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          exact ⟨i, hi, hz⟩
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_len]; simp [inp]; omega)] at ht
      simp at ht

def zf (X Y : Finset (Fin 13)) : ℕ → Bool := fun i =>
  if h : i < 13 then decide ((⟨i, h⟩ : Fin 13) ∈ X) else if h2 : i - 13 < 13 then decide ((⟨i - 13, h2⟩ : Fin 13) ∈ Y) else false

lemma ofFn_zf (X Y : Finset (Fin 13)) : (List.ofFn fun x5 : Fin 26 => Fin.addCases (fun x6 : Fin 13 => decide (x6 ∈ X)) (fun x6 : Fin 13 => decide (x6 ∈ Y)) x5) = inp 26 (zf X Y) := by
  apply List.ext_getElem
  · simp [inp]
  · intro i h1 h2
    have hi : i < 26 := by simpa using h1
    simp only [List.getElem_ofFn, inp, List.getElem_map, List.getElem_range, zf]
    by_cases h : i < 13
    · rw [dif_pos h]
      have : (⟨i, hi⟩ : Fin 26) = Fin.castAdd 13 (⟨i, h⟩ : Fin 13) := rfl
      rw [this, Fin.addCases_left]
    · rw [dif_neg h, dif_pos (by omega : i - 13 < 13)]
      have : (⟨i, hi⟩ : Fin 26) = Fin.natAdd 13 (⟨i - 13, by omega⟩ : Fin 13) := by
        ext
        simp
        omega
      rw [this, Fin.addCases_right]

lemma cf_eq (C : Circuit) (X Y : Finset (Fin 13)) : circuitFun 26 C (fun x5 : Fin 26 => Fin.addCases (fun x6 : Fin 13 => decide (x6 ∈ X)) (fun x6 : Fin 13 => decide (x6 ∈ Y)) x5) = (W C.gates (inp 26 (zf X Y))).getD C.output false := by
  rw [← ofFn_zf]
  rfl

abbrev Pt := Fin 13
def incidence (p l : Pt) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Pt) : Decidable (incidence p l) := by unfold incidence; infer_instance
abbrev vec (X Y : Finset Pt) (z : Fin 26) : Bool := Fin.addCases (motive:=fun _ => Bool) (fun i : Pt => decide (i∈X)) (fun i : Pt => decide (i∈Y)) z
def activeP (x : Fin 26 → Bool) := Finset.univ.filter (fun p : Pt => x (Fin.castAdd 13 p)=true)
def activeL (x : Fin 26 → Bool) := Finset.univ.filter (fun l : Pt => x (Fin.natAdd 13 l)=true)
theorem recover (x : Fin 26 → Bool) : vec (activeP x) (activeL x)=x := by
  funext i
  refine Fin.addCases (m:=13) (n:=13) (motive:=fun i => vec (activeP x) (activeL x) i=x i) ?_ ?_ i
  · intro p; rw [vec,Fin.addCases_left]; simp [activeP]
  · intro l; rw [vec,Fin.addCases_right]; simp [activeL]

def unwanted (C : Circuit) := ∃ X Y : Finset Pt,
  (∀ p∈X, ∀ l∈Y, ¬incidence p l) ∧ (∀ l, (X.filter (fun p => incidence p l)).card≤2) ∧
  (∀ p, (Y.filter (fun l => incidence p l)).card≤2) ∧ ∀ x : Fin 26 → Bool,
   (∀ p∈X, x (Fin.castAdd 13 p)=true) → (∀ l∈Y, x (Fin.natAdd 13 l)=true) → circuitFun 26 C x=true

def flag (p l : Pt) : Fin 26 → Bool := fun z => decide (z=Fin.castAdd 13 p ∨ z=Fin.natAdd 13 l)
def exactGraph (C : Circuit) := ∀ x : Fin 26 → Bool, circuitFun 26 C x=true ↔
  ∃ p l : Pt, incidence p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true

theorem shrink (C : Circuit) (hM : Monotone2 C) (dp : HasLineDegree 26 (Finset.range 13) C 2)
    (dl : HasLineDegree 26 (Finset.Ico 13 26) C 2) (X Y : Finset Pt) (ht : circuitFun 26 C (vec X Y)=true) :
    ∃ X0 Y0 : Finset Pt, X0.card≤2 ∧ Y0.card≤2 ∧ X0⊆X ∧ Y0⊆Y ∧
      ∀ x : Fin 26 → Bool, (∀ p∈X0,x (Fin.castAdd 13 p)=true) →
      (∀ l∈Y0,x (Fin.natAdd 13 l)=true) → circuitFun 26 C x=true := by
  have hT := (cf_eq C X Y).symm.trans ht
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  obtain ⟨S1, hS1c, hS1, hS1z⟩ := key 26 (Finset.Ico 13 26) (zf X Y) C.gates hm C.output hT
  have hS1c' : S1.card ≤ 2 := hS1c.trans dl
  let Y0 : Finset (Fin 13) := Finset.univ.filter (fun l => 13 + l.val ∈ S1)
  have hY0c : Y0.card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun l : Fin 13 => 13 + l.val) ?_ ?_) hS1c'
    · intro l hl
      simpa [Y0] using hl
    · intro a _ b _ hab
      apply Fin.ext
      simpa using hab
  have hY0Y : ∀ l ∈ Y0, l ∈ Y := by
    intro l hl
    have h1 : 13 + l.val ∈ S1 := by simpa [Y0] using hl
    have h2 := (hS1 _ h1).2.2
    have h3 : ¬ (13 + l.val < 13) := by omega
    have h4 : 13 + l.val - 13 < 13 := by omega
    simp only [zf, dif_neg h3, dif_pos h4, decide_eq_true_eq] at h2
    have : (⟨13 + l.val - 13, h4⟩ : Fin 13) = l := by
      apply Fin.ext
      simp
    rwa [this] at h2
  have hT1 : (W C.gates (inp 26 (zf X Y0))).getD C.output false = true := by
    apply hS1z
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hS1 i hi
      rw [Finset.mem_Ico] at h2
      have h4 : ¬ (i < 13) := by omega
      have h5 : i - 13 < 13 := by omega
      simp only [zf, dif_neg h4, dif_pos h5, decide_eq_true_eq]
      have : 13 + (i - 13) = i := by omega
      simp [Y0, this, hi]
    · intro i h1 h2 h3
      rw [Finset.mem_Ico] at h2
      have h4 : i < 13 := by omega
      simp only [zf, dif_pos h4] at h3 ⊢
      exact h3
  obtain ⟨S2, hS2c, hS2, hS2z⟩ := key 26 (Finset.range 13) (zf X Y0) C.gates hm C.output hT1
  have hS2c' : S2.card ≤ 2 := hS2c.trans dp
  let X0 : Finset (Fin 13) := Finset.univ.filter (fun p => p.val ∈ S2)
  have hX0c : X0.card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun p : Fin 13 => p.val) ?_ ?_) hS2c'
    · intro p hp
      simpa [X0] using hp
    · intro a _ b _ hab
      exact Fin.ext hab
  have hX0X : ∀ p ∈ X0, p ∈ X := by
    intro p hp
    have h1 : p.val ∈ S2 := by simpa [X0] using hp
    have h2 := (hS2 _ h1).2.2
    simp only [zf, dif_pos p.isLt, decide_eq_true_eq] at h2
    exact h2
  have hfin : ∀ X' Y' : Finset (Fin 13), (∀ p ∈ X0, p ∈ X') → (∀ l ∈ Y0, l ∈ Y') → (W C.gates (inp 26 (zf X' Y'))).getD C.output false = true := by
    intro X' Y' hX' hY'
    apply hS2z
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hS2 i hi
      rw [Finset.mem_range] at h2
      simp only [zf, dif_pos h2, decide_eq_true_eq]
      apply hX'
      simp [X0, hi]
    · intro i h1 h2 h3
      rw [Finset.mem_range] at h2
      have h5 : i - 13 < 13 := by omega
      simp only [zf, dif_neg h2, dif_pos h5, decide_eq_true_eq] at h3 ⊢
      exact hY' _ h3
  refine ⟨X0,Y0,hX0c,hY0c,hX0X,hY0Y,?_⟩
  intro x hx hy
  rw [←recover x,cf_eq]
  apply hfin
  · intro p hp; simpa [activeP] using hx p hp
  · intro l hl; simpa [activeL] using hy l hl

theorem mono_vec {C : Circuit} (hm : Monotone2 C) {X Y X' Y' : Finset Pt} (hx : X⊆X') (hy : Y⊆Y')
    (h : circuitFun 26 C (vec X Y)=true) : circuitFun 26 C (vec X' Y')=true := by
  have ht := (cf_eq C X Y).symm.trans h
  have hg : ∀ g∈C.gates, g.op=GateOp.and ∨ g.op=GateOp.or := fun g h => (hm g h).1
  obtain ⟨T,sz,mem,suff⟩ := key 26 ∅ (zf X Y) C.gates hg C.output ht
  rw [cf_eq]
  apply suff
  · intro i hi; exact (Finset.notMem_empty i (mem i hi).2.1).elim
  · intro i hi _ hv
    by_cases e : i<13
    · simpa only [zf,dif_pos e,decide_eq_true_eq] using hx (by simpa only [zf,dif_pos e,decide_eq_true_eq] using hv)
    · have b : i-13<13 := by omega
      simp only [zf,dif_neg e,dif_pos b,decide_eq_true_eq] at hv ⊢
      exact hy hv

theorem flagVec (p l : Pt) : flag p l=vec {p} {l} := by
  have all : ∀ p l : Pt, flag p l=vec {p} {l} := by decide +kernel
  exact all p l

theorem no_witness_iff {C : Circuit} (hm : Monotone2 C) (dp : HasLineDegree 26 (Finset.range 13) C 2)
    (dl : HasLineDegree 26 (Finset.Ico 13 26) C 2) (flags : ∀ p l, incidence p l → circuitFun 26 C (flag p l)=true) :
    ¬unwanted C ↔ exactGraph C := by
  constructor
  · intro h x
    constructor
    · intro hv
      by_contra neg
      obtain ⟨X,Y,cx,cy,hx,hy,yes⟩ := shrink C hm dp dl (activeP x) (activeL x) (by simpa [recover] using hv)
      apply h
      refine ⟨X,Y,?_,fun l => (Finset.card_filter_le ..).trans cx,fun p => (Finset.card_filter_le ..).trans cy,yes⟩
      intro p hp l hl ip
      exact neg ⟨p,l,ip,(Finset.mem_filter.mp (hx hp)).2,(Finset.mem_filter.mp (hy hl)).2⟩
    · rintro ⟨p,l,ip,hp,hl⟩
      have base := flags p l ip
      rw [flagVec] at base
      rw [←recover x]
      exact mono_vec hm (Finset.singleton_subset_iff.mpr (by simpa [activeP] using hp))
        (Finset.singleton_subset_iff.mpr (by simpa [activeL] using hl)) base
  · rintro f ⟨X,Y,bad,_,_,yes⟩
    have fire := yes (vec X Y) (fun p hp => by rw [vec,Fin.addCases_left]; simpa using hp) (fun l hl => by rw [vec,Fin.addCases_right]; simpa using hl)
    obtain ⟨p,l,inc,hp,hl⟩ := (f _).mp fire
    exact bad p (by simpa only [vec,Fin.addCases_left,decide_eq_true_eq] using hp) l (by simpa only [vec,Fin.addCases_right,decide_eq_true_eq] using hl) inc
end PEqualNP.Outside.L_meta_7911
