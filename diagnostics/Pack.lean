import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Narrow4785

abbrev Col := Finset (Fin 58)
abbrev Pool := Finset Col

def Op (I : Pool) (z : Col) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, z = a ∪ b ∨ z = a ∩ b

lemma opGrow {I J : Pool} {z : Col} (sub : I ⊆ J) (h : Op I z) : Op J z := by
  obtain ⟨a,ha,b,hb,h⟩ := h
  exact ⟨a,sub ha,b,sub hb,h⟩

def Scan (f : Pool → Col → Prop) (I : Pool) : List Col → Prop
  | [] => True
  | x::xs => f I x ∧ Scan f (insert x I) xs

lemma scanSplits (f : Pool → Col → Prop) (S : List Col) (I : Pool) :
    Scan f I S ↔ ∀ (a b : List Col) (z : Col), S = a ++ z :: b → f (I ∪ a.toFinset) z := by
  induction S generalizing I with
  | nil =>
    constructor
    · intro _ a b z eq
      cases a <;> simp at eq
    · intro _
      trivial
  | cons x xs ih =>
    constructor
    · rintro ⟨first,tail⟩ a b z eq
      cases a with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at eq
        simpa [← eq.1] using first
      | cons h a =>
        simp only [List.cons_append,List.cons.injEq] at eq
        obtain ⟨rfl,he⟩ := eq
        have given := (ih (insert x I)).1 tail a b z he
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using given
    · intro splits
      constructor
      · simpa using splits [] xs x rfl
      · apply (ih (insert x I)).2
        intro a b z eq
        have given := splits (x::a) b z (by simp [eq])
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using given

def Low (P z : Col) := z ⊆ P ∧ z.card ≤ 1
def Allowed (P : Col) (I : Pool) (z : Col) := Low P z ∨ (2 ≤ (z ∩ P).card ∧ Op I z)
def High (P : Col) (I : Pool) (z : Col) := 2 ≤ (z ∩ P).card ∧ Op I z
def atoms (A : Col) : Pool := A.image (fun q => {q})
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma snoc {α : Type*} (w : List α) (b d : α) (i : ℕ) :
    (w ++ [b]).getD i d = if i = w.length then b else w.getD i d := by
  by_cases lt : i < w.length
  · rw [List.getD_append _ _ _ _ lt,if_neg (Nat.ne_of_lt lt)]
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt lt)]
    by_cases eq : i=w.length
    · subst i
      simp
    · have h : 1 ≤ i-w.length := by omega
      rw [if_neg eq,List.getD_eq_default _ _ (by simpa using h),List.getD_eq_default _ _ (Nat.le_of_not_gt lt)]

lemma avail (V : List Col) (I : Pool) (z : ∅ ∈ I) (sub : ∀ a ∈ V, a ∈ I) (i : ℕ) :
    V.getD i ∅ ∈ I := by
  by_cases lt : i<V.length
  · rw [List.getD_eq_getElem _ _ lt]
    exact sub _ (List.getElem_mem lt)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt lt)]
    exact z

def raw (g : Gate) (V : List Col) : Col := Finset.univ.filter (fun k =>
  g.op.eval (g.inputs.map fun i => decide (k ∈ V.getD i ∅))=true)

lemma rawOp (g : Gate) (V : List Col) (I : Pool) (zero : ∅ ∈ I) (one : Finset.univ ∈ I)
    (sub : ∀ a ∈ V, a ∈ I) (hop : g.op=GateOp.and ∨ g.op=GateOp.or) (hs : g.inputs.length ≤ 2) :
    Op I (raw g V) := by
  have get := avail V I zero sub
  cases h : g.inputs with
  | nil =>
    rcases hop with o|o
    · refine ⟨Finset.univ,one,Finset.univ,one,Or.inl ?_⟩
      ext k
      simp [raw,h,o,GateOp.eval]
    · refine ⟨∅,zero,∅,zero,Or.inl ?_⟩
      ext k
      simp [raw,h,o,GateOp.eval]
  | cons a rest =>
    cases rest with
    | nil =>
      refine ⟨_,get a,_,get a,Or.inl ?_⟩
      ext k
      rcases hop with o|o <;> simp [raw,h,o,GateOp.eval]
    | cons b rem =>
      have empty : rem=[] := by rw [h] at hs; cases rem <;> simp_all
      subst rem
      refine ⟨_,get a,_,get b,?_⟩
      rcases hop with o|o
      · right
        ext k
        simp [raw,h,o,GateOp.eval]
      · left
        ext k
        simp [raw,h,o,GateOp.eval]

lemma gateGrow (g : Gate) (hop : g.op=GateOp.and ∨ g.op=GateOp.or) (f h : ℕ → Bool)
    (up : ∀ i, f i = true → h i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map h) = true := by
  rcases hop with o|o
  · simp only [o,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun x i hi => up i (x i hi)
  · simp only [o,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hf⟩
    exact ⟨i,hi,up i hf⟩

theorem simulate (P : Col) (gs : List Gate) (V : List Col) (W : Fin 58 → List Bool) (I : Pool)
    (zero : ∅ ∈ I) (one : Finset.univ ∈ I) (sub : ∀ a ∈ V, a ∈ I)
    (length : ∀ k, (W k).length = V.length)
    (lo : ∀ k i, k ∈ V.getD i ∅ → (W k).getD i false=true)
    (hi : ∀ k ∈ P, ∀ i, (W k).getD i false=true → k ∈ V.getD i ∅)
    (mon : ∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ S : List Col, S.length=gs.length ∧ Scan (Allowed P) I S ∧
      ∀ i, ∃ z ∈ I ∪ S.toFinset,
        (∀ k ∈ z, (gs.foldl step (W k)).getD i false=true) ∧
        (∀ k ∈ P, (gs.foldl step (W k)).getD i false=true → k ∈ z) := by
  induction gs generalizing V W I with
  | nil =>
    refine ⟨[],rfl,True.intro,?_⟩
    intro i
    exact ⟨V.getD i ∅,Finset.mem_union_left _ (avail V I zero sub i),fun k => lo k i,fun k hk => hi k hk i⟩
  | cons g gs ih =>
    obtain ⟨hop,arity⟩ := mon g List.mem_cons_self
    let Z := raw g V
    let cut := Z ∩ P
    let Y := if cut.card ≤ 1 then cut else Z
    let nw := fun k : Fin 58 => step (W k) g
    have allowed : Allowed P I Y := by
      by_cases small : cut.card ≤ 1
      · left
        rw [show Y=cut by simp [Y,small]]
        exact ⟨Finset.inter_subset_right,small⟩
      · right
        change 2 ≤ (Y ∩ P).card ∧ Op I Y
        rw [show Y=Z by simp [Y,small]]
        exact ⟨by change 2 ≤ cut.card; omega,rawOp g V I zero one sub hop arity⟩
    have less : Y ⊆ Z := by
      by_cases small : cut.card ≤ 1
      · simpa [Y,small,cut] using (Finset.inter_subset_left (s₁:=Z) (s₂:=P))
      · simp [Y,small]
    have keep (k : Fin 58) (hk : k ∈ P) (hz : k ∈ Z) : k ∈ Y := by
      by_cases small : cut.card ≤ 1 <;> simp [Y,cut,small,hz,hk]
    have valLo (k : Fin 58) (hk : k ∈ Y) :
        g.op.eval (g.inputs.map (fun i => (W k).getD i false))=true := by
      have z := (Finset.mem_filter.mp (less hk)).2
      exact gateGrow g hop _ _ (fun i hit => lo k i (of_decide_eq_true hit)) z
    have valHi (k : Fin 58) (hk : k ∈ P)
        (hw : g.op.eval (g.inputs.map (fun i => (W k).getD i false))=true) : k ∈ Y := by
      apply keep k hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      exact gateGrow g hop _ _ (fun i hit => decide_eq_true (hi k hk i hit)) hw
    have nlo (k : Fin 58) (i : ℕ) : k ∈ (V++[Y]).getD i ∅ → (nw k).getD i false=true := by
      by_cases eq : i = V.length <;> simp only [nw,step,snoc,length,eq,if_true,if_false]
      · exact valLo k
      · exact lo k i
    have nhi (k : Fin 58) (hk : k∈P) (i : ℕ) : (nw k).getD i false=true → k ∈ (V++[Y]).getD i ∅ := by
      by_cases eq : i = V.length <;> simp only [nw,step,snoc,length,eq,if_true,if_false]
      · exact valHi k hk
      · exact hi k hk i
    obtain ⟨S,sz,prog,last⟩ := ih (V++[Y]) nw (insert Y I)
      (Finset.mem_insert_of_mem zero) (Finset.mem_insert_of_mem one)
      (by intro a ha; rcases List.mem_append.mp ha with h|h
          · exact Finset.mem_insert_of_mem (sub a h)
          · have eq : a=Y := by simpa using h
            exact Finset.mem_insert.mpr (Or.inl eq))
      (by intro k; simp [nw,step,length]) nlo nhi (fun a ha => mon a (List.mem_cons_of_mem g ha))
    refine ⟨Y::S,by simpa using sz,⟨allowed,prog⟩,?_⟩
    intro i
    obtain ⟨z,hz,below,above⟩ := last i
    refine ⟨z,?_,below,above⟩
    simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hz

lemma readCols (cols : List Col) (k : Fin 58) (i : ℕ) :
    (cols.map (fun z => decide (k ∈ z))).getD i false = decide (k ∈ cols.getD i ∅) := by
  by_cases lt : i<cols.length
  · rw [List.getD_eq_getElem _ _ (by simpa using lt),List.getD_eq_getElem _ _ lt]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
    simp

theorem packChild : let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
      let op := fun (M : Finset (Finset (Fin 58))) (z : Finset (Fin 58)) =>
        ∃ a ∈ M, ∃ b ∈ M, z = a ∪ b ∨ z = a ∩ b
      let low := fun z : Finset (Fin 58) => z ⊆ P ∧ z.card ≤ 1
      ∀ (cols : List (Finset (Fin 58))) (C : Circuit), Monotone2 C →
        (∀ k : Fin 58, C.eval (cols.map (fun z => decide (k ∈ z))) = true ↔ k ∈ P) →
        let I := insert ∅ (insert Finset.univ cols.toFinset)
        ∃ S : List (Finset (Fin 58)), S.length ≤ C.size ∧
        (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), S = u ++ z :: v →
          low z ∨ (2 ≤ (z ∩ P).card ∧ op (I ∪ u.toFinset) z)) ∧ P ∈ I ∪ S.toFinset := by
  let P : Col := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
  change ∀ (cols : List Col) (C : Circuit), Monotone2 C →
    (∀ k : Fin 58, C.eval (cols.map (fun z => decide (k ∈ z))) = true ↔ k ∈ P) →
    let I := insert ∅ (insert Finset.univ cols.toFinset)
    ∃ S : List Col, S.length ≤ C.size ∧
      (∀ (u v : List Col) (z : Col), S=u ++ z::v → Allowed P (I ∪ u.toFinset) z) ∧ P ∈ I ∪ S.toFinset
  intro cols C hm correct I
  let W := fun k : Fin 58 => cols.map (fun z => decide (k∈z))
  obtain ⟨S,length,prog,out⟩ := simulate P C.gates cols W I
    (by simp [I]) (by simp [I]) (by intro a h; simp [I,h])
    (by simp [W])
    (by intro k i h; simpa only [W,readCols,decide_eq_true_eq] using h)
    (by intro k hk i h; simpa only [W,readCols,decide_eq_true_eq] using h)
    (fun g hg => ⟨(hm g hg).1,(hm g hg).2⟩)
  obtain ⟨z,mem,lo,hi⟩ := out C.output
  have same : z=P := by
    ext k
    exact ⟨fun h => (correct k).1 (lo k h),fun h => hi k h ((correct k).2 h)⟩
  exact ⟨S,length.le,(scanSplits _ _ _).1 prog,same ▸ mem⟩

end Narrow4785
