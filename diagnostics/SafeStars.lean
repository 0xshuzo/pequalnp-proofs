import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18065.Stars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The star circuit of a vertex cover of a bipartite edge set: every cover vertex with at
-- least one assigned edge gets an OR chain of its assigned neighbours ANDed with the vertex,
-- and the stars are ORed together. All gates have exactly two operands.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_length (gs : List Gate) (w : List Bool) : (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wf]
  | cons g gs ih =>
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

lemma wf_append (gs hs : List Gate) (w : List Bool) : wf (gs ++ hs) w = wf hs (wf gs w) := by
  simp [wf, List.foldl_append]

lemma wf_getD_lt (hs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf hs w).getD i false = w.getD i false := by
  induction hs generalizing w with
  | nil => rfl
  | cons g hs ih =>
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ hi]

def val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wf gs (List.ofFn x)).getD w false

def inp {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool := (List.ofFn x).getD i false

lemma val_old (n : ℕ) (gs hs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + gs.length) :
    val n (gs ++ hs) x w = val n gs x w := by
  unfold val
  rw [wf_append]
  exact wf_getD_lt _ _ _ (by rw [wf_length]; simpa using hw)

lemma val_new (n : ℕ) (gs : List Gate) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    val n (gs ++ [⟨op, [a, b]⟩]) x (n + gs.length) = op.eval [val n gs x a, val n gs x b] := by
  unfold val
  rw [wf_append]
  have hl : (wf gs (List.ofFn x)).length = n + gs.length := by rw [wf_length]; simp
  have e : wf [⟨op, [a, b]⟩] (wf gs (List.ofFn x)) = wf gs (List.ofFn x) ++
      [op.eval [(wf gs (List.ofFn x)).getD a false, (wf gs (List.ofFn x)).getD b false]] := rfl
  rw [e, ← hl, List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma val_lt (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val n gs x i = inp x i := by
  unfold val inp
  exact wf_getD_lt _ _ _ (by simpa using hi)

lemma inp_of_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) : inp x i = x ⟨i, hi⟩ := by
  unfold inp
  simp [List.getD_eq_getElem?_getD, hi]

def OK (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : OK n gs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) : OK n (gs ++ [⟨op, [a, b]⟩]) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h.1 g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hop, rfl⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hi
      exact h.2 j hj i hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl <;> assumption

lemma any_congr' {f g : ℕ → Bool} (ws : List ℕ) (h : ∀ w ∈ ws, f w = g w) :
    ws.any f = ws.any g := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.any_cons]
    rw [h w List.mem_cons_self, ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]


def Safe (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∀ x, val n gs x (n+j) = true → P x

def Aug (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) := OK n gs ∧ Safe n P gs

lemma augSnoc {n : ℕ} {P : (Fin n → Bool) → Prop} {gs : List Gate} (h : Aug n P gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (guard : op = GateOp.and → ∀ x, op.eval [val n gs x a, val n gs x b] = true → P x) :
    Aug n P (gs ++ [⟨op, [a,b]⟩]) := by
  refine ⟨ok_snoc h.1 op hop a b ha hb, ?_⟩
  intro j hj hand x hx
  simp only [List.length_append, List.length_singleton] at hj
  by_cases old : j < gs.length
  · rw [List.getD_append _ _ _ _ old] at hand
    rw [val_old n gs _ x (n+j) (by omega)] at hx
    exact h.2 j old hand x hx
  · have eq : j = gs.length := by omega
    subst j
    rw [List.getD_append_right _ _ _ _ le_rfl] at hand
    simp only [Nat.sub_self, List.getD_cons_zero] at hand
    rw [val_new] at hx
    exact guard hand x hx

lemma orAcc (n : ℕ) (P : (Fin n → Bool) → Prop) : ∀ (ws : List ℕ) (gs : List Gate) (o : ℕ), Aug n P gs → o < n + gs.length →
    (∀ w ∈ ws, w < n + gs.length) →
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧ ext.length = ws.length ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' = (val n gs x o || ws.any (fun w => val n gs x w)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs o h ho _
    exact ⟨[], o, by simpa using h, rfl, by simpa using ho, fun x => by simp⟩
  | cons w ws ih =>
    intro gs o h ho hws
    have hw := hws w List.mem_cons_self
    have h1 := augSnoc h GateOp.or (Or.inr rfl) o w ho hw (by intro hk; cases hk)
    obtain ⟨ext, o', hok, hlen, ho', hv⟩ := ih (gs ++ [⟨GateOp.or, [o, w]⟩]) (n + gs.length) h1
      (by simp) (fun w' hw' => by
        have := hws w' (List.mem_cons_of_mem _ hw')
        simp only [List.length_append, List.length_singleton]
        omega)
    have e : gs ++ (⟨GateOp.or, [o, w]⟩ : Gate) :: ext = (gs ++ [⟨GateOp.or, [o, w]⟩]) ++ ext := by
      simp
    refine ⟨⟨GateOp.or, [o, w]⟩ :: ext, o', by rw [e]; exact hok, by simp [hlen],
      by rw [e]; exact ho', fun x => ?_⟩
    rw [e, hv x, val_new]
    rw [any_congr' ws (fun w' hw' => val_old n gs _ x w' (hws w' (List.mem_cons_of_mem _ hw')))]
    simp [GateOp.eval, Bool.or_assoc]

lemma star (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) (c w0 : ℕ) (ws : List ℕ) (h : Aug n P gs)
    (hc : c < n + gs.length) (hw0 : w0 < n + gs.length) (hws : ∀ w ∈ ws, w < n + gs.length) (paid : ∀ x, (val n gs x c && (val n gs x w0 || ws.any (fun w => val n gs x w))) = true → P x) :
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧ ext.length = ws.length + 1 ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' =
        (val n gs x c && (val n gs x w0 || ws.any (fun w => val n gs x w))) := by
  obtain ⟨ext, o1, hok, hlen, ho1, hv⟩ := orAcc n P ws gs w0 h hw0 hws
  have hc' : c < n + (gs ++ ext).length := by
    simp only [List.length_append]
    omega
  refine ⟨ext ++ [⟨GateOp.and, [c, o1]⟩], n + (gs ++ ext).length, ?_, by simp [hlen], ?_,
    fun x => ?_⟩
  · rw [← List.append_assoc]
    apply augSnoc hok GateOp.and (Or.inl rfl) c o1 hc' ho1
    intro _ x hit
    apply paid x
    simpa [GateOp.eval, val_old n gs ext x c hc, hv x] using hit
  · simp only [List.length_append, List.length_singleton]
    omega
  · rw [← List.append_assoc, val_new, hv x, val_old n gs ext x c hc]
    simp [GateOp.eval]

def starVal {n : ℕ} (x : Fin n → Bool) (s : ℕ × List ℕ) : Bool :=
  inp x s.1 && s.2.any (inp x)

lemma star_val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (s : ℕ × List ℕ) (w0 : ℕ)
    (ws : List ℕ) (hsw : s.2 = w0 :: ws) (h1 : s.1 < n) (h3 : ∀ w ∈ s.2, w < n) :
    (val n gs x s.1 && (val n gs x w0 || ws.any (fun w => val n gs x w))) = starVal x s := by
  unfold starVal
  rw [hsw] at h3 ⊢
  rw [val_lt n gs x s.1 h1, val_lt n gs x w0 (h3 w0 List.mem_cons_self),
    any_congr' ws (fun w hw => val_lt n gs x w (h3 w (List.mem_cons_of_mem _ hw)))]
  simp

lemma starsAcc (n : ℕ) (P : (Fin n → Bool) → Prop) : ∀ (sts : List (ℕ × List ℕ)) (gs : List Gate) (o : ℕ), Aug n P gs →
    o < n + gs.length → (∀ s ∈ sts, s.1 < n ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < n) →
    (∀ s ∈ sts, ∀ x, starVal x s = true → P x) →
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧
      ext.length = (sts.map (fun s => s.2.length)).sum + sts.length ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' = (val n gs x o || sts.any (starVal x)) := by
  intro sts
  induction sts with
  | nil =>
    intro gs o h ho _ _
    exact ⟨[], o, by simpa using h, rfl, by simpa using ho, fun x => by simp⟩
  | cons s sts ih =>
    intro gs o h ho hs paid
    obtain ⟨hs1, hs2, hs3⟩ := hs s List.mem_cons_self
    obtain ⟨w0, ws, hsw⟩ := List.exists_cons_of_ne_nil hs2
    have hw0 : w0 < n := hs3 w0 (by rw [hsw]; exact List.mem_cons_self)
    have hws : ∀ w ∈ ws, w < n := fun w hw => hs3 w (by rw [hsw]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨e1, o1, hok1, hl1, ho1, hv1⟩ := star n P gs s.1 w0 ws h (by omega) (by omega)
      (fun w hw => by have := hws w hw; omega)
      (fun x hx => paid s List.mem_cons_self x (by rwa [← star_val n gs x s w0 ws hsw hs1 hs3]))
    have ho' : o < n + (gs ++ e1).length := by
      simp only [List.length_append]
      omega
    have h2 := augSnoc hok1 GateOp.or (Or.inr rfl) o o1 ho' ho1 (by intro hk; cases hk)
    obtain ⟨e2, o2, hok2, hl2, ho2, hv2⟩ := ih (gs ++ e1 ++ [⟨GateOp.or, [o, o1]⟩])
      (n + (gs ++ e1).length) h2 (by simp) (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
      (fun s' hs' => paid s' (List.mem_cons_of_mem _ hs'))
    have e : gs ++ (e1 ++ [(⟨GateOp.or, [o, o1]⟩ : Gate)] ++ e2) =
        (gs ++ e1 ++ [⟨GateOp.or, [o, o1]⟩]) ++ e2 := by simp
    refine ⟨e1 ++ [⟨GateOp.or, [o, o1]⟩] ++ e2, o2, by rw [e]; exact hok2, ?_,
      by rw [e]; exact ho2, fun x => ?_⟩
    · simp only [List.length_append, List.length_singleton, hl1, hl2, List.map_cons,
        List.sum_cons, List.length_cons, List.length_nil, hsw]
      omega
    · rw [e, hv2 x, val_new, hv1 x, val_old n gs e1 x o ho,
        star_val n gs x s w0 ws hsw hs1 hs3]
      simp [GateOp.eval, Bool.or_assoc]

lemma build (n : ℕ) (P : (Fin n → Bool) → Prop) (sts : List (ℕ × List ℕ)) (hne : sts ≠ [])
    (hs : ∀ s ∈ sts, s.1 < n ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < n)
    (paid : ∀ s ∈ sts, ∀ x, starVal x s = true → P x) :
    ∃ (gs : List Gate) (o : ℕ), Aug n P gs ∧
      gs.length + 1 = (sts.map (fun s => s.2.length)).sum + sts.length ∧
      ∀ x, val n gs x o = sts.any (starVal x) := by
  obtain ⟨s, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hs1, hs2, hs3⟩ := hs s List.mem_cons_self
  obtain ⟨w0, ws, hsw⟩ := List.exists_cons_of_ne_nil hs2
  have hw0 : w0 < n := hs3 w0 (by rw [hsw]; exact List.mem_cons_self)
  have hws : ∀ w ∈ ws, w < n := fun w hw => hs3 w (by rw [hsw]; exact List.mem_cons_of_mem _ hw)
  have h0 : Aug n P [] := ⟨⟨by simp, by simp⟩, by intro j hj; simp at hj⟩
  obtain ⟨e1, o1, hok1, hl1, ho1, hv1⟩ := star n P [] s.1 w0 ws h0 (by simpa using hs1)
    (by simpa using hw0) (fun w hw => by simpa using hws w hw)
    (fun x hx => paid s List.mem_cons_self x (by rwa [← star_val n [] x s w0 ws hsw hs1 hs3]))
  obtain ⟨e2, o2, hok2, hl2, ho2, hv2⟩ := starsAcc n P rest ([] ++ e1) o1 hok1 ho1
    (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    (fun s' hs' => paid s' (List.mem_cons_of_mem _ hs'))
  refine ⟨[] ++ e1 ++ e2, o2, hok2, ?_, fun x => ?_⟩
  · simp only [List.length_append, List.length_nil, hl1, hl2, List.map_cons, List.sum_cons,
      List.length_cons, hsw]
    omega
  · rw [hv2 x, hv1 x, star_val n [] x s w0 ws hsw hs1 hs3]
    simp

noncomputable def stP (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) : List (ℕ × List ℕ) :=
  P.toList.map (fun a => (a.val,
    (((F.filter (fun e => e.1 ∈ P)).filter (fun e => e.1 = a)).toList.map
      (fun e => p + e.2.val))))

noncomputable def stL (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)) :
    List (ℕ × List ℕ) :=
  L.toList.map (fun b => (p + b.val,
    (((F.filter (fun e => e.1 ∉ P)).filter (fun e => e.2 = b)).toList.map
      (fun e => e.1.val))))

noncomputable def sts (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)) :
    List (ℕ × List ℕ) :=
  (stP p l F P ++ stL p l F P L).filter (fun s => !s.2.isEmpty)

lemma not_isEmpty_of_mem {ws : List ℕ} {w : ℕ} (h : w ∈ ws) : (!ws.isEmpty) = true := by
  cases ws with
  | nil => simp at h
  | cons a t => rfl

lemma sts_wires (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) :
    ∀ s ∈ sts p l F P L, s.1 < p + l ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < p + l := by
  intro s hs
  simp only [sts, List.mem_filter, List.mem_append, stP, stL, List.mem_map,
    Finset.mem_toList] at hs
  obtain ⟨hmem, hne⟩ := hs
  have hne' : s.2 ≠ [] := by
    intro h
    simp [h] at hne
  rcases hmem with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
  · refine ⟨?_, hne', ?_⟩
    · show a.val < p + l
      have := a.isLt
      omega
    · intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨e, _, rfl⟩ := hw
      have := e.2.isLt
      omega
  · refine ⟨?_, hne', ?_⟩
    · show p + b.val < p + l
      have := b.isLt
      omega
    · intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨e, _, rfl⟩ := hw
      have := e.1.isLt
      omega

lemma sts_len (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) : (sts p l F P L).length ≤ P.card + L.card := by
  calc (sts p l F P L).length ≤ (stP p l F P ++ stL p l F P L).length :=
        List.length_filter_le _ _
    _ = P.card + L.card := by simp [stP, stL]

lemma filter_sum (ss : List (ℕ × List ℕ)) :
    ((ss.filter (fun s => !s.2.isEmpty)).map (fun s => s.2.length)).sum =
      (ss.map (fun s => s.2.length)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases hs : s.2 with
    | nil => simp [hs, ih]
    | cons a t => simp [hs, ih]

lemma sts_sum (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) :
    ((sts p l F P L).map (fun s => s.2.length)).sum = F.card := by
  unfold sts
  rw [filter_sum]
  have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (s := F.filter (fun e => e.1 ∈ P)) (t := P) (fun e he => (Finset.mem_filter.mp he).2)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
    (s := F.filter (fun e => e.1 ∉ P)) (t := L) (fun e he => by
      have he' := Finset.mem_filter.mp he
      exact (hcov e he'.1).resolve_left he'.2)
  have h3 := Finset.card_filter_add_card_filter_not (s := F) (fun e => e.1 ∈ P)
  simp only [List.map_append, List.sum_append, stP, stL, List.map_map, Function.comp_def,
    List.length_map, Finset.length_toList, Finset.sum_map_toList]
  omega

lemma sts_mem (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) (a : Fin p) (b : Fin l)
    (hab : (a, b) ∈ F) :
    ∃ s ∈ sts p l F P L, (s.1 = a.val ∧ p + b.val ∈ s.2) ∨ (s.1 = p + b.val ∧ a.val ∈ s.2) := by
  by_cases ha : a ∈ P
  · have hm : p + b.val ∈ (((F.filter (fun e => e.1 ∈ P)).filter (fun e => e.1 = a)).toList.map
        (fun e => p + e.2.val)) :=
      List.mem_map.2 ⟨(a, b), Finset.mem_toList.2 (Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨hab, ha⟩, rfl⟩), rfl⟩
    refine ⟨(a.val, _), ?_, Or.inl ⟨rfl, hm⟩⟩
    refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inl ?_), not_isEmpty_of_mem hm⟩
    exact List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩
  · have hb : b ∈ L := (hcov (a, b) hab).resolve_left ha
    have hm : a.val ∈ (((F.filter (fun e => e.1 ∉ P)).filter (fun e => e.2 = b)).toList.map
        (fun e => e.1.val)) :=
      List.mem_map.2 ⟨(a, b), Finset.mem_toList.2 (Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨hab, ha⟩, rfl⟩), rfl⟩
    refine ⟨(p + b.val, _), ?_, Or.inr ⟨rfl, hm⟩⟩
    refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inr ?_), not_isEmpty_of_mem hm⟩
    exact List.mem_map.2 ⟨b, Finset.mem_toList.2 hb, rfl⟩

lemma inp_cast {p l : ℕ} (x : Fin (p + l) → Bool) (a : Fin p) :
    inp x a.val = x (Fin.castAdd l a) := by
  have h : a.val < p + l := by
    have := a.isLt
    omega
  rw [inp_of_lt x a.val h]
  rfl

lemma inp_nat {p l : ℕ} (x : Fin (p + l) → Bool) (b : Fin l) :
    inp x (p + b.val) = x (Fin.natAdd p b) := by
  have h : p + b.val < p + l := by
    have := b.isLt
    omega
  rw [inp_of_lt x (p + b.val) h]
  rfl

lemma sts_sem (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) (x : Fin (p + l) → Bool) :
    (sts p l F P L).any (starVal x) = true ↔
      ∃ a b, (a, b) ∈ F ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
  constructor
  · intro h
    obtain ⟨s, hs, hv⟩ := List.any_eq_true.1 h
    simp only [starVal, Bool.and_eq_true, List.any_eq_true] at hv
    obtain ⟨hv1, w, hw, hv2⟩ := hv
    simp only [sts, List.mem_filter, List.mem_append, stP, stL, List.mem_map,
      Finset.mem_toList] at hs
    rcases hs.1 with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨e, ⟨⟨heF, _⟩, hea⟩, rfl⟩ := hw
      refine ⟨e.1, e.2, heF, ?_, ?_⟩
      · rw [← inp_cast x e.1, hea]
        exact hv1
      · rw [← inp_nat x e.2]
        exact hv2
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨e, ⟨⟨heF, _⟩, heb⟩, rfl⟩ := hw
      refine ⟨e.1, e.2, heF, ?_, ?_⟩
      · rw [← inp_cast x e.1]
        exact hv2
      · rw [← inp_nat x e.2, heb]
        exact hv1
  · rintro ⟨a, b, hab, hxa, hxb⟩
    obtain ⟨s, hs, hcase⟩ := sts_mem p l F P L hcov a b hab
    refine List.any_eq_true.2 ⟨s, hs, ?_⟩
    simp only [starVal, Bool.and_eq_true, List.any_eq_true]
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1, inp_cast]; exact hxa, p + b.val, h2, by rw [inp_nat]; exact hxb⟩
    · exact ⟨by rw [h1, inp_nat]; exact hxb, a.val, h2, by rw [inp_cast]; exact hxa⟩

lemma stars : ∀ (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)),
      F.Nonempty → (∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) →
      ∃ D : Circuit, IsAO2 (p+l) D ∧ D.size+1 ≤ F.card+P.card+L.card ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x, gateVal (p+l) D j x = true →
          ∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true) ∧
        ∀ x : Fin (p+l) → Bool, circuitFun (p+l) D x=decide (∃ a b, (a,b)∈F ∧
          x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true) := by
  intro p l F P L hF hcov
  have hne : sts p l F P L ≠ [] := by
    obtain ⟨⟨a, b⟩, hab⟩ := hF
    obtain ⟨s, hs, _⟩ := sts_mem p l F P L hcov a b hab
    exact List.ne_nil_of_mem hs
  obtain ⟨gs, o, hok, hlen, hval⟩  := build (p + l)
    (fun x => ∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
    (sts p l F P L) hne (sts_wires p l F P L)
    (fun st hst x hval => (sts_sem p l F P L hcov x).mp (List.any_eq_true.mpr ⟨st,hst,hval⟩))
  refine ⟨⟨gs, o⟩, ⟨fun g hg => (hok.1.1 g hg).1, fun j hj i hi => hok.1.2 j hj i hi,
    fun g hg => (hok.1.1 g hg).2⟩, ?_, ?_, fun x => ?_⟩
  · have h1 := sts_sum p l F P L hcov
    have h2 := sts_len p l F P L
    show gs.length + 1 ≤ F.card + P.card + L.card
    omega
  · intro j hj ha x hx
    apply hok.2 j hj _ x hx
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using ha
  · show val (p + l) gs x o = _
    rw [hval x]
    rw [Bool.eq_iff_iff, sts_sem p l F P L hcov x]
    simp


end PEqualNP.Outside.L_meta_18065.Stars
