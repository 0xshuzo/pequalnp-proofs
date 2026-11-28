import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17661

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

abbrev I := Fin 13
abbrev lines := singerLines3

theorem incidenceUp (C : Circuit) (mc : Monotone2 C)
    {A B A' B' : Finset I} (aa : A ⊆ A') (bb : B ⊆ B') :
    C.eval (incidenceInput A B) = true → C.eval (incidenceInput A' B') = true := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append,← List.ofFn_fin_append]
  apply cmono C mc
  intro j
  induction j using Fin.addCases with
  | left i => simpa only [Fin.append, Fin.addCases_left, Fin.addCases_right] using (show decide (i ∈ A) ≤ decide (i ∈ A') by
                          by_cases h : i ∈ A
                          · simp [h,aa h]
                          · simp [h])
  | right i => simpa only [Fin.append, Fin.addCases_left, Fin.addCases_right] using (show decide (i ∈ B) ≤ decide (i ∈ B') by
                          by_cases h : i ∈ B
                          · simp [h,bb h]
                          · simp [h])


def spoke (p : I) (i : Fin 4) : I := p + (![0, 4, 10, 12] : Fin 4 → I) i
def ray (p : I) (i : Fin 4) (t : Fin 3) : I :=
  p + (![![1, 3, 9], ![4, 5, 7], ![6, 10, 11], ![2, 8, 12]] : Fin 4 → Fin 3 → I) i t
def hits (p : I) (a b c d : Fin 3) : Finset I :=
  {ray p 0 a, ray p 1 b, ray p 2 c, ray p 3 d}
def badLine (p : I) (a b c d : Fin 3) : I :=
  p + ([1, 5, 3, 1, 1, 1, 1, 8, 11, 5, 5, 5, 1, 5, 9, 2, 5, 11, 6, 5, 11, 1, 7, 11, 11, 11, 11, 3, 3, 3, 1, 7, 3, 2, 8, 3, 2, 5, 3, 2, 7, 9, 2, 2, 2, 6, 7, 3, 7, 7, 7, 2, 7, 11, 6, 8, 3, 1, 8, 9, 8, 8, 8, 6, 5, 9, 9, 9, 9, 2, 8, 9, 6, 6, 6, 6, 7, 9, 6, 8, 11] : List I).getD (27*a.val+9*b.val+3*c.val+d.val) 0

theorem spokes : ∀ (p : I) (i : Fin 4),
    lines (spoke p i) = {p, ray p i 0, ray p i 1, ray p i 2} := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash0 : ∀ a b c d : Fin 3, 3 ≤ (hits 0 a b c d ∩ lines (badLine 0 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash1 : ∀ a b c d : Fin 3, 3 ≤ (hits 1 a b c d ∩ lines (badLine 1 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash2 : ∀ a b c d : Fin 3, 3 ≤ (hits 2 a b c d ∩ lines (badLine 2 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash3 : ∀ a b c d : Fin 3, 3 ≤ (hits 3 a b c d ∩ lines (badLine 3 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash4 : ∀ a b c d : Fin 3, 3 ≤ (hits 4 a b c d ∩ lines (badLine 4 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash5 : ∀ a b c d : Fin 3, 3 ≤ (hits 5 a b c d ∩ lines (badLine 5 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash6 : ∀ a b c d : Fin 3, 3 ≤ (hits 6 a b c d ∩ lines (badLine 6 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash7 : ∀ a b c d : Fin 3, 3 ≤ (hits 7 a b c d ∩ lines (badLine 7 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash8 : ∀ a b c d : Fin 3, 3 ≤ (hits 8 a b c d ∩ lines (badLine 8 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash9 : ∀ a b c d : Fin 3, 3 ≤ (hits 9 a b c d ∩ lines (badLine 9 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash10 : ∀ a b c d : Fin 3, 3 ≤ (hits 10 a b c d ∩ lines (badLine 10 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash11 : ∀ a b c d : Fin 3, 3 ≤ (hits 11 a b c d ∩ lines (badLine 11 a b c d)).card := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem clash12 : ∀ a b c d : Fin 3, 3 ≤ (hits 12 a b c d ∩ lines (badLine 12 a b c d)).card := by decide

theorem clash (p : I) (a b c d : Fin 3) :
    3 ≤ (hits p a b c d ∩ lines (badLine p a b c d)).card := by
  fin_cases p
  · exact clash0 a b c d
  · exact clash1 a b c d
  · exact clash2 a b c d
  · exact clash3 a b c d
  · exact clash4 a b c d
  · exact clash5 a b c d
  · exact clash6 a b c d
  · exact clash7 a b c d
  · exact clash8 a b c d
  · exact clash9 a b c d
  · exact clash10 a b c d
  · exact clash11 a b c d
  · exact clash12 a b c d

theorem outside_hits {Q : Finset I} (arc : ∀ l, (Q ∩ lines l).card ≤ 2)
    {p : I} (out : p ∉ Q) : ∃ l ∈ missLines lines Q, p ∈ lines l := by
  classical
  by_contra! no
  have pick (i : Fin 4) : ∃ t : Fin 3, ray p i t ∈ Q := by
    have on : p ∈ lines (spoke p i) := by rw [spokes]; simp
    have h : spoke p i ∉ missLines lines Q := fun bad => no _ bad on
    have nd : ¬ Disjoint (lines (spoke p i)) Q := by simpa [missLines] using h
    obtain ⟨q, hq, inQ⟩ := Finset.not_disjoint_iff.mp nd
    rw [spokes] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with eq | eq | eq | eq
    · exact (out (eq ▸ inQ)).elim
    · exact ⟨0, eq ▸ inQ⟩
    · exact ⟨1, eq ▸ inQ⟩
    · exact ⟨2, eq ▸ inQ⟩
  obtain ⟨a,ha⟩ := pick 0
  obtain ⟨b,hb⟩ := pick 1
  obtain ⟨c,hc⟩ := pick 2
  obtain ⟨d,hd⟩ := pick 3
  have sub : hits p a b c d ⊆ Q := by simpa [hits] using And.intro ha ⟨hb,hc,hd⟩
  have hle := Finset.card_le_card (Finset.inter_subset_inter sub (Finset.Subset.refl (lines (badLine p a b c d))))
  have hlo := clash p a b c d
  have hup := arc (badLine p a b c d)
  omega

theorem proper_cube (C : Circuit) (mc : Monotone2 C) (pos : RightOnIncidentPairs lines C)
    {Q A B : Finset I} (arc : ∀ l, (Q ∩ lines l).card ≤ 2)
    (qa : Q ⊆ A) (mb : missLines lines Q ⊆ B)
    (strict : A ≠ Q ∨ B ≠ missLines lines Q) :
    C.eval (incidenceInput A B) = true := by
  classical
  have suff (p l : I) (hp : p ∈ A) (hl : l ∈ B) (flag : p ∈ lines l) :
      C.eval (incidenceInput A B) = true :=
    incidenceUp C mc (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (pos l p flag)
  rcases strict with h | h
  · have ns : ¬ A ⊆ Q := fun rev => h (Finset.Subset.antisymm rev qa)
    obtain ⟨p,hp,out⟩ := Finset.not_subset.mp ns
    obtain ⟨l,hl,flag⟩ := outside_hits arc out
    exact suff p l hp (mb hl) flag
  · have ns : ¬ B ⊆ missLines lines Q := fun rev => h (Finset.Subset.antisymm rev mb)
    obtain ⟨l,hl,out⟩ := Finset.not_subset.mp ns
    have nd : ¬ Disjoint (lines l) Q := by simpa [missLines] using out
    obtain ⟨p,flag,hp⟩ := Finset.not_disjoint_iff.mp nd
    exact suff p l (qa hp) hl flag

theorem sharp_cube (C : Circuit) (mc : Monotone2 C) (pos : RightOnIncidentPairs lines C)
    {Q : Finset I} (hQ : Q ∈ quadrangles lines)
    (rejects : C.eval (incidenceInput Q (missLines lines Q)) = false)
    (A B : Finset I) (qa : Q ⊆ A) (mb : missLines lines Q ⊆ B) :
    C.eval (incidenceInput A B) = true ↔ A ≠ Q ∨ B ≠ missLines lines Q := by
  constructor
  · intro accept
    by_contra! h
    rw [h.1,h.2,rejects] at accept
    contradiction
  · exact proper_cube C mc pos (Finset.mem_filter.mp hQ).2 qa mb

end PEqualNP.Outside.L_meta_17661
