import PEqualNP.Defs

-- From the published L_meta_5355.
namespace PEqualNP.Outside.L_meta_18723.StarCompiler

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

theorem V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

theorem V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

theorem V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

theorem val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

theorem val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

theorem st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_⟩ <;> simp

theorem st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

theorem push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

theorem chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

theorem gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

theorem gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

theorem edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

theorem sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n D j u v := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, -, hB⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_⟩
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp [Circuit.size] at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      refine ⟨c, v, hadj, hj', hand, by rw [gv j hj']; exact h1, ?_⟩
      intro i hi _ hand'
      rw [gv i (by omega)]
      exact h2 i hi hand'

end PEqualNP.Outside.L_meta_18723.StarCompiler


namespace PEqualNP.Outside.L_meta_18723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp



def graphFn {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any fun e => x e.1 && x e.2

def zeroed {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ S then false else x i

theorem true_expand {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (x : Fin n → Bool) :
    graphFn E (Function.update x v true) = ((graphFn E (zeroed {v,u,w} x) || x u) || x w) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [graphFn, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, h, ha, hb⟩
    by_cases av : a = v
    · subst a
      rcases hn b (Or.inl h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using hb))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using hb)
    by_cases bv : b = v
    · subst b
      rcases hn a (Or.inr h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using ha))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using ha)
    have xa : x a = true := by simpa [Function.update_of_ne av] using ha
    have xb : x b = true := by simpa [Function.update_of_ne bv] using hb
    by_cases au : a = u
    · exact Or.inl (Or.inr (au ▸ xa))
    by_cases bu : b = u
    · exact Or.inl (Or.inr (bu ▸ xb))
    by_cases aw : a = w
    · exact Or.inr (aw ▸ xa)
    by_cases bw : b = w
    · exact Or.inr (bw ▸ xb)
    exact Or.inl (Or.inl ⟨(a,b),h,by simpa [zeroed,av,au,aw] using xa, by simpa [zeroed,bv,bu,bw] using xb⟩)
  · rintro ((⟨⟨a,b⟩,h,ha,hb⟩ | hu') | hw')
    · have lift (i : Fin n) (hi : zeroed {v,u,w} x i = true) : Function.update x v true i = true := by
        by_cases mem : i ∈ ({v,u,w} : Finset (Fin n))
        · simp [zeroed,mem] at hi
        · have nv : i ≠ v := by intro eq; subst i; simp at mem
          simpa [zeroed,mem,Function.update_of_ne nv] using hi
      exact ⟨(a,b),h,lift a ha,lift b hb⟩
    · rcases hu with h | h
      · exact ⟨(v,u),h,by simp,by simpa [Function.update_of_ne vu.symm] using hu'⟩
      · exact ⟨(u,v),h,by simpa [Function.update_of_ne vu.symm] using hu',by simp⟩
    · rcases hw with h | h
      · exact ⟨(v,w),h,by simp,by simpa [Function.update_of_ne vw.symm] using hw'⟩
      · exact ⟨(w,v),h,by simpa [Function.update_of_ne vw.symm] using hw',by simp⟩

def addPin (n : ℕ) (D : Circuit) (i : Fin n) : Circuit :=
  ⟨D.gates ++ [⟨.or,[D.output,i.val]⟩], n+D.size⟩

theorem addPin_size (D : Circuit) (i : Fin n) : (addPin n D i).size = D.size+1 := by
  simp [addPin,Circuit.size]

theorem addPin_fan (D : Circuit) (i : Fin n) (h : FanInTwo D) : FanInTwo (addPin n D i) := by
  intro g hg
  simp only [addPin,List.mem_append,List.mem_singleton] at hg
  rcases hg with hv | rfl
  · exact h g hv
  · simp

theorem addPin_eval (D : Circuit) (i : Fin n) (x : Fin n → Bool) :
    (addPin n D i).eval (List.ofFn x) = (D.eval (List.ofFn x) || x i) := by
  let W := wiresFrom D.gates (List.ofFn x)
  have len : W.length = n+D.size := by simp [W,length_wiresFrom,Circuit.size]
  have input : W.getD i.val false = x i := by
    obtain ⟨t,h,_⟩ := wiresFrom_prefix D.gates (List.ofFn x)
    dsimp [W]
    rw [h,List.getD_append _ _ _ _ (by simpa using i.isLt)]
    simp
  change (wiresFrom (D.gates++[⟨.or,[D.output,i.val]⟩]) (List.ofFn x)).getD (n+D.size) false = _
  rw [wiresFrom_append]
  change (W ++ [_]).getD (n+D.size) false = _
  rw [← len, getD_snoc_eq]
  change GateOp.or.eval [W.getD D.output false,W.getD i.val false] = _
  have old : W.getD D.output false = D.eval (List.ofFn x) := rfl
  rw [input,old]
  simp [GateOp.eval]

theorem rebuild {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n) (C D : Circuit)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (hd : FanInTwo D) (sz : D.size + 6 ≤ C.size)
    (mem : ∀ x, D.eval (List.ofFn x) = graphFn E (zeroed {v,u,w} x)) :
    ∃ T : Circuit, FanInTwo T ∧ T.size + 4 ≤ C.size ∧
      ∀ x, T.eval (List.ofFn x) = graphFn E (Function.update x v true) := by
  refine ⟨addPin n (addPin n D u) w, addPin_fan _ _ (addPin_fan _ _ hd), ?_, ?_⟩
  · simpa only [addPin_size, Nat.add_assoc] using sz
  · intro x
    rw [addPin_eval,addPin_eval,mem,true_expand E v u w vu vw hu hw hn]

end PEqualNP.Outside.L_meta_18723



namespace PEqualNP.Outside.L_meta_18723.Accounting

abbrev Edges (n : ℕ) := Finset (Fin n × Fin n)
def cover (A : Edges n) (T : Finset (Fin n)) := ∀ e ∈ A, e.1 ∈ T ∨ e.2 ∈ T
def cut (A : Edges n) (S : Finset (Fin n)) : Edges n :=
  A.filter fun e => e.1 ∉ S ∧ e.2 ∉ S
def touches (e : Fin n × Fin n) (v : Fin n) := e.1=v ∨ e.2=v

theorem cut_cover (A : Edges n) (T S : Finset (Fin n)) (h : cover A T) : cover (cut A S) (T\S) := by
  intro e he
  obtain ⟨ha,x,y⟩ := Finset.mem_filter.mp he
  rcases h e ha with left | right
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨left,x⟩)
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨right,y⟩)

private theorem countDrop {A B W : Finset α} [DecidableEq α] (sub : B ⊆ A) (inside : W ⊆ A)
    (apart : Disjoint B W) : B.card + W.card ≤ A.card := by
  rw [← Finset.card_union_of_disjoint apart]
  exact Finset.card_le_card (Finset.union_subset sub inside)

theorem accounting (A : Edges n) (v u w : Fin n) (T : Finset (Fin n)) (hc : cover A T)
    (uw : u ≠ w) (vu : v ≠ u) (vw : v ≠ w)
    (eu : (v,u) ∈ A ∨ (u,v) ∈ A) (ew : (v,w) ∈ A ∨ (w,v) ∈ A) :
    (∃ R, cover (cut A {v}) R ∧ (cut A {v}).card + R.card + 3 ≤ A.card+T.card) ∨
    (∃ R, cover (cut A {v,u,w}) R ∧ (cut A {v,u,w}).card + R.card + 6 ≤ A.card+T.card) := by
  classical
  let B := cut A {v}
  let K := cut A {v,u,w}
  have endpoints (z : Fin n) (hz : (v,z) ∈ A ∨ (z,v) ∈ A) :
      ∃ e ∈ A, touches e v ∧ touches e z ∧ (∀ p, touches e p → p=v ∨ p=z) := by
    rcases hz with h|h
    · exact ⟨(v,z),h,Or.inl rfl,Or.inr rfl,fun p hp => hp.elim (fun q => Or.inl q.symm) (fun q => Or.inr q.symm)⟩
    · exact ⟨(z,v),h,Or.inr rfl,Or.inl rfl,fun p hp => hp.elim (fun q => Or.inr q.symm) (fun q => Or.inl q.symm)⟩
  obtain ⟨a,ha,av,au,ends⟩ := endpoints u eu
  obtain ⟨b,hb,bv,bw,_⟩ := endpoints w ew
  have ab : a ≠ b := by
    intro q
    rcases ends w (q.symm ▸ bw) with h|h
    · exact vw h.symm
    · exact uw h.symm
  have away {e : Fin n × Fin n} {S : Finset (Fin n)} (z : Fin n) (ts : touches e z) (mem : z ∈ S) :
      e ∉ cut A S := by
    intro h
    have no := (Finset.mem_filter.mp h).2
    rcases ts with l | r
    · exact no.1 (l.symm ▸ mem)
    · exact no.2 (r.symm ▸ mem)
  have na : a ∉ B := away v av (by simp)
  have nb : b ∉ B := away v bv (by simp)
  have cutTwo : B.card+2 ≤ A.card := by
    have pay := countDrop (Finset.filter_subset _ _) (show ({a,b} : Edges n) ⊆ A by intro e he; simp only [Finset.mem_insert,Finset.mem_singleton] at he; rcases he with rfl|rfl <;> assumption)
      (show Disjoint B {a,b} by simpa [Finset.disjoint_insert_right] using And.intro na nb)
    simpa [B,cut,ab] using pay
  have left (R : Finset (Fin n)) (hr : cover B R) (size : R.card < T.card) :
      ∃ R, cover (cut A {v}) R ∧ (cut A {v}).card + R.card + 3 ≤ A.card+T.card :=
    ⟨R,hr,by change B.card + R.card + 3 ≤ _; omega⟩
  by_cases vin : v ∈ T
  · apply Or.inl
    apply left (T.erase v)
    · simpa [Finset.sdiff_singleton_eq_erase] using cut_cover A T {v} hc
    · exact Finset.card_erase_lt_of_mem vin
  have inT (z : Fin n) (ez : (v,z)∈A ∨ (z,v)∈A) : z ∈ T := by
    rcases ez with h|h
    · exact (hc _ h).resolve_left vin
    · exact (hc _ h).resolve_right vin
  have ut := inT u eu
  have wt := inT w ew
  by_cases uc : cover B (T.erase u)
  · exact Or.inl (left _ uc (Finset.card_erase_lt_of_mem ut))
  by_cases wc : cover B (T.erase w)
  · exact Or.inl (left _ wc (Finset.card_erase_lt_of_mem wt))
  have privateEdge (z : Fin n) (fail : ¬ cover B (T.erase z)) :
      ∃ e ∈ B, touches e z ∧ e.1 ∉ T.erase z ∧ e.2 ∉ T.erase z := by
    unfold cover at fail
    push_neg at fail
    obtain ⟨e,he,h1,h2⟩ := fail
    refine ⟨e,he,?_,h1,h2⟩
    rcases hc e ((Finset.mem_filter.mp he).1) with h|h
    · exact Or.inl (by by_contra q; exact h1 (Finset.mem_erase.mpr ⟨q,h⟩))
    · exact Or.inr (by by_contra q; exact h2 (Finset.mem_erase.mpr ⟨q,h⟩))
  obtain ⟨c,hcB,cu,c1,c2⟩ := privateEdge u uc
  obtain ⟨d,hdB,dw,_,_⟩ := privateEdge w wc
  have cd : c ≠ d := by
    intro eq
    have ww : w ∈ T.erase u := Finset.mem_erase.mpr ⟨uw.symm,wt⟩
    rcases (show touches c w from eq.symm ▸ dw) with e|e
    · exact c1 (e.symm ▸ ww)
    · exact c2 (e.symm ▸ ww)
  have ac : a ≠ c := fun e => na (e.symm ▸ hcB)
  have ad : a ≠ d := fun e => na (e.symm ▸ hdB)
  have bc : b ≠ c := fun e => nb (e.symm ▸ hcB)
  have bd : b ≠ d := fun e => nb (e.symm ▸ hdB)
  have nc : c ∉ K := away u cu (by simp)
  have nd : d ∉ K := away w dw (by simp)
  have nkA : a ∉ K := away v av (by simp)
  have nkB : b ∉ K := away v bv (by simp)
  have cutFour : K.card+4 ≤ A.card := by
    have cc : c∈A := (Finset.mem_filter.mp hcB).1
    have dd : d∈A := (Finset.mem_filter.mp hdB).1
    have pay := countDrop (Finset.filter_subset _ _) (show ({a,b,c,d} : Edges n) ⊆ A by intro e he; simp only [Finset.mem_insert,Finset.mem_singleton] at he; rcases he with rfl|rfl|rfl|rfl <;> assumption)
      (show Disjoint K {a,b,c,d} by simp [Finset.disjoint_insert_right,nkA,nkB,nc,nd])
    simpa [K,cut,ab,ac,ad,bc,bd,cd] using pay
  apply Or.inr
  refine ⟨T\{v,u,w},cut_cover A T _ hc,?_⟩
  have sub : T\{v,u,w} ⊆ T := Finset.sdiff_subset
  have wid : ({u,w} : Finset (Fin n)) ⊆ T := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> assumption
  have dis : Disjoint (T\{v,u,w}) {u,w} := by simp [Finset.disjoint_insert_right]
  have two := countDrop sub wid dis
  simp [uw] at two
  change K.card+_+6 ≤ _
  omega

end PEqualNP.Outside.L_meta_18723.Accounting


namespace PEqualNP.Outside.L_meta_18723.Accounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18723
open scoped Sym2

def fromEdges (A : Edges n) (loops : ∀ e ∈ A, e.1 ≠ e.2) : SimpleGraph (Fin n) where
  Adj a b := (a,b) ∈ A ∨ (b,a) ∈ A
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by rcases h with h|h <;> exact loops _ h rfl⟩

def accepts (A : Edges n) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ A, x e.1=true ∧ x e.2=true)

theorem cutSem (A : Edges n) (S : Finset (Fin n)) (x : Fin n → Bool) :
    accepts (cut A S) x = accepts A (zeroed S x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [accepts,decide_eq_true_eq,cut,Finset.mem_filter]
  constructor
  · rintro ⟨e,⟨he,ha,hb⟩,xa,xb⟩
    exact ⟨e,he,by simp [zeroed,ha,xa],by simp [zeroed,hb,xb]⟩
  · rintro ⟨e,he,xa,xb⟩
    have ha : e.1 ∉ S := by intro h; simp [zeroed,h] at xa
    have hb : e.2 ∉ S := by intro h; simp [zeroed,h] at xb
    exact ⟨e,⟨he,ha,hb⟩,by simpa [zeroed,ha] using xa,by simpa [zeroed,hb] using xb⟩

theorem starCompile (A : Edges n) (T : Finset (Fin n)) (loops : ∀ e ∈ A, e.1 ≠ e.2) (vc : cover A T) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ A.card+T.card-1 ∧ ∀ x, D.eval (List.ofFn x) = accepts A x := by
  classical
  let G := fromEdges A loops
  have covered : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T := by
    intro a b h
    rcases h with ab|ba
    · exact vc (a,b) ab
    · exact (vc (b,a) ba).symm
  obtain ⟨D,hd,eq,sz,_⟩ := PEqualNP.Outside.L_meta_18723.StarCompiler.main n G T covered
  have bound : G.edgeSet.ncard ≤ A.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    let send : Fin n × Fin n → Sym2 (Fin n) := fun e => s(e.1,e.2)
    have sub : G.edgeFinset ⊆ A.image send := by
      intro q hq
      induction q using Sym2.inductionOn with
      | _ a b =>
        change s(a,b) ∈ A.image send
        have h : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hq
        rcases h with ab|ba
        · exact Finset.mem_image.mpr ⟨(a,b),ab,rfl⟩
        · exact Finset.mem_image.mpr ⟨(b,a),ba,Sym2.eq_swap⟩
    exact le_trans (Finset.card_le_card sub) (Finset.card_image_le)
  refine ⟨D,?_,by omega,?_⟩
  · intro g hg
    obtain ⟨op,arity⟩ := hd g hg
    have legal : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using op
    exact ⟨by rcases legal with o|o <;> simp [o],arity⟩
  · intro x
    have sem := congrFun eq x
    change D.eval (List.ofFn x) = _ at sem
    rw [sem]
    apply Bool.eq_iff_iff.mpr
    simp only [NestedCover.graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,accepts,decide_eq_true_eq]
    constructor
    · rintro ⟨a,b,ab,xa,xb⟩
      rcases ab with he|he
      · exact ⟨(a,b),he,xa,xb⟩
      · exact ⟨(b,a),he,xb,xa⟩
    · rintro ⟨⟨a,b⟩,he,xa,xb⟩
      exact ⟨a,b,Or.inl he,xa,xb⟩

theorem toFinsetFn (E : List (Fin n × Fin n)) (x : Fin n → Bool) :
    graphFn E x = accepts E.toFinset x := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFn,accepts,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true,List.mem_toFinset]

theorem coverSuffices (E : List (Fin n × Fin n)) (v u w : Fin n) (C : Circuit) (T : Finset (Fin n))
    (loops : ∀ e ∈ E, e.1 ≠ e.2) (uw : u ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (edge : ∃ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ≠ w ∧ e.2 ≠ w)
    (cov : cover E.toFinset T) (budget : E.toFinset.card+T.card ≤ C.size+1) :
    (∃ D : Circuit, FanInTwo D ∧ D.size+3 ≤ C.size ∧ ∀ x, D.eval (List.ofFn x) = graphFn E (Function.update x v false)) ∨
    (∃ D : Circuit, FanInTwo D ∧ D.size+4 ≤ C.size ∧ ∀ x, D.eval (List.ofFn x) = graphFn E (Function.update x v true)) := by
  classical
  let A := E.toFinset
  have vu : v≠u := by intro eq; subst u; rcases hu with a|a <;> exact loops _ a rfl
  have vw : v≠w := by intro eq; subst w; rcases hw with a|a <;> exact loops _ a rfl
  have nog (S : Finset (Fin n)) : ∀ e ∈ cut A S, e.1 ≠ e.2 := by
    intro e he; exact loops e (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)
  obtain ⟨e,he,av,bv,au,bu,aw,bw⟩ := edge
  have posA : 0 < (cut A {v}).card := Finset.card_pos.mpr ⟨e,by simp [cut,A,he,av,bv]⟩
  have posB : 0 < (cut A {v,u,w}).card := Finset.card_pos.mpr ⟨e,by simp [cut,A,he,av,bv,au,bu,aw,bw]⟩
  change A.card+T.card ≤ C.size+1 at budget
  rcases accounting A v u w T cov uw vu vw (by simpa [A] using hu) (by simpa [A] using hw) with left|right
  · obtain ⟨R,hR,le⟩ := left
    obtain ⟨D,fan,sz,cook⟩ := starCompile _ R (nog {v}) hR
    refine Or.inl ⟨D,fan,by omega,fun x => ?_⟩
    rw [cook,cutSem,toFinsetFn]
    congr 1
    funext k
    by_cases eq : k=v
    · subst k; simp [zeroed]
    · simp [zeroed,eq,Function.update_of_ne eq]
  · obtain ⟨R,hR,le⟩ := right
    obtain ⟨D,fan,sz,cook⟩ := starCompile _ R (nog {v,u,w}) hR
    apply Or.inr
    apply rebuild E v u w C D vu vw hu hw hn fan (by omega)
    intro x
    rw [cook,cutSem,toFinsetFn]
end PEqualNP.Outside.L_meta_18723.Accounting
