import PEqualNP.Defs

namespace P7808Star

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


end P7808Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pair7808
namespace Builder
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

theorem appendTerm {n s k : ℕ} {f t : (Fin n → Bool) → Bool} (c : HasCircuitSize n f s) (term : Bld n t k) :
    HasCircuitSize n (fun x => f x || t x) (s+k+1) := by
  obtain ⟨C,fan,cheap,correct⟩ := c
  let m := n+C.gates.length
  obtain ⟨gs,wout,ok,budget,range,computes⟩ := term m (by dsimp [m]; omega)
  let old := if C.output<m then C.output else m+gs.length+1
  let D : Circuit := ⟨C.gates++gs++[⟨.or,[old,wout]⟩],m+gs.length⟩
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    change g ∈ C.gates++gs++[_] at hg
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact fan _ h
      · exact ok _ h
    · obtain rfl := List.mem_singleton.mp h
      simp
  · change (C.gates++gs++[_]).length ≤ s+k+1
    change C.gates.length ≤ s at cheap
    simp
    omega
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    let finalW := wiresFrom gs w
    have lengthW : w.length=m := by simp [w,m,length_wiresFrom]
    have lengthFinal : finalW.length=m+gs.length := by simp [finalW,length_wiresFrom,lengthW]
    have first : finalW.getD old false = f x := by
      have eq : w.getD C.output false = f x := correct x
      rw [← eq]
      by_cases existsWire : C.output < m
      · change (wiresFrom gs w).getD old false = _
        rw [show old=C.output by simp [old,existsWire],getD_wiresFrom _ _ _ (by omega)]
      · rw [show old=m+gs.length+1 by simp [old,existsWire]]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have same : (fun i : Fin n => w.getD i.val false)=x := by
      funext i
      change (wiresFrom C.gates (List.ofFn x)).getD i.val false = _
      rw [getD_wiresFrom _ _ _ (by simp),getD_ofFn]
    have second : finalW.getD wout false = t x := (computes w lengthW).trans (congrArg t same)
    change (wiresFrom (C.gates++gs++[_]) (List.ofFn x)).getD (m+gs.length) false = _
    rw [wiresFrom_append,wiresFrom_append]
    change (finalW++[GateOp.or.eval [finalW.getD old false,finalW.getD wout false]]).getD (m+gs.length) false = _
    rw [← lengthFinal,getD_snoc_eq,first,second]
    simp [GateOp.eval]


open PEqualNP.MetaComplexity.NestedCover
variable {n : Nat}
def zeroPair (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

lemma true_zero (x:Fin n→Bool) (u v i:Fin n) :
    zeroPair u v x i=true ↔ i≠u ∧ i≠v ∧ x i=true := by
  by_cases h:i=v
  · subst i; simp [zeroPair]
  · by_cases q:i=u
    · subst i; simp [zeroPair,h]
    · simp [zeroPair,h,q]

def hit (S:Finset (Fin n)) (x:Fin n→Bool) := decide (∃i∈S,x i=true)
def term (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :=
  (x u && hit (G.neighborFinset u) x) || (x v && hit ((G.neighborFinset v).erase u) x)

lemma termCost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (edge:G.Adj u v)
    (uc:(G.neighborFinset u).card=3) (vc:(G.neighborFinset v).card=3) :
    Bld n (term G u v) 6 := by
  have mem : u∈G.neighborFinset v := (G.mem_neighborFinset _ _).mpr edge.symm
  have er : ((G.neighborFinset v).erase u).card=2 := by rw [Finset.card_erase_of_mem mem,vc]
  have a := bld_anyFinset (G.neighborFinset u) (Finset.card_pos.mp (by omega))
  have b := bld_anyFinset ((G.neighborFinset v).erase u) (Finset.card_pos.mp (by omega))
  have t := bld_or (bld_and (bld_var u) a) (bld_and (bld_var v) b)
  rwa [uc,er] at t

lemma termOff (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :
    term G u v (zeroPair u v x)=false := by
  have a := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v u).mp h).1 rfl)
  have b := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v v).mp h).2.1 rfl)
  simp [term,a,b]

lemma splitGraph (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (u v:Fin n) (ha:u∉A) (hb:v∉A) (x:Fin n→Bool) :
    (graphFun G A (zeroPair u v x) || term G u v x) = graphFun G A x := by
  have spec (y:Fin n→Bool) : graphFun G A y=true ↔ (∃a∈A,y a=true) ∨ ∃a b,G.Adj a b ∧ y a=true ∧ y b=true := by
    simp [graphFun]
  have le (i:Fin n) (h:zeroPair u v x i=true) := ((true_zero x u v i).mp h).2.2
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,spec,term,hit,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · rcases h with ⟨a,aa,xa⟩ | ⟨a,b,ab,xa,xb⟩
      · exact Or.inl ⟨a,aa,le a xa⟩
      · exact Or.inr ⟨a,b,ab,le a xa,le b xb⟩
    · rcases h with ⟨xu,j,hj,xj⟩|⟨xv,j,hj,xj⟩
      · exact Or.inr ⟨u,j,(G.mem_neighborFinset _ _).mp hj,xu,xj⟩
      · exact Or.inr ⟨v,j,(G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hj).2,xv,xj⟩
  · rintro (⟨a,aa,xa⟩|⟨a,b,ab,xa,xb⟩)
    · exact Or.inl (Or.inl ⟨a,aa,(true_zero _ _ _ _).mpr ⟨fun e=>ha (e ▸ aa),fun e=>hb (e ▸ aa),xa⟩⟩)
    · by_cases au:a=u
      · subst a
        exact Or.inr (Or.inl ⟨xa,b,(G.mem_neighborFinset _ _).mpr ab,xb⟩)
      by_cases bu:b=u
      · subst b
        exact Or.inr (Or.inl ⟨xb,a,(G.mem_neighborFinset _ _).mpr ab.symm,xa⟩)
      by_cases av:a=v
      · subst a
        exact Or.inr (Or.inr ⟨xa,b,Finset.mem_erase.mpr ⟨bu,(G.mem_neighborFinset _ _).mpr ab⟩,xb⟩)
      by_cases bv:b=v
      · subst b
        exact Or.inr (Or.inr ⟨xb,a,Finset.mem_erase.mpr ⟨au,(G.mem_neighborFinset _ _).mpr ab.symm⟩,xa⟩)
      exact Or.inl (Or.inr ⟨a,b,ab,(true_zero _ _ _ _).mpr ⟨au,av,xa⟩,
        (true_zero _ _ _ _).mpr ⟨bu,bv,xb⟩⟩)

lemma neighbors_cost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3) (u v:Fin n) (edge:G.Adj u v) :
    u∉A ∧ (G.neighborFinset u).card=3 := by
  have h := rule u
  have eq : (G.neighborSet u).ncard=(G.neighborFinset u).card := by
    symm
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_neighborFinset]
  rw [eq] at h
  have pos := Finset.card_pos.mpr (show (G.neighborFinset u).Nonempty from ⟨v,(G.mem_neighborFinset _ _).mpr edge⟩)
  by_cases hu:u∈A
  · rw [if_pos hu] at h
    omega
  · simpa [hu] using And.intro hu h

def zero₂ {n:Nat} (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false


def ordinary {n:Nat} (C:Circuit) (u v:Fin n) := ∃D:Circuit, FanInTwo D ∧ D.size+7≤C.size ∧
    circuitFun n D=(fun x => circuitFun n C (zero₂ u v x))

variable {n:Nat}
def prune (G:SimpleGraph (Fin n)) (u v:Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a≠u ∧ a≠v ∧ b≠u ∧ b≠v
  symm := ⟨by rintro a b ⟨ab,au,av,bu,bv⟩; exact ⟨ab.symm,bu,bv,au,av⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

instance (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) : DecidableRel (prune G u v).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a≠u ∧ a≠v ∧ b≠u ∧ b≠v))

theorem prune_card (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (uv:G.Adj u v)
    (hu:(G.neighborFinset u).card=3) (hv:(G.neighborFinset v).card=3) :
    (prune G u v).edgeFinset.card + 5 ≤ G.edgeFinset.card := by
  classical
  let P := (prune G u v).edgeFinset
  let L := (G.neighborFinset u).image (fun i => s(u,i))
  let R := ((G.neighborFinset v).erase u).image (fun i => s(v,i))
  have inj (z:Fin n) : Function.Injective (fun i:Fin n => s(z,i)) := by
    intro i j h
    rcases Sym2.eq_iff.mp h with h|h <;> grind
  have cl : L.card=3 := (Finset.card_image_of_injective _ (inj u)).trans hu
  have cr : R.card=2 := by
    have e : u∈G.neighborFinset v := (G.mem_neighborFinset _ _).mpr uv.symm
    change (Finset.image _ _).card=2
    rw [Finset.card_image_of_injective _ (inj v),Finset.card_erase_of_mem e,hv]
  have pl : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro e he hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    have bad : (prune G u v).Adj u i := SimpleGraph.mem_edgeFinset.mp he
    exact bad.2.1 rfl
  have pr : Disjoint (P ∪ L) R := by
    apply Finset.disjoint_left.mpr
    intro e h hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    rcases Finset.mem_union.mp h with h|h
    · have bad : (prune G u v).Adj v i := SimpleGraph.mem_edgeFinset.mp h
      exact bad.2.2.1 rfl
    · obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp h
      rcases Sym2.eq_iff.mp eq with h|h
      · exact uv.ne h.1
      · exact (Finset.mem_erase.mp hi).1 h.1.symm
  have sub : (P∪L)∪R ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with h|h
    · rcases Finset.mem_union.mp h with p|l
      · revert p
        induction e using Sym2.inductionOn with
        | _ a b =>
          intro p
          have ab : (prune G u v).Adj a b := SimpleGraph.mem_edgeFinset.mp p
          exact SimpleGraph.mem_edgeFinset.mpr ab.1
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp l
        exact SimpleGraph.mem_edgeFinset.mpr ((G.mem_neighborFinset _ _).mp hi)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact SimpleGraph.mem_edgeFinset.mpr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hi).2)
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint pr, Finset.card_union_of_disjoint pl,cl,cr] at count
  omega

theorem oddCover {n k:Nat} (G:SimpleGraph (Fin n)) (pick:Fin k→Fin n) (hk:Odd k)
    (cycle:∀i j:Fin k,G.Adj (pick i) (pick j) ↔ (i.val+1)%k=j.val ∨ (j.val+1)%k=i.val)
    (T:Finset (Fin n)) (cover:∀a b,G.Adj a b→a∈T∨b∈T) :
    ∃i j:Fin k, G.Adj (pick i) (pick j) ∧ pick i∈T ∧ pick j∈T := by
  obtain ⟨q,qk⟩ := hk
  have kp:0<k := by omega
  let atN (t:Nat) : Fin k := ⟨t%k,Nat.mod_lt _ kp⟩
  have adj (t:Nat) : G.Adj (pick (atN t)) (pick (atN (t+1))) := by
    apply (cycle _ _).mpr
    left
    change (t%k+1)%k=(t+1)%k
    exact Nat.mod_add_mod _ _ _
  by_contra bad
  have swap (t:Nat) : pick (atN (t+1))∈T ↔ pick (atN t)∉T := by
    constructor
    · intro a b
      exact bad ⟨_,_,adj t,b,a⟩
    · intro a
      exact (cover _ _ (adj t)).resolve_left a
  have dbl (m:Nat) : pick (atN (2*m))∈T ↔ pick (atN 0)∈T := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2*(m+1)=2*m+1+1 by omega,swap,swap,not_not,ih]
  have endeq : atN k=atN 0 := by
    apply Fin.ext
    simp [atN]
  have diff : pick (atN 0)∈T ↔ pick (atN 0)∉T := by
    calc
      _ ↔ pick (atN k)∈T := by rw [endeq]
      _ ↔ pick (atN (2*q+1))∈T := by rw [show k=2*q+1 by omega]
      _ ↔ pick (atN (2*q))∉T := swap _
      _ ↔ _ := not_congr (dbl q)
  tauto

theorem starUpper (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T:Finset (Fin n))
    (cover:∀a b,G.Adj a b→a∈T∨b∈T) :
    HasCircuitSize n (graphFun G A) (G.edgeFinset.card+T.card-1+A.card) := by
  obtain ⟨D,mon,ev,le,_⟩ := P7808Star.main n G T cover
  have co : G.edgeSet.ncard=G.edgeFinset.card := by rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  rw [co] at le
  have df : FanInTwo D := by
    intro g h
    obtain ⟨op,len⟩ := mon g h
    refine ⟨?_,len⟩
    rcases op with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have orig : HasCircuitSize n (graphFun G ∅) (G.edgeFinset.card+T.card-1) :=
    ⟨D,df,le,fun x=>congrFun ev x⟩
  by_cases az:A=∅
  · subst A; simpa using orig
  have ap := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr az)
  obtain ⟨F,ff,fs,fe⟩ := appendTerm orig (bld_anyFinset A (Finset.nonempty_iff_ne_empty.mpr az))
  refine ⟨F,ff,by omega,?_⟩
  intro x
  rw [fe]
  simp [graphFun,Bool.or_comm]

lemma prune_eval (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (u v:Fin n) (ha:u∉A) (hb:v∉A) (x:Fin n→Bool) :
    graphFun (prune G u v) A x=graphFun G A (zeroPair u v x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq,true_zero]
  constructor
  · rintro (⟨a,aa,xa⟩|⟨a,b,h,xa,xb⟩)
    · exact Or.inl ⟨a,aa,fun e=>ha (e ▸ aa),fun e=>hb (e ▸ aa),xa⟩
    · exact Or.inr ⟨a,b,h.1,⟨h.2.1,h.2.2.1,xa⟩,h.2.2.2.1,h.2.2.2.2,xb⟩
  · rintro (⟨a,aa,_,_,xa⟩|⟨a,b,h,⟨au,av,xa⟩,bu,bv,xb⟩)
    · exact Or.inl ⟨a,aa,xa⟩
    · exact Or.inr ⟨a,b,⟨h,au,av,bu,bv⟩,xa,xb⟩

lemma survives (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3)
    (u v:Fin n) (uv:G.Adj u v) : (prune G u v).edgeFinset.Nonempty := by
  have outside (a:Fin n) (ca:(G.neighborFinset a).card=3) : ∃b,G.Adj a b ∧ b≠u ∧ b≠v := by
    by_contra! no
    have sub : G.neighborFinset a ⊆ {u,v} := by
      intro b hb
      by_cases bu:b=u
      · simp [bu]
      · have bv := no b ((G.mem_neighborFinset _ _).mp hb) bu
        simpa [bv]
    have card := Finset.card_le_card sub
    have pair : ({u,v}:Finset (Fin n)).card≤2 := Finset.card_pair_le _ _
    omega
  obtain ⟨a,ua,au,av⟩ := outside u (neighbors_cost G A rule u v uv).2
  obtain ⟨b,ab,bu,bv⟩ := outside a (neighbors_cost G A rule a u ua.symm).2
  have res : (prune G u v).Adj a b := ⟨ab,au,av,bu,bv⟩
  exact ⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr res⟩

theorem star_to_ordinary (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3)
    (T:Finset (Fin n)) (cover:∀a b,G.Adj a b→a∈T∨b∈T)
    (C:Circuit) (same:circuitFun n C=graphFun G A)
    (budget:G.edgeFinset.card+T.card-1+A.card≤C.size)
    (u v:Fin n) (uv:G.Adj u v) (ut:u∈T) (vt:v∈T) : ordinary C u v := by
  let S := (T.erase u).erase v
  obtain ⟨ua,uc⟩ := neighbors_cost G A rule u v uv
  obtain ⟨va,vc⟩ := neighbors_cost G A rule v u uv.symm
  have ve : v∈T.erase u := Finset.mem_erase.mpr ⟨uv.ne.symm,vt⟩
  have sc : S.card+2=T.card := by
    change ((T.erase u).erase v).card+2=_
    rw [Finset.card_erase_of_mem ve,Finset.card_erase_of_mem ut]
    have sc1 := Finset.card_pos.mpr (show (T.erase u).Nonempty from ⟨v,ve⟩)
    rw [Finset.card_erase_of_mem ut] at sc1
    omega
  have cov : ∀a b,(prune G u v).Adj a b → a∈S ∨ b∈S := by
    intro a b h
    rcases cover a b h.1 with p|p
    · exact Or.inl (Finset.mem_erase.mpr ⟨h.2.2.1,Finset.mem_erase.mpr ⟨h.2.1,p⟩⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨h.2.2.2.2,Finset.mem_erase.mpr ⟨h.2.2.2.1,p⟩⟩)
  have ec := prune_card G u v uv uc vc
  have pos := Finset.card_pos.mpr (survives G A rule u v uv)
  obtain ⟨D,df,ds,ev⟩ := starUpper (prune G u v) A S cov
  refine ⟨D,df,by omega,?_⟩
  funext x
  exact (ev x).trans ((prune_eval G A u v ua va x).trans (congrFun same _).symm)

theorem star_cycle {k:Nat} (pick:Fin k→Fin n) (hk:Odd k) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (cycle:∀i j:Fin k,G.Adj (pick i) (pick j) ↔ (i.val+1)%k=j.val ∨ (j.val+1)%k=i.val)
    (A T:Finset (Fin n)) (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3)
    (cover:∀a b,G.Adj a b→a∈T∨b∈T) (C:Circuit) (same:circuitFun n C=graphFun G A)
    (budget:G.edgeFinset.card+T.card-1+A.card≤C.size) :
    ∃i j,G.Adj (pick i) (pick j) ∧ ordinary C (pick i) (pick j) := by
  obtain ⟨i,j,ij,ic,jc⟩ := oddCover G pick hk cycle T cover
  exact ⟨i,j,ij,star_to_ordinary G A rule T cover C same budget _ _ ij ic jc⟩

end Builder
end Pair7808
