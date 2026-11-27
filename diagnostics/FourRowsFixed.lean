import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8117.Empty

-- Helpers adapted from accepted proofs.

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def AO (n : ℕ) (ds : List Gate) : Prop :=
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < n + j

def Rep (n : ℕ) (ds : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c, ∀ y, f y = c) ∨
    ∃ k < n + ds.length, ∀ y, f y = (run ds (List.ofFn y)).getD k false

theorem rep_app (n : ℕ) (ds : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
    rw [h y, run_prefix _ _ _ _ (by simpa using hk)]

theorem rep_two (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (u v : (Fin n → Bool) → Bool)
    (hu : Rep n ds u) (hv : Rep n ds v) :
    ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
  have triv : ∀ w : (Fin n → Bool) → Bool, Rep n ds w → (∀ y, o.eval [u y, v y] = w y) →
      ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
    intro w hw e
    refine ⟨[], by simp, by simpa using hds, ?_⟩
    rw [List.append_nil, show (fun y => o.eval [u y, v y]) = w from funext e]
    exact hw
  have cst : ∀ c : Bool, Rep n ds fun _ => c := fun c => Or.inl ⟨c, fun _ => rfl⟩
  rcases hu with ⟨c, hc⟩ | ⟨a, ha, hua⟩
  · rcases ho with rfl | rfl <;> cases c
    · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
  · rcases hv with ⟨c, hc⟩ | ⟨b, hb, hvb⟩
    · have hu : Rep n ds u := Or.inr ⟨a, ha, hua⟩
      rcases ho with rfl | rfl <;> cases c
      · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
    · refine ⟨[⟨o, [a, b]⟩], by simp, ⟨?_, ?_⟩, Or.inr ⟨n + ds.length, by simp, fun y => ?_⟩⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact hds.1 g h
        · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
      · intro j hj i hi
        by_cases h : j < ds.length
        · rw [List.getElem_append_left h] at hi
          exact hds.2 j h i hi
        · have hj' : j = ds.length := by simp at hj; omega
          subst hj'
          simp at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [run_snoc, show n + ds.length = (run ds (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
        simp [hua, hvb]


theorem rep_c1 (n : ℕ) (ds : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (c : Bool) (v : (Fin n → Bool) → Bool) (hv : Rep n ds v) :
    Rep n ds fun y => o.eval [c, v y] := by
  rcases ho with rfl | rfl <;> cases c
  · exact Or.inl ⟨false, fun y => by simp [GateOp.eval]⟩
  · convert hv using 1; funext y; simp [GateOp.eval]
  · convert hv using 1; funext y; simp [GateOp.eval]
  · exact Or.inl ⟨true, fun y => by simp [GateOp.eval]⟩

theorem rep_c2 (n : ℕ) (ds : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (c : Bool) (v : (Fin n → Bool) → Bool) (hv : Rep n ds v) :
    Rep n ds fun y => o.eval [v y, c] := by
  rcases ho with rfl | rfl <;> cases c
  · exact Or.inl ⟨false, fun y => by simp [GateOp.eval]⟩
  · convert hv using 1; funext y; simp [GateOp.eval]
  · convert hv using 1; funext y; simp [GateOp.eval]
  · exact Or.inl ⟨true, fun y => by simp [GateOp.eval]⟩

theorem ao_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hAO : AO n gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hI : g.inputs = [a, b])
    (ha : a < n + gs.length) (hb : b < n + gs.length) : AO n (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.1 hg' with h | h
    · exact hAO.1 g' h
    · rw [List.mem_singleton.1 h]; exact ⟨hop, by simp [hI]⟩
  · by_cases h : j < gs.length
    · rw [List.getElem_append_left h] at hi
      exact hAO.2 j h i hi
    · have hj' : j = gs.length := by simp at hj; omega
      subst hj'
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, hI] at hi
      simp at hi
      rcases hi with rfl | rfl <;> assumption

theorem build2 (n : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ ds : List Gate, AO n ds ∧ ds.length ≤ gs.length ∧ (ds.length < gs.length ∨ AO n gs) ∧
      ∀ w, Rep n ds fun y => (run gs (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ⟨by simp, by simp⟩, le_rfl, Or.inr ⟨by simp, by simp⟩, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr ⟨w, by simpa using hw, fun y => rfl⟩
    · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by simp [run]; omega)⟩
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h2', h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have cfalse : ∀ a, ¬ a < n + gs.length → ∀ y : Fin n → Bool,
        (run gs (List.ofFn y)).getD a false = false := by
      intro a ha y
      exact List.getD_eq_default _ _ (by rw [run_length]; simp; omega)
    have main : ∃ hs : List Gate, hs.length ≤ 1 ∧ (hs.length = 0 ∨ (AO n gs → AO n (gs ++ [g]))) ∧
        AO n (ds ++ hs) ∧ Rep n (ds ++ hs)
        fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
      match hI : g.inputs, hlen with
      | [], _ =>
        exact ⟨[], by simp, Or.inl rfl, by simpa using h1, Or.inl ⟨g.op.eval [], fun y => rfl⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
        rw [List.append_nil]
        have e : (fun y : Fin n → Bool => g.op.eval ([a].map fun i =>
            (run gs (List.ofFn y)).getD i false)) =
            fun y => (run gs (List.ofFn y)).getD a false := by
          funext y
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
        rw [e]
        exact h3 a
      | [a, b], _ =>
        by_cases ha : a < n + gs.length
        · by_cases hb : b < n + gs.length
          · obtain ⟨hs, k1, k2, k3⟩ := rep_two n ds h1 g.op hop _ _ (h3 a) (h3 b)
            exact ⟨hs, k1, Or.inr fun hAO => ao_snoc n gs g a b hAO hop hI ha hb, k2, k3⟩
          · refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
            rw [List.append_nil]
            have e : (fun y : Fin n → Bool => g.op.eval ([a, b].map fun i =>
                (run gs (List.ofFn y)).getD i false)) =
                fun y => g.op.eval [(run gs (List.ofFn y)).getD a false, false] := by
              funext y
              simp only [List.map_cons, List.map_nil, cfalse b hb y]
            rw [e]
            exact rep_c2 n ds g.op hop false _ (h3 a)
        · refine ⟨[], by simp, Or.inl rfl, by simpa using h1, ?_⟩
          rw [List.append_nil]
          have e : (fun y : Fin n → Bool => g.op.eval ([a, b].map fun i =>
              (run gs (List.ofFn y)).getD i false)) =
              fun y => g.op.eval [false, (run gs (List.ofFn y)).getD b false] := by
            funext y
            simp only [List.map_cons, List.map_nil, cfalse a ha y]
          rw [e]
          exact rep_c1 n ds g.op hop false _ (h3 b)
    obtain ⟨hs, k1, k0, k2, k3⟩ := main
    have k4 : ∀ f : (Fin n → Bool) → Bool, Rep n ds f → Rep n (ds ++ hs) f := by
      intro f hf
      match hs, k1 with
      | [], _ => simpa using hf
      | [g'], _ => exact rep_app n ds g' f hf
    refine ⟨ds ++ hs, k2, by simp; omega, ?_, fun w => ?_⟩
    · rcases k0 with h0 | himp
      · left; simp; omega
      · rcases h2' with hlt | hao
        · left; simp; omega
        · exact Or.inr (himp hao)
    by_cases hw : w = n + gs.length
    · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
          fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
        funext y
        rw [run_snoc, hw, show n + gs.length = (run gs (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
      rw [e]
      exact k3
    · by_cases hw' : w < n + gs.length
      · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
            fun y => (run gs (List.ofFn y)).getD w false := by
          funext y
          exact run_prefix _ _ _ _ (by simpa using hw')
        rw [e]
        exact k4 _ (h3 w)
      · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by
          rw [run_length]; simp; omega)⟩


theorem ofFn_false_getD (n k : ℕ) : (List.ofFn fun _ : Fin n => false).getD k false = false := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (List.ofFn fun _ : Fin n => false)[k]? with _ | b
  · rfl
  · simp only [Option.getD_some]
    rw [List.getElem?_eq_some_iff] at h
    obtain ⟨_, h⟩ := h
    rw [← h]
    simp

theorem run_false (n : ℕ) (gs : List Gate) (hAO : AO n gs) :
    ∀ k, (run gs (List.ofFn fun _ : Fin n => false)).getD k false = false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k n with h | h
    · rw [run_input gs _ k (by simpa using h)]
      exact ofFn_false_getD n k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      rcases Nat.lt_or_ge j gs.length with h2 | h2
      · have hg := run_gate gs (List.ofFn fun _ : Fin n => false) j h2
        simp only [List.length_ofFn] at hg
        rw [hg]
        obtain ⟨hop, hl⟩ := hAO.1 _ (List.getElem_mem h2)
        obtain ⟨a, b, hab⟩ : ∃ a b, gs[j].inputs = [a, b] := by
          match hI : gs[j].inputs, hl with
          | [a, b], _ => exact ⟨a, b, rfl⟩
        have hm : ∀ i : ℕ, (if i < n + j then
            (run gs (List.ofFn fun _ : Fin n => false)).getD i false else false) = false := by
          intro i
          split_ifs with hi
          · exact ih i hi
          · rfl
        rw [hab]
        simp only [List.map_cons, List.map_nil, hm]
        rcases hop with e | e <;> rw [e] <;> rfl
      · exact List.getD_eq_default _ _ (by rw [run_length]; simp; omega)

end PEqualNP.Outside.L_meta_8117.Empty

open PEqualNP.Outside.L_meta_8117.Empty PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8117.Empty.Cleanup : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x7 : Fin (42 : ℕ)) => Bool.false)).getD ((42 : ℕ) + x5) Bool.false = Bool.true) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ x6.size < x3.size := by
  dsimp only
  intro C ⟨hM, hE, hI⟩ ⟨x5, g, hg, hop, hw⟩
  obtain ⟨ds, h1, h2, h2', h3⟩ := build2 42 C.gates fun g hg => by
    obtain ⟨e1, e2⟩ := hM g hg
    exact ⟨by simpa using e1, e2⟩
  have hlt : ds.length < C.gates.length := by
    rcases h2' with h | h
    · exact h
    · have := run_false 42 C.gates h (42 + x5)
      exact Bool.noConfusion (this.symm.trans hw)
  have hedge : C.eval (List.ofFn fun v : Fin 42 => decide (v = 0 ∨ v = 21)) = true :=
    hE 0 21 (by decide)
  have hind : C.eval (List.ofFn fun v : Fin 42 => decide (v.val < 21)) = false := by
    apply hI
    intro a
    constructor
    · intro ha b hb h
      simp only [decide_eq_true_eq] at ha hb
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    · intro h
      by_contra ha
      simp only [decide_eq_true_eq, not_lt] at ha
      apply h ⟨a.val - 21, by omega⟩ (by simp only [decide_eq_true_eq]; omega)
      right
      refine ⟨by simp only; omega, ha, ?_⟩
      show (a.val + 21 - (a.val - 21)) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      rw [show a.val + 21 - (a.val - 21) = 42 by omega]
      decide
  rcases h3 C.output with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
  · have e1 : c = true := (hc (fun v : Fin 42 => decide (v = 0 ∨ v = 21))).symm.trans hedge
    have e2 : c = false := (hc (fun v : Fin 42 => decide (v.val < 21))).symm.trans hind
    exact Bool.noConfusion (e1.symm.trans e2)
  · have heq : ∀ y : Fin 42 → Bool, (⟨ds, k⟩ : Circuit).eval (List.ofFn y) = C.eval (List.ofFn y) :=
      fun y => (hk' y).symm
    refine ⟨⟨ds, k⟩, ⟨fun g hg => ?_, fun a b hab => ?_, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨e1, e2⟩ := h1.1 g hg
      refine ⟨?_, by omega⟩
      rcases e1 with e | e <;> simp [e]
    · rw [heq]
      exact hE a b hab
    · rw [heq]
      exact hI y hy
    · show ds.length < C.gates.length
      exact hlt

namespace PEqualNP.Outside.L_meta_8117
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

abbrev V := Fin 42
lemma lastWire {α : Type} (l : List α) (a d : α) : (l++[a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]
def ListImp (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma listImp_append {l r : List Bool} {a b : Bool} (h : ListImp l r)
    (hab : a = true → b = true) : ListImp (l ++ [a]) (r ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  rcases Nat.lt_trichotomy i l.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by rwa [← h.1])]
    exact h.2 i
  · rw [lastWire, h.1, lastWire]
    exact hab
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma stepImp {g : Gate} {l r : List Bool} (hop : g.op = .and ∨ g.op = .or)
    (h : ListImp l r) : ListImp (stepWire l g) (stepWire r g) := by
  apply listImp_append h
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun ha i hi => h.2 i (ha i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h.2 i hv⟩

lemma runImp (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {l r : List Bool} (h : ListImp l r) : ListImp (gs.foldl stepWire l) (gs.foldl stepWire r) := by
  induction gs generalizing l r with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun q hq => hg q (List.mem_cons_of_mem _ hq)) (stepImp (hg g (by simp)) h)

lemma wire_mono {C : Circuit} (hm : Monotone2 C) {x y : V → Bool}
    (hxy : ∀ i, x i = true → y i = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  have hh : ListImp (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun j => ?_⟩
    by_cases hj : j < 42
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),
        List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn, List.getElem_ofFn]
      exact hxy ⟨j, hj⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp
  exact (runImp C.gates (fun g hg => by simpa using (hm g hg).1) hh).2 i

def direct (u v : V) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ [0, 5, 7, 17, 20]

def flag (a b : V) (i : V) := decide (i=a ∨ i=b)
def one (v : V) (i : V) := decide (i=v)
def maximal (x : V → Bool) := ∀ u, x u=true ↔ ∀ w, x w=true → ¬(direct u w ∨ direct w u)
def spec (C : Circuit) :=
  Monotone2 C ∧ (∀ u v, direct u v → C.eval (List.ofFn (flag u v))=true) ∧
  ∀ x, maximal x → C.eval (List.ofFn x)=false
def least (C : Circuit) := ∀ A, spec A → C.size ≤ A.size

lemma typed {C : Circuit} (h : spec C) (k : ℕ) (hk : k<C.gates.length) :
    (gateAt C k).op = .and ∨ (gateAt C k).op = .or := by
  simpa using (h.1 _ (gateAt_mem hk)).1

lemma proper_bypass {C : Circuit} (h : spec C) (r i : ℕ) : Monotone2 (bypass 42 C r i) := by
  intro g hg
  obtain ⟨q,hq,eq,le⟩ := bypass_mem g hg
  simpa only [eq,le] using h.1 q hq

lemma cheaper {C : Circuit} (small : least C) {r i : ℕ} (hr : r < C.gates.length) :
    ¬spec (bypass 42 C r i) := by
  intro good
  have h := small _ good
  change C.gates.length ≤ (bypass 42 C r i).gates.length at h
  rw [bypass_length] at h
  omega

lemma rawVal (C : Circuit) (x : V → Bool) (v : V) : val C (List.ofFn x) v.val = x v := by
  rw [val_input (n:=42) List.length_ofFn v.isLt]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma carrier {C : Circuit} {r : ℕ} {v : V} (h : spec C)
    (lit : val C (List.ofFn (one v)) (42+r) = true) (x : V → Bool) (hv : x v=true) :
    val C (List.ofFn x) (42+r)=true := by
  apply wire_mono h.1 (x:=one v) (y:=x) _ _ lit
  intro i hi
  have e : i=v := of_decide_eq_true hi
  simpa [e] using hv

/-- A singleton-positive wire in a physical optimum is pivotal away from the singleton. -/
theorem criticalFlag {C : Circuit} {r : ℕ} {v : V} (h : spec C) (small : least C)
    (hr : r < C.gates.length) (lit : val C (List.ofFn (one v)) (42+r)=true) :
    ∃ a b : V, direct a b ∧ v≠a ∧ v≠b ∧
      val C (List.ofFn (flag a b)) (42+r)=true ∧
      (bypass 42 C r v.val).eval (List.ofFn (flag a b))=false := by
  let A := bypass 42 C r v.val
  have earlier : v.val<42+r := by have := v.isLt; omega
  have rev : OpMono (fun a b => b=true → a=true) :=
    fun op ho l f g h => opMono_imp op ho l g f h
  have down (x : V → Bool) : A.eval (List.ofFn x)=true → C.eval (List.ofFn x)=true := by
    apply bypass_eval_rel (fun _ h=>h) rev List.length_ofFn (typed h) hr (Or.inl earlier)
    rw [rawVal]
    exact carrier h lit x
  have bad : ∃ a b, direct a b ∧ A.eval (List.ofFn (flag a b))=false := by
    by_contra! no
    apply cheaper small (i:=v.val) hr
    refine ⟨proper_bypass h _ _,?_,?_⟩
    · intro a b hab
      cases e : A.eval (List.ofFn (flag a b)) <;> simp_all
    · intro x hx
      apply Bool.eq_false_iff.mpr
      intro on
      have orig := down x on
      rw [h.2.2 x hx] at orig
      contradiction
  obtain ⟨a,b,hab,fail⟩ := bad
  have diff : val C (List.ofFn (flag a b)) (42+r) ≠ flag a b v := by
    intro eq
    have old := h.2.1 a b hab
    have rr := bypass_eval_eq (C:=C) (n:=42) (x:=List.ofFn (flag a b))
      List.length_ofFn (typed h) hr (Or.inl earlier) (eq.trans (rawVal C _ v).symm)
    change A.eval (List.ofFn (flag a b)) = _ at rr
    rw [fail,old] at rr
    contradiction
  have off : flag a b v = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    exact diff ((carrier h lit _ hv).trans hv.symm)
  have on : val C (List.ofFn (flag a b)) (42+r)=true := by
    cases eq : val C (List.ofFn (flag a b)) (42+r) <;> simp_all
  have ne : ¬(v=a ∨ v=b) := by simpa [flag] using off
  exact ⟨a,b,hab,fun e=>ne (Or.inl e),fun e=>ne (Or.inr e),on,fail⟩


/-- Each operand of a singleton-active AND has its own maximal independent counterexample
    to bypassing the AND upward. -/
theorem criticalArm {C : Circuit} {r t : ℕ} {v : V} (h : spec C) (small : least C)
    (hr : r<C.gates.length) (hop : (gateAt C r).op=.and)
    (lit : val C (List.ofFn (one v)) (42+r)=true) (port : t∈(gateAt C r).inputs) :
    ∃ x : V→Bool, maximal x ∧ x v=false ∧ val C (List.ofFn x) t=true ∧
      val C (List.ofFn x) (42+r)=false ∧ (bypass 42 C r t).eval (List.ofFn x)=true := by
  let A := bypass 42 C r t
  have earlier := ((val_and List.length_ofFn hr hop).mp lit t port).1
  have up (x : V→Bool) : C.eval (List.ofFn x)=true → A.eval (List.ofFn x)=true := by
    apply bypass_eval_rel (fun _ h=>h) opMono_imp List.length_ofFn (typed h) hr (Or.inl earlier)
    exact fun on => ((val_and List.length_ofFn hr hop).mp on t port).2
  have bad : ∃ x, maximal x ∧ A.eval (List.ofFn x)=true := by
    by_contra! no
    apply cheaper small (i:=t) hr
    refine ⟨proper_bypass h _ _,fun a b hab => up _ (h.2.1 a b hab),?_⟩
    intro x hx
    cases e : A.eval (List.ofFn x) <;> simp_all
  obtain ⟨x,hx,fail⟩ := bad
  have diff : val C (List.ofFn x) (42+r) ≠ val C (List.ofFn x) t := by
    intro eq
    have rr := bypass_eval_eq (C:=C) (n:=42) (x:=List.ofFn x)
      List.length_ofFn (typed h) hr (Or.inl earlier) eq
    change A.eval (List.ofFn x) = _ at rr
    rw [fail,h.2.2 x hx] at rr
    contradiction
  have imp := fun on => ((val_and (x:=List.ofFn x) List.length_ofFn hr hop).mp on t port).2
  have arm : val C (List.ofFn x) t=true := by
    cases ea : val C (List.ofFn x) t <;> cases eb : val C (List.ofFn x) (42+r) <;> simp_all
  have below : val C (List.ofFn x) (42+r)=false := by
    cases eb : val C (List.ofFn x) (42+r) <;> simp_all
  have omitV : x v=false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    have hc := carrier h lit x hv
    rw [below] at hc
    contradiction
  exact ⟨x,hx,omitV,arm,below,fail⟩

/-- Both physical operands of a marked AND are distinct internal wires.
    Each remains true on a second, disjoint incidence flag. -/
theorem marked_shape {C : Circuit} {r : ℕ} {v : V} (h : spec C) (small : least C)
    (hr : r<C.gates.length) (hop : (gateAt C r).op=.and)
    (lit : val C (List.ofFn (one v)) (42+r)=true) :
    ∃ a b : V, ∃ p q : ℕ, direct a b ∧ v≠a ∧ v≠b ∧
      (gateAt C r).inputs=[p,q] ∧ 42≤p ∧ 42≤q ∧ p<42+r ∧ q<42+r ∧ p≠q ∧
      val C (List.ofFn (flag a b)) p=true ∧ val C (List.ofFn (flag a b)) q=true := by
  obtain ⟨a,b,hab,hva,hvb,live,_⟩ := criticalFlag h small hr lit
  have first := (val_and List.length_ofFn hr hop).mp lit
  have second := (val_and List.length_ofFn hr hop).mp live
  have inner (p : ℕ) (hp : p∈(gateAt C r).inputs) : 42≤p := by
    by_contra! raw
    let w : V := ⟨p,raw⟩
    have e1 : one v w=true := (rawVal C (one v) w) ▸ (first p hp).2
    have e2 : flag a b w=true := (rawVal C (flag a b) w) ▸ (second p hp).2
    have hv : w=v := of_decide_eq_true e1
    have hab' : w=a ∨ w=b := of_decide_eq_true e2
    rw [hv] at hab'
    exact hab'.elim hva hvb
  have many (p : ℕ) (hp : p∈(gateAt C r).inputs) :
      ∃ q ∈ (gateAt C r).inputs, q≠p := by
    obtain ⟨x,hx,_,active,dead,_⟩ := criticalArm h small hr hop lit hp
    by_contra! no
    have on := (val_and (x:=List.ofFn x) List.length_ofFn hr hop).mpr (fun q hq => by
      have eq := no q hq
      rw [eq]
      exact ⟨(first p hp).1,active⟩)
    rw [dead] at on
    contradiction
  have len := (h.1 _ (gateAt_mem hr)).2
  have nonempty : (gateAt C r).inputs≠[] := by
    intro empty
    have hh : val C (List.ofFn (fun _ : V=>false)) (42+r)=true :=
      (val_and List.length_ofFn hr hop).mpr (by simp [empty])
    have get : C.gates[r]? = some (gateAt C r) := by
      rw [gateAt_eq hr, List.getElem?_eq_getElem hr]
    obtain ⟨D,hd,lt⟩ := Empty.Cleanup C h ⟨r,gateAt C r,get,hop,hh⟩
    exact (Nat.not_lt_of_ge (small D hd)) lt
  obtain ⟨p,q,he⟩ : ∃ p q : ℕ, (gateAt C r).inputs=[p,q] := by
    cases e : (gateAt C r).inputs with
    | nil => exact (nonempty e).elim
    | cons p rest =>
      cases rest with
      | nil =>
        obtain ⟨q,hq,ne⟩ := many p (by simp [e])
        exact (ne (by simpa [e] using hq)).elim
      | cons q rest =>
        have l : (p::q::rest).length≤2 := by simpa [e] using len
        have z : rest.length=0 := by simp only [List.length_cons] at l; omega
        have zz := List.length_eq_zero_iff.mp z
        subst rest
        exact ⟨p,q,rfl⟩
  have pp : p ∈ (gateAt C r).inputs := by simp [he]
  have qq : q ∈ (gateAt C r).inputs := by simp [he]
  have ne : p≠q := by
    intro eq
    obtain ⟨t,ht,hn⟩ := many p pp
    exact hn (by simpa [he,←eq] using ht)
  exact ⟨a,b,p,q,hab,hva,hvb,he,inner p pp,inner q qq,(first p pp).1,(first q qq).1,ne,
    (second p pp).2,(second q qq).2⟩

end PEqualNP.Outside.L_meta_8117
