import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Sig (N : ℕ) := (Fin N → Bool) → Bool

def Strict (C : Circuit) := ∀ g∈C.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def Scheduled (N : ℕ) (k : ℕ) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack N ⟨gs, 0⟩ ∧ Strict ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem startSched (N : ℕ) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [Strict], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem realizeDeps {N k : ℕ} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < N + k) ∧
      ∀ x : Fin N → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem pushSched {N k : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (shape : ((op=.and ∨ op=.or) ∧ deps.length=2) ∨ (op=.not ∧ deps.length=1)) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + k := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      simpa [g,his] using shape
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨N + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

theorem finishFinBits {N k L : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (bits : Fin L → Sig N) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (out : Fin L → Fin (N + C.size)),
      Strict C ∧ ReadsBack N C ∧ C.size = k ∧
      ∀ (p : Fin L) (x : Fin N → Bool),
        (C.wires (List.ofFn x)).getD (out p).val false = bits p x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  have hcho : ∀ p : Fin L, ∃ i : Fin (N + gs.length),
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨⟨i, by omega⟩, hv⟩
  choose out hout using hcho
  refine ⟨⟨gs, 0⟩, out, hf, hr, hgs, ?_⟩
  intro p x
  exact hout p x

structure Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop where
  run : ∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B)

theorem idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

theorem relaxB {N : ℕ} {A A' B B' : Set (Sig N)} {b b' : ℕ}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)⟩

theorem seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

theorem seq2B {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

theorem extB {N : ℕ} {A B : Set (Sig N)} {b : ℕ} (H : Build A B b) : Build A (A ∪ B) b :=
  relaxB H le_rfl le_rfl le_rfl

theorem transB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build B C c) : Build A C (b + c) :=
  relaxB (seqB H1 (relaxB H2 Set.subset_union_right Set.subset_union_right le_rfl))
    le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

theorem gateB {N : ℕ} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (shape : ((op=.and ∨ op=.or) ∧ deps.length=2) ∨ (op=.not ∧ deps.length=1)) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out shape (fun a hm => ha (hdeps a hm)) hval⟩⟩

theorem notB {N : ℕ} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simpa using hf) (fun _ => rfl)

theorem andB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem orB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

theorem xorB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let s1 : Sig N := fun x => f x || g x
  let s2 : Sig N := fun x => f x && g x
  let s3 : Sig N := fun x => !(s2 x)
  let s4 : Sig N := fun x => s1 x && s3 x
  have h1 : Build A {s1} 1 := orB hf hg
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hf) (Or.inl hg)
  have h3 : Build (A ∪ ({s1} ∪ {s2})) {s3} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({s1} ∪ {s2}) ∪ {s3})) {s4} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have heq : s4 = fun x => xor (f x) (g x) := by
    funext x
    simp only [s4, s3, s2, s1]
    exact (xor_eq_or_and_not_and (f x) (g x)).symm
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

theorem iteB {N : ℕ} {A : Set (Sig N)} {c a b : Sig N}
    (hc : c ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Build A {fun x => if c x then a x else b x} 4 := by
  let nc : Sig N := fun x => !(c x)
  let t1 : Sig N := fun x => c x && a x
  let t2 : Sig N := fun x => nc x && b x
  let out : Sig N := fun x => t1 x || t2 x
  have h1 : Build A {nc} 1 := notB hc
  have h2 : Build (A ∪ {nc}) {t1} 1 := andB (Or.inl hc) (Or.inl ha)
  have h3 : Build (A ∪ ({nc} ∪ {t1})) {t2} 1 :=
    andB (Or.inr (Or.inl rfl)) (Or.inl hb)
  have h4 : Build (A ∪ (({nc} ∪ {t1}) ∪ {t2})) {out} 1 :=
    orB (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  have heq : out = fun x => if c x then a x else b x := by
    funext x
    simp only [out, t1, t2, nc]
    cases c x <;> cases a x <;> cases b x <;> rfl
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

theorem listB {N : ℕ} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))
        Set.subset_union_left Set.subset_union_right le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

theorem finB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : ℕ)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  refine relaxB hl le_rfl ?_ (by simp)
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨List.mem_finRange i, hfi⟩⟩)

theorem finSigB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Sig N) (c : ℕ)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_range.mp hf with ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

theorem fin2SigB {N n1 n2 : ℕ} {A : Set (Sig N)} (F : Fin n1 → Fin n2 → Sig N) (c : ℕ)
    (h : ∀ i j, Build A {F i j} c) :
    Build A {f | ∃ i j, F i j = f} (n1 * (n2 * c)) := by
  have h1 : Build A (⋃ i : Fin n1, Set.range (F i)) (n1 * (n2 * c)) :=
    finB (fun i => Set.range (F i)) (n2 * c) (fun i => finSigB (F i) c (fun j => h i j))
  refine relaxB h1 le_rfl ?_ le_rfl
  rintro f ⟨i, j, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩)

theorem unionB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

theorem andListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using htrue)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.all (fun g => g x)})
        {fun x => (f :: xs).all (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).all (fun g => g x)) =
          (fun x => f x && xs.all (fun g => g x)) := by
        funext x; simp [List.all_cons]
      rw [heq]
      exact andB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

theorem orListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.any (fun g => g x)})
        {fun x => (f :: xs).any (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).any (fun g => g x)) =
          (fun x => f x || xs.any (fun g => g x)) := by
        funext x; simp [List.any_cons]
      rw [heq]
      exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

def xorList (bs : List Bool) : Bool :=
  bs.foldr xor false

theorem xorListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xorList (xs.map fun f => f x)} (4 * xs.length) := by
  induction xs with
  | nil =>
    exact idleB (by simpa [xorList] using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xorList (xs.map fun g => g x)})
        {fun x => xorList ((f :: xs).map fun g => g x)} 4 := by
      have heq : (fun x => xorList ((f :: xs).map fun g => g x)) =
          (fun x => xor (f x) (xorList (xs.map fun g => g x))) := by
        funext x; rfl
      rw [heq]
      exact xorB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp; omega)

theorem iterB {N : ℕ} {α : Type*} (Sigs : ((Fin N → Bool) → α) → Set (Sig N))
    (step : ℕ → α → α) (c : ℕ) (Base : Set (Sig N))
    (hstep : ∀ t (st : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st) (Sigs (fun x => step t (st x))) c) :
    ∀ T (st0 : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st0)
        (Sigs (fun x => (List.range T).foldl (fun s t => step t s) (st0 x)))
        (T * c) := by
  intro T
  induction T with
  | zero =>
    intro st0
    simpa using idleB (A := Base ∪ Sigs st0) (B := Sigs st0) Set.subset_union_right
  | succ T ih =>
    intro st0
    let stT : (Fin N → Bool) → α :=
      fun x => (List.range T).foldl (fun s t => step t s) (st0 x)
    have h1 : Build (Base ∪ Sigs st0) (Sigs stT) (T * c) := ih st0
    have h2 : Build ((Base ∪ Sigs st0) ∪ Sigs stT) (Sigs (fun x => step T (stT x))) c :=
      relaxB (hstep T stT)
        (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
        Set.subset_union_right le_rfl
    have heq : (fun x => (List.range (T + 1)).foldl (fun s t => step t s) (st0 x)) =
        (fun x => step T (stT x)) := by
      funext x
      simp [List.range_succ, List.foldl_append, stT]
    rw [heq]
    exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])

def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orB ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl

def sumListVal {N : ℕ} : List ((Fin N → Bool) → ℕ) → (Fin N → Bool) → ℕ
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

theorem sumListB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (Fs : List ((Fin N → Bool) → ℕ))
    (hFs : ∀ F ∈ Fs, ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal Fs))) (Fs.length * (9 * L)) := by
  induction Fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have : bitsOf L (sumListVal ([] : List ((Fin N → Bool) → ℕ))) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons F Fs ih =>
    have h1 := ih (fun G hG => hFs G (List.mem_cons_of_mem F hG))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal Fs)))
        (Set.range (bitsOf L (fun x => F x + sumListVal Fs x))) (9 * L) :=
      sumTwoB L F (sumListVal Fs) (Or.inl hfalse)
        (fun j => Or.inl (hFs F List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    refine relaxB (seq2B h1 h2) le_rfl Set.subset_union_right ?_
    simp only [List.length_cons]
    ring_nf
    omega


def WordOutputs {N s : Nat} (L : Nat) (F : Fin s→(Fin N→Bool)→Nat) :
    Set (Sig N) := ⋃ i,Set.range (bitsOf L (F i))

def gated {N : Nat} (c : Sig N) (f : (Fin N→Bool)→Nat) : (Fin N→Bool)→Nat :=
  fun x => if c x then f x else 0

def layer {N h s : Nat} (F : Fin h→(Fin N→Bool)→Nat) (E : Fin h→Fin s→Sig N)
    (j : Fin s) : (Fin N→Bool)→Nat :=
  sumListVal ((List.finRange h).map (fun i => gated (E i j) (F i)))

theorem layerBuild {N h s : Nat} {A : Set (Sig N)} (L : Nat)
    (F : Fin h→(Fin N→Bool)→Nat) (E : Fin h→Fin s→Sig N)
    (zero : (fun _ => false) ∈ A) (inputs : ∀ i j,bitsOf L (F i) j ∈ A)
    (select : ∀ i j,E i j ∈ A) :
    Build A (WordOutputs L (layer F E)) (s * (h * (10*L))) := by
  apply finB
  intro dst
  let mask := fun (i : Fin h) => gated (E i dst) (F i)
  have first : Build A (WordOutputs L mask) (h*L) := by
    apply finB
    intro i
    have build := finSigB (A:=A) (bitsOf L (mask i)) 1 (by
      intro j
      have eq : bitsOf L (mask i) j = fun x => E i dst x && bitsOf L (F i) j x := by
        funext x
        cases h : E i dst x <;> simp [mask,gated,bitsOf,h]
      rw [eq]
      exact andB (select i dst) (inputs i j))
    simpa using build
  have add := sumListB (A := A ∪ WordOutputs L mask) L (Or.inl zero)
    ((List.finRange h).map mask) (by
      intro f hf j
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,⟨j,rfl⟩⟩))
  apply relaxB (seq2B first add) le_rfl
  · exact Set.subset_union_right
  · simp; ring_nf; omega

def advance {N s : Nat} (initial : Fin s→(Fin N→Bool)→Nat)
    (steps : List (Fin s→Fin s→Sig N)) :=
  steps.foldl layer initial

theorem layersBuild {N s : Nat} (A : Set (Sig N)) (L : Nat)
    (F : Fin s→(Fin N→Bool)→Nat) (steps : List (Fin s→Fin s→Sig N))
    (zero : (fun _ => false)∈A) (edges : ∀ e∈steps,∀ i j,e i j∈A) :
    Build (A∪WordOutputs L F) (WordOutputs L (advance F steps)) (steps.length*(s*(s*(10*L)))) := by
  induction steps generalizing F with
  | nil => exact idleB Set.subset_union_right
  | cons e es ih =>
    have enter := layerBuild (A:=A∪WordOutputs L F) L F e (Or.inl zero)
      (fun i j => Or.inr (Set.mem_iUnion.mpr ⟨i,⟨j,rfl⟩⟩))
      (fun i j => Or.inl (edges e (.head _) i j))
    have cont := ih (layer F e) (fun k hk => edges k (.tail _ hk))
    have plus : Build ((A∪WordOutputs L F)∪WordOutputs L (layer F e))
        (WordOutputs L (advance (layer F e) es)) (es.length*(s*(s*(10*L)))) :=
      relaxB cont (fun _ q => q.elim (fun h => Or.inl (Or.inl h)) Or.inr)
        Set.subset_union_right le_rfl
    exact relaxB (seq2B enter plus) le_rfl Set.subset_union_right (by simp [Nat.succ_mul,Nat.add_comm])

theorem physical_layers {N s k : Nat} (A : Set (Sig N)) (L : Nat)
    (F : Fin s→(Fin N→Bool)→Nat) (steps : List (Fin s→Fin s→Sig N))
    (start : Scheduled N k (A ∪ WordOutputs L F))
    (zero : (fun _ => false)∈A) (edges : ∀ e∈steps,∀ i j,e i j∈A) :
    ∃ (g : Circuit) (out : Fin s → Fin L → Fin (N+g.size)),
      ReadsBack N g ∧ Strict g ∧ g.size ≤ k+steps.length*(s*(s*(10*L))) ∧
      ∀ i j x,(g.wires (List.ofFn x)).getD (out i j).val false =
        (advance F steps i x).testBit j.val := by
  obtain ⟨c,budget,gs,sz,legal,basis,ws⟩ := (layersBuild A L F steps zero edges).run start le_rfl
  have ready (i : Fin s) (j : Fin L) : ∃ u : Fin (N+gs.length), ∀ x : Fin N→Bool,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD u.val false = (advance F steps i x).testBit j.val := by
    obtain ⟨u,hu,hit⟩ := ws _ (Or.inr (Set.mem_iUnion.mpr ⟨i,⟨j,rfl⟩⟩))
    exact ⟨⟨u,by omega⟩,hit⟩
  choose out ho using ready
  exact ⟨⟨gs,0⟩,out,legal,basis,by change gs.length ≤ _; omega,ho⟩

end PEqualNP.Outside.L_pcx_393_aux
