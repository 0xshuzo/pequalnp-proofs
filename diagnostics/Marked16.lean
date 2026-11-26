import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_134_geo

namespace PNP130Dag

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

inductive Rule (F : Set (LinClause V)) (pi : List (LinClause V)) (i : Fin pi.length)
    : Type
  | ax (inFormula : pi.get i ∈ F)
  | res (j k : Fin pi.length) (hj : i < j) (hk : i < k)
      (valid : IsLinResolvent (pi.get j) (pi.get k) (pi.get i))
  | weak (j : Fin pi.length) (hj : i < j)
      (valid : ∀ a, LinClauseSat a (pi.get j) → LinClauseSat a (pi.get i))

def Rule.parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length)
  | .ax _ => []
  | .res j k _ _ _ => [j, k]
  | .weak j _ _ => [j]

theorem Rule.lt_of_mem_parents {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i j : Fin pi.length} (r : Rule F pi i) (h : j ∈ r.parents) : i < j := by
  cases r with
  | ax _ => simp [parents] at h
  | res a b ha hb _ =>
    simp [parents] at h
    rcases h with rfl | rfl <;> assumption
  | weak a ha _ =>
    simp only [parents, List.mem_singleton] at h
    simpa [h] using ha

def Rule.cons {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (C : LinClause V) (r : Rule F pi i) :
    Rule F (C :: pi) i.succ := by
  cases r with
  | ax h => exact .ax (by simpa using h)
  | res j k hj hk h =>
    exact .res j.succ k.succ (by simpa using hj) (by simpa using hk) (by simpa using h)
  | weak j hj h =>
    exact .weak j.succ (by simpa using hj) (by simpa using h)

theorem line_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) : ∀ i, Nonempty (Rule F pi i) := by
  classical
  induction deriv with
  | nil =>
    intro i
    exact Fin.elim0 i
  | @ax pi C deriv hC ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨.ax (by simpa using hC)⟩
    · exact ⟨(Classical.choice (ih j)).cons C⟩
  | @res pi C D R deriv hC hD hr ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hD
      let j' : Fin pi.length := ⟨j, hj⟩
      let k' : Fin pi.length := ⟨k, hk⟩
      have ej' : pi.get j' = C := ej
      have ek' : pi.get k' = D := ek
      refine ⟨.res j'.succ k'.succ (Fin.succ_pos _) (Fin.succ_pos _) ?_⟩
      change IsLinResolvent (pi.get j') (pi.get k') R
      rwa [ej', ek']
    · exact ⟨(Classical.choice (ih j)).cons R⟩
  | @weak pi C D deriv hC hw ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hC
      let j' : Fin pi.length := ⟨j, hj⟩
      have ej' : pi.get j' = C := ej
      refine ⟨.weak j'.succ (Fin.succ_pos _) ?_⟩
      change ∀ a, LinClauseSat a (pi.get j') → LinClauseSat a D
      rwa [ej']
    · exact ⟨(Classical.choice (ih j)).cons D⟩

noncomputable def choose_rules {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (i : Fin pi.length) : Rule F pi i :=
  Classical.choice (line_rules deriv i)

theorem derivation_dedup {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) :
    ∃ rho, IsLinDerivation F rho ∧ rho.Nodup ∧ rho.Sublist pi ∧
      ∀ c, c ∈ pi ↔ c ∈ rho := by
  classical
  induction deriv with
  | nil =>
    exact ⟨[], .nil, List.nodup_nil, .slnil, fun _ => Iff.rfl⟩
  | @ax pi C deriv hC ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : C ∈ rho
    · refine ⟨rho, hd, nd, sub.cons C, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨C :: rho, .ax hd hC, List.nodup_cons.mpr ⟨h, nd⟩,
        sub.cons_cons C, fun c => by simp [eq]⟩
  | @res pi C D R deriv hC hD hr ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : R ∈ rho
    · refine ⟨rho, hd, nd, sub.cons R, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨R :: rho, .res hd ((eq C).mp hC) ((eq D).mp hD) hr,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons R, fun c => by simp [eq]⟩
  | @weak pi C D deriv hC hw ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : D ∈ rho
    · refine ⟨rho, hd, nd, sub.cons D, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨D :: rho, .weak hd ((eq C).mp hC) hw,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons D, fun c => by simp [eq]⟩

theorem derivation_trim {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (keep : List (Fin pi.length))
    (order : keep.Pairwise (· < ·))
    (closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep) :
    IsLinDerivation F (keep.map pi.get) := by
  induction keep with
  | nil => exact .nil
  | cons i keep ih =>
    obtain ⟨head, later⟩ := List.pairwise_cons.mp order
    have ht : ∀ j ∈ keep, ∀ k ∈ (rules j).parents, k ∈ keep := by
      intro j hj k hk
      have mem := closed j (List.mem_cons_of_mem i hj) k hk
      rcases List.mem_cons.mp mem with eq | hm
      · have hlt := (rules j).lt_of_mem_parents hk
        rw [eq] at hlt
        exact False.elim (not_lt_of_ge (head _ hj).le hlt)
      · exact hm
    have prev := ih later ht
    have hm : ∀ j ∈ (rules i).parents, j ∈ keep := by
      intro j hj
      have hlt := (rules i).lt_of_mem_parents hj
      have mem := closed i List.mem_cons_self j hj
      rcases List.mem_cons.mp mem with eq | mem
      · exact False.elim (hlt.ne eq.symm)
      · exact mem
    generalize eq : rules i = r at hm
    cases r with
    | ax h => exact .ax prev h
    | res j k _ _ h =>
      have hj := hm j (by simp [Rule.parents])
      have hk := hm k (by simp [Rule.parents])
      exact .res prev (List.mem_map_of_mem hj) (List.mem_map_of_mem hk) h
    | weak j _ h =>
      have hj := hm j (by simp [Rule.parents])
      exact .weak prev (List.mem_map_of_mem hj) h

def Parent {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (i j : Fin pi.length) : Prop :=
  j ∈ (rules i).parents

abbrev Reaches {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) := Relation.ReflTransGen (Parent rules)

theorem reachable_of_shortest {F : Set (LinClause V)} {pi : List (LinClause V)}
    (rules : ∀ i, Rule F pi i) (root : Fin pi.length) (hroot : pi.get root = ∅)
    (shortest : ∀ rho, IsLinDerivation F rho → (∅ : LinClause V) ∈ rho → pi.length ≤ rho.length) :
    ∀ i, Reaches rules root i := by
  classical
  let keep := (List.finRange pi.length).filter (fun j => decide (Reaches rules root j))
  have order : keep.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have member (j : Fin pi.length) : j ∈ keep ↔ Reaches rules root j := by
    simp [keep, List.mem_finRange]
  have closed : ∀ i ∈ keep, ∀ j ∈ (rules i).parents, j ∈ keep := by
    intro i hi j hj
    exact (member j).mpr ((member i).mp hi |>.tail hj)
  have deriv := derivation_trim rules keep order closed
  have emptyMem : (∅ : LinClause V) ∈ keep.map pi.get := by
    rw [← hroot]
    exact List.mem_map_of_mem ((member root).mpr .refl)
  have lengthBound := shortest _ deriv emptyMem
  rw [List.length_map] at lengthBound
  have sub : keep.Sublist (List.finRange pi.length) := List.filter_sublist
  have same : keep = List.finRange pi.length :=
    sub.eq_of_length (by have := sub.length_le; simp at this; simp; omega)
  intro i
  exact (member i).mp (same.symm ▸ List.mem_finRange i)

structure ShortestDag (F : Set (LinClause V)) where
  pi : List (LinClause V)
  nodup : pi.Nodup
  root : Fin pi.length
  rootEmpty : pi.get root = ∅
  rules : ∀ i, Rule F pi i
  reachable : ∀ i, Reaches rules root i

theorem shortest_dag {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) (contains : (∅ : LinClause V) ∈ pi) :
    ∃ d : ShortestDag F, d.pi.length ≤ pi.length := by
  classical
  let P (n : Nat) := ∃ rho, IsLinDerivation F rho ∧ (∅ : LinClause V) ∈ rho ∧ rho.length = n
  have exist : ∃ n, P n := ⟨pi.length, pi, deriv, contains, rfl⟩
  obtain ⟨rho, hr, hempty, hlen⟩ := Nat.find_spec exist
  have shortest (tau : List (LinClause V)) (h : IsLinDerivation F tau)
      (he : (∅ : LinClause V) ∈ tau) : rho.length ≤ tau.length := by
    rw [hlen]
    exact Nat.find_min' exist ⟨tau, h, he, rfl⟩
  obtain ⟨delta, hd, nd, sub, eq⟩ := derivation_dedup hr
  have bdd := shortest delta hd ((eq ∅).mp hempty)
  have same : delta = rho := sub.eq_of_length (Nat.le_antisymm sub.length_le bdd)
  have noDup : rho.Nodup := same ▸ nd
  obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.mp hempty
  let root : Fin rho.length := ⟨k, hk⟩
  have rootEmpty : rho.get root = ∅ := ek
  let rules := choose_rules hr
  exact ⟨⟨rho, noDup, root, rootEmpty, rules,
    reachable_of_shortest rules root rootEmpty shortest⟩, shortest pi deriv contains⟩

namespace ShortestDag

variable {F : Set (LinClause V)} (d : ShortestDag F)

def children (i : Fin d.pi.length) : List (Fin d.pi.length) := (d.rules i).parents

theorem children_lt (i j : Fin d.pi.length) (h : j ∈ d.children i) : i < j :=
  (d.rules i).lt_of_mem_parents h

theorem root_val_zero : d.root.val = 0 := by
  let z : Fin d.pi.length := ⟨0, Nat.zero_lt_of_lt d.root.isLt⟩
  have h := d.reachable z
  have le : ∀ v, Reaches d.rules d.root v → d.root ≤ v := by
    intro v hr
    induction hr with
    | refl => exact le_rfl
    | @tail v w _ hp ih => exact ih.trans (d.children_lt v w hp).le
  exact Nat.eq_zero_of_le_zero (le _ h)

theorem exists_parent (j : Fin d.pi.length) (hn : j.val ≠ 0) :
    ∃ i, j ∈ d.children i := by
  have h := d.reachable j
  induction h with
  | refl => exact (hn d.root_val_zero).elim
  | @tail v w hr hp _ => exact ⟨v, hp⟩

def incoming (j : Fin d.pi.length) : ℕ :=
  ∑ i : Fin d.pi.length, (d.children i).count j

theorem incoming_pos (j : Fin d.pi.length) (hn : j.val ≠ 0) : 0 < d.incoming j := by
  obtain ⟨i, hi⟩ := d.exists_parent j hn
  have hpos : 0 < (d.children i).count j := List.count_pos_iff.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun b _ => Nat.zero_le ((d.children b).count j))
    (Finset.mem_univ i))

theorem children_length (i : Fin d.pi.length) : (d.children i).length ≤ 2 := by
  unfold children
  cases d.rules i <;> simp [Rule.parents]

theorem axiom_of_no_children (i : Fin d.pi.length) (h : d.children i = []) :
    d.pi.get i ∈ F := by
  cases hr : d.rules i with
  | ax hf => exact hf
  | res => simp [children, hr, Rule.parents] at h
  | weak => simp [children, hr, Rule.parents] at h

def AxiomIndex := { i : Fin d.pi.length // d.children i = [] }

def axiomClause (i : d.AxiomIndex) : { C : LinClause V // C ∈ F } :=
  ⟨d.pi.get i.val, d.axiom_of_no_children i.val i.property⟩

theorem axiomClause_injective : Function.Injective d.axiomClause := by
  intro a b h
  exact Subtype.ext (d.nodup.injective_get (congrArg Subtype.val h))

private theorem false_res {C D R : LinClause V} (h : IsLinResolvent C D R)
    (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)

theorem false_child_or_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    d.children i = [] ∨ ∃ j ∈ d.children i, ¬ LinClauseSat a (d.pi.get j) := by
  cases hr : d.rules i with
  | ax hae => exact Or.inl (by simp [children, hr, Rule.parents])
  | res j k hj hk hv =>
    rcases false_res hv a hf with eh | eh
    · exact Or.inr ⟨j, by simp [children, hr, Rule.parents], eh⟩
    · exact Or.inr ⟨k, by simp [children, hr, Rule.parents], eh⟩
  | weak j hj hv =>
    exact Or.inr ⟨j, by simp [children, hr, Rule.parents], fun hj' => hf (hv a hj')⟩

theorem reaches_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    ∃ j, Reaches d.rules i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
  have aux (k : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = k →
      ¬ LinClauseSat a (d.pi.get i) →
      ∃ j, Reaches d.rules i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hf
      rcases d.false_child_or_axiom a i hf with e | ⟨j, hj, hn⟩
      · exact ⟨i, .refl, e, hf⟩
      · have edge := d.children_lt i j hj
        have hl : d.pi.length - j.val < k := by
          have hbound := j.isLt
          have hv : i.val < j.val := edge
          omega
        obtain ⟨w, hpath, he, hw⟩ := ih (d.pi.length - j.val) hl j rfl hn
        exact ⟨w, hpath.head hj, he, hw⟩
  exact aux _ i rfl hf

theorem incoming_at_first : d.incoming d.root = 0 := by
  classical
  unfold incoming
  apply Finset.sum_eq_zero
  intro i _
  apply List.count_eq_zero_of_not_mem
  intro h
  have hp : i.val < d.root.val := d.children_lt i d.root h
  rw [d.root_val_zero] at hp
  omega

end ShortestDag

end PNP130Dag

namespace PNP130Dag

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

abbrev Test (V : Type) := Finset V × Bool

def testParity (a : V → Bool) (f : Finset V) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

noncomputable def Rule.labelled {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} : Rule F pi i → List (Fin pi.length × Option (Test V))
  | .ax _ => []
  | .weak j _ _ => [(j, none)]
  | .res j k _ _ hr =>
      let f := Classical.choose hr
      [(j, some (f, true)), (k, some (f, false))]

theorem Rule.labelled_map {F : Set (LinClause V)} {pi : List (LinClause V)}
    {i : Fin pi.length} (r : Rule F pi i) : r.labelled.map Prod.fst = r.parents := by
  cases r <;> rfl

inductive LocalTree (V I : Type)
  | ax (i : I)
  | exit (j : I)
  | weak (i : I) (child : LocalTree V I)
  | res (i : I) (pivot : Finset V) (left right : LocalTree V I)

inductive LocalTree.Route {I : Type} :
    LocalTree V I → I → List (Option (Test V)) → Prop
  | ax (i : I) : Route (.ax i) i []
  | weak {i t j qs} (h : Route t j qs) : Route (.weak i t) j (none :: qs)
  | left {i f l r j qs} (h : Route l j qs) : Route (.res i f l r) j (some (f,true) :: qs)
  | right {i f l r j qs} (h : Route r j qs) : Route (.res i f l r) j (some (f,false) :: qs)

namespace ShortestDag

variable {F : Set (LinClause V)} (d : ShortestDag F)

noncomputable abbrev labels (i : Fin d.pi.length) := (d.rules i).labelled

theorem label_child {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : (j,q) ∈ d.labels i) : j ∈ d.children i := by
  rw [children, ← (d.rules i).labelled_map]
  exact List.mem_map.mpr ⟨(j,q), h, rfl⟩

theorem labelled_of_child {i j : Fin d.pi.length} (h : j ∈ d.children i) :
    ∃ q, (j,q) ∈ d.labels i := by
  rw [children, ← (d.rules i).labelled_map] at h
  obtain ⟨⟨k,q⟩, hk, he⟩ := List.mem_map.mp h
  cases he
  exact ⟨q,hk⟩

theorem res_children_ne {i j k : Fin d.pi.length} (hj : i < j)
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i)) : j ≠ k := by
  rintro rfl
  obtain ⟨f, h0, h1, he⟩ := hr
  have heq : (d.pi.get j).erase (f,false) ∪ (d.pi.get j).erase (f,true) =
      d.pi.get j := by
    ext q
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · exact fun h => h.elim And.right And.right
    · intro h
      by_cases hq : q = (f,false)
      · exact Or.inr ⟨by simp [hq], h⟩
      · exact Or.inl ⟨hq, h⟩
  have eq := d.nodup.injective_get (he.trans heq)
  exact (ne_of_lt hj) eq

theorem labels_unique {i j : Fin d.pi.length} {q r : Option (Test V)}
    (hq : (j,q) ∈ d.labels i) (hr : (j,r) ∈ d.labels i) : q = r := by
  cases h : d.rules i with
  | ax => simp [labels, h, Rule.labelled] at hq
  | weak k hk hw => simp [labels, h, Rule.labelled] at hq hr; exact hq.2.trans hr.2.symm
  | res k l hk hl hv =>
    have hkl := d.res_children_ne hk hv
    simp [labels, h, Rule.labelled] at hq hr
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases hr with ⟨he, rfl⟩ | ⟨he,rfl⟩
    · rfl
    · exact (hkl he).elim
    · exact (hkl he.symm).elim
    · rfl

theorem parent_unique {i k j : Fin d.pi.length} (hin : d.incoming j = 1)
    (hi : j ∈ d.children i) (hk : j ∈ d.children k) : i = k := by
  classical
  by_contra h
  have hci := List.count_pos_iff.mpr hi
  have hck := List.count_pos_iff.mpr hk
  have subset : ({i,k} : Finset (Fin d.pi.length)) ⊆ Finset.univ := Finset.subset_univ _
  have lb := Finset.sum_le_sum_of_subset_of_nonneg subset (fun x _ _ =>
    Nat.zero_le ((d.children x).count j))
  rw [← incoming, hin] at lb
  simp [h] at lb
  omega

def Accepts (a : V → Bool) : Option (Test V) → Prop
  | none => True
  | some (f,b) => testParity a f = b

private theorem res_false_label {i j k : Fin d.pi.length}
    (hr : IsLinResolvent (d.pi.get j) (d.pi.get k) (d.pi.get i))
    (a : V → Bool) (hf : ¬ LinClauseSat a (d.pi.get i)) :
    if testParity a (Classical.choose hr) then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k) := by
  let f := Classical.choose hr
  obtain ⟨_, _, he⟩ := Classical.choose_spec hr
  change (if testParity a f then ¬ LinClauseSat a (d.pi.get j)
    else ¬ LinClauseSat a (d.pi.get k))
  by_cases odd : Odd (f.filter (fun v => a v = true)).card
  · simp [testParity, odd]
    rintro ⟨q,hq,hqs⟩
    apply hf
    refine ⟨q, ?_, hqs⟩
    rw [he]
    refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl
    exact Bool.noConfusion (hqs.1 odd)
  · simp [testParity, odd]
    rintro ⟨q,hq,hqs⟩
    apply hf
    refine ⟨q, ?_, hqs⟩
    rw [he]
    refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hq⟩)
    rintro rfl
    exact odd (hqs.2 rfl)

theorem false_label_or_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    d.children i = [] ∨ ∃ j q, (j,q) ∈ d.labels i ∧ Accepts a q ∧
      ¬ LinClauseSat a (d.pi.get j) := by
  cases h : d.rules i with
  | ax => left; simp [children, h, Rule.parents]
  | weak j hj hw =>
    exact Or.inr ⟨j, none, by simp [labels, h, Rule.labelled], trivial, fun hn => hf (hw a hn)⟩
  | res j k hj hk hr =>
    have hv := d.res_false_label hr a hf
    cases hp : testParity a (Classical.choose hr)
    · exact Or.inr ⟨k, some (Classical.choose hr,false), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩
    · exact Or.inr ⟨j, some (Classical.choose hr,true), by simp [labels, h, Rule.labelled],
        hp, by simpa [hp] using hv⟩

def ActiveStep (a : V → Bool) (i j : Fin d.pi.length) : Prop :=
  ∃ q, (j,q) ∈ d.labels i ∧ Accepts a q ∧
    ¬ LinClauseSat a (d.pi.get i) ∧ ¬ LinClauseSat a (d.pi.get j)

abbrev Active (a : V → Bool) := Relation.ReflTransGen (d.ActiveStep a)

theorem active_axiom (a : V → Bool) (i : Fin d.pi.length)
    (hf : ¬ LinClauseSat a (d.pi.get i)) :
    ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
  have aux (k : ℕ) : ∀ i : Fin d.pi.length, d.pi.length - i.val = k →
      ¬ LinClauseSat a (d.pi.get i) →
      ∃ j, d.Active a i j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hf
      rcases d.false_label_or_axiom a i hf with e | ⟨j, q, hj, ha, hn⟩
      · exact ⟨i, .refl, e, hf⟩
      · have edge : i.val < j.val := d.children_lt i j (d.label_child hj)
        have hb := j.isLt
        have hl : d.pi.length - j.val < k := by omega
        obtain ⟨w, hpath, he, hw⟩ := ih (d.pi.length - j.val) hl j rfl hn
        exact ⟨w, hpath.head ⟨q,hj,ha,hf,hn⟩, he, hw⟩
  exact aux _ i rfl hf

theorem active_initial_clause (a : V → Bool) :
    ∃ j, d.Active a d.root j ∧ d.children j = [] ∧ ¬ LinClauseSat a (d.pi.get j) :=
  d.active_axiom a d.root (by rw [d.rootEmpty]; simp [LinClauseSat])

inductive LocalPath : Fin d.pi.length → Fin d.pi.length → List (Option (Test V)) → Prop
  | nil (i) : LocalPath i i []
  | cons {i j k q qs} (label : (j,q) ∈ d.labels i) (unique : d.incoming j = 1)
      (rest : LocalPath j k qs) : LocalPath i k (q :: qs)

theorem peel_active {a : V → Bool} {i j : Fin d.pi.length} {q : Option (Test V)}
    (h : d.Active a d.root j) (he : (j,q) ∈ d.labels i) (hu : d.incoming j = 1) :
    d.Active a d.root i ∧ Accepts a q ∧ ¬ LinClauseSat a (d.pi.get i) := by
  cases h with
  | refl => have hz := d.incoming_at_first; omega
  | @tail k j hp hs =>
    obtain ⟨r, hr, ar, hnk, _⟩ := hs
    have eq := d.parent_unique hu (d.label_child hr) (d.label_child he)
    subst k
    have eqr := d.labels_unique hr he
    exact ⟨hp, eqr ▸ ar, hnk⟩

theorem local_path_active {a : V → Bool} {i j : Fin d.pi.length} {qs}
    (hp : d.LocalPath i j qs) (ha : d.Active a d.root j)
    (hf : ¬ LinClauseSat a (d.pi.get j)) :
    d.Active a d.root i ∧ ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  induction hp with
  | nil _ => exact ⟨ha, hf, by simp⟩
  | @cons i j k q qs he hu rest ih =>
    obtain ⟨haj, hfj, acc⟩ := ih ha hf
    obtain ⟨hai, aq, hfi⟩ := d.peel_active haj he hu
    exact ⟨hai,hfi,fun r hr => (List.mem_cons.mp hr).elim (fun e => e.symm ▸ aq) (acc r)⟩

noncomputable def unroll (i : Fin d.pi.length) : LocalTree V (Fin d.pi.length) :=
  match d.rules i with
  | .ax _ => .ax i
  | .weak j _hj _ =>
      .weak i (if d.incoming j = 1 then unroll j else .exit j)
  | .res j k _hj _hk h =>
      .res i (Classical.choose h)
        (if d.incoming j = 1 then unroll j else .exit j)
        (if d.incoming k = 1 then unroll k else .exit k)
termination_by d.pi.length - i.val
decreasing_by
  all_goals
    apply Nat.sub_lt_sub_left
    · exact i.isLt
    · first | exact _hj | exact _hk

noncomputable def cutChild (j : Fin d.pi.length) : LocalTree V (Fin d.pi.length) :=
  if d.incoming j = 1 then d.unroll j else .exit j

theorem unroll_ax {i : Fin d.pi.length} {h} (hr : d.rules i = .ax h) :
    d.unroll i = .ax i := by
  rw [unroll, hr]

theorem unroll_weak {i j : Fin d.pi.length} {hj hw}
    (hr : d.rules i = .weak j hj hw) :
    d.unroll i = .weak i (d.cutChild j) := by
  rw [unroll, hr]
  rfl

theorem unroll_res {i j k : Fin d.pi.length} {hj hk hv}
    (hr : d.rules i = .res j k hj hk hv) :
    d.unroll i = .res i (Classical.choose hv) (d.cutChild j) (d.cutChild k) := by
  rw [unroll, hr]
  rfl

theorem no_route_exit {i j : Fin d.pi.length} {qs} :
    ¬ LocalTree.Route (.exit i : LocalTree V _) j qs := by
  intro h
  cases h

theorem route_of_unroll {i j : Fin d.pi.length} {qs}
    (h : LocalTree.Route (d.unroll i) j qs) :
    d.LocalPath i j qs ∧ d.children j = [] := by
  have aux (n : ℕ) : ∀ (i : Fin d.pi.length) qs, d.pi.length - i.val = n →
      LocalTree.Route (d.unroll i) j qs → d.LocalPath i j qs ∧ d.children j = [] := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i qs hn h
      have sub (k : Fin d.pi.length) (lt : i < k) {rs}
          (hk : LocalTree.Route (d.cutChild k) j rs) :
          d.incoming k = 1 ∧ d.LocalPath k j rs ∧ d.children j = [] := by
        by_cases he : d.incoming k = 1
        · rw [cutChild, ite_eq_left he] at hk
          have size : d.pi.length - k.val < n := by
            have hlt : i.val < k.val := lt
            have bound := k.isLt
            omega
          exact ⟨he, ih _ size k rs rfl hk⟩
        · rw [cutChild, ite_eq_right he] at hk
          exact (d.no_route_exit hk).elim
      cases hr : d.rules i with
      | ax ha =>
        rw [d.unroll_ax hr] at h
        cases h
        exact ⟨.nil _, by simp [children, hr, Rule.parents]⟩
      | weak k hlt hv =>
        rw [d.unroll_weak hr] at h
        cases h with
        | weak h =>
          obtain ⟨h1,h2,h3⟩ := sub k hlt h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
      | res k l hk hl hrule =>
        rw [d.unroll_res hr] at h
        cases h with
        | left h =>
          obtain ⟨h1,h2,h3⟩ := sub k hk h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
        | right h =>
          obtain ⟨h1,h2,h3⟩ := sub l hl h
          exact ⟨.cons (by simp [labels,hr,Rule.labelled]) h1 h2,h3⟩
  exact aux _ i qs rfl h

theorem unroll_of_route {i j : Fin d.pi.length} {qs}
    (h : d.LocalPath i j qs) (hax : d.children j = []) :
    LocalTree.Route (d.unroll i) j qs := by
  induction h with
  | nil i =>
    cases hr : d.rules i with
    | ax h => rw [d.unroll_ax hr]; exact .ax i
    | weak => simp [children,hr,Rule.parents] at hax
    | res => simp [children,hr,Rule.parents] at hax
  | @cons i k j q qs he h1 hp ih =>
    have cut : LocalTree.Route (d.cutChild k) j qs := by
      rw [cutChild, ite_eq_left h1]
      exact ih hax
    cases hr : d.rules i with
    | ax => simp [labels,hr,Rule.labelled] at he
    | weak l hlt hv =>
      rw [d.unroll_weak hr]
      simp [labels,hr,Rule.labelled] at he
      obtain ⟨rfl,rfl⟩ := he
      exact .weak cut
    | res l r hl hr' hv =>
      rw [d.unroll_res hr]
      simp [labels,hr,Rule.labelled] at he
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact .left cut
      · exact .right cut

theorem local_path_append {i j k : Fin d.pi.length} {qs rs}
    (h : d.LocalPath i j qs) (g : d.LocalPath j k rs) :
    d.LocalPath i k (qs ++ rs) := by
  induction h with
  | nil => exact g
  | cons h u _ ih =>
    exact .cons h u (ih g)

theorem axiom_component (j : Fin d.pi.length) (hj : d.children j = []) :
    ∃ i qs, d.incoming i ≠ 1 ∧ LocalTree.Route (d.unroll i) j qs := by
  have aux (n : ℕ) : ∀ j : Fin d.pi.length, j.val = n →
      ∃ i qs, d.incoming i ≠ 1 ∧ d.LocalPath i j qs := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro j hn
      by_cases h : d.incoming j = 1
      · have hzero : j.val ≠ 0 := by
          intro hj
          have heq : j = d.root := Fin.ext (hj.trans d.root_val_zero.symm)
          rw [heq, d.incoming_at_first] at h
          contradiction
        obtain ⟨k, hk⟩ := d.exists_parent j hzero
        have lt : k.val < n := hn ▸ d.children_lt k j hk
        obtain ⟨i, qs, h1, hp⟩ := ih k.val lt k rfl
        obtain ⟨q, hq⟩ := d.labelled_of_child hk
        exact ⟨i, qs ++ [q], h1, d.local_path_append hp (.cons hq h (.nil _))⟩
      · exact ⟨j, [], h, .nil j⟩
  obtain ⟨i, qs, hi, hp⟩ := aux j.val j rfl
  exact ⟨i, qs, hi, d.unroll_of_route hp hj⟩

theorem unroll_route_active (a : V → Bool) {i j : Fin d.pi.length} {qs}
    (h : LocalTree.Route (d.unroll i) j qs)
    (unique : ∀ C ∈ F, ¬ LinClauseSat a C → C = d.pi.get j) :
    ¬ LinClauseSat a (d.pi.get i) ∧ ∀ q ∈ qs, Accepts a q := by
  obtain ⟨k, hk, hax, hf⟩ := d.active_initial_clause a
  have heq := d.nodup.injective_get (unique _ (d.axiom_of_no_children k hax) hf)
  subst k
  exact (d.local_path_active (d.route_of_unroll h).1 hk hf).2

end ShortestDag

end PNP130Dag

namespace Pcx130

open PEqualNP.ProofComplexity

abbrev Variable := Fin 5 × Fin 2
abbrev Assignment := Variable → Bool

structure Collision where
  left : Fin 5
  right : Fin 5
  hole : Fin 4
  ordered : left < right

def otherHoles (h : Fin 4) : List (Fin 4) :=
  (List.finRange 4).filter (· != h)

def otherRank (i j p : Fin 5) : ℕ :=
  ((List.finRange 5).filter (fun q => decide (q < p) && q != i && q != j)).length

def sampleHole (i j : Fin 5) (h : Fin 4) (phase : Fin 3) (p : Fin 5) : Fin 4 :=
  if p = i ∨ p = j then h else (otherHoles h).getD ((otherRank i j p + phase.val) % 3) h

def sample (c : Collision) (phase : Fin 3) : Assignment :=
  fun v => (sampleHole c.left c.right c.hole phase v.1).val.testBit v.2.val

def allIn (h : Fin 4) : Assignment := fun v => h.val.testBit v.2.val

theorem sample_hole_facts : ∀ (i j : Fin 5) (h : Fin 4) (r : Fin 3), i < j →
    sampleHole i j h r i = h ∧ sampleHole i j h r j = h ∧
    ∀ p q : Fin 5, p < q →
      (sampleHole i j h r p = sampleHole i j h r q ↔ p = i ∧ q = j) := by
  decide +kernel

theorem bit_geometry : ∀ (i j : Fin 5) (h : Fin 4) (p : Fin 5) (b : Fin 2), i < j →
    ((∀ r : Fin 3, (sampleHole i j h r p).val.testBit b.val = h.val.testBit b.val) ↔
      p = i ∨ p = j) ∧
    ((sampleHole i j h 0 p).val.testBit b.val ^^
      ((sampleHole i j h 1 p).val.testBit b.val ^^
        (sampleHole i j h 2 p).val.testBit b.val)) = h.val.testBit b.val := by
  decide +kernel

theorem sample_bits_xor (c : Collision) (v : Variable) :
    (sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole v :=
  (bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).2

def parity (f : Finset Variable) (a : Assignment) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

theorem parity_insert (a : Assignment) (f : Finset Variable) (v : Variable)
    (fresh : v ∉ f) : parity (insert v f) a = (a v ^^ parity f a) := by
  cases hv : a v
  · simp [parity, Finset.filter_insert, hv]
  · simp [parity, Finset.filter_insert, hv, Finset.card_insert_of_notMem,
      (show v ∉ f.filter (fun v => a v = true) from fun hm => fresh (Finset.mem_of_mem_filter v hm)),
      Nat.odd_add_one]
    let n := (f.filter (fun v => a v = true)).card
    change decide (Even n) = !decide (Odd n)
    by_cases ho : Odd n
    · have he : ¬ Even n := fun h => (Nat.not_odd_iff_even.mpr h) ho
      simp [ho, he]
    · have he : Even n := Nat.not_odd_iff_even.mp ho
      simp [ho, he]

theorem parity_xor (f : Finset Variable) (a b : Assignment) :
    parity f (fun v => a v ^^ b v) = (parity f a ^^ parity f b) := by
  classical
  induction f using Finset.induction_on with
  | empty => simp [parity]
  | insert v f fresh ih =>
    rw [parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, parity_insert _ _ _ fresh, ih]
    cases a v <;> cases b v <;> cases parity f a <;> cases parity f b <;> rfl

theorem allIn_follows (c : Collision) (f : Finset Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, parity f (sample c r) = b) :
    parity f (allIn c.hole) = b := by
  have eq : (fun v => sample c 0 v ^^ (sample c 1 v ^^ sample c 2 v)) = allIn c.hole :=
    funext (sample_bits_xor c)
  rw [← eq, parity_xor, parity_xor, agrees 0, agrees 1, agrees 2]
  cases b <;> rfl

theorem bit_constant (c : Collision) (v : Variable) (b : Bool)
    (agrees : ∀ r : Fin 3, sample c r v = b) : (v.1 = c.left ∨ v.1 = c.right) ∧
      b = allIn c.hole v := by
  have eq := sample_bits_xor c v
  rw [agrees 0, agrees 1, agrees 2] at eq
  have value : b = allIn c.hole v := by cases b <;> simpa using eq
  exact ⟨(bit_geometry c.left c.right c.hole v.1 v.2 c.ordered).1.mp
    (fun r => (agrees r).trans value), value⟩

end Pcx130

namespace Pcx130

def Collision.support (c : Collision) : Finset Variable :=
  Finset.univ.filter (fun v => v.1 = c.left ∨ v.1 = c.right)

theorem support_size (c : Collision) : c.support.card = 4 := by
  have finite : ∀ i j : Fin 5, i < j →
      (Finset.univ.filter (fun v : Variable => v.1 = i ∨ v.1 = j)).card = 4 := by
    decide +kernel
  exact finite c.left c.right c.ordered

def commonSet (i j p q : Fin 5) (h k : Fin 4) : Finset Variable :=
  Finset.univ.filter (fun v =>
    (v.1 = i ∨ v.1 = j) ∧ (v.1 = p ∨ v.1 = q) ∧ allIn h v = allIn k v)

theorem commonSet_card : ∀ (i j p q : Fin 5) (h k : Fin 4), h ≠ k →
    (commonSet i j p q h k).card ≤ 2 := by
  decide +kernel

theorem three_holes_vary : ∀ (h k l : Fin 4) (d : Fin 2), h ≠ k → h ≠ l → k ≠ l →
    ¬ (h.val.testBit d.val = k.val.testBit d.val ∧ h.val.testBit d.val = l.val.testBit d.val) := by
  decide +kernel

theorem parity_singleton (v : Variable) (a : Assignment) : parity {v} a = a v := by
  cases hv : a v <;> simp [parity, Finset.filter_singleton, hv]

end Pcx130

namespace Pcx130

inductive TestTree where
  | ax (c : Collision)
  | exit
  | split (form : Finset Variable) (left right : TestTree)

namespace TestTree

def marks : TestTree → List Collision
  | .ax c => [c]
  | .exit => []
  | .split _ l r => l.marks ++ r.marks

def exits : TestTree → ℕ
  | .ax _ => 0
  | .exit => 1
  | .split _ l r => l.exits + r.exits

def grant (known f : Finset Variable) : Finset Variable :=
  if f.card = 1 then known ∪ f else known

def Shared (cs : List Collision) (known : Finset Variable) : Prop :=
  ∀ v ∈ known, ∃ b : Bool, ∀ c ∈ cs, ∀ r : Fin 3, sample c r v = b

def Route (b : Bool) (f : Finset Variable) (cs : List Collision) : Prop :=
  ∀ c ∈ cs, ∀ r : Fin 3, parity f (sample c r) = b

def Valid : TestTree → Finset Variable → Prop
  | .ax c, known => c.support ⊆ known
  | .exit, _ => True
  | .split f l r, known =>
    Route false f l.marks ∧ Route true f r.marks ∧
      l.Valid (grant known f) ∧ r.Valid (grant known f)

def Routed : TestTree → Prop
  | .ax _ => True
  | .exit => True
  | .split f l r =>
    Route false f l.marks ∧ Route true f r.marks ∧ l.Routed ∧ r.Routed

theorem valid_routed {t : TestTree} {known : Finset Variable} (valid : t.Valid known) :
    t.Routed := by
  induction t generalizing known with
  | ax => trivial
  | exit => trivial
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, validLeft, validRight⟩ := valid
    exact ⟨takesLeft, takesRight, ihl validLeft, ihr validRight⟩

theorem routed_holes {t : TestTree} (routed : t.Routed) :
    (t.marks.map Collision.hole).Nodup := by
  induction t with
  | ax => simp [marks]
  | exit => simp [marks]
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, routeLeft, routeRight⟩ := routed
    rw [marks, List.map_append, List.nodup_append']
    refine ⟨ihl routeLeft, ihr routeRight, ?_⟩
    intro h hl hr
    obtain ⟨c, hc, eqc⟩ := List.mem_map.mp hl
    obtain ⟨d, hd, eqd⟩ := List.mem_map.mp hr
    have even := allIn_follows c f false (takesLeft c hc)
    have odd := allIn_follows d f true (takesRight d hd)
    rw [eqc, ← eqd, odd] at even
    cases even

theorem mark_holes {t : TestTree} {known : Finset Variable} (valid : t.Valid known) :
    (t.marks.map Collision.hole).Nodup :=
  routed_holes (valid_routed valid)

theorem grant_size (known f : Finset Variable) :
    (grant known f).card ≤ known.card + 1 := by
  unfold grant
  split
  · next h => exact (Finset.card_union_le _ _).trans (by omega)
  · omega

theorem shared_grant {cs : List Collision} {known f : Finset Variable} {b : Bool}
    (shared : Shared cs known) (route : Route b f cs) :
    Shared cs (grant known f) := by
  intro v hv
  unfold grant at hv
  split at hv
  · next h =>
    rcases Finset.mem_union.mp hv with hk | hf
    · exact shared v hk
    · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h
      have eq : v = w := Finset.mem_singleton.mp hf
      subst w
      exact ⟨b, fun c hc p => (parity_singleton v (sample c p)).symm.trans (route c hc p)⟩
  · exact shared v hv

theorem shared_pair {cs : List Collision} {known : Finset Variable}
    (nodup : (cs.map Collision.hole).Nodup) (enough : 2 ≤ cs.length)
    (shared : Shared cs known) : known.card ≤ 2 := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp at enough
  · simp at enough
  · have distinct : c.hole ≠ d.hole := by
      intro eq
      have absent := (List.nodup_cons.mp nodup).1
      exact absent (by simp [eq])
    apply (Finset.card_le_card ?_).trans (commonSet_card c.left c.right d.left d.right c.hole d.hole distinct)
    intro v hv
    obtain ⟨b, agree⟩ := shared v hv
    have hc := bit_constant c v b (agree c (by simp))
    have hd := bit_constant d v b (agree d (by simp))
    simpa [commonSet] using And.intro hc.1 (And.intro hd.1 (hc.2.symm.trans hd.2))

theorem shared_three {cs : List Collision} {known : Finset Variable}
    (nodup : (cs.map Collision.hole).Nodup) (enough : 3 ≤ cs.length)
    (shared : Shared cs known) : known.card = 0 := by
  rcases cs with _ | ⟨c, _ | ⟨d, _ | ⟨g, rest⟩⟩⟩
  · simp at enough
  · simp at enough
  · simp at enough
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨b, agree⟩ := shared v hv
    have hc := bit_constant c v b (agree c (by simp))
    have hd := bit_constant d v b (agree d (by simp))
    have hg := bit_constant g v b (agree g (by simp))
    have first := List.nodup_cons.mp nodup
    have second := List.nodup_cons.mp first.2
    apply three_holes_vary c.hole d.hole g.hole v.2
    · intro eq
      exact first.1 (by simp [eq])
    · intro eq
      exact first.1 (by simp [eq])
    · intro eq
      exact second.1 (by simp [eq])
    · exact ⟨hc.2.symm.trans hd.2, hc.2.symm.trans hg.2⟩

private theorem arithmetic (k₀ k₁ e₀ e₁ d d' : ℕ)
    (increase : d' ≤ d + 1)
    (pairCredit : 2 ≤ k₀ + k₁ → d ≤ 2)
    (tripleCredit : 3 ≤ k₀ + k₁ → d = 0)
    (leftEmpty : k₀ = 0 → 1 ≤ e₀) (rightEmpty : k₁ = 0 → 1 ≤ e₁)
    (leftSmall : k₀ = 1 ∨ k₀ = 2 → 4 ≤ e₀ + d')
    (rightSmall : k₁ = 1 ∨ k₁ = 2 → 4 ≤ e₁ + d')
    (leftBig : 3 ≤ k₀ → 6 ≤ e₀) (rightBig : 3 ≤ k₁ → 6 ≤ e₁) :
    (k₀ + k₁ = 0 → 1 ≤ e₀ + e₁) ∧
    (k₀ + k₁ = 1 ∨ k₀ + k₁ = 2 → 4 ≤ e₀ + e₁ + d) ∧
    (3 ≤ k₀ + k₁ → 6 ≤ e₀ + e₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have l := leftEmpty (by omega)
    omega
  · intro h
    by_cases l : k₀ = 0
    · have e := leftEmpty l
      have r := rightSmall (by omega)
      omega
    by_cases r : k₁ = 0
    · have e := rightEmpty r
      have l' := leftSmall (by omega)
      omega
    have dl := leftSmall (by omega)
    have dr := rightSmall (by omega)
    have dh := pairCredit (by omega)
    omega
  · intro h
    by_cases l : 3 ≤ k₀
    · have e := leftBig l
      omega
    by_cases r : 3 ≤ k₁
    · have e := rightBig r
      omega
    have dh := tripleCredit h
    have dl := leftSmall (by omega)
    have dr := rightSmall (by omega)
    omega

theorem exits_lower_aux (t : TestTree) {known : Finset Variable}
    (valid : t.Valid known) (shared : Shared t.marks known) :
    (t.marks.length = 0 → 1 ≤ t.exits) ∧
    (t.marks.length = 1 ∨ t.marks.length = 2 → 4 ≤ t.exits + known.card) ∧
    (3 ≤ t.marks.length → 6 ≤ t.exits) := by
  induction t generalizing known with
  | exit => simp [marks, exits]
  | ax c =>
    have enough := Finset.card_le_card (show c.support ⊆ known from valid)
    rw [support_size] at enough
    simpa [marks, exits] using enough
  | split f l r ihl ihr =>
    obtain ⟨takesLeft, takesRight, validLeft, validRight⟩ := valid
    have knownLeft : Shared l.marks known := by
      intro v hv
      obtain ⟨b, agrees⟩ := shared v hv
      exact ⟨b, fun c hc => agrees c (List.mem_append_left _ hc)⟩
    have knownRight : Shared r.marks known := by
      intro v hv
      obtain ⟨b, agrees⟩ := shared v hv
      exact ⟨b, fun c hc => agrees c (List.mem_append_right _ hc)⟩
    obtain ⟨l₀, l₁, l₂⟩ := ihl validLeft (shared_grant knownLeft takesLeft)
    obtain ⟨r₀, r₁, r₂⟩ := ihr validRight (shared_grant knownRight takesRight)
    have nodup := mark_holes (t := .split f l r) (known := known)
      ⟨takesLeft, takesRight, validLeft, validRight⟩
    have pairCredit (h : 2 ≤ l.marks.length + r.marks.length) : known.card ≤ 2 :=
      shared_pair nodup (by simpa [marks] using h) shared
    have tripleCredit (h : 3 ≤ l.marks.length + r.marks.length) : known.card = 0 :=
      shared_three nodup (by simpa [marks] using h) shared
    simpa [marks, exits] using
      arithmetic l.marks.length r.marks.length l.exits r.exits known.card (grant known f).card
        (grant_size known f) pairCredit tripleCredit l₀ r₀ l₁ r₁ l₂ r₂

theorem marks_at_most_four (t : TestTree) (routed : t.Routed) :
    t.marks.length ≤ 4 := by
  classical
  have nd := routed_holes routed
  have h := (Finset.card_le_univ ((t.marks.map Collision.hole).toFinset))
  rw [List.toFinset_card_of_nodup nd, List.length_map, Fintype.card_fin] at h
  exact h

theorem pure_exit_bound (t : TestTree) {known : Finset Variable}
    (valid : t.Valid known) (shared : Shared t.marks known) :
    2 * t.marks.length ≤ t.exits + 2 := by
  obtain ⟨_, small, large⟩ := exits_lower_aux t valid shared
  have max := marks_at_most_four t (valid_routed valid)
  by_cases h : t.marks.length ≤ 1
  · omega
  by_cases h' : t.marks.length = 2
  · have fits := shared_pair (mark_holes valid) (by omega) shared
    have bound := small (Or.inr h')
    omega
  · have bound := large (by omega)
    omega

end TestTree

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

def bits (h : Fin 4) : Fin 2 → Bool := fun b => h.val.testBit b.val

def holeOf (a : Fin 2 → Bool) : Fin 4 :=
  if a 1 then (if a 0 then 3 else 2) else (if a 0 then 1 else 0)

theorem bits_hole (a : Fin 2 → Bool) : bits (holeOf a) = a := by
  funext b
  cases h0 : a 0 <;> cases h1 : a 1 <;> fin_cases b <;> simp [holeOf, bits, h0, h1] <;> rfl

theorem hole_bits : ∀ h : Fin 4, holeOf (bits h) = h := by decide +kernel

theorem bits_injective : Function.Injective bits := by
  intro h k eq
  rw [← hole_bits h, ← hole_bits k, eq]

def pairClause (i j : Fin 5) (a : Fin 2 → Bool) : Clause Variable :=
  Finset.univ.image (fun b : Fin 2 => ((i, b), !a b)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j, b), !a b))

def Collision.clause (c : Collision) : LinClause Variable :=
  linOfClause (pairClause c.left c.right (bits c.hole))

abbrev Formula := (fun C => linOfClause C) '' BPHP 5 2

theorem Collision.mem_formula (c : Collision) : c.clause ∈ Formula := by
  exact ⟨pairClause c.left c.right (bits c.hole), ⟨c.left, c.right, bits c.hole, c.ordered.ne, rfl⟩, rfl⟩

theorem clause_key {D : LinClause Variable} (mem : D ∈ Formula) :
    ∃ c : Collision, D = c.clause := by
  obtain ⟨D0, ⟨i,j,a,hne,rfl⟩, rfl⟩ := mem
  rcases lt_or_gt_of_ne hne with forward | backward
  · exact ⟨⟨i,j,holeOf a,forward⟩, by simp [Collision.clause, pairClause, bits_hole]⟩
  · exact ⟨⟨j,i,holeOf a,backward⟩, by simp [Collision.clause, pairClause, bits_hole, Finset.union_comm]⟩

private theorem clause_iff (v : Variable) (s : Bool) (a : Assignment) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem falsifies_pair_iff (i j : Fin 5) (b : Fin 2 → Bool) (a : Assignment) :
    ¬ LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∀ q, a (i,q) = b q) ∧ (∀ q, a (j,q) = b q) := by
  have eval : LinClauseSat a (linOfClause (pairClause i j b)) ↔
      (∃ q, a (i,q) = !(b q)) ∨ (∃ q, a (j,q) = !(b q)) := by
    unfold LinClauseSat linOfClause pairClause
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨_, (⟨q, rfl⟩ | ⟨q, rfl⟩), rfl⟩, sat⟩
      · exact Or.inl ⟨q, (clause_iff _ _ _).mp sat⟩
      · exact Or.inr ⟨q, (clause_iff _ _ _).mp sat⟩
    · rintro (⟨q, e⟩ | ⟨q,e⟩)
      · exact ⟨_, ⟨_, Or.inl ⟨q,rfl⟩, rfl⟩, (clause_iff _ _ _).mpr e⟩
      · exact ⟨_, ⟨_, Or.inr ⟨q,rfl⟩, rfl⟩, (clause_iff _ _ _).mpr e⟩
  rw [eval]
  constructor
  · intro hn
    refine ⟨fun q => ?_, fun q => ?_⟩
    · have no : a (i,q) ≠ !(b q) := fun e => hn (Or.inl ⟨q,e⟩)
      cases hv : a (i,q) <;> cases hb : b q <;> simp_all
    · have no : a (j,q) ≠ !(b q) := fun e => hn (Or.inr ⟨q,e⟩)
      cases hv : a (j,q) <;> cases hb : b q <;> simp_all
  · rintro ⟨l,r⟩ (⟨q,e⟩ | ⟨q,e⟩)
    · have eq := l q
      rw [eq] at e
      cases h : b q <;> simp [h] at e
    · have eq := r q
      rw [eq] at e
      cases h : b q <;> simp [h] at e

theorem sample_falsifies (c : Collision) (r : Fin 3) :
    ¬ LinClauseSat (sample c r) c.clause := by
  have h := sample_hole_facts c.left c.right c.hole r c.ordered
  exact (falsifies_pair_iff _ _ _ _).mpr
    ⟨fun q => by simp [sample, bits, h.1], fun q => by simp [sample, bits, h.2.1]⟩

theorem unique_collision (c d : Collision) (r : Fin 3)
    (falsified : ¬ LinClauseSat (sample c r) d.clause) : c = d := by
  obtain ⟨l,r'⟩ := (falsifies_pair_iff _ _ _ _).mp falsified
  have lh : sampleHole c.left c.right c.hole r d.left = d.hole :=
    bits_injective (funext l)
  have rh : sampleHole c.left c.right c.hole r d.right = d.hole :=
    bits_injective (funext r')
  have samples := sample_hole_facts c.left c.right c.hole r c.ordered
  obtain ⟨leftEq,rightEq⟩ := (samples.2.2 d.left d.right d.ordered).mp (lh.trans rh.symm)
  have holeEq : c.hole = d.hole := by rw [leftEq, samples.1] at lh; exact lh
  cases c; cases d; simp_all

theorem sample_only_axiom (c : Collision) (r : Fin 3) {D : LinClause Variable}
    (mem : D ∈ Formula) (falsified : ¬ LinClauseSat (sample c r) D) : D = c.clause := by
  obtain ⟨d, rfl⟩ := clause_key mem
  rw [← unique_collision c d r falsified]

theorem clause_injective : Function.Injective Collision.clause := by
  intro c d same
  exact unique_collision c d 0 (same ▸ sample_falsifies c 0)

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

abbrev CollisionData := { t : Fin 5 × Fin 5 × Fin 4 // t.1 < t.2.1 }

def collisionEquiv : Collision ≃ CollisionData where
  toFun c := ⟨⟨c.left,c.right,c.hole⟩,c.ordered⟩
  invFun t := ⟨t.val.1,t.val.2.1,t.val.2.2,t.property⟩
  left_inv := by rintro ⟨i,j,h,p⟩; rfl
  right_inv := by rintro ⟨⟨i,j,h⟩,p⟩; rfl

instance : Fintype Collision := Fintype.ofEquiv CollisionData collisionEquiv.symm

theorem collision_count : Fintype.card Collision = 40 :=
  (Fintype.card_congr collisionEquiv).trans (by decide +kernel)

theorem Collision.support_has_atom (c : Collision) {v : Variable} (mem : v ∈ c.support) :
    ({v}, !allIn c.hole v) ∈ c.clause := by
  have sides : v.1 = c.left ∨ v.1 = c.right := by simpa [Collision.support] using mem
  rcases v with ⟨i,b⟩
  rcases sides with e | e
  · change i = c.left at e
    subst i
    exact Finset.mem_image.mpr ⟨_, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩
  · change i = c.right at e
    subst i
    exact Finset.mem_image.mpr ⟨_, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), rfl⟩

theorem Collision.atoms_are_singleton (c : Collision) {q : LinEq Variable} (mem : q ∈ c.clause) :
    q.1.card = 1 := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp mem
  simp

end Pcx130

namespace Pcx130

open PEqualNP.ProofComplexity

def singletonVars (C : LinClause Variable) : Finset Variable :=
  Finset.univ.filter (fun v => ∃ b : Bool, ({v}, b) ∈ C)

theorem mem_singletonVars (C : LinClause Variable) (v : Variable) :
    v ∈ singletonVars C ↔ ∃ b : Bool, ({v}, b) ∈ C := by
  simp [singletonVars]

theorem support_subset_singletons (c : Collision) : c.support ⊆ singletonVars c.clause := by
  intro v mem
  exact (mem_singletonVars _ _).mpr ⟨_, c.support_has_atom mem⟩

theorem shared_from_clause (C : LinClause Variable) (cs : List Collision)
    (bad : ∀ c ∈ cs, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) C) :
      TestTree.Shared cs (singletonVars C) := by
  intro v hv
  obtain ⟨b, hb⟩ := (mem_singletonVars _ _).mp hv
  refine ⟨!b, fun c hc p => ?_⟩
  have diff : sample c p v ≠ b := fun h =>
    bad c hc p ⟨({v}, b), hb, (clause_iff _ _ _).mpr h⟩
  cases hv : sample c p v <;> cases b <;> simp_all

theorem grant_old {known f : Finset Variable} : known ⊆ TestTree.grant known f := by
  unfold TestTree.grant
  split
  · exact Finset.subset_union_left
  · exact Finset.Subset.refl _

theorem grant_test {known f : Finset Variable} (h : f.card = 1) :
    f ⊆ TestTree.grant known f := by
  simpa [TestTree.grant, h] using (Finset.subset_union_right (s₁ := known) (s₂ := f))

theorem carry_singletons {C D R : LinClause Variable} {f known : Finset Variable}
    (resolve : R = C.erase (f, false) ∪ D.erase (f, true))
    (knownEnough : singletonVars R ⊆ known) :
    singletonVars C ⊆ TestTree.grant known f ∧ singletonVars D ⊆ TestTree.grant known f := by
  constructor <;> intro v hv <;> obtain ⟨b, hb⟩ := (mem_singletonVars _ _).mp hv
  · by_cases eq : ({v} : Finset Variable) = f
    · subst f
      exact grant_test (by simp) (Finset.mem_singleton_self _)
    · have persists : ({v}, b) ∈ R := resolve ▸ Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨fun h => eq (congrArg Prod.fst h), hb⟩)
      exact grant_old (knownEnough ((mem_singletonVars _ _).mpr ⟨_, persists⟩))
  · by_cases eq : ({v} : Finset Variable) = f
    · subst f
      exact grant_test (by simp) (Finset.mem_singleton_self _)
    · have persists : ({v}, b) ∈ R := resolve ▸ Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨fun h => eq (congrArg Prod.fst h), hb⟩)
      exact grant_old (knownEnough ((mem_singletonVars _ _).mpr ⟨_, persists⟩))

end Pcx130

namespace Pcx130.TestTree

open PEqualNP.ProofComplexity

inductive Certified : TestTree → LinClause Variable → Prop
  | ax (c : Collision) : Certified (.ax c) c.clause
  | exit (C : LinClause Variable) : Certified .exit C
  | split {l r : TestTree} {L R C : LinClause Variable} (f : Finset Variable)
      (left : Certified l L) (right : Certified r R)
      (res : C = R.erase (f,false) ∪ L.erase (f,true)) : Certified (.split f l r) C

theorem valid_of_certified {t : TestTree} {C : LinClause Variable} {known : Finset Variable}
    (cert : Certified t C) (routed : t.Routed) (init : singletonVars C ⊆ known) :
    t.Valid known := by
  induction cert generalizing known with
  | ax c => exact (support_subset_singletons c).trans init
  | exit => trivial
  | split f _ _ resolvent ihl ihr =>
    obtain ⟨takesLeft, takesRight, routeLeft, routeRight⟩ := routed
    obtain ⟨keepRight, keepLeft⟩ := carry_singletons resolvent init
    exact ⟨takesLeft, takesRight, ihl routeLeft keepLeft, ihr routeRight keepRight⟩

theorem cost_of_certified {t : TestTree} {C : LinClause Variable}
    (cert : Certified t C) (routed : t.Routed)
    (bad : ∀ c ∈ t.marks, ∀ r : Fin 3, ¬ LinClauseSat (sample c r) C) :
    2 * t.marks.length ≤ t.exits + 2 :=
  pure_exit_bound t (valid_of_certified cert routed (Finset.Subset.refl _))
    (shared_from_clause C t.marks bad)

end Pcx130.TestTree

namespace Pcx130

theorem tight_accounting
    (components mergeExcess weakenings weakComponents exitEdges weakExits : ℕ)
    (enoughComponents : 40 ≤ 4 * components)
    (connected : components ≤ mergeExcess + 1)
    (budget : mergeExcess + weakenings ≤ 16)
    (weakCount : weakComponents ≤ weakenings)
    (edgeCount : exitEdges + 1 = components + mergeExcess)
    (pureCost : 80 + weakExits ≤ exitEdges + 6 * weakComponents + 2 * components) :
    components = 10 ∧ mergeExcess = 9 ∧ weakenings = 7 ∧
      weakComponents = 7 ∧ exitEdges = 18 ∧ weakExits = 0 := by
  omega

theorem pair_exit_cost {fixed shared before left right : ℕ}
    (common : shared ≤ 2)
    (initial : fixed ≤ shared)
    (prefixCost : shared ≤ before + fixed)
    (leftNeeded : 3 ≤ shared + left)
    (rightNeeded : 3 ≤ shared + right) :
    4 ≤ before + left + right + fixed := by
  omega

theorem pure_exit_cost {k e : ℕ} (cap : k ≤ 4)
    (pair : k = 2 → 2 ≤ e)
    (triple : k = 3 → 6 ≤ e)
    (quad : k = 4 → 6 ≤ e) :
    2 * k ≤ e + 2 := by
  omega

theorem no_small_proof
    (components mergeExcess weakenings weakComponents exitEdges weakExits : ℕ)
    (enoughComponents : 40 ≤ 4 * components)
    (connected : components ≤ mergeExcess + 1)
    (edgeCount : exitEdges + 1 = components + mergeExcess)
    (weakCount : weakComponents ≤ weakenings)
    (pureCost : 80 + weakExits ≤ exitEdges + 6 * weakComponents + 2 * components)
    (sinks : exitEdges = 18 → weakExits = 0 → components = 10 →
        weakComponents = 7 → 2 * weakComponents ≤ weakenings) :
    17 ≤ mergeExcess + weakenings := by
  by_contra cap
  have tight := tight_accounting components mergeExcess weakenings weakComponents exitEdges
    weakExits enoughComponents connected (by omega) weakCount edgeCount pureCost
  obtain ⟨cc, mm, ww, wc, ee, we⟩ := tight
  have extra := sinks ee we cc wc
  omega

end Pcx130

namespace PNP130Dag.ShortestDag

open PEqualNP.ProofComplexity Pcx130

variable (d : ShortestDag Formula)

noncomputable def keyAt (i : Fin d.pi.length) : Collision :=
  if h : d.children i = [] then Classical.choose (clause_key (d.axiom_of_no_children i h))
  else ⟨0, 1, 0, by decide⟩

theorem keyAt_clause {i : Fin d.pi.length} (hi : d.children i = []) :
    (d.keyAt i).clause = d.pi.get i := by
  rw [keyAt, dite_eq_left hi]
  exact (Classical.choose_spec (clause_key (d.axiom_of_no_children i hi))).symm

theorem keyAt_injective {i j : Fin d.pi.length} (hi : d.children i = [])
    (hj : d.children j = []) (same : d.keyAt i = d.keyAt j) : i = j := by
  apply d.nodup.injective_get
  rw [← d.keyAt_clause hi, ← d.keyAt_clause hj, same]

theorem keyAt_surjective (c : Collision) : ∃ i : Fin d.pi.length,
    d.children i = [] ∧ d.keyAt i = c := by
  obtain ⟨i, _, hi, bad⟩ := d.active_initial_clause (sample c 0)
  refine ⟨i, hi, clause_injective ?_⟩
  rw [d.keyAt_clause hi]
  exact sample_only_axiom c 0 (d.axiom_of_no_children i hi) bad

noncomputable def axiomKeyEquiv : d.AxiomIndex ≃ Collision :=
  Equiv.ofBijective (fun i => d.keyAt i.val) ⟨by
    intro i j eq
    exact Subtype.ext (d.keyAt_injective i.property j.property eq), by
    intro c
    obtain ⟨i,h,e⟩ := d.keyAt_surjective c
    exact ⟨⟨i,h⟩,e⟩⟩

theorem axiom_count : (Finset.univ.filter (fun i => (d.children i).length = 0)).card = 40 := by
  classical
  let s : Finset (Fin d.pi.length) := Finset.univ.filter (fun i => (d.children i).length = 0)
  let equiv : (↑s : Type) ≃ d.AxiomIndex :=
    { toFun := fun i => ⟨i.val, List.length_eq_zero_iff.mp ((Finset.mem_filter.mp i.property).2)⟩
      invFun := fun i => ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [i.property]⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype d.AxiomIndex := Fintype.ofEquiv (↑s : Type) equiv
  calc
    s.card = Fintype.card (↑s : Type) := (Fintype.card_coe s).symm
    _ = Fintype.card Collision := Fintype.card_congr (equiv.trans d.axiomKeyEquiv)
    _ = 40 := collision_count

noncomputable def actualTree : LocalTree Variable (Fin d.pi.length) → TestTree
  | .ax i => .ax (d.keyAt i)
  | .exit _ => .exit
  | .weak _ t => actualTree t
  | .res _ f l r => .split f (actualTree r) (actualTree l)

theorem mark_route (t : LocalTree Variable (Fin d.pi.length)) {c : Collision}
    (mem : c ∈ (d.actualTree t).marks) :
    ∃ j qs, LocalTree.Route t j qs ∧ d.keyAt j = c := by
  induction t with
  | ax i =>
    simp [actualTree, TestTree.marks] at mem
    exact ⟨i, [], .ax i, mem.symm⟩
  | exit => simp [actualTree, TestTree.marks] at mem
  | weak _ t ih =>
    obtain ⟨j,qs,rt,eq⟩ := ih mem
    exact ⟨j, none :: qs, .weak rt, eq⟩
  | res _ f l r ihl ihr =>
    change c ∈ (d.actualTree r).marks ++ (d.actualTree l).marks at mem
    rcases List.mem_append.mp mem with hr | hl
    · obtain ⟨j,qs,rt,eq⟩ := ihr hr
      exact ⟨j, some (f,false) :: qs, .right rt, eq⟩
    · obtain ⟨j,qs,rt,eq⟩ := ihl hl
      exact ⟨j, some (f,true) :: qs, .left rt, eq⟩

theorem route_mark {t : LocalTree Variable (Fin d.pi.length)} {i : Fin d.pi.length} {qs}
    (route : LocalTree.Route t i qs) : d.keyAt i ∈ (d.actualTree t).marks := by
  induction route with
  | ax => simp [actualTree, TestTree.marks]
  | weak _ ih => exact ih
  | left _ ih => exact List.mem_append_right _ ih
  | right _ ih => exact List.mem_append_left _ ih

theorem actualTree_routed (t : LocalTree Variable (Fin d.pi.length))
    (phases : ∀ j qs, LocalTree.Route t j qs → ∀ r : Fin 3, ∀ q ∈ qs,
      Accepts (sample (d.keyAt j) r) q) : (d.actualTree t).Routed := by
  induction t with
  | ax => trivial
  | exit => trivial
  | weak _ t ih =>
    exact ih (fun j qs route r q hq => phases j (none :: qs) (.weak route) r q (List.mem_cons_of_mem _ hq))
  | res _ f l r ihl ihr =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc phase
      obtain ⟨j,qs,route,rfl⟩ := d.mark_route r hc
      exact phases j _ (.right route) phase _ (List.mem_cons_self)
    · intro c hc phase
      obtain ⟨j,qs,route,rfl⟩ := d.mark_route l hc
      exact phases j _ (.left route) phase _ (List.mem_cons_self)
    · exact ihr (fun j qs route r q hq => phases j (some (f,false) :: qs) (.right route) r q (List.mem_cons_of_mem _ hq))
    · exact ihl (fun j qs route r q hq => phases j (some (f,true) :: qs) (.left route) r q (List.mem_cons_of_mem _ hq))

theorem marked_sample_route {i j : Fin d.pi.length} {qs}
    (route : LocalTree.Route (d.unroll i) j qs) (r : Fin 3) :
    ¬ LinClauseSat (sample (d.keyAt j) r) (d.pi.get i) ∧
      ∀ q ∈ qs, Accepts (sample (d.keyAt j) r) q := by
  refine d.unroll_route_active _ route (fun C hC bad => ?_)
  rw [← d.keyAt_clause (d.route_of_unroll route).2]
  exact sample_only_axiom _ _ hC bad

theorem actual_unroll_routed (i : Fin d.pi.length) :
    (d.actualTree (d.unroll i)).Routed :=
  d.actualTree_routed _ (fun _ _ route r => (d.marked_sample_route route r).2)

theorem actual_unroll_false (i : Fin d.pi.length) :
    ∀ c ∈ (d.actualTree (d.unroll i)).marks, ∀ r : Fin 3,
      ¬ LinClauseSat (sample c r) (d.pi.get i) := by
  intro c hc r
  obtain ⟨j,qs,route,rfl⟩ := d.mark_route (d.unroll i) hc
  exact (d.marked_sample_route route r).1

end PNP130Dag.ShortestDag


namespace Pcx130
open PEqualNP.ProofComplexity

def colors (h : Fin 4) (t : Fin 6) (p : Fin 3) : Fin 4 :=
  (otherHoles h).getD ((if t.val < 3 then p.val+t.val else 3-p.val+t.val) % 3) h
def fillHole (i j : Fin 5) (h : Fin 4) (z : Fin 3 → Fin 4) (p : Fin 5) : Fin 4 :=
  if p=i ∨ p=j then h else z ⟨otherRank i j p % 3, by omega⟩
def fillA (c : Collision) (z : Fin 3 → Fin 4) : Assignment :=
  fun v => bits (fillHole c.left c.right c.hole z v.1) v.2
def six (c : Collision) (t : Fin 6) := fillA c (colors c.hole t)
set_option maxRecDepth 8192 in
theorem six_hole_facts : ∀ (i j : Fin 5) (h : Fin 4) (t : Fin 6), i<j →
    (fillHole i j h (colors h t) i=h) ∧
    (fillHole i j h (colors h t) j=h) ∧
    ∀ p q : Fin 5, p<q →
      (fillHole i j h (colors h t) p=fillHole i j h (colors h t) q ↔ p=i ∧ q=j) := by
  decide +kernel

theorem six_unique (c d : Collision) (t : Fin 6) (falsified : ¬LinClauseSat (six c t) d.clause) :
    c=d := by
  obtain ⟨l,r'⟩ := (falsifies_pair_iff _ _ _ _).mp falsified
  have lh : fillHole c.left c.right c.hole (colors c.hole t) d.left=d.hole := bits_injective (funext l)
  have rh : fillHole c.left c.right c.hole (colors c.hole t) d.right=d.hole := bits_injective (funext r')
  have facts := six_hole_facts c.left c.right c.hole t c.ordered
  obtain ⟨leftEq,rightEq⟩ := (facts.2.2 d.left d.right d.ordered).mp (lh.trans rh.symm)
  have holeEq : c.hole=d.hole := by rw [leftEq,facts.1] at lh; exact lh
  cases c; cases d; simp_all

def localRow (h x y : Fin 4) (j : Fin 3) : Fin 4 :=
  if j.val=0 then x else if j.val=1 then y else ⟨(h.val ^^^ x.val ^^^ y.val)%4,by omega⟩
def witnesses : List (Fin 6 × Fin 6 × Fin 6) := [(0, 1, 2), (0, 4, 5), (0, 2, 4), (0, 1, 5), (0, 1, 4), (0, 2, 5), (0, 0, 0), (0, 0, 3), (0, 3, 4), (0, 0, 4), (0, 1, 3), (0, 0, 1), (0, 2, 3), (0, 0, 2), (0, 0, 5), (0, 3, 5), (0, 2, 5), (0, 1, 4), (0, 0, 0), (0, 0, 3), (0, 4, 5), (0, 1, 2), (0, 2, 4), (0, 1, 5), (0, 0, 4), (0, 3, 4), (0, 1, 3), (0, 0, 1), (0, 0, 2), (0, 2, 3), (0, 0, 5), (0, 3, 5), (0, 2, 5), (0, 0, 0), (0, 1, 4), (0, 0, 3), (0, 0, 4), (0, 1, 3), (0, 3, 4), (0, 0, 1), (0, 4, 5), (0, 2, 4), (0, 1, 2), (0, 1, 5), (0, 0, 2), (0, 0, 5), (0, 2, 3), (0, 3, 5), (0, 2, 5), (0, 0, 0), (0, 0, 3), (0, 1, 4), (0, 0, 4), (0, 1, 3), (0, 0, 1), (0, 3, 4), (0, 0, 2), (0, 0, 5), (0, 3, 5), (0, 2, 3), (0, 4, 5), (0, 2, 4), (0, 1, 5), (0, 1, 2)]

def witness (h x y : Fin 4) := witnesses.getD (16*h.val+4*x.val+y.val) (0,0,0)
set_option maxRecDepth 8192 in
theorem covers : ∀ (h x y : Fin 4) (j : Fin 3) (b : Fin 2),
    bits (localRow h x y j) b = (bits (colors h (witness h x y).1 j) b ^^
      (bits (colors h (witness h x y).2.1 j) b ^^ bits (colors h (witness h x y).2.2 j) b)) := by
  decide +kernel
theorem fills (c : Collision) (x y : Fin 4) :
    fillA c (localRow c.hole x y) =
    fun v => six c (witness c.hole x y).1 v ^^
      (six c (witness c.hole x y).2.1 v ^^ six c (witness c.hole x y).2.2 v) := by
  funext v
  unfold six fillA fillHole
  by_cases h : v.1=c.left ∨ v.1=c.right
  · simp only [if_pos h]
    cases bits c.hole v.2 <;> rfl
  · simp only [if_neg h]
    exact covers .. 

theorem sat_iff (v : Assignment) (f : Finset Variable) (b : Bool) :
    LinEqSat v (f,b) ↔ parity f v=b := by
  cases b <;> simp [LinEqSat,parity]
theorem flip (u v : Bool) (h : u≠v) : u= !v := by cases u <;> cases v <;> simp_all
theorem three_false (C : LinClause Variable) (a b c : Assignment)
    (ha : ¬LinClauseSat a C) (hb : ¬LinClauseSat b C) (hc : ¬LinClauseSat c C) :
    ¬LinClauseSat (fun v => a v ^^ (b v ^^ c v)) C := by
  rintro ⟨⟨f,s⟩,hs,ok⟩
  have neg (v : Assignment) (bad : ¬LinClauseSat v C) : parity f v= !s :=
    flip _ _ (fun eq => bad ⟨(f,s),hs,(sat_iff _ _ _).mpr eq⟩)
  have ps := (sat_iff _ _ _).mp ok
  rw [parity_xor, parity_xor,neg a ha,neg b hb,neg c hc] at ps
  cases s <;> contradiction
end Pcx130

namespace PNP130Dag.ShortestDag
open PEqualNP.ProofComplexity Pcx130
theorem marked16 (d : ShortestDag Formula) (i : Fin d.pi.length)
    (c : Collision) (m : c ∈ (d.actualTree (d.unroll i)).marks) (x y : Fin 4) :
    ¬ LinClauseSat (fillA c (localRow c.hole x y)) (d.pi.get i) := by
  obtain ⟨j,qs,rt,e⟩ := d.mark_route _ m
  have all (t : Fin 6) : ¬LinClauseSat (six c t) (d.pi.get i) := by
    apply (d.unroll_route_active _ rt (fun C hC bad => ?_)).1
    rw [← d.keyAt_clause (d.route_of_unroll rt).2,e]
    obtain ⟨u,rfl⟩ := clause_key hC
    rw [← six_unique c u t bad]
  rw [fills]
  exact three_false _ _ _ _ (all _) (all _) (all _)
end PNP130Dag.ShortestDag

end PEqualNP.Outside.L_pcx_134_geo
