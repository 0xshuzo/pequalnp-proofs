import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev Cl := Clause (Fin 4 × Fin 3)
structure Links {n : Nat} (atLine : Fin n → Cl) where
  parent : Fin n → Option (Fin n × Fin n)
  ax : ∀ i, parent i = none → atLine i ∈ PHP 4 3
  rule : ∀ i j k, parent i = some (j,k) →
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent (atLine j) (atLine k) (atLine i)


end PCX150


namespace PCX150
variable {n : Nat} {C : Fin n → Cl}
def LeftRaw (g : Links C) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧ g.parent j = none

def RightRaw (g : Links C) (i : Fin n) : Prop := ∃ j k, g.parent i = some (j,k) ∧ g.parent k = none

noncomputable def rawSlots (g : Links C) : Nat := by
  classical
  exact ∑ i : Fin n, ((if LeftRaw g i then 1 else 0) + (if RightRaw g i then 1 else 0))


end PCX150

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

/-- One physical rule contributes separately for each of its two argument positions. -/
def contribution (g : Links C) (i v : Fin n) : Nat :=
  match g.parent i with
  | none => 0
  | some (j,k) => (if v=j then 1 else 0)+(if v=k then 1 else 0)

def incoming (g : Links C) (v : Fin n) : Nat := ∑ i : Fin n, g.contribution i v

noncomputable def derived (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i ≠ none)

noncomputable def raws (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i = none)

theorem rawAndDerived (g : Links C) : g.raws.card + g.derived.card = n := by
  classical
  simpa [raws,derived] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun i => g.parent i = none) (fun _ => (1 : Nat)))

theorem chargeRow (g : Links C) (i : Fin n) :
    ∑ v : Fin n, g.contribution i v = if g.parent i = none then 0 else 2 := by
  cases h : g.parent i with
  | none => simp [contribution,h]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp [contribution,h,Finset.sum_add_distrib]

theorem totalIncoming (g : Links C) : ∑ v : Fin n, g.incoming v = 2*g.derived.card := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ v : Fin n, g.contribution i v := Finset.sum_comm
    _ = ∑ i : Fin n, if g.parent i = none then 0 else 2 :=
      Finset.sum_congr rfl (fun i _ => g.chargeRow i)
    _ = ∑ _i ∈ g.derived, 2 := by
      rw [derived,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : g.parent i = none <;> simp [h]
    _ = _ := by simp [Nat.mul_comm]

theorem rawIncoming (g : Links C) : ∑ v ∈ g.raws, g.incoming v = rawSlots g := by
  classical
  change (∑ v ∈ g.raws, ∑ i : Fin n, g.contribution i v) = _
  rw [Finset.sum_comm]
  unfold rawSlots
  apply Finset.sum_congr rfl
  intro i _
  cases h : g.parent i with
  | none => simp [contribution,h,LeftRaw,RightRaw]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp [contribution,h,LeftRaw,RightRaw,raws,Finset.sum_add_distrib]

theorem derivedIncoming (g : Links C) :
    rawSlots g + ∑ v ∈ g.derived, g.incoming v = 2*g.derived.card := by
  classical
  rw [←g.rawIncoming, ←g.totalIncoming]
  simpa only [raws,derived] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun v => g.parent v = none) g.incoming)

theorem manyRaws (g : Links C) (f : Fin 22 → Fin n) (inj : Function.Injective f)
    (raw : ∀ b, g.parent (f b) = none) : 22 ≤ g.raws.card := by
  classical
  have sub : Finset.univ.image f ⊆ g.raws := by
    intro i hi
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
    simpa [raws] using raw b
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

end PCX150.Links

namespace PCX150

/-- The root has no reader. All other retained resolution lines have one or more. -/
structure ReadBudget where
  axioms : Nat
  derived : Nat
  axiomReads : Nat
  otherReads : List Nat
  linesBound : axioms + derived ≤ 51
  axiomCount : 22 ≤ axioms
  minRaw : 27 ≤ axiomReads
  slots : axiomReads + otherReads.sum = 2 * derived
  count : otherReads.length + 1 = derived
  live : ∀ r ∈ otherReads, 0 < r

private theorem sumWithoutFirst (rs : List Nat) (live : ∀ r ∈ rs, 0 < r) :
    (rs.map Nat.pred).sum + rs.length = rs.sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := live r (by simp)
    have predStep : r.pred + 1 = r := by cases r <;> simp_all
    have tail := ih (fun x hx => live x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem ReadBudget.surplus (b : ReadBudget) :
    b.derived ≤ 29 ∧ (b.otherReads.map Nat.pred).sum ≤ 3 := by
  have hsum := sumWithoutFirst b.otherReads b.live
  have hslots := b.slots
  have hraw := b.minRaw
  have hlen := b.count
  have hl := b.linesBound
  have ha := b.axiomCount
  omega

private def sharedCounts (reads : List Nat) : List Nat := reads.filter (fun n => decide (2 ≤ n))

private theorem sharedCharge (rs : List Nat) :
    (sharedCounts rs).length ≤ (rs.map Nat.pred).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : 2 ≤ r
    · simp [sharedCounts, h] at ih ⊢
      omega
    · simp [sharedCounts, h] at ih ⊢
      omega

private theorem allDouble_of_tight (rs : List Nat)
    (tight : (rs.map Nat.pred).sum = (sharedCounts rs).length) :
    ∀ n ∈ sharedCounts rs, n = 2 := by
  induction rs with
  | nil => simp [sharedCounts]
  | cons r rs ih =>
    have bound := sharedCharge rs
    by_cases h : 2 ≤ r
    · have predStep : r.pred + 1 = r := by cases r <;> simp_all
      have cons : sharedCounts (r :: rs) = r :: sharedCounts rs := by simp [sharedCounts,h]
      rw [cons] at tight ⊢
      simp only [List.map_cons,List.sum_cons,List.length_cons] at tight
      have rt : r = 2 := by omega
      have tail : (rs.map Nat.pred).sum = (sharedCounts rs).length := by omega
      intro n hn
      rcases List.mem_cons.mp hn with eq | mem
      · exact eq.trans rt
      · exact ih tail n mem
    · have cons : sharedCounts (r :: rs) = sharedCounts rs := by simp [sharedCounts,h]
      rw [cons] at tight ⊢
      simp only [List.map_cons,List.sum_cons] at tight
      apply ih
      omega

theorem ReadBudget.shared_cases (b : ReadBudget) :
    (sharedCounts b.otherReads).length ≤ 2 ∨
      ((sharedCounts b.otherReads).length = 3 ∧
       ∀ r ∈ sharedCounts b.otherReads, r = 2) := by
  have bound := b.surplus.2
  have charge := sharedCharge b.otherReads
  by_cases small : (sharedCounts b.otherReads).length ≤ 2
  · exact Or.inl small
  · exact Or.inr ⟨by omega, allDouble_of_tight _ (by omega)⟩

end PCX150


namespace PCX150
open PEqualNP.ProofComplexity
namespace Links
variable {n : Nat} {C : Fin n → Cl}

def inputs (g : Links C) (i : Fin n) : List (Fin n) :=
  match g.parent i with
  | some (j,k) => [j,k]
  | none => []

inductive Used (g : Links C) (root : Fin n) : Fin n → Prop where
  | rootLine : Used g root root
  | input {i j} : Used g root i → j ∈ g.inputs i → Used g root j

theorem later (g : Links C) {i j} (mem : j ∈ g.inputs i) : i.val < j.val := by
  cases h : g.parent i with
  | none => simp [inputs,h] at mem
  | some pair =>
    obtain ⟨u,v⟩ := pair
    have edge := g.rule _ _ _ h
    simp only [inputs,h,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl
    · exact edge.1
    · exact edge.2.1

theorem rootFirst (g : Links C) {root i} (hi : Used g root i) : root.val ≤ i.val := by
  induction hi with
  | rootLine => rfl
  | input _ mem ih => exact Nat.le_trans ih (Nat.le_of_lt (g.later mem))

noncomputable def fill (g : Links C) (root : Fin n) (raw : Cl) (i : Fin n) : Cl := by
  classical
  exact if Used g root i then C i else raw

noncomputable def retain (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3) :
    Links (g.fill root raw) := by
  classical
  refine ⟨fun i => if Used g root i then g.parent i else none,?_,?_⟩
  · intro i h
    by_cases alive : Used g root i
    · simpa [fill,alive] using g.ax i (by simpa [alive] using h)
    · simpa [fill,alive] using ax
  · intro i j k h
    split at h
    next alive =>
      have e := g.rule i j k h
      have a : Used g root j := .input alive (by simp [inputs,h])
      have b : Used g root k := .input alive (by simp [inputs,h])
      simpa [fill,alive,a,b] using e
    next => contradiction

theorem retainParent (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3) (i : Fin n) :
    (g.retain root raw ax).parent i = open Classical in
      if Used g root i then g.parent i else none := by rfl

theorem rootUnseen (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3)
    (i : Fin n) : root ∉ (g.retain root raw ax).inputs i := by
  classical
  intro mem
  by_cases alive : Used g root i
  · have h := (g.retain root raw ax).later mem
    have first := g.rootFirst alive
    omega
  · simpa [inputs,retainParent,alive] using mem

theorem nonrootRead (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3)
    {i : Fin n} (derived : (g.retain root raw ax).parent i ≠ none) (ne : i ≠ root) :
    ∃ u, i ∈ (g.retain root raw ax).inputs u := by
  classical
  have alive : Used g root i := by
    by_contra bad
    simp [retainParent,bad] at derived
  cases alive with
  | rootLine => contradiction
  | @input u j used mem =>
    exact ⟨u,by simpa [inputs,retainParent,used] using mem⟩

end Links
end PCX150


namespace PCX150.Links
variable {n : Nat} {C : Fin n → Cl}

/-- Convert finite physical indegrees to the non-root rows of the read budget. -/
noncomputable def readList (g : Links C) (r : Fin n) : List Nat :=
  (g.derived.erase r).toList.map g.incoming

theorem physicalBudget (g : Links C) (r : Fin n) (derivedRoot : g.parent r ≠ none)
    (unread : g.incoming r = 0) (live : ∀ i, g.parent i ≠ none → i ≠ r → 0 < g.incoming i)
    (small : n ≤ 51) (many : 22 ≤ g.raws.card) (slots : 27 ≤ rawSlots g) :
    ∃ b : ReadBudget, b.derived = g.derived.card ∧ b.otherReads = g.readList r := by
  classical
  have rootMember : r ∈ g.derived := by simpa [derived] using derivedRoot
  have sizes := g.rawAndDerived
  have erase := Finset.sum_erase_add g.derived g.incoming rootMember
  have others : (g.readList r).sum = ∑ i ∈ g.derived.erase r, g.incoming i := by
    simp [readList]
  refine ⟨⟨g.raws.card,g.derived.card,rawSlots g,g.readList r,by omega,many,slots,?_,?_,?_⟩,rfl,rfl⟩
  · rw [others]
    have total := g.derivedIncoming
    omega
  · simp only [readList,List.length_map,Finset.length_toList]
    exact Finset.card_erase_add_one rootMember
  · intro k hk
    obtain ⟨v,mem,rfl⟩ := List.mem_map.mp hk
    have hv : v ∈ g.derived.erase r := by simpa using mem
    obtain ⟨ne,yes⟩ := Finset.mem_erase.mp hv
    exact live v (by simpa [derived] using yes) ne

theorem chargePositive (g : Links C) {i v : Fin n} :
    0 < g.contribution i v ↔ v ∈ g.inputs i := by
  cases h : g.parent i with
  | none => simp [contribution,inputs,h]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    by_cases a : v=j <;> by_cases b : v=k <;> simp [contribution,inputs,h,a,b]

theorem incomingPositive (g : Links C) (v : Fin n) :
    0 < g.incoming v ↔ ∃ i, v ∈ g.inputs i := by
  classical
  constructor
  · intro h
    by_contra! none
    have zero : ∀ i, g.contribution i v = 0 := fun i =>
      Nat.eq_zero_of_not_pos (by rw [g.chargePositive]; exact none i)
    simp [incoming,zero] at h
  · rintro ⟨i,hi⟩
    have pos := g.chargePositive.mpr hi
    have le : g.contribution i v ≤ g.incoming v :=
      Finset.single_le_sum (f := fun u => g.contribution u v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

end PCX150.Links

namespace PCX150
def Taut (C : Cl) : Prop := ∃ v, (v,true) ∈ C ∧ (v,false) ∈ C
end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

theorem oldestEmpty {n : Nat} (f : Fin n → Cl) (has : ∃ r, f r = ∅) :
    ∃ r, f r = ∅ ∧ ∀ i, r.val < i.val → (f i).Nonempty := by
  classical
  let empties : Finset (Fin n) := Finset.univ.filter (fun i => f i = ∅)
  have member (i : Fin n) : i ∈ empties ↔ f i = ∅ := by simp [empties]
  obtain ⟨j,hj⟩ := has
  have nonempty : empties.Nonempty := ⟨j,(member j).2 hj⟩
  let r := empties.max' nonempty
  refine ⟨r,(member r).1 (Finset.max'_mem _ _),?_⟩
  intro i later
  apply Finset.nonempty_iff_ne_empty.mpr
  intro empty
  have hi : i ≤ r := Finset.le_max' empties i ((member i).2 empty)
  exact (Nat.not_le_of_lt later) hi

theorem fillRoot {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl) :
    g.fill r raw r = C r := by
  classical
  simp [Links.fill,Links.Used.rootLine]

theorem fillEarlier {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl)
    (positive : raw.Nonempty) (older : ∀ i, r.val < i.val → (C i).Nonempty) :
    ∀ i, r.val < i.val → (g.fill r raw i).Nonempty := by
  classical
  intro i lt
  by_cases live : g.Used r i
  · simpa [Links.fill,live] using older i lt
  · simpa [Links.fill,live] using positive

theorem fillClean {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl)
    (ok : ¬Taut raw) (clean : ∀ i, ¬Taut (C i)) : ∀ i, ¬Taut (g.fill r raw i) := by
  classical
  intro i
  by_cases live : g.Used r i
  · simpa [Links.fill,live] using clean i
  · simpa [Links.fill,live] using ok

end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

def placeholder : Cl := Finset.univ.image (fun j : Fin 3 => (((0 : Fin 4),j),true))

theorem placeholderFacts :
    placeholder ∈ PHP 4 3 ∧ placeholder.Nonempty ∧ ¬Taut placeholder := by
  refine ⟨Or.inl ⟨0,rfl⟩,?_,?_⟩
  · exact ⟨((0,0),true),Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  · rintro ⟨v,_,neg⟩
    simp [placeholder] at neg

theorem rawNonempty (c : Cl) (h : c ∈ PHP 4 3) : c.Nonempty := by
  rcases h with ⟨i,rfl⟩ | ⟨i,j,k,_,rfl⟩
  · exact ⟨((i,0),true),Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  · exact ⟨_,Finset.mem_insert_self _ _⟩

structure Prepared {n : Nat} (D : Fin n → Cl) (g : Links D) (r : Fin n) : Prop where
  emptyRoot : D r = ∅
  olderNonempty : ∀ i, r.val < i.val → (D i).Nonempty
  rootDerived : g.parent r ≠ none
  rootUnread : g.incoming r = 0
  othersRead : ∀ i, g.parent i ≠ none → i ≠ r → 0 < g.incoming i
  budget : ∃ b : ReadBudget, b.derived = g.derived.card ∧ b.otherReads = g.readList r

theorem prepareGraph {n} {C : Fin n → Cl} (g : Links C) (existsEmpty : ∃ r, C r = ∅)
    (clean : ∀ i, ¬Taut (C i)) (len : n ≤ 51)
    (many : ∀ {D : Fin n → Cl} (h : Links D) r, D r = ∅ → 22 ≤ h.raws.card)
    (pay : ∀ {D : Fin n → Cl} (h : Links D) r, D r = ∅ → (∀ i, ¬Taut (D i)) →
      27 ≤ rawSlots h) : ∃ (D : Fin n → Cl) (dg : Links D) (r : Fin n), Prepared D dg r := by
  classical
  obtain ⟨r,emp,earlier⟩ := oldestEmpty C existsEmpty
  obtain ⟨ax,nonempty,ok⟩ := placeholderFacts
  let D := g.fill r placeholder
  let dg := g.retain r placeholder ax
  have er : D r = ∅ := (fillRoot g r placeholder).trans emp
  have rd : dg.parent r ≠ none := by
    intro raw
    have no := rawNonempty (D r) (dg.ax r raw)
    simpa [er] using no
  have ur : dg.incoming r = 0 := by
    apply Nat.eq_zero_of_not_pos
    rintro pos
    obtain ⟨i,hi⟩ := (dg.incomingPositive r).mp pos
    exact g.rootUnseen r placeholder ax i hi
  have reads (i) (derived : dg.parent i ≠ none) (ne : i ≠ r) : 0 < dg.incoming i :=
    (dg.incomingPositive i).mpr (g.nonrootRead r placeholder ax derived ne)
  refine ⟨D,dg,r,er,fillEarlier g r placeholder nonempty earlier,rd,ur,reads,?_⟩
  exact dg.physicalBudget r rd ur reads len (many dg r er)
    (pay dg r er (fillClean g r placeholder ok clean))

end PCX150

namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
end PCX150

namespace PCX150

private theorem filterMapLength {α} (xs : List α) (f : α → Nat) :
    (xs.filter (fun i => decide (2 ≤ f i))).length =
    ((xs.map f).filter (fun k => decide (2 ≤ k))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : 2 ≤ f a <;> simp [h,ih]

/-- Order the shared vertices from earliest to latest in the derivation. -/
def orderedCuts {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) : List (Fin n) :=
  (ds.filter (fun i => 2 ≤ f i)).sort (· ≥ ·)

theorem cutLength {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).length = ((ds.toList.map f).filter (fun k => decide (2 ≤ k))).length := by
  rw [←filterMapLength]
  let xs := ds.toList.filter (fun i => decide (2 ≤ f i))
  have unique : xs.Nodup := ds.nodup_toList.filter _
  have setEq : xs.toFinset = ds.filter (fun i => 2 ≤ f i) := by ext i; simp [xs]
  have card : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup unique
  simpa [orderedCuts,←setEq] using card

theorem cutMembers {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) (v : Fin n) :
    v ∈ orderedCuts ds f ↔ v ∈ ds ∧ 2 ≤ f v := by simp [orderedCuts]

theorem cutNodup {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).Nodup := by simp [orderedCuts]

theorem cutOrdered {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).Pairwise (fun i j => j.val < i.val) := by
  have order : (orderedCuts ds f).Pairwise (· ≥ ·) := by
    unfold orderedCuts
    exact?
  have unique := cutNodup ds f
  generalize he : orderedCuts ds f = xs at order unique ⊢
  clear he
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    obtain ⟨front,tail⟩ := List.pairwise_cons.mp order
    obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp unique
    apply List.pairwise_cons.mpr
    refine ⟨?_,?_⟩
    · intro y hy
      have ne : y ≠ x := by intro eq; subst y; exact fresh hy
      exact lt_of_le_of_ne (front y hy) (fun eq => ne (Fin.ext eq))
    · exact ih tail uniq

end PCX150

namespace PCX150
variable {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}

noncomputable def sharedIndices (g : Links D) (r : Fin n) :=
  orderedCuts (g.derived.erase r) g.incoming

theorem isShared (v : Fin n) :
    v ∈ sharedIndices g r ↔ v ≠ r ∧ g.parent v ≠ none ∧ 2 ≤ g.incoming v := by
  simp [sharedIndices,cutMembers,Links.derived,and_assoc]

theorem cutSplit (pr : Prepared D g r) :
    g.derived.card ≤ 29 ∧ ((sharedIndices g r).length ≤ 2 ∨
      ((sharedIndices g r).length = 3 ∧ ∀ v ∈ sharedIndices g r, g.incoming v = 2)) := by
  obtain ⟨b,bd,br⟩ := pr.budget
  have eq : (sharedCounts b.otherReads).length = (sharedIndices g r).length := by
    rw [br]
    exact (cutLength _ _).symm
  refine ⟨bd ▸ b.surplus.1,?_⟩
  rcases b.shared_cases with small | ⟨large,doubles⟩
  · exact Or.inl (eq ▸ small)
  · refine Or.inr ⟨eq ▸ large,?_⟩
    intro v mem
    obtain ⟨ne,hd,many⟩ := (isShared _).mp mem
    apply doubles
    rw [br]
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨v,?_,rfl⟩,by simpa using many⟩
    simpa [Links.derived,ne] using hd

theorem offCut (pr : Prepared D g r) (v : Fin n) (hd : g.parent v ≠ none)
    (nr : v ≠ r) (unshared : v ∉ sharedIndices g r) : g.incoming v = 1 := by
  have pos := pr.othersRead v hd nr
  have small : ¬2 ≤ g.incoming v := fun h => unshared ((isShared _).mpr ⟨nr,hd,h⟩)
  omega

end PCX150

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

def natParent (g : Links C) (k : Nat) : Option (Nat × Nat) :=
  if h : k < n then (g.parent ⟨k,h⟩).map (fun p => (p.1.val,p.2.val)) else none

def natClause (C : Fin n → Cl) (outside : Cl) (k : Nat) : Cl :=
  if h : k < n then C ⟨k,h⟩ else outside

theorem natEdge (g : Links C) (outside : Cl) {i j k : Nat}
    (edge : g.natParent i = some (j,k)) :
    i < j ∧ i < k ∧ j < n ∧ k < n ∧
      IsResolvent (natClause C outside j) (natClause C outside k) (natClause C outside i) := by
  unfold natParent at edge
  split at edge
  next hi =>
    cases e : g.parent ⟨i,hi⟩ with
    | none => simp [e] at edge
    | some pair =>
      obtain ⟨u,v⟩ := pair
      obtain ⟨rfl,rfl⟩ : u.val=j ∧ v.val=k := by simpa [e] using edge
      obtain ⟨a,b,r⟩ := g.rule _ _ _ e
      exact ⟨a,b,u.isLt,v.isLt,by simpa [natClause,u.isLt,v.isLt,hi] using r⟩
  next => contradiction

theorem natAx (g : Links C) (outside : Cl) (ok : outside ∈ PHP 4 3)
    {i} (leaf : g.natParent i = none) : natClause C outside i ∈ PHP 4 3 := by
  by_cases hi : i < n
  · have hp : g.parent ⟨i,hi⟩ = none := by simpa [natParent,hi] using leaf
    simpa [natClause,hi] using g.ax ⟨i,hi⟩ hp
  · simpa [natClause,hi] using ok

theorem natDerived (g : Links C) (i : Fin n) :
    g.natParent i.val ≠ none ↔ g.parent i ≠ none := by simp [natParent,i.isLt]

theorem natRoots (g : Links C) (v : Nat) :
    g.natParent v ≠ none ↔ ∃ i : Fin n, i.val = v ∧ g.parent i ≠ none := by
  constructor
  · intro h
    by_cases hv : v < n
    · exact ⟨⟨v,hv⟩,rfl,(g.natDerived ⟨v,hv⟩).1 h⟩
    · simp [natParent,hv] at h
  · rintro ⟨i,rfl,h⟩
    exact (g.natDerived i).2 h

end PCX150.Links

namespace PCX150
open PEqualNP.ProofComplexity

/-- A leaf records a physical source, so two copies of an equal clause can use different labels. -/
inductive LabeledTree (clause : Nat → Cl) : Cl → Type where
  | leaf (id : Nat) : LabeledTree clause (clause id)
  | resolve {C D R : Cl} (left : LabeledTree clause C) (right : LabeledTree clause D)
      (rule : IsResolvent C D R) : LabeledTree clause R

namespace LabeledTree

def cost {f R} : LabeledTree f R → Nat
  | .leaf _ => 0
  | .resolve l r _ => l.cost + r.cost + 1

def leaves {f R} : LabeledTree f R → List Nat
  | .leaf i => [i]
  | .resolve l r _ => l.leaves ++ r.leaves

theorem leafCount {f R} (t : LabeledTree f R) : t.leaves.length = t.cost+1 := by
  induction t with
  | leaf _ => rfl
  | resolve _ _ _ ih jh =>
    simp only [leaves,List.length_append,cost]
    omega

theorem toResTree {f R} (t : LabeledTree f R) {F : Set Cl}
    (available : ∀ i ∈ t.leaves, f i ∈ F) : ResTree F R t.cost := by
  induction t with
  | leaf i => exact .ax (available i (by simp [leaves]))
  | resolve l r rule ih jh =>
    exact .res (ih (fun x hx => available x (by simp [leaves,hx])))
      (jh (fun x hx => available x (by simp [leaves,hx]))) rule

/-- Substitute exactly the designated physical line. Other equal clauses are kept as leaves. -/
def splice {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    LabeledTree f R :=
  match t with
  | .leaf k => if h : i = k then h ▸ proof else .leaf k
  | .resolve l r rule => .resolve (l.splice i proof) (r.splice i proof) rule

theorem spliceCost {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    (t.splice i proof).cost = t.cost + t.leaves.count i * proof.cost := by
  induction t with
  | leaf k =>
    by_cases eq : i = k
    · subst k
      simp [splice,cost,leaves]
    · simp [splice,cost,leaves,eq,Ne.symm eq]
  | resolve l r rule ih jh =>
    simp only [splice,cost,leaves,List.count_append,ih,jh,Nat.add_mul]
    omega

theorem spliceLeaves {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    ∀ k ∈ (t.splice i proof).leaves,
      (k ≠ i ∧ k ∈ t.leaves) ∨ k ∈ proof.leaves := by
  induction t with
  | leaf j =>
    by_cases h : i = j
    · subst j
      intro k hk
      exact Or.inr (by simpa [splice] using hk)
    · simp [splice,leaves,h,Ne.symm h]
  | resolve l r _ ih jh =>
    simp only [splice,leaves,List.mem_append]
    intro k hk
    rcases hk with left | right
    · rcases ih k left with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inl mem⟩
      · exact Or.inr mem
    · rcases jh k right with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inr mem⟩
      · exact Or.inr mem

end LabeledTree
end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

def portList (pair : Option (Nat × Nat)) : List Nat :=
  match pair with
  | none => []
  | some (j,k) => [j,k]

inductive Fragment (f : Nat → Cl) (parent : Nat → Option (Nat × Nat))
    (boundary : Nat → Bool) : Nat → Bool → Type where
  | leaf (i : Nat) (force : Bool) (reason : parent i = none ∨ force = false ∧ boundary i = true) :
      Fragment f parent boundary i force
  | node (i j k : Nat) (force : Bool) (openAt : force = true ∨ boundary i = false)
      (edge : parent i = some (j,k)) (step : IsResolvent (f j) (f k) (f i))
      (left : Fragment f parent boundary j false) (right : Fragment f parent boundary k false) :
      Fragment f parent boundary i force

namespace Fragment

def expanded {f p b i t} : Fragment f p b i t → List Nat
  | .leaf _ _ _ => []
  | .node u _ _ _ _ _ _ l r => u :: l.expanded ++ r.expanded

def tree {f p b i t} : Fragment f p b i t → LabeledTree f (f i)
  | .leaf u _ _ => .leaf u
  | .node _ _ _ _ _ _ rule l r => .resolve l.tree r.tree rule

theorem costCount {f p b i t} (g : Fragment f p b i t) : g.tree.cost = g.expanded.length := by
  induction g with
  | leaf => rfl
  | node _ _ _ _ _ _ _ _ _ ih jh =>
    simp only [tree,LabeledTree.cost,expanded,List.length_append,List.length_cons,ih,jh]
    omega

/-- Every occurrence other than the root came through exactly one parent slot.
    A physical line may appear more than once in either list. -/
theorem occurrenceBalance {f p b i t} (g : Fragment f p b i t) (v : Nat) :
    g.expanded.count v + g.tree.leaves.count v =
      [i].count v + (g.expanded.flatMap (fun u => portList (p u))).count v := by
  induction g with
  | leaf => simp [expanded,tree,LabeledTree.leaves]
  | node i j k force op edge rule l r ih jh =>
    simp only [tree,LabeledTree.leaves,expanded,List.count_append,List.flatMap_append,
      List.flatMap_cons,edge,portList,List.count_cons,List.count_nil,Nat.zero_add,
      List.cons_append] at ih jh ⊢
    omega

end Fragment

theorem canExpand {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      IsResolvent (f j) (f k) (f i)) (b : Nat → Bool) (i : Nat) (force : Bool) :
    Nonempty (Fragment f p b i force) := by
  have aux (m : Nat) : ∀ i, bound-i = m → ∀ t, Nonempty (Fragment f p b i t) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro u eq t
      by_cases cut : t = false ∧ b u = true
      · exact ⟨.leaf u t (Or.inr cut)⟩
      · cases hp : p u with
        | none => exact ⟨.leaf u t (Or.inl hp)⟩
        | some pair =>
          obtain ⟨j,k⟩ := pair
          obtain ⟨hj,hk,bj,bk,step⟩ := rules u j k hp
          obtain ⟨l⟩ := ih (bound-j) (by omega) j rfl false
          obtain ⟨r⟩ := ih (bound-k) (by omega) k rfl false
          have op : t = true ∨ b u = false := by cases t <;> cases hb : b u <;> simp_all
          exact ⟨.node u j k t op hp step l r⟩
  exact aux _ i rfl force

end PCX150

namespace PCX150.Fragment

theorem leafReason {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.tree.leaves, p v = none ∨ b v = true := by
  induction g with
  | leaf u force reason =>
    intro v hv
    have hv' : v = u := by simpa [tree,LabeledTree.leaves] using hv
    subst v
    exact reason.imp_right And.right
  | node _ _ _ _ _ _ _ l r ih jh =>
    intro v hv
    rcases List.mem_append.mp hv with a | a
    · exact ih v a
    · exact jh v a

theorem boundaryExpansion {f p b i t} (g : Fragment f p b i t) (v : Nat) (cut : b v = true) :
    g.expanded.count v = if t = true ∧ i = v ∧ p i ≠ none then 1 else 0 := by
  induction g with
  | leaf u force reason =>
    rcases reason with raw | ⟨nf,_⟩
    · simp [expanded,raw]
    · simp [expanded,nf]
  | node u j k force op edge rule l r ih jh =>
    by_cases eq : u = v
    · subst u
      have forced : force = true := op.resolve_right (by simp [cut])
      simp [expanded,ih,jh,forced,edge]
    · simp [expanded,ih,jh,eq,Ne.symm eq]

theorem openedDerived {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.expanded, p v ≠ none := by
  induction g with
  | leaf => simp [expanded]
  | node u j k force op edge rule l r ih jh =>
    intro v hv
    simp only [expanded,List.cons_append,List.mem_cons,List.mem_append] at hv
    rcases hv with rfl | hl | hr
    · simp [edge]
    · exact ih v hl
    · exact jh v hr

end PCX150.Fragment

namespace PCX150
open PEqualNP.ProofComplexity

abbrev Rooted (f : Nat → Cl) (p : Nat → Option (Nat × Nat)) (b : Nat → Bool) :=
  (i : Nat) × Fragment f p b i true

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

def nodes (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.expanded)
def tips (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.tree.leaves)
def starts (fs : List (Rooted f p b)) := fs.map (fun z => z.1)

theorem balance (fs : List (Rooted f p b)) (v : Nat) :
    (nodes fs).count v + (tips fs).count v =
      (starts fs).count v + ((nodes fs).flatMap (fun k => portList (p k))).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.occurrenceBalance v
    simp only [nodes,tips,starts,List.flatMap_cons,List.map_cons,List.count_append,
      List.flatMap_append,List.count_cons,List.count_nil,Nat.zero_add] at ih h ⊢
    omega

theorem cutRoots (fs : List (Rooted f p b)) (v : Nat) (cut : b v = true)
    (proper : ∀ g ∈ fs, p g.1 ≠ none) : (nodes fs).count v = (starts fs).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.boundaryExpansion v cut
    have d := proper ⟨i,g⟩ (by simp)
    have t := ih (fun z hz => proper z (by simp [hz]))
    by_cases eq : i = v
    · subst i
      simp [nodes,starts,d,List.count_append] at h t ⊢
      omega
    · simp [nodes,starts,d,eq,Ne.symm eq,List.count_append] at h t ⊢
      omega

theorem noncutNotTip (fs : List (Rooted f p b)) {v : Nat} (derived : p v ≠ none)
    (uncut : b v = false) : (tips fs).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hv
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  rcases g.2.leafReason v hg with empty | cut <;> simp_all

theorem physicalDerived (fs : List (Rooted f p b)) {v : Nat} (hv : v ∈ nodes fs) : p v ≠ none := by
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  exact g.2.openedDerived v hg

end Rooted
end PCX150


namespace PCX150

/-- A unique incoming slot is preserved when a list of line indices is replaced by
    its expanded occurrences, provided the unique reader has been expanded once. -/
theorem countParentsSingle (lines : List Nat) (ports : Nat → List Nat) (v u : Nat)
    (sole : ∀ x ∈ lines, (ports x).count v = if x = u then 1 else 0) :
    (lines.flatMap ports).count v = lines.count u := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := sole x (by simp)
    have tail := ih (fun y hy => sole y (by simp [hy]))
    by_cases eq : x = u
    · subst x
      simp_all [List.flatMap_cons,List.count_append,Nat.add_comm]
    · simp [List.flatMap_cons,List.count_append,h,tail,eq,Ne.symm eq]

theorem countParentsZero (lines : List Nat) (ports : Nat → List Nat) (v : Nat)
    (none : ∀ x ∈ lines, v ∉ ports x) : (lines.flatMap ports).count v = 0 := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := none x (by simp)
    have tail := ih (fun y hy => none y (by simp [hy]))
    simp [List.flatMap_cons,List.count_append,tail,List.count_eq_zero.mpr h]

/-- Conservation over the forest of fragments. The roots list has one copy of
    each cut line and the conclusion. A non-cut derived line ends no fragment. -/
theorem oneExpansionPerLine (nodes tips roots : List Nat) (ports : Nat → List Nat)
    (derived : Nat → Prop) (balance : ∀ v, nodes.count v + tips.count v =
      roots.count v + (nodes.flatMap ports).count v)
    (casesFor : ∀ v, derived v →
      nodes.count v = 1 ∨
      (tips.count v = 0 ∧ roots.count v = 0 ∧ ∃ u, u < v ∧ derived u ∧
        ∀ x ∈ nodes, (ports x).count v = if x = u then 1 else 0)) :
    ∀ v, derived v → nodes.count v = 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    rcases casesFor v hv with done | ⟨tip,seed,u,lt,hu,sole⟩
    · exact done
    · have incoming := countParentsSingle nodes ports v u sole
      have earlier := ih u lt hu
      have h := balance v
      omega

end PCX150

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

theorem soleReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Fin n, u.val < v.val ∧ g.parent u ≠ none ∧
      ∀ x, g.contribution x v = if x = u then 1 else 0 := by
  classical
  have pos : 0 < g.incoming v := by omega
  obtain ⟨u,slot⟩ := (g.incomingPositive v).mp pos
  have hu := g.chargePositive.mpr slot
  have le := Finset.single_le_sum (f := fun x => g.contribution x v)
    (fun x _ => Nat.zero_le _) (Finset.mem_univ u)
  change g.contribution u v ≤ g.incoming v at le
  have one : g.contribution u v = 1 := by omega
  have nonzero : g.parent u ≠ none := by
    intro bad
    simp [contribution,bad] at one
  refine ⟨u,g.later slot,nonzero,?_⟩
  intro x
  by_cases eq : x = u
  · simpa [eq] using one
  · rw [if_neg eq]
    have e := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun j => g.contribution j v) (Finset.mem_univ u)
    change _ + _ = g.incoming v at e
    have xmem : x ∈ (Finset.univ : Finset (Fin n)).erase u := by simp [eq]
    have b := Finset.single_le_sum (f := fun j => g.contribution j v) (fun j _ => Nat.zero_le _) xmem
    omega

theorem portCount (g : Links C) (x v : Fin n) :
    (portList (g.natParent x.val)).count v.val = g.contribution x v := by
  cases h : g.parent x with
  | none => simp [natParent,x.isLt,h,contribution,portList]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp only [natParent,dif_pos x.isLt,h,Option.map_some,contribution,portList]
    have comp (z : Fin n) : (z.val == v.val) = decide (v = z) := by
      by_cases yes : v = z
      · subst z; simp
      · have no : z.val ≠ v.val := fun h => yes (Fin.ext h.symm)
        simp [yes,no]
    simp only [List.count_cons,List.count_nil,comp]
    by_cases a : v = j <;> by_cases b : v = k <;> simp [a,b] <;> omega

theorem soleNatReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Nat, u < v.val ∧ g.natParent u ≠ none ∧
      ∀ x, (portList (g.natParent x)).count v.val = if x = u then 1 else 0 := by
  obtain ⟨u,lt,hd,only⟩ := g.soleReader v single
  refine ⟨u.val,lt,(g.natDerived u).2 hd,?_⟩
  intro x
  by_cases hx : x < n
  · have cnt := g.portCount ⟨x,hx⟩ v
    rw [only] at cnt
    simpa [Fin.ext_iff] using cnt
  · have ne : x ≠ u.val := by intro eq; subst x; exact hx u.isLt
    simp [natParent,hx,ne,portList]

end PCX150.Links

namespace PCX150.Links
variable {n : Nat} {C : Fin n → Cl}

noncomputable def physicalList (g : Links C) := g.derived.toList.map Fin.val

theorem listMember (g : Links C) (v : Nat) :
    v ∈ g.physicalList ↔ g.natParent v ≠ none := by
  unfold physicalList
  rw [List.mem_map,g.natRoots]
  constructor
  · rintro ⟨i,mem,eq⟩
    exact ⟨i,eq,by simpa [derived] using mem⟩
  · rintro ⟨i,eq,mem⟩
    exact ⟨i,by simpa [derived] using mem,eq⟩

theorem listNodup (g : Links C) : g.physicalList.Nodup := by
  exact g.derived.nodup_toList.map Fin.val_injective

theorem countFlatMap {α} (xs : List α) (f : α → List Nat) (v : Nat) :
    (xs.flatMap f).count v = (xs.map (fun x => (f x).count v)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.count_append,ih]

theorem physicalPorts (g : Links C) (v : Fin n) :
    (g.physicalList.flatMap (fun x => portList (g.natParent x))).count v.val = g.incoming v := by
  classical
  rw [countFlatMap]
  have sum : (g.physicalList.map (fun x => (portList (g.natParent x)).count v.val)).sum =
      ∑ i ∈ g.derived, g.contribution i v := by
    simp [physicalList,List.map_map,Function.comp_def,g.portCount]
  rw [sum]
  unfold derived
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g.parent i = none <;> simp [contribution,h]

end PCX150.Links

namespace PCX150

private theorem occursAtMost {xs ys : List Nat} (h : ∀ x, xs.count x ≤ ys.count x) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have positive := h a
    have mem : a ∈ ys := by
      by_contra bad
      have zero := List.count_eq_zero.mpr bad
      simp [zero] at positive
    have tail : ∀ x, xs.count x ≤ (ys.erase a).count x := by
      intro x
      have old := h x
      by_cases eq : x = a
      · subst x
        simp at old
        rw [List.count_erase_self]
        omega
      · simpa [List.count_erase_of_ne,eq,Ne.symm eq] using old
    have len := ih tail
    rw [List.length_erase_of_mem mem] at len
    have pos := List.length_pos_of_mem mem
    simp only [List.length_cons]
    omega

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {b : Nat → Bool}

/-- If every uncut live internal node has exactly one incoming slot, expansion
    partitions the physical rules without charging any physical line twice. -/
theorem partitionCost (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (present : ∀ v, p v ≠ none → v ∈ physical)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none)
    (cut : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u < v ∧ p u ≠ none ∧
        ∀ x ∈ nodes fs, (portList (p x)).count v = if x = u then 1 else 0) :
    (nodes fs).length = physical.length ↔ ∀ v ∈ physical, p v ≠ none := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hv
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb rootsDerived).trans (cut v hv hb))
    | false =>
      obtain ⟨zero,u,lt,d,only⟩ := single v hv hb
      exact Or.inr ⟨noncutNotTip fs hv hb,zero,u,lt,d,only⟩
  have charge : ∀ v, (nodes fs).count v ≤ physical.count v := by
    intro v
    by_cases mem : v ∈ nodes fs
    · have hd := physicalDerived fs mem
      rw [once v hd]
      exact List.count_pos_iff.mpr (present v hd)
    · simp [List.count_eq_zero.mpr mem]
  constructor
  · intro eq v hv
    by_contra bad
    have absent : v ∉ nodes fs := fun h => physicalDerived fs h bad
    have charge' : ∀ x, (nodes fs).count x ≤ (physical.erase v).count x := by
      intro x
      by_cases same : x = v
      · subst x
        simp [List.count_eq_zero.mpr absent]
      · simpa [List.count_erase_of_ne,same,Ne.symm same] using charge x
    have h := occursAtMost charge'
    rw [List.length_erase_of_mem hv] at h
    have pos := List.length_pos_of_mem hv
    omega
  · intro proper
    apply Nat.le_antisymm (occursAtMost charge)
    apply occursAtMost
    intro v
    by_cases mem : v ∈ physical
    · rw [once v (proper v mem)]
      exact List.nodup_iff_count_le_one.mp unique v
    · simp [List.count_eq_zero.mpr mem]

end Rooted
end PCX150

namespace PCX150.Rooted

variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

/-- Expand one fragment per selected root, preserving their physical labels and order. -/
noncomputable def chooseForest {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : List (Rooted f p b) :=
  xs.map (fun i => ⟨i,Classical.choice (canExpand rules b i true)⟩)

theorem chooseStarts {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : starts (chooseForest rules b xs) = xs := by
  simp [starts,chooseForest,List.map_map,Function.comp_def]

/-- A non-root with unit indegree is expanded once, no matter how the fragments
    were selected by the kernel's existential unrolling lemma. -/
theorem ownership (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (allRoots : ∀ z ∈ fs, p z.1 ≠ none)
    (cuts : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u<v ∧ p u ≠ none ∧ ∀ x, (portList (p x)).count v = if x = u then 1 else 0) :
    ∀ v, (nodes fs).count v = physical.count v := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hd
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb allRoots).trans (cuts v hd hb))
    | false =>
      obtain ⟨zero,u,lt,hu,only⟩ := single v hd hb
      exact Or.inr ⟨noncutNotTip fs hd hb,zero,u,lt,hu,fun x _ => only x⟩
  intro v
  by_cases hd : p v ≠ none
  · have low := List.count_pos_iff.mpr ((proper v).2 hd)
    have high := List.nodup_iff_count_le_one.mp unique v
    have one := once v hd
    omega
  · have no : v ∉ nodes fs := fun h => hd (physicalDerived fs h)
    have other : v ∉ physical := fun h => hd ((proper v).1 h)
    simp [List.count_eq_zero.mpr no,List.count_eq_zero.mpr other]

end PCX150.Rooted

namespace PCX150.Rooted

variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

/-- Identical multiplicities let us count each parent slot directly in the physical list. -/
theorem countPhysical (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v) (v : Nat) :
    ((nodes fs).flatMap (fun k => portList (p k))).count v =
      (physical.flatMap (fun k => portList (p k))).count v := by
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  have out : ((nodes fs).flatMap (fun k => portList (p k))).Perm
      (physical.flatMap (fun k => portList (p k))) := perm.flatMap (fun _ _ => .refl _)
  exact (List.perm_iff_count.mp out) v

/-- For every marked derived line there is exactly one forced opening.
    The remaining occurrences on the frontier are exactly all physical reads. -/
theorem cutReads (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none) {v : Nat} (cut : b v = true) :
    (tips fs).count v = (physical.flatMap (fun k => portList (p k))).count v := by
  have bal := balance fs v
  have atRoot := cutRoots fs v cut rootsDerived
  have charge := countPhysical fs physical same v
  omega

end PCX150.Rooted

namespace PCX150.Rooted
open PEqualNP.ProofComplexity
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {N : Nat}

/-- Build the partition at every selected shared rule and at the empty conclusion. -/
theorem markedFamily
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < N ∧ k < N ∧
      IsResolvent (f j) (f k) (f i))
    (physical roots : List Nat) (unique : physical.Nodup) (distinct : roots.Nodup)
    (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (relevant : ∀ v ∈ roots, p v ≠ none)
    (read : ∀ v, p v ≠ none → v ∉ roots → ∃ u, u < v ∧ p u ≠ none ∧
      ∀ x, (portList (p x)).count v = if x=u then 1 else 0) :
    ∃ fs : List (Rooted f p (fun k => decide (k ∈ roots))),
      starts fs = roots ∧ (nodes fs).length = physical.length ∧
      (∀ v, (nodes fs).count v = physical.count v) ∧
      ∀ v ∈ roots, (tips fs).count v =
        (physical.flatMap (fun k => portList (p k))).count v := by
  let b := fun k : Nat => decide (k ∈ roots)
  let fs := chooseForest rules b roots
  have start : starts fs = roots := chooseStarts rules b roots
  have allRoots : ∀ z ∈ fs, p z.1 ≠ none := by
    intro z hz
    apply relevant
    rw [←start]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have one (v) (mem : v ∈ roots) : (starts fs).count v = 1 := by
    rw [start]
    have pos := List.count_pos_iff.mpr mem
    have low := List.nodup_iff_count_le_one.mp distinct v
    omega
  have same := ownership fs physical unique proper allRoots
    (fun v _ hv => one v (by simpa [b] using hv)) (by
      intro v hv cut
      have absent : v ∉ roots := by simpa [b] using cut
      exact ⟨by rw [start]; exact List.count_eq_zero.mpr absent,read v hv absent⟩)
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  refine ⟨fs,start,perm.length_eq,same,?_⟩
  intro v hv
  exact cutReads fs physical same allRoots (by simp [b,hv])

end PCX150.Rooted

namespace PCX150
open PEqualNP.ProofComplexity
variable {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}

noncomputable def boundaryRoots (g : Links D) (r : Fin n) : List Nat :=
  r.val :: (sharedIndices g r).map Fin.val

theorem boundaryMember (i : Fin n) :
    i.val ∈ boundaryRoots g r ↔ i = r ∨ i ∈ sharedIndices g r := by
  change (i.val ∈ r.val :: (sharedIndices g r).map Fin.val) ↔ _
  rw [List.mem_cons,List.mem_map]
  constructor
  · rintro (eq | ⟨v,hv,eq⟩)
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr ((Fin.ext eq : v = i) ▸ hv)
  · rintro (rfl | mem)
    · exact Or.inl rfl
    · exact Or.inr ⟨i,mem,rfl⟩

theorem boundaryDistinct (g : Links D) (r : Fin n) : (boundaryRoots g r).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
    exact ((isShared _).mp hi).1 (Fin.ext eq)
  · exact (cutNodup _ _).map Fin.val_injective

theorem graphFamily (pr : Prepared D g r) :
    let roots := boundaryRoots g r
    let f := Links.natClause D placeholder
    let p := g.natParent
    ∃ fs : List (Rooted f p (fun k => decide (k ∈ roots))),
      Rooted.starts fs = roots ∧
      (Rooted.nodes fs).length = g.derived.card ∧
      ∀ i : Fin n, i.val ∈ roots → (Rooted.tips fs).count i.val = g.incoming i := by
  dsimp only
  have proper (i : Nat) := g.listMember i
  have read (i : Nat) (hd : g.natParent i ≠ none) (absent : i ∉ boundaryRoots g r) :
      ∃ u, u < i ∧ g.natParent u ≠ none ∧
        ∀ x, (portList (g.natParent x)).count i = if x=u then 1 else 0 := by
    obtain ⟨v,rfl,hv⟩ := (g.natRoots i).mp hd
    have ne : v ≠ r := fun eq => absent ((boundaryMember v).2 (Or.inl eq))
    have un : v ∉ sharedIndices g r := fun h => absent ((boundaryMember v).2 (Or.inr h))
    exact g.soleNatReader v (offCut pr v hv ne un)
  have req (v : Nat) (m : v ∈ boundaryRoots g r) : g.natParent v ≠ none := by
    rcases List.mem_cons.mp m with eq | rest
    · subst v; exact (g.natDerived r).2 pr.rootDerived
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp rest
      exact (g.natDerived i).2 ((isShared _).mp hi).2.1
  obtain ⟨fs,start,len,_,tips⟩ := Rooted.markedFamily (f := Links.natClause D placeholder)
    (fun _ _ _ e => g.natEdge placeholder e) g.physicalList (boundaryRoots g r)
    g.listNodup (boundaryDistinct g r) proper req read
  refine ⟨fs,start,?_,fun i hi => (tips i.val hi).trans (g.physicalPorts i)⟩
  simpa [Links.physicalList] using len

end PCX150
