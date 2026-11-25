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
