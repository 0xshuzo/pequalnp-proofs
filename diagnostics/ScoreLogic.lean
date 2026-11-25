import PEqualNP.Defs

namespace PCX150.Sparse

abbrev Point := Fin 60
abbrev Query := Fin 12
abbrev Label := Fin 22
abbrev Box := Sum Label (Fin 2)

inductive TestTree where
  | leaf
  | cut (v : Query) (no yes : TestTree)

def leaves : TestTree → Nat
  | .leaf => 1
  | .cut _ t u => leaves t + leaves u

def half (bit : Point → Query → Bool) (s : Set Point) (v : Query) (b : Bool) : Set Point :=
  {p | p ∈ s ∧ bit p v = b}

def Valid (bit : Point → Query → Bool) (term : Box → Set Point) : TestTree → Set Point → Prop
  | .leaf,s => ∃ i, s ⊆ term i
  | .cut v t u,s => Valid bit term t (half bit s v false) ∧ Valid bit term u (half bit s v true)

theorem coverExists (bit : Point → Query → Bool) (term : Box → Set Point)
    {t : TestTree} {s : Set Point} (h : Valid bit term t s) :
    ∃ f : Finset Box, f.card ≤ leaves t ∧ ∀ p ∈ s, ∃ i ∈ f, p ∈ term i := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    exact ⟨{i},by simp [leaves],fun p hp => ⟨i,by simp,hi hp⟩⟩
  | cut v t u ht hu =>
    obtain ⟨a,ha,ca⟩ := ht h.1
    obtain ⟨b,hb,cb⟩ := hu h.2
    refine ⟨a ∪ b,(Finset.card_union_le _ _).trans (Nat.add_le_add ha hb),?_⟩
    intro p hp
    cases m : bit p v with
    | false =>
      obtain ⟨i,hi,hit⟩ := ca p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_left _ hi,hit⟩
    | true =>
      obtain ⟨i,hi,hit⟩ := cb p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_right _ hi,hit⟩

def box (tag : Point → Label) (A B : Set Point) : Box → Set Point
  | .inl i => {p | tag p = i}
  | .inr i => if i = 0 then A else B

noncomputable def liveTags (tag : Point → Label) (s : Set Point) : Finset Label := by
  classical
  exact Finset.univ.filter (fun k => ∃ p ∈ s, tag p = k)

theorem ofLive {tag : Point → Label} {s : Set Point} {i : Label}
    (hi : i ∈ liveTags tag s) : ∃ p ∈ s, tag p = i := by
  classical
  unfold liveTags at hi
  exact (Finset.mem_filter.mp hi).2

noncomputable def residual (tag : Point → Label) (s A B : Set Point) (x y : Bool) : Finset Box := by
  classical
  exact ((liveTags tag {p | p ∈ s ∧ (x = true → p ∉ A) ∧ (y = true → p ∉ B)}).map
      ⟨Sum.inl,Sum.inl_injective⟩) ∪
    (if x then {Sum.inr 0} else ∅) ∪ (if y then {Sum.inr 1} else ∅)

theorem cheapLower (bit : Point → Query → Bool) (tag : Point → Label)
    {t : TestTree} {s A B : Set Point} (h : Valid bit (box tag A B) t s) (k : Nat)
    (hk : ∀ x y : Bool, k ≤ (residual tag s A B x y).card) : k ≤ leaves t := by
  classical
  obtain ⟨f,hf,cover⟩ := coverExists _ _ h
  let x := decide ((Sum.inr 0 : Box) ∈ f)
  let y := decide ((Sum.inr 1 : Box) ∈ f)
  have subset : residual tag s A B x y ⊆ f := by
    intro u hu
    simp only [residual,Finset.mem_union] at hu
    rcases hu with (lab | fst) | snd
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp lab
      obtain ⟨p,⟨ps,pa,pb⟩,eq⟩ := ofLive hi
      obtain ⟨b,mem,hit⟩ := cover p ps
      cases b with
      | inl j =>
        change tag p = j at hit
        have ji : j=i := hit.symm.trans eq
        simpa [ji] using mem
      | inr j =>
        fin_cases j
        · exact False.elim (pa (by simpa [x] using mem) (by simpa [box] using hit))
        · exact False.elim (pb (by simpa [y] using mem) (by simpa [box] using hit))
    · by_cases hx : (Sum.inr 0 : Box) ∈ f
      · have e : u = Sum.inr 0 := by simpa [x,hx] using fst
        simpa [e] using hx
      · simp [x,hx] at fst
    · by_cases hy : (Sum.inr 1 : Box) ∈ f
      · have e : u = Sum.inr 1 := by simpa [y,hy] using snd
        simpa [e] using hy
      · simp [y,hy] at snd
  exact (hk x y).trans ((Finset.card_le_card subset).trans hf)

end PCX150.Sparse

namespace PCX150.Scoring
open PCX150.Sparse
def bitset (m : Nat) : Set Point := {p : Point | m.testBit p.val = true}
def tags : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def label (p : Point) : Label := Fin.ofNat 22 (#[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21][p.val]!)
def present (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tags[k]! != 0 then n+1 else n) 0
def apart (a b : Nat) := a ^^^ (a &&& b)
theorem tagBits : ∀ (k : Label) (p : Point),
    (tags[k.val]!).testBit p.val = decide (label p=k) := by decide +kernel
theorem tagSmall : ∀ k : Label, tags[k.val]! < 2^60 := by decide +kernel

theorem tagHit (m : Nat) (k : Label) (h : m &&& tags[k.val]! ≠ 0) :
    ∃ p ∈ bitset m, label p = k := by
  classical
  by_contra no
  apply h
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and]
  by_cases sm : n < 60
  · let p : Point := ⟨n,sm⟩
    have e := tagBits k p
    change (tags[k.val]!).testBit n = _ at e
    rw [e]
    by_cases bit : m.testBit n = true
    · have ne : label p ≠ k := fun eq => no ⟨p,bit,eq⟩
      simp [ne]
    · simp [show m.testBit n = false by cases z : m.testBit n <;> simp_all]
  · have low := Nat.testBit_lt_two_pow (lt_of_lt_of_le (tagSmall k)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 60 ≤ n)))
    simp [low]

theorem presentBound (m : Nat) : present m ≤ (liveTags label (bitset m)).card := by
  classical
  let test := fun k : Nat => m &&& tags[k]! != 0
  let ls := (List.range 22).filter test
  have fold (ws : List Nat) (n : Nat) :
      ws.foldl (fun v k => if test k then v+1 else v) n = n+(ws.filter test).length := by
    induction ws generalizing n with
    | nil => simp
    | cons a as ih =>
      cases h : test a <;> simp [h,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have size : present m = ls.length := by simpa [present,ls,test] using fold (List.range 22) 0
  let target := (liveTags label (bitset m)).image Fin.val
  have subset : ls.toFinset ⊆ target := by
    intro k hk
    have hit := List.mem_filter.mp (List.mem_toFinset.mp hk)
    have kt := List.mem_range.mp hit.1
    let v : Label := ⟨k,kt⟩
    have ne : m &&& tags[v.val]! ≠ 0 := by simpa [test,v] using hit.2
    have witness := tagHit m v ne
    have live : v ∈ liveTags label (bitset m) := by
      unfold liveTags
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,witness⟩
    exact Finset.mem_image.mpr ⟨v,live,rfl⟩
  have h := Finset.card_le_card subset
  have nd : ls.Nodup := List.nodup_range.filter _
  rw [size,←List.toFinset_card_of_nodup nd]
  exact h.trans (Finset.card_image_le)

theorem apartSet (m a : Nat) (p : Point) :
    p ∈ bitset (apart m a) ↔ p ∈ bitset m ∧ p ∉ bitset a := by
  change (apart m a).testBit p.val = true ↔ m.testBit p.val = true ∧ ¬ a.testBit p.val = true
  simp only [apart,Nat.testBit_xor,Nat.testBit_and]
  cases m.testBit p.val <;> cases a.testBit p.val <;> decide

theorem countResidual (s a b : Set Point) (x y : Bool) :
    (residual label s a b x y).card =
    (liveTags label {p | p ∈ s ∧ (x = true → p ∉ a) ∧ (y = true → p ∉ b)}).card + x.toNat + y.toNat := by
  classical
  cases x <;> cases y <;> simp [PCX150.Sparse.residual,Finset.union_singleton,Finset.mem_map,Finset.card_insert_of_notMem]

def basic (s a b : Nat) := min (present s) (min (1+present (apart s a))
       (min (1+present (apart s b)) (2+present (apart (apart s a) b))))

theorem numericalLeafCover (val : Point → Query → Bool) (s a b : Nat) (t : TestTree)
    (v : Valid val (box label (bitset a) (bitset b)) t (bitset s)) : basic s a b ≤ leaves t := by
  apply cheapLower val label v
  intro x y
  rw [countResidual]
  cases x <;> cases y
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset s := by ext; simp
    rw [eq]
    unfold basic
    exact (min_le_left _ _).trans (by simpa using presentBound s)
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart s b) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s b)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset (apart s a) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s a)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart (apart s a) b) := by
      ext p; simp [apartSet,and_assoc]; aesop
    rw [eq]
    have z := presentBound (apart (apart s a) b)
    unfold basic
    simp only [Bool.toNat_true]
    omega
end PCX150.Scoring
