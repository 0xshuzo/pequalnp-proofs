import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25639

def blockTag (k r : Nat) : Nat := if r < 3*(k/3) then if r%3=2 then 0 else r/3+1 else 1

def tag (k n : Nat) : Nat := blockTag k (n%k)

theorem modSmall {k r d : Nat} (big : 5 ≤ k) (hr : r<k) (hd : d≤3) :
    (r+d)%k = if r+d<k then r+d else r+d-k := by
  split
  next h => exact Nat.mod_eq_of_lt h
  next h => rw [Nat.mod_eq_sub_mod (by omega : k≤r+d), Nat.mod_eq_of_lt (by omega)]

theorem tagPlus {k : Nat} (big : 5 ≤ k) (n d : Nat) (hd : d≤3) :
    tag k (n+d) = blockTag k (if n%k+d<k then n%k+d else n%k+d-k) := by
  unfold tag
  rw [← Nat.mod_add_mod n k d, modSmall big (Nat.mod_lt _ (by omega)) hd]

theorem tag_adj {k : Nat} (big : 5≤k) (n : Nat) :
    tag k n = 0 ∨ tag k (n+1) = 0 ∨ tag k n = tag k (n+1) := by
  rw [tagPlus big n 1 (by decide)]
  unfold tag blockTag
  have h := Nat.mod_lt n (show 0<k by omega)
  split_ifs <;> omega

theorem tag_zeroPair {k : Nat} (big : 5≤k) (n : Nat) (h : tag k (n+1)=0) :
    tag k n ≠ 0 ∧ tag k (n+2) ≠ 0 := by
  rw [tagPlus big n 1 (by decide)] at h
  rw [tagPlus big n 2 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_afterZero {k : Nat} (big : 5≤k) (n : Nat) (h : tag k n=0) :
    tag k (n+1)=tag k (n+2) := by
  rw [tagPlus big n 1 (by decide),tagPlus big n 2 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_beforeZero {k : Nat} (big : 5≤k) (n : Nat) (h : tag k (n+2)=0) :
    tag k n=tag k (n+1) := by
  rw [tagPlus big n 2 (by decide)] at h
  rw [tagPlus big n 1 (by decide)]
  unfold tag blockTag at *
  have bound := Nat.mod_lt n (show 0<k by omega)
  split_ifs at * <;> omega

theorem tag_sample {k : Nat} (big : 5≤k) (i : Fin (k/3)) :
    tag k (3*i.val) = i.val+1 := by
  have h := i.isLt
  have hk : 3*i.val<k := by omega
  unfold tag blockTag
  rw [Nat.mod_eq_of_lt hk, if_pos (by omega)]
  have hm : 3*i.val%3=0 := by omega
  have hd : 3*i.val/3=i.val := by omega
  simp [hm,hd]

def patternVal {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) (n : Nat) : A :=
  if h : tag k n = 0 then 0 else if h' : tag k n-1<k/3 then u ⟨tag k n-1,h'⟩ else 0

theorem pat_same {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) {t v : Nat}
    (h : tag k t=tag k v) : patternVal u t=patternVal u v := by simp [patternVal,h]

theorem pat_zero {A : Type*} [Zero A] {k : Nat} (u : Fin (k/3) → A) {t : Nat}
    (h : tag k t=0) : patternVal u t=0 := by simp [patternVal,h]

theorem pattern_compatible {A : Type*} [AddCommGroup A] (char : ∀ v:A, v+v=0) {k : Nat}
    (big : 5≤k) (u : Fin (k/3) → A) (n : Nat) :
    let a := patternVal u
    (a n=0 ∨ a (n+1)=0 ∨ a n=a (n+1)) ∧
    (a n+a (n+1)+a (n+2)=0 ∨ a (n+1)+a (n+2)+a (n+3)=0 ∨
      a n+a (n+1)+a (n+2)=a (n+1)+a (n+2)+a (n+3)) := by
  dsimp only
  constructor
  · rcases tag_adj big n with h|h|h
    · exact Or.inl (pat_zero u h)
    · exact Or.inr (Or.inl (pat_zero u h))
    · exact Or.inr (Or.inr (pat_same u h))
  · by_cases h1 : tag k (n+1)=0
    · right; left
      rw [pat_zero u h1, ← pat_same u (tag_afterZero big (n+1) h1),zero_add,char]
    · by_cases h2 : tag k (n+2)=0
      · left
        rw [pat_zero u h2, ← pat_same u (tag_beforeZero big n h2),add_zero,char]
      · have e := ((tag_adj big (n+1)).resolve_left h1).resolve_left h2
        have e' := pat_same u e
        rw [← e', add_assoc (patternVal u n), char, add_zero, char, zero_add]
        rcases tag_adj big n with h|h|h
        · exact Or.inl (pat_zero u h)
        · exact (h1 h).elim
        · rcases tag_adj big (n+2) with q|q|q
          · exact (h2 q).elim
          · exact Or.inr (Or.inl (pat_zero u q))
          · exact Or.inr (Or.inr (pat_same u (h.trans (e.trans q))))

end PEqualNP.Outside.L_meta_25639
