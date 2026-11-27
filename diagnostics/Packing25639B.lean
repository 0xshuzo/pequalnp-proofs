import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25639

def Period {A : Type*} (k : Nat) (a : Nat → A) := ∀ i, a (i+k) = a i

theorem per_iter {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (s q : Nat) : a (s+q*k) = a s := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]

theorem per_reduce {A : Type*} {a : Nat → A} {k : Nat} (h : Period k a)
    (n d : Nat) : a (n+d) = a (n%k+d) := by
  have eq : n+d = (n%k+d) + (n/k)*k := by
    have := Nat.mod_add_div n k
    rw [Nat.mul_comm (n/k) k]
    omega
  rw [eq, per_iter h]

def Adj {A : Type*} [Zero A] (a : Nat → A) : Prop :=
  ∀ i, a i = 0 ∨ a (i+1) = 0 ∨ a i = a (i+1)

def start {A : Type*} [Zero A] (a : Nat → A) (i : Nat) :=
  a (i+1) ≠ 0 ∧ a i ≠ a (i+1)

theorem starts_close {A : Type*} [AddCommGroup A] (char : ∀ z : A, z + z = 0)
    (a : Nat → A) (ha : Adj a)
    (hb : Adj (fun i => a i + a (i+1) + a (i+2))) (i j : Nat)
    (si : start a i) (sj : start a j) (h1 : i ≤ j+2) (h2 : j ≤ i+2) :
    a (i+1) = a (j+1) := by
  have fwd : ∀ t d : Nat, start a t → start a (t+d) → d ≤ 2 →
      a (t+1) = a (t+d+1) := by
    intro t d st su hd
    obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    · rfl
    · rcases ha (t+1) with h | h | h
      · exact (st.1 h).elim
      · exact (su.1 h).elim
      · exact h
    · have z0 : a t = 0 := (ha t).resolve_right (by
          rintro (h | h)
          · exact st.1 h
          · exact st.2 h)
      have z2 : a (t+2) = 0 := (ha (t+2)).resolve_right (by
          rintro (h | h)
          · exact su.1 h
          · exact su.2 h)
      have opp := hb t
      simp only [z0, z2, zero_add, add_zero] at opp
      rcases opp with h | h | h
      · exact (st.1 h).elim
      · calc
          a (t+1) = a (t+1) + (a (t+2+1) + a (t+2+1)) := by rw [char, add_zero]
          _ = (a (t+1) + a (t+2+1)) + a (t+2+1) := (add_assoc _ _ _).symm
          _ = a (t+2+1) := by rw [show a (t+1) + a (t+2+1) = 0 from h, zero_add]
      · have z : a (t+2+1) = 0 := add_left_cancel (show a (t+1) + a (t+2+1) = a (t+1) + 0 by simpa using h.symm)
        exact (su.1 z).elim
  by_cases hij : i ≤ j
  · have he : i+(j-i)=j := by omega
    simpa only [he] using fwd i (j-i) si (by rw [he]; exact sj) (by omega)
  · have he : j+(i-j)=i := by omega
    symm
    simpa only [he] using fwd j (i-j) sj (by rw [he]; exact si) (by omega)

noncomputable def labels {A : Type*} [Zero A] (k : Nat) (a : Nat → A) : Finset A := by
  classical
  exact ((Finset.range k).image a).erase 0

theorem label_mem {A : Type*} [Zero A] {a : Nat → A} {k : Nat} {x : A} :
    x ∈ labels k a ↔ x ≠ 0 ∧ ∃ i < k, a i = x := by
  classical
  simp [labels]

theorem findStart {A : Type*} [Zero A] {a : Nat → A} {k : Nat} (per : Period k a)
    (x : A) (hx : x ∈ labels k a) (hvar : ∃ j < k, a j ≠ x) :
    ∃ r < k, start a r ∧ a (r+1) = x := by
  obtain ⟨nz,t,ht,atval⟩ := label_mem.mp hx
  obtain ⟨bad,hbad,ne⟩ := hvar
  by_contra h
  have back : ∀ i, a (i+1) = x → a i = x := by
    intro i hit
    by_contra other
    have hk : 0 < k := by omega
    have hi : a (i%k) ≠ x := fun h => other ((per_reduce per i 0).trans h)
    have hh : a (i%k+1) = x := (per_reduce per i 1).symm.trans hit
    exact h ⟨i%k, Nat.mod_lt _ hk, ⟨fun h0 => nz (hh.symm.trans h0), fun he => hi (he.trans hh)⟩, hh⟩
  have iter : ∀ n, a (bad+n) = x → a bad = x := by
    intro n
    induction n with
    | zero => simpa
    | succ n ih => exact fun hv => ih (back (bad+n) hv)
  have he : bad+(t+k-bad) = t+k := by omega
  exact ne (iter (t+k-bad) (by rw [he, per, atval]))

theorem label_budget {A : Type*} [AddCommGroup A] (char : ∀ z : A, z+z=0)
    (k : Nat) (big : 5 ≤ k) (a : Nat → A) (per : Period k a) (ha : Adj a)
    (hb : Adj (fun i => a i + a (i+1) + a (i+2))) :
    (labels k a).card ≤ k/3 := by
  classical
  by_cases small : (labels k a).card ≤ 1
  · omega
  have rep : ∀ x : ↥(labels k a), ∃ r < k, start a r ∧ a (r+1) = x.val := by
    intro x
    apply findStart per x.val x.property
    by_contra h
    have sub : labels k a ⊆ {x.val} := by
      intro y hy
      obtain ⟨_,i,hi,eq⟩ := label_mem.mp hy
      have hz : a i = x.val := by_contra (fun ne => h ⟨i,hi,ne⟩)
      simpa using eq.symm.trans hz
    have hc := Finset.card_le_card sub
    simp only [Finset.card_singleton] at hc
    omega
  choose r hr hs hv using rep
  let alloc := fun p : ↥(labels k a) × Fin 3 =>
    (⟨(r p.1 + p.2.val)%k, Nat.mod_lt _ (by omega)⟩ : Fin k)
  have inj : Function.Injective alloc := by
    rintro ⟨x,t⟩ ⟨y,u⟩ heq
    have eq : (r x+t.val)%k = (r y+u.val)%k := congrArg Fin.val heq
    let z := (r x+t.val)%k + k
    have lift : ∀ (v : ↥(labels k a)) (d : Fin 3), (r v+d.val)%k+k = z →
        ∃ j, j+d.val=z ∧ start a j ∧ a (j+1)=v.val := by
      intro v d e
      by_cases hlt : r v+d.val<k
      · rw [Nat.mod_eq_of_lt hlt] at e
        have bump : a (r v+k+1) = a (r v+1) := by rw [show r v+k+1=r v+1+k by omega, per]
        refine ⟨r v+k, by omega, ?_, bump.trans (hv v)⟩
        exact ⟨by rw [bump]; exact (hs v).1, by rw [per, bump]; exact (hs v).2⟩
      · have less : r v+d.val-k<k := by have := hr v; have := d.isLt; omega
        rw [Nat.mod_eq_sub_mod (by omega : k ≤ r v+d.val), Nat.mod_eq_of_lt less] at e
        exact ⟨r v, by omega, hs v, hv v⟩
    obtain ⟨i,hi,si,vi⟩ := lift x t rfl
    obtain ⟨j,hj,sj,vj⟩ := lift y u (by dsimp [z]; rw [eq])
    have lab := starts_close char a ha hb i j si sj (by have := u.isLt; omega) (by have := t.isLt; omega)
    have xy : x=y := Subtype.ext (vi.symm.trans (lab.trans vj))
    subst y
    have tu : t=u := by
      apply Fin.ext
      have hmod : ∀ d : Nat, d<3 → (r x+d)%k = if r x+d<k then r x+d else r x+d-k := by
        intro d hd
        split
        next h => exact Nat.mod_eq_of_lt h
        next h => rw [Nat.mod_eq_sub_mod (by omega : k ≤ r x+d), Nat.mod_eq_of_lt (by have := hr x; omega)]
      rw [hmod t.val t.isLt,hmod u.val u.isLt] at eq
      split at eq <;> split at eq <;> omega
    subst u
    rfl
  have card := Fintype.card_le_of_injective alloc inj
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at card
  omega


end PEqualNP.Outside.L_meta_25639
