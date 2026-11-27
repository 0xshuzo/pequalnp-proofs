import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_865_aux

abbrev N (a : Nat) := 2*a+1
def site {a : Nat} (s : Fin (N a)) (d : Nat) : Fin (N a) :=
  ⟨(s.val+d) % N a, Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem site_zero {a} (s : Fin (N a)) : site s 0 = s := by
  apply Fin.ext; simp [site,Nat.mod_eq_of_lt s.isLt]

theorem site_comp {a} (s : Fin (N a)) (i j : Nat) : site (site s i) j = site s (i+j) := by
  apply Fin.ext
  simp [site, Nat.mod_add_mod, Nat.add_assoc]

theorem site_full {a} (s : Fin (N a)) : site s (N a) = s := by
  apply Fin.ext
  simp [site,Nat.mod_eq_of_lt s.isLt]

theorem offsets {a} (s t : Fin (N a)) :
    ∃ d < N a, site s d = t := by
  have hs := s.isLt
  have ht := t.isLt
  by_cases st : s.val ≤ t.val
  · refine ⟨t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(t.val-s.val)) % N a = t.val
    rw [show s.val+(t.val-s.val)=t.val by omega,Nat.mod_eq_of_lt ht]
  · refine ⟨N a+t.val-s.val,by omega,Fin.ext ?_⟩
    change (s.val+(N a+t.val-s.val)) % N a = t.val
    rw [show s.val+(N a+t.val-s.val)=t.val+N a by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

def Mark {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) : Prop :=
  h s ≠ 0 ∧ (∀ d : Nat, 0 < d → d < a → h (site s d) = 0) ∧
    (h (site s a) = 0 ∨ h (site s a) = h s)

def Canon {a : Nat} {A : Type*} [Zero A] (h : Fin (N a) → A) (s : Fin (N a)) :=
  Mark h s ∧ ¬ Mark h (site s a)

theorem mark_spacing {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s : Fin (N a)} {d : Nat} (pos : 0<d) (lt : d<N a)
    (hs : Mark h s) (ht : Mark h (site s d)) : d=a ∨ d=a+1 := by
  have fwd : a≤d := by
    by_contra! small
    exact ht.1 (hs.2.1 d pos small)
  have rt : site (site s d) (N a-d) = s := by
    rw [site_comp,show d+(N a-d)=N a by omega,site_full]
  have rev : a≤N a-d := by
    by_contra! small
    exact hs.1 (rt ▸ (ht.2.1 _ (by omega) small))
  dsimp [N] at rev lt
  omega

theorem has_canon {a : Nat} {A : Type*} [Zero A] (ha : 2≤a) {h : Fin (N a) → A}
    {s : Fin (N a)} (hs : Mark h s) : ∃ t, Canon h t := by
  by_cases ht : Mark h (site s a)
  · refine ⟨site s a,ht,?_⟩
    intro bad
    rw [site_comp] at bad
    have eq := mark_spacing (d:=a+a) (by omega) (by dsimp [N];omega) hs bad
    omega
  · exact ⟨s,hs,ht⟩

theorem canon_unique {a : Nat} {A : Type*} [Zero A] {h : Fin (N a) → A}
    {s t : Fin (N a)} (hs : Canon h s) (ht : Canon h t) : s=t := by
  obtain ⟨d,lt,eq⟩ := offsets s t
  subst t
  by_cases zero : d=0
  · subst d; exact (site_zero s).symm
  have split := mark_spacing (d:=d) (by omega) lt hs.1 ht.1
  rcases split with e | e
  · subst d; exact (hs.2 ht.1).elim
  · subst d
    apply False.elim
    apply ht.2
    rw [site_comp,show a+1+a=N a by dsimp [N];omega,site_full]
    exact hs.1

end PEqualNP.Outside.L_lib_865_aux
