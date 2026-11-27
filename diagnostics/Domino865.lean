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


theorem site_one_inj {a} : Function.Injective (fun s : Fin (N a) => site s 1) := by
  intro s t he
  have eq : site (site s 1) (N a-1)=site (site t 1) (N a-1) := congrArg (fun i => site i (N a-1)) he
  simpa only [site_comp,show 1+(N a-1)=N a by dsimp [N];omega,site_full] using eq

theorem site_offsets_inj {a} (s : Fin (N a)) {i j : Nat} (hi : i<N a) (hj : j<N a)
    (eq : site s i=site s j) : i=j := by
  have e : s+(⟨i,hi⟩ : Fin (N a))=s+(⟨j,hj⟩ : Fin (N a)) := eq
  exact congrArg Fin.val (add_left_cancel e)

theorem domino {a : Nat} (D : Finset (Fin (N a))) (large : a≤D.card)
    (apart : ∀ i ∈ D, site i 1 ∉ D) :
    D.card=a ∧ ∃ u : Fin (N a), ∀ j : Fin a,
      site u (2*j.val+1)∈D ∧ site u (2*j.val+2)∉D := by
  classical
  let E := D.image (fun i => site i 1)
  have dis : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro x hx he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact apart p hp hx
  have count : E.card=D.card := Finset.card_image_of_injective _ site_one_inj
  have union := Finset.card_union_of_disjoint dis
  have room : (D∪E).card≤N a := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have dc : D.card=a := by dsimp [N] at room;omega
  refine ⟨dc,?_⟩
  have one : ((D∪E)ᶜ).card=1 := by
    rw [Finset.card_compl,Fintype.card_fin,union,count,dc]
    dsimp [N];omega
  obtain ⟨u,eq⟩ := Finset.card_eq_one.mp one
  have out : u∉D∪E := by
    have : u∈(D∪E)ᶜ := by rw [eq];simp
    exact Finset.mem_compl.mp this
  have comp {i : Fin (N a)} (ne : i≠u) : i∈D∪E := by
    by_contra h
    have ic := Finset.mem_compl.mpr h
    rw [eq] at ic
    exact ne (Finset.mem_singleton.mp ic)
  have after (d : Nat) (hl : d+1<N a) (pre : site u d∉D) : site u (d+1)∈D := by
    have ne : site u (d+1) ≠ u := by
      intro h
      have bad := site_offsets_inj u hl (Nat.succ_pos _) (h.trans (site_zero u).symm)
      omega
    rcases Finset.mem_union.mp (comp ne) with yes|no
    · exact yes
    · obtain ⟨p,hp,hq⟩ := Finset.mem_image.mp no
      have h := site_one_inj (hq.trans (site_comp u d 1).symm)
      exact (pre (h ▸ hp)).elim
  have odds (j : Nat) (hj : j<a) : site u (2*j+1)∈D := by
    induction j with
    | zero =>
      apply after 0 (by dsimp [N];omega)
      simpa only [site_zero] using (fun hu => out (Finset.mem_union_left _ hu) : u∉D)
    | succ j ih =>
      have hi := ih (by omega)
      have hn := apart _ hi
      rw [site_comp] at hn
      have sub := after (2*j+1+1) (by dsimp [N];omega) hn
      convert sub using 1 <;> congr 2 <;> omega
  refine ⟨u,fun j => ⟨odds j.val j.isLt,?_⟩⟩
  simpa only [site_comp,show 2*j.val+1+1=2*j.val+2 by omega] using apart _ (odds j.val j.isLt)

end PEqualNP.Outside.L_lib_865_aux
