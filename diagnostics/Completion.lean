import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10008.Completion
abbrev V := Fin 31
abbrev Sh := Finset V
abbrev Box := Sh × Sh
def avoids (x s : Sh) := ∀p∈s,p∉x
def has (a : List Sh) (s : Sh) (p : V) := ∃x∈a,p∈x ∧ avoids x s
def realizes (a : List Sh) (s : Sh) := ∀p : V,p∉s → has a s p
def deficit (a : List Sh) (s : Sh) (p : V) := p∉s ∧ ¬has a s p

theorem extra (a : List Sh) (x s : Sh) :
    realizes (x::a) s ↔ (∀p,deficit a s p → p∈x) ∧
      ((∃p,deficit a s p) → avoids x s) := by
  classical
  constructor
  · intro ok
    have unique {p} (fail : deficit a s p) : p∈x ∧ avoids x s := by
      obtain ⟨v,member,h⟩ := ok p fail.1
      rcases List.mem_cons.mp member with e|ea
      · simpa [e] using h
      · exact False.elim (fail.2 ⟨v,ea,h⟩)
    exact ⟨fun p h => (unique h).1,fun ⟨p,h⟩ => (unique h).2⟩
  · rintro ⟨owns,clear⟩ p hp
    by_cases old : has a s p
    · rcases old with ⟨v,hv,h⟩
      exact ⟨v,List.mem_cons_of_mem _ hv,h⟩
    · have missing : deficit a s p := ⟨hp,old⟩
      exact ⟨x,by simp,owns p missing,clear ⟨p,missing⟩⟩

-- One unrestricted extra side can fix a whole family precisely when all its
-- required points avoid every block that needs the extra side.
theorem oneFree {I : Type} (a : List Sh) (blocks : I → Sh) :
    (∃x : Sh,∀j,realizes (x::a) (blocks j)) ↔
    ∀ i j p,deficit a (blocks i) p → (∃q,deficit a (blocks j) q) → p∉blocks j := by
  classical
  constructor
  · rintro ⟨x,fit⟩ i j p need bad belongs
    exact ((extra a x (blocks j)).mp (fit j)).2 bad p belongs
      (((extra a x (blocks i)).mp (fit i)).1 p need)
  · intro h
    let x := Finset.univ.filter fun p : V => ∃i,deficit a (blocks i) p
    refine ⟨x,fun j => (extra a x (blocks j)).mpr ⟨?_,?_⟩⟩
    · intro p need
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,need⟩
    · intro bad p hp present
      obtain ⟨i,need⟩ := (Finset.mem_filter.mp present).2
      exact h i j p need bad hp

theorem carrierPencil (a : List Sh) (x s : Sh) {p : V}
    (hp : p∈x) (hs : p∈s) (yes : realizes (x::a) s) : realizes a s := by
  classical
  intro q hq
  by_contra missing
  exact ((extra a x s).mp yes).2 ⟨q,hq,missing⟩ p hs hp

def physical (M : V → V → Bool) (L : List Box) :=
  (∀r∈L,∀p∈r.1,∀j∈r.2,M p j=false) ∧
  ∀p j,M p j=false → ∃r∈L,p∈r.1 ∧ j∈r.2

def line (M : V → V → Bool) (j : V) : Sh := Finset.univ.filter fun p => M p j=true
private theorem inLine (M : V → V → Bool) (j p : V) : p∈line M j ↔ M p j=true := by
  simp [line]

noncomputable def complete (M : V → V → Bool) (a : Sh) : Box := by
  classical
  exact (a,Finset.univ.filter fun j => avoids a (line M j))

theorem build (M : V → V → Bool) (a : List Sh) :
    (∀j,realizes a (line M j)) ↔ physical M (a.map (complete M)) := by
  classical
  constructor
  · intro yes
    constructor
    · intro r hr p hp j hj
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
      have avoid := (Finset.mem_filter.mp hj).2
      cases e : M p j with
      | false => rfl
      | true => exact False.elim (avoid p ((inLine M j p).mpr e) hp)
    · intro p j blank
      have h : p∉line M j := by simp [line,blank]
      obtain ⟨z,hz,atP,away⟩ := yes j p h
      exact ⟨complete M z,List.mem_map.mpr ⟨z,hz,rfl⟩,atP,Finset.mem_filter.mpr ⟨Finset.mem_univ _,away⟩⟩
  · rintro ⟨_,cov⟩ j p hp
    have h : M p j=false := by cases e : M p j <;> simp_all [line]
    obtain ⟨r,hr,pr,jr⟩ := cov p j h
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    exact ⟨z,hz,pr,(Finset.mem_filter.mp jr).2⟩

theorem physicalFree (M : V → V → Bool) (a : List Sh) :
    (∃x,physical M ((x::a).map (complete M))) ↔
    ∀i j p,deficit a (line M i) p → (∃q,deficit a (line M j) q) → p∉line M j := by
  rw [← oneFree a (line M)]
  exact exists_congr fun x => (build M (x::a)).symm
end PEqualNP.Outside.L_meta_10008.Completion
