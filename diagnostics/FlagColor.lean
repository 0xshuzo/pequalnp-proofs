import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007_FlagColor
open Finset
variable {n m k : Nat}
abbrev Box (n m : Nat) := Finset (Fin n) × Finset (Fin m)
abbrev Cell (n m : Nat) := Fin n × Fin m

def blank (I : Fin n → Fin m → Bool) (B : Box n m) : Prop :=
  ∀ p∈B.1, ∀ l∈B.2, I p l = false

def conflict (I : Fin n → Fin m → Bool) (a b : Cell n m) : Prop :=
  I a.1 b.2=true ∨ I b.1 a.2=true

def cluster (S : Finset (Cell n m)) : Box n m := (S.image Prod.fst,S.image Prod.snd)

theorem cluster_iff (I : Fin n → Fin m → Bool) (S : Finset (Cell n m)) :
    blank I (cluster S) ↔ ∀a∈S,∀b∈S,¬conflict I a b := by
  constructor
  · intro good a ha b hb
    have h1 := good a.1 (mem_image_of_mem _ ha) b.2 (mem_image_of_mem _ hb)
    have h2 := good b.1 (mem_image_of_mem _ hb) a.2 (mem_image_of_mem _ ha)
    simp [conflict,h1,h2]
  · intro pair p hp l hl
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hp
    obtain ⟨b,hb,rfl⟩:=mem_image.mp hl
    have h := pair a ha b hb
    cases e : I a.1 b.2
    · rfl
    · exact False.elim (h (Or.inl e))

theorem list_cover_iff (I : Fin n → Fin m → Bool) (D : Finset (Cell n m)) :
    (∃ L : List (Box n m), L.length≤k ∧ (∀B∈L,blank I B) ∧
      ∀ z∈D,∃B∈L,z.1∈B.1 ∧ z.2∈B.2) ↔
    (∃ color : D → Fin k, ∀a b : D, color a=color b → ¬conflict I a.val b.val) := by
  classical
  constructor
  · rintro ⟨L,limit,good,cover⟩
    have existsIndex (z : D) : ∃ i : Fin L.length,
        z.val.1∈(L.get i).1 ∧ z.val.2∈(L.get i).2 := by
      obtain ⟨B,hb,hp,hl⟩:=cover z.val z.property
      obtain ⟨i,eq⟩:=List.mem_iff_get.mp hb
      exact ⟨i,eq.symm ▸ hp,eq.symm ▸ hl⟩
    let pick (z : D) := Classical.choose (existsIndex z)
    have picked (z : D) := Classical.choose_spec (existsIndex z)
    refine ⟨fun z=>⟨(pick z).val,lt_of_lt_of_le (pick z).isLt limit⟩,?_⟩
    intro a b eq
    have same : pick a=pick b := Fin.ext (congrArg Fin.val eq)
    have av : a.val.1∈(L.get (pick a)).1 ∧ a.val.2∈(L.get (pick a)).2 := picked a
    have bv : b.val.1∈(L.get (pick a)).1 ∧ b.val.2∈(L.get (pick a)).2 := same.symm ▸ picked b
    have law := good _ (List.get_mem L (pick a))
    have h1:=law _ av.1 _ bv.2
    have h2:=law _ bv.1 _ av.2
    simp [conflict,h1,h2]
  · rintro ⟨color,proper⟩
    let group (t : Fin k) := ((univ : Finset D).filter (fun z=>color z=t)).image (fun z=>z.val)
    let box (t : Fin k) := cluster (group t)
    refine ⟨List.ofFn box,by simp,?_,?_⟩
    · intro B mem
      obtain ⟨t,rfl⟩:=List.mem_ofFn.mp mem
      apply (cluster_iff I _).2
      intro a ha b hb
      obtain ⟨x,hx,rfl⟩:=mem_image.mp ha
      obtain ⟨y,hy,rfl⟩:=mem_image.mp hb
      exact proper x y ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    · intro z hz
      let a : D := ⟨z,hz⟩
      have m : z∈group (color a) := mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩
      exact ⟨box (color a),List.mem_ofFn.mpr ⟨_,rfl⟩,mem_image_of_mem _ m,mem_image_of_mem _ m⟩

end PEqualNP.Outside.L_meta_10007_FlagColor
