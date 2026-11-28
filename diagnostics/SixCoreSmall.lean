import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18065
def HasPartners {n : ℕ} (F : Finset (Fin n × Fin n)) : Prop :=
  ∀ a b, (a,b) ∈ F → (∃ c, c≠b ∧ (a,c)∈F) ∧ (∃ d, d≠a ∧ (d,b)∈F)

theorem side_count {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (two : ∀ a b, (a,b) ∈ E → ∃ c, c ≠ b ∧ (a,c) ∈ E) :
    (E.image Prod.fst).card * 2 ≤ E.card := by
  classical
  let P := E.image Prod.fst
  have picks (p : P) : ∃ b c, b ≠ c ∧ (p.val,b) ∈ E ∧ (p.val,c) ∈ E := by
    obtain ⟨⟨a,b⟩,ab,e⟩ := Finset.mem_image.mp p.property
    change a = p.val at e
    obtain ⟨c,ne,ac⟩ := two a b ab
    exact ⟨b,c,ne.symm,e ▸ ab,e ▸ ac⟩
  choose first second diff one two using picks
  let edge (p : P) (b : Bool) : E := if b then ⟨(p.val,first p),one p⟩ else ⟨(p.val,second p),two p⟩
  have inj : Function.Injective (fun x : P × Bool => edge x.1 x.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have row (r : P) (b : Bool) : (edge r b).val.1 = r.val := by cases b <;> rfl
    have pe : p = q := Subtype.ext ((row p i).symm.trans ((congrArg (fun t : E => t.val.1) eq).trans (row q j)))
    subst q
    cases i <;> cases j
    · rfl
    · exact ((diff p).symm (congrArg (fun t : E => t.val.2) eq)).elim
    · exact (diff p (congrArg (fun t : E => t.val.2) eq)).elim
    · rfl
  have bound := Fintype.card_le_of_injective _ inj
  simpa [P] using bound



theorem sixConcentration {n : ℕ} (E F : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
    (sub : F ⊆ E) (mat : ∀ i, (i,p i)∈E) (hp : HasPartners F)
    (few : E.card ≤ n+6) (large : 10 < F.card) :
    ∃ T : Finset (Fin n), (T.card=5 ∨ T.card=6) ∧
      F.card=T.card+6 ∧ (∀ i∈T, (i,p i)∈F) ∧
      ∀ i j, (i,j)∈E → j≠p i → (i,j)∈F ∧ i∈T ∧ p.symm j∈T := by
  classical
  let M : Finset (Fin n × Fin n) := Finset.univ.image (fun i => (i,p i))
  have mem (e : Fin n × Fin n) : e∈M ↔ e.2=p e.1 := by
    rcases e with ⟨a,b⟩
    constructor
    · intro h
      obtain ⟨i,_,h⟩ := Finset.mem_image.mp h
      cases h
      rfl
    · intro h
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,Prod.ext rfl h.symm⟩
  have mcard : M.card=n := by
    dsimp [M]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h)]
    simp
  have subM : M ⊆ E := by
    rintro ⟨a,b⟩ h
    have eq : b=p a := (mem _).mp h
    simpa [eq] using mat a
  let A := F ∩ M
  let B := F \ M
  have part : B.card + A.card = F.card := Finset.card_sdiff_add_card_inter F M
  have rest : (E \ M).card + M.card = E.card := Finset.card_sdiff_add_card_eq_card subM
  have bsub : B ⊆ E \ M := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨sub (Finset.mem_sdiff.mp he).1,(Finset.mem_sdiff.mp he).2⟩
  have bs := Finset.card_le_card bsub
  have sA : A ⊆ F := Finset.inter_subset_left
  have injL : Set.InjOn Prod.fst (↑A : Set (Fin n × Fin n)) := by
    intro a ha b hb eq
    apply Prod.ext eq
    rw [(mem a).mp (Finset.mem_inter.mp ha).2,(mem b).mp (Finset.mem_inter.mp hb).2,eq]
  have injR : Set.InjOn Prod.snd (↑A : Set (Fin n × Fin n)) := by
    intro a ha b hb eq
    apply Prod.ext _ eq
    apply p.injective
    exact ((mem a).mp (Finset.mem_inter.mp ha).2).symm.trans
      (eq.trans ((mem b).mp (Finset.mem_inter.mp hb).2))
  have lc : (A.image Prod.fst).card=A.card := Finset.card_image_of_injOn injL
  have rc : (A.image Prod.snd).card=A.card := Finset.card_image_of_injOn injR
  have lsub : A.image Prod.fst ⊆ F.image Prod.fst := Finset.image_subset_image sA
  have rsub : A.image Prod.snd ⊆ F.image Prod.snd := Finset.image_subset_image sA
  have lmax := side_count F (fun a b ab => (hp a b ab).1)
  have flip {a b : Fin n} : (b,a) ∈ F.image Prod.swap ↔ (a,b)∈F := by
    constructor
    · rintro h
      obtain ⟨⟨u,v⟩,hu,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact hu
    · exact fun h => Finset.mem_image_of_mem Prod.swap h
  have rmax := side_count (F.image Prod.swap) (fun b a ba => by
    obtain ⟨d,ne,h⟩ := (hp a b (flip.mp ba)).2
    exact ⟨d,ne,flip.mpr h⟩)
  rw [Finset.image_image,Finset.card_image_of_injective _ Prod.swap_injective] at rmax
  change (F.image Prod.snd).card*2 ≤ F.card at rmax
  have ll := Finset.card_le_card lsub
  have rr := Finset.card_le_card rsub
  have lsame : A.image Prod.fst = F.image Prod.fst := Finset.eq_of_subset_of_card_le lsub (by omega)
  have rsame : A.image Prod.snd = F.image Prod.snd := Finset.eq_of_subset_of_card_le rsub (by omega)
  have extras : B = E \ M := Finset.eq_of_subset_of_card_le bsub (by omega)
  refine ⟨A.image Prod.fst,by omega,by omega,?_,?_⟩
  · intro i hi
    obtain ⟨⟨u,v⟩,h,eq⟩ := Finset.mem_image.mp hi
    change u=i at eq
    subst i
    have paired : v=p u := (mem _).mp (Finset.mem_inter.mp h).2
    exact paired ▸ (sA h)
  · intro i j hi ne
    have hB : (i,j) ∈ B := by
      rw [extras]
      exact Finset.mem_sdiff.mpr ⟨hi,fun a => ne ((mem _).mp a)⟩
    have hf : (i,j)∈F := (Finset.mem_sdiff.mp hB).1
    refine ⟨hf,lsame.symm ▸ Finset.mem_image_of_mem Prod.fst hf,?_⟩
    have hr : j ∈ A.image Prod.snd := rsame.symm ▸ Finset.mem_image_of_mem Prod.snd hf
    obtain ⟨⟨u,v⟩,h,eq⟩ := Finset.mem_image.mp hr
    change v=j at eq
    have paired : v=p u := (mem _).mp (Finset.mem_inter.mp h).2
    have key : p.symm j=u := by rw [← eq,paired,p.symm_apply_apply]
    rw [key]
    exact Finset.mem_image_of_mem Prod.fst h
end PEqualNP.Outside.L_meta_18065
