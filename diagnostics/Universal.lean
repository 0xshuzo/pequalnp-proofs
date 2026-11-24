import Mathlib
import PEqualNP.Defs

namespace Universal3451

abbrev pt {N : ℕ} (p : Fin N) : Fin (N+N) := Fin.castAdd N p
abbrev ln {N : ℕ} (l : Fin N) : Fin (N+N) := Fin.natAdd N l

theorem apart {N : ℕ} (p l : Fin N) : pt p ≠ ln l := by
  intro e
  have h := congrArg Fin.val e
  change p.val=N+l.val at h
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj a b := ∃ p l, I p l ∧ ((a=pt p ∧ b=ln l) ∨ (b=pt p ∧ a=ln l))
  symm := ⟨fun _ _ ⟨p,l,h,edge⟩ => ⟨p,l,h,edge.symm⟩⟩
  loopless := ⟨fun _ ⟨p,l,_,h⟩ => by rcases h with ⟨a,b⟩|⟨a,b⟩ <;> exact apart p l (a.symm.trans b)⟩

instance {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] : DecidableRel (graph I).Adj :=
  fun a b => inferInstanceAs (Decidable (∃ p l, I p l ∧ ((a=pt p ∧ b=ln l) ∨ (b=pt p ∧ a=ln l))))

theorem isForest {V : Type*} [Fintype V] (G : SimpleGraph V) (rank : V → ℕ)
    (fork : ∀ x u v, G.Adj x u → G.Adj x v → u≠v → rank x<rank u ∨ rank x<rank v) : G.IsAcyclic := by
  classical
  intro z w cyc
  obtain ⟨m, hm, hmax⟩ := w.support.toFinset.exists_max_image rank ⟨z, by simp⟩
  have hm' : m ∈ w.support := by simpa using hm
  have hq : (w.rotate m hm').IsCycle := cyc.rotate hm'
  have hs := (w.rotate m hm').adj_snd hq.not_nil
  have hp := ((w.rotate m hm').adj_penultimate hq.not_nil).symm
  have m1 : (w.rotate m hm').snd ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have m2 : (w.rotate m hm').penultimate ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  rcases fork m _ _ hs hp hq.snd_ne_penultimate with h|h
  · exact (not_lt_of_ge (hmax _ (List.mem_toFinset.mpr m1))) h
  · exact (not_lt_of_ge (hmax _ (List.mem_toFinset.mpr m2))) h

theorem starForest {α β V : Type*} [Fintype V] (G : SimpleGraph V) (L : α → V) (R : β → V)
    (inj : Function.Injective L) (different : ∀ a b, L a ≠ R b) (I : α → β → Prop)
    (adj : ∀ a b, G.Adj a b ↔ ∃ p l, I p l ∧ ((a=L p ∧ b=R l) ∨ (b=L p ∧ a=R l)))
    (r : α) (leaf : ∀ p, p≠r → ∀ a b, I p a → I p b → a=b) : G.IsAcyclic := by
  classical
  let rank (x : V) : ℕ := if x=L r then 0 else if x∈Set.range L then 2 else 1
  have right (l : β) : rank (R l)=1 := by
    have outside : R l ∉ Set.range L := by rintro ⟨a,eq⟩;exact different a l eq
    simp only [rank,if_neg (different r l).symm,if_neg outside]
  have left (p : α) (h : p≠r) : rank (L p)=2 := by
    have neq : L p≠L r := fun e => h (inj e)
    simp [rank,neq,Set.mem_range_self]
  have center : rank (L r)=0 := by simp [rank]
  apply isForest G rank
  intro x u v xu xv ne
  obtain ⟨p,l,pl,h⟩ := (adj x u).mp xu
  obtain ⟨q,k,qk,h'⟩ := (adj x v).mp xv
  rcases h with ⟨xp,ul⟩|⟨up,xl⟩ <;> rcases h' with ⟨xq,vk⟩|⟨vq,xk⟩
  · have pq := inj (xp.symm.trans xq)
    subst q
    by_cases pr : p=r
    · subst p;exact Or.inl (by rw [xp,ul,center,right];decide)
    · have lk := leaf p pr l k pl qk
      exact False.elim (ne (ul.trans ((congrArg R lk).trans vk.symm)))
  · exact False.elim (different p k (xp.symm.trans xk))
  · exact False.elim (different q l (xq.symm.trans xl))
  · by_cases pr : p=r
    · have qr : q≠r := fun eq => ne (up.trans ((congrArg L (pr.trans eq.symm)).trans vq.symm))
      exact Or.inr (by rw [xl,vq,right,left q qr];decide)
    · exact Or.inl (by rw [xl,up,right,left p pr];decide)

theorem universal {N : ℕ} (I : Fin N → Fin N → Prop)
    (free : ∀ p q a b, p≠q → a≠b → ¬(I p a ∧ I p b ∧ I q a ∧ I q b))
    (full : (∃ r, ∀ l, I r l) ∨ (∃ c, ∀ p, I p c)) : (graph I).IsAcyclic := by
  rcases full with ⟨r,hr⟩|⟨c,hc⟩
  · apply starForest (graph I) pt ln (fun _ _ h => Fin.ext (congrArg Fin.val h)) apart I (fun _ _ => Iff.rfl) r
    intro p pr a b pa pb
    by_contra ab
    exact free p r a b pr ab ⟨pa,pb,hr a,hr b⟩
  · have lined : Function.Injective (@ln N) := by
      intro i j e
      have h := congrArg Fin.val e
      change N+i.val=N+j.val at h
      exact Fin.ext (Nat.add_left_cancel h)
    have flipped (a b : Fin (N+N)) : (graph I).Adj a b ↔ ∃ l p, I p l ∧ ((a=ln l ∧ b=pt p) ∨ (b=ln l ∧ a=pt p)) := by
      constructor
      · rintro ⟨p,l,h,⟨a,b⟩|⟨b,a⟩⟩
        · exact ⟨l,p,h,Or.inr ⟨b,a⟩⟩
        · exact ⟨l,p,h,Or.inl ⟨a,b⟩⟩
      · rintro ⟨l,p,h,⟨a,b⟩|⟨b,a⟩⟩
        · exact ⟨p,l,h,Or.inr ⟨b,a⟩⟩
        · exact ⟨p,l,h,Or.inl ⟨a,b⟩⟩
    apply starForest (graph I) ln pt lined (fun l p => (apart p l).symm) (fun l p => I p l) flipped c
    intro l ne a b al bl
    by_contra ab
    exact free a b l c ab ne ⟨al,hc a,bl,hc b⟩

end Universal3451
