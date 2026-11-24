import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3501_215
    (profile : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (s o : ℕ)
      (F : ℕ → Finset (Finset (Fin (N+N)))),
      let H (w i j : ℕ) := ∀ t ∈ F w, ∃ z ∈ t, z.val=i ∨ z.val=j
      2≤q → (∀ t ∈ F o, ∀ p l, I p l → Fin.castAdd N p ∈ t ∨ Fin.natAdd N l ∈ t) →
      (∀ Y : Finset (Fin N), Y.card≤q → ∃ t ∈ F o,
        (∀ p, Fin.castAdd N p ∈ t ↔ ∃ l∈Y, I p l) ∧ (∀ l, Fin.natAdd N l ∈ t ↔ l∉Y)) →
      ∀ u<N+N, ∀ v<N+N, H o u v ↔ (∃ p l : Fin N, I p l ∧ ((u=p.val ∧ v=N+l.val) ∨ (v=p.val ∧ u=N+l.val))))
    (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (s o : ℕ) (H : ℕ → ℕ → ℕ → Prop),
      (∀ l, Fintype.card {p // I p l}=q+1) →
      (∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) →
      o<N+N+s →
      (∀ i<N+N, ∀ u v, H i u v ↔ i=u ∨ i=v) →
      (∀ u<N+N, ∀ v<N+N, H o u v ↔ (∃ p l : Fin N, I p l ∧ ((u=p.val ∧ v=N+l.val) ∨ (v=p.val ∧ u=N+l.val)))) →
      (∀ g<s, ∃ a b, a<N+N+g ∧ b<N+N+g ∧
        ((∀ u v, H (N+N+g) u v ↔ H a u v ∨ H b u v) ∨
         (∀ u v, H (N+N+g) u v ↔ H a u v) ∨
         ((∀ u, ¬ H (N+N+g) u u) ∧ ∀ u v, H (N+N+g) u v ↔
           (H a u u ∧ H b v v) ∨ (H a v v ∧ H b u u)))) →
      N*(q+1)≤2*s)
    (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (s o : ℕ)
      (F : ℕ → Finset (Finset (Fin (N+N)))),
      let H (w i j : ℕ) := ∀ t ∈ F w, ∃ z ∈ t, z.val=i ∨ z.val=j
      let le (a b : ℕ) := ∀ u v, H a u v → H b u v
      let bad (a b : ℕ) := (∃ u, H a u u ∧ H b u u) ∨
        ∃ u v, H a u v ∧ H b u v ∧ ¬((H a u u ∧ H b v v) ∨ (H a v v ∧ H b u u))
      250≤q → N=q^2+q+1 → (∀ l, Fintype.card {p // I p l}=q+1) →
      (∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) →
      o<N+N+s →
      (∀ i : Fin (N+N), F i={{i}}) →
      (∀ g<s, ∃ a b, a<b ∧ b<N+N+g ∧
        (F (N+N+g) = F a ∪ F b ∨ F (N+N+g) = (F a).biUnion (fun u => (F b).image (u ∪ ·)))) →
      (∀ t ∈ F o, ∀ p l, I p l → Fin.castAdd N p ∈ t ∨ Fin.natAdd N l ∈ t) →
      (∀ Y : Finset (Fin N), Y.card≤q → ∃ t ∈ F o,
        (∀ p, Fin.castAdd N p ∈ t ↔ ∃ l∈Y, I p l) ∧ (∀ l, Fin.natAdd N l ∈ t ↔ l∉Y)) →
      (∃ g<s, ∃ a b, a<b ∧ b<N+N+g ∧ F (N+N+g)=F a∪F b ∧
        ¬le a b ∧ ¬le b a ∧ bad a b) → N*q≤100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq hn col join s o F ho leaf gates cover canonical _
  let H (w i j : ℕ) := ∀ t ∈ F w, ∃ z ∈ t, z.val=i ∨ z.val=j
  let le (a b : ℕ) := ∀ u v, H a u v → H b u v
  let bad (a b : ℕ) := (∃ u, H a u u ∧ H b u u) ∨
    ∃ u v, H a u v ∧ H b u v ∧ ¬((H a u u ∧ H b v v) ∨ (H a v v ∧ H b u u))
  by_cases obstruction : ∃ g<s, ∃ a b, a<b ∧ b<N+N+g ∧ F (N+N+g)=F a∪F b ∧
      ¬le a b ∧ ¬le b a ∧ bad a b
  · exact core q N I s o F hq hn col join ho leaf gates cover canonical obstruction
  · have atom (i : ℕ) (hi : i<N+N) (u v : ℕ) : H i u v ↔ i=u ∨ i=v := by
      have h := leaf (⟨i,hi⟩ : Fin (N+N))
      change F i = _ at h
      simp [H,h]
    have mono (w u v : ℕ) : H w u u → H w u v := by
      intro h t ht
      obtain ⟨z,hz,eq⟩ := h t ht
      exact ⟨z,hz,Or.inl (eq.elim id id)⟩
    have symm (w u v : ℕ) : H w u v → H w v u := fun h t ht => by
      obtain ⟨z,hz,e⟩ := h t ht
      exact ⟨z,hz,e.symm⟩
    have out := profile q N I s o F (by omega) cover canonical
    have bound := count q N I s o H col join ho atom out (by
      intro g hg
      obtain ⟨a,b,hab,hb,form⟩ := gates g hg
      have ha := hab.trans hb
      rcases form with hu | hp
      · have conj (u v : ℕ) : H (N+N+g) u v ↔ H a u v ∧ H b u v := by
          change (∀ t ∈ F (N+N+g), _) ↔ _
          rw [hu]
          constructor
          · intro h; exact ⟨fun t ht => h t (Finset.mem_union_left _ ht),fun t ht => h t (Finset.mem_union_right _ ht)⟩
          · rintro ⟨x,y⟩ t ht; exact (Finset.mem_union.mp ht).elim (x t) (y t)
        by_cases ab : le a b
        · exact ⟨a,b,ha,hb,Or.inr (Or.inl (fun u v => (conj u v).trans ⟨And.left,fun h => ⟨h,ab u v h⟩⟩))⟩
        by_cases ba : le b a
        · exact ⟨b,a,hb,ha,Or.inr (Or.inl (fun u v => (conj u v).trans ⟨And.right,fun h => ⟨ba u v h,h⟩⟩))⟩
        have clean : ¬bad a b := fun wrong => obstruction ⟨g,hg,a,b,hab,hb,hu,ab,ba,wrong⟩
        refine ⟨a,b,ha,hb,Or.inr (Or.inr ⟨fun u h => clean (Or.inl ⟨u,(conj u u).1 h⟩),?_⟩)⟩
        intro u v
        constructor
        · intro h
          by_contra miss
          exact clean (Or.inr ⟨u,v,(conj u v).1 h |>.1,(conj u v).1 h |>.2,miss⟩)
        · rintro (⟨x,y⟩|⟨x,y⟩)
          · exact (conj u v).2 ⟨mono _ _ _ x,symm _ _ _ (mono _ _ _ y)⟩
          · exact (conj u v).2 ⟨symm _ _ _ (mono _ _ _ x),mono _ _ _ y⟩
      · refine ⟨a,b,ha,hb,Or.inl ?_⟩
        intro u v
        constructor
        · intro h
          by_contra hn'
          push_neg at hn'
          have na := hn'.1
          have nb := hn'.2
          change ¬(∀ t ∈ F a, ∃ z ∈ t, z.val=u ∨ z.val=v) at na
          change ¬(∀ t ∈ F b, ∃ z ∈ t, z.val=u ∨ z.val=v) at nb
          push_neg at na nb
          obtain ⟨A,hA,missA⟩ := na
          obtain ⟨B,hB,missB⟩ := nb
          have hterm : A∪B ∈ F (N+N+g) := hp ▸ Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_image.mpr ⟨B,hB,rfl⟩⟩
          obtain ⟨z,hz,yes⟩ := h _ hterm
          rcases Finset.mem_union.mp hz with hza | hzb
          · exact yes.elim (missA _ hza).1 (missA _ hza).2
          · exact yes.elim (missB _ hzb).1 (missB _ hzb).2
        · intro h t ht
          rw [hp] at ht
          obtain ⟨A,hA,im⟩ := Finset.mem_biUnion.mp ht
          obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp im
          rcases h with x | y
          · obtain ⟨z,hz,eq⟩ := x A hA; exact ⟨z,Finset.mem_union_left _ hz,eq⟩
          · obtain ⟨z,hz,eq⟩ := y B hB; exact ⟨z,Finset.mem_union_right _ hz,eq⟩)
    exact (Nat.mul_le_mul_left N (by omega : q≤q+1)).trans (bound.trans (by omega))
