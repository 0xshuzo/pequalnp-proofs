import PEqualNP.Defs

-- The sparse-cover and small-order arguments are from R_meta_2794_601.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3781_215
    (certificates : ∀ (Z : Type) (m s : ℕ) (X : ℕ → Set Z), (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        X (m+g) = X a ∪ X b ∨ X (m+g) = X a ∨ X (m+g) = ∅ ∨ X (m+g) = X a ∩ X b) →
      ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
        (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) ∧
        ∀ w < m+s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
          ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v)
    (freshPoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ T : Finset (Fin N), T.card ≤ q → ∀ l : Fin N, l ∉ T →
        ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (collide : ∀ (m s : ℕ) (F : ℕ → Set (Finset ℕ)),
      (∀ v < m, F v = {{v}}) →
      (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) →
      let K (w : ℕ) : Set ℕ := {v | ∀ A ∈ F w, v ∈ A}
      (∃ g < s, (K (m+g)).Nonempty ∧
        ¬ ∃ a < m+g, ∃ b < m+g, K (m+g) = K a ∪ K b) →
      ∃ g < s, ∃ a < m+g, ∃ b < m+g, F (m+g) = F a ∪ F b ∧
        ∃ A ∈ F a, ∃ B ∈ F b, ¬ Disjoint A B)
    (overlapBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∃ x15 < x9, ∃ x16 < x2 + x2 + x15, ∃ x17 < x2 + x2 + x15, x11 (x2 + x2 + x15) = x11 x16 ∪ x11 x17 ∧ ∃ x18 ∈ x11 x16, ∃ x19 ∈ x11 x17, ¬Disjoint x18 x19) → (∀ x16 ∈ x11 x10, ∀ (x18 x19 : Fin x2), x3 x18 x19 → ↑x18 ∈ x16 ∨ x2 + ↑x19 ∈ x16) → (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ x19 ∈ x11 x10, ∀ (x20 : Fin x2), (↑x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (x2 + ↑x20 ∈ x19 ↔ x20 ∉ x17)) → x2 * x1 ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (0 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  dsimp only
  intro q N I inst hq hN degrees unique even s o X ho inputs steps pos neg witness
  classical
  obtain ⟨F, leaves, gates, spec⟩ := certificates _ (N+N) s X (by
    intro i hi
    obtain ⟨a,b,h,law⟩ := steps i hi
    exact ⟨a,(max_lt_iff.mp h).1,b,(max_lt_iff.mp h).2,by simpa using law⟩)
  have cover (A : Finset ℕ) (hA : A ∈ F o) (p l : Fin N) (h : I p l) : p.val ∈ A ∨ N+l.val ∈ A := by
    by_contra! miss
    apply ((spec o ho).2 _).mpr ⟨A,hA,?_⟩ (pos p l h)
    intro v hv
    have hvb := (spec o ho).1 A hA v hv
    by_cases small : v < N
    · let k : Fin N := ⟨v,small⟩
      rw [(inputs k).1]
      change ¬ decide (k = p) = true
      exact fun e => miss.1 ((congrArg Fin.val (of_decide_eq_true e)) ▸ hv)
    · let k : Fin N := ⟨v-N,by omega⟩
      have e : v = N + k.val := by dsimp [k]; omega
      rw [e,(inputs k).2]
      change ¬ decide (k = l) = true
      intro eq
      have : v = N+l.val := e.trans (congrArg (fun a : Fin N => N+a.val) (of_decide_eq_true eq))
      exact miss.2 (this ▸ hv)
  have saturated : ∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
      (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T) := by
    intro T ht
    let y := fun l : Fin N => decide (l ∈ T)
    let x := fun p : Fin N => decide (¬ ∃ l, I p l ∧ y l = true)
    have cy : Fintype.card {l : Fin N // y l = true} ≤ q := by
      simpa [Fintype.card_subtype, y] using ht
    obtain ⟨A,hA,zero⟩ := ((spec o ho).2 (x,y)).mp (neg y cy)
    have pl (p : Fin N) (h : p.val ∈ A) : ∃ l ∈ T, I p l := by
      have hh := zero p.val h
      rw [(inputs p).1] at hh
      change ¬ x p = true at hh
      simpa [x,y,and_comm] using hh
    have ln (l : Fin N) (h : N+l.val ∈ A) : l ∉ T := by
      have hh := zero _ h
      rw [(inputs l).2] at hh
      exact fun m => hh (show y l = true from decide_eq_true m)
    refine ⟨A,hA,fun p => ⟨⟨pl p,?_⟩,⟨ln p,?_⟩⟩⟩
    · rintro ⟨l,hl,inc⟩
      exact (cover A hA p l inc).resolve_right (fun bad => ln l bad hl)
    · intro hp
      obtain ⟨a, ha, avoid⟩ := freshPoint q N I degrees unique T ht p hp
      apply (cover A hA a p ha).resolve_left
      intro bad
      obtain ⟨l,hl,inc⟩ := pl a bad
      exact avoid l hl inc
  let idx (d : Bool) (p : Fin N) := if d then p.val else N+p.val
  let sample (d : Bool) (p : Fin N) : (Fin N → Bool) × (Fin N → Bool) :=
    if d then (fun i => decide (i=p), fun _ => false) else (fun _ => false, fun i => decide (i=p))
  have raw (d : Bool) (p : Fin N) (v : ℕ) (hv : v < N+N) :
      sample d p ∈ X v ↔ v = idx d p := by
    by_cases small : v < N
    · let k : Fin N := ⟨v,small⟩
      have eq : X v = {z | z.1 k = true} := (inputs k).1
      rw [eq]
      cases d <;> simp [sample,idx,k,Fin.ext_iff] <;> omega
    · let k : Fin N := ⟨v-N,by omega⟩
      have ve : N+k.val=v := by dsimp [k]; omega
      have eq : X v = {z | z.2 k = true} := ve ▸ (inputs k).2
      rw [eq]
      cases d <;> simp [sample,idx,k,Fin.ext_iff] <;> omega
  have axis (d : Bool) (p : Fin N) (w : ℕ) (hw : w < N+N+s) :
      sample d p ∈ X w ↔ ∀ A ∈ F w, idx d p ∈ A := by
    constructor
    · intro hit A hA
      by_contra miss
      apply ((spec w hw).2 _).mpr ⟨A,hA,?_⟩ hit
      intro v hv active
      have e := (raw d p v ((spec w hw).1 A hA v hv)).mp active
      exact miss (e ▸ hv)
    · intro every
      by_contra miss
      obtain ⟨A,hA,absent⟩ := ((spec w hw).2 _).mp miss
      have inc := every A hA
      exact absent _ inc ((raw d p _ ((spec w hw).1 A hA _ inc)).mpr rfl)
  by_cases large : 200 ≤ q
  · apply overlapBound q N I large hN degrees unique s o F ho leaves gates _ cover saturated
    apply collide (N+N) s F leaves gates
    obtain ⟨i,hi,d,p,r,_,hp,_,novel⟩ := witness
    refine ⟨i,hi,⟨idx d p,(axis d p _ (by omega)).mp hp⟩,?_⟩
    rintro ⟨a,ha,b,hb,e⟩
    apply novel
    refine ⟨a,ha,b,hb,?_⟩
    ext t
    change sample d t ∈ X (N+N+i) ↔ sample d t ∈ X a ∨ sample d t ∈ X b
    rw [axis d t _ (by omega), axis d t a (by omega), axis d t b (by omega)]
    exact Set.ext_iff.mp e (idx d t)
  have propagate (g : ℕ) (hg : g < s) : ∃ a < N+N+g, ∃ b < N+N+g,
      ∀ A ∈ F (N+N+g), ∀ v ∈ A, ∃ B, (B ∈ F a ∨ B ∈ F b) ∧ v ∈ B := by
    obtain ⟨a,ha,b,hb,law⟩ := gates g hg
    refine ⟨a,ha,b,hb,?_⟩
    intro A hA v hv
    rcases law with join|copy|empty|meet
    · rw [join] at hA
      obtain ⟨U,hU,V,hV,rfl⟩ := hA
      exact (Finset.mem_union.mp hv).elim (fun h => ⟨U,Or.inl hU,h⟩) (fun h => ⟨V,Or.inr hV,h⟩)
    · exact ⟨A,Or.inl (copy ▸ hA),hv⟩
    · have e : A = ∅ := Set.mem_singleton_iff.mp (empty ▸ hA)
      exact False.elim (Finset.notMem_empty _ (e ▸ hv))
    · rw [meet] at hA; exact ⟨A,hA,hv⟩
  have reach (k : ℕ) (hk : k ≤ s) (W : Finset ℕ) (hw : ∀ w ∈ W, w < N+N+k) :
      ∃ S : Finset ℕ, S.card ≤ W.card+k ∧ ∀ w ∈ W, ∀ A ∈ F w, A ⊆ S := by
    induction k generalizing W with
    | zero =>
      refine ⟨W,by omega,?_⟩
      intro w mem A cert
      rw [leaves w (by simpa using hw w mem)] at cert
      have : A = {w} := Set.mem_singleton_iff.mp cert
      simpa [this] using mem
    | succ k ih =>
      let w := N+N+k
      by_cases use : w ∈ W
      · obtain ⟨a,ha,b,hb,parent⟩ := propagate k (by omega)
        let U := insert a (insert b (W.erase w))
        have bounds : ∀ u ∈ U, u < w := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl|h
          · exact hb
          obtain ⟨ne,inc⟩ := Finset.mem_erase.mp h
          have bound := hw u inc
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,dep⟩ := ih (by omega) U bounds
        have uc : U.card ≤ W.card+1 := by
          have c1 := Finset.card_insert_le a (insert b (W.erase w))
          have c2 := Finset.card_insert_le b (W.erase w)
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_,use⟩
          dsimp [U]; omega
        refine ⟨S,by omega,?_⟩
        intro u hu A cert v hv
        by_cases eq : u=w
        · subst u
          obtain ⟨B,anc,hv'⟩ := parent A cert v hv
          rcases anc with h|h
          · exact dep a (by simp [U]) B h hv'
          · exact dep b (by simp [U]) B h hv'
        · exact dep u (by simp [U,eq,hu]) A cert hv
      · have bounds : ∀ u ∈ W, u < w := by
          intro u hu
          have ne : u ≠ w := fun eq => use (eq ▸ hu)
          have bound := hw u hu
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,h⟩ := ih (by omega) W bounds
        exact ⟨S,by omega,h⟩
  obtain ⟨S,card,dep⟩ := reach s le_rfl {o} (by simpa using ho)
  have allBits : Finset.range (N+N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_cases point : v < N
    · let p : Fin N := ⟨v,point⟩
      have big : 2 ≤ N := by nlinarith [Nat.zero_le (q^2)]
      let p' : Fin N := if p.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : p ≠ p' := by
        intro e
        have eq := congrArg Fin.val e
        unfold p' at eq
        split at eq
        · change p.val = 1 at eq; omega
        · change p.val = 0 at eq; contradiction
      obtain ⟨l,hl,_⟩ := unique p p' ne
      obtain ⟨A,hA,eq⟩ := saturated {l} (by simp; omega)
      exact dep o (by simp) A hA ((eq p).1.mpr ⟨l,by simp,hl.1⟩)
    · let l : Fin N := ⟨v-N,by omega⟩
      obtain ⟨A,hA,eq⟩ := saturated ∅ (by simp)
      have inc := dep o (by simp) A hA ((eq l).2.mpr (by simp))
      have e : N+l.val=v := by dsimp [l]; omega
      exact e ▸ inc
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range] at count
  simp only [Finset.card_singleton] at card
  have qmax : q ≤ 199 := by omega
  have := Nat.mul_le_mul_left N qmax
  have nn : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  omega
