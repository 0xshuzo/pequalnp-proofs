import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17257

abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : Bank α) (n s : ℕ) := ∀ j<s,
  ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a∩W b

def UnionAt {α : Type*} (W : Bank α) (n j : ℕ) := ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b

theorem upward {α : Type*} {W : Bank α} {n s : ℕ} (hs : Steps W n s)
    {x y : α} (h : ∀ i<n, x∈W i → y∈W i) : ∀ w<n+s, x∈W w → y∈W w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hi : w<n
    · exact h w hi hx
    let j := w-n
    have eq : n+j=w := by dsimp [j]; omega
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := hs j (by dsimp [j]; omega) <;>
      rw [eq] at ha hb e <;> rw [e] at hx ⊢
    · exact hx.elim (fun t => Or.inl (ih a ha (ha.trans hw) t)) (fun t => Or.inr (ih b hb (hb.trans hw) t))
    · exact ih a ha (ha.trans hw) hx
    · exact hx
    · exact ⟨ih a ha (ha.trans hw) hx.1,ih b hb (hb.trans hw) hx.2⟩

theorem certificate {α : Type*} (W : Bank α) (n s : ℕ) (hs : Steps W n s)
    (U : Finset ℕ) (uni : ∀ j<s, j∈U ↔ UnionAt W n j) (x : α)
    (k : ℕ) (hk : k≤s) (S : Finset ℕ) (lo : ∀ w∈S,w<n+k) (off : ∀ w∈S,x∉W w) :
    ∃ R : Finset ℕ, R ⊆ Finset.range n ∧ R.card ≤ S.card+(U∩Finset.range k).card ∧
      (∀ r∈R,x∉W r) ∧ ∀ y : α, (∀ r∈R,y∉W r) → ∀ w∈S,y∉W w := by
  classical
  induction k generalizing S with
  | zero =>
    exact ⟨S,fun i hi => Finset.mem_range.mpr (by simpa using lo i hi),by simp,off,fun _ h => h⟩
  | succ k ih =>
    let v := n+k
    have below (i : ℕ) (hi : i∈S) (ne : i≠v) : i<n+k := by
      have := lo i hi
      dsimp [v] at ne
      omega
    have older : U∩Finset.range k ⊆ U∩Finset.range (k+1) :=
      fun i hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (Finset.mem_inter.mp hi).2))⟩
    by_cases active : v∈S
    · have old := off v active
      have clause : ∃ B : Finset ℕ, B.card ≤ 1+(if k∈U then 1 else 0) ∧
          (∀ i∈B,i<v) ∧ (∀ i∈B,x∉W i) ∧ ∀ y : α, (∀ i∈B,y∉W i) → y∉W v := by
        by_cases hu : k∈U
        · obtain ⟨a,ha,b,hb,hg⟩ := (uni k (by omega)).mp hu
          change W v=W a∪W b at hg
          rw [hg] at old
          refine ⟨{a,b},by simpa [hu] using (Finset.card_le_two (a:=a) (b:=b)),?_,?_,?_⟩
          · simpa using And.intro ha hb
          · simpa using (show x∉W a ∧ x∉W b from ⟨fun t => old (Or.inl t),fun t => old (Or.inr t)⟩)
          · intro y h
            rw [hg]
            exact fun t => t.elim (h a (by simp)) (h b (by simp))
        · obtain ⟨a,ha,b,hb,eq|eq|eq|eq⟩ := hs k (by omega)
          · exact (hu ((uni k (by omega)).mpr ⟨a,ha,b,hb,eq⟩)).elim
          · change W v=W a at eq
            rw [eq] at old
            refine ⟨{a},by simp [hu],by simpa using ha,by simpa using old,?_⟩
            intro y h
            rw [eq]
            exact h a (by simp)
          · change W v=∅ at eq
            exact ⟨∅,by simp,by simp,by simp,by simp [eq]⟩
          · change W v=W a∩W b at eq
            rw [eq] at old
            by_cases ax : x∈W a
            · have bx : x∉W b := fun t => old ⟨ax,t⟩
              refine ⟨{b},by simp [hu],by simpa using hb,by simpa using bx,?_⟩
              intro y h
              rw [eq]
              exact fun t => h b (by simp) t.2
            · refine ⟨{a},by simp [hu],by simpa using ha,by simpa using ax,?_⟩
              intro y h
              rw [eq]
              exact fun t => h a (by simp) t.1
      obtain ⟨B,bs,bl,bo,bc⟩ := clause
      let Q := S.erase v ∪ B
      have ql : ∀ i∈Q,i<n+k := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact below i (Finset.mem_erase.mp a).2 (Finset.mem_erase.mp a).1
        · exact bl i b
      have qo : ∀ i∈Q,x∉W i := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact off i (Finset.mem_erase.mp a).2
        · exact bo i b
      obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) Q ql qo
      refine ⟨R,rr,?_,ro,?_⟩
      · have merge := Finset.card_union_le (S.erase v) B
        have er := Finset.card_erase_add_one active
        dsimp [Q] at cr
        by_cases inU : k∈U
        · have strict : U∩Finset.range k ⊂ U∩Finset.range (k+1) := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨older,?_⟩
            intro eq
            have mem : k∈U∩Finset.range (k+1) := by simp [inU]
            rw [←eq] at mem
            simpa using mem
          have := Finset.card_lt_card strict
          simp [inU] at bs
          omega
        · have := Finset.card_le_card older
          simp [inU] at bs
          omega
      · intro y yr w hw
        have h := rc y yr
        by_cases eq : w=v
        · exact eq ▸ bc y (fun b hb => h b (Finset.mem_union_right _ hb))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) S (fun w hw => below w hw (fun eq => active (eq ▸ hw))) off
      exact ⟨R,rr,cr.trans (Nat.add_le_add_left (Finset.card_le_card older) _),ro,rc⟩

def one {N : ℕ} (l : Fin N) : Vec N := fun k => decide (k=l)
def negRow {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (Y : Vec N) :
    Board N := (fun p => decide (¬∃ l, I p l ∧ Y l=true),Y)
def Inputs {N} (W : Bank (Board N)) := ∀ i : Fin N,
    W i.val = {z | z.1 i=true} ∧ W (N+i.val) = {z | z.2 i=true}

theorem union_floor {q N s o} (I : Fin N → Fin N → Prop) [DecidableRel I] (W : Bank (Board N))
    (ho : o<N+N+s) (raw : Inputs W) (steps : Steps W (N+N) s)
    (pos : ∀ p l, I p l → (one p,one l)∈W o)
    (neg : ∀ Y : Vec N, Fintype.card {l // Y l=true} ≤ q → negRow I Y ∉ W o)
    (cols : ∀ l, ∃ p,I p l) (U : Finset ℕ) (uni : ∀ j<s, j∈U ↔ UnionAt W (N+N) j) :
    N≤U.card+1 := by
  classical
  let x : Board N := ((fun _ => true),(fun _ => false))
  have xoff : x∉W o := by
    have h := neg (fun _ => false) (by simp)
    simpa [negRow,x] using h
  obtain ⟨R,rr,cr,ro,rc⟩ := certificate W (N+N) s steps U uni x s le_rfl {o}
    (by simpa using ho) (by simpa using xoff)
  have inc (l : Fin N) : N+l.val∈R := by
    by_contra miss
    obtain ⟨p,hp⟩ := cols l
    let y : Board N := ((fun _ => true),one l)
    have yr : ∀ r∈R,y∉W r := by
      intro r hr
      have lt := Finset.mem_range.mp (rr hr)
      by_cases left : r<N
      · let t : Fin N := ⟨r,left⟩
        exact (ro r hr (by change x∈W t.val; rw [(raw t).1]; rfl)).elim
      · let t : Fin N := ⟨r-N,by omega⟩
        have e : N+t.val=r := by dsimp [t]; omega
        have ne : t≠l := by rintro rfl; exact miss (e.symm ▸ hr)
        rw [←e,(raw t).2]
        change ¬decide (t=l)=true
        simp [ne]
    have up : ∀ r<N+N, (one p,one l)∈W r → y∈W r := by
      intro r hr
      by_cases left : r<N
      · let t : Fin N := ⟨r,left⟩
        change _ → y∈W t.val
        rw [(raw t).1]
        exact fun _ => rfl
      · let t : Fin N := ⟨r-N,by omega⟩
        have e : N+t.val=r := by dsimp [t]; omega
        rw [←e,(raw t).2]
        exact fun h => h
    exact rc y yr o (by simp) (upward steps up o ho (pos p l hp))
  have a : (Finset.univ : Finset (Fin N)).card≤R.card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin N => N+i.val)
    · exact fun i _ => inc i
    · exact fun i _ j _ e => Fin.ext (Nat.add_left_cancel e)
  have b := Finset.card_le_card (Finset.inter_subset_left : U∩Finset.range s ⊆ U)
  simp only [Finset.card_singleton] at cr
  simpa using (show (Finset.univ : Finset (Fin N)).card ≤ U.card+1 by omega)

def Posted : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → x1 % (2 : ℕ) = (0 : ℕ) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11

def Unrestricted : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 Steps x14 (x2+x2) x11 → (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → x1 % (2 : ℕ) = (0 : ℕ) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11

theorem exact_equivalence : Posted ↔ Unrestricted := by
  classical
  constructor
  · intro h q N I inst
    dsimp only
    intro hq hn cols geom s o W ho raw steps pos neg even
    by_contra! small
    let U := (Finset.range s).filter (UnionAt W (N+N))
    let M := Finset.range s \ U
    have hu (j : ℕ) (hj : j<s) : j∈U ↔ UnionAt W (N+N) j := by
      simp [U,hj]
    have col (l : Fin N) : ∃ p, I p l := by
      have hpos : 0<Fintype.card {p : Fin N // I p l} := by rw [cols l]; omega
      obtain ⟨⟨p,hp⟩⟩ := Fintype.card_pos_iff.mp hpos
      exact ⟨p,hp⟩
    have floor := union_floor I W ho raw steps pos neg col U hu
    have exactcount : M.card + U.card = s := by
      simpa [M] using Finset.card_sdiff_add_card_eq_card (show U ⊆ Finset.range s from Finset.filter_subset _ _)
    have big : 2≤N := by rw [hn]; omega
    have mark : 100*M.card < N*q := by
      rw [Nat.mul_add,Nat.mul_one] at small
      omega
    apply small.not_ge
    apply h q N I hq hn cols geom s o M W ho raw _ pos neg mark even
    intro j hj
    by_cases uj : j∈U
    · obtain ⟨a,ha,b,hb,eq⟩ := (hu j hj).mp uj
      exact ⟨a,ha,b,hb,Or.inl (by simp [eq])⟩
    · have mj : j∈M := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj,uj⟩
      obtain ⟨a,ha,b,hb,eq|eq|eq|eq⟩ := steps j hj
      · exact ⟨a,ha,b,hb,Or.inl (by simp [eq])⟩
      · exact ⟨a,ha,b,hb,Or.inl (by simp [eq])⟩
      · exact ⟨a,ha,b,hb,Or.inl (by simp [eq])⟩
      · exact ⟨a,ha,b,hb,Or.inr ⟨eq,Or.inl mj⟩⟩
  · intro h q N I inst
    dsimp only
    intro hq hn cols geom s o M W ho raw steps pos neg mark even
    apply h q N I hq hn cols geom s o W ho raw _ pos neg even
    intro j hj
    obtain ⟨a,ha,b,hb,eq|eq⟩ := steps j hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at eq
      exact ⟨a,ha,b,hb,eq.imp_right (Or.imp_right Or.inl)⟩
    · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr eq.1))⟩

namespace Normal
variable {α : Type*}

def Improves (P F A B : Set α) : Prop :=
  (∀ x∈P, x∈A → x∈B) ∧ (∀ x∈F, x∈B → x∈A)

def Split (S A B : Set α) : Prop :=
  (∃ x∈S, x∈A ∧ x∉B) ∧ ∃ x∈S, x∈B ∧ x∉A

def Sharp (P F A B V : Set α) : Prop :=
  V=A ∨ V=B ∨ V=∅ ∨ (V=A∪B ∧ Split P A B) ∨ (V=A∩B ∧ Split F A B)

def Clean (P F : Set α) (W : Bank α) (n s : ℕ) :=
  ∀ j<s, ∃ a<n+j, ∃ b<n+j, Sharp P F (W a) (W b) (W (n+j))

private theorem reflImp (P F A : Set α) : Improves P F A A :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

private theorem oneUnion {P F A B A' B' : Set α}
    (ha : Improves P F A A') (hb : Improves P F B B') :
    ∃ V, Sharp P F A' B' V ∧ Improves P F (A∪B) V := by
  classical
  by_cases ab : ∀ x∈P, x∈A' → x∈B'
  · refine ⟨B',Or.inr (Or.inl rfl),?_,?_⟩
    · intro x hp hx
      exact hx.elim (fun t => ab x hp (ha.1 x hp t)) (hb.1 x hp)
    · exact fun x hf h => Or.inr (hb.2 x hf h)
  by_cases ba : ∀ x∈P, x∈B' → x∈A'
  · refine ⟨A',Or.inl rfl,?_,?_⟩
    · intro x hp hx
      exact hx.elim (ha.1 x hp) (fun t => ba x hp (hb.1 x hp t))
    · exact fun x hf h => Or.inl (ha.2 x hf h)
  push_neg at ab ba
  refine ⟨A'∪B',Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,ab,ba⟩))),?_,?_⟩
  · intro x hp hx
    exact hx.imp (ha.1 x hp) (hb.1 x hp)
  · intro x hf hx
    exact hx.imp (ha.2 x hf) (hb.2 x hf)

private theorem oneInter {P F A B A' B' : Set α}
    (ha : Improves P F A A') (hb : Improves P F B B') :
    ∃ V, Sharp P F A' B' V ∧ Improves P F (A∩B) V := by
  classical
  by_cases ab : ∀ x∈F, x∈A' → x∈B'
  · exact ⟨A',Or.inl rfl,fun x hp h => ha.1 x hp h.1,
      fun x hf h => ⟨ha.2 x hf h,hb.2 x hf (ab x hf h)⟩⟩
  by_cases ba : ∀ x∈F, x∈B' → x∈A'
  · exact ⟨B',Or.inr (Or.inl rfl),fun x hp h => hb.1 x hp h.2,
      fun x hf h => ⟨ha.2 x hf (ba x hf h),hb.2 x hf h⟩⟩
  push_neg at ab ba
  exact ⟨A'∩B',Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,ab,ba⟩))),
    fun x hp h => ⟨ha.1 x hp h.1,hb.1 x hp h.2⟩,
    fun x hf h => ⟨ha.2 x hf h.1,hb.2 x hf h.2⟩⟩

theorem normalize (W : Bank α) (n s : ℕ) (P F : Set α) (steps : Steps W n s) :
    ∃ D : Bank α, (∀ i<n,D i=W i) ∧ Clean P F D n s ∧
      ∀ w<n+s, Improves P F (W w) (D w) := by
  classical
  induction s with
  | zero =>
    exact ⟨W,fun _ _ => rfl,fun _ h => (Nat.not_lt_zero _ h).elim,
      fun w _ => reflImp P F (W w)⟩
  | succ s ih =>
    obtain ⟨D,raw,clean,imp⟩ := ih (fun j hj => steps j (Nat.lt_succ_of_lt hj))
    obtain ⟨a,ha,b,hb,eq⟩ := steps s (Nat.lt_succ_self s)
    have hv : ∃ V, Sharp P F (D a) (D b) V ∧ Improves P F (W (n+s)) V := by
      rcases eq with e|e|e|e <;> rw [e]
      · exact oneUnion (imp a ha) (imp b hb)
      · exact ⟨D a,Or.inl rfl,imp a ha⟩
      · exact ⟨∅,Or.inr (Or.inr (Or.inl rfl)),reflImp P F ∅⟩
      · exact oneInter (imp a ha) (imp b hb)
    obtain ⟨V,hV,iv⟩ := hv
    let E : Bank α := fun w => if w=n+s then V else D w
    have old (w : ℕ) (hw : w<n+s) : E w=D w := if_neg (Nat.ne_of_lt hw)
    have last : E (n+s)=V := if_pos rfl
    refine ⟨E,fun w hw => (old w (by omega)).trans (raw w hw),?_,?_⟩
    · intro j hj
      by_cases eq : j=s
      · subst j
        exact ⟨a,ha,b,hb,by simpa only [old a ha,old b hb,last] using hV⟩
      · have lt : j<s := by omega
        obtain ⟨u,hu,v,hv,h⟩ := clean j lt
        refine ⟨u,hu,v,hv,?_⟩
        rw [old u (by omega),old v (by omega),old (n+j) (by omega)]
        exact h
    · intro w hw
      by_cases e : w=n+s
      · subst w; rwa [last]
      · have lt : w<n+s := by omega
        rw [old w lt]
        exact imp w lt

theorem forget {P F : Set α} {D : Bank α} {n s : ℕ} (clean : Clean P F D n s) :
    Steps D n s := by
  intro j hj
  obtain ⟨a,ha,b,hb,h⟩ := clean j hj
  rcases h with e|e|e|⟨e,_⟩|⟨e,_⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inl e)⟩
  · exact ⟨b,hb,a,ha,Or.inr (Or.inl e)⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inl e))⟩
  · exact ⟨a,ha,b,hb,Or.inl e⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr e))⟩

end Normal

def Flags {N} (I : Fin N → Fin N → Prop) : Set (Board N) :=
  {z | ∃ p l, I p l ∧ z=(one p,one l)}
def Tests {N} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Set (Board N) :=
  {z | ∃ Y : Vec N, Fintype.card {l : Fin N // Y l=true}≤q ∧ z=negRow I Y}

def CleanVersion : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 Normal.Clean (Flags x3) (Tests x1 x3) x14 (x2+x2) x11 → (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → x1 % (2 : ℕ) = (0 : ℕ) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11

theorem clean_equiv : Posted ↔ CleanVersion := by
  rw [exact_equivalence]
  constructor
  · intro h q N I inst
    dsimp only
    intro hq hn cols geom s o D ho raw clean pos neg even
    exact h q N I hq hn cols geom s o D ho raw (Normal.forget clean) pos neg even
  · intro h q N I inst
    dsimp only
    intro hq hn cols geom s o W ho raw steps pos neg even
    obtain ⟨D,rd,cl,imp⟩ := Normal.normalize W (N+N) s (Flags I) (Tests q I) steps
    apply h q N I hq hn cols geom s o D ho _ cl _ _ even
    · intro i
      rw [rd i.val (by have hi := i.isLt; omega),rd (N+i.val) (by have hi := i.isLt; omega)]
      exact raw i
    · intro p l pl
      exact (imp o ho).1 _ ⟨p,l,pl,rfl⟩ (pos p l pl)
    · intro Y hy hh
      exact neg Y hy ((imp o ho).2 _ ⟨Y,hy,rfl⟩ hh)

end PEqualNP.Outside.L_meta_17257
