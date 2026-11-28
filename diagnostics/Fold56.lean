import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_frontier
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
abbrev LC (V : Type) := LinClause V
def holds (x : V → Bool) (S : Finset (LC V)) := ∀ c∈S,LinClauseSat x c
def avail (B : Finset (LC V)) (π : List (LC V)) (c : LC V) := c∈B ∨ c∈π

inductive Tail (B : Finset (LC V)) : Nat → List (LC V) → Prop where
| nil : Tail B 0 []
| step {k π c} (d : Tail B k π) (P : Finset (LC V))
    (earlier : ∀t∈P,avail B π t) (valid : ∀x, holds x P → LinClauseSat x c) :
    Tail B (k+(P.card-1)) (c::π)

theorem shrink {B : Finset (LC V)} {π k} (d : Tail B k π) :
    ∀ S : Finset (LC V), (∀c∈S,avail B π c) →
      ∃ T : Finset (LC V), T⊆B ∧ T.card≤S.card+k ∧ ∀x,holds x T → holds x S := by
  classical
  induction d with
  | nil =>
    intro S ok
    exact ⟨S,fun c hc=>(ok c hc).resolve_right (by simp),by simp,fun _ a=>a⟩
  | @step k π c d P earlier valid ih =>
    intro S ok
    have old {t} (h : t∈S) (ne : t≠c) : avail B π t := by
      rcases ok t h with hb|hl
      · exact Or.inl hb
      · exact Or.inr ((List.mem_cons.mp hl).resolve_left ne)
    by_cases hc : c∈S
    · let S' := S.erase c ∪ P
      have fit : ∀t∈S',avail B π t := by
        intro t ht
        rcases Finset.mem_union.mp ht with h|h
        · exact old (Finset.mem_of_mem_erase h) (Finset.mem_erase.mp h).1
        · exact earlier t h
      obtain ⟨T,sub,price,good⟩ := ih S' fit
      have un : S'.card ≤ (S.erase c).card + P.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_of_mem hc
      have pos := Finset.card_pos.mpr ⟨c,hc⟩
      refine ⟨T,sub,by omega,?_⟩
      intro x ht z hz
      have works := good x ht
      by_cases eq : z=c
      · subst z
        exact valid x (fun t hm=>works t (Finset.mem_union_right _ hm))
      · exact works z (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hz⟩))
    · obtain ⟨T,sub,price,good⟩:=ih S (fun t ht=>old ht (fun e=>hc (e ▸ ht)))
      exact ⟨T,sub,by omega,good⟩

theorem soundRes {x : V → Bool} {C D R : LC V} (p : IsLinResolvent C D R)
    (c : LinClauseSat x C) (d : LinClauseSat x D) : LinClauseSat x R := by
  obtain ⟨f,_,_,rfl⟩ := p
  obtain ⟨u,hu,su⟩ := c
  obtain ⟨v,hv,sv⟩ := d
  by_cases e : u = (f,false)
  · by_cases e' : v = (f,true)
    · subst u
      subst v
      have impossible : false = true := su.mp (sv.mpr rfl)
      contradiction
    · exact ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e',hv⟩),sv⟩
  · exact ⟨u,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hu⟩),su⟩

theorem fromPhysical {F : Set (LC V)} {B : Finset (LC V)} {base : List (LC V)}
    (raw : ∀c∈F,c∈B) (pre : ∀c∈base,c∈B) (suffix : List (LC V))
    (proof : IsLinDerivation F (suffix++base)) :
    ∃ k≤suffix.length, Tail B k suffix := by
  classical
  induction suffix with
  | nil => exact ⟨0,by simp,.nil⟩
  | cons c tail ih =>
    change IsLinDerivation F (c::(tail++base)) at proof
    have ready {q : LC V} (h : q∈tail++base) : avail B tail q := by
      rcases List.mem_append.mp h with a|b
      · exact Or.inr a
      · exact Or.inl (pre q b)
    cases proof with
    | ax d ax =>
      obtain ⟨k,h,tag⟩:=ih d
      have r := Tail.step (c:=c) tag {c}
        (by intro t ht; obtain rfl:=Finset.mem_singleton.mp ht; exact Or.inl (raw _ ax))
        (by intro x hs; exact hs _ (Finset.mem_singleton_self _))
      exact ⟨_,by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega, r⟩
    | weak d h w =>
      obtain ⟨k,hk,tag⟩:=ih d
      have r := Tail.step tag {_}
        (by intro t ht; obtain rfl:=Finset.mem_singleton.mp ht; exact ready h)
        (by intro x hs; exact w x (hs _ (Finset.mem_singleton_self _)))
      exact ⟨_,by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega, r⟩
    | @res _ lft rgt _ d h1 h2 step =>
      obtain ⟨k,hk,tag⟩:=ih d
      let P : Finset (LC V) := {lft,rgt}
      have pp : P.card ≤ 2 := by
        calc
          P.card ≤ ({rgt} : Finset (LC V)).card+1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      have r := Tail.step tag P
        (by intro t ht; rcases Finset.mem_insert.mp ht with rfl|ht
            · exact ready h1
            · obtain rfl:=Finset.mem_singleton.mp ht; exact ready h2)
        (by intro x hs; exact soundRes step (hs _ (by simp [P])) (hs _ (by simp [P])))
      exact ⟨_,by simp only [List.length_cons];omega,r⟩

theorem necessaryCover {F : Set (LC V)} {B : Finset (LC V)} {base suffix : List (LC V)}
    (raw : ∀c∈F,c∈B) (pre : ∀c∈base,c∈B)
    (d : IsLinDerivation F (suffix++base)) (empty : (∅ : LC V)∈suffix++base) :
    ∃T : Finset (LC V),T⊆B ∧ T.card≤suffix.length+1 ∧ ∀x,∃c∈T,¬LinClauseSat x c := by
  classical
  obtain ⟨k,price,tag⟩:=fromPhysical raw pre suffix d
  have a : avail B suffix (∅ : LC V) := by
    rcases List.mem_append.mp empty with h|h
    · exact Or.inr h
    · exact Or.inl (pre _ h)
  obtain ⟨T,sub,cnt,h⟩:=shrink tag {∅} (by intro c hc; obtain rfl:=Finset.mem_singleton.mp hc; exact a)
  refine ⟨T,sub,by simp only [Finset.card_singleton] at cnt;omega,?_⟩
  intro x
  by_contra! positive
  have no:=h x positive ∅ (Finset.mem_singleton_self _)
  simpa [LinClauseSat] using no


def plain (f : Finset V) (c : LC V) := ∀e∈c, e.1 ≠ f

theorem inherits {A D R : LC V} {f : Finset V} (h : IsLinResolvent A D R)
    (a : plain f A) (b : plain f D) : plain f R := by
  obtain ⟨_,_,_,rfl⟩ := h
  intro q mq
  rcases Finset.mem_union.mp mq with l|r
  · exact a _ (Finset.mem_of_mem_erase l)
  · exact b _ (Finset.mem_of_mem_erase r)
theorem priceTrack {F : Set (LC V)} {B : Finset (LC V)} {base : List (LC V)}
    (raw : ∀c∈F,c∈B) (pre : ∀c∈base,c∈B) {f : Finset V} (clean : ∀ c∈B, plain f c) (suffix : List (LC V))
    (proof : IsLinDerivation F (suffix++base)) :
    ∃ k≤suffix.length, Tail B k suffix ∧ (k<suffix.length ∨ ∀c∈suffix, plain f c) := by
  classical
  induction suffix with
  | nil => exact ⟨0,by simp,.nil,Or.inr (by simp)⟩
  | cons c tail ih =>
    change IsLinDerivation F (c::(tail++base)) at proof
    have ready {q : LC V} (h : q∈tail++base) : avail B tail q := by
      rcases List.mem_append.mp h with a|b
      · exact Or.inr a
      · exact Or.inl (pre q b)
    cases proof with
    | ax d ax =>
      obtain ⟨k,h,tag,_⟩:=ih d
      have r := Tail.step (c:=c) tag {c}
        (by intro t ht; obtain rfl:=Finset.mem_singleton.mp ht; exact Or.inl (raw _ ax))
        (by intro x hs; exact hs _ (Finset.mem_singleton_self _))
      exact ⟨_,by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega, r,Or.inl (by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega)⟩
    | weak d h w =>
      obtain ⟨k,hk,tag,_⟩:=ih d
      have r := Tail.step tag {_}
        (by intro t ht; obtain rfl:=Finset.mem_singleton.mp ht; exact ready h)
        (by intro x hs; exact w x (hs _ (Finset.mem_singleton_self _)))
      exact ⟨_,by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega, r,Or.inl (by simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero,List.length_cons];omega)⟩
    | @res _ lft rgt _ d h1 h2 step =>
      obtain ⟨k,hk,tag,extra⟩:=ih d
      let P : Finset (LC V) := {lft,rgt}
      have pp : P.card ≤ 2 := by
        calc
          P.card ≤ ({rgt} : Finset (LC V)).card+1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      have r := Tail.step tag P
        (by intro t ht; rcases Finset.mem_insert.mp ht with rfl|ht
            · exact ready h1
            · obtain rfl:=Finset.mem_singleton.mp ht; exact ready h2)
        (by intro x hs; exact soundRes step (hs _ (by simp [P])) (hs _ (by simp [P])))
      refine ⟨_,by simp only [List.length_cons];omega,r,?_⟩
      rcases extra with strict|old
      · exact Or.inl (by simp only [List.length_cons];omega)
      · apply Or.inr
        have prior {q : LC V} (m : q∈tail++base) : plain f q := by
          rcases List.mem_append.mp m with l|l
          · exact old _ l
          · exact clean _ (pre _ l)
        intro c mc
        rcases List.mem_cons.mp mc with rfl|before
        · exact inherits step (prior h1) (prior h2)
        · exact old _ before
def privateLabels (B : Finset (LC V)) (R : LC V) :=
  ∀ c∈B, ∃x, ¬LinClauseSat x R ∧ ∀t∈B,t≠c → LinClauseSat x t

theorem exclusive {B T : Finset (LC V)} {R : LC V} (has : privateLabels B R)
    (sub : T⊆B) (entails : ∀x, holds x T → LinClauseSat x R) : T=B := by
  apply Finset.Subset.antisymm sub
  intro c mc
  by_contra lost
  obtain ⟨x,off,on⟩ := has c mc
  exact off (entails x (fun t mt => on t (sub mt) (fun eq=>lost (eq ▸ mt))))

theorem firstExotic {F : Set (LC V)} {B : Finset (LC V)} {base suffix : List (LC V)}
    (raw : ∀c∈F,c∈B) (pre : ∀c∈base,c∈B)
    {f : Finset V} (clean : ∀c∈B, plain f c)
    (proof : IsLinDerivation F (suffix++base)) {R : LC V}
    (mem : R∈suffix++base) (exotic : ¬plain f R) (has : privateLabels B R) :
    B.card≤suffix.length := by
  classical
  have sr : R∈suffix := (List.mem_append.mp mem).resolve_right (fun m=>exotic (clean _ (pre _ m)))
  obtain ⟨k,_,tag,ex⟩ := priceTrack raw pre clean suffix proof
  have lt := ex.resolve_right (fun h=>exotic (h R sr))
  obtain ⟨T,sub,cnt,works⟩ := shrink tag {R} (by
    intro c hc
    obtain rfl := Finset.mem_singleton.mp hc
    exact Or.inr sr)
  have teq := exclusive has sub (fun x a=>works x a R (Finset.mem_singleton_self _))
  rw [teq] at cnt
  simp only [Finset.card_singleton] at cnt
  omega

theorem dropLegal {F : Set (LC V)} {base : List (LC V)} (xs : List (LC V)) (t : Nat)
    (d : IsLinDerivation F (xs++base)) : IsLinDerivation F ((xs.drop t)++base) := by
  induction xs generalizing t with
  | nil => simpa using d
  | cons h xs ih =>
    cases t with
    | zero => simpa using d
    | succ t =>
      change IsLinDerivation F (h::(xs++base)) at d
      have earlier : IsLinDerivation F (xs++base) := by cases d <;> assumption
      simpa using ih t earlier

theorem manyPrices {F : Set (LC V)} {base xs : List (LC V)} (d : IsLinDerivation F (xs++base))
    {K : Finset (LC V)} {n : Nat} (pos : 0<n) (nonempty : K.Nonempty)
    (has : ∀ c∈K,c∈xs++base)
    (price : ∀ ys : List (LC V), IsLinDerivation F (ys++base) → ∀c∈K,c∈ys++base → n≤ys.length) :
    n+K.card≤xs.length+1 := by
  classical
  obtain ⟨c,mc⟩ := nonempty
  have nle := price xs d c mc (has c mc)
  let takeN := xs.length+1-n
  have small : (xs.drop takeN).length<n := by simp [takeN];omega
  have sub : K ⊆ (xs.take takeN).toFinset := by
    intro t mt
    apply List.mem_toFinset.mpr
    by_contra absent
    have other : t∈(xs.drop takeN)++base := by
      have split : xs++base = xs.take takeN ++ (xs.drop takeN ++ base) := by
        rw [←List.append_assoc, List.take_append_drop]
      have z := has t mt
      rw [split] at z
      exact (List.mem_append.mp z).resolve_left absent
    have conflict := price _ (dropLegal xs takeN d) t mt other
    omega
  have size := Finset.card_le_card sub
  have size' := List.toFinset_card_le (l:=xs.take takeN)
  have lim : (xs.take takeN).length≤takeN := by simp
  dsimp [takeN] at *
  omega

abbrev VV := Fin 4 × Fin 3
abbrev Row := LC VV
def assignment (n : Nat) (v : VV) := n.testBit (3*v.1.val+v.2.val)
instance judgeEq (x : VV → Bool) (q : LinEq VV) : Decidable (LinEqSat x q) :=
  inferInstanceAs (Decidable (Odd (q.1.filter (fun v=>x v=true)).card ↔ q.2=true))
instance judgeClause (x : VV → Bool) (c : Row) : Decidable (LinClauseSat x c) :=
  inferInstanceAs (Decidable (∃q∈c, LinEqSat x q))
instance judgeHolds (x : VV → Bool) (B : Finset Row) : Decidable (holds x B) :=
  inferInstanceAs (Decidable (∀q∈B, LinClauseSat x q))
instance judgePlain (f : Finset VV) (C : Row) : Decidable (plain f C) :=
  inferInstanceAs (Decidable (∀q∈C, q.1≠f))
def LocallyBuilds (B K : Finset Row) (xs : List Row) : Prop :=
  ∃ base : List Row, (∀c∈base,c∈B) ∧
    IsLinDerivation (↑B : Set Row) (xs++base) ∧ ∀c∈K, c∈xs++base

theorem localPrice {B K : Finset Row} {xs : List Row} (d : LocallyBuilds B K xs)
    (nonempty : K.Nonempty) (positive : 0<B.card)
    (cost : ∀c∈K, privateLabels B c ∧ ∃ f, (∀b∈B,plain f b) ∧ ¬plain f c) :
    B.card+K.card≤xs.length+1 := by
  obtain ⟨base,pre,legal,has⟩ := d
  apply manyPrices legal positive nonempty has
  intro ys localD c cm member
  obtain ⟨priv,f,clean,novel⟩ := cost c cm
  exact firstExotic (fun _ h=>h) pre clean localD member novel priv
def row0 : Row := ({(({(0, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true)} : Row)
def row1 : Row := ({(({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 2)} : Finset VV), true)} : Row)
def row2 : Row := ({(({(0, 0)} : Finset VV), false), (({(1, 0)} : Finset VV), false)} : Row)
def row3 : Row := ({(({(0, 1)} : Finset VV), false), (({(1, 1)} : Finset VV), false)} : Row)
def row4 : Row := ({(({(0, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), false)} : Row)
def row5 : Row := ({(({(2, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), true)} : Row)
def row6 : Row := ({(({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : Row)
def row7 : Row := ({(({(2, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : Row)
def row8 : Row := ({(({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : Row)
def row9 : Row := ({(({(2, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : Row)
def row10 : Row := ({(({(0, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : Row)
def row11 : Row := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : Row)
def row12 : Row := ({(({(1, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : Row)
def row13 : Row := ({(({(1, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : Row)
def row14 : Row := ({(({(0, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false)} : Row)
def row15 : Row := ({(({(0, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : Row)
def row16 : Row := ({(({(1, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false)} : Row)
def row17 : Row := ({(({(1, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : Row)
def row18 : Row := ({(({(0, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), false)} : Row)
def row19 : Row := ({(({(0, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : Row)
def row20 : Row := ({(({(1, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), false)} : Row)
def row21 : Row := ({(({(1, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : Row)
def row22 : Row := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 1), (1, 1)} : Finset VV), true)} : Row)
def row23 : Row := ({(({(0, 0), (1, 0)} : Finset VV), true), (({(0, 2), (1, 2)} : Finset VV), true)} : Row)
def row24 : Row := ({(({(0, 1), (1, 1)} : Finset VV), true), (({(0, 2), (1, 2)} : Finset VV), true)} : Row)
def row25 : Row := ({(({(2, 0), (3, 0)} : Finset VV), true), (({(2, 1), (3, 1)} : Finset VV), true)} : Row)
def row26 : Row := ({(({(2, 0), (3, 0)} : Finset VV), true), (({(2, 2), (3, 2)} : Finset VV), true)} : Row)
def row27 : Row := ({(({(2, 1), (3, 1)} : Finset VV), true), (({(2, 2), (3, 2)} : Finset VV), true)} : Row)
def row28 : Row := ({(({(0, 0), (1, 0)} : Finset VV), false), (({(2, 0), (3, 0)} : Finset VV), false)} : Row)
def row29 : Row := ({(({(0, 1), (1, 1)} : Finset VV), false), (({(2, 1), (3, 1)} : Finset VV), false)} : Row)
def row30 : Row := ({(({(0, 2), (1, 2)} : Finset VV), false), (({(2, 2), (3, 2)} : Finset VV), false)} : Row)
def row31 : Row := (∅ : Row)
def b0 := ({row0,row1,row2,row3,row4} : Finset Row)
def k0 := ({row22,row23,row24} : Finset Row)
theorem priv0x0 : privateLabels b0 row22 := by
  intro m hm
  simp only [b0,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 32,by decide +kernel,?_⟩
    have ok : holds (assignment 32) (b0.erase row0) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 4,by decide +kernel,?_⟩
    have ok : holds (assignment 4) (b0.erase row1) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 9,by decide +kernel,?_⟩
    have ok : holds (assignment 9) (b0.erase row2) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 18,by decide +kernel,?_⟩
    have ok : holds (assignment 18) (b0.erase row3) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 36,by decide +kernel,?_⟩
    have ok : holds (assignment 36) (b0.erase row4) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem priv0x1 : privateLabels b0 row23 := by
  intro m hm
  simp only [b0,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 16,by decide +kernel,?_⟩
    have ok : holds (assignment 16) (b0.erase row0) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2,by decide +kernel,?_⟩
    have ok : holds (assignment 2) (b0.erase row1) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 9,by decide +kernel,?_⟩
    have ok : holds (assignment 9) (b0.erase row2) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 18,by decide +kernel,?_⟩
    have ok : holds (assignment 18) (b0.erase row3) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 36,by decide +kernel,?_⟩
    have ok : holds (assignment 36) (b0.erase row4) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem priv0x2 : privateLabels b0 row24 := by
  intro m hm
  simp only [b0,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 8,by decide +kernel,?_⟩
    have ok : holds (assignment 8) (b0.erase row0) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1,by decide +kernel,?_⟩
    have ok : holds (assignment 1) (b0.erase row1) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 9,by decide +kernel,?_⟩
    have ok : holds (assignment 9) (b0.erase row2) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 18,by decide +kernel,?_⟩
    have ok : holds (assignment 18) (b0.erase row3) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 36,by decide +kernel,?_⟩
    have ok : holds (assignment 36) (b0.erase row4) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem price0 {xs : List Row} (localD : LocallyBuilds b0 k0 xs) : 7≤xs.length := by
  have p := localPrice localD (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [k0,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨priv0x0,({(0, 0), (1, 0)} : Finset VV),by decide +kernel,by decide +kernel⟩
    · exact ⟨priv0x1,({(0, 0), (1, 0)} : Finset VV),by decide +kernel,by decide +kernel⟩
    · exact ⟨priv0x2,({(0, 1), (1, 1)} : Finset VV),by decide +kernel,by decide +kernel⟩
    )
  have cb : b0.card=5 := by decide +kernel
  have ck : k0.card=3 := by decide +kernel
  omega
def b1 := ({row5,row6,row7,row8,row9} : Finset Row)
def k1 := ({row25,row26,row27} : Finset Row)
theorem priv1x0 : privateLabels b1 row25 := by
  intro m hm
  simp only [b1,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 2048,by decide +kernel,?_⟩
    have ok : holds (assignment 2048) (b1.erase row5) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 256,by decide +kernel,?_⟩
    have ok : holds (assignment 256) (b1.erase row6) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 576,by decide +kernel,?_⟩
    have ok : holds (assignment 576) (b1.erase row7) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1152,by decide +kernel,?_⟩
    have ok : holds (assignment 1152) (b1.erase row8) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2304,by decide +kernel,?_⟩
    have ok : holds (assignment 2304) (b1.erase row9) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem priv1x1 : privateLabels b1 row26 := by
  intro m hm
  simp only [b1,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 1024,by decide +kernel,?_⟩
    have ok : holds (assignment 1024) (b1.erase row5) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 128,by decide +kernel,?_⟩
    have ok : holds (assignment 128) (b1.erase row6) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 576,by decide +kernel,?_⟩
    have ok : holds (assignment 576) (b1.erase row7) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1152,by decide +kernel,?_⟩
    have ok : holds (assignment 1152) (b1.erase row8) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2304,by decide +kernel,?_⟩
    have ok : holds (assignment 2304) (b1.erase row9) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem priv1x2 : privateLabels b1 row27 := by
  intro m hm
  simp only [b1,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 512,by decide +kernel,?_⟩
    have ok : holds (assignment 512) (b1.erase row5) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 64,by decide +kernel,?_⟩
    have ok : holds (assignment 64) (b1.erase row6) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 576,by decide +kernel,?_⟩
    have ok : holds (assignment 576) (b1.erase row7) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1152,by decide +kernel,?_⟩
    have ok : holds (assignment 1152) (b1.erase row8) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2304,by decide +kernel,?_⟩
    have ok : holds (assignment 2304) (b1.erase row9) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem price1 {xs : List Row} (localD : LocallyBuilds b1 k1 xs) : 7≤xs.length := by
  have p := localPrice localD (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [k1,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨priv1x0,({(2, 0), (3, 0)} : Finset VV),by decide +kernel,by decide +kernel⟩
    · exact ⟨priv1x1,({(2, 0), (3, 0)} : Finset VV),by decide +kernel,by decide +kernel⟩
    · exact ⟨priv1x2,({(2, 1), (3, 1)} : Finset VV),by decide +kernel,by decide +kernel⟩
    )
  have cb : b1.card=5 := by decide +kernel
  have ck : k1.card=3 := by decide +kernel
  omega
def b2 := ({row10,row11,row12,row13} : Finset Row)
def k2 := ({row28} : Finset Row)
theorem priv2x0 : privateLabels b2 row28 := by
  intro m hm
  simp only [b2,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl
  · refine ⟨assignment 65,by decide +kernel,?_⟩
    have ok : holds (assignment 65) (b2.erase row10) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 513,by decide +kernel,?_⟩
    have ok : holds (assignment 513) (b2.erase row11) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 72,by decide +kernel,?_⟩
    have ok : holds (assignment 72) (b2.erase row12) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 520,by decide +kernel,?_⟩
    have ok : holds (assignment 520) (b2.erase row13) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem price2 {xs : List Row} (localD : LocallyBuilds b2 k2 xs) : 4≤xs.length := by
  have p := localPrice localD (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [k2,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl
    · exact ⟨priv2x0,({(0, 0), (1, 0)} : Finset VV),by decide +kernel,by decide +kernel⟩
    )
  have cb : b2.card=4 := by decide +kernel
  have ck : k2.card=1 := by decide +kernel
  omega
def b3 := ({row14,row15,row16,row17} : Finset Row)
def k3 := ({row29} : Finset Row)
theorem priv3x0 : privateLabels b3 row29 := by
  intro m hm
  simp only [b3,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl
  · refine ⟨assignment 130,by decide +kernel,?_⟩
    have ok : holds (assignment 130) (b3.erase row14) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1026,by decide +kernel,?_⟩
    have ok : holds (assignment 1026) (b3.erase row15) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 144,by decide +kernel,?_⟩
    have ok : holds (assignment 144) (b3.erase row16) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 1040,by decide +kernel,?_⟩
    have ok : holds (assignment 1040) (b3.erase row17) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem price3 {xs : List Row} (localD : LocallyBuilds b3 k3 xs) : 4≤xs.length := by
  have p := localPrice localD (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [k3,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl
    · exact ⟨priv3x0,({(0, 1), (1, 1)} : Finset VV),by decide +kernel,by decide +kernel⟩
    )
  have cb : b3.card=4 := by decide +kernel
  have ck : k3.card=1 := by decide +kernel
  omega
def b4 := ({row18,row19,row20,row21} : Finset Row)
def k4 := ({row30} : Finset Row)
theorem priv4x0 : privateLabels b4 row30 := by
  intro m hm
  simp only [b4,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl
  · refine ⟨assignment 260,by decide +kernel,?_⟩
    have ok : holds (assignment 260) (b4.erase row18) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2052,by decide +kernel,?_⟩
    have ok : holds (assignment 2052) (b4.erase row19) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 288,by decide +kernel,?_⟩
    have ok : holds (assignment 288) (b4.erase row20) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 2080,by decide +kernel,?_⟩
    have ok : holds (assignment 2080) (b4.erase row21) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
theorem price4 {xs : List Row} (localD : LocallyBuilds b4 k4 xs) : 4≤xs.length := by
  have p := localPrice localD (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [k4,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl
    · exact ⟨priv4x0,({(0, 2), (1, 2)} : Finset VV),by decide +kernel,by decide +kernel⟩
    )
  have cb : b4.card=4 := by decide +kernel
  have ck : k4.card=1 := by decide +kernel
  omega
def b5 := ({row22,row23,row24,row25,row26,row27,row28,row29,row30} : Finset Row)
def k5 := ({row31} : Finset Row)
theorem priv5x0 : privateLabels b5 row31 := by
  intro m hm
  simp only [b5,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨assignment 196,by decide +kernel,?_⟩
    have ok : holds (assignment 196) (b5.erase row22) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 322,by decide +kernel,?_⟩
    have ok : holds (assignment 322) (b5.erase row23) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 385,by decide +kernel,?_⟩
    have ok : holds (assignment 385) (b5.erase row24) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 259,by decide +kernel,?_⟩
    have ok : holds (assignment 259) (b5.erase row25) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 133,by decide +kernel,?_⟩
    have ok : holds (assignment 133) (b5.erase row26) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 70,by decide +kernel,?_⟩
    have ok : holds (assignment 70) (b5.erase row27) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 197,by decide +kernel,?_⟩
    have ok : holds (assignment 197) (b5.erase row28) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 198,by decide +kernel,?_⟩
    have ok : holds (assignment 198) (b5.erase row29) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)
  · refine ⟨assignment 326,by decide +kernel,?_⟩
    have ok : holds (assignment 326) (b5.erase row30) := by decide +kernel
    exact fun t mt ne=>ok t (Finset.mem_erase.mpr ⟨ne,mt⟩)

theorem price5 {xs : List Row} (localD : LocallyBuilds b5 k5 xs) : 8≤xs.length := by
  obtain ⟨base,pre,d,has⟩ := localD
  have empty : (∅ : Row)∈xs++base := has ∅ (by decide +kernel)
  obtain ⟨T,sub,size,cover⟩ := necessaryCover (fun _ h=>h) pre d empty
  have same : T=b5 := exclusive priv5x0 sub (by
    intro x good
    obtain ⟨c,m,off⟩ := cover x
    exact False.elim (off (good c m)))
  have card : b5.card=9 := by decide +kernel
  rw [same,card] at size
  omega

theorem collapsedBank56 {a b c d e t : List Row}
    (h0 : LocallyBuilds b0 k0 a) (h1 : LocallyBuilds b1 k1 b)
    (h2 : LocallyBuilds b2 k2 c) (h3 : LocallyBuilds b3 k3 d)
    (h4 : LocallyBuilds b4 k4 e) (ht : LocallyBuilds b5 k5 t) :
    56≤22+a.length+b.length+c.length+d.length+e.length+t.length := by
  have := price0 h0
  have := price1 h1
  have := price2 h2
  have := price3 h3
  have := price4 h4
  have := price5 ht
  omega
end PEqualNP.Outside.L_pcx_121_frontier
