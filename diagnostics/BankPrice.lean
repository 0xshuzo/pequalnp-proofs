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
end PEqualNP.Outside.L_pcx_121_frontier
