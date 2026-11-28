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

end PEqualNP.Outside.L_pcx_121_frontier
