import PEqualNP.Defs

namespace Research10009.SixTags
abbrev K := Fin 6
abbrev F := K → Bool
def Small (w : F) := ∃a b : K, ∀k : K,w k=true → k=a ∨ k=b
instance (w : F) : Decidable (Small w) := by unfold Small; infer_instance
def holes (w : F) (i : Fin 3) : K :=
  ((List.finRange 6).filter (fun k => !w k)).getD i.val 0
theorem counts : ∀w : F, Small w ∨ ∀k : K,w k=false → ∃i : Fin 3,holes w i=k := by decide +kernel
def tag (v : Fin 3 → Bool) : Fin 3 :=
  let n := (if v 0 then 1 else 0) + (if v 1 then 2 else 0) + (if v 2 then 4 else 0)
  (#[0,0,1,0,2,2,1,0] : Array (Fin 3))[n]!
theorem chain : ∀u v : Fin 3 → Bool,tag u=tag v →
    (∀i,u i=true → v i=true) ∨ (∀i,v i=true → u i=true) := by decide +kernel
def other (p : K) (i : Fin 4) : K :=
  if h : i.val<p.val then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
theorem different : ∀p : K,∀i : Fin 4,other p i≠p := by decide +kernel
theorem distinct : ∀p : K,∀i j : Fin 4,other p i=other p j → i=j := by decide +kernel
def Strong (W : K → F) := ∀p q r : K,p≠q → p≠r → ∃i : K,
    W p i=true ∧ W q i=false ∧ W r i=false

theorem low (W : K→F) (ok : Strong W) (p : K) : Small (W p) := by
  rcases counts (W p) with yes|few
  · exact yes
  · let cut (i : Fin 4) (k : Fin 3) := W (other p i) (holes (W p) k)
    let code (i : Fin 4) := tag (cut i)
    have inj : Function.Injective code := by
      intro i j eq
      by_contra bad
      have ne : other p i≠other p j := fun h => bad (distinct p i j h)
      have diff (a b : Fin 4) (hne : other p a≠other p b) :
          ¬∀k : Fin 3,cut a k=true → cut b k=true := by
        intro le
        obtain ⟨t,wa,wp,wb⟩ := ok (other p a) p (other p b) (different p a) hne
        obtain ⟨k,hk⟩ := few t wp
        have fa : cut a k=true := by simpa [cut,hk] using wa
        have fb : cut b k=false := by simpa [cut,hk] using wb
        exact Bool.noConfusion ((le k fa).symm.trans fb)
      rcases chain (cut i) (cut j) eq with d|d
      · exact diff i j ne d
      · exact diff j i ne.symm d
    have void := Fintype.card_le_of_injective code inj
    simp at void

theorem own (W : K→F) (ok : Strong W) (p : K) :
    ∃k : K,W p k=true ∧ ∀q : K,q≠p → W q k=false := by
  classical
  by_contra none
  have use (k : K) : ∃q : K,q≠p ∧ (W p k=true → W q k=true) := by
    by_cases h : W p k=true
    · by_contra bad
      apply none
      refine ⟨k,h,?_⟩
      intro q nq
      cases eq : W q k with
      | false => rfl
      | true => exact (bad ⟨q,nq,fun _ => eq⟩).elim
    · exact ⟨other p 0,different p 0,fun z => (h z).elim⟩
  obtain ⟨a,b,h⟩ := low W ok p
  obtain ⟨q,nq,cq⟩ := use a
  obtain ⟨r,nr,cr⟩ := use b
  obtain ⟨i,wi,wq,wr⟩ := ok p q r nq.symm nr.symm
  rcases h i wi with e|e
  · subst i
    exact Bool.noConfusion ((cq wi).symm.trans wq)
  · subst i
    exact Bool.noConfusion ((cr wi).symm.trans wr)

theorem permutation (W : K→F) (ok : Strong W) :
    ∃j : K→K,Function.Bijective j ∧ ∀p i,W p i=true ↔ i=j p := by
  classical
  choose j has uniq using own W ok
  have inj : Function.Injective j := by
    intro p q eq
    by_contra ne
    have no := uniq p q ne.symm
    rw [eq,has q] at no
    contradiction
  have sur := Finite.surjective_of_injective inj
  refine ⟨j,⟨inj,sur⟩,?_⟩
  intro p i
  constructor
  · intro yes
    obtain ⟨q,rfl⟩:=sur i
    by_contra ne
    have nq : p≠q := fun h => ne (h ▸ rfl)
    exact Bool.noConfusion (yes.symm.trans (uniq q p nq))
  · rintro rfl
    exact has p
end Research10009.SixTags
