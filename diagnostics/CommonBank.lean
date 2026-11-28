import PEqualNP.Defs
open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_178.CommonBank

variable {V : Type} [DecidableEq V]
abbrev Bank (V : Type) := Set (LinClause V)
def Hits (T : Finset (LinClause V)) (a : V → Bool) := ∃ c ∈ T, ¬ LinClauseSat a c

def Certified (F : Bank V) (b : Nat) (G : Bank V) : Prop :=
  ∀ T : Finset (LinClause V), (∀ c ∈ T, c ∈ G) →
    ∃ U : Finset (LinClause V), (∀ c ∈ U, c ∈ F) ∧
      U.card ≤ T.card+b ∧ ∀ a, Hits T a → Hits U a

theorem starting (F : Bank V) : Certified F 0 F := by
  intro T inc
  exact ⟨T,inc,by omega,fun _ x => x⟩

theorem add {F G : Bank V} {b k : Nat} {R : LinClause V}
    (old : Certified F b G) (parents : Finset (LinClause V))
    (known : ∀ c ∈ parents, c ∈ G) (fee : parents.card ≤ k+1)
    (sound : ∀ a, ¬ LinClauseSat a R → Hits parents a) :
    Certified F (b+k) (insert R G) := by
  classical
  intro T inc
  by_cases hr : R ∈ T
  · let S := (T.erase R) ∪ parents
    have sub : ∀ c ∈ S, c ∈ G := by
      intro c hc
      rcases Finset.mem_union.mp hc with h | h
      · have e := Finset.mem_erase.mp h
        exact (Set.mem_insert_iff.mp (inc c e.2)).resolve_left e.1
      · exact known c h
    obtain ⟨U,uf,sz,covers⟩ := old S sub
    refine ⟨U,uf,?_,?_⟩
    · have ub := Finset.card_union_le (T.erase R) parents
      have er := Finset.card_erase_of_mem hr
      change U.card ≤ ((T.erase R) ∪ parents).card+b at sz
      have pos := Finset.card_pos.mpr ⟨R,hr⟩
      omega
    · intro a h
      apply covers a
      obtain ⟨c,ct,bad⟩ := h
      by_cases eq : c=R
      · subst c
        obtain ⟨d,dp,df⟩ := sound a bad
        exact ⟨d,Finset.mem_union_right _ dp,df⟩
      · exact ⟨c,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ct⟩),bad⟩
  · have sub : ∀ c ∈ T, c ∈ G := by
      intro c ct
      rcases Set.mem_insert_iff.mp (inc c ct) with rfl | h
      · contradiction
      · exact h
    obtain ⟨U,uf,sz,cover⟩ := old T sub
    exact ⟨U,uf,by omega,cover⟩

theorem resolve_branch {V : Type} [DecidableEq V] {D H R : LinClause V}
    (a : V → Bool) {f : Finset V}
    (rr : R = D.erase (f, false) ∪ H.erase (f, true))
    (fr : ¬ LinClauseSat a R) :
    if Odd (f.filter (fun x => a x = true)).card
    then ¬ LinClauseSat a D else ¬ LinClauseSat a H := by
  subst R
  by_cases h : Odd (f.filter (fun x => a x = true)).card
  · rw [ite_eq_left h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat
  · rw [ite_eq_right h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat

theorem resStep {F G : Bank V} {b : Nat} {C D R : LinClause V}
    (old : Certified F b G) (c : C ∈ G) (d : D ∈ G)
    (res : IsLinResolvent C D R) : Certified F (b+1) (insert R G) := by
  classical
  apply add old ({C,D} : Finset (LinClause V))
  · intro e h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> assumption
  · have h := Finset.card_insert_le C ({D} : Finset (LinClause V))
    simpa using h
  · intro a hr
    obtain ⟨f,_,_,eq⟩ := res
    have h := resolve_branch a eq hr
    split at h
    · exact ⟨C,by simp,h⟩
    · exact ⟨D,by simp,h⟩

theorem weakStep {F G : Bank V} {b : Nat} {C D : LinClause V}
    (old : Certified F b G) (c : C ∈ G)
    (w : ∀ a, LinClauseSat a C → LinClauseSat a D) : Certified F b (insert D G) := by
  apply add (k:=0) old ({C} : Finset (LinClause V))
  · intro e h
    simpa [Finset.mem_singleton.mp h] using c
  · simp
  · intro a h
    exact ⟨C,by simp,fun s => h (w a s)⟩

def available (F : Bank V) (π : List (LinClause V)) : Bank V := {c | c∈F ∨ c∈π}
theorem availCons (F : Bank V) (C : LinClause V) (π : List (LinClause V)) :
    available F (C::π) = insert C (available F π) := by
  ext d
  simp [available,or_left_comm,or_assoc]

theorem physicalSuffix (F : Bank V) (π s : List (LinClause V))
    (h : IsLinDerivation F (s++π)) :
    ∃ b ≤ s.length, Certified (available F π) b (available F (s++π)) := by
  induction s with
  | nil => exact ⟨0,by simp,starting _⟩
  | cons R t ih =>
    have h' : IsLinDerivation F (R::(t++π)) := h
    change ∃ b ≤ (R::t).length, Certified (available F π) b (available F (R::(t++π)))
    rw [availCons]
    cases h' with
    | ax prev ax =>
      obtain ⟨b,le,old⟩ := ih prev
      have en : R ∈ available F (t++π) := Or.inl ax
      rw [Set.insert_eq_of_mem en]
      exact ⟨b,by simp; omega,old⟩
    | res prev cl dl rr =>
      obtain ⟨b,le,old⟩ := ih prev
      exact ⟨b+1,by simpa using le,resStep old (Or.inr cl) (Or.inr dl) rr⟩
    | weak prev cl w =>
      obtain ⟨b,le,old⟩ := ih prev
      exact ⟨b,by simp; omega,weakStep old (Or.inr cl) w⟩

theorem emptyCore {F G : Bank V} {b : Nat} (h : Certified F b G) (e : ∅ ∈ G) :
    ∃ U : Finset (LinClause V), (∀ c ∈ U,c ∈ F) ∧ U.card ≤ b+1 ∧
      ∀ a,Hits U a := by
  obtain ⟨U,ok,sz,cov⟩:=h ({∅} : Finset (LinClause V)) (by simpa using e)
  refine ⟨U,ok,by simpa [Nat.add_comm] using sz,?_⟩
  intro a
  exact cov a ⟨∅,by simp,by simp [LinClauseSat]⟩

end PEqualNP.Outside.L_pcx_178.CommonBank
