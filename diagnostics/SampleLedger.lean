import PEqualNP.Defs
open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_178.SampleLedger

variable {V : Type} [DecidableEq V]
abbrev Bank (V : Type) := Set (LinClause V)
def Hits (T : Finset (LinClause V)) (a : V → Bool) := ∃ c ∈ T, ¬ LinClauseSat a c

variable {I : Type}

def Certified (pts : I→V→Bool) (F : Bank V) (b : Nat) (G : Bank V) : Prop :=
  ∀ T : Finset (LinClause V), (∀ c ∈ T, c ∈ G) →
    ∃ U : Finset (LinClause V), (∀ c ∈ U, c ∈ F) ∧
      U.card ≤ T.card+b ∧ ∀ i, Hits T (pts i) → Hits U (pts i)

theorem starting (pts : I→V→Bool) (F : Bank V) : Certified pts F 0 F := by
  intro T inc
  exact ⟨T,inc,by omega,fun _ x => x⟩

theorem add {pts : I→V→Bool} {F G : Bank V} {b k : Nat} {R : LinClause V}
    (old : Certified pts F b G) (parents : Finset (LinClause V))
    (known : ∀ c ∈ parents, c ∈ G) (fee : parents.card ≤ k+1)
    (sound : ∀ i, ¬ LinClauseSat (pts i) R → Hits parents (pts i)) :
    Certified pts F (b+k) (insert R G) := by
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

theorem resStep {pts : I→V→Bool} {F G : Bank V} {b : Nat} {C D R : LinClause V}
    (old : Certified pts F b G) (c : C ∈ G) (d : D ∈ G)
    (res : IsLinResolvent C D R) : Certified pts F (b+1) (insert R G) := by
  classical
  apply add old ({C,D} : Finset (LinClause V))
  · intro e h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> assumption
  · have h := Finset.card_insert_le C ({D} : Finset (LinClause V))
    simpa using h
  · intro a hr
    obtain ⟨f,_,_,eq⟩ := res
    have h := resolve_branch (pts a) eq hr
    split at h
    · exact ⟨C,by simp,h⟩
    · exact ⟨D,by simp,h⟩

theorem weakStep {pts : I→V→Bool} {F G : Bank V} {b : Nat} {C D : LinClause V}
    (old : Certified pts F b G) (c : C ∈ G)
    (w : ∀ i, LinClauseSat (pts i) C → LinClauseSat (pts i) D) : Certified pts F b (insert D G) := by
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


def Con {I : Type} (pts : I→V→Bool) (C R : LinClause V) : Prop :=
  ∀ i, LinClauseSat (pts i) C → LinClauseSat (pts i) R

inductive Ledger {I : Type} (pts : I→V→Bool) (F : Bank V) :
    Nat → List (LinClause V) → Prop
  | nil : Ledger pts F 0 []
  | ax {b π C} : Ledger pts F b π → C∈F → Ledger pts F b (C::π)
  | weak {b π C R} : Ledger pts F b π → C∈π → (∀a,LinClauseSat a C → LinClauseSat a R) →
      Ledger pts F b (R::π)
  | contract {b π C D R} : Ledger pts F b π → C∈π → D∈π → IsLinResolvent C D R →
      (Con pts C R ∨ Con pts D R) → Ledger pts F b (R::π)
  | charged {b π C D R} : Ledger pts F b π → C∈π → D∈π → IsLinResolvent C D R →
      ¬ (Con pts C R ∨ Con pts D R) → Ledger pts F (b+1) (R::π)

theorem ofDer {I : Type} (pts : I→V→Bool) {F : Bank V} {π} (h : IsLinDerivation F π) :
    ∃ b,Ledger pts F b π := by
  classical
  induction h with
  | nil => exact ⟨0,.nil⟩
  | ax _ mem ih =>
    obtain ⟨b,h⟩:=ih
    exact ⟨b,.ax h mem⟩
  | weak _ c w ih =>
    obtain ⟨b,h⟩:=ih
    exact ⟨b,.weak h c w⟩
  | @res π C D R _ c d rr ih =>
    obtain ⟨b,h⟩:=ih
    by_cases e : Con pts C R ∨ Con pts D R
    · exact ⟨b,.contract h c d rr e⟩
    · exact ⟨b+1,.charged h c d rr e⟩

theorem accounting {pts : I→V→Bool} {F : Bank V} {π b} (h : Ledger pts F b π) :
    Certified pts F b (available F π) := by
  induction h with
  | nil =>
    have e : available F [] = F := by ext c; simp [available]
    rw [e]
    exact starting pts F
  | @ax b π C _ mem ih =>
    rw [availCons,Set.insert_eq_of_mem (show C∈available F π from Or.inl mem)]
    exact ih
  | weak _ c w ih =>
    rw [availCons]
    exact weakStep ih (Or.inr c) (fun i => w (pts i))
  | contract _ c d _ tr ih =>
    rw [availCons]
    rcases tr with tr|tr
    · exact weakStep ih (Or.inr c) tr
    · exact weakStep ih (Or.inr d) tr
  | charged _ c d rr _ ih =>
    rw [availCons]
    exact resStep ih (Or.inr c) (Or.inr d) rr

theorem separated {n : Nat} {pts : Fin n→V→Bool} {F : Bank V} {π b}
    (h : Ledger pts F b π) (empty : (∅ : LinClause V) ∈ π)
    (unique : ∀ c∈F,∀ i j, ¬LinClauseSat (pts i) c → ¬LinClauseSat (pts j) c → i=j) :
    n ≤ b+1 := by
  classical
  have e : (∅ : LinClause V) ∈ available F π := Or.inr empty
  obtain ⟨U,ok,sz,cov⟩:=(accounting h) ({∅} : Finset (LinClause V)) (by simpa using e)
  have finds (i : Fin n) : ∃ c∈U, ¬LinClauseSat (pts i) c :=
    cov i ⟨∅,by simp,by simp [LinClauseSat]⟩
  choose c inc bad using finds
  let f (i : Fin n) : U := ⟨c i,inc i⟩
  have fi : Function.Injective f := by
    intro i j eq
    have same : c i=c j := congrArg Subtype.val eq
    exact unique _ (ok _ (inc i)) i j (bad i) (same.symm ▸ bad j)
  have count := Fintype.card_le_of_injective f fi
  simp at count sz
  omega
end PEqualNP.Outside.L_pcx_178.SampleLedger
