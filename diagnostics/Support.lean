import Mathlib
namespace Support238
open Polynomial
variable {K : Type*} [Field K]

theorem splitMul {p q : K[X]} {k : ℕ} (hm : k∈(p*q).support) :
    ∃a∈p.support,∃b∈q.support,a+b=k := by
  classical
  have h := Polynomial.mem_support_iff.mp hm
  rw [coeff_mul] at h
  obtain ⟨⟨a,b⟩,hab,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨a,Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hv),
    b,Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hv),Finset.mem_antidiagonal.mp hab⟩

theorem label (S : Finset ℕ) (small : S.card≤4) :
    ∃ f : Fin 4 → ℕ,∀a∈S,∃i,f i=a := by
  classical
  let e := Fintype.equivFin S
  let idx (a : S) : Fin 4 := ⟨(e a).val,lt_of_lt_of_le (e a).isLt (by simpa using small)⟩
  let pick (i : Fin 4) : ℕ := if h : ∃a:S,idx a=i then (Classical.choose h).val else 0
  refine ⟨pick,?_⟩
  intro a ha
  let v : S := ⟨a,ha⟩
  have z : ∃u:S,idx u=idx v := ⟨v,rfl⟩
  refine ⟨idx v,?_⟩
  change (if h : ∃u:S,idx u=idx v then (Classical.choose h).val else 0)=a
  rw [dif_pos z]
  have same : Classical.choose z=v := e.injective (Fin.ext (congrArg Fin.val (Classical.choose_spec z)))
  exact congrArg Subtype.val same

def triples : Finset (Fin 4 × Fin 4 × Fin 4) := Finset.univ.filter (fun t => t.1≤t.2.1 ∧ t.2.1≤t.2.2)
theorem number : triples.card=20 := by decide +kernel

theorem ordered (f : Fin 4 → ℕ) (i j k : Fin 4) :
    ∃t∈triples, f t.1+f t.2.1+f t.2.2=f i+f j+f k := by
  have pick (a b c : Fin 4) (ab : a≤b) (bc : b≤c)
      (eqn : f a+f b+f c=f i+f j+f k) : ∃t∈triples,f t.1+f t.2.1+f t.2.2=f i+f j+f k :=
    ⟨(a,b,c),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc⟩,eqn⟩
  rcases le_total i j with ij|ji
  · rcases le_total j k with jk|kj
    · exact pick i j k ij jk rfl
    · rcases le_total i k with ik|ki
      · exact pick i k j ik kj (by omega)
      · exact pick k i j ki ij (by omega)
  · rcases le_total i k with ik|ki
    · exact pick j i k ji ik (by omega)
    · rcases le_total j k with jk|kj
      · exact pick j k i jk ki (by omega)
      · exact pick k j i kj ji (by omega)

theorem cube (p : K[X]) (small : p.support.card≤4) : (p^3).support.card≤20 := by
  classical
  obtain ⟨f,repr⟩ := label p.support small
  let total (t : Fin 4 × Fin 4 × Fin 4) := f t.1+f t.2.1+f t.2.2
  have sub : (p^3).support ⊆ triples.image total := by
    intro k hk
    have eqn : p^3=(p*p)*p := by ring
    rw [eqn] at hk
    obtain ⟨u,hu,c,hc,e⟩ := splitMul hk
    obtain ⟨a,ha,b,hb,ab⟩ := splitMul hu
    obtain ⟨i,hi⟩ := repr a ha
    obtain ⟨j,hj⟩ := repr b hb
    obtain ⟨l,hl⟩ := repr c hc
    obtain ⟨t,ht,ts⟩ := ordered f i j l
    exact Finset.mem_image.mpr ⟨t,ht,by change f t.1+f t.2.1+f t.2.2=k; omega⟩
  have bound := (Finset.card_le_card sub).trans Finset.card_image_le
  simpa [number] using bound

theorem constantMul (s : K) (p : K[X]) : (C s*p).support⊆p.support := by
  intro j hj
  apply Polynomial.mem_support_iff.mpr
  have h := Polynomial.mem_support_iff.mp hj
  rw [coeff_C_mul] at h
  exact right_ne_zero_of_mul h

theorem terms (s : Fin 3 → K) (g : Fin 3 → K[X]) (small : ∀i,(g i).support.card≤4) :
    (∑i,C (s i)*g i^3).support.card≤60 := by
  classical
  let S (i : Fin 3) := (g i^3).support
  have sub : (∑ i,C (s i)*g i^3).support⊆Finset.univ.biUnion S := by
    intro j hj
    have h := Polynomial.mem_support_iff.mp hj
    rw [finset_sum_coeff] at h
    obtain ⟨i,hi,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Finset.mem_biUnion.mpr ⟨i,hi,constantMul _ _ (Polynomial.mem_support_iff.mpr hc)⟩
  calc
    _ ≤ (Finset.univ.biUnion S).card := Finset.card_le_card sub
    _ ≤ ∑i, (S i).card := Finset.card_biUnion_le
    _ ≤ ∑_i : Fin 3,20 := Finset.sum_le_sum (fun i _ => cube _ (small i))
    _ = 60 := by decide

end Support238
