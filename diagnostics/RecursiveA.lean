import Mathlib.Combinatorics.Hall.Basic
import PEqualNP.Defs

namespace BlockQuotaRouting
open Finset

theorem switches {A : Type} [Fintype A] [DecidableEq A]
    (E : Equiv.Perm (A × Bool)) :
    ∃ (left right : A → Bool) (p q : Equiv.Perm A),
      (∀ i, E (i,left i) = (p i,right (p i))) ∧
      (∀ i, E (i,!(left i)) = (q i,!(right (q i)))) := by
  classical
  let adj (i : A) := ({(E (i,false)).1, (E (i,true)).1} : Finset A)
  have hall (S : Finset A) : S.card ≤ (S.biUnion adj).card := by
    let U := (S ×ˢ (univ : Finset Bool)).map E.toEmbedding
    have incl : U ⊆ (S.biUnion adj) ×ˢ (univ : Finset Bool) := by
      intro y hy
      obtain ⟨⟨i,b⟩,hi,rfl⟩ := mem_map.mp hy
      refine mem_product.mpr ⟨mem_biUnion.mpr ⟨i,(mem_product.mp hi).1,?_⟩,mem_univ _⟩
      cases b <;> simp [adj]
    have h := card_le_card incl
    simp [U] at h
    omega
  obtain ⟨f,hfi,hfa⟩ := (all_card_le_biUnion_card_iff_exists_injective adj).mp hall
  let p := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  have pick (i : A) : ∃ b : Bool, (E (i,b)).1 = p i := by
    have h := hfa i
    change f i ∈ ({(E (i,false)).1, (E (i,true)).1} : Finset A) at h
    simp only [mem_insert, mem_singleton] at h
    rcases h with h|h
    · exact ⟨false,h.symm⟩
    · exact ⟨true,h.symm⟩
  choose a ha using pick
  let b (j : A) := (E (p.symm j,a (p.symm j))).2
  have sel (i : A) : E (i,a i) = (p i,b (p i)) := by
    apply Prod.ext
    · exact ha i
    · simp [b]
  let f' (i : A) := (E (i,!(a i))).1
  have other (i : A) : E (i,!(a i)) = (f' i,!(b (f' i))) := by
    apply Prod.ext
    · rfl
    · have neq : (E (i,!(a i))).2 ≠ b (f' i) := by
        intro h
        have ee : E (i,!(a i)) = E (p.symm (f' i),a (p.symm (f' i))) := by
          rw [sel,p.apply_symm_apply]
          exact Prod.ext rfl h
        have hin := E.injective ee
        have hp := congrArg Prod.fst hin
        have hb := congrArg Prod.snd hin
        change i = p.symm (f' i) at hp
        change (!(a i)) = a (p.symm (f' i)) at hb
        rw [← hp] at hb
        cases a i <;> contradiction
      change (E (i,!(a i))).2 = !(b (f' i))
      cases h : b (f' i) <;> cases hv : (E (i,!(a i))).2 <;> simp_all
  have hinj : Function.Injective f' := by
    intro i k he
    have ee : E (i,!(a i)) = E (k,!(a k)) := by rw [other,other,he]
    exact congrArg Prod.fst (E.injective ee)
  exact ⟨a,b,p,Equiv.ofBijective f' (Finite.injective_iff_bijective.mp hinj),sel,other⟩

end BlockQuotaRouting

namespace BlockQuotaRouting
def I : ℕ → Type
  | 0 => Unit
  | k+1 => I k × Bool

def iFin : (k : ℕ) → Fintype (I k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => letI := iFin k; inferInstanceAs (Fintype (I k × Bool))

def budget : ℕ → ℕ
  | 0 => 0
  | k+1 => 2*budget k + 24*2^k + (k+1)

theorem budgetBound (k : ℕ) : budget k ≤ 13*k*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hh : k+1 ≤ 2^k := Nat.lt_two_pow_self
    rw [budget,pow_succ]
    calc 2*budget k+24*2^k+(k+1) ≤ 2*(13*k*2^k)+26*2^k := by omega
         _ = _ := by ring

theorem permute {A W : Type} (total : (k : ℕ) → (I k → A) → W)
    (add : W → W → W) (Cert : ℕ → W → W → Prop)
    (refl : ∀ x, Cert 0 x x)
    (symm : ∀ {n x y}, Cert n x y → Cert n y x)
    (trans : ∀ {n m x y z}, Cert n x y → Cert m y z → Cert (n+m) x z)
    (merge : ∀ (k : ℕ) (f g f' g' : I k → A) {p q : ℕ},
      Cert p (total k f) (total k f') → Cert q (total k g) (total k g') →
      Cert (p+q+(k+1)) (add (total k f) (total k g)) (add (total k f') (total k g')))
    (splitBank : ∀ (k : ℕ) (x : I (k+1) → A) (color : I k → Bool),
      Cert (12*2^k) (total (k+1) x)
        (add (total k (fun i => x (i,color i))) (total k (fun i => x (i,!(color i)))))) :
    ∀ (k : ℕ) (E : Equiv.Perm (I k)) (x : I k → A),
      Cert (budget k) (total k (fun u => x (E u))) (total k x) := by
  intro k
  induction k with
  | zero =>
    intro E x
    have eq : (fun u => x (E u)) = x := by funext u; congr 1; exact Subsingleton.elim _ _
    rw [eq]
    exact refl _
  | succ k ih =>
    classical
    letI := iFin k
    intro E x
    obtain ⟨a,b,p,q,hp,hq⟩ := switches (A := I k) E
    let l (i : I k) := x (i,b i)
    let r (i : I k) := x (i,!(b i))
    have hl := ih p l
    have hr := ih q r
    have hm := merge k _ _ _ _ hl hr
    have first := splitBank k (fun u => x (E u)) a
    have last := splitBank k x b
    have eq₁ : (fun i => x (E (i,a i))) = (fun i => l (p i)) := by
      funext i
      rw [hp]
    have eq₂ : (fun i => x (E (i,!(a i)))) = (fun i => r (q i)) := by
      funext i
      rw [hq]
    rw [eq₁,eq₂] at first
    have h := trans (trans first hm) (symm last)
    have hn : 12*2^k + (budget k+budget k+(k+1)) + 12*2^k = budget (k+1) := by
      rw [budget]
      omega
    rw [hn] at h
    exact h
end BlockQuotaRouting
