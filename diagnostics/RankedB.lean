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
        have hneq (t : Bool) : (!t) ≠ t := by cases t <;> decide
        exact hneq _ hb
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

end BlockQuotaRouting

namespace BlockQuotaRouting

def front : (k : ℕ) → Bool → I k → I (k+1)
  | 0,b,_ => ((),b)
  | k+1,b,(i,c) => (front k b i,c)

def total {W : ℕ → Type} (add : ∀ k, W k → W k → W (k+1)) :
    (k : ℕ) → (I k → W 0) → W k
  | 0,x => x ()
  | k+1,x => add k (total add k (fun u => x (front k false u)))
                     (total add k (fun u => x (front k true u)))

def splitCost : ℕ → ℕ
  | 0 => 1
  | k+1 => 2*splitCost k + 2*k + 3

theorem splitBound (k : ℕ) : splitCost k + 2*k + 5 = 6*2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [splitCost,pow_succ]; omega

section Ranked
variable {W : ℕ → Type} (add : ∀ k, W k → W k → W (k+1))
    (Cert : (k : ℕ) → ℕ → W k → W k → Prop)

theorem compileSplit
    (refl : ∀ k (x : W k), Cert k 0 x x)
    (mono : ∀ {k p q} {x y : W k}, p ≤ q → Cert k p x y → Cert k q x y)
    (trans : ∀ {k p q} {x y z : W k}, Cert k p x y → Cert k q y z → Cert k (p+q) x z)
    (swap : ∀ (a b : W 0), Cert 1 1 (add 0 a b) (add 0 b a))
    (merge : ∀ (k : ℕ) {p q} {a b c d : W k}, Cert k p a b → Cert k q c d →
      Cert (k+1) (p+q+(k+1)) (add k a c) (add k b d))
    (cross : ∀ (k : ℕ) (a b c d : W k),
      Cert (k+2) (k+1) (add (k+1) (add k a b) (add k c d))
                         (add (k+1) (add k a c) (add k b d))) :
    ∀ k (x : I (k+1) → W 0) (color : I k → Bool),
      Cert (k+1) (splitCost k) (total add (k+1) x)
        (add k (total add k (fun i => x (i,color i))) (total add k (fun i => x (i,!(color i))))) := by
  intro k
  induction k with
  | zero =>
    intro x color
    cases h : color () with
    | false => simpa [total,front,splitCost,h] using
        (mono (by decide : 0 ≤ 1) (refl 1 (add 0 (x ((),false)) (x ((),true)))))
    | true => simpa [total,front,splitCost,h] using (swap (x ((),false)) (x ((),true)))
  | succ k ih =>
    intro x color
    let xx (b : Bool) (u : I (k+1)) := x (front (k+1) b u)
    let cc (b : Bool) (u : I k) := color (front k b u)
    let L (b : Bool) := total add k (fun u => xx b (u,cc b u))
    let R (b : Bool) := total add k (fun u => xx b (u,!(cc b u)))
    have h0 := ih (xx false) (cc false)
    have h1 := ih (xx true) (cc true)
    have h2 := trans (merge (k+1) h0 h1) (cross k (L false) (R false) (L true) (R true))
    have eq : splitCost k+splitCost k+(k+1+1)+(k+1) = splitCost (k+1) := by
      rw [splitCost]; omega
    rw [eq] at h2
    exact h2

theorem compilePermutation
    (refl : ∀ k (x : W k), Cert k 0 x x)
    (symm : ∀ {k n} {x y : W k}, Cert k n x y → Cert k n y x)
    (mono : ∀ {k p q} {x y : W k}, p ≤ q → Cert k p x y → Cert k q x y)
    (trans : ∀ {k p q} {x y z : W k}, Cert k p x y → Cert k q y z → Cert k (p+q) x z)
    (swap : ∀ (a b : W 0), Cert 1 1 (add 0 a b) (add 0 b a))
    (merge : ∀ (k : ℕ) {p q} {a b c d : W k}, Cert k p a b → Cert k q c d →
      Cert (k+1) (p+q+(k+1)) (add k a c) (add k b d))
    (cross : ∀ (k : ℕ) (a b c d : W k),
      Cert (k+2) (k+1) (add (k+1) (add k a b) (add k c d))
                         (add (k+1) (add k a c) (add k b d))) :
    ∀ (k : ℕ) (E : Equiv.Perm (I k)) (x : I k → W 0),
      Cert k (budget k) (total add k (fun u => x (E u))) (total add k x) := by
  intro k
  induction k with
  | zero =>
    intro E x
    have eq : (fun u => x (E u)) = x := by
      funext u
      exact congrArg x (show E u = u from @Subsingleton.elim Unit _ _ _)
    rw [eq]
    exact refl _ _
  | succ k ih =>
    classical
    letI := iFin k
    intro E x
    obtain ⟨a,b,p,q,hp,hq⟩ := switches (A := I k) E
    let l (i : I k) := x (i,b i)
    let r (i : I k) := x (i,!(b i))
    have hl := ih p l
    have hr := ih q r
    have hm := merge k hl hr
    have first := compileSplit add Cert refl mono trans swap merge cross k (fun u => x (E u)) a
    have last := compileSplit add Cert refl mono trans swap merge cross k x b
    have eq₁ : (fun i => x (E (i,a i))) = (fun i => l (p i)) := by
      funext i
      exact congrArg (fun z : I k × Bool => x z) (hp i)
    have eq₂ : (fun i => x (E (i,!(a i)))) = (fun i => r (q i)) := by
      funext i
      exact congrArg (fun z : I k × Bool => x z) (hq i)
    rw [eq₁,eq₂] at first
    have hh := trans (trans first hm) (symm last)
    have hb := splitBound k
    apply mono _ hh
    rw [budget]
    omega
end Ranked
end BlockQuotaRouting
