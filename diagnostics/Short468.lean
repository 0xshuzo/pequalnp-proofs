import PEqualNP.Defs
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev V (m k : ℕ) := Fin m × Option (Fin k)
abbrev P (m k : ℕ) := MvPolynomial (V m k) K
abbrev Mask (m : ℕ) := Finset (Fin m)
noncomputable def part {m k : ℕ} (S : Mask m) (j : Option (Fin k)) : P m k := ∑ i∈S, X (i,j)
noncomputable def test {m k : ℕ} (S : Mask m) : P m k :=
  part S none * ∏ j : Fin k, (1 + part S (some j))
def bools (m k : ℕ) : Set (P m k) := Set.range (fun v : V m k => X v * X v + X v)
def pin {m k : ℕ} (S : Mask m) : Set (P m k) := {1 + part S none} ∪ Set.range (fun j : Fin k => part S (some j))
def sys {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) : Set (P m k) :=
  bools m k ∪ Set.image (test (k:=k)) (H : Set (Mask m)) ∪ pin S
def short (m k : ℕ) : Finset (Mask m) := Finset.univ.filter (fun S => S.card≤k+1)
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

/-- Multiplication of a derived line by a monomial, inside a fixed degree bound. -/
theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add,
          add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

/-- Finite sums of derived lines are derived. -/
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Multiplication of a derived line by an arbitrary polynomial: the degree bound grows to
at most the sum of the two degrees. -/
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

theorem degPart {m k : ℕ} (S : Mask m) (j : Option (Fin k)) : (part S j).totalDegree≤1 :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i _ => by simp))
theorem twice {V : Type} (a : MvPolynomial V K) : a+a=0 := by
  rw [← two_smul (ZMod 2) a,show (2 : ZMod 2) = 0 from rfl,zero_smul]
theorem shortRef {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) (own : S∈H) :
    PCRefutable (sys (k:=k) H S) (k+1) := by
  classical
  let F := sys (k:=k) H S
  let A : P m k := part S none
  let B (i : Fin k) : P m k := part S (some i)
  let Q (T : Finset (Fin k)) : P m k := A * ∏ j∈T, (1+B j)
  have degQ (T : Finset (Fin k)) : (Q T).totalDegree≤1+T.card := by
    apply (totalDegree_mul _ _).trans
    apply Nat.add_le_add (degPart S none)
    calc
      _ ≤ ∑ j∈T, (1+B j).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ _j∈T, 1 := Finset.sum_le_sum (fun j _ => (totalDegree_add _ _).trans
        (max_le (by simp) (degPart S (some j))))
      _ = _ := by simp
  have diff (T : Finset (Fin k)) : PCDerivable F (k+1) (Q T + A) := by
    induction T using Finset.induction_on with
    | empty => simpa [Q,twice] using (PCDerivable.zero : PCDerivable F (k+1) 0)
    | insert j T hj ih =>
      have hb : B j ∈ F := Or.inr (Or.inr ⟨j,rfl⟩)
      have small := Finset.card_le_univ (insert j T)
      rw [Finset.card_insert_of_notMem hj,Fintype.card_fin] at small
      have hprod := pcDerivable_mul_left (PCDerivable.ax hb (B := k+1) ((degPart S (some j)).trans (by omega))) (Q T)
      have cap : (Q T).totalDegree+(B j).totalDegree≤k+1 := by
        have := degQ T; have := degPart S (some j); change (B j).totalDegree ≤ 1 at this; omega
      rw [max_eq_left cap] at hprod
      have eq : Q (insert j T)+A = Q T*B j+(Q T+A) := by
        dsimp [Q]; rw [Finset.prod_insert hj]; ring
      rw [eq]
      exact .add hprod ih
  have htest : Q Finset.univ ∈ F := Or.inl (Or.inr ⟨S,own,rfl⟩)
  have hd : (Q Finset.univ).totalDegree≤k+1 := by simpa [Nat.add_comm] using degQ Finset.univ
  have a := PCDerivable.add (PCDerivable.ax htest hd) (diff Finset.univ)
  rw [← add_assoc,twice,zero_add] at a
  have hp : 1+A∈F := Or.inr (Or.inl rfl)
  have dp : (1+A).totalDegree≤k+1 := (totalDegree_add _ _).trans
    (max_le (by simp) ((degPart S none).trans (by omega)))
  have final := PCDerivable.add (PCDerivable.ax hp dp) a
  rwa [add_assoc,twice,add_zero] at final

end Pool468
