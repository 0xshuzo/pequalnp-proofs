import PEqualNP.Defs

namespace Plane8311.Flat
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

def Flags {N : ℕ} (S : Fin N → Finset (Fin N)) :=
  Finset.univ.filter fun e : Fin N × Fin N => e.1 ∈ S e.2

def Guarded {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) : Prop :=
  ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ → ℕ),                   PEqualNP.MetaComplexity.Monotone2 x12 ∧                     List.take C.size x12.gates = C.gates ∧                       x12.size ≤ (5 : ℕ) * C.size + (2 : ℕ) ∧                         have x14 : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun (x14 x15 : Finset (Fin N)) (x16 : ℕ) => (x12.wires (PEqualNP.GenericRejection.incidenceInput x14 x15)).getD x16 Bool.false;                         have x15 : Finset (Fin N) → Finset (Fin N) → Prop := fun (x15 x16 : Finset (Fin N)) => ∃ x17 < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x12 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x12 x17).inputs.length = (2 : ℕ) ∧ ∃ (x18 : Fin (2 : ℕ)), (x14 x15 ∅ (PEqualNP.TopForm.opnd x12 x17 x18) && x14 ∅ x16 (PEqualNP.TopForm.opnd x12 x17 ((1 : Fin (2 : ℕ)) - x18)) && (x14 x15 ∅ (x13 x17) || x14 ∅ x16 (x13 x17))) = Bool.true;                         (∀ (x16 x17 : Finset (Fin N)), x15 x16 x17 → PEqualNP.GenericRejection.incidenceFun S x16 x17 = Bool.true) ∧ ∀ (x16 : Finset (Fin N × Fin N)), (∀ x17 ∈ x16, x17.1 ∈ S x17.2 ∧ ¬x15 {x17.1} {x17.2}) → x16.card ≤ (86 : ℕ) * C.size

def W {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) (i : ℕ) :=
  (C.wires (incidenceInput X Y)).getD i false

def Mix {N : ℕ} (C : Circuit) (j : ℕ) (X Y : Finset (Fin N)) : Prop :=
  (gateAt C j).op=.and ∧ (gateAt C j).inputs.length=2 ∧ ∃ b : Fin 2,
    W C X ∅ (opnd C j b)=true ∧ W C ∅ Y (opnd C j (1-b))=true

def witnessed {N : ℕ} (D : Circuit) (size : ℕ) (k : ℕ → ℕ) (X Y : Finset (Fin N)) :=
  ∃ j<size, (gateAt D j).op=.and ∧ (gateAt D j).inputs.length=2 ∧ ∃ b : Fin 2,
    (W D X ∅ (opnd D j b) && W D ∅ Y (opnd D j (1-b)) &&
       (W D X ∅ (k j) || W D ∅ Y (k j)))=true

theorem singleHit {N : ℕ} (D : Circuit) (s : ℕ) (k : ℕ → ℕ) (X Y : Finset (Fin N)) :
    witnessed D s k X Y ↔ ∃ j<s, Mix D j X Y ∧
      (W D X ∅ (k j)=true ∨ W D ∅ Y (k j)=true) := by
  constructor
  · rintro ⟨j,hj,op,arity,b,ok⟩
    simp only [Bool.and_eq_true,Bool.or_eq_true] at ok
    exact ⟨j,hj,⟨op,arity,b,ok.1⟩,ok.2⟩
  · rintro ⟨j,hj,⟨op,arity,b,both⟩,gate⟩
    refine ⟨j,hj,op,arity,b,?_⟩
    simpa only [Bool.and_eq_true,Bool.or_eq_true] using And.intro both gate

def FlatCross (N : ℕ) (D : Circuit) (s : ℕ) :=
  ∀ j<s, ∀ p l : Fin N, Mix D j {p} {l} → ∀ p' l' : Fin N, Mix D j {p'} {l'}

theorem flatNoFlag {N : ℕ} (S : Fin N → Finset (Fin N)) (D : Circuit) (s : ℕ) (k : ℕ → ℕ)
    (flat : FlatCross N D s)
    (missingL : ∀ p, ∃ l, p∉S l) (missingP : ∀ l, ∃ p, p∉S l)
    (sound : ∀ X Y, witnessed D s k X Y → incidenceFun S X Y=true) :
    ∀ p l : Fin N, ¬witnessed D s k {p} {l} := by
  intro p l hit
  obtain ⟨j,hj,mix,hp|hl⟩ := (singleHit ..).mp hit
  · obtain ⟨l',bad⟩ := missingL p
    have h := (singleHit D s k {p} {l'}).mpr ⟨j,hj,flat j hj p l mix p l',Or.inl hp⟩
    exact bad (by simpa [incidenceFun] using sound {p} {l'} h)
  · obtain ⟨p',bad⟩ := missingP l
    have h := (singleHit D s k {p'} {l}).mpr ⟨j,hj,flat j hj p l mix p' l,Or.inr hl⟩
    exact bad (by simpa [incidenceFun] using sound {p'} {l} h)

theorem bound {q N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 2≤q) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (flat : ∀ D : Circuit, D.gates.take C.size=C.gates → FlatCross N D C.size)
    (solution : Guarded S C) : N*(q+1)≤86*C.size := by
  classical
  obtain ⟨D,k,_,preEq,_,sound,charge⟩ := solution
  have row := lines_through q N (fun p l => p∈S l) hq ord (fun l => by simpa using col l) uniq
  have miss (A : Finset (Fin N)) (hA : A.card=q+1) : ∃ i, i∉A := by
    by_contra! full
    have all : A=Finset.univ := Finset.eq_univ_iff_forall.mpr full
    rw [all,Finset.card_univ,Fintype.card_fin] at hA
    nlinarith
  have missingL (p : Fin N) : ∃ l, p∉S l := by
    obtain ⟨l,no⟩ := miss _ (row p)
    exact ⟨l,fun h => no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)⟩
  have none := flatNoFlag S D C.size k (flat D preEq) missingL (fun l => miss _ (col l)) sound
  have result := charge (Flags S) (fun e h => ⟨(Finset.mem_filter.mp h).2,none e.1 e.2⟩)
  have flags : (Flags S).card = N*(q+1) := by
    let swap : {e : Fin N × Fin N // e.1∈S e.2} ≃ (Σ l : Fin N, {p // p∈S l}) :=
      { toFun := fun e => ⟨e.1.2,e.1.1,e.2⟩
        invFun := fun d => ⟨(d.2.1,d.1),d.2.2⟩
        left_inv := fun e => by rcases e with ⟨⟨a,b⟩,h⟩; rfl
        right_inv := fun d => by rcases d with ⟨l,p,h⟩; rfl }
    calc
      (Flags S).card = Fintype.card {e : Fin N × Fin N // e.1∈S e.2} := by simp [Flags,Fintype.card_subtype]
      _ = Fintype.card (Σ l : Fin N, {p // p∈S l}) := Fintype.card_congr swap
      _ = N*(q+1) := by simp [Fintype.card_sigma,Fintype.card_subtype,col]
  rwa [flags] at result

end Plane8311.Flat
