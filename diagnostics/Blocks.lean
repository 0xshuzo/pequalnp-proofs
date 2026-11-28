import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3310
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def blocks {N t d : ℕ} (e : (Fin t × Fin d) ↪ Fin N)
    (f : Fin t → Option (Fin d)) : Finset (Fin N) :=
  Finset.univ.biUnion fun i => (f i).toFinset.image fun j => e (i,j)

private theorem block_mem {N t d} (e : (Fin t × Fin d) ↪ Fin N)
    (f : Fin t → Option (Fin d)) (i : Fin t) (j : Fin d) :
    e (i,j) ∈ blocks e f ↔ f i = some j := by
  classical
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hk
    have eqp := e.injective eq
    have hki : k=i := congrArg Prod.fst eqp
    have hvj : v=j := congrArg Prod.snd eqp
    subst i
    subst j
    cases h : f k <;> simp_all
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, ?_,rfl⟩⟩
    simp [h]

private theorem block_inj {N t d} (e : (Fin t × Fin d) ↪ Fin N) :
    Function.Injective (blocks e) := by
  intro f g eq
  funext i
  have mem (j : Fin d) : f i=some j ↔ g i=some j := by
    rw [←block_mem e f i j, eq, block_mem]
  cases hf : f i with
  | none =>
    cases hg : g i with
    | none => rfl
    | some j => have contra := (mem j).mpr hg; simp [hf] at contra
  | some j => exact ((mem j).mp hf).symm

private theorem block_size {N t d} (e : (Fin t × Fin d) ↪ Fin N)
    (f : Fin t → Option (Fin d)) : (blocks e f).card ≤ t := by
  classical
  have mx (i : Fin t) : ((f i).toFinset.image fun j => e (i,j)).card ≤ 1 := by
    cases h : f i <;> simp
  calc
    (blocks e f).card ≤ ∑ i : Fin t, ((f i).toFinset.image fun j => e (i,j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin t, 1 := Finset.sum_le_sum fun i _ => mx i
    _ = t := by simp

theorem subfamily_block_lower (N t d : ℕ) (room : t*d ≤ N) :
    ∃ F : Finset (Finset (Fin N)), (∀ L ∈ F, L.card ≤ t) ∧ F.card=(d+1)^t := by
  classical
  let eqv := Fintype.equivFin (Fin t × Fin d)
  have cap : Fintype.card (Fin t × Fin d) ≤ N := by simpa using room
  let enc : (Fin t × Fin d) ↪ Fin N :=
    { toFun := fun a => ⟨(eqv a).val, lt_of_lt_of_le (eqv a).isLt cap⟩
      inj' := fun _ _ h => eqv.injective (Fin.ext (congrArg Fin.val h)) }
  refine ⟨Finset.univ.image (blocks enc), ?_, ?_⟩
  · intro L hL
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hL
    exact block_size enc f
  · rw [Finset.card_image_of_injective _ (block_inj enc)]
    simp [Fintype.card_fun, Nat.add_comm]

theorem subfamily_choose_lower (N t : ℕ) :
    ∃ F : Finset (Finset (Fin N)), (∀ L ∈ F, L.card ≤ t) ∧ F.card=N.choose t := by
  classical
  refine ⟨Finset.univ.powersetCard t, ?_, ?_⟩
  · intro L hL
    exact (Finset.mem_powersetCard.mp hL).2.le
  · simp [Finset.card_powersetCard]

end PEqualNP.Outside.L_meta_3310
