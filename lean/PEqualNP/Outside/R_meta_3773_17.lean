import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3773_17
    (patch : let D : Finset (Fin 13) := {0,1,3,9}
      let J : Finset (Fin 13) := {1,2,3,5,8}
      let P : Circuit := ⟨([10001,10309,12627,2813,10509,11012,13031,3217,10307,10810,13435,3619,10206,10709,13839,4020,10004,10507,14243,4422,10304,10612,14647,4823,10203,10511,15051,5224,10102,10410,15455,5625,12933,15837,15941,16045,16149,16253,16357] : List ℕ).map (fun e => ⟨if e < 10000 then .and else .or, [(e / 100) % 100,e % 100]⟩),64⟩
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 23 ∧ ∀ x : Fin 26 → Bool,
        C.eval (P.wires (List.ofFn x)) = true ↔ ∃ p l : Fin 13, l ∈ J ∧ p + l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (outer : let D : Finset (Fin 13) := {0,1,3,9}
      let J : Finset (Fin 13) := {1,2,3,5,8}
      let P : Circuit := ⟨([10001,10309,12627,2813,10509,11012,13031,3217,10307,10810,13435,3619,10206,10709,13839,4020,10004,10507,14243,4422,10304,10612,14647,4823,10203,10511,15051,5224,10102,10410,15455,5625,12933,15837,15941,16045,16149,16253,16357] : List ℕ).map (fun e => ⟨if e < 10000 then .and else .or, [(e / 100) % 100,e % 100]⟩),64⟩
      ∀ x : Fin 26 → Bool, P.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, l ∉ J ∧ p + l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (join : ∀ (m : ℕ) (P C : Circuit) (g : Gate), P.gates.head? = some g → Monotone2 P → Monotone2 C → P.output < m + P.size →
      ∃ K : Circuit, Monotone2 K ∧ K.size = P.size + C.size + 1 ∧ K.gates.head? = some g ∧
        ∀ w : List Bool, w.length = m → K.eval w = (P.eval w || C.eval (P.wires w))) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  let D : Finset (Fin 13) := {0,1,3,9}
  let J : Finset (Fin 13) := {1,2,3,5,8}
  let P : Circuit := ⟨([10001,10309,12627,2813,10509,11012,13031,3217,10307,10810,13435,3619,10206,10709,13839,4020,10004,10507,14243,4422,10304,10612,14647,4823,10203,10511,15051,5224,10102,10410,15455,5625,12933,15837,15941,16045,16149,16253,16357] : List ℕ).map (fun e => ⟨if e < 10000 then .and else .or, [(e / 100) % 100,e % 100]⟩),64⟩
  obtain ⟨C,hm,hsize,hC⟩ := patch
  have hP : Monotone2 P := by
    intro g hg
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hg
    by_cases h : e < 10000 <;> simp [h]
  let g : Gate := ⟨.or,[0,1]⟩
  have hfirst : P.gates.head? = some g := rfl
  have len : P.size = 39 := rfl
  obtain ⟨K,hK,sz,hd,eval⟩ := join 26 P C g hfirst hP hm (by decide)
  have exactK (x : Fin 26 → Bool) : K.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, p + l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    rw [eval _ (by simp),Bool.or_eq_true]
    rw [outer x,hC x]
    constructor
    · rintro (⟨p,l,_,he,hp,hl⟩ | ⟨p,l,_,he,hp,hl⟩) <;> exact ⟨p,l,he,hp,hl⟩
    · rintro ⟨p,l,he,hp,hl⟩
      by_cases h : l ∈ J
      · exact Or.inr ⟨p,l,h,he,hp,hl⟩
      · exact Or.inl ⟨p,l,h,he,hp,hl⟩
  refine ⟨K,hK,by omega,⟨g,hd,Or.inr ⟨rfl,by decide⟩⟩,?_,?_⟩
  · intro p l he
    apply (exactK _).2
    let u := Fin.castAdd 13 p
    let v := Fin.natAdd 13 l
    refine ⟨p,l,he,?_,?_⟩
    · change decide (u = u ∨ u = v) = true
      exact decide_eq_true (Or.inl rfl)
    · change decide (v = u ∨ v = v) = true
      exact decide_eq_true (Or.inr rfl)
  · intro S _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,he,hp,hl⟩ := (exactK _).1 h
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hl p hp he
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,he,hp,hl⟩ := (exactK _).1 h
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hp l hl he
