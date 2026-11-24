import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2567_633
    (patch : let tab := fun (r : Fin 32) => List.ofFn (fun i : Fin 70 => (202801006564288716445520060226817288485868830419401851822812357915392168020546573741375376491503117448766704125209537762215549618824766787476987875360511752526352191696350036638594431731775774354280671643553931730455872963484232917823087140970862171523317778615179539565805555850136178147157052018326689159967393894148491260661900198420184932531388729998419461786735484175666163508806687935780634196792469834788514971665662208998899922974418664056510357370217964630064817462479718832559766307414956033010201808310156202136519664165437786621233806262417005364538792160361350678037058074631509679395971466735550427679133192492135771990970382120130615020922983853594986405707777 : ℕ).testBit (70*r.val+i.val))
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 18 ∧
        ∀ r : Fin 32, C.eval (tab r) = decide (r.val < 16))
    (join : ∀ (m : ℕ) (P C : Circuit), Monotone2 P → Monotone2 C → P.output < m + P.size →
      ∃ D : Circuit, Monotone2 D ∧ D.size = P.size + C.size + 1 ∧
        ∀ w : List Bool, w.length = m → D.eval w = (P.eval w || C.eval (P.wires w)))
    (mono : ∀ (n : ℕ) (C : Circuit), Monotone2 C → Monotone (circuitFun n C)) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  let P : Circuit := ⟨([10309,12627,2813,10509,11012,13031,3217,10408,10911,13435,3618,10307,10810,13839,4019,10206,10709,14243,4420,10004,10507,14647,4822,10304,10612,15051,5223,10203,10511,15455,5624,10102,10410,15859,6025,12933,16237,16341,16445,16549,16653,16757,16861] : List ℕ).map (fun e => ⟨if e < 10000 then .and else .or, [(e / 100) % 100,e % 100]⟩),69⟩
  let J : Finset (Fin 13) := {1,2,3,8}
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let inp := fun (s t : Finset (Fin 13)) => List.ofFn (vec s t) ++ [vec s t 0 || vec s t 1]
  let off := fun s : Finset (Fin 13) => Finset.univ.filter (fun l => ∀ p ∈ s, ¬near p l)
  let tab := fun (r : Fin 32) => List.ofFn (fun i : Fin 70 => (202801006564288716445520060226817288485868830419401851822812357915392168020546573741375376491503117448766704125209537762215549618824766787476987875360511752526352191696350036638594431731775774354280671643553931730455872963484232917823087140970862171523317778615179539565805555850136178147157052018326689159967393894148491260661900198420184932531388729998419461786735484175666163508806687935780634196792469834788514971665662208998899922974418664056510357370217964630064817462479718832559766307414956033010201808310156202136519664165437786621233806262417005364538792160361350678037058074631509679395971466735550427679133192492135771990970382120130615020922983853594986405707777 : ℕ).testBit (70*r.val+i.val))
  obtain ⟨C,hC,sizeC,rows⟩ := patch
  have posData : ∀ p l : Fin 13, l ∈ J → near p l → ∃ r : Fin 32, r.val < 16 ∧ tab r = P.wires (inp {p} {l}) := by
    dsimp only [tab,P,J,near,inp,vec]
    decide +kernel
  let pickT := fun (a b c d : Bool) => J.filter (fun l : Fin 13 =>
    ((l == 1 && a) || (l == 2 && b) || (l == 3 && c) || (l == 8 && d)) = true)
  have reprT (t : Finset (Fin 13)) (ht : t ⊆ J) :
      pickT (decide (1 ∈ t)) (decide (2 ∈ t)) (decide (3 ∈ t)) (decide (8 ∈ t)) = t := by
    ext l
    by_cases hl : l ∈ J
    · have casesL : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 8 := by simpa [J] using hl
      rcases casesL with h | h | h | h <;> subst l <;> simp [pickT,J]
    · have hn : l ∉ t := fun h => hl (ht h)
      simp [pickT,hl,hn]
  have smallRows : ∀ a b c d : Bool, let t := pickT a b c d
      ∃ r : Fin 32, 16 ≤ r.val ∧ tab r = P.wires (inp (off t) (t ∪ Jᶜ)) := by
    dsimp only [tab,P,J,near,inp,vec,off,pickT]
    decide +kernel
  have negData (t : Finset (Fin 13)) (ht : t ⊆ J) :
      ∃ r : Fin 32, 16 ≤ r.val ∧ tab r = P.wires (inp (off t) (t ∪ Jᶜ)) := by
    have h := smallRows (decide (1 ∈ t)) (decide (2 ∈ t)) (decide (3 ∈ t)) (decide (8 ∈ t))
    rwa [reprT t ht] at h
  have posC (p l : Fin 13) (hl : l ∈ J) (he : near p l) : C.eval (P.wires (inp {p} {l})) = true := by
    obtain ⟨i,lt,eq⟩ := posData p l hl he
    rw [← eq]
    simpa only [decide_eq_true lt] using rows i
  have negC (t : Finset (Fin 13)) (ht : t ⊆ J) : C.eval (P.wires (inp (off t) (t ∪ Jᶜ))) = false := by
    obtain ⟨i,ge,eq⟩ := negData t ht
    rw [← eq]
    simpa only [decide_eq_false (Nat.not_lt.mpr ge)] using rows i
  have hp : P.size = 43 := rfl
  have hmono : Monotone2 P := by
    intro g hg
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hg
    by_cases h : e < 10000 <;> simp [h]
  have positive : ∀ p l : Fin 13, l ∉ J → near p l → P.eval (inp {p} {l}) = true := by
    dsimp only [P,J,near,inp,vec]
    decide +kernel
  have outer (x : Fin 26 → Bool) : P.eval (List.ofFn x ++ [x 0 || x 1]) = (((((((((((x 0 || x 1) || (x 3 || x 9)) && x 13) || (((x 5 || x 9) || (x 10 || x 12)) && x 17)) || (((x 4 || x 8) || (x 9 || x 11)) && x 18)) || (((x 3 || x 7) || (x 8 || x 10)) && x 19)) || (((x 2 || x 6) || (x 7 || x 9)) && x 20)) || (((x 0 || x 4) || (x 5 || x 7)) && x 22)) || (((x 3 || x 4) || (x 6 || x 12)) && x 23)) || (((x 2 || x 3) || (x 5 || x 11)) && x 24)) || (((x 1 || x 2) || (x 4 || x 10)) && x 25)) := by
    let u26 := x 0 || x 1
    let u27 := x 3 || x 9
    let u28 := u26 || u27
    let u29 := u28 && x 13
    let u30 := x 5 || x 9
    let u31 := x 10 || x 12
    let u32 := u30 || u31
    let u33 := u32 && x 17
    let u34 := x 4 || x 8
    let u35 := x 9 || x 11
    let u36 := u34 || u35
    let u37 := u36 && x 18
    let u38 := x 3 || x 7
    let u39 := x 8 || x 10
    let u40 := u38 || u39
    let u41 := u40 && x 19
    let u42 := x 2 || x 6
    let u43 := x 7 || x 9
    let u44 := u42 || u43
    let u45 := u44 && x 20
    let u46 := x 0 || x 4
    let u47 := x 5 || x 7
    let u48 := u46 || u47
    let u49 := u48 && x 22
    let u50 := x 3 || x 4
    let u51 := x 6 || x 12
    let u52 := u50 || u51
    let u53 := u52 && x 23
    let u54 := x 2 || x 3
    let u55 := x 5 || x 11
    let u56 := u54 || u55
    let u57 := u56 && x 24
    let u58 := x 1 || x 2
    let u59 := x 4 || x 10
    let u60 := u58 || u59
    let u61 := u60 && x 25
    let u62 := u29 || u33
    let u63 := u62 || u37
    let u64 := u63 || u41
    let u65 := u64 || u45
    let u66 := u65 || u49
    let u67 := u66 || u53
    let u68 := u67 || u57
    let u69 := u68 || u61
    let values : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,u26,u27,u28,u29,u30,u31,u32,u33,u34,u35,u36,u37,u38,u39,u40,u41,u42,u43,u44,u45,u46,u47,u48,u49,u50,u51,u52,u53,u54,u55,u56,u57,u58,u59,u60,u61,u62,u63,u64,u65,u66,u67,u68,u69]
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have h27 : step (values.take 27) (⟨.or,[3,9]⟩ : Gate) = values.take 28 := by
      change values.take 27 ++ [(x 3 || (x 9 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h28 : step (values.take 28) (⟨.or,[26,27]⟩ : Gate) = values.take 29 := by
      change values.take 28 ++ [(u26 || (u27 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h29 : step (values.take 29) (⟨.and,[28,13]⟩ : Gate) = values.take 30 := by
      change values.take 29 ++ [(u28 && (x 13 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h30 : step (values.take 30) (⟨.or,[5,9]⟩ : Gate) = values.take 31 := by
      change values.take 30 ++ [(x 5 || (x 9 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h31 : step (values.take 31) (⟨.or,[10,12]⟩ : Gate) = values.take 32 := by
      change values.take 31 ++ [(x 10 || (x 12 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h32 : step (values.take 32) (⟨.or,[30,31]⟩ : Gate) = values.take 33 := by
      change values.take 32 ++ [(u30 || (u31 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h33 : step (values.take 33) (⟨.and,[32,17]⟩ : Gate) = values.take 34 := by
      change values.take 33 ++ [(u32 && (x 17 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h34 : step (values.take 34) (⟨.or,[4,8]⟩ : Gate) = values.take 35 := by
      change values.take 34 ++ [(x 4 || (x 8 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h35 : step (values.take 35) (⟨.or,[9,11]⟩ : Gate) = values.take 36 := by
      change values.take 35 ++ [(x 9 || (x 11 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h36 : step (values.take 36) (⟨.or,[34,35]⟩ : Gate) = values.take 37 := by
      change values.take 36 ++ [(u34 || (u35 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h37 : step (values.take 37) (⟨.and,[36,18]⟩ : Gate) = values.take 38 := by
      change values.take 37 ++ [(u36 && (x 18 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h38 : step (values.take 38) (⟨.or,[3,7]⟩ : Gate) = values.take 39 := by
      change values.take 38 ++ [(x 3 || (x 7 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h39 : step (values.take 39) (⟨.or,[8,10]⟩ : Gate) = values.take 40 := by
      change values.take 39 ++ [(x 8 || (x 10 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h40 : step (values.take 40) (⟨.or,[38,39]⟩ : Gate) = values.take 41 := by
      change values.take 40 ++ [(u38 || (u39 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h41 : step (values.take 41) (⟨.and,[40,19]⟩ : Gate) = values.take 42 := by
      change values.take 41 ++ [(u40 && (x 19 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h42 : step (values.take 42) (⟨.or,[2,6]⟩ : Gate) = values.take 43 := by
      change values.take 42 ++ [(x 2 || (x 6 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h43 : step (values.take 43) (⟨.or,[7,9]⟩ : Gate) = values.take 44 := by
      change values.take 43 ++ [(x 7 || (x 9 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h44 : step (values.take 44) (⟨.or,[42,43]⟩ : Gate) = values.take 45 := by
      change values.take 44 ++ [(u42 || (u43 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h45 : step (values.take 45) (⟨.and,[44,20]⟩ : Gate) = values.take 46 := by
      change values.take 45 ++ [(u44 && (x 20 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h46 : step (values.take 46) (⟨.or,[0,4]⟩ : Gate) = values.take 47 := by
      change values.take 46 ++ [(x 0 || (x 4 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h47 : step (values.take 47) (⟨.or,[5,7]⟩ : Gate) = values.take 48 := by
      change values.take 47 ++ [(x 5 || (x 7 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h48 : step (values.take 48) (⟨.or,[46,47]⟩ : Gate) = values.take 49 := by
      change values.take 48 ++ [(u46 || (u47 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h49 : step (values.take 49) (⟨.and,[48,22]⟩ : Gate) = values.take 50 := by
      change values.take 49 ++ [(u48 && (x 22 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h50 : step (values.take 50) (⟨.or,[3,4]⟩ : Gate) = values.take 51 := by
      change values.take 50 ++ [(x 3 || (x 4 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h51 : step (values.take 51) (⟨.or,[6,12]⟩ : Gate) = values.take 52 := by
      change values.take 51 ++ [(x 6 || (x 12 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h52 : step (values.take 52) (⟨.or,[50,51]⟩ : Gate) = values.take 53 := by
      change values.take 52 ++ [(u50 || (u51 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h53 : step (values.take 53) (⟨.and,[52,23]⟩ : Gate) = values.take 54 := by
      change values.take 53 ++ [(u52 && (x 23 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h54 : step (values.take 54) (⟨.or,[2,3]⟩ : Gate) = values.take 55 := by
      change values.take 54 ++ [(x 2 || (x 3 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h55 : step (values.take 55) (⟨.or,[5,11]⟩ : Gate) = values.take 56 := by
      change values.take 55 ++ [(x 5 || (x 11 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h56 : step (values.take 56) (⟨.or,[54,55]⟩ : Gate) = values.take 57 := by
      change values.take 56 ++ [(u54 || (u55 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h57 : step (values.take 57) (⟨.and,[56,24]⟩ : Gate) = values.take 58 := by
      change values.take 57 ++ [(u56 && (x 24 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h58 : step (values.take 58) (⟨.or,[1,2]⟩ : Gate) = values.take 59 := by
      change values.take 58 ++ [(x 1 || (x 2 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h59 : step (values.take 59) (⟨.or,[4,10]⟩ : Gate) = values.take 60 := by
      change values.take 59 ++ [(x 4 || (x 10 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h60 : step (values.take 60) (⟨.or,[58,59]⟩ : Gate) = values.take 61 := by
      change values.take 60 ++ [(u58 || (u59 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h61 : step (values.take 61) (⟨.and,[60,25]⟩ : Gate) = values.take 62 := by
      change values.take 61 ++ [(u60 && (x 25 && true))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h62 : step (values.take 62) (⟨.or,[29,33]⟩ : Gate) = values.take 63 := by
      change values.take 62 ++ [(u29 || (u33 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h63 : step (values.take 63) (⟨.or,[62,37]⟩ : Gate) = values.take 64 := by
      change values.take 63 ++ [(u62 || (u37 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h64 : step (values.take 64) (⟨.or,[63,41]⟩ : Gate) = values.take 65 := by
      change values.take 64 ++ [(u63 || (u41 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h65 : step (values.take 65) (⟨.or,[64,45]⟩ : Gate) = values.take 66 := by
      change values.take 65 ++ [(u64 || (u45 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h66 : step (values.take 66) (⟨.or,[65,49]⟩ : Gate) = values.take 67 := by
      change values.take 66 ++ [(u65 || (u49 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h67 : step (values.take 67) (⟨.or,[66,53]⟩ : Gate) = values.take 68 := by
      change values.take 67 ++ [(u66 || (u53 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h68 : step (values.take 68) (⟨.or,[67,57]⟩ : Gate) = values.take 69 := by
      change values.take 68 ++ [(u67 || (u57 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have h69 : step (values.take 69) (⟨.or,[68,61]⟩ : Gate) = values.take 70 := by
      change values.take 69 ++ [(u68 || (u61 || false))] = _
      simp only [Bool.or_false,Bool.and_true] <;> rfl
    have decode : P.gates = [(⟨.or,[3,9]⟩ : Gate),(⟨.or,[26,27]⟩ : Gate),(⟨.and,[28,13]⟩ : Gate),(⟨.or,[5,9]⟩ : Gate),(⟨.or,[10,12]⟩ : Gate),(⟨.or,[30,31]⟩ : Gate),(⟨.and,[32,17]⟩ : Gate),(⟨.or,[4,8]⟩ : Gate),(⟨.or,[9,11]⟩ : Gate),(⟨.or,[34,35]⟩ : Gate),(⟨.and,[36,18]⟩ : Gate),(⟨.or,[3,7]⟩ : Gate),(⟨.or,[8,10]⟩ : Gate),(⟨.or,[38,39]⟩ : Gate),(⟨.and,[40,19]⟩ : Gate),(⟨.or,[2,6]⟩ : Gate),(⟨.or,[7,9]⟩ : Gate),(⟨.or,[42,43]⟩ : Gate),(⟨.and,[44,20]⟩ : Gate),(⟨.or,[0,4]⟩ : Gate),(⟨.or,[5,7]⟩ : Gate),(⟨.or,[46,47]⟩ : Gate),(⟨.and,[48,22]⟩ : Gate),(⟨.or,[3,4]⟩ : Gate),(⟨.or,[6,12]⟩ : Gate),(⟨.or,[50,51]⟩ : Gate),(⟨.and,[52,23]⟩ : Gate),(⟨.or,[2,3]⟩ : Gate),(⟨.or,[5,11]⟩ : Gate),(⟨.or,[54,55]⟩ : Gate),(⟨.and,[56,24]⟩ : Gate),(⟨.or,[1,2]⟩ : Gate),(⟨.or,[4,10]⟩ : Gate),(⟨.or,[58,59]⟩ : Gate),(⟨.and,[60,25]⟩ : Gate),(⟨.or,[29,33]⟩ : Gate),(⟨.or,[62,37]⟩ : Gate),(⟨.or,[63,41]⟩ : Gate),(⟨.or,[64,45]⟩ : Gate),(⟨.or,[65,49]⟩ : Gate),(⟨.or,[66,53]⟩ : Gate),(⟨.or,[67,57]⟩ : Gate),(⟨.or,[68,61]⟩ : Gate)] := by rfl
    have init : List.ofFn x ++ [x 0 || x 1] = values.take 27 := by rfl
    change (P.gates.foldl step (List.ofFn x ++ [x 0 || x 1])).getD 69 false = _
    conv_lhs =>
      rw [decode,init]
      rw [List.foldl_cons,h27,List.foldl_cons,h28,List.foldl_cons,h29,List.foldl_cons,h30,List.foldl_cons,h31]
      rw [List.foldl_cons,h32,List.foldl_cons,h33,List.foldl_cons,h34,List.foldl_cons,h35,List.foldl_cons,h36]
      rw [List.foldl_cons,h37,List.foldl_cons,h38,List.foldl_cons,h39,List.foldl_cons,h40,List.foldl_cons,h41]
      rw [List.foldl_cons,h42,List.foldl_cons,h43,List.foldl_cons,h44,List.foldl_cons,h45,List.foldl_cons,h46]
      rw [List.foldl_cons,h47,List.foldl_cons,h48,List.foldl_cons,h49,List.foldl_cons,h50,List.foldl_cons,h51]
      rw [List.foldl_cons,h52,List.foldl_cons,h53,List.foldl_cons,h54,List.foldl_cons,h55,List.foldl_cons,h56]
      rw [List.foldl_cons,h57,List.foldl_cons,h58,List.foldl_cons,h59,List.foldl_cons,h60,List.foldl_cons,h61]
      rw [List.foldl_cons,h62,List.foldl_cons,h63,List.foldl_cons,h64,List.foldl_cons,h65,List.foldl_cons,h66]
      rw [List.foldl_cons,h67,List.foldl_cons,h68,List.foldl_cons,h69]
    rfl
  have outerZero (s t : Finset (Fin 13)) (hn : ∀ p ∈ s, ∀ l ∈ t, ¬near p l) : P.eval (inp s t) = false := by
    have lb (p : Fin 13) : vec s t (p.castAdd 13) = true ↔ p ∈ s := by
      have pos : ∀ p : Fin 13, (p.castAdd 13).val < 13 ∧ Fin.ofNat 13 (p.castAdd 13).val = p := by decide
      simp only [vec,if_pos (pos p).1,(pos p).2,decide_eq_true_eq]
    have rb (l : Fin 13) : vec s t (Fin.natAdd 13 l) = true ↔ l ∈ t := by
      have pos : ∀ l : Fin 13, ¬(Fin.natAdd 13 l).val < 13 ∧ Fin.ofNat 13 (Fin.natAdd 13 l).val = l := by decide
      simp only [vec,if_neg (pos l).1,(pos l).2,decide_eq_true_eq]
    have edge (p l : Fin 13) (h : near p l) : ¬(vec s t (p.castAdd 13) = true ∧ vec s t (Fin.natAdd 13 l) = true) :=
      fun e => hn p ((lb p).1 e.1) l ((rb l).1 e.2) h
    have stop : ∀ a b c d k : Bool, ¬(a = true ∧ k = true) → ¬(b = true ∧ k = true) →
        ¬(c = true ∧ k = true) → ¬(d = true ∧ k = true) → (((a || b) || (c || d)) && k) = false := by decide
    have kill0 : (((vec s t 0 || vec s t 1) || (vec s t 3 || vec s t 9)) && vec s t 13) = false :=
      stop _ _ _ _ _ (edge 0 0 (by dsimp only [near]; decide)) (edge 1 0 (by dsimp only [near]; decide)) (edge 3 0 (by dsimp only [near]; decide)) (edge 9 0 (by dsimp only [near]; decide))
    have kill4 : (((vec s t 5 || vec s t 9) || (vec s t 10 || vec s t 12)) && vec s t 17) = false :=
      stop _ _ _ _ _ (edge 5 4 (by dsimp only [near]; decide)) (edge 9 4 (by dsimp only [near]; decide)) (edge 10 4 (by dsimp only [near]; decide)) (edge 12 4 (by dsimp only [near]; decide))
    have kill5 : (((vec s t 4 || vec s t 8) || (vec s t 9 || vec s t 11)) && vec s t 18) = false :=
      stop _ _ _ _ _ (edge 4 5 (by dsimp only [near]; decide)) (edge 8 5 (by dsimp only [near]; decide)) (edge 9 5 (by dsimp only [near]; decide)) (edge 11 5 (by dsimp only [near]; decide))
    have kill6 : (((vec s t 3 || vec s t 7) || (vec s t 8 || vec s t 10)) && vec s t 19) = false :=
      stop _ _ _ _ _ (edge 3 6 (by dsimp only [near]; decide)) (edge 7 6 (by dsimp only [near]; decide)) (edge 8 6 (by dsimp only [near]; decide)) (edge 10 6 (by dsimp only [near]; decide))
    have kill7 : (((vec s t 2 || vec s t 6) || (vec s t 7 || vec s t 9)) && vec s t 20) = false :=
      stop _ _ _ _ _ (edge 2 7 (by dsimp only [near]; decide)) (edge 6 7 (by dsimp only [near]; decide)) (edge 7 7 (by dsimp only [near]; decide)) (edge 9 7 (by dsimp only [near]; decide))
    have kill9 : (((vec s t 0 || vec s t 4) || (vec s t 5 || vec s t 7)) && vec s t 22) = false :=
      stop _ _ _ _ _ (edge 0 9 (by dsimp only [near]; decide)) (edge 4 9 (by dsimp only [near]; decide)) (edge 5 9 (by dsimp only [near]; decide)) (edge 7 9 (by dsimp only [near]; decide))
    have kill10 : (((vec s t 3 || vec s t 4) || (vec s t 6 || vec s t 12)) && vec s t 23) = false :=
      stop _ _ _ _ _ (edge 3 10 (by dsimp only [near]; decide)) (edge 4 10 (by dsimp only [near]; decide)) (edge 6 10 (by dsimp only [near]; decide)) (edge 12 10 (by dsimp only [near]; decide))
    have kill11 : (((vec s t 2 || vec s t 3) || (vec s t 5 || vec s t 11)) && vec s t 24) = false :=
      stop _ _ _ _ _ (edge 2 11 (by dsimp only [near]; decide)) (edge 3 11 (by dsimp only [near]; decide)) (edge 5 11 (by dsimp only [near]; decide)) (edge 11 11 (by dsimp only [near]; decide))
    have kill12 : (((vec s t 1 || vec s t 2) || (vec s t 4 || vec s t 10)) && vec s t 25) = false :=
      stop _ _ _ _ _ (edge 1 12 (by dsimp only [near]; decide)) (edge 2 12 (by dsimp only [near]; decide)) (edge 4 12 (by dsimp only [near]; decide)) (edge 10 12 (by dsimp only [near]; decide))
    change P.eval (List.ofFn (vec s t) ++ [vec s t 0 || vec s t 1]) = false
    rw [outer]
    simp only [kill0,kill4,kill5,kill6,kill7,kill9,kill10,kill11,kill12,Bool.or_false]
  have negative (s : Finset (Fin 13)) (_hs : s.card ≤ 3) :
      P.eval (inp s (off s)) = false ∧ P.eval (inp (off s) s) = false := by
    have mem (p : Fin 13) (hp : p ∈ off s) : ∀ l ∈ s, ¬near l p := (Finset.mem_filter.mp hp).2
    refine ⟨outerZero s (off s) (fun p hp l hl => mem l hl p hp),?_⟩
    apply outerZero (off s) s
    intro p hp l hl he
    exact mem p hp l hl (by simpa only [near,Nat.add_comm l.val p.val] using he)
  have pv : P.output < 27 + P.size := by change 69 < 27 + P.size; rw [hp]; decide
  obtain ⟨D,hD,sizeD,ev⟩ := join 27 P C hmono hC pv
  have len (s t : Finset (Fin 13)) : (inp s t).length = 27 := by simp [inp]
  have vin (s t : Finset (Fin 13)) : inp s t = List.ofFn (vec s t) ++ [GateOp.or.eval [vec s t 0,vec s t 1]] := by
    simp [inp,GateOp.eval]
  let g : Gate := ⟨.or,[0,1]⟩
  let T : Circuit := ⟨g :: (P.gates ++ C.gates),C.output⟩
  have hT : Monotone2 T := by
    intro a ha
    change a ∈ g :: (P.gates ++ C.gates) at ha
    simp only [List.mem_cons,List.mem_append] at ha
    rcases ha with h | h | h
    · subst a; simp [g]
    · exact hmono a h
    · exact hC a h
  have seed (x : Fin 26 → Bool) : g.op.eval (g.inputs.map (fun k => (List.ofFn x).getD k false)) = (x 0 || x 1) := by
    change (x 0 || (x 1 || false)) = _
    simp
  have firstStep (A B : Circuit) (x : Fin 26 → Bool) :
      circuitFun 26 (⟨g :: (A.gates ++ B.gates),B.output⟩ : Circuit) x =
        B.eval (A.wires (List.ofFn x ++ [x 0 || x 1])) := by
    simp only [circuitFun,Circuit.eval,Circuit.wires,List.foldl_cons,List.foldl_append]
    rw [seed x]
  have full (s t : Finset (Fin 13)) : circuitFun 26 T (vec s t) = C.eval (P.wires (inp s t)) :=
    firstStep P C (vec s t)
  have vc (s t S U : Finset (Fin 13)) (hs : s ⊆ S) (ht : t ⊆ U) : vec s t ≤ vec S U := by
    intro i
    apply Bool.le_iff_imp.mpr
    by_cases hi : i.val < 13
    · simp only [vec,if_pos hi,decide_eq_true_eq]; exact fun h => hs h
    · simp only [vec,if_neg hi,decide_eq_true_eq]; exact fun h => ht h
  have symmNear (p l : Fin 13) (h : near p l) : near l p := by simpa only [near,Nat.add_comm l.val p.val] using h
  have memOff (s : Finset (Fin 13)) (l : Fin 13) : l ∈ off s ↔ ∀ p ∈ s, ¬near p l := by simp [off]
  have noPatch (s t : Finset (Fin 13)) (no : ∀ p ∈ s, ∀ l ∈ t, ¬near p l) : C.eval (P.wires (inp s t)) = false := by
    let U := t ∩ J
    have sub : U ⊆ J := Finset.inter_subset_right
    have hleft : s ⊆ off U := by
      intro p hp
      apply (memOff U p).2
      intro l hl h
      exact no p hp l (Finset.mem_inter.mp hl).1 (symmNear l p h)
    have hright : t ⊆ U ∪ Jᶜ := by
      intro l hl
      by_cases hj : l ∈ J
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl,hj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hj)
    have le : C.eval (P.wires (inp s t)) ≤ false := calc
      C.eval (P.wires (inp s t)) = circuitFun 26 T (vec s t) := (full s t).symm
      _ ≤ circuitFun 26 T (vec (off U) (U ∪ Jᶜ)) := mono 26 T hT (vc s t (off U) (U ∪ Jᶜ) hleft hright)
      _ = C.eval (P.wires (inp (off U) (U ∪ Jᶜ))) := full (off U) (U ∪ Jᶜ)
      _ = false := negC U sub
    cases h : C.eval (P.wires (inp s t)) with
    | false => rfl
    | true => rw [h] at le; exact ((by decide : ¬ true ≤ false) le).elim
  refine ⟨.or,0,1,D,Or.inr rfl,by simp,hD,by omega,?_,?_⟩
  · intro p l h
    change D.eval (List.ofFn (vec {p} {l}) ++ [GateOp.or.eval [vec {p} {l} 0,vec {p} {l} 1]]) = true
    rw [← vin,ev _ (len _ _)]
    by_cases inJ : l ∈ J
    · rw [posC p l inJ h]; simp
    · rw [positive p l inJ h]; simp
  · intro s hs
    have a := negative s hs
    have h1 := noPatch s (off s) (fun p hp l hl => (memOff s l).1 hl p hp)
    have h2 := noPatch (off s) s (fun p hp l hl h => (memOff s p).1 hp l hl (symmNear p l h))
    change D.eval (List.ofFn (vec s (off s)) ++ [GateOp.or.eval [vec s (off s) 0,vec s (off s) 1]]) = false ∧ D.eval (List.ofFn (vec (off s) s) ++ [GateOp.or.eval [vec (off s) s 0,vec (off s) s 1]]) = false
    rw [←vin,←vin,ev _ (len _ _),ev _ (len _ _),a.1,a.2,h1,h2]
    decide
