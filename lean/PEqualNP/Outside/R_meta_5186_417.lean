import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5186_417
    (adapter : ∀ (π : Fin 16 → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.output < 16 + C.size →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size + 1 ∧ D.output < 26 + D.size ∧
  ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 D x =
    PEqualNP.MetaComplexity.circuitFun 16 C (fun i => if h : π i < 26 then x ⟨π i,h⟩ else x 6 || x 12))
    (mono : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → Monotone (PEqualNP.MetaComplexity.circuitFun n C))
    (cover : let diff : Finset (Fin 13) := ({0,1,3,9} : Finset (Fin 13))
  ∀ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, p-l ∉ diff) →
    (∀ l : Fin 13, (P.filter fun p => p-l ∈ diff).card ≤ 2) →
    (∀ p : Fin 13, (L.filter fun l => p-l ∈ diff).card ≤ 2) →
    let z : Fin 26 → Bool := fun x : Fin 26 => decide ((∃ p ∈ P, x = Fin.castAdd 13 p) ∨ ∃ l ∈ L, x = Fin.natAdd 13 l)
    ∃ j : Fin 143, ∀ i : Fin 16, (if i.val = 6 then z 6 || z 12 else z (Fin.ofNat 26 (if i.val < 8 then i.val else if i.val < 11 then i.val + 1 else i.val + 2))) = true →
      (50633381429251597295096306565475970040628795277860986960974492206347664081817639554784693002069944086615226335066906993062066395665910000710366471902462307880028757897677525446404438915131908948639455926634315735034885464966049415814141873322421050428052830730571929583253794397651758281231070735885496660195100825334394060841242947315795264081339026828704284310844021975572373420036160604462332114233969855533533015538038543534869125600530634772498462854058803684151182609422516427085491611021569618819384059536762698042419847526163616179921847239523757046081168214754445360771801333767790915271288809390889849433640259913746558533662618150369108075108534553930563054553224347072595623965 : Nat).testBit (16 * j.val+i.val) = true)
    (search : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 22 ∧ C.output < 16 + C.size ∧
      (∀ t : Fin 19, PEqualNP.MetaComplexity.circuitFun 16 C (fun i => (16360194093184343553691749814189951281568510792456287393242132819712534929154052884283918337 : Nat).testBit (16*t.val+i.val)) = true) ∧
      ∀ t : Fin 143, PEqualNP.MetaComplexity.circuitFun 16 C (fun i => (50633381429251597295096306565475970040628795277860986960974492206347664081817639554784693002069944086615226335066906993062066395665910000710366471902462307880028757897677525446404438915131908948639455926634315735034885464966049415814141873322421050428052830730571929583253794397651758281231070735885496660195100825334394060841242947315795264081339026828704284310844021975572373420036160604462332114233969855533533015538038543534869125600530634772498462854058803684151182609422516427085491611021569618819384059536762698042419847526163616179921847239523757046081168214754445360771801333767790915271288809390889849433640259913746558533662618150369108075108534553930563054553224347072595623965 : Nat).testBit (16*t.val+i.val)) = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ x2.output < (26 : ℕ) + x2.size ∧ (∀ (x3 x4 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  let ports : Fin 16 → Nat := fun i : Fin 16 => (661701331946294267185184 : Nat) / (32 ^ i.val) % 32
  let f := fun (z : Fin 26 → Bool) (i : Fin 16) => let k := (661701331946294267185184 : Nat) / (32 ^ i.val) % 32; if h : k < 26 then z ⟨k,h⟩ else z 6 || z 12
  obtain ⟨C,hmono,hsize,hout,hp,hn⟩ := search
  obtain ⟨T,hT,htsize,hto,eval⟩ := adapter ports C hmono hout
  refine ⟨T,hT,by omega,hto,?_,?_⟩
  · have finiteFlags : ∀ p l : Fin 13, l.val < 5 → p-l ∈ ({0,1,3,9} : Finset (Fin 13)) →
        ∃ t : Fin 19, ∀ i : Fin 16, f (fun x : Fin 26 => decide (x = Fin.castAdd 13 p ∨ x = Fin.natAdd 13 l)) i = (16360194093184343553691749814189951281568510792456287393242132819712534929154052884283918337 : Nat).testBit (16*t.val+i.val) := by
      dsimp only [f]
      decide +kernel
    intro p l hl hi
    obtain ⟨t,ht⟩ := finiteFlags p l hl hi
    rw [eval]
    change PEqualNP.MetaComplexity.circuitFun 16 C (f (fun x : Fin 26 => decide (x = Fin.castAdd 13 p ∨ x = Fin.natAdd 13 l))) = true
    rw [funext ht]
    exact hp t
  · intro P L h0 h1 h2
    obtain ⟨j,hj⟩ := cover P L h0 h1 h2
    rw [eval]
    change PEqualNP.MetaComplexity.circuitFun 16 C (f (fun x : Fin 26 => decide ((∃ p ∈ P, x = Fin.castAdd 13 p) ∨ ∃ l ∈ L, x = Fin.natAdd 13 l))) = false
    have splitPort (z : Fin 26 → Bool) (i : Fin 16) : f z i = (fun (z : Fin 26 → Bool) (i : Fin 16) => if i.val = 6 then z 6 || z 12 else z (Fin.ofNat 26 (if i.val < 8 then i.val else if i.val < 11 then i.val + 1 else i.val + 2))) z i := by
      fin_cases i <;> rfl
    let z : Fin 26 → Bool := fun x : Fin 26 => decide ((∃ p ∈ P, x = Fin.castAdd 13 p) ∨ ∃ l ∈ L, x = Fin.natAdd 13 l)
    have lePorts : f z ≤ (fun i : Fin 16 => (50633381429251597295096306565475970040628795277860986960974492206347664081817639554784693002069944086615226335066906993062066395665910000710366471902462307880028757897677525446404438915131908948639455926634315735034885464966049415814141873322421050428052830730571929583253794397651758281231070735885496660195100825334394060841242947315795264081339026828704284310844021975572373420036160604462332114233969855533533015538038543534869125600530634772498462854058803684151182609422516427085491611021569618819384059536762698042419847526163616179921847239523757046081168214754445360771801333767790915271288809390889849433640259913746558533662618150369108075108534553930563054553224347072595623965 : Nat).testBit (16*j.val+i.val)) := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      exact hj i ((splitPort z i).symm.trans hi)
    have comp := mono 16 C hmono lePorts
    have neg := hn j
    change PEqualNP.MetaComplexity.circuitFun 16 C (f (fun x : Fin 26 => decide ((∃ p ∈ P, x = Fin.castAdd 13 p) ∨ ∃ l ∈ L, x = Fin.natAdd 13 l))) ≤ _ at comp
    rw [neg] at comp
    exact le_antisymm comp bot_le
