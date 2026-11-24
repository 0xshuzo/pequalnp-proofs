import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4706_417
    (search : let feature := fun (y : ℕ → Bool) (i : Fin 33) => if i.val < 17 then y i.val else
       let q := (5721692458950692931333779303423457015614510219543676140502893221252812956276359184 : ℕ) >>> (17*(i.val-17))
       let a := y (q % 16) || y ((q/16) % 16)
       if q.testBit 16 then a || (y ((q/256) % 16) || y ((q/4096) % 16)) else a
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 33 C ∧ C.size ≤ 23 ∧ C.output < 33+C.size ∧
        ∀ t : Fin 191, circuitFun 33 C (feature (fun i => (246717392476363050053700684732416204591262471366432878262674175352996106843162590045010697966443203016504654445617984075747453471851979150269426806997903278203441858967090251015880136574064584914983363652640574647952390328738634897550486897442920520837034958022773650143599343461722069941052853598377831011876219502962005682302081854864886148095737011866110730074101040345173971287113972331057396935225662037253866498421992070648221539056033735943982587365228428434817015455454554624415351392512785893294961216733722735790898634023566581697846837555061767985320988557529875857863433497902147681885034607429788379661207783996788127979068664323623706827766479333790706480586430578835692952706431183513761831958173678838019220884635037999228352420014382196337024132359135722496072098081922212900792385484111744473594535773018070423771904877518435019725561938331710605533461302965734539278384910300603373245298174652391129937581790786740678907368935997187022561910787897713154854914 : ℕ).testBit (17*t.val+i))) = decide (t.val<20))
    (stage : let base := fun (x : Fin 26 → Bool) (i : ℕ) => x (Fin.ofNat 26 (if i < 9 then i else if i < 12 then i+1 else i+2))
      let feature := fun (y : ℕ → Bool) (i : Fin 33) => if i.val < 17 then y i.val else
       let q := (5721692458950692931333779303423457015614510219543676140502893221252812956276359184 : ℕ) >>> (17*(i.val-17))
       let a := y (q % 16) || y ((q/16) % 16)
       if q.testBit 16 then a || (y ((q/256) % 16) || y ((q/4096) % 16)) else a
      let outer := fun (x : Fin 26 → Bool) =>
       let star := fun l : ℕ =>
         let p := fun d : ℕ => x (Fin.ofNat 26 ((l+d) % 13))
         ((p 0 || p 1) || (p 3 || p 9)) && x (Fin.ofNat 26 (l+13))
       ([6,7,8,9,10,11,12] : List ℕ).foldl (fun a l => a || star l) (star 0)
      ∃ (P : Circuit) (π : Fin 33 → Fin (27+P.size)), Monotone2 P ∧ ReadsBack 27 P ∧
        P.size = 38 ∧ P.output < 27+P.size ∧ ∀ x : Fin 26 → Bool, let z : Fin 27 → Bool := (fun (x : Fin 26 → Bool) => Fin.lastCases (x 0 || x 1) x) x
          circuitFun 27 P z = outer x ∧ ∀ i : Fin 33,
            (P.wires (List.ofFn z)).getD (π i).val false = feature (base x) i)
    (graft : ∀ (n m : ℕ) (P C : Circuit) (π : Fin m → Fin (n+P.size)), Monotone2 P → ReadsBack n P →
      P.output < n+P.size → Monotone2 C → ReadsBack m C → C.output < m+C.size →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = P.size+C.size+1 ∧
        ∀ x : Fin n → Bool, circuitFun n D x =
          (circuitFun n P x || circuitFun m C (fun i => (P.wires (List.ofFn x)).getD (π i).val false)))
    (mono : ∀ (n : ℕ) (C : Circuit), Monotone2 C → Monotone (circuitFun n C)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (4 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x5 ∧       x5.size ≤ (62 : ℕ) ∧         have x6 : Fin (26 : ℕ) := if ↑x4 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x4 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x7 : Bool := Decidable.decide (↑x4 = (0 : ℕ));         have x8 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x8 : Fin (26 : ℕ) → Bool) (x9 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x7 = Bool.true then x8 (0 : Fin (26 : ℕ)) && x8 x6 else x8 (0 : Fin (26 : ℕ)) || x8 x6) x8 x9;         (∀ (x9 x10 : Fin (13 : ℕ)), (∃ x11 ∈ x1, x9 = x10 + x11) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) ∧ ∀ x9 ∈ x2, ∀ x11 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x13 : Fin (13 : ℕ)) (x14 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 (x3 x9 x11 x13 x14)) = Bool.false := by
  let base := fun (x : Fin 26 → Bool) (i : ℕ) => x (Fin.ofNat 26 (if i < 9 then i else if i < 12 then i+1 else i+2))
  let feature := fun (y : ℕ → Bool) (i : Fin 33) => if i.val < 17 then y i.val else
       let q := (5721692458950692931333779303423457015614510219543676140502893221252812956276359184 : ℕ) >>> (17*(i.val-17))
       let a := y (q % 16) || y ((q/16) % 16)
       if q.testBit 16 then a || (y ((q/256) % 16) || y ((q/4096) % 16)) else a
  let outer := fun (x : Fin 26 → Bool) =>
       let star := fun l : ℕ =>
         let p := fun d : ℕ => x (Fin.ofNat 26 ((l+d) % 13))
         ((p 0 || p 1) || (p 3 || p 9)) && x (Fin.ofNat 26 (l+13))
       ([6,7,8,9,10,11,12] : List ℕ).foldl (fun a l => a || star l) (star 0)
  let seed : (Fin 26 → Bool) → Fin 27 → Bool := fun (x : Fin 26 → Bool) => Fin.lastCases (x 0 || x 1) x
  let row (t : Fin 191) (i : ℕ) := (246717392476363050053700684732416204591262471366432878262674175352996106843162590045010697966443203016504654445617984075747453471851979150269426806997903278203441858967090251015880136574064584914983363652640574647952390328738634897550486897442920520837034958022773650143599343461722069941052853598377831011876219502962005682302081854864886148095737011866110730074101040345173971287113972331057396935225662037253866498421992070648221539056033735943982587365228428434817015455454554624415351392512785893294961216733722735790898634023566581697846837555061767985320988557529875857863433497902147681885034607429788379661207783996788127979068664323623706827766479333790706480586430578835692952706431183513761831958173678838019220884635037999228352420014382196337024132359135722496072098081922212900792385484111744473594535773018070423771904877518435019725561938331710605533461302965734539278384910300603373245298174652391129937581790786740678907368935997187022561910787897713154854914 : ℕ).testBit (17*t.val+i)
  obtain ⟨C,cm,cb,cs,co,ht⟩ := search
  obtain ⟨P,π,pm,pb,ps,po,sem⟩ := stage
  obtain ⟨D,dm,db,ds,ev⟩ := graft 27 33 P C π pm pb po cm cb co
  have combined (x : Fin 26 → Bool) :
      circuitFun 27 D (seed x) = (outer x || circuitFun 33 C (feature (base x))) := by
    obtain ⟨prev,taps⟩ := sem x
    rw [ev,prev,funext taps]
  have liftLe (a b : ℕ → Bool) (h : ∀ i : Fin 17, a i.val ≤ b i.val) : feature a ≤ feature b := by
    have join {u v w y : Bool} (hh : u ≤ w) (hk : v ≤ y) : (u || v) ≤ (w || y) := by
      cases u <;> cases v <;> cases w <;> cases y <;> simp_all
    have bit (t : ℕ) : a (t % 16) ≤ b (t % 16) := h ⟨t % 16,by omega⟩
    intro i
    dsimp only [feature]
    split
    · exact h ⟨i.val,by assumption⟩
    · split
      · exact join (join (bit _) (bit _)) (join (bit _) (bit _))
      · exact join (bit _) (bit _)
  let pair := fun (p l : Fin 13) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let table := fun (v : ℕ × ℕ) (m t : Fin 13) (b : Bool) =>
    let bit := fun (a c : ℕ) (i : Fin 13) => if b = true then c.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
    Fin.append (bit v.1 v.2) (bit v.2 v.1)
  let rep (i : Fin 8) : ℕ × ℕ := ([(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)] : List (ℕ×ℕ)).getD i.val (0,0)
  let mul (i : Fin 3) : Fin 13 := ([1,3,9] : List (Fin 13)).getD i.val 0
  let key (p l : Fin 13) := Fin.ofNat 191 (((2292129961302449906716184559167367212923426356920720429558708613432056392430486686903845734883415736693303678374788331510086417979640835799719599440956608335822894550600801365368208348537783639297823431324797175894993940986051197712671440896 : ℕ) >>> (5*(13*p.val+l.val)))%32)
  let idx (a : Fin 8) (s : Fin 3) (t : Fin 13) (b : Bool) :=
    Fin.ofNat 191 (((223583775274006441981864143384057103432872904102845140124203234177685795375016977514299645322089580289464183609389858029270701611240681335443528029376641847328163210978811640967454270091246628676695890284265155579814637586951039541090373500964237389036494474463781407232892356959258558129792207514042206638532383814897209710469252064668433879487732235844448489870787568230112502104952372381437006341665322113239196139675581892199184878333660240139034324117317406395479457435734243776385288881782454673724775992451274932987059830852885368506384137814711013050927215868454397359957343904947353923467879464389433032796912445983723863277412977545997003608968747559765149687323231947997914181763384490476628165027018997314519354476150283130034809507455621602943032568947787726349591921117274364607119673919250399693411576715606838394657902346535667976415432445446159188007624624994277435275058200571702243882531984841011288250269225718162095410206250823201309951874863830986457164118463836462295965565697907975258611660698923646912506131531200038369839897656073458722362030025540770279454844790359711144901423305518596595961646199759299780758249810980811564972980872387764786768741709373131773319436281718881264746463166943779432179285601870657874310628903112732304770420527636610251167354654450894426501830623287525963987437661462006030140277042494369127836399419741080013788811459111652533497671289910562192636195001178774573048078772505719258849047741554591240534166285053687678536777861402071100460575333 : ℕ) >>> (8*(78*a.val+26*s.val+2*t.val+(if b then 1 else 0))))%256)
  have positive : ∀ p l : Fin 13, (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d) →
      outer (pair p l) = true ∨ ((key p l).val < 20 ∧
        ∀ j : Fin 17, row (key p l) j.val = true → base (pair p l) j.val = true) := by
    dsimp only [outer,pair,key,row,base]
    decide +kernel
  have negative : ∀ (a : Fin 8) (s : Fin 3) (t : Fin 13) (b : Bool),
      let x := table (rep a) (mul s) t b
      outer x = false ∧ 20 ≤ (idx a s t b).val ∧
        ∀ j : Fin 17, base x j.val = true → row (idx a s t b) j.val = true := by
    dsimp only [outer,table,rep,mul,idx,row,base]
    intro a
    fin_cases a <;> decide +kernel
  refine ⟨(1 : Fin 4),D,dm,db,by omega,?_,?_⟩
  · intro p l hp
    change circuitFun 27 D (seed (pair p l)) = true
    rw [combined]
    rcases positive p l hp with yes | ⟨small,on⟩
    · rw [yes]; rfl
    · have lower := mono 33 C cm (liftLe (row (key p l)) (base (pair p l)) (fun i => Bool.le_iff_imp.mpr (on i)))
      have accepted : circuitFun 33 C (feature (row (key p l))) = true := (ht _).trans (decide_eq_true small)
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.le_iff_imp.mp lower accepted))
  · intro v hv m hm t b
    obtain ⟨i,hi,evr⟩ := List.getElem_of_mem hv
    obtain ⟨q,hq,evm⟩ := List.getElem_of_mem hm
    let a : Fin 8 := ⟨i,by exact hi⟩
    let s : Fin 3 := ⟨q,by exact hq⟩
    have rv : rep a = v := (List.getD_eq_getElem _ _ hi).trans evr
    have mv : mul s = m := (List.getD_eq_getElem _ _ hq).trans evm
    change circuitFun 27 D (seed (table v m t b)) = false
    rw [← rv,← mv,combined]
    obtain ⟨no,large,under⟩ := negative a s t b
    rw [no,Bool.false_or]
    let x := table (rep a) (mul s) t b
    have upper := mono 33 C cm (liftLe (base x) (row (idx a s t b)) (fun i => Bool.le_iff_imp.mpr (under i)))
    have falseRow : circuitFun 33 C (feature (row (idx a s t b))) = false := (ht _).trans (decide_eq_false (by omega))
    change circuitFun 33 C (feature (base x)) ≤ circuitFun 33 C (feature (row (idx a s t b))) at upper
    rw [falseRow] at upper
    exact le_antisymm upper bot_le
