import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4087.Boundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 0
set_option maxRecDepth 32768

abbrev Pt := Fin 13
def D : Finset Pt := {0,1,3,9}
def config (j : Fin 9) : Bool × Pt × Fin 3 := (true, ⟨j.val,by omega⟩, 0)
def allowed (l p : Pt) (hole : Bool) : Bool :=
  decide (l.val ≥ 9 ∧ p-l ∈ D) && !(hole && (p==12) && (l==12))

def full : Circuit := ⟨[⟨.or,[9,10]⟩,⟨.or,[70,12]⟩,⟨.or,[71,5]⟩,⟨.and,[22,72]⟩,⟨.or,[10,11]⟩,⟨.or,[74,0]⟩,⟨.or,[75,6]⟩,⟨.and,[23,76]⟩,⟨.or,[11,12]⟩,⟨.or,[78,1]⟩,⟨.or,[79,7]⟩,⟨.and,[24,80]⟩,⟨.or,[12,0]⟩,⟨.or,[82,2]⟩,⟨.or,[83,8]⟩,⟨.and,[25,84]⟩,⟨.or,[73,77]⟩,⟨.or,[86,81]⟩,⟨.or,[87,85]⟩],88⟩
def near : Circuit := ⟨[⟨.or,[9,10]⟩,⟨.or,[70,12]⟩,⟨.or,[71,5]⟩,⟨.and,[22,72]⟩,⟨.or,[10,11]⟩,⟨.or,[74,0]⟩,⟨.or,[75,6]⟩,⟨.and,[23,76]⟩,⟨.or,[11,12]⟩,⟨.or,[78,1]⟩,⟨.or,[79,7]⟩,⟨.and,[24,80]⟩,⟨.or,[0,2]⟩,⟨.or,[82,8]⟩,⟨.and,[25,83]⟩,⟨.or,[73,77]⟩,⟨.or,[85,81]⟩,⟨.or,[86,84]⟩],87⟩
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i=>w.getD i false))]
def asBool (P L : Finset Pt) (i : Nat) : Bool :=
  if i<13 then decide (Fin.ofNat 13 i∈P) else decide (Fin.ofNat 13 (i-13)∈L)

def formula (hole : Bool) (P L : Finset Pt) : Bool := (((((((decide ((9:Pt)∈P) || decide ((10:Pt)∈P)) || decide ((12:Pt)∈P)) || decide ((5:Pt)∈P)) && decide ((9:Pt)∈L)) || ((((decide ((10:Pt)∈P) || decide ((11:Pt)∈P)) || decide ((0:Pt)∈P)) || decide ((6:Pt)∈P)) && decide ((10:Pt)∈L))) || ((((decide ((11:Pt)∈P) || decide ((12:Pt)∈P)) || decide ((1:Pt)∈P)) || decide ((7:Pt)∈P)) && decide ((11:Pt)∈L))) || (((((!hole && decide ((12:Pt)∈P)) || decide ((0:Pt)∈P)) || decide ((2:Pt)∈P)) || decide ((8:Pt)∈P)) && decide ((12:Pt)∈L)))

def raw (w acc : List Bool) (i : Nat) : Bool :=
  if i < 70 then w.getD i false else acc.getD (i-70) false
def part (w acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map (raw w acc))]

theorem read_append (w acc : List Bool) (h : w.length=70) (i : Nat) :
   (w++acc).getD i false = raw w acc i := by
  by_cases hi:i<70
  · rw [List.getD_append _ _ _ _ (by omega)]
    simp [raw,hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [raw,hi,h]

theorem split_run (gs : List Gate) (w acc : List Bool) (h : w.length=70) :
    gs.foldl step (w++acc)=w++gs.foldl (part w) acc := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have eq : step (w++acc) g = w++part w acc g := by
      simp [step,part,List.append_assoc,read_append w acc h]
    rw [eq,ih]
theorem full_eval (w : List Bool) (P L : Finset Pt) (hlen : w.length = 70)
    (hw : ∀i:Pt,w.getD i.val false=decide (i∈P) ∧ w.getD (13+i.val) false=decide (i∈L)) :
    full.eval w = formula false P L := by
  have w0: w.getD 0 false = decide ((0:Pt)∈P) := (hw 0).1
  have w13: w.getD 13 false = decide ((0:Pt)∈L) := (hw 0).2
  have w1: w.getD 1 false = decide ((1:Pt)∈P) := (hw 1).1
  have w14: w.getD 14 false = decide ((1:Pt)∈L) := (hw 1).2
  have w2: w.getD 2 false = decide ((2:Pt)∈P) := (hw 2).1
  have w15: w.getD 15 false = decide ((2:Pt)∈L) := (hw 2).2
  have w3: w.getD 3 false = decide ((3:Pt)∈P) := (hw 3).1
  have w16: w.getD 16 false = decide ((3:Pt)∈L) := (hw 3).2
  have w4: w.getD 4 false = decide ((4:Pt)∈P) := (hw 4).1
  have w17: w.getD 17 false = decide ((4:Pt)∈L) := (hw 4).2
  have w5: w.getD 5 false = decide ((5:Pt)∈P) := (hw 5).1
  have w18: w.getD 18 false = decide ((5:Pt)∈L) := (hw 5).2
  have w6: w.getD 6 false = decide ((6:Pt)∈P) := (hw 6).1
  have w19: w.getD 19 false = decide ((6:Pt)∈L) := (hw 6).2
  have w7: w.getD 7 false = decide ((7:Pt)∈P) := (hw 7).1
  have w20: w.getD 20 false = decide ((7:Pt)∈L) := (hw 7).2
  have w8: w.getD 8 false = decide ((8:Pt)∈P) := (hw 8).1
  have w21: w.getD 21 false = decide ((8:Pt)∈L) := (hw 8).2
  have w9: w.getD 9 false = decide ((9:Pt)∈P) := (hw 9).1
  have w22: w.getD 22 false = decide ((9:Pt)∈L) := (hw 9).2
  have w10: w.getD 10 false = decide ((10:Pt)∈P) := (hw 10).1
  have w23: w.getD 23 false = decide ((10:Pt)∈L) := (hw 10).2
  have w11: w.getD 11 false = decide ((11:Pt)∈P) := (hw 11).1
  have w24: w.getD 24 false = decide ((11:Pt)∈L) := (hw 11).2
  have w12: w.getD 12 false = decide ((12:Pt)∈P) := (hw 12).1
  have w25: w.getD 25 false = decide ((12:Pt)∈L) := (hw 12).2
  have runEq := split_run full.gates w [] hlen
  rw [List.append_nil] at runEq
  change (full.gates.foldl step w).getD full.output false = _
  rw [runEq,read_append _ _ hlen]
  change (((((w.getD 22 false) && (((((w.getD 9 false) || ((w.getD 10 false) || false)) || ((w.getD 12 false) || false)) || ((w.getD 5 false) || false)) && true)) || (((w.getD 23 false) && (((((w.getD 10 false) || ((w.getD 11 false) || false)) || ((w.getD 0 false) || false)) || ((w.getD 6 false) || false)) && true)) || false)) || (((w.getD 24 false) && (((((w.getD 11 false) || ((w.getD 12 false) || false)) || ((w.getD 1 false) || false)) || ((w.getD 7 false) || false)) && true)) || false)) || (((w.getD 25 false) && (((((w.getD 12 false) || ((w.getD 0 false) || false)) || ((w.getD 2 false) || false)) || ((w.getD 8 false) || false)) && true)) || false)) = formula false P L
  simp [formula,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25]

theorem near_eval (w : List Bool) (P L : Finset Pt) (hlen : w.length = 70)
    (hw : ∀i:Pt,w.getD i.val false=decide (i∈P) ∧ w.getD (13+i.val) false=decide (i∈L)) :
    near.eval w = formula true P L := by
  have w0: w.getD 0 false = decide ((0:Pt)∈P) := (hw 0).1
  have w13: w.getD 13 false = decide ((0:Pt)∈L) := (hw 0).2
  have w1: w.getD 1 false = decide ((1:Pt)∈P) := (hw 1).1
  have w14: w.getD 14 false = decide ((1:Pt)∈L) := (hw 1).2
  have w2: w.getD 2 false = decide ((2:Pt)∈P) := (hw 2).1
  have w15: w.getD 15 false = decide ((2:Pt)∈L) := (hw 2).2
  have w3: w.getD 3 false = decide ((3:Pt)∈P) := (hw 3).1
  have w16: w.getD 16 false = decide ((3:Pt)∈L) := (hw 3).2
  have w4: w.getD 4 false = decide ((4:Pt)∈P) := (hw 4).1
  have w17: w.getD 17 false = decide ((4:Pt)∈L) := (hw 4).2
  have w5: w.getD 5 false = decide ((5:Pt)∈P) := (hw 5).1
  have w18: w.getD 18 false = decide ((5:Pt)∈L) := (hw 5).2
  have w6: w.getD 6 false = decide ((6:Pt)∈P) := (hw 6).1
  have w19: w.getD 19 false = decide ((6:Pt)∈L) := (hw 6).2
  have w7: w.getD 7 false = decide ((7:Pt)∈P) := (hw 7).1
  have w20: w.getD 20 false = decide ((7:Pt)∈L) := (hw 7).2
  have w8: w.getD 8 false = decide ((8:Pt)∈P) := (hw 8).1
  have w21: w.getD 21 false = decide ((8:Pt)∈L) := (hw 8).2
  have w9: w.getD 9 false = decide ((9:Pt)∈P) := (hw 9).1
  have w22: w.getD 22 false = decide ((9:Pt)∈L) := (hw 9).2
  have w10: w.getD 10 false = decide ((10:Pt)∈P) := (hw 10).1
  have w23: w.getD 23 false = decide ((10:Pt)∈L) := (hw 10).2
  have w11: w.getD 11 false = decide ((11:Pt)∈P) := (hw 11).1
  have w24: w.getD 24 false = decide ((11:Pt)∈L) := (hw 11).2
  have w12: w.getD 12 false = decide ((12:Pt)∈P) := (hw 12).1
  have w25: w.getD 25 false = decide ((12:Pt)∈L) := (hw 12).2
  have runEq := split_run near.gates w [] hlen
  rw [List.append_nil] at runEq
  change (near.gates.foldl step w).getD near.output false = _
  rw [runEq,read_append _ _ hlen]
  change (((((w.getD 22 false) && (((((w.getD 9 false) || ((w.getD 10 false) || false)) || ((w.getD 12 false) || false)) || ((w.getD 5 false) || false)) && true)) || (((w.getD 23 false) && (((((w.getD 10 false) || ((w.getD 11 false) || false)) || ((w.getD 0 false) || false)) || ((w.getD 6 false) || false)) && true)) || false)) || (((w.getD 24 false) && (((((w.getD 11 false) || ((w.getD 12 false) || false)) || ((w.getD 1 false) || false)) || ((w.getD 7 false) || false)) && true)) || false)) || (((w.getD 25 false) && ((((w.getD 0 false) || ((w.getD 2 false) || false)) || ((w.getD 8 false) || false)) && true)) || false)) = formula true P L
  simp [formula,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25]

theorem formula_spec (hole : Bool) (P L : Finset Pt) :
    formula hole P L=true ↔ ∃p∈P,∃l∈L,allowed l p hole=true := by
  constructor
  · simp only [formula,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true']
    intro h
    rcases h with ((h|h)|h)|h
    · obtain ⟨hp,hl⟩:=h
      rcases hp with ((hp|hp)|hp)|hp
      · exact ⟨9,hp,9,hl,by cases hole <;> decide⟩
      · exact ⟨10,hp,9,hl,by cases hole <;> decide⟩
      · exact ⟨12,hp,9,hl,by cases hole <;> decide⟩
      · exact ⟨5,hp,9,hl,by cases hole <;> decide⟩
    · obtain ⟨hp,hl⟩:=h
      rcases hp with ((hp|hp)|hp)|hp
      · exact ⟨10,hp,10,hl,by cases hole <;> decide⟩
      · exact ⟨11,hp,10,hl,by cases hole <;> decide⟩
      · exact ⟨0,hp,10,hl,by cases hole <;> decide⟩
      · exact ⟨6,hp,10,hl,by cases hole <;> decide⟩
    · obtain ⟨hp,hl⟩:=h
      rcases hp with ((hp|hp)|hp)|hp
      · exact ⟨11,hp,11,hl,by cases hole <;> decide⟩
      · exact ⟨12,hp,11,hl,by cases hole <;> decide⟩
      · exact ⟨1,hp,11,hl,by cases hole <;> decide⟩
      · exact ⟨7,hp,11,hl,by cases hole <;> decide⟩
    · obtain ⟨hp,hl⟩:=h
      rcases hp with ((hp|hp)|hp)|hp
      · obtain ⟨hF,hp⟩:=hp
        refine ⟨12,hp,12,hl,?_⟩
        cases hole <;> simp_all [allowed,D]
      · exact ⟨0,hp,12,hl,by cases hole <;> decide⟩
      · exact ⟨2,hp,12,hl,by cases hole <;> decide⟩
      · exact ⟨8,hp,12,hl,by cases hole <;> decide⟩
  · rintro ⟨p,hp,l,hl,hok⟩
    have table : ∀ (p l : Pt) (hole : Bool), allowed l p hole=true → (p=9 ∧ l=9) ∨ (p=10 ∧ l=9) ∨ (p=12 ∧ l=9) ∨ (p=5 ∧ l=9) ∨ (p=10 ∧ l=10) ∨ (p=11 ∧ l=10) ∨ (p=0 ∧ l=10) ∨ (p=6 ∧ l=10) ∨ (p=11 ∧ l=11) ∨ (p=12 ∧ l=11) ∨ (p=1 ∧ l=11) ∨ (p=7 ∧ l=11) ∨ (p=12 ∧ l=12 ∧ hole=false) ∨ (p=0 ∧ l=12) ∨ (p=2 ∧ l=12) ∨ (p=8 ∧ l=12) := by decide +kernel
    rcases table p l hole hok with this | this | this | this | this | this | this | this | this | this | this | this | this | this | this | this
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]
    · obtain ⟨rfl,rfl⟩:=this
      simp [formula,hp,hl]

theorem full_boundary : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∃ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (19 : ℕ) ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))) (x7 : List Bool), x2 x3 x5 x6 x7 → ((∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x5 = {x9} ∧ x6 = {x10} ∧ x9 - x10 ∈ x1 ∧ ¬∃ (x11 : Fin (9 : ℕ)), if (x3 x11).1 = Bool.true then (x3 x11).2.1 = x10 else (x3 x11).2.1 = x9) → x4.eval x7 = Bool.true) ∧ ((∀ x9 ∈ x5, ∀ x11 ∈ x6, x9 - x11 ∉ x1) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x5 | x11 - x10 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x6 | x11 - x12 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval x7 = Bool.false) := by
  dsimp only
  have hm : Monotone2 full := by
    intro g hg
    simp only [full,List.mem_cons,List.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by simp,by decide⟩
  refine ⟨config,full,hm,by decide +kernel,?_⟩
  intro P L w hw
  rw [full_eval w P L hw.1 hw.2.1]
  constructor
  · rintro ⟨p,l,rfl,rfl,hinc,hfree⟩
    have hline : 9 ≤ l.val := by
      by_contra! h
      exact hfree ⟨⟨l.val,h⟩,by simp [config]⟩
    apply (formula_spec _ _ _).2
    refine ⟨p,by simp,l,by simp,?_⟩
    simp [allowed,hline,D,hinc]
  · intro hdis _ _
    cases e : formula false P L with
    | false => rfl
    | true =>
      obtain ⟨p,hp,l,hl,h⟩ := (formula_spec _ _ _).1 e
      have hI : p-l∈D := by
        simp only [allowed,Bool.and_eq_true,decide_eq_true_eq] at h
        exact h.1.2
      exact False.elim (hdis p hp l hl hI)

theorem near_boundary : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∃ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (18 : ℕ) ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))) (x7 : List Bool), x2 x3 x5 x6 x7 → ((∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x5 = {x9} ∧ x6 = {x10} ∧ x9 - x10 ∈ x1 ∧ (x9 ≠ 12 ∨ x10 ≠ 12) ∧ ¬∃ (x11 : Fin (9 : ℕ)), if (x3 x11).1 = Bool.true then (x3 x11).2.1 = x10 else (x3 x11).2.1 = x9) → x4.eval x7 = Bool.true) ∧ ((∀ x9 ∈ x5, ∀ x11 ∈ x6, x9 - x11 ∉ x1) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x5 | x11 - x10 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x6 | x11 - x12 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval x7 = Bool.false) := by
  dsimp only
  have hm : Monotone2 near := by
    intro g hg
    simp only [near,List.mem_cons,List.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by simp,by decide⟩
  refine ⟨config,near,hm,by decide +kernel,?_⟩
  intro P L w hw
  rw [near_eval w P L hw.1 hw.2.1]
  constructor
  · rintro ⟨p,l,rfl,rfl,hinc,hdiff,hfree⟩
    have hline : 9 ≤ l.val := by
      by_contra! h
      exact hfree ⟨⟨l.val,h⟩,by simp [config]⟩
    apply (formula_spec _ _ _).2
    refine ⟨p,by simp,l,by simp,?_⟩
    rcases hdiff with hh|hh <;> simp [allowed,hline,D,hh,hinc]
  · intro hdis _ _
    cases e : formula true P L with
    | false => rfl
    | true =>
      obtain ⟨p,hp,l,hl,h⟩ := (formula_spec _ _ _).1 e
      have hI : p-l∈D := by
        simp only [allowed,Bool.and_eq_true,decide_eq_true_eq] at h
        exact h.1.2
      exact False.elim (hdis p hp l hl hI)

end PEqualNP.Outside.L_meta_4087.Boundary
