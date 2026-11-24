import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5284_215
    (normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let F := graphFun G ∅
      let one (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        ∀ v : Fin n, gateVal n B j (pairInput v v)=false
      let loss (B : Circuit) (j : ℕ) := G.edgeFinset.filter fun e =>
        ({B with gates := B.gates.set j ⟨.or,[]⟩} : Circuit).eval (List.ofFn fun v : Fin n => decide (v∈e)) = false
      let fixed (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        (∃ x, gateVal n B j x=true ∧ F x=false) → 2 ≤ (loss B j).card
      ∀ C : Circuit, Monotone2 C → circuitFun n C=F → one C →
      ∃ D : Circuit, Monotone2 D ∧ D.size≤C.size ∧ circuitFun n D=F ∧ one D ∧ fixed D)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let F := graphFun G ∅
      let one (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        ∀ v : Fin n, gateVal n B j (pairInput v v)=false
      let loss (B : Circuit) (j : ℕ) := G.edgeFinset.filter fun e =>
        ({B with gates := B.gates.set j ⟨.or,[]⟩} : Circuit).eval (List.ofFn fun v : Fin n => decide (v∈e)) = false
      let fixed (B : Circuit) := ∀ j < B.size, (gateAt B j).op=.and →
        (∃ x, gateVal n B j x=true ∧ F x=false) → 2 ≤ (loss B j).card
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      ∀ D : Circuit, Monotone2 D → circuitFun n D=F → one D → fixed D →
      ∃ B : Circuit, Monotone2 B ∧ B.size≤D.size ∧ circuitFun n B=F ∧
        ∀ j < B.size, (gateAt B j).op=.and → ∀ x, gateVal n B j x=true → F x=true) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by
  intro n G inst F on one tri sq C mono exactC old
  have fg (x : Fin n → Bool) : graphFun G ∅ x = F x := by
    change ((decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true)) || F x) = F x
    simp
  have init : circuitFun n C=graphFun G ∅ := by funext x; exact (exactC x).trans (fg x).symm
  have atG (Z : Circuit) (j : ℕ) (g : Gate) (h : Z.gates[j]?=some g) : gateAt Z j = g := by
    change Z.gates.getD j _ = g
    rw [List.getD_eq_getElem?_getD,h]
    rfl
  have single (j : ℕ) (hj : j<C.size) (a : (gateAt C j).op=.and) (v : Fin n) :
      gateVal n C j (pairInput v v)=false := by
    have ent : C.gates[j]?=some C.gates[j] := List.getElem?_eq_getElem hj
    have sa : C.gates[j].op=.and := (atG C j _ ent) ▸ a
    have eq : pairInput v v = on {v} := by funext z; change decide (z=v ∨ z=v) = decide (z∈({v} : Finset (Fin n))); simp
    rw [eq]
    exact old j _ ent sa {v} (by simp)
  obtain ⟨D,dm,ds,df,do',fix⟩ := normal n G C mono init single
  obtain ⟨B,bm,bs,bf,clean⟩ := core n G tri sq D dm df do' fix
  have ev (x : Fin n → Bool) : B.eval (List.ofFn x) = F x := (congrFun bf x).trans (fg x)
  refine ⟨B,bm,bs.trans ds,?_,?_,?_⟩
  · intro u v edge
    rw [ev]
    change decide (∃ a b, G.Adj a b ∧ decide (a∈({u,v} : Finset (Fin n)))=true ∧ decide (b∈({u,v} : Finset (Fin n)))=true)=true
    exact decide_eq_true ⟨u,v,edge,by simp,by simp⟩
  · intro u
    rw [ev]
    change decide (∃ a b, G.Adj a b ∧ decide (a∈({u} : Finset (Fin n)))=true ∧ decide (b∈({u} : Finset (Fin n)))=true)=false
    simp
  · intro j g ent a T _ ht
    obtain ⟨hj,_⟩ := List.getElem?_eq_some_iff.mp ent
    have hit := (fg (on T)).symm.trans (clean j hj ((atG B j g ent).symm ▸ a) (on T) ht)
    change decide (∃ a b, G.Adj a b ∧ decide (a∈T)=true ∧ decide (b∈T)=true)=true at hit
    obtain ⟨p,r,pr,hp,hr⟩ := of_decide_eq_true hit
    exact ⟨p,of_decide_eq_true hp,r,of_decide_eq_true hr,pr⟩
