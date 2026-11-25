import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2428
namespace Upper2626
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def C : Circuit := ⟨[⟨.or,[13,25]⟩,⟨.or,[23,17]⟩,⟨.or,[26,27]⟩,⟨.and,[0,28]⟩,⟨.or,[13,24]⟩,⟨.or,[18,14]⟩,⟨.or,[30,31]⟩,⟨.and,[1,32]⟩,⟨.or,[25,19]⟩,⟨.or,[15,14]⟩,⟨.or,[34,35]⟩,⟨.and,[2,36]⟩,⟨.or,[13,20]⟩,⟨.or,[16,15]⟩,⟨.or,[38,39]⟩,⟨.and,[3,40]⟩,⟨.or,[21,17]⟩,⟨.or,[16,14]⟩,⟨.or,[42,43]⟩,⟨.and,[4,44]⟩,⟨.or,[22,18]⟩,⟨.or,[17,15]⟩,⟨.or,[46,47]⟩,⟨.and,[5,48]⟩,⟨.or,[23,19]⟩,⟨.or,[18,16]⟩,⟨.or,[50,51]⟩,⟨.and,[6,52]⟩,⟨.or,[24,20]⟩,⟨.or,[19,17]⟩,⟨.or,[54,55]⟩,⟨.and,[7,56]⟩,⟨.or,[25,21]⟩,⟨.or,[20,18]⟩,⟨.or,[58,59]⟩,⟨.and,[8,60]⟩,⟨.or,[13,22]⟩,⟨.or,[21,19]⟩,⟨.or,[62,63]⟩,⟨.and,[9,64]⟩,⟨.or,[23,22]⟩,⟨.or,[20,14]⟩,⟨.or,[66,67]⟩,⟨.and,[10,68]⟩,⟨.or,[24,23]⟩,⟨.or,[21,15]⟩,⟨.or,[70,71]⟩,⟨.and,[11,72]⟩,⟨.or,[25,24]⟩,⟨.or,[22,16]⟩,⟨.or,[74,75]⟩,⟨.and,[12,76]⟩,⟨.or,[29,33]⟩,⟨.or,[37,41]⟩,⟨.or,[45,49]⟩,⟨.or,[53,57]⟩,⟨.or,[61,65]⟩,⟨.or,[69,73]⟩,⟨.or,[78,79]⟩,⟨.or,[80,81]⟩,⟨.or,[82,83]⟩,⟨.or,[84,85]⟩,⟨.or,[86,77]⟩,⟨.or,[87,88]⟩], 89⟩
theorem mono : Monotone2 C := by
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,le_rfl⟩ | exact ⟨Or.inr rfl,le_rfl⟩

def inc (p l : Fin 13) := (p.val+13-l.val)%13 ∈ ([0,1,3,9] : List ℕ)
instance (p l : Fin 13) : Decidable (inc p l) := inferInstanceAs (Decidable (_ ∈ ([0,1,3,9] : List ℕ)))
def vec (s t : Finset (Fin 13)) (i : Fin 26) :=
  if i.val<13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
def off (s : Finset (Fin 13)) := Finset.univ.filter fun l => ∀ p ∈ s,¬ inc p l


open PEqualNP.Outside.L_meta_2428 (evalD tstep okb Good T0 good_fold good_init)
def terms := (C.gates.foldl tstep T0).getD C.output []

def literalTerms : List (List Nat) := [[0,13],[0,25],[0,23],[0,17],[1,13],[1,24],[1,18],[1,14],[2,25],[2,19],[2,15],[2,14],[3,13],[3,20],[3,16],[3,15],[4,21],[4,17],[4,16],[4,14],[5,22],[5,18],[5,17],[5,15],[6,23],[6,19],[6,18],[6,16],[7,24],[7,20],[7,19],[7,17],[8,25],[8,21],[8,20],[8,18],[9,13],[9,22],[9,21],[9,19],[10,23],[10,22],[10,20],[10,14],[11,24],[11,23],[11,21],[11,15],[12,25],[12,24],[12,22],[12,16]]
theorem termEvaluation : terms = literalTerms := by decide +kernel

theorem encoded : ∀ c∈terms, ∃ p l : Fin 13, inc p l ∧ c=[p.val,13+l.val] := by rw [termEvaluation]; decide +kernel
theorem complete : ∀ p l : Fin 13, inc p l → [p.val,13+l.val]∈terms := by rw [termEvaluation]; decide +kernel
theorem reflect (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output

abbrev I := Fin 13
abbrev V := Fin (13+13)
def D : Finset I := {0,1,3,9}
def seeds : List (Nat × Nat) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
def mult : List I := [1,3,9]
def row (x : Nat × Nat) (m t : I) (sw : Bool) : V → Bool :=
  let get := fun (a b : Nat) (i : I) => if sw=true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
  Fin.append (get x.1 x.2) (get x.2 x.1)
def pair (p l : I) (i : V) := decide (i=p.castAdd 13 ∨ i=Fin.natAdd 13 l)
def Positive (C : Circuit) := ∀ p l : I, (∃ v∈D,p=l+v) → circuitFun 26 C (pair p l)=true
def Negative (C : Circuit) := ∀ s∈seeds,∀ m∈mult, ∀ (t : I) (w : Bool), circuitFun 26 C (row s m t w)=false

theorem truth (x : V → Bool) : circuitFun 26 C x=true ↔
    ∃ p l : I, inc p l ∧ x (p.castAdd 13)=true ∧ x (Fin.natAdd 13 l)=true := by
  have points : ∀ p : I, Fin.ofNat 26 p.val=p.castAdd 13 := by decide
  have lines : ∀ l : I, Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide
  change C.eval (List.ofFn x)=true ↔ _
  rw [reflect,evalD,List.any_eq_true]
  constructor
  · rintro ⟨c,hc,hit⟩
    obtain ⟨p,l,incid,rfl⟩ := encoded c hc
    simp only [List.all_cons,List.all_nil,Bool.and_true,points,lines,Bool.and_eq_true] at hit
    exact ⟨p,l,incid,hit⟩
  · rintro ⟨p,l,yes,hp,hl⟩
    refine ⟨_,complete _ _ yes,?_⟩
    simp only [List.all_cons,List.all_nil,Bool.and_true,points,lines,Bool.and_eq_true]
    exact ⟨hp,hl⟩
theorem pos : Positive C := by
  have conv : ∀ p l : I,(∃ v∈D,p=l+v) → inc p l := by decide +kernel
  intro p l h
  exact (truth _).mpr ⟨p,l,conv p l h,by simp [pair],by simp [pair]⟩

def baseSafe (s : Nat × Nat) := ∀ p l : I, inc p l → s.1.testBit p.val=true → s.2.testBit l.val=false
instance (s : Nat × Nat) : Decidable (baseSafe s) := by unfold baseSafe; infer_instance
theorem bases : ∀ s∈seeds,baseSafe s := by decide +kernel
theorem geometric : ∀ m∈mult,∀ (t p l : I),inc p l →
      inc (m*p+t) (m*l+t) ∧ inc (-(m*l+t)) (-(m*p+t)) := by decide +kernel
theorem neg : Negative C := by
  intro s hs m hm t w
  cases h : circuitFun 26 C (row s m t w) with
  | false => rfl
  | true =>
    obtain ⟨p,l,yes,hp,hl⟩ := (truth _).mp h
    have geom := geometric m hm t p l yes
    cases w with
    | false =>
      simp only [row,Fin.append_left,Fin.append_right,Bool.false_ne_true,if_false] at hp hl
      have no := bases s hs _ _ geom.1 hp
      exact Bool.noConfusion (no.symm.trans hl)
    | true =>
      simp only [row,Fin.append_left,Fin.append_right,if_true] at hp hl
      have no := bases s hs _ _ geom.2 hl
      exact Bool.noConfusion (no.symm.trans hp)
theorem threshold64 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (64 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  exact ⟨C,mono,by decide,pos,neg⟩
end Upper2626
