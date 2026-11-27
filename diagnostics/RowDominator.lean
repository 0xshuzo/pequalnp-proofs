import PEqualNP.Defs
namespace Lpcx178ThreeDemands
open PEqualNP.ProofComplexity
section
variable {V : Type} [DecidableEq V]
def flip (x : V→Bool) (v : V) (i : V) := if i=v then !(x i) else x i

theorem opposite {x : V→Bool} {f : Finset V} {v : V} (hv : v∈f) (b : Bool) :
    LinEqSat (flip x v) (f,b) ↔ ¬LinEqSat x (f,b) := by
  let S := (f.erase v).filter (fun i=>x i=true)
  have nv : v∉S := by simp [S]
  have h0 : f.filter (fun i=>x i=true) = (if x v then insert v S else S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S]
    · cases hx : x v <;> simp [hx,S,he]
  have h1 : f.filter (fun i=>flip x v i=true) = (if x v then S else insert v S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S,flip]
    · cases hx : x v <;> simp [hx,S,he,flip]
  unfold LinEqSat
  change (Odd (f.filter (fun i=>flip x v i=true)).card ↔ b=true) ↔
    ¬(Odd (f.filter (fun i=>x i=true)).card ↔ b=true)
  rw [h0,h1]
  cases xx : x v <;> cases b <;> simp [xx,Finset.card_insert_of_notMem nv,Nat.odd_iff] <;> omega


end
abbrev Cell := Fin 5 × Fin 4
def board (x : Cell → Bool) : Prop :=
  ∀ i j : Cell, i.2 = j.2 → x i = true → x j = true → i = j
def served (x : Cell → Bool) (p : Fin 5) := ∃ h, x (p,h) = true
def seed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (v : Cell) : Bool :=
  decide (∃ n : Fin 3, v = (r n, k n))

theorem freshHoles : ∀ h : Fin 4, ∃ k : Fin 3 → Fin 4,
    Function.Injective k ∧ ∀ n, k n ≠ h := by decide +kernel

theorem seedBoard (r : Fin 3 → Fin 5) {k : Fin 3 → Fin 4} (inj : Function.Injective k) :
    board (seed r k) := by
  intro i j eq hi hj
  obtain ⟨m,ei⟩ := of_decide_eq_true hi
  obtain ⟨n,ej⟩ := of_decide_eq_true hj
  subst i
  subst j
  obtain rfl := inj eq
  rfl

theorem seedServed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (n : Fin 3) :
    served (seed r k) (r n) :=
  ⟨k n,decide_eq_true ⟨n,rfl⟩⟩

theorem freshFlip (x : Cell → Bool) (i : Cell) (hx : board x)
    (clear : ∀ u : Cell, u.2 = i.2 → x u = false) : board (flip x i) := by
  intro u v eq hu hv
  by_cases ui : u = i
  · by_cases vi : v = i
    · exact ui.trans vi.symm
    · have z := clear v (eq.symm.trans (congrArg Prod.snd ui))
      simp [flip,vi,z] at hv
  · by_cases vi : v = i
    · have z := clear u (eq.trans (congrArg Prod.snd vi))
      simp [flip,ui,z] at hu
    · exact hx u v eq (by simpa [flip,ui] using hu) (by simpa [flip,vi] using hv)

theorem threeDemandFiber {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinEqSat x (f,b) := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨k,inj,avoid⟩ := freshHoles i.2
  let x := seed r k
  have bx : board x := seedBoard r inj
  have clear (u : Cell) (hu : u.2 = i.2) : x u = false := by
    change decide (∃ n : Fin 3, u = (r n,k n)) = false
    apply decide_eq_false
    rintro ⟨n,e⟩
    exact avoid n ((congrArg Prod.snd e).symm.trans hu)
  by_cases hit : LinEqSat x (f,b)
  · exact ⟨x,bx,seedServed r k,hit⟩
  · refine ⟨flip x i,freshFlip x i bx clear,?_,(opposite hi b).mpr hit⟩
    intro n
    have ne : (r n,k n) ≠ i := fun e => avoid n (congrArg Prod.snd e)
    refine ⟨k n,?_⟩
    have yes : x (r n,k n) = true := decide_eq_true ⟨n,rfl⟩
    simpa [flip,ne] using yes

theorem noThreeDemandFiberClause {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) (K : LinClause Cell)
    (valid : ∀ x, board x → (∀ n, served x (r n)) → LinClauseSat x K) :
    ¬ (∀ x, LinEqSat x (f,b) → ¬ LinClauseSat x K) := by
  obtain ⟨x,bx,rows,hf⟩ := threeDemandFiber h b r
  exact fun bad => bad x hf (valid x bx rows)


theorem threeRowsSpan (K : LinClause Cell) (r : Fin 3 → Fin 5)
    {z : Cell → Bool} (hz : LinClauseSat z K) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinClauseSat x K := by
  obtain ⟨⟨f,b⟩,mem,eq⟩ := hz
  by_cases nonempty : f.Nonempty
  · obtain ⟨x,bx,rows,hit⟩ := threeDemandFiber nonempty b r
    exact ⟨x,bx,rows,(f,b),mem,hit⟩
  · have fe : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst f
    obtain ⟨x,bx,rows,_⟩ := threeDemandFiber
      (f := {((0 : Fin 5),(0 : Fin 4))}) (by simp) false r
    refine ⟨x,bx,rows,(∅,b),mem,?_⟩
    unfold LinEqSat at eq ⊢
    simpa only [Finset.filter_empty] using eq

theorem noProperDominator (K : LinClause Cell) (r : Fin 3 → Fin 5)
    (onlyPaths : ∀ x, board x → (∀ n, served x (r n)) → ¬ LinClauseSat x K) :
    ∀ z, ¬ LinClauseSat z K := by
  intro z hit
  obtain ⟨x,bx,rows,sat⟩ := threeRowsSpan K r hit
  exact onlyPaths x bx rows sat

end Lpcx178ThreeDemands
