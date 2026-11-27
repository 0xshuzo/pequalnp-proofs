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


theorem resolutionSound {x : Cell → Bool} {C D R : LinClause Cell}
    (p : IsLinResolvent C D R) (c : LinClauseSat x C) (d : LinClauseSat x D) :
    LinClauseSat x R := by
  obtain ⟨f,_,_,rfl⟩ := p
  obtain ⟨u,hu,su⟩ := c
  obtain ⟨v,hv,sv⟩ := d
  by_cases e : u = (f,false)
  · by_cases e' : v = (f,true)
    · subst u
      subst v
      have impossible : false = true := su.mp (sv.mpr rfl)
      contradiction
    · exact ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e',hv⟩),sv⟩
  · exact ⟨u,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hu⟩),su⟩

theorem derivationSound {F : Set (LinClause Cell)} {π} {x : Cell → Bool}
    (d : IsLinDerivation F π) (init : ∀ C ∈ F, LinClauseSat x C) :
    ∀ C ∈ π, LinClauseSat x C := by
  induction d with
  | nil => simp
  | ax _ ax ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|old
    · exact init _ ax
    · exact ih _ old
  | res _ hC hD step ih =>
    intro R hr
    rcases List.mem_cons.mp hr with rfl|old
    · exact resolutionSound step (ih _ hC) (ih _ hD)
    · exact ih _ old
  | weak _ hc w ih =>
    intro D hd
    rcases List.mem_cons.mp hd with rfl|old
    · exact w _ (ih _ hc)
    · exact ih _ old

def row (p : Fin 5) : Clause Cell :=
  Finset.univ.image (fun h : Fin 4 => ((p,h),true))
def coll (p q : Fin 5) (h : Fin 4) : Clause Cell :=
  {((p,h),false),((q,h),false)}
def threeAxioms (r : Fin 3 → Fin 5) : Set (LinClause Cell) :=
  {K | (∃ n, K = linOfClause (row (r n))) ∨
       ∃ p q h, p ≠ q ∧ K = linOfClause (coll p q h)}

theorem litEq {x : Cell → Bool} (v : Cell) (b : Bool) (h : x v = b) :
    LinEqSat x ({v},b) := by
  cases b <;> simp [LinEqSat,h]

theorem axiomsTrue {x : Cell → Bool} (r : Fin 3 → Fin 5) (xb : board x)
    (rows : ∀ n, served x (r n)) : ∀ A ∈ threeAxioms r, LinClauseSat x A := by
  intro A ha
  rcases ha with ⟨n,rfl⟩|⟨p,q,h,pq,rfl⟩
  · obtain ⟨h,yes⟩ := rows n
    refine ⟨_,Finset.mem_image.mpr ⟨((r n,h),true),?_,rfl⟩,litEq _ true yes⟩
    exact Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩
  · have no : x (p,h) = false ∨ x (q,h) = false := by
      by_cases hp : x (p,h) = true
      · right
        cases hq : x (q,h) with
        | false => rfl
        | true => exact (pq (congrArg Prod.fst (xb (p,h) (q,h) rfl hp hq))).elim
      · left
        cases h : x (p,h) <;> simp_all
    rcases no with no|no
    · exact ⟨_,Finset.mem_image.mpr ⟨((p,h),false),by simp [coll],rfl⟩,litEq _ false no⟩
    · exact ⟨_,Finset.mem_image.mpr ⟨((q,h),false),by simp [coll],rfl⟩,litEq _ false no⟩

theorem physicalRowBound {f : Finset Cell} (hf : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) {π} (d : IsLinDerivation (threeAxioms r) π)
    {K : LinClause Cell} (mem : K ∈ π) :
    ¬ (∀ x, LinEqSat x (f,b) → ¬ LinClauseSat x K) := by
  apply noThreeDemandFiberClause hf b r K
  intro x xb rows
  exact derivationSound d (axiomsTrue r xb rows) K mem

end Lpcx178ThreeDemands
