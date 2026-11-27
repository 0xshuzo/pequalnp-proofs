import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_177.Colors
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
def red (p : Fin 3) : Fin 5 := ⟨p.val+2,by omega⟩
def mark (h : Fin 4) : LinEq Cell := ({(0,h),(1,h)},false)
def neg (p : Fin 3) (h : Fin 4) : LinClause Cell := {({(red p,h)},false),mark h}

def badPoint (p : Fin 3) (h : Fin 4) (v : Cell) : Bool :=
  decide (v.2=h ∧ (v.1=0 ∨ v.1=red p))

def checks (x : Cell→Bool) (C : LinClause Cell) : Bool :=
  decide (∃q∈C,(Odd (q.1.filter (fun t => x t=true)).card ↔ q.2=true))
theorem checks_correct {x C} : checks x C=true ↔ LinClauseSat x C := by
  unfold checks LinClauseSat LinEqSat
  exact decide_eq_true_iff

theorem coordinates : ∀ (p : Fin 3) (h : Fin 4),
    checks (badPoint p h) (neg p h)=false ∧
    ∀ v : Cell,v.2≠h → checks (flip (badPoint p h) v) (neg p h)=false := by decide +kernel

def WeakFrom (U : LinClause Cell) (h : Fin 4) :=
  ∃p,∀x,LinClauseSat x U → LinClauseSat x (neg p h)
def ResFrom (U : LinClause Cell) (h : Fin 4) :=
  mark h∈U ∧ ∃ (p : Fin 3) (q : LinEq Cell),U.erase q ⊆ neg p h

theorem coordinatesOnly {U : LinClause Cell} {h : Fin 4} (w : WeakFrom U h)
    {q : LinEq Cell} (hq : q∈U) {v : Cell} (hv : v∈q.1) : v.2=h := by
  obtain ⟨p,imp⟩ := w
  by_contra ne
  let x := badPoint p h
  obtain ⟨no,flipno⟩ := coordinates p h
  have bad : ¬LinEqSat x q := by
    intro eq
    have yes := checks_correct.mpr (imp x ⟨q,hq,eq⟩)
    rw [no] at yes
    contradiction
  have flipped : LinEqSat (flip x v) q := (opposite hv q.2).mpr bad
  have yes := checks_correct.mpr (imp (flip x v) ⟨q,hq,flipped⟩)
  rw [flipno v ne] at yes
  contradiction

theorem weakUnique {U : LinClause Cell} (sat : ∃ x,LinClauseSat x U)
    {h k : Fin 4} (w : WeakFrom U h) (z : WeakFrom U k) : h=k := by
  obtain ⟨x,q,hq,yes⟩ := sat
  by_contra diff
  have empty : q.1=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact diff ((coordinatesOnly w hq hv).symm.trans (coordinatesOnly z hq hv))
  obtain ⟨p,imp⟩ := w
  have const : LinEqSat (badPoint p h) q := by
    unfold LinEqSat at yes ⊢
    simpa only [empty,Finset.filter_empty] using yes
  have no := (coordinates p h).1
  have good := checks_correct.mpr (imp (badPoint p h) ⟨q,hq,const⟩)
  rw [no] at good
  contradiction

theorem weakRes {U : LinClause Cell} {h k : Fin 4}
    (w : WeakFrom U h) (r : ResFrom U k) : k=h := by
  exact coordinatesOnly w r.1 (v:=(0,k)) (by simp [mark])

theorem distinctMarks : ∀i j : Fin 4,mark i=mark j → i=j := by decide +kernel
theorem markedNeg : ∀(p : Fin 3) (i j : Fin 4),mark i ∈ neg p j → i=j := by decide +kernel

theorem missing {U : LinClause Cell} (sat : ∃ x,LinClauseSat x U) :
    ¬∀h : Fin 4, WeakFrom U h ∨ ResFrom U h := by
  intro all
  by_cases anyWeak : ∃h,WeakFrom U h
  · obtain ⟨h,w⟩ := anyWeak
    have same (k : Fin 4) : k=h := by
      rcases all k with z|r
      · exact weakUnique sat z w
      · exact weakRes w r
    have bad : (0 : Fin 4)=1 := (same 0).trans (same 1).symm
    exact (by decide : (0 : Fin 4)≠1) bad
  · have source (h : Fin 4) : ResFrom U h := (all h).resolve_left (fun w=>anyWeak ⟨h,w⟩)
    obtain ⟨p,q,sub⟩ := (source 0).2
    have erase (j : Fin 4) (nz : j≠0) : mark j=q := by
      by_contra ne
      exact nz (markedNeg p j 0 (sub (Finset.mem_erase.mpr ⟨ne,(source j).1⟩)))
    have bad := distinctMarks 1 2 ((erase 1 (by decide)).trans (erase 2 (by decide)).symm)
    exact (by decide : (1 : Fin 4)≠2) bad
end PEqualNP.Outside.L_pcx_177.Colors
