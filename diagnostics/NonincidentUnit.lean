import PEqualNP.Defs
namespace Lpcx178MixedOwner
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

-- Missing row 0 and the collision of rows 1 and 2 in hole 0 are the only permitted faults.
def noOtherFaults (x : Cell → Bool) : Prop :=
    (∀ r : Fin 5, r ≠ 0 → ∃ h : Fin 4, x (r,h) = true) ∧
    ∀ (r s : Fin 5) (h : Fin 4), r ≠ s → x (r,h) = true → x (s,h) = true →
      h = 0 ∧ ((r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1))

def first (k : Fin 4) : Fin 4 := if k = 1 then 2 else 1
def second (k : Fin 4) : Fin 4 := if k = 3 then 2 else 3
def placement (k : Fin 4) (v : Cell) : Bool :=
  decide ((v.2 = 0 ∧ (v.1 = 1 ∨ v.1 = 2)) ∨ v = (3,first k) ∨ v = (4,second k))

theorem placements : ∀ (k : Fin 4) (r : Fin 5), k ≠ 0 →
    (∀ t : Fin 5, t ≠ 0 → ∃ h : Fin 4, placement k (t,h) = true) ∧
    (∀ (i j : Fin 5) (h : Fin 4), i ≠ j → placement k (i,h) = true →
      placement k (j,h) = true → h = 0 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))) ∧
    (∀ t : Fin 5, t ≠ 0 → ∃ h : Fin 4, flip (placement k) (r,k) (t,h) = true) ∧
    (∀ (i j : Fin 5) (h : Fin 4), i ≠ j → flip (placement k) (r,k) (i,h) = true →
      flip (placement k) (r,k) (j,h) = true → h = 0 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))) := by
  decide +kernel

theorem columnOnly (K : LinClause Cell) (bottleneck : ∀ x, noOtherFaults x → ¬ LinClauseSat x K)
    {q : LinEq Cell} (mem : q ∈ K) {v : Cell} (support : v ∈ q.1) : v.2 = 0 := by
  by_contra off
  obtain ⟨r,k⟩ := v
  obtain ⟨u,w,u',w'⟩ := placements k r off
  have z : ¬ LinEqSat (placement k) q := fun sat =>
    bottleneck _ ⟨u,w⟩ ⟨q,mem,sat⟩
  obtain ⟨f,b⟩ := q
  have yes := (opposite (x := placement k) support b).mpr z
  exact bottleneck _ ⟨u',w'⟩ ⟨(f,b),mem,yes⟩


-- Four permutations of the nonmissing rows and one board with the named collision.
def sample (a : Fin 5) (v : Cell) : Bool :=
  if a=4 then decide (v=(1,0) ∨ v=(2,0) ∨ v=(3,1) ∨ v=(4,2))
  else decide (v.1.val ≠ 0 ∧ v.2.val = (v.1.val-1 + a.val)%4)
def goodSample (a : Fin 5) : Bool :=
  (List.finRange 5).all (fun r => r==0 || (List.finRange 4).any (fun h => sample a (r,h))) &&
  (List.finRange 5).all (fun r => (List.finRange 5).all (fun s => (List.finRange 4).all (fun h =>
    r==s || !(sample a (r,h) && sample a (s,h)) ||
      (h==0 && ((r==1 && s==2) || (r==2 && s==1))))))
theorem samplesGood : ∀ a, noOtherFaults (sample a) := by
  intro a
  have num : ∀ i : Fin 5,
      (∀ r : Fin 5, r≠0 → ∃ h : Fin 4, sample i (r,h) = true) ∧
      ∀ r s : Fin 5, ∀ h : Fin 4, r≠s → sample i (r,h)=true → sample i (s,h)=true →
      h=0 ∧ ((r=1 ∧ s=2) ∨ (r=2 ∧ s=1)) := by decide +kernel
  exact num a

def col (S : Finset (Fin 5)) : Finset Cell := S.image fun r => (r,0)
theorem fiber : ∀ (S : Finset (Fin 5)) (b : Bool), (∃ r∈S, r≠0) →
    ∃ k : Fin 5, (Odd (((col S).filter (fun v => sample k v=true)).card) ↔ b=true) := by decide +kernel

theorem singletonSupport (K : LinClause Cell)
    (must : ∀ x, noOtherFaults x → ¬LinClauseSat x K) {q : LinEq Cell} (mem : q∈K) :
    ∀ v∈q.1, v=((0 : Fin 5),(0 : Fin 4)) := by
  let S := Finset.univ.filter fun r : Fin 5 => (r,(0 : Fin 4)) ∈ q.1
  have rep : q.1 = col S := by
    ext v
    constructor
    · intro hv
      obtain ⟨r,h⟩ := v
      have hz := columnOnly K must mem hv
      change h=0 at hz
      subst h
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
    · intro hv
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hr).2
  intro v hv
  have vc : v ∈ col S := rep ▸ hv
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp vc
  by_contra ne
  have nz : r≠0 := fun eq => ne (by simp [eq])
  obtain ⟨k,hk⟩ := fiber S q.2 ⟨r,hr,nz⟩
  have sat : LinEqSat (sample k) q := by
    unfold LinEqSat
    rw [rep]
    exact hk
  exact must _ (samplesGood k) ⟨q,mem,sat⟩

theorem forcedUnit (K : LinClause Cell) (must : ∀ x, noOtherFaults x → ¬LinClauseSat x K)
    {x : Cell → Bool} (off : x (0,0)=false) : ¬ LinClauseSat x K := by
  rintro ⟨q,hq,yes⟩
  have none : ∀ v∈q.1, x v=false := by
    intro v hv
    rw [singletonSupport K must hq v hv]
    exact off
  have other : ∀ v∈q.1, sample 0 v=false := by
    intro v hv
    rw [singletonSupport K must hq v hv]
    decide
  have vals (a : Cell → Bool) (hz : ∀ v∈q.1,a v=false) :
      q.1.filter (fun v => a v=true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v m
    obtain ⟨hv,on⟩ := Finset.mem_filter.mp m
    rw [hz v hv] at on
    contradiction
  apply must _ (samplesGood 0)
  refine ⟨q,hq,?_⟩
  unfold LinEqSat at yes ⊢
  simpa only [vals x none,vals (sample 0) other] using yes
end Lpcx178MixedOwner
