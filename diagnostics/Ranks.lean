import PEqualNP.Defs
open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Ranks
variable {V : Type} [Fintype V] [DecidableEq V]
abbrev L (V : Type) := Literal V
abbrev C (V : Type) := Clause V
def conflictAt (G : Set (C V)) (s : Finset (L V)) :=
  ∃d∈G, ∀l∈d, negLit l∈s
def Unit (G : Set (C V)) (s : Finset (L V)) (l : L V) :=
  ∃d∈G, l∈d ∧ ∀k∈d, k≠l → negLit k∈s
inductive Trace (G : Set (C V)) : Finset (L V) → Nat → Prop
  | stop {s} (bad : conflictAt G s) : Trace G s 0
  | learn {s l n} (first : l∉s) (opposite : negLit l∉s) (reason : Unit G s l)
      (rest : Trace G (insert l s) n) : Trace G s (n+1)
def cells (s : Finset (L V)) : Finset V := s.image Prod.fst

theorem room {s : Finset (L V)} {l : L V} (fresh : l∉s) (neg : negLit l∉s) :
    l.1∉cells s := by
  rintro hl
  obtain ⟨⟨v,b⟩,h,m⟩ := Finset.mem_image.mp hl
  rcases l with ⟨u,a⟩
  change v=u at m
  subst v
  cases a <;> cases b <;> first | exact fresh h | exact neg h

theorem traceBound {G : Set (C V)} {s : Finset (L V)} {n} (t : Trace G s n) :
    n+(cells s).card≤Fintype.card V := by
  induction t with
  | stop _ => simpa using Finset.card_le_univ (cells _)
  | @learn s l n free neg reason rest ih =>
    have newcell := room free neg
    have more : (cells (insert l s)).card=(cells s).card+1 := by
      change ((insert l s).image Prod.fst).card=_
      rw [Finset.image_insert,Finset.card_insert_of_notMem newcell]
    rw [more] at ih
    omega

theorem hasTrace {G : Set (C V)} {A : Set (L V)}
    (failed : ∃d∈G, ∀l∈d, UPForces G A (negLit l)) (s : Finset (L V))
    (hyp : ∀l∈A,l∈s) : ∃n, Trace G s n := by
  classical
  generalize eq : Fintype.card V - (cells s).card = potential
  induction potential using Nat.strong_induction_on generalizing s with
  | h potential ih =>
    by_cases bad : conflictAt G s
    · exact ⟨0,.stop bad⟩
    have pick : ∃l : L V, l∉s ∧ Unit G s l := by
      by_contra! absent
      have all {l : L V} (forced : UPForces G A l) : l∈s := by
        induction forced with
        | hyp hm => exact hyp _ hm
        | @unit d p hd member rest prev =>
          by_contra no
          exact absent p no ⟨d,hd,member,prev⟩
      obtain ⟨d,hd,out⟩ := failed
      exact bad ⟨d,hd,fun k hk => all (out k hk)⟩
    obtain ⟨l,fresh,why⟩ := pick
    have noOpp : negLit l∉s := by
      intro known
      obtain ⟨d,hd,mem,rest⟩ := why
      apply bad
      refine ⟨d,hd,?_⟩
      intro k hk
      by_cases eq : k=l
      · simpa [eq] using known
      · exact rest k hk eq
    have freshCell := room fresh noOpp
    have next : (cells (insert l s)).card=(cells s).card+1 := by
      change ((insert l s).image Prod.fst).card=_
      rw [Finset.image_insert, Finset.card_insert_of_notMem freshCell]
    have available : (cells (insert l s)).card≤Fintype.card V := Finset.card_le_univ _
    have small : Fintype.card V - (cells (insert l s)).card < potential := by omega
    obtain ⟨n,rest⟩ := ih _ small (insert l s) (fun z hz => Finset.mem_insert_of_mem (hyp z hz)) rfl
    exact ⟨n+1,.learn fresh noOpp why rest⟩

theorem traceSound {G : Set (C V)} {A : Set (L V)} {s n} (trace : Trace G s n)
    (built : ∀l∈s, UPForces G A l) : ∃d∈G, ∀l∈d, UPForces G A (negLit l) := by
  induction trace with
  | stop bad =>
    obtain ⟨d,hd,dead⟩ := bad
    exact ⟨d,hd,fun z hz => built _ (dead z hz)⟩
  | @learn s l n free opp step rest ih =>
    obtain ⟨d,hd,ml,other⟩ := step
    have force : UPForces G A l := .unit hd ml (fun k hk neq => built _ (other k hk neq))
    apply ih
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|old
    · exact force
    · exact built z old

theorem rupRanked (G : Set (C V)) (c : C V) :
    IsRUP G c ↔ ∃n, n+(cells (c.image negLit)).card≤Fintype.card V ∧
      Trace G (c.image negLit) n := by
  constructor
  · intro ok
    obtain ⟨n,t⟩ := hasTrace ok (c.image negLit) (by
      rintro l ⟨k,hk,rfl⟩
      exact Finset.mem_image.mpr ⟨k,hk,rfl⟩)
    exact ⟨n,traceBound t,t⟩
  · rintro ⟨n,_,t⟩
    apply traceSound t
    intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    exact .hyp ⟨k,hk,rfl⟩
end PEqualNP.Outside.L_meta_9471.Ranks
