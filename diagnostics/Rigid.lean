import PEqualNP.Defs

namespace PCX164.Rigid

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def NegsIn (S : Finset V) (R : C) : Prop :=
  ∀ v : V, (v, false) ∈ R → v ∈ S

def Hits (S : Finset V) (R : C) : Prop :=
  ∃ v : V, (v, false) ∈ R ∧ v ∈ S

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

def Controls (π : List C) (U : Finset C) (S : Finset V) : Prop :=
  ∀ (U' : Finset C) (S' : Finset V), U ⊆ U' → S ⊆ S' →
  ∀ a : V → Bool, (∀ B ∈ PHP 5 4, ¬ Coll B → ClauseSat a B) →
    (∀ B ∈ U', Coll B → Hits S' B → ClauseSat a B) →
    ∀ R ∈ π, ¬ Coll R → NegsIn S' R → ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

abbrev Edge := Fin 40
abbrev Sample := Fin 6
def ends : Array Nat := #[8,8,8,8,16,16,16,16,24,24,24,24,32,32,32,32,17,17,17,17,25,25,25,25,33,33,33,33,26,26,26,26,34,34,34,34,35,35,35,35]
def lo (e : Edge) : Row := Fin.ofNat 5 (ends[e.val]!%8)
def hi (e : Edge) : Row := Fin.ofNat 5 (ends[e.val]!/8)
def hole (e : Edge) : Hole := Fin.ofNat 4 (e.val%4)
def first (e : Edge) : V := (lo e,hole e)
def second (e : Edge) : V := (hi e,hole e)
def raw (e : Edge) : C := {(first e,false),(second e,false)}
def samples : Array Nat := #[541201,295441,533521,164881,272401,149521,540962,295202,529442,99362,268322,84002,532804,164164,528964,98884,137284,75844,270728,147848,266888,82568,136328,74888,540961,295201,532801,164161,270721,147841,541202,295442,528962,98882,266882,82562,533524,164884,529444,99364,136324,74884,272408,149528,268328,84008,137288,75848,529441,268321,528961,137281,266881,136321,533522,272402,532802,75842,270722,74882,541204,149524,540964,84004,147844,82564,295448,164888,295208,99368,164168,98888,99361,84001,98881,75841,82561,74881,164882,149522,164162,137282,147842,136322,295444,272404,295204,268324,270724,266884,541208,533528,540968,529448,532808,528968,540946,295186,532756,164116,270616,147736,541217,295457,528932,98852,266792,82472,533569,164929,529474,99394,136264,74824,272513,149633,268418,84098,137348,75908,529426,268306,528916,137236,266776,136216,533537,272417,532772,75812,270632,74792,541249,149569,540994,84034,147784,82504,295553,164993,295298,99458,164228,98948,99346,83986,98836,75796,82456,74776,164897,149537,164132,137252,147752,136232,295489,272449,295234,268354,270664,266824,541313,533633,541058,529538,532868,529028,528706,266626,528676,135556,266536,135496,533057,270977,533012,74372,270872,74312,541729,148609,541714,83074,148504,82984,296993,165953,296978,100418,165908,100388,98626,82306,98596,74116,82216,74056,164417,148097,164372,135812,147992,135752,295969,271489,295954,267394,271384,267304,542753,534593,542738,530498,534548,530468,71746,70786,71716,70276,70696,70216,141377,140417,141332,139652,140312,139592,280609,279169,280594,278914,279064,278824,558113,557633,558098,557378,557588,557348]
def model (e : Edge) (s : Sample) (v : V) : Bool :=
  samples[6*e.val+s.val]!.testBit (4*v.1.val+v.2.val)
theorem distinct : ∀ e, first e ≠ second e := by decide +kernel
theorem everyRow : ∀ e s (r : Row), ∃ h : Hole, model e s (r,h) = true := by decide +kernel
theorem oneCollision : ∀ e s (r q : Row) (h : Hole), r≠q →
    model e s (r,h)=true → model e s (q,h)=true →
    ((r,h)=first e ∧ (q,h)=second e) ∨ ((q,h)=first e ∧ (r,h)=second e) := by decide +kernel
theorem commonTrue : ∀ e v, (∀ s, model e s v=true) ↔ v=first e ∨ v=second e := by decide +kernel
theorem commonFalse : ∀ e (v : V), (∀ s, model e s v=false) ↔
    ((v.1=lo e ∨ v.1=hi e) ∧ v.2≠hole e) ∨ (v.1≠lo e ∧ v.1≠hi e ∧ v.2=hole e) := by decide +kernel

theorem isolates (e : Edge) (s : Sample) {Q : C} (ax : Q ∈ PHP 5 4) (other : Q ≠ raw e) :
    ClauseSat (model e s) Q := by
  rcases ax with ⟨r,rfl⟩ | ⟨r,q,h,rq,rfl⟩
  · obtain ⟨h,hit⟩ := everyRow e s r
    exact ⟨((r,h),true),Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩,hit⟩
  · by_cases a : model e s (r,h)=true
    · by_cases b : model e s (q,h)=true
      · exfalso
        apply other
        rcases oneCollision e s r q h rq a b with ⟨u,v⟩ | ⟨v,u⟩
        · simp [raw,u,v]
        · simp [raw,u,v,Finset.pair_comm]
      · exact ⟨((q,h),false),by simp,Bool.eq_false_iff.mpr b⟩
    · exact ⟨((r,h),false),by simp,Bool.eq_false_iff.mpr a⟩

inductive Trace (target : C) : List C → List C → Prop where
  | nil : Trace target [] []
  | ax {π reads R} (tail : Trace target π reads) (member : R∈PHP 5 4) : Trace target (R::π) reads
  | res {π reads P N R} (tail : Trace target π reads) (left : P∈π) (right : N∈π)
      (step : IsResolvent P N R) :
      Trace target (R::π) (if N=target then R::reads else reads)

theorem tracked (target : C) {π : List C} (proof : IsDerivation (PHP 5 4) π) :
    ∃ reads, Trace target π reads := by
  induction proof with
  | nil => exact ⟨[],.nil⟩
  | ax _ a ih => obtain ⟨reads,t⟩ := ih; exact ⟨_,.ax t a⟩
  | res _ l r st ih => obtain ⟨reads,t⟩ := ih; exact ⟨_,.res t l r st⟩

theorem inherited (e : Edge) (s : Sample) {π reads} (tr : Trace (raw e) π reads) :
    (∀ Q∈reads, ClauseSat (model e s) Q) → ∀ Q∈π, Q≠raw e → ClauseSat (model e s) Q := by
  induction tr with
  | nil => simp
  | @ax π reads R tail member ih =>
    intro ok Q mem dif
    rcases List.mem_cons.mp mem with rfl | old
    · exact isolates e s member dif
    · exact ih ok Q old dif
  | @res π reads P N R tail left right step ih =>
    intro ok
    have keep : ∀ Q∈reads, ClauseSat (model e s) Q := by
      intro Q h
      by_cases hit : N=raw e
      · exact ok Q (by simp [hit,h])
      · exact ok Q (by simpa [hit] using h)
    intro Q mem dif
    rcases List.mem_cons.mp mem with rfl | old
    · by_cases hit : N=raw e
      · exact ok Q (by simp [hit])
      · obtain ⟨v,pos,neg,eq⟩ := step
        have diff : P ≠ raw e := by
          intro he
          simp [he,raw] at pos
        exact satResolve eq (ih keep P left diff) (ih keep N right hit)
    · exact ih keep Q old dif

theorem uniqueBad {π : List C} {e : Edge} {R : C} (tr : Trace (raw e) π [R])
    (finish : (∅:C)∈π) (s : Sample) : ¬ClauseSat (model e s) R := by
  intro sat
  have all := inherited e s tr (by simpa using sat) (∅:C) finish (by simp [raw])
  simpa [ClauseSat] using all

theorem negativeEndpoint {π : List C} {e : Edge} {R : C} (tr : Trace (raw e) π [R])
    (finish : (∅:C)∈π) {w : V} (mem : (w,false)∈R) : w=first e ∨ w=second e := by
  apply (commonTrue e w).mp
  intro s
  cases h : model e s w with
  | false => exact False.elim (uniqueBad tr finish s ⟨(w,false),mem,h⟩)
  | true => rfl

theorem positiveCross {π : List C} {e : Edge} {R : C} (tr : Trace (raw e) π [R])
    (finish : (∅:C)∈π) {w : V} (mem : (w,true)∈R) :
    ((w.1=lo e ∨ w.1=hi e) ∧ w.2≠hole e) ∨ (w.1≠lo e ∧ w.1≠hi e ∧ w.2=hole e) := by
  apply (commonFalse e w).mp
  intro s
  cases h : model e s w with
  | false => rfl
  | true => exact False.elim (uniqueBad tr finish s ⟨(w,true),mem,h⟩)

theorem fixedColumn {π : List C} {e f : Edge} {P R T : C} (et : Trace (raw e) π [R])
    (ft : Trace (raw f) π [T]) (finish : (∅:C)∈π)
    (s1 : IsResolvent P (raw e) R) (s2 : IsResolvent R (raw f) T) :
    hole e = hole f := by
  obtain ⟨x,hx,nx,er⟩ := s1
  obtain ⟨y,hy,ny,fr⟩ := s2
  obtain ⟨z,ne,hz⟩ : ∃ z : V, z≠x ∧ (z,false)∈raw e := by
    rcases (show x=first e ∨ x=second e by simpa [raw] using nx) with rfl | rfl
    · exact ⟨second e,(distinct e).symm,by simp [raw]⟩
    · exact ⟨first e,distinct e,by simp [raw]⟩
  have negR : (z,false)∈R := by
    rw [er]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun eq => ne (congrArg Prod.fst eq),hz⟩)
  have negT : (z,false)∈T := by
    rw [fr]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,negR⟩)
  have col (d : Edge) (w : V) (h : w=first d ∨ w=second d) : w.2=hole d := by
    rcases h with rfl|rfl <;> rfl
  exact (col e z (negativeEndpoint et finish negR)).symm.trans (col f z (negativeEndpoint ft finish negT))

end PCX164.Rigid
