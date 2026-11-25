import Mathlib
import PEqualNP.Outside.L_meta_7684

namespace Load2585
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

inductive Pool (X : Type*) [DecidableEq X] : Nat → Finset (Finset X) → Prop where
  | raw {S} (h : ∀ A∈S, A.card ≤ 1) : Pool X 0 S
  | join {k S} (pr : Pool X k S) {A B : Finset X} (ha : A∈S) (hb : B∈S) :
      Pool X (k+1) (insert (A∪B) S)

def edges (R : Finset (Y × Finset X)) : Finset (Y × X) :=
  R.biUnion fun z => z.2.image (fun x => (z.1,x))

theorem edge_mem (R : Finset (Y × Finset X)) (y : Y) (x : X) :
    (y,x) ∈ edges R ↔ ∃ A, (y,A)∈R ∧ x∈A := by
  constructor
  · intro h
    obtain ⟨⟨t,A⟩,ha,r⟩ := Finset.mem_biUnion.mp h
    obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp r
    cases eq
    exact ⟨A,ha,hs⟩
  · rintro ⟨A,ha,hx⟩
    exact Finset.mem_biUnion.mpr ⟨(y,A),ha,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩

theorem at_most_one_union {A B : Finset X} (small : (A∪B).card ≤ 1) :
    A∪B=A ∨ A∪B=B := by
  by_cases non : A.Nonempty
  · left
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_union_left : A⊆A∪B)
      (small.trans (Finset.card_pos.mpr non))).symm
  · right
    have h := Finset.not_nonempty_iff_eq_empty.mp non
    simp [h]

theorem price (N : Y → Finset X)
    (linear : ∀ i j, i≠j → (N i∩N j).card ≤ 1)
    {k : Nat} {S : Finset (Finset X)} (program : Pool X k S) (R : Finset (Y × Finset X))
    (ready : ∀ z∈R,z.2∈S) (safe : ∀ z∈R,z.2⊆N z.1) :
    (edges R).card  ≤  R.card+k := by
  classical
  induction program generalizing R with
  | raw h =>
    calc
      _  ≤  ∑ z∈R, (z.2.image (fun x => (z.1,x))).card := Finset.card_biUnion_le
      _  ≤  ∑ _z∈R, 1 := Finset.sum_le_sum (fun z hz => Finset.card_image_le.trans (h _ (ready z hz)))
      _ = _ := by simp
  | @join k S pr A B ha hb ih =>
    by_cases seen : A∪B∈S
    · have bound := ih R (fun z hz => (Finset.mem_insert.mp (ready z hz)).elim (fun e => by rw [e]; exact seen) id) safe
      omega
    by_cases used : ∃ y, (y,A∪B)∈R
    · obtain ⟨v,hv⟩ := used
      have large : 1 < (A∪B).card := by
        by_contra! small
        rcases at_most_one_union small with eq|eq
        · exact seen (by rw [eq]; exact ha)
        · exact seen (by rw [eq]; exact hb)
      have unique (y : Y) (hy : (y,A∪B)∈R) : y=v := by
        by_contra ne
        have sub : A∪B⊆N y∩N v := Finset.subset_inter (safe _ hy) (safe _ hv)
        have z := (Finset.card_le_card sub).trans (linear y v ne)
        omega
      let T := R.erase (v,A∪B)
      let Q := insert (v,A) (insert (v,B) T)
      have qr : ∀ z∈Q, z.2∈S := by
        rintro ⟨y,Z⟩ hz
        rcases Finset.mem_insert.mp hz with eq|hz
        · cases eq; exact ha
        rcases Finset.mem_insert.mp hz with eq|hz
        · cases eq; exact hb
        obtain ⟨ne,hr⟩ := Finset.mem_erase.mp hz
        rcases Finset.mem_insert.mp (ready _ hr) with eq|old
        · change Z=A∪B at eq
          subst Z
          exact False.elim (ne (by rw [unique y hr]))
        · exact old
      have qs : ∀ z∈Q,z.2⊆N z.1 := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact Finset.subset_union_left.trans (safe _ hv)
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact Finset.subset_union_right.trans (safe _ hv)
        exact safe _ (Finset.mem_erase.mp hz).2
      have sub : edges R⊆edges Q := by
        rintro ⟨y,x⟩ hx
        obtain ⟨Z,hZ,xZ⟩ := (edge_mem R y x).mp hx
        apply (edge_mem Q y x).mpr
        by_cases he : (y,Z)=(v,A∪B)
        · cases he
          rcases Finset.mem_union.mp xZ with xA|xB
          · exact ⟨A,Finset.mem_insert_self ..,xA⟩
          · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),xB⟩
        · exact ⟨Z,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hZ⟩)),xZ⟩
      have hq := (Finset.card_le_card sub).trans (ih Q qr qs)
      have h1 := Finset.card_insert_le (v,A) (insert (v,B) T)
      have h2 := Finset.card_insert_le (v,B) T
      have h3 : T.card+1=R.card := Finset.card_erase_add_one hv
      change (edges R).card  ≤  (insert (v,A) (insert (v,B) T)).card+k at hq
      omega
    · have rb : ∀ z∈R,z.2∈S := by
        rintro ⟨y,Z⟩ h
        rcases Finset.mem_insert.mp (ready _ h) with eq|old
        · change Z=A∪B at eq
          exact False.elim (used ⟨y,eq ▸ h⟩)
        · exact old
      have base := ih R rb safe
      omega

end Load2585
namespace Double2585
open Load2585
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

structure Block (P L : Type*) where
  point : P
  line : L
  points : Finset P
  lines : Finset L
deriving DecidableEq

variable {p l : ℕ}
local notation "P" => Fin p
local notation "L" => Fin l

def pointRoots (sl : Finset (L × Finset P)) (d : Finset (Block P L)) :=
  sl ∪ d.image (fun b => (b.line,b.points))
def lineRoots (sp : Finset (P × Finset L)) (d : Finset (Block P L)) :=
  sp ∪ d.image (fun b => (b.point,b.lines))
def centers (d : Finset (Block P L)) := d.image (fun b => (b.point,b.line))
def pointEdges (r : Finset (L×Finset P)) : Finset (P×L) :=
  (edges r).image Prod.swap

theorem pointEdge_mem (r : Finset (L×Finset P)) (i : P) (j : L) :
    (i,j)∈pointEdges r ↔ ∃ S,(j,S)∈r ∧ i∈S := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,r',e⟩ := Finset.mem_image.mp h
    cases e
    exact (edge_mem r a b).mp r'
  · intro h
    exact Finset.mem_image.mpr ⟨(j,i),(edge_mem r j i).mpr h,rfl⟩

def graph (sp : Finset (P×Finset L)) (sl : Finset (L×Finset P)) (d : Finset (Block P L)) :
    Finset (P×L) := pointEdges (pointRoots sl d) ∪ edges (lineRoots sp d)

theorem normalize (sp : Finset (P×Finset L)) (sl : Finset (L×Finset P)) (d : Finset (Block P L))
    (incident : ∀ b∈d,b.point∈b.points ∧ b.line∈b.lines)
    (square : ∀ a a' b b',a≠a' → b≠b' →
      ¬ ((a,b)∈graph sp sl d ∧ (a,b')∈graph sp sl d ∧ (a',b)∈graph sp sl d ∧ (a',b')∈graph sp sl d))
    {k t : Nat} {SP : Finset (Finset P)} {SL : Finset (Finset L)}
    (pb : Pool P k SP) (lb : Pool L t SL)
    (pa : ∀ z∈pointRoots sl d,z.2∈SP) (la : ∀ z∈lineRoots sp d,z.2∈SL) (size : Nat)
    (cost : k+t+2*(sp.card+sl.card+d.card)+(centers d).card  ≤  size+1) :
    ∃ D : Circuit,IsAO2 (p+l) D ∧
      (∀ x,circuitFun (p+l) D x = decide (∃ a b, (a,b)∈graph sp sl d ∧
        x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)) ∧
      D.size ≤ size ∧ IsReadK (p+l) D 1 := by
  classical
  let E := graph sp sl d
  let RP := pointRoots sl d
  let RL := lineRoots sp d
  let EP := pointEdges RP
  let EL := edges RL
  let K := centers d
  let A := (sp.image Prod.fst) ∪ K.image Prod.fst
  let M := (sl.image Prod.fst) ∪ K.image Prod.snd
  let NP (j : L) := Finset.univ.filter fun i : P => (i,j)∈E
  let NL (i : P) := Finset.univ.filter fun j : L => (i,j)∈E
  have npl (j j' : L) (ne : j≠j') : (NP j∩NP j').card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha a' ha'
    by_contra neq
    simp only [NP,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at ha ha'
    exact square a a' j j' neq ne ⟨ha.1,ha.2,ha'.1,ha'.2⟩
  have nll (i i' : P) (ne : i≠i') : (NL i∩NL i').card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    by_contra neq
    simp only [NL,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hb hb'
    exact square i i' b b' ne neq ⟨hb.1,hb'.1,hb.2,hb'.2⟩
  have pSafe (z : L×Finset P) (hz : z∈RP) : z.2⊆NP z.1 := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_union_left _
      ((pointEdge_mem RP i z.1).mpr ⟨z.2,hz,hi⟩)⟩
  have lSafe (z : P×Finset L) (hz : z∈RL) : z.2⊆NL z.1 := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_union_right _
      ((edge_mem RL z.1 j).mpr ⟨z.2,hz,hj⟩)⟩
  have ep : EP.card ≤ RP.card+k := Finset.card_image_le.trans (price NP npl pb RP pa pSafe)
  have el : EL.card ≤ RL.card+t := price NL nll lb RL la lSafe
  have overlap : K⊆EP∩EL := by
    intro e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hp,hl⟩ := incident b hb
    exact Finset.mem_inter.mpr ⟨(pointEdge_mem RP b.point b.line).mpr ⟨b.points,
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb),hp⟩,
      (edge_mem RL b.point b.line).mpr ⟨b.lines,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb),hl⟩⟩
  have cover : ∀ e∈E,e.1∈A ∨ e.2∈M := by
    rintro ⟨a,b⟩ he
    rcases Finset.mem_union.mp he with hp|hl
    · right
      obtain ⟨U,hU,_⟩ := (pointEdge_mem RP a b).mp hp
      rcases Finset.mem_union.mp hU with hs|hd
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hs)
      · obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp hd
        have eqb := congrArg Prod.fst eq
        change z.line=b at eqb
        rw [←eqb]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(z.point,z.line),
          Finset.mem_image_of_mem (fun z : Block P L => (z.point,z.line)) hz,rfl⟩)
    · left
      obtain ⟨U,hU,_⟩ := (edge_mem RL a b).mp hl
      rcases Finset.mem_union.mp hU with hs|hd
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hs)
      · obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp hd
        have eqa := congrArg Prod.fst eq
        change z.point=a at eqa
        rw [←eqa]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(z.point,z.line),
          Finset.mem_image_of_mem (fun z : Block P L => (z.point,z.line)) hz,rfl⟩)
  have ar : A.card ≤ sp.card+K.card := (Finset.card_union_le ..).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  have mr : M.card ≤ sl.card+K.card := (Finset.card_union_le ..).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  have pr : RP.card ≤ sl.card+d.card := (Finset.card_union_le ..).trans
    (Nat.add_le_add_left Finset.card_image_le _)
  have lr : RL.card ≤ sp.card+d.card := (Finset.card_union_le ..).trans
    (Nat.add_le_add_left Finset.card_image_le _)
  have hcard := Finset.card_union_add_card_inter EP EL
  have hc := Finset.card_le_card overlap
  change E.card+(EP∩EL).card=EP.card+EL.card at hcard
  change k+t+2*(sp.card+sl.card+d.card)+K.card ≤ size+1 at cost
  have bud : E.card+A.card+M.card ≤ size+1 := by omega
  obtain ⟨D,ao,sz,computes,r⟩ := PEqualNP.Outside.L_meta_7684 p l E A M cover
  exact ⟨D,ao,computes,by omega,r⟩

end Double2585
