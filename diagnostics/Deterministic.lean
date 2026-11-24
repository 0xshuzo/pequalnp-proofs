import Mathlib

namespace Affine3576

def primeAt : Fin 9 → ℕ := ![2,3,5,7,11,13,17,19,23]

private theorem q0 {y z : ℤ} (h : y%2=z%2) : y-z=2*(y/2-z/2) := by omega
private theorem q1 {y z : ℤ} (h : y%3=z%3) : y-z=3*(y/3-z/3) := by omega
private theorem q2 {y z : ℤ} (h : y%5=z%5) : y-z=5*(y/5-z/5) := by omega
private theorem q3 {y z : ℤ} (h : y%7=z%7) : y-z=7*(y/7-z/7) := by omega
private theorem q4 {y z : ℤ} (h : y%11=z%11) : y-z=11*(y/11-z/11) := by omega
private theorem q5 {y z : ℤ} (h : y%13=z%13) : y-z=13*(y/13-z/13) := by omega
private theorem q6 {y z : ℤ} (h : y%17=z%17) : y-z=17*(y/17-z/17) := by omega
private theorem q7 {y z : ℤ} (h : y%19=z%19) : y-z=19*(y/19-z/19) := by omega
private theorem q8 {y z : ℤ} (h : y%23=z%23) : y-z=23*(y/23-z/23) := by omega

private theorem only_multiple {y z q : ℤ} (hy : 0≤y) (hz : 0≤z) (uy : y<50000000) (uz : z<50000000)
    (h : y-z=223092870*q) : y=z := by omega

set_option maxHeartbeats 800000 in
theorem small_separated {y z : ℤ} (hy : 0≤y) (hz : 0≤z) (uy : y<50000000) (uz : z<50000000)
    (eq : ∀ i, y%(primeAt i : ℤ) = z%(primeAt i : ℤ)) : y=z := by
  have e0 : y%2 = z%2 := eq (0 : Fin 9)
  have h0 := q0 e0
  have e1 : y%3 = z%3 := eq (1 : Fin 9)
  have h1 := q1 e1
  have e2 : y%5 = z%5 := eq (2 : Fin 9)
  have h2 := q2 e2
  have e3 : y%7 = z%7 := eq (3 : Fin 9)
  have h3 := q3 e3
  have e4 : y%11 = z%11 := eq (4 : Fin 9)
  have h4 := q4 e4
  have e5 : y%13 = z%13 := eq (5 : Fin 9)
  have h5 := q5 e5
  have e6 : y%17 = z%17 := eq (6 : Fin 9)
  have h6 := q6 e6
  have e7 : y%19 = z%19 := eq (7 : Fin 9)
  have h7 := q7 e7
  have e8 : y%23 = z%23 := eq (8 : Fin 9)
  have h8 := q8 e8
  let Q : ℤ := (-11)*(y/2-z/2) + (2)*(y/3-z/3) + (4)*(y/5-z/5) + (3)*(y/7-z/7) + (7)*(y/11-z/11) + (7)*(y/13-z/13) + (14)*(y/17-z/17) + (14)*(y/19-z/19) + (20)*(y/23-z/23)
  have h : y-z=223092870*Q := by
    dsimp only [Q]
    linear_combination (-1227010785)*h0 + (148728580)*h1 + (178474296)*h2 + (95611230)*h3 + (141968190)*h4 + (120126930)*h5 + (183723540)*h6 + (164384220)*h7 + (193993800)*h8
  exact only_multiple hy hz uy uz h

abbrev ModBlock := (i : Fin 9) × (Fin (primeAt i) × Fin (primeAt i))

theorem mod_count : Fintype.card ModBlock = 1556 := by
  change Fintype.card (Sigma fun i : Fin 9 => Fin (primeAt i) × Fin (primeAt i)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin]
  decide

abbrev Point := Fin 5000 × Fin 50000000
abbrev Line := Fin 5000 × Fin 25000000

def onLine (P : Point) (A : Line) : Prop := (P.2.val : ℤ) = (A.1.val : ℤ)*P.1.val + A.2.val

theorem four {P Q : Point} {A B : Line} (pA : onLine P A) (pB : onLine P B)
    (qA : onLine Q A) (qB : onLine Q B) : P=Q ∨ A=B := by
  obtain ⟨x,y⟩ := P
  obtain ⟨w,z⟩ := Q
  obtain ⟨a,b⟩ := A
  obtain ⟨c,e⟩ := B
  change (y.val : ℤ)=(a.val : ℤ)*x.val+b.val at pA
  change (y.val : ℤ)=(c.val : ℤ)*x.val+e.val at pB
  change (z.val : ℤ)=(a.val : ℤ)*w.val+b.val at qA
  change (z.val : ℤ)=(c.val : ℤ)*w.val+e.val at qB
  have prod : ((a.val : ℤ)-c.val)*((x.val : ℤ)-w.val)=0 := by
    linear_combination -pA + pB + qA - qB
  rcases mul_eq_zero.mp prod with ac|xw
  · right
    have ea : a=c := Fin.ext (by omega)
    subst c
    have eb : b=e := Fin.ext (by omega)
    rw [eb]
  · left
    have ex : x=w := Fin.ext (by omega)
    subst w
    have ey : y=z := Fin.ext (by omega)
    rw [ey]

noncomputable def incidentPoint (A : Line) (x : Fin 5000) : Point :=
  (x,⟨A.1.val*x.val+A.2.val,by
    have u : A.1.val*x.val ≤ 4999*4999 := Nat.mul_le_mul (by have := A.1.isLt; omega) (by have := x.isLt; omega)
    have v := A.2.isLt
    omega⟩)

theorem incident_correct (A : Line) (x : Fin 5000) : onLine (incidentPoint A x) A := by
  change ((A.1.val*x.val+A.2.val : ℕ) : ℤ) = (A.1.val : ℤ)*x.val + A.2.val
  simp only [Nat.cast_add,Nat.cast_mul]

theorem card_margin : (Fintype.card Point + Fintype.card Line + 2)*(1556+2) < Fintype.card (Line × Fin 5000) := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  decide

end Affine3576
namespace Affine3576

private theorem posPrime (i : Fin 9) : 0<primeAt i := by
  fin_cases i <;> decide

def res (z : ℕ) (i : Fin 9) : Fin (primeAt i) := ⟨z%(primeAt i),Nat.mod_lt _ (posPrime i)⟩

def pointIn (P : Point) (j : ModBlock) : Prop := res P.1.val j.1=j.2.1 ∧ res P.2.val j.1=j.2.2

def lineIn (A : Line) (j : ModBlock) : Prop := res (A.1.val*j.2.1.val+A.2.val) j.1 ≠ j.2.2

private theorem mod_replace (a x b p : ℕ) : (a*(x%p)+b)%p=(a*x+b)%p := by
  calc
    _ = ((a*(x%p))%p+b%p)%p := Nat.add_mod _ _ _
    _ = ((a%p*(x%p))%p+b%p)%p := by rw [Nat.mul_mod a (x%p) p,Nat.mod_mod]
    _ = _ := by rw [← Nat.mul_mod,← Nat.add_mod]

private theorem eval_res (a x b : ℕ) (i : Fin 9) : res (a*(res x i).val+b) i=res (a*x+b) i :=
  Fin.ext (mod_replace a x b (primeAt i))

theorem cross_rep (P : Point) (A : Line) : ¬onLine P A ↔ ∃ j : ModBlock, pointIn P j ∧ lineIn A j := by
  classical
  constructor
  · intro missing
    have diff : ∃ i, res (A.1.val*P.1.val+A.2.val) i ≠ res P.2.val i := by
      by_contra! eq
      apply missing
      change (P.2.val : ℤ) = (A.1.val : ℤ)*P.1.val + A.2.val
      have bound : A.1.val*P.1.val + A.2.val < 50000000 := (incidentPoint A P.1).2.isLt
      have sep : (P.2.val : ℤ) = ((A.1.val*P.1.val + A.2.val : ℕ) : ℤ) := by
        apply small_separated (by positivity) (by positivity) (by exact_mod_cast P.2.isLt) (by exact_mod_cast bound)
        intro i
        have raw : P.2.val%(primeAt i)=(A.1.val*P.1.val+A.2.val)%(primeAt i) := congrArg Fin.val (eq i).symm
        exact_mod_cast raw
      simpa only [Nat.cast_add,Nat.cast_mul] using sep
    obtain ⟨i,hi⟩ := diff
    refine ⟨⟨i,res P.1.val i,res P.2.val i⟩,⟨rfl,rfl⟩,?_⟩
    change res (A.1.val*(res P.1.val i).val+A.2.val) i ≠ res P.2.val i
    rwa [eval_res]
  · rintro ⟨⟨i,u,v⟩,⟨hx,hy⟩,hl⟩ edge
    change res P.1.val i=u at hx
    change res P.2.val i=v at hy
    subst u
    subst v
    apply hl
    rw [eval_res]
    apply congrArg (fun n => res n i)
    change (P.2.val : ℤ) = (A.1.val : ℤ)*P.1.val+A.2.val at edge
    exact_mod_cast edge.symm

end Affine3576
namespace Affine3576

set_option maxRecDepth 8192

abbrev Vert := (Point ⊕ Line) ⊕ Fin 2
abbrev Mask := Bool ⊕ ModBlock

def Pnode (p : Point) : Vert := .inl (.inl p)
def Anode (a : Line) : Vert := .inl (.inr a)
def spare (d : Fin 2) : Vert := .inr d

def adj : Vert → Vert → Prop
  | .inl (.inl p),.inl (.inr a) => onLine p a
  | .inl (.inr a),.inl (.inl p) => onLine p a
  | _,_ => False

def side : Vert → Bool
  | .inl (.inr _) => true
  | _ => false

def mem : Vert → Mask → Prop
  | .inl (.inl _),.inl s => s=false
  | .inl (.inr _),.inl s => s=true
  | .inr _,.inl _ => True
  | .inl (.inl p),.inr j => pointIn p j
  | .inl (.inr a),.inr j => lineIn a j
  | .inr _,.inr _ => False

theorem abip (u v : Vert) (h : adj u v) : side u≠side v := by
  rcases u with (p|a)|d <;> rcases v with (q|b)|e <;>
    first | exact False.elim h | exact Bool.false_ne_true | exact (by decide : true ≠ false)

theorem afour (u v w x : Vert) (uw : u≠w) (vx : v≠x) : ¬(adj u v ∧ adj v w ∧ adj w x ∧ adj x u) := by
  rintro ⟨h1,h2,h3,h4⟩
  rcases u with (a|b)|d <;> rcases v with (a'|b')|d' <;> rcases w with (a''|b'')|d'' <;> rcases x with (a'''|b''')|d''' <;>
    first | exact False.elim h1 | exact False.elim h2 | exact False.elim h3 | exact False.elim h4 | skip
  · rcases four h1 h4 h2 h3 with pp|aa
    · exact uw (by rw [pp])
    · exact vx (by rw [aa])
  · rcases four h1 h2 h4 h3 with pp|aa
    · exact vx (by rw [pp])
    · exact uw (by rw [aa])

theorem mem_pair (u v : Vert) : ¬adj u v ↔ ∃ j, mem u j ∧ mem v j := by
  have f (p : Point) (a : Line) : ¬onLine p a ↔ ∃ j, mem (Pnode p) j ∧ mem (Anode a) j := by
    constructor
    · intro h
      obtain ⟨j,hp,ha⟩ := (cross_rep p a).mp h
      exact ⟨.inr j,hp,ha⟩
    · rintro ⟨j,hp,ha⟩
      rcases j with s|j
      · exact False.elim (Bool.false_ne_true (hp.symm.trans ha))
      · exact (cross_rep p a).mpr ⟨j,hp,ha⟩
  rcases u with (a|b)|d <;> rcases v with (x|y)|e
  · exact ⟨fun _ => ⟨.inl false,rfl,rfl⟩,fun _ => id⟩
  · exact f a y
  · exact ⟨fun _ => ⟨.inl false,rfl,True.intro⟩,fun _ => id⟩
  · constructor
    · intro h
      obtain ⟨j,hx,hb⟩ := (f x b).mp h
      exact ⟨j,hb,hx⟩
    · rintro ⟨j,hb,hx⟩
      exact (f x b).mpr ⟨j,hx,hb⟩
  · exact ⟨fun _ => ⟨.inl true,rfl,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl true,rfl,True.intro⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl false,True.intro,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl true,True.intro,rfl⟩,fun _ => id⟩
  · exact ⟨fun _ => ⟨.inl false,True.intro,True.intro⟩,fun _ => id⟩

theorem mem_some (u : Vert) : (∃ j,mem u j) ∧ ∃ j,¬mem u j := by
  rcases u with (a|b)|z
  · exact ⟨⟨.inl false,rfl⟩,⟨.inl true,(by decide : true ≠ false)⟩⟩
  · exact ⟨⟨.inl true,rfl⟩,⟨.inl false,Bool.false_ne_true⟩⟩
  · exact ⟨⟨.inl false,True.intro⟩,⟨.inr ⟨0,res 0 0,res 0 0⟩,id⟩⟩

theorem omit_two (j : Mask) : ∃ u v, u≠v ∧ ¬mem u j ∧ ¬mem v j := by
  rcases j with s|j
  · cases s
    · exact ⟨Anode (0,0),Anode (1,0),by decide,Bool.false_ne_true,Bool.false_ne_true⟩
    · exact ⟨Pnode (0,0),Pnode (1,0),by decide,(by decide : true ≠ false),(by decide : true ≠ false)⟩
  · exact ⟨spare 0,spare 1,by decide,id,id⟩

noncomputable def structur : SimpleGraph (Fin (Fintype.card Vert)) where
  Adj := fun u v => adj ((Fintype.equivFin Vert).symm u) ((Fintype.equivFin Vert).symm v)
  symm := by
    constructor
    have sym (a b : Vert) (h : adj a b) : adj b a := by
      rcases a with (p|l)|d <;> rcases b with (q|k)|e <;> exact h
    exact fun _ _ h => sym _ _ h
  loopless := by
    constructor
    have loop (a : Vert) : ¬adj a a := by rcases a with (p|l)|d <;> exact id
    exact fun _ => loop _

theorem large [DecidableRel structur.Adj] : Fintype.card (Line × Fin 5000) ≤ structur.edgeFinset.card := by
  let ev := Fintype.equivFin Vert
  let P (t : Line × Fin 5000) := ev (Pnode (incidentPoint t.1 t.2))
  let A (t : Line × Fin 5000) := ev (Anode t.1)
  have edge (t : Line × Fin 5000) : structur.Adj (P t) (A t) := by
    change adj (ev.symm (ev _)) (ev.symm (ev _))
    rw [ev.symm_apply_apply,ev.symm_apply_apply]
    exact incident_correct _ _
  change _ ≤ _
  rw [← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun t : Line × Fin 5000 => s(P t,A t))
  · exact fun t _ => SimpleGraph.mem_edgeFinset.mpr (edge t)
  · intro t ht w hw eq
    rcases Sym2.eq_iff.mp eq with ⟨hp,ha⟩|⟨bad,_⟩
    · have lap : t.1=w.1 := by simpa [A,Anode] using (ev.injective ha)
      have pt : incidentPoint t.1 t.2=incidentPoint w.1 w.2 := by simpa [P,Pnode] using (ev.injective hp)
      exact Prod.ext lap (congrArg Prod.fst pt)
    · have no : Pnode (incidentPoint t.1 t.2) = Anode w.1 := ev.injective bad
      simp [Pnode,Anode] at no

noncomputable def members (j : Fin (Fintype.card Mask)) : Finset (Fin (Fintype.card Vert)) := by
  classical
  exact Finset.univ.filter (fun v => mem ((Fintype.equivFin Vert).symm v) ((Fintype.equivFin Mask).symm j))

private theorem member_iff (j : Fin (Fintype.card Mask)) (v : Fin (Fintype.card Vert)) :
    v∈members j ↔ mem ((Fintype.equivFin Vert).symm v) ((Fintype.equivFin Mask).symm j) := by
  classical
  simp [members]

private theorem two_more {m n : ℕ} (le : m≤n) (h : 2≤n-m) : m+2≤n := by omega

theorem omitted_bound (j : Fin (Fintype.card Mask)) : (members j).card+2 ≤ Fintype.card Vert := by
  classical
  let e := Fintype.equivFin Vert
  obtain ⟨u,v,ne,hu,hv⟩ := omit_two ((Fintype.equivFin Mask).symm j)
  have miss {w : Vert} (h : ¬mem w ((Fintype.equivFin Mask).symm j)) : e w ∉ members j := by
    intro hw
    have mw := (member_iff j (e w)).mp hw
    change mem (e.symm (e w)) _ at mw
    exact h (by simpa only [e.symm_apply_apply] using mw)
  let Q := Finset.univ \ members j
  have sub : {e u,e v} ⊆ Q := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl|rfl
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,miss hu⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,miss hv⟩
  have neq : e u≠e v := fun h => ne (e.injective h)
  have hsub := Finset.card_le_card sub
  have qcard : Q.card = Fintype.card Vert-(members j).card := by
    simp [Q,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have le := Finset.card_le_univ (members j)
  simp only [Fintype.card_fin] at le
  have cardpair : ({e u,e v} : Finset _).card=2 := by simp [neq]
  rw [cardpair,qcard] at hsub
  exact two_more le hsub

private theorem over_budget {edges cover cost upper count : ℕ}
    (h : edges+cover+1≤cost) (co : cost≤upper) (too : upper<count) (number : count≤edges) : False := by omega

theorem exact_negation : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro allGraphs
  let e := Fintype.equivFin Vert
  let f := Fintype.equivFin Mask
  have bip (u v) (h : structur.Adj u v) : side (e.symm u)≠side (e.symm v) := abip _ _ h
  have nocyc (a b c d) (ac : a≠c) (bd : b≠d) : ¬(structur.Adj a b ∧ structur.Adj b c ∧ structur.Adj c d ∧ structur.Adj d a) :=
    afour _ _ _ _ (fun he => ac (e.symm.injective he)) (fun he => bd (e.symm.injective he))
  have k : Fintype.card Mask=1558 := by rw [Fintype.card_sum,Fintype.card_bool,mod_count]
  have indep (j a) (ha : a∈members j) (b) (hb : b∈members j) : ¬structur.Adj a b :=
    (mem_pair _ _).mpr ⟨_,(member_iff _ _).mp ha,(member_iff _ _).mp hb⟩
  have mt (u : Fin (Fintype.card Vert)) (j : Mask) : u ∈ members (f j) ↔ mem (e.symm u) j := by
    rw [member_iff]
    change mem (e.symm u) (f.symm (f j)) ↔ _
    rw [f.symm_apply_apply]
  have hits (u : Fin (Fintype.card Vert)) : ∃ j,u∈members j := by
    obtain ⟨j,hj⟩ := (mem_some (e.symm u)).1
    exact ⟨f j,(mt u j).mpr hj⟩
  have misses (u : Fin (Fintype.card Vert)) : ∃ j,u∉members j := by
    obtain ⟨j,hj⟩ := (mem_some (e.symm u)).2
    exact ⟨f j,fun h => hj ((mt u j).mp h)⟩
  have pair (u v : Fin (Fintype.card Vert)) (_ : u≠v) (h : ¬structur.Adj u v) : ∃ j, u∈members j ∧ v∈members j := by
    obtain ⟨j,hu,hv⟩ := (mem_pair (e.symm u) (e.symm v)).mp h
    exact ⟨f j,(mt u j).mpr hu,(mt v j).mpr hv⟩
  obtain ⟨T,_,ht⟩ := allGraphs _ _ structur (fun v => side (e.symm v)) members bip nocyc (by omega) indep hits misses omitted_bound pair
  have total : ∑ j : Fin (Fintype.card Mask), (Fintype.card Vert - (members j).card) ≤
      Fintype.card Mask * Fintype.card Vert := by
    calc
      _ ≤ ∑ _j : Fin (Fintype.card Mask), Fintype.card Vert := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
      _ = _ := by simp
  have nv : Fintype.card Vert = Fintype.card Point + Fintype.card Line + 2 := by
    simp only [Fintype.card_sum,Fintype.card_fin]
  have cap : Fintype.card Mask * Fintype.card Vert < Fintype.card (Line × Fin 5000) := by
    rw [k,nv,Nat.mul_comm]
    simpa only [show 1556+2=1558 by decide] using card_margin
  exact over_budget ht total cap large

end Affine3576
