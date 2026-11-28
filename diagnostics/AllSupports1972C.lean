import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1972
section Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)}
def girthFive (G : SimpleGraph (Fin n)) := ∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length

lemma triangle (h : girthFive G) {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w)
    (wu : G.Adj w u) : False := by
  let p := Walk.cons uv (Walk.cons vw (Walk.cons wu Walk.nil))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have a := uv.ne
    have b := vw.ne
    have c := wu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
  have bound := h u p hp
  simp [p] at bound

lemma square (h : girthFive G) {u a w b : Fin n} (ua : G.Adj u a) (aw : G.Adj a w)
    (wb : G.Adj w b) (bu : G.Adj b u) (uw : u ≠ w) (ab : a ≠ b) : False := by
  let p := Walk.cons ua (Walk.cons aw (Walk.cons wb (Walk.cons bu Walk.nil)))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have h1 := ua.ne
    have h2 := aw.ne
    have h3 := wb.ne
    have h4 := bu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,h1,h2,h3,h4,uw,ab,
      Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm uw,Ne.symm ab]
  have bound := h u p hp
  simp [p] at bound

end Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def excluded (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v p : Fin n) : Finset (Fin n) :=
  (G.neighborFinset v).filter fun z => z=p ∨ G.Adj p z

theorem excluded_card {v p : Fin n} (wide : girthFive G) (vp : v≠p) :
    (excluded G v p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨vs,bs⟩ := Finset.mem_filter.mp hs
  obtain ⟨vt,bt⟩ := Finset.mem_filter.mp ht
  have vs := (G.mem_neighborFinset v s).mp vs
  have vt := (G.mem_neighborFinset v t).mp vt
  by_contra ne
  rcases bs with rfl|ps <;> rcases bt with rfl|pt
  · exact ne rfl
  · exact triangle wide vs pt vt.symm
  · exact triangle wide vt ps vs.symm
  · exact square wide vs ps.symm pt vt.symm vp ne

theorem third_private {v p q : Fin n} (wide : girthFive G) (degree : (G.neighborSet v).ncard=3)
    (vp : v≠p) (vq : v≠q) :
    ∃ t, G.Adj v t ∧ t≠p ∧ ¬G.Adj p t ∧ t≠q ∧ ¬G.Adj q t := by
  classical
  have size : (G.neighborFinset v).card=3 := by
    change G.degree v=3
    rw [←G.ncard_neighborSet]
    exact degree
  have a := excluded_card wide vp
  have b := excluded_card wide vq
  have union := Finset.card_union_le (excluded G v p) (excluded G v q)
  have bad : ¬G.neighborFinset v ⊆ excluded G v p ∪ excluded G v q := by
    intro h
    have le := Finset.card_le_card h
    omega
  obtain ⟨t,ht,nt⟩ := Finset.not_subset.mp bad
  have pfree : t≠p ∧ ¬G.Adj p t := by
    by_contra! h
    exact nt (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,by tauto⟩))
  have qfree : t≠q ∧ ¬G.Adj q t := by
    by_contra! h
    exact nt (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,by tauto⟩))
  exact ⟨t,(G.mem_neighborFinset v t).mp ht,pfree.1,pfree.2,qfree.1,qfree.2⟩

open PEqualNP.MetaComplexity.NestedCover

theorem sensitivePattern (A : Finset (Fin n)) {v p q : Fin n} (wide : girthFive G)
    (degree : (G.neighborSet v).ncard=3) (iso : ∀ i j, G.Adj i j → i∉A)
    (po : p∉A) (qo : q∉A) (vp : v≠p) (vq : v≠q) (pq : p≠q) (a b : Bool)
    (legal : a=true → b=true → ¬G.Adj p q) :
    ∃ x : Fin n → Bool, x p=a ∧ x q=b ∧ x v=false ∧ graphFun G A x=false ∧
      graphFun G A (Function.update x v true)=true := by
  classical
  obtain ⟨t,vt,tp,pt,tq,qt⟩ := third_private wide degree vp vq
  let x : Fin n → Bool := fun i => decide (i=t ∨ (i=p ∧ a=true) ∨ (i=q ∧ b=true))
  have xp : x p=a := by cases a <;> simp [x,tp.symm,pq]
  have xq : x q=b := by cases b <;> simp [x,tq.symm,pq.symm]
  have xv : x v=false := by simp [x,vt.ne,vp,vq]
  have xon (i : Fin n) : x i=true ↔ i=t ∨ (i=p ∧ a=true) ∨ (i=q ∧ b=true) := by simp [x]
  have off : graphFun G A x=false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have lifted : (∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
      simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A x=true from yes)
    rcases lifted with ⟨i,hi,xi⟩|⟨i,j,ij,xi,xj⟩
    · rcases (xon i).mp xi with rfl|⟨rfl,_⟩|⟨rfl,_⟩
      · exact iso _ _ vt.symm hi
      · exact po hi
      · exact qo hi
    · rcases (xon i).mp xi with rfl|⟨rfl,ap⟩|⟨rfl,bq⟩ <;>
        rcases (xon j).mp xj with rfl|⟨rfl,ap'⟩|⟨rfl,bq'⟩
      · exact ij.ne rfl
      · exact pt ij.symm
      · exact qt ij.symm
      · exact pt ij
      · exact ij.ne rfl
      · exact legal ap bq' ij
      · exact qt ij
      · exact legal ap' bq ij.symm
      · exact ij.ne rfl
  refine ⟨x,xp,xq,xv,off,?_⟩
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨v,t,vt,by simp,by simpa [Function.update_of_ne vt.ne.symm] using (xon t).mpr (Or.inl rfl)⟩

theorem binaryShield (A : Finset (Fin n)) {v p q : Fin n} (wide : girthFive G)
    (degree : (G.neighborSet v).ncard=3) (iso : ∀ i j, G.Adj i j → i∉A)
    (po : p∉A) (qo : q∉A) (vp : v≠p) (vq : v≠q) (pq : p≠q)
    (W : Bool → Bool → Bool) (required : Bool)
    (shield : ∀ x, x v=false → graphFun G A x=false → graphFun G A (Function.update x v true)=true →
      W (x p) (x q) = required) :
    (∀ a b, W a b ≠ required → a=true ∧ b=true ∧ G.Adj p q) := by
  intro a b mismatch
  by_contra! h
  have legal : a=true → b=true → ¬G.Adj p q := by tauto
  obtain ⟨x,xp,xq,xv,off,on⟩ := sensitivePattern A wide degree iso po qo vp vq pq a b legal
  exact mismatch (by simpa [xp,xq] using shield x xv off on)

open PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def independent (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ p∈S, ∀ q∈S, ¬G.Adj p q

theorem project_sensitive (A : Finset (Fin n)) (v : Fin n) (S Z : Finset (Fin n))
    (vo : v∉A) (vS : v∉S) (away : Disjoint A S) (sz : Disjoint S Z)
    (iso : ∀ i j, G.Adj i j → i∉A) :
    (∃ x : Fin n → Bool, (∀ p∈S, x p=true) ∧ (∀ q∈Z, x q=false) ∧ x v=false ∧
      graphFun G A x=false ∧ graphFun G A (Function.update x v true)=true) ↔
    independent G S ∧ ∃ t, G.Adj v t ∧ t∉Z ∧ ∀ p∈S, ¬G.Adj p t := by
  classical
  constructor
  · rintro ⟨x,pos,neg,xv,off,on⟩
    have forbid : ¬ ((∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) := by
      intro bad
      have yes : graphFun G A x=true := by simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using bad
      rw [off] at yes
      contradiction
    have indep : independent G S := fun a ha b hb e => forbid (Or.inr ⟨a,b,e,pos a ha,pos b hb⟩)
    have claim (t : Fin n) (vt : G.Adj v t) (xt : x t=true) :
        G.Adj v t ∧ t∉Z ∧ ∀ p∈S, ¬G.Adj p t :=
      ⟨vt,fun h => Bool.noConfusion ((neg t h).symm.trans xt),
        fun p hp e => forbid (Or.inr ⟨p,t,e,pos p hp,xt⟩)⟩
    refine ⟨indep,?_⟩
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq] at on
    rcases on with ⟨a,am,va⟩ | ⟨a,b,ab,xa,xb⟩
    · have av : a≠v := fun eq => vo (eq ▸ am)
      exact False.elim (forbid (Or.inl ⟨a,am,by simpa only [Function.update_of_ne av] using va⟩))
    · by_cases av : a=v
      · subst a
        exact ⟨b,claim _ ab (by simpa only [Function.update_of_ne ab.ne.symm] using xb)⟩
      by_cases bv : b=v
      · subst b
        exact ⟨a,claim _ ab.symm (by simpa only [Function.update_of_ne ab.ne] using xa)⟩
      exact False.elim (forbid (Or.inr ⟨a,b,ab,by simpa [Function.update_of_ne av] using xa,
        by simpa [Function.update_of_ne bv] using xb⟩))
  · rintro ⟨indep,t,vt,tz,pt⟩
    let x : Fin n → Bool := fun i => decide (i=t ∨ i∈S)
    have xt : x t=true := by simp [x]
    have xon (i : Fin n) : x i=true ↔ i=t ∨ i∈S := by simp [x]
    refine ⟨x,fun p hp => (xon p).mpr (Or.inr hp),?_,by simp [x,vt.ne,vS],?_,?_⟩
    · intro q hq
      have qt : q≠t := fun h => tz (h ▸ hq)
      have qs : q∉S := fun h => Finset.disjoint_left.mp sz h hq
      simp [x,qt,qs]
    · apply Bool.eq_false_iff.mpr
      intro yes
      have lifted : (∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
        simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using (show graphFun G A x=true from yes)
      rcases lifted with ⟨p,ap,xp⟩|⟨p,q,pq,xp,xq⟩
      · rcases (xon p).mp xp with rfl|hp
        · exact iso _ _ vt.symm ap
        · exact Finset.disjoint_left.mp away ap hp
      · rcases (xon p).mp xp with rfl|sp <;> rcases (xon q).mp xq with rfl|sq
        · exact pq.ne rfl
        · exact pt _ sq pq.symm
        · exact pt _ sp pq
        · exact indep _ sp _ sq pq
    · simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
      exact Or.inr ⟨v,t,vt,by simp,by simpa only [Function.update_of_ne vt.ne.symm] using xt⟩

theorem missing_branch (A B : Finset (Fin n)) {v t : Fin n} (vt : G.Adj v t)
    (vo : v∉A) (vB : v∉B) (iso : ∀ i j, G.Adj i j → i∉A)
    (fresh : t∉B) (openT : ∀ p∈B, ¬G.Adj p t)
    (F : (Fin n → Bool) → Bool) (localF : ∀ x y, (∀ p∈B, x p=y p) → F x=F y)
    (required : Bool)
    (onChange : ∀ x, x v=false → graphFun G A x=false → graphFun G A (Function.update x v true)=true →
      F x=required) :
    ∀ x, graphFun G A x=false → F x=required := by
  classical
  intro x off
  let P := B.filter fun p => x p=true
  let Z := B.filter fun p => x p=false
  have forbid : ¬ ((∃ a∈A, x a=true) ∨ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) := by
    intro bad
    have yes : graphFun G A x=true := by simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using bad
    rw [off] at yes
    contradiction
  have pinfo (p) (h : p∈P) : p∈B ∧ x p=true := Finset.mem_filter.mp h
  have zinfo (p) (h : p∈Z) : p∈B ∧ x p=false := Finset.mem_filter.mp h
  have dp : Disjoint A P := by
    apply Finset.disjoint_left.mpr
    intro p hp h
    exact forbid (Or.inl ⟨p,hp,(pinfo p h).2⟩)
  have dz : Disjoint P Z := by
    apply Finset.disjoint_left.mpr
    intro p hp hz
    exact Bool.noConfusion ((zinfo p hz).2.symm.trans (pinfo p hp).2)
  have ip : independent G P := fun a ha b hb e =>
    forbid (Or.inr ⟨a,b,e,(pinfo _ ha).2,(pinfo _ hb).2⟩)
  obtain ⟨y,yP,yZ,yv,yo,yi⟩ := (project_sensitive A v P Z vo
    (fun h => vB (pinfo _ h).1) dp dz iso).mpr ⟨ip,t,vt,fun h => fresh (zinfo _ h).1,
      fun p hp => openT p (pinfo _ hp).1⟩
  rw [localF x y]
  · exact onChange y yv yo yi
  · intro p hp
    cases h : x p
    · exact (yZ p (Finset.mem_filter.mpr ⟨hp,h⟩)).symm
    · exact (yP p (Finset.mem_filter.mpr ⟨hp,h⟩)).symm

theorem outside_or (F W : (Fin n → Bool) → Bool)
    (H : (Fin n → Bool) → Bool → Bool) (v : Fin n)
    (orig : ∀ x, F x=H x (x v || W x)) (absorbed : ∀ x, F x=false → W x=false) :
    ∀ x, F x=(H x (x v) || W x) := by
  intro x
  cases w : W x with
  | false => simpa only [w,Bool.or_false] using orig x
  | true =>
    rw [Bool.or_true]
    cases f : F x with
    | true => rfl
    | false => exact False.elim (Bool.noConfusion (w.symm.trans (absorbed x f)))

end PEqualNP.Outside.L_meta_1972
