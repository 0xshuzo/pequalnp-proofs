import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_7911
namespace Meet7911
open PEqualNP.MetaComplexity
abbrev F (n : ℕ) := DMFormula n
def copies {n} (u : Fin n) : F n → ℕ
  | .lit i _ => if i=u then 1 else 0
  | .and a b | .or a b => copies u a + copies u b
def deg {n} (M : Finset (Fin n)) : F n → ℕ
  | .lit i _ => if i∈M then 1 else 0
  | .and a b => deg M a+deg M b
  | .or a b => max (deg M a) (deg M b)
def same {n} (p : Fin n) (x y : Fin n → Bool) := ∀ i, i≠p → x i=y i
lemma unchanged {n} (p : Fin n) {x y : Fin n → Bool} (h : same p x y) (f : F n) (none : copies p f=0) : f.eval x=f.eval y := by
  induction f with
  | lit v b =>
    have ne : v≠p := by intro e; simp [copies,e] at none
    simp [DMFormula.eval,h v ne]
  | and a b ha hb | or a b ha hb =>
    change copies p a+copies p b=0 at none
    simp only [DMFormula.eval,ha (by omega),hb (by omega)]
lemma used {n} (M : Finset (Fin n)) (f : F n) (h : 0<deg M f) : ∃ p∈M, 0<copies p f := by
  induction f with
  | lit v b =>
    by_cases h' : v∈M
    · exact ⟨v,h',by simp [copies]⟩
    · simp [deg,h'] at h
  | and a b ha hb | or a b ha hb =>
    by_cases za : 0<deg M a
    · obtain ⟨p,hp,v⟩ := ha za
      exact ⟨p,hp,by change 0<copies p a+copies p b; omega⟩
    · have zb : 0<deg M b := by simp only [deg] at h; omega
      obtain ⟨p,hp,v⟩ := hb zb
      exact ⟨p,hp,by change 0<copies p a+copies p b; omega⟩

def comb (t a b : Bool) := if t then a && b else a || b
def node {n} (t : Bool) (a b : F n) : F n := if t then .and a b else .or a b
lemma copies_node {n} (t) (u : Fin n) (a b : F n) : copies u (node t a b)=copies u a+copies u b := by cases t <;> rfl
lemma eval_node {n} (t) (a b : F n) (x) : (node t a b).eval x=comb t (a.eval x) (b.eval x) := by cases t <;> rfl
lemma commute (t a b : Bool) : comb t a b=comb t b a := by cases t <;> cases a <;> cases b <;> rfl
lemma liftBit (t s a b c : Bool) (h : b=true → c=true → a=true) (hb : comb t b s=true) (hc : comb t c s=true) : comb t a s=true := by
  cases t <;> cases s <;> simp_all [comb]
def exclusive {n} (M : Finset (Fin n)) (f : F n) := ∀ p∈M, copies p f≤1
def witness {n} (M : Finset (Fin n)) (f : F n) := ∃ p∈M, ∃ q∈M, p≠q ∧ 0<copies p f ∧ 0<copies q f ∧
  ∀ x y z, same p x y → same q x z → f.eval y=true → f.eval z=true → f.eval x=true
lemma liftNode {n} (M : Finset (Fin n)) (t : Bool) (a b : F n) (h : exclusive M (node t a b))
    (child : witness M a ∨ witness M b) : witness M (node t a b) := by
  have size p (hp : p∈M) : copies p a+copies p b≤1 := (copies_node t p a b) ▸ h p hp
  rcases child with ⟨p,hp,q,hq,ne,pa,qa,base⟩|⟨p,hp,q,hq,ne,pb,qb,base⟩
  · have ps := size p hp; have qs := size q hq
    refine ⟨p,hp,q,hq,ne,by rw [copies_node]; omega,by rw [copies_node]; omega,?_⟩
    intro x y z hy hz fy fz
    rw [eval_node,←unchanged p hy b (by omega)] at fy
    rw [eval_node,←unchanged q hz b (by omega)] at fz
    rw [eval_node]; exact liftBit _ _ _ _ _ (base x y z hy hz) fy fz
  · have ps := size p hp; have qs := size q hq
    refine ⟨p,hp,q,hq,ne,by rw [copies_node]; omega,by rw [copies_node]; omega,?_⟩
    intro x y z hy hz fy fz
    rw [eval_node,←unchanged p hy a (by omega),commute] at fy
    rw [eval_node,←unchanged q hz a (by omega),commute] at fz
    rw [eval_node,commute]; exact liftBit _ _ _ _ _ (base x y z hy hz) fy fz
lemma obstruction {n} (M : Finset (Fin n)) (f : F n) (h : exclusive M f) (d : 1<deg M f) : witness M f := by
  induction f with
  | lit v b => simp only [deg] at d; split at d <;> omega
  | and a b ha hb =>
    have size p (hp : p∈M) : copies p a+copies p b≤1 := h p hp
    by_cases high : 1<deg M a
    · exact liftNode M true a b h (Or.inl (ha (fun p hp => by have := size p hp; omega) high))
    by_cases high' : 1<deg M b
    · exact liftNode M true a b h (Or.inr (hb (fun p hp => by have := size p hp; omega) high'))
    change 1<deg M a+deg M b at d
    obtain ⟨p,hp,pa⟩ := used M a (by omega)
    obtain ⟨q,hq,qb⟩ := used M b (by omega)
    have ps := size p hp; have qs := size q hq
    have ne : p≠q := by intro eq; subst q; omega
    refine ⟨p,hp,q,hq,ne,by change 0<copies p a+copies p b; omega,by change 0<copies q a+copies q b; omega,?_⟩
    intro x y z hy hz fy fz
    have ya := Bool.and_eq_true_iff.mp fy
    have za := Bool.and_eq_true_iff.mp fz
    exact Bool.and_eq_true_iff.mpr ⟨(unchanged q hz a (by omega)).trans za.1,(unchanged p hy b (by omega)).trans ya.2⟩
  | or a b ha hb =>
    have size p (hp : p∈M) : copies p a+copies p b≤1 := h p hp
    apply liftNode M false a b h
    change 1<max (deg M a) (deg M b) at d
    rcases lt_max_iff.mp d with l|r
    · exact Or.inl (ha (fun p hp => by have z := size p hp; omega) l)
    · exact Or.inr (hb (fun p hp => by have z := size p hp; omega) r)

theorem degree_one_of_or_faces {n} (M : Finset (Fin n)) (f : F n) (u : exclusive M f)
    (faces : ∀ p∈M, ∀ q∈M, p≠q → ∃ x y z, same p x y ∧ same q x z ∧ f.eval x=false ∧ f.eval y=true ∧ f.eval z=true) :
    deg M f≤1 := by
  by_contra! high
  obtain ⟨p,hp,q,hq,ne,_,_,cross⟩ := obstruction M f u high
  obtain ⟨x,y,z,hp',hq',off,on1,on2⟩ := faces p hp q hq ne
  exact Bool.noConfusion (off.symm.trans (cross x y z hp' hq' on1 on2))
end Meet7911
end PEqualNP.Outside.L_meta_7911
