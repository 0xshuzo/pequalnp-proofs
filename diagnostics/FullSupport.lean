import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.FullSupport
abbrev N := Fin 42
abbrev Input := Finset N
abbrev Arm := Input → Bool
def mono (a : Arm) := ∀s t : Input, s ⊆ t → a s=true → a t=true
def changes (a : Arm) (x : N) := ∃s : Input,a (insert x s) ≠ a s
def masks : Array Nat := #[2474236706816,550433193984,1100866387968,2201732775936,5421137920,10842275840,21684551680,43369103360,86738206720,173476413440,346952826880,693905653760,1387811307520,2775622615040,1153200816128,2306401632256,214758850560,429517701120,859035402240,1718070804480,3436141608960,81938,163878,327756,655512,1311024,524897,1049794,2437,4874,9748,19496,38992,77984,155968,311936,623872,1247744,398337,796674,1593348,1089545]
def edge (x y : N) : Bool := masks[x.val]!.testBit y.val
def first : Array N := #[26,21,22,23,21,22,23,24,25,26,27,28,29,30,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,9,0,1,2,0]
def second : Array N := #[28,22,23,24,24,25,26,27,28,29,30,31,32,33,31,32,23,24,25,26,27,4,2,3,4,5,5,6,2,3,4,5,6,7,8,9,10,11,10,11,12,3]

def probe (x y : N) : N × N :=
  let p := first[x.val]!
  let q := second[x.val]!
  let u := first[y.val]!
  let v := second[y.val]!
  if !edge p u then (p,u) else if !edge p v then (p,v) else if !edge q u then (q,u) else (q,v)
def checked (x y : N) :=
  let (p,q) := probe x y
  edge x p && edge y q && !edge p q
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem allProbes : ∀x y : N, checked x y=true := by decide +kernel

theorem allInputs (a b : Arm) (ma : mono a) (mb : mono b)
    (onPairs : ∀x y : N, (a {x,y} && b {x,y}) = edge x y) :
    (∀x,changes a x) ∨ (∀y,changes b y) := by
  classical
  by_cases ac : ∀x,changes a x
  · exact Or.inl ac
  right
  intro y
  by_contra hy
  obtain ⟨x,hx⟩ := Classical.not_forall.mp ac
  have xa : ∀s : Input,a (insert x s)=a s := by
    intro s
    by_contra hh
    exact hx ⟨s,hh⟩
  have yb : ∀s : Input,b (insert y s)=b s := by
    intro s
    by_contra hh
    exact hy ⟨s,hh⟩
  obtain ⟨p,q,pq⟩ : ∃p q : N,probe x y=(p,q) := ⟨_,_,rfl⟩
  have chk:=allProbes x y
  simp only [checked,pq] at chk
  have ex : edge x p=true := by
    cases u : edge x p <;> simp_all
  have ey : edge y q=true := by
    cases u : edge y q <;> simp_all
  have ep : edge p q=false := by
    cases u : edge p q <;> simp_all
  have ax := onPairs x p
  have byy := onPairs y q
  rw [ex] at ax
  rw [ey] at byy
  have ap : a {p}=true := by
    rw [←xa {p}]
    cases u : a {x,p} <;> simp_all
  have bq : b {q}=true := by
    rw [←yb {q}]
    cases u : b {y,q} <;> simp_all
  have both := onPairs p q
  rw [ma {p} {p,q} (by simp) ap, mb {q} {p,q} (by simp) bq,ep] at both
  contradiction

end PEqualNP.Outside.L_meta_9743.FullSupport
