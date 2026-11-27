import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9829.ConnectedRows
open Finset
abbrev P := Fin 13

inductive Built {X : Type} (initial : List (X → Bool)) : List (X → Bool) → Nat → Prop
  | start : Built initial initial 0
  | unary {bank n} (prev : Built initial bank n) {a} (ha : a∈bank) (op : Bool→Bool) :
      Built initial ((fun x => op (a x)) :: bank) n
  | binary {bank n} (prev : Built initial bank n) {a b} (ha : a∈bank) (hb : b∈bank)
      (op : Bool→Bool→Bool) : Built initial ((fun x => op (a x) (b x)) :: bank) (n+1)

section
variable {X T : Type} (x y : T→X) (pt : T→P)

def uniform (c : P→P) (v : X→Bool) := ∃ q : P, ∀ t, v (x t) ≠ v (y t) → c (pt t)=q

theorem recolor (S : Finset P) (c : P→P) (a b : P) :
    (S.image c).card ≤ (S.image (fun p => if c p=b then a else c p)).card+1 := by
  classical
  let d := fun p => if c p=b then a else c p
  have covered : (S.image c).erase b ⊆ S.image d := by
    intro w hw
    obtain ⟨ne,h⟩ := mem_erase.mp hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_image.mpr ⟨i,hi,by simp [d,ne]⟩
  have le := card_le_card covered
  by_cases h : b∈S.image c
  · have eq := card_erase_add_one h
    change (S.image c).card ≤ (S.image d).card+1
    omega
  · rw [erase_eq_of_notMem h] at le
    exact Nat.le.step le

theorem account (S : Finset P) {initial bank : List (X→Bool)} {n : Nat}
    (h : Built initial bank n) (base : ∀ v∈initial,uniform x y pt id v) :
    ∃ c : P→P, (∀ v∈bank,uniform x y pt c v) ∧ S.card≤(S.image c).card+n := by
  classical
  induction h with
  | start => exact ⟨id,base,by simp⟩
  | @unary bank n prev v hv op ih =>
    obtain ⟨c,good,count⟩ := ih
    refine ⟨c,?_,count⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|old
    · obtain ⟨q,f⟩ := good _ hv
      exact ⟨q,fun t diff => f t (fun eq => diff (congrArg op eq))⟩
    · exact good _ old
  | @binary bank n prev u v hu hv op ih =>
    obtain ⟨c,good,count⟩ := ih
    obtain ⟨a,ua⟩ := good _ hu
    obtain ⟨b,vb⟩ := good _ hv
    let k := fun p : P => if p=b then a else p
    let d := fun p => k (c p)
    have cn : (S.image c).card ≤ (S.image d).card+1 := recolor S c a b
    refine ⟨d,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|old
    · refine ⟨a,?_⟩
      intro t changed
      by_cases eq : u (x t)=u (y t)
      · have nv : v (x t)≠v (y t) := by
          intro e
          apply changed
          change op (u (x t)) (v (x t)) = op (u (y t)) (v (y t))
          rw [eq,e]
        simp [d,k,vb t nv]
      · simp [d,k,ua t eq]
    · obtain ⟨q,oldq⟩ := good _ old
      exact ⟨k q,fun t e => congrArg k (oldq t e)⟩

theorem connectedPrice {R : Type} (S : Finset P) {initial bank : List (X→Bool)} {n : Nat}
    (built : Built initial bank n) (base : ∀ v∈initial,uniform x y pt id v)
    (row : T→R) (out : R→X→Bool) (live : ∀ r,out r∈bank)
    (test : ∀ t,out (row t) (x t) ≠ out (row t) (y t))
    (cover : ∀ p∈S,∃t,pt t=p) (root : R)
    (connected : ∀r,∃ i j, row i=r ∧ row j=root ∧ pt i=pt j) : S.card≤n+1 := by
  classical
  obtain ⟨c,good,count⟩ := account x y pt S built base
  choose col uniformCol using fun r => good _ (live r)
  have key (t : T) : c (pt t)=col (row t) := uniformCol (row t) t (test t)
  have same (r : R) : col r=col root := by
    obtain ⟨i,j,a,b,e⟩ := connected r
    simpa only [a,b] using (key i).symm.trans ((congrArg c e).trans (key j))
  have sub : S.image c ⊆ {col root} := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨t,rfl⟩ := cover p hp
    simpa using (key t).trans (same (row t))
  have le := card_le_card sub
  simp only [card_singleton] at le
  omega
end
end PEqualNP.Outside.L_meta_9829.ConnectedRows
