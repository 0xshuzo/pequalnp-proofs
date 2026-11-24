import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.EdgeUpperMono

namespace Near4919
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.EdgeUpperMono
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

def line (p : Fin 21) (d : Nat) : Fin 56 := Fin.ofNat 56 (21+(p.val+d)%21)
def point (p : Fin 21) : Fin 56 := Fin.ofNat 56 p.val
def tail (p : Fin 21) : List (Fin 56) :=
  if p.val%3=0 then [line p 7, Fin.ofNat 56 (49+p.val/3)]
  else [line p 5,line p 7,line p 17,line p 20]
def ls (p : Fin 21) := line p 0 :: tail p
def evalRow (p : Fin 21) (z : Fin 56 → Bool) := z (point p) && (ls p).any z
def cost (p : Fin 21) := (tail p).length+1

theorem rowBld (p : Fin 21) : Bld 56 (evalRow p) (cost p) := by
  simpa [cost, evalRow, ls] using bld_and (bld_var (point p)) (bld_anyList (tail p) (line p 0))

theorem rowsBld (p : Fin 21) (ps : List (Fin 21)) :
    Bld 56 (fun z => (p::ps).any (fun q => evalRow q z))
      (cost p + (ps.map (fun q => cost q + 1)).sum) := by
  induction ps generalizing p with
  | nil => simpa using rowBld p
  | cons q qs ih =>
    refine bld_congr (bld_mono (bld_or (rowBld p) (ih q)) ?_) ?_
    · simp
      omega
    · intro z
      simp

def rline (j d : Nat) : Fin 42 := Fin.ofNat 42 (21+(3*j+d)%21)
def supp (i : Fin 56) : List (Fin 42) :=
  if i.val<42 then [Fin.ofNat 42 i.val]
  else if i.val<49 then [rline (i.val-42) 5,rline (i.val-42) 17]
  else [rline (i.val-49) 5,rline (i.val-49) 17,rline (i.val-49) 20]
def feature (x : Fin 42 → Bool) (i : Fin 56) : Bool :=
  if i.val<42 then x (Fin.ofNat 42 i.val)
  else if i.val<49 then x (rline (i.val-42) 5) || x (rline (i.val-42) 17)
  else x (rline (i.val-49) 5) || x (rline (i.val-49) 17) || x (rline (i.val-49) 20)

theorem feature_spec (x : Fin 42 → Bool) (i : Fin 56) :
    feature x i=true ↔ ∃ v∈supp i, x v=true := by
  unfold feature supp
  split
  · simp
  · split <;> simp [Bool.or_eq_true] <;> aesop

def bank (x : Fin 42 → Bool) :=
  let y (j : Fin 7) (d : Nat) := x (Fin.ofNat 42 (21+(3*j.val+d)%21))
  (List.ofFn x ++ List.ofFn (fun j : Fin 7 => y j 5 || y j 17)) ++
    List.ofFn (fun j : Fin 7 => y j 5 || y j 17 || y j 20)

theorem bank_eq (x : Fin 42 → Bool) : List.ofFn (feature x)=bank x := by rfl

def D := [0,5,7,17,20]
def incidence (u v : Fin 42) := u.val<21 ∧ 21≤v.val ∧ (v.val+21-u.val)%21∈D
def raw (p : Fin 21) : Fin 42 := ⟨p.val,by have := p.isLt; omega⟩
def ps : List (Fin 21) := (List.finRange 21).tail
theorem allrows : ∀ p : Fin 21, p∈(0::ps) := by decide +kernel

theorem point_ok : ∀ p : Fin 21, supp (point p)=[raw p] := by decide +kernel
theorem row_ok : ∀ (p : Fin 21) (v : Fin 42), v∈(ls p).flatMap supp ↔ incidence (raw p) v := by
  decide +kernel

theorem rows_spec (x : Fin 42 → Bool) :
    ((0::ps).any (fun p => evalRow p (feature x)))=true ↔
      ∃ u v : Fin 42, incidence u v ∧ x u=true ∧ x v=true := by
  simp only [List.any_eq_true,evalRow,Bool.and_eq_true,feature_spec,point_ok,List.mem_singleton]
  constructor
  · rintro ⟨p,_,⟨u,eu,xu⟩,i,hi,v,hv,xv⟩
    subst u
    exact ⟨raw p,v,(row_ok p v).mp (List.mem_flatMap.mpr ⟨i,hi,hv⟩),xu,xv⟩
  · rintro ⟨u,v,hit,xu,xv⟩
    let p : Fin 21 := ⟨u.val,hit.1⟩
    have e : raw p = u := Fin.ext rfl
    have hv := (row_ok p v).mpr (by simpa only [e] using hit)
    obtain ⟨i,hi,jv⟩ := List.mem_flatMap.mp hv
    exact ⟨p,allrows p,u,e.symm,xu,i,hi,v,jv,xv⟩

theorem candidate : ∃ C : Circuit, Monotone2 C ∧ C.size≤111 ∧
    ∀ x : Fin 42 → Bool, C.eval (bank x)=true ↔
      ∃ u v : Fin 42, incidence u v ∧ x u=true ∧ x v=true := by
  have budget : cost 0 + (ps.map (fun q => cost q + 1)).sum = 111 := by decide +kernel
  obtain ⟨C,fan,no,eval,sz⟩ := bld_circuit (rowsBld 0 ps)
  refine ⟨C,?_,by omega,?_⟩
  · intro g hg
    have f := fan g hg
    have h := no g hg
    refine ⟨?_,f.2⟩
    have op := f.1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    aesop
  · intro x
    have he := congrFun eval (feature x)
    change C.eval (List.ofFn (feature x)) = _ at he
    rw [← bank_eq,he]
    exact rows_spec x

end Near4919
