import PEqualNP.Defs
namespace KeySpace1018

def good (upper : ℕ) : ℕ → List ℕ → Prop
  | p,[] => p≤upper
  | p,j::rest => p≤j ∧ good upper j rest

def enc : ℕ → List ℕ → List Bool
  | _,[] => []
  | p,j::rest => List.replicate (j-p) false ++ true::enc j rest

def dec (p : ℕ) : List Bool → List ℕ
  | [] => []
  | true::rest => p::dec p rest
  | false::rest => dec (p+1) rest
termination_by l => l.length

theorem skip (z p : ℕ) (w : List Bool) : dec p (List.replicate z false++w) = dec (p+z) w := by
  induction z generalizing p with
  | zero => simp
  | succ z ih =>
    rw [List.replicate_succ,List.cons_append,dec,ih]
    congr 1
    omega

theorem inverse {u p} {xs : List ℕ} (h : good u p xs) (z : ℕ) :
    dec p (enc p xs++List.replicate z false)=xs := by
  induction xs generalizing p with
  | nil =>
    change dec p (List.replicate z false)=[]
    simpa [dec] using skip z p []
  | cons j xs ih =>
    obtain ⟨pj,tail⟩ := h
    simp only [enc,List.append_assoc,List.cons_append,skip]
    rw [show p+(j-p)=j by omega,dec,ih tail]

theorem enc_size {u p} {xs : List ℕ} (h : good u p xs) :
    (enc p xs).length+p ≤ u+xs.length := by
  induction xs generalizing p with
  | nil => simpa [enc] using h
  | cons j xs ih =>
    obtain ⟨pj,tail⟩ := h
    specialize ih tail
    simp only [enc,List.length_append,List.length_replicate,List.length_cons]
    omega

structure Key (k : ℕ) where
  xs : List ℕ
  bounded : good (4*k) 0 xs
  short : xs.length ≤ 2*k

def padded {k} (q : Key k) : List Bool := enc 0 q.xs ++ List.replicate (6*k-(enc 0 q.xs).length) false

theorem padded_len {k} (q : Key k) : (padded q).length=6*k := by
  have b := enc_size q.bounded
  have s := q.short
  simp only [padded,List.length_append,List.length_replicate]
  omega

def physical {k} (q : Key k) (i : Fin (6*k)) : Bool :=
  (padded q)[i.val]'(by rw [padded_len]; exact i.isLt)

theorem physical_inj (k : ℕ) : Function.Injective (@physical k) := by
  intro a b eq
  have p : padded a=padded b := by
    apply List.ext_getElem
    · rw [padded_len,padded_len]
    · intro i ha hb
      exact congrFun eq ⟨i,by simpa only [padded_len] using ha⟩
  have sa := inverse a.bounded (6*k-(enc 0 a.xs).length)
  have sb := inverse b.bounded (6*k-(enc 0 b.xs).length)
  change dec 0 (padded a)=a.xs at sa
  change dec 0 (padded b)=b.xs at sb
  have eqxs := sa.symm.trans ((congrArg (dec 0) p).trans sb)
  cases a
  cases b
  congr

noncomputable instance (k : ℕ) : Fintype (Key k) := Fintype.ofInjective physical (physical_inj k)

theorem count_keys (k : ℕ) : Fintype.card (Key k) ≤ 2^(6*k) := by
  simpa using Fintype.card_le_of_injective physical (physical_inj k)

end KeySpace1018
