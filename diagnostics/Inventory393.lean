import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

def mass : List Nat → Nat
  | [] => 0
  | x::xs => x + xs.sum + mass xs

def live : List Nat → Nat
  | [] => 0
  | x::xs => (if x = 0 then 0 else 1) + live xs

def quarter (xs : List Nat) := xs.map (· / 4)
def cost : Nat → List Nat → Nat
  | 0, _ => 0
  | f+1, xs => live xs + cost f (quarter xs)

lemma live_le_sum (xs : List Nat) : live xs ≤ xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x=0 <;> simp [live,h] <;> omega

lemma live_tri (xs : List Nat) : live xs * live xs + live xs ≤ 2*mass xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hh := live_le_sum xs
    by_cases eq : x=0
    · simp [mass,live,eq]; omega
    · simp [mass,live,eq]; nlinarith

lemma quarter_sum (xs : List Nat) : 4*(quarter xs).sum ≤ xs.sum := by
  induction xs with
  | nil => simp [quarter]
  | cons x xs ih =>
    change 4*(x/4+(quarter xs).sum) ≤ x+xs.sum
    omega

lemma quarter_mass (xs : List Nat) : 4*mass (quarter xs) ≤ mass xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hs := quarter_sum xs
    change 4*(x/4+(quarter xs).sum+mass (quarter xs)) ≤ x+xs.sum+mass xs
    omega

theorem cost_bound (fuel : Nat) (xs : List Nat) :
    cost fuel xs ≤ 2 * Nat.sqrt (2*mass xs) := by
  induction fuel generalizing xs with
  | zero => exact Nat.zero_le _
  | succ f ih =>
    have low : live xs ≤ Nat.sqrt (2*mass xs) :=
      Nat.le_sqrt.mpr (by have := live_tri xs; nlinarith)
    have small : 2 * Nat.sqrt (2 * mass (quarter xs)) ≤ Nat.sqrt (2 * mass xs) := by
      apply Nat.le_sqrt.mpr
      have hh := Nat.sqrt_le (2 * mass (quarter xs))
      have hq := quarter_mass xs
      nlinarith
    change live xs + cost f (quarter xs) ≤ _
    have := ih (quarter xs)
    omega

def writeCell : Nat → Nat → List (Fin 5)
  | 0, _ => [4]
  | f+1, x => if x=0 then [4] else ⟨x%4,by omega⟩ :: writeCell f (x/4)

def decode : List (Fin 5) → List Nat
  | [] => []
  | a::as => if a.val=4 then 0 :: decode as else
      match decode as with
      | [] => []
      | x::xs => (4*x+a.val) :: xs

lemma decode_cell (f x : Nat) (h : x≤f) (tail : List (Fin 5)) :
    decode (writeCell f x ++ tail) = x :: decode tail := by
  induction f generalizing x with
  | zero => have eq : x=0 := by omega
            simp [eq,writeCell,decode]
  | succ f ih =>
    by_cases eq : x=0
    · simp [eq,writeCell,decode]
    · simp only [writeCell,if_neg eq,List.cons_append,decode]
      rw [if_neg (show x%4 ≠ 4 by omega),ih (x/4) (by omega)]
      congr 1
      omega

def encode (f : Nat) (xs : List Nat) := xs.flatMap (writeCell f)

lemma decode_many (f : Nat) (xs : List Nat) (h : ∀ x∈xs,x≤f) (tail : List (Fin 5)) :
    decode (encode f xs ++ tail) = xs ++ decode tail := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih =>
    change decode ((writeCell f x ++ encode f xs) ++ tail) = _
    rw [List.append_assoc,decode_cell f x (h _ (by simp)),ih (fun k hk => h _ (by simp [hk]))]
    rfl

lemma write_zero (f : Nat) : writeCell f 0 = [4] := by cases f <;> simp [writeCell]

lemma cost_cons (f x : Nat) (xs : List Nat) :
    cost f (x::xs) + 1 = (writeCell f x).length + cost f xs := by
  induction f generalizing x xs with
  | zero => simp [writeCell,cost]
  | succ f ih =>
    have hh := ih (x/4) (quarter xs)
    by_cases eq : x=0
    · subst x
      simp only [Nat.zero_div,write_zero,List.length_cons,List.length_nil] at hh
      simp [writeCell,cost,live,quarter] at hh ⊢
      omega
    · change ((if x=0 then 0 else 1) + live xs + cost f ((x/4)::quarter xs)) + 1 =
        (writeCell (f+1) x).length + (live xs + cost f (quarter xs))
      simp only [eq,if_false,writeCell,List.length_cons]
      omega

lemma encode_length (f : Nat) (xs : List Nat) :
    (encode f xs).length = xs.length + cost f xs := by
  induction xs with
  | nil =>
    have zero (k : Nat) : cost k []=0 := by induction k <;> simp_all [cost,live,quarter]
    simp [encode,zero]
  | cons x xs ih =>
    change (writeCell f x ++ encode f xs).length = _
    rw [List.length_append,ih,List.length_cons]
    have := cost_cons f x xs
    omega

theorem inventory_code_bound (N : Nat) (xs : List Nat)
    (size : xs.length ≤ Nat.sqrt (2*N)) (wt : mass xs ≤ N) :
    (encode N xs).length ≤ 3 * Nat.sqrt (2*N) := by
  rw [encode_length]
  have a := cost_bound N xs
  have b : Nat.sqrt (2*mass xs) ≤ Nat.sqrt (2*N) := Nat.sqrt_le_sqrt (by omega)
  omega

end PEqualNP.Outside.L_pcx_393_aux
