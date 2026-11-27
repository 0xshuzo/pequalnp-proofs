import PEqualNP.Defs

namespace BinaryWords851

def digit : Bool → ℕ
  | false => 0
  | true => 1

def rank : (b : ℕ) → (Fin b → Bool) → ℕ
  | 0, _ => 0
  | b+1, w => 2*rank b (fun j => w j.castSucc) + digit (w (Fin.last b))

theorem rank_lt (b : ℕ) (w : Fin b → Bool) : rank b w < 2^b := by
  induction b with
  | zero => decide +revert
  | succ b ih =>
    have h := ih (fun j => w j.castSucc)
    rw [rank, pow_succ]
    cases w (Fin.last b) <;> simp [digit] <;> omega

theorem rank_inj (b : ℕ) : Function.Injective (rank b) := by
  induction b with
  | zero => intro u w _; exact Subsingleton.elim _ _
  | succ b ih =>
    intro u w huv
    have eqp : rank b (fun j => u j.castSucc) = rank b (fun j => w j.castSucc) ∧
        u (Fin.last b) = w (Fin.last b) := by
      simp only [rank] at huv
      cases ha : u (Fin.last b) <;> cases hb : w (Fin.last b) <;>
        simp [ha, hb, digit] at * <;> omega
    have he := ih eqp.1
    funext i
    exact Fin.lastCases eqp.2 (fun j => congrFun he j) i

theorem rank_onto (b k : ℕ) (hk : k < 2^b) : ∃ w : Fin b → Bool, rank b w = k := by
  induction b generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    exact ⟨fun i => i.elim0, by simp [rank, this]⟩
  | succ b ih =>
    rw [pow_succ] at hk
    obtain ⟨v,hv⟩ := ih (k/2) (by omega)
    let bit := decide (k%2=1)
    refine ⟨Fin.lastCases bit v, ?_⟩
    simp [rank, Fin.lastCases_castSucc, Fin.lastCases_last, hv]
    by_cases hb : k%2=1 <;> simp [bit, hb, digit] <;> omega

theorem fold (α : Type) (update : α → Bool → α) (z : α) (state : ℕ → ℕ → α)
    (init : state 0 0 = z)
    (next : ∀ b k bit, k < 2^b → update (state b k) bit = state (b+1) (2*k+digit bit))
    (b : ℕ) (w : Fin b → Bool) :
    (List.ofFn w).foldl update z = state b (rank b w) := by
  induction b with
  | zero => simpa [rank] using init.symm
  | succ b ih =>
    rw [List.ofFn_succ', List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    apply next
    apply rank_lt

theorem filter_card {ι : Type} [DecidableEq ι] (state : ℕ → Option ι) (b : ℕ) (i : ι)
    (k : ℕ) (hk : k < 2^b) (hstate : ∀ t, t < 2^b → (state t = some i ↔ t = k)) :
    ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => state (rank b w) = some i)).card = 1 := by
  obtain ⟨v,hv⟩ := rank_onto b k hk
  have he : (Finset.univ : Finset (Fin b → Bool)).filter (fun w => state (rank b w) = some i) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hstate _ (rank_lt ..), ← hv]
    exact (rank_inj b).eq_iff
  simp [he]

end BinaryWords851
