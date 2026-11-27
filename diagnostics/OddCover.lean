import PEqualNP.Defs
namespace Odd7808

theorem oddCover {n k:Nat} (G:SimpleGraph (Fin n)) (pick:Fin k→Fin n) (hk:Odd k)
    (cycle:∀i j:Fin k,G.Adj (pick i) (pick j) ↔ (i.val+1)%k=j.val ∨ (j.val+1)%k=i.val)
    (T:Finset (Fin n)) (cover:∀a b,G.Adj a b→a∈T∨b∈T) :
    ∃i j:Fin k, G.Adj (pick i) (pick j) ∧ pick i∈T ∧ pick j∈T := by
  obtain ⟨q,qk⟩ := hk
  have kp:0<k := by omega
  let atN (t:Nat) : Fin k := ⟨t%k,Nat.mod_lt _ kp⟩
  have adj (t:Nat) : G.Adj (pick (atN t)) (pick (atN (t+1))) := by
    apply (cycle _ _).mpr
    left
    change (t%k+1)%k=(t+1)%k
    exact Nat.mod_add_mod _ _ _
  by_contra bad
  have swap (t:Nat) : pick (atN (t+1))∈T ↔ pick (atN t)∉T := by
    constructor
    · intro a b
      exact bad ⟨_,_,adj t,b,a⟩
    · intro a
      exact (cover _ _ (adj t)).resolve_left a
  have dbl (m:Nat) : pick (atN (2*m))∈T ↔ pick (atN 0)∈T := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2*(m+1)=2*m+1+1 by omega,swap,swap,not_not,ih]
  have endeq : atN k=atN 0 := by
    apply Fin.ext
    simp [atN]
  have diff : pick (atN 0)∈T ↔ pick (atN 0)∉T := by
    calc
      _ ↔ pick (atN k)∈T := by rw [endeq]
      _ ↔ pick (atN (2*q+1))∈T := by rw [show k=2*q+1 by omega]
      _ ↔ pick (atN (2*q))∉T := swap _
      _ ↔ _ := not_congr (dbl q)
  tauto
end Odd7808
