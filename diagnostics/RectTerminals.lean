import PEqualNP.Defs
namespace Research9815.Terminals
abbrev V := Fin 7
def neighbors (p : V) : Nat := (#[10,69,66,49,88,44,22] : Array Nat)[p.val]!
def edge (p q : V) := (neighbors p).testBit q.val
def mate (p : V) : V := (#[1,0,6,4,3,5,2] : Array V)[p.val]!
theorem matching : ∀p q : V,edge p (mate p)=true ∧ (p≠q → edge p (mate q)=false ∨ edge q (mate p)=false) := by decide +kernel
theorem four : ∀a b u v : V,edge a u=true → edge a v=true →
    edge b u=true → edge b v=true → a=b ∨ u=v := by decide +kernel
theorem oneShore (r c : V→Bool) (ok : ∀a b,r a=true → c b=true → edge a b=true) :
    (∀a b,r a=true → r b=true → a=b) ∨ (∀u v,c u=true → c v=true → u=v) := by
  by_cases yes : ∀a b,r a=true → r b=true → a=b
  · exact Or.inl yes
  · push_neg at yes
    obtain ⟨a,b,ha,hb,ne⟩ := yes
    exact Or.inr (fun u v hu hv => (four a b u v (ok _ _ ha hu) (ok _ _ ha hv)
      (ok _ _ hb hu) (ok _ _ hb hv)).resolve_left ne)
theorem seven (k : Nat) (r c : Fin k → V → Bool)
    (law : ∀i a b,r i a=true → c i b=true → edge a b=true)
    (cv : ∀a b,edge a b=true → ∃i,r i a=true ∧ c i b=true) : 7≤k := by
  classical
  have pick (p : V) : ∃i,r i p=true ∧ c i (mate p)=true := cv _ _ (matching p p).1
  choose sel rp cp using pick
  have inj : Function.Injective sel := by
    intro p q eq
    by_contra ne
    have r1 := rp p
    have c1 := cp p
    rw [eq] at r1 c1
    rcases (matching p q).2 ne with bad|bad
    · exact Bool.noConfusion ((law _ _ _ r1 (cp q)).symm.trans bad)
    · exact Bool.noConfusion ((law _ _ _ (rp q) c1).symm.trans bad)
  simpa using Fintype.card_le_of_injective sel inj
theorem price (k combined enc unions expanded : Nat) (terms : 7≤k) (merge : combined≤k)
    (joined : unions+combined=k) (covers : 19≤expanded+combined)
    (decoder : expanded≤enc+unions) :
    25≤enc+k+(k-1) := by omega
end Research9815.Terminals
