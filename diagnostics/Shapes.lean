import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_363

abbrev Role := Fin 4 × Bool
abbrev Inc := Bool × Fin 9 × Bool

def ends (j : Fin 9) (b : Bool) : Role :=
  let table : Fin 9 → Fin 2 → Role :=
  ![![((0,true) : Role),(1,true)],![(1,true),(2,true)],![(2,true),(0,true)],
    ![(0,false),(2,false)],![(2,false),(3,false)],![(3,false),(0,false)],
    ![(1,false),(2,false)],![(2,false),(3,false)],![(3,false),(1,false)]]
  table j (if b then 1 else 0)

def localPin (r : Inc) : Role :=
  let p := ends r.2.1 r.2.2
  (p.1, if r.1 then !p.2 else p.2)

def turn (r : Inc) : Inc := (r.1, r.2.1, if r.1 then r.2.2 else !r.2.2)

theorem turn_inv : Function.Involutive turn := by
  rintro ⟨b,j,t⟩
  cases b <;> simp [turn]

def loc (h : Role → Bool) : ℕ :=
  (Finset.univ.filter fun r : Inc => h (localPin r) ≠ h (localPin (turn r))).card

def evalRole (A B Z : Bool) (p : Role) : Bool :=
  let t := ![A,B,Z,false] p.1
  if p.2 then !t else t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_le : ∀ h : Role → Bool, loc h ≤ 12 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_top : ∀ A B Z : Bool, loc (evalRole A B Z) = 12 ↔ Z = !(A && B) := by decide +kernel

def pairCost (h : Bool → Bool) : ℕ :=
  (Finset.univ.filter fun t : Bool => h t ≠ h (!t)).card

theorem pair_le : ∀ h, pairCost h ≤ 2 := by decide +kernel

theorem pair_top : ∀ h, pairCost h = 2 ↔ h true = !(h false) := by decide +kernel

end PEqualNP.Outside.L_pcx_363
