import PEqualNP.Defs
namespace PHP169Private
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V
abbrev Row := C × Nat × Nat × Nat
def bank : List Row := [
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)}, 541200, 99360, 137280),
  ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}, 541185, 99330, 137220),
  ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, 540705, 98370, 135300),
  ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, 525345, 67650, 131460),
  ({((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)}, 33825, 6210, 8580),
  ({((0, 0), false), ((1, 0), false)}, 541201, 164881, 272401),
  ({((0, 1), false), ((1, 1), false)}, 540962, 99362, 268322),
  ({((0, 2), false), ((1, 2), false)}, 532804, 98884, 137284),
  ({((0, 3), false), ((1, 3), false)}, 270728, 82568, 136328),
  ({((0, 0), false), ((2, 0), false)}, 540961, 164161, 270721),
  ({((0, 1), false), ((2, 1), false)}, 541202, 98882, 266882),
  ({((0, 2), false), ((2, 2), false)}, 533524, 99364, 136324),
  ({((0, 3), false), ((2, 3), false)}, 272408, 84008, 137288),
  ({((0, 0), false), ((3, 0), false)}, 529441, 137281, 266881),
  ({((0, 1), false), ((3, 1), false)}, 533522, 75842, 270722),
  ({((0, 2), false), ((3, 2), false)}, 541204, 84004, 147844),
  ({((0, 3), false), ((3, 3), false)}, 295448, 99368, 164168),
  ({((0, 0), false), ((4, 0), false)}, 99361, 75841, 82561),
  ({((0, 1), false), ((4, 1), false)}, 164882, 137282, 147842),
  ({((0, 2), false), ((4, 2), false)}, 295444, 268324, 270724),
  ({((0, 3), false), ((4, 3), false)}, 541208, 529448, 532808),
  ({((1, 0), false), ((2, 0), false)}, 540946, 164116, 270616),
  ({((1, 1), false), ((2, 1), false)}, 541217, 98852, 266792),
  ({((1, 2), false), ((2, 2), false)}, 533569, 99394, 136264),
  ({((1, 3), false), ((2, 3), false)}, 272513, 84098, 137348),
  ({((1, 0), false), ((3, 0), false)}, 529426, 137236, 266776),
  ({((1, 1), false), ((3, 1), false)}, 533537, 75812, 270632),
  ({((1, 2), false), ((3, 2), false)}, 541249, 84034, 147784),
  ({((1, 3), false), ((3, 3), false)}, 295553, 99458, 164228),
  ({((1, 0), false), ((4, 0), false)}, 99346, 75796, 82456),
  ({((1, 1), false), ((4, 1), false)}, 164897, 137252, 147752),
  ({((1, 2), false), ((4, 2), false)}, 295489, 268354, 270664),
  ({((1, 3), false), ((4, 3), false)}, 541313, 529538, 532868),
  ({((2, 0), false), ((3, 0), false)}, 528706, 135556, 266536),
  ({((2, 1), false), ((3, 1), false)}, 533057, 74372, 270872),
  ({((2, 2), false), ((3, 2), false)}, 541729, 83074, 148504),
  ({((2, 3), false), ((3, 3), false)}, 296993, 100418, 165908),
  ({((2, 0), false), ((4, 0), false)}, 98626, 74116, 82216),
  ({((2, 1), false), ((4, 1), false)}, 164417, 135812, 147992),
  ({((2, 2), false), ((4, 2), false)}, 295969, 267394, 271384),
  ({((2, 3), false), ((4, 3), false)}, 542753, 530498, 534548),
  ({((3, 0), false), ((4, 0), false)}, 71746, 70276, 70696),
  ({((3, 1), false), ((4, 1), false)}, 141377, 139652, 140312),
  ({((3, 2), false), ((4, 2), false)}, 280609, 278914, 279064),
  ({((3, 3), false), ((4, 3), false)}, 558113, 557378, 557588)
]
def raw := bank.map Prod.fst
def children : List C := [
  {((1, 0), true), ((2, 0), true), ((3, 0), true), ((4, 0), true)},
  {((1, 1), true), ((2, 1), true), ((3, 1), true), ((4, 1), true)},
  {((1, 2), true), ((2, 2), true), ((3, 2), true), ((4, 2), true)},
  {((1, 3), true), ((2, 3), true), ((3, 3), true), ((4, 3), true)},
  {((0, 0), true), ((2, 0), true), ((3, 0), true), ((4, 0), true)},
  {((0, 1), true), ((2, 1), true), ((3, 1), true), ((4, 1), true)},
  {((0, 2), true), ((2, 2), true), ((3, 2), true), ((4, 2), true)},
  {((0, 3), true), ((2, 3), true), ((3, 3), true), ((4, 3), true)},
  {((0, 0), true), ((1, 0), true), ((3, 0), true), ((4, 0), true)},
  {((0, 1), true), ((1, 1), true), ((3, 1), true), ((4, 1), true)},
  {((0, 2), true), ((1, 2), true), ((3, 2), true), ((4, 2), true)},
  {((0, 3), true), ((1, 3), true), ((3, 3), true), ((4, 3), true)},
  {((0, 0), true), ((1, 0), true), ((2, 0), true), ((4, 0), true)},
  {((0, 1), true), ((1, 1), true), ((2, 1), true), ((4, 1), true)},
  {((0, 2), true), ((1, 2), true), ((2, 2), true), ((4, 2), true)},
  {((0, 3), true), ((1, 3), true), ((2, 3), true), ((4, 3), true)},
  {((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true)},
  {((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true)},
  {((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true)},
  {((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 3), true)}
]
def test (a : Nat) (v : V) : Bool := a.testBit (4*v.1.val+v.2.val)
def yes (a : Nat) (c : C) : Bool := decide (∃ l ∈ c, test a l.1 = l.2)
theorem yes_true (a : Nat) (c : C) : yes a c = true ↔ ClauseSat (test a) c := by
  simp [yes, ClauseSat]
def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)
theorem intersect (a b c d e f : Bool)
    (h : majority a b c = true) (k : majority d e f = true) :
    (a = true ∧ d = true) ∨ (b = true ∧ e = true) ∨ (c = true ∧ f = true) := by
  revert a b c d e f
  decide
def privateAt (c : C) (a : Nat) : Bool :=
  !yes a c && raw.all (fun d => d == c || yes a d)
def check (r : Row) : Bool :=
  privateAt r.1 r.2.1 && privateAt r.1 r.2.2.1 && privateAt r.1 r.2.2.2 &&
  children.all (fun k => majority (yes r.2.1 k) (yes r.2.2.1 k) (yes r.2.2.2 k))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem all_checks : bank.all check = true := by decide +kernel

theorem compulsory (x y : C) (hx : x ∈ children) (hy : y ∈ children)
    (S : Finset C) (sub : ∀ t ∈ S, t ∈ raw ∨ t = x ∨ t = y)
    (un : ∀ a : Nat, ¬(∀ t ∈ S, ClauseSat (test a) t)) : 45 ≤ S.card := by
  have incl : raw.toFinset ⊆ S := by
    intro t ht
    have hm : t ∈ bank.map Prod.fst := List.mem_toFinset.mp ht
    obtain ⟨⟨c,a,b,d⟩,hc,rfl⟩ := List.mem_map.mp hm
    have tag := List.all_eq_true.mp all_checks _ hc
    simp only [check, Bool.and_eq_true] at tag
    have pick := intersect _ _ _ _ _ _ (List.all_eq_true.mp tag.2 x hx)
      (List.all_eq_true.mp tag.2 y hy)
    by_contra no
    have finish (m : Nat) (pr : privateAt c m = true) (vg : yes m x = true)
        (vh : yes m y = true) : False := by
      simp only [privateAt, Bool.and_eq_true] at pr
      apply un m
      intro q hq
      apply (yes_true m q).mp
      rcases sub q hq with h | eq | eq
      · have w := List.all_eq_true.mp pr.2 q h
        have ne : q ≠ c := fun e => no (e ▸ hq)
        have bb : (q == c) = false := by simpa using ne
        simpa [bb] using w
      · simpa [eq] using vg
      · simpa [eq] using vh
    rcases pick with h | h | h
    · exact finish a tag.1.1.1 h.1 h.2
    · exact finish b tag.1.1.2 h.1 h.2
    · exact finish d tag.1.2 h.1 h.2
  have card : raw.toFinset.card = 45 := by decide +kernel
  rw [← card]
  exact Finset.card_le_card incl
end PHP169Private
