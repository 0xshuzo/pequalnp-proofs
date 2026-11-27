import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9838.Shadow
abbrev V := Fin 20
def listed : List (ℕ × ℕ) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]
def masks : Array Nat := #[0x200a1,0x40142,0x80286,0x50d,0xa18,0x1432,0x2864,0x50c8,0xa190,0x14320,0x28640,0x50c80,0xa1900,0x43201,0x86400,0xc803,0x19004,0x3200a,0x64014,0xc8028]
def incident (a b : V) := ((masks[a.val]?).getD 0).testBit b.val
def edges : Finset (V × V) := Finset.univ.filter (fun e => incident e.1 e.2)
def spec (x : Fin 40 → Bool) := ∃ u v : Fin 40, (u.val,v.val)∈listed ∧ x u=true ∧ x v=true

theorem incidence (a b : V) : (a,b)∈edges ↔ incident a b=true := by simp [edges]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem data : (∀ a b : V, incident a b=true ↔ (a.val,20+b.val)∈listed) ∧
    (∀ u v : Fin 40, (u.val,v.val)∈listed → u.val<20 ∧ 20≤v.val) ∧
    (∀ i : V, incident i i=true) ∧ edges.card=95 := by decide +kernel

def common (a c : V) : Finset V := Finset.univ.filter (fun b => incident a b && incident c b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem uniqueCard : ∀ a c : V, a≠c → (common a c).card≤1 := by decide +kernel

theorem linear (a c b d : V) (ac : a≠c) (bd : b≠d) :
    ¬((a,b)∈edges ∧ (a,d)∈edges ∧ (c,b)∈edges ∧ (c,d)∈edges) := by
  rintro ⟨ab,ad,cb,cd⟩
  have mem {j : V} (h1 : (a,j)∈edges) (h2 : (c,j)∈edges) : j∈common a c := by
    simp [common,(incidence _ _).mp h1,(incidence _ _).mp h2]
  exact bd (Finset.card_le_one.mp (uniqueCard a c ac) b (mem ab cb) d (mem ad cd))

theorem specEq (x : Fin 40 → Bool) :
    (∃ a b : V, (a,b)∈edges ∧ x (Fin.castAdd 20 a)=true ∧ x (Fin.natAdd 20 b)=true) ↔ spec x := by
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨Fin.castAdd 20 a, Fin.natAdd 20 b,(data.1 a b).mp ((incidence a b).mp ab),xa,xb⟩
  · rintro ⟨u,v,uv,xu,xv⟩
    obtain ⟨hu,hv⟩ := data.2.1 u v uv
    let a : V := ⟨u.val,hu⟩
    let b : V := ⟨v.val-20,by have := v.isLt; omega⟩
    have eqv : 20+(v.val-20)=v.val := by omega
    have eb : Fin.natAdd 20 b=v := Fin.ext eqv
    have mem : (a.val,20+b.val)∈listed := by
      change (u.val,20+(v.val-20))∈listed
      rwa [eqv]
    exact ⟨a,b,(incidence a b).mpr ((data.1 a b).mpr mem),xu,eb.symm ▸ xv⟩

theorem coverSize (A M : Finset V) (cover : ∀ e∈edges,e.1∈A ∨ e.2∈M) : 20≤A.card+M.card := by
  have sub : (Finset.univ : Finset V) ⊆ A∪M := by
    intro i _
    exact Finset.mem_union.mpr (cover (i,i) ((incidence i i).mpr (data.2.2.1 i)))
  simpa using (Finset.card_le_card sub).trans (Finset.card_union_le A M)

def Covers (A B : Finset V) (E : Finset (V × V)) := ∀ e∈E, e.1∈A ∨ e.2∈B

theorem pricedShadow (L R : Finset (V × V)) (A B C D : Finset V)
    (covers : edges ⊆ L∪R) (hl : Covers A B L) (hr : Covers C D R)
    (leftCost rightCost : Nat)
    (priceL : L.card + A.card + B.card ≤ leftCost+1)
    (priceR : R.card + C.card + D.card ≤ rightCost) :
    114 ≤ leftCost + rightCost := by
  have ac := Finset.card_union_le A C
  have bd := Finset.card_union_le B D
  have ec := (Finset.card_le_card covers).trans (Finset.card_union_le L R)
  have total := data.2.2.2
  have cv := coverSize (A∪C) (B∪D) (by
    intro e he
    rcases Finset.mem_union.mp (covers he) with lo | ro
    · rcases hl e lo with a | b
      · exact Or.inl (Finset.mem_union_left _ a)
      · exact Or.inr (Finset.mem_union_left _ b)
    · rcases hr e ro with c | d
      · exact Or.inl (Finset.mem_union_right _ c)
      · exact Or.inr (Finset.mem_union_right _ d))
  omega

theorem clampExterior {α β : Type} (exterior : α → Bool) (helpers : α → β → Bool)
    (localFn : α → (β → Bool) → Bool)
    (contained : ∀ x i, helpers x i=true → exterior x=true) (x : α) :
    (exterior x || localFn x (helpers x)) = (exterior x || localFn x (fun _ => false)) := by
  cases he : exterior x with
  | true => simp
  | false =>
    have eq : helpers x = (fun _ => false) := by
      funext i
      cases hi : helpers x i with
      | false => rfl
      | true => have contra := contained x i hi; simp [he] at contra
    rw [eq]

-- The exterior may supply any subset of a foreign center's OR neighborhood.
-- On the two rows testing r at x, every nonsingleton such OR agrees.
def lo (row : V → Bool) (y : V) := !(row y)
def hi (row : V → Bool) (x y : V) := lo row y || decide (y=x)
theorem privateFlip (row : V → Bool) (x : V) (h : List V)
    (mixed : x∈h → ∃ y∈h, row y=false) :
    h.any (lo row) = h.any (hi row x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨y,hy,ey⟩
    exact ⟨y,hy,by simp [hi,ey]⟩
  · rintro ⟨y,hy,ey⟩
    by_cases z : y=x
    · subst y
      obtain ⟨t,ht,ot⟩ := mixed hy
      exact ⟨t,ht,by simp [lo,ot]⟩
    · exact ⟨y,hy,by simpa [hi,z] using ey⟩

theorem exteriorFlip (r s x : V) (ne : r≠s) (hx : incident r x=true) (h : List V)
    (fromS : ∀ z∈h,incident s z=true) (several : ∃ z∈h,z≠x) :
    h.any (lo (incident r)) = h.any (hi (incident r) x) := by
  apply privateFlip
  intro xin
  obtain ⟨z,hz,diff⟩ := several
  refine ⟨z,hz,?_⟩
  cases az : incident r z with
  | false => rfl
  | true =>
    have hboth : x=z := Finset.card_le_one.mp (uniqueCard r s ne) x (by simp [common,hx,fromS x xin])
      z (by simp [common,az,fromS z hz])
    exact (diff hboth.symm).elim
end PEqualNP.Outside.L_meta_9838.Shadow
