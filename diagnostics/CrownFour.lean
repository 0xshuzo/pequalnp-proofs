import PEqualNP.Defs
namespace Lmeta10008Crown
open Finset
abbrev V := Fin 31
abbrev F := Fin 6
abbrev Box := Finset V × Finset V
def rows : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def M (p l : V) := (rows.getD p.val 0).testBit l.val
def pointData : Array Nat := #[932981921,967618754,1002255587,1036892420,1002939552,1037576385,1024826432,616827936,651464769,686101602,720738435,755375268,790012101,824648934,859285767,893922600,928559433,963196266,997833099,1032469932,861419936,896056769,930693602,965330435,999967268,1034604101,929713344,964350177,998987010,1033623843,898345088]
def lineData : Array Nat := #[894376071,166338374,162484423,206393598,138547332,206207815,207820996,242457828,893548743,894374118,675507143,893622430,1013587780,1014632666,698513638,1034557575,893591492,161730782,166547686,233640583,692736644,1034097287,904122502,166533767,156048606,233466084,900557636,166357191,166547686,223307911,1039104964]
def offset (p l : V) := (l.val+31-p.val)%31
def named (data : Array Nat) (p l : V) (u : F) : V :=
  ⟨(p.val+(data[offset p l]! >>> (5*u.val))%32)%31,Nat.mod_lt _ (by decide)⟩
def P := named pointData
def L := named lineData
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem tables (p l : V) (z : M p l=false) : ∀ i j : F,
    M (P p l i) l=true ∧ M p (L p l j)=true ∧ M (P p l i) (L p l j)=decide (i=j) := by
  have all : ∀ p l : V, M p l=false → ∀ i j : F,
    M (P p l i) l=true ∧ M p (L p l j)=true ∧ M (P p l i) (L p l j)=decide (i=j) := by decide +kernel
  exact all p l z

def effective {k : Nat} (R : Fin k → Box) (p l : V) : Finset (Fin k) :=
  univ.filter fun t => (∃ i, P p l i∈(R t).1) ∧ (∃ j, L p l j∈(R t).2)

theorem threeSperner : ∀ A : Finset (Finset (Fin 3)),
    (∀ a∈A, ∀ b∈A, a⊆b → a=b) → A.card ≤ 3 := by decide +kernel

theorem crownFour {k : Nat} (R : Fin k → Box)
    (good : ∀ t p, p∈(R t).1 → ∀ l, l∈(R t).2 → M p l=false)
    (cover : ∀ p l, M p l=false → ∃ t, p∈(R t).1 ∧ l∈(R t).2)
    (p l : V) (z : M p l=false) :
    4 ≤ (effective R p l).card := by
  classical
  let T := effective R p l
  change 4 ≤ T.card
  by_contra! short
  have bound : T.card ≤ 3 := by omega
  let g (t : T) : Fin 3 := Fin.castLE bound ((T.orderIsoOfFin rfl).symm t)
  have gi : Function.Injective g := (Fin.castLE_injective bound).comp (T.orderIsoOfFin rfl).symm.injective
  let A (i : F) := (univ.filter fun t : T => P p l i∈(R t.val).1).image g
  have ant (i j : F) (le : A i⊆A j) : i=j := by
    by_contra ne
    have hit : M (P p l i) (L p l j)=false := by simpa [ne] using (tables p l z i j).2.2
    obtain ⟨t,hp,hl⟩ := cover _ _ hit
    have mt : t∈T := mem_filter.mpr ⟨mem_univ _,⟨i,hp⟩,⟨j,hl⟩⟩
    let u : T := ⟨t,mt⟩
    have own : g u∈A i := mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hp⟩,rfl⟩
    obtain ⟨w,mw,eq⟩ := mem_image.mp (le own)
    have ew := gi eq
    have hs : P p l j∈(R t).1 := by
      have h := (mem_filter.mp mw).2
      simpa only [ew] using h
    have diag := (tables p l z j j).2.2
    have no := good t _ hs _ hl
    simp_all
  have inj : Function.Injective A := fun i j eq => ant i j (le_of_eq eq)
  have lim := threeSperner (univ.image A) (by
    rintro a ha b hb sub
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact congrArg A (ant i j sub))
  rw [card_image_of_injective _ inj,card_univ,Fintype.card_fin] at lim
  omega

theorem neutral {k : Nat} (R : Fin k → Box)
    (good : ∀ t p, p∈(R t).1 → ∀ l, l∈(R t).2 → M p l=false)
    (p l : V) (z : M p l=false) (t : Fin k) (eff : t∈effective R p l) :
    p∉(R t).1 ∧ l∉(R t).2 := by
  obtain ⟨⟨i,hp⟩,⟨j,hl⟩⟩ := (mem_filter.mp eff).2
  have vals := tables p l z i j
  exact ⟨fun h => Bool.noConfusion (vals.2.1.symm.trans (good t _ h _ hl)),
    fun h => Bool.noConfusion (vals.1.symm.trans (good t _ hp _ h))⟩
end Lmeta10008Crown
