import PEqualNP.Defs

namespace Lpcx119Private
structure Move where
  premise : Nat
  base : Nat
  side : Bool
  deriving DecidableEq
structure Sheet where
  site : Nat
  point : Nat
  rows : List (Nat × Nat)
  deriving Inhabited

def raw : List Nat := [42, 65, 260, 1040, 2688, 4097, 4160, 16388, 16640, 65552, 66560, 172032, 262145, 262208, 266240, 1048580, 1048832, 1064960, 4194320, 4195328, 4259840, 11010048]
def moves : List Move := [⟨42,524328,true⟩,⟨262145,262144,true⟩,⟨524289,1,false⟩]
def sheets : List Sheet := [
⟨1,512,[(0,784),(2,786),(3,676),(4,770),(7,674),(8,660),(9,788),(10,802),(11,546)]⟩,
⟨0,1,[(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185),(19,2209)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(12,785),(16,1297),(17,1185)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(12,785),(16,1297),(17,1185)]⟩,
⟨0,1,[(0,2128),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185),(19,2209)]⟩,
⟨2,513,[(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(12,785),(16,1297),(17,1185),(19,2209)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,1121),(10,1313),(11,1057),(17,1185),(19,2209),(21,161)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,1121),(10,1313),(11,1057),(12,673),(17,1185),(19,2209),(21,161)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(16,1297),(20,2321),(21,273)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(12,785),(16,1297),(20,2321),(21,273)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185),(19,2209)]⟩,
⟨2,513,[(1,2185),(4,2177),(8,2193),(10,1313),(11,2065),(12,785),(16,1297),(17,1185),(19,2209)]⟩,
⟨0,1,[(0,2128),(1,1289),(4,1281),(5,2129),(10,1313),(11,2065),(16,1297),(20,2321),(21,273)]⟩,
⟨2,513,[(1,1289),(4,1281),(5,2129),(10,1313),(11,2065),(12,785),(16,1297),(20,2321),(21,273)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(17,1185),(19,2209),(21,161)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(12,673),(17,1185),(19,2209),(21,161)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185)]⟩,
⟨1,512,[(0,784),(2,786),(3,676),(4,770),(7,674),(8,660),(9,788),(10,802),(11,546)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(19,2209),(20,2321),(21,273)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(11,2065),(12,785),(19,2209),(20,2321),(21,273)]⟩,
⟨0,1,[(0,1288),(1,1289),(4,1281),(5,1121),(10,1313),(11,1057),(16,1297),(17,1185),(21,273)]⟩,
⟨2,513,[(1,1289),(4,1281),(5,1121),(10,1313),(11,1057),(12,785),(16,1297),(17,1185),(21,273)]⟩,
⟨2,513,[(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(12,785),(16,1297),(17,1185)]⟩,
⟨0,1,[(0,2184),(1,2185),(4,2177),(5,2129),(8,2193),(10,1313),(11,2065),(16,1297),(17,1185)]⟩]

def val (C w : Nat) : Bool := (List.range 24).any (fun j =>
  C.testBit j && (w.testBit (j/2) == j.testBit 0))
def moveAt (j : Nat) := moves.getD j ⟨0,0,false⟩
def rhs (k j : Nat) : Nat := let m := moveAt j
  m.base ||| (if k<24 then 1 <<< (if m.side then k ^^^ 1 else k) else 0)
def applies (k j : Nat) : Bool := decide (k<24) || ((moveAt j).side == (k==25))
def axVal (i w : Nat) := val (raw.getD i 0) w
def rowOK (k site : Nat) (iw : Nat × Nat) : Bool :=
  decide (iw.1<22) && !(val (rhs k site) iw.2) &&
  (List.range 22).all (fun j => (j == iw.1) || axVal j iw.2)
def strong (k : Nat) (s : Sheet) : Bool :=
  decide (s.site<3) && applies k s.site && val (moveAt s.site).premise s.point &&
  !(val (rhs k s.site) s.point) && (s.rows.length==9) &&
  decide ((s.rows.map Prod.fst).Nodup) && s.rows.all (rowOK k s.site)
def sheet (k : Fin 26) := sheets.getD k.val default

set_option maxHeartbeats 2000000 in
theorem board : ∀ k : Fin 26, strong k.val (sheet k) = true := by decide +kernel

def Entails (source : List Nat) (dest : Nat) : Prop :=
  ∀ w, (∀ j ∈ source, j<22 ∧ axVal j w=true) → val dest w=true

theorem nine (k : Fin 26) :
    ∃ j w, j<3 ∧ applies k.val j=true ∧ val (moveAt j).premise w=true ∧ val (rhs k.val j) w=false ∧
      ∀ source : List Nat, (∀ i∈source,i<22) → Entails source (rhs k.val j) → 9 ≤ source.length := by
  let s := sheet k
  have hs : strong k.val s=true := board k
  simp only [strong,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',beq_iff_eq] at hs
  rcases hs with ⟨⟨⟨⟨⟨⟨range,ap⟩,tp⟩,td⟩,num⟩,nd⟩,rows⟩
  refine ⟨s.site,s.point,range,ap,tp,td,?_⟩
  intro src inRange bounds
  have contained : (s.rows.map Prod.fst).toFinset ⊆ src.toFinset := by
    intro i hi
    obtain ⟨⟨j,w⟩,hw,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    change j=i at eq
    subst j
    have hh := List.all_eq_true.mp rows (i,w) hw
    simp only [rowOK,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hh
    obtain ⟨⟨_,bad⟩,priv⟩ := hh
    apply List.mem_toFinset.mpr
    by_contra absent
    have target := bounds w (by
      intro t ht
      have rt := inRange t ht
      have ne : t≠i := fun e => absent (e ▸ ht)
      have b := List.all_eq_true.mp priv t (List.mem_range.mpr rt)
      exact ⟨rt,by simpa [ne] using b⟩)
    rw [bad] at target
    contradiction
  have card := Finset.card_le_card contained
  rw [List.toFinset_card_of_nodup nd,List.length_map,num] at card
  exact card.trans (List.toFinset_card_le _)

end Lpcx119Private
