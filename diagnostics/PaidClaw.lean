import PEqualNP.Outside.L_meta_35002

namespace PEqualNP.Outside.L_meta_2374
open PEqualNP.Outside.L_meta_35002

theorem sameRows {R : Type} {u goal s ws} (h : @Run R u goal s ws) (x y : R)
    (same : ∀ f∈ws, f x=f y) : goal x=goal y := by
  induction h using Run.ind with
  | stop => exact same goal (by simp)
  | perm p h ih => exact ih (fun f hf => same f (p.mem_iff.mp hf))
  | @two n a b rest op hd ka kb h ih =>
    have ha := same a (by simp)
    have hb := same b (by simp)
    apply ih
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · unfold comb combine inv
      split_ifs <;> simp only [ha,hb]
    · apply same
      cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto

abbrev PRow := Fin 1024
def rawP (i : Nat) (r : PRow) := r.val.testBit i

def src (i : Fin 19) (r : PRow) : Bool :=
  let a := rawP 4 r || rawP 5 r
  let b := rawP 3 r || rawP 7 r
  let c := rawP 5 r || rawP 6 r
  match i.val with
  | 10 => a | 11 => a || rawP 1 r | 12 => rawP 0 r && (a || rawP 1 r)
  | 13 => b | 14 => b || rawP 1 r | 15 => rawP 2 r && (b || rawP 1 r)
  | 16 => c | 17 => c || rawP 3 r | 18 => rawP 8 r && (c || rawP 3 r)
  | j => rawP j r

def want (r : PRow) : Bool := (rawP 0 r && rawP 1 r) || (rawP 1 r && rawP 2 r) || (rawP 2 r && rawP 3 r) || (rawP 3 r && rawP 4 r) || (rawP 0 r && rawP 4 r) || (rawP 0 r && rawP 5 r) || (rawP 1 r && rawP 6 r) || (rawP 2 r && rawP 7 r) || (rawP 3 r && rawP 8 r) || (rawP 4 r && rawP 9 r) || (rawP 5 r && rawP 7 r) || (rawP 7 r && rawP 9 r) || (rawP 6 r && rawP 9 r) || (rawP 6 r && rawP 8 r) || (rawP 5 r && rawP 8 r)
def eraseThree (r : PRow) : PRow := ⟨(r.val &&& 762)%1024,by
  exact Nat.mod_lt _ (by decide)⟩
def mark (i : Fin 19) : Bool := [0,2,8,12,15,18].contains i.val
def pos : Fin 3 → PRow := ![3,6,264]
def negPt : Fin 3 → PRow := ![2,2,8]
def splitAt (j : Fin 3) (i : Fin 19) := src i (pos j)!=src i (negPt j)

theorem witnesses : ∀ j : Fin 3, want (pos j)≠want (negPt j) := by decide +kernel
theorem qualified : ∀ j i, splitAt j i=true → mark i=true := by decide +kernel
theorem uniqueMark : ∀ j k i, splitAt j i=true → splitAt k i=true → j=k := by decide +kernel
theorem clamped : ∀ i, mark i=true → ∀ r, src i (eraseThree r)=false := by decide +kernel

theorem atLeastThree {u s} {ls : List (Fin 19)} (h : Run u want s (ls.map src)) :
    3≤(ls.filter mark).length := by
  classical
  have hit (j : Fin 3) : ∃ i∈ls, splitAt j i=true := by
    by_contra! no
    apply witnesses j
    apply sameRows h
    intro f hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    simpa [splitAt] using no i hi
  choose v mem signal using hit
  let good := (ls.filter mark).toFinset
  let pick (j : Fin 3) : good := ⟨v j,by
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨mem j,qualified j _ (signal j)⟩⟩
  have inj : Function.Injective pick := by
    intro j k eq
    have vw : v j=v k := congrArg Subtype.val eq
    apply uniqueMark j k (v j) (signal j)
    rw [vw]
    exact signal k
  have bound := Fintype.card_le_of_injective pick inj
  simp only [Fintype.card_fin, Fintype.card_coe] at bound
  exact bound.trans (List.toFinset_card_le _)

theorem massLower (ls : List (Fin 19)) :
    (ls.filter mark).length≤mass ((ls.map src).map (restrictRows eraseThree)) := by
  classical
  induction ls with
  | nil => simp [mass]
  | cons a ls ih =>
    by_cases m : mark a=true
    · have ct : Constant (restrictRows eraseThree (src a)) := ⟨false,funext (clamped a m)⟩
      simp only [List.filter_cons,m,↓reduceIte,List.length_cons,List.map_cons,mass_cons,cost,if_pos ct]
      omega
    · simp only [List.filter_cons,m,↓reduceIte,List.map_cons,mass_cons]
      omega

theorem threeStarPrice {u s} {ls : List (Fin 19)} (h : Run u want s (ls.map src))
    {base : List (Wire PRow)} (stock : supply u base ((ls.map src).map (restrictRows eraseThree)))
    {L : Nat} (lower : ∀ q bs, Reach u base q bs →
        Available u bs (restrictRows eraseThree want) → L≤q) : L+3≤s := by
  have spread : ¬Constant (restrictRows eraseThree want) := by
    rintro ⟨c,hc⟩
    have u0 := congrFun hc 0
    have u1 := congrFun hc 66
    have no : restrictRows eraseThree want 0=false := by decide
    have yes : restrictRows eraseThree want 66=true := by decide
    rw [no] at u0
    rw [yes] at u1
    exact Bool.false_ne_true (u0.trans u1.symm)
  have pay := projected_bound eraseThree h spread (p:=0) Reach.start stock lower
  have seen := atLeastThree h
  have price := massLower ls
  omega

end PEqualNP.Outside.L_meta_2374
