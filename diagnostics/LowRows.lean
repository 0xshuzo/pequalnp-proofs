import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10025.Low
open Finset
def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def inc (p : Fin 25) (l : Fin 30) : Bool := (rows.getD p.val 0).testBit l.val
abbrev Box := Finset (Fin 25) × Finset (Fin 30)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : Finset (Fin k) := univ.filter fun t => p ∈ (R t).1
def tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : Finset (Fin k) := univ.filter fun t => l ∈ (R t).2

theorem cov_tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : ∑ l, cov R p l = ∑ t ∈ tp R p, (R t).2.card := by
  have e : ∀ l, cov R p l = ∑ t ∈ tp R p, if l ∈ (R t).2 then 1 else 0 := by
    intro l; unfold cov tp; rw [← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : ∑ p, cov R p l = ∑ t ∈ tl R l, (R t).1.card := by
  have e : ∀ p, cov R p l = ∑ t ∈ tl R l, if p ∈ (R t).1 then 1 else 0 := by
    intro p; unfold cov tl
    rw [filter_congr (fun t _ => and_comm), ← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_le_tp {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tp R p).card :=
  card_le_card fun t ht => by simp [tp] at ht ⊢; exact ht.1
theorem cov_le_tl {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tl R l).card :=
  card_le_card fun t ht => by simp [tl] at ht ⊢; exact ht.2

theorem swap_tp {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ p, ∑ t ∈ tp R p, f t = ∑ t, (R t).1.card * f t := by
  unfold tp; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp
theorem swap_tl {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ l, ∑ t ∈ tl R l, f t = ∑ t, (R t).2.card * f t := by
  unfold tl; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp


set_option maxRecDepth 8000 in
theorem countRow : ∀ p, (∑ l : Fin 30, if inc p l = false then 1 else 0 : ℕ) = 24 := by decide +kernel

theorem lowRows {k : ℕ} (hk : k ≤ 15) (R : Fin k → Box)
    (rowsix : ∀ t, (R t).1.card ≤ 6) (colnine : ∀ t, (R t).2.card ≤ 9)
    (hits : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2) :
    10 ≤ (univ.filter fun p => (tp R p).card = 3).card := by
  classical
  have lo (p : Fin 25) : 3 ≤ (tp R p).card := by
    have per (l : Fin 30) : (if inc p l = false then 1 else 0 : ℕ) ≤ cov R p l := by
      split
      · rename_i h
        obtain ⟨t,pt,lt⟩ := hits p l h
        exact card_pos.mpr ⟨t, by simp [pt,lt]⟩
      · omega
    have h := sum_le_sum fun l (_ : l ∈ (univ : Finset (Fin 30))) => per l
    rw [countRow, cov_tp] at h
    have u := sum_le_sum fun t (_ : t ∈ tp R p) => colnine t
    simp only [sum_const, nsmul_eq_mul] at u
    omega
  have upper : ∑ p, (tp R p).card ≤ 90 := by
    have e := swap_tp R (fun _ => 1)
    simp only [Nat.mul_one, sum_const, nsmul_eq_mul] at e
    simp only [Nat.mul_one] at e
    rw [e]
    have u := sum_le_sum fun t (_ : t ∈ (univ : Finset (Fin k))) => rowsix t
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at u
    omega
  have per (p : Fin 25) : 4 ≤ (tp R p).card + (if (tp R p).card = 3 then 1 else 0 : ℕ) := by
    have := lo p
    split <;> omega
  have all := sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin 25))) => per p
  rw [sum_add_distrib, ← card_filter] at all
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at all
  omega
def side : Array Nat := #[807542988,822501512,807555602,816071234,809779608,811993224,824251024,807739922,822675604,824256784,809769346,818680080,813903940,830611980,822675784,826820676,814237770,810172994,817959174,814232324,543429394,554313804,541870280,547435028,673714772,673720904,543434828,606865496,541864468,610802192,555950232,549998914,688009496,677523714,556278104,543821906,625615112,608309578,675893328,682172496,547434696,606167128,549998744,610812112,558172560,545415750,675685136,675684422,553921298,625221908,557976134,608315716,683935940,683958788,545612368,541149396,612639380,608512132,692142226,679559506,557998480,620970192,549658946,629235778,539378314,562632964,690620932,690227722,539367690,606866178,554308364,621287942,679549068,680280204,548162056,612651656,539564676,614797444,696783240,673386888,555962498,614600842,562643210,613044488,688212226,688016002,562446980,545589638,620970502,629213954,270739848,274877058,279520016,281698820,73992340,71975320,79767814,138633490,76040970,145230476,270733908,285559064,273044240,276896076,73795912,77873752,88295492,147144788,92426764,153230088,404818712,409158160,274876696,339937548,348275464,146948884,205605396,144902412,211896840,75713284,285356696,281282762,289478802,294136392,71965250,80482960,75706442,143200472,92611090,155593218,411705992,406988938,340265618,281676298,344533506,143206936,214442136,138611346,79768208,214114434,427886680,419633680,344330776,293802568,348264520,155587096,147134536,71572056,222431824,210045520,279322694,287967428,277627218,294130068,86780176,69357778,136982864,84304020,77863298,159664262,411705620,413280388,338315408,271067540,346556690,145252626,209871248,136988806,78266754,209848710,411324692,413274436,354566228,279334992,337922384,153229396,159664464,84281684,203823364,226902276,419961040,428607554,344330434,360984720,277616786,160051344,218763346,143009986,218376274,92414162,287597066,290209932,275067138,273240134,88617732,69542092,141304388,84500808,86053510,151081354,404841218,409485830,341909892,340287756,273228550,138961548,140583306,74014856,204030596,204030218,423907592,407179588,354762824,352408132,289489228,140595780,207884364,153436936,218370828,69554700,407179402,423895688,285553282,352395850,357110274,151790154,206320136,155783362,88617034,205598920,419971270,405561410,287596740,337916038,353116548,136589638,220733762,151802244,86774022,220745858]
def rowMask : Nat := 1039104990
def completes (i j : Fin 240) : Bool := (side[0]! ||| side[i.val]! ||| side[j.val]!) == rowMask
def listed (i j : Nat) : Bool := ((i == 84) && (j == 125)) || ((i == 125) && (j == 84)) || ((i == 176) && (j == 224)) || ((i == 224) && (j == 176))
set_option maxRecDepth 4096
theorem slice0 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨0 + i.val, by omega⟩ j = listed (0 + i.val) j.val := by decide +kernel
theorem slice1 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨15 + i.val, by omega⟩ j = listed (15 + i.val) j.val := by decide +kernel
theorem slice2 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨30 + i.val, by omega⟩ j = listed (30 + i.val) j.val := by decide +kernel
theorem slice3 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨45 + i.val, by omega⟩ j = listed (45 + i.val) j.val := by decide +kernel
theorem slice4 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨60 + i.val, by omega⟩ j = listed (60 + i.val) j.val := by decide +kernel
theorem slice5 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨75 + i.val, by omega⟩ j = listed (75 + i.val) j.val := by decide +kernel
theorem slice6 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨90 + i.val, by omega⟩ j = listed (90 + i.val) j.val := by decide +kernel
theorem slice7 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨105 + i.val, by omega⟩ j = listed (105 + i.val) j.val := by decide +kernel
theorem slice8 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨120 + i.val, by omega⟩ j = listed (120 + i.val) j.val := by decide +kernel
theorem slice9 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨135 + i.val, by omega⟩ j = listed (135 + i.val) j.val := by decide +kernel
theorem slice10 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨150 + i.val, by omega⟩ j = listed (150 + i.val) j.val := by decide +kernel
theorem slice11 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨165 + i.val, by omega⟩ j = listed (165 + i.val) j.val := by decide +kernel
theorem slice12 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨180 + i.val, by omega⟩ j = listed (180 + i.val) j.val := by decide +kernel
theorem slice13 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨195 + i.val, by omega⟩ j = listed (195 + i.val) j.val := by decide +kernel
theorem slice14 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨210 + i.val, by omega⟩ j = listed (210 + i.val) j.val := by decide +kernel
theorem slice15 : ∀ i : Fin 15, ∀ j : Fin 240, completes ⟨225 + i.val, by omega⟩ j = listed (225 + i.val) j.val := by decide +kernel
end PEqualNP.Outside.L_meta_10025.Low
