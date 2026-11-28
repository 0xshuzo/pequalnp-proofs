import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17132
open Finset
theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)


def column {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (f : Fin N → Nat) (l : Fin N) :=
  ∑ r, if I r l then f r else 0

theorem pencil_transform {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (ord : N=q^2+q+1)
    (line : ∀ l : Fin N, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (f : Fin N → Nat) (p : Fin N) :
    (∑ l, if I p l then column I f l else 0) = (∑ r, f r)+q*f p := by
  classical
  have cols (l : Fin N) : (univ.filter (fun r => I r l)).card=q+1 := by
    rw [← Fintype.card_coe]
    refine (Fintype.card_congr (Equiv.subtypeEquivRight ?_)).trans (line l)
    intro r; simp
  have row := lines_through q N I hq ord cols hu p
  let term (r l : Fin N) := if I p l ∧ I r l then f r else 0
  have per (r : Fin N) : (∑ l, term r l) = f r+(if r=p then q*f p else 0) := by
    by_cases eq : r=p
    · subst r
      change (∑ l, if I p l ∧ I p l then f p else 0)=_
      simp only [and_self,if_pos rfl]
      rw [← Finset.sum_filter]
      simp [row,Nat.add_mul,Nat.add_comm]
    · obtain ⟨t,ht,uniq⟩ := hu p r (Ne.symm eq)
      have e (l : Fin N) : (I p l ∧ I r l) ↔ l=t := ⟨fun k => uniq l k,fun k => k.symm ▸ ht⟩
      simp [term,e,eq]
  calc
    (∑ l, if I p l then column I f l else 0) = ∑ l : Fin N, ∑ r : Fin N, term r l := by
      apply sum_congr rfl
      intro l _
      by_cases h : I p l <;> simp [column,term,h]
    _ = ∑ r : Fin N, ∑ l : Fin N, term r l := Finset.sum_comm
    _ = (∑ r, f r) + q*f p := by simp_rw [per]; simp [sum_add_distrib]

theorem kernel_parity {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (ord : N=q^2+q+1) (odd : q%2≠0)
    (line : ∀ l : Fin N, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (f : Fin N → Nat) (ev : ∀ l, 2∣column I f l) (p : Fin N) :
    f p % 2 = (∑ r, f r) % 2 := by
  classical
  have total : 2 ∣ (∑ l : Fin N, if I p l then column I f l else 0) := by
    apply Finset.dvd_sum
    intro l _
    by_cases h : I p l <;> simp [h,ev]
  rw [pencil_transform I hq ord line hu f p] at total
  have hh := Nat.mod_eq_zero_of_dvd total
  rw [Nat.add_mod,Nat.mul_mod] at hh
  have o : q%2=1 := by omega
  rw [o,one_mul] at hh
  omega

theorem odd_detector {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (ord : N=q^2+q+1) (odd : q%2≠0)
    (line : ∀ l : Fin N, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (S : Finset (Fin N)) (p r : Fin N) (hp : p∈S) (hr : r∉S) :
    ∃ l, ¬2∣column I (fun s => if s∈S then 1 else 0) l := by
  classical
  by_contra! ev
  let f (s : Fin N) : Nat := if s∈S then 1 else 0
  have hp' := kernel_parity I hq ord odd line hu f ev p
  have hr' := kernel_parity I hq ord odd line hu f ev r
  have diff := hp'.trans hr'.symm
  simp [f,hp,hr] at diff
end PEqualNP.Outside.L_meta_17132
