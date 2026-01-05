import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
open Set

universe u v

open Classical
variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]

def to_0mod2_εNFA (A : εNFA alphabet ℕ) : (εNFA alphabet ℕ) :=
    {
        start  := { 2*q' | q' ∈ A.start  }
        accept := { 2*q' | q' ∈ A.accept }
        step   := fun q c => match (q % 2), c with
            | 0, _ => {2*q' | q' ∈ (A.step (q/2) c) }
            | _, _ => ∅
        : εNFA alphabet ℕ
    }

def to_1mod2_εNFA (A : εNFA alphabet ℕ) : (εNFA alphabet ℕ) :=
    {
        start  := { 2*q' + 1 | q' ∈ A.start  }
        accept := { 2*q' + 1 | q' ∈ A.accept }
        step   := fun q c => match (q % 2), c with
            | 0, _ => {2*q' + 1 | q' ∈ (A.step (q/2) c) }
            | _, _ => ∅
        : εNFA alphabet ℕ
    }

lemma if_0mod2_qf_is_0mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (qf : ℕ):
    (A' = to_0mod2_εNFA A) → qf ∈ A'.accept → (qf % 2 = 0) := by
    sorry

lemma if_1mod2_qf_is_1mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (qf : ℕ):
    (A' = to_1mod2_εNFA A) → qf ∈ A'.accept → (qf % 2 = 1) := by
    sorry

lemma accepts_eq_0mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    (A' = to_0mod2_εNFA A) → A.accepts = A'.accepts := by
    intro hmodzero
    have hA'start: A'.start = { 2*q' | q' ∈ A.start  } := by
        rw [hmodzero]
        unfold to_0mod2_εNFA
        rw [@setOf_exists]
    have hA'accept: A'.accept = { 2*q' | q' ∈ A.accept  } := by
        rw [hmodzero]
        unfold to_0mod2_εNFA
        rw [@setOf_exists]

    refine Language.ext_iff.mpr ?_
    intro x
    rw [A.mem_accepts_iff_exists_path, A'.mem_accepts_iff_exists_path]
    constructor

    case mp =>
        rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩
        let q'_start := 2 * q_start
        have h_q'_start: q'_start ∈ A'.start := by
            simp_all only [q'_start]
            rw [@mem_setOf_eq]
            use q_start
        let q'_accept := 2 * q_accept
        have h_q'_accept: q'_accept ∈ A'.accept := by
            simp_all only [q'_accept]
            rw [@mem_setOf_eq]
            use q_accept

        use q'_start, q'_accept, x'
        refine ⟨ h_q'_start, h_q'_accept, h_x' , ?_⟩

        have h_A_path_A'_path: (q₁ q₂ q'₁ q'₂ : ℕ) → (y : List (Option alphabet)) → (q'₁ = 2 * q₁) → (q'₂ = 2* q₂) → (A.IsPath q₁ q₂ y) → (A'.IsPath q'₁ q'₂ y) := by
            intro q₁ q₂ q'₁ q'₂ y hq'1 hq'2 h_A_path
            induction h_A_path generalizing q'₁
            case nil _ _ q_same=>
                rw [@εNFA.isPath_iff]
                left
                rw [hq'1]
                rw [hq'2]
                refine ⟨ rfl, rfl ⟩
            case cons _ _ q_mid q_prev q_final σ tail h_prev_to_mid h_path_mid_to_final h_induction=>
                rw [@εNFA.isPath_iff]
                right
                let q'_mid := 2 * q_mid
                use q'_mid, σ, tail
                constructor
                case left =>
                    unfold q'_mid
                    rw [hq'1]
                    rw [hmodzero]
                    unfold to_0mod2_εNFA
                    simp_all
                case right =>
                    constructor
                    case left =>
                        unfold q'_mid
                        rw [hq'2]
                        rw [hq'2] at h_induction
                        apply h_induction
                        rfl
                        rfl
                    case right =>
                        rfl

        apply h_A_path_A'_path q_start q_accept
        rfl
        rfl
        exact h_ispath
    case mpr =>
        rintro ⟨ q'_start, q'_accept, x', h_q'_start, h_q'_accept, h_x', h_ispath ⟩
        let q_start := q'_start / 2
        have h_q_start: q_start ∈ A.start := by
            rw [hA'start] at h_q'_start
            simp at h_q'_start
            obtain ⟨ q_orig, h_q_orig_tot ⟩ := h_q'_start
            have horig_is_even: 2 * q_orig = q'_start := by exact h_q_orig_tot.right
            have h_orig_is_start : q_orig = q_start := by
                simp [q_start]
                symm
                symm at horig_is_even
                rw [horig_is_even]
                simp
            symm at h_orig_is_start
            rw [h_orig_is_start]
            exact h_q_orig_tot.left
        let q_accept := q'_accept / 2
        have h_q_accept: q_accept ∈ A.accept := by
            rw [hA'accept] at h_q'_accept
            simp at h_q'_accept
            obtain ⟨ q_orig, h_q_orig_tot ⟩ := h_q'_accept
            have horig_is_even: 2 * q_orig = q'_accept := by exact h_q_orig_tot.right
            have h_orig_is_accept : q_orig = q_accept := by
                simp [q_accept]
                symm
                symm at horig_is_even
                rw [horig_is_even]
                simp
            symm at h_orig_is_accept
            rw [h_orig_is_accept]
            exact h_q_orig_tot.left

        use q_start, q_accept, x'
        refine ⟨ h_q_start, h_q_accept, h_x' , ?_⟩

        have h_A'_path_A_path: (q₁ q₂ q'₁ q'₂ : ℕ) → (y : List (Option alphabet)) → (q₁ = q'₁ / 2) → (q₂ = q'₂ / 2) → (A'.IsPath q'₁ q'₂ y) → (A.IsPath q₁ q₂ y) := by
            intro q₁ q₂ q'₁ q'₂ y hq1 hq2 h_A_path
            induction h_A_path generalizing q₁
            case nil _ _ q_same=>
                rw [@εNFA.isPath_iff]
                left
                rw [hq1]
                rw [hq2]
                refine ⟨ rfl, rfl ⟩
            case cons _ _ q_mid q_prev q_final σ tail h_prev_to_mid h_path_mid_to_final h_induction=>
                rw [@εNFA.isPath_iff]
                right
                let q_mid := q_mid / 2
                use q_mid, σ, tail
                constructor
                case left =>
                    unfold q_mid
                    rw [hq1]
                    sorry
                    --rw [hmodzero]
                    --unfold to_0mod2_εNFA
                    --simp_all
                case right =>
                    constructor
                    case left =>
                        unfold q_mid
                        rw [hq2]
                        rw [hq2] at h_induction
                        apply h_induction
                        rfl
                        rfl
                    case right =>
                        rfl

        apply h_A'_path_A_path q_start q_accept
        rfl
        rfl
        exact h_ispath

lemma accepts_eq_1mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    (A' = to_1mod2_εNFA A) → A.accepts = A'.accepts := by

    sorry


theorem Regex_to_εNFA (r: RegularExpression alphabet) : ∃ (A: εNFA alphabet ℕ), r.matches' = A.accepts := by
    induction r

    case zero =>
        let A : εNFA alphabet ℕ := {
            start  := ∅
            accept := ∅
            step   := fun q a => ∅
        }
        use A
        simp only [RegularExpression.zero_def, RegularExpression.matches'_zero, Language.zero_def, εNFA.accepts]
        simp only [mem_empty_iff_false, false_and, exists_false, setOf_false, ne_eq, not_true_eq_false, A]

    case epsilon =>
        let A : εNFA alphabet ℕ := {
            start  := {0}
            accept := {0}
            step   := fun q a => ∅
        }
        use A
        simp only [RegularExpression.one_def, RegularExpression.matches'_epsilon, Language.one_def, @Language.ext_iff]
        intro x
        rw [@mem_singleton_iff, A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 0, []
            exact ⟨ rfl, rfl, id (Eq.symm hx), (εNFA.isPath_nil A).mpr rfl ⟩

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩
            cases h_ispath
            case nil => exact id (Eq.symm h_x')
            case cons _ _ _ h_step _ =>
                exact False.elim h_step

    case char σ =>
        let A : εNFA alphabet ℕ := {
            start  := {0}
            accept := {1}
            step   := fun q a =>
                if (q = 0) ∧ (a = (some σ)) then
                    {1}
                else
                    ∅
        }
        use A

        simp only [RegularExpression.matches'_char, @Language.ext_iff]
        intro x
        rw [@mem_singleton_iff, A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 1, [σ]
            simp
            refine ⟨ ?_, ?_, ?_ , ?_⟩
            · rfl
            · rfl
            · exact id (Eq.symm hx)
            · simp only [A, and_self, ↓reduceIte, mem_singleton_iff]

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩

            cases h_ispath
            case nil =>
                subst h_x'
                simp_all only [mem_singleton_iff, zero_ne_one, A]
            case cons t c tail _ h_step =>
                cases c
                case none h_none =>
                    absurd h_none
                    subst A
                    simp
                case some c h_some =>
                    by_cases c = σ
                    case neg h_σ' =>
                        absurd h_some
                        subst A
                        subst h_x'
                        simp_all only [mem_singleton_iff, Option.some.injEq, and_false, ↓reduceIte,
                          mem_empty_iff_false]
                    case pos h_σ =>
                        cases tail
                        case nil =>
                            subst A
                            simp only at *
                            rw[h_σ] at h_x'
                            exact id (Eq.symm h_x')
                        case cons c' _ =>
                            rw[h_σ] at h_some
                            unfold A at h_some
                            simp at h_some
                            rw [h_some.right] at h_step
                            cases h_step
                            case cons t₂ h_t₂ _ =>
                                absurd h_t₂
                                subst A
                                simp only [one_ne_zero, false_and, ↓reduceIte, mem_empty_iff_false,
                                  not_false_eq_true]

    case plus r₁ r₂ h_r₁ h_r₂ =>
        obtain ⟨ A₁, hA₁ ⟩ := h_r₁
        obtain ⟨ A₂, hA₂ ⟩ := h_r₂

        let A₁' := to_0mod2_εNFA A₁
        let A₂' := to_1mod2_εNFA A₂

        let A : εNFA alphabet ℕ := {
            start  := A₁'.start  ∪ A₂'.start
            accept := A₁'.accept ∪ A₂'.accept
            step   := fun q c => match (q % 2), c with
                | 0, _ => A₁'.step q c
                | 1, _ => A₂'.step q c
                | _, _ => ∅
        }
        use A

        simp [RegularExpression.plus]
        rw [hA₁, hA₂, @Language.add_def, @Language.ext_iff]
        intro x
        constructor
        case mp =>
            intro h
            cases h
            case inl h_in_A₁ =>
                sorry -- STEPPPPP
            case inr h_in_A₂ =>
                sorry -- STEPPPPP
        case mpr =>
            intro h_in_A
            unfold εNFA.accepts at h_in_A
            obtain ⟨ qf, ⟨ h_qf_accept, h_qf_eval ⟩ ⟩ := h_in_A
            by_cases (qf % 2) = 0
            case pos =>
                left
                let qf_A₁ := (qf/2)
                have h_qf_accept : qf_A₁ ∈ A₁.accept := by
                    sorry
                have h_qf_eval : qf_A₁ ∈ A₁.eval x := by
                    sorry
                unfold εNFA.accepts
                simp only [mem_setOf_eq]
                exact Filter.frequently_principal.mp fun a => a h_qf_accept h_qf_eval
            case neg =>
                right
                let qf_A₂ := ((qf-1)/2)
                have h_qf_accept : qf_A₂ ∈ A₂.accept := by
                    sorry
                have h_qf_eval : qf_A₂ ∈ A₂.eval x := by
                    sorry
                unfold εNFA.accepts
                simp only [mem_setOf_eq]
                exact Filter.frequently_principal.mp fun a => a h_qf_accept h_qf_eval

    case comp r₁ r₂ h_r₁ h_r₂ =>
        obtain ⟨ A₁, hA₁ ⟩ := h_r₁
        obtain ⟨ A₂, hA₂ ⟩ := h_r₂

        let A₁' := to_0mod2_εNFA A₁
        let A₂' := to_1mod2_εNFA A₂

        let A : εNFA alphabet ℕ := {
            start  := A₁'.start
            accept := A₂'.accept
            step   := fun q c => match (q % 2), c with
                | 0, none =>
                    if (q ∈ A₁'.accept) then
                        A₁'.step q c ∪ A₂'.start
                    else
                        A₁'.step q c
                | 0, _ => A₁'.step q c
                | 1, _ => A₂'.step q c
                | _, _ => ∅
        }
        use A

        simp [RegularExpression.comp]
        rw [hA₁, hA₂, @Language.mul_def, @Language.ext_iff]
        intro x
        constructor
        case mp =>
            intro h
            rw[image2] at h
            obtain ⟨ x₁, h_x₁, x₂, h_x₂, h_comp ⟩ := h
            rw [A₁.mem_accepts_iff_exists_path] at h_x₁
            rw [A₂.mem_accepts_iff_exists_path] at h_x₂
            obtain ⟨ qs₁, qf₁, x₁', h_qs₁, h_qf₁, h_x₁', h_ispath1 ⟩ := h_x₁
            obtain ⟨ qs₂, qf₂, x₂', h_qs₂, h_qf₂, h_x₂', h_ispath2 ⟩ := h_x₂
            have h_connect_A₁_A₂ : A.IsPath (2*qf₁) (2*qs₂ + 1) [] := by
                sorry

            rw [A.mem_accepts_iff_exists_path]
            use (qs₁*2), (qf₂*2 + 1), (x₁' ++ x₂')
        case mpr =>
            sorry



    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry


def g (xs ys : List Nat) : Nat :=
    match xs, ys with
    | [a, b], _ => a+b+1
    | _, [b, c] => b+1
    | _, _ => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
    simp [g] at h;
    split at h
    simp +arith at h
