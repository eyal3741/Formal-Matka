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
            | 1, _ => {2*q' + 1 | q' ∈ (A.step (q/2) c) }
            | _, _ => ∅
        : εNFA alphabet ℕ
    }

lemma accepts_eq_0mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    (A' = to_0mod2_εNFA A) → A.accepts = A'.accepts := by
    sorry

lemma accepts_eq_1mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    (A' = to_1mod2_εNFA A) → A.accepts = A'.accepts := by
    sorry

lemma if_0mod2_step_is_0mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q₁ : ℕ) (q₂ : ℕ) (σ : Option alphabet):
    (A' = to_0mod2_εNFA A) → (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro hA' hmem
    subst hA'
    by_cases h : q₁ % 2 = 0
    ·
        have : q₂ ∈ {2*q' | q' ∈ A.step (q₁ / 2) σ} := by
            simpa [to_0mod2_εNFA, h] using hmem
        rcases this with ⟨q', _, rfl⟩
        have h2 : (2 * q') % 2 = 0 :=
            Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')
        simpa [h, h2]
    ·
        have : q₂ ∈ (∅ : Set ℕ) := by
            simp [to_0mod2_εNFA, h] at hmem
        simp at this

lemma if_1mod2_step_is_1mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q₁ : ℕ) (q₂ : ℕ) (σ : Option alphabet):
    (A' = to_1mod2_εNFA A) → (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro hA' hmem
    subst hA'
    by_cases h : q₁ % 2 = 0
    ·
        have : q₂ ∈ (∅ : Set ℕ) := by
            simp [to_1mod2_εNFA, h] at hmem
        simp at this
    ·
        have : q₂ ∈ {2*q' + 1 | q' ∈ A.step (q₁ / 2) σ} := by
            simp [to_1mod2_εNFA, h] at hmem
            simp only [mem_setOf_eq]
            simp_all only [Nat.mod_two_not_eq_zero, mem_setOf_eq]
        rcases this with ⟨q', hq', rfl⟩

        have hodd : q₁ % 2 = 1 := by

            have : q₁ % 2 = 0 ∨ q₁ % 2 = 1 := by
                exact Nat.mod_two_eq_zero_or_one q₁
            cases this with
            | inl hz => exact (h hz).elim
            | inr ho => exact ho

        have h2 : (2*q' + 1) % 2 = 1 := by
            simp
        simp [hodd, h2]

lemma if_0mod2_path_is_0mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q₁ : ℕ) (q₂ : ℕ) (x : List (Option alphabet)):
    (A' = to_0mod2_εNFA A) → (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro hA' hpath
    subst hA'
    induction hpath with
    | nil s =>
        simp only
    | cons t s u a x hstep hrest ih =>
        have hst : s % 2 = t % 2 := by
            exact if_0mod2_step_is_0mod2
                (A := A) (A' := to_0mod2_εNFA A)
                (q₁ := s) (q₂ := t) (σ := a)
                rfl hstep
        exact Eq.trans hst ih


lemma if_1mod2_path_is_1mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q₁ : ℕ) (q₂ : ℕ) (x : List (Option alphabet)):
    (A' = to_1mod2_εNFA A) → (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro hA' hpath
    subst hA'
    induction hpath with
    | nil s =>
        simp only
    | cons t s u a x hstep hrest ih =>
        have hst : s % 2 = t % 2 := by
            exact if_1mod2_step_is_1mod2
                (A := A) (A' := to_1mod2_εNFA A)
                (q₁ := s) (q₂ := t) (σ := a)
                rfl hstep
        exact Eq.trans hst ih

lemma if_0mod2_qs_is_0mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q : ℕ):
    (A' = to_0mod2_εNFA A) → q ∈ A'.start → (q % 2 = 0) := by
    intro hA' hq
    subst hA'
    simp [to_0mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')


lemma if_1mod2_qs_is_1mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q : ℕ):
    (A' = to_1mod2_εNFA A) → q ∈ A'.start → (q % 2 = 1) := by
    intro hA' hq
    subst hA'
    simp [to_1mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    simp only [Nat.mul_add_mod_self_left, Nat.mod_succ]

lemma if_0mod2_qf_is_0mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q : ℕ):
    (A' = to_0mod2_εNFA A) → q ∈ A'.accept → (q % 2 = 0) := by
    intro hA' hq
    subst hA'
    simp [to_0mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')

lemma if_1mod2_qf_is_1mod2 (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (q : ℕ):
    (A' = to_1mod2_εNFA A) → q ∈ A'.accept → (q % 2 = 1) := by
    intro hA' hq
    subst hA'
    simp [to_1mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    simp only [Nat.mul_add_mod_self_left, Nat.mod_succ]

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
            refine ⟨ ?_, ?_, ?_, ?_ ⟩
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
            step   := fun q c =>
                if (q % 2 = 0) then
                    A₁'.step q c
                else
                    A₂'.step q c
            -- match (q % 2), c with
            --     | 0, _ => A₁'.step q c
            --     | 1, _ => A₂'.step q c
            --     | _, _ => ∅
        }
        use A

        have h_A_path_implies_eq_mod2: (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (A.IsPath q₁ q₂ y') → (q₁ % 2 = q₂ % 2) := by
            intro q₁ q₂ y' h_is_path
            induction h_is_path
            case nil => exact rfl
            case cons _ _ t q₁ q₂ c y' h_step h_path h_induction =>
                rw [Eq.symm h_induction]
                unfold A at h_step
                simp only at *
                by_cases q₁ % 2 = 0
                case pos h_q₁_0mod2 =>
                    simp_rw [h_q₁_0mod2] at h_step
                    exact if_0mod2_step_is_0mod2 A₁ A₁' q₁ t c rfl h_step
                case neg h_q₁_1mod2 =>
                    simp_rw [h_q₁_1mod2] at h_step
                    exact if_1mod2_step_is_1mod2 A₂ A₂' q₁ t c rfl h_step

        simp [RegularExpression.plus]
        rw [hA₁, hA₂, @Language.add_def, @Language.ext_iff]
        intro x
        constructor
        case mp =>
            intro h
            cases h
            case inl h_in_A₁ =>
                rw [accepts_eq_0mod2_accepts A₁ A₁'] at h_in_A₁
                rw [A.mem_accepts_iff_exists_path]
                rw [A₁'.mem_accepts_iff_exists_path] at h_in_A₁
                obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₁'_path ⟩ := h_in_A₁
                use s₁, s₂, x'
                refine ⟨ ?_, ?_, ?_, ?_ ⟩
                · exact mem_union_left A₂'.start h_s₁
                · exact mem_union_left A₂'.accept h_s₂
                · exact h_x'
                ·   have hs1_even : s₁ % 2 = 0 :=
                        if_0mod2_qs_is_0mod2 (A := A₁) (A' := A₁') (q := s₁) rfl h_s₁
                    have thisA1 :
                        ∀ {q₁ q₂ : ℕ} {y : List (Option alphabet)},
                        q₁ % 2 = 0 → A₁'.IsPath q₁ q₂ y → A.IsPath q₁ q₂ y := by
                        intro q₁ q₂ y hq1_even hpath
                        induction hpath with
                        | nil q =>
                        exact (εNFA.isPath_nil A).mpr rfl
                        | cons t q₁ q₂ a tail h_step h_rest ih =>
                            constructor
                            ·
                                unfold A
                                simpa [hq1_even] using h_step
                            ·
                                have hpar : q₁ % 2 = t % 2 :=
                                    if_0mod2_step_is_0mod2
                                        (A := A₁) (A' := A₁') (q₁ := q₁) (q₂ := t) (σ := a)
                                        rfl h_step
                                have ht_even : t % 2 = 0 := by
                                    simpa [hq1_even] using hpar.symm
                                exact ih ht_even
                    exact thisA1 hs1_even h_A₁'_path
                exact rfl

            case inr h_in_A₂ =>
                rw [accepts_eq_1mod2_accepts A₂ A₂'] at h_in_A₂
                rw [A.mem_accepts_iff_exists_path]
                rw [A₂'.mem_accepts_iff_exists_path] at h_in_A₂
                obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₂'_path ⟩ := h_in_A₂
                use s₁, s₂, x'
                refine ⟨ ?_, ?_, ?_, ?_ ⟩
                · exact mem_union_right A₁'.start h_s₁
                · exact mem_union_right A₁'.accept h_s₂
                · exact h_x'
                ·   have hs1_odd : s₁ % 2 = 1 :=
                        if_1mod2_qs_is_1mod2 (A := A₂) (A' := A₂') (q := s₁) rfl h_s₁
                    have thisA1 :
                        ∀ {q₁ q₂ : ℕ} {y : List (Option alphabet)},
                        q₁ % 2 = 1 → A₂'.IsPath q₁ q₂ y → A.IsPath q₁ q₂ y := by
                        intro q₁ q₂ y hq1_odd hpath
                        induction hpath with
                        | nil q =>
                        exact (εNFA.isPath_nil A).mpr rfl
                        | cons t q₁ q₂ a tail h_step h_rest ih =>
                            constructor
                            ·
                                unfold A
                                simpa [hq1_odd] using h_step
                            ·
                                have hpar : q₁ % 2 = t % 2 :=
                                   if_1mod2_step_is_1mod2
                                        (A := A₂) (A' := A₂') (q₁ := q₁) (q₂ := t) (σ := a)
                                        rfl h_step
                                have ht_odd : t % 2 = 1 := by
                                    simpa [hq1_odd] using hpar.symm
                                exact ih ht_odd
                    exact thisA1 hs1_odd h_A₂'_path
                exact rfl



        case mpr =>
            intro h_in_A
            rw [A.mem_accepts_iff_exists_path] at h_in_A
            rw [Set.mem_union]
            obtain ⟨ qs, qf, x', h_qs, h_qf, h_x', h_A_path ⟩ := h_in_A
            by_cases (qs % 2) = 0
            case pos h_qs_is_0mod2 =>
                left
                rw [accepts_eq_0mod2_accepts A₁ A₁' rfl]
                rw [A₁'.mem_accepts_iff_exists_path]
                use qs, qf, x'
                refine ⟨ ?_, ?_, ?_, ?_ ⟩
                · simp [A] at h_qs
                  cases h_qs
                  case inl h_in_A₁' => exact h_in_A₁'
                  case inr h_in_A₂' =>
                    absurd h_qs_is_0mod2
                    simp
                    exact if_1mod2_qs_is_1mod2 A₂ A₂' qs rfl h_in_A₂'
                · by_cases (qf % 2) = 0
                  case pos h_qf_is_0mod2 =>
                    simp [A] at h_qf
                    cases h_qf
                    case inl h_qf_in_A₁'_accept => exact h_qf_in_A₁'_accept
                    case inr h_qf_in_A₂'_accept =>
                        have : qf % 2 = 1 := by
                            exact if_1mod2_qf_is_1mod2 A₂ A₂' qf rfl h_qf_in_A₂'_accept
                        absurd this
                        simp [h_qf_is_0mod2, this]
                  case neg h_qf_is_1mod2 =>
                    simp at h_qf_is_1mod2
                    absurd h_qf_is_1mod2
                    simp
                    have : qs % 2 = qf % 2 := by exact h_A_path_implies_eq_mod2 qs qf x' h_A_path
                    rw [h_qs_is_0mod2] at this
                    exact id (Eq.symm this)
                · exact h_x'
                · have : (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (q₁ % 2 = 0) → (A.IsPath q₁ q₂ y') → (A₁'.IsPath q₁ q₂ y') := by
                    intro q₁ q₂ y' h_q₁_0mod2 h_A_path
                    induction h_A_path
                    case nil qs => exact (εNFA.isPath_nil A₁').mpr rfl
                    case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
                        unfold A at h_step
                        simp only at *
                        simp_rw [h_q₁_0mod2] at h_step
                        simp at h_step
                        constructor
                        · exact h_step
                        · apply h_induction
                          have :  q₁ % 2 = t % 2 := by
                            exact if_0mod2_step_is_0mod2 A₁ A₁' q₁ t c rfl h_step
                          rw[h_q₁_0mod2] at this
                          exact Eq.symm this
                  exact this qs qf x' h_qs_is_0mod2 h_A_path
            case neg h_qs_is_1mod2 =>
                simp at h_qs_is_1mod2
                right
                rw [accepts_eq_1mod2_accepts A₂ A₂' rfl]
                rw [A₂'.mem_accepts_iff_exists_path]
                use qs, qf, x'
                refine ⟨ ?_, ?_, ?_, ?_ ⟩
                · simp [A] at h_qs
                  cases h_qs
                  case inl h_in_A₁' =>
                    absurd h_qs_is_1mod2
                    simp
                    exact if_0mod2_qs_is_0mod2 A₁ A₁' qs rfl h_in_A₁'
                  case inr h_in_A₂' => exact h_in_A₂'
                · by_cases (qf % 2) = 1
                  case pos h_qf_is_1mod2 =>
                    simp [A] at h_qf
                    cases h_qf
                    case inr h_qf_in_A₂'_accept => exact h_qf_in_A₂'_accept
                    case inl h_qf_in_A₁'_accept =>
                        have : qf % 2 = 0 := by
                            exact if_0mod2_qf_is_0mod2 A₁ A₁' qf rfl h_qf_in_A₁'_accept
                        absurd this
                        simp [h_qf_is_1mod2, this]
                  case neg h_qf_is_0mod2 =>
                    simp at h_qf_is_0mod2
                    absurd h_qf_is_0mod2
                    simp
                    have : qs % 2 = qf % 2 := by exact h_A_path_implies_eq_mod2 qs qf x' h_A_path
                    rw [h_qs_is_1mod2] at this
                    exact id (Eq.symm this)
                · exact h_x'
                · have : (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (q₁ % 2 = 1) → (A.IsPath q₁ q₂ y') → (A₂'.IsPath q₁ q₂ y') := by
                    intro q₁ q₂ y' h_q₁_1mod2 h_A_path
                    induction h_A_path
                    case nil qs => exact (εNFA.isPath_nil A₂').mpr rfl
                    case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
                        unfold A at h_step
                        simp only at *
                        simp_rw [h_q₁_1mod2] at h_step
                        simp at h_step
                        constructor
                        · exact h_step
                        · apply h_induction
                          have : t % 2 = q₁ % 2 := by
                            exact Eq.symm (if_1mod2_step_is_1mod2 A₂ A₂' q₁ t c rfl h_step)
                          rw[h_q₁_1mod2] at this
                          exact this
                  exact this qs qf x' h_qs_is_1mod2 h_A_path

    case comp r₁ r₂ h_r₁ h_r₂ =>
        obtain ⟨ A₁, hA₁ ⟩ := h_r₁
        obtain ⟨ A₂, hA₂ ⟩ := h_r₂

        let A₁' := to_0mod2_εNFA A₁
        let A₂' := to_1mod2_εNFA A₂

        let A : εNFA alphabet ℕ := {
            start  := A₁'.start
            accept := A₂'.accept
            step   := fun q c =>
                if hq : q % 2 = 0 then
                    match c with
                    | none =>
                        if q ∈ A₁'.accept then
                            A₁'.step q none ∪ A₂'.start
                        else
                            A₁'.step q none
                    | some a =>
                        A₁'.step q (some a)
                else
                    A₂'.step q c
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
            rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_x₁
            rw [accepts_eq_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_x₂
            obtain ⟨ qs₁, qf₁, x₁', h_qs₁, h_qf₁, h_x₁', h_ispath1 ⟩ := h_x₁
            obtain ⟨ qs₂, qf₂, x₂', h_qs₂, h_qf₂, h_x₂', h_ispath2 ⟩ := h_x₂
            rw [A.mem_accepts_iff_exists_path]
            use qs₁, qf₂, (x₁' ++ x₂')
            refine ⟨ ?_, ?_, ?_, ?_ ⟩
            · exact h_qs₁
            · exact h_qf₂
            · rw [Eq.symm h_comp]
              subst h_x₁' h_x₂'
              exact List.reduceOption_append x₁' x₂'
            · rw [εNFA.isPath_append]
              use qf₁
              constructor
              case left =>
                have hs1_even : qs₁ % 2 = 0 :=
                        if_0mod2_qs_is_0mod2 (A := A₁) (A' := A₁') (q := qs₁) rfl h_qs₁
                have thisA1 :
                        ∀ {q₁ q₂ : ℕ} {y : List (Option alphabet)},
                        q₁ % 2 = 0 → A₁'.IsPath q₁ q₂ y → A.IsPath q₁ q₂ y := by
                        intro q₁ q₂ y hq1_even hpath
                        induction hpath with
                        | nil q =>
                        exact (εNFA.isPath_nil A).mpr rfl
                        | cons t q₁ q₂ a tail h_step h_rest ih =>
                            constructor
                            ·
                                unfold A
                                cases a with
                                | some a' =>
                                simpa [hq1_even] using h_step
                                | none =>
                                by_cases hacc : q₁ ∈ A₁'.accept
                                ·
                                    have : t ∈ A₁'.step q₁ none := by
                                        simpa using h_step
                                    simpa [hq1_even, hacc] using Or.inl this
                                ·
                                    simpa [hq1_even, hacc] using h_step
                            ·
                                have hpar : q₁ % 2 = t % 2 :=
                                    if_0mod2_step_is_0mod2
                                        (A := A₁) (A' := A₁') (q₁ := q₁) (q₂ := t) (σ := a)
                                        rfl h_step
                                have ht_even : t % 2 = 0 := by
                                    simpa [hq1_even] using hpar.symm
                                exact ih ht_even


                exact thisA1 hs1_even h_ispath1
              case right =>
                have h_qf1_even : qf₁ % 2 = 0 :=
                        if_0mod2_qf_is_0mod2 (A := A₁) (A' := A₁') (q := qf₁) rfl h_qf₁
                have h_step_mem : qs₂ ∈ A.step qf₁ none := by
                    unfold A
                    simp [h_qf1_even, h_qf₁]
                    exact mem_union_right (A₁'.step qf₁ none) h_qs₂
                have h_epsilon : A.IsPath qf₁ qs₂ [none] := by
                    constructor
                    · exact h_step_mem
                    · exact (εNFA.isPath_nil A).mpr rfl
                have hs1_odd : qs₂ % 2 = 1 :=
                        if_1mod2_qs_is_1mod2 (A := A₂) (A' := A₂') (q := qs₂) rfl h_qs₂
                have thisA1 :
                        ∀ {q₁ q₂ : ℕ} {y : List (Option alphabet)},
                        q₁ % 2 = 1 → A₂'.IsPath q₁ q₂ y → A.IsPath q₁ q₂ y := by
                        intro q₁ q₂ y hq1_odd hpath
                        induction hpath with
                        | nil q =>
                        exact (εNFA.isPath_nil A).mpr rfl
                        | cons t q₁ q₂ a tail h_step h_rest ih =>
                            constructor
                            ·
                                unfold A
                                simpa [hq1_odd] using h_step
                            ·
                                have hpar : q₁ % 2 = t % 2 :=
                                   if_1mod2_step_is_1mod2
                                        (A := A₂) (A' := A₂') (q₁ := q₁) (q₂ := t) (σ := a)
                                        rfl h_step
                                have ht_odd : t % 2 = 1 := by
                                    simpa [hq1_odd] using hpar.symm
                                exact ih ht_odd



        case mpr =>
            sorry

    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet ℕ) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
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
