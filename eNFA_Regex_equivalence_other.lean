import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

open Set Classical

universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false


namespace εNFA

def to_0mod2 (A : εNFA α ℕ) : εNFA α ℕ := {
    start  := { 2*q' | q' ∈ A.start  }
    accept := { 2*q' | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 0 then
            { 2*q' | q' ∈ (A.step (q/2) c) }
        else
            ∅
    : εNFA α ℕ
}

def to_1mod2 (A : εNFA α ℕ) : εNFA α ℕ := {
    start  := { 2*q' + 1 | q' ∈ A.start  }
    accept := { 2*q' + 1 | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 1 then
            { 2*q' + 1 | q' ∈ (A.step ((q - 1)/2) c) }
        else
            ∅
    : εNFA α ℕ
}

def is_0mod2 (A' : εNFA α ℕ) :=
    ∃ (A : εNFA α ℕ), A' = to_0mod2 A

def is_1mod2 (A' : εNFA α ℕ) :=
    ∃ (A : εNFA α ℕ), A' = to_1mod2 A

lemma if_0mod2_step_is_0mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (σ : Option α) : (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = 0 ∧  q₂ % 2 = 0) := by
    intro h_step
    obtain ⟨A, hA⟩ := hA'

    subst hA
    simp [to_0mod2] at h_step
    omega

lemma if_1mod2_step_is_1mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (σ : Option α) : (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = 1 ∧  q₂ % 2 = 1) := by
    intro h_step
    obtain ⟨A, hA⟩ := hA'

    subst hA
    simp [to_1mod2] at h_step
    omega


lemma if_mod2_step_is_same_mod2 (A' : εNFA α ℕ) (q₁ q₂ : ℕ) (σ : Option α) :
    A'.is_0mod2 ∨ A'.is_1mod2 → (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro h_mod2_eNFA h_step
    cases h_mod2_eNFA
    case inl h_0mod2 =>
        have := if_0mod2_step_is_0mod2 A' h_0mod2 q₁ q₂ σ h_step
        omega
    case inr h_1mod2 =>
        have := if_1mod2_step_is_1mod2 A' h_1mod2 q₁ q₂ σ h_step
        omega

lemma if_0mod2_step_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (σ : Option α) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    apply if_mod2_step_is_same_mod2 A' q₁ q₂ σ
    left
    exact hA'

lemma if_1mod2_step_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (σ : Option α) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    apply if_mod2_step_is_same_mod2 A' q₁ q₂ σ
    right
    exact hA'

lemma if_mod2_path_is_same_mod2 (A' : εNFA α ℕ) (q₁ q₂ : ℕ) (x : List (Option α)):
    A'.is_0mod2 ∨ A'.is_1mod2 → (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro h_mod2_eNFA h_path
    induction h_path with
    | nil _ => rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        have := if_mod2_step_is_same_mod2 A' q₁ t c h_mod2_eNFA h_step
        omega

lemma if_0mod2_path_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (x : List (Option α)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inl hA')

lemma if_1mod2_path_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (x : List (Option α)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inr hA')

lemma if_mod2_consequences (A' : εNFA α ℕ) (q : ℕ) :
    (A'.is_0mod2 → ((q ∈ A'.start → (q % 2 = 0)) ∧ (q ∈ A'.accept → (q % 2 = 0)))) ∧
    (A'.is_1mod2 → ((q ∈ A'.start → (q % 2 = 1)) ∧ (q ∈ A'.accept → (q % 2 = 1)))) := by
    constructor <;>
    intro h_is_mod2
    <;> constructor <;>
    intro hq
    <;> obtain ⟨ A, hA ⟩ := h_is_mod2
    <;> subst hA
    <;> simp [to_0mod2, to_1mod2] at hq
    <;> omega

lemma if_0mod2_qs_is_0mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q : ℕ) (hq: q ∈ A'.start) :
    (q % 2 = 0) := ((if_mod2_consequences A' q).left hA').left hq

lemma if_1mod2_qs_is_1mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q : ℕ) (hq: q ∈ A'.start) :
    (q % 2 = 1) := ((if_mod2_consequences A' q).right hA').left hq

lemma if_0mod2_qf_is_0mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q : ℕ) (hq: q ∈ A'.accept) :
    (q % 2 = 0) := ((if_mod2_consequences A' q).left hA').right hq

lemma if_1mod2_qf_is_1mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q : ℕ) (hq: q ∈ A'.accept) :
    (q % 2 = 1) := ((if_mod2_consequences A' q).right hA').right hq

lemma path_iff_mod2_path (A : εNFA α ℕ) (A' : εNFA α ℕ) (qs qf qs' qf' : ℕ) (y : List (Option α)) :
    (((A' = A.to_0mod2) ∧ (qs' = 2 * qs)     ∧ (qf' = 2 * qf)) ∨
     ((A' = A.to_1mod2) ∧ (qs' = 2 * qs + 1) ∧ (qf' = 2 * qf + 1))) →
     ((A.IsPath qs qf y) ↔ (A'.IsPath qs' qf' y)) := by

    rintro (⟨ hA', h_qs', h_qf' ⟩ | ⟨ hA', h_qs', h_qf' ⟩)

    focus
        let s := 0
        have h_A'_mod2: A'.is_0mod2 := by use A
    swap
    focus
        let s := 1
        have h_A'_mod2: A'.is_1mod2 := by use A

    all_goals constructor
    case inl.mp | inr.mp =>
        intro h_path_in_A
        induction h_path_in_A generalizing qs'
        case nil => simp [εNFA.isPath_nil]; omega
        case cons t q₁ q₂ σ tail h_step h_path h_induction =>
            rw [@εNFA.isPath_iff]
            right
            let t' := 2 * t + s
            subst s
            use t', σ, tail
            have h_t'_step: t' ∈ A'.step qs' σ := by simp_all [t', to_0mod2, to_1mod2]
            have h_t'_path: A'.IsPath t' qf' tail := by simp_all [t']
            exact ⟨ h_t'_step, h_t'_path, rfl ⟩

    case inl.mpr | inr.mpr =>
        intro h_path_in_A'
        induction h_path_in_A' generalizing qs
        case nil => simp [εNFA.isPath_nil]; omega
        case cons t' q₁' q₂' σ tail h_step h_path h_induction =>
            rw [@εNFA.isPath_iff]
            right
            let t := (t' - s) / 2
            use t, σ, tail

            have h_t'_0mod2: t' % 2 = s := by
                try exact (if_0mod2_step_is_0mod2 A' h_A'_mod2 q₁' t' σ h_step).right
                try exact (if_1mod2_step_is_1mod2 A' h_A'_mod2 q₁' t' σ h_step).right
            have h_t'_2t: t' = 2 * t + s := by omega

            subst s
            have h_t_step: t ∈ A.step qs σ := by simp_all [to_0mod2, to_1mod2]
            have h_t_path: A.IsPath t qf tail := by simp_all

            exact ⟨ h_t_step, h_t_path, rfl ⟩

lemma path_iff_0mod2_path (A : εNFA α ℕ) (A' : εNFA α ℕ) (qs qf qs' qf' : ℕ) (y : List (Option α))
    (hA': A' = to_0mod2 A) (h_qs': qs' = 2 * qs) (h_qf': qf' = 2 * qf) :
    (A.IsPath qs qf y) ↔ (A'.IsPath qs' qf' y) :=
    (path_iff_mod2_path A A' qs qf qs' qf' y (Or.inl ⟨ hA', h_qs', h_qf' ⟩))

lemma path_iff_1mod2_path (A : εNFA α ℕ) (A' : εNFA α ℕ) (qs qf qs' qf' : ℕ) (y : List (Option α))
    (hA': A' = to_1mod2 A) (h_qs': qs' = 2 * qs + 1) (h_qf': qf' = 2 * qf + 1) :
    (A.IsPath qs qf y) ↔ (A'.IsPath qs' qf' y) :=
    (path_iff_mod2_path A A' qs qf qs' qf' y (Or.inr ⟨ hA', h_qs', h_qf' ⟩))

lemma accepts_iff_mod2_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) :
    (A' = to_0mod2 A) ∨ (A' = to_1mod2 A) → A.accepts = A'.accepts := by
    rintro (hA' | hA')

    all_goals
        rw [@Language.ext_iff]
        intro x
        rw [A.mem_accepts_iff_exists_path, A'.mem_accepts_iff_exists_path]

    focus
        let s := 0
        have h_A'_mod2: A'.is_0mod2 := by use A
        have h_A'_start:  A'.start =  { 2*q' + s | q' ∈ A.start  } := by simp_all [s, to_0mod2]
        have h_A'_accept: A'.accept = { 2*q' + s | q' ∈ A.accept } := by simp_all [s, to_0mod2]
    swap
    focus
        let s := 1
        have h_A'_mod2: A'.is_1mod2 := by use A
        have h_A'_start:  A'.start =  { 2*q' + s | q' ∈ A.start  } := by simp_all [s, to_1mod2]
        have h_A'_accept: A'.accept = { 2*q' + s | q' ∈ A.accept } := by simp_all [s, to_1mod2]

    all_goals constructor
    case inl.mp | inr.mp =>
        rintro ⟨ qs, qf, x', h_qs, h_qf, h_x', h_path_in_A ⟩
        let qs' := 2 * qs + s
        let qf' := 2 * qf + s
        subst s
        have h_qs': qs' ∈ A'.start  := by simp_all [qs']
        have h_qf': qf' ∈ A'.accept := by simp_all [qf']
        have h_iff_path : A.IsPath qs qf x' ↔ A'.IsPath qs' qf' x' := by
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inl ⟨ hA', rfl, rfl ⟩)
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inr ⟨ hA', rfl, rfl ⟩)

        use qs', qf', x'
        exact ⟨ h_qs', h_qf', h_x', h_iff_path.mp h_path_in_A ⟩

    case inl.mpr | inr.mpr =>
        rintro ⟨ qs', qf', x', h_qs', h_qf', h_x', h_path_in_A' ⟩
        let qs := (qs' - s) / 2
        let qf := (qf' - s) / 2

        have h_qs'_qf'_mod2: qs' % 2 = s ∧ qf' % 2 = s := by
            try exact ⟨ if_0mod2_qs_is_0mod2 A' h_A'_mod2 qs' h_qs', if_0mod2_qf_is_0mod2 A' h_A'_mod2 qf' h_qf' ⟩
            try exact ⟨ if_1mod2_qs_is_1mod2 A' h_A'_mod2 qs' h_qs', if_1mod2_qf_is_1mod2 A' h_A'_mod2 qf' h_qf' ⟩

        have h_qs'_2qs: qs' = 2 * qs + s := by grind only
        have h_qf'_2qf: qf' = 2 * qf + s := by grind only

        subst s
        have h_qs: qs ∈ A.start  := by simp_all
        have h_qf: qf ∈ A.accept := by simp_all
        have h_iff_path : A.IsPath qs qf x' ↔ A'.IsPath qs' qf' x' := by
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inl ⟨ hA', h_qs'_2qs, h_qf'_2qf ⟩)
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inr ⟨ hA', h_qs'_2qs, h_qf'_2qf ⟩)

        use qs, qf, x'
        exact ⟨ h_qs, h_qf, h_x', h_iff_path.mpr h_path_in_A' ⟩

lemma accepts_iff_0mod2_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = to_0mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inl hA')

lemma accepts_iff_1mod2_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = to_1mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inr hA')

end εNFA


namespace εNFA

def contains (A : εNFA α ℕ) (A' : εNFA α ℕ) :=
    ∀ (q : ℕ), ∀ (σ: Option α), A'.step q σ ⊆ A.step q σ

lemma path_if_contains (A : εNFA α ℕ) (A' : εNFA α ℕ) (h_contains: A.contains A')
    (q₁ q₂ : ℕ) (x : List (Option α)) :
    A'.IsPath q₁ q₂ x → A.IsPath q₁ q₂ x := by
    intro h_path_in_A'
    unfold contains at h_contains
    induction h_path_in_A' with
    | nil q => exact A.isPath_nil.mpr rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        constructor
        · exact mem_preimage.mp (h_contains q₁ c h_step)
        · exact h_induction


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- ZERO -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

def εNFA_zero : εNFA α ℕ := {
    start  := ∅
    accept := ∅
    step   := fun _ _ => ∅
}

lemma Zero_Regex_to_εNFA :
    ∃ (A: εNFA α ℕ), RegularExpression.zero.matches' = A.accepts := by
        use εNFA_zero
        simp [εNFA_zero, εNFA.accepts, Language.zero_def]


 -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- EPSILON -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- -- --

def εNFA_epsilon : εNFA α ℕ := {
    start  := {0}
    accept := {0}
    step   := fun _ _ => ∅
}

lemma Epsilon_Regex_to_εNFA :
    ∃ (A: εNFA α ℕ), RegularExpression.epsilon.matches' = A.accepts := by
        let A : εNFA α ℕ := εNFA_epsilon
        use A
        simp only [RegularExpression.one_def, RegularExpression.matches'_epsilon, Language.one_def, @Language.ext_iff]
        intro x
        rw [@mem_singleton_iff, A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 0, []
            exact ⟨ rfl, rfl, id (Eq.symm hx), (A.isPath_nil).mpr rfl ⟩

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩
            cases h_ispath
            case nil => exact id (Eq.symm h_x')
            case cons _ _ _ h_step _ =>
                exact False.elim h_step


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- CHAR -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

def εNFA_char (σ : α) : εNFA α ℕ := {
    start  := {0}
    accept := {1}
    step   := fun q a =>
        if (q = 0) ∧ (a = (some σ)) then
            {1}
        else
            ∅
}

lemma Char_Regex_to_εNFA (σ : α) :
    ∃ (A: εNFA α ℕ), (RegularExpression.char σ).matches' = A.accepts := by
        let A := εNFA_char σ
        use A

        simp only [RegularExpression.matches'_char, @Language.ext_iff]
        intro x
        rw [@mem_singleton_iff, A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 1, [σ]
            simp
            have : 1 ∈ A.step 0 (some σ) := by simp [A, εNFA_char]
            exact ⟨ rfl, rfl, symm hx, this ⟩

        case mpr =>
            rintro ⟨ qs, qf, x', h_qs, h_qf, h_x', h_ispath ⟩

            cases h_ispath
            case nil => simp_all [A, εNFA_char]
            case cons t c tail _ h_step =>
                cases c
                case none h_none =>
                    absurd h_none
                    simp [A, εNFA_char]

                case some c h_some =>
                    by_cases h_σ: c = σ
                    case pos =>
                        cases tail
                        case nil =>
                            subst A h_σ
                            exact symm h_x'
                        case cons c' _ =>
                            subst h_σ A
                            simp [εNFA_char] at h_some
                            rw [h_some.right] at h_step
                            cases h_step
                            case cons t₂ h_t₂ _ =>
                                absurd h_t₂
                                simp [εNFA_char]
                    case neg =>
                        subst h_x' A
                        absurd h_some
                        simp [εNFA_char]
                        intro h_qs h_qc
                        simp [h_σ] at h_qc -- contradiction


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- PLUS -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

def εNFA_plus (A₁: εNFA α ℕ) (A₂: εNFA α ℕ) : εNFA α ℕ := {
    start  := A₁.start  ∪ A₂.start
    accept := A₁.accept ∪ A₂.accept
    step   := fun q c =>
        if (q % 2 = 0) then
            A₁.step q c
        else
            A₂.step q c
}

lemma Plus_Regex_to_εNFA (r₁ r₂ : RegularExpression α) :
     (∃ (A₁: εNFA α ℕ), r₁.matches' = A₁.accepts) →
     (∃ (A₂: εNFA α ℕ), r₂.matches' = A₂.accepts) →
     ∃ (A: εNFA α ℕ), (r₁.plus r₂).matches' = A.accepts := by
    intro h_r₁ h_r₂
    obtain ⟨ A₁, hA₁ ⟩ := h_r₁
    obtain ⟨ A₂, hA₂ ⟩ := h_r₂

    let A₁' := A₁.to_0mod2
    let A₂' := A₂.to_1mod2
    have hA₁' : A₁'.is_0mod2 := by use A₁
    have hA₂' : A₂'.is_1mod2 := by use A₂

    let A : εNFA α ℕ := εNFA_plus A₁' A₂'
    use A

    have h_A_contains_A₁' : A.contains A₁' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 0
        case pos h_0mod2 => simp [A, εNFA_plus, h_0mod2]
        case neg h_1mod2 => simp [A₁', to_0mod2, h_1mod2]

    have h_A_contains_A₂' : A.contains A₂' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 1
        case pos h_1mod2 => simp [A, εNFA_plus, h_1mod2]
        case neg h_0mod2 => simp [A₂', to_1mod2, h_0mod2]

    have h_A_path_implies_eq_mod2: (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option α)) → (A.IsPath q₁ q₂ y') → (q₁ % 2 = q₂ % 2) := by
        intro q₁ q₂ y' h_is_path
        induction h_is_path
        case nil => exact rfl
        case cons _ _ t q₁ q₂ c y' h_step h_path h_induction =>
            rw [symm h_induction]
            simp_rw [A, εNFA_plus] at h_step
            by_cases q₁ % 2 = 0
            case pos h_q₁_0mod2 =>
                simp_rw [h_q₁_0mod2] at h_step
                exact if_0mod2_step_is_same_mod2 A₁' hA₁' q₁ t c h_step
            case neg h_q₁_1mod2 =>
                simp_rw [h_q₁_1mod2] at h_step
                exact if_1mod2_step_is_same_mod2 A₂' hA₂' q₁ t c h_step

    simp [hA₁, hA₂, @Language.add_def, @Language.ext_iff]
    intro x
    constructor
    case mp =>
        intro h
        cases h
        case inl h_in_A₁ =>
            rw [accepts_iff_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_in_A₁
            rw [A.mem_accepts_iff_exists_path]
            obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₁'_path ⟩ := h_in_A₁
            use s₁, s₂, x'
            exact ⟨ mem_union_left A₂'.start h_s₁,
                    mem_union_left A₂'.accept h_s₂,
                    h_x',
                    path_if_contains A A₁' h_A_contains_A₁' s₁ s₂ x' h_A₁'_path ⟩

        case inr h_in_A₂ =>
            rw [accepts_iff_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_in_A₂
            rw [A.mem_accepts_iff_exists_path]
            obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₂'_path ⟩ := h_in_A₂
            use s₁, s₂, x'
            exact ⟨ mem_union_right A₁'.start h_s₁,
                    mem_union_right A₁'.accept h_s₂,
                    h_x',
                    path_if_contains A A₂' h_A_contains_A₂' s₁ s₂ x' h_A₂'_path ⟩

    case mpr =>
        intro h_in_A
        rw [A.mem_accepts_iff_exists_path] at h_in_A
        rw [Set.mem_union]
        obtain ⟨ qs, qf, x', h_qs, h_qf, h_x', h_A_path ⟩ := h_in_A
        by_cases (qs % 2) = 0
        case pos h_qs_is_0mod2 =>
            left
            rw [accepts_iff_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path]
            use qs, qf, x'

            have h_qs_start : qs ∈ A₁'.start := by
                simp [A] at h_qs
                cases h_qs
                case inl h_in_A₁' => exact h_in_A₁'
                case inr h_in_A₂' =>
                    absurd h_qs_is_0mod2
                    simp
                    exact if_1mod2_qs_is_1mod2 A₂' hA₂' qs h_in_A₂'

            have h_qf_accept : qf ∈ A₁'.accept := by
                by_cases (qf % 2) = 0
                case pos h_qf_is_0mod2 =>
                    simp [A] at h_qf
                    cases h_qf
                    case inl h_qf_in_A₁'_accept => exact h_qf_in_A₁'_accept
                    case inr h_qf_in_A₂'_accept =>
                        absurd if_1mod2_qf_is_1mod2 A₂' hA₂' qf h_qf_in_A₂'_accept
                        simp [h_qf_is_0mod2]
                case neg h_qf_is_1mod2 =>
                    simp at h_qf_is_1mod2
                    absurd h_qf_is_1mod2
                    simp
                    have : qs % 2 = qf % 2 := h_A_path_implies_eq_mod2 qs qf x' h_A_path
                    rw [h_qs_is_0mod2] at this
                    exact symm this

            have h_path_qs_to_qf_x' : (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option α)) → (q₁ % 2 = 0) → (A.IsPath q₁ q₂ y') → (A₁'.IsPath q₁ q₂ y') := by
                intro q₁ q₂ y' h_q₁_0mod2 h_A_path
                induction h_A_path
                case nil qs => exact (εNFA.isPath_nil A₁').mpr rfl
                case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
                    unfold A at h_step
                    simp only at *
                    simp_rw [εNFA_plus, h_q₁_0mod2] at h_step
                    simp at h_step
                    constructor
                    · exact h_step
                    · apply h_induction
                      have : q₁ % 2 = t % 2 := if_0mod2_step_is_same_mod2 A₁' hA₁' q₁ t c h_step
                      rw [h_q₁_0mod2] at this
                      exact symm this

            exact ⟨ h_qs_start, h_qf_accept, h_x',
                    h_path_qs_to_qf_x' qs qf x' h_qs_is_0mod2 h_A_path ⟩
        case neg h_qs_1mod2 =>
            simp at h_qs_1mod2
            right
            rw [accepts_iff_1mod2_accepts A₂ A₂' rfl]
            rw [A₂'.mem_accepts_iff_exists_path]
            use qs, qf, x'

            have h_qs_start : qs ∈ A₂'.start := by
                simp [A] at h_qs
                cases h_qs
                case inl h_in_A₁' =>
                    absurd h_qs_1mod2
                    simp
                    exact if_0mod2_qs_is_0mod2 A₁' hA₁' qs h_in_A₁'
                case inr h_in_A₂' => exact h_in_A₂'

            have h_qf_accept : qf ∈ A₂'.accept := by
                by_cases (qf % 2) = 1
                case pos h_qf_1mod2 =>
                    simp [A] at h_qf
                    cases h_qf
                    case inr h_qf_in_A₂'_accept => exact h_qf_in_A₂'_accept
                    case inl h_qf_in_A₁'_accept =>
                        absurd if_0mod2_qf_is_0mod2 A₁' hA₁' qf h_qf_in_A₁'_accept
                        simp [h_qf_1mod2]
                case neg h_qf_0mod2 =>
                    simp at h_qf_0mod2
                    absurd h_qf_0mod2
                    simp
                    have : qs % 2 = qf % 2 := h_A_path_implies_eq_mod2 qs qf x' h_A_path
                    rw [h_qs_1mod2] at this
                    exact symm this

            have h_path_qs_to_qf_x': (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option α)) → (q₁ % 2 = 1) → (A.IsPath q₁ q₂ y') → (A₂'.IsPath q₁ q₂ y') := by
                intro q₁ q₂ y' h_q₁_1mod2 h_A_path
                induction h_A_path
                case nil qs => exact (εNFA.isPath_nil A₂').mpr rfl
                case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
                    unfold A at h_step
                    simp only at *
                    simp_rw [εNFA_plus, h_q₁_1mod2] at h_step
                    simp at h_step
                    constructor
                    · exact h_step
                    · apply h_induction
                      have : q₁ % 2 = t % 2 := if_1mod2_step_is_same_mod2 A₂' hA₂' q₁ t c h_step
                      rw [h_q₁_1mod2] at this
                      exact symm this

            exact ⟨ h_qs_start, h_qf_accept, h_x',
                    h_path_qs_to_qf_x' qs qf x' h_qs_1mod2 h_A_path ⟩


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- COMP -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

def εNFA_comp (A₁: εNFA α ℕ) (A₂: εNFA α ℕ) (_ : A₁.is_0mod2) (_ : A₂.is_1mod2) : εNFA α ℕ := {
    start  := A₁.start
    accept := A₂.accept
    step   := fun q c =>
        if q % 2 = 0 then
            if q ∈ A₁.accept ∧ c = none then
                A₁.step q c ∪ A₂.start
            else
                A₁.step q c
        else
            A₂.step q c
}

lemma comp_step_1mod2_to_1mod2 (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (q₁ q : ℕ)  :
    ∀ (c : Option α), q₁ % 2 = 1 → (q ∈ A.step q₁ c) → q % 2 = 1 := by
    rintro  c h_q₁_1mod2 h_q
    simp [hA, εNFA_comp, h_q₁_1mod2] at h_q
    have h_q₁_eq_q_mod2 := if_1mod2_step_is_same_mod2 A₂' hA₂' (q₁ := q₁) (q₂ := q) c h_q
    simp [symm h_q₁_eq_q_mod2, h_q₁_1mod2]

lemma comp_path_1mod2_to_0mod2_is_empty (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (q₁ q₂ : ℕ):
    ∀ (x' : List (Option α)), q₁ % 2 = 1 ∧ q₂ % 2 = 0 → ¬A.IsPath q₁ q₂ x' := by
    rintro x' ⟨ h_q₁, h_q₂ ⟩ h
    induction h with
    | nil => absurd h_q₁; simp; exact h_q₂
    | cons t q₁ q₂ c tail h_step h_path h_induction =>
        by_cases t % 2 = 0
        case pos h_t_0mod2 =>
            absurd h_t_0mod2
            simp
            exact comp_step_1mod2_to_1mod2 A A₁' A₂' hA₁' hA₂' hA q₁ t c h_q₁ h_step
        case neg h_t_1mod2 =>
            simp at h_t_1mod2
            simp [h_t_1mod2] at h_induction
            absurd h_induction
            exact Nat.mod_two_ne_one.mpr h_q₂

lemma comp_path_0mod2 (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option α)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 0 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option α)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 0 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_1mod2
    have h_t_1mod2 : t % 2 = 1 := Nat.mod_two_ne_zero.mp h_t_1mod2
    absurd h_path_t_q₂
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA₁' hA₂' hA t q₂ b' ⟨ h_t_1mod2, h_q₂ ⟩

lemma comp_path_0mod2_in_A₁' (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option α)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 0 → (A₁'.IsPath q₁ q₂ x') := by
    rintro ⟨ h_path_in_A, h_q₁, h_q₂ ⟩
    induction h_path_in_A with
    | nil => exact (isPath_nil A₁').mpr rfl
    | cons t q₁ q₂ c tail h_step h_path h_induction =>
        by_cases t % 2 = 0
        case pos h_t_0mod2 =>
            simp [h_t_0mod2, h_q₂] at h_induction
            have h_path_q₁_t : A₁'.IsPath q₁ t [c] := by
                simp [hA, εNFA_comp, h_q₁] at h_step
                split_ifs at h_step
                case pos q₁_acc =>
                    simp at h_step
                    cases h_step
                    case inl h_step => apply A₁'.isPath_singleton.mpr h_step
                    case inr h_start =>
                        by_contra!
                        simp [if_1mod2_qs_is_1mod2 A₂' hA₂' t h_start] at h_t_0mod2
                case neg h_n => exact IsPath.singleton A₁' h_step

            exact A₁'.isPath_append.mpr ⟨ t, ⟨ h_path_q₁_t, h_induction ⟩ ⟩

        case neg h_t_1mod2 =>
            simp at h_t_1mod2
            absurd h_path
            exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA₁' hA₂' hA t q₂ tail ⟨ h_t_1mod2, h_q₂ ⟩

lemma comp_path_1mod2 (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option α)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 1 ∧ q₂ % 2 = 1 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option α)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 1 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_0mod2
    have h_t_0mod2 : t % 2 = 0 := Nat.mod_two_ne_one.mp h_t_0mod2
    absurd h_path_q₁_t
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA₁' hA₂' hA q₁ t a' ⟨ h_q₁, h_t_0mod2 ⟩

lemma comp_path_1mod2_in_A₂' (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option α)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 1 ∧ q₂ % 2 = 1 → (A₂'.IsPath q₁ q₂ x') := by
    rintro ⟨ h_path_in_A, h_q₁, h_q₂ ⟩
    induction h_path_in_A with
    | nil => exact (isPath_nil A₂').mpr rfl
    | cons t q₁ q₂ c tail h_step h_path h_induction =>
        by_cases t % 2 = 1
        case pos h_t_1mod2 =>
            simp [h_t_1mod2, h_q₂] at h_induction
            have h_path_q₁_t : A₂'.IsPath q₁ t [c] := by
                simp [hA, εNFA_comp, h_q₁] at h_step
                exact IsPath.singleton A₂' h_step

            exact A₂'.isPath_append.mpr ⟨ t, ⟨ h_path_q₁_t, h_induction ⟩ ⟩

        case neg h_t_0mod2 =>
            simp at h_t_0mod2
            simp [hA, εNFA_comp, h_q₁] at h_step
            have h_t : q₁ % 2 = t % 2 :=
                if_1mod2_step_is_same_mod2 A₂' hA₂' q₁ t c h_step
            simp [h_q₁, h_t_0mod2] at h_t

lemma comp_step_change_mod_implies_epsilon (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (c : Option α) :
    q₂ ∈ A.step q₁ c ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 1 → c = none := by
    rintro ⟨ h_step, h_q₁, h_q₂ ⟩
    by_contra! h_c_some
    simp [hA, εNFA_comp, h_q₁] at h_step

    by_cases h_q₁_accept: q₁ ∈ A₁'.accept
    case pos =>
        simp [h_q₁_accept, h_c_some] at h_step
        have : q₁ % 2 = q₂ % 2 := if_0mod2_step_is_same_mod2 A₁' hA₁' q₁ q₂ c h_step
        simp [h_q₁, h_q₂] at this
    case neg =>
        simp [h_q₁_accept] at h_step
        have : q₁ % 2 = q₂ % 2 := if_0mod2_step_is_same_mod2 A₁' hA₁' q₁ q₂ c h_step
        simp [h_q₁, h_q₂] at this

lemma comp_path_decomposition (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') :
    ∀ (qs qf : ℕ), ∀ (y : List α), ∀ (y' : List (Option α)),
    qs % 2 = 0 ∧ qf % 2 = 1 ∧ y = y'.reduceOption ∧ A.IsPath qs qf y' →
    ∃ (qf₁ qs₂ : ℕ), ∃ (a' b' : List (Option α)),
    (qf₁ % 2 = 0) ∧ (qs₂ % 2 = 1) ∧ ((a' ++ ([none] ++ b')).reduceOption = y) ∧
    qf₁ ∈ A.evalFrom {qs} a'.reduceOption ∧ qf ∈ A.evalFrom {qs₂} b'.reduceOption ∧
    qs₂ ∈ A.step qf₁ none := by
    rintro qs qf y y' ⟨ h_qs, h_qf, h_y', h_path ⟩

    induction h_path generalizing y with
    | nil => simp [h_qs] at h_qf
    | cons t qs qf c tail h_step h_path h_induction =>
        by_cases t % 2 = 0
        case pos h_t_0mod2 =>
            simp [h_t_0mod2, h_qf] at h_induction
            obtain ⟨ qf₁, h_qf₁, qs₂, h_qs₂, a'', b', h_tail, h_eval_t_qf₁, h_eval_qs₂_qf₂, h_none ⟩ := h_induction
            let a' := [c] ++ a''
            use qf₁, qs₂, a', b'

            have h_y : (a' ++ ([none] ++ b')).reduceOption = y := by
                simp [List.reduceOption_append] at h_tail
                have : (c :: tail).reduceOption = ([c] ++ tail).reduceOption := List.toList_toArray
                simp_rw [this] at h_y'
                subst a' h_y'
                simp_rw [List.reduceOption_append]
                simp
                exact h_tail

            have h_evalfrom_qs_qf₁_a' : qf₁ ∈ A.evalFrom {qs} a'.reduceOption := by
                subst a'
                rw [mem_evalFrom_iff_exists_path]
                obtain ⟨ w, ⟨ h_w, h_path_t_qf₁ ⟩ ⟩ := A.mem_evalFrom_iff_exists_path.mp h_eval_t_qf₁
                use ([c] ++ w)
                constructor
                case left =>
                    rw [List.reduceOption_append]
                    symm
                    rw [List.reduceOption_append]
                    simp [h_w]
                case right =>
                    apply A.isPath_append.mpr ⟨ t, A.isPath_singleton.mpr h_step, h_path_t_qf₁ ⟩

            exact ⟨ h_qf₁, h_qs₂, h_y, h_evalfrom_qs_qf₁_a', h_eval_qs₂_qf₂, h_none ⟩

        case neg h_t_1mod2 =>
            simp at h_t_1mod2
            use qs, t, [c], tail

            have h_c_none : c = none :=
                comp_step_change_mod_implies_epsilon A A₁' A₂' hA₁' hA₂' hA qs t c ⟨ h_step, h_qs, h_t_1mod2 ⟩
            subst h_c_none

            have h_y : ([none] ++ ([none] ++ tail)).reduceOption = y := by simp [h_y']

            have h_qs_eval : qs ∈ A.evalFrom {qs} [none].reduceOption := by
                simp [List.reduceOption_nil]
                tauto

            have h_qf_eval : qf ∈ A.evalFrom {t} tail.reduceOption :=
                A.mem_evalFrom_iff_exists_path.mpr ⟨ tail, rfl, h_path ⟩

            exact ⟨ h_qs, h_t_1mod2, h_y, h_qs_eval, h_qf_eval, h_step ⟩

lemma comp_word_decomposition (A A₁' A₂': εNFA α ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (x : List α) :
    (x ∈ A.accepts) → ∃ (a b : List α), (x = a ++ b) ∧ (a ∈ A₁'.accepts) ∧ (b ∈ A₂'.accepts) := by
    intro h_x
    have ⟨ qs₁, qf₂, x', h_qs₁, h_qf₂, h_x', h_x'_path  ⟩ := A.mem_accepts_iff_exists_path.mp h_x
    simp [hA, εNFA_comp] at h_qs₁ h_qf₂
    have h_qs₁_0mod2 : qs₁ % 2 = 0 := if_0mod2_qs_is_0mod2 A₁' hA₁' qs₁ h_qs₁
    have h_qf₂_1mod2 : qf₂ % 2 = 1 := if_1mod2_qf_is_1mod2 A₂' hA₂' qf₂ h_qf₂

    have h_comp := comp_path_decomposition A A₁' A₂' hA₁' hA₂' hA qs₁ qf₂ x x' ⟨ h_qs₁_0mod2, h_qf₂_1mod2, symm h_x', h_x'_path ⟩
    obtain ⟨ qf₁, qs₂, a', b', h_qf₁, h_qs₂, h_a'b', h_eval_a', h_eval_b', h_step ⟩ := h_comp

    have h_qf₁_A₁'_accept : qf₁ ∈ A₁'.accept := by
        by_contra!
        simp [hA, εNFA_comp, this, h_qf₁] at h_step
        simp [if_0mod2_step_is_same_mod2 A₁' hA₁' qf₁ qs₂ none h_step] at h_qf₁
        simp [h_qf₁] at h_qs₂

    have h_qs₂_A₂'_start : qs₂ ∈ A₂'.start := by
        simp [hA, εNFA_comp, h_qf₁, h_qf₁_A₁'_accept] at h_step
        by_cases qs₂ ∈ A₂'.start
        case pos h_start => exact h_start
        case neg h_no_start =>
            simp [h_no_start] at h_step
            simp [if_0mod2_step_is_same_mod2 A₁' hA₁' qf₁ qs₂ none h_step, h_qs₂] at h_qf₁

    let a := a'.reduceOption
    let b := b'.reduceOption
    use a, b

    have h_x_ab : x = a ++ b := by
        rw [Eq.symm h_a'b']
        subst a b
        exact List.reduceOption_append a' ([none] ++ b')

    have h_A₁'_accepts_a : a ∈ A₁'.accepts := by
        rw [A₁'.mem_accepts_iff_exists_path]
        obtain ⟨ w, ⟨ h_w, h_path_qs₁_qf₁ ⟩ ⟩ := A.mem_evalFrom_iff_exists_path.mp h_eval_a'
        use qs₁, qf₁, w
        have h_A₁'_path_w := comp_path_0mod2_in_A₁' A A₁' A₂' hA₁' hA₂' hA qs₁ qf₁ w  ⟨ h_path_qs₁_qf₁, h_qs₁_0mod2, h_qf₁ ⟩
        exact ⟨ h_qs₁, h_qf₁_A₁'_accept, h_w, h_A₁'_path_w ⟩

    have h_A₂'_accepts_b : b ∈ A₂'.accepts := by
        rw [A₂'.mem_accepts_iff_exists_path]
        obtain ⟨ w, ⟨ h_w, h_path_qs₂_qf₂ ⟩ ⟩ := A.mem_evalFrom_iff_exists_path.mp h_eval_b'
        use qs₂, qf₂, w
        have h_A₂'_path_w := comp_path_1mod2_in_A₂' A A₁' A₂' hA₁' hA₂' hA qs₂ qf₂ w ⟨ h_path_qs₂_qf₂, h_qs₂, h_qf₂_1mod2⟩
        exact ⟨ h_qs₂_A₂'_start, h_qf₂, h_w, h_A₂'_path_w ⟩

    exact ⟨ h_x_ab, h_A₁'_accepts_a, h_A₂'_accepts_b ⟩

lemma Comp_Regex_to_εNFA (r₁ r₂ : RegularExpression α) :
     (∃ (A₁: εNFA α ℕ), r₁.matches' = A₁.accepts) →
     (∃ (A₂: εNFA α ℕ), r₂.matches' = A₂.accepts) →
     ∃ (A: εNFA α ℕ), (r₁.comp r₂).matches' = A.accepts := by
    intro h_r₁ h_r₂
    obtain ⟨ A₁, hA₁ ⟩ := h_r₁
    obtain ⟨ A₂, hA₂ ⟩ := h_r₂

    let A₁' := A₁.to_0mod2
    let A₂' := A₂.to_1mod2

    have hA₁' : A₁'.is_0mod2 := by use A₁
    have hA₂' : A₂'.is_1mod2 := by use A₂

    let A : εNFA α ℕ := εNFA_comp A₁' A₂' hA₁' hA₂'
    use A

    have h_A_contains_A₁' : A.contains A₁' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 0
        case pos h_0mod2 =>
            simp [A, εNFA_comp, h_0mod2]
            split_ifs <;>
            simp only [subset_union_left, subset_refl]
        case neg h_1mod2 => simp [A₁', to_0mod2, h_1mod2]

    have h_A_contains_A₂' : A.contains A₂' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 1
        case pos h_1mod2 => simp [A, εNFA_comp, h_1mod2]
        case neg h_0mod2 => simp [A₂', to_1mod2, h_0mod2]

    simp only [RegularExpression.matches']
    rw [hA₁, hA₂, @Language.mul_def, @Language.ext_iff]
    intro x
    constructor
    case mp =>
        intro h_in_image
        rw [image2] at h_in_image
        obtain ⟨ x₁, h_x₁, x₂, h_x₂, h_comp ⟩ := h_in_image
        rw [accepts_iff_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_x₁
        rw [accepts_iff_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_x₂
        obtain ⟨ qs₁, qf₁, x₁', h_qs₁, h_qf₁, h_x₁', h_ispath1 ⟩ := h_x₁
        obtain ⟨ qs₂, qf₂, x₂', h_qs₂, h_qf₂, h_x₂', h_ispath2 ⟩ := h_x₂
        rw [A.mem_accepts_iff_exists_path]

        let x' :=  (x₁' ++ ([none] ++ x₂'))
        use qs₁, qf₂, x'

        have h_x' : x'.reduceOption = x := by
            rw [Eq.symm h_comp]
            subst h_x₁' h_x₂'
            exact List.reduceOption_append x₁' ([none] ++ x₂')

        have h_A_path_qs₁_qf₂_x : A.IsPath qs₁ qf₂ x' := by
            rw [isPath_append]
            use qf₁
            constructor
            case left => exact path_if_contains A A₁' h_A_contains_A₁' qs₁ qf₁ x₁' h_ispath1
            case right =>
                have h_qf1_even : qf₁ % 2 = 0 :=
                        if_0mod2_qf_is_0mod2 A₁' hA₁' (q := qf₁) h_qf₁
                have h_step_mem : qs₂ ∈ A.step qf₁ none := by
                    unfold A
                    simp [εNFA_comp, h_qf1_even, h_qf₁]
                    exact mem_union_right (A₁'.step qf₁ none) h_qs₂
                have h_epsilon : A.IsPath qf₁ qs₂ [none] := by
                    constructor
                    · exact h_step_mem
                    · exact (εNFA.isPath_nil A).mpr rfl
                have h_connect : ∃ (t : ℕ), A.IsPath qf₁ t [none] ∧ A.IsPath t qf₂ x₂' := by
                    use qs₂
                    constructor
                    case left => exact h_epsilon
                    case right => exact path_if_contains A A₂' h_A_contains_A₂' qs₂ qf₂ x₂' h_ispath2
                apply A.isPath_append.mpr h_connect

        exact ⟨ h_qs₁, h_qf₂, h_x', h_A_path_qs₁_qf₂_x ⟩

    case mpr =>
        intro h_in_A
        rw [image2, accepts_iff_0mod2_accepts A₁ A₁' rfl, accepts_iff_1mod2_accepts A₂ A₂' rfl]
        obtain ⟨ a, b, h_ab, h_a_accept, h_b_accept ⟩ := comp_word_decomposition A A₁' A₂' hA₁' hA₂' rfl x h_in_A
        exact ⟨ a, h_a_accept, b, h_b_accept, Eq.symm h_ab ⟩


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- STAR -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

/--
We have 1 as a starting and accepting state so that ε is always accepted.
We'll use it as a "chokepoint" to force a path into separate parts, so a word will
be broken cleanly into a list of words that are accepted by the original εNFA.
--/
def εNFA_kstar (A: εNFA α ℕ) : εNFA α ℕ := {
    start  := {1}
    accept := {1}
    step   := fun q c =>
        if q ∈ A.accept ∧ c = none then
            A.step q c ∪ {1}
        else if q = 1 ∧ c = none then
            A.start ∪ {1}
        else
            A.step q c
}

lemma kstar_accepts_nil (A A' : εNFA α ℕ) (hA: A = εNFA_kstar A'):
    [] ∈ A.accepts := by
    rw [mem_accepts_iff_exists_path]
    use 1, 1, []
    simp [hA, εNFA_kstar]

lemma kstar_contains (A A' : εNFA α ℕ) (hA: A = εNFA_kstar A') (hA': A'.is_0mod2):
    A.contains A' := by
    subst hA
    simp only [contains, εNFA_kstar]
    intro q σ
    have h_A'_step_empty : ∀ (σ : Option α), A'.step 1 σ = ∅ := by
        simp [is_0mod2, to_0mod2] at hA'
        obtain ⟨ A'', hA' ⟩ := hA'
        subst hA'
        simp
    split_ifs
    · simp only [union_singleton, subset_insert]
    · simp_all only [and_true, empty_subset]
    · simp only [subset_refl]

lemma kstar_accepts_contains (A A' : εNFA α ℕ) (hA: A = εNFA_kstar A') (hA': A'.is_0mod2)
    (x : List α) : x ∈ A'.accepts → x ∈ A.accepts := by
    intro h_x_in_A'

    rw [mem_accepts_iff_exists_path] at h_x_in_A' ⊢
    obtain ⟨ qs, qf, x'', h_qs, h_qf, h_x'', h_x_path ⟩ := h_x_in_A'
    let x' : List (Option α) := [none] ++ x'' ++ [none]
    use 1, 1, x'

    have h_x' : x'.reduceOption = x := by
        subst x' hA
        simp [List.reduceOption_append, h_x'']

    -- TODO: move the following into a general lemma; q % 2 = 1 → q ∉ A'.start etc.
    have h_1_notin_A': 1 ∉ A'.start ∧ 1 ∉ A'.accept := by
        have h_1_notin_start : 1 ∉ A'.start := by
            by_contra!
            apply if_0mod2_qs_is_0mod2 A' hA' 1 at this
            contradiction
        have h_1_notin_accept : 1 ∉ A'.accept := by
            by_contra!
            apply if_0mod2_qf_is_0mod2 A' hA' 1 at this
            contradiction
        exact ⟨h_1_notin_start, h_1_notin_accept⟩

    have h_step_qs : qs ∈ A.step 1 none := by
        subst hA
        simp [εNFA_kstar, h_1_notin_A']
        right
        exact h_qs

    have h_path_1_1: A.IsPath 1 1 x' := by
        subst x'
        have h_path_1_qs: A.IsPath 1 qs [none] := by
            simp [hA, εNFA_kstar, h_1_notin_A']
            right
            exact h_qs
        have h_path_qf_1: A.IsPath qf 1 [none] := by
            simp [hA, εNFA_kstar, h_qf]

        have h_contains := kstar_contains A A' hA hA'
        have h_path_qs_qf: A.IsPath qs qf x'' := A.path_if_contains A' h_contains qs qf x'' h_x_path

        have h_path_1_qf : A.IsPath 1 qf ([none] ++ x'') := A.isPath_append.mpr ⟨ qs, ⟨ h_path_1_qs, h_path_qs_qf ⟩ ⟩

        exact A.isPath_append.mpr ⟨ qf, ⟨ h_path_1_qf, h_path_qf_1 ⟩ ⟩

    subst hA
    exact ⟨ rfl, rfl, h_x', h_path_1_1 ⟩


lemma kstar_append (A A' : εNFA α ℕ) (y y₁ y₂ : List α)
    (hA: A = εNFA_kstar A') (hy: y = y₁ ++ y₂) :
    (y₁ ∈ A.accepts) ∧ (y₂ ∈ A.accepts) → y ∈ A.accepts := by
    intro ⟨ h_y₁_acc, h_y₂_acc ⟩
    rw [mem_accepts_iff_exists_path] at h_y₁_acc h_y₂_acc ⊢
    obtain ⟨ qs₁, qf₁, y₁', h_qs₁, h_qf₁, h_y₁', h_y₁_path ⟩ := h_y₁_acc
    obtain ⟨ qs₂, qf₂, y₂', h_qs₂, h_qf₂, h_y₂', h_y₂_path ⟩ := h_y₂_acc
    let y' := y₁' ++ ([none] ++ y₂')
    use qs₁, qf₂, y'

    have h_y' : y'.reduceOption = y := by
        subst h_y₁' h_y₂' hy y'
        exact List.reduceOption_append y₁' ([none] ++ y₂')

    have h_connect : A.IsPath qf₁ qs₂ [none] := by
        simp at ⊢
        have hqf1 : qf₁ = 1 := by simpa [hA, εNFA_kstar] using h_qf₁
        have hqs2 : qs₂ = 1 := by simpa [hA, εNFA_kstar] using h_qs₂
        subst hqf1; subst hqs2
        simp [hA, εNFA_kstar]
        by_cases hacc : (1 ∈ A'.accept) <;>
        simp [hacc]

    have h_full_path : A.IsPath qs₁ qf₂ y' := by
        rw [A.isPath_append]
        use qf₁
        constructor
        case left  => exact h_y₁_path
        case right => rw [A.isPath_append]; use qs₂

    exact ⟨ h_qs₁, h_qf₂, h_y', h_full_path ⟩

lemma if_0mod2_1_is_invalid (A' : εNFA α ℕ) (hA': A'.is_0mod2):
    1 ∉ A'.start ∧ 1 ∉ A'.accept ∧ ∀ (c : Option α), A'.step 1 c = ∅ := by
    have h_1_notin_start : 1 ∉ A'.start := by
        by_contra!
        apply if_0mod2_qs_is_0mod2 A' hA' 1 at this
        contradiction
    have h_1_notin_accept : 1 ∉ A'.accept := by
        by_contra!
        apply if_0mod2_qf_is_0mod2 A' hA' 1 at this
        contradiction
    have h_1_notin_step : ∀ (c : Option α), A'.step 1 c = ∅ := by
        intro c
        by_contra!
        obtain ⟨ t, ht ⟩ := this
        apply if_0mod2_step_is_0mod2 A' hA' 1 at ht
        omega
    exact ⟨h_1_notin_start, h_1_notin_accept, h_1_notin_step⟩

/--
The first complex thing we need for kstar's mpr direction, is to obtain a decomposition
of a series of ε-steps in a kstar-εNFA, starting from a non-trivial state (qs ≠ 1).

Decomposition of n ε-steps will either be: the whole path is contained in A', or exists
an n' s.t. the first n' ε-steps are contained in A', and after those steps there is a step
to 1, and the rest of the path is contained in A.
-/
lemma kstar_epsilon_path_decomposition (A A': εNFA α ℕ) (hA': A'.is_0mod2) (hA: A = εNFA_kstar A')
    (qs qf : ℕ) (x' : List (Option α)) (n : ℕ) (h_x' : x' = List.replicate n none)
    (h_path: A.IsPath qs qf x') (h_qs_not_1 : qs ≠ 1) :
    A'.IsPath qs qf x' ∨ ∃ (n' qf' : ℕ), (n' < n) ∧
    A'.IsPath qs qf' (List.replicate n' none) ∧ qf' ∈ A'.accept ∧
    A.IsPath 1 qf (List.replicate (n - n' - 1) none) := by

    subst x'
    induction n using Nat.twoStepInduction generalizing qs
    case zero =>
        left
        simp at h_path ⊢
        exact h_path
    case one =>
        by_cases h_qf_1: qf = 1
        case pos =>
            right
            use 0, qs
            simp at h_path
            have h_t_accept: qs ∈ A'.accept := by
                simp [hA, εNFA_kstar] at h_path
                split_ifs at h_path
                case pos h_accept => exact h_accept
                case neg =>
                    absurd h_path
                    have := A'.if_0mod2_step_is_0mod2 hA' qs qf none h_path
                    omega
            simp [h_t_accept, h_qf_1]
        case neg =>
            left
            simp [hA, εNFA_kstar, h_qs_not_1] at h_path ⊢
            split_ifs at h_path
            case pos =>
                simp [h_qf_1] at h_path
                exact h_path
            case neg => exact h_path

    case more n' h_induction₁ h_induction₂ =>
        clear h_induction₁
        let tail₁ : List (Option α) := List.replicate (n' + 1) none
        let tail₂ : List (Option α) := List.replicate (n' + 2) none

        have h_tail₁: tail₁ = [none] ++ List.replicate n' none := by
            subst tail₁
            rw [Nat.add_comm]
            exact List.replicate_add 1 n' none

        have h_tail₂: tail₂ = List.replicate 2 none ++ List.replicate n' none := by
            subst tail₂
            rw [Nat.add_comm]
            exact List.replicate_add 2 n' none

        subst tail₂
        rw [h_tail₂] at h_path
        apply A.isPath_append.mp at h_path
        obtain ⟨ t₂, h_path_t_t₂, h_path_t₂_qf ⟩ := h_path

        let two_nones : List (Option α) := (List.replicate 2 none)
        have h_nones: two_nones = [none] ++ [none] := by
            subst two_nones
            simp only [List.reduceReplicate, List.cons_append, List.nil_append]

        subst two_nones
        rw [h_nones] at h_path_t_t₂
        apply A.isPath_append.mp at h_path_t_t₂
        obtain ⟨ t₁, h_step_t_t₁, h_path_t₁_t₂ ⟩ := h_path_t_t₂
        apply A.isPath_singleton.mp at h_step_t_t₁

        have h_path_t₁_qf := A.isPath_append.mpr ⟨ t₂, h_path_t₁_t₂, h_path_t₂_qf ⟩

        by_cases h_t₁_1: t₁ = 1
        case pos =>
            clear h_induction₂
            right
            use 0, qs
            subst h_t₁_1 tail₁
            simp
            rw [symm h_tail₁] at h_path_t₁_qf
            simp [h_path_t₁_qf]
            simp [hA, εNFA_kstar] at h_step_t_t₁
            split_ifs at h_step_t_t₁
            case pos h_t_accept => exact h_t_accept
            case neg =>
                have := A'.if_0mod2_step_is_0mod2 hA' qs 1 none h_step_t_t₁
                omega

        case neg =>
            have := h_induction₂ t₁ h_t₁_1 h_path_t₁_qf
            clear h_induction₂
            cases this
            case inl h =>
                left
                simp [hA, εNFA_kstar, h_qs_not_1] at h_step_t_t₁
                split_ifs at h_step_t_t₁
                case pos h_t_accept =>
                    simp [h_t₁_1] at h_step_t_t₁
                    apply A'.isPath_singleton.mpr at h_step_t_t₁
                    exact A'.isPath_append.mpr ⟨ t₁, h_step_t_t₁, h ⟩
                case neg =>
                    apply A'.isPath_singleton.mpr at h_step_t_t₁
                    exact A'.isPath_append.mpr ⟨ t₁, h_step_t_t₁, h ⟩

            case inr ih =>
                right
                obtain ⟨ n₁', qf', ih ⟩ := ih
                obtain ⟨ h_n₁', h_path_t₁_qf', h_qf'_accept, h_path_qf'_1 ⟩ := ih
                use n₁' + 1, qf'
                simp [h_n₁', h_path_qf'_1, h_qf'_accept]

                simp [hA, εNFA_kstar] at h_step_t_t₁
                have h_path_t_t₁ : A'.IsPath qs t₁ [none] := by
                    split_ifs at h_step_t_t₁
                    case pos =>
                        simp [h_t₁_1] at h_step_t_t₁
                        exact A'.isPath_singleton.mpr h_step_t_t₁
                    case neg =>
                        exact A'.isPath_singleton.mpr h_step_t_t₁

                exact A'.isPath_append.mpr ⟨ t₁, h_path_t_t₁ , h_path_t₁_qf' ⟩

/--
We want to be able to decompose a general path (denoted x') in a kstar εNFA.
case 1: x' is empty or is a series of ε-steps (handled separately later)
case 2: x' can be decomposed to a non-trivial path fully contained in A' (a')
        and the rest of the path in A (b').
        This case needs to support an arbitrary amount of ε-steps before and after a',
        as well as a list of edge cases that need to be handled:
        - a' must not be empty for making induction progress
        - we either need to take an ε-step from 1 before a' (if qs = 1) or not (if qs ≠ 1).
        - b' can be a either empty, a series of ε-steps or a non-trivial path in A.
          unless b' is empty, b' _must_ start from 1, because we want to include the maximum
          character count we can get out of a', that means we might need to add an additional
          ε-step from qf' to 1.
--/

lemma kstar_decompose_path_lemma_of_absolute_evil
    (A A' : εNFA α ℕ) (hA': A'.is_0mod2) (hA : A = εNFA_kstar A')
    (qs qf : ℕ) (x' : List (Option α)) (h_x'_not_empty: x'.reduceOption ≠ [])
    (h_A_path_qs_qf_x': A.IsPath qs qf x') :
        ∃ (qs' qf' : ℕ) (ε₁' a' ε₂' b' : List (Option α)),
        (x' = (ε₁' ++ a' ++ ε₂' ++ b')) ∧ (a'.reduceOption ≠ []) ∧
        (ε₁'.reduceOption = []) ∧ (ε₂'.reduceOption = []) ∧
        ((ε₁' = [] ∧ qs' = qs) ∨ (ε₁' ≠ [] ∧ (A.IsPath qs qs' ε₁') ∧ qs' ∈ A'.start)) ∧
        (A'.IsPath qs' qf' a') ∧
        ((ε₂' = [] ∧ b' = [] ∧ qf' = qf) ∨
         (ε₂' = [none]) ∧ (qf' ∈ A'.accept) ∧ (A.IsPath qf' 1 ε₂') ∧ (A.IsPath 1 qf b')) := by

    --    A           A'         A         A
    -- qs ->(ε₁') qs' ->(a') qf' ->(ε₂') 1 ->(b') qf

    induction h_A_path_qs_qf_x'
    case nil =>
        contradiction -- x' cannot be nil in order to make induction progress
    case cons t qs qf c tail h_step h_path h_induction =>
        by_cases h_tail_empty: tail = []
        case pos =>
            clear h_induction
            subst h_tail_empty
            cases c
            case none h_c_none => contradiction
            case some c =>
                use qs, t, [], [some c], []
                simp at h_path
                subst h_path
                simp [hA, εNFA_kstar] at h_step
                simp [h_step]

        case neg =>
            by_cases h_tail_reduce_empty: tail.reduceOption = []
            case pos =>
                -- The tail is a seris of ε-steps, we cannot use h_induction directly on it
                clear h_induction
                use qs

                obtain ⟨ n, h_n ⟩ := tail.reduceOption_eq_nil_iff.mp h_tail_reduce_empty

                -- x' is non-trivial, so c cannot be ε
                have h_c_some: ∃ c', c = some c' := by
                    cases c
                    case none => contradiction
                    case some c' => use c'

                obtain ⟨ c, h_c_some ⟩ := h_c_some
                subst h_c_some

                have h_t_not_1 : t ≠ 1 := by
                    by_contra!
                    subst this
                    simp [hA, εNFA_kstar] at h_step
                    apply A'.if_0mod2_step_is_0mod2 hA' qs 1 c at h_step
                    omega

                have h_qs_not_1 : qs ≠ 1 := by
                    by_contra!
                    subst this
                    simp [hA, εNFA_kstar] at h_step
                    apply A'.if_0mod2_step_is_0mod2 hA' 1 t c at h_step
                    omega

                cases kstar_epsilon_path_decomposition A A' hA' hA t qf tail n h_n h_path h_t_not_1
                case inl h_path_in_A' =>
                    use qf, [], c :: tail, [], []
                    simp
                    simp [hA, εNFA_kstar, h_qs_not_1] at h_step
                    apply A'.isPath_singleton.mpr at h_step
                    exact A'.isPath_append.mpr ⟨ t, h_step, h_path_in_A' ⟩

                case inr h =>
                        obtain ⟨ n', qf', h_n', h_path_t_qf', h_qf'_accept, h_path_qf'_qf ⟩ := h

                        have h_stepA : t ∈ A'.step qs (some c) := by
                            simp [hA, εNFA_kstar, h_qs_not_1] at h_step
                            exact h_step

                        use qf', [], [some c] ++ List.replicate n' none, [none], List.replicate (n - n' - 1) none
                        have h_path_qs_qf' := A'.isPath_append.mpr ⟨ t, A'.isPath_singleton.mpr h_stepA, h_path_t_qf' ⟩

                        refine ⟨ ?_, by simp, by simp, by simp, by simp, h_path_qs_qf', ?_ ⟩
                        ·
                            rw [h_n]
                            have h_eq : n = n' + (1 + (n - n' - 1)) := by
                                omega
                            rw [h_eq, List.replicate_add, List.replicate_add]
                            simp [List.append_assoc]
                        ·
                            right
                            have : A.IsPath qf' 1 [none] := by
                                apply A.isPath_singleton.mpr
                                simp [hA, εNFA_kstar, h_qf'_accept]
                            exact ⟨ rfl, h_qf'_accept, this, h_path_qf'_qf ⟩

            case neg =>
                /-
                    The tail is not empty and not trivial, now we need to handle a load of annoying edge cases
                    using the induction hypothesis, and build a path corresponding to each of them.
                    It turns out, there are *7* different cases each needing a different proof.
                    Yap, *7*. This is my life now. 🥲
                    I'm not going to bother documenting it, figure it out by yourself, FEEL THE PAIN 👿
                -/

                obtain ⟨ qs', qf', ε₁', a', ε₂', b', ih ⟩ := h_induction h_tail_reduce_empty
                clear h_induction
                obtain ⟨ h_tail, h_a', h_ε₁', h_ε₂', h_first_part, h_path_a'_in_A', h_next_part ⟩ := ih
                cases c
                case none =>
                    cases h_first_part
                    case inl h_ε₁'_empty =>
                        obtain ⟨ h_ε₁_empty, h_qs'_t ⟩ := h_ε₁'_empty
                        subst h_ε₁_empty h_qs'_t

                        simp [hA, εNFA_kstar] at h_step
                        split_ifs at h_step
                        case pos h_qs_accept =>
                            have := A'.if_0mod2_qf_is_0mod2 hA' qs h_qs_accept
                            have h_qs_not_1 : qs ≠ 1 := by omega

                            use qs, qf', [], [none] ++ a', ε₂', b'
                            simp [h_tail, h_ε₂', h_next_part, h_a']

                            cases h_step
                            case inl h_qs'_1 =>
                                subst h_qs'_1
                                cases h_path_a'_in_A'
                                case nil => contradiction
                                case cons t' c' _ h_step' _ =>
                                    have := A'.if_0mod2_step_is_0mod2 hA' 1 t' c' h_step'
                                    omega -- contradiction

                            case inr h_qs'_step_qs =>
                                apply A'.isPath_singleton.mpr at h_qs'_step_qs
                                exact A'.isPath_append.mpr ⟨ qs', h_qs'_step_qs, h_path_a'_in_A' ⟩
                        case pos h_qs_1 =>
                            subst h_qs_1
                            use qs', qf', [none], a', ε₂', b'

                            simp [h_tail, h_ε₂', h_next_part, h_a', h_path_a'_in_A']
                            have h_qs'_not_1 : qs' ≠ 1 := by
                                cases h_path_a'_in_A'
                                case nil => contradiction
                                case cons t' c' _ h_step' _ =>
                                    have := A'.if_0mod2_step_is_0mod2 hA' qs' t' c' h_step'
                                    omega
                            simp [h_qs'_not_1] at h_step
                            simp [hA, εNFA_kstar]
                            have := A'.if_0mod2_1_is_invalid hA'
                            simp [h_step, this]

                        case neg =>
                            use qs, qf', [], [none] ++ a', ε₂', b'

                            simp [h_tail, h_a', h_ε₁', h_ε₂', h_next_part]
                            apply A'.isPath_singleton.mpr at h_step
                            exact A'.isPath_append.mpr ⟨qs', h_step, h_path_a'_in_A' ⟩

                    case inr h_ε₁'_not_empty =>
                        use qs', qf', [none] ++ ε₁', a', ε₂', b'

                        simp [h_tail, h_a', h_ε₁', h_ε₂', h_next_part, h_path_a'_in_A' , h_ε₁'_not_empty]
                        obtain ⟨ h_ε₁'_not_empty, h_ε₁'_path, h_qs'_start ⟩ := h_ε₁'_not_empty
                        apply A.isPath_singleton.mpr at h_step
                        exact A.isPath_append.mpr ⟨ t, h_step, h_ε₁'_path ⟩

                case some c =>
                    cases h_first_part
                    case inl h_ε₁'_empty =>
                        obtain ⟨ h_ε₁'_empty, h_qs'_t ⟩ := h_ε₁'_empty
                        use qs, qf', [], [some c] ++ ε₁' ++ a', ε₂', b'

                        simp [h_tail, h_ε₂', h_next_part]
                        subst h_ε₁'_empty h_qs'_t
                        simp [hA, εNFA_kstar] at h_step
                        apply A'.isPath_singleton.mpr at h_step
                        exact A'.isPath_append.mpr ⟨ qs', h_step, h_path_a'_in_A' ⟩
                    case inr h_ε₁'_not_empty =>
                        obtain ⟨ h_ε₁'_not_empty, h_ε₁'_path, h_qs'_start ⟩ := h_ε₁'_not_empty
                        obtain ⟨ n, h_n ⟩ := ε₁'.reduceOption_eq_nil_iff.mp h_ε₁'

                        have h_t_not_1 : t ≠ 1 := by
                            by_contra!
                            subst this
                            simp [hA, εNFA_kstar] at h_step
                            apply A'.if_0mod2_step_is_0mod2 hA' qs 1 c at h_step
                            omega

                        simp [hA, εNFA_kstar] at h_step
                        apply A'.isPath_singleton.mpr at h_step

                        cases kstar_epsilon_path_decomposition A A' hA' hA t qs' ε₁' n h_n h_ε₁'_path h_t_not_1
                        case inl h_path_in_A' =>
                            use qs, qf', [], [some c] ++ ε₁' ++ a', ε₂', b'
                            simp [h_tail, h_ε₂', h_next_part]
                            have h_ε₁'_a'_path : A'.IsPath t qf' (ε₁' ++ a') :=
                                A'.isPath_append.mpr ⟨ qs', h_path_in_A', h_path_a'_in_A'⟩

                            exact A'.isPath_append.mpr ⟨ t, h_step, h_ε₁'_a'_path ⟩
                        case inr h =>
                            -- This case... tHiS CaSe....... THIS CASE TOOK MY *SOUL*
                            obtain ⟨ n', qf'', h_n', h_path_t_qf'', h_qf''_accept, h_path_qf''_qf ⟩ := h
                            let a'' := [some c] ++ (List.replicate n' none)
                            let b'' := (List.replicate (n - n' - 1) none) ++ a' ++ ε₂' ++ b'

                            use qs, qf'', [], a'', [none], b''

                            subst a'' b''

                            simp [h_tail, h_n]
                            have h_1_step_qf'' : 1 ∈ A.step qf'' none := by
                                simp [h_qf''_accept, hA, εNFA_kstar]

                            have h_path_qs_qf'' := A'.isPath_append.mpr ⟨ t, h_step, h_path_t_qf'' ⟩
                            apply A.path_if_contains A' (A.kstar_contains A' hA hA') qs' qf' at h_path_a'_in_A'
                            have h_path_q_qf' := A.isPath_append.mpr ⟨ qs', h_path_qf''_qf, h_path_a'_in_A' ⟩

                            have h_tail_split : List.replicate n none ++ (a' ++ (ε₂' ++ b')) =
                                List.replicate n' none ++
                                none :: (List.replicate (n - n' - 1) none ++ (a' ++ (ε₂' ++ b'))) := by
                                have h_eq : n = n' + (1 + (n - n' - 1)) := by
                                    omega
                                rw [h_eq, List.replicate_add, List.replicate_add]
                                simp [List.append_assoc]

                            refine ⟨ h_tail_split, h_path_qs_qf'', h_qf''_accept, h_1_step_qf'', ?_ ⟩

                            cases h_next_part
                            case inl h_ε₂'_empty =>
                                obtain ⟨h_ε₂'_empty, h_b'_empty, h_qf'_qf ⟩ := h_ε₂'_empty
                                subst h_ε₂'_empty h_b'_empty h_qf'_qf
                                simp [h_path_q_qf']
                            case inr h_ε₂'_step =>
                                obtain ⟨ h_ε₂'_none, h_qf'_accept, h_ε₂'_step, h_path_b' ⟩ := h_ε₂'_step
                                subst h_ε₂'_none

                                have h_1_step_qf' : 1 ∈ A.step qf' none := by
                                    simp [h_qf'_accept, hA, εNFA_kstar]
                                apply A.isPath_singleton.mpr at h_1_step_qf'

                                have := A.isPath_append.mpr ⟨ qs', h_path_qf''_qf, h_path_a'_in_A' ⟩
                                have := A.isPath_append.mpr ⟨ qf', this, h_1_step_qf' ⟩
                                have := A.isPath_append.mpr ⟨ 1, this, h_path_b' ⟩
                                simp at this
                                simp [this]

/--
Using the previous horrible, horribly evil lemma, now we can obtain the first sub-word
from a non-trivial word in L(A).
-/
lemma kstar_obtain_first_word (A A' : εNFA α ℕ) (hA': A'.is_0mod2) (hA : A = εNFA_kstar A')
    (x: List α) (hx: x ∈ A.accepts) (h_x_not_empty: x ≠ []) :
    ∃ (a b : List α), (x = a ++ b) ∧ (a ≠ []) ∧ a ∈ A'.accepts ∧ b ∈ A.accepts := by

    obtain ⟨ qs, qf, x', ⟨ h_qs, h_qf, h_x', h_path ⟩ ⟩ := A.mem_accepts_iff_exists_path.mp hx

    have h_x'_not_empty : x'.reduceOption ≠ [] := by
        subst hA h_x'
        exact h_x_not_empty

    obtain ⟨ qs', qf', ε₁', a', ε₂', b', h_decompose_words ⟩ :=
        A.kstar_decompose_path_lemma_of_absolute_evil A' hA' hA qs qf x' h_x'_not_empty h_path
    obtain ⟨ h_x'_decomposition, h_progression, h_ε₁', h_ε₂', h_path_ε₁', h_path_a', h_next_part⟩ :=
        h_decompose_words

    by_cases h_ε₁'_empty: ε₁' = []
    case pos =>
        subst h_ε₁'_empty
        simp at h_path_ε₁' h_progression
        cases h_path_a'
        case nil => contradiction
        case cons t c tail h_step h_path =>
            apply A'.if_0mod2_step_is_0mod2 hA' at h_step
            simp [hA, εNFA_kstar] at h_qs
            subst h_qs h_path_ε₁'
            omega

    case neg =>
        simp [h_ε₁'_empty] at h_path_ε₁'
        have h_ε₂'_not_empty: ε₂' ≠ [] := by
            by_contra!
            simp [this] at h_next_part
            simp [hA, εNFA_kstar] at h_qf
            obtain ⟨_, h_qf'⟩ := h_next_part
            subst h_qf h_qf'
            obtain ⟨ _, h_qs'_start ⟩ := h_path_ε₁'
            apply A'.if_0mod2_qs_is_0mod2 hA' at h_qs'_start
            apply A'.if_0mod2_path_is_same_mod2 hA' at h_path_a'
            omega

        simp [h_ε₂'_not_empty] at h_next_part
        let a := a'.reduceOption
        let b := b'.reduceOption
        use a, b
        subst h_x'_decomposition

        simp [List.reduceOption_append, h_ε₁', h_ε₂'] at h_x'

        obtain ⟨ _, h_qf'_accept, _, h_path_b' ⟩ := h_next_part

        have h_a_in_A' : a ∈ A'.accepts :=
            A'.mem_accepts_iff_exists_path.mpr ⟨ qs', qf', a', ⟨ h_path_ε₁'.right, h_qf'_accept, rfl, h_path_a' ⟩ ⟩

        have h_1_start : 1 ∈ A.start := by simp [hA, εNFA_kstar]
        have h_b_in_A : b ∈ A.accepts :=
            A.mem_accepts_iff_exists_path.mpr ⟨ 1, qf, b', ⟨ h_1_start, h_qf, rfl, h_path_b' ⟩ ⟩

        simp [h_x', a, b]
        refine ⟨ h_progression, h_a_in_A', h_b_in_A ⟩

/--
To obtain a decomposition of a word in L(A) into a list of words in L(A') we'll use the following
recursive lemma, and that concludes the second direction of the kstar proof.
-/
lemma kstar_word_list_decompisition
    (A A' : εNFA α ℕ) (hA': A'.is_0mod2) (hA : A = εNFA_kstar A')
    (x : List α) (hx: x ∈ A.accepts) :
    ∃ (L : List (List α)), x = L.flatten ∧ ∀ y ∈ L, y ∈ A'.accepts := by
    by_cases h_x_empty: x = []
    case pos =>
        use []
        tauto

    case neg =>
        obtain ⟨ a, b, h_x_a_b, h_a_not_empty, h_a_in_A', h_b_in_A ⟩ :=
            A.kstar_obtain_first_word A' hA' hA x hx h_x_empty
        obtain ⟨ L', h_L' ⟩ := A.kstar_word_list_decompisition A' hA' hA b h_b_in_A
        use [a] ++ L'

        simp [h_x_a_b, h_a_in_A', h_L']
        exact h_L'.right

termination_by x.length
decreasing_by
    simp only [h_x_a_b, List.length_append, lt_add_iff_pos_left]
    exact a.ne_nil_iff_length_pos.mp h_a_not_empty

lemma Star_Regex_to_εNFA (r : RegularExpression α) :
    (∃ (Ar: εNFA α ℕ), r.matches' = Ar.accepts) →
    ∃ (A: εNFA α ℕ), (r.star).matches' = A.accepts := by
    intro h_r
    obtain ⟨ Ar, hAr ⟩ := h_r
    let A' := Ar.to_0mod2
    have hA' : A'.is_0mod2 := by use Ar

    let A : εNFA α ℕ := εNFA_kstar A'
    use A

    simp
    rw [hAr, @Language.kstar_def, @Language.ext_iff, accepts_iff_0mod2_accepts Ar A' rfl]

    intro x
    constructor
    case mp =>
        intro h_x
        obtain ⟨ L, h_L, h_y  ⟩ := h_x
        subst h_L

        induction L
        case nil =>
            simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.flatten_nil]
            rw [mem_accepts_iff_exists_path]
            use 1, 1, []
            simp [A, εNFA_kstar]
        case cons head tail h_induction =>
            simp at h_y
            obtain ⟨ h_head, h_tail ⟩ := h_y
            have h_head_acc : head ∈ A.accepts := by
                rw [A.mem_accepts_iff_exists_path]
                rw [A'.mem_accepts_iff_exists_path] at h_head
                obtain ⟨qs, qf, head', h_qs, h_qf, h_head', h_path⟩ := h_head

                let connect_head := ([none] ++ head' ++ [none])
                use 1, 1, connect_head

                have h_start:  1 ∈ A.start  := by simp [A, εNFA_kstar]
                have h_accept: 1 ∈ A.accept := by simp [A, εNFA_kstar]
                have h_head: connect_head.reduceOption = head := by
                    simp [connect_head, List.reduceOption_append, h_head']

                have h_path_qf_to_1_ε: A.IsPath qf 1 [none] := by
                    simp [isPath_singleton, A, εNFA_kstar, h_qf]

                have h_path_1_to_qs_ε : A.IsPath 1 qs [none] := by
                    have : (1 : ℕ) ∉ A'.accept := by simp [A', to_0mod2]
                    simp [A, εNFA_kstar, this, h_qs, isPath_singleton]

                refine ⟨ h_start, h_accept, h_head, ?_ ⟩

                apply A.isPath_append.mpr; use qf
                refine ⟨ ?_, h_path_qf_to_1_ε ⟩

                apply A.isPath_append.mpr; use qs
                refine ⟨ h_path_1_to_qs_ε, ?_ ⟩

                have h_contains : A.contains A' := kstar_contains A A' rfl hA'

                exact path_if_contains A A' h_contains qs qf head' h_path

            apply h_induction at h_tail
            exact kstar_append A A' (head :: tail).flatten head tail.flatten rfl rfl ⟨ h_head_acc, h_tail⟩

    case mpr =>
        intro h_x_in_A

        by_cases h_x_empty: x ≠ []
        case neg => use []; tauto
        case pos =>
            exact A.kstar_word_list_decompisition A' hA' rfl x h_x_in_A


theorem Regex_to_εNFA (r: RegularExpression α) : ∃ (A: εNFA α ℕ), r.matches' = A.accepts := by
    induction r
    case zero    => exact Zero_Regex_to_εNFA
    case epsilon => exact Epsilon_Regex_to_εNFA
    case char σ  => exact Char_Regex_to_εNFA σ
    case plus _ _ r₁ r₂ h_r₁ h_r₂ => exact Plus_Regex_to_εNFA r₁ r₂ h_r₁ h_r₂
    case comp _ _ r₁ r₂ h_r₁ h_r₂ => exact Comp_Regex_to_εNFA r₁ r₂ h_r₁ h_r₂
    case star _ _ r h_r => exact Star_Regex_to_εNFA r h_r





--------------------------
-- THE OTHER DIRECTION: --
--------------------------

variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]  --removed?


lemma dont_go_nowhere (A : εNFA alphabet ℕ): A.start = ∅ → A.accept = ∅ := by sorry



def to_singular (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 1 }
    accept := { 2 }
    step   := fun q c =>
        if q > 4 then
            { q' + 5 | q' ∈ (A.step (q - 5) c) }
        else
            if q == 1 && c == none then
                { q' + 5 | q' ∈ A.start  }
            else
                if q ∈ { q' + 5 | q' ∈ A.accept } && c == none then
                    { 2 }
                else
                    ∅
    : εNFA alphabet ℕ
}

def is_singular (A' : εNFA alphabet ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_singular A

lemma accepts_iff_singular_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_singular A) :
    A.accepts = A'.accepts := by sorry


def is_finite_automata (A : εNFA alphabet ℕ) :=
    (A.start = ∅) ∨ (A.start ≠ ∅ ∧ (∃n: ℕ, --n is the latest reachable from the start
    (∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n x)
    ∧
    ∀n': ℕ, (n' > n) → ¬(∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n' x)
    ))

def to_trim (A : εNFA alphabet ℕ) (i j k : ℕ) : εNFA alphabet ℕ := {
    start  := { i }
    accept := { j }
    step   := fun q c =>
        if j > k then
            if q == j then
                ∅
            else
                { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k) ∨ (q' == j)) }
        else
            { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k)) }
    : εNFA alphabet ℕ
}

def is_trim (A' : εNFA alphabet ℕ) (i' j' k' : ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_trim A i' j' k'

lemma singular_finite_accepts_iff_trim_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hAsingular: is_singular A) (hAfinite: is_finite_automata A) (hhhhh: 1==1): -- to add - A' = trim(A, 1, 2, n)
    A.accepts = A'.accepts := by sorry




def regex_for_path_from_i_to_j_through_k (A : εNFA alphabet ℕ) (i j k : ℕ) : RegularExpression alphabet :=
    if k==0 then
        if i==j then
            1
        else
            0 --TODO: REAL REGEX
    else
        0 --TODO: REAL REGEX






def regex_is_path (A : εNFA alphabet ℕ) (i j k : ℕ) (r: RegularExpression alphabet) (hr: r = regex_for_path_from_i_to_j_through_k A i j k) :
    ∀x : List (Option alphabet), ((x.reduceOption ∈ r.matches') ↔ ((to_trim A i j k).IsPath i j x)) := by
    sorry



theorem εNFA_to_Regex (A: εNFA alphabet ℕ) : is_finite_automata A → (∃ (r: RegularExpression alphabet), r.matches' = A.accepts) := by
    rw [is_finite_automata]
    rintro ( hnill | ⟨ hAStartNotEmpty, n, hnReachable, hGreaternUnreachable ⟩ )
    case inl =>
        use 0
        simp only [RegularExpression.matches']

        sorry
    case inr =>

        sorry




end εNFA
