import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

open Set Classical


universe u v
variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]

set_option linter.unusedSectionVars false


namespace εNFA

def to_0mod2 (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 2*q' | q' ∈ A.start  }
    accept := { 2*q' | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 0 then
            { 2*q' | q' ∈ (A.step (q/2) c) }
        else
            ∅
    : εNFA alphabet ℕ
}

def to_1mod2 (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 2*q' + 1 | q' ∈ A.start  }
    accept := { 2*q' + 1 | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 1 then
            { 2*q' + 1 | q' ∈ (A.step ((q - 1)/2) c) }
        else
            ∅
    : εNFA alphabet ℕ
}

def is_0mod2 (A' : εNFA alphabet ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_0mod2 A

def is_1mod2 (A' : εNFA alphabet ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_1mod2 A

lemma if_0mod2_step_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (σ : Option alphabet) : (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = 0 ∧  q₂ % 2 = 0) := by
    intro h_step
    obtain ⟨A, hA⟩ := hA'

    subst hA
    simp [to_0mod2] at h_step
    omega

lemma if_1mod2_step_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (σ : Option alphabet) : (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = 1 ∧  q₂ % 2 = 1) := by
    intro h_step
    obtain ⟨A, hA⟩ := hA'

    subst hA
    simp [to_1mod2] at h_step
    omega


lemma if_mod2_step_is_same_mod2 (A' : εNFA alphabet ℕ) (q₁ q₂ : ℕ) (σ : Option alphabet) :
    A'.is_0mod2 ∨ A'.is_1mod2 → (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro h_mod2_eNFA h_step
    cases h_mod2_eNFA
    case inl h_0mod2 =>
        have := if_0mod2_step_is_0mod2 A' h_0mod2 q₁ q₂ σ h_step
        omega
    case inr h_1mod2 =>
        have := if_1mod2_step_is_1mod2 A' h_1mod2 q₁ q₂ σ h_step
        omega

lemma if_0mod2_step_is_same_mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (σ : Option alphabet) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    apply if_mod2_step_is_same_mod2 A' q₁ q₂ σ
    left
    exact hA'

lemma if_1mod2_step_is_same_mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (σ : Option alphabet) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    apply if_mod2_step_is_same_mod2 A' q₁ q₂ σ
    right
    exact hA'

lemma if_mod2_path_is_same_mod2 (A' : εNFA alphabet ℕ) (q₁ q₂ : ℕ) (x : List (Option alphabet)):
    A'.is_0mod2 ∨ A'.is_1mod2 → (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro h_mod2_eNFA h_path
    induction h_path with
    | nil _ => rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        have := if_mod2_step_is_same_mod2 A' q₁ t c h_mod2_eNFA h_step
        omega

lemma if_0mod2_path_is_same_mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (x : List (Option alphabet)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inl hA')

lemma if_1mod2_path_is_same_mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (x : List (Option alphabet)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inr hA')

lemma if_mod2_consequences (A' : εNFA alphabet ℕ) (q : ℕ) :
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

lemma if_0mod2_qs_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (q : ℕ) (hq: q ∈ A'.start) :
    (q % 2 = 0) := ((if_mod2_consequences A' q).left hA').left hq

lemma if_1mod2_qs_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2) (q : ℕ) (hq: q ∈ A'.start) :
    (q % 2 = 1) := ((if_mod2_consequences A' q).right hA').left hq

lemma if_0mod2_qf_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (q : ℕ) (hq: q ∈ A'.accept) :
    (q % 2 = 0) := ((if_mod2_consequences A' q).left hA').right hq

lemma if_1mod2_qf_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2) (q : ℕ) (hq: q ∈ A'.accept) :
    (q % 2 = 1) := ((if_mod2_consequences A' q).right hA').right hq

lemma path_iff_mod2_path (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (qs qf qs' qf' : ℕ) (y : List (Option alphabet)) :
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

lemma path_iff_0mod2_path (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (qs qf qs' qf' : ℕ) (y : List (Option alphabet))
    (hA': A' = to_0mod2 A) (h_qs': qs' = 2 * qs) (h_qf': qf' = 2 * qf) :
    (A.IsPath qs qf y) ↔ (A'.IsPath qs' qf' y) :=
    (path_iff_mod2_path A A' qs qf qs' qf' y (Or.inl ⟨ hA', h_qs', h_qf' ⟩))

lemma path_iff_1mod2_path (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (qs qf qs' qf' : ℕ) (y : List (Option alphabet))
    (hA': A' = to_1mod2 A) (h_qs': qs' = 2 * qs + 1) (h_qf': qf' = 2 * qf + 1) :
    (A.IsPath qs qf y) ↔ (A'.IsPath qs' qf' y) :=
    (path_iff_mod2_path A A' qs qf qs' qf' y (Or.inr ⟨ hA', h_qs', h_qf' ⟩))

lemma accepts_iff_mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
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

lemma accepts_eq_0mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_0mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inl hA')

lemma accepts_eq_1mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_1mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inr hA')

end εNFA


namespace εNFA

def contains (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :=
    ∀ (q : ℕ), ∀ (σ: Option alphabet), A'.step q σ ⊆ A.step q σ

lemma path_if_contains (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (h_contains: A.contains A')
    (q₁ q₂ : ℕ) (x : List (Option alphabet)) :
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

def εNFA_zero : εNFA alphabet ℕ := {
    start  := ∅
    accept := ∅
    step   := fun _ _ => ∅
}

lemma Zero_Regex_to_εNFA :
    ∃ (A: εNFA alphabet ℕ), RegularExpression.zero.matches' = A.accepts := by
        use εNFA_zero
        simp [εNFA_zero, εNFA.accepts, Language.zero_def]


 -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- EPSILON -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- -- --

def εNFA_epsilon : εNFA alphabet ℕ := {
    start  := {0}
    accept := {0}
    step   := fun _ _ => ∅
}

lemma Epsilon_Regex_to_εNFA :
    ∃ (A: εNFA alphabet ℕ), RegularExpression.epsilon.matches' = A.accepts := by
        let A : εNFA alphabet ℕ := εNFA_epsilon
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

def εNFA_char (σ : alphabet) : εNFA alphabet ℕ := {
    start  := {0}
    accept := {1}
    step   := fun q a =>
        if (q = 0) ∧ (a = (some σ)) then
            {1}
        else
            ∅
}

lemma Char_Regex_to_εNFA (σ : alphabet) :
    ∃ (A: εNFA alphabet ℕ), (RegularExpression.char σ).matches' = A.accepts := by
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
            refine ⟨ rfl, rfl, symm hx, this ⟩

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

def εNFA_plus (A₁: εNFA alphabet ℕ) (A₂: εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := A₁.start  ∪ A₂.start
    accept := A₁.accept ∪ A₂.accept
    step   := fun q c =>
        if (q % 2 = 0) then
            A₁.step q c
        else
            A₂.step q c
}

lemma Plus_Regex_to_εNFA (r₁ r₂ : RegularExpression alphabet) :
     (∃ (A₁: εNFA alphabet ℕ), r₁.matches' = A₁.accepts) →
     (∃ (A₂: εNFA alphabet ℕ), r₂.matches' = A₂.accepts) →
     ∃ (A: εNFA alphabet ℕ), (r₁.plus r₂).matches' = A.accepts := by
    intro h_r₁ h_r₂
    obtain ⟨ A₁, hA₁ ⟩ := h_r₁
    obtain ⟨ A₂, hA₂ ⟩ := h_r₂

    let A₁' := A₁.to_0mod2
    let A₂' := A₂.to_1mod2
    have hA₁' : A₁'.is_0mod2 := by use A₁
    have hA₂' : A₂'.is_1mod2 := by use A₂

    let A : εNFA alphabet ℕ := εNFA_plus A₁' A₂'
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

    have h_A_path_implies_eq_mod2: (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (A.IsPath q₁ q₂ y') → (q₁ % 2 = q₂ % 2) := by
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
            rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_in_A₁
            rw [A.mem_accepts_iff_exists_path]
            obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₁'_path ⟩ := h_in_A₁
            use s₁, s₂, x'
            exact ⟨ mem_union_left A₂'.start h_s₁,
                    mem_union_left A₂'.accept h_s₂,
                    h_x',
                    path_if_contains A A₁' h_A_contains_A₁' s₁ s₂ x' h_A₁'_path ⟩

        case inr h_in_A₂ =>
            rw [accepts_eq_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_in_A₂
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
            rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path]
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

            have h_path_qs_to_qf_x' : (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (q₁ % 2 = 0) → (A.IsPath q₁ q₂ y') → (A₁'.IsPath q₁ q₂ y') := by
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
            rw [accepts_eq_1mod2_accepts A₂ A₂' rfl]
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

            have h_path_qs_to_qf_x': (q₁ : ℕ) → (q₂ : ℕ) → (y' : List (Option alphabet)) → (q₁ % 2 = 1) → (A.IsPath q₁ q₂ y') → (A₂'.IsPath q₁ q₂ y') := by
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

def εNFA_comp (A₁: εNFA alphabet ℕ) (A₂: εNFA alphabet ℕ) (_ : A₁.is_0mod2) (_ : A₂.is_1mod2) : εNFA alphabet ℕ := {
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

lemma comp_step_1mod2_to_1mod2 (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (q₁ q : ℕ)  :
    ∀ (c : Option alphabet), q₁ % 2 = 1 → (q ∈ A.step q₁ c) → q % 2 = 1 := by
    rintro  c h_q₁_1mod2 h_q
    simp [hA, εNFA_comp, h_q₁_1mod2] at h_q
    have h_q₁_eq_q_mod2 := if_1mod2_step_is_same_mod2 A₂' hA₂' (q₁ := q₁) (q₂ := q) c h_q
    simp [symm h_q₁_eq_q_mod2, h_q₁_1mod2]

lemma comp_path_1mod2_to_0mod2_is_empty (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (q₁ q₂ : ℕ):
    ∀ (x' : List (Option alphabet)), q₁ % 2 = 1 ∧ q₂ % 2 = 0 → ¬A.IsPath q₁ q₂ x' := by
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

lemma comp_path_0mod2 (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 0 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option alphabet)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 0 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_1mod2
    have h_t_1mod2 : t % 2 = 1 := Nat.mod_two_ne_zero.mp h_t_1mod2
    absurd h_path_t_q₂
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA₁' hA₂' hA t q₂ b' ⟨ h_t_1mod2, h_q₂ ⟩

lemma comp_path_0mod2_in_A₁' (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
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

lemma comp_path_1mod2 (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 1 ∧ q₂ % 2 = 1 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option alphabet)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 1 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_0mod2
    have h_t_0mod2 : t % 2 = 0 := Nat.mod_two_ne_one.mp h_t_0mod2
    absurd h_path_q₁_t
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA₁' hA₂' hA q₁ t a' ⟨ h_q₁, h_t_0mod2 ⟩

lemma comp_path_1mod2_in_A₂' (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
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

lemma comp_step_change_mod_implies_epsilon (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂')
    (q₁ q₂ : ℕ) (c : Option alphabet) :
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

lemma comp_path_decomposition (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') :
    ∀ (qs qf : ℕ), ∀ (y : List alphabet), ∀ (y' : List (Option alphabet)),
    qs % 2 = 0 ∧ qf % 2 = 1 ∧ y = y'.reduceOption ∧ A.IsPath qs qf y' →
    ∃ (qf₁ qs₂ : ℕ), ∃ (a' b' : List (Option alphabet)),
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

lemma comp_word_decomposition (A A₁' A₂': εNFA alphabet ℕ)
    (hA₁': A₁'.is_0mod2) (hA₂': A₂'.is_1mod2) (hA: A = εNFA_comp A₁' A₂' hA₁' hA₂') (x : List alphabet) :
    (x ∈ A.accepts) → ∃ (a b : List alphabet), (x = a ++ b) ∧ (a ∈ A₁'.accepts) ∧ (b ∈ A₂'.accepts) := by
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

lemma Comp_Regex_to_εNFA (r₁ r₂ : RegularExpression alphabet) :
     (∃ (A₁: εNFA alphabet ℕ), r₁.matches' = A₁.accepts) →
     (∃ (A₂: εNFA alphabet ℕ), r₂.matches' = A₂.accepts) →
     ∃ (A: εNFA alphabet ℕ), (r₁.comp r₂).matches' = A.accepts := by
    intro h_r₁ h_r₂
    obtain ⟨ A₁, hA₁ ⟩ := h_r₁
    obtain ⟨ A₂, hA₂ ⟩ := h_r₂

    let A₁' := A₁.to_0mod2
    let A₂' := A₂.to_1mod2

    have hA₁' : A₁'.is_0mod2 := by use A₁
    have hA₂' : A₂'.is_1mod2 := by use A₂

    let A : εNFA alphabet ℕ := εNFA_comp A₁' A₂' hA₁' hA₂'
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
        rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_x₁
        rw [accepts_eq_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_x₂
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
        rw [image2, accepts_eq_0mod2_accepts A₁ A₁' rfl, accepts_eq_1mod2_accepts A₂ A₂' rfl]
        obtain ⟨ a, b, h_ab, h_a_accept, h_b_accept ⟩ := comp_word_decomposition A A₁' A₂' hA₁' hA₂' rfl x h_in_A
        exact ⟨ a, h_a_accept, b, h_b_accept, Eq.symm h_ab ⟩


 -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- STAR -- -- -- -- --
 -- -- -- -- -- -- -- -- -- -- --

def εNFA_kstar (A: εNFA alphabet ℕ) : εNFA alphabet ℕ := {
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

lemma kstar_append (A A' : εNFA alphabet ℕ) (y y₁ y₂ : List alphabet)
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

lemma extract_first_chunk
        {α : Type u} [DecidableEq α]
        (A' : εNFA α ℕ)
        (t : ℕ) (tail : List (Option α))
        (ht : t ∈ A'.step 1 none)
        (h_rest : (εNFA_kstar A').IsPath t 1 tail) :
        ∃ a b : List α,
            tail.reduceOption = a ++ b ∧
            a ≠ [] ∧
            a ∈ A'.accepts ∧
            b ∈ (εNFA_kstar A').accepts :=
        by
        sorry

lemma kstar_decompose_path
    (A A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (hA : A = εNFA_kstar A')
    (qs qf : ℕ) (x : List alphabet) (x' : List (Option alphabet))
    (h_x': x'.reduceOption = x) (h_x_not_empty: x ≠ []) (h_A_path_qs_qf_x': A.IsPath qs qf x') :
    ∃ (qs' qf' : ℕ) (a b : List alphabet) (a' b' : List (Option alphabet)),
    (a'.reduceOption = a) ∧ (b'.reduceOption = b) ∧
    (x = a ++ b) ∧ (qs' ∈ A.εClosure {qs}) ∧ (A'.IsPath qs' qf' a') ∧ (A.IsPath qf' qf b') := by

    by_cases h_qs_1: qs = 1
    case pos =>
        sorry
    case neg =>
        sorry
    -- cases h_x_path_in_A
    -- case nil =>
    --     sorry
    -- case cons t qs qf c tail h_step h_rest =>
    --     sorry

lemma kstar_accepts_decomposed_nonempty
    (A A' : εNFA alphabet ℕ) (hA': A'.is_0mod2) (hA : A = εNFA_kstar A') (x : List alphabet) :
    x ∈ A.accepts → x = [] ∨ ∃ a b : List alphabet, x = a ++ b ∧ a ≠ [] ∧ a ∈ A'.accepts ∧ b ∈ A.accepts := by
    intro h_x_in_A

    by_cases h_x_nil : x = []
    case pos => left; exact h_x_nil
    case neg =>
        right
        obtain ⟨ qs, qf, y', h_qs, h_qf, h_x, h_path ⟩ := A.mem_accepts_iff_exists_path.mp h_x_in_A
        clear h_qs h_qf
        induction h_path generalizing x with
        | nil q =>
            subst h_x
            absurd h_x_nil
            exact List.reduceOption_nil
        | cons t qs qf c tail h_step h_rest ih =>
            by_cases h_tail_empty: tail = []
            case pos =>
                cases c with
                | none =>
                    simp [h_tail_empty] at h_x
                    simp [h_x] at h_x_nil
                | some σ =>
                    absurd h_step
                    simp [hA, εNFA_kstar]

                    have h_qs_1: qs = 1 := by
                        simp [hA, εNFA_kstar] at h_qs
                        exact h_qs


                    use [σ], []

                    have h_x_σ_nil : x = [σ] ++ [] := by
                        subst h_tail_empty h_x
                        exact Eq.symm (List.append_nil [σ])

                    have h_x_σ : x = [σ] :=
                        Multiset.coe_eq_singleton.mp (congrArg Multiset.ofList h_x_σ_nil)

                    refine ⟨ h_x_σ_nil, List.cons_ne_nil σ [], ?_ ⟩

                    have h_1_notin_A': 1 ∉ A'.start ∧ 1 ∉ A'.accept:= by
                        constructor
                        case left =>
                            by_contra!
                            apply if_0mod2_qs_is_0mod2 A' hA' 1 at this
                            contradiction
                        case right =>
                            by_contra!
                            apply if_0mod2_qf_is_0mod2 A' hA' 1 at this
                            contradiction

                    constructor
                    case left =>
                        subst h_x_σ
                        --obtain ⟨ qs, qf, y', h_qs, h_qf, h_x, h_path ⟩ := A.mem_accepts_iff_exists_path.mp h_x_in_A
                        -- have h_qs_qf_1 : qs = 1 ∧ qf = 1 := by
                        --     simp [hA, εNFA_kstar] at h_qs h_qf
                        --     exact ⟨ h_qs, h_qf ⟩
                        -- have : qs ∉ A'.start ∧ qf ∉ A'.accept := by
                        --     simp [h_qs_qf_1, h_1_notin_A']


                        have : ∃ q₂ ∈ A'.accept, ∃ (x' : List (Option alphabet)),  x'.reduceOption = [σ] ∧ A'.IsPath t q₂ x' := by
                            sorry
                        obtain ⟨ q₂, hq₂, x', hx' ⟩ := this

                        apply A'.mem_accepts_iff_exists_path.mpr
                        use t, q₂, x'
                        refine ⟨ ?_, hq₂, hx'.left, hx'.right ⟩
                        have : some σ ≠ none := Option.some_ne_none σ
                        rw [hA, εNFA_kstar] at h_step
                        simp [this] at h_step



                    case right =>
                        rw [mem_accepts_iff_exists_path]
                        use 1, 1, [none]

                        simp [hA, εNFA_kstar, h_1_notin_A']

lemma Star_Regex_to_εNFA (r : RegularExpression alphabet) :
    (∃ (Ar: εNFA alphabet ℕ), r.matches' = Ar.accepts) →
    ∃ (A: εNFA alphabet ℕ), (r.star).matches' = A.accepts := by
    intro h_r
    obtain ⟨ Ar, hAr ⟩ := h_r
    let A' := Ar.to_0mod2
    have hA' : A'.is_0mod2 := by use Ar

    let A : εNFA alphabet ℕ := εNFA_kstar A'
    use A

    have h_contains: A.contains A' := by
        unfold εNFA.contains
        intro q σ
        simp [A, εNFA_kstar]
        split_ifs
        case pos => exact subset_insert 1 (A'.step q σ)
        case pos h_1 =>
            obtain ⟨ hq_1, h_σ_none ⟩ := h_1
            subst hq_1 h_σ_none
            have h_empty : A'.step 1 none = ∅ := by
                simp [A', to_0mod2]
            simp [h_empty]

        case neg => simp [subset_refl]

    simp
    rw [hAr, @Language.kstar_def, @Language.ext_iff, accepts_eq_0mod2_accepts Ar A' rfl]

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

                exact path_if_contains A A' h_contains qs qf head' h_path

            apply h_induction at h_tail
            exact kstar_append A A' (head :: tail).flatten head tail.flatten rfl rfl ⟨ h_head_acc, h_tail⟩

    case mpr =>
        intro h_x_in_A
        by_cases h_x_empty: x ≠ []
        case neg => use []; tauto
        case pos =>
            rw [mem_accepts_iff_exists_path] at h_x_in_A
            obtain ⟨ qs, qf, x', ⟨ h_qs, h_qf, h_x', h_path ⟩ ⟩ := h_x_in_A



            obtain ⟨ qs', qf', a, b, a', b', ⟨ h_a', h_b', h_x_ab, h_A_path_qs_qs'_nil, h_A'_path_qs'_qf'_a, h_A_path_qf'_qf_b ⟩ ⟩ :=
                kstar_decompose_path A A' hA' rfl qs qf x x' h_x' h_x_empty h_path

            --subst h_qs h_qf
            --(x' = a ++ b ∧ A.IsPath qs qs' [] ∧ A'.IsPath qs' qf' a ∧ A.IsPath qf' qf b) := by
            induction h_A_path_qf'_qf_b with
            | nil q' =>
                --simp [A, εNFA_kstar] at h_qs h_qf
                use [a]
                simp
                simp at h_b'
                simp [h_b'] at h_x_ab
                refine ⟨ h_x_ab , ?_ ⟩

                have h_qs'_start: qs' ∈ A'.start := by
                    by_cases qs = 1
                    case pos h_qs_1 =>
                        subst h_qs_1
                    cases h_A_path_qs_qs'_nil with
                    | base _ h_eq =>
                        simp at h_eq
                        --simp [A, εNFA_kstar, symm h_eq] at h_qs
                        --have : qs' % 2 = 1 := by omega
                        have : a = x := by
                            exact List.append_cancel_left (congrArg (HAppend.hAppend x) (id (symm h_x_ab)))
                        subst this

                        cases h_A'_path_qs'_qf'_a with
                        | nil =>
                            simp_all only [ne_eq, List.reduceOption_nil, List.nil_eq, A', A]
                        | cons t q₁ q₂ c tail h_step h_path =>

                            sorry

                    | step => sorry

                sorry

            | cons =>
                sorry

            have hx :
                ∃ L : List (List alphabet),
                    x = L.flatten ∧ ∀ y ∈ L, y ∈ A'.accepts :=
                    kstar_decompose_path (A := A) (A' := A') (hA := rfl) (x := x) h_in_A
            rcases hx with ⟨L, h_flat, h_all⟩
            exact ⟨L, h_flat, h_all⟩




theorem Regex_to_εNFA (r: RegularExpression alphabet) : ∃ (A: εNFA alphabet ℕ), r.matches' = A.accepts := by
    induction r
    case zero => exact Zero_Regex_to_εNFA
    case epsilon => exact Epsilon_Regex_to_εNFA
    case char σ => exact Char_Regex_to_εNFA σ
    case plus _ _ r₁ r₂ h_r₁ h_r₂ => exact Plus_Regex_to_εNFA r₁ r₂ h_r₁ h_r₂
    case comp _ _ r₁ r₂ h_r₁ h_r₂ => exact Comp_Regex_to_εNFA r₁ r₂ h_r₁ h_r₂
    case star _ _ r h_r => exact Star_Regex_to_εNFA r h_r

end εNFA

theorem εNFA_to_Regex (A: εNFA alphabet ℕ) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry
