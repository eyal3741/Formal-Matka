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

--------------------------
-- THE OTHER DIRECTION: --
--------------------------

variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]  --removed?


lemma dont_go_nowhere (A : εNFA alphabet ℕ) (hAempty : A.start = ∅) : A.accepts = 0 := by sorry



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
        simp only [dont_go_nowhere A hnill, RegularExpression.matches']

    case inr =>

        sorry
