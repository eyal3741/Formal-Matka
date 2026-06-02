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
        if q % 2 = 0 then
            { 2*q' | q' ∈ (A.step (q/2) c) }
        else
            ∅
    : εNFA α ℕ
}

def to_1mod2 (A : εNFA α ℕ) : εNFA α ℕ := {
    start  := { 2*q' + 1 | q' ∈ A.start  }
    accept := { 2*q' + 1 | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 = 1 then
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

end εNFA

--------------------------
-- THE OTHER DIRECTION: --
--------------------------

variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]  --TODO: NOAM change format

lemma dont_go_nowhere (A : εNFA alphabet ℕ) (hAempty : A.start = ∅) : A.accepts = 0 := by
    simp [Language.zero_def]
    rw [Set.eq_empty_iff_forall_notMem] at hAempty ⊢
    intro x
    by_contra!
    obtain ⟨ s₁, _, _, h_s₁, _⟩ := A.mem_accepts_iff_exists_path.mp this
    simp [hAempty] at h_s₁ -- contradiction


def SingularStart  := 2
def SingularAccept := 0

def to_singular (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { SingularStart }
    accept := { SingularAccept }
    step   := fun q c =>
        let A' := A.to_1mod2
        if q % 2 = 1 then
            if q ∈ A'.accept && c = none then
                A'.step q c ∪ { SingularAccept }
            else
                A'.step q c
        else
            if q = SingularStart && c = none then
                A'.start
            else
                ∅
    : εNFA alphabet ℕ
}

def is_alone_in_set (set: Set ℕ) (n: ℕ):= set = { n }
def is_singular (A : εNFA alphabet ℕ) :=
    (∃s: ℕ, is_alone_in_set A.start s) ∧ (∃a: ℕ, is_alone_in_set A.accept a)

lemma to_singular_contains (A: εNFA alphabet ℕ): (to_singular A).contains A.to_1mod2 := by
    unfold εNFA.contains
    intro q σ
    simp [to_singular, εNFA.to_1mod2]
    split_ifs
    all_goals simp only [subset_insert, subset_refl, empty_subset]


lemma accepts_iff_singular_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_singular A) :
    A.accepts = A'.accepts := by
    rw [@Language.ext_iff]
    intro x
    constructor
    case mp =>
        intro h_A_accepts_x
        rw[@εNFA.mem_accepts_iff_exists_path] at h_A_accepts_x ⊢

        obtain ⟨ s, a, x', hs, ha, hx', hApath⟩ := h_A_accepts_x
        use SingularStart, SingularAccept, ([none] ++ x' ++ [none])

        refine ⟨ by subst hA'; rfl, by subst hA'; rfl,
            by simp only [List.nil_append, List.reduceOption_cons_of_none, List.reduceOption_append, List.reduceOption_nil, List.append_nil, hx']
            , ?_ ⟩

        have hfirst: A'.IsPath SingularStart (2*s + 1) [none] := by
            subst hA'
            simp [to_singular, εNFA.to_1mod2, hs, SingularStart]

        have hlast: A'.IsPath (2*a + 1) SingularAccept [none] := by
            subst hA'
            simp [to_singular, εNFA.to_1mod2, ha, SingularAccept]

        have hmiddle: A'.IsPath (2*s + 1) (2*a + 1) x' := by
            subst hA'
            have h_A_0mod2_path := (A.path_iff_1mod2_path A.to_1mod2 s a (2*s + 1) (2*a + 1) x' rfl rfl rfl).mp hApath
            have hcontains := to_singular_contains A
            apply εNFA.path_if_contains at hcontains
            exact hcontains (2*s + 1) (2*a + 1) x' h_A_0mod2_path

        apply A'.isPath_append.mpr; use (2*a + 1)
        refine ⟨ ?_, hlast ⟩

        apply A'.isPath_append.mpr; use (2*s + 1)

    case mpr =>
        intro h_A'_accepts_x
        rw [A.accepts_iff_1mod2_accepts A.to_1mod2 rfl]

        rw[@εNFA.mem_accepts_iff_exists_path] at h_A'_accepts_x ⊢
        obtain ⟨ s', a', x', h_s'_start, h_a'_accept, h_x', hA'path ⟩ := h_A'_accepts_x

        have h_s'_2: s' = SingularStart := by
            subst hA'
            simp [to_singular] at h_s'_start
            exact h_s'_start

        have h_a'_4: a' = SingularAccept := by
            subst hA'
            simp [to_singular] at h_a'_accept
            exact h_a'_accept

        subst h_s'_2
        subst h_a'_4
        clear h_s'_start h_a'_accept

        cases hA'path
        case cons s σ y' h_step h_path_s_accept =>
            simp [hA', to_singular, SingularStart, SingularAccept] at h_step
            obtain ⟨ ⟨ _, h_σ_none ⟩ , h_s_start ⟩ := h_step

            have first_transition_is_to_odd_state: s % 2 = 1:=
                A.to_1mod2.if_1mod2_qs_is_1mod2 ⟨A, rfl⟩ s h_s_start

            have h_temp: ∀ (q q': ℕ) (σ : Option alphabet), (q % 2 = 1) → (q' % 2 = 1) → (q' ∈ A'.step q σ )
            → (q' ∈ A.to_1mod2.step q σ ) := by
                intro q q' σ hq_odd hq'_odd hstep
                subst hA'
                simp [to_singular, hq_odd] at hstep ⊢
                by_cases hacc : q ∈ (A.to_1mod2).accept ∧ σ = none
                · simp [hacc] at hstep ⊢
                  rcases hstep with h | h
                  · exfalso
                    simp[SingularAccept] at h
                    omega
                  · exact h
                · simp [hacc] at hstep ⊢
                  exact hstep

               --transition between odds in A' -> same transition in A1

            --next step: path between odds in A' is odd
            --next step: odd path in A' -> odd path in A1

            have path_to_singular_accept (q : ℕ) (y : List (Option alphabet))
                (h_q_1mod2: q % 2 = 1) (h_path : A'.IsPath q SingularAccept y) :
                ∃ qf mid, qf ∈ (A.to_1mod2).accept ∧ (A.to_1mod2).IsPath q qf mid ∧ y = mid ++ [none] := by
                induction y generalizing q
                case nil =>
                    simp only [εNFA.isPath_nil] at h_path
                    simp [SingularAccept] at h_path
                    omega
                case cons c tail h_induction =>
                    cases h_path
                    case cons t h_step h_path =>
                        by_cases tail = []
                        case pos h_tail_empty =>
                            clear h_induction
                            subst h_tail_empty
                            simp only [εNFA.isPath_nil] at h_path
                            subst h_path

                            have h_c_none : c = none := by
                                simp [hA', to_singular, h_q_1mod2] at h_step
                                split_ifs at h_step
                                case pos h_none => exact h_none.right
                                case neg =>
                                    have : SingularAccept % 2 = 1 :=
                                        (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A,rfl⟩ q SingularAccept c h_step).right
                                    simp [SingularAccept] at this -- contradiction
                            subst h_c_none

                            use q, []
                            simp only [εNFA.isPath_nil, List.nil_append, and_self, and_true]

                            simp [hA', to_singular, h_q_1mod2] at h_step
                            split_ifs at h_step
                            case pos h_q_accept => exact h_q_accept
                            case neg =>
                                have : SingularAccept % 2 = 1 :=
                                        (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A,rfl⟩ q SingularAccept none h_step).right
                                simp [SingularAccept] at this -- contradiction

                        case neg h_tail_nonempty =>
                            have h_t_1mod2 : t % 2 = 1 := by
                                cases h_path
                                case nil => contradiction
                                case cons t' c' tail' h_step' h_path' =>
                                    have h_t_not_SAS : t ≠ SingularAccept := by
                                        by_contra!
                                        subst this

                                        have h_step'_empty : A'.step SingularAccept c' = ∅ := by
                                            simp [hA', to_singular, SingularAccept, SingularStart]

                                        simp [h_step'_empty] at h_step' --contradiction

                                    simp [hA', to_singular, h_q_1mod2] at h_step
                                    split_ifs at h_step
                                    case pos h_accept =>
                                        simp [h_t_not_SAS] at h_step
                                        exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step).right
                                    case neg => exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step).right

                            obtain ⟨ qf, mid', h_induction ⟩ := h_induction t h_t_1mod2 h_path
                            use qf, c :: mid'
                            simp [h_induction]
                            replace h_induction := h_induction.right.left
                            simp [hA', to_singular, h_q_1mod2] at h_step
                            split_ifs at h_step
                            case pos =>
                                have : t ≠ SingularAccept := by simp [SingularAccept]; omega
                                simp [this] at h_step
                                apply A.to_1mod2.isPath_singleton.mpr at h_step
                                exact A.to_1mod2.isPath_append.mpr ⟨ t, h_step, h_induction⟩
                            case neg =>
                                apply A.to_1mod2.isPath_singleton.mpr at h_step
                                exact A.to_1mod2.isPath_append.mpr ⟨ t, h_step, h_induction⟩

            obtain ⟨qf, mid, h_qf_accept, h_mid_path, h_y'_eq⟩ :=
              path_to_singular_accept (q := s) (y := y') first_transition_is_to_odd_state h_path_s_accept

            have h_mid : mid.reduceOption = x := by
                simp only [h_y'_eq, List.reduceOption_cons_of_none, List.reduceOption_append,
                  List.reduceOption_nil, List.append_nil] at h_x'
                exact h_x'

            use s, qf, mid


def εNFA.max_reachable_node (A : εNFA alphabet ℕ) (n : ℕ) :=
    (∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n x)
    ∧
    ∀n': ℕ, (n' > n) → ¬(∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n' x)

def εNFA.is_finite_automata (A : εNFA alphabet ℕ) :=
    (A.start = ∅) ∨ (∃n: ℕ, A.max_reachable_node n)

lemma if_1mod2_max_reachable_is_1mod2 (A : εNFA alphabet ℕ) (n: ℕ) (hA: A.is_1mod2) (h_n: A.max_reachable_node n) :
    n % 2 = 1 := by
    unfold εNFA.max_reachable_node at h_n
    obtain ⟨ ⟨ s, x, ⟨ h_s_start, h_path ⟩ ⟩, _ ⟩ := h_n
    apply A.if_1mod2_qs_is_1mod2 hA at h_s_start
    apply A.if_1mod2_path_is_same_mod2 hA s n x at h_path
    omega

lemma finite_iff_1mod2_is_finite (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = A.to_1mod2) :
    A.is_finite_automata ↔ A'.is_finite_automata := by
    constructor
    case mp =>
        intro h_A_is_finite
        unfold εNFA.is_finite_automata at h_A_is_finite ⊢
        cases h_A_is_finite
        case inl h_A_start_empty =>
            left
            simp [hA', εNFA.to_1mod2, h_A_start_empty]
        case inr h_max_reachable =>
            right
            obtain ⟨ n, h_max_reachable ⟩ := h_max_reachable
            use 2*n + 1
            unfold εNFA.max_reachable_node at h_max_reachable ⊢
            obtain ⟨ ⟨ s, x, ⟨ h_s_start, h_path ⟩ ⟩, h ⟩ := h_max_reachable
            have h_A_path_iff_A'_path := (A.path_iff_1mod2_path A' s n (2*s + 1) (2*n + 1) x hA' rfl rfl).mp h_path
            constructor
            case left =>
                use 2*s + 1, x
                exact ⟨ by simp [hA', εNFA.to_1mod2, h_s_start], h_A_path_iff_A'_path ⟩
            case right =>
                intro k' h_k'
                by_cases k' % 2 = 0
                case pos h_k'_0mod2 =>
                    simp
                    intro s' h_s' x h_A'_path

                    replace h_s' := A'.if_1mod2_qs_is_1mod2 ⟨A, hA'⟩ s' h_s'
                    have := A'.if_1mod2_path_is_same_mod2 ⟨A, hA'⟩ s' k' x h_A'_path
                    omega

                case neg =>
                    let k := (k' - 1)/2

                    have h_k_greater: k > n := by omega
                    have h_path_A := h k h_k_greater
                    simp at h_path_A ⊢
                    intro s' h_s' x

                    simp [hA', εNFA.to_1mod2] at h_s'
                    obtain ⟨ s, h_s_start, h_s ⟩ := h_s'
                    replace h_path_A := h_path_A s h_s_start x
                    replace h_k': k' = 2*k + 1 := by omega
                    by_contra! h_path_A'
                    have := (A.path_iff_1mod2_path A' s k s' k' x hA' (symm h_s) h_k').mpr h_path_A'
                    contradiction

    case mpr =>
        intro h_A'_is_finite
        unfold εNFA.is_finite_automata at h_A'_is_finite ⊢
        cases h_A'_is_finite
        case inl h_A'_start_empty =>
            left
            by_contra! h_A_start_nonempty
            obtain ⟨ q, h_q ⟩ := nonempty_def.mp h_A_start_nonempty
            clear h_A_start_nonempty
            absurd h_A'_start_empty
            push_neg
            simp [nonempty_def]
            use 2*q + 1
            simp [hA', εNFA.to_1mod2, h_q]

        case inr h_max_reachable =>
            right
            obtain ⟨n', h_max_reachable⟩ := h_max_reachable
            have h_n'_1mod2 : n' % 2 = 1 := if_1mod2_max_reachable_is_1mod2 A' n' ⟨A, hA'⟩ h_max_reachable

            let n := (n' - 1) / 2
            use n
            unfold εNFA.max_reachable_node at h_max_reachable ⊢
            constructor
            case left =>
                obtain ⟨ ⟨ s', x, ⟨ h_s'_start, h_A'_path ⟩ ⟩, _ ⟩ := h_max_reachable
                simp [hA', εNFA.to_1mod2] at h_s'_start
                obtain ⟨s, h_s ⟩ := h_s'_start
                use s, x

                refine ⟨ h_s.left, ?_ ⟩
                have := A.path_iff_1mod2_path A' s n s' n' x hA' (symm h_s.right) (by omega)
                exact this.mpr h_A'_path

            case right =>
                obtain ⟨ ⟨_ ⟩, h ⟩ := h_max_reachable
                intro k h_k
                let k' := k*2 + 1
                simp
                intro s h_s x h_path_A
                have := h k' (by omega)
                absurd this

                let s' := s*2 + 1
                have h_s'_start: s' ∈ A'.start := by
                    simp [hA', εNFA.to_1mod2, s']
                    use s
                    exact ⟨h_s, by omega⟩

                use s', x
                refine ⟨ h_s'_start, ?_ ⟩
                have := A.path_iff_1mod2_path A' s k s' k' x hA' (by omega) (by omega)
                exact this.mp h_path_A

lemma if_singular_1mod2_path (A A' : εNFA alphabet ℕ) (qs qf : ℕ) (hA': A' = to_singular A)
    (h_qs: qs % 2 = 1) (h_qf: qf % 2 = 1) (x: List (Option alphabet)):
    A'.IsPath qs qf x ↔ A.to_1mod2.IsPath qs qf x := by
    constructor
    case mp =>
        intro h_A'_path
        induction h_A'_path
        case nil => simp only [εNFA.isPath_nil]
        case cons t qs qf c tail h_step h_path h_induction =>
            have h_t : t % 2 = 1 := by
                clear h_induction
                by_contra!
                simp [hA', to_singular, h_qs] at h_step
                split_ifs at h_step
                case pos h_c_none =>
                    simp at h_step
                    cases h_step
                    case inl h_t_singular =>
                        replace h_c_none := h_c_none.right
                        subst h_c_none

                        have h_t_step :∀ (c: Option alphabet), A'.step t c = ∅ := by
                            simp [h_t_singular, hA', to_singular, SingularAccept, SingularStart]

                        cases h_path
                        case nil => contradiction
                        case cons t' c tail' h_step' _ =>
                            replace h_t_step := h_t_step c
                            simp [h_t_step] at h_step' -- contradiction

                    case inr h_step =>
                        have := A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ qs t c h_step
                        omega

                case neg =>
                    have := A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ qs t c h_step
                    omega

            replace h_step : t ∈ A.to_1mod2.step qs c := by
                simp [hA', to_singular, h_qs, SingularAccept, SingularStart] at h_step
                split_ifs at h_step
                case pos =>
                    simp at h_step
                    cases h_step
                    case inl => omega
                    case inr h_step=>  exact h_step
                case neg => exact h_step

            apply A.to_1mod2.isPath_singleton.mpr at h_step
            have := h_induction h_t h_qf
            exact A.to_1mod2.isPath_append.mpr ⟨ t, h_step, this ⟩

    case mpr =>
        intro h_A1mod2_path

        have h_A'_contains_A_1mod2 : A'.contains A.to_1mod2 := by
            subst hA'
            exact to_singular_contains A

        exact A'.path_if_contains A.to_1mod2 h_A'_contains_A_1mod2 qs qf x h_A1mod2_path

lemma singular_path_from_odd_ends_odd
    (A A' : εNFA alphabet ℕ) (q qf : ℕ) (y : List (Option alphabet))
    (hA' : A' = to_singular A)
    (h_q_odd : q % 2 = 1)
    (h_qf_gt : qf > SingularStart)
    (h_path : A'.IsPath q qf y) :
    qf % 2 = 1 := by
  induction h_path
  · omega
  · rename_i t q qf c tail h_step h_rest ih
    by_cases h_tail_empty : tail = []
    · subst h_tail_empty
      simp at h_rest
      subst h_rest
      have h_t_ne_zero : t ≠ SingularAccept := by
        simp [SingularAccept]
        omega

      simp [hA', to_singular, h_q_odd, SingularAccept, SingularStart] at h_step h_t_ne_zero
      split_ifs at h_step
      · simp [h_t_ne_zero] at h_step
        exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step).right
      · exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step).right
    · have h_t_odd : t % 2 = 1 := by
        simp [hA', to_singular, h_q_odd] at h_step
        split_ifs at h_step
        · rcases h_step with h_zero | h_step1
          · subst h_zero
            cases h_rest with
            | nil => contradiction
            | cons =>
                rename_i u d tail' hstep_bad hpath_bad
                simp [hA', to_singular, SingularAccept, SingularStart] at hstep_bad
          · exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step1).right
        · exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ q t c h_step).right
      exact ih h_t_odd h_qf_gt


lemma finite_iff_to_singular_finite (A A' : εNFA alphabet ℕ) (hA': A' = to_singular A):
    A.is_finite_automata ↔ A'.is_finite_automata := by
    rw [finite_iff_1mod2_is_finite A A.to_1mod2 rfl]

    unfold εNFA.is_finite_automata
    constructor
    case mp =>
        rintro (h_start_empty | h_max_reachable)
        case inl =>
            right

            use SingularStart
            unfold εNFA.max_reachable_node
            constructor
            case h.left =>
                use SingularStart, []
                simp [hA', to_singular]
            case h.right =>
                intro n' h_n'
                by_contra!
                obtain ⟨ s₁, x, h ⟩ := this
                have : s₁ = SingularStart := by
                    replace h := h.left
                    simp [hA', to_singular] at h
                    exact h
                subst this
                replace h := h.right
                cases h
                case nil => contradiction
                case cons t c x' h_step h_path =>
                    simp [hA', to_singular, h_start_empty, SingularStart] at h_step

        case inr =>
            right
            obtain ⟨ n, h_n ⟩ := h_max_reachable

            unfold εNFA.max_reachable_node at h_n ⊢

            obtain ⟨ ⟨ q, x, h_q_start, h_path_q_n_x ⟩, h_n_max ⟩ := h_n

            have h_A'_contains_A_1mod2 := to_singular_contains A
            rw[← hA'] at h_A'_contains_A_1mod2

            by_cases n > SingularStart
            case pos =>
                use n
                constructor
                case left =>
                    use SingularStart, [none] ++ x
                    refine ⟨ by simp [hA', to_singular], ?_ ⟩
                    apply A'.path_if_contains A.to_1mod2 h_A'_contains_A_1mod2 at h_path_q_n_x

                    have h_step: q ∈ A'.step SingularStart none := by
                        simp [hA', to_singular, SingularStart, h_q_start]

                    apply A'.isPath_singleton.mpr at h_step
                    exact A'.isPath_append.mpr ⟨ q, h_step, h_path_q_n_x ⟩

                case right =>
                    intro n' h_n'

                    simp at h_n_max ⊢
                    intro s' h_s' x

                    simp [hA', to_singular] at h_s'
                    subst h_s'

                    by_contra!
                    cases this
                    case nil =>
                        omega
                    case cons t' c tail h_step h_path =>
                        have h_t_start: t' ∈ A.to_1mod2.start := by
                            simp [hA', to_singular, SingularStart] at h_step
                            exact h_step.right

                        absurd h_n_max
                        simp
                        use n'
                        have : n' > n := by omega
                        simp [this]
                        clear this

                        use t'

                        refine ⟨ h_t_start, ?_ ⟩
                        use tail
                        by_cases h_tail_empty: tail = []
                        case pos =>
                            subst h_tail_empty
                            simp at h_path ⊢
                            exact h_path
                        case neg =>
                            have h_t' : t' % 2 = 1 := A.to_1mod2.if_1mod2_qs_is_1mod2 ⟨A, rfl⟩ t' h_t_start
                            have h_n' : n' % 2 = 1 := by
                                clear h_step h_n_max h_t_start
                                induction h_path
                                case nil => omega
                                case cons t t' n' c tail' h_step h_path h_induction =>
                                    by_cases h_tail'_empty: tail' = []
                                    case pos =>
                                        subst h_tail'_empty
                                        simp at h_path
                                        subst h_path
                                        have : t ≠ SingularAccept := by
                                            have : SingularStart > SingularAccept := by
                                                simp [SingularStart, SingularAccept]
                                            omega
                                        simp [hA', to_singular, h_t'] at h_step
                                        split_ifs at h_step
                                        case pos =>
                                            simp [this] at h_step
                                            exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ t' t c h_step).right
                                        case neg =>
                                            exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ t' t c h_step).right

                                    case neg =>
                                        apply h_induction h_n' h_tail'_empty
                                        simp [hA', to_singular, h_t'] at h_step
                                        split_ifs at h_step
                                        case pos h_accept =>
                                            replace h_accept := h_accept.left
                                            simp at h_step
                                            cases h_step
                                            case inl h_t_accept =>
                                                subst h_t_accept
                                                cases h_path
                                                case nil => contradiction
                                                case cons u c _ h_step _ =>
                                                    simp [hA', to_singular, SingularAccept, SingularStart] at h_step -- contradiction

                                            case inr h_step =>
                                                exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ t' t c h_step).right
                                        case neg =>
                                            exact (A.to_1mod2.if_1mod2_step_is_1mod2 ⟨A, rfl⟩ t' t c h_step).right

                            exact (if_singular_1mod2_path A A' t' n' hA' h_t' h_n' tail).mp h_path
            case neg =>
                use SingularStart
                constructor
                case left =>
                    use SingularStart, []
                    simp [hA', to_singular]
                case right  h_n_less =>
                    simp at h_n_less
                    intro n' h_n'

                    have h_not_reach : ¬ ∃ s₁ x, s₁ ∈ A.to_1mod2.start ∧ A.to_1mod2.IsPath s₁ n' x := by
                        exact h_n_max n' (by omega)

                    rintro ⟨ q, x, h_q_start, h_A'_path ⟩
                    have h_q : q = SingularStart := by
                        simp [hA', to_singular] at h_q_start
                        exact h_q_start
                    subst h_q
                    cases h_A'_path with
                    | nil =>
                        omega
                    | cons =>
                        rename_i t' σ tail hstep hpath
                        have h_t_start : t' ∈ A.to_1mod2.start := by
                            simp [hA', to_singular, SingularStart] at hstep
                            exact hstep.2
                        have h_t_odd : t' % 2 = 1 :=
                            A.to_1mod2.if_1mod2_qs_is_1mod2 ⟨A, rfl⟩ t' h_t_start
                        have h_n'_odd : n' % 2 = 1 := by
                             exact singular_path_from_odd_ends_odd A A' t' n' tail hA' h_t_odd h_n' hpath
                        have h_path_1mod2 : A.to_1mod2.IsPath t' n' tail :=
                            (if_singular_1mod2_path A A' t' n' hA' h_t_odd h_n'_odd tail).mp hpath

                        exact h_not_reach ⟨ t', tail, h_t_start, h_path_1mod2 ⟩

    case mpr =>
        rintro (h_start_empty | h_max_reachable)
        case inl =>
            exfalso
            rw [hA'] at h_start_empty
            simp [to_singular] at h_start_empty
        case inr =>
            have h_A'_contains_A_1mod2 := to_singular_contains A
            rw[← hA'] at h_A'_contains_A_1mod2

            by_cases h_start_empty : A.to_1mod2.start = ∅
            case pos =>
                exact Or.inl h_start_empty
            case neg =>
                right
                obtain ⟨n, h_n⟩ := h_max_reachable
                unfold εNFA.max_reachable_node at h_n ⊢
                obtain ⟨h_n_reachable, h_n_max⟩ := h_n
                obtain ⟨s, x, h_s_start, h_path⟩ := h_n_reachable
                have h_bound :
                ∀ k s x, s ∈ A.to_1mod2.start → A.to_1mod2.IsPath s k x → k ≤ n := by
                    intro k s x h_s_start h_path_1mod2
                    by_contra h_not_le
                    have hk_gt : k > n := by omega
                    have h_step_from_singular : s ∈ A'.step SingularStart none := by
                        simp [hA', to_singular, SingularStart, h_s_start]
                    have h_singleton : A'.IsPath SingularStart s [none] := by
                        apply A'.isPath_singleton.mpr
                        exact h_step_from_singular
                    have h_path_in_A' : A'.IsPath s k x := by
                        exact A'.path_if_contains A.to_1mod2 h_A'_contains_A_1mod2 s k x h_path_1mod2
                    have h_reach_k_in_A' : A'.IsPath SingularStart k ([none] ++ x) := by
                        exact A'.isPath_append.mpr ⟨s, h_singleton, h_path_in_A'⟩
                    have h_not_reach := h_n_max k hk_gt
                    apply h_not_reach
                    use SingularStart, [none] ++ x
                    constructor
                    · simp [hA', to_singular]
                    · exact h_reach_k_in_A'
                have h_nonempty : ∃ s, s ∈ A.to_1mod2.start := by
                    by_contra h_no_s
                    apply h_start_empty
                    rw [Set.eq_empty_iff_forall_notMem]
                    intro s hs
                    exact h_no_s ⟨s, hs⟩
                obtain ⟨s, h_s_start⟩ := h_nonempty

                let R : ℕ → Prop :=
                    fun k => ∃ s₁ x,
                        s₁ ∈ A.to_1mod2.start ∧
                        A.to_1mod2.IsPath s₁ k x

                have hR_nonempty_bounded : ∃ k ≤ n, R k := by
                    use s
                    constructor
                    · exact h_bound s s [] h_s_start ((A.to_1mod2.isPath_nil).mpr rfl)
                    · unfold R
                      use s, []
                      exact ⟨h_s_start, (A.to_1mod2.isPath_nil).mpr rfl⟩

                let m := Nat.findGreatest R n

                use m

                constructor
                · unfold m
                  obtain ⟨k, hk_le_n, hk_R⟩ := hR_nonempty_bounded
                  exact Nat.findGreatest_spec hk_le_n hk_R

                · intro k hk
                  by_contra h_reach_k

                  have hk_le_n : k ≤ n := by
                    obtain ⟨s₁, x, h_s₁_start, h_path⟩ := h_reach_k
                    exact h_bound k s₁ x h_s₁_start h_path

                  have h_not_reach_k : ¬ R k := by
                    unfold m at hk
                    exact Nat.findGreatest_is_greatest hk hk_le_n

                  exact h_not_reach_k h_reach_k

def to_trim (A : εNFA alphabet ℕ) (i j k : ℕ) : εNFA alphabet ℕ := {
    start  := { i }
    accept := { j }
    step   := fun q c =>
        if j > k then
            { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k) ∨ (q' = j)) }
        else
            { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k)) }
    : εNFA alphabet ℕ
}

def is_trim (A' : εNFA alphabet ℕ) (i' j' k' : ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_trim A i' j' k'

def to_trim_contains (A A' : εNFA α ℕ) (i' j' k' : ℕ)
    (h_trim : A' = to_trim A i' j' k') : A.contains A' := by
    unfold εNFA.contains
    intro q σ
    subst h_trim
    unfold to_trim
    simp
    split_ifs
    case pos => simp
    case neg => simp

def path_if_to_trim_path (A A' : εNFA α ℕ) (qs qf i' j' k' : ℕ) (y : List (Option α))
    (h_trim : A' = to_trim A i' j' k'):
    (A'.IsPath qs qf y) → (A.IsPath qs qf y) := by
    have h_contains := to_trim_contains A A' i' j' k' h_trim
    exact εNFA.path_if_contains A A' h_contains qs qf y


lemma singular_finite_accepts_iff_trim_accepts (A A': εNFA alphabet ℕ) (s a n: ℕ)
(hAsingular: is_singular A) (hAfinite: A.is_finite_automata)
(hn_max: A.max_reachable_node n) (hs_start: is_alone_in_set A.start s) (ha_accept: is_alone_in_set A.accept a)
(hA'istrim: A' = to_trim A s a n):
    A.accepts = A'.accepts := by sorry -- TODO: EYAL

def character_list_to_regex : List alphabet → RegularExpression alphabet
    | .nil => 0
    | .cons head tail => (RegularExpression.char head) + (character_list_to_regex tail)

lemma character_list_regex_accepts_characters (characters : List alphabet) (r: RegularExpression alphabet)
    (hr: r = character_list_to_regex characters) (x : List alphabet):
    x ∈ r.matches' ↔ ∃ (σ : alphabet), σ ∈ characters ∧ x = [σ] := by
    constructor
    case mp =>
        induction characters generalizing r
        case nil =>
            simp [character_list_to_regex] at hr
            simp [hr]
        case cons σ tail h_induction =>
            intro h_r_matches_x
            simp [character_list_to_regex] at hr
            subst hr
            simp [Language.add_def] at h_r_matches_x
            cases h_r_matches_x
            case inl h_x_σ =>
                use σ
                simp
                exact h_x_σ
            case inr h_x_tail =>
                obtain ⟨ σ, h ⟩ := h_induction (character_list_to_regex tail) rfl h_x_tail
                simp [h]

    case mpr =>
        intro h_σ
        obtain ⟨ σ, h_σ_characters, h_x_σ ⟩ := h_σ
        --unfold character_list_to_regex at hr
        induction characters generalizing r with
        | nil => contradiction
        | cons head tail h_induction =>
            simp at h_σ_characters
            unfold character_list_to_regex at hr
            subst hr
            simp [Language.mem_add]

            cases h_σ_characters
            case inl h_σ_head =>
                left
                subst h_σ_head
                exact h_x_σ
            case inr h_σ_tail =>
                right
                exact h_induction (character_list_to_regex tail) rfl h_σ_tail

noncomputable
def regex_for_path_from_i_to_j_through_k (A : εNFA alphabet ℕ) (i j k : ℕ) :
    RegularExpression alphabet :=
    if k = 0 then
        if i = j then
            let character_set_ii: Finset alphabet := { σ |  i ∈ A.step i (some σ) }
            let characters_ii := character_set_ii.toList

            (character_list_to_regex characters_ii).star
        else if j ∈ A.step i none then
            let character_set_ij: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
            let characters_ij := character_set_ij.toList
            let character_set_jj: Finset alphabet := { σ |  j ∈ A.step j (some σ) }
            let characters_jj := character_set_jj.toList

            (1 + character_list_to_regex characters_ij) * (character_list_to_regex characters_jj).star
        else
            let character_set_ij: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
            let characters_ij := character_set_ij.toList

            character_list_to_regex characters_ij
    else
        let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k-1)
        let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k-1)
        let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k-1)
        let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k-1)

        rᵢⱼ + (rᵢₖ * rₖₖ.star * rₖⱼ)

termination_by k
decreasing_by
    all_goals omega

lemma regex_for_path_contains_ij (A : εNFA alphabet ℕ) (i j k k' : ℕ) (h_k' : k' ≤ k) :
    (to_trim A i j k).contains (to_trim A i j k') := by
    simp [εNFA.contains]
    intro q σ
    rw [@subset_def]
    intro t h_step
    simp [to_trim] at h_step ⊢
    split_ifs
    case pos h_k_j =>
        have h_k'_j: k' < j := by omega
        simp [h_k'_j] at h_step ⊢
        cases h_step
        case inl h_t_k' =>
            left
            simp [h_t_k']
            omega
        case inr h_t_j =>
            right
            exact h_t_j
    case neg h_k_j =>
        simp at h_k_j
        split_ifs at h_step
        case pos h_k'_j =>
            simp at h_step
            cases h_step
            case inl h_step =>
                simp [h_step.left]
                omega
            case inr h_step =>
                simp [h_step.left]
                omega
        case neg h_k'_j =>
            simp at h_k'_j h_step ⊢
            simp [h_step.left]
            omega

lemma regex_for_path_contains_ik (A : εNFA alphabet ℕ) (i j k k' : ℕ) (h_k' : k' ≤ k) :
    (to_trim A i j k).contains (to_trim A i k k') := by
    simp [εNFA.contains]
    intro q σ
    rw [@subset_def]
    intro t h_step
    simp [to_trim] at h_step ⊢
    split_ifs
    case pos h_k_j =>
        have h_k'_j: k' < j := by omega
        simp
        split_ifs at h_step
        case pos h_k'_less =>
            left
            simp_all
            cases h_step
            case inl h => simp [h.left]; omega
            case inr h => simp [h.left]; omega
        case neg h_k'_more =>
            simp at h_step
            left
            simp [h_step]
            omega
    case neg h_k_j =>
        simp at h_k_j
        split_ifs at h_step
        case pos h_k'_j =>
            simp at h_step
            cases h_step
            case inl h_step =>
                simp [h_step.left]
                omega
            case inr h_step =>
                simp [h_step.left]
                omega
        case neg h_k'_j =>
            simp at h_k'_j h_step ⊢
            simp [h_step.left]
            omega

lemma regex_for_path_contains_kk (A : εNFA alphabet ℕ) (i j k k' : ℕ) (h_k' : k' ≤ k) :
    (to_trim A i j k).contains (to_trim A k k k') := by
    simp [εNFA.contains]
    intro q σ
    rw [@subset_def]
    intro t h_step
    simp [to_trim] at h_step ⊢
    split_ifs
    case pos h_k_j =>
        have h_k'_j: k' < j := by omega
        simp
        split_ifs at h_step
        case pos h_k'_less =>
            left
            simp_all
            cases h_step
            case inl h => simp [h.left]; omega
            case inr h => simp [h.left]; omega
        case neg h_k'_more =>
            simp at h_step
            left
            simp [h_step]
            omega
    case neg h_k_j =>
        simp at h_k_j
        split_ifs at h_step
        case pos h_k'_j =>
            simp at h_step
            cases h_step
            case inl h_step =>
                simp [h_step.left]
                omega
            case inr h_step =>
                simp [h_step.left]
                omega
        case neg h_k'_j =>
            simp at h_k'_j h_step ⊢
            simp [h_step.left]
            omega

lemma regex_for_path_kk_star_is_path_in_kk (A : εNFA alphabet ℕ) (k : ℕ) (L': List (List (Option alphabet))) :
    (∀ (x' : List (Option alphabet)), (x' ∈ L' → A.IsPath k k x')) → A.IsPath k k L'.flatten := by
    intro h_y

    induction L'
    case nil =>
        simp only [List.flatten_nil, εNFA.isPath_nil]
    case cons head tail h_induction =>
        have h_tail : (∀ y' ∈ tail, A.IsPath k k y') := by
            simp at h_y
            exact h_y.right
        apply h_induction at h_tail

        simp only [List.flatten_cons]
        apply A.isPath_append.mpr
        use k
        exact ⟨ by simp [h_y], h_tail ⟩

lemma regex_for_path_contains_kj (A : εNFA alphabet ℕ) (i j k k' : ℕ) (h_k' : k' ≤ k) :
    (to_trim A i j k).contains (to_trim A k j k') := by
    simp [εNFA.contains]
    intro q σ
    rw [@subset_def]
    intro t h_step
    simp [to_trim] at h_step ⊢
    split_ifs
    case pos h_k_j =>
        have h_k'_j: k' < j := by omega
        simp [h_k'_j] at h_step ⊢
        cases h_step
        case inl h_t_k' =>
            left
            simp [h_t_k']
            omega
        case inr h_t_j =>
            right
            exact h_t_j
    case neg h_k_j =>
        simp at h_k_j
        split_ifs at h_step
        case pos h_k'_j =>
            simp at h_step
            cases h_step
            case inl h_step =>
                simp [h_step.left]
                omega
            case inr h_step =>
                simp [h_step.left]
                omega
        case neg h_k'_j =>
            simp at h_k'_j h_step ⊢
            simp [h_step.left]
            omega

lemma not_none_is_some (c : Option alphabet):
    c ≠ none → ∃ (σ : alphabet), c = some σ := by
    sorry --TODO

lemma regex_is_path (A : εNFA alphabet ℕ) (i j k : ℕ) (r: RegularExpression alphabet) (hr: r = regex_for_path_from_i_to_j_through_k A i j k) (h_zero_step: ∀ (σ : Option alphabet), A.step 0 σ = ∅):
    ∀(x : List alphabet), ((x ∈ r.matches') ↔ (∃(x': List ((Option alphabet))), (x'.reduceOption = x) ∧ ((to_trim A i j k).IsPath i j x'))) := by
    intro x
    constructor
    case mp =>
        intro h_r_matches_x
        unfold regex_for_path_from_i_to_j_through_k at hr
        split_ifs at hr
        case pos h_k_0 h_ij =>
            subst h_k_0

            simp [hr, Language.kstar_def] at h_r_matches_x
            cases h_r_matches_x
            case intro L h_L =>
                obtain ⟨ h_x_L, h_L ⟩ := h_L

                by_cases h_i_eq_j: i = j
                case pos =>
                    subst h_i_eq_j
                    use []
                    simp [h_x_in_1]
                case neg =>
                    use [none]
                    simp [h_x_in_1, to_trim, h_i_eq_j] at h_ij ⊢
                    split_ifs
                    case pos =>
                        simp
                        right
                        exact h_ij
                    case neg =>
                        simp [h_ij]
                        omega

            case inr h_x_in_character_list =>
                let character_set: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
                let characters := character_set.toList

                obtain ⟨ σ, h_step, h_x_σ ⟩ := (character_list_regex_accepts_characters characters (character_list_to_regex characters) rfl x).mp h_x_in_character_list
                subst characters character_set
                simp at h_step

                use [some σ]
                simp [to_trim, h_x_σ]
                split_ifs
                case pos => simp [h_step]
                case neg => simp [h_step] ; omega

        case neg h_k_0 =>
            simp [hr] at h_r_matches_x
            let character_set: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
            let characters := character_set.toList

            obtain ⟨ σ, h_step, h_x_σ ⟩ := (character_list_regex_accepts_characters characters (character_list_to_regex characters) rfl x).mp h_r_matches_x
            subst characters character_set
            simp at h_step

            use [some σ]
            simp [to_trim, h_x_σ]
            split_ifs
            case pos => simp [h_step]
            case neg => simp [h_step] ; omega

        case neg =>
            let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k - 1)
            let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k - 1)
            let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k - 1) -- later: handle kstar
            let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k - 1)

            simp at h_r_matches_x
            simp [hr, Language.add_def] at h_r_matches_x
            clear hr
            cases h_r_matches_x
            case inl h_x_in_rᵢⱼ =>
                have h_induction := (regex_is_path A i j (k-1) rᵢⱼ rfl x).mp h_x_in_rᵢⱼ
                clear rᵢⱼ rᵢₖ rₖⱼ rₖₖ
                obtain ⟨ x', h_x', h_path ⟩ := h_induction

                use x'
                refine ⟨ h_x', ?_ ⟩

                have h_contains := regex_for_path_contains_ij A i j k (k-1) (by omega)
                exact εNFA.path_if_contains (to_trim A i j k) (to_trim A i j (k-1)) h_contains i j x' h_path
            case inr h_x_in_rᵢₖ_rₖₖ_rₖⱼ =>
                clear rᵢⱼ
                simp [Language.mul_def] at h_x_in_rᵢₖ_rₖₖ_rₖⱼ
                obtain ⟨ xᵢₖ, h_xᵢₖ, xₖₖ, h_xₖₖ, xₖⱼ, h_xₖⱼ, h_x ⟩ := h_x_in_rᵢₖ_rₖₖ_rₖⱼ
                obtain ⟨ xᵢₖ', h_xᵢₖ', h_path_ik ⟩ := (regex_is_path A i k (k-1) rᵢₖ rfl xᵢₖ).mp h_xᵢₖ
                obtain ⟨ xₖⱼ', h_xₖⱼ', h_path_kj ⟩ := (regex_is_path A k j (k-1) rₖⱼ rfl xₖⱼ).mp h_xₖⱼ
                clear rᵢₖ rₖⱼ h_xᵢₖ h_xₖⱼ

                simp [Language.kstar_def] at h_xₖₖ
                obtain ⟨ L, h_L, h_xₖₖ ⟩ := h_xₖₖ

                have h_path_L_kk : ∃ (L' : List (List (Option alphabet))), L'.flatten.reduceOption = L.flatten ∧
                    (∀ x' ∈ L', (to_trim A k k (k - 1)).IsPath k k x') := by
                    clear h_L
                    induction L
                    case nil => use []; simp
                    case cons head tail h_induction =>
                        simp at h_xₖₖ
                        obtain ⟨ L'', h_L'', h_path_L'' ⟩ := h_induction h_xₖₖ.right
                        obtain ⟨ head', h_head', h_path_head' ⟩ := (regex_is_path A k k (k-1) rₖₖ rfl head).mp h_xₖₖ.left
                        use head' :: L''
                        simp [List.reduceOption_append, h_head', h_L'', h_path_head']
                        exact h_path_L''
                clear rₖₖ h_xₖₖ

                obtain ⟨ L', h_L', h_path_kk ⟩ := h_path_L_kk

                let xₖₖ' := L'.flatten
                replace h_path_kk : (to_trim A k k (k - 1)).IsPath k k xₖₖ' := by
                    clear h_L h_L'
                    subst xₖₖ'
                    induction L'
                    case nil => simp only [List.flatten_nil, εNFA.isPath_nil]
                    case cons head tail h_induction =>
                        simp at h_path_kk
                        replace h_induction := h_induction h_path_kk.right

                        simp [List.flatten_cons]
                        apply (to_trim A k k (k - 1)).isPath_append.mpr
                        exact ⟨ k, h_path_kk.left, h_induction ⟩

                use xᵢₖ' ++ xₖₖ' ++ xₖⱼ'

                simp [symm h_xᵢₖ', symm h_xₖⱼ'] at h_x
                simp [List.reduceOption_append]

                have : xₖₖ'.reduceOption = L.flatten := by
                    subst h_L
                    simp_all only [xₖₖ']

                refine ⟨ by simp_all, ?_ ⟩

                have h_containsᵢₖ := regex_for_path_contains_ik A i j k (k-1) (by omega)
                have h_containsₖⱼ := regex_for_path_contains_kj A i j k (k-1) (by omega)
                have h_containsₖₖ := regex_for_path_contains_kk A i j k (k-1) (by omega)
                replace h_path_ik := εNFA.path_if_contains (to_trim A i j k) (to_trim A i k (k-1)) h_containsᵢₖ i k xᵢₖ' h_path_ik
                replace h_path_kj := εNFA.path_if_contains (to_trim A i j k) (to_trim A k j (k-1)) h_containsₖⱼ k j xₖⱼ' h_path_kj
                replace h_path_kk := εNFA.path_if_contains (to_trim A i j k) (to_trim A k k (k-1)) h_containsₖₖ k k xₖₖ' h_path_kk

                apply (to_trim A i j k).isPath_append.mpr
                refine ⟨ k, h_path_ik , ?_ ⟩
                apply (to_trim A i j k).isPath_append.mpr
                use k

    case mpr =>
        intro h
        obtain ⟨ x', h_x', h_x'_path ⟩ := h
        unfold regex_for_path_from_i_to_j_through_k at hr

        split_ifs at hr
        case pos h_k_0 h_ij =>
            subst h_ij h_k_0
            simp at hr
            subst hr
            induction x' generalizing x
            case nil =>
                simp at h_x'
                subst h_x'
                simp [Language.kstar_def]
                use []
                simp
            case cons c tail h_induction =>
                have h_tail_path : (to_trim A i i 0).IsPath i i tail := by
                    by_cases h_i_0: i = 0
                    case pos =>
                        subst h_i_0
                        cases h_x'_path
                        case cons t h_step h_path =>
                            simp [to_trim] at h_step
                            simp [h_step.right] at h_path
                            exact h_path
                    case neg =>
                        cases h_x'_path
                        case cons t h_step h_path =>
                            replace h_i_0: i > 0 := by omega
                            simp [to_trim, h_i_0] at h_step
                            cases h_step
                            case inl h_t_0 =>
                                have := h_t_0.right
                                subst this
                                simp at h_t_0

                                cases h_path
                                case nil => simp
                                case cons _ _ _ h_step' _ =>
                                    unfold to_trim at h_step'
                                    split_ifs at h_step'
                                    simp at h_step'
                                    cases h_step'
                                    case inl h_t'_0 =>
                                        simp [h_t'_0.right, h_zero_step] at h_t'_0 --contradiction
                                    case inr h_t'_i =>
                                        simp [h_t'_i.right, h_zero_step] at h_t'_i --contradiction

                            case inr h_t_i =>
                                simp [h_t_i.right] at h_path
                                exact h_path

                by_cases c = none
                case pos h_c_none =>
                    subst h_c_none
                    exact h_induction x h_x' h_tail_path
                case neg h_c_some =>
                    have h_step: i ∈ (to_trim A i i 0).step i c := by
                        cases h_x'_path
                        case cons t h_step h_path =>
                            simp [to_trim] at h_step
                            split_ifs at h_step
                            case pos h_i =>
                                simp at h_step
                                cases h_step
                                case inl h_t_0 =>
                                    have := h_t_0.right
                                    subst this
                                    cases h_path
                                    case nil => simp [h_zero_step] at h_t_0 -- contradiction
                                    case cons _ _ _ h_step' _ =>
                                        simp [to_trim] at h_step'
                                        split_ifs at h_step'
                                        simp at h_step'
                                        cases h_step'
                                        case inl h_step' =>
                                            simp [h_zero_step] at h_step' -- contradiction
                                        case inr h_step' =>
                                            simp [h_zero_step] at h_step' -- contradiction

                                case inr h_t_i =>
                                    simp [h_t_i.right] at h_t_i
                                    simp [to_trim, h_i]
                                    right
                                    exact h_t_i

                            case neg h_i =>
                                replace h_i : i = 0 := by omega
                                subst h_i
                                simp [h_zero_step] at h_step --contradiction

                    replace h_induction := h_induction tail.reduceOption rfl h_tail_path
                    simp [Language.kstar_def] at h_induction ⊢
                    obtain ⟨ L, h_L_tail, h_L_matches ⟩ := h_induction

                    replace h_c_some := not_none_is_some c h_c_some
                    obtain ⟨ σ, h_σ ⟩ := h_c_some
                    subst h_σ

                    use [σ] :: L
                    simp [h_L_tail] at h_x'
                    simp
                    refine ⟨ symm h_x', ?_, h_L_matches ⟩
                    simp [to_trim] at h_step
                    split_ifs at h_step
                    case pos h_i_0 =>
                        replace h_i_0 : i ≠ 0 := by omega
                        simp [h_i_0] at h_step
                        let character_set: Finset alphabet := { σ |  i ∈ A.step i (some σ) }
                        let characters := character_set.toList
                        let r := character_list_to_regex characters

                        apply (character_list_regex_accepts_characters characters r rfl [σ]).mpr
                        use σ
                        subst characters character_set
                        simp
                        exact h_step
                    case neg h_i_0 =>
                        replace h_i_0 : i = 0 := by omega
                        subst h_i_0
                        simp [h_zero_step] at h_step --contradiction

        case pos h_k_0 h_i_neq_j h_step =>
            cases x'
            case nil =>
                subst h_x' hr
                simp [Language.mem_add, Language.mem_mul]
                left
                sorry -- TODO
            case cons c tail =>
                subst hr
                simp [Language.mem_add, Language.mem_mul]
                by_cases c = none
                case pos h_c_none =>
                    left
                    subst h_c_none
                    simp at h_x'
                    cases h_x'_path
                    case cons t h_step h_path =>

                        sorry

                    exact h_x'
                case neg h_c_some =>
                    right
                    replace h_c_some := not_none_is_some c h_c_some
                    obtain ⟨ σ, h_σ ⟩ := h_c_some
                    subst h_σ
                    simp at h_x'
                    subst h_x'
                    let character_set: Finset alphabet := { σ | j ∈ A.step i (some σ) }
                    let characters := character_set.toList
                    let r := character_list_to_regex characters
                    apply (character_list_regex_accepts_characters characters r rfl [σ]).mpr
                    use σ
                    subst characters character_set
                    simp
                    have h_path_trim := path_if_to_trim_path A (to_trim A i j k) i j i j k [some σ] rfl
                    apply h_path_trim at h_x'_path
                    simp [εNFA.isPath_singleton] at h_x'_path
                    exact h_x'_path


            sorry
        case neg h_k_0 h_i_neq_j h_not_step =>
            subst h_k_0



            -- cases h_step
            -- case inl h_ij =>
            --     subst h_k_0
            --     simp [Language.mem_add]
            --     by_cases x = []
            --     case pos h_x_empty => left; exact h_x_empty
            --     case neg h_x_not_empty =>
            --         right


            sorry

theorem εNFA_to_Regex (A: εNFA alphabet ℕ) : A.is_finite_automata → (∃ (r: RegularExpression alphabet), r.matches' = A.accepts) := by
    let A' := to_singular A
    have hA'tosinA: A' = to_singular A := by
        simp_all only [A']
    rw [accepts_iff_singular_accepts A A']
    swap
    simp_all only [A']
    rw [finite_iff_to_singular_finite A A' hA'tosinA]

    rw [εNFA.is_finite_automata]
    rintro ( hnill | ⟨ n, hnmax ⟩ )
    case inl =>
        use 0
        simp only [dont_go_nowhere A' hnill, RegularExpression.matches']
    case inr =>
        have hA'singular: is_singular A' := by
            simp_all only [A']
            unfold to_singular
            unfold is_singular
            constructor
            use SingularStart
            exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
            use SingularAccept
            exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
        unfold is_singular at hA'singular
        obtain ⟨ s, hs ⟩ := hA'singular.left
        obtain ⟨ a, ha ⟩ := hA'singular.right
        let A'' := to_trim A' s a n
        have histrim: A'' = to_trim A' s a n := by
            simp_all only [A', A'']
        have hA'finite: A'.is_finite_automata := by
            rw [εNFA.is_finite_automata]
            right
            use n
        rw [singular_finite_accepts_iff_trim_accepts
        A' A'' s a n
        hA'singular hA'finite
        hnmax hs ha
        histrim]
        let r' := regex_for_path_from_i_to_j_through_k A'' s a n
        have hr: r' = regex_for_path_from_i_to_j_through_k A' s a n := by
            subst A'
            simp_all only [A'', r']
            obtain ⟨left, right⟩ := hA'singular
            obtain ⟨w, h⟩ := left
            obtain ⟨w_1, h_1⟩ := right
            -- TODO: EYAL
            sorry
        have hgs: A''.start = {s} := by
            simp_all only [A', A'', r']
            obtain ⟨left, right⟩ := hA'singular
            obtain ⟨w, h⟩ := left
            obtain ⟨w_1, h_1⟩ := right
            rfl
        have hga: A''.accept = {a} := by
            simp_all only [A', A'', r']
            obtain ⟨left, right⟩ := hA'singular
            obtain ⟨w, h⟩ := left
            obtain ⟨w_1, h_1⟩ := right
            rfl
        use r'
        rw [@Language.ext_iff]
        intro x
        rw [A''.mem_accepts_iff_exists_path]
        rw [hgs, hga]

        constructor
        case mp =>
            intro hmatch
            use s
            use a
            let hreg := ((regex_is_path A' s a n r' hr) x).mp hmatch

            obtain ⟨ x', ⟨ hx', hpath⟩ ⟩ := hreg

            use x'
            refine ⟨ mem_singleton s, mem_singleton a, hx', ?_ ⟩
            rw [histrim]
            exact hpath
        case mpr =>
            rintro ⟨ temps, tempa, tempx', htemps, htempa, htempx, hpath ⟩
            let hreg := ((regex_is_path A' s a n r' hr) x).mpr
            apply hreg
            use tempx'
            constructor
            · exact htempx
            subst htempx
            simp_all only [mem_singleton_iff, A', A'']
