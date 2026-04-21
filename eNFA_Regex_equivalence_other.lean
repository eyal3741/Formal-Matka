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

variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]  --TODO: change format

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

lemma finite_iff_to_singular_finite (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_singular A):
    A.is_finite_automata ↔ A'.is_finite_automata := by

    unfold εNFA.is_finite_automata
    constructor
    case mp =>
        rintro (h_start_empty | h_max_reachable)
        case inl =>
            right
            replace h_start_empty : A.to_1mod2.start = ∅ := by
                simp [εNFA.to_1mod2, h_start_empty]

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
            let q₂ := 2*q + 1
            let n₂ := 2*n + 1
            rw [A.path_iff_1mod2_path A.to_1mod2 q n q₂ n₂ x] at h_path_q_n_x

            have h_A'_contains_A_1mod2 := to_singular_contains A
            rw[← hA'] at h_A'_contains_A_1mod2

            by_cases n > SingularStart
            case pos =>
                use n₂
                constructor
                case left =>
                    use SingularStart, [none] ++ x
                    refine ⟨ by simp [hA', to_singular], ?_ ⟩
                    have h_step: q₂ ∈ A'.step SingularStart none := by
                        simp [hA', to_singular, SingularStart, εNFA.to_1mod2, q₂, h_q_start]
                    apply A'.isPath_singleton.mpr at h_step

                    have := A'.path_if_contains A.to_1mod2 h_A'_contains_A_1mod2 q₂ n₂ x h_path_q_n_x

                    exact A'.isPath_append.mpr ⟨ q₂, h_step, this ⟩

                case right =>
                    intro n' h_n'

                    --replace h_n_max := h_n_max n' (by omega)
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
                        simp [εNFA.to_1mod2] at h_t_start
                        obtain ⟨ t, h_t'_start, h_t ⟩ := h_t_start

                        sorry
            case neg =>
                use SingularStart
                constructor
                case left =>
                    use SingularStart, []
                    simp [hA', to_singular]
                case right =>
                    intro n' h_n'
                    by_contra!
                    absurd h_n_max
                    -- todo...
                    sorry
    case mpr =>
        sorry

def to_trim (A : εNFA alphabet ℕ) (i j k : ℕ) : εNFA alphabet ℕ := {
    start  := { i }
    accept := { j }
    step   := fun q c =>
        if j > k then
            if q = j then
                ∅
            else
                { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k) ∨ (q' = j)) }
        else
            { q' | q' ∈ (A.step q c) ∧ ((q' ≤ k)) }
    : εNFA alphabet ℕ
}

def is_trim (A' : εNFA alphabet ℕ) (i' j' k' : ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = to_trim A i' j' k'

lemma singular_finite_accepts_iff_trim_accepts (A A': εNFA alphabet ℕ) (s a n: ℕ)
(hAsingular: is_singular A) (hAfinite: A.is_finite_automata)
(hn_max: A.max_reachable_node n) (hs_start: is_alone_in_set A.start s) (ha_accept: is_alone_in_set A.accept a)
(hA'istrim: A' = to_trim A s a n):
    A.accepts = A'.accepts := by sorry

def character_list_to_regex : List alphabet → RegularExpression alphabet
    | .nil => 0
    | .cons head tail => (RegularExpression.char head) + (character_list_to_regex tail)

noncomputable
def regex_for_path_from_i_to_j_through_k (A : εNFA alphabet ℕ) (i j k : ℕ) :
    RegularExpression alphabet :=
    if k = 0 then
        let character_set: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
        let characters := character_set.toList
        if i = j then
            1 + character_list_to_regex characters
        else
            character_list_to_regex characters
    else
        let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k-1)
        let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k-1)
        let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k-1)
        let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k-1)

        rᵢⱼ + (rᵢₖ * rₖₖ.star * rₖⱼ)

termination_by k
decreasing_by
    all_goals omega

lemma regex_is_path (A : εNFA alphabet ℕ) (i j k : ℕ) (r: RegularExpression alphabet) (hr: r = regex_for_path_from_i_to_j_through_k A i j k) :
    ∀(x : List alphabet), ((x ∈ r.matches') ↔ (∃(x': List ((Option alphabet))), (x'.reduceOption = x) ∧ ((to_trim A i j k).IsPath i j x'))) := by
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
            --rfl
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
