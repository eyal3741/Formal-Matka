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

set_option linter.unusedSectionVars false

namespace εNFA

def to_0mod2_εNFA (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 2*q' | q' ∈ A.start  }
    accept := { 2*q' | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 0 then
            {2*q' | q' ∈ (A.step (q/2) c) }
        else
            ∅
    : εNFA alphabet ℕ
}

def to_1mod2_εNFA (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 2*q' + 1 | q' ∈ A.start  }
    accept := { 2*q' + 1 | q' ∈ A.accept }
    step   := fun q c =>
        if q % 2 == 1 then
            {2*q' + 1 | q' ∈ (A.step ((q - 1)/2) c) }
        else
            ∅
    : εNFA alphabet ℕ
}

def is_0mod2_εNFA (A' : εNFA alphabet ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = A.to_0mod2_εNFA

def is_1mod2_εNFA (A' : εNFA alphabet ℕ) :=
    ∃ (A : εNFA alphabet ℕ), A' = A.to_1mod2_εNFA

def contains (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :=
    ∀ (q : ℕ), ∀ (σ: Option alphabet), A'.step q σ ⊆ A.step q σ


lemma reduced_option_append (c : Option alphabet) (tail : List (Option alphabet)) :
    ([c] ++ tail).reduceOption = [c].reduceOption ++ tail.reduceOption := by
    exact List.reduceOption_append [c] tail

lemma reduced_option_of_none (c : Option alphabet): c = none → [c].reduceOption = [] := by
    intro h_c
    simp [h_c]

lemma path_if_contains (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    A.contains A' → ∀ (q₁ q₂ : ℕ), ∀ (x : List (Option alphabet)), A'.IsPath q₁ q₂ x → A.IsPath q₁ q₂ x := by
    intro h_contains q₁ q₂ x h_path
    unfold εNFA.contains at h_contains
    induction h_path with
    | nil q => exact (εNFA.isPath_nil A).mpr rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        constructor
        · exact mem_preimage.mp (h_contains q₁ c h_step)
        · exact h_induction

lemma if_0mod2_step_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2_εNFA) (q₁ : ℕ) (q₂ : ℕ) (σ : Option alphabet) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro hmem
    obtain ⟨ A, hA ⟩ := hA'
    subst hA
    by_cases h : q₁ % 2 = 0
    case pos =>
        have : q₂ ∈ {2*q' | q' ∈ A.step (q₁ / 2) σ} := by
            simpa [to_0mod2_εNFA, h] using hmem
        rcases this with ⟨q', _, rfl⟩
        have h2 : (2 * q') % 2 = 0 :=
            Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')
        simp [h, h2]
    case neg =>
        have : q₂ ∈ (∅ : Set ℕ) := by
            simp [to_0mod2_εNFA, h] at hmem
        simp at this

lemma if_1mod2_step_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2_εNFA) (q₁ : ℕ) (q₂ : ℕ) (σ : Option alphabet) :
    (q₂ ∈ A'.step q₁ σ) → (q₁ % 2 = q₂ % 2) := by
    intro hmem
    obtain ⟨ A, hA ⟩ := hA'
    subst hA
    by_cases h : q₁ % 2 = 0
    case pos =>
        have : q₂ ∈ (∅ : Set ℕ) := by
            simp [to_1mod2_εNFA, h] at hmem
        simp at this
    case neg =>
        have : q₂ ∈ {2*q' + 1 | q' ∈ A.step ((q₁ - 1) / 2) σ} := by
            simp [to_1mod2_εNFA] at hmem
            obtain ⟨ _, ⟨ q', hmem ⟩ ⟩ := hmem
            simp only [mem_setOf_eq]
            use q'
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

lemma if_0mod2_path_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2_εNFA) (q₁ : ℕ) (q₂ : ℕ) (x : List (Option alphabet)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro hpath
    have ⟨ A, hA ⟩ := hA'
    subst hA
    induction hpath with
    | nil s =>
        simp only
    | cons t s u a x hstep hrest ih =>
        have hst : s % 2 = t % 2 := by
            exact if_0mod2_step_is_0mod2 A.to_0mod2_εNFA hA' s t a hstep
        exact Eq.trans hst ih


lemma if_1mod2_path_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2_εNFA) (q₁ : ℕ) (q₂ : ℕ) (x : List (Option alphabet)) :
    (A'.IsPath q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro hpath
    have ⟨ A, hA ⟩ := hA'
    subst hA
    induction hpath with
    | nil s =>
        simp only
    | cons t s u a x hstep hrest ih =>
        have hst : s % 2 = t % 2 := by
            exact if_1mod2_step_is_1mod2 A.to_1mod2_εNFA hA' s t a hstep
        exact Eq.trans hst ih

lemma if_0mod2_qs_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2_εNFA) (q : ℕ) :
    q ∈ A'.start → (q % 2 = 0) := by
    intro hq
    have ⟨ A, hA ⟩ := hA'
    subst hA
    simp [to_0mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')

lemma if_1mod2_qs_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2_εNFA)  (q : ℕ) :
    q ∈ A'.start → (q % 2 = 1) := by
    intro hq
    have ⟨ A, hA ⟩ := hA'
    subst hA
    simp [to_1mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    simp only [Nat.mul_add_mod_self_left, Nat.mod_succ]

lemma if_0mod2_qf_is_0mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_0mod2_εNFA) (q : ℕ) :
    q ∈ A'.accept → (q % 2 = 0) := by
    intro hq
    have ⟨ A, hA ⟩ := hA'
    subst hA
    simp [to_0mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 q')

lemma if_1mod2_qf_is_1mod2 (A' : εNFA alphabet ℕ) (hA': A'.is_1mod2_εNFA)  (q : ℕ) :
    q ∈ A'.accept → (q % 2 = 1) := by
    intro hq
    have ⟨ A, hA ⟩ := hA'
    subst hA
    simp [to_1mod2_εNFA] at hq
    rcases hq with ⟨q', _hq'inStart, rfl⟩
    simp only [Nat.mul_add_mod_self_left, Nat.mod_succ]

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
                    refine ⟨ ?_, rfl ⟩
                    unfold q'_mid
                    rw [hq'2]
                    rw [hq'2] at h_induction
                    apply h_induction
                    rfl
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
            case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
                subst hq1 hq2
                simp at h_induction
                rw [@εNFA.isPath_iff]
                right
                let q_mid := t / 2
                use q_mid, c, tail
                constructor
                case left =>
                    unfold q_mid
                    simp only [hmodzero, to_0mod2_εNFA] at h_step
                    split_ifs at h_step
                    case pos h_0mod2 =>
                        obtain ⟨ q', ⟨ hq', ht ⟩ ⟩ := h_step
                        subst ht
                        simp
                        exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hq'
                    case neg h_1mod2 => simp at h_step
                case right =>
                    refine ⟨ ?_, rfl ⟩
                    unfold q_mid
                    apply h_induction

        apply h_A'_path_A_path q_start q_accept
        rfl
        rfl
        exact h_ispath

lemma accepts_eq_1mod2_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) :
    (A' = to_1mod2_εNFA A) → A.accepts = A'.accepts := by
    sorry

def εNFA_zero : εNFA alphabet ℕ := {
    start  := ∅
    accept := ∅
    step   := fun _ _ => ∅
}


lemma Zero_Regex_to_εNFA :
    ∃ (A: εNFA alphabet ℕ), RegularExpression.zero.matches' = A.accepts := by
        let A : εNFA alphabet ℕ := εNFA_zero
        use A
        simp only [RegularExpression.zero_def, RegularExpression.matches'_zero, Language.zero_def, εNFA.accepts]
        simp only [mem_empty_iff_false, false_and, exists_false, setOf_false, A, εNFA_zero]

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
            exact ⟨ rfl, rfl, id (Eq.symm hx), (εNFA.isPath_nil A).mpr rfl ⟩

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩
            cases h_ispath
            case nil => exact id (Eq.symm h_x')
            case cons _ _ _ h_step _ =>
                exact False.elim h_step

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
            refine ⟨ rfl, rfl, ?_, ?_ ⟩
            · exact id (Eq.symm hx)
            · simp only [A, εNFA_char, and_self, ↓reduceIte, mem_singleton_iff]

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩

            cases h_ispath
            case nil =>
                subst h_x'
                simp_all only [mem_singleton_iff, zero_ne_one, A, εNFA_char]
            case cons t c tail _ h_step =>
                cases c
                case none h_none =>
                    absurd h_none
                    subst A
                    simp [εNFA_char]
                case some c h_some =>
                    by_cases c = σ
                    case neg h_σ' =>
                        absurd h_some
                        subst A
                        subst h_x'
                        simp_all only [εNFA_char, mem_singleton_iff, Option.some.injEq, and_false, ↓reduceIte,
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
                            simp [εNFA_char] at h_some
                            rw [h_some.right] at h_step
                            cases h_step
                            case cons t₂ h_t₂ _ =>
                                absurd h_t₂
                                subst A
                                simp only [εNFA_char, one_ne_zero, false_and, ↓reduceIte, mem_empty_iff_false,
                                  not_false_eq_true]

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

    let A₁' := A₁.to_0mod2_εNFA
    let A₂' := A₂.to_1mod2_εNFA
    have hA₁' : A₁'.is_0mod2_εNFA := by use A₁
    have hA₂' : A₂'.is_1mod2_εNFA := by use A₂

    let A : εNFA alphabet ℕ := εNFA_plus A₁' A₂'
    use A

    have h_A_contains_A₁' : A.contains A₁' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 0
        case pos h_0mod2 => simp [A, εNFA_plus, h_0mod2]
        case neg h_1mod2 => simp [A₁', to_0mod2_εNFA, h_1mod2]

    have h_A_contains_A₂' : A.contains A₂' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 1
        case pos h_1mod2 => simp [A, εNFA_plus, h_1mod2]
        case neg h_0mod2 => simp [A₂', to_1mod2_εNFA, h_0mod2]

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
                simp_rw [εNFA_plus, h_q₁_0mod2] at h_step
                exact if_0mod2_step_is_0mod2 A₁' hA₁' q₁ t c h_step
            case neg h_q₁_1mod2 =>
                simp_rw [εNFA_plus, h_q₁_1mod2] at h_step
                exact if_1mod2_step_is_1mod2 A₂' hA₂' q₁ t c h_step

    simp
    rw [hA₁, hA₂, @Language.add_def, @Language.ext_iff]
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
            refine ⟨ ?_, ?_, ?_, ?_ ⟩
            · exact mem_union_left A₂'.start h_s₁
            · exact mem_union_left A₂'.accept h_s₂
            · exact h_x'
            · exact path_if_contains A A₁' h_A_contains_A₁' s₁ s₂ x' h_A₁'_path

        case inr h_in_A₂ =>
            rw [accepts_eq_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_in_A₂
            rw [A.mem_accepts_iff_exists_path]
            obtain ⟨ s₁, s₂, x', h_s₁, h_s₂, h_x', h_A₂'_path ⟩ := h_in_A₂
            use s₁, s₂, x'
            refine ⟨ ?_, ?_, ?_, ?_ ⟩
            · exact mem_union_right A₁'.start h_s₁
            · exact mem_union_right A₁'.accept h_s₂
            · exact h_x'
            · exact path_if_contains A A₂' h_A_contains_A₂' s₁ s₂ x' h_A₂'_path

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
            ·   simp [A] at h_qs
                cases h_qs
                case inl h_in_A₁' => exact h_in_A₁'
                case inr h_in_A₂' =>
                    absurd h_qs_is_0mod2
                    simp
                    exact if_1mod2_qs_is_1mod2 A₂' hA₂' qs h_in_A₂'
            ·   by_cases (qf % 2) = 0
                case pos h_qf_is_0mod2 =>
                    simp [A] at h_qf
                    cases h_qf
                    case inl h_qf_in_A₁'_accept => exact h_qf_in_A₁'_accept
                    case inr h_qf_in_A₂'_accept =>
                        have : qf % 2 = 1 := by
                            exact if_1mod2_qf_is_1mod2 A₂' hA₂' qf h_qf_in_A₂'_accept
                        absurd this
                        simp [h_qf_is_0mod2]
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
                      simp_rw [εNFA_plus, h_q₁_0mod2] at h_step
                      simp at h_step
                      constructor
                      · exact h_step
                      · apply h_induction
                        have :  q₁ % 2 = t % 2 := by
                            exact if_0mod2_step_is_0mod2 A₁' hA₁' q₁ t c h_step
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
                exact if_0mod2_qs_is_0mod2 A₁' hA₁' qs h_in_A₁'
              case inr h_in_A₂' => exact h_in_A₂'
            · by_cases (qf % 2) = 1
              case pos h_qf_is_1mod2 =>
                  simp [A] at h_qf
                  cases h_qf
                  case inr h_qf_in_A₂'_accept => exact h_qf_in_A₂'_accept
                  case inl h_qf_in_A₁'_accept =>
                      have : qf % 2 = 0 := by
                          exact if_0mod2_qf_is_0mod2 A₁' hA₁' qf h_qf_in_A₁'_accept
                      absurd this
                      simp [h_qf_is_1mod2]
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
                      simp_rw [εNFA_plus, h_q₁_1mod2] at h_step
                      simp at h_step
                      constructor
                      · exact h_step
                      · apply h_induction
                        have : t % 2 = q₁ % 2 := by
                          exact Eq.symm (if_1mod2_step_is_1mod2 A₂' hA₂' q₁ t c h_step)
                        rw[h_q₁_1mod2] at this
                        exact this
              exact this qs qf x' h_qs_is_1mod2 h_A_path


-- -- -- -- -- COMP -- -- -- -- --
def εNFA_comp (A₁: εNFA alphabet ℕ) (A₂: εNFA alphabet ℕ) : εNFA alphabet ℕ := {
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
    (hA: A = εNFA_comp A₁' A₂') (_: A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA) (q₁ q : ℕ)  :
    ∀ (c : Option alphabet), q₁ % 2 = 1 → (q ∈ A.step q₁ c) → q % 2 = 1 := by
    rintro  c h_q₁_1mod2 h_q
    simp [hA, εNFA_comp, h_q₁_1mod2] at h_q
    have h_q₁_eq_q_mod2 := if_1mod2_step_is_1mod2 A₂' hA₂' (q₁ := q₁) (q₂ := q) c h_q
    simp [symm h_q₁_eq_q_mod2, h_q₁_1mod2]

lemma comp_path_1mod2_to_0mod2_is_empty (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA) (q₁ q₂ : ℕ):
    ∀ (x' : List (Option alphabet)), q₁ % 2 = 1 ∧ q₂ % 2 = 0 → ¬A.IsPath q₁ q₂ x' := by
    rintro x' ⟨ h_q₁, h_q₂ ⟩ h
    induction h with
    | nil => absurd h_q₁; simp; exact h_q₂
    | cons t q₁ q₂ c tail h_step h_path h_induction =>
        by_cases t % 2 = 0
        case pos h_t_0mod2 =>
            absurd h_t_0mod2
            simp
            exact comp_step_1mod2_to_1mod2 A A₁' A₂' hA hA₁' hA₂' q₁ t c h_q₁ h_step
        case neg h_t_1mod2 =>
            simp at h_t_1mod2
            simp [h_t_1mod2] at h_induction
            absurd h_induction
            exact Nat.mod_two_ne_one.mpr h_q₂

lemma comp_path_0mod2 (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA)
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 0 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option alphabet)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 0 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_1mod2
    have h_t_1mod2 : t % 2 = 1 := by exact Nat.mod_two_ne_zero.mp h_t_1mod2
    absurd h_path_t_q₂
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA hA₁' hA₂' t q₂ b' ⟨ h_t_1mod2, h_q₂ ⟩

lemma comp_path_0mod2_in_A₁' (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA)
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
            exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA hA₁' hA₂' t q₂ tail ⟨ h_t_1mod2, h_q₂ ⟩

lemma comp_path_1mod2 (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA)
    (q₁ q₂ : ℕ) (x' : List (Option alphabet)) :
    A.IsPath q₁ q₂ x' ∧ q₁ % 2 = 1 ∧ q₂ % 2 = 1 →
    ∀ (t : ℕ), ∀ (a' b' : List (Option alphabet)),
    (a' ++ b' = x') ∧ A.IsPath q₁ t a' ∧ A.IsPath t q₂ b' → t % 2 = 1 := by
    rintro ⟨ h_path_x', h_q₁, h_q₂ ⟩ t a' b' ⟨ h_a'b', h_path_q₁_t, h_path_t_q₂ ⟩
    by_contra! h_t_0mod2
    have h_t_0mod2 : t % 2 = 0 := by exact Nat.mod_two_ne_one.mp h_t_0mod2
    absurd h_path_q₁_t
    exact comp_path_1mod2_to_0mod2_is_empty A A₁' A₂' hA hA₁' hA₂' q₁ t a' ⟨ h_q₁, h_t_0mod2 ⟩

lemma comp_path_1mod2_in_A₂' (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (_: A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA)
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
            have h_t : q₁ % 2 = t % 2 := by
                exact if_1mod2_step_is_1mod2 A₂' hA₂' q₁ t c h_step
            simp [h_q₁, h_t_0mod2] at h_t

lemma comp_step_change_mod_implies_epsilon (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (_: A₂'.is_1mod2_εNFA)
    (q₁ q₂ : ℕ) (c : Option alphabet) :
    q₂ ∈ A.step q₁ c ∧ q₁ % 2 = 0 ∧ q₂ % 2 = 1 → c = none := by
    rintro ⟨ h_step, h_q₁, h_q₂ ⟩
    by_contra! h_c_some
    simp [hA, εNFA_comp, h_q₁] at h_step

    by_cases q₁ ∈ A₁'.accept
    case pos h =>
        simp [h, h_c_some] at h_step
        have : q₁ % 2 = q₂ % 2 := if_0mod2_step_is_0mod2 A₁' hA₁' q₁ q₂ c h_step
        simp [h_q₁, h_q₂] at this
    case neg h =>
        simp [h] at h_step
        have : q₁ % 2 = q₂ % 2 := if_0mod2_step_is_0mod2 A₁' hA₁' q₁ q₂ c h_step
        simp [h_q₁, h_q₂] at this

lemma comp_path_decomposition (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA) :
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
                -- TODO: SIMPLIFY THIS DISGUSTING MESS
                rw [h_y']
                simp [List.reduceOption_append] at h_tail
                have : (c :: tail).reduceOption = ([c] ++ tail).reduceOption := by exact List.toList_toArray
                rw [this, List.reduceOption_append]
                symm
                rw[List.reduceOption_append]
                simp
                rw [symm h_tail]
                have : [c].reduceOption ++ (a''.reduceOption ++ b'.reduceOption) =
                    ([c].reduceOption ++ a''.reduceOption) ++ b'.reduceOption := by
                    simp [List.append_assoc]
                rw [this]
                have : [c].reduceOption ++ a''.reduceOption = a'.reduceOption := by
                    subst a'
                    exact Eq.symm (reduced_option_append c a'')
                simp [this]

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
            have h_c_none : c = none :=
                comp_step_change_mod_implies_epsilon A A₁' A₂' hA hA₁' hA₂' qs t c ⟨ h_step, h_qs, h_t_1mod2 ⟩
            use qs, t, [c], tail
            refine ⟨ h_qs, h_t_1mod2, ?_, ?_, ?_, ?_ ⟩
            · rw [h_y']; exact List.toList_toArray
            · subst h_c_none
              simp [List.reduceOption_nil]
              tauto
            · exact A.mem_evalFrom_iff_exists_path.mpr ⟨ tail, rfl, h_path ⟩
            · rw [h_c_none] at h_step; exact h_step

lemma comp_word_decomposition (A A₁' A₂': εNFA alphabet ℕ)
    (hA: A = εNFA_comp A₁' A₂') (hA₁': A₁'.is_0mod2_εNFA) (hA₂': A₂'.is_1mod2_εNFA) (x : List alphabet) :
    (x ∈ A.accepts) → ∃ (a b : List alphabet), (x = a ++ b) ∧ (a ∈ A₁'.accepts) ∧ (b ∈ A₂'.accepts) := by
    intro h_x
    have ⟨ qs₁, qf₂, x', h_qs₁, h_qf₂, h_x', h_x'_path  ⟩ := A.mem_accepts_iff_exists_path.mp h_x
    simp [hA, εNFA_comp] at h_qs₁ h_qf₂
    have h_qs₁_0mod2 : qs₁ % 2 = 0 := if_0mod2_qs_is_0mod2 A₁' hA₁' qs₁ h_qs₁
    have h_qf₂_1mod2 : qf₂ % 2 = 1 := if_1mod2_qf_is_1mod2 A₂' hA₂' qf₂ h_qf₂

    have h_comp := comp_path_decomposition A A₁' A₂' hA hA₁' hA₂' qs₁ qf₂ x x' ⟨ h_qs₁_0mod2, h_qf₂_1mod2, symm h_x', h_x'_path ⟩
    obtain ⟨ qf₁, qs₂, a', b', h_qf₁, h_qs₂, h_a'b', h_eval_a', h_eval_b', h_step ⟩ := h_comp

    have h_qf₁_A₁'_accept : qf₁ ∈ A₁'.accept := by
        by_contra!
        simp [hA, εNFA_comp, this, h_qf₁] at h_step
        simp [if_0mod2_step_is_0mod2 A₁' hA₁' qf₁ qs₂ none h_step] at h_qf₁
        simp [h_qf₁] at h_qs₂

    have h_qs₂_A₂'_start : qs₂ ∈ A₂'.start := by
        simp [hA, εNFA_comp, h_qf₁, h_qf₁_A₁'_accept] at h_step
        by_cases qs₂ ∈ A₂'.start
        case pos h_start => exact h_start
        case neg h_no_start =>
            simp [h_no_start] at h_step
            simp [if_0mod2_step_is_0mod2 A₁' hA₁' qf₁ qs₂ none h_step, h_qs₂] at h_qf₁

    let a := a'.reduceOption
    let b := b'.reduceOption
    use a, b
    refine ⟨ ?_, ?_, ?_ ⟩
    · rw[Eq.symm h_a'b']
      subst a b
      exact List.reduceOption_append a' ([none] ++ b')
    · rw[A₁'.mem_accepts_iff_exists_path]
      obtain ⟨ w, ⟨ h_w, h_path_qs₁_qf₁ ⟩ ⟩ := A.mem_evalFrom_iff_exists_path.mp h_eval_a'
      use qs₁, qf₁, w
      have h_A₁'_path_w := comp_path_0mod2_in_A₁' A A₁' A₂' hA hA₁' hA₂' qs₁ qf₁ w  ⟨ h_path_qs₁_qf₁, h_qs₁_0mod2, h_qf₁ ⟩
      exact ⟨ h_qs₁, h_qf₁_A₁'_accept, h_w, h_A₁'_path_w ⟩
    · rw[A₂'.mem_accepts_iff_exists_path]
      obtain ⟨ w, ⟨ h_w, h_path_qs₂_qf₂ ⟩ ⟩ := A.mem_evalFrom_iff_exists_path.mp h_eval_b'
      use qs₂, qf₂, w
      have h_A₂'_path_w := comp_path_1mod2_in_A₂' A A₁' A₂' hA hA₁' hA₂' qs₂ qf₂ w ⟨ h_path_qs₂_qf₂, h_qs₂, h_qf₂_1mod2⟩
      exact ⟨ h_qs₂_A₂'_start, h_qf₂, h_w, h_A₂'_path_w ⟩

lemma Comp_Regex_to_εNFA (r₁ r₂ : RegularExpression alphabet) :
     (∃ (A₁: εNFA alphabet ℕ), r₁.matches' = A₁.accepts) →
     (∃ (A₂: εNFA alphabet ℕ), r₂.matches' = A₂.accepts) →
     ∃ (A: εNFA alphabet ℕ), (r₁.comp r₂).matches' = A.accepts := by
    intro h_r₁ h_r₂
    obtain ⟨ A₁, hA₁ ⟩ := h_r₁
    obtain ⟨ A₂, hA₂ ⟩ := h_r₂

    let A₁' := to_0mod2_εNFA A₁
    let A₂' := to_1mod2_εNFA A₂

    have hA₁' : A₁'.is_0mod2_εNFA := by use A₁
    have hA₂' : A₂'.is_1mod2_εNFA := by use A₂

    let A : εNFA alphabet ℕ := εNFA_comp A₁' A₂'
    use A

    have h_A_contains_A₁' : A.contains A₁' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 0
        case pos h_0mod2 =>
            simp [A, εNFA_comp, h_0mod2]
            split_ifs <;>
            simp only [subset_union_left, subset_refl]
        case neg h_1mod2 => simp [A₁', to_0mod2_εNFA, h_1mod2]

    have h_A_contains_A₂' : A.contains A₂' := by
        unfold εNFA.contains
        intro q σ
        by_cases q % 2 = 1
        case pos h_1mod2 => simp [A, εNFA_comp, h_1mod2]
        case neg h_0mod2 => simp [A₂', to_1mod2_εNFA, h_0mod2]

    simp
    rw [hA₁, hA₂, @Language.mul_def, @Language.ext_iff]
    intro x
    constructor
    case mp =>
        intro h_in_image
        rw[image2] at h_in_image
        obtain ⟨ x₁, h_x₁, x₂, h_x₂, h_comp ⟩ := h_in_image
        rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, A₁'.mem_accepts_iff_exists_path] at h_x₁
        rw [accepts_eq_1mod2_accepts A₂ A₂' rfl, A₂'.mem_accepts_iff_exists_path] at h_x₂
        obtain ⟨ qs₁, qf₁, x₁', h_qs₁, h_qf₁, h_x₁', h_ispath1 ⟩ := h_x₁
        obtain ⟨ qs₂, qf₂, x₂', h_qs₂, h_qf₂, h_x₂', h_ispath2 ⟩ := h_x₂
        rw [A.mem_accepts_iff_exists_path]
        use qs₁, qf₂, (x₁' ++ ([none] ++ x₂'))
        refine ⟨ h_qs₁, h_qf₂, ?_, ?_ ⟩
        · rw [Eq.symm h_comp]
          subst h_x₁' h_x₂'
          exact List.reduceOption_append x₁' ([none] ++ x₂')
        · rw [isPath_append]
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

    case mpr =>
        intro h_in_A
        rw[image2]
        rw [accepts_eq_0mod2_accepts A₁ A₁' rfl, accepts_eq_1mod2_accepts A₂ A₂' rfl]
        obtain ⟨ a, b, h_ab, h_a_accept, h_b_accept ⟩ := comp_word_decomposition A A₁' A₂' rfl hA₁' hA₂' x h_in_A
        rw [A.mem_accepts_iff_exists_path] at h_in_A
        obtain ⟨ qs₁, qf₂, x', h_qs₁, h_qf₂, h_x', h_ispath ⟩ := h_in_A

        exact ⟨ a, h_a_accept, b, h_b_accept, Eq.symm h_ab ⟩

def εNFA_kstar (A: εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := A.start ∪ {1}
    accept := A.accept ∪ {1}
    step   := fun q c =>
        if q ∈ A.accept ∪ {1} ∧ c = none then
            A.step q c ∪ A.start ∪ {1}
        else
            A.step q c
}

lemma kstar_append (A A' : εNFA alphabet ℕ) (y y₁ y₂ : List alphabet) (hA: A = εNFA_kstar A') (hy: y = y₁ ++ y₂) :
    (y₁ ∈ A.accepts) ∧ (y₂ ∈ A.accepts) → y ∈ A.accepts := by
    intro ⟨ h_y₁_acc, h_y₂_acc ⟩
    rw[mem_accepts_iff_exists_path]
    rw[mem_accepts_iff_exists_path] at h_y₁_acc h_y₂_acc
    obtain ⟨ qs₁, qf₁, y₁', h_qs₁, h_qf₁, h_y₁', h_y₁_path ⟩ := h_y₁_acc
    obtain ⟨ qs₂, qf₂, y₂', h_qs₂, h_qf₂, h_y₂', h_y₂_path ⟩ := h_y₂_acc
    let y' := y₁' ++ ([none] ++ y₂')
    use qs₁, qf₂, y'

    have h_y' : y'.reduceOption = y := by
        subst h_y₁' h_y₂' hy y'
        exact List.reduceOption_append y₁' ([none] ++ y₂')

    have h_connect : A.IsPath qf₁ qs₂ [none] := by
        simp
        simp[hA, εNFA_kstar] at h_qf₁
        simp[hA, εNFA_kstar] at h_qs₂

        cases h_qs₂
        case inl h_qs₂ =>
            subst qs₂
            simp [hA, εNFA_kstar, h_qf₁]
        case inr h_qs₂ =>
            simp [hA, εNFA_kstar, h_qf₁]
            right; right
            exact h_qs₂

    have h_full_path : A.IsPath qs₁ qf₂ y' := by
        rw [A.isPath_append]
        use qf₁
        constructor
        case left => exact h_y₁_path
        case right => rw [A.isPath_append]; use qs₂

    exact ⟨ h_qs₁, h_qf₂, h_y', h_full_path ⟩

lemma Star_Regex_to_εNFA (r : RegularExpression alphabet) :
    (∃ (Ar: εNFA alphabet ℕ), r.matches' = Ar.accepts) →
    ∃ (A: εNFA alphabet ℕ), (r.star).matches' = A.accepts := by
    intro h_r
    obtain ⟨ Ar, hAr ⟩ := h_r
    let A' := Ar.to_0mod2_εNFA
    let A : εNFA alphabet ℕ := εNFA_kstar A'
    use A

    have h_contains: A.contains A' := by
        unfold εNFA.contains
        intro q σ
        simp[A, εNFA_kstar]
        rw [@insert_eq, @union_left_comm]
        split_ifs
        case pos => exact subset_union_left
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
            rw[mem_accepts_iff_exists_path]
            use 1, 1, []
            simp[A, εNFA_kstar]
        case cons head tail h_induction =>
            simp at h_y
            obtain ⟨ h_head, h_tail ⟩ := h_y
            have h_head : head ∈ A.accepts := by
                rw[mem_accepts_iff_exists_path] at h_head
                obtain ⟨ qs₁, qf₁, head', h_qs₁, h_qf₁, h_head', h_path ⟩ := h_head
                have h_qs₁: qs₁ ∈ A.start := by
                    simp[A, εNFA_kstar]
                    exact Or.symm (Or.intro_left (qs₁ = 1) h_qs₁)
                have h_qf₁: qf₁ ∈ A.accept := by
                    simp[A, εNFA_kstar]
                    exact Or.symm (Or.intro_left (qf₁ = 1) h_qf₁)
                rw[mem_accepts_iff_exists_path]
                use qs₁, qf₁, head'
                exact ⟨ h_qs₁, h_qf₁, h_head',  path_if_contains A A' h_contains qs₁ qf₁ head' h_path ⟩
            apply h_induction at h_tail
            exact kstar_append A A' (head :: tail).flatten head tail.flatten rfl rfl ⟨ h_head, h_tail⟩

    case mpr =>
        intro h_x
        induction x
        case nil => use []; simp
        case cons c tail h_induction =>

        rw[mem_accepts_iff_exists_path] at h_x
        obtain ⟨ qs, qf, x', h_qs, h_qf, h_x, h_path ⟩ := h_x

        induction x
        case nil => use []; simp
        case cons c tail h_induction =>
        have : (q₁ q₂ : ℕ) → (x' : List (Option alphabet)) → ∃ (t : ℕ), A.IsPath q₁ t
        induction' h_path
        case nil =>
            use []
            subst h_x
            simp
        case cons _ _ t q₁ q₂ c tail h_step h_path h_induction =>
            sorry

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
