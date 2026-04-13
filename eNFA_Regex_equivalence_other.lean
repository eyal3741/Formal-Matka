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

--TODO: eliminate ==

lemma dont_go_nowhere (A : εNFA alphabet ℕ) (hAempty : A.start = ∅) : A.accepts = 0 := by
    simp [Language.zero_def]
    rw [Set.eq_empty_iff_forall_notMem] at hAempty ⊢
    intro x
    by_contra!
    obtain ⟨ s₁, _, _, h_s₁, _⟩ := A.mem_accepts_iff_exists_path.mp this
    simp [hAempty] at h_s₁ -- contradiction


def to_singular (A : εNFA alphabet ℕ) : εNFA alphabet ℕ := {
    start  := { 2 }
    accept := { 4 }
    step   := fun q c =>
        if q % 2 == 1 then
            if q ∈ (εNFA.to_1mod2 A).accept && c == none then
                    (εNFA.to_1mod2 A).step q c ∪ { 4 }
            else
                (εNFA.to_1mod2 A).step q c
        else
            if q == 2 && c == none then
                (εNFA.to_1mod2 A).start
            else
                ∅
    : εNFA alphabet ℕ
}

def is_alone_in_set (set: Set ℕ) (n: ℕ):= set = { n }
def is_singular (A : εNFA alphabet ℕ) :=
    (∃s: ℕ, is_alone_in_set A.start s) ∧ (∃a: ℕ, is_alone_in_set A.accept a)

lemma accepts_iff_singular_accepts (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_singular A) :
    A.accepts = A'.accepts := by
    rw [@Language.ext_iff]
    intro x
    rw [hA']
    constructor
    case mp =>
        intro hx
        rw[@εNFA.mem_accepts_iff_exists_path]
        use 2
        use 4
        rw[@εNFA.mem_accepts_iff_exists_path] at hx
        obtain ⟨ s, a, x', hs, ha, hx', hApath⟩ := hx
        use ([none] ++ x' ++ [none])

        subst hA' hx'
        refine ⟨ rfl, rfl, ?_, ?_ ⟩

        simp_all only [List.cons_append, List.nil_append, List.reduceOption_cons_of_none, List.reduceOption_append]
        simp [List.reduceOption_nil, List.append_nil]

        have hfirst: (to_singular A).IsPath 2 (2*s + 1) [none] := by
            simp_all only [εNFA.isPath_singleton]
            unfold to_singular
            simp_all only [Nat.mod_self, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_self]
            unfold εNFA.to_1mod2
            simp_all only [mem_setOf_eq, Nat.add_right_cancel_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
              exists_eq_right]

        have hlast: (to_singular A).IsPath (2*a + 1) 4 [none] := by
            simp_all only [εNFA.isPath_singleton]
            unfold to_singular
            simp_all only [Nat.mul_add_mod_self_left, Nat.mod_succ, BEq.rfl, ↓reduceIte, Bool.and_true,
              decide_eq_true_eq, union_singleton]
            split
            next h => simp_all only [mem_insert_iff, true_or]
            next h =>
                absurd h
                unfold εNFA.to_1mod2
                simp_all only [mem_setOf_eq, Nat.add_right_cancel_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
                  or_false, exists_eq_right]

        have hmiddle: (to_singular A).IsPath (2*s + 1) (2*a + 1) x' := by
            have hcontains : (to_singular A).contains A.to_1mod2 := by
                unfold εNFA.contains
                intro q σ
                simp [to_singular, εNFA.to_1mod2]
                split_ifs
                all_goals simp only [subset_insert, subset_refl, empty_subset]

            apply εNFA.path_if_contains at hcontains
            have h_A_0mod2_path := (A.path_iff_1mod2_path A.to_1mod2 s a (2*s + 1) (2*a + 1) x' rfl rfl rfl).mp hApath
            exact hcontains (2*s + 1) (2*a + 1) x' h_A_0mod2_path

        apply (to_singular A).isPath_append.mpr; use (2*a + 1)
        refine ⟨ ?_, hlast ⟩

        apply (to_singular A).isPath_append.mpr; use (2*s + 1)

    case mpr =>
        sorry

def max_reachable_node_n (A : εNFA alphabet ℕ) (n : ℕ) :=
    (∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n x)
    ∧
    ∀n': ℕ, (n' > n) → ¬(∃s₁: ℕ, ∃x: List (Option alphabet), s₁ ∈ A.start ∧ A.IsPath s₁ n' x)

def is_finite_automata (A : εNFA alphabet ℕ) :=
    (A.start = ∅) ∨ (A.start ≠ ∅ ∧ (∃n: ℕ, max_reachable_node_n A n))

lemma finite_iff_to_singular_finite (A : εNFA alphabet ℕ) (A' : εNFA alphabet ℕ) (hA': A' = to_singular A):
    is_finite_automata A ↔ is_finite_automata A' := by sorry

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

lemma singular_finite_accepts_iff_trim_accepts (A A': εNFA alphabet ℕ) (s a n: ℕ)
(hAsingular: is_singular A) (hAfinite: is_finite_automata A)
(hn_max: max_reachable_node_n A n) (hs_start: is_alone_in_set A.start s) (ha_accept: is_alone_in_set A.accept a)
(hA'istrim: A' = to_trim A s a n):
    A.accepts = A'.accepts := by sorry


def letters_to_or_regex (Letters: Finset alphabet): RegularExpression alphabet :=
    let f := fun (σ: alphabet) => RegularExpression.char σ
    let op := fun (a b : RegularExpression alphabet) => (a + b)
    --Letters.fold (Std.Commutative op) RegularExpression.epsilon f
    sorry


def regex_for_path_from_i_to_j_through_k (A : εNFA alphabet ℕ) (i j k : ℕ) :
    RegularExpression alphabet :=
    if k = 0 then
        --let Letters: Fintype alphabet := { σ |  j ∈ A.step i (some σ) }
        if i = j then
            0 --1 + letters_to_or_regex Letters
            ---{ x | ∃ S ∈ M.accept, ∃ (L : List (RegularExpression α)),
            ---(regex_comp L).rmatch x ∧ S ∈ M.eval L }
        else
            0 --letters_to_or_regex Letters
    else
        let r₁ := regex_for_path_from_i_to_j_through_k A i j (k-1)
        let r₂ := regex_for_path_from_i_to_j_through_k A i k (k-1)
        let r₃ := regex_for_path_from_i_to_j_through_k A k k (k-1)
        let r₄ := regex_for_path_from_i_to_j_through_k A k j (k-1)

        r₁ + (r₂ * r₃.star * r₄)

termination_by k
decreasing_by
    all_goals omega

lemma regex_is_path (A : εNFA alphabet ℕ) (i j k : ℕ) (r: RegularExpression alphabet) (hr: r = regex_for_path_from_i_to_j_through_k A i j k) :
    ∀(x : List alphabet), ((x ∈ r.matches') ↔ (∃(x': List ((Option alphabet))), (x'.reduceOption = x) ∧ ((to_trim A i j k).IsPath i j x'))) := by
    sorry

theorem εNFA_to_Regex (A: εNFA alphabet ℕ) : is_finite_automata A → (∃ (r: RegularExpression alphabet), r.matches' = A.accepts) := by
    let A' := to_singular A
    have hA'tosinA: A' = to_singular A := by
        simp_all only [A']
    rw [accepts_iff_singular_accepts A A']
    swap
    simp_all only [A']
    rw [finite_iff_to_singular_finite A A' hA'tosinA]

    rw [is_finite_automata]
    rintro ( hnill | ⟨ hAStartNotEmpty, n, hnmax ⟩ )
    case inl =>
        use 0
        simp only [dont_go_nowhere A' hnill, RegularExpression.matches']
    case inr =>
        have hA'singular: is_singular A' := by
            simp_all only [ne_eq, A']
            unfold to_singular
            unfold is_singular
            constructor
            use 2 --todo: fix if to_singular changes
            exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
            use 4 --todo: fix if to_singular changes
            exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
        unfold is_singular at hA'singular
        obtain ⟨ s, hs ⟩ := hA'singular.left
        obtain ⟨ a, ha ⟩ := hA'singular.right
        let A'' := to_trim A' s a n
        have histrim: A'' = to_trim A' s a n := by
            simp_all only [ne_eq, A', A'']
        have hA'finite: is_finite_automata A' := by
            rw [is_finite_automata]
            right
            constructor
            · exact hAStartNotEmpty
            · use n
        rw [singular_finite_accepts_iff_trim_accepts
        A' A'' s a n
        hA'singular hA'finite
        hnmax hs ha
        histrim]
        let r' := regex_for_path_from_i_to_j_through_k A'' s a n
        have hr: r' = regex_for_path_from_i_to_j_through_k A s a n := by
            simp_all only [ne_eq, A', A'', r']
            obtain ⟨left, right⟩ := hA'singular
            obtain ⟨w, h⟩ := left
            obtain ⟨w_1, h_1⟩ := right

            rfl
        have hgs: A''.start = {s} := by
            simp_all only [ne_eq, A', A'', r']
            obtain ⟨left, right⟩ := hA'singular
            obtain ⟨w, h⟩ := left
            obtain ⟨w_1, h_1⟩ := right
            rfl
        have hga: A''.accept = {a} := by
            simp_all only [ne_eq, A', A'', r']
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
            simp_all only [ne_eq, mem_singleton_iff, A', A''] --todo: is simp_all allowed?
