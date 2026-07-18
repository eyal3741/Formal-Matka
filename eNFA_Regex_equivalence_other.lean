import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

import eNFA_Regex_Equivalence.Basic

open Set Classical

universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

--------------------------
-- THE OTHER DIRECTION: --
--------------------------

variable {α : Type u} [Fintype α] [DecidableEq α]
open εNFA

def character_list_to_regex : List α → RegularExpression α
    | .nil => 0
    | .cons head tail => (RegularExpression.char head) + (character_list_to_regex tail)

lemma character_list_regex_accepts_characters (characters : List α) (r: RegularExpression α)
    (hr: r = character_list_to_regex characters) (x : List α):
    x ∈ r.matches' ↔ ∃ (σ : α), σ ∈ characters ∧ x = [σ] := by
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
def regex_for_path_from_i_to_j_through_k (A : εNFA α ℕ) (i j k : ℕ) :
    RegularExpression α :=
    if k = 0 then
        let character_set_ij: Finset α := { σ |  j ∈ A.step i (some σ) }
        let characters_ij := character_set_ij.toList

        if i = j ∨ j ∈ A.step i none then
            1 + character_list_to_regex characters_ij
        else
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

lemma path_start_mem_supp
    (A : εNFA α ℕ) (s u : ℕ) (x : List (Option α))
    (p : A.Path s u x) :
    x = [] ∨ s ∈ p.supp := by
        cases p with
        | nil => left; rfl
        | cons t s u c tail h_step h_rest =>
            right
            simp [εNFA.Path.supp]

lemma not_none_is_some (c : Option α):
    c ≠ none → ∃ (σ : α), c = some σ := by
    intro h_not_none
    cases c
    case none => contradiction
    case some σ => use σ

lemma list_map_of_reduce_option (L' : List (List (Option α))) :
    L'.flatten.reduceOption = (List.map (fun x' ↦ x'.reduceOption) L').flatten := by
    induction L'
    case nil => simp
    case cons head tail h_induction =>
        simp [List.reduceOption_append]
        exact h_induction

lemma supp_of_nil (A : εNFA α ℕ) (s t : ℕ) (path: A.Path s t []) : path.supp = ∅ := by
    cases path
    simp

lemma supp_of_singleton (A : εNFA α ℕ) (s t : ℕ) (c: (Option α)) (path: A.Path s t [c]) : path.supp = {s} := by
    cases path
    next cons t' h_step path' =>
    have : path'.supp = ∅ := supp_of_nil A t' t path'
    simp [this]

structure path_split (A : εNFA α ℕ) (qs qf t : ℕ) (word_qs_qf: List (Option α)) (path_qs_qf: A.Path qs qf word_qs_qf) where
  word_qs_t : List (Option α)
  word_t_qf : List (Option α)
  path_qs_t : A.Path qs t word_qs_t
  path_t_qf : A.Path t qf word_t_qf
  h_word_qs_qf : word_qs_qf = word_qs_t ++ word_t_qf
  h_path_qs_qf : path_qs_qf = h_word_qs_qf▸(path_qs_t ++ path_t_qf)
  h_t : t ∉ path_qs_t.supp

lemma path_split_at_state (A : εNFA α ℕ) (qs qf t : ℕ) (x': List (Option α)) (path_qs_qf: A.Path qs qf x') :
    t ∈ path_qs_qf.supp → qs = t ∨
    ∃ (_ : path_split A qs qf t x' path_qs_qf), True := by

    intro h_t_in_path_qs_qf
    induction path_qs_qf
    case nil s =>
        simp at h_t_in_path_qs_qf
    case cons s qs qf c tail h_step path_s_qf h_induction =>
        by_cases t = qs
        case pos h => left; exact symm h
        case neg h_qs_neq_t =>
            right
            have := A.isPath_singleton.mpr h_step
            obtain ⟨ path_qs_s ⟩ := this
            by_cases t = s
            case pos h =>
                clear h_induction
                symm at h
                subst h
                use {
                    word_qs_t := [c]
                    word_t_qf := tail
                    path_qs_t := path_qs_s
                    path_t_qf := path_s_qf
                    h_word_qs_qf := by simp only [List.cons_append, List.nil_append]
                    h_path_qs_qf := (by
                        simp
                        cases path_qs_s
                        case cons t h_step path_t_s =>
                            cases path_t_s
                            case nil => simp
                    )
                    h_t := (by
                        cases path_qs_s
                        case cons t h_step path_t_s =>
                            cases path_t_s
                            case nil => simp [h_qs_neq_t]
                    )
                }

            case neg h_s_neq_t =>
                simp[h_qs_neq_t] at h_t_in_path_qs_qf
                replace h_induction := h_induction h_t_in_path_qs_qf
                cases h_induction
                case inl h => simp [symm h] at h_s_neq_t
                case inr h_induction =>
                    obtain ⟨ p ⟩ := h_induction
                    obtain ⟨ y', tail', path_s_t, path_t_qf, h_tail, heq_append, h_supp ⟩ := p
                    have h_word_qs_qf : c :: tail = [c] ++ y' ++ tail' := by
                        subst h_tail
                        simp only [List.cons_append, List.nil_append]
                    use {
                        word_qs_t := [c] ++ y'
                        word_t_qf := tail'
                        path_qs_t := Path.cons s qs t c y' h_step path_s_t
                        path_t_qf := path_t_qf
                        h_word_qs_qf := h_word_qs_qf
                        h_path_qs_qf := (by
                            subst tail
                            simp only [List.cons_append, List.nil_append]
                            subst path_s_qf
                            rfl
                        )
                        h_t := by simp [h_qs_neq_t, h_supp]
                    }

structure path_split_full (A : εNFA α ℕ) (i j k : ℕ) (word_ij: List (Option α)) (path_ij: A.Path i j word_ij) where
  word_ik : List (Option α)
  list_kk : List (List (Option α))
  word_kj : List (Option α)
  path_ik : A.Path i k word_ik
  path_kk : A.Path k k list_kk.flatten
  path_kj : A.Path k j word_kj
  h_paths_kk : ∀ word_kk ∈ list_kk, ∃ (path_kk : A.Path k k word_kk), k ∉ path_kk.suppAfterStart
  h_word_ij  : word_ij = word_ik ++ list_kk.flatten ++ word_kj
  h_path_ij  : path_ij = h_word_ij▸(path_ik ++ path_kk ++ path_kj)
  h_k_notin_ik : k ∉ path_ik.supp
  h_k_notin_kj : k ∉ path_kj.suppAfterStart

lemma path_multiple_split_at_state (A : εNFA α ℕ) (i j k : ℕ) (x': List (Option α)) (path_ij: A.Path i j x'):
    (k ∈ path_ij.supp) → ∃ (_ : path_split_full A i j k x' path_ij), True := by
    intro h_k_supp
    induction path_ij
    case nil => simp at h_k_supp
    case cons t i j c tail h_step path_tj h_induction =>
        simp at h_k_supp
        cases h_k_supp
        case inl h_ik =>
            subst i
            by_cases hk_tail : k ∈ path_tj.supp

            case neg =>
                have path_nil : A.Path k k [] := Path.nil k

                use {
                    word_ik := []
                    list_kk := []
                    word_kj := c :: tail
                    path_ik := path_nil
                    path_kk := path_nil
                    path_kj := Path.cons t k j c tail h_step path_tj
                    h_paths_kk := by simp
                    h_word_ij  := by simp
                    h_path_ij  := by cases path_nil; rfl
                    h_k_notin_ik := by cases path_nil; simp
                    h_k_notin_kj := by simpa [Path.suppAfterStart] using hk_tail
                }

            case pos =>
                obtain ⟨p, _⟩ := h_induction hk_tail
                obtain ⟨
                    word_tk, list_kk, word_kj,
                    path_tk, path_kk, path_kj,
                    h_paths_kk, h_word, h_path,
                    h_notin_tk, h_notin_kj
                ⟩ := p

                have path_nil : A.Path k k [] := Path.nil k

                let path_k_to_k : A.Path k k ([c] ++ word_tk) :=
                    Path.cons t k k c word_tk h_step path_tk

                use {
                    word_ik := []
                    list_kk := [[c] ++ word_tk].append list_kk
                    word_kj := word_kj
                    path_ik := path_nil
                    path_kk := (path_k_to_k ++ path_kk)
                    path_kj := path_kj
                    h_paths_kk := (by
                        simp at ⊢ path_k_to_k
                        refine ⟨ ?_, h_paths_kk ⟩
                        use path_k_to_k
                        subst path_k_to_k
                        simp [Path.suppAfterStart]
                        exact h_notin_tk
                    )
                    h_word_ij := (by
                        subst tail
                        simp [List.append_assoc]
                    )
                    h_path_ij := (by
                        subst tail
                        subst path_tj
                        cases path_nil
                        rfl
                    )
                    h_k_notin_ik := (by
                        cases path_nil
                        simp
                    )
                    h_k_notin_kj := h_notin_kj
                }
        case inr h_k_supp =>
            replace h_induction := h_induction h_k_supp
            obtain ⟨ p, _ ⟩ := h_induction
            obtain ⟨
                word_tk, list_kk, word_kj,
                path_tk, path_kk, path_kj,
                h_paths_kk, h_word, h_path,
                h_notin_tk, h_notin_kj
            ⟩ := p

            by_cases h_ik : k = i
            case pos =>
                subst i

                have path_ik : A.Path k k [] := Path.nil k
                let path_k_to_k : A.Path k k ([c] ++ word_tk) :=
                    Path.cons t k k c word_tk h_step path_tk

                use {
                    word_ik := []
                    list_kk := [[c] ++ word_tk].append list_kk
                    word_kj := word_kj
                    path_ik := path_ik
                    path_kk := (Path.cons t k k c word_tk h_step path_tk) ++ path_kk
                    path_kj := path_kj
                    h_paths_kk := (by
                        simp at ⊢ path_k_to_k
                        refine ⟨ ?_, h_paths_kk ⟩
                        use path_k_to_k
                        subst path_k_to_k
                        simp [Path.suppAfterStart]
                        exact h_notin_tk
                    )
                    h_word_ij := by
                        subst tail
                        simp [List.append_assoc]
                    h_path_ij := by
                        subst tail
                        subst path_tj
                        cases path_ik
                        rfl
                    h_k_notin_ik := by
                        cases path_ik
                        simp
                    h_k_notin_kj := h_notin_kj
                }
            case neg =>
                use {
                    word_ik := [c] ++ word_tk
                    list_kk := list_kk
                    word_kj := word_kj
                    path_ik := Path.cons t i k c word_tk h_step path_tk
                    path_kk := path_kk
                    path_kj := path_kj
                    h_paths_kk := h_paths_kk
                    h_word_ij := (by
                        subst tail
                        simp [List.append_assoc]
                    )
                    h_path_ij := (by
                        subst tail
                        subst path_tj
                        rfl
                    )
                    h_k_notin_ik := by simp [h_ik, h_notin_tk]
                    h_k_notin_kj := h_notin_kj
                }

theorem regex_is_path (A : εNFA α ℕ) (i j k : ℕ) (r: RegularExpression α) (hr: r = regex_for_path_from_i_to_j_through_k A i j k)
    (h_zero_step: ∀ (σ : Option α), A.step 0 σ = ∅) (h_step_zero: ∀ (q : ℕ) (σ : Option α), 0 ∉ A.step q σ):
    ∀ (x : List α), ((x ∈ r.matches') ↔ (∃(x': List (Option α)), (x'.reduceOption = x) ∧
     ∃ (path_ij: A.Path i j x'), ∀ (k': ℕ), (k' ∈ path_ij.suppAfterStart → (k' ≤ k)))) := by
    intro x
    constructor
    case mp =>
        intro h_x_in_r
        unfold regex_for_path_from_i_to_j_through_k at hr
        split_ifs at hr
        case pos h_k_0 h_i_j =>
            subst h_k_0
            simp [hr] at h_x_in_r
            cases h_x_in_r
            case inl h_x_empty =>
                simp [Language.one_def] at h_x_empty
                cases h_i_j
                case inl h_i_eq_j =>
                    subst h_i_eq_j
                    use []
                    simp only [List.reduceOption_nil, h_x_empty, nonpos_iff_eq_zero, true_and]
                    obtain ⟨ path_ii ⟩ : Nonempty (A.Path i i []) := A.isPath_nil.mpr rfl
                    use path_ii
                    intro k' h_k'
                    cases path_ii
                    case nil => simp [Path.suppAfterStart] at h_k'
                case inr h_step =>
                    use [none]
                    simp only [List.reduceOption_cons_of_none, List.reduceOption_nil, h_x_empty, nonpos_iff_eq_zero, true_and]
                    obtain ⟨ path_ij ⟩ : Nonempty (A.Path i j [none]) := A.isPath_singleton.mpr h_step
                    use path_ij
                    intro k' h_k'
                    cases path_ij
                    case cons p =>
                        cases p
                        case nil => simp [Path.suppAfterStart] at h_k'
            case inr h_some =>
                let character_set: Finset α := { σ |  j ∈ A.step i (some σ) }
                let characters := character_set.toList
                obtain ⟨ σ, h_step, h_x_σ ⟩ := (character_list_regex_accepts_characters characters (character_list_to_regex characters) rfl x).mp h_some
                use [some σ]
                simp only [List.reduceOption_cons_of_some, List.reduceOption_nil, h_x_σ, nonpos_iff_eq_zero, true_and]
                subst characters character_set
                simp at h_step
                obtain ⟨ path_ij ⟩ : Nonempty (A.Path i j [some σ]) := A.isPath_singleton.mpr h_step
                use path_ij
                intro k' h_k'
                cases path_ij
                case cons p =>
                    cases p
                    case nil => simp [Path.suppAfterStart] at h_k'

        case neg h_k_0 h_i_neq_j =>
            let character_set: Finset α := { σ |  j ∈ A.step i (some σ) }
            let characters := character_set.toList
            subst hr
            obtain ⟨ σ, h_step, h_x_σ ⟩ :=
                (character_list_regex_accepts_characters characters
                 (character_list_to_regex characters) rfl x).mp h_x_in_r
            use [some σ]
            simp only [List.reduceOption_cons_of_some, List.reduceOption_nil, h_x_σ, true_and]
            subst characters character_set
            simp at h_step
            obtain ⟨ path_ij ⟩ : Nonempty (A.Path i j [some σ]) := A.isPath_singleton.mpr h_step
            use path_ij
            intro k' h_k'
            cases path_ij
            case cons p =>
                cases p
                case nil => simp [Path.suppAfterStart] at h_k'

        case neg h_k_neq_0 =>
            let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k - 1)
            let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k - 1)
            let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k - 1) -- later: handle kstar
            let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k - 1)

            simp [hr, Language.add_def] at h_x_in_r
            clear hr
            cases h_x_in_r
            case inl h_x_in_rᵢⱼ =>
                have h_induction := (regex_is_path A i j (k-1) rᵢⱼ rfl h_zero_step h_step_zero x).mp h_x_in_rᵢⱼ
                clear rᵢⱼ rᵢₖ rₖⱼ rₖₖ
                obtain ⟨ x', h_x', path_ij, h_k' ⟩ := h_induction

                use x'
                refine ⟨ h_x', ?_ ⟩
                use path_ij
                intro k' h_supp
                replace h_k' := h_k' k' h_supp
                omega
            case inr h_x_in_rᵢₖ_rₖₖ_rₖⱼ =>
                clear rᵢⱼ
                simp [Language.mul_def] at h_x_in_rᵢₖ_rₖₖ_rₖⱼ
                obtain ⟨ xᵢₖ, h_xᵢₖ, xₖₖ, h_xₖₖ, xₖⱼ, h_xₖⱼ, h_x ⟩ := h_x_in_rᵢₖ_rₖₖ_rₖⱼ
                obtain ⟨ xᵢₖ', h_xᵢₖ', h_path_ik ⟩ := (regex_is_path A i k (k-1) rᵢₖ rfl h_zero_step h_step_zero xᵢₖ).mp h_xᵢₖ
                obtain ⟨ xₖⱼ', h_xₖⱼ', h_path_kj ⟩ := (regex_is_path A k j (k-1) rₖⱼ rfl h_zero_step h_step_zero xₖⱼ).mp h_xₖⱼ
                clear rᵢₖ rₖⱼ h_xᵢₖ h_xₖⱼ

                simp [Language.kstar_def] at h_xₖₖ
                obtain ⟨ L, h_L, h_xₖₖ ⟩ := h_xₖₖ

                have h_path_L_kk : ∃ (L' : List (List (Option α))), L'.flatten.reduceOption = L.flatten ∧
                    (∀ x' ∈ L', ∃ (path_kk : A.Path k k x'), ∀ k' ∈ path_kk.suppAfterStart, k' ≤ k - 1) := by
                    clear h_L
                    induction L
                    case nil => use []; simp
                    case cons head tail h_induction =>
                        simp at h_xₖₖ
                        obtain ⟨ L'', h_L'', h_path_L'' ⟩ := h_induction h_xₖₖ.right
                        obtain ⟨ head', h_head', path_head', h_path_head' ⟩ := (regex_is_path A k k (k-1) rₖₖ rfl h_zero_step h_step_zero head).mp h_xₖₖ.left
                        use head' :: L''
                        simp only [List.flatten_cons, List.reduceOption_append, h_head', h_L'', List.mem_cons, forall_eq_or_imp, true_and]
                        constructor
                        case left => use path_head'
                        case right => exact h_path_L''
                clear rₖₖ h_xₖₖ

                obtain ⟨ L', h_L', h_path_kk ⟩ := h_path_L_kk

                let xₖₖ' := L'.flatten
                replace h_path_kk : ∃ (path_kk : A.Path k k xₖₖ'), ∀ k' ∈ path_kk.suppAfterStart, k' ≤ k := by
                    clear h_L h_L'
                    subst xₖₖ'
                    induction L'
                    case nil =>
                        obtain ⟨ path_kk ⟩ : Nonempty (A.Path k k []) := A.isPath_nil.mpr rfl
                        use path_kk
                        intro k' h_supp
                        simp [Path.suppAfterStart] at h_supp
                        split at h_supp
                        case h_1 => trivial
                        case h_2 => contradiction
                    case cons head tail h_induction =>
                        simp only [List.mem_cons, forall_eq_or_imp] at h_path_kk
                        replace h_induction := h_induction h_path_kk.right
                        obtain ⟨ path_kk_left,  h_path_kk_left  ⟩ := h_path_kk.left
                        obtain ⟨ path_kk_right, h_path_kk_right ⟩ := h_induction
                        use path_kk_left ++ path_kk_right

                        intro k' h_k'
                        simp at h_k'

                        have h_decEq : (instDecidableEqNat : DecidableEq ℕ) = Classical.decEq ℕ := by
                            apply Subsingleton.elim

                        have h_append := A.supp_after_start_of_path_append path_kk_left path_kk_right k'
                        rw [h_decEq] at h_k' h_path_kk_left

                        cases h_append h_k'
                        case inl h_k'_in_left =>
                            have := h_path_kk_left k' h_k'_in_left
                            omega
                        case inr h_k'_in_right =>
                            replace h_k'_in_right : k' = k ∨ k' ∈ path_kk_right.suppAfterStart := by
                                unfold εNFA.Path.supp at h_k'_in_right
                                split at h_k'_in_right
                                case h_1 => trivial
                                case h_2 =>
                                    simp at h_k'_in_right
                                    cases h_k'_in_right
                                    case inl h => left; exact h
                                    case inr h heq =>
                                        right
                                        unfold εNFA.Path.suppAfterStart
                                        split
                                        case h_1 => simp_all
                                        case h_2 =>
                                        sorry
                            cases h_k'_in_right
                            case inl => omega
                            case inr h => exact h_path_kk_right k' h

                use xᵢₖ' ++ xₖₖ' ++ xₖⱼ'
                simp [symm h_xᵢₖ', symm h_xₖⱼ'] at h_x

                have : xₖₖ'.reduceOption = L.flatten := by
                    subst h_L
                    simp_all only [xₖₖ']

                refine ⟨ (by simp_all [List.reduceOption_append]), ?_ ⟩

                obtain ⟨ path_ik, h_path_ik ⟩ := h_path_ik
                obtain ⟨ path_kk, h_path_kk ⟩ := h_path_kk
                obtain ⟨ path_kj, h_path_kj ⟩ := h_path_kj
                use path_ik ++ path_kk ++ path_kj
                intro k' h_k'
                cases path_ik
                case nil =>
                    cases path_kj
                    case nil => sorry
                    case cons => sorry
                case cons p =>
                    simp [Path.suppAfterStart] at h_k'
                    -- have := (supp_of_path_append p (path_kk ++ path_kj)).mp h_k'
                    -- TODO: Associativity of ++ for paths
                    sorry

    case mpr =>
        intro h
        obtain ⟨ x', h_x', h_path_ij ⟩ := h
        obtain ⟨ path_ij, h_k ⟩ := h_path_ij

        by_cases k ∈ path_ij.supp
        case pos h_k_in_supp =>
            unfold regex_for_path_from_i_to_j_through_k at hr
            split_ifs at hr
            case pos h_k_0 h_i_j =>
                subst h_k_0
                sorry
            case neg h_k_0 h =>
                sorry
            case neg h_k_neq_0 =>
                obtain ⟨ p, _ ⟩ := path_multiple_split_at_state A i j k x' path_ij h_k_in_supp
                obtain ⟨
                    word_ik, list_kk, word_kj,
                    path_ik, path_kk, path_kj,
                    h_paths_kk, h_word, h_path,
                    h_notin_ik, h_notin_kj
                ⟩ := p

                subst hr
                simp [Language.add_def]
                right
                simp [Language.mul_def]
                use word_ik.reduceOption
                refine ⟨ ?_, ?_ ⟩
                case refine_1 =>
                    exact (regex_is_path A i k (k - 1) (regex_for_path_from_i_to_j_through_k A i k (k - 1))
                        rfl h_zero_step h_step_zero word_ik.reduceOption).mpr ⟨ word_ik, rfl, path_ik, sorry ⟩

                use list_kk.flatten.reduceOption
                refine ⟨ ?_, ?_ ⟩
                case refine_1 =>
                    simp [Language.kstar_def]
                    use (List.map (fun x' ↦ x'.reduceOption) list_kk)
                    simp
                    refine ⟨ list_map_of_reduce_option list_kk , ?_ ⟩
                    intro word_kk h_word_kk
                    obtain ⟨ path_kk, h_path_kk ⟩ := h_paths_kk word_kk h_word_kk

                    exact (regex_is_path A k k (k - 1) (regex_for_path_from_i_to_j_through_k A k k (k - 1))
                        rfl h_zero_step h_step_zero word_kk.reduceOption).mpr ⟨ word_kk, rfl, path_kk, sorry ⟩

                use word_kj.reduceOption
                refine ⟨ ?_, ?_ ⟩
                case refine_1 =>
                    exact (regex_is_path A k j (k - 1) (regex_for_path_from_i_to_j_through_k A k j (k - 1))
                        rfl h_zero_step h_step_zero word_kj.reduceOption).mpr ⟨ word_kj, rfl, path_kj, sorry ⟩

                subst h_word
                simp [List.reduceOption_append] at h_x'
                exact h_x'

        case neg h_k_notin_supp =>
            subst hr
            unfold regex_for_path_from_i_to_j_through_k
            split_ifs
            case pos h_k_0 h_i_j =>
                cases h_i_j
                case inl h_i_j =>
                    subst h_i_j
                    have : x'.length ≤ 1 := by
                        by_contra!
                        cases path_ij
                        case nil => contradiction
                        case cons => sorry

                    simp [Language.add_def, Language.one_def]
                    by_cases x'.length = 0
                    case pos h_x'_0 =>
                        left
                        simp at h_x'_0
                        subst h_x'_0
                        simp at h_x'
                        exact h_x'
                    case neg h_x'_1 =>
                        replace h_x'_1 : x'.length = 1 := by omega
                        obtain ⟨ σ, h_σ ⟩ := x'.length_eq_one_iff.mp h_x'_1
                        cases σ
                        case none =>
                            left
                            subst h_σ
                            simp at h_x'
                            exact h_x'
                        case some c =>
                            right
                            cases path_ij
                            case nil => contradiction
                            case cons _ c' _ h_step p =>
                                simp at h_x'_1
                                subst h_x'_1
                                have := (A.isPath_nil.mp (by use p)).symm
                                simp at h_σ
                                subst this h_σ

                                let character_set: Finset α := { σ | i ∈ A.step i (some σ) }
                                let characters := character_set.toList

                                have h_c : c ∈ characters := by
                                    subst characters character_set
                                    simp [h_step]

                                simp at h_x'

                                exact (character_list_regex_accepts_characters characters
                                       (character_list_to_regex characters) rfl x).mpr ⟨c, h_c, h_x'.symm⟩
                case inr h_step =>
                    subst h_k_0
                    simp at h_k
                    simp
                    have h_i_neq_0: i > 0 := by
                        by_contra! h_i_0
                        simp at h_i_0
                        subst h_i_0
                        have := h_zero_step none
                        simp [this] at h_step -- contradiction
                    have h_j_neq_0: j > 0 := by
                        by_contra! h_i_0
                        simp at h_i_0
                        subst h_i_0
                        have := h_step_zero i none
                        simp [this] at h_step -- contradiction

                    let character_set: Finset α := { σ | j ∈ A.step i (some σ) }
                    let characters := character_set.toList

                    have h_x'_empty : x' = [] ∨ x' = [none] ∨ ∃ σ ∈ characters, x' = [some σ] := by
                        cases path_ij
                        case nil => left; rfl
                        case cons t c tail h_step p =>
                            right
                            have : tail = [] := by
                                cases p
                                case nil => rfl
                                case cons t' c' _ h_step' _ =>
                                    simp [Path.suppAfterStart] at h_k
                                    obtain ⟨ h_t_0, _ ⟩ := h_k
                                    subst h_t_0
                                    have := h_zero_step c'
                                    simp [this] at h_step' --contradiction
                            subst this
                            have := A.isPath_nil.mp (by use p)
                            subst this
                            simp
                            cases c
                            case none => left; rfl
                            case some σ =>
                                right
                                use σ
                                subst characters character_set
                                simp [h_step]

                    simp [Language.one_def]
                    cases h_x'_empty
                    case inl h => left; subst h; simp at h_x'; exact h_x'
                    case inr h =>
                        cases h
                        case inl h => left; subst h; simp at h_x'; exact h_x'
                        case inr h =>
                            right
                            obtain ⟨ σ, h_σ_in_characters, h_σ ⟩ := h
                            subst h_σ
                            simp at h_x'
                            exact (character_list_regex_accepts_characters characters
                                   (character_list_to_regex characters) rfl x).mpr ⟨ σ, h_σ_in_characters, h_x'.symm ⟩

            case neg h_k_0 h =>
                simp at h
                subst h_k_0
                simp at h_k
                cases path_ij
                case nil => simp at h -- contradiction
                case cons t c tail h_step p =>
                    have : tail = [] := by
                        cases p
                        case nil => rfl
                        case cons t' c' _ h_step' _ =>
                            simp [Path.suppAfterStart] at h_k
                            obtain ⟨ h_t_0, _ ⟩ := h_k
                            subst h_t_0
                            have := h_zero_step c'
                            simp [this] at h_step' --contradiction
                    subst this
                    have := (A.isPath_nil.mp (by use p)).symm
                    subst this

                    let character_set: Finset α := { σ | j ∈ A.step i (some σ) }
                    let characters := character_set.toList
                    have : ∃ σ ∈ characters, c = some σ := by
                        cases c
                        case none => simp [h.right] at h_step --contradiction
                        case some σ =>
                            use σ
                            refine ⟨ ?_, rfl ⟩
                            subst characters character_set
                            simp [h_step]

                    obtain ⟨ σ, h_σ_in_characters, h_σ ⟩ := this
                    subst h_σ
                    simp at h_x'
                    exact (character_list_regex_accepts_characters characters
                            (character_list_to_regex characters) rfl x).mpr ⟨ σ, h_σ_in_characters, h_x'.symm ⟩

            case neg h_k_neq_0 =>
                simp [Language.add_def]
                left

                replace h_k : ∀ k' ∈ path_ij.suppAfterStart, k' ≤ (k-1) := by
                    intro k' h_k'
                    replace h_k := h_k k' h_k'
                    have : k' ≠ k := by
                        by_contra!
                        subst this
                        have : k' ∉ path_ij.suppAfterStart := by
                            have h_k'_in_supp : k' ∈ path_ij.supp := by
                                clear h_k_notin_supp
                                have h_decEq : (instDecidableEqNat : DecidableEq ℕ) = Classical.decEq ℕ := by
                                    apply Subsingleton.elim
                                have := Finset.subset_iff.mp (if_supp_after_start_then_supp path_ij)
                                simp_all only [le_refl]
                            contradiction
                        contradiction
                    omega

                exact (regex_is_path A i j (k - 1) (regex_for_path_from_i_to_j_through_k A i j (k - 1))
                            rfl h_zero_step h_step_zero x).mpr ⟨ x', h_x', path_ij, h_k ⟩

theorem εNFA_to_Regex (A: εNFA α ℕ) : A.is_finite_automata → (∃ (r: RegularExpression α), r.matches' = A.accepts) := by
    sorry
    -- let A' := to_singular A
    -- have hA'tosinA: A' = to_singular A := by
    --     simp_all only [A']
    -- rw [accepts_iff_singular_accepts A A']
    -- swap
    -- simp_all only [A']
    -- rw [finite_iff_to_singular_finite A A' hA'tosinA]

    -- rw [εNFA.is_finite_automata]
    -- rintro ( hnill | ⟨ n, hnmax ⟩ )
    -- case inl =>
    --     use 0
    --     simp only [dont_go_nowhere A' hnill, RegularExpression.matches']
    -- case inr =>
    --     have hA'singular: is_singular A' := by
    --         simp_all only [A']
    --         unfold to_singular
    --         unfold is_singular
    --         constructor
    --         use SingularStart
    --         exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
    --         use SingularAccept
    --         exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
    --     unfold is_singular at hA'singular
    --     obtain ⟨ s, hs ⟩ := hA'singular.left
    --     obtain ⟨ a, ha ⟩ := hA'singular.right
    --     let A'' := to_trim A' s a n
    --     have histrim: A'' = to_trim A' s a n := by
    --         simp_all only [A', A'']
    --     have hA'finite: A'.is_finite_automata := by
    --         rw [εNFA.is_finite_automata]
    --         right
    --         use n
    --     rw [singular_finite_accepts_iff_trim_accepts
    --     A' A'' s a n
    --     hA'singular hA'finite
    --     hnmax hs ha
    --     histrim]
    --     let r' := regex_for_path_from_i_to_j_through_k A'' s a n
    --     have hr: r' = regex_for_path_from_i_to_j_through_k A' s a n := by
    --         subst A'
    --         simp_all only [A'', r']
    --         obtain ⟨left, right⟩ := hA'singular
    --         obtain ⟨w, h⟩ := left
    --         obtain ⟨w_1, h_1⟩ := right
    --         -- TODO: EYAL
    --         sorry
    --     have hgs: A''.start = {s} := by
    --         simp_all only [A', A'', r']
    --         obtain ⟨left, right⟩ := hA'singular
    --         obtain ⟨w, h⟩ := left
    --         obtain ⟨w_1, h_1⟩ := right
    --         rfl
    --     have hga: A''.accept = {a} := by
    --         simp_all only [A', A'', r']
    --         obtain ⟨left, right⟩ := hA'singular
    --         obtain ⟨w, h⟩ := left
    --         obtain ⟨w_1, h_1⟩ := right
    --         rfl
    --     use r'
    --     rw [@Language.ext_iff]
    --     intro x
    --     rw [A''.mem_accepts_iff_exists_path]
    --     rw [hgs, hga]

    --     constructor
    --     case mp =>
    --         intro hmatch
    --         use s
    --         use a
    --         let hreg := ((regex_is_path A' s a n r' hr) x).mp hmatch

    --         obtain ⟨ x', ⟨ hx', hpath⟩ ⟩ := hreg

    --         use x'
    --         refine ⟨ mem_singleton s, mem_singleton a, hx', ?_ ⟩
    --         rw [histrim]
    --         exact hpath
    --     case mpr =>
    --         rintro ⟨ temps, tempa, tempx', htemps, htempa, htempx, hpath ⟩
    --         let hreg := ((regex_is_path A' s a n r' hr) x).mpr
    --         apply hreg
    --         use tempx'
    --         constructor
    --         · exact htempx
    --         subst htempx
    --         simp_all only [mem_singleton_iff, A', A'']
