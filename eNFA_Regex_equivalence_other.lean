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
        if i = j then
            let character_set_ii: Finset α := { σ |  i ∈ A.step i (some σ) }
            let characters_ii := character_set_ii.toList

            (character_list_to_regex characters_ii).star
        else if j ∈ A.step i none then
            let character_set_ij: Finset α := { σ |  j ∈ A.step i (some σ) }
            let characters_ij := character_set_ij.toList
            let character_set_jj: Finset α := { σ |  j ∈ A.step j (some σ) }
            let characters_jj := character_set_jj.toList

            (1 + character_list_to_regex characters_ij) * (character_list_to_regex characters_jj).star
        else
            let character_set_ij: Finset α := { σ |  j ∈ A.step i (some σ) }
            let characters_ij := character_set_ij.toList
            let character_set_jj: Finset α := { σ |  j ∈ A.step j (some σ) }
            let characters_jj := character_set_jj.toList

            character_list_to_regex characters_ij * (character_list_to_regex characters_jj).star
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


@[simp]
def εNFA.Path.suppAfterStart
    {σ : Type*} [DecidableEq σ]
    {M : εNFA α σ} {s t : σ} {x : List (Option α)} :
    M.Path s t x → Finset σ
  | Path.nil _ => ∅
  | Path.cons _ _ _ _ _ _ p => p.supp


structure path_split_full (A : εNFA α ℕ) (i j k : ℕ) (word_ij: List (Option α)) (path_ij: A.Path i j word_ij) where
  word_ik : List (Option α)
  word_kk : List (Option α)
  word_kj : List (Option α)
  path_ik : A.Path i k word_ik
  path_kk : A.Path k k word_kk
  path_kj : A.Path k j word_kj
  h_word_ij : word_ij = word_ik ++ word_kk ++ word_kj
  h_path_ij : path_ij = h_word_ij▸(path_ik ++ path_kk ++ path_kj)
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
                    word_kk := []
                    word_kj := c :: tail
                    path_ik := path_nil
                    path_kk := path_nil
                    path_kj := Path.cons t k j c tail h_step path_tj
                    h_word_ij := by
                        simp
                    h_path_ij := by
                        cases path_nil
                        rfl
                    h_k_notin_ik := by
                        cases path_nil
                        simp
                    h_k_notin_kj := by
                        simpa [Path.suppAfterStart] using hk_tail
                }

            case pos =>
                obtain ⟨p, _⟩ := h_induction hk_tail
                obtain ⟨
                    word_tk, word_kk, word_kj,
                    path_tk, path_kk, path_kj,
                    h_word, h_path,
                    h_notin_tk, h_notin_kj
                ⟩ := p

                have path_nil : A.Path k k [] := Path.nil k

                let path_k_to_k : A.Path k k ([c] ++ word_tk) :=
                    Path.cons t k k c word_tk h_step path_tk

                use {
                    word_ik := []
                    word_kk := [c] ++ word_tk ++ word_kk
                    word_kj := word_kj
                    path_ik := path_nil
                    path_kk := path_k_to_k ++ path_kk
                    path_kj := path_kj
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
            obtain ⟨ p ⟩ := h_induction
            obtain ⟨word_tk, word_kk, word_kj,path_tk, path_kk, path_kj,
                h_word_equiv, h_path_equiv,h_k_notin_path_tk, h_notin_path_kj_tail
            ⟩ := p

            by_cases h_ik : k = i
            case pos =>
                subst i

                have path_ik : A.Path k k [] := Path.nil k

                use {
                    word_ik := []
                    word_kk := [c] ++ word_tk ++ word_kk
                    word_kj := word_kj
                    path_ik := path_ik
                    path_kk :=
                        (Path.cons t k k c word_tk h_step path_tk) ++ path_kk
                    path_kj := path_kj
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
                    h_k_notin_kj := h_notin_path_kj_tail
                }
            case neg =>
                use {
                    word_ik := [c] ++ word_tk
                    word_kk := word_kk
                    word_kj := word_kj
                    path_ik :=
                        Path.cons t i k c word_tk h_step path_tk
                    path_kk := path_kk
                    path_kj := path_kj
                    h_word_ij := by
                        subst tail
                        simp [List.append_assoc]
                    h_path_ij := by
                        subst tail
                        subst path_tj
                        rfl
                    h_k_notin_ik := by
                        simp [h_ik, h_k_notin_path_tk]
                    h_k_notin_kj :=
                        h_notin_path_kj_tail
                }

lemma regex_is_path_mp (A : εNFA α ℕ) (i j k : ℕ) (r: RegularExpression α) (hr: r = regex_for_path_from_i_to_j_through_k A i j k)
    (h_zero_step: ∀ (σ : Option α), A.step 0 σ = ∅) (h_step_zero: ∀ (q : ℕ) (σ : Option α), 0 ∉ A.step q σ):
    ∀(x : List α), ((x ∈ r.matches') → (∃(x': List ((Option α))), (x'.reduceOption = x) ∧ Nonempty ((to_trim A i j k).Path i j x'))) := by
    sorry
    -- intro x h_r_matches_x
    -- unfold regex_for_path_from_i_to_j_through_k at hr
    -- split_ifs at hr
    -- case pos h_k_0 h_ij =>
    --     subst h_k_0 h_ij

    --     simp [hr, Language.kstar_def] at h_r_matches_x
    --     cases h_r_matches_x
    --     case intro L h_L =>
    --         obtain ⟨ h_x_L, h_L ⟩ := h_L

    --         use [none]
    --         simp [to_trim]
    --         split_ifs
    --         case pos =>
    --             simp

    --         case neg =>
    --             simp [h_ij]
    --             omega

    --     case inr h_x_in_character_list =>
    --         let character_set: Finset alphabet := { σ |  j ∈ A.step i (some σ) }
    --         let characters := character_set.toList

    --         obtain ⟨ σ, h_step, h_x_σ ⟩ := (character_list_regex_accepts_characters characters (character_list_to_regex characters) rfl x).mp h_x_in_character_list
    --         subst characters character_set
    --         simp at h_step

    --         use [some σ]
    --         simp [to_trim, h_x_σ]
    --         split_ifs
    --         case pos => simp [h_step]
    --         case neg => simp [h_step] ; omega

    -- case neg h_k_0 =>
    --     simp [hr] at h_r_matches_x
    --     let character_set: Finset α := { σ |  j ∈ A.step i (some σ) }
    --     let characters := character_set.toList

    --     obtain ⟨ σ, h_step, h_x_σ ⟩ := (character_list_regex_accepts_characters characters (character_list_to_regex characters) rfl x).mp h_r_matches_x
    --     subst characters character_set
    --     simp at h_step

    --     use [some σ]
    --     simp [to_trim, h_x_σ]
    --     split_ifs
    --     case pos => simp [h_step]
    --     case neg => simp [h_step] ; omega

    -- case neg =>
    --     let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k - 1)
    --     let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k - 1)
    --     let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k - 1) -- later: handle kstar
    --     let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k - 1)

    --     simp at h_r_matches_x
    --     simp [hr, Language.add_def] at h_r_matches_x
    --     clear hr
    --     cases h_r_matches_x
    --     case inl h_x_in_rᵢⱼ =>
    --         have h_induction := (regex_is_path A i j (k-1) rᵢⱼ rfl x).mp h_x_in_rᵢⱼ
    --         clear rᵢⱼ rᵢₖ rₖⱼ rₖₖ
    --         obtain ⟨ x', h_x', h_path ⟩ := h_induction

    --         use x'
    --         refine ⟨ h_x', ?_ ⟩

    --         have h_contains := regex_for_path_contains_ij A i j k (k-1) (by omega)
    --         exact εNFA.path_if_contains (to_trim A i j k) (to_trim A i j (k-1)) h_contains i j x' h_path
    --     case inr h_x_in_rᵢₖ_rₖₖ_rₖⱼ =>
    --         clear rᵢⱼ
    --         simp [Language.mul_def] at h_x_in_rᵢₖ_rₖₖ_rₖⱼ
    --         obtain ⟨ xᵢₖ, h_xᵢₖ, xₖₖ, h_xₖₖ, xₖⱼ, h_xₖⱼ, h_x ⟩ := h_x_in_rᵢₖ_rₖₖ_rₖⱼ
    --         obtain ⟨ xᵢₖ', h_xᵢₖ', h_path_ik ⟩ := (regex_is_path A i k (k-1) rᵢₖ rfl xᵢₖ).mp h_xᵢₖ
    --         obtain ⟨ xₖⱼ', h_xₖⱼ', h_path_kj ⟩ := (regex_is_path A k j (k-1) rₖⱼ rfl xₖⱼ).mp h_xₖⱼ
    --         clear rᵢₖ rₖⱼ h_xᵢₖ h_xₖⱼ

    --         simp [Language.kstar_def] at h_xₖₖ
    --         obtain ⟨ L, h_L, h_xₖₖ ⟩ := h_xₖₖ

    --         have h_path_L_kk : ∃ (L' : List (List (Option alphabet))), L'.flatten.reduceOption = L.flatten ∧
    --             (∀ x' ∈ L', Nonempty ((to_trim A k k (k - 1)).Path k k x')) := by
    --             clear h_L
    --             induction L
    --             case nil => use []; simp
    --             case cons head tail h_induction =>
    --                 simp at h_xₖₖ
    --                 obtain ⟨ L'', h_L'', h_path_L'' ⟩ := h_induction h_xₖₖ.right
    --                 obtain ⟨ head', h_head', h_path_head' ⟩ := (regex_is_path A k k (k-1) rₖₖ rfl head).mp h_xₖₖ.left
    --                 use head' :: L''
    --                 simp [List.reduceOption_append, h_head', h_L'', h_path_head']
    --                 exact h_path_L''
    --         clear rₖₖ h_xₖₖ

    --         obtain ⟨ L', h_L', h_path_kk ⟩ := h_path_L_kk

    --         let xₖₖ' := L'.flatten
    --         replace h_path_kk : Nonempty ((to_trim A k k (k - 1)).Path k k xₖₖ') := by
    --             clear h_L h_L'
    --             subst xₖₖ'
    --             induction L'
    --             case nil => simp only [List.flatten_nil, εNFA.isPath_nil]
    --             case cons head tail h_induction =>
    --                 simp at h_path_kk
    --                 replace h_induction := h_induction h_path_kk.right

    --                 simp [List.flatten_cons]
    --                 apply (to_trim A k k (k - 1)).isPath_append.mpr
    --                 exact ⟨ k, h_path_kk.left, h_induction ⟩

    --         use xᵢₖ' ++ xₖₖ' ++ xₖⱼ'

    --         simp [symm h_xᵢₖ', symm h_xₖⱼ'] at h_x
    --         simp [List.reduceOption_append]

    --         have : xₖₖ'.reduceOption = L.flatten := by
    --             subst h_L
    --             simp_all only [xₖₖ']

    --         refine ⟨ by simp_all, ?_ ⟩

    --         have h_containsᵢₖ := regex_for_path_contains_ik A i j k (k-1) (by omega)
    --         have h_containsₖⱼ := regex_for_path_contains_kj A i j k (k-1) (by omega)
    --         have h_containsₖₖ := regex_for_path_contains_kk A i j k (k-1) (by omega)
    --         replace h_path_ik := εNFA.path_if_contains (to_trim A i j k) (to_trim A i k (k-1)) h_containsᵢₖ i k xᵢₖ' h_path_ik
    --         replace h_path_kj := εNFA.path_if_contains (to_trim A i j k) (to_trim A k j (k-1)) h_containsₖⱼ k j xₖⱼ' h_path_kj
    --         replace h_path_kk := εNFA.path_if_contains (to_trim A i j k) (to_trim A k k (k-1)) h_containsₖₖ k k xₖₖ' h_path_kk

    --         apply (to_trim A i j k).isPath_append.mpr
    --         refine ⟨ k, h_path_ik , ?_ ⟩
    --         apply (to_trim A i j k).isPath_append.mpr
    --         use k

theorem regex_is_path (A : εNFA α ℕ) (i j k : ℕ) (r: RegularExpression α) (hr: r = regex_for_path_from_i_to_j_through_k A i j k)
    (h_zero_step: ∀ (σ : Option α), A.step 0 σ = ∅) (h_step_zero: ∀ (q : ℕ) (σ : Option α), 0 ∉ A.step q σ):
    ∀ (x : List α), ((x ∈ r.matches') ↔ (∃(x': List (Option α)), (x'.reduceOption = x) ∧
     ∃ (path_ij: A.Path i j x'), ∀ (k': ℕ), ((k' > k) → k' ∉ path_ij.states.tail))) := by
    intro x
    constructor
    case mp =>
        sorry
        -- exact regex_is_path_mp A i j k r hr h_zero_step h_step_zero x
    case mpr =>
        intro h
        obtain ⟨ x', h_x', h_path_ij ⟩ := h
        obtain ⟨ path_ij, h_path_ij ⟩ := h_path_ij

        by_cases k ∈ h_path_ij.supp
        case pos h_k =>
            obtain ⟨ stesp_ik, steps_kk, steps_kj, h_steps ⟩ := split_path_by_state A i j k x' path_ij h_k


            sorry
        case neg =>
            -- by induction r₁
            sorry

        -- unfold regex_for_path_from_i_to_j_through_k at hr

        -- split_ifs at hr
        -- case pos h_k_0 h_ij => sorry
        --     subst h_ij h_k_0
        --     simp at hr
        --     subst hr
        --     induction x' generalizing x
        --     case nil =>
        --         simp at h_x'
        --         subst h_x'
        --         simp [Language.kstar_def]
        --         use []
        --         simp
        --     case cons c tail h_induction =>
        --         have h_tail_path : Nonempty ((to_trim A i i 0).Path i i tail) := by
        --             by_cases h_i_0: i = 0
        --             case pos =>
        --                 subst h_i_0
        --                 obtain ⟨ h_x'_path ⟩ := h_x'_path
        --                 cases h_x'_path
        --                 case cons t h_step h_path =>
        --                     simp [to_trim] at h_step
        --                     simp [h_step.right] at h_path
        --                     use h_path
        --             case neg =>
        --                 obtain ⟨ h_x'_path ⟩ := h_x'_path
        --                 cases h_x'_path
        --                 case cons t h_step h_path =>
        --                     replace h_i_0: i > 0 := by omega
        --                     simp [to_trim, h_i_0] at h_step
        --                     cases h_step
        --                     case inl h_t_0 =>
        --                         have := h_t_0.right
        --                         subst this
        --                         simp at h_t_0

        --                         cases h_path
        --                         case nil => simp
        --                         case cons _ _ _ h_step' _ =>
        --                             unfold to_trim at h_step'
        --                             split_ifs at h_step'
        --                             simp at h_step'
        --                             cases h_step'
        --                             case inl h_t'_0 =>
        --                                 simp [h_t'_0.right, h_zero_step] at h_t'_0 --contradiction
        --                             case inr h_t'_i =>
        --                                 simp [h_t'_i.right, h_zero_step] at h_t'_i --contradiction

        --                     case inr h_t_i =>
        --                         simp [h_t_i.right] at h_path
        --                         use h_path

        --         by_cases c = none
        --         case pos h_c_none =>
        --             subst h_c_none
        --             exact h_induction x h_x' h_tail_path
        --         case neg h_c_some =>
        --             have h_step: i ∈ (to_trim A i i 0).step i c := by
        --                 obtain ⟨ h_x'_path ⟩ := h_x'_path
        --                 cases h_x'_path
        --                 case cons t h_step h_path =>
        --                     simp [to_trim] at h_step
        --                     split_ifs at h_step
        --                     case pos h_i =>
        --                         simp at h_step
        --                         cases h_step
        --                         case inl h_t_0 =>
        --                             have := h_t_0.right
        --                             subst this
        --                             cases h_path
        --                             case nil => simp [h_zero_step] at h_t_0 -- contradiction
        --                             case cons _ _ _ h_step' _ =>
        --                                 simp [to_trim] at h_step'
        --                                 split_ifs at h_step'
        --                                 simp at h_step'
        --                                 cases h_step'
        --                                 case inl h_step' =>
        --                                     simp [h_zero_step] at h_step' -- contradiction
        --                                 case inr h_step' =>
        --                                     simp [h_zero_step] at h_step' -- contradiction

        --                         case inr h_t_i =>
        --                             simp [h_t_i.right] at h_t_i
        --                             simp [to_trim, h_i]
        --                             right
        --                             exact h_t_i

        --                     case neg h_i =>
        --                         replace h_i : i = 0 := by omega
        --                         subst h_i
        --                         simp [h_zero_step] at h_step --contradiction

        --             replace h_induction := h_induction tail.reduceOption rfl h_tail_path
        --             simp [Language.kstar_def] at h_induction ⊢
        --             obtain ⟨ L, h_L_tail, h_L_matches ⟩ := h_induction

        --             replace h_c_some := not_none_is_some c h_c_some
        --             obtain ⟨ σ, h_σ ⟩ := h_c_some
        --             subst h_σ

        --             use [σ] :: L
        --             simp [h_L_tail] at h_x'
        --             simp
        --             refine ⟨ symm h_x', ?_, h_L_matches ⟩
        --             simp [to_trim] at h_step
        --             split_ifs at h_step
        --             case pos h_i_0 =>
        --                 replace h_i_0 : i ≠ 0 := by omega
        --                 simp [h_i_0] at h_step
        --                 let character_set: Finset α := { σ |  i ∈ A.step i (some σ) }
        --                 let characters := character_set.toList
        --                 let r := character_list_to_regex characters

        --                 apply (character_list_regex_accepts_characters characters r rfl [σ]).mpr
        --                 use σ
        --                 subst characters character_set
        --                 simp
        --                 exact h_step
        --             case neg h_i_0 =>
        --                 replace h_i_0 : i = 0 := by omega
        --                 subst h_i_0
        --                 simp [h_zero_step] at h_step --contradiction

        -- case pos h_k_0 h_i_neq_j h_step =>
        --     cases x'
        --     case nil =>
        --         subst h_x' hr
        --         simp [Language.mem_add, Language.mem_mul]
        --         left
        --         simp [Language.kstar_def]
        --         use []
        --         simp
        --     case cons c tail =>
        --         subst hr
        --         simp [Language.mem_add, Language.mem_mul]
        --         by_cases c = none
        --         case pos h_c_none =>
        --             left
        --             subst h_c_none
        --             simp at h_x'
        --             obtain ⟨ h_x'_path ⟩ := h_x'_path
        --             cases h_x'_path
        --             case cons t h_step h_path =>
        --                 let character_set: Finset α := { σ | j ∈ A.step j (some σ) }
        --                 let characters := character_set.toList
        --                 let r := character_list_to_regex characters
        --                 have h_t_j : j = t := by
        --                     subst h_k_0
        --                     unfold to_trim at h_step
        --                     simp at h_step
        --                     split_ifs at h_step
        --                     case pos =>
        --                         simp at h_step
        --                         cases h_step
        --                         case inl h =>
        --                             obtain ⟨ h_step', h_t_0 ⟩ := h
        --                             subst h_t_0
        --                             cases h_path
        --                             case nil => rfl
        --                             case cons _ σ' _ h_step' _ =>
        --                                 simp [to_trim] at h_step'
        --                                 simp_all
        --                         case inr h => exact symm h.right
        --                     case neg =>
        --                         simp at h_step
        --                         obtain ⟨ h_step', h_t_0 ⟩ := h_step
        --                         subst h_t_0
        --                         cases h_path
        --                         case nil => rfl
        --                         case cons _ σ' _ h_step' _ =>
        --                             simp [to_trim] at h_step'
        --                             simp_all

        --                 subst h_t_j
        --                 simp [Language.kstar_def]
        --                 induction tail generalizing x
        --                 case nil =>
        --                     simp at h_x'
        --                     use []
        --                     simp [h_x']
        --                 case cons c' tail' h_induction =>
        --                     rw [← List.singleton_append] at h_path
        --                     replace h_path : Nonempty ((to_trim A i j k).Path j j ([c'] ++ tail')) := by use h_path
        --                     obtain ⟨ t, h_path_c, h_path_tail' ⟩ := (to_trim A i j k).isPath_append.mp h_path

        --                     have h_t_j : j = t := by
        --                         simp [to_trim, h_k_0] at h_path_c
        --                         split_ifs at h_path_c
        --                         case pos =>
        --                             simp at h_path_c
        --                             cases h_path_c
        --                             case inl h =>
        --                                 obtain ⟨ h_step_t, h_t_0 ⟩ := h
        --                                 subst h_t_0
        --                                 have := h_step_zero j c'
        --                                 contradiction
        --                             case inr h =>
        --                                 obtain ⟨ h_step_t, h_t_j ⟩ := h
        --                                 exact symm h_t_j
        --                         case neg =>
        --                             simp at h_path_c
        --                             obtain ⟨ h_step_t, h_t_0 ⟩ := h_path_c
        --                             subst h_t_0
        --                             have := h_step_zero j c'
        --                             contradiction

        --                     subst h_t_j

        --                     obtain ⟨ h_path_tail' ⟩ := h_path_tail'
        --                     have := h_induction tail'.reduceOption rfl h_path_tail'
        --                     obtain ⟨ L', h ⟩ := this
        --                     cases c'
        --                     case none =>
        --                         use L'
        --                         simp at h_x'
        --                         subst h_x'
        --                         exact h
        --                     case some σ =>
        --                         use [σ] :: L'
        --                         simp [h.left] at h_x'
        --                         simp [h_x']
        --                         refine ⟨ ?_, h.right ⟩
        --                         simp [to_trim, h_k_0] at h_path_c
        --                         split_ifs at h_path_c
        --                         case pos =>
        --                             simp at h_path_c
        --                             cases h_path_c
        --                             case inl => omega -- contradiction
        --                             case inr h =>
        --                                 have : σ ∈ characters := by
        --                                     unfold characters character_set
        --                                     simp [h]
        --                                 exact (character_list_regex_accepts_characters characters r rfl [σ]).mpr ⟨ σ, this, rfl ⟩
        --                         case neg =>
        --                             simp at h_path_c
        --                             obtain ⟨ h_step, h_j_0 ⟩ := h_path_c
        --                             subst h_j_0
        --                             have := h_zero_step (some σ)
        --                             simp [this] at h_step -- contradiction

        --         case neg h_c_some =>
        --             right
        --             clear h_step
        --             replace h_c_some := not_none_is_some c h_c_some
        --             obtain ⟨ σ, h_σ ⟩ := h_c_some
        --             subst h_σ
        --             simp at h_x'

        --             obtain ⟨ h_x'_path ⟩ := h_x'_path
        --             cases h_x'_path
        --             case cons t h_step h_path =>
        --                 have h_t_j : j = t := by
        --                     simp [to_trim, h_k_0] at h_step
        --                     split_ifs at h_step
        --                     case pos =>
        --                         simp at h_step
        --                         cases h_step
        --                         case inl h =>
        --                             obtain ⟨ h_step_t, h_t_0 ⟩ := h
        --                             subst h_t_0
        --                             have := h_step_zero i (some σ)
        --                             contradiction
        --                         case inr h =>
        --                             obtain ⟨ h_step_t, h_t_j ⟩ := h
        --                             exact symm h_t_j
        --                     case neg =>
        --                         simp at h_step
        --                         obtain ⟨ h_step_t, h_t_0 ⟩ := h_step
        --                         subst h_t_0
        --                         have := h_step_zero i (some σ)
        --                         contradiction
        --                 subst h_t_j

        --                 use [σ]
        --                 simp
        --                 constructor
        --                 case left =>
        --                     let character_set: Finset α := { σ | j ∈ A.step i (some σ) }
        --                     let characters := character_set.toList
        --                     let r := character_list_to_regex characters

        --                     have : σ ∈ characters := by
        --                         unfold characters character_set
        --                         simp [to_trim] at h_step
        --                         subst h_k_0
        --                         split_ifs at h_step
        --                         case pos =>
        --                             simp at h_step ⊢
        --                             cases h_step
        --                             case inl h => exact h.left
        --                             case inr h => exact h
        --                         case neg =>
        --                             simp at h_step ⊢
        --                             exact h_step.left

        --                     exact (character_list_regex_accepts_characters characters r rfl [σ]).mpr ⟨ σ, this, rfl ⟩

        --                 case right =>
        --                     induction tail generalizing x
        --                     case nil =>
        --                         simp at h_x'
        --                         use []
        --                         simp [h_x', Language.kstar_def]
        --                         use []
        --                         simp

        --                     case cons c' tail' h_induction =>
        --                         rw [← List.singleton_append] at h_path
        --                         replace h_path : Nonempty ((to_trim A i j k).Path j j ([c'] ++ tail')) := by use h_path
        --                         have := (to_trim A i j k).isPath_append.mp h_path
        --                         obtain ⟨ t, h_path_c, h_path_tail' ⟩ := this
        --                         have h_t_j : j = t := by sorry --TODO!!!
        --                         subst h_t_j
        --                         obtain ⟨ h_path_tail' ⟩ := h_path_tail'
        --                         have := h_induction (σ :: tail'.reduceOption) rfl h_path_tail'
        --                         obtain ⟨ b, h_b, h_tail' ⟩ := this
        --                         simp at h_tail' h_x'

        --                         cases c'
        --                         case none =>
        --                             use b
        --                             simp at h_x'
        --                             subst h_x' h_tail'
        --                             simp
        --                             exact h_b
        --                         case some σ =>
        --                             use σ :: b
        --                             simp at h_x'
        --                             subst h_x' h_tail'
        --                             simp

        --                             simp [to_trim, h_k_0] at h_path_c
        --                             split_ifs at h_path_c
        --                             case pos =>
        --                                 simp at h_path_c
        --                                 cases h_path_c
        --                                 case inl => omega -- contradiction
        --                                 case inr h =>
        --                                     let character_set: Finset α := { σ | j ∈ A.step j (some σ) }
        --                                     let characters := character_set.toList
        --                                     let r := character_list_to_regex characters
        --                                     have : σ ∈ characters := by
        --                                         unfold characters character_set
        --                                         simp [h]
        --                                     replace := (character_list_regex_accepts_characters characters r rfl [σ]).mpr ⟨ σ, this, rfl ⟩

        --                                     simp [Language.kstar_def] at h_b ⊢
        --                                     obtain ⟨ L', h_L' ⟩ := h_b
        --                                     use [σ] :: L'
        --                                     subst character_set characters r
        --                                     simp [h_L', this]
        --                                     exact h_L'.right

        --                             case neg =>
        --                                 simp at h_path_c
        --                                 obtain ⟨ h_step, h_j_0 ⟩ := h_path_c
        --                                 subst h_j_0
        --                                 have := h_zero_step (some σ)
        --                                 simp [this] at h_step -- contradiction

        case neg h_k_0 h_i_neq_j h_not_step => sorry
            -- cases x'
            -- case nil =>
            --     simp at h_x'_path
            --     contradiction
            -- case cons c tail =>
            --     rw [← List.singleton_append] at h_x'_path
            --     obtain ⟨ t, h_path_c, h_path' ⟩ := (to_trim A i j k).isPath_append.mp h_x'_path
            --     simp [to_trim, h_k_0] at h_path_c
            --     split_ifs at h_path_c
            --     case pos =>
            --         simp at h_path_c
            --         cases h_path_c
            --         case inl h_t_0 => simp_all [h_t_0.right]
            --         case inr h_t_j =>
            --             obtain ⟨ h_step_t, h_t_j ⟩ := h_t_j
            --             symm at h_t_j
            --             subst h_t_j

            --             have : ∃ σ, c = some σ := by
            --                 apply not_none_is_some
            --                 by_contra!
            --                 subst this
            --                 contradiction
            --             obtain ⟨ σ, h_σ ⟩ := this
            --             subst h_σ

            --             simp at h_x'_path
            --             subst hr
            --             simp
            --             simp at h_x'
            --             subst h_x'
            --             rw [← List.singleton_append] at h_x'_path
            --             obtain ⟨ t, h_path_σ, h_path_tail ⟩ := (to_trim A i j k).isPath_append.mp h_x'_path
            --             clear h_x'_path
            --             have h_t_j : j = t := by
            --                 simp [to_trim, h_k_0] at h_path_σ
            --                 split_ifs at h_path_σ
            --                 simp at h_path_σ
            --                 cases h_path_σ
            --                 case inl h =>
            --                     obtain ⟨ h_step_t, h_t_0 ⟩ := h
            --                     subst h_t_0
            --                     have := h_step_zero i (some σ)
            --                     contradiction
            --                 case inr h =>
            --                     obtain ⟨ h_step_t, h_t_j ⟩ := h
            --                     exact symm h_t_j
            --             subst h_t_j

            --             let character_set_ij: Finset α := { σ | j ∈ A.step i (some σ) }
            --             let characters_ij := character_set_ij.toList
            --             let r_ij := character_list_to_regex characters_ij

            --             have h_matches_σ : σ ∈ characters_ij := by
            --                 simp [to_trim, h_k_0] at h_path_σ
            --                 split_ifs at h_path_σ
            --                 simp at h_path_σ
            --                 simp [characters_ij, character_set_ij]
            --                 cases h_path_σ
            --                 case inl h => exact h.left
            --                 case inr h => exact h

            --             replace h_matches_σ := (character_list_regex_accepts_characters characters_ij r_ij rfl [σ]).mpr ⟨ σ, h_matches_σ, rfl ⟩
            --             simp [Language.mem_mul]
            --             use [σ]
            --             refine ⟨ h_matches_σ, ?_ ⟩

            --             induction tail
            --             case nil =>
            --                 use []
            --                 simp [Language.kstar_def]
            --                 use []
            --                 simp

            --             case cons c' tail' h_induction =>
            --                 clear h_path_tail
            --                 rw [← List.singleton_append] at h_path'
            --                 obtain ⟨ t, h_path_c', h_path_tail' ⟩ := (to_trim A i j k).isPath_append.mp h_path'
            --                 have h_t_j : j = t := by
            --                     simp [to_trim, h_k_0] at h_path_c'
            --                     split_ifs at h_path_c'
            --                     simp at h_path_c'
            --                     cases h_path_c'
            --                     case inl h =>
            --                         obtain ⟨ h_step_t, h_t_0 ⟩ := h
            --                         subst h_t_0
            --                         have := h_step_zero j c'
            --                         contradiction
            --                     case inr h =>
            --                         obtain ⟨ h_step_t, h_t_j ⟩ := h
            --                         exact symm h_t_j
            --                 subst h_t_j

            --                 have := h_induction h_path_tail' h_path_tail'
            --                 simp [Language.kstar_def] at this ⊢
            --                 obtain ⟨ L', h_L' ⟩ := this

            --                 cases c'
            --                 case none =>
            --                     simp
            --                     use L'
            --                 case some σ' =>
            --                     use [σ'] :: L'
            --                     simp
            --                     refine ⟨ h_L'.left , ?_, h_L'.right ⟩

            --                     let character_set_jj: Finset α := { σ | j ∈ A.step j (some σ) }
            --                     let characters_jj := character_set_jj.toList
            --                     let r_jj := character_list_to_regex characters_jj

            --                     have h_matches_σ' : σ' ∈ characters_jj := by
            --                         simp [to_trim, h_k_0] at h_path_c'
            --                         split_ifs at h_path_c'
            --                         simp at h_path_c'
            --                         simp [characters_jj, character_set_jj]
            --                         cases h_path_c'
            --                         case inl h => exact h.left
            --                         case inr h => exact h

            --                     exact (character_list_regex_accepts_characters characters_jj r_jj rfl [σ']).mpr ⟨ σ', h_matches_σ', rfl ⟩

            --     case neg h_j_0 =>
            --         simp at h_j_0
            --         subst h_j_0
            --         simp at h_path_c
            --         obtain ⟨ h_step, h_t_0 ⟩ := h_path_c
            --         subst h_t_0
            --         have := h_step_zero i c
            --         contradiction

        -- case neg h_k_not_0 =>
        --     let rᵢⱼ := regex_for_path_from_i_to_j_through_k A i j (k - 1)
        --     let rᵢₖ := regex_for_path_from_i_to_j_through_k A i k (k - 1)
        --     let rₖₖ := regex_for_path_from_i_to_j_through_k A k k (k - 1)
        --     let rₖⱼ := regex_for_path_from_i_to_j_through_k A k j (k - 1)

        --     let A_ij := (to_trim A i j k)
        --     let A_ik := (to_trim A i k (k - 1))
        --     let A_kk := (to_trim A k k (k - 1))
        --     let A_kj := (to_trim A k j (k - 1))

        --     have h_path_ij : Nonempty (A_ij.Path i j x') := h_x'_path
        --     obtain ⟨ path_ij ⟩ := h_path_ij

        --     simp [hr]
        --     by_cases k ∈ path_ij.supp
        --     case pos h_k_supp =>
        --         right
        --         have h_lemma : ∃ (x'_ik x'_kk x'_kj : List (Option α)),
        --             Nonempty (A_ik.Path i k x'_ik) ∧
        --             (∃ (L' : List (List (Option α))), L'.flatten = x'_kk ∧
        --              ∀ y' ∈ L', Nonempty (A_kk.Path k k y')) ∧
        --             Nonempty (A_kj.Path k j x'_kj) ∧
        --             x' = x'_ik ++ x'_kk ++ x'_kj := by

        --             have h_x'_ik : ∃ (x'_ik : List (Option α)), x'_ik.isPrefixOf x' ∧
        --                 ((i = k ∧ x'_ik = []) ∨ ∃ (path_ik : A_ij.Path i k x'_ik), k ∉ path_ik.supp) := by
        --                 have := path_prefix_of_state A_ij i j k x' path_ij h_k_supp
        --                 cases this
        --                 case inl h_ik =>
        --                     subst h_ik
        --                     use []
        --                     simp
        --                 case inr h_y' =>
        --                     obtain ⟨ y', h_y'_prefix, path_ik, h_path_ik ⟩ := h_y'
        --                     use y'
        --                     simp [h_y'_prefix]
        --                     right
        --                     use path_ik

        --             obtain ⟨ x'_ik, h_prefix, h ⟩ := h_x'_ik

        --             use x'_ik
        --             have : Nonempty (A_ik.Path i k x'_ik) := by
        --                 cases h
        --                 case inl h =>
        --                     obtain ⟨ h_ik, h_empty ⟩ := h
        --                     subst h_ik h_empty
        --                     apply A_ik.isPath_nil.mpr
        --                     rfl
        --                 case inr h_path_ik =>
        --                     obtain ⟨ path_ik , h_k_notin_supp ⟩ := h_path_ik
        --                     have := path_trim_of_not_mem_supp A i j k i k x'_ik h_k_not_0 path_ik h_k_notin_supp

        --                     -- have h_x_in_left : Nonempty ((to_trim A i j (k - 1)).Path i j x') :=
        --                     --     path_trim_of_not_mem_supp A i j k i j x' h_k_not_0 path_ij h_k_notin_supp

        --                     sorry
        --             sorry

        --         simp [Language.mul_def]
        --         obtain ⟨ x'_ik, x'_kk, x'_kj, h_x'', h_x'_ik, h_x'_kk, h_x'_kj ⟩ := h_lemma

        --         refine ⟨ x'_ik.reduceOption, ?_, x'_kk.reduceOption, ?_, x'_kj.reduceOption, ?_, ?_ ⟩
        --         case refine_1 =>
        --             exact (regex_is_path A i k (k - 1) rᵢₖ rfl
        --                 h_zero_step h_step_zero x'_ik.reduceOption).mpr
        --                 ⟨x'_ik, rfl, h_x'_ik⟩

        --         case refine_2 =>
        --             simp [Language.kstar_def]
        --             obtain ⟨ L', h_L'_x'_kk, h_L' ⟩ := h_x'_kk
        --             let L : List (List α) := L'.map (fun x' => x'.reduceOption)
        --             use L
        --             refine ⟨ ?_, ?_ ⟩
        --             case refine_1 =>
        --                 subst h_L'_x'_kk L
        --                 exact list_map_of_reduce_option L'

        --             case refine_2 =>
        --                 intro y h_y
        --                 have : ∃ y' ∈ L', y'.reduceOption = y := by
        --                     subst L
        --                     simp at h_y
        --                     exact h_y
        --                 obtain ⟨ y', h_y'_in_L', h_y' ⟩ := this
        --                 have := h_L' y' h_y'_in_L'

        --                 exact (regex_is_path A k k (k - 1) rₖₖ rfl
        --                     h_zero_step h_step_zero y).mpr
        --                     ⟨y', h_y', this⟩

        --         case refine_3 =>
        --             exact (regex_is_path A k j (k - 1) rₖⱼ rfl
        --                 h_zero_step h_step_zero x'_kj.reduceOption).mpr
        --                 ⟨x'_kj, rfl, h_x'_kj⟩

        --         case refine_4 =>
        --             have : x'.reduceOption = x'_ik.reduceOption ++ x'_kk.reduceOption ++ x'_kj.reduceOption := by
        --                 subst h_x''
        --                 simp [List.reduceOption_append]
        --             subst h_x'
        --             simp [this]

        --     case neg h_k_notin_supp =>
        --         left
        --         have h_x_in_left : Nonempty ((to_trim A i j (k - 1)).Path i j x') :=
        --             path_trim_of_not_mem_supp A i j k i j x' h_k_not_0 path_ij h_k_notin_supp

        --         exact (regex_is_path A i j (k - 1) rᵢⱼ rfl
        --             h_zero_step h_step_zero x).mpr
        --             ⟨x', h_x', h_x_in_left⟩

            --cases h_x'_path

            -- by_cases Nonempty ((to_trim A i j (k - 1)).Path i j x')
            -- case pos h_x_in_left =>
            --     left
            --     exact (regex_is_path A i j (k-1) rᵢⱼ rfl h_zero_step h_step_zero x).mpr ⟨ x', h_x', h_x_in_left ⟩
            -- case neg h_x_not_in_left =>
            --     right
            --     simp [Language.mul_def]

            --     have h_x_decomposition : ∃ (x_ik x_kk x_kj : List α), x = x_ik ++ x_kk ++ x_kj ∧
            --         x_ik ∈ rᵢₖ.matches' ∧ x_kk ∈ rₖₖ.star.matches' ∧ x_kj ∈ rₖⱼ.matches' := by
            --         induction x'
            --         case nil =>
            --             use [], [], []
            --             simp at h_x'
            --             simp [h_x']
            --             sorry
            --         case cons c tail h_induction =>


            --         unfold to_trim at h_x'_path
            --         split_ifs at h_x'_path
            --         case pos h_k_greater_than_j =>
            --             simp at h_x'_path
            --             cases h_x'_path
            --             sorry
            --         case neg h_k_leq_than_j =>
            --             sorry

            --     obtain ⟨ x_ik, x_kk, x_kj, h_x, h_x_ik, h_x_kk, h_x_kj ⟩ := h_x_decomposition
            --     use x_ik
            --     refine ⟨ h_x_ik , ?_ ⟩
            --     use x_kk
            --     refine ⟨ h_x_kk , ?_ ⟩
            --     use x_kj
            --     refine ⟨ h_x_kj, ?_ ⟩
            --     simp [h_x]

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
