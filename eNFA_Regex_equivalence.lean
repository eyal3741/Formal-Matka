import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
open Set

universe u v

variable {alphabet : Type u} { Q : Type v}

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
        simp only [RegularExpression.one_def, RegularExpression.matches'_epsilon, Language.one_def]
        rw [@Language.ext_iff]
        intro x
        rw [@mem_singleton_iff]
        rw[A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 0, []
            exact ⟨ rfl, rfl, id (Eq.symm hx), (εNFA.isPath_nil A).mpr rfl ⟩

        case mpr =>
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩

            induction x
            case nil => rfl
            case cons σ tail _ =>
                absurd h_ispath
                intro h
                induction h
                case nil =>
                    simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff,
                      List.reduceOption_nil, List.nil_eq, reduceCtorEq, A]
                case cons _ _ _ _ h_step_with_σ _ _ _ =>
                    exact h_step_with_σ

    case char σ =>
        let A : εNFA alphabet ℕ := {
            start  := {0}
            accept := {1}
            step   := fun q a => match q, a with
                | 0, σ => {1}
                | _, _ => ∅
        }
        use A

        simp only [RegularExpression.matches'_char]
        rw [@Language.ext_iff]
        intro x
        rw [@mem_singleton_iff]
        rw[A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 1, [σ]
            exact ⟨ rfl, rfl, id (Eq.symm hx), εNFA.IsPath.singleton A rfl ⟩

        case mpr =>
            -- TODO!!!!!!!!!!!
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩

            induction x
            case nil =>
                absurd h_ispath
                intro h
                induction h
                case nil =>
                    simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff,
                      List.reduceOption_nil, List.nil_eq, reduceCtorEq, A]
                case cons q_start q_step q_accept σ x h₁ h₂ h₃ =>


            case cons σ tail _ =>
                absurd hx
                push_neg
                intro q_start q_accept x' h_q_start h_q_accept h_x'
                intro h
                induction h
                case nil =>
                    simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff,
                      List.reduceOption_nil, List.nil_eq, reduceCtorEq, A]
                case cons q_start q_step q_accept σ x h₁ h₂ h₃ =>
                    exact h₁
    case plus =>
        sorry
    case comp =>
        sorry
    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry
