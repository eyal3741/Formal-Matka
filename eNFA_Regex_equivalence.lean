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

        have accepts_non_empty : A.accept ∩ (A.eval []) ≠ ∅ := by
            unfold εNFA.eval εNFA.evalFrom
            simp
            rw [@singleton_inter_eq_empty]
            push_neg
            constructor
            exact rfl

        constructor
        case mp =>
            intro hx
            subst hx
            unfold εNFA.accepts
            simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff, exists_eq_left, A]
            exact accepts_non_empty
        case mpr =>
            intro hx

            induction x
            case nil => tauto
            case cons σ tail _ =>
                absurd hx
                rw[A.mem_accepts_iff_exists_path]
                push_neg
                intro q_start q_accept x' h_q_start h_q_accept h_x'
                intro h
                induction h
                case nil =>
                    simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff,
                      List.reduceOption_nil, List.nil_eq, reduceCtorEq, A]
                case cons q_start q_step q_accept σ x h₁ h₂ h₃ =>
                    exact h₁

                -- have h_empty_σ : A.evalFrom A.start [σ] = ∅ := by
                --     simp_all [A]
                --     ext x : 1
                --     simp_all only [εNFA.mem_stepSet_iff, mem_singleton_iff, εNFA.εClosure_empty, mem_empty_iff_false,
                --       and_false, exists_const, A]

                -- have h_empty_tail : A.evalFrom (A.evalFrom A.start [σ]) tail = ∅ := by
                --     rw[h_empty_σ]
                --     exact εNFA.evalFrom_empty A tail

                -- have h_eval : A.eval (σ :: tail) = A.evalFrom (A.evalFrom A.start [σ]) tail := by

                -- have h_empty_x : A.eval (σ :: tail) = ∅ := by


                --     sorry

                -- have h_empty_implies_not_accepted: ∀(x : List alphabet), A.eval x = ∅ → x ∉ A.accepts := by
                --     intro x
                --     rw[εNFA.accepts, εNFA.eval]
                --     intro h_x_empty
                --     have : ∀ S ∈ A.accept, S ∉ A.evalFrom A.start x := by
                --         exact fun S a => of_eq_false (congrFun h_x_empty S)

                --     have lean_is_stupid: ∀ S ∈ A.accept, S ∉ A.evalFrom A.start x → x ∉ {x | ∃ S ∈ A.accept, S ∈ A.evalFrom A.start x} := by
                --         simp only [mem_setOf_eq, not_exists, not_and, A]

                --     exact lean_is_stupid 0 rfl (this 0 rfl)

                -- exact h_empty_implies_not_accepted (σ :: tail) h_empty_x


    case char =>
        sorry
    case plus =>
        sorry
    case comp =>
        sorry
    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry
