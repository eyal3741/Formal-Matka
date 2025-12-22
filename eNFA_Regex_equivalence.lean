import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
open Set

universe u v

variable {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]

-- def step_char (q : ℕ) (c : Option ℕ) : Finset ℕ := match q, c with
--     | (0 : ℕ), (100 : ℕ) => {1}
--     | (_ : ℕ), (_ : Option ℕ) => ∅

-- #eval (step_char 0 (some 10))
set_option diagnostics true

open Classical

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

    case char σ =>
        let A : εNFA alphabet ℕ := {
            start  := {0}
            accept := {1}
            step   := fun q a => match q, a with -- WTF???
                | (0 : ℕ), (some σ) => {1}
                | (_ : ℕ), (_ : Option alphabet) => ∅
        }
        use A

        simp only [RegularExpression.matches'_char, @Language.ext_iff]
        intro x
        rw [@mem_singleton_iff, A.mem_accepts_iff_exists_path]

        constructor
        case mp =>
            intro hx
            use 0, 1, [σ]
            exact ⟨ rfl, rfl, id (Eq.symm hx), εNFA.IsPath.singleton A rfl ⟩

        case mpr =>
            -- TODO!!!!!!!!!!!
            rintro ⟨ q_start, q_accept, x', h_q_start, h_q_accept, h_x', h_ispath ⟩

            cases h_ispath
            case nil =>
                subst h_x'
                simp_all only [mem_singleton_iff, zero_ne_one, A]
            case cons t c y _ h_step =>
                cases c
                case none => sorry
                case some c h_some =>
                    have h_step_empty: A.step q_start c = ∅ := by

                        simp_rw[A]
                        by_cases c = σ
                        case pos => sorry
                        case neg  h_neq_σ =>
                            rw[← h_neq_σ]

            if h_empty: x' = [] then
                absurd h_ispath
                intro _
                subst h_empty h_x'
                simp_all only [mem_singleton_iff, εNFA.isPath_nil, zero_ne_one, A]
            else if h_σ: x' = [σ] then
                subst h_x' h_σ
                simp_all only [mem_singleton_iff, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil, εNFA.isPath_singleton, List.cons_ne_self, not_false_eq_true,
                  List.reduceOption_cons_of_some, List.reduceOption_nil, A]
            else
                simp at h_σ
                push_neg at h_σ
                absurd h_ispath
                intro _


                sorry

            induction h_ispath
            case nil q =>
                have h_0_acc : 0 ∉ A.accept := by exact of_decide_eq_false rfl
                have : q ∉ A.accept := by exact Eq.mpr_not (congrArg (Membership.mem A.accept) h_q_start) h_0_acc
                contradiction
            case cons t s u c tail h_step h_ispath _ =>

                by_cases tail = []
                case pos h_empty_tail =>
                    by_cases c = σ
                    case pos h_c_eq_σ => -- Only true case
                        subst h_empty_tail h_x' h_c_eq_σ
                        simp_all only [mem_singleton_iff, εNFA.isPath_nil, List.reduceOption_cons_of_some,
                          List.reduceOption_nil, one_ne_zero, implies_true, List.ne_cons_self, imp_self, A]
                    case neg h_c_neq_σ =>
                        push_neg at h_c_neq_σ
                        have h_step_empty: A.step s c = ∅ := by
                            simp_rw[A]
                            match _:s, hc:c with
                            | 0, .(σ) => sorry



                        subst h_empty_tail h_x'
                        simp_all only [mem_singleton_iff, ne_eq, singleton_ne_empty, A]

                case neg h_nonempty_tail =>
                    push_neg at h_nonempty_tail
                    absurd h_ispath

    case plus r₁ r₂ h_r₁ h_r₂ =>
        obtain ⟨ A₁, hA₁ ⟩ := h_r₁
        obtain ⟨ A₂, hA₂ ⟩ := h_r₂

        let A : εNFA alphabet ℕ := {
            start  := { 2*q' | q' ∈ A₁.start  } ∪ { 2*q' + 1 | q' ∈ A₂.start  }
            accept := { 2*q' | q' ∈ A₁.accept } ∪ { 2*q' + 1 | q' ∈ A₂.accept }
            step   := fun q c => match (q % 2), c with
                | 0, _ => {2*q' | q' ∈ (A₁.step (q/2) c) }
                | 1, _ => {2*q' | q' ∈ (A₂.step ((q-1)/2) c) }
                | _, _ => ∅
        }
        use A

        simp [RegularExpression.plus]
        rw [hA₁, hA₂, @Language.add_def, @Language.ext_iff]
        intro x
        constructor
        case mp =>
            intro h
            cases h
            case inl h_in_A₁ =>
                sorry -- STEPPPPP
            case inr h_in_A₂ =>
                sorry -- STEPPPPP
        case mpr =>
            intro h_in_A
            unfold εNFA.accepts at h_in_A
            obtain ⟨ qf, ⟨ h_qf_accept, h_qf_eval ⟩ ⟩ := h_in_A
            by_cases (qf % 2) = 0
            case pos =>
                left
                let qf_A₁ := (qf/2)
                have h_qf_accept : qf_A₁ ∈ A₁.accept := by
                    sorry
                have h_qf_eval : qf_A₁ ∈ A₁.eval x := by
                    sorry
                unfold εNFA.accepts
                simp only [mem_setOf_eq]
                exact Filter.frequently_principal.mp fun a => a h_qf_accept h_qf_eval
            case neg =>
                right
                let qf_A₂ := ((qf-1)/2)
                have h_qf_accept : qf_A₂ ∈ A₂.accept := by
                    sorry
                have h_qf_eval : qf_A₂ ∈ A₂.eval x := by
                    sorry
                unfold εNFA.accepts
                simp only [mem_setOf_eq]
                exact Filter.frequently_principal.mp fun a => a h_qf_accept h_qf_eval

    case comp r₁ r₂ h_r₁ h_r₂ =>
        obtain ⟨ A₁, hA₁ ⟩ := h_r₁
        obtain ⟨ A₂, hA₂ ⟩ := h_r₂

        let A₁' : εNFA alphabet ℕ := {
            start  := { 2*q' | q' ∈ A₁.start  }
            accept := { 2*q' | q' ∈ A₁.accept }
            step   := fun q c => match (q % 2), c with
                | 0, _ => {2*q' | q' ∈ (A₁.step (q/2) c) }
                | _, _ => ∅
        }
        let A₂' : εNFA alphabet ℕ := {
            start  := { 2*q' + 1 | q' ∈ A₂.start  }
            accept := { 2*q' + 1 | q' ∈ A₂.accept }
            step   := fun q c => match (q % 2), c with
                | 1, _ => {2*q' + 1 | q' ∈ (A₂.step (q/2) c) }
                | _, _ => ∅
        }

        have : (w : List alphabet) → w ∈ A₁.accepts ↔ w ∈ A₁'.accepts := by
            sorry


        let A : εNFA alphabet ℕ := {
            start  := A₁'.start
            accept := A₂'.accept
            step   := fun q c => match (q % 2), c with
                | 0, none =>
                    if (q ∈ A₁'.accept) then
                        A₁'.step q c ∪ A₂'.start
                    else
                        A₁'.step q c
                | 0, _ => A₁'.step q c
                | 1, _ => A₂'.step q c
                | _, _ => ∅
        }


        use A

        simp [RegularExpression.comp]
        rw [hA₁, hA₂, @Language.mul_def, @Language.ext_iff]
        intro x
        constructor
        case mp =>
            intro h
            rw[image2] at h
            obtain ⟨ x₁, h_x₁, x₂, h_x₂, h_comp ⟩ := h
            rw [A₁.mem_accepts_iff_exists_path] at h_x₁
            rw [A₂.mem_accepts_iff_exists_path] at h_x₂
            obtain ⟨ qs₁, qf₁, x₁', h_qs₁, h_qf₁, h_x₁', h_ispath1 ⟩ := h_x₁
            obtain ⟨ qs₂, qf₂, x₂', h_qs₂, h_qf₂, h_x₂', h_ispath2 ⟩ := h_x₂
            have h_connect_A₁_A₂ : A.IsPath (2*qf₁) (2*qs₂ + 1) [] := by
                sorry

            rw [A.mem_accepts_iff_exists_path]
            use (qs₁*2), (qf₂*2 + 1), (x₁' ++ x₂')
        case mpr =>
            sorry



    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry


def g (xs ys : List Nat) : Nat :=
    match xs, ys with
    | [a, b], _ => a+b+1
    | _, [b, c] => b+1
    | _, _ => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
    simp [g] at h;
    split at h
    simp +arith at h
