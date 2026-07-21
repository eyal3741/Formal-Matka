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
set_option linter.unusedVariables false

------------------------------------
---------- Helpfull tools ----------
------------------------------------

namespace εNFA

-----------------------------------------
---------- Automata Path Tools ----------
-----------------------------------------

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s t u : σ} {a : α}

@[simp]
def Path.append {M : εNFA α σ} {qs qf t : σ} {x y : List (Option α)} :
    (path_y : M.Path qs t y) → (path_x : M.Path t qf x) → M.Path qs qf (y ++ x)
  | Path.nil _, p => p
  | Path.cons u _ _ c tail_y h_step path_tail, p => Path.cons u qs qf c (tail_y ++ x) h_step (Path.append path_tail p)

infixl:65 " ++ " => Path.append

def reverse (M : εNFA α σ) : (εNFA α σ) := {
    start  := M.accept
    accept := M.start
    step   := fun q c => { q' | q ∈ M.step q' c}
}

lemma dec_eq_nat_to_dec_eq :
    (instDecidableEqNat : DecidableEq ℕ) = Classical.decEq ℕ := by
    apply Subsingleton.elim

lemma reverse_of_reverse_rfl (M : εNFA α σ) : M.reverse.reverse = M := by
    simp [εNFA.reverse]

lemma List.reverse_of_reverse_rfl (L : List (Option α)) : L.reverse.reverse = L := by
    simp

def Path.reverse {M : εNFA α σ} {s u : σ} {x : List (Option α)} :
    (path : M.Path s u x) → M.reverse.Path u s x.reverse
  | Path.nil s => Path.nil s
  | Path.cons t s u c tail h_step p => by
        simp
        replace h_step : s ∈ M.reverse.step t c := by simp [εNFA.reverse, h_step]
        let p_c : M.reverse.Path t s [c] := (@Path.cons α σ M.reverse) s t s c [] h_step (@Path.nil α σ M.reverse s)
        use p.reverse ++ p_c

-- lemma path_reverse_of_reverse_rfl {M : εNFA α σ} {s u : σ} {x : List (Option α)} (path : M.Path s u x) :
--     path = (List.reverse_of_reverse_rfl x)▸(reverse_of_reverse_rfl M)▸path.reverse.reverse := by
--     induction path
--     case nil s => simp [Path.reverse]
--     case cons p ih =>
--         simp
--         sorry
--         -- Maybe not needed, don't solve yet




lemma path_append_cons_nil {M : εNFA α σ} {qs qf t : σ} {c : Option α} {x : List (Option α)}
    { h_step : t ∈ M.step qs c } { p : M.Path t qf x } { path_nil_qf : M.Path qf qf []} :
    (List.append_nil (c :: x))▸(Path.cons t qs qf c (x ++ []) h_step (p ++ path_nil_qf)) =
    (Path.cons t qs qf c x h_step ((List.append_nil x)▸(p ++ path_nil_qf))) := by

    induction p generalizing c qs
    case nil => simp
    case cons t' qs' qf' c' tail' h_step' p' ih =>
        replace ih := @ih qs' c' h_step' (Path.nil qf')
        sorry

lemma path_append_nil {M : εNFA α σ} {s u : σ} {x : List (Option α)} (path : M.Path s u x) :
    path = (List.append_nil x)▸(path ++ Path.nil u) := by
    induction path
    case nil => simp
    case cons t s u c tail h_step p ih =>
        have : (List.append_nil (c :: tail)) ▸ (Path.cons t s u c tail h_step p ++ Path.nil u) =
                (Path.cons t s u c tail h_step ((List.append_nil tail)▸(p ++ Path.nil u))) := by
            apply path_append_cons_nil

        rw [this]
        simp
        exact ih


lemma path_append_cons_assoc {M : εNFA α σ} {qs qf t s : σ} {c : Option α} {x₁ x₂ : List (Option α)}
    {h_step₁ : t ∈ M.step qs c} {p₁ : M.Path t s x₁} {path₂ : M.Path s qf x₂} :
    Path.cons t qs qf c (x₁ ++ x₂) h_step₁ (p₁ ++ path₂) =
    ((Path.cons t qs s c x₁ h_step₁ p₁) ++ path₂) := by
    simp only [Path.append]

-- lemma path_append_assoc {M : εNFA α σ} {q₁ q₂ q₃ q₄ : σ} {x₁ x₂ x₃ : List (Option α)}
--     {path₁ : M.Path q₁ q₂ x₁} {path₂ : M.Path q₂ q₃ x₂} {path₃ : M.Path q₃ q₄ x₃} :
--     (path₁ ++ path₂) ++ path₃ = ((List.append_assoc x₁ x₂ x₃)▸(path₁ ++ (path₂ ++ path₃))) := by
--     induction path₁
--     case nil =>
--         induction path₂
--         case nil => simp
--         case cons p ih => simp
--     case cons t₁ q₁ q₂ c₁ tail₁ h_step₁ p₁ ih₁ =>
--         replace ih₁ := @ih₁ path₂
--         induction path₂
--         case nil q =>
--             simp at ih₁
--             let := (List.append_assoc tail₁ [] x₃) ▸ (p₁ ++ (Path.nil q ++ path₃))
--             -- have : ((List.append_assoc tail₁ [] x₃) ▸ ((Path.cons t₁ q₁ q c₁ tail₁ h_step₁ p₁) ++ (Path.nil q ++ path₃))) =
--             --      (Path.cons t₁ q₁ q₄ c₁ (tail₁ ++ [] ++ x₃) h_step₁ ((List.append_assoc tail₁ [] x₃) ▸ (p₁ ++ (Path.nil q ++ path₃)))) := by
--             --     sorry
--             -- rw [← this]
--             --     -- path_append_cons_assoc
--             -- rw [← path_append_cons_assoc]
--             -- rw [← path_append_cons_assoc]
--             -- rw [← path_append_cons_assoc]
--             -- simp [ih₁]
--             sorry
--         case cons =>
--             simp
--             sorry

-- lemma path_append_assoc2 {M : εNFA α σ} {q₁ q₂ q₃ q₄ : σ} {x₁ x₂ x₃ : List (Option α)}
--     {path₁ : M.Path q₁ q₂ x₁} {path₂ : M.Path q₂ q₃ x₂} {path₃ : M.Path q₃ q₄ x₃} :
--     ((List.append_assoc x₁ x₂ x₃)▸((path₁ ++ path₂) ++ path₃)) = (path₁ ++ (path₂ ++ path₃)) := by
--     induction path₁
--     case nil =>
--         induction path₂
--         case nil => simp
--         case cons p ih => simp
--     case cons t₁ q₁ q₂ c₁ tail₁ h_step₁ p₁ ih₁ =>
--         replace ih₁ := @ih₁ path₂
--         induction path₂
--         case nil q =>
--             simp at ih₁
--             let := (List.append_assoc tail₁ [] x₃) ▸ (p₁ ++ (Path.nil q ++ path₃))
--             -- have : ((List.append_assoc tail₁ [] x₃) ▸ ((Path.cons t₁ q₁ q c₁ tail₁ h_step₁ p₁) ++ (Path.nil q ++ path₃))) =
--             --      (Path.cons t₁ q₁ q₄ c₁ (tail₁ ++ [] ++ x₃) h_step₁ ((List.append_assoc tail₁ [] x₃) ▸ (p₁ ++ (Path.nil q ++ path₃)))) := by
--             --     sorry
--             -- rw [← this]
--             --     -- path_append_cons_assoc
--             -- rw [← path_append_cons_assoc]
--             -- rw [← path_append_cons_assoc]
--             -- rw [← path_append_cons_assoc]
--             -- simp [ih₁]
--             sorry
--         case cons =>
--             simp
--             sorry

structure Path_contains {M : εNFA α σ} {qs qf s t : σ} {word_qs_qf word_s_t : List (Option α)}
    (path_qs_qf : M.Path qs qf word_qs_qf) (path_s_t : M.Path s t word_s_t) where
    word_qs_s : List (Option α)
    word_t_qf : List (Option α)
    path_qs_s : M.Path qs s word_qs_s
    path_t_qf : M.Path t qf word_t_qf
    h_word : word_qs_qf = word_qs_s ++ word_s_t ++ word_t_qf
    h_path : path_qs_qf = h_word▸(path_qs_s ++ path_s_t ++ path_t_qf)

def Path.contains {M : εNFA α σ} {qs qf s t : σ} {word_qs_qf word_s_t : List (Option α)}
    (path_qs_qf : M.Path qs qf word_qs_qf) (path_s_t : M.Path s t word_s_t) :=
    ∃ (_ : Path_contains path_qs_qf path_s_t), True

lemma path_cons_contains_tail {M : εNFA α σ} {qs qf t : σ} {c : Option α} {x : List (Option α)}
    {p : M.Path t qf x} {h_step : t ∈ M.step qs c} :
    (Path.cons t qs qf c x h_step p).contains p := by
    induction p generalizing c qs
    case nil t =>
        use {
            word_qs_s := [c]
            word_t_qf := []
            path_qs_s := Path.cons t qs t c [] h_step (Path.nil t)
            path_t_qf := Path.nil t
            h_word := by simp
            h_path := by simp
        }
    case cons t' t qf c' tail h_step' p' ih =>
        replace ih := @ih t c' h_step'
        use {
            word_qs_s := [c]
            word_t_qf := []
            path_qs_s := Path.cons t qs t c [] h_step (Path.nil t)
            path_t_qf := Path.nil qf
            h_word := by simp
            h_path := by apply path_append_nil
        }

lemma path_contains_reflex {M : εNFA α σ} {s₁ t₁ : σ} {word₁ : List (Option α)}
    (path₁ : M.Path s₁ t₁ word₁):
    path₁.contains path₁ := by
        use {
            word_qs_s := []
            word_t_qf := []
            path_qs_s := Path.nil s₁
            path_t_qf := Path.nil t₁
            h_word := by simp
            h_path := by
                simp
                apply path_append_nil
        }

lemma path_contains_trans {M : εNFA α σ} {s₁ t₁ s₂ t₂ s₃ t₃ : σ} {word₁ word₂ word₃ : List (Option α)}
    (path₁ : M.Path s₁ t₁ word₁) (path₂ : M.Path s₂ t₂ word₂) (path₃ : M.Path s₃ t₃ word₃) :
    path₁.contains path₂ ∧ path₂.contains path₃ → path₁.contains path₃ := by
    rintro ⟨ h₁, h₂ ⟩
    obtain ⟨ h₁ ⟩ := h₁
    obtain ⟨ h₂ ⟩ := h₂
    obtain ⟨ word_qs₁_qs₂, word_qf₂_qf₁,
             path_qs₁_qs₂, path_qf₂_qf₁,
             h_word₁₂, h_path₁₂ ⟩ := h₁
    obtain ⟨ word_qs₂_qs₃, word_qf₃_qf₂,
             path_qs₂_qs₃, path_qf₃_qf₂,
             h_word₂₃, h_path₂₃ ⟩ := h₂
    use {
        word_qs_s := word_qs₁_qs₂ ++ word_qs₂_qs₃
        word_t_qf := word_qf₃_qf₂ ++ word_qf₂_qf₁
        path_qs_s := path_qs₁_qs₂ ++ path_qs₂_qs₃
        path_t_qf := path_qf₃_qf₂ ++ path_qf₂_qf₁
        h_word := by subst word₂; simp [h_word₁₂]
        h_path := (by
            have h_word : word₁ = word_qs₁_qs₂ ++ word_qs₂_qs₃ ++ word₃ ++ (word_qf₃_qf₂ ++ word_qf₂_qf₁) := by
                subst word₂
                simp [h_word₁₂]

            subst path₁ path₂ word₂ word₁
            -- TODO
            sorry
        )
    }

lemma supp_of_path_append {M : εNFA α σ} {qs qf t : σ} {x₁ x₂: List (Option α)}
    (path₁: M.Path qs t x₁) (path₂: M.Path t qf x₂) (q : σ) :
    q ∈ (path₁ ++ path₂).supp ↔ q ∈ path₁.supp ∨ q ∈ path₂.supp := by
    constructor
    case mp =>
        intro h_q_in_append
        induction path₁
        case nil =>
            simp at h_q_in_append ⊢
            exact h_q_in_append
        case cons t' qs t c h_step path_tail₁ h_induction =>
            simp at h_q_in_append
            cases h_q_in_append
            case inl h_q_t₁ =>
                left
                simp
                left
                exact h_q_t₁
            case inr h =>
                simp
                replace h_induction := h_induction path₂ h
                cases h_induction
                case inl h => simp [h]
                case inr h => simp [h]
    case mpr =>
        intro h
        induction path₁
        case nil =>
            simp at h ⊢
            exact h
        case cons t' qs t c h_step path_tail₁ h_induction =>
            simp at h ⊢
            rw [or_assoc] at h
            cases h
            case inl h => left;  exact h
            case inr h => right; exact h_induction path₂ h

lemma supp_of_path_contains {M : εNFA α σ} {qs qf s t : σ} {word_qs_qf word_s_t : List (Option α)}
    (path_qs_qf : M.Path qs qf word_qs_qf) (path_s_t : M.Path s t word_s_t) (q : σ):
    path_qs_qf.contains path_s_t → q ∈ path_s_t.supp → q ∈ path_qs_qf.supp := by
    intro h h_q
    obtain ⟨ h ⟩ := h
    obtain ⟨ word_qs_s, word_t_qf,
             path_qs_s, path_t_qf,
             h_word, h_path ⟩ := h

    induction path_qs_s generalizing word_qs_qf word_s_t
    case nil =>
        simp at h_path
        have := (supp_of_path_append path_s_t path_t_qf q).mpr (by left; exact h_q)
        subst h_word h_path
        simp [this]
    case cons p ih =>
        simp at h_path
        subst h_word h_path
        simp
        right
        exact ih (p ++ path_s_t ++ path_t_qf) path_s_t h_q rfl rfl

def Path.suppAfterStart [DecidableEq σ] {M : εNFA α σ} {s t : σ} {x : List (Option α)} :
    M.Path s t x → Finset σ
  | Path.nil _ => ∅
  | Path.cons _ _ _ _ _ _ p => p.supp

lemma supp_after_start_of_path_append {M : εNFA α σ} {qs qf t} {x₁ x₂: List (Option α)}
    (path₁: M.Path qs t x₁) (path₂: M.Path t qf x₂) (q : σ) : q ∈ (path₁ ++ path₂).suppAfterStart →
    q ∈ path₁.suppAfterStart ∨ q ∈ path₂.supp := by
    intro h_q_in_append
    cases path₁
    case nil =>
        right
        simp [Path.suppAfterStart] at h_q_in_append
        split at h_q_in_append
        case h_1 => trivial
        case h_2 => simp [h_q_in_append]

    case cons t' c tail₁ path_tail₁=>
        simp at h_q_in_append
        exact (supp_of_path_append path_tail₁ path₂ q).mp h_q_in_append

lemma if_supp_after_start_then_supp {M : εNFA α σ} {s t : σ} {x: List (Option α)}
    (path: M.Path s t x) (q : σ): q ∈ path.suppAfterStart → q ∈ path.supp := by
    intro h_q
    cases path
    case nil  => simp [Path.suppAfterStart] at h_q
    case cons =>
        simp [Path.suppAfterStart] at h_q ⊢
        right
        exact h_q

lemma if_supp_then_start_or_supp_after_start {M : εNFA α σ} {s t : σ} {x: List (Option α)}
    (path: M.Path s t x) (q : σ) : q ∈ path.supp → q = s ∨ q ∈ path.suppAfterStart := by
    intro h_q
    unfold Path.supp at h_q
    split at h_q
    case h_1 => contradiction
    case h_2 =>
        simp at h_q
        cases h_q
        case inl h => left; exact h
        case inr h =>
            right
            simp [Path.suppAfterStart]
            exact h

lemma if_q_in_supp {A : εNFA α σ} {s t q : σ} {x: List (Option α)} (path : A.Path s t x)
      (hq : q ∈ path.supp):  q = s ∨ q ∈ path.suppAfterStart := by
       cases path <;> simp_all [Path.suppAfterStart]


---------------------------------------
---------- Automata Doubling ----------
---------------------------------------


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
    A'.is_0mod2 ∨ A'.is_1mod2 → Nonempty (A'.Path q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := by
    intro h_mod2_eNFA h_path
    obtain ⟨ h_path ⟩ := h_path
    induction h_path with
    | nil _ => rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        have := if_mod2_step_is_same_mod2 A' q₁ t c h_mod2_eNFA h_step
        omega

lemma if_0mod2_path_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_0mod2) (q₁ q₂ : ℕ) (x : List (Option α)) :
    Nonempty (A'.Path q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inl hA')

lemma if_1mod2_path_is_same_mod2 (A' : εNFA α ℕ) (hA': A'.is_1mod2) (q₁ q₂ : ℕ) (x : List (Option α)) :
    Nonempty (A'.Path q₁ q₂ x) → (q₁ % 2 = q₂ % 2) := if_mod2_path_is_same_mod2 A' q₁ q₂ x (Or.inr hA')

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
     (Nonempty (A.Path qs qf y) ↔ Nonempty (A'.Path qs' qf' y)) := by

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
        obtain ⟨ h_path_in_A ⟩ := h_path_in_A
        induction h_path_in_A generalizing qs'
        case nil => simp [εNFA.isPath_nil]; omega
        case cons t q₁ q₂ σ tail h_step h_path h_induction =>
            let t' := 2 * t + s
            subst s
            have h_t'_step: t' ∈ A'.step qs' σ := by simp_all [t', to_0mod2, to_1mod2]
            have h_t'_path: Nonempty (A'.Path t' qf' tail) := by simp_all [t']
            apply A'.isPath_singleton.mpr at h_t'_step
            exact A'.isPath_append.mpr ⟨ t', h_t'_step, h_t'_path ⟩
    case inl.mpr | inr.mpr =>
        intro h_path_in_A'
        obtain ⟨ h_path_in_A' ⟩ := h_path_in_A'
        induction h_path_in_A' generalizing qs
        case nil => simp [εNFA.isPath_nil]; omega
        case cons t' q₁' q₂' σ tail h_step h_path h_induction =>
            let t := (t' - s) / 2

            have h_t'_0mod2: t' % 2 = s := by
                try exact (if_0mod2_step_is_0mod2 A' h_A'_mod2 q₁' t' σ h_step).right
                try exact (if_1mod2_step_is_1mod2 A' h_A'_mod2 q₁' t' σ h_step).right
            have h_t'_2t: t' = 2 * t + s := by omega

            subst s
            have h_t_step: t ∈ A.step qs σ := by simp_all [to_0mod2, to_1mod2]
            have h_t_path: Nonempty (A.Path t qf tail) := by simp_all
            apply A.isPath_singleton.mpr at h_t_step
            exact A.isPath_append.mpr ⟨ t, h_t_step, h_t_path ⟩

lemma path_iff_0mod2_path (A : εNFA α ℕ) (A' : εNFA α ℕ) (qs qf qs' qf' : ℕ) (y : List (Option α))
    (hA': A' = to_0mod2 A) (h_qs': qs' = 2 * qs) (h_qf': qf' = 2 * qf) :
    Nonempty (A.Path qs qf y) ↔ Nonempty (A'.Path qs' qf' y) :=
    (path_iff_mod2_path A A' qs qf qs' qf' y (Or.inl ⟨ hA', h_qs', h_qf' ⟩))

lemma path_iff_1mod2_path (A : εNFA α ℕ) (A' : εNFA α ℕ) (qs qf qs' qf' : ℕ) (y : List (Option α))
    (hA': A' = to_1mod2 A) (h_qs': qs' = 2 * qs + 1) (h_qf': qf' = 2 * qf + 1) :
    Nonempty (A.Path qs qf y) ↔ Nonempty (A'.Path qs' qf' y) :=
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
        have h_iff_path : Nonempty (A.Path qs qf x') ↔ Nonempty (A'.Path qs' qf' x') := by
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
        have h_iff_path : Nonempty (A.Path qs qf x') ↔ Nonempty (A'.Path qs' qf' x') := by
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inl ⟨ hA', h_qs'_2qs, h_qf'_2qf ⟩)
            try exact path_iff_mod2_path A A' qs qf qs' qf' x' (Or.inr ⟨ hA', h_qs'_2qs, h_qf'_2qf ⟩)

        use qs, qf, x'
        exact ⟨ h_qs, h_qf, h_x', h_iff_path.mpr h_path_in_A' ⟩

lemma accepts_iff_0mod2_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = to_0mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inl hA')

lemma accepts_iff_1mod2_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = to_1mod2 A) :
    A.accepts = A'.accepts := accepts_iff_mod2_accepts A A' (Or.inr hA')


---------------------------------------
---------- General Automata  ----------
---------------------------------------

def contains (A : εNFA α ℕ) (A' : εNFA α ℕ) :=
    ∀ (q : ℕ), ∀ (σ: Option α), A'.step q σ ⊆ A.step q σ

lemma path_if_contains (A : εNFA α ℕ) (A' : εNFA α ℕ) (h_contains: A.contains A')
    (q₁ q₂ : ℕ) (x : List (Option α)) :
    Nonempty (A'.Path q₁ q₂ x) → Nonempty (A.Path q₁ q₂ x) := by
    intro h_path_in_A'
    unfold contains at h_contains
    obtain ⟨ h_path_in_A' ⟩ := h_path_in_A'
    induction h_path_in_A' with
    | nil q => exact A.isPath_nil.mpr rfl
    | cons t q₁ q₂ c tail h_step h_rest h_induction =>
        replace h_step : t ∈ A.step q₁ c := by
            have := h_contains q₁ c
            exact mem_of_subset_of_mem (h_contains q₁ c) h_step
        apply A.isPath_singleton.mpr at h_step
        exact A.isPath_append.mpr ⟨ t, h_step, h_induction ⟩


lemma suppAfterStart_of_path_contains
    {A : εNFA α σ}
    {s₁ t₁ s₂ t₂ q : σ}
    {x₁ x₂ : List (Option α)}
    (outer : A.Path s₁ t₁ x₁)
    (inner : A.Path s₂ t₂ x₂) :
    outer.contains inner →
    q ∈ inner.suppAfterStart →
    q ∈ outer.suppAfterStart := by
        intro h_contains hq
        obtain ⟨h_data,_⟩  := h_contains
        obtain ⟨word_prefix, word_suffix, pre ,suffix, h_word, h_path⟩ := h_data
        induction pre generalizing x₁
        case nil =>
            simp at h_path
            subst h_word h_path
            cases inner with
            | nil =>
                simp [Path.suppAfterStart] at hq
            | cons next start finish c tail hstep p =>
                simp [Path.suppAfterStart] at hq ⊢
                exact
                    (supp_of_path_append p suffix q).mpr
                    (Or.inl hq)
        case cons next start finish c tail h_step pre_tail ih =>
            simp at h_path
            subst h_word h_path
            have q_in_supp: q ∈ inner.supp :=
                (if_supp_after_start_then_supp inner q hq)


            have q_in_pre_inner : q ∈ (pre_tail ++ inner).supp :=
                 (supp_of_path_append pre_tail inner q).mpr
                    (Or.inr q_in_supp)

            simp [Path.suppAfterStart]
            exact
                (supp_of_path_append (pre_tail ++ inner) suffix q).mpr
                (Or.inl q_in_pre_inner)






lemma dont_go_nowhere (A : εNFA α ℕ) (hAempty : A.start = ∅) :
    A.accepts = 0 := by
  rw [@Language.ext_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨s₁, _, _, h_s₁, _⟩ :=
      A.mem_accepts_iff_exists_path.mp hx
    simp [hAempty] at h_s₁
  · intro hx
    exact (Language.notMem_zero x hx).elim

end εNFA

variable {α : Type u} [Fintype α] [DecidableEq α]


def SingularStart  := 2
def SingularAccept := 0

def to_singular (A : εNFA α ℕ) : εNFA α ℕ := {
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
    : εNFA α ℕ
}

lemma to_singular_contains (A: εNFA α ℕ): (to_singular A).contains A.to_1mod2 := by
    unfold εNFA.contains
    intro q σ
    simp [to_singular, εNFA.to_1mod2]
    split_ifs
    all_goals simp only [subset_insert, subset_refl, empty_subset]


lemma accepts_iff_singular_accepts (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = to_singular A) :
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

        have hfirst: Nonempty (A'.Path SingularStart (2*s + 1) [none]) := by
            subst hA'
            simp [to_singular, εNFA.to_1mod2, hs, SingularStart]

        have hlast: Nonempty (A'.Path (2*a + 1) SingularAccept [none]) := by
            subst hA'
            simp [to_singular, εNFA.to_1mod2, ha, SingularAccept]

        have hmiddle: Nonempty (A'.Path (2*s + 1) (2*a + 1) x') := by
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

        obtain ⟨ hA'path ⟩ := hA'path
        cases hA'path
        case cons s σ y' h_step h_path_s_accept =>
            simp [hA', to_singular, SingularStart, SingularAccept] at h_step
            obtain ⟨ ⟨ _, h_σ_none ⟩ , h_s_start ⟩ := h_step

            have first_transition_is_to_odd_state: s % 2 = 1:=
                A.to_1mod2.if_1mod2_qs_is_1mod2 ⟨A, rfl⟩ s h_s_start

            have h_temp: ∀ (q q': ℕ) (σ : Option α), (q % 2 = 1) → (q' % 2 = 1) → (q' ∈ A'.step q σ )
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

            have path_to_singular_accept (q : ℕ) (y : List (Option α))
                (h_q_1mod2: q % 2 = 1) (h_path : Nonempty (A'.Path q SingularAccept y)) :
                ∃ qf mid, qf ∈ (A.to_1mod2).accept ∧ (Nonempty (A.to_1mod2.Path q qf mid)) ∧ y = mid ++ [none] := by
                induction y generalizing q
                case nil =>
                    simp only [εNFA.isPath_nil] at h_path
                    simp [SingularAccept] at h_path
                    omega
                case cons c tail h_induction =>
                    obtain ⟨ h_path ⟩ := h_path
                    cases h_path
                    case cons t h_step h_path =>
                        by_cases tail = []
                        case pos h_tail_empty =>
                            clear h_induction
                            subst h_tail_empty
                            replace h_path : Nonempty (A'.Path t SingularAccept []) := by use h_path
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

                            replace h_path: Nonempty (A'.Path t SingularAccept tail) := by use h_path
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

            replace h_path_s_accept: Nonempty (A'.Path s SingularAccept y') := by use h_path_s_accept
            obtain ⟨qf, mid, h_qf_accept, h_mid_path, h_y'_eq⟩ :=
              path_to_singular_accept (q := s) (y := y') first_transition_is_to_odd_state h_path_s_accept

            have h_mid : mid.reduceOption = x := by
                simp only [h_y'_eq, List.reduceOption_cons_of_none, List.reduceOption_append,
                  List.reduceOption_nil, List.append_nil] at h_x'
                exact h_x'

            use s, qf, mid

def εNFA.max_reachable_node (A : εNFA α ℕ) (n : ℕ) :=
    (∃s₁: ℕ, ∃x: List (Option α), s₁ ∈ A.start ∧ Nonempty (A.Path s₁ n x))
    ∧
    ∀n': ℕ, (n' > n) → ¬(∃s₁: ℕ, ∃x: List (Option α), s₁ ∈ A.start ∧ Nonempty (A.Path s₁ n' x))

def εNFA.is_finite_automata (A : εNFA α ℕ) :=
    (A.start = ∅) ∨ (∃n: ℕ, A.max_reachable_node n)

lemma if_1mod2_max_reachable_is_1mod2 (A : εNFA α ℕ) (n: ℕ) (hA: A.is_1mod2) (h_n: A.max_reachable_node n) :
    n % 2 = 1 := by
    unfold εNFA.max_reachable_node at h_n
    obtain ⟨ ⟨ s, x, ⟨ h_s_start, h_path ⟩ ⟩, _ ⟩ := h_n
    apply A.if_1mod2_qs_is_1mod2 hA at h_s_start
    apply A.if_1mod2_path_is_same_mod2 hA s n x at h_path
    omega

lemma finite_iff_1mod2_is_finite (A : εNFA α ℕ) (A' : εNFA α ℕ) (hA': A' = A.to_1mod2) :
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
                    intro s' h_s' x
                    by_contra! h_A'_path

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
                    absurd h_path_A
                    simp only [not_isEmpty_of_nonempty, not_false_eq_true]

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
                intro s h_s x
                by_contra! h_path_A
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

lemma if_singular_1mod2_path (A A' : εNFA α ℕ) (qs qf : ℕ) (hA': A' = to_singular A)
    (h_qs: qs % 2 = 1) (h_qf: qf % 2 = 1) (x: List (Option α)):
    Nonempty (A'.Path qs qf x) ↔ Nonempty (A.to_1mod2.Path qs qf x) := by
    constructor
    case mp =>
        intro h_A'_path
        obtain ⟨ h_A'_path ⟩ := h_A'_path
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

                        have h_t_step :∀ (c: Option α), A'.step t c = ∅ := by
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
    (A A' : εNFA α ℕ) (q qf : ℕ) (y : List (Option α))
    (hA' : A' = to_singular A)
    (h_q_odd : q % 2 = 1)
    (h_qf_gt : qf > SingularStart)
    (h_path : Nonempty (A'.Path q qf y)) :
    qf % 2 = 1 := by
  obtain ⟨ h_path ⟩ := h_path
  induction h_path
  · omega
  · rename_i t q qf c tail h_step h_rest ih
    by_cases h_tail_empty : tail = []
    · subst h_tail_empty
      replace h_rest : Nonempty (A'.Path t qf []) := by use h_rest
      apply A'.isPath_nil.mp at h_rest

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

lemma finite_iff_to_singular_finite (A A' : εNFA α ℕ) (hA': A' = to_singular A):
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
                obtain ⟨ h ⟩ := h
                cases h
                case nil =>
                    contradiction
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
                    obtain ⟨ this ⟩ := this
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
                            replace h_path : Nonempty (A'.Path t' n' []) := by use h_path
                            simp [A'.isPath_nil] at h_path ⊢
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
                                        replace h_path : Nonempty (A'.Path t n' []) := by use h_path
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

                            replace h_path : Nonempty (A'.Path t' n' tail) := by use h_path
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

                    have h_not_reach : ¬ ∃ s₁ x, s₁ ∈ A.to_1mod2.start ∧ Nonempty (A.to_1mod2.Path s₁ n' x) := by
                        exact h_n_max n' (by omega)

                    rintro ⟨ q, x, h_q_start, h_A'_path ⟩
                    have h_q : q = SingularStart := by
                        simp [hA', to_singular] at h_q_start
                        exact h_q_start
                    subst h_q
                    obtain ⟨ h_A'_path ⟩ := h_A'_path
                    cases h_A'_path with
                    | nil =>
                        omega
                    | cons =>
                        rename_i t' σ tail hstep hpath
                        replace hpath : Nonempty (A'.Path t' n' tail) := by use hpath
                        have h_t_start : t' ∈ A.to_1mod2.start := by
                            simp [hA', to_singular, SingularStart] at hstep
                            exact hstep.2
                        have h_t_odd : t' % 2 = 1 :=
                            A.to_1mod2.if_1mod2_qs_is_1mod2 ⟨A, rfl⟩ t' h_t_start
                        have h_n'_odd : n' % 2 = 1 := by
                             exact singular_path_from_odd_ends_odd A A' t' n' tail hA' h_t_odd h_n' hpath
                        have h_path_1mod2 : Nonempty (A.to_1mod2.Path t' n' tail) :=
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
                ∀ k s x, s ∈ A.to_1mod2.start → Nonempty (A.to_1mod2.Path s k x) → k ≤ n := by
                    intro k s x h_s_start h_path_1mod2
                    by_contra h_not_le
                    have hk_gt : k > n := by omega
                    have h_step_from_singular : s ∈ A'.step SingularStart none := by
                        simp [hA', to_singular, SingularStart, h_s_start]
                    have h_singleton : Nonempty (A'.Path SingularStart s [none]) := by
                        apply A'.isPath_singleton.mpr
                        exact h_step_from_singular
                    have h_path_in_A' : Nonempty (A'.Path s k x) := by
                        exact A'.path_if_contains A.to_1mod2 h_A'_contains_A_1mod2 s k x h_path_1mod2
                    have h_reach_k_in_A' : Nonempty (A'.Path SingularStart k ([none] ++ x)) := by
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
                        Nonempty (A.to_1mod2.Path s₁ k x)

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
