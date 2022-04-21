Require Import List.
Import ListNotations.
Require Import BirkStar.birk_star.
Require Import Utf8.
Require Import Coq.Program.Equality.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma weakening:
∀ (t A B : term), ∀ (Γ Δ : context), ∀ (x : termvar), ∀ (ix : i),
type_of_term (Δ ++ Γ) t B
→ type_of_term Γ A (t_Univ ix)
→ type_of_term (Δ ++ (C_var (x, A) :: Γ)) t B.
Proof.
Admitted.

Lemma substitution_lemma: 
∀ (t u A B : term), ∀ (Γ Δ : context), ∀ (x : termvar),
type_of_term (Δ ++ (C_var (x, A) :: Γ)) t B 
→ type_of_term Γ u A
→ type_of_term ((subst_context [(x, u)] Δ) ++ Γ) (subst_term [(x, u)] t) (subst_term [(x, u)] B).
Proof.
  intros t u A B Γ Δ x ht hu.
  induction Δ.
  {
    simpl in ht.
    (* remember (C_var (x, A) :: Γ) as ΓΓ.
    generalize dependent Γ. *)
    induction ht.
    { admit. } { admit. }
    {(* unfold subst_context in IHht1, IHht2. simpl in IHht1, IHht2. *)
      apply pi_form. apply IHht1.
      set h := weakening x0 IHht2 IHht1.
      simpl in h.
      simpl.
      admit. (* I just needed to figure out what the IHs are for the pen & paper proof *)
    }
    {
      unfold subst_context in IHht. simpl in IHht.
    }
  }
Admitted.