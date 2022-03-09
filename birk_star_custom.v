Require Import List.
Import ListNotations.
Require Import BirkStar.birk_star.
Require Import Utf8.
Require Import Coq.Program.Equality.

Definition x := t_Var 0.
Definition y := t_Var 1.
Definition z := t_Var 2.

Definition x' := 0.
Definition y' := 1.
Definition z' := 2.

(* Let A B C represent arbitrary well-formed types. *)
Context {A B C : type}.
Context (hA : forall ctx, type_form ctx A).
Context (hB : forall ctx, type_form ctx B).
Context (hC : forall ctx, type_form ctx C).

Lemma example_typing: type_of_term [Some (x', A)] x A.
Proof.
apply term_var.
{ apply ctx_var. apply ctx_emp. apply hA.
}
unfold C_in.
exists C_nil.
exists C_nil.
simpl.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Qed.

Lemma example_typing2: type_of_term [] 
  (t_Lam x' (t_Lam y' (t_Var y'))) (T_Fun x' A (T_Fun y' B B)).
Proof.
apply pi_intro.
apply hA.
apply pi_intro.
apply hB.
apply term_var.
{ apply ctx_var. apply ctx_var. apply ctx_emp. apply hA. apply hB. }
unfold C_in.
exists C_nil.
exists [Some (x', A)].
simpl.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Qed.

Lemma axiom_T: type_of_term [] (t_Lam x' (t_Open x)) (T_Fun x' (T_Box A) A).
Proof.
apply pi_intro.
{ apply box_form. apply hA. }
apply box_elim.
{ apply hA. }
apply term_var.
unfold C_unlock.
unfold C_in.
simpl.
{ apply ctx_var. apply ctx_emp. apply box_form. apply hA. }
exists C_nil.
exists C_nil.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Qed.

Locate "~=".

(* Lemma ctx_form_cong_app {ctx1 ctx2 : context} 
: ctx_form (ctx1 ++ ctx2) <-> ctx_form ctx1 /\ ctx_form ctx2.
Proof.
  induction ctx1.
  { unfold app.
    split.
    { intro h. split. apply ctx_emp. apply h. }
    { intros (_, h). apply h. }
  }
  { simpl.
    destruct a.
    split.
    { intro h. inversion h. rewrite IHctx1 in H1. 
      destruct H1 as (Hctx1, Hctx2). split. apply ctx_var. }
  }

Admitted. *)

Theorem subst {ctx1 ctx2 : context} {t} {x} (h : type_of_term (ctx2 ++ ctx1) t B) 
: type_of_term (ctx2 ++ (C_var (x, A) :: ctx1)) t B.
Proof.
remember (ctx2 ++ ctx1) as ctx.
induction h.
{ apply nat_zero. 
  rewrite Heqctx in H.
  generalize dependent ctx1.
  induction ctx2.
  { intro ctx1. unfold app in H. unfold app. apply ctx_var. apply H. apply hA. }
  { simpl in H. simpl. destruct a.
    { destruct p. apply ctx_var. apply IHctx2.  } 
  }
  admit. (* Too lazy to prove, its obvious *) }
{ rewrite <-x. apply nat_succ. rewrite x. apply IHh. apply JMeq_refl. apply x. }
{ admit. }
{ apply term_var. admit. admit. (* Too lazy *) }
{ rewrite <-x. apply pi_intro. admit. admit. (* ??? genuinely can't do *) }
{ admit. (* pi_elim doesn't work for some reason *) }
{ rewrite <-x. apply box_intro. admit. (* too lazy *) }
{ apply box_elim. admit. (* Too lazy*) admit. (* not sure if I can do *) }
Admitted.