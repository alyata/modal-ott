Require Import List.
Import ListNotations.
Require Import BirkStar.birk_star.
Require Import Utf8.

Definition x := t_Var 0.
Definition y := t_Var 1.
Definition z := t_Var 2.

Definition x' := 0.
Definition y' := 1.
Definition z' := 2.

Definition A := T_Var 0.
Definition B := T_Var 1.
Definition C := T_Var 2.

Lemma example_typing: type_of_term [Some (x', A)] x A.
Proof.
apply term_var.
unfold C_in.
exists C_nil.
exists C_nil.
simpl.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Defined.

Lemma example_typing2: type_of_term [] 
  (t_Lam x' (t_Lam y' (t_Var y'))) (T_Fun x' A (T_Fun y' B B)).
Proof.
apply pi_intro.
{ apply pi_form. apply type_var. apply pi_form. apply type_var. apply type_var. }
apply pi_intro.
{ apply pi_form. apply type_var. apply type_var. }
apply term_var.
unfold C_in.
exists C_nil.
exists [Some (x', A)].
simpl.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Defined.

Lemma axiom_T: type_of_term [] (t_Lam x' (t_Open x)) (T_Fun x' (T_Box A) A).
Proof.
apply pi_intro.
{ apply pi_form. apply box_form. apply type_var. apply type_var. }
apply box_elim.
{ apply type_var. }
apply term_var.
unfold C_unlock.
unfold C_in.
simpl.
exists C_nil.
exists C_nil.
split.
{ auto. }
split.
{ intro. destruct H. exact H. }
{ auto. }
Defined.