Require Import List.
Import ListNotations.
Require Import Ascii.

From Verbatim Require Import ltac.


Definition ascii2list (a : ascii) : list bool :=
  match a with
  | Ascii b b0 b1 b2 b3 b4 b5 b6 =>
    [b; b0; b1; b2; b3; b4; b5; b6]
  end.

Lemma ascii2list_eq : forall x y,
    x = y <-> ascii2list x = ascii2list y.
Proof.
  intros. split; intros.
  - subst. auto.
  - destruct x; destruct y. simpl in H.
    injection H. intros; subst; auto.
Qed.

Definition bool_order (b1 b2 : bool) : comparison :=
  match b1, b2 with
  | false, false => Eq
  | false, true => Lt
  | true, false => Gt
  | true, true => Eq
  end.

Lemma bool_order_eq : forall x y,
    bool_order x y = Eq <-> x = y.
Proof.
  destruct x; destruct y; split; intros; try(discriminate); auto.
Qed.

Lemma bool_order_eq' : forall x,
    bool_order x x = Eq.
Proof.
  intros. apply bool_order_eq. auto.
Qed.

Lemma bool_order_trans : forall c x y z,
    bool_order x y = c -> bool_order y z = c -> bool_order x z = c.
Proof.
  intros. destruct x; destruct y; destruct z; auto; simpl in *; subst; discriminate.
Qed.
  
Fixpoint bool_list_order (bs bs' : list bool) : comparison :=
  match bs, bs' with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | h :: t, h' :: t' =>
    match bool_order h h' with
    | Eq => bool_list_order t t'
    | o => o
    end
  end.

Lemma bool_list_order_eq : forall bs bs',
    bool_list_order bs bs' = Eq <-> bs = bs'.
Proof.
  induction bs; destruct bs'; split; intros; try(discriminate); auto.
  - destruct a; destruct b.
    + simpl in H. apply IHbs in H. subst. auto.
    + simpl in H. discriminate.
    + simpl in H. discriminate.
    + simpl in H. apply IHbs in H. subst. auto.
  - injection H. intros. subst. simpl.
    assert(bool_order b b = Eq).
    { apply bool_order_eq. auto. }
    rewrite H0. apply IHbs. auto.
Qed.

Lemma bool_list_order_trans : forall c x y z,
    bool_list_order x y = c -> bool_list_order y z = c -> bool_list_order x z = c.
Proof.
  induction x; destruct y; destruct z; intros; auto;
    try(simpl in *; rewrite <- H0 in *; discriminate).
  simpl in *.
  repeat dm;
    try(rewrite bool_order_eq in *; subst; rewrite bool_order_eq' in *; discriminate);
    try(apply bool_order_trans with (x:=a) in E; auto; rewrite E in E1; discriminate);
    try(rewrite bool_order_eq in *; subst; rewrite E1 in *; discriminate).
  - try(eapply IHx; eauto; reflexivity).
  - rewrite bool_order_eq in *; subst. discriminate.
  - rewrite bool_order_eq in *; subst. discriminate.
Qed.

Definition ascii_order (a1 a2 : ascii) : comparison :=
  bool_list_order (ascii2list a1) (ascii2list a2).

Lemma ascii_order_eq : forall x y,
    ascii_order x y = Eq <-> x = y.
Proof.
  intros. unfold ascii_order. rewrite ascii2list_eq. apply bool_list_order_eq.
Qed.

Lemma ascii_order_trans : forall c x y z,
    ascii_order x y = c -> ascii_order y z = c -> ascii_order x z = c.
Proof.
  intros. unfold ascii_order in *. 
  eapply bool_list_order_trans; eauto.
Qed.
