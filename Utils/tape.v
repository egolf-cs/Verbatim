Require Import List.
Import ListNotations.

From Verbatim Require Import ltac.

Definition Stack {Target : Type} : Type := list Target.
Definition EmptyStack {Target : Type} : @Stack Target := [].

Definition Tape {Target : Type} : Type := (@Stack (option Target)) * (@Stack (option Target)).
Definition EmptyTape {Target : Type} : (@Tape Target) := (EmptyStack, EmptyStack).

Definition length_Tape {Target : Type} (T : @Tape Target) : nat :=
  match T with (X, Y) => length X + length Y end.

Fixpoint reset_Tape' {Target : Type} (X Y : @Stack (option Target))
  : (@Stack (option Target)) * (@Stack (option Target)) :=
  match X with
  | [] => (X, Y)
  | x :: xs => reset_Tape' xs (x :: Y)
  end.

Fixpoint reset_Tape {Target : Type} (T : @Tape Target) : (@Tape Target) :=
  match T with
    (X, Y) => reset_Tape' X Y
  end.
  
Fixpoint set_Tape' {Target : Type} (x : Target) (i : nat) (T : @Tape Target) : @Tape Target :=
  match i with
  | 0 =>
    match T with
    | (xs, []) => (xs, [Some x])
    | (xs, y :: ys) => (xs, (Some x) :: ys) end
  | S n =>
    match T with
    | (xs, []) => set_Tape' x n (None :: xs, [])
    | (xs, y :: ys) => set_Tape' x n (y :: xs, ys)
    end
  end.

Definition set_Tape {Target : Type} (x : Target) (i : nat) (T : @Tape Target) : @Tape Target :=
  set_Tape' x i (reset_Tape T).

Fixpoint get_Tape' {Target : Type} (i : nat) (T : @Tape Target) : option Target :=
  match i with
  | 0 =>
    match T with
    | (_, []) => None
    | (_, y :: ys) => y
    end
  | S n =>
    match T with
    | (_, []) => None
    | (xs, y :: ys) => get_Tape' n (y :: xs, ys)
    end
  end.

Definition get_Tape {Target : Type} (i : nat) (T : @Tape Target) : option Target :=
  get_Tape' i (reset_Tape T).

Lemma reset_Tape_empty : forall {Target : Type} (T : @Tape Target) X Y,
    reset_Tape T = (X, Y) -> X = [].
Proof.
  intros. destruct T. simpl in H.
  generalize dependent X. generalize dependent Y. generalize dependent s0.
  induction s; intros.
  - sis. inj_all. auto.
  - sis. eapply IHs; eauto.
Qed.

Definition exTape :=  ([Some 1; Some 2], [Some 0]).
Compute (reset_Tape exTape).
Compute (get_Tape 0 exTape).

Compute (reset_Tape (set_Tape 5 0 exTape)).
Compute (reset_Tape (set_Tape 5 1 exTape)).
Compute (reset_Tape (set_Tape 5 2 exTape)).
Compute (reset_Tape (set_Tape 5 3 exTape)).

Compute (get_Tape 0 (set_Tape 5 0 exTape)).
Compute (get_Tape 1 (set_Tape 5 1 exTape)).
Compute (get_Tape 2 (set_Tape 5 2 exTape)).
Compute (get_Tape 3 (set_Tape 5 3 exTape)).

Lemma get_of_set_eq : forall {Target : Type} i x (T : @Tape Target),
    get_Tape i (set_Tape x i T) = Some x.
Proof.
  induction i; intros; unfold get_Tape in *; unfold set_Tape in *.
  - sis. repeat dm.
    + apply reset_Tape_empty in E0. subst. sis. inj_all. discriminate.
    + apply reset_Tape_empty in E0. subst. sis. inj_all. auto.
    + apply reset_Tape_empty in E0. subst. sis. inj_all. discriminate.
    + apply reset_Tape_empty in E0. subst. sis. inj_all. auto.
  - sis. repeat dm; admit.
Admitted.

Lemma get_of_set_neq : forall {Target : Type} i i' x (T : @Tape Target),
    i <> i' -> get_Tape i (set_Tape x i' T) = get_Tape i T.
Proof.
  induction i; intros; unfold get_Tape in *; unfold set_Tape in *.
  - sis. repeat dm.
    + admit.
    + admit.
    + admit.
  - sis. repeat dm; admit.
Admitted.

(* Return left of the current tape pointer, update the tape pointer to point there *)
Definition get_left_Tape {Target : Type} (T : @Tape Target) :
  (option Target) * @Tape Target :=
  match T with
  | ([], _) => (None, T)
  | (x :: xs, ys) => (x, (xs, x :: ys))
  end.

Definition get_right_Tape {Target : Type} (T : @Tape Target) :
  (option Target) * @Tape Target :=
  match T with
  | (_, []) => (None, T)
  | (_, [y]) => (None, T)
  | (xs, y0 :: y1 :: ys) => (y1, (y0 :: xs, y1 :: ys))
  end.

Compute exTape.
Compute (fst (get_left_Tape exTape)).
Compute (get_Tape ((length (fst exTape)) - 1) exTape).

Definition exTape2 : @Tape nat :=  ([], [Some 1; Some 2]).
Compute (fst (get_left_Tape exTape2)).
Compute (get_Tape ((length (fst exTape2)) - 1) exTape2).

Compute exTape.
Compute (fst (get_right_Tape exTape)).

Compute (fst (get_right_Tape exTape2)).
Compute (get_Tape (((length_Tape exTape2) + 1) - (length (snd exTape2))) exTape2).

Definition exTape3 : @Tape nat :=  ([Some 2; Some 1; Some 0], [Some 3; Some 4; Some 5]).
Compute (fst (get_right_Tape exTape3)).
Compute (get_Tape (((length_Tape exTape3) + 1) - (length (snd exTape3))) exTape3).

(* This is wrong without length fst T > 0 *)
Lemma get_left_indexed : forall {Target : Type} (T : @Tape Target),
    fst (get_left_Tape T) = get_Tape ((length (fst T)) - 1) T.
Admitted.

(* This needs similar qualification *)
Lemma get_right_indexed : forall {Target : Type} (T : @Tape Target),
    fst (get_right_Tape T)
    = get_Tape (((length_Tape T) + 1) - (length (snd T))) T.
Admitted.
