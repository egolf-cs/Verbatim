Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.


From Verbatim Require Import ltac.
From Verbatim Require Import Utils.order.
From Verbatim Require Import regex.

Module Type TABLE (R : regex.T).

  Import R.Ty.
  Import R.Defs.

  Parameter Table : Type.
  Parameter emptyTable : Table.
  (*The first regex is for indexing, the second is the content of the cell*)
  Parameter set_Table : Table -> regex -> Sigma -> regex -> Table.
  Parameter get_Table : Table -> regex -> Sigma -> option (regex).

  Parameter correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
  Parameter moot_setTable : forall T e0 e a b r,
      a <> b
      \/ e <> e0
      -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
  Parameter correct_emptyTable : forall e a, get_Table emptyTable e a = None.


  Parameter add_state : Table -> regex -> Table.
  Parameter get_states : Table -> list regex.
  Parameter empty_states : get_states emptyTable = [].
  Parameter correct_states : forall T r, In r (get_states (add_state T r)).
  Parameter moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  (* might need a hypothesis about not being in states *)

End TABLE.

Module DefsFn (R : regex.T) (TabTy : TABLE R).

  Import TabTy.
  Import R.Defs.
  Import R.Ty.

  Module Export Get_Sim.
    (*
    Fixpoint get_sim' (es : list regex) (e : regex) : option regex :=
      match es with
      | [] => None
      | h :: t => if re_sim e h then Some h else get_sim' t e
      end.

    Theorem get_sim'_correct : forall es e e',
        get_sim' es e = Some e' -> In e' es /\ re_sim e e' = true.
    Proof.
      induction es; intros; try(discriminate).
      simpl in H. dm.
      - injection H; intros. rewrite H0 in *. split; simpl; auto.
      - apply IHes in H. destruct H. split; simpl; auto.
    Qed.
    
    Definition get_sim (T : Table) (e : regex) : option regex :=
      get_sim' (get_states T) e.
    
    Theorem get_sim_correct : forall T e e',
        get_sim T e = Some e' -> In e' (get_states T) /\ re_sim e e' = true.
    Proof.
      intros. unfold get_sim in *. apply get_sim'_correct; auto.
    Qed.*)

    (* If the regexes are ordered this can be faster *)
    Fixpoint get_eq' (es : list regex) (e : regex) : option regex :=
      match es with
      | [] => None
      | h :: t => if regex_eq e h then Some h else get_eq' t e
      end.

    Definition get_eq (T : Table) (e : regex) : option regex :=
      get_eq' (get_states T) e.

    Lemma get_eq_correct : forall T e e',
        get_eq T e = Some e' -> In e' (get_states T) /\ regex_eq e e' = true.
    Admitted.

  End Get_Sim.

  Module Export FillTable.

    Import R.Defs.Helpers.

    Fixpoint re_order (e1 e2 : regex) : order :=
      match e1, e2 with
      | EmptyStr, EmptyStr => EQUAL
      | EmptyStr, _ => LESSER
      | _, EmptyStr => GREATER
      | EmptySet, EmptySet => EQUAL
      | EmptySet, _ => LESSER
      | _, EmptySet => GREATER
      | Char a, Char b => Sigma_order a b
      | Char _, _ => LESSER
      | _, Char _ => GREATER
      | App e1 e2, App e3 e4 =>
        match re_order e1 e3 with
        | EQUAL => re_order e2 e4
        | comp => comp
        end
      | App _ _, _ => LESSER
      | _, App _ _ => GREATER
      | Star e1, Star e2 => re_order e1 e2
      | Star _, _ => LESSER
      | _, Star _ => GREATER
      | Union e1 e2, Union e3 e4 =>
        match re_order e1 e3 with
        | EQUAL => re_order e2 e4
        | comp => comp
        end
      end.

    (* Assume all union inputs are already canonical:
       1. All iterared unions are recursively right associated
       2. All iterated unions are in lexicographic order
       3. The EmptySet is not present in any union
       4. All regexes in all iterated unions are unique
     *)
    Fixpoint mkIterUnion' (e : regex) : list regex :=
      match e with
      | Union e1 e2 =>
        e1 :: (mkIterUnion' e2)
      | _ => [e]
      end.

    Program Fixpoint merge (es1 es2 : list regex)
            { measure ((length es1) + (length es2)) } : list regex :=
      match es1, es2 with
      | [], _ => es2
      | _, [] => es1
      | h1 :: t1, h2 :: t2 =>
        match re_order h1 h2 with
        | EQUAL => merge (h1 :: t1) t2
        | LESSER => h1 :: (merge t1 (es2))
        | GREATER => h2 :: (merge es1 t2)
        end
      end.
    Next Obligation.
      simpl. omega.
    Defined.
    Next Obligation.
      simpl. omega.
    Defined.
      

    (* Assume all App inputs and subterms are recursively right associated *)
    Fixpoint mkIterApp' (e : regex) : list regex :=
      match e with
      | App e1 e2 => e1 :: (mkIterApp' e2)
      | _ => [e]
      end.      

    (* Instead of checking for similarity, 
       force all regexes to be in the right hand form of the relation.
       Also use associativity/commutativity to force lexical ordering on Unioned exps
       Then check for equality.
     *)
    Fixpoint canon (e : regex) : regex :=
      match e with
      | Union e1 e2 =>
        match canon e1, canon e2 with
        (* The next two patters ensure that unions don't contain EmptySet *)
        | EmptySet, ec2 => ec2
        | ec1, EmptySet => ec1
        | ec1, ec2 =>
          (* sort and make right recursive *)
          (* Note : merge also removes duplicates *)
          IterUnion (merge (mkIterUnion' ec1) (mkIterUnion' ec2))
        end
      | App e1 e2 =>
        match canon e1, canon e2 with
        (* The next two patterns ensure that all iterated apps
           containing an EmptySet reduce to the EmptySet *)
        | EmptySet, _ => EmptySet
        | _, EmptySet => EmptySet
        (* The next two patters ensure that apps don't contain EmptyStr *)
        | EmptyStr, ec2 => ec2
        | ec1, EmptyStr => ec1
        | ec1, ec2 =>
          IterApp ( (mkIterApp' ec1) ++ (mkIterApp' ec2) )
        end
      | Star EmptySet => EmptyStr
      | Star EmptyStr => EmptyStr
      | Star (Star r) => canon r
      | _ => e
      end.

    Lemma canon_equiv : forall e,
        re_equiv (canon e) e.
    Proof.
    Admitted.
    
    Fixpoint fill_Table_all' (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
      match fuel with
      | 0 => T
      | S n =>
        let
          (* We need a helper function to apply fill_Table_all to each derivative of e *)
          fix fill_Table_ds (bs' : list Sigma) :=
          match bs' with
          | [] => T
          | c :: cs =>
            let
              (* fill the table with respect to the tail *)
              T1 := fill_Table_ds cs in
            let
              (* now we'll do it with respect to c *)
              d := canon (derivative c e) in
            (** 
                get_sim is probably very expensive.
                The list of states doesn't have any logical order to it right now.
                Given a regex, there is only a small class of regexes that could be similar.
                Should somehow bucket the list of states by these classes.
             **)
            (**
               One of the paper talks about canonicalizing regexes with smart constructors.
               I'm not sure if this is necessary for the DFA construction.
               I can imagine how it would make similarity checks faster/bucketing easier.
             **)
            (**
               Right now states are regexes. It would be better if they were integers.
               Would need to keep track of the association between integers and regexes.
               Maybe that should be handled by the table?
            **)
            match get_eq T d with
            | None =>
              let
                (* we didn't find a similar regex, we need to add d *)
                T2 := add_state T1 d in
              let
                (* we also need to transition from regex e to regex d on symbol c *)
                T3 := set_Table T2 e c d in
              (* finally we need to fill up the table with respect to d *)
              fill_Table_all' T3 d bs n
            | Some e' =>
              (* In this case, we found a regex that has already been added to the table *)
              (* Anytime we add a regex, we immediately call fill_Table_all for it *)
              (* Therefore, we don't need to call fill_Table_all again *)
              (* Instead, we transition from e to e' when we see c *)
              set_Table T1 e c e'
            end
          end
        in
        fill_Table_ds bs
      end.

    Definition fill_Table_all (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
      fill_Table_all' T (canon e) bs fuel.
    

  End FillTable.

  Module Export Spec.

    Definition derived (T : Table) : Prop :=
      forall e a r, get_Table T e a = Some r -> re_equiv r (derivative a e).

  End Spec.

  Module Export Correct.

    Theorem emptyTable_derived : derived emptyTable.
    Proof.
      unfold derived. intros. rewrite correct_emptyTable in H. discriminate.
    Qed.

    Lemma unfold_filler' : forall bs T e n,
        fill_Table_all' T e bs (S n)
        =
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d bs n
            end
          end in
        fill_Table_ds bs.
    Proof.
      auto.
    Qed.

    Lemma unfold_filler_ds : forall T T' e x xs n,
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d (x :: xs) n
            end
          end in
        T' = fill_Table_ds (x :: xs)
        ->
        (exists e' T0, get_eq T (canon (derivative x e)) = Some e'
                  /\ T0 = (fill_Table_ds xs)
                  /\ T' = set_Table T0 e x e')
        \/
        (exists T0, get_eq T (canon (derivative x e)) = None
               /\
               T0 = (fill_Table_ds xs)
               /\
               T' = fill_Table_all'
                      (set_Table (add_state T0 (canon (derivative x e))) e x
                                 (canon (derivative x e)))
                      (canon (derivative x e)) (x :: xs) n).
    Proof.
      intros. simpl in *. destruct (get_eq T (canon (derivative x e))) eqn:E.
      - left. eexists; eauto.
      - right. eexists; eauto.
    Qed.

    Theorem derived_closure_set : forall T b e r,
        derived T
        -> re_equiv r (derivative b e)
        -> derived (set_Table T e b r).
    Proof.
      intros.
      (* 1. T' is derived before the set. 
     2. We know (derivative b e) and r are similar.
     3. The only entry in T' that changes is the (e, b) entry
     ---
     4. T' is still derived after the set.
       *)
      unfold derived. intros.
      (* If e = e0 and a = b, r = r0. Otherwise the entry was there before the set. *)
      (** may need a hypothesis about getting something that wasn't set **)
      destruct (regex_eq e e0) eqn:E; destruct (Sigma_dec a b).
      - apply regex_eq_correct in E. subst.
        rewrite correct_Table in H1. injection H1; intros; subst.
        auto.
      - rewrite moot_setTable in H1; auto.
      - rewrite moot_setTable in H1; auto.
        assert(regex_eq e e0 <> true).
        { intros C. rewrite C in *. discriminate. }
        right. intros C. destruct H2. apply regex_eq_correct. auto.
      - rewrite moot_setTable in H1; auto.
    Qed.

    Theorem derived_closure_add : forall T T' e,
        derived T
        -> T' = add_state T e
        -> derived T'.
    Proof.
      unfold derived in *. intros.
      rewrite H0 in H1. rewrite <- moot_add_state with (r:=e) in H1.
      apply H in H1. auto.
    Qed.
    
    Lemma derived_closure_ds' : forall bs T T' e n xs,
        (forall (cs : list Sigma) (e : regex) (T T' : Table),
            derived T -> T' = fill_Table_all' T e cs n -> derived T')
        -> derived T
        ->
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d xs n
            end
          end in
        T' = fill_Table_ds bs
        -> derived T'.
    Proof.
      intros.
      generalize dependent T.
      generalize dependent T'.
      generalize dependent e.
      generalize dependent xs.
      induction bs as [|b bs]; intros.
      - subst; auto.
      - simpl in H1. repeat dm.
        + assert(derived (fill_Table_ds bs)).
          {
            apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
          }
          apply get_eq_correct in E. destruct E.
          rewrite H1.
          apply derived_closure_set; auto.
          rewrite <- regex_eq_correct in H4. rewrite <- H4.
          apply canon_equiv.
        + assert(derived (fill_Table_ds bs)).
          {
            apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
          }
          assert(derived (add_state (fill_Table_ds bs) (canon (derivative b e)))).
          {
            eapply derived_closure_add; eauto.
          }
          clear H2.
          assert(derived (set_Table
                            (add_state (fill_Table_ds bs) (canon (derivative b e)))
                            e b (canon (derivative b e)))).
          {
            eapply derived_closure_set; eauto.
            apply canon_equiv.
          }
          eapply H; eauto.
    Qed.
    
    Lemma derived_closure_ds : forall bs T e n xs,
        (forall (cs : list Sigma) (e : regex) (T T' : Table),
            derived T -> T' = fill_Table_all' T e cs n -> derived T')
        -> derived T
        ->
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d xs n
            end
          end in
        derived (fill_Table_ds bs).
    Proof.
      intros. apply derived_closure_ds' with (bs:=bs) (T:=T) (e:=e) (n:=n) (xs:=xs); auto.
    Qed.
    
    
    Theorem derived_closure_all' : forall n bs e T T',
        derived T
        -> T' = fill_Table_all' T e bs n
        -> derived T'.
    Proof.
      induction n; intros; try(simpl in H0; subst; auto; reflexivity).
      destruct bs as [|b bs].
      - simpl in H0. subst. auto.
      - rewrite unfold_filler' in H0. apply unfold_filler_ds in H0. destruct H0.
        + destruct H0 as (e' & T0 & H0 & H1 & H2).
          assert(derived T0).
          {
            apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
            subst. auto. apply IHn.
          }
          clear H1.
          subst. eapply derived_closure_set; eauto.
          apply get_eq_correct in H0. destruct H0.
          apply regex_eq_correct in H1. rewrite <- H1.
          apply canon_equiv.
        + destruct H0 as (T0 & H0 & H1 & H2).
          assert(derived T0).
          {
            apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
            subst. auto. apply IHn.
          }
          clear H1.
          assert(derived (add_state T0 (canon (derivative b e)))).
          {
            eapply derived_closure_add; eauto.
          }
          assert(derived (set_Table (add_state T0 (canon (derivative b e)))
                                    e b (canon (derivative b e)))).
          {
            eapply derived_closure_set; eauto.
            apply canon_equiv.
          }
          eapply IHn; eauto.
    Qed.

    Theorem derived_closure_all : forall n bs e T T',
        derived T
        -> T' = fill_Table_all T e bs n
        -> derived T'.
    Proof.
      intros. unfold fill_Table_all in *. eapply derived_closure_all'; eauto.
    Qed.

    Theorem derived_get_some : forall T e a e',
        derived T
        -> get_Table T e a = Some e'
        -> re_equiv e' (derivative a e).
    Proof.
      intros. unfold derived in *. apply H in H0. auto.
    Qed.

  End Correct.

End DefsFn.

Module Type DefsT (R : regex.T) (TabTy : TABLE R).
  Include DefsFn R TabTy.
End DefsT.

Module Type T.
  Declare Module R : regex.T.
  Declare Module TabTy : TABLE R.
  Declare Module Defs : DefsT R TabTy.
  Export R.
  Export R.Ty.
  Export R.Defs.
  Export TabTy.
  Export Defs.
End T.
