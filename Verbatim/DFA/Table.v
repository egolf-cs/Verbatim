Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.


From Verbatim Require Import ltac.
From Verbatim Require Import regex.

Module Type TABLE (R : regex.T).

  Import R.Ty.
  Module Import DS := R.Defs.
  Module Import reFS := DS.reFS.

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
  Parameter get_states : Table -> t.
  Parameter empty_states : get_states emptyTable = empty.
  Parameter correct_states : forall T r, In r (get_states (add_state T r)).
  Parameter moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  (* might need a hypothesis about not being in states *)

  
  Parameter get_eq : Table -> regex -> option regex.

  Parameter get_eq_correct : forall T e e',
      get_eq T e = Some e' -> In e' (get_states T) /\ regex_eq e e' = true.


End TABLE.

Module DefsFn (R : regex.T) (TabTy : TABLE R).

  Import TabTy.
  Import R.Defs.
  Import R.Ty.

  Module Export FillTable.

    Import R.Defs.Helpers.

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

    (* automation *)
    Program Fixpoint merge (es1 es2 : list regex)
            { measure ((length es1) + (length es2)) } : list regex :=
      match es1, es2 with
      | [], _ => es2
      | _, [] => es1
      | h1 :: t1, h2 :: t2 =>
        match re_compare h1 h2 with
        | Eq => merge (h1 :: t1) t2
        | Lt => h1 :: (merge t1 (h2 :: t2))
        | Gt => h2 :: (merge (h1 :: t1) t2)
        end
      end.
    Next Obligation. 
      simpl. omega.
    Defined.
    Next Obligation.
      simpl. omega.
    Defined.

    (* issues unfolding things *)
    Lemma merge_cons : forall t1 t2 h1 h2,
        match re_compare h1 h2 with
        | Eq => merge (h1 :: t1) (h2 :: t2) = merge (h1 :: t1) t2
        | Lt => merge (h1 :: t1) (h2 :: t2) = h1 :: (merge t1 (h2 :: t2))
        | Gt => merge (h1 :: t1) (h2 :: t2) =  h2 :: (merge (h1 :: t1) t2)
        end.
    Proof.
      intros. dm.
      - unfold merge. unfold merge_func. rewrite fix_sub_eq.
        + simpl. rewrite E. auto.
        + intros. destruct x. induction x.
          * auto.
          * admit.
    Admitted.



    (* acc proof method, issues type checking *)
    Lemma merge_acc1 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length (h1 :: t1)) + (length t2)).
    Proof.
      intros. inv H0. inv H. apply H0. simpl. omega.
    Qed.


    Lemma merge_acc2 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length t1) + (length (h2 :: t2))).
    Proof. 
      intros. inv H0. inv H. auto.
    Qed.


    Lemma merge_acc3 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length (h1 :: t1)) + (length t2)).
    Proof.
      apply merge_acc1.
    Qed.
    
    (*
    Fixpoint merge' (es1 es2 : list regex)
            (Ha : Acc lt ((length es1) + (length es2)))
            {struct Ha} : list regex :=
      match (es1, es2) as tpl return (es1, es2) = tpl -> _ with
      | ([], _) => fun _ => es2
      | (_, []) => fun _ => es1
      | (h1 :: t1, h2 :: t2) =>
        fun Heq =>
        match re_compare h1 h2 with
        | Eq => merge' (h1 :: t1) t2 (merge_acc1 _ _ _ _ _ _ Ha Heq)
        | Lt => h1 :: (merge' t1 (h2 :: t2) (merge_acc2 _ _ _ _ _ _ Ha Heq))
        | Gt => h2 :: (merge' (h1 :: t1) t2 (merge_acc3 _ _ _ _ _ _ Ha Heq))
        end
      end eq_refl.*)
    
    Lemma MNil : forall z,
        not (exp_match z EmptySet).
    Proof.
      intros. intros C. inv C.
    Qed.

    Lemma merge_nil1 : forall es,
        merge [] es = es.
    Proof. auto. Qed.

    Lemma merge_nil2 : forall es,
        merge es [] = es.
    Proof. destruct es; auto. Qed.


    Lemma merge_In : forall es es' e,
        In e (merge es es') <-> (In e es \/ In e es').
    Proof.
      intros. split; intros.
      {
        generalize dependent es'. generalize dependent e.
        induction es; intros.
        - rewrite merge_nil1 in H. auto.
        - induction es'; sis; auto.
          assert(L := merge_cons es es' a a0). destruct (re_compare a a0).
          + rewrite L in H. apply IHes' in H. destruct H; auto.
          + rewrite L in H. simpl in H. destruct H; auto.
            apply IHes in H. destruct H; auto.
          + rewrite L in H. simpl in H. destruct H; auto.
            apply IHes' in H. destruct H; auto.
      }
      {
        generalize dependent es'. generalize dependent e.
        induction es; intros.
        - rewrite merge_nil1. destruct H; auto. contradiction.
        - induction es'; sis.
          + destruct H; auto. contradiction.
          + assert(L := merge_cons es es' a a0). destruct (re_compare a a0) eqn:E.
            * rewrite L. apply IHes'. destruct H; auto. destruct H; auto.
              left. left. apply re_compare_eq in E. rewrite E. auto.
            * rewrite L. simpl. destruct H; auto. destruct H; auto.
            * rewrite L. simpl. destruct H; auto. destruct H; auto.
      } 
    Qed.

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
      | Star r =>
        match canon r with
        | Star _ => r
        | r' => Star r'
        end
      | _ => e
      end.


    Lemma invertIterApp : forall e z,
        exp_match z (IterApp (mkIterApp' e)) <-> exp_match z e.
    Proof.
      induction e; try(sis; reflexivity).
      sis. dm; try(destruct e2; discriminate).
      rewrite <- E in *. clear E.
      split; intros.
      - inv H. apply IHe2 in H4. constructor; auto.
      - inv H. constructor; auto. apply IHe2. auto.
    Qed.

    Lemma consIterApp : forall es e z,
        exp_match z (IterApp (e :: es))
        <-> exp_match z (App e (IterApp es)).
    Proof.
      intros. simpl. destruct es.
      {
        split; intros.
        - sis. assert(z = z ++ []). symmetry. apply app_nil_r.
          rewrite H0. clear H0.
          constructor; auto; constructor.
        - inv H. inv H4. rewrite app_nil_r. auto.
      }
      {
        split; intros; auto.
      }
    Qed.

    Lemma bar : forall es es' z,
        exp_match z (IterApp (es ++ es'))
        <-> exp_match z (App (IterApp es) (IterApp es')).
    Proof.
      induction es; intros.
      {
        split; intros; sis; assert(z = [] ++ z); auto.
        - rewrite H0. constructor; auto; constructor.
        - inv H. inv H4. sis. auto.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons in H. apply consIterApp in H. inv H.
          apply IHes in H4. inv H4. rewrite app_assoc. constructor; auto.
          apply consIterApp. constructor; auto.
        - remember (a :: es) as es0. inversion H. rewrite Heqes0 in *. clear H1 H2 H0 re1 re2.
          apply consIterApp in H3. inv H3.
          rewrite <- app_comm_cons. rewrite consIterApp. rewrite <- app_assoc.
          constructor; auto. apply IHes. constructor; auto.
      }
    Qed.
        
    Lemma foo : forall es z e',
        exp_match z (IterApp (es ++ [e']))
        <-> exp_match z (App (IterApp es) e').
    Proof. intros. apply bar. Qed.
    
    
    Lemma invertIterUnion : forall e z,
        exp_match z (IterUnion (mkIterUnion' e)) <-> exp_match z e.
    Proof.
      induction e; try(sis; reflexivity).
      sis. dm; try(destruct e2; discriminate).
      rewrite <- E in *. clear E.
      split; intros.
      - inv H.
        + apply MUnionL. auto.
        + apply IHe2 in H1. apply MUnionR. auto.
      - inv H.
        + constructor; auto.
        + apply MUnionR. apply IHe2. auto.
    Qed.
    
    Lemma consIterUnion : forall es e z,
        exp_match z (IterUnion (e :: es))
        <-> exp_match z (Union e (IterUnion es)).
    Proof.
      intros; simpl; destruct es.
      - simpl. split; intros.
        + constructor. auto.
        + inv H; auto. inv H1.
      - split; auto.
    Qed.

    Lemma IterUnion_In_match : forall es z,
      exp_match z (IterUnion es)
      <-> (exists e, In e es /\ exp_match z e).
    Proof.
      induction es; intros.
      {
        split; intros.
        - simpl in H. inv H.
        - destruct H. destruct H. contradiction.
      }
      {
        split; intros.
        - apply consIterUnion in H. inv H.
          + exists a. split; auto. simpl. left. auto.
          + apply IHes in H1. destruct H1. destruct H. exists x. split.
            * simpl. right. auto.
            * auto.
        - apply consIterUnion. destruct H. destruct H. destruct (regex_eq a x) eqn:E.
          + apply regex_eq_correct in E. subst. constructor. auto.
          + destruct H.
            * apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
            * apply MUnionR. apply IHes. eexists; eauto.
      }
    Qed.
    

    Lemma eq_set_eq_U : forall es es',
        (forall e, In e es <-> In e es')
        -> re_equiv (IterUnion es) (IterUnion es').
    Proof.
      unfold re_equiv. intros. split; intros.
      - rewrite IterUnion_In_match in *. destruct H0. destruct H0.
        apply H in H0. eexists; eauto.
      - rewrite IterUnion_In_match in *. destruct H0. destruct H0.
        apply H in H0. eexists; eauto.
    Qed.
         
    Lemma remove_head : forall es es' z a,
      exp_match z (IterUnion (merge (a :: es) es'))
      <-> exp_match z (IterUnion (a :: (merge es es'))).
    Proof.
      intros. assert(L := eq_set_eq_U). unfold re_equiv in *. apply L. clear L.
      intros. split; intros.
      - sis. rewrite merge_In in *. sis. rewrite <- or_assoc. auto.
      - sis. rewrite merge_In in *. sis. rewrite or_assoc. auto.
    Qed.
      
    Lemma barU : forall es es' z,
        exp_match z (IterUnion (merge es es'))
        <-> exp_match z (IterUnion (es ++ es')).
    Proof.
      induction es; intros.
      {
        assert([] ++ es' = es').
        { auto. }
        split; intros.
        - rewrite H in *; destruct es'; auto.
        - rewrite H in *; destruct es'; auto.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons. rewrite consIterUnion. apply remove_head in H.
          rewrite consIterUnion in H. inv H.
          + constructor; auto.
          + apply MUnionR. apply IHes. auto.
        - rewrite <- app_comm_cons in *. rewrite consIterUnion in *. apply remove_head.
          rewrite consIterUnion. inv H.
          + constructor. auto.
          + apply MUnionR. apply IHes. auto.
      }
    Qed.

    Lemma barU' : forall es es' z,
        exp_match z (IterUnion (es ++ es'))
        <-> exp_match z (Union (IterUnion es) (IterUnion es')).
    Proof.
      induction es; intros.
      {
        split; intros; sis.
        - apply MUnionR. auto.
        - inv H; auto. inv H2.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons in H. apply consIterUnion in H. inv H.
          + apply MUnionL. apply consIterUnion. apply MUnionL. auto.
          + apply IHes in H1. inv H1.
            * apply MUnionL. apply consIterUnion. apply MUnionR. auto.
            * apply MUnionR. auto.
        - rewrite <- app_comm_cons. apply consIterUnion. remember (a :: es) as es0.
          inv H.
          + apply consIterUnion in H2. inv H2.
            * apply MUnionL. auto.
            * apply MUnionR. apply IHes. apply MUnionL. auto.
          + apply MUnionR. apply IHes. apply MUnionR. auto.
      }
    Qed.
    
    Lemma fooU : forall es z e',
        exp_match z (IterUnion (es ++ [e']))
        <-> exp_match z (Union (IterUnion es) e').
    Proof. intros. apply barU'. Qed.

    Lemma canon_deriv : forall z e a,
        exp_match (a :: z) (canon e) = exp_match z (canon (derivative a e)).
    Admitted.

    Lemma canon_App_F : forall z e1 e2,
        exp_match z (canon (App e1 e2))
        -> (forall z : String, exp_match z (canon e1) <-> exp_match z e1)
        -> (forall z : String, exp_match z (canon e2) <-> exp_match z e2)
        -> exp_match z (App e1 e2).
    Proof.
      intros z e1 e2 H IHe1 IHe2.
      simpl in H.
        repeat dm; try(inv H; reflexivity);
          assert(z = [] ++ z); assert(z = z ++ []);
            try(auto; reflexivity); try(rewrite app_nil_r; auto);
              try(rewrite H0; constructor; [apply IHe1; constructor|];
                  apply IHe2; auto; reflexivity);
              try(rewrite H1; constructor; [apply IHe1; auto|];
                  apply IHe2; constructor; reflexivity); clear H0 H1;
                try(inv H; constructor; [apply IHe1; auto|]; apply IHe2; auto; reflexivity);
                try(destruct r2; discriminate);
                try(destruct r4; discriminate);
                try(destruct r0_2; discriminate);
                try(rewrite <- E1 in H; inv H; rewrite foo in H4; inv H4;
                    rewrite invertIterApp in H0; rewrite app_assoc; constructor;
                    [apply IHe1; constructor; auto | apply IHe2; auto]).
        + rewrite <- E1 in H. inv H. constructor; [apply IHe1; auto|].
          inv H4. apply IHe2. constructor; auto. rewrite invertIterApp in H5. auto.
        + rewrite <- E1 in H. inv H. rewrite bar in H4. inv H4. dm.
          * rewrite invertIterApp in H0. rewrite app_assoc. constructor.
            -- apply IHe1. constructor; auto.
            -- destruct r4; try(discriminate).
          * rewrite <- E2 in H5. inv H5. rewrite invertIterApp in *. rewrite app_assoc.
            constructor; [apply IHe1|apply IHe2]; constructor; auto.
        + rewrite <- E1 in H. inv H. inv H4. rewrite invertIterApp in *.
          constructor; [apply IHe1; auto|]. apply IHe2. constructor; auto.
        + rewrite <- E1 in H. inv H. inv H4. rewrite invertIterApp in *.
          constructor; [apply IHe1; auto|]. apply IHe2. constructor; auto.
    Qed.

    Lemma eq_Star : forall e1 e2,
        re_equiv e1 e2
        -> re_equiv (Star e1) (Star e2).
    Admitted.

    Lemma canon_Star : forall z e,
        (forall z : String, exp_match z (canon e) <-> exp_match z e)
        -> (exp_match z (canon (Star e))
        <-> exp_match z (Star (canon e))).
    Proof.
      induction z.
      {
        intros. split; intros.
        - constructor.
        - simpl. repeat dm; try apply H; constructor.
      }
      {
        intros. split; intros.
        - apply der_match. simpl. rewrite canon_deriv in H0.
          assert (derivative a (Star e) = App (derivative a e) (Star e)); auto.
          rewrite H1 in H0. clear H1.
          (* get rid of canon in H0 *)
          apply canon_App_F in H0.
          + inv H0. constructor.
            * apply der_match in H4. apply der_match. apply H. auto.
            * assert (L := eq_Star e (canon e)). unfold re_equiv in L.
              symmetry in H. eapply L in H. apply H. auto.
          + intros. rewrite <- canon_deriv. rewrite H. apply der_match.
          + intros. rewrite IHz.
    Admitted.
        
        
    Lemma canon_Star_B : forall z e,
        (forall z : String, exp_match z (canon e) <-> exp_match z e)
        -> exp_match z (Star (canon e))
        -> exp_match z (canon (Star e)).
    Admitted.

    Lemma canon_Star : forall z e,
        (forall z : String, exp_match z (canon e) <-> exp_match z e)
        ->
        (exp_match z (canon (Star e))
         <-> exp_match z (Star (canon e))).
    Proof.
      intros. split.
      - apply canon_Star_F. auto.
      - apply canon_Star_B. auto.
    Qed.
          
    Lemma canon_equiv : forall e,
        re_equiv (canon e) e.
    Proof.
      induction e; unfold re_equiv in *; split; intros; try(sis; auto; discriminate).
      - apply canon_App_F; auto. 
      - simpl.
        repeat dm; try(inv H; reflexivity);
          assert(z = [] ++ z); assert(z = z ++ []);
            try(auto; reflexivity); try(rewrite app_nil_r; auto);
              try(rewrite H0 in H; inv H; rewrite <- IHe1 in *; inv H5; reflexivity);
              try(rewrite H1 in H; inv H; rewrite <- IHe2 in *; inv H6; reflexivity);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  constructor; auto; reflexivity);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; simpl; constructor; auto; reflexivity);
              try(destruct r2; discriminate);
              try(rewrite <- E1; inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; repeat constructor; auto; rewrite invertIterApp; auto);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; repeat rewrite app_nil_r; repeat constructor; auto; reflexivity);
              try(rewrite <- E1; inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; rewrite <- app_assoc; constructor; auto;
                  rewrite bar; constructor; [rewrite invertIterApp|]; auto);
              try(destruct r4; discriminate);
              try(destruct r0_2; discriminate).
        + simpl. dm; try(destruct r4; discriminate).
          inv H6. constructor; auto. rewrite <-  E2. apply invertIterApp. auto.
          
      - simpl in H.
        repeat dm; repeat dm; try(inv H; reflexivity);
          try(apply MUnionR; rewrite <- IHe2; auto; reflexivity);
          try(apply MUnionL; rewrite <- IHe1; auto; reflexivity);
          try(inv H; [apply MUnionL; rewrite <- IHe1; auto
                     |apply MUnionR; rewrite <- IHe2; auto]; reflexivity);
          try(inv H; [apply MUnionR; rewrite <- IHe2; auto
                     |apply MUnionL; rewrite <- IHe1; auto]; reflexivity);
          try(rewrite barU in H; simpl in H; dm; try(destruct r2; discriminate);
              rewrite <- E1 in H; inv H; [apply MUnionL; rewrite <- IHe1; auto|];
              apply MUnionR; rewrite <- IHe2; inv H1; [apply MUnionL; auto|];
              apply MUnionR; rewrite invertIterUnion in *; auto);
          try(rewrite barU in H; simpl in H; inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto]; reflexivity).
        + rewrite barU in H; simpl in H; inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; try(destruct r4; discriminate).
          rewrite <- E1 in *. inv H1; [apply MUnionL; auto|rewrite invertIterUnion in H0].
          apply MUnionR; auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite barU' in H.
          inv H; dm; try(destruct r2; destruct r4; discriminate).
          * apply MUnionL. rewrite <- IHe1. rewrite <- E1 in H2. inv H2.
            apply MUnionL; auto. rewrite invertIterUnion in *. apply MUnionR. auto.
          * apply MUnionR. rewrite <- IHe2. rewrite <- E1 in H1. inv H1.
            apply MUnionL; auto. rewrite invertIterUnion in *. apply MUnionR. auto.
        + rewrite barU in H. rewrite barU' in H.
          inv H; [dm|]; try(destruct r2; discriminate).
          * apply MUnionL. rewrite <- IHe1. rewrite <- E1 in H2. inv H2.
            apply MUnionL. auto. apply MUnionR. rewrite invertIterUnion in *. auto.
          * apply MUnionR. rewrite <- IHe2. auto.
        + rewrite barU in H. rewrite barU' in H. inv H.
          * rewrite IHe1 in *. apply MUnionL. auto.
          * dm; try(destruct r0_2; discriminate). rewrite <- E1 in *.
            apply MUnionR. apply IHe2. inv H1.
            -- apply MUnionL. auto.
            -- apply MUnionR. rewrite invertIterUnion in *. auto.
      - simpl.
        repeat dm; try(inv H; reflexivity);
          try(rewrite barU; simpl);
          try(inv H; [rewrite <- IHe1 in *; inv H2 | rewrite <- IHe2 in *; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; auto | rewrite <- IHe2 in *; inv H1]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; auto | rewrite <- IHe2 in *; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; apply MUnionL; auto
                     | rewrite <- IHe2 in *; apply MUnionR; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; apply MUnionR; auto
                     | rewrite <- IHe2 in *; apply MUnionL; auto]; reflexivity);
          dm; try(destruct r4; discriminate); try(destruct r2; discriminate);
            try(destruct r0_2; discriminate); try(rewrite <- E1; clear E1);
              try(inv H; [rewrite <- IHe1 in * | rewrite <- IHe2 in *]);
              try(apply MUnionL; auto; reflexivity);
              try(inv H1);
              try(apply MUnionL; auto; reflexivity);
              try(apply MUnionR; apply MUnionL; auto; reflexivity);
              try(apply MUnionR; apply MUnionR; rewrite invertIterUnion; auto; reflexivity);
              try(inv H2; [apply MUnionL; auto; reflexivity|];
                  apply MUnionR; apply barU'; apply MUnionL; apply invertIterUnion; auto);
              try(apply MUnionR; apply barU'; apply MUnionR; simpl; constructor); auto.
        + apply MUnionR. apply barU'. apply MUnionR. simpl.
          dm; try(discriminate). apply MUnionL. auto.
        + apply MUnionR. apply barU'. apply MUnionR. simpl.
          dm; try(destruct r4; discriminate). apply MUnionR. rewrite <- E1.
          apply invertIterUnion. auto.
      - rewrite canon_Star in H; auto. apply star_concat in H.
        destruct H as (xss & H). destruct H.
        rewrite H in *. apply concat_star. intros. apply IHe. apply H0. auto.
      - apply canon_Star; auto. apply star_concat in H. destruct H as (xss & H). destruct H.
        rewrite H in *. apply concat_star. intros. apply IHe. apply H0. auto.
    Qed.                                                                                        
        
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
      unfold derived. intros.
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
