Require Import List.
Import ListNotations.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Coq.ZArith.BinInt.

From Verbatim Require Import regex.
From Verbatim Require Import state.
From Verbatim Require Import Table.
From Verbatim Require Import DFA.
From Verbatim Require Import lexer.impl.
From Verbatim Require Import Utils.ltac.
From Verbatim Require Import Utils.asciiFinite.
From Verbatim Require Import Utils.ascii_order.
From Verbatim Require Import concrete_table.

From Verbatim Require Import memo.memo.
From Verbatim Require Import memo.impl.
From Verbatim Require Import memo.correctness.
From Verbatim Require Import concrete_memo.

Module Import MEM <: memo.T.
  
  Module Import STT <: state.T.
    
    Module TabT <: Table.T.
      
      Module  R <: regex.T.
        
        Module Import Ty <: SIGMA.
          
          Definition Sigma : Type := ascii.
          Definition SigmaEnum : list Sigma := asciiEnum.
          Definition compareT := ascii_order.
          Definition compareT_eq := ascii_order_eq.
          Definition compareT_trans := ascii_order_trans.

          Lemma Sigma_finite : forall a : Sigma, In a SigmaEnum.
          Proof. apply ascii_finite. Qed.

          Lemma Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
          Proof. apply ascii_dec.  Qed.
          
        End Ty.
        
        Module Import Defs := regex.DefsFn Ty.
        
      End R.

      Module TabTy <: TABLE R := FTable R.

      Module Import Defs := DefsFn R TabTy.

    End TabT.

    Module Import R := TabT.R.
    Import R.Ty.
    Import R.Defs.Helpers.
    Import R.Defs.
    
    Module Import Ty <: STATE R.

      Module Import D := DFAFn TabT.
      

      Inductive Label' : Type :=
      | INT
      | PNT
      | DEC
      | EXP.

      Definition Label := Label'.
      Definition defLabel : Label := INT.
      Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
      Proof. decide equality. Qed.

      Definition Pointer : Type := regex.
      Definition defPointer : Pointer := EmptySet.
      Definition Delta : Type := TabT.TabTy.Table * TabT.R.Defs.reFS.t.
      Definition defDelta := (TabT.TabTy.emptyTable, TabT.TabTy.reFS.empty).
      Definition State := prod Pointer Delta.
      Definition defState := (defPointer, defDelta).
      
      Definition transition (a : Sigma) (e : State) : State :=
        match e with
          (x, (y, z)) =>
          match DFAtransition a (x,y,z) with
            (x',y',z') => (x',(y',z'))
          end
        end.
      Definition transition_list (bs : list Sigma) (e : State) : State :=
        match e with
          (x, (y, z)) =>
          match DFAtransition_list bs (x,y,z) with
            (x',y',z') => (x',(y',z'))
          end
        end.
      
      Lemma transition_list_nil : forall fsm,
          transition_list [] fsm = fsm.
      Proof.
        intros. unfold transition_list. repeat dm.
      Qed.
      
      Lemma transition_list_cons : forall bs a fsm,
          transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
      Proof.
        intros. unfold transition_list. repeat dm. sis. repeat dm.
        - repeat inj_all.
          assert((r, t2, t1) = (r0, t6, t5)).
          { rewrite <- E1. rewrite <- E5. auto. }
          inv H. auto.
        - repeat inj_all.
          assert((r, t2, t1) = (r0, t6, t5)).
          { rewrite <- E1. rewrite <- E5. auto. }
          inv H. auto.
      Qed.
      
      Lemma transition_Delta : forall a p p' d d',
          transition a (p, d) = (p', d') -> d = d'.
      Proof.
        intros. unfold transition in *. repeat dm. repeat inj_all.
        apply DFAtransition_Delta in E0. destruct E0. subst. auto.
      Qed.
      
      Definition accepts (s : String) (e : State) : bool :=
        match e with
          (x, (y, z)) => DFAaccepts s (x, y, z)
        end.
      Definition accepting (e : State) :=
        match e with
          (x, (y, z)) => DFAaccepting (x, y, z)
        end.

      Lemma accepts_nil: forall(fsm : State), accepting fsm = accepts [] fsm.
      Proof. intros fsm. reflexivity. Qed.

      Lemma accepts_transition : forall cand a fsm,
          accepts cand (transition a fsm) = accepts (a :: cand) fsm.
      Proof.
        intros. unfold accepts. repeat dm. rewrite accepts_cons. unfold transition in E.
        repeat dm. repeat inj_all. auto.
      Qed.

      Definition init_state (r : regex) : State :=
        match regex2dfa r with
          (x, y, z) => (x, (y, z))
        end.
      Definition init_state_inv (r : State) : regex :=
        match r with
          (x, (y, z)) => dfa2regex (x, y, z)
        end.
      
      Lemma invert_init_correct : forall r s,
          exp_match s (init_state_inv (init_state r)) <-> exp_match s r.
      Proof. intros. simpl. apply TabT.Defs.FillTable.canon_equiv. Qed.
      
      Lemma accepts_matches : forall(s : String) (e : regex),
          true = accepts s (init_state e) <-> exp_match s e.
      Proof.
        split; intros.
        - symmetry in H. apply r2d_accepts_match. auto.
        - symmetry. apply r2d_accepts_match. auto.
      Qed.

      Definition accepting_dt_list : forall bs e,
          accepting (transition_list bs (init_state e))
          = accepting (init_state (derivative_list bs e)).
      Proof.
        intros. unfold accepting. repeat dm.
        unfold transition_list in E. repeat dm. repeat inj_all.
        unfold init_state in *. repeat dm. repeat inj_all.
        assert(DFAaccepting (p, t, t0)
               = DFAaccepting (DFAtransition_list bs (p1, t3, t4))).
        { rewrite E5. auto. }
        rewrite H. clear H.
        assert(DFAaccepting (p0, t1, t2)
               = DFAaccepting (regex2dfa (derivative_list bs e))).
        { rewrite E. auto. }
        rewrite H. clear H.
        assert(DFAaccepting (DFAtransition_list bs (p1, t3, t4))
               = DFAaccepting (DFAtransition_list bs (regex2dfa e))).
        { rewrite E2. auto. }
        rewrite H. clear H.
        apply DFAaccepting_dt_list.
      Qed.
        

      Definition pointer_compare (s1 s2 : Pointer) : comparison :=
        re_compare s1 s2.

      Lemma pointer_compare_eq : forall x y,
          pointer_compare x y = Eq <-> x = y.
      Proof. apply re_compare_eq. Qed.

      Lemma pointer_compare_trans : forall c x y z,
          pointer_compare x y = c -> pointer_compare y z = c -> pointer_compare x z = c.
      Proof. apply re_compare_trans. Qed.

      Fixpoint pos2list (p : positive) : list bool :=
        match p with
          | xH => []
          | xO p' => false :: (pos2list p')
          | xI p' => true :: (pos2list p')
        end.

      Fixpoint list2pos (bs : list bool) : positive :=
        match bs with
        | [] => xH
        | false :: bs' => xO (list2pos bs')
        | true :: bs' => xI (list2pos bs')
        end.

      Lemma list_inv_pos : forall p,
          list2pos (pos2list p) = p.
      Proof.
        induction p; sis; try rewrite IHp; auto.
      Qed.

      Definition int2list (z : Z) : list bool :=
        match z with
        | 0%Z => []
        | Z.pos z' => true :: (pos2list z')
        | Z.neg z' => false :: (pos2list z')
        end.

      Definition list2int (bs : list bool) : Z :=
        match bs with
        | [] => 0%Z
        | true :: bs' => Z.pos (list2pos bs')
        | false :: bs' => Z.neg (list2pos bs')
        end.

      Lemma list_inv_int : forall z,
          list2int (int2list z) = z.
      Proof.
        destruct z.
        - sis. auto.
        - sis. rewrite list_inv_pos. auto.
        - sis. rewrite list_inv_pos. auto.
      Qed.

      Definition index : Type := Z.
      Definition index0 : index := 0%Z.

      Lemma index_eq_dec : forall (i ii : index), {i = ii} + {i <> ii}.
      Proof. repeat decide equality. Qed.
      
      Definition init_index (n : nat) : index :=
        match n with
        | 0 => index0
        | S m => Z.pos (P_of_succ_nat m)
        end.
      
      Definition index2list : index -> list bool:= int2list.
      Definition list2index : list bool -> index := list2int.
      
      Lemma list_inv : forall (x : index), list2index (index2list x) = x.
      Proof. apply list_inv_int. Qed.

      Definition incr : index -> index := Z.succ.
      Definition decr : index -> index := Z.pred.

      (* for index correctness *)
      Lemma decr_inv_incr : forall i, decr (incr i) = i.
      Proof. apply Z.pred_succ. Qed.
        
        
      Lemma incr_inv_decr : forall i, incr (decr i) = i.
      Proof. apply Z.succ_pred. Qed.
      
      Lemma decr_inv_S : forall n, decr (init_index (S n)) = init_index n.
      Proof.
        induction n; auto.
        sis. repeat dm.
        - sis. inv E0.
        - sis. inv E0. inv E. apply f_equal. rewrite H0. apply Pos.pred_double_succ.
        - sis. inv E0.
      Qed.
      
      Lemma incr_is_S : forall n, init_index (S n) = incr (init_index n).
      Proof.
        induction n; auto.
        unfold init_index. unfold incr. apply Pos2Z.inj_succ.
      Qed.
      
      Lemma n_det_index : forall n1 n2, init_index n1 = init_index n2 -> n1 = n2.
      Proof.
        intros. unfold init_index in *. destruct n1; destruct n2; try discriminate; auto.
        repeat rewrite Znat.Zpos_P_of_succ_nat in H. repeat rewrite <- Znat.Nat2Z.inj_succ in *.
        apply Znat.Nat2Z.inj; auto.
      Qed.
      
    End Ty.
    
    Module Import Defs := state.DefsFn R Ty.

  End STT.

  Module Import MemTy <: MEMO STT := FMemo STT.

  Module Import Defs := memo.MemoDefsFn STT MemTy.

End MEM.

Import MEM.STT.
Import MEM.STT.Defs.
Import MEM.STT.Ty.
Module L := memo.impl.ImplFn MEM.
Import L.
Import L.IMPL.Lex.
Module C := memo.correctness.CorrectFn MEM.
Import C.
Import MEM.STT.R.Defs.
Import MEM.STT.R.Defs.Helpers.
Import MEM.STT.R.Ty.


(*** Helpers ***)
Definition toS (z : string) : String := list_ascii_of_string z.
Definition Sig_of_N (n : nat) : Sigma := ascii_of_nat 65.
Fixpoint range' (n : nat) : (list nat) :=
  match n with
  | 0 => []
  | S n' => (range' n') ++ [n']
  end.

Fixpoint range (n1 n2 : nat) : (list nat) := map (plus n1) (range' (n2 - n1 + 1)).

(*** Numbers ***)
(* [0-9] *)
Definition ascii_digit := range 48 57.
Definition chars_digit := map Char (map ascii_of_nat ascii_digit).
Definition regex_digit := IterUnion chars_digit.

(* [1-9], nz = non-zero *)
Definition ascii_nz_digit := range 49 57.
Definition chars_nz_digit := map Char (map ascii_of_nat ascii_nz_digit).
Definition regex_nz_digit := IterUnion chars_nz_digit.

(* "fragment INT" *)
Definition regex_zero := Char (ascii_of_nat 48).
Definition regex_nzero := App regex_nz_digit (Star regex_digit).
Definition regex_nat := Union regex_zero regex_nzero.

Definition regex_sign := Char (ascii_of_nat 45).
Definition regex_sign_option := Optional regex_sign.

Definition regex_int := IterApp [regex_sign_option;regex_nat].
Definition ru_int := (INT, regex_int).



Definition regex_dec_point := Char (ascii_of_nat 46).
Definition ru_dec_point := (PNT, regex_dec_point).

Definition regex_dec := Plus regex_digit.
Definition ru_dec := (DEC, regex_dec).

Definition regex_Ee := Union (Char (ascii_of_nat 69)) (Char (ascii_of_nat 101)).
Definition regex_plus_option := Optional (Char (ascii_of_nat 43)).
Definition regex_Ee_delim := App regex_plus_option regex_Ee.
(* matches e, E, e+, E+ *)
Definition ru_Ee_delim := (EXP, regex_Ee_delim).


Definition rules : list Rule := [ru_int;ru_dec_point;ru_dec;ru_Ee_delim].

Module Splitter.
  
  Definition Split_float_str (z : String) : option (String * String * String) :=
    match lex_M rules z with
    | ([(INT,i)], []) => Some (i, [], [])
    | ([(INT,i);(PNT,_);(DEC,d)], []) => Some (i, d, [])
    | ([(INT,i);(EXP,_);(INT,e)], []) => Some (i, [], e)
    | ([(INT,i);(PNT,_);(DEC,d);(EXP,_);(INT,e)], []) => Some (i, d, e)
    | _ => None
    end.

End Splitter.

