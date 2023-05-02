(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(** This short chapter constructs such a function and proves it
    correct. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Locate "Bool".

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T. induction T; simpl.
    reflexivity.
    rewrite IHT1. rewrite IHT2. reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [T11->T12]
    for some [T11] and [T12]). *)

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2->T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11->T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.

(* ################################################################# *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T2)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T1)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** **** Exercise: 5 stars, standard (typechecker_extensions)

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | <{ inl T1 t }> =>
      T0 <- type_check Gamma t ;;
      return <{{T0 + T1}}>
  | <{ inr T0 t }> =>
      T1 <- type_check Gamma t ;;
      return <{{T0 + T1}}>
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2 }> => 
      match type_check Gamma t0 with
      | Some <{{T1 + T2}}> =>
        match type_check (x1 |-> T1 ; Gamma) t1,
              type_check (x2 |-> T2 ; Gamma) t2 with
        | Some T1', Some T2' => if eqb_ty T1' T2' then return T1' else fail
        | _, _ => fail
        end
      | _ => fail
      end

  (* lists (the [tlcase] is given for free) *)
  | <{nil T}> => return <{{List T}}>
  | <{h :: t}> => 
      T1 <- type_check Gamma h ;;
      match type_check Gamma t with
      | Some <{{List T2}}> => 
          if eqb_ty T1 T2 then return <{{List T2}}> else fail
      | _ => fail
      end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      match type_check Gamma t0 with
      | Some <{{List T}}> =>
          match type_check Gamma t1,
                type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then return T1' else fail
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  | <{ unit }> => return <{{Unit}}>
  (* pairs *)
  | <{ (t1, t2) }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return <{{T1 * T2}}>
  | <{ t.fst }> =>
      match type_check Gamma t with
      | Some <{{T * _}}> => return T
      | _ => fail
      end
  | <{ t.snd }> =>
      match type_check Gamma t with
      | Some <{{_ * T}}> => return T
      | _ => fail
      end
  (* let *)
  | <{ let x = t1 in t2 }> =>
      T1 <- type_check Gamma t1 ;;
      type_check (x |-> T1 ; Gamma) t2 
  (* fix *)
  | <{ fix t }> => 
      match type_check Gamma t with
      | Some <{{T1 -> T2}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* inl *) invert_typecheck Gamma t0 T1.
  - (* inr *) invert_typecheck Gamma t0 T1.
  - (* tcase *)
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck (s |-> T11; Gamma) t2 T2.
    invert_typecheck (s0 |-> T12; Gamma) t3 T3.
    case_equality T2 T3.
  - (* nil *) eauto.
  - (* cons *)
    invert_typecheck Gamma t1 T1.
    fully_invert_typecheck Gamma t2 T2 T21 T22.
    case_equality T1 T21.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *) eauto.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *) fully_invert_typecheck Gamma t T T1 T2.
  - (* snd *) fully_invert_typecheck Gamma t T T1 T2.
  - (* let *) invert_typecheck Gamma t1 T1.
  - (* fix *) 
    fully_invert_typecheck Gamma t T1 T11 T12.
    case_equality T11 T12.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma x0); [assumption| solve_by_invert].
Qed.
(* 
Qed. (* ... and uncomment this one *)
*)
End TypecheckerExtensions.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_step_function)

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

Fixpoint is_value (t : tm) : bool := 
  match t with
  | tm_var _ => false
  | <{  \ _ : _, _ }> => true
  | <{ _ _ }> => false
  | tm_const n => true
  | <{ succ _ }> => false
  | <{ pred _ }> => false
  | <{ _ * _ }> => false
  | <{ if0 _ then _ else _ }> => false
  | <{ inl _ v }> => is_value v
  | <{ inr _ v }> => is_value v
  | <{ case _ of | inl _ => _ | inr _ => _ }> => false
  | <{ nil _ }> => true
  | <{ v1 :: v2 }> => is_value v1 && is_value v2
  | <{ case _ of | nil => _ | _ :: _ => _ }> => false
  | <{ unit }> => true
  | <{ (v1, v2) }> => is_value v1 && is_value v2
  | <{ _.fst }> => false
  | <{ _.snd }> => false
  | <{ let _ = _ in _ }> => false
  | <{ fix _ }> => false
  end.

Theorem value_sound : forall v,
  is_value v = true -> value v.
Proof.
  induction v; intros H; inversion H; try (
    apply andb_true_iff in H1 as [H1 H2];
    apply IHv1 in H1; apply IHv2 in H2
  ); auto.
Qed.

Theorem value_complete : forall v,
  value v -> is_value v = true.
Proof.
  intros v H.
  induction H; try apply andb_true_iff;
    try (split; apply IHvalue1; apply IHvalue2); auto.
Qed.

Notation "` x <- e1 ;; e2" := (match e1 with
                                | x => e2
                                | _ => None
                                end)
         (right associativity, x pattern, at level 60).

Notation "'TRY' x <- e1 ;; e2 'OR' e3" := (match e1 with
                                           | Some x => e2
                                           | None => e3
                                           end)
         (right associativity, x pattern, at level 60).

Notation "'TRY' ` x <- e1 ;; e2 'OR' e3" := (match e1 with
                                             | x => e2
                                             | _ => e3
                                             end)
         (right associativity, x pattern, at level 60).


(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | tm_var x => fail
  | <{ \ x : _, t }> => fail
  | <{ t1 t2 }> => 
      let step_t2 := t2' <- stepf t2 ;; return <{ t1 t2' }> in
      TRY t1' <- stepf t1 ;; return <{ t1' t2 }> 
      OR TRY ` <{ \ x : _, t1' }> <- t1 ;;
        if is_value t2 then return <{ [x:=t2]t1' }> else step_t2
      OR if is_value t1 then step_t2 else fail
  | tm_const n => fail
  | <{ succ t }> =>
      TRY t' <- stepf t ;; return <{ succ t' }>
      OR ` (tm_const n) <- t ;; return tm_const (S n)
  | <{ pred t }> =>
      TRY t' <- stepf t ;; return <{ pred t' }>
      OR ` (tm_const n) <- t ;; return tm_const (n - 1)
  | <{ t1 * t2 }> =>
      TRY t1' <- stepf t1 ;; return <{ t1' * t2  }> 
      OR if is_value t1 then 
        TRY t2' <- stepf t2 ;; return <{ t1  * t2' }>
        OR ` (tm_const n1) <- t1 ;;
           ` (tm_const n2) <- t2 ;;
           return tm_const (n1 * n2)
      else fail
  | <{ if0 guard then t1 else t2 }> =>
      TRY guard' <- stepf guard ;;
          return <{ if0 guard' then t1 else t2 }>
      OR  match guard with
          | tm_const 0     => return t1
          | tm_const (S _) => return t2
          | _ => fail
          end
  (* sums *)
  | <{ inl T1 t }> => t' <- stepf t ;; return <{ inl T1 t' }>
  | <{ inr T0 t }> => t' <- stepf t ;; return <{ inr T0 t' }>
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2 }> => 
      TRY t0' <- stepf t0 ;;
          return <{ case t0' of | inl x1 => t1 | inr x2 => t2 }>
      OR  match t0 with
          | <{ inl _ v }> =>
              if is_value v then return <{ [x1:=v]t1 }> else fail
          | <{ inr _ v }> =>
              if is_value v then return <{ [x2:=v]t2 }> else fail
          | _ => fail
          end
  (* lists *)
  | <{nil T}> => fail
  | <{h :: t}> => 
      TRY h' <- stepf h ;; return <{ h' :: t }>
      OR  if is_value h 
          then t' <- stepf t ;; return <{ h :: t' }>
          else fail
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      TRY t0' <- stepf t0 ;;
          return <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
      OR  match t0 with
          | <{ nil _ }> => return t1
          | <{ v1 :: v2 }> => 
              if is_value t0 
              then return <{ [x22:=v2][x21:=v1]t2 }>
              else fail
          | _ => fail
          end
  (* unit *)
  | <{ unit }> => fail
  (* pairs *)
  | <{ (t1, t2) }> =>
      TRY t1' <- stepf t1 ;; return <{ (t1', t2) }>
      OR  if is_value t1 
          then t2' <- stepf t2 ;; return <{ (t1, t2') }>
          else fail
  | <{ t.fst }> => 
      TRY t' <- stepf t ;; return <{ t'.fst }>
      OR ` <{ (v1, v2) }> <- t ;;
          if is_value t then return v1 else fail
  | <{ t.snd }> =>
      TRY t' <- stepf t ;; return <{ t'.snd }>
      OR ` <{ (v1, v2) }> <- t ;;
          if is_value t then return v2 else fail
  (* let *)
  | <{ let x = t1 in t2 }> =>
      TRY t1' <- stepf t1 ;; return <{ let x = t1' in t2  }>
      OR  if is_value t1 then return <{ [x:=t1]t2 }> else fail
  (* fix *)
  | <{ fix t }> => 
      TRY t' <- stepf t ;; return <{ fix t' }>
      OR ` <{ \ x : T, t' }> <- t ;; 
          return <{ ([x := fix (\ x : T, t')] t') }>
  end.

Lemma step_not_value : forall t t',
    t --> t' -> value t -> False.
Proof.
  intros t t' H.
  induction H; intros Hf; inversion Hf; subst; congruence.
Qed.

Lemma value_no_step : forall t,
  value t -> stepf t = fail.
Proof.
  intros t H.
  induction H; simpl;
  try rewrite IHvalue; try reflexivity; rewrite IHvalue1;
    apply value_complete in H; rewrite H; rewrite IHvalue2; auto.
Qed.

Ltac invert_stepf t := 
  match goal with
  | H : match stepf t with | Some t' => _ | None => _ end = Some _
  , IHt : forall t' : tm, stepf t = Some t' -> t --> t'
  |- _ => 
      let Ht := fresh "Ht" in
      destruct (stepf t) eqn:Ht;
        [pose (IHt _ (f_equal Some (eq_refl _))); inversion H; auto|
         try congruence]
  end.

Ltac invert_is_value t := 
  match goal with
  | H : (if is_value t then _ else _) = Some _ |- _ => 
      let Ht := fresh "Ht" in
      destruct (is_value t) eqn:Ht;
        [apply value_sound in Ht; inversion H; auto|try congruence]
  end.

(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof.
  assert (Heq: forall t : tm, return t = return t); [intros; auto|].
  induction t; intros t' H; try congruence; inversion H;
    try invert_stepf t0.
  - (* t1 t2 *)
    invert_stepf t1.
    destruct t1; try solve_by_invert;
      try invert_is_value <{ t1_1 :: t1_2 }>;
      try invert_is_value <{ (t1_1, t1_2) }>;
      try invert_is_value t2;
      simpl in H1;
      try invert_is_value t1;
      invert_stepf t2.
  - (* succ t *)
    invert_stepf t.
      destruct t; try congruence.
      inversion H1. auto.
  - (* prev t *)
    invert_stepf t.
      destruct t; try congruence.
      inversion H1. auto.
  - (* t1 * t2 *)
    invert_stepf t1.
    invert_is_value t1.
    invert_stepf t2.
    destruct t1; try congruence.
    destruct t2; try congruence.
    inversion H1. auto.
  - (* if0 t0 then t1 else t2 *)
    invert_stepf t1.
    destruct t1; try congruence.
    destruct n; inversion H1; auto.
  - (* case t of | inl x1 => t1 | inr x2 => t2 *)
    invert_stepf t1.
    destruct t1; try congruence; invert_is_value t1.
  - (* t1 :: t2 *)
    invert_stepf t1. invert_is_value t1. invert_stepf t2.
  - (* case t of | nil => t1 | x21 :: x22 => t2 *)
    invert_stepf t1.
    destruct t1; try congruence; [inversion H1; auto|].
    invert_is_value <{ t1_1 :: t1_2 }>.
    inversion Ht0. inversion H1. auto.
  - (* (t1, t2) *)
    invert_stepf t1. invert_is_value t1. invert_stepf t2.
  - (* t.fst *)
    invert_stepf t.
    destruct t; try congruence.
    invert_is_value <{ (t1, t2) }>.
    inversion Ht0. subst. auto.
  - (* t.snd *)
    invert_stepf t.
    destruct t; try congruence.
    invert_is_value <{ (t1, t2) }>.
    inversion Ht0. subst. auto.
  - (* let x = t1 in t2 *) invert_stepf t1. invert_is_value t1. 
  - (* fix t *)
    invert_stepf t.
    destruct t; try congruence.
    inversion H1; auto.
Qed.

(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof.
  intros.
  induction H; simpl; try (
    try rewrite (value_no_step _ H), (value_complete _ H);
    try rewrite (value_no_step _ H0), (value_complete _ H0);
    try rewrite IHstep; reflexivity
  ).
  (* ST_App2 *)
  inversion H; simpl; try (
    try rewrite (value_no_step _ H1), (value_complete _ H1);
    try rewrite (value_no_step _ H2), (value_complete _ H2);
    rewrite IHstep; auto
  ). 
  destruct (is_value t2) eqn:Ht2; auto.
  exfalso. apply value_sound in Ht2.
  apply (step_not_value t2 t2'); try apply sound_stepf; auto.
Qed.

End StepFunction.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_impl)

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import MoreStlc.
Import STLCExtended.
Import StepFunction.
Import TypecheckerExtensions.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Program.Basics.
From Coq Require Import Lists.List. Import ListNotations.


(* ################################################################# *)
(** * Internals *)

(* ================================================================= *)
(** ** Lexical Analysis *)

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
    (n =? 32) || (* space *)
    (n =? 9)  || (* tab *)
    (n =? 10) || (* linefeed *)
    (n =? 13).   (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    (97 <=? n) && (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    (65 <=? n) && (n <=? 90) ||
    (97 <=? n) && (n <=? 122).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     (48 <=? n) && (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if      isWhite c then white
  else if isAlpha c then alpha
  else if isDigit c then digit
  else other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,digit,"0"  =>
        match acc with
        | ["f"; "i"] => (* deal with [if0] *)
            ["i"; "f"; "0"] :: (tokenize_helper white [] xs')
        | _ => tk ++ (tokenize_helper digit [x] xs')
        end
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

(* ================================================================= *)
(** ** Parsing *)

(* ----------------------------------------------------------------- *)

(** An [option] type with error messages: *)

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

(** Some syntactic sugar to make writing nested match-expressions on
    optionE more convenient. *)

Open Scope string_scope.

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).

(* ----------------------------------------------------------------- *)
(** *** Generic Combinators for Building Parsers *)

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(** A (step-indexed) parser that expects zero or more [p]s: *)

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(** A parser that expects a given token, followed by [p]: *)

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

(** A parser that expects a particular token: *)

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(* ----------------------------------------------------------------- *)
(** *** A Recursive-Descent Parser for Imp *)

(** Identifiers: *)

Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(** Numbers: *)

Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

Definition left_assoc {A B} f (x : A) (xs : list B) := 
  fold_left f xs x.

Definition right_assoc {T} f (x : T) (xs : list T) := 
  match rev xs with
  | [] => x
  | x' :: xs' => fold_left (fun A B => f B A) (xs' ++ [x]) x'
  end.
(** Parse types *)

Fixpoint parsePrimaryType (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      match xs with
      | "Nat" :: rest => SomeE (<{{Nat}}>, rest)
      | "Unit" :: rest => SomeE (<{{Unit}}>, rest)
      | "List" :: rest => 
          ' (T, rest') <- parseSumType steps' rest ;;
          SomeE (<{{List T}}>, rest')
      | "(" :: rest0 => 
          ' (T, rest1) <- parseArrowType steps' rest0 ;;
          ' (_, rest2) <- expect ")" rest1 ;;
          SomeE (T, rest2)
      | _ => NoneE "Expected a type"
      end
  end

with parseProductType (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (T, rest) <- parsePrimaryType steps' xs ;;
      ' (Ts, rest') <-
        many (firstExpect "*" (parsePrimaryType steps')) steps' rest  ;;
      SomeE (left_assoc Ty_Prod T Ts, rest')
  end

with parseSumType (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (T, rest) <- parseProductType steps' xs ;;
      ' (Ts, rest') <-
        many (firstExpect "+" (parseProductType steps')) steps' rest ;;
      SomeE (left_assoc Ty_Sum T Ts, rest')
  end

with parseArrowType (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (T, rest) <- parseSumType steps' xs ;;
      ' (Ts, rest') <-
        many (firstExpect "->" (parseSumType steps')) steps' rest ;;
      SomeE (right_assoc Ty_Arrow T Ts, rest')
  end
.

Definition parseType := parseArrowType.

Definition testParsing {X : Type}
           (p : nat ->
                list token ->
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in p 100 t.

Example type1 :
  testParsing parseType
  "Unit -> (Nat -> List Nat) * Unit + Nat -> Unit"
  = SomeE (<{{Unit -> (Nat -> List Nat) * Unit + Nat -> Unit}}>, []).
Proof. cbv. reflexivity. Qed.

(** Printing *)

Fixpoint stringifyType T :=
  match T with
  | <{{T1 -> T2}}> => stringifyType T1 ++ " -> " ++ stringifyType T2
  | <{{Nat}}> => "Nat"
  | <{{T1 + T2}}> => stringifyType T1 ++ " + " ++ stringifyType T2
  | <{{List T'}}> => "List " ++ stringifyType T'
  | <{{Unit}}> => "Unit"
  | <{{Prod}}> => "Prod"
  end.

Fixpoint string_of_nat_aux (steps n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" 
           | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match steps with
    | 0 => acc'
    | S steps' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux steps' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Fixpoint stringify t :=
  match t with
  | tm_var x => x
  | <{ t1 t2 }> =>
    "(" ++ stringify t1 ++ " " ++ stringify t2 ++ ")"
  | <{ \ x : T , t' }>  =>
      "\ " ++ x ++ " : " ++ stringifyType T ++
      " , " ++ stringify t'
  | tm_const n => string_of_nat n
  | <{ succ t' }> => "succ (" ++ stringify t' ++ ")"
  | <{ pred t' }> => "pred (" ++ stringify t' ++ ")"
  | <{ t1 * t2 }> => stringify t1 ++ " * " ++ stringify t2
  | <{ if0 t0 then t1 else t2 }> =>
      "if0 " ++ stringify t0
          ++ " then " ++ stringify t1 ++ " else " ++ stringify t2
  | <{ inl T t0 }> =>
      "inl " ++ stringifyType T ++ " (" ++ stringify t0 ++ ")"
  | <{ inr T t0 }> =>
      "inr " ++ stringifyType T ++ " (" ++ stringify t0 ++ ")"
  | <{ case t0 of | inl x1 => t1 | inr x2 => t2 }> =>
      "case " ++ stringify t0 ++ " of"
          ++ " | inl " ++ x1 ++ " => " ++ stringify t1
          ++ " | inr " ++ x2 ++ " => " ++ stringify t2
  | <{ nil T }> => "nil " ++ stringifyType T
  | <{ t1 :: t2 }> =>
      stringify t1 ++ " :: " ++ stringify t2
  | <{ case t0 of | nil => t1 | x2_1 :: x2_2 => t2 }> =>
      "case " ++ stringify t0 ++ " of"
          ++ " | nil => " ++ stringify t1 
          ++ " | " ++ x2_1 ++ " :: " ++ x2_2 
          ++ " => " ++ stringify t2
  | <{ unit }> => "unit"
  | <{ (t1, t2) }> =>
      "(" ++ stringify t1 ++ ", " ++ stringify t2 ++ ")"
  | <{ t0.fst }> => stringify t0 ++ ".fst"
  | <{ t0.snd }> => stringify t0 ++ ".snd"
  | <{ let x = t1 in t2 }> =>
      "let " ++ x ++ " = " ++ stringify t1
          ++ " in " ++ stringify t2
  | <{ fix t0 }> => "fix " ++ stringify t0
  end.


(** Parse terms *)

Fixpoint parsePrimaryTerm (steps:nat)
                          (xs : list token)
                          : optionE (tm * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      match xs with
      | "unit" :: rest => SomeE (<{ unit }>, rest)
      | "let" :: _ => parseLetTerm steps' xs
      | "case" :: _ => parseCaseTerm steps' xs
      | "pred" :: rest => 
          ' (t, rest') <- parseConsTerm steps' rest ;;
          SomeE (<{ pred t }>, rest')
      | "succ" :: rest => 
          ' (t, rest') <- parseConsTerm steps' rest ;;
          SomeE (<{ pred t }>, rest')
      | "fix" :: rest => 
          ' (t, rest') <- parseConsTerm steps' rest ;;
          SomeE (<{ fix t }>, rest')
      | "inl" :: rest0 =>
          ' (T, rest1) <- parseType steps' rest0 ;;
          ' (t0, rest2) <- parseProductOrAppTerm steps' rest1 ;;
          SomeE (<{ inl T t0 }>, rest2)
      | "inr" :: rest0 =>
          ' (T, rest1) <- parseType steps' rest0 ;;
          ' (t0, rest2) <- parseProductOrAppTerm steps' rest1 ;;
          SomeE (<{ inr T t0 }>, rest2)
      | "\" :: _ => parseAbsTerm steps' xs
      | "if0" :: _ => parseIf0Term steps' xs
      | "nil" :: rest =>
          ' (T, rest') <- parseType steps' rest ;;
          SomeE (<{ nil T }>, rest')
      | "(" :: rest => parseMaybePairTerm steps' rest
      | "in" :: _ | "then" :: _ | "else" :: _  | "of" :: _=>
          NoneE ("Identifiers should not be one of "
              ++ "['in'; 'then'; 'else', 'of']")
      | _ => 
          TRY ' (id, rest) <- parseIdentifier xs ;;
              SomeE (tm_var id, rest)
          OR
          TRY ' (n, rest) <- parseNumber xs ;;
              SomeE (tm_const n, rest)
          OR
          NoneE "Expected a term"
      end
  end

with parseLetTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (x , rest0) <- firstExpect "let" parseIdentifier xs ;;
    ' (t1, rest1) <- firstExpect "=" (parseConsTerm steps') rest0 ;;
    ' (t2, rest2) <- firstExpect "in" (parseConsTerm steps') rest1 ;;
    SomeE (<{ let x = t1 in t2 }>, rest2)
  end

with parseCaseTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (t0, rest0) <- firstExpect "case" (parseConsTerm steps') xs ;;
    match rest0 with
    | "of" :: "|" :: "inl" :: rest1 => 
        ' (x1, rest2) <- parseIdentifier rest1 ;;
        ' (t1, rest3) <- firstExpect "=>" (parseConsTerm steps') rest2 ;;
        ' (_ , rest4) <- expect "|" rest3 ;;
        ' (x2, rest5) <- firstExpect "inr" parseIdentifier rest4 ;;
        ' (t2, rest6) <- firstExpect "=>" (parseConsTerm steps') rest5 ;;
        SomeE (<{ case t0 of | inl x1 => t1 | inr x2 => t2 }>, rest6)
    | "of" :: "|" :: "nil" :: "=>" :: rest1 =>
        ' (t1, rest2) <- parseConsTerm steps' rest1 ;;
        ' (x2_1, rest3) <- firstExpect "|"  parseIdentifier rest2 ;;
        ' (x2_2, rest4) <- firstExpect "::" parseIdentifier rest3 ;;
        ' (t2, rest5) <- firstExpect "=>" (parseConsTerm steps') rest4 ;;
        SomeE (<{ case t0 of | nil => t1 | x2_1 :: x2_2 => t2 }>, rest5)
    | _ => NoneE "Expected 'of | nil =>' or 'of | inl'"
    end
  end

with parseAbsTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (x, rest0) <- firstExpect "\" parseIdentifier xs ;;
    ' (T, rest1) <- firstExpect ":" (parseType steps') rest0 ;;
    ' (t, rest2) <- firstExpect "," (parseConsTerm steps') rest1 ;;
    SomeE (<{ \ x : T , t }>, rest2)
  end

with parseIf0Term (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (t0, rest0) <- firstExpect "if0" (parseConsTerm steps') xs ;;
    ' (t1, rest1) <- firstExpect "then" (parseConsTerm steps') rest0 ;;
    ' (t2, rest2) <- firstExpect "else" (parseConsTerm steps') rest1 ;;
    SomeE (<{ if0 t0 then t1 else t2 }>, rest2)
  end

with parseMaybePairTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (t, rest) <- parseConsTerm steps' xs ;;
      match rest with
      | "," :: rest1 =>
          ' (t2, rest2) <- parseConsTerm steps' rest1 ;;
          ' (_, rest3) <- expect ")" rest2 ;;
          SomeE (<{ (t, t2) }>, rest3)
      | ")" :: rest' => SomeE (t, rest')
      | _ => NoneE "Expected ',' or ')' after a term"
      end
  end

with parseProjTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (t, rest) <- parsePrimaryTerm steps' xs ;;
      ' (projs, rest') <- many (fun xs =>
          match xs with
          | "." :: "fst" :: rest => SomeE (false, rest)
          | "." :: "snd" :: rest => SomeE (true, rest)
          | _ => NoneE "Expect '.fst' or '.snd'"
          end) steps' rest ;;
      SomeE (left_assoc (fun t proj =>
          match proj with
          | false => <{ t.fst }>
          | true => <{ t.snd }>
          end) t projs, rest')
  end

with parseProductOrAppTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (t, rest) <- parseProjTerm steps' xs ;;
      ' (ts, rest') <- many (fun xs =>
          match xs with
          | "*" :: rest => 
              ' (t, rest') <- parseProjTerm steps' rest ;;
              SomeE ((t, true), rest')
          | _ =>
              ' (t, rest') <- parseProjTerm steps' xs ;;
              SomeE ((t, false), rest')
          end
      ) steps' rest ;;
      SomeE (left_assoc (fun t1 t2p =>
          match t2p with
          | (t2, true) => <{ t1 * t2 }>
          | (t2, false) => <{ t1 t2 }>
          end) t ts, rest')
  end

with parseConsTerm (steps:nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      ' (t, rest) <- parseProductOrAppTerm steps' xs ;;
      ' (ts, rest') <- many (firstExpect "::" (parseProductOrAppTerm steps')) steps' rest ;;
      SomeE (right_assoc tm_cons t ts, rest')
  end.

Definition parseTerm := parseConsTerm.

Example term1 :
  testParsing parseTerm
  "let x = \ y : Unit , y in (x unit, 1).snd"
  = SomeE (<{ let x = \ y : Unit , y in (x unit, 1).snd }>, []).
Proof. cbv. reflexivity. Qed.

Definition bignumber := 1000.

Definition parseN (steps:nat) (str : string) := 
  let tokens := tokenize str in
  match parseTerm steps tokens with
  | SomeE (t, []) => SomeE t
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

Definition parse := parseN bignumber.

(** Evaluation: *)

Fixpoint evalTerm (steps:nat) t := 
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      match stepf t with
      | Some t' => 
          if is_value t' then SomeE t'
          else evalTerm steps' t'
      | None => NoneE ("Stuck on term: " ++ stringify t)
      end
  end.

Definition evalN (steps:nat) str :=
  ' t <- parse str ;; 
  match type_check empty t with
  | Some _ => evalTerm steps t
  | None => NoneE "Type error"
  end.

Definition eval := evalN bignumber.

Fixpoint fact n :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

Definition factorial_def :=
  "(fix \ f : Nat -> Nat, \ n : Nat,
      if0 n then 1 else n * (f (pred n)))".

Definition factorial_term := <{
    fix \ "f" : Nat -> Nat, \ "n" : Nat,
        if0 "n" then 1 else "n" * ("f" (pred "n"))
    }>.

Eval compute in parse factorial_def.
Eval compute in type_check empty factorial_term.

Theorem factorial_parse_correct :
  parse factorial_def = SomeE factorial_term.
Proof. cbv. reflexivity. Qed.

Theorem factorial_type_check_correct :
  type_check empty factorial_term = Some <{{Nat -> Nat}}>.
Proof. cbv. reflexivity. Qed.

Example factorial_7 :
  eval (factorial_def ++ "7") = SomeE (tm_const (fact 7)).
Proof. cbv. reflexivity. Qed.

Definition try_prod_def :=
  "(fix \ f : List (Nat + Unit) -> (Nat + Unit), \ l : List (Nat + Unit),
      case l of
      | nil => inl Unit 1
      | h :: t => case h of
                  | inl n =>
                          let x = f t in
                          case x of 
                          | inl r => inl Unit (n * r)
                          | inr x => inr Nat unit
                  | inr y => inr Nat unit)".

Definition try_prod_term := <{
  fix \ "f" : List (Nat + Unit) -> (Nat + Unit), \ "l" : List (Nat + Unit),
      case "l" of
      | nil => inl Unit 1
      | "h" :: "t" => case "h" of
                      | inl "n" => 
                          let "x" = "f" "t" in
                          case "x" of 
                          | inl "r" => inl Unit ("n" * "r")
                          | inr "x" => inr Nat unit
                      | inr "y" => inr Nat unit
    }>.

Theorem try_prod_parse_correct :
  parse try_prod_def = SomeE try_prod_term.
Proof. cbv. reflexivity. Qed.

Theorem try_prod_type_check_correct :
  type_check empty try_prod_term =
    Some <{{List (Nat + Unit) -> (Nat + Unit)}}>.
Proof. cbv. reflexivity. Qed.

Example try_prod_nil :
  eval (try_prod_def ++ "nil (Nat + Unit)") =
    SomeE <{ inl Unit 1 }>.
Proof. cbv. reflexivity. Qed.

Example try_prod_singleton :
  eval (try_prod_def ++ "(inl Unit 1 :: nil (Nat + Unit))") =
    SomeE <{ inl Unit 1 }>.
Proof. cbv. reflexivity. Qed.

Example try_prod_some :
  eval (try_prod_def ++ "(inl Unit 3 :: inl Unit 5 :: nil (Nat + Unit))") =
    SomeE <{ inl Unit 15 }>.
Proof. cbv. reflexivity. Qed.

Example try_prod_none :
  eval (try_prod_def ++
    "(inl Unit 3 :: inr Nat unit :: inl Unit 5 :: nil (Nat + Unit))") =
    SomeE <{ inr Nat unit }>.
Proof. cbv. reflexivity. Qed.

Definition swap_pair_def :=
  "(\ pair : Nat * Nat,
      let x = pair.fst in
      let y = pair.snd in
      (y, x))".

Definition swap_pair_term := <{
  \ "pair" : Nat * Nat,
      let x = "pair".fst in
      let y = "pair".snd in
      (y, x)
  }>.

Theorem swap_pair_parse_correct :
  parse swap_pair_def = SomeE swap_pair_term.
Proof. cbv. reflexivity. Qed.

Theorem swap_pair_type_check_correct :
  type_check empty swap_pair_term = 
    Some <{{(Nat * Nat) -> (Nat * Nat)}}>.
Proof. cbv. reflexivity. Qed.

Example swap_pair_test :
  eval (swap_pair_def ++ "(1, 2)") = SomeE (<{ (2, 1) }>).
Proof. cbv. reflexivity. Qed.

End StlcImpl.
(** [] *)

(* 2021-08-11 15:11 *)
