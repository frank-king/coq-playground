(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductively defined propositions_.

    _Note_: For the sake of simplicity, most of this chapter uses an
    inductive definition of "evenness" as a running example.  This is
    arguably a bit confusing, since we already have a perfectly good
    way of defining evenness as a proposition ("[n] is even if it is
    equal to the result of doubling some number").  Rest assured that
    we will see many more compelling examples of inductively defined
    propositions toward the end of this chapter and in future
    chapters. *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true], or

      (2) [exists k, n = double k].

    A third possibility that we'll explore here is to say that [n] is
    even if we can _establish_ its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation.  (We'll
    use [ev] for the name of this property, since [even] is already
    used.)

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(** Each of the textual rules that we started with is
    reformatted here as an inference rule; the intended reading is
    that, if the _premises_ above the line all hold, then the
    _conclusion_ below the line follows.  For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also
    does.  If a rule has no premises above the line, then its
    conclusion holds unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(** (Why call this a "tree", rather than a "stack", for example?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly.) *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of
    [ev] appears to the _right_ of the colon on the first line, it
    is allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same (i.e., [list X]).  Had we tried to bring [nat] to the left
   of the colon in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter; in [Inductive ev : nat -> Prop := ...], the unnamed
    [nat] argument is an index. *)

(** We can think of this as defining a Coq property [ev : nat ->
    Prop], together with "evidence constructors" [ev_0 : ev 0]
    and [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n IHn].
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, which amounts to reasoning about how it
    could have been built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove that a number is [ev], and
    the inversion lemma makes this explicit. *)

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** If we [remember] that term [S (S n)], the proof goes
    through.  (We'll discuss [remember] in more detail below.) *)

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Hk.
  destruct E as [|n' E'] eqn:EE.
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. *)
    discriminate Hk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

(** Alternatively, the proof is straightforward using the inversion
    lemma that we proved above. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
    - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra practice,
    you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  inversion E' as [| n'' E'' Heq'].
  apply E''.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E as [| n' E' Heq].
  inversion E' as [| n'' E'' Heq'].
  inversion E''.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to re-prove some theorems from chapter
    [Tactics].  (Here we are being a bit lazy by omitting the [as]
    clause from [inversion], thereby asking Coq to choose names for
    the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *)
  unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would
    probably lead to a dead end, because (as we've noted before) the
    induction hypothesis will talk about n-1 (which is _not_ even!).
    Thus, it seems better to first try [inversion] on the evidence for
    [ev].  Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *)

(** Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    { intros [k' EQ'']. exists (S k'). simpl. rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unforunately, now we are stuck. To make that apparent, let's move
        [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is clear we are trying to prove another instance of the
        same theorem we set out to prove.  This instance is with [n'],
        instead of [n], where [n'] is a smaller natural number than [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to
    use case analysis to prove results that required induction.  And
    once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [ev
    n] holds, we can use induction on [ev n]. This requires us to
    prove two things, corresponding to the two ways in which [ev n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [ev n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [ev n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even E' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E.
  generalize dependent m.
  induction E as [|n' E' IH].
  - intros m Em. apply Em.
  - intros m Em.
    simpl.
    apply ev_SS.
    apply IH.
    apply Em.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from [Logic]) of
    applying theorems to arguments, and note that the same technique
    works with constructors of inductively defined propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros E.
    induction E as [| |n' m En' IHn' Em IHm].
    + apply ev_0.
    + apply ev_SS.
      apply ev_0.
    + apply ev_sum.
      * apply IHn'.
      * apply IHm.
  - intros E.
    induction E as [|n' E' IH].
    + apply ev'_0.
    + destruct n' as [|n''].
      * apply ev'_2.
      * assert (H: S (S (S n'')) = S n'' + 2).
        { rewrite add_comm. reflexivity. }
        rewrite H.
        apply ev'_sum.
        { apply IH. }
        { apply ev'_2. }
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev)

    There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m E En.
  induction En as [|n' En' IH].
  - apply E.
  - inversion E as [|n'' E' H].
    + apply IH in E'. apply E'.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint:  is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  assert (H: ev ((n + n) + (m + p))).
  { 
    rewrite <- add_assoc.
    rewrite (add_assoc n m).
    rewrite (add_comm n m).
    rewrite <- add_assoc.
    rewrite add_assoc.
    apply ev_sum.
    - apply Enm.
    - apply Enp.
  }
  rewrite <- double_plus in H.
  apply (ev_ev__ev (double n) (m + p)) in H.
  - apply H.
  - apply ev_double.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** ... And, just like properties, relations can be defined
    inductively.  One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition says that there are two ways to
    show that one number is less than or equal to another: either
    observe that they are the same number, or, if the second has the
    form [S m], give evidence that the first is less than or equal to
    [m]. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation: nat -> nat -> Prop :=
  | tt n m: total_relation n m.
(* [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation: nat -> nat -> Prop := .
(* [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros n m o H H0.
  induction H0 as [|n' H0 IH].
  - apply H.
  - apply le_S. apply IH.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [|n' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.  
  induction H as [|m' H IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [|m' IH].
  - intros n H. inversion H. 
    + apply le_n.
    + inversion H1.
  - intros n H.
    inversion H.
    + apply le_n.
    + apply IH in H1.
      apply le_S.
      apply H1.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.  induction n as [|n' IH].
  - destruct m as [|m'].
    + right. apply le_n.
    + left. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
  - destruct IH as [IH|IH].
    + inversion IH as [|m'].
      * right. apply le_n.
      * left. unfold lt. apply n_le_m__Sn_le_Sm. apply H.
    + right. apply le_S. apply IH. 
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [|b' IH].
  - rewrite <- plus_n_O. apply le_n.
  - rewrite add_comm.
    simpl.
    apply le_S.
    rewrite add_comm.
    apply IH.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H. split.
  - apply (le_trans _ (n1 + n2)).
    + apply le_plus_l.
    + apply H.
  - apply (le_trans _ (n1 + n2)).
    + rewrite add_comm. apply le_plus_l.
    + apply H.
Qed.

(** Hint: the next one may be easiest to prove by induction on [n]. *)

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n. induction n as [|n' IH].
  - intros m p q H. left. apply O_le_n.
  - intros m p q H.
    destruct p as [|p'] eqn:Hp.
    + right.  apply (le_trans _ (S n' + m)).
      * rewrite add_comm. apply le_plus_l.
      * apply H.
    + assert (H0: n' + S m <= p' + S q).
      { 
        rewrite add_comm.
        simpl.
        rewrite add_comm.
        rewrite (add_comm p').
        simpl.
        rewrite (add_comm q).
        apply H.
      }
      apply IH in H0.
      destruct H0 as [H0|H0].
      * left. apply n_le_m__Sn_le_Sm. apply H0.
      * right. apply Sn_le_Sm__n_le_m. apply H0.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p H. induction p as [|p' IH].
  - apply H.
  - simpl. apply n_le_m__Sn_le_Sm. apply IH.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  rewrite add_comm.
  rewrite (add_comm m).
  apply plus_le_compat_l.
  apply H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  apply (le_trans _ (n + p)).
  - apply le_plus_l.
  - apply plus_le_compat_r. apply H.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n [|m] H.
  - unfold lt in H. inversion H.
  - unfold lt in H. apply Sn_le_Sm__n_le_m in H. apply le_S. apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  unfold lt in H.
  unfold lt.
  split.
  - apply (le_trans _ (S (n1 + n2))). 
    + assert (H0: S (n1 + n2) = S n1 + n2).
      { reflexivity. }
      rewrite H0. apply le_plus_l.
    + apply H.
  - apply (le_trans _ (S (n1 + n2))). 
    + assert (H0: S (n1 + n2) = n1 + S n2).
      { rewrite plus_n_Sm. reflexivity. }
      rewrite H0. rewrite add_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m. 
  generalize dependent n.
  induction m as [|m' IH].
  - intros [|n'] H. 
    + apply le_n.
    + discriminate H.
  - intros [|n'] H.
    + apply O_le_n.
    + simpl in H.
      apply IH in H.
      apply n_le_m__Sn_le_Sm.
      apply H.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IH].
  - intros [|n'] H. 
    + reflexivity.
    + inversion H.
  - intros [|n'] H.
    + reflexivity.
    + apply Sn_le_Sm__n_le_m in H.
      apply IH in H.
      simpl.
      apply H.
Qed.
(** Hint: The next one can easily be proved without using [induction]. *)

 
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_correct.
  apply (le_trans n m).
  - apply H1.
  - apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff) *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2] [R 0 0 0 -> R 1 0 1 -> R 1 1 2].
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

      No. [c1], [c2], [c3], and [c4] are all symmetric about [n] and [m].

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

      No. [c1], [c2], [c3], and [c4] are cyclic.  *)

(* *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

Definition fR : nat -> nat -> nat := fun n m => n + m.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  split.
  - intros H. induction H.
    + reflexivity.
    + unfold fR. simpl. apply f_equal. apply IHR.
    + unfold fR. simpl. rewrite <- plus_n_Sm. apply f_equal. apply IHR.
    + unfold fR in IHR.
      rewrite <- plus_n_Sm in IHR.
      simpl in IHR.
      injection IHR as IHR.
      apply IHR.
    + unfold fR. rewrite add_comm. apply IHR.
  - generalize dependent o.
    generalize dependent n.
    induction m as [|m' IHm].
    + intros n. induction n as [|n' IHn].
      * intros o H. unfold fR in H. simpl in H. rewrite <- H. apply c1.
      * intros o H. unfold fR in H. simpl in H. rewrite <- H. apply c3.
        apply IHn. reflexivity.
    + intros n. induction n as [|n' IHn].
      * intros o H.
        unfold fR in H.
        rewrite <- plus_n_O in H.
        rewrite <- H.
        apply c2.
        apply IHm.
        rewrite <- plus_n_O.
        reflexivity.
      * intros [|o'] H.
        { simpl in H. discriminate. }
        {
          apply c3.
          apply IHn.
          rewrite add_comm in H.
          simpl in H.
          injection H as H.
          rewrite add_comm in H.
          apply H.
        }
Qed.
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
  | ss_refl l: subseq l l
  | ss_cons l1 l2 (x : nat) (H : subseq l1 l2) : subseq l1 (x :: l2)
  | ss_app l1 l2 (l3 : list nat) (H : subseq l1 l2) : subseq l1 (l2 ++ l3).


Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  apply ss_refl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  apply ss_app.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H H0.
  induction H0 as [l|l1' l2' x H0 IH|l1' l2' l3' H0 IH].
  - apply H.
  - apply ss_cons. apply IH. apply H.
  - apply ss_app. apply IH. apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]] [R 0 []] -> [R 1 [0]] -> [R 2 [1;0]]
    - [R 1 [1;2;1;0]] [R 0 []] -> ... -> [R 4 [1;2;1;]] -> [R 3 [1;2;1;0]] -> ...
    - [R 6 [3;2;1;0]]  No. *)

(* [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re].  (By "reserving" the notation before
    defining the [Inductive], we can use it in the definition.) *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

(** Again, for readability, we can also display this definition using
    inference-rule notation. *)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H|H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [|s ss IH].
  - apply MStar0.
  - simpl.
    simpl in H.
    apply MStarApp.
    + apply H. left. reflexivity. 
    + apply IH. intros s' H1. apply H. right. apply H1.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - (* induction s1 as [|h1 s1 IH].
    + intros H.
      destruct s2 as [|h2 s2].
      * reflexivity.
      * simpl in H. *)
    generalize dependent s1.
    induction s2 as [|h2 s2 IH].
    + intros s1 H. inversion H. reflexivity.
    + intros s1 H. simpl in H.
      destruct s1 as [|h1 s1].
      * inversion H.
        assert (Hs1: s1 = []).
        { destruct s1. reflexivity. discriminate H1. }
        rewrite Hs1 in H3. inversion H3.
      * inversion H.
        inversion H3.
        simpl.
        apply f_equal.
        apply IH.
        apply H4.
  - generalize dependent s1.
    induction s2 as [|h2 s2 IH].
    + intros s1 H. rewrite H. apply MEmpty.
    + intros s1 H.
      rewrite H.
      assert (H0: (h2 :: s2) = ([h2] ++ s2)).
      { reflexivity. }
      rewrite H0.
      apply MApp.
      * apply MChar.
      * apply IH. reflexivity.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2
  | Union r1 r2 => re_not_empty r1 || re_not_empty r2
  | Star _ => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros [s H].
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + simpl. rewrite IHexp_match. reflexivity.
    + simpl. rewrite IHexp_match. rewrite orb_true_iff. right. reflexivity.
    + reflexivity.
    + reflexivity.
  - intros H.
    induction re.
    + discriminate.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2).
      apply MApp. { apply H1. } { apply H2. }
    + simpl in H.
      apply orb_true_iff in H.
      destruct H as [H|H].
      * apply IHre1 in H. destruct H as [s H]. exists s. apply MUnionL. apply H.
      * apply IHre2 in H. destruct H as [s H]. exists s. apply MUnionR. apply H.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt.

    (We can begin by generalizing [s2], since it's pretty clear that we
    are going to have to walk over both [s1] and [s2] in parallel.) *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing"
    over the problematic expressions by adding explicit equality
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a
    tactic to automatically generate such equations for us, avoiding
    thus the need for changing the statements of our theorems. *)
Abort.

(** As we saw above, The tactic [remember e as x] causes Coq to (1)
    replace all occurrences of the expression [e] by the variable [x],
    and (2) add an equation [x = e] to the context.  Here's how we can
    use it to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre' as Heqre''. intros s H. apply H.

  - (* MStarApp *)
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre' as Heqre'.
    exists []. split.
    + reflexivity.
    + intros s' H.  destruct H.
  - assert (Heqre: re0 = re). { injection Heqre' as Heqre'. apply Heqre'. }
    apply IHexp_match2 in Heqre'.
    destruct Heqre' as [ss [Heqre' Heqre'']].
    exists (s1 :: ss).
    split.
    + simpl. apply f_equal. apply Heqre'.
    + simpl. intros s' [H'|H'].
      * rewrite <- H'. rewrite <- Heqre. apply H.
      * apply Heqre''. apply H'.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory.)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. rewrite app_length. intros H.
    apply add_le_cases in H.
    destruct H as [H|H].
    + apply IH1 in H.
      destruct H as [s11 [s12 [s13 [H' [H2 H3]]]]].
      exists s11. exists s12. exists (s13 ++ s2). split.
      * rewrite H'.
        rewrite app_assoc.
        rewrite app_assoc.
        rewrite app_assoc.
        reflexivity.
      * split. { apply H2. }
        { 
          intros m.
          rewrite app_assoc.
          rewrite app_assoc.
          apply MApp.  { rewrite <- app_assoc. apply H3. } { apply Hmatch2. }
        }
    + apply IH2 in H.
      destruct H as [s21 [s22 [s23 [H' [H2 H3]]]]].
      exists (s1 ++ s21). exists s22. exists s23. split.
      * rewrite H'. 
        rewrite app_assoc.
        rewrite app_assoc.
        reflexivity.
      * split. { apply H2. }
        { 
          intros m.
          rewrite <- app_assoc.
          apply MApp.  { apply Hmatch1. } { apply H3. }
        }
  - simpl. intros H. apply plus_le in H. destruct H as [H1 H2].
    apply IH in H1.
    destruct H1 as [s11 [s12 [s13 [H1' [H3 H4]]]]].
    exists s11. exists s12. exists s13. split.
    + apply H1'.
    + split. { apply H3. } { intros m. apply MUnionL. apply H4. }
  - simpl. intros H. apply plus_le in H. destruct H as [H1 H2].
    apply IH in H2.
    destruct H2 as [s11 [s12 [s13 [H2' [H3 H4]]]]].
    exists s11. exists s12. exists s13. split.
    + apply H2'.
    + split. { apply H3. } { intros m. apply MUnionR. apply H4. }
  - simpl. intros contra. inversion contra.
    apply pumping_constant_0_false in H0.
    destruct H0.
  - intros H. destruct s1 as [|h s1].
    + apply IH2 in H. apply H.
    + exists []. exists (h :: s1). exists s2. split.
      * reflexivity.
      * split. { discriminate. }
        {
          intros m.
          apply napp_star. { apply Hmatch1. } { apply Hmatch2. }
        }
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping)

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. rewrite app_length. intros H.
    assert (H0: pumping_constant (App re1 re2) <= length s1 + length s2).
    { apply H. }
    simpl in H0.
    apply add_le_cases in H.
    destruct H as [H|H].
    + (* [H: pumping_constant re1 <= length s1]. *)
      apply IH1 in H.
      destruct H as [s11 [s12 [s13 [H' [H2 [H3 H4]]]]]].
      exists s11. exists s12. exists (s13 ++ s2). split.
      * rewrite H'.
        rewrite app_assoc.
        rewrite app_assoc.
        rewrite app_assoc.
        reflexivity.
      * split. { apply H2. }
        { 
          split.
          {
            apply (le_trans _ (pumping_constant re1)).
            { apply H3. }
            { apply le_plus_l. }
          }
          {
            intros m.
            rewrite app_assoc.
            rewrite app_assoc.
            apply MApp.  { rewrite <- app_assoc. apply H4. } { apply Hmatch2. }
          }
        }
    + (* [H: pumping_constant re2 <= length s2]. *)
      apply IH2 in H.
      destruct H as [s21 [s22 [s23 [Hb [H2 [H3 H4]]]]]].
      remember (length s1) as a.
      remember (length s2) as b.
      remember (length s21 + length s22) as b1.
      remember (length s23) as b2.
      remember (pumping_constant re1) as m.
      remember (pumping_constant re2) as n.
      assert (H: a < m \/ a >= m ).
      { apply lt_ge_cases. }
      destruct H as [H|H].
      * (* [H: length s1 < pumping_constant re1]. *)
        apply n_lt_m__n_le_m in H.
        exists (s1 ++ s21). exists s22. exists s23. split.
        { rewrite Hb. rewrite <- app_assoc. reflexivity. }
        {
          split. { apply H2. }
          {
            split.
            {
              rewrite app_length.
              rewrite <- add_assoc.
              rewrite <- Heqa.
              rewrite <- Heqb1.
              apply (plus_le_compat_r _ _ b1) in H.
              apply (plus_le_compat_l _ _ m) in H3.
              apply (le_trans _ (m + b1)). { apply H. } { apply H3. }
            }
            { 
              intros m'.
              rewrite <- app_assoc.
              apply MApp.  { apply Hmatch1. } { apply H4. }
            }
          }
        }
      * (* [H: length s1 >= pumping_constant re1]. Use [IH1] to pump [s1]. *)
        apply IH1 in H.
        destruct H as [s11 [s12 [s13 [Ha [H5 [H6 H7]]]]]].
        remember (length s11 + length s12) as a1.
        remember (length s13) as a2.
        exists s11. exists s12. exists (s13 ++ s2). split.
        { rewrite Ha. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
        {
          split. { apply H5. }
          {
            split.
            {
              rewrite <- Heqa1.
              apply (le_trans _ m). { apply H6. } { apply le_plus_l. }
            }
            { 
              intros m'.
              rewrite app_assoc.
              rewrite app_assoc.
              apply MApp. { rewrite <- app_assoc. apply H7. } { apply Hmatch2. }
            }
          }
        }
  - (* MUnionL *)
    simpl. intros H. apply plus_le in H. destruct H as [H1 H2].
    apply IH in H1.
    destruct H1 as [s11 [s12 [s13 [H1' [H3 [H4 H5]]]]]].
    exists s11. exists s12. exists s13. split.
    + apply H1'.
    + split.
      * apply H3.
      * split.
        {
          apply (le_trans _ (pumping_constant re1)).
          { apply H4. } { apply le_plus_l. }
        }
        { intros m. apply MUnionL. apply H5. }
  - (* MUnionR *)
    simpl. intros H. apply plus_le in H. destruct H as [H1 H2].
    apply IH in H2.
    destruct H2 as [s11 [s12 [s13 [H2' [H3 [H4 H5]]]]]].
    exists s11. exists s12. exists s13. split.
    + apply H2'.
    + split.
      * apply H3.
      * split.
        {
          apply (le_trans _ (pumping_constant re2)).
          { apply H4. } { rewrite add_comm. apply le_plus_l. }
        }
        { intros m. apply MUnionR. apply H5. }
  - (* MStar0 *)
    simpl. intros contra. inversion contra.
    apply pumping_constant_0_false in H0.
    destruct H0.
  - (* MStarApp *)
    intros H0. 
    simpl in H0.
    simpl in IH2.
    rewrite app_length in H0.
    remember (length s1) as a.
    remember (length s2) as b.
    remember (pumping_constant re) as n.
    assert (H: a < n \/ a >= n ).
    { apply lt_ge_cases. }
    destruct H as [H|H].
    + (* [H: length s1 < pumping_constant re]. *)
      apply n_lt_m__n_le_m in H.
      destruct s1 as [|h s1].
      * (* [s1 = []]. *) 
        simpl in Heqa.
        simpl.
        rewrite <- Heqn.
        rewrite Heqa in H0.
        apply IH2 in H0.
        apply H0.
      * (* [s1 <> []]. *)
        exists []. exists (h :: s1). exists s2. split.
        { reflexivity. }
        {
          split. { discriminate. }
          {
            split.
            { rewrite <- Heqa. simpl. rewrite <- Heqn. apply H. }
            {
              intros m.
              apply napp_star. { apply Hmatch1. } { apply Hmatch2. }
            }
          }
        }
    + (* [H: length s1 >= pumping_constant re]. Use [IH1] to pump [s1]. *)
      apply IH1 in H.
      destruct H as [s11 [s12 [s13 [H' [H2 [H3 H4]]]]]].
      exists s11. exists s12. exists (s13 ++ s2). split.
      * rewrite H'.
        rewrite <- app_assoc.
        rewrite <- app_assoc.
        reflexivity.
      * split. { apply H2. }
        {
          split. { simpl. rewrite <- Heqn. apply H3. }
          {
            intros m.
            rewrite app_assoc.
            rewrite app_assoc.
            apply MStarApp. { rewrite <- app_assoc. apply H4. } { apply Hmatch2. }
          }
        }
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].  Instead of
    generating an equation such as [(n =? m) = true], which is
    generally not directly useful, this principle gives us right away
    the assumption we really need: [n = m].

    Following the terminology introduced in [Logic], we call
    this the "reflection principle for equality (between numbers),"
    and we say that the boolean [n =? m] is _reflected in_ the
    proposition [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  induction H.
  - split.
    + intros. reflexivity.
    + intros. apply H.
  - split.
    + intros. exfalso. apply H. apply H0.
    + intros. discriminate.
Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [rewrite] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l.
  induction l as [|h l IH].
  - simpl. intros H contra. apply contra.
  - simpl. intros H contra.
    destruct (eqbP n h) as [H0|H0].
    + discriminate.
    + apply IH.
      * apply H.
      * destruct contra.
        { exfalso. apply H0. symmetry. apply H1. }
        { apply H1. }
Qed.
(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | ns_nil : nostutter []
  | ns_single (x : X) : nostutter [x]
  | ns_cons (x1 x2 : X) (l : list X) (Heq : x1 <> x2) (H : nostutter (x2 :: l)) :
      nostutter (x1 :: x2 :: l).

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

Inductive in_order_merge {X : Type} (test : X -> bool) :
  list X -> list X -> list X -> Prop :=
  | m_nil : in_order_merge test [] [] []
  | m_true (h : X) (l1 l2 l : list X) (Htest : test h = true) 
      (H : in_order_merge test l l1 l2) :
      in_order_merge test (h :: l) (h :: l1) l2
  | m_false (h : X) (l1 l2 l : list X) (Htest: test h = false)
      (H : in_order_merge test l l1 l2) :
      in_order_merge test (h :: l) l1 (h :: l2)
.

Theorem in_order_merge_correct (X : Type) (test : X -> bool) (l l1 l2 : list X) :
  in_order_merge test l l1 l2 <->
    filter test l = l1 /\ filter (fun x => negb (test x)) l = l2.
Proof.
  split.
  - intros H.
    induction H as [|h l1 l2 l Htest H IH|h l1 l2 l Htest H IH].
    + split. { reflexivity. } { reflexivity. }
    + simpl. rewrite Htest. simpl. destruct IH as [IH IH']. split.
      * apply f_equal. apply IH.
      * apply IH'.
    + simpl. rewrite Htest. simpl. destruct IH as [IH IH']. split.
      * apply IH.
      * apply f_equal. apply IH'.
  - generalize dependent l2.
    generalize dependent l1.
    induction l as [|h l IH].
    + intros [] [] [H H'].
      * apply m_nil.
      * discriminate.
      * discriminate.
      * discriminate.
    + intros [] [] [H H'].
      * simpl in H. simpl in H'.
        destruct (test h). { discriminate. } { discriminate. }
      * simpl in H. simpl in H'.
        destruct (test h) eqn:Htest. { discriminate. } 
        {
          simpl in H'.
          injection H' as Hx H'.
          rewrite <- Hx.
          apply m_false. { apply Htest. }
          {
            apply IH.
            split. { apply H. } { apply H'. }
          }
        }
      * simpl in H. simpl in H'.
        destruct (test h) eqn:Htest.
        {
          simpl in H'.
          injection H as Hx H.
          rewrite <- Hx.
          apply m_true. { apply Htest. }
          {
            apply IH.
            split. { apply H. } { apply H'. }
          }
        }
        { discriminate. }
      * simpl in H. simpl in H'.
        destruct (test h) eqn:Htest.
        {
          simpl in H'.
          injection H as Hx H.
          rewrite <- Hx.
          apply m_true. { apply Htest. }
          {
            apply IH.
            split. { apply H. } { apply H'. }
          }
        }
        {
          simpl in H'.
          injection H' as Hx H'.
          rewrite <- Hx.
          apply m_false. { apply Htest. }
          {
            apply IH.
            split. { apply H. } { apply H'. }
          }
        }
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

Inductive filter_all_true {X : Type} (test: X -> bool) : list X -> Prop :=
  | f_nil : filter_all_true test []
  | f_cons (h : X) (l : list X) (H0: test h = true) (H: filter_all_true test l) :
      filter_all_true test(h :: l).

Lemma filter_length (X : Type) (l : list X) (test : X -> bool) :
  length (filter test l) <= length l.
Proof.
  induction l as [|h l IH].
  - simpl. apply le_n.
  - simpl. destruct (test h) eqn:H.
    + simpl. apply n_le_m__Sn_le_Sm. apply IH.
    + apply (le_trans _ (length l)).
      * apply IH.
      * apply le_S. apply le_n.
Qed.

Lemma filter_all_true_correct (X : Type) (l : list X) (test : X -> bool) :
  filter_all_true test l <-> filter test l = l.
Proof.
  split.
  - intros H. induction H as [|h l H0 H IH].
    + reflexivity.
    + simpl. rewrite H0. apply f_equal. apply IH.
  - intros H. induction l as [|h l IH].
    + apply f_nil.
    + assert (Htest: test h = true).
      {
        destruct (test h) eqn:Htest.
        { simpl in H. rewrite Htest in H. injection H as H. reflexivity. }
        {
          simpl in H.
          rewrite Htest in H.
          apply (f_equal _ _ length) in H.
          simpl in H.
          assert (H': length (filter test l) <= length l).
          { apply filter_length. }
          rewrite H in H'.
          assert (H2: forall n, S n <= n -> False).
          {
            induction n as [|n' IH'].
            { intros contra. inversion contra. }
            { intros contra. apply Sn_le_Sm__n_le_m in contra. contradiction. }
          }
          exfalso. apply (H2 (length l)). apply H'.
        }
      }
      simpl in H.
      rewrite Htest in H.
      injection H as H.
      apply f_cons.
      * apply Htest.
      * apply IH. apply H.
Qed.

Lemma filter_all_true_instance (X : Type) (test : X -> bool) (l : list X) :
  (forall x, test x = true) ->
  filter_all_true test l.
Proof.
  induction l as [|h l IH].
  - intros H. apply f_nil.
  - intros H. apply f_cons.
    + apply H.
    + apply IH. apply H.
Qed.

(*
Lemma filter_all_longest_length  (X : Type) :
  forall n (l : list X), length l = n ->
  (forall (test : X -> bool),
  filter_all_true test l <-> length (filter test l) = n).
Proof.
  intros n. induction n as [|n IH].
  - split.
    + intros H1. apply  destruct l as [|h l]. { reflexivity. } { discriminate H. }
    + intros H1. destruct l as [|h l]. { apply f_nil. } { discriminate H. }
  - split.
    + intros H1.
      destruct l as [|h l]. { discriminate H. }
      {
        apply
        injection H as H.
        destruct (test h) eqn:Htest.
        { 
          simpl.
          rewrite Htest.
          simpl.
          apply f_equal.
      }
    intros H1.
    + intros H1. d
    intros [|h l] H0 test H. { reflexivity. } { discriminate H0. }
    + discriminate H0.
    + simpl in H0.
      injection H0 as H0.

  - intros test' H. reflexivity.
  - intros test' H.
Qed.
 *)

Lemma filter_all_longest_induction (X : Type) (l : list X) (test0 : X -> bool):
  (forall (test : X -> bool), length (filter test l) <= length (filter test0 l)) ->
  length (filter test0 l) = length l.
Proof.
  induction l as [|h l IH].
  - intros H. reflexivity.
  - intros H. 
    assert (Htest0: test0 h = true).
    {
      destruct (test0 h) eqn:Htest0.  { reflexivity. }
      apply dist_not_exists in H.
      exfalso.
      apply H.
      remember (fun _: X => true) as test.
      exists test.
      apply Gt.gt_not_le.
      simpl.
      rewrite Htest0.
      simpl.
      assert (Hl: filter_all_true test l).
      { 
        apply filter_all_true_instance.
        rewrite Heqtest.
        reflexivity.
      } 
      apply filter_all_true_correct in Hl.
      rewrite Hl.
      rewrite Heqtest.
      simpl.
      unfold gt.
      unfold lt.
      apply n_le_m__Sn_le_Sm.
      apply filter_length.
    }
    simpl.
    rewrite Htest0.
    simpl.
    apply f_equal.
    apply IH.
    assert (H': ~ (exists test, length (filter test l) > length (filter test0 l))).
    {
      intros [test H'].
      apply dist_not_exists in H.
      apply H.
      exists test.
      apply Gt.gt_not_le.
      simpl.
      rewrite Htest0.
      destruct (test h) eqn:Htest.
      {
        simpl.
        apply n_le_m__Sn_le_Sm.
        unfold gt in H'.
        unfold lt in H'.
        apply H'.
      }
      {
        simpl.
        admit.
      }
    }

    (* apply not_exists_dist. *)

    simpl.
    remember (length l) as n eqn:Hl.
    symmetry in Hl.
    assert (H'': forall test, length (filter test l) <=
    length (filter test (h :: l)) <= S (length (filter test l))).
    {
      admit.
    }
Admitted.

Theorem filter_all_longest (X : Type) :
  forall (l : list X) (test0 : X -> bool),
  filter_all_true test0 l <-> 
  forall (test : X -> bool), length (filter test l) <= length (filter test0 l).
Proof.
  split.
  - intros H. induction H as [|h l H0 H IH].
    + intros test. apply le_n.
    + intros test.
      apply filter_all_true_correct in H.
      assert (H1: length (filter test (h :: l)) <= length (h :: l)).
      { apply filter_length. }
      simpl.
      rewrite H.
      rewrite H0.
      apply H1.
  - induction l as [|h l IH].
    + intros test. apply f_nil.
    + intros H0. 
      remember (fun _ : X => true) as Hf.
      assert (H: filter_all_true Hf l).
      { apply filter_all_true_instance. rewrite HeqHf. reflexivity. }
      assert (H1: test0 h = true).
      {
        apply dist_not_exists in H0.
        destruct (test0 h) eqn:Htest.
        { reflexivity. }
        {
          simpl in H0. 
          exfalso.
          apply H0.
          exists Hf.
          assert (Hfh: Hf h = true). { rewrite HeqHf. reflexivity. } 
          rewrite Hfh.
          rewrite Htest.
          intros contra.
          apply filter_all_true_correct in H.
          rewrite H in contra.
          simpl in contra.
          assert (H1: length (filter test0 l) < S (length l)).
          { unfold lt. apply n_le_m__Sn_le_Sm. apply filter_length. }
          apply Gt.gt_not_le in H1.
          contradiction.
        }
      }
      apply f_cons. { apply H1. }
      { 
        apply IH.
        intros test'.
        assert (H2: length (filter test' (h :: l)) <= length (filter test0 (h :: l))).
        { apply H0. }
        destruct (test' h) eqn:Htest'.
        {
          simpl in H2.
          rewrite Htest' in H2.
          rewrite H1 in H2.
          simpl in H2.
          apply Sn_le_Sm__n_le_m in H2.
          apply H2.
        }
        (*
        {
          simpl in H2.
          rewrite Htest' in H2.
          rewrite H1 in H2.
          simpl in H2.
          (* apply Sn_le_Sm__n_le_m in H2. *)
          apply H2.

          assert (H2: length (filter test' (h :: l)) <= length (filter test0 (h :: l))).
          { apply H0. }
          simpl in H2.
          rewrite H1 in H2.
          rewrite Htest' in H2.
          simpl in H2.
          apply Sn_le_Sm__n_le_m.
          apply H2.
        }
        {
          assert (H2: length (filter test' (h :: l)) <= length (filter test0 (h :: l))).
          { apply H0. }
          (* apply dist_not_exists in H0. *)
          simpl in H2.
          rewrite H1 in H2.
          rewrite Htest' in H2.
          simpl in H2.
          admit. (* It might need the [excluded_middle] rule. *)
        }
         *)
        admit.
Admitted.
(* [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
  | p_nil : pal []
  | p_single (x : X) : pal [x]
  | p_cons (x : X) (l : list X) (H: pal l) : pal (x :: l ++ [x]).

Theorem pal_app_rev (X : Type) :
  forall (l : list X), pal (l ++ rev l).
Proof.
  intros l.
  induction l as [|h l IH].
  - apply p_nil.
  - simpl. rewrite app_assoc. apply p_cons. apply IH.
Qed.


Theorem pal_rev (X : Type) :
  forall (l : list X), pal l -> l = rev l.
Proof.
  intros l H.
  induction H as [|x|x l H IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl. apply f_equal. 
    apply (f_equal _ _ (fun l => l ++ [x])). apply IH.
Qed.
(* [] *)

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Lemma pal_rev_inv_length (X : Type) :
  forall (n : nat) (l : list X), length l <= n -> l = rev l -> pal l.
Proof.
  intros n. induction n as [|n IH].
  - intros [|h l] H.
    + intros. apply p_nil.
    + simpl in H. apply Gt.le_not_gt in H. exfalso. apply H. apply Gt.gt_Sn_O.
  - intros [|h l] H.
    + intros. apply p_nil.
    + simpl.
      destruct (rev l) as [|h' l'] eqn:Hrevl.
      * intros H1. simpl in H1. injection H1 as H1. rewrite H1. apply p_single.
      * intros H1. injection H1 as H1 H2. rewrite H2. apply p_cons. apply IH.
        {
          simpl in H.
          apply Sn_le_Sm__n_le_m in H.
          apply (f_equal _ _ length) in H2.
          rewrite app_length in H2.
          rewrite add_comm in H2.
          simpl in H2.
          apply (le_trans _ (length l)).
          { rewrite H2. apply le_S. apply le_n. }
          { apply H. }
        }
        { 
          rewrite H2 in Hrevl.
          rewrite rev_app_distr in Hrevl.
          simpl in Hrevl.
          injection Hrevl as _ Hrevl.
          symmetry.
          apply Hrevl.
        }
Qed.

Theorem pal_rev_inv (X : Type) :
  forall (l : list X), l = rev l -> pal l.
Proof.
  intros l.
  apply (pal_rev_inv_length _ (length l)).
  apply le_n.
Qed.

(* [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Fixpoint disjoint {X : Type} (l1 l2 : list X) : Prop := 
  match l1, l2 with
  | [], [] => True
  | [], _ => True
  | _, [] => True
  | h1 :: l1', h2 :: l2' =>
      h1 <> h2 /\ ~ In h1 l2' /\ ~ In h2 l1' /\ disjoint l1' l2'
  end. 

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup {X : Type} : list X -> Prop :=
  | nd_nil : NoDup []
  | nd_cons (x : X) (l : list X) (H0 : ~ In x l) (H : NoDup l) : NoDup (x :: l).


(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Lemma app_nil_is_nil (X : Type) :
  forall (l1 l2 : list X), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros [|h l1] l2 H.
  - split. { reflexivity. } { simpl in H. apply H. }
  - split. { discriminate. } { discriminate. }
Qed.

Lemma disjoint_sym (X : Type) :
  forall (l1 l2 : list X), disjoint l1 l2 -> disjoint l2 l1.
Proof.
  intros l1. induction l1 as [|h1 l1 IH].
  - intros [|h2 l2] H. { apply I. } { apply I. }
  - intros [|h2 l2] H. { apply I. }
    destruct H as [H12 [H1 [H2 H]]].
    simpl.
    split. { apply not_eq_sym. apply H12. }
    split. { apply H2. }
    split. { apply H1. }
    apply IH.
    apply H.
Qed.

Lemma disjoint_nil_r (X : Type) : forall (l : list X), disjoint [] l.
Proof.
  intros [|h l]. { apply I. } { apply I. }
Qed.

Lemma disjoint_nil_l (X : Type) : forall (l : list X), disjoint l [].
Proof.
  intros. apply disjoint_sym. apply disjoint_nil_r.
Qed.

Lemma disjoint_cons_r (X : Type) :
  forall (l1 l2 : list X) (x : X),
  (disjoint l1 l2 /\ ~ In x l1) <-> disjoint l1 (x :: l2).
Proof.
  split.
  - generalize dependent x.
    generalize dependent l2.
    induction l1 as [|h1 l1 IH].
    + intros l2 x [H H0]. apply disjoint_nil_r.
    + intros l2 x [H H0].
      simpl in H0.
      apply Decidable.not_or in H0.
      destruct H0 as [H1 Hl1].
      simpl.
      split. { apply H1. }
      split.
      {
        destruct l2 as [|h2 l2]. { auto. }
        {
          destruct H as [H12 [Hin12 [Hin21 H]]].
          intros [contra|contra]. { auto. } { auto. }
        }
      }
      split. { auto. }
      {
        destruct l2 as [|h2 l2]. { apply disjoint_nil_l. }
        destruct H as [H12 [Hin12 [Hin21 H]]].
        apply IH. split. { apply H. } { apply Hin21. }
      }
  - generalize dependent x.
    generalize dependent l2.
    induction l1 as [|h1 l1 IH].
    + intros l2 x H. split. { apply disjoint_nil_r. } { auto. }
    + intros l2 x H. 
      destruct H as [Hh1x [Hh1inl2 [Hxinl1 H]]].
      * destruct l2 as [|h2 l2].
        split. { apply disjoint_nil_l. }
        {
          simpl.
          intros [contra|contra]. { contradiction. } { contradiction. }
        }
        split.
        {
          apply IH in H.
          destruct H as [H Hh2inl1].
          simpl.
          simpl in Hh1inl2.
          apply Decidable.not_or in Hh1inl2.
          destruct Hh1inl2 as [Hh1h2 Hh1inl2].
          split. { apply not_eq_sym in Hh1h2. apply Hh1h2. }
          split. { apply Hh1inl2. }
          split. { apply Hh2inl1. }
          { apply H. }
        }
        {
          simpl.
          intros contra.
          destruct contra as [contra|contra].
          { contradiction. } { contradiction. }
        }
Qed.

Lemma disjoint_cons_l (X : Type) :
  forall (l1 l2 : list X) (x : X),
  (disjoint l1 l2 /\ ~ In x l2) <-> disjoint (x :: l1) l2.
Proof.
  split.
  - intros [H H0]. apply disjoint_sym. apply disjoint_cons_r.
    split. { apply disjoint_sym. apply H. } { apply H0. }
  - intros H. apply disjoint_sym in H. apply disjoint_cons_r in H.
    split. { apply disjoint_sym. apply H. } { apply H. }
Qed.

Lemma disjoint_app_r (X : Type) :
  forall (l l1 l2 : list X), 
  (disjoint l l1 /\ disjoint l l2) <-> disjoint l (l1 ++ l2).
Proof.
  split.
  - generalize dependent l2.
    generalize dependent l1.
    induction l as [|h l IH].
    + intros l1 l2 [H1 H2]. apply disjoint_nil_r.
    + intros [|h1 l1] [|h2 l2] [H1 H2].
      * apply I.
      * apply H2.
      * rewrite app_nil_r. apply H1.
      * simpl in H1.
        simpl in H2.
        destruct H1 as [Hh1 [Hinl1 [H1inl H1]]].
        destruct H2 as [Hh2 [Hinl2 [H2inl H2]]].
        simpl.
        split. { apply Hh1. }
        split. 
        {
          intros H'.
          apply In_app_iff in H'.
          destruct H' as [H'|H'].
          { contradiction. } 
          {
            simpl in H'.
            destruct H' as [H'|H'].
            { symmetry in H'. contradiction. }
            { contradiction. }
          }
        }
        {
          split. { intros contra. contradiction. }
          {
            apply IH. split. { apply H1. }
            apply disjoint_cons_r. split. { apply H2. } { apply H2inl. }
          } 
        }
  - generalize dependent l2.
    generalize dependent l1.
    induction l as [|h l IH].
    + intros l1 l2 H. split. { apply disjoint_nil_r. } { apply disjoint_nil_r. }
    + intros [|h1 l1] [|h2 l2] H.
      * split. { apply disjoint_nil_l. } { apply disjoint_nil_l. }
      * split. { apply disjoint_nil_l. }
        destruct H as [Hhh2 [Hhinl2 [Hh2inl H]]].
        split. { apply Hhh2. }
        split. { apply Hhinl2. }
        split. { apply Hh2inl. }
        { apply H. }
      * rewrite app_nil_r in H.
        destruct H as [Hhh2 [Hhinl2 [Hh2inl H]]].
        simpl. split.
        split. { apply Hhh2. }
        split. { apply Hhinl2. }
        split. { apply Hh2inl. }
        { apply H. }
        apply I.
      * destruct H as [Hhh1 [Hhinl2 [Hh1inl H]]].
        apply IH in H.
        destruct H as [H1 H2].
        split.
        split. { apply Hhh1. }
        split. 
        {
          intros contra.
          apply Hhinl2.
          apply In_app_iff.
          left.
          apply contra.
        }
        split. { apply Hh1inl. }
        { apply H1. }
        {
          apply disjoint_cons_r in H2.
          destruct H2 as [H2 Hh2inl].
          simpl. split. 
          {
            intros contra.
            apply Hhinl2.
            apply In_app_iff.
            right. simpl. left. auto.
          }
          split. 
          { 
            intros contra.
            apply Hhinl2.
            apply In_app_iff.
            right. simpl. right. auto.
          }
          split. { apply Hh2inl. }
          { apply H2. }
        }
Qed.

Lemma disjoint_app_l (X : Type) :
  forall (l l1 l2 : list X), 
  (disjoint l1 l /\ disjoint l2 l) <-> disjoint (l1 ++ l2) l.
Proof.
  split.
  - intros [H1 H2]. apply disjoint_sym. apply disjoint_app_r.
    split. { apply disjoint_sym. apply H1. } { apply disjoint_sym. apply H2. }
  - intros H. apply disjoint_sym in H. apply disjoint_app_r in H.
    destruct H as [H1 H2].
    split. { apply disjoint_sym. apply H1. } { apply disjoint_sym. apply H2. }
Qed.

Theorem no_dup_app_is_disjoint (X : Type) :
  forall (l1 l2 : list X), NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros l1. induction l1 as [|h1 l1 IH].
  - intros l2 H. apply disjoint_nil_r. 
  - intros l2 H.
    inversion H as [|h1' l1' H0 H' Hh1].
    apply IH in H'.
    apply disjoint_cons_l.
    split. { apply H'. }
    { intros contra. apply H0. apply In_app_iff. right. apply contra. }
Qed.

Theorem no_dup_iff_disjoint_splittable (X : Type) :
  forall (l : list X), NoDup l <-> 
  (forall (l1 l2 : list X), l = l1 ++ l2 -> disjoint l1 l2).
Proof.
  split.
  - intros H. induction H as [|h l H0 Hnd IH].
    + intros l1 l2 H. symmetry in H.
      apply app_nil_is_nil in H.
      destruct H as [H1 H2].
      rewrite H1.
      rewrite H2.
      apply I.
    + intros [|h1 l1] [|h2 l2] H.
      * apply I.
      * apply disjoint_nil_r.
      * apply disjoint_nil_l.
      * simpl in H.
        inversion H.
        simpl.
        rewrite H3 in H0.
        split. 
        {
          intros contra.
          apply H0.
          apply In_app_iff.
          right. left. symmetry. rewrite H2. apply contra.
        }
        split.
        {
          intros contra.
          apply H0.
          apply In_app_iff.
          right. right. rewrite H2. apply contra.
        } 
        apply IH in H3.
        apply disjoint_cons_r in H3.
        apply and_commut.
        apply H3.
  - induction l as [|h l IH].
    + intros H. apply nd_nil.
    + intros H.
      assert (Hl: h :: l = [h] ++ l).
      { reflexivity. }
      apply H in Hl.
      destruct l as [|h' l'].
      * apply nd_cons. { intros contra. apply contra. } { apply nd_nil. }
      * simpl in Hl.
        destruct Hl as [Hhh' [Hhinl' [_ _]]].
        apply nd_cons.
        {
          simpl.
          intros contra.
          destruct contra as [contra|contra].
          { symmetry in contra. contradiction. } { contradiction. }
        }
        apply IH.
        intros l1 l2 H12.
        assert (H12': h :: h' :: l' = (h :: l1) ++ l2).
        { simpl. apply f_equal. apply H12. }
        apply H in H12'.
        apply disjoint_cons_l in H12'.
        apply H12'.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l as [|h l IH].
  - simpl. intros contra. destruct contra.
  - simpl. intros [H|H].
    + exists []. exists l. rewrite H. reflexivity.
    + apply IH in H.
      destruct H as [l1 [l2 H]].
      exists (h :: l1). exists l2.
      rewrite H. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rp_cons (x : X) (l : list X) (H : In x l \/ repeats l) : repeats (x :: l).

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Lemma remove_one (X : Type) (x : X) l (H : In x l) :
  exists l', (forall x', x <> x' -> In x' l -> In x' l') /\
  (length l = S (length l')). 
Proof.
  induction l as [|h l IH].
  - inversion H.
  - destruct H as [H|H].
    + exists l. split.
      * intros x' Hneq Hin.
        destruct Hin as [Heq|Hin].
        { rewrite H in Heq. contradiction. }
        { apply Hin. }
      * reflexivity.
    + apply IH in H.
      destruct H as [l' [H1 H2]].
      exists (h :: l').
      split.
      * simpl. intros x' Hneq [Heq|H].
        { left. apply Heq. }
        { right. apply H1. { apply Hneq. } { apply H. } }
      * simpl. rewrite H2. reflexivity.
Qed.

Lemma nil_not_repeats (X : Type) : ~ (@repeats X []).
Proof.
  intros H. inversion H.
Qed.

Lemma single_not_repeats (X : Type) (x : X) : ~ (repeats [x]).
Proof.
  intros H. inversion H. destruct H1. { destruct H1. } { inversion H1. }
Qed.

Fixpoint unique {X : Type} (l : list X) :=
  match l with
  | [] => True
  | h :: l' => ~ In h l' /\ unique l'
  end.

Definition subset {X : Type} (l1 l2 : list X) := 
  forall x, In x l1 -> In x l2.

Lemma pigeonhole_lemma (X : Type) :
  forall (l1 l2 : list X),
  subset l1 l2 -> length l2 < length l1 -> ~ unique l1.
Proof.
  induction l1 as [|h1 l1 IH].
  - intros l2 Hsub Hl Hu. inversion Hl.
  - intros l2 Hsub Hl Hu. 
    destruct (remove_one X h1 l2) as [l2' H'].
    { apply Hsub. left. reflexivity. }
    destruct H' as [Hsub' Hl'].
    destruct Hu as [Hnotin Hu].
    apply (IH l2').
    + intros x Hxinl1. apply Hsub'.
      { intros Hneq. apply Hnotin. rewrite Hneq. apply Hxinl1. }
      { apply Hsub. right. apply Hxinl1. }
    + rewrite Hl' in Hl. apply Lt.lt_S_n. apply Hl.
    + apply Hu.
Qed.

Lemma not_unique_repeats (X : Type) :
  forall (l : list X), ~ unique l -> repeats l.
Proof.
  induction l.
  - simpl. intros H. contradiction. 
  - intros H. simpl in H.
    apply rp_cons.
    right.
    apply IHl.
    intros Hu.
    apply H.
    destruct l as [|h l].
    + exfalso. apply H. split. { intros H'. inversion H'. } { apply I. }
    + 
Admitted.

Lemma subset_cons (X : Type):
  forall (x : X) (l1 l2 : list X),
  subset (x :: l1) l2 <-> In x l2 \/ subset l1 l2.
Proof.
  split.
  - generalize dependent l2.
    induction l1 as [|h1 l1 IH].
    + intros l2 H. right. unfold subset. intros x' contra. inversion contra.
    + intros l2 H.
Admitted.

Lemma not_unique_repeats': excluded_middle ->
  forall (X : Type) (l : list X), ~ unique l -> repeats l.
Proof.
  intros EM X l.
  induction l.
  - simpl. intros H. contradiction. (*{ intros H. inversion H. }*)
  - intros H. apply rp_cons. simpl in H. 
    assert (H': ~ (~ In x l /\ ~ repeats l)).
    { 
      intros [Hin Hr].
      apply Hr.
      apply IHl.
      intros Hu.
      apply H.
      split. { apply Hin. } { apply Hu. }
    }
    assert (DM: Logic.de_morgan_not_and_not).
    {
      intros P Q HPQ.
      destruct (EM (P \/ Q)) as [[HP|HQ]|HPQ']. 
      { left. apply HP. }
      { right. apply HQ. }
      { exfalso. apply HPQ. split.
        { intros HP. apply HPQ'. left. apply HP. }
        { intros HQ. apply HPQ'. right. apply HQ. }
      }
    }
    apply DM in H'.
    apply H'.
Qed.

Theorem pigeonhole_principle: excluded_middle ->
  forall (X : Type) (l1 l2 : list X),
  subset l1 l2 -> length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1 l2 Hsub Hl.
  apply not_unique_repeats'. { apply EM. }
  { apply (pigeonhole_lemma X l1 l2). { apply Hsub. } { apply Hl. } }
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H.
    destruct s1 as [|a1 s1].
    + left. split. { apply H3. } { apply H4. }
    + right. injection H1 as H5 H6. exists s1. exists s2.
      split. { symmetry. apply H6. }
      split. { rewrite <- H5. apply H3. }
      { apply H4. }
  - intros [[H0 H1]|[s1 [s2 [H0 [H1 H2]]]]].
    + apply (MApp [] _ (a :: s) _ H0 H1).
    + rewrite H0. apply (MApp (a :: s1) _ s2 _ H1 H2).
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  - intros .
    assert (H1: a :: s =~ Star re). { apply H. }
    remember (a :: s) as s0.
    remember (Star re) as re0.
    induction H.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct s1.
      * apply IHexp_match2 in Heqs0. apply Heqs0. apply Heqre0. apply H0.
      * injection Heqs0 as Hx Heqs0.
        exists s1. exists s2.
        split. { symmetry. apply Heqs0. }
        split. { injection Heqre0 as H'. rewrite Hx in H. rewrite H' in H. apply H. }
        { apply H0. }
  - intros [s0 [s1 [Happ [Hre Hstar]]]].
    assert (Happ': (a :: s = (a :: s0) ++ s1)).
    { simpl. apply f_equal. apply Happ. }
    rewrite Happ'.
    apply (MStarApp (a :: s0) s1 re Hre Hstar ).
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool :=
  match re with
  | EmptyStr => true
  | App re1 re2 => match_eps re1 && match_eps re2
  | Union re1 re2 => match_eps re1 || match_eps re2
  | Star _ => true
  | _ => false
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)
    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros re. induction re.
  - apply ReflectF. intros contra. inversion contra.
  - apply ReflectT. apply MEmpty.
  - apply ReflectF. intros contra. inversion contra.
  - apply reflect_iff in IHre1.
    apply reflect_iff in IHre2.
    unfold match_eps. fold match_eps.
    destruct (match_eps re1).
    + destruct (match_eps re2).
      * apply ReflectT. 
        rewrite <- (app_nil_r _ []).
        apply MApp. { apply IHre1. reflexivity. } { apply IHre2. reflexivity. }
      * apply ReflectF.
        intros contra. inversion contra.
        apply app_nil_is_nil in H0.
        destruct IHre2 as [IHre2 _].
        destruct H0 as [Hs1 Hs2].
        rewrite Hs2 in H3. 
        apply IHre2 in H3.
        discriminate.
    + apply ReflectF.
      intros H. apply app_exists in H. destruct H as [s1 [s2 [Hs [Hre1 Hre2]]]].
      symmetry in Hs. apply app_nil_is_nil in Hs. destruct Hs as [Hs1 _].
      rewrite Hs1 in Hre1. 
      apply IHre1 in Hre1.
      discriminate.
  - apply reflect_iff in IHre1.
    apply reflect_iff in IHre2.
    unfold match_eps. fold match_eps.
    destruct (match_eps re1).
    + apply ReflectT. apply MUnionL. apply IHre1. reflexivity.
    + destruct (match_eps re2).
      * apply ReflectT. apply MUnionR. apply IHre2. reflexivity.
      * apply ReflectF.
        intros H. apply union_disj in H. destruct H as [H|H].
        { apply IHre1 in H. discriminate. }
        { apply IHre2 in H. discriminate. }
  - apply ReflectT. apply MStar0.
Qed.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    ybe to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)
Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.


(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char t => if eqb a t then EmptyStr else EmptySet
  | App re1 re2 => if match_eps re1 
      then Union (derive a re2) (App (derive a re1) re2) 
      else App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re' => App (derive a re') (Star re')
  end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

Eval simpl in (derive c (App (Char c) EmptyStr)).

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

Eval simpl in (derive c (App EmptyStr (Char c))).

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

Eval simpl in (derive c (Star (Char c))).
Eval simpl in (derive c (derive c (Star (Char c)))).

(** "ccc" =~ Star (Char c) : *)
Example test_der8 :
  match_eps (derive c (derive c (derive c (Star (Char c))))) = true.
Proof. reflexivity. Qed.

(** "cccd" =~ App (Star (Char c)) (Char d): *)
Example test_der9 :
  match_eps (derive d (derive c (
    derive c (derive c (
    App (Star (Char c)) (Char d)))))) = true.
Proof. reflexivity. Qed.

(** "cdcddcc" =~ (cd)*(dc)*c
 App (App (Star (App (Char c) (Char d)) (Star (App (Char d) (Char c)))) (Char c)): *)
Example test_der10 :
  match_eps 
    (derive c (derive c (derive d (derive d (derive c (derive d (derive c 
      (App 
        (App 
          (Star (App (Char c) (Char d)))
          (Star (App (Char d) (Char c)))
        )
        (Char c)
      )
    ))))))) = true.
Proof. reflexivity. Qed.

(** "cdcdcc" =~ (cd)*cc
 App (App (Star (App (Char c) (Char d)) (Star  (Char c))) (Char c)): *)
Example test_der11 :
  match_eps 
    (derive c (derive c (derive d (derive c (derive d (derive c 
      (App 
        (App 
          (Star (App (Char c) (Char d)))
          (Char c)
        )
        (Char c)
      )
    )))))) = true.
Proof. reflexivity. Qed.


(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)

Lemma derive_corr : derives derive.
Proof.
  unfold derives.
  intros a re.
  induction re.
  - split. { intros H. inversion H. } { intros H. inversion H. }
  - split. { intros H. inversion H. } { intros H. inversion H. }
  - split.
    + intros H. inversion H. unfold derive. rewrite eqb_refl. apply MEmpty.
    + intros H. unfold derive in H. destruct (eqb_spec a t) as [Ha|Ha].
      { inversion H. rewrite Ha. apply MChar. } { inversion H. }
  - unfold is_der in IHre1. unfold is_der in IHre2. split.
    + intros H. unfold derive. fold derive. unfold derive. fold derive.
      destruct (match_eps_refl re1) as [Hre1|Hre1].
      * apply app_ne in H.
        destruct H as [[Hre1' Hre2]|[s1 [s2 [Hs [Hre1' Hre2']]]]].
        { apply IHre2 in Hre2. apply (MUnionL _ _ _ Hre2). }
        {
          apply IHre1 in Hre1'.
          rewrite Hs.
          apply MUnionR.
          apply (MApp _ _ _ _ Hre1' Hre2').
        }
      * apply app_ne in H.
        destruct H as [[Hre1' _]|[s1 [s2 [Hs [Hre1' Hre2']]]]]. { contradiction. }
        { apply IHre1 in Hre1'. rewrite Hs. apply (MApp _ _ _ _ Hre1' Hre2'). }

    + intros H. apply app_ne. unfold derive in H. fold derive in H.
      destruct (match_eps_refl re1) as [Hre1|Hre1].
      * apply union_disj in H. destruct H as [H|H].
        { left. split. { apply Hre1. } { apply IHre2. apply H. } }
        {
          apply app_exists in H.
          destruct H as [s1 [s2 [Hs [Hdre1 Hre2]]]].
          right. exists s1. exists s2.
          split. { apply Hs. }
          split. { apply IHre1. apply Hdre1. }
          { apply Hre2. }
        }
      * apply app_exists in H.
        destruct H as [s1 [s2 [Hs [Hdre1 Hre2]]]].
        right. exists s1. exists s2.
        split. { apply Hs. }
        split. { apply IHre1. apply Hdre1. }
        { apply Hre2. }
  - unfold is_der in IHre1. unfold is_der in IHre2. split.
    + intros H. apply union_disj in H.
      destruct H as [H|H].
      * apply IHre1 in H. unfold derive. apply union_disj. left. apply H.
      * apply IHre2 in H. unfold derive. apply union_disj. right. apply H.
    + intros H. apply union_disj. unfold derive in H. apply union_disj in H.
      destruct H as [H|H].
      { left. apply IHre1. apply H. } { right. apply IHre2. apply H. }
  - unfold is_der in IHre. split.
    + intros H. apply star_ne in H.
      destruct H as [s1 [s2 [Hs [Hre Hstar]]]].
      unfold derive. fold derive.
      apply app_exists. exists s1. exists s2.
      split. { apply Hs. }
      split. { apply IHre in Hre. apply Hre. }
      { apply Hstar. }
    + intros H. apply star_ne. unfold derive in H. fold derive in H.
      apply app_exists in H. destruct H as [s1 [s2 [Hs [Hre Hstar]]]].
      exists s1. exists s2.
      split. { apply Hs. }
      split. { apply IHre. apply Hre. }
      { apply Hstar. }
Qed.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | x :: s' => regex_match s' (derive x re)
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  unfold matches_regex.
  intros s. induction s as [|x s' IH].
  - apply match_eps_refl.
  - intros re. unfold regex_match. fold regex_match.
    destruct (IH (derive x re)) as [H|H].
    + apply ReflectT. apply derive_corr. apply H.
    + apply ReflectF. intros contra. apply H. apply derive_corr. apply contra.
Qed.
(** [] *)

(* 2021-08-11 15:08 *)
