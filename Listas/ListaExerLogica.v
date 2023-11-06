Require Export Coq.Lists.List.
Import ListNotations.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1 H2.
  destruct H2 as [x H3].
  apply H3.
  apply H1.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros H.
    destruct H as [x [H1 | H2]].
    + left. exists x. exact H1.
    + right. exists x. exact H2.
  - intros H.
    destruct H as [H1 | H2].
    + destruct H1 as [x H3].
      exists x. left. exact H3.
    + destruct H2 as [x H4].
      exists x. right. exact H4.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros X P Q H.
  destruct H as [x [H1 H2]].
  split.
  - exists x. exact H1.
  - exists x. exact H2.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [|y l' IHl].
  - simpl in H. contradiction.
  - simpl in H. destruct H as [H1 | H2].
    + left. rewrite H1. reflexivity.
    + right. apply IHl. exact H2.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
    intros A B c d e. split.
    induction d as [|m n].
      simpl. intros [].
      simpl. intros [H | H].
        exists m. split. apply H. left. reflexivity.
        apply IHn in H. destruct H as [j [l k]].
        exists j. split. apply l.
        right. apply k.
      intros [j [k l]]. rewrite <- k. apply In_map. apply l.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
    induction l as [|b c].
      simpl. intro. right. apply H.
      simpl. intros [].
        left. left. apply H.
        apply IHc in H. destruct H.
        left. right. apply H.
        right. apply H.
    induction l as [|b c].
      intros []. inversion H. simpl. apply H.
      intros []. simpl. inversion H.
        left. apply H0.
        right. apply IHc. left. apply H0.
        simpl. right. apply IHc. right. apply H.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P H1.
  apply H1.
  right.
  intros H2.
  apply H1.
  left.
  exact H2.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros P Q H1 H2.
  destruct H1 as [H3 | H4].
  - contradiction.
  - exact H4.
Qed.

Theorem Peirce_double_negation: forall (P:Prop),
  (forall Q: Prop, (((P->Q)->P)->P)) -> (~~ P -> P).
Proof.
  intros P H1 H2.
  apply H1.
  intros H3.
  apply H2.
  right.
  intros H4.
  apply H3.
  intros H5.
  apply H2.
  left.
  exact H5.
Qed.


Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (P:Prop), (~~ P -> P)) -> (P \/ ~P).
Proof.
  intros P H.
  apply H.
  intros H1.
  apply H1.
  right.
  intros H2.
  apply H1.
  left.
  exact H2.
Qed.
