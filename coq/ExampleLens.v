(* The main results formalized here are
   [weak_backward_bind]:
     weak backward round tripping is preserved by [bind].
   [weak_forward_bind]:
     weak forward round tripping is preserved by [bind]
     when the continuation is an injective arrow.
 *)

Require Import FunctionalExtensionality.
Require Import PeanoNat.
Require Import List.
Import ListNotations.

Require Import Promonad.

Record Lens (S U A : Type) : Type := {
  get : S -> option A;
  put : U -> option (A * (S -> option S) * (S -> bool));
}.

Arguments get {S U A}.
Arguments put {S U A}.

Definition bind {S U A B : Type}
           (m : Lens S U A) (k : A -> Lens S U B) : Lens S U B := {|
  get s := a <- get m s;; get (k a) s;
  put u :=
    abc <- put m u;;
    let '(a, f, p) := abc in
    def <- put (k a) u;;
    let '(b, g, q) := def in
    ret (b, fun x => y <- f x;; g y, fun x => (p x && q x)%bool)
|}.

Definition ret {S U A : Type} (a : A) : Lens S U A := {|
  get _ := Some a;
  put _ := Some (a, Some, fun _ => true);
|}.

Instance Monad_Lens S U : Monad (Lens S U) := {|
  Promonad.bind _ _ := bind;
  Promonad.ret _ := ret;
|}.

Definition weak_backward {S U A} (m : Lens S U A) : Prop :=
  forall u a f s' p,
    put m u = Some (a, f, p) ->
    p s' = true ->
    get m s' = Some a.

Lemma weak_backward_bind {S U A B} (m : Lens S U A)
      (k : A -> Lens S U B)
      (Hm : weak_backward m)
      (Hk : forall a, weak_backward (k a)) :
  weak_backward (bind m k).
Proof.
  intros u a f s' p Hu Hp.
  simpl in *.
  destruct (put m u) as [[[]] | ] eqn:eputm; try discriminate; simpl in *.
  destruct (put (k a0) u) as [[[]] | ] eqn:eputk; try discriminate; simpl in *.
  inversion Hu; subst; clear Hu.
  destruct (andb_prop _ _ Hp).
  replace (get m s') with (Some a0).
  { simpl. eapply Hk; eauto. }
  { symmetry. eapply Hm; eauto. }
Qed.

Definition weak_forward {S U A} (m : Lens S U A) : Prop :=
  forall u a f s p,
    get m s = Some a ->
    put m u = Some (a, f, p) ->
    f s = Some s.

Lemma weak_forward_bind {S U A B} (m : Lens S U A)
      (k : A -> Lens S U B) (i : B -> option A)
      (Hi : forall a,
          (x <- k a;; ret (i x)) = (x <- k a;; ret (Some a)))
      (Hm : weak_forward m)
      (Hk : forall a, weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros u b f s p Hget Hput.
  simpl in *.
  destruct (get m s) eqn:egetm; try discriminate; simpl in *.
  destruct (put m u) as [[[]] | ] eqn:eputm;
    try discriminate; simpl in *.
  destruct (put (k a0) u) as [[[]] | ] eqn:eputk;
    try discriminate; simpl in *.
  inversion Hput; subst; clear Hput.
  pose proof (Hi a).
  pose proof (Hi a0).
  apply (f_equal (fun l => get l s)) in H.
  apply (f_equal (fun l => put l u)) in H0.
  simpl in *.
  rewrite Hget in H; simpl in H.
  rewrite eputk in H0; simpl in H0.
  inversion H0; clear H0.
  inversion H; clear H.
  rewrite H2 in H1; inversion H1; clear H1; subst.
  replace (o s) with (Some s); [simpl | symmetry; eapply Hm; eauto ].
  eapply Hk; eauto.
Qed.

