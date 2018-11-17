(* Biparsers *)

(* The main results formalized here are
   [Compositional_weak_backward]:
     weak backward round tripping is compositional;
     in particular it is preserved by [bind] ([weak_backward_bind]).
   [Quasicompositional_weak_forward]:
     weak forward round tripping is quasicompositional;
     in particular it is preserved by [bind]
     when the continuation is an injective arrow
     ([weak_forward_bind]). *)

Typeclasses eauto := 6.
Generalizable Variables P.

Require Import FunctionalExtensionality.
Require Import PeanoNat.
Require Import List.
Import ListNotations.

Require Import Promonad.

(* Primitives *)

Definition t : Type := nat.

Class Biparser (P : Type -> Type -> Type) :=
  {
    Biparser_Promonad :> Promonad P;
    Biparser_Partial :> forall U, MonadPartial (P U);
    biparse_token : P t t;
  }.

Arguments biparse_token {P _}.

Instance Biparser_product P1 P2 `{Biparser P1, Biparser P2} :
  Biparser (Product P1 P2) :=
  { biparse_token := (biparse_token, biparse_token);
  }.

(*********************)
(* Example biparsers *)
(*********************)

Definition total {A B} (f : A -> B) : A -> option B :=
  fun a => Some (f a).

(* Get a single [nat] token less than b. *)
Definition biparse_digit `{Biparser P} (b : nat) : P nat nat :=
  x <- biparse_token ;;
  if Nat.leb b x then
    empty
  else
    ret x.

(* Parse a k-digit number in base b *)
Fixpoint biparse_nat `{Biparser P} (b : nat) (k : nat)
  : P nat nat :=
  match k with
  | O => ret 0
  | S k' =>
    x <-( fun z => Nat.div z b ) biparse_nat b k';;
    y <-( fun z => Nat.modulo z b ) biparse_digit b ;;
    ret (b * x + y)
  end.

(* Parse a length n followed by a list of nat-tokens ("string"). *)
Definition biparse_string `{Biparser P} : P (list nat) (list nat) :=
  n <-( @length _ ) biparse_nat 10 3;;
  replicate n biparse_token.

(*** Parser promonad ***)

Definition stream := list nat.

(* Parser monad *)
Definition parser (A : Type) : Type := stream -> option (A * stream).

Instance Monad_parser : Monad parser :=
  { ret A x := fun s => Some (x, s);
    bind A B m k := fun s =>
      bind (m s) (fun '(a, s') => k a s')
  }.

Instance MonadLaws_parser : MonadLaws Monad_parser := {}.
Proof.
  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    destruct (m s) as [ [ ] | ]; auto.

  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    auto.

  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    destruct (m s) as [ [ ] | ]; simpl; auto.
Qed.

Instance MonadPartial_parser : MonadPartial parser :=
  { empty := fun _ _ => None }.

Definition parser2 := Fwd parser.

Definition Promonad_parser2 := Promonad_Fwd parser.

Instance Biparser_parser2 : Biparser parser2 :=
  { biparse_token s :=
      match s with
      | [] => None
      | n :: s' => Some (n, s')
      end
  }.


(*** Printer promonad ***)

Definition printer (A : Type) := option (stream * A).

Instance Monad_printer : Monad printer :=
  { ret A a := Some ([], a);
    bind A B m k :=
      @bind option _ _ _ m (fun '(s, a) =>
      @bind option _ _ _ (k a) (fun '(s', b) =>
      Some (s ++ s', b)));
  }.

Instance MonadLaws_printer : MonadLaws Monad_printer := { }.
Proof.
  - intros.
    destruct m as [[]|]; auto.
    simpl.
    rewrite app_nil_r.
    auto.

  - intros.
    simpl.
    destruct (k a) as [[]|]; simpl; auto.

  - intros. simpl.
    destruct m as [[]|]; simpl; auto.
    destruct (k a) as [[]|]; simpl; auto.
    destruct (h b) as [[]|]; simpl; auto.
    rewrite app_assoc.
    auto.
Qed.

Instance MonadPartial_printer : MonadPartial printer :=
  { empty A := None }.

Instance MonadPartialLaws_printer :
  MonadPartialLaws (MonadPartial_printer) := {}.
Proof. auto. Qed.

Definition printer2 := Bwd printer.

Instance Biparser_printer2 : Biparser printer2 :=
  { biparse_token := (fun n => Some ([n], n));
  }.

Instance Biparser_pure : Biparser pfunction :=
  {|
    biparse_token := (fun n => Some n) : pfunction nat nat;
  |}.

(* Extract the pure component of the printer *)
Definition printer_to_pure {U A} : printer2 U A -> pfunction U A :=
  fun m u =>
    match m u with
    | None => None
    | Some (_, a) => Some a
    end.

(* printer_to_pure is a monad homomorphism. *)
Lemma ptp_ret_hom U A (a : A)
  : forall u, printer_to_pure (ret a) u = (ret a : pfunction U A) u.
Proof. intro; auto. Qed.

Lemma ptp_bind_hom U A B (m : printer2 U A) (k : A -> printer2 U B)
  : forall u,
    printer_to_pure (bind m k) u
    = bind (printer_to_pure m) (fun a => printer_to_pure (k a)) u.
Proof.
  intro.
  unfold printer_to_pure; simpl.
  destruct (m u) as [ [ ? a ] | ].
  - simpl; destruct (k a u) as [ [ ? b ] | ]; auto.
  - auto.
Qed.

(*********************************)
(* Toplevel roundtrip properties *)
(*********************************)

Definition left_round_trip A (P : A -> Prop)
           (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall a, P a ->
    match pr a with
    | None => True
    | Some (s, _) => pa s = Some (a, [])
    end.

(* We have proved [biparse_string_left_round_trip] *)

Definition right_round_trip A (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall s,
    match pa s with
    | None => True
    | Some (a, []) =>
      match pr a with
      | None => False
      | Some (s', _) => s = s'
      end
    | Some _ => True
    end.

Definition biparser : Type -> Type -> Type := Product parser2 printer2.

Definition purify {U V} (p : biparser U V) : pfunction U V :=
  fun a => bind_option (snd p a) (fun x => Some (snd x)).

Definition weak_backward {U A} (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s s' : list t),
    snd p u = Some (s, a) ->
    fst p (s ++ s') = Some (a, s').

Definition weak_forward {U A} (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s01 s1 s0 : list t),
    fst p s01 = Some (a, s1) ->
    snd p u = Some (s0, a) ->
    s01 = s0 ++ s1.

Lemma weak_backward_ret U A (a : A) : @weak_backward U A (ret a).
Proof.
  intros u b s s' e; inversion_clear e; reflexivity.
Qed.

Lemma weak_backward_comap U U' A (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_backward m) :
  weak_backward (comap f m).
Proof.
  intros u b s s' e.
  simpl in *.
  destruct (f u) eqn:ef; try discriminate.
  eauto.
Qed.

Lemma weak_backward_bind U A B
      (m : biparser U A) (k : A -> biparser U B)
      (Hm : weak_backward m)
      (Hk : forall a, weak_backward (k a)) :
  weak_backward (bind m k).
Proof.
  intros u b s s'.
  simpl.
  destruct (snd m u) as [ [s1 a] | ] eqn:em; simpl; try discriminate.
  destruct (snd (k a) u) as [ [s2 b'] | ] eqn:ek; simpl; try discriminate.
  intros Hmk.
  inversion Hmk.
  eapply Hm in em.
  eapply Hk in ek.
  rewrite <- app_assoc.
  rewrite em; simpl.
  rewrite ek.
  subst; reflexivity.
Qed.

Instance Compositional_weak_backward :
  Compositional biparser (@weak_backward) := {
  ret_comp := weak_backward_ret;
  bind_comp := weak_backward_bind;
  comap_comp := weak_backward_comap;
}.

Lemma weak_backward_empty U A :
  weak_backward (@empty (biparser U) _ _ A).
Proof.
  discriminate.
Qed.

Lemma weak_backward_token :
  weak_backward biparse_token.
Proof.
  intros u b s s' H; inversion H; subst; reflexivity.
Qed.

Lemma weak_forward_ret U A (a : A) : @weak_forward U A (ret a).
Proof.
  intros u b s s' s'' e e';
    inversion_clear e; inversion_clear e'; reflexivity.
Qed.

Lemma weak_forward_comap U U' A (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_forward m) :
  weak_forward (comap f m).
Proof.
  intros u b s s' s'' e e'.
  simpl in *.
  destruct (f u) eqn:ef; try discriminate.
  eauto.
Qed.

Lemma weak_forward_bind U A B
      (m : biparser U A) (k : A -> biparser U B) (f : B -> option A)
      (Hf : forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a)))
      (Hm : weak_forward m)
      (Hk : forall a, weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros u b s01 s1 s0 Hparse Hprint.
  simpl in *.
  destruct fst as [ [a1 s__m1] | ] eqn:em1 in Hparse; try discriminate;
    simpl in Hparse;
    destruct fst as [ [b1 s__mk1] | ] eqn:ek1 in Hparse; try discriminate;
    inversion Hparse; clear Hparse; subst.
  destruct snd as [ [s__m2 a2] | ] eqn:em2 in Hprint; try discriminate;
    simpl in Hprint;
    destruct snd as [ [s__mk2 b2] | ] eqn:ek2 in Hprint; try discriminate;
    inversion Hprint; clear Hprint; subst.
  assert (ea : a2 = a1).
  { pose proof (Hf a1) as Hf1.
    apply (f_equal (fun f => fst f s__m1)) in Hf1; simpl in Hf1.
    rewrite ek1 in Hf1; inversion Hf1.
    pose proof (Hf a2) as Hf2.
    apply (f_equal (fun f => snd f u)) in Hf2; simpl in Hf2.
    rewrite ek2 in Hf2; inversion Hf2.
    rewrite H0 in H1; inversion H1.
    reflexivity.
  }
  subst.
  specialize (Hm u a1 s01 s__m1 s__m2 em1 em2).
  specialize (Hk a1 u b s__m1 s1 s__mk2 ek1 ek2).
  subst.
  apply app_assoc.
Qed.

Instance Quasicompositional_weak_forward :
  Quasicompositional (@weak_forward) := {
  ret_comp' := weak_forward_ret;
  bind_comp' := weak_forward_bind;
  comap_comp' := weak_forward_comap;
}.

Lemma weak_forward_empty U A :
  weak_forward (@empty (biparser U) _ _ A).
Proof.
  discriminate.
Qed.

Lemma weak_forward_token :
  weak_forward biparse_token.
Proof.
  intros u b s s' s'' H1 H2.
  destruct s; simpl in *.
  - discriminate.
  - inversion H1; inversion H2; subst.
    reflexivity.
Qed.
