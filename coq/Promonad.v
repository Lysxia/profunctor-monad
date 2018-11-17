(* Promonad definitions *)

(* Some naming conventions
   - [M]: a monad
   - [P]: a promonad
   - [A], [B]: "view types", covariant parameters of [P] and [M]
   - [U], [V]: "pre-view types", contravariant parameters of [P]
   - [Q], [Q_A], [Q_B]: a property on (pre-)views [A -> Prop], [B -> Prop]
   - [R]: a property on (pro)monadic values, possibly indexed by [Q]
 *)

Generalizable Variables P.

Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.

Notation TyCon2 := (Type -> Type -> Type).

(*** Common functions ***)

Definition head A (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: _ => Some x
  end.

Definition tail A (xs : list A) : option (list A) :=
  match xs with
  | [] => None
  | _ :: xs' => Some xs'
  end.

Arguments head {A}.
Arguments tail {A}.

(*** Monads ***)

(* Operations *)
Class Monad (M : Type -> Type) :=
  { ret : forall A, A -> M A;
    bind : forall A B, M A -> (A -> M B) -> M B;
  }.

Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Notation "x <- m ;; k" := (bind m (fun x => k))
(at level 90, right associativity).

(* Laws *)
Class MonadLaws (M : Type -> Type) (Monad_M : Monad M) :=
  { bind_ret : forall A (m : M A), bind m ret = m;
    ret_bind : forall A B (a : A) (k : A -> M B), bind (ret a) k = k a;
    bind_bind : forall A B C (m : M A) (k : A -> M B) (h : B -> M C),
      bind (bind m k) h = bind m (fun a => bind (k a) h);
  }.

Arguments MonadLaws {M} Monad_M.

Definition map {M : Type -> Type} `{Monad_M : Monad M} {A B : Type}
           (f : A -> B) (m : M A) :=
  x <- m;; ret (f x).

(* Monads with failure *)
Class MonadPartial (M : Type -> Type) `{Monad M} :=
  { empty : forall A, M A }.

Arguments empty {M _ _ A}.

Class MonadPartialLaws (M : Type -> Type)
      `{MonadPartial_M : MonadPartial M} :=
  { partial_MonadLaws :> MonadLaws _;
    partial_left_zero : forall A B (k : A -> M B),
      bind empty k = empty;
  }.

Arguments MonadPartialLaws {_ _} MonadPartial_M.

Definition ret_opt {M : Type -> Type}
           `{Monad_M : Monad M} `{MonadPartial_M : MonadPartial M}
           {A : Type}
           (oa : option A) : M A :=
  match oa with
  | None => empty
  | Some a => ret a
  end.

Definition map_opt {M : Type -> Type}
           `{Monad_M : Monad M} `{MonadPartial_M : MonadPartial M}
           {A B : Type}
           (f : A -> option B) (m : M A) :=
  x <- m;; ret_opt (f x).

(** Example: the [option] monad **)

Definition bind_option {A B} (m : option A) (k : A -> option B) :=
  match m with
  | None => None
  | Some x => k x
  end.

Delimit Scope opt_scope with opt.
Bind Scope opt_scope with option.

Notation "x <- m ;; k" := (bind_option m (fun x => k))
(at level 90, right associativity) : opt_scope.

Instance Monad_option : Monad option :=
  {| ret _ a := Some a;
     bind := @bind_option;
  |}.

Instance MonadLaws_option : MonadLaws Monad_option := {}.
Proof.
  - intros A []; auto.
  - intros; auto.
  - intros A B C m k h; simpl.
    destruct m as [a|]; simpl; auto;
      destruct (k a) as [b|]; simpl; auto;
        destruct (h b); simpl; auto.
Qed.

Instance MonadPartial_option : MonadPartial option :=
  { empty _ := None }.

Instance MonadPartialLaws_option :
  MonadPartialLaws MonadPartial_option := {}.
Proof.
  auto.
Qed.

Fixpoint traverse_option {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs =>
    y <- f x;;
    ys <- traverse_option f xs;;
    ret (y :: ys)
  end.

Lemma traverse_option_pure {A B} (f : A -> option B) (xs : list A) :
  traverse_option (fun x => Some (f x)) xs = Some (List.map f xs).
Proof.
  induction xs; auto.
  simpl; rewrite IHxs; auto.
Qed.

(** Monad morphisms ***)

Class MonadMorphism {M N} `{Monad M} `{Monad N}
      (f : forall {A}, M A -> N A) :=
  { morph_ret : forall A (a : A), f (ret a) = ret a;
    morph_bind : forall A B (m : M A) (k : A -> M B),
        f (bind m k) = bind (f m) (fun a => f (k a));
  }.

(*** Promonads *)

Class Promonad (P : Type -> Type -> Type) :=
  { asMonad :> forall U, Monad (P U);
    comap :
      forall U V A, (U -> option V) -> P V A -> P U A
  }.

Arguments comap {P _ U V A} f.

Notation "x <-( f ?) m ;; m2" := (x <- comap f m ;; m2)
(at level 90, right associativity).

Notation "x <- m 'upon' f ;; m2" := (x <- comap f m ;; m2)
(at level 90, right associativity).

Notation "x <-( f ) m ;; m2" :=
  (x <- comap (fun z => Some (f z)) m ;; m2)
(at level 90, right associativity).

Class PromonadLaws (P : Type -> Type -> Type)
      (Promonad_P : Promonad P) :=
  { p_MonadLaws :> forall U, MonadLaws (@asMonad P Promonad_P U);
    comap_morphism :> forall U V (f : U -> V),
        MonadMorphism (fun A => comap (fun u => Some (f u)));
  }.

Arguments PromonadLaws {P} Promonad_P.

Lemma comap_morph_ret P `{PromonadLaws P} U V A
      (f : U -> V) (a : A) :
  comap (fun u => Some (f u)) (ret a) = ret a.
Proof.
  match goal with
  | [ |- ?comap1 _ = _ ] =>
    let comap' := (eval pattern A in comap1) in
    change (comap' (ret a) = ret a)
  end.
  apply morph_ret.
Qed.

Lemma comap_morph_bind P `{PromonadLaws P} U V A B
      (f : V -> U) (m : P U A) (k : A -> P U B) :
  let h A := comap (fun u => Some (f u)) : P U A -> P V A in
  h B (bind m k)
  = bind (h A m) (fun a => h B (k a)).
Proof.
  apply morph_bind.
Qed.

(** Promonad morphisms *)

Class PromonadMorphism {P Q : TyCon2}
      `{Promonad P} `{Promonad Q}
      (phi : forall U V, P U V -> Q U V) : Prop := {
    asMonadMorphism :> forall U, MonadMorphism (phi U);
    morph_comap : forall U U' V (f : U -> option U') (m : P U' V),
        phi _ _ (comap f m) = comap f (phi _ _ m);
  }.

(*** [Fwd] promonad ***)

Definition Fwd (M : Type -> Type) : TyCon2 :=
  fun U A => M A.

Instance Monad_Fwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Fwd M U) :=
  { ret A a := ret a;
    bind A B m k := bind m k;
  }.

Instance MonadLaws_Fwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Monad_Fwd M U).
Proof.
  intro U; constructor; apply H.
Qed.

Instance MonadPartial_Fwd (M : Type -> Type) `{MonadPartial M} :
  forall U, MonadPartial (Fwd M U) :=
  { empty _ := empty }.

Instance MonadPartialLaws_Fwd (M : Type -> Type)
         `{MonadPartialLaws M} :
  forall U, MonadPartialLaws (MonadPartial_Fwd M U) := {}.
Proof. intros; simpl; apply partial_left_zero. Qed.

Instance Promonad_Fwd (M : Type -> Type) `{Monad M} :
  Promonad (Fwd M) :=
  { comap U V A f m := m }.

Instance PromonadLaws_Fwd (M : Type -> Type) `{MonadLaws M} :
  PromonadLaws (Promonad_Fwd M) := {}.
Proof. intros U V f; split; auto. Qed.

(*** [Bwd] promonad ***)

Definition Bwd (M : Type -> Type) : Type -> Type -> Type :=
  fun U A => U -> M A.

Instance Monad_Bwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Bwd M U) :=
  { ret A a := fun u => ret a;
    bind A B m k := fun u => bind (m u) (fun a => k a u);
  }.

Instance MonadLaws_Bwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Monad_Bwd M U).
Proof.
  constructor;
    intros;
    apply functional_extensionality; intro u; simpl;
    apply H.
Qed.

Instance MonadPartial_Bwd (M : Type -> Type) `{MonadPartial M} :
  forall U, MonadPartial (Bwd M U) :=
  { empty _ := fun _ => empty }.

Instance MonadPartialLaws_Bwd (M : Type -> Type)
         `{MonadPartialLaws M} :
  forall U, MonadPartialLaws (MonadPartial_Bwd M U) := {}.
Proof.
  intros.
  apply functional_extensionality; intro u.
  simpl; apply partial_left_zero.
Qed.

Instance Promonad_Bwd (M : Type -> Type) `{MonadPartial M} :
  Promonad (Bwd M) :=
  { comap U V A f m := fun v =>
      match f v with
      | None => empty
      | Some u => m u
      end
  }.

Instance PromonadLaws_Bwd (M : Type -> Type) `{MonadPartialLaws M} :
  PromonadLaws (Promonad_Bwd M) := {}.
Proof.
  intros U V f.
  constructor; intros; apply functional_extensionality; intro u; auto.
Qed.

(*** Product promonad ***)

Definition Product (P1 P2 : Type -> Type -> Type) :=
  fun U A => (P1 U A * P2 U A)%type.

Instance Monad_Product P1 P2 U
         `{Monad (P1 U), Monad (P2 U)} :
  Monad (Product P1 P2 U) :=
  { ret A a := (ret a, ret a);
    bind A B m k :=
      (bind (fst m) (fun a => fst (k a)),
       bind (snd m) (fun a => snd (k a)));
  }.

Instance MonadLaws_Product P1 P2 U
         `{MonadLaws (P1 U),
           MonadLaws (P2 U)} :
  MonadLaws (Monad_Product P1 P2 U) := {}.
Proof.
  - intros A []; simpl; f_equal; apply bind_ret.
  - intros A B a k; simpl; do 2 rewrite ret_bind; destruct (k a); auto.
  - intros A B C m k h; simpl; f_equal; rewrite bind_bind; auto.
Qed.

Instance MonadPartial_Product P1 P2 U
         `{MonadPartial (P1 U),
           MonadPartial (P2 U)} :
  MonadPartial (Product P1 P2 U) :=
  { empty _ := (empty, empty) }.

Instance MonadPartialLaws_Product P1 P2 U
         `{MonadPartialLaws (P1 U),
           MonadPartialLaws (P2 U)} :
  MonadPartialLaws (MonadPartial_Product P1 P2 U) := {}.
Proof.
  intros. simpl. f_equal; apply partial_left_zero.
Qed.

Instance Promonad_Product P1 P2
         `{Promonad P1, Promonad P2} :
  Promonad (Product P1 P2) :=
  { comap U V A f m := (comap f (fst m), comap f (snd m)) }.

Lemma comap_as_morph P `{Promonad P} U V A f :
  comap f = (fun A => @comap P _ U V A f) A.
Proof. auto. Qed.

Instance LawfulPromonad_Product P1 P2
         `{PromonadLaws P1, PromonadLaws P2} :
  PromonadLaws (Promonad_Product P1 P2) := {}.
Proof.
  intros.
  constructor; intros; simpl; f_equal;
    apply comap_morph_ret + apply comap_morph_bind; auto.
Qed.

(*****)


(* Common combinators *)

Fixpoint replicate `{Promonad P} {U A} (n : nat) (m : P U A)
  : P (list U) (list A) :=
  match n with
  | O => ret []
  | S n' =>
    x  <- m  upon head;;
    xs <- (replicate n' m)  upon tail;;
    ret (x :: xs)
  end.

Arguments replicate {P _ U A}.

Definition hom (P1 P2 : Type -> Type -> Type) : Type :=
  forall A B, P1 A B -> P2 A B.

Definition pfunction (A B : Type) : Type := A -> option B.

Instance Monad_pfunction {A} : Monad (pfunction A) := {|
  ret _ a := fun _ => Some a;
  bind _ _ m k u := x <- m u;; k x u;
|}.

Instance Promonad_pfunction : Promonad pfunction := {|
  asMonad := @Monad_pfunction;
  comap _ _ _ f m u := u' <- f u;; m u';
|}.

(*** Compositionality ***)

Class Compositional
      (P : Type -> Type -> Type)
      `{Promonad P}
      (R : forall A B, P A B -> Prop) :=
  {
    CompositionalWithLawful :> PromonadLaws _;
    ret_comp :
      forall U A (a : A), R U A (ret a : P U A);
    bind_comp :
      forall U A B (m : P U A) (k : A -> P U B) ,
        R U A m ->
        (forall a, R U B (k a)) ->
        R U B (bind m k);
    comap_comp :
      forall U V A (f : U -> option V) (m : P V A),
        R V A m ->
        R U A (comap f m);
  }.

(*** Quasicompositionality ***)

Class Quasicompositional
      {P : Type -> Type -> Type}
      `{Promonad P}
      (R : forall A B, P A B -> Prop) :=
  {
    ret_comp' :
      forall A0 A a, R A0 A (ret a);
    bind_comp' :
      forall U A B (m : P U A) (k : A -> P U B) (f : B -> option A),
        (forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
        R U A m ->
        (forall a, R U B (k a)) ->
        R U B (bind m k);
    comap_comp' :
      forall U V A (f : U -> option V) (m : P V A),
        R V A m -> R U A (comap f m)
  }.

(* replicate preserves quasicompositional properties *)
Lemma replicate_comp M
      (R : forall U A, M U A -> Prop)
      `{Promonad_M : Promonad M}
      `{forall U, MonadLaws (asMonad U)}
      `{@Quasicompositional M Promonad_M R}
      U A (n : nat) (m : M U A)
  : R _ _ m ->
    R _ _ (replicate n m).
Proof.
  intro Hm.
  induction n.
  - apply ret_comp'.
  - apply bind_comp' with (f := head); auto.
    { intros a.
      repeat rewrite @bind_bind; auto.
      f_equal.
      apply functional_extensionality; intros a0.
      do 2 (rewrite @ret_bind; auto).
    }
    { apply comap_comp'; auto. }
    { intros a.
      apply bind_comp' with (f := tail); auto.
      { intros xs.
        do 2 (rewrite @ret_bind; auto).
      }
      { auto using comap_comp'. }
      { auto using ret_comp'. }
    }
Qed.

Lemma purify_replicate P
      `{Promonad P}
      (phi : forall U A, P U A -> pfunction U A) (* promonad morphism *)
      `{@PromonadMorphism _ _ _ _ phi}
      U A (n : nat) (m : P U A) (xs : list U) :
  length xs = n ->
  phi _ _ (replicate n m) xs = traverse_option (phi _ _ m) xs.
Proof.
  intros Hn; subst; induction xs.
  - simpl; rewrite morph_ret; auto.
  - simpl; rewrite morph_bind, morph_comap; simpl.
    f_equal. apply functional_extensionality. intro y.
    rewrite morph_bind, morph_comap; simpl; rewrite IHxs.
    f_equal. apply functional_extensionality. intro ys.
    rewrite morph_ret; auto.
Qed.
