Require Import Coq.Program.Program.
Require Import eqchain.

Inductive PolyF : Type :=
| zer : PolyF
| one : PolyF
| arg1 : PolyF
| arg2 : PolyF
| Sum : PolyF -> PolyF -> PolyF
| Prod : PolyF -> PolyF -> PolyF
.

Fixpoint inst (F : PolyF) (A X : Type) : Type :=
  match F with
  | zer      => Empty_set
  | one      => unit
  | arg1     => A
  | arg2     => X
  | Sum F G  => (inst F A X) + (inst G A X)
  | Prod F G => (inst F A X) * (inst G A X)
  end.

Notation "⟦ F ⟧" := (inst F) (at level 20).

Definition fprod {A B C : Type} (f : A -> B) (g : A -> C): A -> B * C :=
  fun (x : A) => (f x, g x).

Definition fsum {A B C : Type} (f : A -> C) (g : B -> C): A + B -> C :=
  fun (x : A + B) =>
    match x with
    | inl x => f x
    | inr x => g x
    end.

Notation "〈 f , g 〉" := (fprod f g) (at level 20).
Notation "[ f , g ]" := (fsum  f g) (at level 20).

Notation " f ⊗ g " := ( 〈 f ∘ fst , g ∘ snd 〉 )   (at level 20).
Notation " f ⊕ g " := ( [ inl ∘ fst , snd ∘ g ] ) (at level 20).

Definition unique_mor_initial  {A : Type} : Empty_set -> A := fun x => match x with end. 
Definition unique_mor_terminal {A : Type} : A -> unit      := fun (x : A) => tt.

Notation " ¡ " := ( @unique_mor_initial _ ).
Notation " ! " := ( @unique_mor_terminal _ ).

Section Basic_Properties.

  Variable A B C D E X : Type.
  
  Lemma fst_fprod :
    forall (f : A -> B) (g : A -> C), fst ∘ 〈 f , g 〉 = f.
  Proof.
    intros f g. extensionality x. cbv. reflexivity.
  Qed.  

  Lemma snd_fprod :
    forall (f : A -> B) (g : A -> C), snd ∘ 〈 f , g 〉 = g.
  Proof.
    intros f g. extensionality x. cbv. reflexivity.
  Qed.

  Lemma paring :
    forall (f : A -> B*C), 〈 fst ∘ f , snd ∘ f 〉 = f.
  Proof.
    intros f. extensionality x. cbv. induction (f x). easy.
  Qed.

  Lemma paring2 :
    forall (f : X -> A) (g : X -> B) (i : A -> C) (j : B -> D),
      (i ⊗ j) ∘ 〈 f , g 〉 = 〈 i ∘ f , j ∘ g 〉.
  Proof.
    intros f g h i. extensionality x. cbv; easy.
  Qed.
End Basic_Properties.
Hint Resolve paring.
Hint Resolve paring2. 

Fixpoint fmap (F : PolyF) {A0 A1 X0 X1 : Type}
  (f : A0 -> A1) (g : X0 -> X1) : ⟦F⟧ A0 X0 -> ⟦F⟧ A1 X1 :=
  match F with
  | zer      => id
  | one      => id
  | arg1     => f
  | arg2     => g
  | Sum F G  => fun x
                => match x with
                   | inl x => inl (fmap F f g x)
                   | inr x => inr (fmap G f g x)
                   end
  | Prod F G => fun x
                => (fmap F f g (fst x), fmap G f g (snd x))
  end.

Notation " F ❲ f ❳ [ g ]" := (@fmap F _ _ _ _ f g) (at level 10).
Notation " F [ f ]"       := (@fmap F _ _ _ _ id f) (at level 10).

Lemma fmap_functor_dist :
  forall (F : PolyF) {A0 A1 A2 X0 X1 X2 : Type}
         (f0 : A0 -> A1) (f1 : A1 -> A2) (g0 : X0 -> X1) (g1 : X1 -> X2),
    F ❲f1 ∘ f0❳ [g1 ∘ g0] = F ❲ f1 ❳ [ g1 ] ∘ F ❲ f0 ❳ [g0] .
Proof.
  intros F A0 A1 A2 X0 X1 X2 f0 f1 g0 g1.
  extensionality x. induction F.
  - easy.
  - easy.
  - easy.
  - easy.
  - cbn. induction x.
    + rewrite IHF1. easy.
    + rewrite IHF2. easy.
  - cbn. rewrite IHF1; rewrite IHF2. induction x. easy.
Qed.
Hint Resolve fmap_functor_dist.

Lemma fmap_functor_distr :
  forall (F : PolyF) {A X0 X1 X2 : Type} (g0 : X0 -> X1) (g1 : X1 -> X2),
    F ❲ @id A ❳ [g1 ∘ g0] = F [ g1 ] ∘ F [g0] .
Proof.
  intros F A X0 X1 X2 g0 g1.
  rewrite <- fmap_functor_dist.
  easy.
Qed.
Hint Resolve fmap_functor_distr. 

Lemma fmap_functor_id :
  forall (F : PolyF) {A X : Type},
    F ❲ @id A ❳ [ @id X ] = id.
Proof.
  intros F A X. extensionality x. induction F.
  - easy.
  - easy.
  - easy.
  - easy.
  - cbn. induction x.
    + rewrite IHF1; easy.
    + rewrite IHF2; easy. 
  - cbn. induction x. rewrite IHF1; rewrite IHF2. easy.
Qed.
Hint Resolve fmap_functor_id. 

Class F_initial_algebra (F : PolyF) (A : Type) (μF : Type)
      (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) ) :=
  {
    cata := c;
    in_        : ⟦ F ⟧ A μF -> μF;
    cata_charn : forall (X : Type) (f : μF -> X) (φ : ⟦ F ⟧ A X -> X),
        f ∘ in_ = φ ∘ F[f] <-> f = cata X φ
  (*
    cata_axiom1 : forall (X : Type) (f : μF -> X) (φ : ⟦ F ⟧ A X -> X) (x : ⟦ F ⟧ A μF),
        cata X φ (in_ x) = φ (F[cata X φ] x);
    cata_axiom2 : forall (X : Type) (f : μF -> X) (φ : ⟦ F ⟧ A X -> X),
        (forall x : ⟦ F ⟧ A μF, f (in_ x) = φ (F[f] x)) -> forall x : μF, f x = cata X φ x *)
  }.

Notation "⦇ f ⦈" := (cata _ f) (at level 5).

Definition cata_bool (X : Type) (f : unit + unit -> X) : bool -> X :=
  fix cataf (b : bool) :=
    match b with
    | true  => f (inl ())
    | false => f (inr ())
    end.

Definition cata_nat (X : Type) (f : unit + X -> X) : nat -> X :=
  fix cataf (n : nat)
    := match n with
       | O    => f (inl ()) 
       | S n' => f (inr (cataf n'))
       end.

Definition cata_list (A X : Type) (f : unit + A*X -> X) : list A -> X :=
  fix cataf (l : list A)
    := match l with
       | nil       => f (inl ())
       | cons x xs => f (inr (x, cataf xs))
       end.

(*
Definition cata (F : PolyF) (A X : Type) (f : ⟦ F ⟧ A X -> X) (μF : Type) : μF -> X :=
  match F with
  | zer  => fix cataf ()
  | one  : PolyF
  | arg1 : PolyF
  | arg2 : PolyF
  | Sum  : PolyF -> PolyF -> PolyF
  | Prod : PolyF -> PolyF -> PolyF
  end.                               
 *)

Instance Nat_ia : F_initial_algebra (Sum one arg2) unit nat cata_nat :=
  {
    in_  := [ fun x => O , S ];
  }.
Proof.
  intros X f φ.
  split.
  - intros H. unfold cata_nat.
    extensionality x.
    induction x.
    + specialize (equal_f H (inl tt)) as H0; cbv in H0.
      exact H0.
    + specialize (equal_f H (inr x)) as H1; cbv in H1.
      rewrite <- IHx.
      exact H1.
  - intros H; extensionality x; induction x.
    + rewrite H. induction a. easy.
    + rewrite H; easy.
Qed.

Proposition cata_cancel :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
  forall (X : Type) (φ : ⟦ F ⟧ A X -> X),
    ⦇ φ ⦈ ∘ in_ = φ ∘ F[⦇ φ ⦈].
Proof.
  intros F A μF c ia X φ. 
  apply cata_charn; reflexivity.
Qed.

Proposition cata_refl :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
    ⦇ in_ ⦈ = id.
Proof.
  intros F A μF c ia. symmetry. apply cata_charn.
  rewrite fmap_functor_id. easy.
Qed.
Hint Resolve cata_refl.

Proposition cata_fusion :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
  forall (X Y : Type) (φ : ⟦ F ⟧ A X -> X) (ψ : ⟦ F ⟧ A Y -> Y) f,
      f ∘ φ = ψ ∘ F[f] -> f ∘ ⦇φ⦈ = ⦇ψ⦈.
Proof.
  intros F A μF c ia X Y φ ψ f H. 
  apply cata_charn.
  Left
  = ( f ∘ ⦇ φ ⦈ ∘ in_ ).
  = ( f ∘ (⦇ φ ⦈ ∘ in_) ).
  = ( f ∘ φ ∘ F[⦇ φ ⦈] )       { by cata_cancel }.
  = ( ψ ∘ F[f] ∘ F[⦇ φ ⦈] )    { by H }.
  = ( ψ ∘ (F[f] ∘ F[⦇ φ ⦈]) ).
  = ( ψ ∘ F[f ∘ ⦇ φ ⦈] )       { by fmap_functor_distr }.
  = Right.
Qed.

Proposition lambek1 :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
    (in_) ∘ ⦇ F[in_] ⦈ = id.
Proof.
  intros F A μF c ia.
  Left
  = ( ⦇ in_ ⦈ )     { apply cata_fusion; easy }.
  = ( @id (μF) )    { by cata_refl }.
  = Right.
Qed.

Proposition lambek2 :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
     ⦇ F[in_] ⦈ ∘ in_  = id.
Proof.
  intros F A μF C ia.
  Left
  = ( ⦇ F[in_] ⦈ ∘ in_ ).
  = ( F[in_] ∘ ( F❲@id A❳[⦇ F[in_] ⦈] ) )  { by cata_cancel }.
  = ( F❲@id A❳[in_ ∘ ⦇ F[in_] ⦈] ).
  = ( F❲@id A❳[@id μF] )                   { by lambek1 }.
  = ( @id (⟦F⟧ A μF) ).
  = Right.
Qed.

Definition in_inv {F : PolyF} {A : Type} {μF : Type}
           {c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X)}
           {ia : F_initial_algebra F A μF c}
  := ⦇ F❲@id A❳[in_] ⦈.


Proposition in_inv_charn1 :
   forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
     in_ ∘ in_inv = id.
Proof.
  apply lambek1.
Qed.

Proposition in_inv_charn2 :
   forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
     in_inv ∘ in_ = id.
Proof.
  apply lambek2.
Qed.

Proposition lemma1 :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
    in_ ∘ in_inv = id /\ in_inv ∘ in_ = id.
Proof.
  intros; split.
  - apply lambek1.
  - apply lambek2.
Qed.

Proposition lemma2 :
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),    
  forall {C : Type} (f : μF -> C) (φ : ⟦ F ⟧ A (C * μF)%type -> C),
    f ∘ in_ = φ ∘ F [ 〈 f , id 〉 ] <-> f = fst ∘ ⦇ 〈 φ , in_ ∘ F[snd] 〉 ⦈.
Proof.
  intros; split.
  - intros H.
    assert ( 〈 f, id 〉 ∘ in_ = 〈 φ , in_ ∘ F[snd] 〉 ∘ F[〈 f , id 〉] ) as H1.
    {
      Left
      = ( 〈 f, id 〉 ∘ in_ ).
      = ( 〈 f ∘ in_ , id ∘ in_ 〉 ).
      = ( 〈 f ∘ in_ , in_ 〉 ).
      = ( 〈 f ∘ in_ , in_ ∘ id 〉 ).
      = ( 〈 f ∘ in_ , in_ ∘ F[id] 〉 )                        { by fmap_functor_id }.
      = ( 〈 f ∘ in_ , in_ ∘ F[snd ∘ 〈 f, id 〉] 〉 ).
      = ( 〈 φ ∘ F[〈 f, id 〉] , in_ ∘ F[snd ∘ 〈 f, id 〉] 〉 )    { by H }.
      = ( 〈 φ ∘ F[〈 f, id 〉] , in_ ∘ F[snd] ∘ F[〈 f, id 〉] 〉 ) { by fmap_functor_distr }.
      = ( 〈 φ , in_ ∘ F[snd] 〉 ∘ F[〈 f, id 〉] ).
      = Right.
    }
    apply cata_charn in H1.
    @ H1 : ( 〈 f, id 〉 = ⦇ 〈 φ, in_ ∘ F [snd] 〉 ⦈ ).
    Left
    = ( f ).
    = ( fst ∘ 〈f, id〉 ).
    = ( fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ )   { by H1 }.
    = Right.
  - intros H.
    assert ( ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ ∘ in_ = 〈 φ, in_ ∘ F[snd] 〉 ∘ F[⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈])
      as H1 by (apply cata_charn; easy).
    assert ( snd ∘ 〈 φ, in_ ∘ F[snd] 〉 = in_ ∘ F[snd] ) as H2 by auto.
    assert ( snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ = ⦇ in_ ⦈ ) as H3.
    {
      apply cata_fusion; easy.
    }
    Left
    = ( f ∘ in_ ).
    = ( fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ ∘ in_ )                                     { by H }.
    = ( fst ∘ (⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ ∘ in_) ).
    = ( fst ∘ 〈 φ, in_ ∘ F[snd] 〉 ∘ F[⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈] )                   { by H1 }.
    = ( φ ∘ F[⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈] ).
    = ( φ ∘ F[〈 fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ , snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ 〉] )  { by paring }.
    = ( φ ∘ F[〈 f , snd ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈ 〉] )                             { by H }.
    = ( φ ∘ F[〈 f , ⦇ in_ ⦈ 〉] )                                                  { by H3 }.
    = ( φ ∘ F[〈 f , id 〉] )                                                       { by cata_refl }.
    = Right.
Qed.

(* Class F_initial_algebra (F : PolyF) (μF : Type) :=
  {
    in_        : forall (A : Type), ⟦ F ⟧ A μF -> μF; 
    cata       : forall (A X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X);
    cata_charn : forall (A X : Type) (f : μF -> X) (φ : ⟦ F ⟧ A X -> X),
        f ∘ (in_ A) = φ ∘ F[f]  <-> f = cata A X φ
  }. *)

(* Terminal-coalgebra and anamorphism *)

Class F_terminal_coalgebra (F : PolyF) (A : Type) (νF : Type)
      (a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF) ) :=
  {
    ana := a;
    out_      : νF -> ⟦ F ⟧ A νF;
    ana_charn : forall (X : Type) (f : X -> νF) (φ : X -> ⟦ F ⟧ A X),
        out_ ∘ f = F[f] ∘ φ <-> f = ana X φ
  }.

Notation "〖 f 〗" := (@ana _ _ _ _ _ _ f) (at level 5).

Section anamorphism.
  Variable (F : PolyF) (A : Type) (νF : Type)
           (a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF) )
           (tc : F_terminal_coalgebra F A νF a).
  
  Proposition ana_cancel:
    forall (X : Type) (φ : X -> ⟦ F ⟧ A X),
      out_ ∘〖 φ 〗 = F[〖 φ 〗] ∘ φ.
  Proof.
    intros; apply ana_charn; reflexivity.
  Qed.

  Proposition ana_refl:〖 out_ 〗 = id.
  Proof.
    intros; symmetry.
    apply ana_charn. rewrite fmap_functor_id. easy.
  Qed.

  Proposition ana_fusion:
    forall (X Y : Type) (φ : X -> ⟦ F ⟧ A X) (ψ: Y -> ⟦ F ⟧ A Y) (f : X -> Y),
      ψ ∘ f = F[f] ∘ φ -> 〖 ψ 〗∘ f = 〖 φ 〗. 
  Proof.
    intros. apply ana_charn.
    Left
    = ( out_ ∘〖 ψ 〗∘ f ).
    = ( F[〖 ψ 〗] ∘ ψ ∘ f )      { by ana_cancel }.
    = ( F[〖 ψ 〗] ∘ (ψ ∘ f) ).
    = ( F[〖 ψ 〗] ∘ F[f] ∘ φ )   { by H }.
    = ( F[〖 ψ 〗∘ f] ∘ φ )       { by fmap_functor_distr }.
    = Right.
  Qed.

  Proposition out_inv_charn1_in: 〖 F[out_] 〗∘ out_ = id.
  Proof.
    intros.
    Left
    = (〖 F[out_] 〗∘ out_ ).
    = (〖 out_ 〗 )              { apply ana_fusion }.
    = ( @id νF )                { by ana_refl }.
    = Right.
  Qed.

  Proposition out_inv_charn2_in: out_ ∘〖 F[out_] 〗= id.
  Proof.
    intros.
    Left
    = ( out_ ∘ 〖 F[out_] 〗).
    = ( F[〖 F[out_] 〗] ∘ F❲@id A❳[out_] )   { by ana_cancel }.
    = ( F❲@id A❳[〖 F[out_] 〗∘ out_ ] ).
    = ( F❲@id A❳[@id νF] )                   { by out_inv_charn1_in }.
    = ( @id (⟦ F ⟧ A νF) ).
    = Right.
  Qed.
End anamorphism.

Definition out_inv {F : PolyF} {A : Type} {νF : Type}
           {a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF)}
           {tc : F_terminal_coalgebra F A νF a}
  := 〖 F[out_] 〗.

Proposition out_inv_charn1:
  forall  {F : PolyF} {A : Type} {νF : Type}
          {a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF)}
          {tc : F_terminal_coalgebra F A νF a},
    out_inv ∘ out_ = id.
Proof.
  apply out_inv_charn1_in.
Qed.

Proposition out_inv_charn2:
  forall  {F : PolyF} {A : Type} {νF : Type}
          {a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF)}
          {tc : F_terminal_coalgebra F A νF a},
    out_ ∘ out_inv = id.
Proof.
  apply out_inv_charn2_in.
Qed.

Proposition out_inv_charn:
  forall  {F : PolyF} {A : Type} {νF : Type}
          {a : forall (X : Type), (X -> ⟦ F ⟧ A X) -> (X -> νF)}
          {tc : F_terminal_coalgebra F A νF a},
    out_inv ∘ out_ = id /\ out_ ∘ out_inv = id.
Proof.
  intros; split.
  - apply out_inv_charn1.
  - apply out_inv_charn2.
Qed.

Definition para (F : PolyF) (A : Type) (μF : Type)
           (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
           (ia : F_initial_algebra F A μF c)
           {C : Type} (φ : ⟦ F ⟧ A (C * μF)%type -> C) 
  := fst ∘ ⦇ 〈 φ, in_ ∘ F[snd] 〉 ⦈.

Notation "◃ f ▹" := (@para _ _ _ _ _ _ f) (at level 5).

Proposition para_charn:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c)
         {C : Type} (f : μF -> C) (φ : ⟦ F ⟧ A (C * μF)%type -> C),
    f ∘ in_ = φ ∘ F[〈f, id〉] <-> f = ◃φ▹.
Proof.
  intros; apply lemma2.
Qed.

Proposition para_cancel:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c)
         {C : Type} (φ : ⟦ F ⟧ A (C * μF)%type -> C),
    ◃ φ ▹ ∘ in_ = φ ∘ F[〈◃φ▹, id〉].
Proof.
  intros. apply para_charn; reflexivity.
Qed.

Proposition para_refl:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
    id = ◃ in_ ∘ F[fst] ▹.
Proof.
  intros. apply para_charn.
  Right
  = ( in_ ∘ F [fst] ∘ F [〈 id, id 〉] ).
  = ( in_ ∘ ( F [fst] ∘ F [〈 id, id 〉] ) ).
  = ( in_ ∘ ( F [fst ∘ 〈 id, id 〉] ) )          { by fmap_functor_distr }.
  = ( in_ ∘ F [id] ).
  = ( in_ ∘ id )                               { by fmap_functor_id } .
  = Left.
Qed.

Proposition para_fusion:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c)
         {C D : Type} (f : C -> D) (φ : ⟦ F ⟧ A (C * μF)%type -> C)
         (ψ : ⟦ F ⟧ A (D * μF)%type -> D),
    f ∘ φ = ψ ∘ F[f ⊗ id] -> f ∘ ◃ φ ▹ = ◃ ψ ▹.
Proof.
  intros. apply para_charn.
  Left
  = ( f ∘ ◃ φ ▹ ∘ in_ ).
  = ( f ∘ (◃ φ ▹ ∘ in_) ).
  = ( f ∘ (φ ∘ F[〈 ◃ φ ▹, id 〉]) )        { by para_cancel }.
  = ( (f ∘ φ) ∘ F[〈 ◃ φ ▹, id 〉] ).
  = ( ψ ∘ F[f ⊗ id] ∘ F[〈◃ φ ▹, id〉] )    { by H }.
  = ( ψ ∘ F[f ⊗ id ∘ 〈◃ φ ▹, id〉] )       { by fmap_functor_distr }.
  = ( ψ ∘ F[〈f ∘ ◃ φ ▹, id ∘ id〉] )       { by paring2 }.
  = Right.
Qed.

Proposition para_cata:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c)
         {C : Type} (φ : ⟦ F ⟧ A (C * μF)%type -> C * μF),
    ⦇ φ ⦈ = ◃ φ ∘ F[fst] ▹.
Proof.
  intros; apply para_charn.
  Left
  = ( ⦇ φ ⦈ ∘ in_ ).
  = ( φ ∘ F[⦇ φ ⦈] )                 { by cata_cancel }.
  = ( φ ∘ F[fst ∘ 〈⦇ φ ⦈, id〉] ).
  = ( φ ∘ F[fst] ∘ F[〈⦇ φ ⦈, id〉] )   { by fmap_functor_distr }.
  = Right.
Qed.

Proposition para_any:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c)
         {C : Type} (f : μF -> C),
    f = ◃ f ∘ in_ ∘ F[snd] ▹.
Proof.
  intros; apply para_charn.
  Right
  = ( f ∘ in_ ∘ F[snd] ∘ F[〈 f, id 〉] ).
  = ( f ∘ in_ ∘ (F[snd] ∘ F[〈 f, id 〉]) ).
  = ( f ∘ in_ ∘ (F[snd ∘ 〈 f, id 〉]) )      { by fmap_functor_distr }.
  = ( f ∘ in_ ∘ F[id] ).
  = ( f ∘ in_ ∘ id)                        { by fmap_functor_id }.
  = Left.
Qed.

Proposition para_in_inv:
  forall (F : PolyF) (A : Type) (μF : Type)
         (c : forall (X : Type), (⟦ F ⟧ A X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F A μF c),
    ◃ F[snd] ▹ ∘ in_ = id /\ in_ ∘ ◃ F[snd] ▹ = id.
Proof.
Admitted.

Notation " F ×" := (Prod arg1 F)              (at level 20).
Notation "⟦ F ⟧× A" := (inst (Prod arg1 F) A) (at level 20).

Lemma lemma3:
  forall (F : PolyF) (μF : Type) (C : Type) (νFC : Type)
         (c : forall (X : Type), (⟦ F ⟧ C X -> X) -> (μF -> X) )
         (ia : F_initial_algebra F C μF c)
         (a : forall (X : Type), (X -> (inst (Prod arg1 F) C X)) -> (X -> νFC) )
         (tc : F_terminal_coalgebra (Prod arg1 F) C νFC a),
  forall (f : μF -> C) (φ : ⟦F⟧ C νFC -> C),
    f ∘ in_ = φ ∘ F[〖 〈 f, in_inv 〉 〗]
    <-> f = fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ , id 〉 ⦈.
Proof.
  intros. split.
  - intros H.
    assert ( 〖 〈 f, in_inv 〉 〗∘ in_ = out_inv ∘ 〈 φ , id 〉 ∘ F[〖 〈 f, in_inv 〉 〗] ) as H1.
    {
      Left
      = (〖 〈 f, in_inv 〉 〗∘ in_ ).
      = ( id ∘〖 〈 f, in_inv 〉 〗∘ in_ ).
      = ( out_inv ∘ out_ ∘〖 〈 f, in_inv 〉 〗∘ in_ )   { by out_inv_charn1 }.
      = ( out_inv ∘ (out_ ∘〖 〈 f, in_inv 〉 〗) ∘ in_ ).
      = ( out_inv ∘ ((F ×) [〖 〈 f, in_inv 〉 〗] ∘ 〈 f, in_inv 〉) ∘ in_ )  { by ana_cancel }.
      = ( out_inv ∘ 〈 f , F[〖 〈 f, in_inv 〉 〗] ∘ in_inv 〉 ∘ in_ ).
      = ( out_inv ∘ 〈 f ∘ in_  , F[〖 〈 f, in_inv 〉 〗] ∘ in_inv ∘ in_  〉 ).
      = ( out_inv ∘ 〈 φ ∘ F [〖 〈 f, in_inv 〉 〗], F [〖 〈 f, in_inv 〉 〗] ∘ (in_inv ∘ in_) 〉 )
          { by H }.
      = ( out_inv ∘ 〈 φ ∘ F [〖 〈 f, in_inv 〉 〗], F [〖 〈 f, in_inv 〉 〗] 〉 )
          { by in_inv_charn2 }.
      = Right.
    }
    apply cata_charn in H1.
    @ H1 : (〖 〈 f, in_inv 〉 〗 = ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ).
    Left
    = f.
    = ( fst ∘ 〈f, in_inv〉).
    = ( fst ∘ (Prod arg1 F)[〖 〈 f, in_inv 〉 〗] ∘ 〈f, in_inv〉 ).
    = ( fst ∘ ( (Prod arg1 F)[〖 〈 f, in_inv 〉 〗] ∘ 〈f, in_inv〉) ).
    = ( fst ∘ (out_ ∘ 〖 〈 f, in_inv 〉 〗) )   { by ana_cancel }.
    = ( fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ) { by H1 }.
    = Right.
  - intros.
    assert ( out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ = (F ×) [ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ] ∘ 〈 f, in_inv 〉 ) as H1.
    {
      Left
      = ( out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ).
      = ( 〈 fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ 〉 )
          { symmetry; apply paring }.
      = ( 〈 f , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈〉 )
          { by H }.
      = ( 〈 f , snd ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ (in_ ∘ in_inv) 〉 )
          { by in_inv_charn1 }.
      = ( 〈 f , snd ∘ out_ ∘ (⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ in_) ∘ in_inv 〉 ).
      = ( 〈 f, snd ∘ out_ ∘ (out_inv ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈]) ∘ in_inv 〉 )
          { by cata_cancel }.
      = ( 〈 f, snd ∘ (out_ ∘ out_inv) ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 ).
      = ( 〈 f, snd ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 )
          { by out_inv_charn2 }.
      = ( 〈 f, F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ∘ in_inv 〉 ).
      = Right.
    }
    apply ana_charn in H1.
    @ H1 : ( ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ = 〖 〈 f, in_inv 〉 〗 ).
    Left
    = ( f ∘ in_ ).
    = ( fst ∘ out_ ∘ ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ in_ )  { by H }.
    = ( fst ∘ out_ ∘ ( ⦇ out_inv ∘ 〈 φ, id 〉 ⦈ ∘ in_) ).
    = ( fst ∘ (out_ ∘ out_inv) ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] )
        { by cata_cancel }.
    = ( fst ∘ 〈 φ, id 〉 ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] )
        { by out_inv_charn2 }.
    = ( φ ∘ F [⦇ out_inv ∘ 〈 φ, id 〉 ⦈] ).
    = (  φ ∘ F [〖 〈 f, in_inv 〉 〗] )                 { by H1 }.
    = Right.
Qed.

    
  
Notation (f : )

Inductive Nat :=
| Z : Nat
| S : Nat -> Nat.

Definition plus :=
  fix p' (n m : Nat) : Nat :=
    match n with
    | Z => m
    | S n0 => S (p' n0 m)
    end.

Definition hoge (n : Nat) :=
  (fun m => (match m with
  | Z   => S Z
  | S m => Z
  end)) n.

μx.(x = 1 + x)

Eval compute in
    ((fix p' (n : Nat)
      :=
        fun (m : Nat) =>
          match n with
          | Z => m
          | S n0 => S (p' n0 m)
          end) (S Z) (S Z)).

Eval compute in (plus (S Z) (S Z)).

(* ERROR *)
Fixpoint plus (n m : Nat) :=
  match n with
  | Z   => m
  | S n => S (plus n m)
  end.

fix :: (a -> a) -> a
fix f = f (fix f)

fix f = let x = f x in x

fix (λx.3)
-> (let x = [(λx.3) x] in x)
-> (let x = 3 in x)                       -> 3    