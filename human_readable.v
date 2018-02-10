Require Import Arith.
Require Import String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Inductive calstate : Type :=
  CFL   : calstate
| CFR   : calstate
| CFTMP : string -> calstate.

Inductive memo (cs : calstate) : Prop :=
  state : memo cs.

Tactic Notation "add_state" constr(cs) :=
  pose ( state _ : memo cs ).

Tactic Notation "set_state" constr(cs) :=
  first [ match goal with
          | [m := _ : _ |- _] => clear m ; add_state cs
          end
        | add_state cs
        ].

Tactic Notation "calrewrite_inner" constr(l) constr(term) tactic(tactic) :=
  let Hre := fresh "Hrewrite" in (
         assert (l = term) as Hre by (tactic ; (try reflexivity)) ;
         match goal with
         | [Hre : ?l1 = ?l1 |- _] => clear Hre
         | [Hre : _ |- _]         => rewrite Hre at 1 ; clear Hre
         end).

Tactic Notation "calrewrite_inner_tmp" ident(i) constr(l) constr(term) tactic(tactic) :=
  let Hre := fresh "Hrewrite" in (
    assert (l = term) as Hre by (tactic ; (try reflexivity))
  ).

Tactic Notation "calrewrite_l" constr(term) "by" tactic(tactic) :=
  match goal with
  | [|- ?l = _]  => calrewrite_inner l term tactic
  | [|- ?l <= _] => calrewrite_inner l term tactic
  | [|- ?l >= _] => calrewrite_inner l term tactic
  end.

Tactic Notation "calrewrite_r" constr(term) "by" tactic(tactic) :=
  match goal with
  | [|- _ = ?l] => calrewrite_inner l term tactic
  | [|- _ <= ?l] => calrewrite_inner l term tactic
  | [|- _ >= ?l] => calrewrite_inner l term tactic
  end.

Tactic Notation "calrewrite_tmp" ident(i) constr(term) "by" tactic(tactic) :=
  match goal with
  | [_ : i = ?l |- _] => calrewrite_inner_tmp i l term tactic
  end.

Ltac equal_l term tactic :=
  match goal with
  | [|- ?l = _]  => calrewrite_inner l term tactic
  | [|- ?l <= _] => calrewrite_inner l term tactic
  | [|- ?l >= _] => calrewrite_inner l term tactic
  | [|- ?l < _] => calrewrite_inner l term tactic
  | [|- ?l > _] => calrewrite_inner l term tactic
  | [|- _ ?l _]  => calrewrite_inner l term tactic
  end.
     
Ltac equal_r term tactic := calrewrite_r term by (tactic).
Ltac equal_tmp ident term tactic := calrewrite_tmp i term by (tactic).
Ltac equal term tactic :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l term by (tactic)
    | CFR        => calrewrite_r term by (tactic)
    | (CFTMP ?s) => calrewrite_tmp s term by tactic
    end
  end.

Ltac bydef := simpl ; reflexivity.

Ltac bydefof q := unfold q.
  
Ltac strivial := (repeat bydef) ; (try trivial).
  

Tactic Notation (at level 2)
       "Left"  "=" constr(e) "{" tactic(t) "}" :=
  (equal_l e t) ; set_state CFL.

Tactic Notation (at level 2) "Left"  "=" constr(e):=
  (equal_l e (strivial)) ; set_state CFL.

Tactic Notation (at level 2) "Right" "=" constr(e) "{" tactic(t) "}" :=
  (equal_r e t) ; set_state CFR.

Tactic Notation (at level 2) "Right" "=" constr(e) :=
  (equal_r e (strivial)) ; set_state CFR.

Tactic Notation (at level 2) "=" constr(x) "{" tactic(t) "}" := (equal x t).

Tactic Notation (at level 2) "=" constr(x) := (equal x (strivial)).

Tactic Notation (at level 2) "=" "Right" :=
  match goal with
  | [Hst : (memo CFL) |- _] =>
    trivial || tauto || (try apply transitivity ; reflexivity)
  end.

Tactic Notation (at level 2) "=" "Left"  :=
  match goal with
  | [Hst : (memo CFR) |- _] => trivial
  end.

Tactic Notation (at level 2) "Temp" ident(i) "=" constr(e) "{" tactic(t) "}" :=
 (equal_tmp i e t) ; set_state (CFTMP "i").

Tactic Notation (at level 2) "=" "Temp" ident(i) :=
  match goal with
  | [ _ : i = ?ir |- _ ] =>
    match goal with
    | [H : i = ?t |- i = ?t ] => rewrite H ; reflexivity
    | [H : ?t = i |- i = ?t ] => rewrite <- H ; reflexivity
    | [H : i = ?t |- ?t = i ] => rewrite H ; reflexivity
    | [H : ?t = i |- ?t = i ] => rewrite <- H ; reflexivity
    | _ => match goal with
           | [Hst : (memo ?ns) |- ?l = ?r] =>
             match ns with
             | CFL => remember l as i
             | CFR => let tmp := fresh "tmp" in (
                        remember r as i
                      )
             end
           end
    end
  | _ =>
    match goal with
    | [Hst : (memo ?ns) |- ?l = ?r] =>
      match ns with
      | CFL => remember l as i
      | CFR => let tmp := fresh "tmp" in (
                 remember r as i
               )
      end
    end
  end.


Tactic Notation (at level 2) "=" constr(x) "{" "by" uconstr(u) "}" :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l x by (try rewrite u || (try rewrite <- u))
    | CFR        => calrewrite_r x by (try rewrite u || (try rewrite <- u))
    | (CFTMP ?s) => calrewrite_tmp s x by ((try rewrite u) || (try rewrite <- u))
    end
  end.

Tactic Notation (at level 2) "=" constr(x) "{" "by" uconstr(u0) "," uconstr(u1) "}" :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | CFR        => calrewrite_r x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | (CFTMP ?s) => calrewrite_tmp s x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    end
  end.
  
  Tactic Notation (at level 2) "=" constr(x) "{" "by" uconstr(u0) "," uconstr(u1) "}" :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | CFR        => calrewrite_r x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | (CFTMP ?s) => calrewrite_tmp s x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    end
  end.

Tactic Notation (at level 2)
       "<" uconstr(rel) ">*" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [|- (?rel ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      assert (rel l e) as Hre by (t ; (try reflexivity))
      ; apply (transitivity Hre)
      || reflexivity
      ; clear Hre
      ; set_state CFL
    )
  end.

Tactic Notation (at level 2)
       "<" uconstr(rel) ">" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [|- (?rel ?l ?r)] =>
    let Hre  := fresh "Hrewrite" in
    let Hre2 := fresh "Hrewrite2" in
    let H0   := fresh "H0" in
    let H1   := fresh "H1" in
    (
      assert (rel l e) as Hre by (t ; (try reflexivity))
      ; assert (rel l e -> e = r -> rel l r) as Hre2
          by (
              intros H0 H1 ;
              try rewrite <- H1 ;
              exact H0 || reflexivity
            )
      ; apply Hre2
      ; [exact Hre | idtac ]
      ; clear Hre
      ; set_state CFL
    )
  end.
