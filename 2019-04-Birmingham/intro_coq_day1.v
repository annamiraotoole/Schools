Require Import UniMath.Foundations.Preamble.

(* Press C-c C-n *)

(*

Preamble:

- natural numbers, bools, unit, empty,
- notations for Pi, Sigma types
- the universe of types UU

*)

Definition idfun : forall (A : UU), A -> A :=
  fun (A : UU) (a : A) => a.

Check idfun.
Print idfun.

Definition idfun' (A : UU) (a : A) : A := a.

Definition const (A B : UU) (a : A) (b : B) : A := a.

(* Booleans *)

About bool.
Print bool.
Check true.

About bool_rect.

Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (fun _ : bool => A) x y.

(* example: ifbool A x y b := if b then x else y *)

Definition negbool : bool -> bool := ifbool bool false true.

Eval compute in negbool true.

(* Natural Numbers *)

About nat.
Print nat.

Check (S 3).

Check nat_rect.

Definition nat_rec (A : UU) (a : A) (f : nat -> A -> A) : nat -> A :=
  nat_rect (fun _ : nat => A) a f.

(*
example:
nat_rec a f 0 = a
nat_rec a f (S n) = f n (nat_rec a f n)
 *)

Definition pred : nat -> nat :=
  nat_rec nat 0 (fun x _ => x).

(*
example:
pred 0 = 0
pred (S n) = n
 *)

Eval compute in pred 3.

Definition even : nat -> bool :=
  nat_rec bool true (fun _ b => negbool b).

Definition add (m : nat) : nat -> nat :=
  nat_rec nat m (fun _ x => S x).

Notation "x + y" := (add x y).

Eval compute in 7 + 4.

(* for finding the use of syntax:  *)
Locate "+".

(* Fancy symbols in Coq:

fun = λ (type \lambda
forall = ∏ (type \prod
-> = → (type \r)

*)

Check (λ x y, add x y).

Definition iter (A : UU) (a : A) (f : A → A) (n : nat) : A :=
  nat_rec A a (λ _ x, f x) n.

Notation "f ^ n" := (λ x, iter _ x f n).

Eval compute in (pred ^ 2) 5.

Definition sub (m n : nat) : nat := (pred ^ n) m.

Check idfun _ 3.

Definition idfun'' {A : UU} (a : A) : A := a.

Check idfun'' 3.
Check @idfun bool true.


(* Unit and Empty types *)

Print unit.
Print empty.

(* Sigma (Σ) types *)

(* "total2" in UniMath, the only Record in UniMath *)

Print total2.

Check tpair.
Locate ",,".

Check pr1.
Check pr2.

(* \sum = ∑ *)

Definition even_nat : UU :=
  ∑ (n : nat), ifbool _ unit empty (even n).

Definition test20 : even_nat := (20,,tt).
Fail Definition test21 : even_nat := (21,,tt).

(* Sections *)

Definition dirprod (X Y : UU) : UU :=
  ∑ (x : X), Y.

Notation "X × Y" := (dirprod X Y).

Section curry_sec.

  Variables (A B C : UU).

  Definition curry : (A × B → C) → (A → B → C) :=
    λ (f : A × B → C) (a : A) (b : B), f (a,,b).

End curry_sec.

(* Searching *)

Search nat.
