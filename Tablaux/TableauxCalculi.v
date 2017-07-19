(* Imports *)
Require Import List.

Inductive Result : Set :=
  | closed : Result
  | open : Result
.

Definition notClosedisOpen := (forall A : Result, A <> closed -> A = open).

