(* Imports *)
Require Import Bool List String Datatypes.

(*
Definition PropVars : string.
Axiom Varseq_dec : forall x y : PropVars, {x = y} + {x <> y}.
*)

Inductive PropF : Type :=
 | Var : string -> PropF
 | Bot : PropF
 | Conj : PropF -> PropF -> PropF
 | Disj : PropF -> PropF -> PropF
 | Impl : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1).
Notation "A ∨ B" := (Disj A B) (at level 15, right associativity).
Notation "A ∧ B" := (Conj A B) (at level 15, right associativity).
Notation "A → B" := (Impl A B) (at level 16, right associativity).
Notation "⊥" := Bot (at level 0).
Definition Neg A := A → ⊥.
Notation "¬ A" := (Neg A) (at level 5).
Definition Top := ¬⊥.
Notation "⊤" := Top (at level 0).
Definition BiImpl A B := (A→B)∧(B→A).
Notation "A ↔ B" := (BiImpl A B) (at level 17, right associativity).

(* Defining equivalence for PropF *)
Fixpoint EquivPropF x y :=
  match (x, y) with
  | (# a, #b) => if string_dec a b then true else false
  | (⊥, ⊥) => true
  | (a1 ∧ a2, b1 ∧ b2) => andb (EquivPropF a1 b1) (EquivPropF a2 b2)
  | (a1 ∨ a2, b1 ∨ b2) => andb (EquivPropF a1 b1) (EquivPropF a2 b2)
  | (a1 → a2, b1 → b2) => andb (EquivPropF a1 b1) (EquivPropF a2 b2)
  | (_, _) => false
  end.

(* Basic set of PropF *)
Definition PropFSet : Type := list PropF.

(* Possible Results after proof search *)
Inductive Results :=
  | Open
  | Closed
  | Failure
.

(* Defining a tableau rule *)
Definition Numerator := PropFSet.
Definition Denominator := sum (list PropFSet) Results.

Definition Rule := prod Numerator Denominator.

Definition getNumerator (rule : Rule) := fst rule.
Definition getDenominator (rule : Rule) := snd rule.

(* Method to get propsitional variables *)
Fixpoint getPropVar (prop : PropF) :=
  match prop with
  | # pv => pv::nil
  | ⊥ => nil
  | a ∧ b => getPropVar a ++ getPropVar b
  | a ∨ b => getPropVar a ++ getPropVar b
  | a → b => getPropVar a ++ getPropVar b
  end.

Fixpoint getPropVars (props : PropFSet) :=
  match props with
  | nil => nil
  | x::xs => getPropVar x ++ getPropVars xs
  end.

Fixpoint isInstanceOf (formula : PropF) (scheme : PropF) :=
  match (formula, scheme) with
  | (_, #b) => true
  | (⊥, ⊥) => true
  | (a1 ∧ a2, b1 ∧ b2) => andb (isInstanceOf a1 b1) (isInstanceOf a2 b2)
  | (a1 ∨ a2, b1 ∨ b2) => andb (isInstanceOf a1 b1) (isInstanceOf a2 b2)
  | (a1 → a2, b1 → b2) => andb (isInstanceOf a1 b1) (isInstanceOf a2 b2)
  | (_, _) => false
  end.

Definition partitionTuple := list (PropF * PropF).

(* Fix with fail monad or something ... *)
Fixpoint matchVarHelp (scheme : PropF) (γ : PropF) : partitionTuple :=
  match (scheme, γ) with
  | (# pv, x) => (# pv, x)::nil
  | (⊥, ⊥) => nil
  | (a1 ∧ a2, b1 ∧ b2) => matchVarHelp a1 b1 ++ matchVarHelp a2 b2
  | (a1 ∨ a2, b1 ∨ b2) => matchVarHelp a1 b1 ++ matchVarHelp a2 b2
  | (a1 → a2, b1 → b2) => matchVarHelp a1 b1 ++ matchVarHelp a2 b2
  | (_, _) => nil
  end.

Definition matchVar (scheme : PropF) (γ : PropF) :=
  if isInstanceOf γ scheme then Some (matchVarHelp scheme γ)
  else None.

Recursive Extraction matchVar.

Compute (matchVar (# "p" → # "r") (⊥ → (# "q"))).

Fixpoint getSetVars (π : partitionTuple) : PropFSet :=
  match π with
  | nil => nil
  | x::xs => (snd x) :: getSetVars xs
  end.

Compute getSetVars ((# "p", ⊥) :: (# "r", # "q") :: nil).

Fixpoint lookupPartition (γ : PropF) (π : partitionTuple) :=
  match π with
  | nil => None
  | (v1, v2)::xs => if EquivPropF γ v1 then Some v2
                else lookupPartition γ xs
  end.

Fixpoint applyPartitionPropF (γ : PropF) (π : partitionTuple) :=
  match lookupPartition γ π with
  | None => 
    match γ with
    | # pv => # pv
    | ⊥ => ⊥
    | a1 ∧ a2 => applyPartitionPropF a1 π ∧ applyPartitionPropF a2 π
    | a1 ∨ a2 => applyPartitionPropF a1 π ∨ applyPartitionPropF a2 π
    | a1 → a2 => applyPartitionPropF a1 π → applyPartitionPropF a2 π
    end
  | Some x => x
  end.

Fixpoint applyPartition (Γ : PropFSet) (π : partitionTuple) :=
  match Γ with
  | nil => nil
  | x::xs => (applyPartitionPropF x π) :: (applyPartition xs π)
  end.

Compute (applyPartition ((# "p" → # "r")::nil) ((# "p", ⊥) :: (# "r", # "q") :: nil)).

Definition option_bind (A : Type) (B : Type) (x : option A) (f : A -> option B) :=
  match x with
  | None => None
  | Some v => f v
  end.

Definition flip (A : Type) (B : Type) (C : Type) 
  (f : B -> A -> C) (a : A) (b : B) := f b a.

Fixpoint option_fold (A : Type) (B : Type)
  (f : B -> A -> option B) (z : B) (l : list A) : option B :=
    match l with
    | nil => Some z
    | x::xs => option_bind B B (option_fold A B f z xs) (flip A B (option B) f x)
    end.

Fixpoint inPartitionTuple p (π : partitionTuple) :=
  match π with
  | nil => false
  | x::xs => if andb (EquivPropF (fst x) (fst p)) (EquivPropF (snd x) (snd p))
              then true else inPartitionTuple p xs
  end.

Fixpoint usedVar (γ : PropF) (π : partitionTuple) :=
  match π with
  | nil => false
  | x::xs => if (EquivPropF γ (fst x)) then true else usedVar γ xs
  end.

Fixpoint extendPartition (π1 π2 : partitionTuple) :=
  match π2 with
  | nil => Some π1
  | x::xs => if inPartitionTuple x π1 then extendPartition π1 xs
              else (if usedVar (fst x) π1 then None else extendPartition (x::π1) xs)
  end.

Check matchVar.

Fixpoint partition_help (scheme : PropF) (Γ : PropFSet) (π : partitionTuple) :=
  match Γ with
  | nil => nil
  | γ::γs =>
    match matchVar scheme γ with
    | None => partition_help scheme γs π
    | Some π' =>
      match extendPartition π π' with
      | None => partition_help scheme γs π
      | Some newπ => newπ :: partition_help scheme γs π
      end
    end
  end.

Check flat_map.

Require Import Omega.
Require Import Coq.Arith.Compare_dec.

Lemma length_wf : forall A, well_founded (fun (xs : list A) ys => length xs < length ys).
intros. unfold well_founded. induction a.
constructor. intros. simpl in H. omega. constructor.
intros. destruct (eq_nat_dec (length y) (length a0)).
constructor. intros. apply IHa. rewrite <- e. exact H0.
apply IHa. simpl in H. omega.
Defined.

Lemma unchanging : forall x π, length (applyPartition x π) <= length x.
Proof.
  induction x. intros. unfold applyPartition. trivial.
  simpl in *. intuition.
Qed.

Definition partitions_help (schema : PropFSet) : PropFSet -> partitionTuple -> list partitionTuple.
  refine (Fix (length_wf PropF) (fun _ => PropFSet -> partitionTuple -> list partitionTuple)
   (fun schema partitions_help_rec =>
   (match schema as schema' return (schema = schema' -> PropFSet -> partitionTuple -> list partitionTuple) with
    | nil => fun _ _ accπ => accπ::nil
    | s::ss => fun H Γ accπ => let Π := partition_help s Γ accπ in
        flat_map (fun π => partitions_help_rec (applyPartition ss π) _ Γ π) Π
    end) eq_refl) schema).
    rewrite H. assert (length (applyPartition ss π) <= length ss) by apply unchanging.
    simpl. omega.
    Defined.

Definition partitions schema Γ := partitions_help schema Γ nil.

Compute (partitions ((# "p" → # "q")::nil) ((⊥ → ⊥::# "r" → ⊥::nil))).

Check Fix.