(* Imports *)
Require Import Bool List String Datatypes Omega Coq.Arith.Compare_dec Coq.Arith.Max.
Check max_dec.

(*
Definition PropVars : string.
Axiom Varseq_dec : forall x y : PropVars, {x = y} + {x <> y}.
*)

Definition optionBind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some v => (f v)
  end.

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

Fixpoint EquivPropV x y :=
  match (x, y) with
  | (# a, #b) => if string_dec a b then true else false
  | (# a, ⊥) => false
  | (# a, b1 ∧ b2) => orb (EquivPropV (# a) b1) (EquivPropV (# a) b2)
  | (# a, b1 ∨ b2) => orb (EquivPropV (# a) b1) (EquivPropV (# a) b2)
  | (# a, b1 → b2) => orb (EquivPropV (# a) b1) (EquivPropV (# a) b2)
  | (_, _) => false
  end.

(* Basic set of PropF *)
Definition PropFSet : Type := list PropF.

(* Possible Results after proof search *)
Inductive Results :=
  | Closed
.

(* Defining a tableau rule *)
Definition Numerator := PropFSet.
Definition Denominator := sum (list PropFSet) Results.

Check inr Closed : Denominator.

Definition Rule := prod Numerator Denominator.

Definition getNumerator (rule : Rule) := fst rule.
Definition getDenominator (rule : Rule) := snd rule.

Definition TableauNode := sum PropFSet Results.

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
  | x::xs => if (EquivPropV γ (snd x)) then true else usedVar γ xs
  end.

Fixpoint extendPartition (π1 π2 : partitionTuple) :=
  match π2 with
  | nil => Some π1
  | x::xs => if inPartitionTuple x π1 then extendPartition π1 xs
              else (if usedVar (fst x) π1 then (if (EquivPropF (fst x) (snd x))
              then extendPartition π1 xs else None) else extendPartition (x::π1) xs)
  end.

Compute usedVar (#"a") ((# "p", # "a" ∨ # "b")::nil).
Compute extendPartition ((# "a", # "a")::nil) ((# "p", # "a" ∨ # "b")::nil).
Compute extendPartition ((# "p", # "a" ∨ # "b")::nil) ((# "a", # "a")::nil).
Compute extendPartition (nil) ((# "a", # "a")::nil).
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

Fixpoint filterpi (π : partitionTuple) :=
  match π with
  | nil => nil
  | x::xs => if EquivPropF (fst x) (snd x) then filterpi xs else x::(filterpi xs)
  end.

Definition partitions schema Γ := (partitions_help schema Γ nil).

Fixpoint removeFromSet remove Γ :=
  match Γ with
  | nil => nil
  | γ::γs => if EquivPropF γ remove then γs else γ::(removeFromSet remove γs)
  end.

Fixpoint removeMultSet Remove Γ :=
  match Remove with
  | nil => Γ
  | r::rs => removeMultSet rs (removeFromSet r Γ)
  end.

Print Denominator.
Print TableauNode.

Fixpoint denoApply (π : partitionTuple) (d : Denominator) : list TableauNode :=
  match d with
  | inr s => (inr s) :: nil
  | inl lst => let mapApply a b := applyPartition b a in
               map inl (map (mapApply π) lst)
  end.

Check (app).

Fixpoint tableauAppend (Γ : PropFSet) (T : list TableauNode) : list TableauNode :=
  match T with
  | nil => nil
  | node::rest => match node with
                  | inr res => inr res :: tableauAppend Γ rest
                  | inl lst => inl (lst ++ Γ) :: tableauAppend Γ rest
                  end
  end.

Print TableauNode.

Fixpoint applyRule' (rule : Rule) (T : TableauNode) : option (list TableauNode) :=
  match T with
  | inr res => Some ((inr res) :: nil)
  | inl Γ => match (partitions (getNumerator rule) Γ) with
             | nil => None
             | π::πs => let inst := applyPartition (getNumerator rule) π in
                        let X := removeMultSet inst Γ in
                        Some (tableauAppend X (denoApply π (getDenominator rule)))
             end
  end.

Definition IdRule : Rule := (((# "p")::(¬(# "p"))::nil), ((inr Closed)):Denominator).
Definition OrRule : Rule := (((# "p" ∨ # "q")::nil), (inl (((# "p")::nil)::((# "q")::nil)::nil))).
Definition AndRule : Rule := (((# "p" ∧ # "q")::nil), (inl (((# "p")::(# "q")::nil)::nil))).

Compute applyRule' IdRule (inl ((¬(#"a" ∨ #"b"))::(#"a" ∨ #"b")::(#"c" ∨ #"d")::(#"s")::nil)).
Compute applyRule' AndRule (inl ((¬(#"a" ∨ #"b"))::(#"a" ∧ #"b")::(#"c" ∨ #"d")::(#"s")::nil)).
Compute applyRule' OrRule (inl ((¬(#"a" ∨ #"b"))::(#"a" ∨ #"b")::(#"c" ∨ #"d")::(#"s")::nil)).
Compute applyRule' AndRule (inl ((¬(#"a" ∨ #"b"))::(#"a" ∨ #"b")::(#"c" ∨ #"d")::(#"s")::nil)).

Compute (partitions ((# "p")::(¬(# "p"))::nil) (((¬(#"a" ∨ #"b"))::(#"a" ∨ #"b")::(#"c" ∨ #"d")::(#"s")::nil))).
Compute (partitions ((# "p") :: nil) ((# "p") :: nil)).
Compute (extendPartition ((# "p", # "s") :: nil) ((# "s", ⊥)::nil) ).

Inductive DerTree :=
  | Unf : PropFSet -> DerTree
  | Der : PropFSet -> Rule -> list DerTree -> DerTree
  | Clf : DerTree
  .

Fixpoint instantiateAllPartitions (rule : Rule) (Γ : PropFSet) (π : list partitionTuple) : list (list TableauNode) :=
  match π with
  | nil => nil
  | x::xs => let inst := applyPartition (getNumerator rule) x in
                        let X := removeMultSet inst Γ in
                        (tableauAppend X (denoApply x (getDenominator rule)))
                          :: instantiateAllPartitions rule Γ xs
  end
.

Compute instantiateAllPartitions AndRule ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil)
  (partitions (getNumerator AndRule) ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil)).

Fixpoint applyRule' (rule : Rule) (T : TableauNode) : option (list TableauNode) :=
  match T with
  | inr res => Some ((inr res) :: nil)
  | inl Γ => match (partitions (getNumerator rule) Γ) with
             | nil => None
             | π::πs => let inst := applyPartition (getNumerator rule) π in
                        let X := removeMultSet inst Γ in
                        Some (tableauAppend X (denoApply π (getDenominator rule)))
             end
  end.
Fixpoint applyRuleN (rule : Rule) (T : TableauNode) : list (list TableauNode) :=
  match T with
  | inr res => ((inr res) :: nil) :: nil
  | inl Γ => match (partitions (getNumerator rule) Γ) with
             | nil => nil
             | π => instantiateAllPartitions rule Γ π
             end
  end.

Print map.

Definition errorMap := fun (A B : Type) (f : list A -> B) =>
  fix errorMap (l : list (list A)) : list B :=
    match l with
    | nil => nil
    | a :: t => match a with
                | nil => errorMap t
                | _ => f a :: errorMap t
                end
    end.

Fixpoint closeMap (l : list TableauNode) :=
  match l with
  | nil => nil
  | x::xs => match x with
             | inr Closed => Clf :: closeMap xs
             | _ => Unf x :: closeMap xs
             end
  end.

(*
Fixpoint applyRule (rule : Rule) (T : DerTree) : list DerTree :=
  match T with
  | Unf Γ => let llst := applyRuleN rule Γ in
              map (fun l => (Der Γ rule (closeMap l))) llst
  | Der Γ r derlist => let children := map (applyRule rule) derlist in
              errorMap _ _ (Der Γ r) children
  | Clf => Clf :: nil
  end.
*)

Inductive treeResult (A : Type) : Type :=
  | ClosedLeaf : treeResult A
  | Ok : A -> treeResult A
  | FailRes : treeResult A
  .

Fixpoint treeResBranch (A B : Type) (f : A -> treeResult B) (branches : list A) : treeResult B :=
  match branches with
  | nil => FailRes _
  | b::bs => match f b with
             | FailRes _ => FailRes _
             | ClosedLeaf _ => treeResBranch _ _ f bs
             | Ok _ res => Ok _ res
             end
  end.

Fixpoint derTreeCons (x : treeResult DerTree) (xs : treeResult (list DerTree)) :=
  match x with
  | FailRes _ => FailRes _
  | ClosedLeaf _ => match xs with
                    | FailRes _ => FailRes _
                    | ClosedLeaf _ => FailRes _
                    | Ok _ ress => Ok _ (Clf :: ress)
                    end
  | Ok _ res => match xs with
                    | FailRes _ => FailRes _
                    | ClosedLeaf _ => FailRes _
                    | Ok _ ress => Ok _ (res :: ress)
                    end
  end.

Fixpoint derTreeResBind' (A : Type) (f : A -> treeResult DerTree) (branches : list A) (rule : Rule) (Γ : TableauNode) (acc : treeResult (list DerTree)) :=
  match branches with
  | nil => match acc with
           | Ok _ lst => match lst with
                         | nil => FailRes _
                         | _ => Ok _ (Der Γ rule lst)
                         end
           | _ => FailRes _
           end
  | b::bs => derTreeResBind' _ f bs rule Γ (derTreeCons (f b) acc)
  end.

Definition derTreeResBind (A : Type) (f : A -> treeResult DerTree) (branches : list A) rule Γ :=
  derTreeResBind' A f branches rule Γ (Ok _ nil).

Fixpoint forBranchRes (A B : Type) (f : A -> treeResult B) (branches : list A) : treeResult B :=
  match branches with
  | nil => FailRes _
  | b::bs => match f b with
             | FailRes _ => forBranchRes _ _ f bs
             | res => res
             end
  end.

Fixpoint forBranch (A B : Type) (f : A -> option B) (branches : list A) : option B :=
  match branches with
  | nil => None
  | b::bs => match f b with
             | None => forBranch _ _ f bs
             | Some res => Some res
             end
  end.

Print DerTree.

(* Given a list of branches (of nodes), generates the parents of said nodes in DerTree *)
Fixpoint derTreeAppend (rule : Rule) (Γ : PropFSet) (branches : list TableauNode) (acc : list DerTree): option DerTree :=
  match branches with
  | nil => match acc with
           | nil => None
           | _ => Some (Der Γ rule acc)
           end
  | node::rest => match node with
                  | inr Closed => derTreeAppend rule Γ rest (Clf :: acc)
                  | inl lst => derTreeAppend rule Γ rest (Unf lst :: acc)
                  end
  end.

Print tableauAppend.

Definition applyPartitionRuleD (rule : Rule) (Γ : PropFSet) (π : partitionTuple) :=
  let inst := applyPartition (getNumerator rule) π in
  let X := removeMultSet inst Γ in
  match π with
  | nil => None
  | _ => derTreeAppend rule Γ (tableauAppend X (denoApply π (getDenominator rule))) nil
  end.

Print DerTree.
Compute (applyPartitionRuleD AndRule (# "p"::nil) nil).

Check applyPartitionRuleD.

Print Denominator.
Print denoApply.
Print DerTree.
Print optionBind.

Definition optionCons (A : Type) (x : option A) (olst : option (list A)) :=
  match olst with
  | None => optionBind _ _ (fun a => Some (a::nil)) x
  | Some lst => match x with
         | None => olst
         | Some a => Some (a :: lst)
         end
  end.

Fixpoint optionSucMap' (A B : Type) (f : A -> option B) (xs : list A) (acc : option (list B)) :=
  match xs with
  | nil => acc
  | y::ys => optionSucMap' _ _ f ys (optionCons _ (f y) acc)
  end.

Definition optionSucMap (A B : Type) f xs := optionSucMap' A B f xs None.

(* Applies rule to a DerTree and gives a list of resulting derTrees. Only works on Leafs
   so that in the strat we apply a dft approach on the leaves such that this works *)
Fixpoint applyRuleD (rule : Rule) (T : DerTree) : option (list (DerTree)) :=
  match T with
  | Clf => Some (Clf :: nil)
  | Unf Γ => match (partitions (getNumerator rule) Γ) with
             | nil => None
             | Π => optionSucMap _ _ (applyPartitionRuleD rule Γ) Π
             end
  | Der Γ r lst => None
  end.

Compute applyRuleD AndRule (Unf (((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil))).

Print DerTree.
Print optionBind.

Inductive CRule := 
  | IdC : CRule
  | OrC : CRule
  | AndC : CRule.

Definition getCRule (cr : CRule) :=
  match cr with
  | IdC => IdRule
  | OrC => OrRule
  | AndC => AndRule
  end.

Inductive StrategyC :=
  | ApplyRule : CRule -> StrategyC
  | Sequence : StrategyC -> StrategyC -> StrategyC
  | Alternation : StrategyC -> StrategyC -> StrategyC
  | Skip : StrategyC
  | Fail : StrategyC
  | Repeat : StrategyC -> StrategyC
  .

Fixpoint stratLeftAlign (strat : StrategyC) : StrategyC :=
  match strat with
  | Sequence (Sequence s1 s2) s3 => Sequence s1 (Sequence s2 s3)
  | Alternation (Alternation s1 s2) s3 => Alternation s1 (Alternation s2 s3)
  | Sequence s1 s2 => Sequence (stratLeftAlign s1) (stratLeftAlign s2)
  | Alternation s1 s2 => Alternation (stratLeftAlign s1) (stratLeftAlign s2)
  | Repeat s => Repeat (stratLeftAlign s)
  | other => other
  end.

Fixpoint connectivesProp (F : PropF) :=
  match F with
  | # pv => 0
  | ⊥ => 0
  | a ∧ b
  | a ∨ b
  | a → b => 1 + connectivesProp a + connectivesProp b
  end.

Fixpoint connectivesSet (Γ : PropFSet) :=
  match Γ with
  | nil => 0
  | x::xs => connectivesProp x + connectivesSet xs
  end.

Lemma connectivesSetNonZero : forall Γ, connectivesSet Γ > 0.
Proof.
  induction Γ. simpl. omega.
  simpl. omega.
Qed.

Fixpoint maxList (A : Type) (f : A -> nat) (lst : list A) :=
  match lst with
  | nil => 0
  | x::xs => max (f x) (maxList _ f xs)
  end.

Check connectivesSet.

(* Define the relation as the maximum of leaves *)
Fixpoint countConnectivesDerTree (T : DerTree) :=
  match T with
  | Clf => 0
  | Unf Γ => connectivesSet Γ
  | Der _ _ branches => maxList _ id (map countConnectivesDerTree branches)
  end.

Definition countOptionConnectivesDer (T : option DerTree) :=
  match T with
  | None => 0
  | Some res => countConnectivesDerTree res
  end.

Definition countFirstConnectives (Tlist : option (list DerTree)) :=
  match Tlist with
  | None => 0
  | Some res => match res with
                | nil => 0
                | x::_ => countConnectivesDerTree x
                end
  end.

Print applyRuleD.

Fixpoint applyRuleDFirst (rule : Rule) (T : DerTree) :=
  match applyRuleD rule T with
  | Some (x::_) => Some x
  | _ => None
  end.

Lemma cRelDec : forall (r : CRule) (T : DerTree),
  countOptionConnectivesDer (Some T) > countOptionConnectivesDer (applyRuleDFirst (getCRule r) T).
Proof.
Admitted.
  (*intros. induction T; induction r; simpl in *.
    case (partitions (# "p" :: ¬ # "p" :: nil) p).
    simpl. apply connectivesSetNonZero.
    intros.
     unfold optionSucMap. simpl.
    case p0; simpl. 
    case (optionSucMap' partitionTuple DerTree
      (applyPartitionRuleD
         (# "p" :: ¬ # "p" :: nil, inr Closed) p) l).
    intros. induction l0; simpl; intuition; try apply connectivesSetNonZero.
    
    Check applyPartitionRuleD.
    Print applyPartitionRuleD.
    Print optionSucMap. *)

Print DerTree.
Print optionCons.

Fixpoint optionMap (A B : Type) (f : A -> option B) (lstA : list A) :=
  match lstA with
  | nil => Some nil
  | x::xs => match f x with
          | None => None
          | res => optionCons _ res (optionMap _ _ f xs)
          end
  end.

Fixpoint optionDerConstruct (f : DerTree -> option DerTree) (Γ : PropFSet) (rule : Rule) (branches : list DerTree) :=
  match branches with
  | nil => None
  | lst => match (optionMap _ _ f lst) with
           | None => None
           | Some res => Some (Der Γ rule res)
           end
  end.

Lemma maxAdd : forall n m, n + m <= 2 * max n m.
Proof.
  intros.
  pose (h1 := le_max_l n m).
  pose (h2 := le_max_r n m).
  intuition.
Qed.

Lemma connectivesProp_wf : well_founded (fun (p : PropF) q => connectivesProp p < connectivesProp q).
unfold well_founded.
induction a;
constructor; intros. try (simpl in *; induction y; simpl; try omega).
try (simpl in *; induction y; simpl; try omega).
simpl in *.
assert ((connectivesProp a1 + connectivesProp a2) <= (2 * max (connectivesProp a1) (connectivesProp a2)))
by apply maxAdd.
assert (connectivesProp y <= S ( 2 * Nat.max (connectivesProp a1) (connectivesProp a2))) by omega.
destruct IHa1.

(*
destruct (eq_nat_dec (connectivesProp y) (2 * max (connectivesProp a1) (connectivesProp a2))).
constructor. intros.
destruct (max_dec (connectivesProp a1) (connectivesProp a2)).
rewrite e0 in e.
apply IHa1. rewrite e in H2. exact H0.
rewrite e0 in e.
apply IHa2. rewrite e in H0. exact H0.
simpl in *.
apply IHa1. *)
Admitted.

Lemma connectivesSet_wf : well_founded (fun (Γ : PropFSet) Δ => connectivesSet Γ < connectivesSet Δ).
unfold well_founded. induction a.
constructor. intros. simpl in H. omega.
constructor. intros.
destruct (eq_nat_dec (connectivesSet y) (connectivesSet a0)).
constructor; intros. apply IHa. rewrite e in H0. exact H0.
apply IHa. simpl in *.
induction a; simpl in *; try (assumption).
Admitted.

Lemma rel_wfzzz : well_founded (fun (T1 : option DerTree) T2 =>
countOptionConnectivesDer T1  < countOptionConnectivesDer T2).
unfold well_founded. induction a.
induction a.
constructor. intros. simpl in *.


induction p. simpl in *. induction y; simpl in *. induction a.
simpl in *. induction p. simpl in *. omega. simpl in*.
induction a. simpl in *. constructor.
Admitted.

Lemma rel_wf : well_founded (fun (T1 : DerTree) T2 =>
countConnectivesDerTree T1  < countConnectivesDerTree T2).
Admitted.

Definition inputTest := prod DerTree StrategyC.

Lemma test_wf : well_founded (fun (x : inputTest) y =>
  countConnectivesDerTree (fst x) < countConnectivesDerTree (fst y)).
  Admitted.

Fixpoint mapTest (strat : StrategyC) (lstT : list DerTree) :=
  match lstT with
  | nil => nil
  | x::xs => (x, strat) :: mapTest strat xs
  end.

Definition constructorODer (Γ : PropFSet) (rule : Rule) (olst : option (list DerTree)) :=
  match olst with
  | None => None
  | Some res => Some (Der Γ rule res)
  end.

Definition applyStratNBleaf (T : DerTree) : StrategyC -> option DerTree.
  refine ((Fix rel_wf) (fun _ => StrategyC -> option DerTree)
  (fun T applyStratNBleaf_rec =>
  (match T as T' return (T=T' -> StrategyC -> option DerTree) with
  | Unf _ => fun H strat => (
             match strat with
             | Skip => Some T
             | Fail => None
             | ApplyRule r => applyRuleDFirst (getCRule r) T
             | Sequence s1 s2 => match applyStratNBleaf_rec T _ s1 with
                                 | None => None
                                 | Some Clf => Some Clf
                                 | Some (Der Γ r branches) => constructorODer Γ r (optionMap _ _ (fun i => applyStratNBleaf_rec i _ s1) branches)
                                 
                                 | _ => None
                                 end
             | Alternation s1 s2 => match applyStratNBleaf_rec T _ s1 with
                                    | None => applyStratNBleaf_rec T _ s2
                                    | res => res
                                    end
             | Repeat s => match applyStratNBleaf_rec T _ s with
                           | Some (Der Γ r branches) => constructorODer Γ r (optionMap _ _ (fun i => applyStratNBleaf_rec i _ (Repeat s)) branches)
                           | _ => Some T
                           end
             (*| _ => None*)
    end)
  | _ => fun _ _ => None
  end) eq_refl) T).
  rewrite H. simpl.
  admit.
  rewrite H. simpl. admit. admit. admit. admit.
Admitted.
  
  
  
  
  
  
  
Fixpoint applyStratNBleaf_norepeat (strat : StrategyC) (T : DerTree) :=
  match T with
  | Unf _ => match strat with
             | Skip => Some T
             | Fail => None
             | ApplyRule r => applyRuleDFirst (getCRule r) T
             | Sequence s1 s2 => match applyStratNBleaf_norepeat s1 T with
                                 | None => None
                                 | Some Clf => Some Clf
                                 | Some (Der Γ r branches) => 
                                 
                                 optionDerConstruct (applyStratNBleaf_norepeat s2) Γ r branches
                                 | _ => None
                                 end
             | Alternation s1 s2 => match applyStratNBleaf_norepeat s1 T with
                                    | None => applyStratNBleaf_norepeat s2 T
                                    | res => res
                                    end
             | _ => None
    end
  | _ => None
  end.

Fixpoint applyStratNB' (strat : StrategyC) (T : DerTree) :=
  match T with
  | Clf => Some Clf
  | Der Γ r branches => optionDerConstruct (applyStratNB' strat) Γ r branches
  | leaf => 
    match strat with
    | Skip => Some T
    | Fail => None
    | ApplyRule r => applyRuleDFirst (getCRule r) T
    | Sequence s1 s2 => optionBind _ _ (applyStratNB' s2) (applyStratNB' s1 T)
    | Alternation s1 s2 => match applyStratNB' s1 T with
                           | None => applyStratNB' s2 T
                           | res => res
                           end
    (*| Repeat s => applyStratNB' (Sequence (Alternation s Skip) (Repeat s)) T*)
    | _ => None
    end
  end.

(*
Fixpoint applyRule (rule : Rule) (T : DerTree) : list (treeResult DerTree) :=
  match T with
  | Unf Γ => match applyRuleN rule Γ with
             | nil => nil
             | llst => 
             Ok _ (map (fun l => (Der Γ rule (closeMap l))) llst)
             end
  | Der Γ r derlist => match derlist with
                       | nil => FailRes _
                       | b::bs => match b with
                                  | ClosedLeaf _ 
  | Clf => (ClosedLeaf _) :: nil
  end.

Fixpoint applyRules' (rule : Rule) (T : DerTree) : list (treeResult DerTree) :=
  match T with
  | Clf => Clf
  | Unf node => match applyRuleN rule Γ with
                | nil => FailRes _
                | 

Fixpoint applyStrat' (strat : Strategy) (T : DerTree) : treeResult DerTree :=
  match T with
  | Unf node => match strat with
                | Skip => Ok _ (Unf node)
                | Fail => FailRes _
                | ApplyRule r => match applyRule Γ r with
                                 | nil => FailRes _
                                 | r::res => Ok _ r
                                 end
                | Sequence s1 s2 => match s1 with
                                    | ApplyRules r => forBranchRes _ _ (applyStrat' s1) 
                                    | _ => 
                end
  | Der node rule children =>
  | Clf => Clf
*)
(*
Fixpoint applyRule (rule : Rule) (T : DerTree) : treeResult (list DerTree) :=
  match T with
  | Unf Γ => match applyRuleN rule Γ with
             | nil => FailRes _
             | llst => Ok _ (map (fun l => (Der Γ rule (closeMap l))) llst)
             end
  | Der Γ r derlist => match derlist with
                       | nil => FailRes _
                       | lst => treeResBranch _ _ (applyRule rule) lst
                       end
  | Clf => ClosedLeaf _
  end.

Fixpoint applyRule (rule : Rule) (T : DerTree) : option (list DerTree) :=
  match T with
  | Unf Γ => let llst := applyRuleN rule Γ in
              Some (map (fun l => (Der Γ rule (closeMap l))) llst)
  | Der Γ r derlist => let children := map (applyRule rule) derlist in
              errorMap _ _ (Der Γ r) children
  | Clf => Some (Clf :: nil)
  end.

Compute applyRule AndRule (Unf (inl ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil))).
Compute applyRule AndRule (Der
         (inl
            (# "a" ∧ # "b" → ⊥
             :: # "a" ∧ # "b"
                :: # "c" ∧ # "d" :: # "s" :: nil))
         (# "p" ∧ # "q" :: nil,
         inl ((# "p" :: # "q" :: nil) :: nil))
         (Unf
            (inl
               (# "a"
                :: # "b"
                   :: # "a" ∧ # "b" → ⊥
                      :: # "c" ∧ # "d" :: # "s" :: nil))
          :: nil)).
(* Should return nil as no leaf can be used with or rule *)
Compute applyRule OrRule (Der
         (inl
            (# "a" ∧ # "b" → ⊥
             :: # "a" ∧ # "b"
                :: # "c" ∧ # "d" :: # "s" :: nil))
         (# "p" ∧ # "q" :: nil,
         inl ((# "p" :: # "q" :: nil) :: nil))
         (Unf
            (inl
               (# "a"
                :: # "b"
                   :: # "a" ∧ # "b" → ⊥
                      :: # "c" ∧ # "d" :: # "s" :: nil))
          :: nil)).
Compute applyRule OrRule (Unf (inl ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil))).
Compute applyRule OrRule (Unf (inl ((¬(#"a" ∧ #"b"))::(#"a" ∨ #"b")::(#"c" ∧ #"d")::(#"s")::nil))).
Compute applyRule AndRule (Der
         (inl
            (# "a" ∧ # "b" → ⊥
             :: # "a" ∨ # "b"
                :: # "c" ∧ # "d" :: # "s" :: nil))
         (# "p" ∨ # "q" :: nil,
         inl ((# "p" :: nil) :: (# "q" :: nil) :: nil))
         (Unf
            (inl
               (# "a"
                :: # "a" ∧ # "b" → ⊥
                   :: # "c" ∧ # "d" :: # "s" :: nil))
          :: Unf
               (inl
                  (# "b"
                   :: # "a" ∧ # "b" → ⊥
                      :: # "c" ∧ # "d" :: # "s" :: nil))
             :: nil)).
*)
(*
Definition addHistory := fun (steps : list DerTree) :=
  fix addHistory (branches : list DerTree) :=
  match branches with
  | nil => nil
  | x::xs => match x with
             | nil => addHistory xs
             | _ => (x :: steps
*)

(* History is currently being displayed as a list of lists of (DerTree, Strategy) Tuples *)
(*
Definition historyStack := list (list (prod DerTree Strategy)).

Fixpoint popHistory (history : historyStack) : option (prod (prod DerTree Strategy) historyStack) :=
  match history with
  | nil => None
  | level::rst => match level with
                  | nil => popHistory rst
                  | x::xs => Some (x, (xs::rst))
                  end
  end.

Definition pushHistory entry (history : historyStack) := entry :: history.

Definition stackPair := prod DerTree historyStack.

Fixpoint applyStrategy' (strat : Strategy) (pair : stackPair) : option DerTree :=
  let (Γ, history) := pair in
  match strat with
  | Skip => Some Γ
  | Fail => match popHistory history with
            | None => None
            | Some ((Γ', strat'), history') => applyStrategy' strat' (Γ', history')
            end
  | _ => None
  end.
  | ApplyRule r => let next := applyRule r Γ in
                   match next with
                   | nil => match popHistory history with
                            | None => nil
                   | x::xs => applyRule 
                   end
  | Sequence s1 s2 => let next1 := applyStrategy' s1 Γ in optionBind _ _ (applyStrategy' s2) next1
  | _ => None
  end.
*)

Fixpoint applyStrategy' (strat : Strategy) (Γ : DerTree) : option DerTree :=
  match strat with
  | Skip => Some Γ
  | Fail => None
  | ApplyRule r => match applyRule r Γ with
                   | nil => None
                   | x::_ => Some x
                   end
  | Sequence s1 s2 => match s1 with
                      | ApplyRule r => forBranch _ _ (applyStrategy' s2) (applyRule r Γ)
                      | other => optionBind _ _ (applyStrategy' s2) (applyStrategy' s1 Γ)
                      end
  | Alternation s1 s2 => match applyStrategy' s1 Γ with
                         | None => applyStrategy' s2 Γ
                         | Some res => Some res
                         end
  | _ => None
  end.

Definition applyStrategy (strat : Strategy) (Γ : PropFSet) : option DerTree :=
  applyStrategy' (stratLeftAlign strat) (Unf (inl Γ)).

Compute applyStrategy (ApplyRule AndRule) ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil).
Compute applyStrategy (Sequence (ApplyRule AndRule) (ApplyRule AndRule)) ((¬(#"a" ∧ #"b"))::(#"a" ∧ #"b")::(#"c" ∧ #"d")::(#"s")::nil).

Definition SystematicTableau 

Recursive Extraction applyRule.