Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Require Import String.
Require Import Coq.Lists.List.
Import ListNotations.

Section ListUtil.

Variable V : Set.
Hypothesis V_eq_dec : forall x y : V, { x = y } + { x <> y }.

(* TODO: prove *)
Axiom edge_eq_dec : 
	forall (x y : prod String String), { x = y } + { x <> y }.

Fixpoint FilterLenGEQ (L : list String) (a : String) : list String :=
	match L with
	| [] => []
	| b :: R => 
		if le_lt_dec (length a) (length b) then
			b :: FilterLenGEQ R a
		else
			FilterLenGEQ R a
	end.

Fixpoint StalinSort (L : list String) : list String :=
	match L with
	| [] => []
	| a :: R => a :: FilterLenGEQ (StalinSort R) a
	end.

Definition FilterMax (L : list String) : list String :=
	rev (StalinSort (rev (StalinSort L))).

Fixpoint RemoveFirst (L : list V) (a : V) : list V :=
	match L with
	| [] => []
	| b :: R => if V_eq_dec a b then R else (b :: (RemoveFirst R a))
	end.

Fixpoint RemoveAll (L : list V) (a : V) : list V :=
	match L with
	| [] => []
	| b :: R => if V_eq_dec a b then RemoveAll R a else (b :: RemoveAll R a)
	end.

Fixpoint Contains (L : list V) (a : V) : bool :=
	match L with
	| [] => false
	| b :: R => if V_eq_dec a b then true else Contains R a
	end.

Fixpoint Count (L : list V) (a : V) : nat :=
	match L with
	| [] => 0
	| b :: R => 
		if V_eq_dec a b then
			1 + (Count R a)
		else 
			Count R a
	end.

Fixpoint RemoveDuplicates' (S L : list V) : list V :=
	match L with
	| [] => S
	| a :: R =>
		if Contains S a then
			RemoveDuplicates' S R
		else
			RemoveDuplicates' (a :: S) R
	end.

Definition RemoveDuplicates (L : list V) : list V :=
	RemoveDuplicates' [] L.

Fixpoint RemoveList (L S : list V) : list V :=
	match S with
	| [] => L
	| a :: R => RemoveList (RemoveFirst L a) R
	end.

Fixpoint StrSuffixes (L : list String) : list String :=
	match L with
	| [] => []
	| a :: R => (suff a) :: StrSuffixes R
	end.

Fixpoint StrPrefixes (L : list String) : list String :=
	match L with
	| [] => []
	| a :: R => (pref a) :: StrPrefixes R
	end.

Fixpoint StrMaxLen' (L : list String) (n : nat) {struct L} : nat :=
	match L with
	| [] => n
	| a :: R => StrMaxLen' R (max n (length a))
	end.

Definition StrMaxLen (L : list String) : nat := StrMaxLen' L 0.

Variable U : Set.
Hypothesis U_le : U -> U -> bool.
Hypothesis U_le_dec : 
	forall (x y : U), { U_le x y = true } + { U_le y x = true }.

Fixpoint InsertSorted (L : list U) (z : U) : list U :=
	match L with
	| [] => [z]
	| a :: R =>
		if U_le_dec z a then
			z :: a :: R
		else
			a :: InsertSorted R z
	end.

Fixpoint Sort' (L S : list U) {struct L} : list U :=
	match L with
	| [] => S
	| a :: R => Sort' R (InsertSorted S a)
	end.

Definition Sort (L : list U) : list U :=
	Sort' L [].

End ListUtil.
