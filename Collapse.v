Require Import String.
Require Import StringGraph.
Require Import ListUtil.
Require Import Bool.Bool.
Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Section Collapse.

Definition Double (S : list StringGraphEdge) : list StringGraphEdge :=
	S ++ S.

Fixpoint FindInEdgesFrom (L : list StringGraphEdge) (A : String) {struct L} : list StringGraphEdge :=
	match L with
	| [] => []
	| e :: R =>
		if str_eq_dec (To e) A then
			e :: FindInEdgesFrom R A
		else
			FindInEdgesFrom R A
	end.

(* H : connected components of the same level as A *)
Fixpoint CollapseNodeAtLevel' (H : list list String) (S L : list StringGraphEdge) (A : String) {struct L} : list StringGraphEdge) :=
	match L with
	| [] => S
	| e :: R =>
		if str_eq_dec (To e) A then (* L is sorted so no more edges will be removed *)
			S
		else
			match FindInEdgesFrom L A with
			| [] => CollapseNodeAtLevel' S R A
			| [u] => (* ... *)
			| u :: U =>
				let eCollapsed := pair (pref (suff (From e))) (To e) in
					let uCollapsed := pair (From u) (suff (pref (To u))) in
						CollapseNodeAtLevel' (eCollapsed :: uCollapsed :: (RemoveList StringGraphEdge edge_eq_dec S [e; u])) R A
			end
	end.
								

Fixpoint CollapseLevel' (S B : list StringGraphEdge) (l : nat) {struct S} : list StringGraphEdge :=
	match S with
	| [] => []
	| e :: R => S (* ... *)
		(*if (length ())*)
	end.
	
Definition CollapseLevel (S : list StringGraphEdge) (l : nat) : list StringGraphEdge :=
	CollapseLevel' S [] l.

Fixpoint RemoveLowerPairsFor' (S B : list StringGraphEdge) (V : String) {struct S} : list StringGraphEdge :=
	match S with
	| [] => []
	| e :: R =>
		if Contains StringGraphEdge edge_eq_dec B e then (* B: edges marked for removal *)
			RemoveLowerPairsFor' R (RemoveFirst StringGraphEdge edge_eq_dec B e) V
		else
			let eInv := pair (To e) (From e) in
				let eInvBlacklisted := Count StringGraphEdge edge_eq_dec B eInv in
					let eInvRemaining := Count StringGraphEdge edge_eq_dec R eInv in
						let eRemaining := Count StringGraphEdge edge_eq_dec R e in
							if str_eq_dec (From e) [] then
								if (eInvBlacklisted + 2) <=? eInvRemaining then
									RemoveLowerPairsFor' R (eInv :: B) V
								else
									if (0 <? eRemaining) && ((1 + eInvBlacklisted) <=? eInvRemaining) then
										RemoveLowerPairsFor' R (eInv :: B) V
									else
										e :: RemoveLowerPairsFor' R B V
							else
								if str_eq_dec (To e) [] then
									if (eInvBlacklisted + 2) <=? eInvRemaining then
										RemoveLowerPairsFor' R (eInv :: B) V
									else
										if (0 <? eRemaining) && ((1 + eInvBlacklisted) <=? eInvRemaining) then
											RemoveLowerPairsFor' R (eInv :: B) V
										else
											e :: RemoveLowerPairsFor' R B V
								else
									e :: RemoveLowerPairsFor' R B V
	end.

Definition RemoveLowerPairsFor (S : list StringGraphEdge) (V : String) : list StringGraphEdge :=
	RemoveLowerPairsFor' S [] V.

Fixpoint RemoveLowerPairs' (S : list StringGraphEdge) (V : list String) {struct V} : list StringGraphEdge :=
	match V with
	| [] => S
	| v :: R => RemoveLowerPairs' (RemoveLowerPairsFor S v) R
	end.

Definition RemoveLowerPairs (S : list StringGraphEdge) :=
	RemoveLowerPairs' S (FilterVertexLevel S 1).

Fixpoint Collapse' (S : list StringGraphEdge) (l : nat) {struct l} : list StringGraphEdge :=
	match l with
	| 0 | 1 => RemoveLowerPairs S
	| S k => Collapse' (CollapseLevel S l) k
	end.

Definition Collapse (S : list StringGraphEdge) : list StringGraphEdge :=
	Collapse' S (GraphHeight S).

Definition DoubleAndCollapse (S : list String) : String :=
	GenerateSuperstring (Collapse (Double (FindTrivialSolution S (ConstructFullGraph S)))).

End Collapse.
