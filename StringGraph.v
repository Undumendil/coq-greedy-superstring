Require Import GraphBasics.Graphs.
Require Import String.
Require Import Bool.Bool.
Require Import ZArith.
Require Import ListUtil.
Import ListNotations.

Section StringGraph.

Definition StringGraphEdge := prod String String.
Notation "A -> B" := (pair A B).

Definition From (E : StringGraphEdge) : String :=
	match E with
	| pair A _ => A
	end.

Definition To (E : StringGraphEdge) : String :=
	match E with
	| pair _ B => B
	end.

Definition edge_le (x y : StringGraphEdge) : bool :=
	if (length (From x)) <? (length (From y)) then
		true
	else
		if (length (From y)) <? (length (From x)) then
			false
		else
			if str_lt (From x) (From y) then
				true
			else
				if str_lt (From y) (From x) then
					false
				else
					if str_le (To x) (To y) then
						true
					else
						false.

Axiom edge_le_dec : forall (x y : StringGraphEdge), { edge_le x y = true } + { edge_le y x = true }.

Definition InLowerEdge (S : String) : StringGraphEdge :=
	(pref S) -> S.

Definition OutLowerEdge (S : String) : StringGraphEdge :=
	S -> (suff S).

Fixpoint LowerEdges (S : list String) : list StringGraphEdge :=
	match S with
	| [] => []
	| s :: R => match s with
		| [] => LowerEdges R
		| _ => (InLowerEdge s) :: (OutLowerEdge s) :: LowerEdges R
		end
	end.

Fixpoint InEdges (S : list StringGraphEdge) (s : String) {struct S} : list StringGraphEdge :=
	match S with
	| [] => []
	| e :: R => 
		if str_eq_dec s (To e) then
			e :: InEdges R s
		else
			InEdges R s
	end.

Fixpoint OutEdges (S : list StringGraphEdge) (s : String) {struct S} : list StringGraphEdge :=
	match S with
	| [] => []
	| e :: R => 
		if str_eq_dec s (From e) then
			e :: OutEdges R s
		else
			OutEdges R s
	end.

Fixpoint OutVertices (S : list StringGraphEdge) (s : String) {struct S} : list String :=
	match S with
	| [] => []
	| e :: R =>
		if str_eq_dec s (From e) then
			(To e) :: OutVertices R s
		else
			OutVertices R s
	end.

Fixpoint OutVerticesBatch (S : list StringGraphEdge) (L : list String) {struct L} : list String :=
	match L with
	| [] => []
	| s :: R => RemoveDuplicates String str_eq_dec ((OutVertices S s) ++ (OutVerticesBatch S R))
	end.

Fixpoint GraphHeight (E : list StringGraphEdge) : nat :=
	match E with
	| [] => 0
	| e :: R => 
		max 
			(max 
				(length (From e)) 
				(length (To e))) 
			(GraphHeight R)
	end.

Fixpoint GenerateVertices' (E : list StringGraphEdge) (C B : list String) (n : nat) {struct n} : list String :=
	match n with
	| 0 => C
	| S k => let M := (RemoveList String str_eq_dec (OutVerticesBatch E C) B) in
		C ++ (GenerateVertices' E M (RemoveDuplicates String str_eq_dec (C ++ B)) k)
	end.

Definition GenerateVertices (E : list StringGraphEdge) : list String :=
	GenerateVertices' E [[]] [] (GraphHeight E).

(*Fixpoint ToVertex (E : list StringGraphEdge) : Vertex :=
	match E with
	| [] => V_nil
	| e :: R => *)

Fixpoint ConstructFullGraphLayer (S : list String) : list StringGraphEdge :=
	let M := FilterMax S in
		match M with
		| [] => []
		| _ => RemoveDuplicates StringGraphEdge edge_eq_dec (LowerEdges M)
		end.

Fixpoint ConstructFullGraph' (L : list String) (lev : nat) {struct lev} : list StringGraphEdge :=
	match lev with                        (* level is the maximal length of strings from L *)
	| 0 => []                             (* level 0, no more edges *)
	| S k =>                              (* it is known there are nodes of maximum level k *)
		let M := FilterMax L in
			(ConstructFullGraphLayer L)   (* edges between levels k and k+1 *)
			++
			(ConstructFullGraph'          (* edges below, if any *)
				(RemoveDuplicates String str_eq_dec (
					(StrSuffixes M)
					++
					(StrPrefixes M)
					++
					(RemoveList String str_eq_dec L M)
				))
				k)
	end.

Definition ConstructFullGraph (L : list String) : list StringGraphEdge :=
	ConstructFullGraph' L (StrMaxLen L).

Fixpoint FilterEdgeLevel (S : list StringGraphEdge) (l : nat) {struct S} : list StringGraphEdge :=
	match S with
	| [] => []
	| e :: R => 
		if ((length (From e)) =? l) && ((length (To e)) =? (1 + l)) then
			e :: FilterEdgeLevel R l
		else
			if ((length (To e)) =? l) && ((length (From e)) =? (1 + l)) then
				e :: FilterEdgeLevel R l
			else
				FilterEdgeLevel R l
	end.

Fixpoint FilterVertexLevel (S : list StringGraphEdge) (l : nat) {struct S} : list String :=
	match S with
	| [] => []
	| e :: R => 
		if (length (From e)) =? l then
			RemoveDuplicates String str_eq_dec ((From e) :: FilterVertexLevel R l)
		else
			if (length (To e)) =? l then
				RemoveDuplicates String str_eq_dec ((To e) :: FilterVertexLevel R l)
			else
				FilterVertexLevel R l
	end.

Fixpoint GenerateSuperstring' (E : list StringGraphEdge) (V : String) (n : nat) {struct n} : String :=
	match n with
	| 0 => []
	| S k =>
		match OutEdges E V with
		| [] => [] (* Impossible in properly generated graphs *)
		| e :: R =>
			if (length (From e)) <? (length (To e)) then
				(last (To e) Z0) :: GenerateSuperstring' (RemoveFirst StringGraphEdge edge_eq_dec E e) (To e) k
			else
				GenerateSuperstring' (RemoveFirst StringGraphEdge edge_eq_dec E e) (To e) k
		end
	end.

Fixpoint GenerateSuperstring (E : list StringGraphEdge) : String :=
	GenerateSuperstring' E [] (length E).

Fixpoint FindTrivialSolution' (T : String) (E : list StringGraphEdge) (V : String) (n : nat) {struct n} : list StringGraphEdge :=
	match n with
	| 0 => []
	| S k =>
		match T with
		| [] =>
			match V with
			| [] => []
			| v :: R =>
				let eDown := pair V R in
					eDown :: FindTrivialSolution' T (RemoveFirst StringGraphEdge edge_eq_dec E eDown) R k
			end
		| t :: R =>
			if (length T) <=? (length V) then
				match V with
				| [] => []
				| v :: W =>
					let eDown := pair V W in
						eDown :: FindTrivialSolution' T (RemoveFirst StringGraphEdge edge_eq_dec E eDown) W k
				end
			else
				let ch := nth (length V) T Z0 in (* will always succeed *)
					let eUp := pair V (V ++ [ch]) in
						if Contains StringGraphEdge edge_eq_dec E eUp then
							eUp :: FindTrivialSolution' T (RemoveFirst StringGraphEdge edge_eq_dec E eUp) (V ++ [ch]) k
						else (* the only way is down *)
							match V with
							| [] => [] (* impossible since T's length > 0 *)
							| v :: W =>
								let eDown := pair V W in
									eDown :: FindTrivialSolution' R (RemoveFirst StringGraphEdge edge_eq_dec E eDown) W k
							end
		end
	end.

Definition FindTrivialSolution (S : list String) (E : list StringGraphEdge) : list StringGraphEdge :=
	FindTrivialSolution' (ListSuperstring S) E [] (length E).

End StringGraph.
