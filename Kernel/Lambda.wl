(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`Lambda`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


RandomLambda;
EnumerateLambdas;

LambdaSubstitute;
EvalLambda;
LambdaFreeVariablePositions;

BetaReductions;
BetaReduce;
EtaReduce;

LambdaFunction;
FunctionLambda;

TagLambda;
ColorizeLambda;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


EnumerateLambdas[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1] :=
	\[FormalLambda] /@ If[ depth == maxDepth,
		Groupings[Catenate[Tuples[Range[maxDepth], #] & /@ Range[maxLength]], {Construct -> 2}],
		Groupings[Catenate[Tuples[Join[Range[depth], EnumerateLambdas[maxDepth, maxLength, depth + 1]], #] & /@ Range[maxLength]], {Construct -> 2}]
	]


randomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1] := \[FormalLambda] @ If[ depth == maxDepth,
	Fold[Construct, RandomInteger[{1, depth}, RandomInteger[{1, maxLength}]]],
	Fold[Construct, Table[randomLambda[maxDepth, maxLength, depth + 1], RandomInteger[{1, maxLength}]]]
]
RandomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, n : _Integer | Automatic : Automatic] := If[n === Automatic, randomLambda[maxDepth, maxLength], Table[randomLambda[maxDepth, maxLength], n]]


(* From Max Niederman *)

(* offset only the free variables in a lambda term *)
offsetFree[\[FormalLambda][body_], offset_, depth_ : 0] := \[FormalLambda][offsetFree[body, offset, depth + 1]]
offsetFree[fun_[x_], offset_, depth_ : 0] := offsetFree[fun, offset, depth][offsetFree[x, offset, depth]]
offsetFree[var_Integer, offset_, depth_ : 0] := If[var > depth, var + offset, var]
offsetFree[expr_, offset_, depth_ : 0] := expr

(* perform a substitution of an argument into the body of a lambda, and also decrement the free parameters by one *)
betaSubstitute[\[FormalLambda][body_], arg_, paramIdx_ : 1] := \[FormalLambda][betaSubstitute[body, arg, paramIdx + 1]]
betaSubstitute[fun_[x_], arg_, paramIdx_ : 1] := betaSubstitute[fun, arg, paramIdx][betaSubstitute[x, arg, paramIdx]]
betaSubstitute[var_Integer, arg_, paramIdx_ : 1] := Which[
	var < paramIdx, var,
	var == paramIdx,  offsetFree[arg, paramIdx - 1],
	var > paramIdx, var - 1
]
betaSubstitute[expr_, arg_, paramIdx_ : 1] := expr

(* find all possible beta-reductions by walking the expression tree applying betaSubstitute where possible *)
BetaReductions[\[FormalLambda][body_][arg_]] := Join[
	{betaSubstitute[body, arg]},
	\[FormalLambda][#][arg] & /@ BetaReductions[body],
	\[FormalLambda][body][#] & /@ BetaReductions[arg]
]
BetaReductions[\[FormalLambda][body_]] := \[FormalLambda] /@ BetaReductions[body]
BetaReductions[fun_[arg_]] := Join[#[arg] & /@ BetaReductions[fun], fun[#] & /@ BetaReductions[arg]]
BetaReductions[expr_] := {}


BetaReduce[expr_] := expr //. \[FormalLambda][body_][arg_] :> betaSubstitute[body, arg]
BetaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, \[FormalLambda][_][_]]}, If[MissingQ[pos], expr, BetaReduce[ReplaceAt[expr, \[FormalLambda][body_][arg_] :> betaSubstitute[body, arg], pos], n - 1]]]
]


(* substitute all variables *)
LambdaSubstitute[expr_, vars_Association : <||>, depth_Integer : 0] := If[ Length[vars] == 0,
	expr
	,
	Replace[expr, {
		\[FormalLambda][body_] :> \[FormalLambda][LambdaSubstitute[body, vars, depth + 1]],
		f_[x_] :> LambdaSubstitute[f, vars, depth][LambdaSubstitute[x, vars, depth]],
		var_Integer :> If[KeyExistsQ[vars, var - depth], offsetFree[Lookup[vars, var - depth], depth + 1], var]
	}]
]


EvalLambda[expr_, vars_Association : <||>, n : _Integer | Infinity : Infinity, k_Integer : 0] := If[ k >= n,
	With[{subst = LambdaSubstitute[expr, vars]}, Sow[k]; subst]
	,
	Replace[
		expr,
		{
			(* beta reductions uses argument->head order *)
			(lambda : \[FormalLambda][body_])[arg_] :> With[{evalArg = Reap[EvalLambda[arg, vars, n, k]]}, {l = evalArg[[2, 1, 1]]},
				If[ l >= n,
					With[{subst = LambdaSubstitute[lambda, vars]}, Sow[If[subst === lambda, l, l + 1]]; subst[evalArg[[1]]]]
					,
					offsetFree[EvalLambda[body, <|1 -> evalArg[[1]], KeyMap[# + 1 &, vars]|>, n, l + 1], -1]
				]
			],
			\[FormalLambda][body_] :> \[FormalLambda][EvalLambda[body, KeyMap[# + 1 &, vars], n, k]],
			(* standard head->argument evaluation order *)
			head_[arg_] :> With[{evalHead = Reap[EvalLambda[head, vars, n, k]]}, {evalArg = Reap[EvalLambda[arg, vars, n, evalHead[[2, 1, 1]]]]}, {l = evalArg[[2, 1, 1]]},
				If[ evalHead[[1]][evalArg[[1]]] === head[arg],
					With[{subst = LambdaSubstitute[head[arg], vars]}, Sow[If[subst === expr, l, l + 1]]; subst],
					If[ l >= n,
						With[{subst = LambdaSubstitute[evalHead[[1]][evalArg[[1]]], vars]}, Sow[If[subst === expr, l, l + 1]]; subst]
						,
						EvalLambda[evalHead[[1]][evalArg[[1]]], vars, n, l]
					]
				]
			]
			,
			_ :> With[{subst = LambdaSubstitute[expr, vars]}, Sow[k]; subst]
		}
	]
]


EtaReduce[expr_] := expr //. \[FormalLambda][(f : Except[_Integer])[1]] :> f
EtaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, \[FormalLambda][Except[_Integer][1]]]}, If[MissingQ[pos], expr, EtaReduce[ReplaceAt[expr, \[FormalLambda][f_[1]] :> f, pos], n - 1]]]
]


LambdaFreeVariablePositions[expr_, pos_List : {}, depth_Integer : 0] :=  Replace[expr, {
	\[FormalLambda][body_][arg_] :> Join[LambdaFreeVariablePositions[body, Join[pos, {0, 1}], depth + 1], LambdaFreeVariablePositions[arg, Append[pos, 1], depth]],
	\[FormalLambda][body_] :> LambdaFreeVariablePositions[body, Append[pos, 1], depth + 1],
	f_[x_] :> Join[LambdaFreeVariablePositions[f, Append[pos, 0], depth], LambdaFreeVariablePositions[x, Append[pos, 1], depth]],
	var_Integer :> If[var > depth, {pos}, {}]
}
]


TagLambda[expr_, lambdas_Association] := With[{
	nextLambdas = KeyMap[# + 1 &] @ lambdas
},
	expr /. {
		\[FormalLambda][body_][y_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]][TagLambda[y, lambdas]]],
		\[FormalLambda][body_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]]],
		term_Integer :> Interpretation[term, Evaluate @ lambdas[term][[2]]]
	}
]
TagLambda[\[FormalLambda][body_]] := With[{lambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, lambda[TagLambda[body, <|1 -> lambda|>]]]
TagLambda[expr_] := expr /. lambda_\[FormalLambda] :> TagLambda[lambda]


LambdaFunction[expr_, head_ : Identity] := head[Evaluate @ TagLambda[expr]] //. {Interpretation["\[Lambda]", x_][body_] :> Function[x, body], Interpretation[_Integer, x_] :> x}


FunctionLambda[expr_, vars_Association : <||>] := Replace[Unevaluated[expr], {
	Verbatim[Function][var_, body_][x_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]][FunctionLambda[x, vars]],
	Verbatim[Function][var_, body_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]],
	f_[x_] :> FunctionLambda[Unevaluated[f], vars][FunctionLambda[Unevaluated[x], vars]],
	var_Symbol :> Lookup[vars, var]
}]


ColorizeTaggedLambda[lambda_] := With[{lambdas = Union @ Cases[lambda, Interpretation["\[Lambda]", x_], All, Heads -> True]},
	lambda /. MapThread[x : #1 | Interpretation[_Integer, Evaluate @ #1[[2]]] :> Style[x, Bold, #2] &, {lambdas, ColorData[109] /@ Range[Length[lambdas]]}]
]


ColorizeLambda[expr_] := expr /. lambda_\[FormalLambda] :> ColorizeTaggedLambda[TagLambda[lambda]]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
