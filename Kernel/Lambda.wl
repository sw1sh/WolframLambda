(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`Lambda`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


RandomLambda;
EnumerateLambdas;
EvalLambda;
TagLambda;
LambdaFunction;
FunctionLambda;
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


LambdaSubstitute[expr_, vars_Association] := Replace[expr, {
	\[FormalLambda][body_] :> \[FormalLambda][LambdaSubstitute[body, KeyMap[# + 1 &] @ vars]],
	var_Integer :> Replace[var, vars],
	f_[x_] :> LambdaSubstitute[f, vars][LambdaSubstitute[x, vars]]
}]


EvalLambda[expr_, vars_Association] := Replace[expr, {
	\[FormalLambda][body_][y_] :> EvalLambda[body, Prepend[1 -> EvalLambda[y, vars]] @ KeyMap[# + 1 &] @ vars],
	lambda_\[FormalLambda] :> LambdaSubstitute[lambda, vars],
	_ :> EvalLambda[LambdaSubstitute[expr, vars]]
}]
EvalLambda[expr_] := expr /. \[FormalLambda][body_][x_] :> EvalLambda[body, <|1 -> x|>]


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
