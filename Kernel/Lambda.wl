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
LambdaFreeVariables;

BetaReductions;
BetaReduce;
EtaReduce;

LambdaFunction;
FunctionLambda;
LambdaTree;
LambdaConvert;

TagLambda;
ColorizeLambda;
LambdaSmiles;


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
offsetFree[expr_, 0, ___] := expr
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
LambdaSubstitute[expr_, vars_Association : <||>, offset_Integer : 0, depth_Integer : 0, subDepth_Integer : 0] :=
	If[ Length[vars] == 0,
	expr
	,
	Replace[expr, {
		\[FormalLambda][body_] :> \[FormalLambda][LambdaSubstitute[body, vars, offset, depth, subDepth + 1]],
		f_[x_] :> LambdaSubstitute[f, vars, offset, depth, subDepth][LambdaSubstitute[x, vars, offset, depth, subDepth]],
		var_Integer :> 
			If[	KeyExistsQ[vars, var - subDepth],
				(* argument variable substitutution *)
				offsetFree[Lookup[vars, var - subDepth], subDepth + depth]
				,
				(* free or bound variable *)
				If[	var > subDepth + depth + 1,
					(* free variable *)
					var + offset,
					(* bound variable *)
					var
				]
			]
	}]
]

(* TODO: non-recursive version *)
(* this tries to delay substitution *)
EvalLambda[expr_, vars_Association : <||>, n : _Integer | Infinity : Infinity, k_Integer : 0, offset_Integer : 0, depth_Integer : 0] := If[ k >= n,
	With[{subst = LambdaSubstitute[expr, vars, offset, depth]}, Sow[k]; subst]
	,
	Replace[
		expr,
		{
			(* beta reductions uses argument->head order *)
			(lambda : \[FormalLambda][body_])[arg_] :> With[{evalArg = Reap[EvalLambda[arg, vars, n, k, offset, depth]]},
				{l = If[MatchQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n,
					With[{subst = LambdaSubstitute[lambda, vars, offset, depth][evalArg[[1]]]}, Sow[If[subst === lambda, l, l + 1]]; subst]
					,
					EvalLambda[body, <|1 -> evalArg[[1]], KeyMap[# + 1 &, vars]|>, n, l + 1, -1]
				]
			],
			\[FormalLambda][body_] :> \[FormalLambda][EvalLambda[body, KeyMap[# + 1 &, vars], n, k, offset, depth + 1]],
			(* standard head->argument evaluation order *)
			head_[arg_] :> With[
				{evalHead = Reap[EvalLambda[head, vars, n, k, offset, depth]]},
				{evalArg = If[MatchQ[evalHead, _TerminatedEvaluation], Return[evalHead, With], Reap[EvalLambda[arg, vars, n, evalHead[[2, 1, 1]], offset, depth]]]},
				{l = If[MatchQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n || evalHead[[1]][evalArg[[1]]] === head[arg],
					Sow[l]; evalHead[[1]][evalArg[[1]]]
					,
					EvalLambda[evalHead[[1]][evalArg[[1]]], n, l]
				]
			]
			,
			_ :> With[{subst = LambdaSubstitute[expr, vars, offset, depth]}, Sow[k]; subst]
		}
	]
]


EtaReduce[expr_] := expr //. \[FormalLambda][(f : Except[_Integer])[1]] :> f
EtaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, \[FormalLambda][Except[_Integer][1]]]}, If[MissingQ[pos], expr, EtaReduce[ReplaceAt[expr, \[FormalLambda][f_[1]] :> f, pos], n - 1]]]
]


LambdaFreeVariables[expr_, pos_List : {}, depth_Integer : 0] := Replace[expr, {
	\[FormalLambda][body_][arg_] :> Join[LambdaFreeVariables[body, Join[pos, {0, 1}], depth + 1], LambdaFreeVariables[arg, Append[pos, 1], depth]],
	\[FormalLambda][body_] :> LambdaFreeVariables[body, Append[pos, 1], depth + 1],
	f_[x_] :> Join[LambdaFreeVariables[f, Append[pos, 0], depth], LambdaFreeVariables[x, Append[pos, 1], depth]],
	var_Integer :> If[var > depth, {{depth, pos, var}}, {}],
	_ :> {}
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

SetAttributes[AlphabetString, Listable]
AlphabetString[0] = ""
AlphabetString[n_Integer ? NonNegative] := Block[{q, r},
	{q, r} = QuotientRemainder[n, 26];
	If[r == 0, (q -= 1; r = 26)];
	AlphabetString[q] <> FromLetterNumber[r]
]

TagLambda[expr_, "Alphabet"] := Block[{lambda = TagLambda[expr], vars},
	vars = Cases[lambda, Interpretation["\[Lambda]", tag_] :> tag, All, Heads -> True];
	lambda /. MapThread[With[{sym = Unevaluated @@ #2}, #1 :> sym] &, {vars, MakeExpression /@ AlphabetString[Range[Length[vars]]]}]
]
ResourceFunction["AddCodeCompletion"]["TagLambda"][None, {"Alphabet"}]


LambdaFunction[expr_, head_ : Identity] := head[Evaluate @ TagLambda[expr]] //. {Interpretation["\[Lambda]", x_][body_] :> Function[x, body], Interpretation[_Integer, x_] :> x}


FunctionLambda[expr_, vars_Association : <||>] := Replace[Unevaluated[expr], {
	Verbatim[Function][var_, body_][x_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]][FunctionLambda[x, vars]],
	Verbatim[Function][var_, body_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]],
	f_[x_] :> FunctionLambda[Unevaluated[f], vars][FunctionLambda[Unevaluated[x], vars]],
	var_Symbol :> Lookup[vars, var]
}]


LambdaTree[lambda_] := ExpressionTree[
	TagLambda[lambda, "Alphabet"] //. (f : Except[Interpretation["\[Lambda]", _]])[x_] :> Application[f, x] //. Interpretation[_, tag_] :> ToString[Unevaluated[tag]],
	"Heads", Heads -> False, TreeElementLabel -> TreeCases[Application] -> "@"
]


LambdaConvert[expr_, form_ : "Application"] := Switch[form,
	"Application",
	expr //. (f : Except[\[FormalLambda]])[x_] :> Application[f, x],
	"Composition" | "SmallCircle",
	expr //. (f : Except[\[FormalLambda]])[x_] :> {f, x} //. {\[FormalLambda][body_List] :> Row[{"(", Splice[Riffle[Flatten[body], "\[SmallCircle]"]], ")"}], \[FormalLambda][x_] :> Row[{"(", x, ")"}]},
	"Parentheses",
	expr //. (f : Except[\[FormalLambda]])[x_] :> {f, x} //. {\[FormalLambda][body_List] :> Row[{"(", Splice[Flatten[body]], ")"}], \[FormalLambda][x_] :> Row[{"(", x, ")"}]},
	"Function",
	LambdaFunction[expr],
	"Tree",
	LambdaTree[expr],
	_,
	Missing[form]
]
ResourceFunction["AddCodeCompletion"]["LambdaConvert"][None, {"Application", "Composition", "SmallCircle", "Parentheses", "Function", "Tree"}]


ColorizeTaggedLambda[lambda_] := With[{lambdas = Union @ Cases[lambda, Interpretation["\[Lambda]", x_], All, Heads -> True]},
	lambda /. MapThread[x : #1 | Interpretation[_Integer, Evaluate @ #1[[2]]] :> Style[x, Bold, #2] &, {lambdas, ColorData[109] /@ Range[Length[lambdas]]}]
]


ColorizeLambda[expr_] := expr /. lambda_\[FormalLambda] :> ColorizeTaggedLambda[TagLambda[lambda]]


LambdaRow[Interpretation["\[Lambda]", tag_][body_], depth_ : 0] := {{\[FormalLambda][tag] -> depth, Splice[LambdaRow[body, depth + 1]]}}
LambdaRow[Interpretation[i_Integer, tag_], depth_ : 0] := {i -> tag}
LambdaRow[f_[x_], depth_ : 0] := Join[LambdaRow[f, depth], LambdaRow[x, depth]]
LambdaRow[x_, depth_ : 0] := {x}

Options[LambdaSmiles] = Join[{"Height" -> 3}, Options[Style], Options[Graphics]];
LambdaSmiles[lambda_, opts : OptionsPattern[]] := Block[{row = LambdaRow[TagLambda[lambda]], lambdaPos, varPos, lambdas, vars, colors, arrows, height = OptionValue["Height"], styleOpts = FilterRules[{opts}, Options[Style]]},
	row = row //. body : {_\[FormalLambda] -> _, __} :> Splice[{"(", Splice[body], ")"}];
	lambdaPos = Position[row, _\[FormalLambda] -> _, {1}, Heads -> False];
	varPos = Position[row, _Integer -> _, {1}, Heads -> False];
	lambdas = AssociationThread[#[[All, 1, 1]], Thread[First /@ lambdaPos -> #[[All, 2]]]] & @ Extract[row, lambdaPos];
	vars = Extract[row, varPos];
	colors = Association @ MapIndexed[#1[[1, 1]] -> ColorData[109][#2[[1]]] &, Extract[row, lambdaPos]];
	row = MapAt[Style["\[Lambda]", Lookup[colors, #[[1, 1]], Black]] &, lambdaPos] @ MapAt[Style[#[[1]], Lookup[colors, #[[2]], Black]] &, varPos] @ row;
	
	arrows = MapThread[With[{dh = Ceiling[#1[[1]] / 2], sign = (-1) ^ Boole[EvenQ[#1[[1]]]], l = lambdas[#1[[2]]]},
		If[MissingQ[l], Nothing, {colors[#1[[2]]], Line[Threaded[{1, sign}] * {{#2, 1}, {#2, 1 + dh / (l[[2]] + 1)}, {l[[1]], 1 + dh / (l[[2]] + 1)}, {l[[1]], 1}}]}]] &,
		{vars, First /@ varPos}
	];
	Graphics[{
		MapIndexed[Inset[Style[#1, styleOpts, FontSize -> 16], {#2[[1]], 0}] &, row],
		arrows
	},
		FilterRules[{opts}, Options[Graphics]],
		AspectRatio -> height / Length[row]
	]
]

(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
