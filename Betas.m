Begin["Betas`"]

(*#####################################*)
(*----------Utility functions----------*)
(*#####################################*)
(*Symmetrizing in indices*)
Sym[i1_, i2_][expr_] := expr /2 + ReplaceAll[expr, {i1 -> i2, i2 -> i1}] /2 ;
AntiSym[i1_, i2_][expr_] := expr /2 - ReplaceAll[expr, {i1 -> i2, i2 -> i1}] /2 ;
Sym[a_, b_, c_, d_][expr_] := 
	Block[{perm},
		perm = {a -> #[[1]], b -> #[[2]], c -> #[[3]], d -> #[[4]]} & /@ Permutations[{a, b, c, d}];
		Mean[expr/.perm]	
	];
Sym4[a_, b_, c_, d_][expr_] := 
	Block[{perm},
		perm = {a -> #, # -> a} & /@ {a, b, c, d};
		Mean[expr/.perm]	
	];	
Sym[a_, b_, c_][expr_] := 
	Block[{perm},
		perm = {a -> #[[1]], b -> #[[2]], c -> #[[3]]} & /@ Permutations[{a, b, c}];
		Mean[expr/.perm]	
	];
	

(*Functions that speed up evaluation by applying expand succesively to each couple of terms in the evaluation.*)
Ttimes[a_, b_, c___] := Ttimes[Expand[a b], c];
Ttimes[a_] = a;
Tdot[a_, b_, c___] := Tdot[Expand[a.b], c];
Tdot[a_] = a;


(*##################################*)
(*----------Beta functions----------*)
(*##################################*)

(*Function returns the beta function of the given coupling and loop order*)
BetaTerm::gaugeLoops = "The gauge beta function is only implemented to 3 loops."
BetaTerm::yukawaLoops = "The Yukawa beta function is only implemented to 2 loops."
BetaTerm::quarticLoops = "The quartic beta function is only implemented to 2 loops."
BetaTerm::loopNumber = "The `1` beta function is only implemented up to `2` loops."
BetaTerm::unkown = "The coupling `1` has not been defined."
BetaTerm[coupling_, loop_Integer] :=
	Module[{beta, group, tensor, C1, C2},
		(*Determines the correct tensor structure based on coupling type*)
		Switch[$couplings @ coupling
		,x_ /; MemberQ[Keys @ $gaugeGroups, x],
			If[loop > 3, 
				Message[BetaTerm::loopNumber, "gauge", 3];
				Return[Null];
			];
			group = $couplings @ coupling;
			beta = Ttimes[G2Matrix[C1, $A] ,GaugeTensors[loop], G2Matrix[$B, C2], $gaugeGroups[group, Projector][C1, C2] ];
			
			(*Puts U1-mixing matrix on matrix form*)
			If[MatchQ[$gaugeGroups[group, LieGroup], U1[n_] /; n >1],
				beta = beta /. Matrix[l1_List][group[adj] @ v1] Matrix[l2_List][group[adj] @ v2] :> Outer[Times, l1, l2];
			];
		,Yukawa,
			If[loop > 2, 
				Message[BetaTerm::loopNumber, "Yukawa", 2];
				Return[Null];
			];
			
			Switch[$yukawas[coupling, Chirality]
			,Left,
				tensor = YukawaTensors[loop][[1, 1]];
			,Right,
				tensor = YukawaTensors[loop][[2, 2]];
			];
			
			beta = tensor $yukawas[coupling, Projector][$a, $i, $j] // Expand // Expand;
		,Quartic,
			If[loop > 2, 
				Message[BetaTerm::loopNumber, "quartic", 2];
				Return[Null];
			];
			
			beta = QuarticTensors[loop] $quartics[coupling, Projector][$a, $b, $c, $d] // Expand // Expand;
		,FermionMass,
			If[loop > 2, 
				Message[BetaTerm::loopNumber, "fermion mass", 2];
				Return[Null];
			];
			
			Switch[$fermionMasses[coupling, Chirality]
			,Left,
				tensor = YukawaTensors[loop][[1, 1]];
			,Right,
				tensor = YukawaTensors[loop][[2, 2]];
			];
			
			beta = tensor $fermionMasses[coupling, Projector][$a, $i, $j] // Expand // Expand;
		,Trilinear,
			If[loop > 2, 
				Message[BetaTerm::loopNumber, "trilinear scalar", 2];
				Return[Null];
			];
			
			beta = QuarticTensors[loop] $trilinears[coupling, Projector][$a, $b, $c, $d] // Expand // Expand;
		,ScalarMass,
			If[loop > 2, 
				Message[BetaTerm::loopNumber, "scalar mass", 2];
				Return[Null];
			];
			
			beta = QuarticTensors[loop] $scalarMasses[coupling, Projector][$a, $b, $c, $d] // Expand // Expand;
		,_Missing,
			Message[BetaTerm::unkown, coupling];
			Return[Null];
		];
		
		Return @ beta;
	];

(*Function that produces the beta function for the requested coupling*)
BetaFunction::unkown = "The coupling `1` has not been defined."
BetaFunction[coupling_Symbol, loop_Integer, OptionsPattern[{RescaledCouplings -> False, FourDimensions -> True}] ] :=
	Block[{coef = 4 Pi, firstTerm = 0, l},
		If[Head @ $couplings @ coupling === Missing, 
			Message[BetaFunction::unkown, coupling];
			Return @ Null;
		];
		
		If[OptionValue @ RescaledCouplings, coef = 1; ];
		If[OptionValue @ FourDimensions, firstTerm = 1; ];
		
		Sum[ Power[coef, -2 l] BetaTerm[coupling, l], {l, firstTerm, loop}]
	];

(*Fuction for diagonalizing the quartic beta functions. It inherits the options from BetaFunction*)
QuarticBetaFunctions[loop_Integer, opt:OptionsPattern[]] :=
	Block[{betaFunctions, couplings, qProjections, invMatrix},
		couplings = Keys @ $quartics;
		Print["The quartic couplings are ", couplings];
		
		(*Finds inversion matrix for the quartic projectors*)
		qProjections = CheckProjection /@ couplings;
		invMatrix = Inverse @ Transpose @ Table[Simplify @ D[qProjections, c], {c, couplings}];
		
		(*Extracts beta functions*)
		betaFunctions = Monitor[
							Table[BetaFunction[c, loop, opt], {c, couplings}]
						,StringForm["Evaluating the `` \[Beta]-function", c] ];
		
		Return[invMatrix . betaFunctions];
	];


(*Function for finalizing a betafunction, bringing it from a nice compact output to a form more suitable for 
further Mathematica manipulations. Can also be used to specify particular cases for coupling matrices.*)
Finalize[expr_, OptionsPattern[{Parametrizations -> {}}] ] :=
	Internal`InheritedBlock[{out, Bar, Trans, Matrix},
		out = expr /. OptionValue @ Parametrizations;
			Bar[a_List] := Bar /@ a;
			Bar[Times[a__]] := Bar /@ Times[a];
			Bar[Plus[a__]] := Bar /@ Plus[a];
			Bar[a_Symbol] := Conjugate @ a;
			Bar[a_] /; NumberQ[a] := Conjugate @ a;
			Trans[a_List] /; MatrixQ[a] === True := Transpose @ a;
		Matrix[y__][a_[f1_], b_[f2_]] /; !OrderedQ[{f1, f2}] :=
			Matrix[Sequence @@ Reverse[Trans /@ List@ y]][b[f2], a[f1]];
		Matrix[y__][a_[f1], b_[f2]] := Dot[y];
		(*Matrix /: Matrix[u_List][_[v1]] Matrix[w_List][_[v2]] := List /@ u . List @ w;*)
		out
	];

(*Function to check the projected value of a coupling*)
CheckProjection::unkown = "The coupling `1` has not been defined."
CheckProjection[coupling_Symbol] :=
	Module[{cop, tensor, A, B, a, i, j, b, c, d},
		Switch[$couplings @ coupling
		,x_ /; MemberQ[Keys @ $gaugeGroups, x],
			cop = Ttimes[G2Matrix[A, B], $gaugeGroups[$couplings @ coupling, Projector][B, A] ] // Expand;
		,Yukawa,			
			Switch[$yukawas[coupling, Chirality]
			,Left,
				tensor = Yuk[a, i, j][[1, 1]];
			,Right,
				tensor = Yuk[a, i, j][[2, 2]];
			];
			cop = tensor $yukawas[coupling, Projector][a, i, j] // Expand // Expand;
		,Quartic,
			cop = Lam[a, b, c, d] $quartics[coupling, Projector][a, b, c, d] // Expand // Expand;
		,FermionMass,
			Switch[$fermionMasses[coupling, Chirality]
			,Left,
				tensor = Yuk[a, i, j][[1, 1]];
			,Right,
				tensor = Yuk[a, i, j][[2, 2]];
			];
			cop = tensor $fermionMasses[coupling, Projector][a, i, j] // Expand // Expand;
		,Trilinear,
			cop = Lam[a, b, c, d] $trilinears[coupling, Projector][a, b, c, d] // Expand // Expand;
		,ScalarMass,
			cop = Lam[a, b, c, d] $scalarMasses[coupling, Projector][a, b, c, d] // Expand // Expand;
		,_Missing,
			Message[CheckProjection::unkown, coupling];
			Return @ Null;
		];
		Return @ cop;
	];


End[]