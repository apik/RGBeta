(*
	Author: Anders Eller Thomsen
	Released under the MIT license (see 'LICENSE').
*)
Package["RGBeta`"]

(*##################################*)
(*----------Package Export----------*)
(*##################################*)

PackageExport["Acoef"]
PackageExport["Bcoef"]

PackageScope["$fermionAnomalousCoefficients"]
PackageScope["$gaugeCoefficients"]
PackageScope["$quarticCoefficients"]
PackageScope["$scalarAnomalousCoefficients"]
PackageScope["$yukawaCoefficients"]

PackageScope["FermionAnomalousTensors"]
PackageScope["FermionMassTensors"]
PackageScope["GaugeTensors"]
PackageScope["QuarticTensors"]
PackageScope["ScalarAnomalousTensors"]
PackageScope["ScalarMassiveTensors"]
PackageScope["YukawaTensors"]

(*#####################################*)
(*----------Usage Definitions----------*)
(*#####################################*)

Acoef::usage =
	"Acoef[i, j, k] is used internally to denote the coefficients of the differnet tensor contraction appering in the anomalous dimensions."
Bcoef::usage =
	"Bcoef[i, j, k] is used internally to denote the coefficients of the differnet tensor contraction appering in the beta functions."


$fermionAnomalousCoefficients::usage =
	"$fermionAnomalousCoefficients is an internal replacement lsit containing the coefficients of all the tensors structures in the fermion anomalous dimension."
$gaugeCoefficients::usage =
	"$gaugeCoefficients is an internal replacement list containing the coefficient of all tensor constractions used in the quartic beta function."
$quarticCoefficients::usage =
	"$quarticCoefficients is an internal replacement list containing the coefficient of all tensor constractions used in the quartic beta function."
$scalarAnomalousCoefficients::usage =
	"$scalarAnomalousCoefficients is an internal replacement lsit containing the coefficients of all the tensors structures in the fermion anomalous dimension."
$yukawaCoefficients::usage =
	"$yukawaCoefficients is an internal replacement list containing the coefficient of all tensor constractions used in the yukawa beta function."

FermionAnomalousTensors::uasge =
	"FermionAnomalousTensors[field, loop] evaluates all tensor contractions of the general anomalous dimension tensor and the field projector."
FermionMassTensors::usage =
	"FermionMassTensors[coupling, loop] is a function that computes all the tensor contractions used the general fermion mass beta function at the given loop order."
GaugeTensors::usage =
	"GaugeTensors[coupling, loop] is a function that computes all the tensor contractions used the general gauge beta function at the given loop order."
QuarticTensors::usage =
	"QuarticTensors[coupling, loop] is a function that computes all the tensor contractions used the general quartic beta function at the given loop order."
ScalarAnomalousTensors::uasge =
	"ScalarAnomalousTensors[field, loop] evaluates all tensor contractions of the general anomalous dimension tensor and the field projector."
ScalarMassiveTensors::usage =
	"ScalarMassiveTensors[coupling, loop] is a function that computes all the tensor contractions used in the the trillinear and scalar mass beta functions at the given loop order."
YukawaTensors::usage =
	"YukawaTensors[coupling, loop] is a function that computes all the tensor contractions used the general yukawa beta function at the given loop order."

(*########################################*)
(*----------All kinds of tensors----------*)
(*########################################*)

<< BetaTensors`; (*Loads all the tensors from ancillary file*)

sig1 = {{0, 1}, {1, 0}};
sig3 = {{1, 0}, {0, -1}};
sig3Til = {{-1, 0}, {0, 1}};

(*Gauge coupling multiplied on generators*)
TfG2[A_, i_, j_] := Module[{B}, Tferm[B, i, j] G2Matrix[A, B] // Expand]
TfG2t[A_, i_, j_] := Module[{B}, TfermTil[B, i, j] G2Matrix[A, B] // Expand]
TsG2[A_, a_, b_] := Module[{B}, Tscal[B, a, b] G2Matrix[A, B] // Expand]

(*######################################*)
(*----------2-point structures----------*)
(*######################################*)
(*1-loop*)
C2G[A_, B_] := Module[{C1, C2, D1, D2},
		Ttimes[FGauge[A, C1, D1], G2Matrix[C1, C2], G2Matrix[D1, D2], FGauge[B, C2, D2]]
	];
S2F[A_, B_] := Module[{i, j},
		Tr[Tferm[A, i, j].Tferm[B, j, i]] // Expand
	];
S2S[A_, B_] := Module[{i, j},
		Tscal[A, i, j] Tscal[B, j, i] // Expand
	];
C2F[i_, j_] := Module[{A, k},
		TfG2[A, i, k].Tferm[A, k, j] // Expand
	];
C2Ft[i_, j_] :=	Module[{A, k},
		TfG2t[A, i, k].TfermTil[A, k, j] // Expand
	];
C2S[a_, b_] := Module[{A, c},
	TsG2[A, a, c] Tscal[A, c, b] // Expand
	];
Y2S[a_, b_] := Module[{i, j},
		Tr[Yuk[a, i, j].YukTil[b, j, i]] // Expand
	];
Y2F[i_, j_] := Module[{a, k},
		Yuk[a, i, k].YukTil[a, k, j] // Expand
	];
Y2Ft[i_, j_] := Module[{a, k},
		YukTil[a, i, k].Yuk[a, k, j] // Expand
	];

(*----------2-loop----------*)
(*g^4*)
S2SC2S[A_, B_] := Module[{a, b, c},
		Ttimes[Tscal[B, c, a], Tscal[A, a, b], C2S[b, c]]
	];
S2FC2F[A_, B_] := Module[{i, j, k},
		Tr[Tdot[Tferm[B, k, i], Tferm[A, i, j], C2F[j, k]]]
	];
C2FC2G[i_, j_] := Module[{A, B, k},
		Tdot[TfG2[A, i, k], TfG2[B, k, j]] C2G[A, B] // Expand
	];
C2FS2F[i_, j_] := Module[{A, B, k},
		Tdot[TfG2[A, i, k], TfG2[B, k, j]] S2F[A, B] // Expand
	];
C2FS2S[i_, j_] := Module[{A, B,k},
		Tdot[TfG2[A, i, k], TfG2[B, k, j]] S2S[A, B] // Expand
	];
C2FC2Gt[i_, j_] := sig1.C2FC2G[i, j].sig1;
C2FS2Ft[i_, j_] := sig1.C2FS2F[i, j].sig1;
C2FS2St[i_, j_] := sig1.C2FS2S[i, j].sig1;
C2SC2G[a_, b_] := Module[{A, B, c},
		Ttimes[TsG2[A, a, c], TsG2[B, c, b], C2G[A, B]]
	];
C2SS2F[a_, b_] := Module[{A, B, c},
		Ttimes[TsG2[A, a, c], TsG2[B, c, b], S2F[A, B]]
	];
C2SS2S[a_, b_] := Module[{A, B, c},
		Ttimes[TsG2[A, a, c], TsG2[B, c, b], S2S[A, B]]
	];

(*g^2 y^2*)
Y2SC2F[a_, b_] := Module[{i, j, k},
		Tr @ Tdot[Yuk[a, i, j], C2F[j, k], YukTil[b, k, i]]
	];
Y2FC2F[i_, j_] := Module[{a, k, l},
		Tdot[Yuk[a, i, k], C2F[k, l], YukTil[a, l, j]]
	];
Y2FC2S[i_, j_] := Module[{a, b, k},
		Tdot[Yuk[a, i, k], YukTil[b, k, j]] C2S[a, b] // Expand
	];
Y2FC2Ft[i_, j_] := sig1.Y2FC2F[i, j].sig1;
Y2FC2St[i_, j_] := sig1.Y2FC2S[i, j].sig1;
S2SY2S[A_, B_] := Module[{a, b, c},
		Ttimes[Tscal[B, c, a], Tscal[A, a, b], Y2S[b, c]]
	];
S2FY2F[A_, B_] := Module[{i, j, k},
		Tr @ Tdot[TfermTil[B, k, i], TfermTil[A, i, j], Y2F[j, k]]
	];

(*y^4*)
Y2SY2F[a_, b_] := Module[{k1, k2, k3},
		Tr @ Tdot[Yuk[a, k1, k2], YukTil[b, k2, k3], Y2F[k3, k1]]
	];
Y4cS[a_, b_] := Module[{c, k1, k2, k3, k4},
		Tr @ Tdot[Yuk[a, k1, k2], YukTil[c, k2, k3], Yuk[b, k3, k4], YukTil[c, k4, k1]]
	];
Y4cF[i_, j_] := Module[{a, b, k1, k2, k3},
		Ttimes[Yuk[a, i, k1], YukTil[b, k1, k2], Yuk[a, k2, k3], YukTil[b, k3, j]]
	];
Y2FY2F[i_, j_] := Module[{a, k1, k2},
		Tdot[Yuk[a, i, k1], Y2Ft[k1, k2], YukTil[a, k2, j]]
	];
Y2FY2S[i_, j_] := Module[{a, b, k1},
		Tdot[Yuk[a, i, k1], YukTil[b, k1, j]] Y2S[a, b] // Expand
	];
Y4cFt[i_, j_] := sig1.Y4cF[i, j].sig1;
Y2FY2Ft[i_, j_] := sig1.Y2FY2F[i, j].sig1;
Y2FY2St[i_, j_] := sig1.Y2FY2S[i, j].sig1;

(*lambda^2*)
Lam2[a_, b_] := Module[{c, d, e},
		Lam[a, c, d, e] Lam[c, d, e, b] // Expand
	];

(*1-loop vertices*)
FourGLam[a_, b_, c_, d_] := Module[{A1, A2, b1, b2},
	Ttimes[TsG2[A1, a, b1], TsG2[A2, b1, b], Tscal[A1, c, b2], Tscal[A2, b2, d]]
];

(* Extra identities required to handle the more complicated combinations of struture constants appearing in the 4-loop gauge beta functions. *)
NewIdentities[expr_] := Block[{fStruct, tGen, n},
	fStruct /: fStruct[gr_, x : OrderlessPatternSequence[A_, B_, C_]] tGen[gr_[rep_], B_, a_, b_] tGen[gr_[rep_], C_, b_, c_] :=
    	I/2 Signature[List@x] Signature[{A, B, C}] Casimir2[gr@adj] tGen[gr@rep, A, a, c];
	fStruct /: fStruct[gr_, OrderlessPatternSequence[A_, C_, E_]] fStruct[gr_, OrderlessPatternSequence[B_, D_, E_]] *
		tGen[gr_@rep_, A_, a_,b_] tGen[gr_@rep_, B_, b_, c_] tGen[gr_@rep_, C_, c_, d_] tGen[gr_@rep_, D_, d_, a_] := 0;
	fStruct /: fStruct[gr_, x1 : OrderlessPatternSequence[E_, A_, F_]] fStruct[gr_, x2 : OrderlessPatternSequence[F_, B_, G_]] *
		fStruct[gr_, x3 : OrderlessPatternSequence[G_, C_, H_]] fStruct[gr_, x4 : OrderlessPatternSequence[H_, D_, E_]] fStruct[gr_, y1 : OrderlessPatternSequence[I_, A_, J_]] *
		fStruct[gr_, y2 : OrderlessPatternSequence[J_, B_, K_]] fStruct[gr_, y3 : OrderlessPatternSequence[K_, C_, L_]] fStruct[gr_, y4 : OrderlessPatternSequence[L_, D_, I_]] /;
		Head@$gaugeGroups[gr, LieGroup] == SU :=
		(n = $gaugeGroups[gr, LieGroup][[1]]; Signature[List@x1] Signature[List@x2] Signature[List@x3] Signature[List@x4] Signature[List@y1]  *
			Signature[List@y2] Signature[List@y3] Signature[List@y4] Signature[{E, A, F}] Signature[{F, B, G}] Signature[{G, C, H}] Signature[{H, D, E}] *
			Signature[{I, A, J}] Signature[{J, B, K}] Signature[{K, C, L}] Signature[{L, D, I}] n^2 (n^2 - 1) (n^2 + 12)/8);
	expr
];

(*##################################*)
(*------------RG tensors------------*)
(*##################################*)
(* These functions project out specific coupling beta functions from the general tensors.*)

GaugeTensors[coupling_Symbol, loop_Integer] :=
	Module[{diagrams = {3, 7, 33, 202}[[loop]], n, C1, C2, proj, bTerm},
		(* The 0-loop contribution in d = 4 - \epsilon dimensions *)
		If[loop === 0,
			bTerm = Expand[ - Global`\[Epsilon] $gaugeGroups[$couplings @ coupling, Projector][C1, C2] G2Matrix[C1, C2] ];
			If[ MatchQ[ $gaugeGroups[$couplings @ coupling, LieGroup], U1[m_] /; m > 1],
				bTerm = bTerm /. coupling -> $gaugeGroups[$couplings @ coupling, CouplingMatrix];
			];
			Return @ {bTerm};
		];

		proj = Ttimes[G2Matrix[$A, C1], $gaugeGroups[$couplings @ coupling, Projector][C1, C2], G2Matrix[C2, $B]];
		Monitor[
			bTerm = Table[
				Bcoef[1, loop, n] RefineGroupStructures @ Ttimes[proj, BetaTensor[1, loop, n] ],
			{n, diagrams}];
		,StringForm["Evaluating term `` / ``", n, diagrams]];

		(* At 4-loops additional identities are required.*)
		If[(loop > 3) && FreeQ[$gaugeGroups, Arb],
       (* SU(n) @ 4-loop *)
			NewIdentities /@ bTerm
		 ,
       If[(loop > 3) && Not[FreeQ[$gaugeGroups, Arb]],
          (* Color @ 4-loop *)
          Color /@ bTerm
        ,
          (* Do nothing *)
			    bTerm
       ]
		]
	];

YukawaTensors[coupling_Symbol, loop_Integer] :=
	Module[{diagrams = {1, 5, 33, 308}[[loop + 1]], n, bTerm},
		Monitor[
			bTerm = Table[
				Bcoef[2, loop, n] RefineGroupStructures @ Tr@ Tdot[$yukawas[coupling, Projector][$a, $i, $j], BetaTensor[2, loop, n] ],
			{n, diagrams}]
		 ,StringForm["Evaluating term `` / ``", n, diagrams]];

    If[(loop > 2) && Not[FreeQ[$gaugeGroups, Arb]],
       (* Color @ 3-loop *)
       Color /@ bTerm
     ,
       (* Do nothing *)
			 bTerm
    ]
	];

FermionMassTensors[coupling_Symbol, loop_Integer] :=
	Module[{diagrams = {1, 5, 33}[[loop + 1]], n},
		Monitor[
			Table[
				Bcoef[2, loop, n] RefineGroupStructures @ Tr@ Tdot[$fermionMasses[coupling, Projector][$a, $i, $j], BetaTensor[4, loop, n] ],
			{n, diagrams}]
		,StringForm["Evaluating term `` / ``", n, diagrams] ]
	];

QuarticTensors[coupling_Symbol, loop_Integer] :=
	Module[{diagrams = {1, 5, 33}[[loop + 1]], n},
		Monitor[
			Table[
				Bcoef[3, loop, n] RefineGroupStructures @ Ttimes[$quartics[coupling, Projector][$a, $b, $c, $d],
				BetaTensor[3, loop, n] ],
			{n, diagrams}]
		,StringForm["Evaluating term `` / ``", n, diagrams]]
	];

ScalarMassiveTensors[coupling_Symbol, loop_Integer] :=
	Module[{diagrams = {1, 5, 33}[[loop + 1]], n},
		Monitor[
			Switch[$couplings @ coupling
			,Trilinear,
				Table[
					Bcoef[3, loop, n] RefineGroupStructures @ Ttimes[$trilinears[coupling, Projector][$a, $b, $c, $d],
					BetaTensor[5, loop, n] ],
				{n, diagrams}]
			,ScalarMass,
				Table[
					Bcoef[3, loop, n] RefineGroupStructures @ Ttimes[$scalarMasses[coupling, Projector][$a, $b, $c, $d],
					BetaTensor[5, loop, n] ],
				{n, diagrams}]
			]
		,StringForm["Evaluating term `` / ``", n, diagrams]]
	];

FermionAnomalousTensors[field_, loop_Integer] :=
	Module[{diagrams = {2, 9}[[loop]], n},
		Monitor[
			Table[
				Acoef[1, loop, n] RefineGroupStructures @ Tr@ Tdot[$fermions[field, Projector][$i, $j], AnomalousTensor[1, loop, n] = AnomalousTensor[1, loop, n] ],
			{n, diagrams}]
		,StringForm["Evaluating term `` / ``", n, diagrams]]
	];

ScalarAnomalousTensors[field_, loop_Integer] :=
	Module[{diagrams = {2, 8}[[loop]], n},
		Monitor[
			Table[
				Acoef[2, loop, n] RefineGroupStructures @ Ttimes[$scalars[field, Projector][$a, $b], AnomalousTensor[2, loop, n] = AnomalousTensor[2, loop, n] ],
			{n, diagrams}]
		,StringForm["Evaluating term `` / ``", n, diagrams]]
	];



(*#####################################*)
(*----------Beta Coefficients----------*)
(*#####################################*)
$quarticCoefficients = {
	Bcoef[3, 0, 1] -> 1,
	(* 1-loop *)
	Bcoef[3, 1, 1] -> 36,
	Bcoef[3, 1, 2] -> -12,
	Bcoef[3, 1, 3] -> 3,
	Bcoef[3, 1, 4] -> 2,
	Bcoef[3, 1, 5] -> -12,
	(*2-loop*)
	Bcoef[3, 2, 1] -> 324,
	Bcoef[3, 2, 2] -> -684,
	Bcoef[3, 2, 3] -> 646,
	Bcoef[3, 2, 4] -> -28,
	Bcoef[3, 2, 5] -> -32,
	Bcoef[3, 2, 6] -> 12,
	Bcoef[3, 2, 7] -> 60,
	Bcoef[3, 2, 8] -> 0,
	Bcoef[3, 2, 9] -> 6,
	Bcoef[3, 2, 10] -> -143/3,
	Bcoef[3, 2, 11] -> 11/3,
	Bcoef[3, 2, 12] -> 10/3,
	Bcoef[3, 2, 13] -> -18,
	Bcoef[3, 2, 14] -> 24,
	Bcoef[3, 2, 15] -> -18,
	Bcoef[3, 2, 16] -> 1/3,
	Bcoef[3, 2, 17] -> -6,
	Bcoef[3, 2, 18] -> 0,
	Bcoef[3, 2, 19] -> -144,
	Bcoef[3, 2, 20] -> 60,
	Bcoef[3, 2, 21] -> 10,
	Bcoef[3, 2, 22] -> 0,
	Bcoef[3, 2, 23] -> -3,
	Bcoef[3, 2, 24] -> 0,
	Bcoef[3, 2, 25] -> 24,
	Bcoef[3, 2, 26] -> -48,
	Bcoef[3, 2, 27] -> 12,
	Bcoef[3, 2, 28] -> 0,
	Bcoef[3, 2, 29] -> -2,
	Bcoef[3, 2, 30] -> -3,
	Bcoef[3, 2, 31] -> 48,
	Bcoef[3, 2, 32] -> 24,
	Bcoef[3, 2, 33] -> 24
};

$yukawaCoefficients = {
	Bcoef[2, 0, 1] -> 1,
	(* 1-loop *)
	Bcoef[2, 1, 1] -> 0,
	Bcoef[2, 1, 2] -> -6,
	Bcoef[2, 1, 3] -> 2,
	Bcoef[2, 1, 4] -> 1,
	Bcoef[2, 1, 5] -> 1/2,
	(* 2-loop *)
	Bcoef[2, 2, 1] -> -21/2,
	Bcoef[2, 2, 2] -> 12,
	Bcoef[2, 2, 3] -> 0,
	Bcoef[2, 2, 4] -> -3,
	Bcoef[2, 2, 5] -> 49/4,
	Bcoef[2, 2, 6] -> -1/4,
	Bcoef[2, 2, 7] -> -1/2,
	Bcoef[2, 2, 8] -> -97/3,
	Bcoef[2, 2, 9] -> 11/6,
	Bcoef[2, 2, 10] -> 5/3,
	Bcoef[2, 2, 11] -> 1/12,
	Bcoef[2, 2, 12] -> 12,
	Bcoef[2, 2, 13] -> 0,
	Bcoef[2, 2, 14] -> 6,
	Bcoef[2, 2, 15] -> -12,
	Bcoef[2, 2, 16] -> 10,
	Bcoef[2, 2, 17] -> 6,
	Bcoef[2, 2, 18] -> 5/2,
	Bcoef[2, 2, 19] -> 9,
	Bcoef[2, 2, 20] -> -1/2,
	Bcoef[2, 2, 21] -> -7/2,
	Bcoef[2, 2, 22] -> 0,
	Bcoef[2, 2, 23] -> -2,
	Bcoef[2, 2, 24] -> 2,
	Bcoef[2, 2, 25] -> 0,
	Bcoef[2, 2, 26] -> -2,
	Bcoef[2, 2, 27] -> 0,
	Bcoef[2, 2, 28] -> -1/2,
	Bcoef[2, 2, 29] -> -2,
	Bcoef[2, 2, 30] -> -1/4,
	Bcoef[2, 2, 31] -> -3/4,
	Bcoef[2, 2, 32] -> -1,
	Bcoef[2, 2, 33] -> -3/4,
	(*3-loop*)
  Bcoef[2, 3, 1] -> -72,
  Bcoef[2, 3, 2] -> -3,
  Bcoef[2, 3, 3] -> 33 - 12*Zeta[3],
  Bcoef[2, 3, 4] -> -3/2,
  Bcoef[2, 3, 5] -> 45/2 - 24*Zeta[3],
  Bcoef[2, 3, 6] -> 93/2,
  Bcoef[2, 3, 7] -> -78,
  Bcoef[2, 3, 8] -> -12,
  Bcoef[2, 3, 9] -> 102,
  Bcoef[2, 3, 10] -> -48,
  Bcoef[2, 3, 11] -> -9,
  Bcoef[2, 3, 12] -> -297/2,
  Bcoef[2, 3, 13] -> 53/8,
  Bcoef[2, 3, 14] -> 25/4,
  Bcoef[2, 3, 15] -> 62,
  Bcoef[2, 3, 16] -> -3,
  Bcoef[2, 3, 17] -> 48,
  Bcoef[2, 3, 18] -> -4,
  Bcoef[2, 3, 19] -> -2,
  Bcoef[2, 3, 20] -> 102,
  Bcoef[2, 3, 21] -> -3,
  Bcoef[2, 3, 22] -> -219/2,
  Bcoef[2, 3, 23] -> 17/4,
  Bcoef[2, 3, 24] -> -4,
  Bcoef[2, 3, 25] -> -6,
  Bcoef[2, 3, 26] -> 13/2,
  Bcoef[2, 3, 27] -> 11/144,
  Bcoef[2, 3, 28] -> -1165/144,
  Bcoef[2, 3, 29] -> 9721/72,
  Bcoef[2, 3, 30] -> 2/9,
  Bcoef[2, 3, 31] -> -925/72,
  Bcoef[2, 3, 32] -> 5/216,
  Bcoef[2, 3, 33] -> 181/27 + 12*Zeta[3],
  Bcoef[2, 3, 34] -> -10441/54,
  Bcoef[2, 3, 35] -> 5/36,
  Bcoef[2, 3, 36] -> 19/27,
  Bcoef[2, 3, 37] -> 278/27 + 24*Zeta[3],
  Bcoef[2, 3, 38] -> 35/54,
  Bcoef[2, 3, 39] -> -12,
  Bcoef[2, 3, 40] -> 5/4,
  Bcoef[2, 3, 41] -> -17/48,
  Bcoef[2, 3, 42] -> 19/16,
  Bcoef[2, 3, 43] -> -1/16,
  Bcoef[2, 3, 44] -> -2 - 144*Zeta[3],
  Bcoef[2, 3, 45] -> 36 - 72*Zeta[3],
  Bcoef[2, 3, 46] -> 8,
  Bcoef[2, 3, 47] -> 3/4,
  Bcoef[2, 3, 48] -> -23/4,
  Bcoef[2, 3, 49] -> 0,
  Bcoef[2, 3, 50] -> -9/4,
  Bcoef[2, 3, 51] -> 44,
  Bcoef[2, 3, 52] -> -64,
  Bcoef[2, 3, 53] -> 6,
  Bcoef[2, 3, 54] -> 22,
  Bcoef[2, 3, 55] -> 0,
  Bcoef[2, 3, 56] -> 24,
  Bcoef[2, 3, 57] -> 16,
  Bcoef[2, 3, 58] -> -4,
  Bcoef[2, 3, 59] -> 64,
  Bcoef[2, 3, 60] -> -58,
  Bcoef[2, 3, 61] -> 4,
  Bcoef[2, 3, 62] -> 10 - 12*Zeta[3],
  Bcoef[2, 3, 63] -> 65/4 - 72*Zeta[3],
  Bcoef[2, 3, 64] -> 80 - 42*Zeta[3],
  Bcoef[2, 3, 65] -> -59/2 - 36*Zeta[3],
  Bcoef[2, 3, 66] -> -15 + 72*Zeta[3],
  Bcoef[2, 3, 67] -> -149/2 + 36*Zeta[3],
  Bcoef[2, 3, 68] -> 16 + 144*Zeta[3],
  Bcoef[2, 3, 69] -> -141/2 + 36*Zeta[3],
  Bcoef[2, 3, 70] -> -47/2 + 72*Zeta[3],
  Bcoef[2, 3, 71] -> -17,
  Bcoef[2, 3, 72] -> 15 - 24*Zeta[3],
  Bcoef[2, 3, 73] -> 47/2 - 36*Zeta[3],
  Bcoef[2, 3, 74] -> 15 - 48*Zeta[3],
  Bcoef[2, 3, 75] -> 63/2 - 36*Zeta[3],
  Bcoef[2, 3, 76] -> -11/2,
  Bcoef[2, 3, 77] -> -11/8 + 9*Zeta[3],
  Bcoef[2, 3, 78] -> -27/2 + 9*Zeta[3],
  Bcoef[2, 3, 79] -> 235/8 - 15*Zeta[3],
  Bcoef[2, 3, 80] -> -53/4 + 36*Zeta[3],
  Bcoef[2, 3, 81] -> 5,
  Bcoef[2, 3, 82] -> -297/4 + 36*Zeta[3],
  Bcoef[2, 3, 83] -> -83/4 + 3*Zeta[3],
  Bcoef[2, 3, 84] -> 17 - 33*Zeta[3],
  Bcoef[2, 3, 85] -> 26 - 6*Zeta[3],
  Bcoef[2, 3, 86] -> -5,
  Bcoef[2, 3, 87] -> 139/16 - (3*Zeta[3])/2,
  Bcoef[2, 3, 88] -> 5 - 6*Zeta[3],
  Bcoef[2, 3, 89] -> 81,
  Bcoef[2, 3, 90] -> -3,
  Bcoef[2, 3, 91] -> -2,
  Bcoef[2, 3, 92] -> -19,
  Bcoef[2, 3, 93] -> 0,
  Bcoef[2, 3, 94] -> 0,
  Bcoef[2, 3, 95] -> 51/8,
  Bcoef[2, 3, 96] -> -11/8,
  Bcoef[2, 3, 97] -> -115/2 + 6*Zeta[3],
  Bcoef[2, 3, 98] -> 3,
  Bcoef[2, 3, 99] -> 99 - 36*Zeta[3],
  Bcoef[2, 3, 100] -> -5/4,
  Bcoef[2, 3, 101] -> -25/4,
  Bcoef[2, 3, 102] -> 2,
  Bcoef[2, 3, 103] -> 61/2,
  Bcoef[2, 3, 104] -> -3/2,
  Bcoef[2, 3, 105] -> -11/2,
  Bcoef[2, 3, 106] -> -1,
  Bcoef[2, 3, 107] -> 77/4 - 9*Zeta[3],
  Bcoef[2, 3, 108] -> -11/8,
  Bcoef[2, 3, 109] -> -1,
  Bcoef[2, 3, 110] -> 785/16 - 3*Zeta[3],
  Bcoef[2, 3, 111] -> -43/16,
  Bcoef[2, 3, 112] -> -9*Zeta[3],
  Bcoef[2, 3, 113] -> -3/4,
  Bcoef[2, 3, 114] -> -21/8,
  Bcoef[2, 3, 115] -> -9/4 - 9*Zeta[3],
  Bcoef[2, 3, 116] -> 1/8,
  Bcoef[2, 3, 117] -> -3/4,
  Bcoef[2, 3, 118] -> 0,
  Bcoef[2, 3, 119] -> -75/32 + (3*Zeta[3])/2,
  Bcoef[2, 3, 120] -> 3/32,
  Bcoef[2, 3, 121] -> 1/16,
  Bcoef[2, 3, 122] -> 0,
  Bcoef[2, 3, 123] -> -17/2,
  Bcoef[2, 3, 124] -> -17,
  Bcoef[2, 3, 125] -> 19/2,
  Bcoef[2, 3, 126] -> 2,
  Bcoef[2, 3, 127] -> 0,
  Bcoef[2, 3, 128] -> 3/2,
  Bcoef[2, 3, 129] -> -3/8,
  Bcoef[2, 3, 130] -> -11/48,
  Bcoef[2, 3, 131] -> 1,
  Bcoef[2, 3, 132] -> -5/32,
  Bcoef[2, 3, 133] -> -30,
  Bcoef[2, 3, 134] -> 6,
  Bcoef[2, 3, 135] -> 0,
  Bcoef[2, 3, 136] -> 10,
  Bcoef[2, 3, 137] -> 7,
  Bcoef[2, 3, 138] -> -3,
  Bcoef[2, 3, 139] -> -6,
  Bcoef[2, 3, 140] -> -26,
  Bcoef[2, 3, 141] -> -14,
  Bcoef[2, 3, 142] -> 2,
  Bcoef[2, 3, 143] -> -14,
  Bcoef[2, 3, 144] -> -12,
  Bcoef[2, 3, 145] -> -22,
  Bcoef[2, 3, 146] -> 12,
  Bcoef[2, 3, 147] -> -8,
  Bcoef[2, 3, 148] -> -6,
  Bcoef[2, 3, 149] -> -12,
  Bcoef[2, 3, 150] -> -22,
  Bcoef[2, 3, 151] -> 24,
  Bcoef[2, 3, 152] -> -22,
  Bcoef[2, 3, 153] -> 2,
  Bcoef[2, 3, 154] -> 0,
  Bcoef[2, 3, 155] -> -5,
  Bcoef[2, 3, 156] -> 3,
  Bcoef[2, 3, 157] -> -5,
  Bcoef[2, 3, 158] -> 0,
  Bcoef[2, 3, 159] -> -3/2,
  Bcoef[2, 3, 160] -> 3/2,
  Bcoef[2, 3, 161] -> 0,
  Bcoef[2, 3, 162] -> 0,
  Bcoef[2, 3, 163] -> 3,
  Bcoef[2, 3, 164] -> -11,
  Bcoef[2, 3, 165] -> 0,
  Bcoef[2, 3, 166] -> 0,
  Bcoef[2, 3, 167] -> 0,
  Bcoef[2, 3, 168] -> -10,
  Bcoef[2, 3, 169] -> 34 - 48*Zeta[3],
  Bcoef[2, 3, 170] -> -8,
  Bcoef[2, 3, 171] -> 4,
  Bcoef[2, 3, 172] -> 7/4 + DELTA - 6*Zeta[3],
  Bcoef[2, 3, 173] -> 7/4 - DELTA - 6*Zeta[3],
  Bcoef[2, 3, 174] -> 2,
  Bcoef[2, 3, 175] -> 36,
  Bcoef[2, 3, 176] -> -5,
  Bcoef[2, 3, 177] -> 11/2,
  Bcoef[2, 3, 178] -> -11 + 24*Zeta[3],
  Bcoef[2, 3, 179] -> -17 + 24*Zeta[3],
  Bcoef[2, 3, 180] -> -24*Zeta[3],
  Bcoef[2, 3, 181] -> 12 - 12*Zeta[3],
  Bcoef[2, 3, 182] -> -24 + 24*Zeta[3],
  Bcoef[2, 3, 183] -> 13 - 12*Zeta[3],
  Bcoef[2, 3, 184] -> 35/8 - 3*Zeta[3],
  Bcoef[2, 3, 185] -> -3 + 9*Zeta[3],
  Bcoef[2, 3, 186] -> 35/8 - 3*Zeta[3],
  Bcoef[2, 3, 187] -> -13/8,
  Bcoef[2, 3, 188] -> -13/8,
  Bcoef[2, 3, 189] -> -3 + 12*Zeta[3],
  Bcoef[2, 3, 190] -> -10 + 12*Zeta[3],
  Bcoef[2, 3, 191] -> -14,
  Bcoef[2, 3, 192] -> -31/4 + 9*Zeta[3],
  Bcoef[2, 3, 193] -> -51/4 + 12*Zeta[3],
  Bcoef[2, 3, 194] -> -8 + 6*Zeta[3],
  Bcoef[2, 3, 195] -> 1,
  Bcoef[2, 3, 196] -> -1/8 - 3*Zeta[3],
  Bcoef[2, 3, 197] -> 12 + 12*Zeta[3],
  Bcoef[2, 3, 198] -> 5/4 + 3*Zeta[3],
  Bcoef[2, 3, 199] -> -77/2 + 12*Zeta[3],
  Bcoef[2, 3, 200] -> -47/8 + 3*Zeta[3],
  Bcoef[2, 3, 201] -> -67/8 + 3*Zeta[3],
  Bcoef[2, 3, 202] -> 87/4 - 24*Zeta[3],
  Bcoef[2, 3, 203] -> 13/2 - 12*Zeta[3],
  Bcoef[2, 3, 204] -> 25/4 - 6*Zeta[3],
  Bcoef[2, 3, 205] -> 25/8 - 6*Zeta[3],
  Bcoef[2, 3, 206] -> 5/8 - 3*Zeta[3],
  Bcoef[2, 3, 207] -> 7/4 + 12*Zeta[3],
  Bcoef[2, 3, 208] -> -1 + 3*Zeta[3],
  Bcoef[2, 3, 209] -> -25/8 + 3*Zeta[3],
  Bcoef[2, 3, 210] -> -11/2,
  Bcoef[2, 3, 211] -> -11/2,
  Bcoef[2, 3, 212] -> 0,
  Bcoef[2, 3, 213] -> -1/4 + 3*Zeta[3],
  Bcoef[2, 3, 214] -> 3/2 - 12*Zeta[3],
  Bcoef[2, 3, 215] -> -29/8 - 6*Zeta[3],
  Bcoef[2, 3, 216] -> 5,
  Bcoef[2, 3, 217] -> 0,
  Bcoef[2, 3, 218] -> 15/2 - 6*Zeta[3],
  Bcoef[2, 3, 219] -> 21/4 - 3*Zeta[3],
  Bcoef[2, 3, 220] -> -9/2 + 6*Zeta[3],
  Bcoef[2, 3, 221] -> 27/8 + 3*Zeta[3],
  Bcoef[2, 3, 222] -> 0,
  Bcoef[2, 3, 223] -> -3/4,
  Bcoef[2, 3, 224] -> 3,
  Bcoef[2, 3, 225] -> -2,
  Bcoef[2, 3, 226] -> 4,
  Bcoef[2, 3, 227] -> 5,
  Bcoef[2, 3, 228] -> 2,
  Bcoef[2, 3, 229] -> 6,
  Bcoef[2, 3, 230] -> 2,
  Bcoef[2, 3, 231] -> 5/8,
  Bcoef[2, 3, 232] -> 5/8,
  Bcoef[2, 3, 233] -> 1,
  Bcoef[2, 3, 234] -> 3/2,
  Bcoef[2, 3, 235] -> 1,
  Bcoef[2, 3, 236] -> -3,
  Bcoef[2, 3, 237] -> -4 + 12*Zeta[3],
  Bcoef[2, 3, 238] -> -6 + 12*Zeta[3],
  Bcoef[2, 3, 239] -> -8 + 12*Zeta[3],
  Bcoef[2, 3, 240] -> 2,
  Bcoef[2, 3, 241] -> 2,
  Bcoef[2, 3, 242] -> -4 + 12*Zeta[3],
  Bcoef[2, 3, 243] -> -6 + 12*Zeta[3],
  Bcoef[2, 3, 244] -> -5 + 6*Zeta[3],
  Bcoef[2, 3, 245] -> -2 + 3*Zeta[3],
  Bcoef[2, 3, 246] -> -1 + (3*Zeta[3])/2,
  Bcoef[2, 3, 247] -> -3,
  Bcoef[2, 3, 248] -> -1,
  Bcoef[2, 3, 249] -> -1,
  Bcoef[2, 3, 250] -> -8,
  Bcoef[2, 3, 251] -> -6,
  Bcoef[2, 3, 252] -> 0,
  Bcoef[2, 3, 253] -> -2,
  Bcoef[2, 3, 254] -> -4,
  Bcoef[2, 3, 255] -> 2,
  Bcoef[2, 3, 256] -> 4,
  Bcoef[2, 3, 257] -> 5/4,
  Bcoef[2, 3, 258] -> -2,
  Bcoef[2, 3, 259] -> 4,
  Bcoef[2, 3, 260] -> -2,
  Bcoef[2, 3, 261] -> -5/8,
  Bcoef[2, 3, 262] -> 1,
  Bcoef[2, 3, 263] -> 1,
  Bcoef[2, 3, 264] -> 0,
  Bcoef[2, 3, 265] -> 0,
  Bcoef[2, 3, 266] -> -3/8,
  Bcoef[2, 3, 267] -> -3/4,
  Bcoef[2, 3, 268] -> 7/4,
  Bcoef[2, 3, 269] -> 1,
  Bcoef[2, 3, 270] -> 25/8,
  Bcoef[2, 3, 271] -> 7/8,
  Bcoef[2, 3, 272] -> -3,
  Bcoef[2, 3, 273] -> 4,
  Bcoef[2, 3, 274] -> 3,
  Bcoef[2, 3, 275] -> -2,
  Bcoef[2, 3, 276] -> -3,
  Bcoef[2, 3, 277] -> 3/16,
  Bcoef[2, 3, 278] -> 1/2,
  Bcoef[2, 3, 279] -> 2,
  Bcoef[2, 3, 280] -> 1/8,
  Bcoef[2, 3, 281] -> 3/16,
  Bcoef[2, 3, 282] -> 7/16,
  Bcoef[2, 3, 283] -> 5/16,
  Bcoef[2, 3, 284] -> 7/16,
  Bcoef[2, 3, 285] -> 2,
  Bcoef[2, 3, 286] -> 25/8,
  Bcoef[2, 3, 287] -> -3,
  Bcoef[2, 3, 288] -> 3,
  Bcoef[2, 3, 289] -> -1,
  Bcoef[2, 3, 290] -> -3/16,
  Bcoef[2, 3, 291] -> 9/16,
  Bcoef[2, 3, 292] -> -3/16,
  Bcoef[2, 3, 293] -> 9/16,
  Bcoef[2, 3, 294] -> 1,
  Bcoef[2, 3, 295] -> -1/2,
  Bcoef[2, 3, 296] -> -1,
  Bcoef[2, 3, 297] -> -5/16,
  Bcoef[2, 3, 298] -> 1/32,
  Bcoef[2, 3, 299] -> -3/16,
  Bcoef[2, 3, 300] -> -1,
  Bcoef[2, 3, 301] -> -1/4,
  Bcoef[2, 3, 302] -> -1/2,
  Bcoef[2, 3, 303] -> -3/16,
  Bcoef[2, 3, 304] -> -24,
  Bcoef[2, 3, 305] -> -12,
  Bcoef[2, 3, 306] -> 8 - 24*Zeta[3],
  Bcoef[2, 3, 307] -> 8 - 24*Zeta[3],
  Bcoef[2, 3, 308] -> 8 - 24*Zeta[3]
};

$gaugeCoefficients = {
	Bcoef[1, 0, 1] -> 1,
	(* 1-loop *)
	Bcoef[1, 1, 1] -> -22/3,
	Bcoef[1, 1, 2] -> 2/3,
	Bcoef[1, 1, 3] -> 1/3,
	(* 2-loop *)
	Bcoef[1, 2, 1] -> 2,
	Bcoef[1, 2, 2] -> 4,
	Bcoef[1, 2, 3] -> -68/3,
	Bcoef[1, 2, 4] -> 10/3,
	Bcoef[1, 2, 5] -> 2/3,
	Bcoef[1, 2, 6] -> -1,
	Bcoef[1, 2, 7] -> 0,
	(* 3-loop *)
	Bcoef[1, 3, 1] -> -1,
	Bcoef[1, 3, 2] -> 29/2,
	Bcoef[1, 3, 3] -> 133/18,
	Bcoef[1, 3, 4] -> 679/36,
	Bcoef[1, 3, 5] -> -11/18,
	Bcoef[1, 3, 6] -> -25/18,
	Bcoef[1, 3, 7] -> -23/36,
	Bcoef[1, 3, 8] -> -49/36,
	Bcoef[1, 3, 9] -> 4,
	Bcoef[1, 3, 10] -> 25/2,
	Bcoef[1, 3, 11] -> -2857/27,
	Bcoef[1, 3, 12] -> -79/108,
	Bcoef[1, 3, 13] -> 1/54,
	Bcoef[1, 3, 14] -> 1415/54,
	Bcoef[1, 3, 15] -> 545/108,
	Bcoef[1, 3, 16] -> -29/54,
	Bcoef[1, 3, 17] -> 1,
	Bcoef[1, 3, 18] -> -1/12,
	Bcoef[1, 3, 19] -> -5/4,
	Bcoef[1, 3, 20] -> -1/4,
	Bcoef[1, 3, 21] -> -1,
	Bcoef[1, 3, 22] -> -7,
	Bcoef[1, 3, 23] -> -7/2,
	Bcoef[1, 3, 24] -> -6,
	Bcoef[1, 3, 25] -> 9/4,
	Bcoef[1, 3, 26] -> 1,
	Bcoef[1, 3, 27] -> -1,
	Bcoef[1, 3, 28] -> 3/2,
	Bcoef[1, 3, 29] -> 7/8,
	Bcoef[1, 3, 30] -> 1/2,
	Bcoef[1, 3, 31] -> 1/8,
	Bcoef[1, 3, 32] -> 3/8,
	Bcoef[1, 3, 33] -> -1/8,
	(* 4-loop *)
  Bcoef[1, 4, 1] -> 160/9 - (1408*Zeta[3])/3,
  Bcoef[1, 4, 2] -> -14/9 + (32*Zeta[3])/3,
  Bcoef[1, 4, 3] -> -457/9 + (640*Zeta[3])/3,
  Bcoef[1, 4, 4] -> -128/9 + (32*Zeta[3])/3,
  Bcoef[1, 4, 5] -> 88/9 - (64*Zeta[3])/3,
  Bcoef[1, 4, 6] -> -256/9 + (832*Zeta[3])/3,
  Bcoef[1, 4, 7] -> -71/3 + 8*Zeta[3],
  Bcoef[1, 4, 8] -> -95/6 + 16*Zeta[3],
  Bcoef[1, 4, 9] -> -34/3 + 4*Zeta[3],
  Bcoef[1, 4, 10] -> -23/3 + 8*Zeta[3],
  Bcoef[1, 4, 11] -> 49/9 - (832*Zeta[3])/3,
  Bcoef[1, 4, 12] -> -3/2,
  Bcoef[1, 4, 13] -> 92/27 + (2320*Zeta[3])/9,
  Bcoef[1, 4, 14] -> 13733/108 + (352*Zeta[3])/9,
  Bcoef[1, 4, 15] -> 38/27 + (16*Zeta[3])/9,
  Bcoef[1, 4, 16] -> -181/27 - (32*Zeta[3])/9,
  Bcoef[1, 4, 17] -> 28/27 + (8*Zeta[3])/9,
  Bcoef[1, 4, 18] -> -221/27 - (16*Zeta[3])/9,
  Bcoef[1, 4, 19] -> 158/9 + (832*Zeta[3])/3,
  Bcoef[1, 4, 20] -> 291/4,
  Bcoef[1, 4, 21] -> -77/486,
  Bcoef[1, 4, 22] -> -47/486,
  Bcoef[1, 4, 23] -> 91/1944,
  Bcoef[1, 4, 24] -> 323/1944,
  Bcoef[1, 4, 25] -> -769/486 - (88*Zeta[3])/9,
  Bcoef[1, 4, 26] -> -15025/1944 - (20*Zeta[3])/3,
  Bcoef[1, 4, 27] -> 29/486,
  Bcoef[1, 4, 28] -> -539/486 - (44*Zeta[3])/9,
  Bcoef[1, 4, 29] -> 9271/486 - (448*Zeta[3])/9,
  Bcoef[1, 4, 30] -> 60659/486 - (88*Zeta[3])/3,
  Bcoef[1, 4, 31] -> -12025/972 - (40*Zeta[3])/3,
  Bcoef[1, 4, 32] -> -49/486,
  Bcoef[1, 4, 33] -> -463/27 - (1676*Zeta[3])/9,
  Bcoef[1, 4, 34] -> 5633/108 + (424*Zeta[3])/9,
  Bcoef[1, 4, 35] -> 707/27 - (1292*Zeta[3])/9,
  Bcoef[1, 4, 36] -> 4801/54 - (176*Zeta[3])/9,
  Bcoef[1, 4, 37] -> -85/27 + (4*Zeta[3])/9,
  Bcoef[1, 4, 38] -> -208/27 + (16*Zeta[3])/9,
  Bcoef[1, 4, 39] -> -121/54 + (2*Zeta[3])/9,
  Bcoef[1, 4, 40] -> -641/108 + (8*Zeta[3])/9,
  Bcoef[1, 4, 41] -> -221/54 + (28*Zeta[3])/9,
  Bcoef[1, 4, 42] -> -1081/108 + (28*Zeta[3])/9,
  Bcoef[1, 4, 43] -> 211/108 - (22*Zeta[3])/9,
  Bcoef[1, 4, 44] -> 53/216 - (4*Zeta[3])/9,
  Bcoef[1, 4, 45] -> -151013/243 + (440*Zeta[3])/9,
  Bcoef[1, 4, 46] -> 37223/162 + (836*Zeta[3])/9,
  Bcoef[1, 4, 47] -> 20873/432 - (136*Zeta[3])/9,
  Bcoef[1, 4, 48] -> -53/972,
  Bcoef[1, 4, 49] -> -4229/324 - (4*Zeta[3])/3,
  Bcoef[1, 4, 50] -> -59/1944,
  Bcoef[1, 4, 51] -> 251/1296 - (10*Zeta[3])/9,
  Bcoef[1, 4, 52] -> -661/108 - (26*Zeta[3])/9,
  Bcoef[1, 4, 53] -> -7/216,
  Bcoef[1, 4, 54] -> -4/81,
  Bcoef[1, 4, 55] -> -27/2,
  Bcoef[1, 4, 56] -> 17,
  Bcoef[1, 4, 57] -> 3/2,
  Bcoef[1, 4, 58] -> -37/36,
  Bcoef[1, 4, 59] -> -5/36,
  Bcoef[1, 4, 60] -> 1/2,
  Bcoef[1, 4, 61] -> 1/18,
  Bcoef[1, 4, 62] -> -5/3,
  Bcoef[1, 4, 63] -> -1/12,
  Bcoef[1, 4, 64] -> -11/24,
  Bcoef[1, 4, 65] -> -13/8,
  Bcoef[1, 4, 66] -> -1/9,
  Bcoef[1, 4, 67] -> -1/12,
  Bcoef[1, 4, 68] -> 1/8,
  Bcoef[1, 4, 69] -> -36,
  Bcoef[1, 4, 70] -> 17/4,
  Bcoef[1, 4, 71] -> 3/2,
  Bcoef[1, 4, 72] -> 2,
  Bcoef[1, 4, 73] -> 3/4,
  Bcoef[1, 4, 74] -> -59/24 + 25*Zeta[3],
  Bcoef[1, 4, 75] -> -33/2 - 6*Zeta[3],
  Bcoef[1, 4, 76] -> 49/4 + 6*Zeta[3],
  Bcoef[1, 4, 77] -> -28 + 15*Zeta[3],
  Bcoef[1, 4, 78] -> 593/24 + 5*Zeta[3],
  Bcoef[1, 4, 79] -> 1 - 6*Zeta[3],
  Bcoef[1, 4, 80] -> -36*Zeta[3],
  Bcoef[1, 4, 81] -> -55/3 + 10*Zeta[3],
  Bcoef[1, 4, 82] -> 29 - 36*Zeta[3],
  Bcoef[1, 4, 83] -> -27/2,
  Bcoef[1, 4, 84] -> -3445/216 - (7*Zeta[3])/9,
  Bcoef[1, 4, 85] -> 71/216 + (8*Zeta[3])/9,
  Bcoef[1, 4, 86] -> 359/432 + (4*Zeta[3])/9,
  Bcoef[1, 4, 87] -> -5093/216 + (169*Zeta[3])/9,
  Bcoef[1, 4, 88] -> -1259/36 + 3*Zeta[3],
  Bcoef[1, 4, 89] -> 68/9 - (22*Zeta[3])/3,
  Bcoef[1, 4, 90] -> 463/216 - (8*Zeta[3])/9,
  Bcoef[1, 4, 91] -> 97/36,
  Bcoef[1, 4, 92] -> -4/9 + (2*Zeta[3])/3,
  Bcoef[1, 4, 93] -> 679/432 - (4*Zeta[3])/9,
  Bcoef[1, 4, 94] -> 43/18,
  Bcoef[1, 4, 95] -> -1/18 + Zeta[3]/3,
  Bcoef[1, 4, 96] -> -37/2,
  Bcoef[1, 4, 97] -> 15/2,
  Bcoef[1, 4, 98] -> -11/3 + 2*Zeta[3],
  Bcoef[1, 4, 99] -> -41,
  Bcoef[1, 4, 100] -> -520/27 + (55*Zeta[3])/9,
  Bcoef[1, 4, 101] -> 77/108 - (5*Zeta[3])/9,
  Bcoef[1, 4, 102] -> 203/216 - (5*Zeta[3])/18,
  Bcoef[1, 4, 103] -> -19/2,
  Bcoef[1, 4, 104] -> -823/18,
  Bcoef[1, 4, 105] -> 109/36,
  Bcoef[1, 4, 106] -> 43/72,
  Bcoef[1, 4, 107] -> 4721/216 + (11*Zeta[3])/9,
  Bcoef[1, 4, 108] -> -61/216 - Zeta[3]/9,
  Bcoef[1, 4, 109] -> -223/432 - Zeta[3]/18,
  Bcoef[1, 4, 110] -> -4,
  Bcoef[1, 4, 111] -> -13/6,
  Bcoef[1, 4, 112] -> 1/4,
  Bcoef[1, 4, 113] -> -1/144,
  Bcoef[1, 4, 114] -> 11/48,
  Bcoef[1, 4, 115] -> 20/3,
  Bcoef[1, 4, 116] -> 6 - 12*Zeta[3],
  Bcoef[1, 4, 117] -> 7/3 - 24*Zeta[3],
  Bcoef[1, 4, 118] -> 38/3,
  Bcoef[1, 4, 119] -> 2/3,
  Bcoef[1, 4, 120] -> -1,
  Bcoef[1, 4, 121] -> -11/3,
  Bcoef[1, 4, 122] -> -1/2,
  Bcoef[1, 4, 123] -> -19/6,
  Bcoef[1, 4, 124] -> -31/12 - 6*Zeta[3],
  Bcoef[1, 4, 125] -> 61/9 - (52*Zeta[3])/3,
  Bcoef[1, 4, 126] -> -9/2 + 24*Zeta[3],
  Bcoef[1, 4, 127] -> 2 + 36*Zeta[3],
  Bcoef[1, 4, 128] -> 131/12 - 14*Zeta[3],
  Bcoef[1, 4, 129] -> -539/36 - (16*Zeta[3])/3,
  Bcoef[1, 4, 130] -> 89/9 - (38*Zeta[3])/3,
  Bcoef[1, 4, 131] -> 87/8 - 6*Zeta[3],
  Bcoef[1, 4, 132] -> 43/12 + 6*Zeta[3],
  Bcoef[1, 4, 133] -> -1/2 + Zeta[3],
  Bcoef[1, 4, 134] -> -301/72 - Zeta[3]/3,
  Bcoef[1, 4, 135] -> -113/72 + Zeta[3]/3,
  Bcoef[1, 4, 136] -> 80/9 - (5*Zeta[3])/3,
  Bcoef[1, 4, 137] -> 11/6,
  Bcoef[1, 4, 138] -> 3/2 + Zeta[3],
  Bcoef[1, 4, 139] -> 1/6 + Zeta[3],
  Bcoef[1, 4, 140] -> -9/4 + 3*Zeta[3],
  Bcoef[1, 4, 141] -> 31/12,
  Bcoef[1, 4, 142] -> 7/6,
  Bcoef[1, 4, 143] -> 23/3 - 3*Zeta[3],
  Bcoef[1, 4, 144] -> 113/144 + (4*Zeta[3])/3,
  Bcoef[1, 4, 145] -> -131/144 - (4*Zeta[3])/3,
  Bcoef[1, 4, 146] -> -779/144 + (14*Zeta[3])/3,
  Bcoef[1, 4, 147] -> 229/72 - (5*Zeta[3])/3,
  Bcoef[1, 4, 148] -> 145/48 - 3*Zeta[3],
  Bcoef[1, 4, 149] -> 203/72 + Zeta[3]/6,
  Bcoef[1, 4, 150] -> 59/6,
  Bcoef[1, 4, 151] -> -115/9 + (4*Zeta[3])/3,
  Bcoef[1, 4, 152] -> 97/6,
  Bcoef[1, 4, 153] -> 25/4,
  Bcoef[1, 4, 154] -> 10/9 - Zeta[3]/3,
  Bcoef[1, 4, 155] -> 3/4,
  Bcoef[1, 4, 156] -> 17/12,
  Bcoef[1, 4, 157] -> -373/144 + Zeta[3]/3,
  Bcoef[1, 4, 158] -> 0,
  Bcoef[1, 4, 159] -> 1/6,
  Bcoef[1, 4, 160] -> -5/2,
  Bcoef[1, 4, 161] -> -5/3,
  Bcoef[1, 4, 162] -> -3/2,
  Bcoef[1, 4, 163] -> 17/6 - 3*Zeta[3],
  Bcoef[1, 4, 164] -> -6,
  Bcoef[1, 4, 165] -> -1,
  Bcoef[1, 4, 166] -> -1,
  Bcoef[1, 4, 167] -> -1/2,
  Bcoef[1, 4, 168] -> -1/2,
  Bcoef[1, 4, 169] -> -3/2,
  Bcoef[1, 4, 170] -> 34/9 - (4*Zeta[3])/3,
  Bcoef[1, 4, 171] -> -2/9 - (4*Zeta[3])/3,
  Bcoef[1, 4, 172] -> -31/9 + (4*Zeta[3])/3,
  Bcoef[1, 4, 173] -> -17/18 + (4*Zeta[3])/3,
  Bcoef[1, 4, 174] -> -15/8,
  Bcoef[1, 4, 175] -> 11/18 + (2*Zeta[3])/3,
  Bcoef[1, 4, 176] -> -3/2,
  Bcoef[1, 4, 177] -> -113/72 - Zeta[3]/6,
  Bcoef[1, 4, 178] -> -55/72 - Zeta[3]/3,
  Bcoef[1, 4, 179] -> 115/72 - Zeta[3]/6,
  Bcoef[1, 4, 180] -> 9/8,
  Bcoef[1, 4, 181] -> 11/18 - Zeta[3]/3,
  Bcoef[1, 4, 182] -> 43/36 - Zeta[3]/3,
  Bcoef[1, 4, 183] -> -115/72 + (2*Zeta[3])/3,
  Bcoef[1, 4, 184] -> -41/16,
  Bcoef[1, 4, 185] -> -3/8,
  Bcoef[1, 4, 186] -> -1/4,
  Bcoef[1, 4, 187] -> 19/96,
  Bcoef[1, 4, 188] -> -9/32,
  Bcoef[1, 4, 189] -> 1/12,
  Bcoef[1, 4, 190] -> -1/2,
  Bcoef[1, 4, 191] -> 3/16,
  Bcoef[1, 4, 192] -> -17/96,
  Bcoef[1, 4, 193] -> -25/32,
  Bcoef[1, 4, 194] -> -3/16,
  Bcoef[1, 4, 195] -> -1/4,
  Bcoef[1, 4, 196] -> 3/16,
  Bcoef[1, 4, 197] -> 1/16,
  Bcoef[1, 4, 198] -> 1/16,
  Bcoef[1, 4, 199] -> -4,
  Bcoef[1, 4, 200] -> -2,
  Bcoef[1, 4, 201] -> 4/3 - 4*Zeta[3],
  Bcoef[1, 4, 202] -> 8/3 - 8*Zeta[3]
};

$fermionAnomalousCoefficients = {
	(* 1-loop *)
	Acoef[1, 1, 1] -> Global`\[Xi],
	Acoef[1, 1, 2] -> 1/2,
	(* 2-loop *)
	Acoef[1, 2, 1] -> -3/2,
	Acoef[1, 2, 2] -> 25/4 + 2 Global`\[Xi] + Global`\[Xi]^2/4,
	Acoef[1, 2, 3] -> -1/4,
	Acoef[1, 2, 4] -> -1/2,
	Acoef[1, 2, 5] -> 9/2,
	Acoef[1, 2, 6] -> -1/4,
	Acoef[1, 2, 7] -> -7/4,
	Acoef[1, 2, 8] -> -1/8,
	Acoef[1, 2, 9] -> -3/8
};

$scalarAnomalousCoefficients = {
	(* 1-loop *)
	Acoef[2, 1, 1] -> Global`\[Xi] - 3,
	Acoef[2, 1, 2] -> 1/2,
	(* 2-loop *)
	Acoef[2, 2, 1] -> 3/2,
	Acoef[2, 2, 2] -> Global`\[Xi]^2/4 + 2 Global`\[Xi] - 35/3,
	Acoef[2, 2, 3] -> 11/12,
	Acoef[2, 2, 4] -> 5/6,
	Acoef[2, 2, 5] -> 1/12,
	Acoef[2, 2, 6] -> 5/2,
	Acoef[2, 2, 7] -> -1/2,
	Acoef[2, 2, 8] -> -3/4
};


Protect[$gaugeCoefficients, $quarticCoefficients, $yukawaCoefficients, $fermionAnomalousCoefficients, $scalarAnomalousCoefficients];
