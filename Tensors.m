sig1 = {{0, 1}, {1, 0}};

(*Gauge coupling multiplied on generators*)
TfG2[A_, i_, j_] := Module[{B}, Tf[B, i, j] G2[A, B] // Expand]
TfG2t[A_, i_, j_] := Module[{B}, Tft[B, i, j] G2[A, B] // Expand]
TsG2[A_, a_, b_] := Module[{B}, Ts[B, a, b] G2[A, B] // Expand]

(*######################################*)
(*----------2-point structures----------*)
(*######################################*)
(*1-loop*)
C2G[A_, B_] := Module[{C1, C2, D1, D2},
		Ttimes[FGauge[A, C1, D1], G2[C1, C2], G2[D1, D2], FGauge[B, C2, D2]]
	]; 
S2F[A_, B_] := Module[{i, j},
		Tr[Tf[A, i, j].Tf[B, j, i]] // Expand
	];
S2S[A_, B_] := Module[{i, j},
		Ts[A, i, j] Ts[B, j, i] // Expand
	];
C2F[i_, j_] := Module[{A, k},
		TfG2[A, i, k].Tf[A, k, j] // Expand
	];
C2Ft[i_, j_] :=	Module[{A, k},
		TfG2t[A, i, k].Tft[A, k, j] // Expand
	];
C2S[a_, b_] := Module[{A, c},
	TsG2[A, a, c] Ts[A, c, b] // Expand
	];
Y2S[a_, b_] := Module[{i, j},
		Tr[y[a, i, j].yt[b, j, i]] // Expand
	];
Y2F[i_, j_] := Module[{a, k},
		y[a, i, k].yt[a, k, j] // Expand
	];
Y2Ft[i_, j_] := Module[{a, k},
		yt[a, i, k].y[a, k, j] // Expand
	];

(*----------2-loop----------*)
(*g^4*)
S2SC2S[A_, B_] := Module[{a, b, c},
		Ttimes[Ts[B, c, a], Ts[A, a, b], C2S[b, c]]
	];
S2FC2F[A_, B_] := Module[{i, j, k},
		Tr[Tdot[Tf[B, k, i], Tf[A, i, j], C2F[j, k]]]
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
		Tr @ Tdot[y[a, i, j], C2F[j, k], yt[b, k, i]]
	];
Y2FC2F[i_, j_] := Module[{a, k, l},
		Tdot[y[a, i, k], C2F[k, l], yt[a, l, j]]
	];
Y2FC2S[i_, j_] := Module[{a, b, k},
		Tdot[y[a, i, k], yt[b, k, j]] C2S[a, b] // Expand
	];
Y2FC2Ft[i_, j_] := sig1.Y2FC2F[i, j].sig1;
Y2FC2St[i_, j_] := sig1.Y2FC2S[i, j].sig1;
S2SY2S[A_, B_] := Module[{a, b, c},
		Ttimes[Ts[B, c, a], Ts[A, a, b], Y2S[b, c]]
	];
S2FY2F[A_, B_] := Module[{i, j, k},
		Tr @ Tdot[Tft[B, k, i], Tft[A, i, j], Y2F[j, k]]
	];

(*y^4*)
Y2SY2F[a_, b_] := Module[{k1, k2, k3},
		Tr @ Tdot[y[a, k1, k2], yt[b, k2, k3], Y2F[k3, k1]]
	];
Y4cS[a_, b_] := Module[{c, k1, k2, k3, k4},
		Tr @ Tdot[y[a, k1, k2], yt[c, k2, k3], y[b, k3, k4], yt[c, k4, k1]]
	];
Y4cF[i_, j_] := Module[{a, b, k1, k2, k3},
		Ttimes[y[a, i, k1], yt[b, k1, k2], y[a, k2, k3], yt[b, k3, j]]
	];
Y2FY2F[i_, j_] := Module[{a, k1, k2},
		Tdot[y[a, i, k1], Y2Ft[k1, k2], yt[a, k2, j]]
	];
Y2FY2S[i_, j_] := Module[{a, b, k1},
		Tdot[y[a, i, k1], yt[b, k1, j]] Y2S[a, b] // Expand
	];
Y4cFt[i_, j_] := sig1.Y4cF[i, j].sig1;
Y2FY2Ft[i_, j_] := sig1.Y2FY2F[i, j].sig1;
Y2FY2St[i_, j_] := sig1.Y2FY2S[i, j].sig1;

(*lambda^2*)
Lam2[a_, b_] := Module[{c, d, e},
		Lam[a, c, d, e] Lam[c, d, e, b] // Expand
	];


(*#################################*)
(*----------Gauge tensors----------*)
(*#################################*)
(*Gauge tensors at 1-loop order*)
GaugeTensors[1] := GaugeTensors[1] = 
	Block[{bg, n},
		bg[1, 1] = C2G[A, B];
		bg[1, 2] = S2F[A, B];
		bg[1, 3] = S2S[A, B];
		Sum[B[1, 1, n] bg[1, n], {n, 3}]
	];
	
(*Gauge tensors at 2-loop order*)	
GaugeTensors[2] := GaugeTensors[2] =
	Block[{bg, n},
		bg[2, 1] = S2FC2F[A, B];
		bg[2, 2] = S2SC2S[A, B];
		bg[2, 3] = Ttimes[C2G[A, A1], G2[A1, B1], C2G[B1, B]];
		bg[2, 4] = Ttimes[C2G[A, A1], G2[A1, B1], S2F[B1, B]];
		bg[2, 5] = Ttimes[C2G[A, A1], G2[A1, B1], S2S[B1, B]];
		bg[2, 6] = S2FY2F[A, B];
		bg[2, 7] = S2SY2S[A, B];
		Sum[B[1, 2, n] bg[2, n], {n, 7}]
	];

(*Gauge tensors at 3-loop order*)	
GaugeTensors[3] := GaugeTensors[3] =
	Block[{bg, n},
		(*y^0 terms*)
		bg[3, 1] = Tr@Tdot[Tf[B, l, i], Tf[A, i, j], C2F[j, k], C2F[k, l]];
		bg[3, 2] = Ttimes[Ts[B, d, a], Ts[A, a, b], C2S[b, c], C2S[c, d]];
		bg[3, 3] = Tr@Tdot[Tf[B, k, i], Tf[A, i, j], C2FC2G[j, k]];
		bg[3, 4] = Ttimes[Ts[B, c, a], Ts[A, a, b], C2SC2G[b, c]];
		bg[3, 5] = Tr@Tdot[Tf[B, k, i], Tf[A, i, j], C2FS2F[j, k]];
		bg[3, 6] = Ttimes[Ts[B, c, a], Ts[A, a, b], C2SS2F[b, c]];
		bg[3, 7] = Tr@Tdot[Tf[B, k, i], Tf[A, i, j], C2FS2S[j, k]];
		bg[3, 8] = Ttimes[Ts[B, c, a], Ts[A, a, b], C2SS2S[b, c]];		
		bg[3, 9] = Ttimes[S2FC2F[A, C1], G2[C1, C2], C2G[C2, B]];
		bg[3, 10] = Ttimes[S2SC2S[A, C1], G2[C1, C2], C2G[C2, B]];
		bg[3, 11] = Ttimes[C2G[A, C1], G2[C1, C2], C2G[C2, C3], G2[C3, C4], C2G[C4, B]];
		bg[3, 12] = Ttimes[C2G[A, C1], G2[C1, C2], S2F[C2, C3], G2[C3, C4], S2F[C4, B]];
		bg[3, 13] = Ttimes[C2G[A, C1], G2[C1, C2], S2S[C2, C3], G2[C3, C4], S2S[C4, B]];
		bg[3, 14] = Ttimes[C2G[A, C1], G2[C1, C2], C2G[C2, C3], G2[C3, C4], S2F[C4, B]];
		bg[3, 15] = Ttimes[C2G[A, C1], G2[C1, C2], C2G[C2, C3], G2[C3, C4], S2S[C4, B]];
		bg[3, 16] = Ttimes[S2F[A, C1], G2[C1, C2], C2G[C2, C3], G2[C3, C4], S2S[C4, B]];
		bg[3, 17] = Ttimes[Ts[A, a, b], TsG2[B1, b, c], Lam[a, c, d, f], Ts[B, d, e], Ts[B1, e, f]];
		bg[3, 18] = Ttimes[Ts[A, a, b], Lam2[b, c], Ts[B, c, a]];
		(*y^2 terms*)
		bg[3, 19] = Tr @ Tdot[Tf[B, l, i], Tf[A, i, j], Y2Ft[j, k], C2F[k, l]];
		bg[3, 20] = Tr @ Tdot[Tf[B, k, i], Tf[A, i, j], Y2FC2Ft[j, k]];
		bg[3, 21] = Ttimes[Ts[B, c, a], Ts[A, a, b], Y2SC2F[b, c]];
		bg[3, 22] = Tr @ Tdot[Tf[B, k, i], Tf[A, i, j], Y2FC2St[j, k]];
		bg[3, 23] = Ttimes[Ts[B, d, a], Ts[A, a, b], Y2S[b, c], C2S[c, d]];
		bg[3, 24] = Ttimes[S2FY2F[A, C1], G2[C1, C2], C2G[C2, B]];
		bg[3, 25] = Ttimes[S2SY2S[A, C1], G2[C1, C2], C2G[C2, B]];
		(*y^4 terms*)
		bg[3, 26] = Tr @ Tdot[y[a, k6, k1], Tf[A, k1, k2], yt[a, k2, k3], y[b, k3, k4], Tf[B, k4, k5], yt[b, k5, k6]];
		bg[3, 27] = Ttimes[Ts[B, c, a], Ts[A, a, b], Y4cS[b, c]];
		bg[3, 28] = Tr @ Tdot[Tf[B, k, i], Tf[A, i, j], Y4cFt[j, k]];
		bg[3, 29] = Tr @ Tdot[Tf[B, k, i], Tf[A, i, j], Y2FY2St[j, k]];
		bg[3, 30] = Ttimes[Ts[B, c, a], Ts[A, a, b], Y2SY2F[b, c]];
		bg[3, 31] = Tr @ Tdot[Tf[B, l, i], Tf[A, i, j], Y2Ft[j, k], Y2Ft[k, l]];
		bg[3, 32] = Tr @ Tdot[Tf[B, k, i], Tf[A, i, j], Y2FY2Ft[j, k]];
		bg[3, 33] = Ttimes[Ts[B, d, a], Ts[A, a, b], Y2S[b, c], Y2S[c, d]];
		Sum[B[1, 3, n] bg[3, n], {n, 33}]
	];


(*##################################*)
(*----------Yukawa tensors----------*)
(*##################################*)
(*Yukawa tensors at 1-loop order*)
YukawaTensors[1] := YukawaTensors[1] = 
	Block[{by, n},
		by[1, 1] = y[b, i, j] C2S[a, b] // Expand;
		by[1, 2] = Tdot[C2Ft[i, k], y[a, k, j]] // Sym[i, j];
		by[1, 3] = Tdot[y[b, i, k1], yt[a, k1, k2], y[b, k2, j]];
		by[1, 4] = Tdot[Y2F[i, k], y[a, k, j]] // Sym[i, j];
		by[1, 5] = y[b, i, j] Y2S[b, a] // Expand;
		Sum[B[2, 1, n] by[1, n], {n, 5}]
	];

(*Yukawa tensors at 1-loop order*)
YukawaTensors[2] := YukawaTensors[2] = 
	Block[{by, n},
		(* y^1 terms*)
		by[2, 1] = Ttimes[y[c, i, j], C2S[c, b], C2S[b, a]];
		by[2, 2] = Tdot[C2Ft[i, k], y[b, k, j]] C2S[b, a] // Expand // Sym[i, j];
		by[2, 3] = Tdot[C2Ft[i, k], y[a, k, l], C2F[l, j]];
		by[2, 4] = Tdot[C2Ft[i, k], C2Ft[k, l], y[a, l, j]] // Sym[i, j];
		by[2, 5] = y[b, i, j] C2SC2G[b, a] // Expand;
		by[2, 6] = y[b, i, j] C2SS2S[b, a] // Expand;
		by[2, 7] = y[b, i, j] C2SS2F[b, a] // Expand;
		by[2, 8] = C2FC2Gt[i, k]. y[a, k, j] // Expand // Sym[i, j];
		by[2, 9] = C2FS2St[i, k]. y[a, k, j] // Expand // Sym[i, j];
		by[2, 10] = C2FS2Ft[i, k]. y[a, k, j] // Expand // Sym[i, j];
		by[2, 11] = y[b, i, j] Lam2[b, a] // Expand;
		(*y^3 terms*)
		by[2, 12] = Tdot[Tft[A, i, k1], y[a, k1, k2], yt[b, k2, k3], TfG2t[A, k3, k4], y[b, k4, j]] // Sym[i, j];
		by[2, 13] = Tdot[Y2F[i, k1], Tft[A, k1, k2], y[a, k2, k3], TfG2[A, k3, j]] // Sym[i, j];
		by[2, 14] = Tdot[y[b, i, k1], yt[a, k1, k2], y[c, k2, j]] C2S[b, c] // Expand;
		by[2, 15] = Tdot[y[b, i, k1], yt[c, k1, k2], y[b, k2, j]] C2S[c, a] // Expand;
		by[2, 16] = Tdot[y[b, i, k1], C2F[k1, k2], yt[a, k2, k3], y[b, k3, j]] // Sym[i, j];
		by[2, 17] = Tdot[C2Ft[i, k1], y[b, k1, k2], yt[a, k2, k3], y[b, k3, j]] // Sym[i, j];
		by[2, 18] = y[b, i, j] Y2SC2F[b, a] // Expand;
		by[2, 19] = y[a, i, k].Y2FC2St[k, j] // Expand // Sym[i, j];
		by[2, 20] = y[a, i, k].Y2FC2Ft[k, j] // Expand // Sym[i, j];
		by[2, 21] = Tdot[y[a, i, k1], Y2Ft[k1, k2], C2F[k2, j]] // Sym[i, j];
		by[2, 22] = Ttimes[y[c, i, j], Y2S[c, b], C2S[b, a]];
		by[2, 23] = Tdot[y[b, i, k1], yt[c, k1, k2], y[d, k2, j]] Lam[a, b, c, d] // Expand;
		(*y^5 terms*)
		by[2, 24] = Tdot[y[b, i, k1], yt[c, k1, k2], y[a, k2, k3], yt[b, k3, k4], y[c, k4, j]];
		by[2, 25] = Tdot[y[b, i, k1], yt[a, k1, k2], y[c, k2, k3], yt[b, k3, k4], y[c, k4, j]] // Sym[i, j];
		by[2, 26] = Tdot[y[c, i, k1], yt[b, k1, k2], y[a, k2, k3], yt[b, k3, k4], y[c, k4, j]];
		by[2, 27] = Tdot[y[a, i, k], Y4cFt[k, j]] // Sym[i, j];
		by[2, 28] = y[b, i, j] Y4cS[b, a] // Expand;
		by[2, 29] = Tdot[y[b, i, k1], Y2Ft[k1, k2], yt[a, k2, k3], y[b, k3, j]] // Sym[i, j];
		by[2, 30] = Tdot[y[a, i, k], Y2FY2Ft[k, j]] // Sym[i, j];
		by[2, 31] = y[b, i, j] Y2SY2F[b, a] // Expand;
		by[2, 32] = Tdot[y[b, i, k1], yt[a, k1, k2], y[c, k2, j]] Y2S[b, c] // Expand;
		by[2, 33] = Tdot[y[a, i, k], Y2FY2St[k, j]] // Sym[i, j];
		Sum[B[2, 2, n] by[2, n], {n, 23}]
	];

















	