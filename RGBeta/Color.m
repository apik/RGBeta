Package["RGBeta`"]
PackageExport["Color"]
PackageExport["ColorSUn"]
PackageExport["d3FF"]
PackageExport["d4FF"]
PackageExport["d4FA"]
PackageExport["d4AA"]
PackageExport["d433FFF"]
PackageExport["d444FFF"]

Color::usage =
  "Color[expr]"

ColorSUn::usage =
"ColorSUn[expr]"

(* Higher rank invariants *)
d3FF::usage =
"dF[a1,a2,a3]*dF[a1,a2,a3]"

d4FF::usage =
"dF[a1,a2,a3,a4]*dF[a1,a2,a3,a4]"

d4FA::usage =
"dF[a1,a2,a3,a4]*dA[a1,a2,a3,a4]"

d4AA::usage =
"dA[a1,a2,a3,a4]*dA[a1,a2,a3,a4]"

d433FFF::usage =
"dF[a1,a2,a3,a4]*dF[a1,a2,a5]*dF[a3,a4,a5]"

d444FFF::usage =
"dF[a1,a2,a3,a4]*dF[a1,a2,a5,a6]*dF[a3,a4,a5,a6]"


ColorSUn[e_]:= RefineGroupStructures[Expand[e]];


(* Comute T(a)...T(a) *)
ComuteTdelta[e_] :=
        Expand[ e //. FunTr[id_][gr_,A___,X_,B___,X_,C___] :>
                      FixedPoint[Expand[# //.
                                            {
                                                    del[gr[adj], x:OrderlessPatternSequence[A1_, XX_] ]*FunTr[id][gr,B1___,XX_,C1___]:>FunTr[id][gr,B1,A1,C1],
                                                    FunTr[id][gr] :> Dim[gr[fund]],
                                                    FunTr[id][gr,A1___,X,X,C1___] :> FunTr[id][gr, A1, C1] Casimir2[gr[fund]],
                                                    FunTr[id][gr,A1_,B1_] :> del[gr[adj],A1,B1] TraceNormalization[gr[fund]],
                                                    FunTr[id][gr,A1___,X,B1___,Y_,X,C1___] :>
                                                         FunTr[id][gr,A1,X,B1,X,Y,C1] + I*With[{Z=Unique["aIdx"]},fStruct[gr,Y,X,Z]*FunTr[id][gr,A1,X,B1,Z,C1]]
                                            }]&,
                                       FunTr[id][gr,A,X,B,X,C]]]



(* Comute T(a)...T(b)f(a,b,...) *)
ComuteTfabc[e_] :=
        Expand[e //. fStruct[gr_, x : OrderlessPatternSequence[X_, Y_, R_]]*
                   FunTr[id_][gr_, A___, X_, B___, Y_, C___] :>
                        FixedPoint[Expand[# //.
                                              {
                                                      fStruct[gr, X, Y, R]*FunTr[id][gr, A1___, X, Y, C1___] :> 
                                                             I/2 Casimir2[gr[adj]] FunTr[id][gr, A1, R, C1],
                                                      fStruct[gr, X, Y, R]*FunTr[id][gr, A1___, X, B1___, U1_, Y, C1___] :>
                                                             fStruct[gr, X, Y, R] (FunTr[id][gr, A1, X, B1, Y, U1, C1] + I*With[{Z = Unique["aIdx"]}, fStruct[gr, U1, Y, Z]*FunTr[id][gr, A1, X, B1, Z, C1]])
                                              }] &,
                                         Signature[List@x] Signature[{X, Y, R}] fStruct[gr, X, Y, R]*FunTr[id][gr, A, X, B, Y, C]]]


ColorFund[e_] :=
        Module[{res},
           (* All T[A,i,j] to traces *)
           res = e //. {tGen[gr_[fund], A_, b_, c_] /; ($gaugeGroups[gr, LieGroup] === Arb) :> oTr[gr, b, A, c]};
           (* All closed T-loops converted to the FunTr *)
           res = res //. { oTr[gr_, a_, A__, x_]*oTr[gr_, x_, B__, b_] :> oTr[gr, a, A, B, b] } //. {oTr[gr_, a_, A__, a_] :> FunTr[Unique["ftr"]][gr, A]};
           (* No tGen at this step *)
           Assert[FreeQ[res,tGen]];

           (* Simplify all fundamental traces with delta(a,b) and f(a,b,c) contractions *)
           res = FixedPoint[ComuteTfabc[ComuteTdelta[#]]&,res];

           (* At this step we have FunTr with max 4 indices *)
           res = Expand[res /. {
                   FunTr[_][gr_,A_,B_] :> del[gr[adj],A,B] TraceNormalization[gr[fund]],
                   FunTr[_][gr_,A_,B_,C_] :> dF[gr,A,B,C] + I/2 TraceNormalization[gr[fund]] fStruct[gr,A,B,C],
                   FunTr[_][gr_,a1_,a2_,a3_,a4_] :> dF[gr, a1, a2, a3, a4]
                   + Module[{x},
                          + 1/2 I dF[gr, a1, a2, x] fStruct[gr, a3, a4, x]
                          + 1/2 I dF[gr, a3, a4, x] fStruct[gr, a1, a2, x]
                          - 1/6 TraceNormalization[gr[fund]] fStruct[gr, a1, a3, x] fStruct[gr, a2, a4, x]
                          + 1/3 TraceNormalization[gr[fund]] fStruct[gr, a1, a4, x] fStruct[gr, a2, a3, x]
                     ]
                             }] //. {del[gr_[adj], x:OrderlessPatternSequence[A1_, XX_] ]*dF[gr_,B1___,XX_,C1___]:>dF[gr,B1,A1,C1]};


           (* No FunTr at this step *)
           Assert[FreeQ[res,FunTr]];

           (* Symmetrize dF[A1,A2,...] *)
           res = res /. { dF[gr_, A___] :> dF[gr, Sequence@@Sort[{A}]] };

           (* Identify scalar combinations *)
           res = res/. {
                   dF[gr_, A_, B_, C_]^2 :> d3FF[gr],
                   dF[gr_, A_, B_, C_, D_]^2 :> d4FF[gr]}
        ]



(* Closed loops of f(a,b,c) *)
TraceAdj[e_] :=
        Expand[e] //. {
                (* Trace 2 *)
                fStruct[gr_, A_, B_, C_ ]^2 :> Casimir2[gr@ adj]*Dim[gr[adj]],
                (* Trace 3 *)
                fStruct[group_, x:OrderlessPatternSequence[I1_, I2_, A1_] ]
                fStruct[group_, y:OrderlessPatternSequence[I2_, I3_, A2_] ]
                fStruct[group_, z:OrderlessPatternSequence[I3_, I1_, A3_] ] :>
                Signature[List@ x] Signature[List@ y] Signature[List@ z]
                Signature[{I1, I2, A1}] Signature[{I2, I3, A2}] Signature[{I3, I1, A3}]
                Casimir2[group@ adj]/2 fStruct[group, A1, A2, A3],
                (* Trace 4 *)
                fStruct[gr_, x1 : OrderlessPatternSequence[E_, a1_, F_]]
                fStruct[gr_, x2 : OrderlessPatternSequence[F_, a2_, G_]]
                fStruct[gr_, x3 : OrderlessPatternSequence[G_, a3_, H_]]
                fStruct[gr_, x4 : OrderlessPatternSequence[H_, a4_, E_]] :>
                Signature[List@x1] Signature[List@x2] Signature[List@x3] Signature[List@x4]
                (dA[gr, a1, a2, a3, a4]
                 + Casimir2[gr@ adj] With[{x=Unique["a4col"]},
                                          + 1/12 fStruct[gr, a1, a4, x] fStruct[gr, a2, a3, x]
                                          + 1/12 fStruct[gr, a1, a3, x] fStruct[gr, a2, a4, x]
                                          - 1/4  fStruct[gr, a1, a2, x] fStruct[gr, x, a3, a4]
                                     ])}

SimpAdj[e_]:=
        Module[{},
               (* Contraction of f(a,b,c) with dF[...] and dA[...] *)
               Expand[e] //.
        {
                fStruct[gr_, x:OrderlessPatternSequence[A_, B_, C_] ] dF[gr_, y:OrderlessPatternSequence[A_, B_, D1_]] :> 0,
                fStruct[gr_, x:OrderlessPatternSequence[A_, B_, C_] ] dF[gr_, y:OrderlessPatternSequence[A_, B_, D1_, D2_]] :> 0,
                fStruct[gr_, x:OrderlessPatternSequence[A_, B_, C_] ] dA[gr_, y:OrderlessPatternSequence[A_, B_, D1_, D2_]] :> 0,

                (* eq.97 *)
                dF[gr_, x:OrderlessPatternSequence[A1_, B1_, C1_]]
                fStruct[gr_, y1:OrderlessPatternSequence[B1_, C_, B2_] ]
                fStruct[gr_, y2:OrderlessPatternSequence[C1_, C_, C2_] ] :>
                Signature[List@y1]Signature[{B1,C,B2}] Signature[List@y2]Signature[{C1,C,C2}] Casimir2[gr@ adj]/2 dF[gr, A1, B2, C2],

                (* eq.98 *)
                (* n=1 *)
                dF[gr_, x1:OrderlessPatternSequence[A1_, B_, C1_]]
                dF[gr_, x2:OrderlessPatternSequence[A2_, B_, C2_]]
                fStruct[gr_, y:OrderlessPatternSequence[C1_, C2_, A3_] ] :>
                Signature[List@y]Signature[{C1,C2,A3}] fStruct[gr, A1, A2, A3]/2/Dim[gr@adj] d3FF[gr],
                (* n=2 *)
                dF[gr_, x1:OrderlessPatternSequence[A1_, B1_, B2_, C1_]]
                dF[gr_, x2:OrderlessPatternSequence[A2_, B1_, B2_, C2_]]
                fStruct[gr_, y:OrderlessPatternSequence[C1_, C2_, A3_] ] :>
                Signature[List@y]Signature[{C1,C2,A3}] fStruct[gr, A1, A2, A3]/3/Dim[gr@adj] d4FF[gr],

                (* eq.99 *)
                (* n=1, m=2 *)
                dF[gr_, x1:OrderlessPatternSequence[A1_, B1_, C1_]]
                dF[gr_, x2:OrderlessPatternSequence[A3_, A4_, B1_, C2_]]
                fStruct[gr_, y:OrderlessPatternSequence[C1_, C2_, A2_] ] :>
                With[{k=Unique["kA"],j=Unique["jA"]},Signature[List@y]Signature[{C1,C2,A2}] (-1/2)
                dF[gr,B1,j,k]dF[gr,A3,A4,B1,j]fStruct[gr, k, A1, A2]],

                (* n=2, m=2 *)
                dF[gr_, x1:OrderlessPatternSequence[A1_, B1_, B2_, C1_]]
                dF[gr_, x2:OrderlessPatternSequence[A3_, A4_, B1_, B2_, C2_]]
                fStruct[gr_, y:OrderlessPatternSequence[C1_, C2_, A2_] ] :>
                With[{k=Unique["kA"],j=Unique["jA"]},Signature[List@y]Signature[{C1,C2,A2}] (-1/3)
                dF[gr,B1,B2,j,k]dF[gr,A3,A4,B1,B2,j]fStruct[gr, k, A1, A2]],

                (* eq.139 *)
                dF[gr_, x1:OrderlessPatternSequence[A1_, B1_, C1_]]
                dA[gr_, x2:OrderlessPatternSequence[A2_, A3_, B1_, C1_]] :>
                Casimir2[gr@ adj]^2/6*dF[gr, A1, A2, A3],

                (* eq.105 *)
                dF[gr_, OrderlessPatternSequence[A1_, A2_, A3_]]*dF[gr_, OrderlessPatternSequence[A4_, A5_, A6_]]*
                fStruct[gr_, OrderlessPatternSequence[A1_, A4_, A9_]]*fStruct[gr_, OrderlessPatternSequence[A2_, A5_, A8_]]*
                fStruct[gr_, OrderlessPatternSequence[A3_, A6_, A7_]]*fStruct[gr_, OrderlessPatternSequence[A7_, A8_, A9_]] :> 0,


                (* !!! CHECK ME !!!  *)
                (* Non planar d3d3d3d3*f(a,..)f(a,...)  *)
                dF[gr_, OrderlessPatternSequence[A1_, A4_, A8_]]*dF[gr_, OrderlessPatternSequence[A1_, A2_, A9_]]*
                dF[gr_, OrderlessPatternSequence[A2_, A3_, A7_]]*dF[gr_, OrderlessPatternSequence[A3_, A4_, A5_]]*
                fStruct[gr_, OrderlessPatternSequence[A5_, A6_, A9_]]*fStruct[gr_, OrderlessPatternSequence[A6_, A7_, A8_]] :> 0
        }

]

(* Simplify closed loops in adjoint representation *)
ColorAdj[e_] :=
        Module[{res},
               (* First we antisymmetrize f(a,b,c) *)
               res = e /. { fStruct[gr_, A_,B_,C_] :> Signature[{A,B,C}] fStruct[gr, Sequence@@Sort[{A,B,C}]] };

               (* No del[A,B] *)
               Assert[FreeQ[res,del]];
               (* Closed f(a,b,c) loops and contractions of f(a,b,c) with dF[...] and dA[...] *)
               res = FixedPoint[SimpAdj[TraceAdj[#]]&,res];

               (* No f(a,b,c) at this step *)
               Assert[FreeQ[res,fStruct]];

               res
        ]

(* Simplify different contractions of dF[...], dA[...] with f(a,b,c)  *)
ColorInvRed[e_] :=
        Module[{res},
               res = e /. {dF[gr_, A___] :> dF[gr, Sequence@@Sort[{A}]],
                           dA[gr_, A___] :> dA[gr, Sequence@@Sort[{A}]]};


               res = res //. {
                       dF[gr_, OrderlessPatternSequence[A_, A1_, A2_] ]*dF[gr_, OrderlessPatternSequence[B_, A1_, A2_] ] :>
                         del[gr[adj],A,B]/Dim[gr[adj]]*d3FF[gr],
                       dF[gr_, OrderlessPatternSequence[A_, A1_, A2_, A3_] ]*dF[gr_, OrderlessPatternSequence[B_, A1_, A2_, A3_] ] :>
                         del[gr[adj],A,B]/Dim[gr[adj]]*d4FF[gr],
                       (* delta reduce *)
                       del[gr_[adj], x:OrderlessPatternSequence[A1_, XX_] ]*dF[gr_,B1___,XX_,C1___]:>dF[gr,B1,A1,C1],
                       del[gr_[adj], x:OrderlessPatternSequence[A1_, XX_] ]*dA[gr_,B1___,XX_,C1___]:>dA[gr,B1,A1,C1]
                           };


               res = res /. {dF[gr_, A_, B_, C_]^2 :> d3FF[gr],
                             dF[gr_, A_, B_, C_, D_]^2 :> d4FF[gr],
                             dA[gr_, A_, B_, C_, D_]^2 :> d4AA[gr],
                             (* from eq:140 *)
                             dF[gr_, x:OrderlessPatternSequence[A_, A_, B_, B_] ] :> (Casimir2[gr@ fund] - Casimir2[gr@ adj]/6) TraceNormalization[gr[fund]] Dim[gr[adj]],
                             dA[gr_, A_, B_, C_, D_]*dF[gr_, A_, B_, C_, D_] :> d4FA[gr],
                             dF[gr_, OrderlessPatternSequence[A1_, A2_, A3_, A4_] ]*dF[gr_, OrderlessPatternSequence[A1_, A2_, A5_] ]*dF[gr_, OrderlessPatternSequence[A3_, A4_, A5_] ] :> d433FFF[gr],
                             dF[gr_, OrderlessPatternSequence[A1_, A2_, A3_, A4_] ]*dF[gr_, OrderlessPatternSequence[A1_, A2_, A5_, A6_] ]*dF[gr_, OrderlessPatternSequence[A3_, A4_, A5_, A6_] ] :> d444FFF[gr]
                            };

               res
        ]



(* Based on "Group theory factors for Feynman diagrams", hep-ph/9802376
   by T. van Ritbergen, A.N. Schellekens and J.A.M. Vermaseren *)
Color[e_] :=
        Module[{res},
               res = ColorFund[Expand[e]];
               res = ColorAdj[res];
               res = ColorInvRed[res];

               res
        ]

