AppendTo[$Path, "../../RGBetaArbG"];
<< RGBeta`;

ResetModel[]
AddGaugeGroupArb[g, G];
AddFermion[qL, GaugeRep -> {G[fund]}, FlavorIndices -> {fgen}];
AddFermion[qR, GaugeRep -> {Bar@G[fund]}, FlavorIndices -> {fgen}];
Dim[fgen] = nf;
Print["Couplings: ", Keys[$couplings]];

bt = BetaTerm[g, 4];

Print[bt]
