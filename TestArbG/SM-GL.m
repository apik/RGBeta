AppendTo[$Path, "../../RGBetaArbG"];
<< RGBeta`;

ResetModel[];
AddGaugeGroup[g2, SU2L, SU[2]];
AddGaugeGroupArb[g3, Gc];
AddFermion[q, FlavorIndices -> {gen},
           GaugeRep -> {SU2L[fund], Gc[fund]}];
AddFermion[u, FlavorIndices -> {gen},
           GaugeRep -> {Bar@Gc[fund]}];
AddFermion[d, FlavorIndices -> {gen},
           GaugeRep -> {Bar@Gc[fund]}];
Dim[gen] = ng;
AddScalar[H, GaugeRep -> {SU2L[fund]}];

AddYukawa[yt, {H, q, u},
          GroupInvariant -> (del[Gc@fund, #2, #3] eps[SU2L@fund, #2, #1] &),
          CouplingIndices -> ({gen[#2], gen[#3]} &),
          Chirality -> Right];
Bar[yu] = yt;

AddQuartic[lam, {Bar@H, H, Bar@H, H},
           GroupInvariant -> ((del[SU2L@fund, #1, #2] del[SU2L@fund, #3, #4]) &)];

Print["Couplings: ", Keys[$couplings]];


bYt = Finalize[BetaTerm[yt,3]]/. {g2->0, (Bar|Trans|Tr) -> Identity, Dot -> Times, ng -> nf/2};
bG  = BetaTerm[g3,4]/. {g2->0, (Bar|Trans|Tr) -> Identity, Dot -> Times, ng -> nf/2};


Print["Yukawa 3-loop:\n", bYt];

Print["Gauge  4-loop:\n", bG];

Exit[]

