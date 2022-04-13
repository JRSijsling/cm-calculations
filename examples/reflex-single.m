SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 1);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "C6/fields.m";

prec := 1200;
F := RationalsExtra(prec);
R<x> := PolynomialRing(F);
f := data[12][2];
K := NumberFieldExtra(f);
Phis := AllCMTypes(K : Galois := true, Primitive := true);
PhiK := Phis[1];

Q, G, H, Krinfo, Kinfo := ClassGroupQuotient(PhiK, K);
ClKr, phiClKr := Explode(Krinfo);
ClK, phiClK := Explode(Kinfo);

