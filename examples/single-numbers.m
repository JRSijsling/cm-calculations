SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

prec := 2000;

R<x> := PolynomialRing(Rationals());
f := x^6 + 10*x^4 + 21*x^2 + 4;

taushyp, tausnonhyp := EnumerationUpToGalois(f : exp := 4, prec := prec);
print #taushyp, #tausnonhyp;
