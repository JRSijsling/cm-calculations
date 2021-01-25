SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields.m";

prec := 2000;
for i in [9528] do
    print "";
    print "Checking", i;
    taushyp, tausnonhyp := EnumerationUpToGalois(data[i] : prec := prec, exp := 2);
end for;
exit;
