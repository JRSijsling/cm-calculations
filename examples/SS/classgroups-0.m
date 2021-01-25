SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields-0.m";

prec := 2000;
m1 := 0; m2 := 0; m3 := 0;
for i in [1..#data] do
    print "";
    print "Checking", i;
    n1, n2, n3 := ClassGroupData(data[i] : prec := prec, exp := 4);
    m1 := Maximum(m1, n1); m2 := Maximum(m2, n2); m3 := Maximum(m3, n3);
    print m1, m2, m3;
end for;
PrintFile("classgroup-0.m", [m1, m2, m3]);
exit;
