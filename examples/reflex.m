SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 1);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "SS/fields.m";

prec := 1200;
for i in [1..#data] do
    print "Checking", i;
    datum := data[i];

    F := RationalsExtra(prec);
    R<x> := PolynomialRing(F);
    f := R ! datum[2];
    K := NumberFieldExtra(f);
    Phis := AllCMTypes(K : Galois := true, Primitive := true);

    for PhiK in Phis do
        Q := ClassGroupQuotient(PhiK, K);
        if Exponent(Q) gt 2 then
            print Q;
        end if;
    end for;
end for;
