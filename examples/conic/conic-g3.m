SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "dataallcl4.m";

prec := 1000;
for i in [1..#data] do
    print "Checking", i;
    datum := data[i]; f := R ! datum[2];
    if #TorsionSubgroup(UnitGroup(NumberField(f))) ne 2 then continue; end if;
    try
        test := InterestingConicFromPolynomialG3(f : prec := prec);
        done := true;
    catch err
        print "error";
        test := false;
    end try;
    if test then
        print datum;
    end if;
end for;
