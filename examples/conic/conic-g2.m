SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 1);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "datag2.m";

prec := 300;
for i in [1..#data] do
    print "Checking", i;
    datum := data[i]; f := R ! datum[2];
    if #TorsionSubgroup(UnitGroup(NumberField(f))) ne 2 then continue; end if;
    test := InterestingConicFromPolynomialG2(f : prec := prec);
    /*
    try
        test := InterestingConicFromPolynomialG2(f : prec := prec);
        done := true;
    catch err
        print "error";
        test := false;
    end try;
    */
    if test then
        print datum;
    end if;
end for;
