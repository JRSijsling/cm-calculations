SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields-1.m";

prec := 2000;
for i in [1..#data] do
    print "";
    print "Checking", i;
    try
        taushyp, tausnonhyp := EnumerationUpToGalois(data[i] : prec := prec, exp := 4);
        if #taushyp ne 0 then
            PrintFile("results-1.m", [i, #taushyp, #tausnonhyp]);
        elif (#taushyp eq 0) and (#tausnonhyp eq 0) then
            PrintFile("results-1-none.m", [i, #taushyp, #tausnonhyp]);
        end if;
    catch e
        PrintFile("results-1-fail.m", i);
    end try;
end for;
exit;
