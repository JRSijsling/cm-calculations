SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields.m";

prec := 2000;
for i in [10054, 10067, 10038, 10062, 10047, 10027, 10028, 10053, 10063, 10058, 10046, 10066, 10061, 10031] do
    print "";
    print "Checking", i;
    try
        taushyp, tausnonhyp := EnumerationUpToGalois(data[i] : prec := prec, precred := 1000, prectau := 200, exp := 2);
        if #taushyp ne 0 then
            PrintFile("results.m", [i, #taushyp, #tausnonhyp]);
        elif (#taushyp eq 0) and (#tausnonhyp eq 0) then
            PrintFile("results-none.m", i);
        end if;
    catch e
        PrintFile("results-fail.m", i);
    end try;
end for;
exit;
