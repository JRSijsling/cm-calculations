SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields.m";

prec := 2000;
for i in [1..#data] do
    if i mod 24 eq 11 then
        print "";
        print "Checking", i;
        try
            taushyp, tausnonhyp := EnumerationUpToGalois(data[i] : prec := prec, exp := 2);
            if #taushyp ne 0 then
                PrintFile("results.m", [i, #taushyp, #tausnonhyp]);
            elif (#taushyp eq 0) and (#tausnonhyp eq 0) then
                PrintFile("results-none.m", i);
            end if;
        catch e
            PrintFile("results-fail.m", i);
        end try;
    end if;
end for;
exit;
