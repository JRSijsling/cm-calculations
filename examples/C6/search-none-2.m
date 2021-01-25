SetSeed(1);
SetVerbose("EndoFind", 0);
SetVerbose("CurveRec", 0);
SetVerbose("CMExp", 2);
SetClassGroupBounds("GRH");

R<x> := PolynomialRing(Rationals());
load "fields.m";

prec := 2000;
for i in [8995, 9236, 9947, 9560, 9608, 9369, 8704, 9655, 9999, 9896, 9920, 9968, 8499, 8831, 9878, 9736, 8811, 9335, 10055, 9963] do
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
end for;
exit;
