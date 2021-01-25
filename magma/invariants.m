/***
 *  Recognizing invariants
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


// TODO: UPDATE

intrinsic FindSingleInvariantsFromPolynomialG3(f::RngUPolElt : prec := 4000, HypAndNonhyp := true) -> .
{Finds a sample set of invariants.}

taus, tausnonhyp := FindHyperellipticCMFromPolynomialG3(f : prec := prec);
if HypAndNonhyp then
    taus cat:= tausnonhyp;
end if;
if #taus eq 0 then return 0; end if;

F := RationalsExtra(prec);
invs := AlgebraizedInvariants(taus[1], F : Base := false);
return invs;

end intrinsic;


intrinsic FindAllInvariantsFromPolynomialG3(f::RngUPolElt : prec := 4000, HypAndNonhyp := true) -> .
{Finds all invariants.}

taus, tausnonhyp := FindHyperellipticCMFromPolynomialG3(f : prec := prec);
if HypAndNonhyp then
    taus cat:= tausnonhyp;
end if;
if #taus eq 0 then return 0; end if;

F := RationalsExtra(prec);
invss := [* *];
for tau in taus do
    invs := AlgebraizedInvariants(tau, F : Base := false);
    Append(~invss, invs);
end for;
return invss;

end intrinsic;
