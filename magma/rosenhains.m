/***
 *  Determination of Rosenhain invariants
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


// TODO: UPDATE

intrinsic FindSingleRosenhainsFromPolynomial(f::RngUPolElt : prec := 4000) -> .
{Finds a sample set of Rosenhain invariants.}

taushyp := FindHyperellipticCMFromPolynomialG3(f : prec := prec);
if #taushyp eq 0 then return 0; end if;

F := RationalsExtra(prec);
rosensCC := RosenhainInvariantsBILV(taushyp[1]);
K, rosens := NumberFieldExtra(rosensCC, F);
return rosens;

end intrinsic;


intrinsic FindAllRosenhainsFromPolynomialG3(f::RngUPolElt : prec := 4000) -> .
{Finds all Rosenhain invariants.}

taushyp := FindHyperellipticCMFromPolynomialG3(f : prec := prec);
if #taushyp eq 0 then return [ ]; end if;

F := RationalsExtra(prec);
rosenss := [* *];
for tau in taushyp do
    rosensCC := RosenhainInvariantsBILV(tau);
    K, rosens := NumberFieldExtra(rosensCC, F);
    Append(~rosenss, rosens);
end for;
return rosenss;

end intrinsic;
