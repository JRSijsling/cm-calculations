/***
 *  Recognizing invariants
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "conic_123.m": Genus3ConicAndQuartic123;
import "g2twists.m": ClebschMestreConicAndCubic;

// TODO: UPDATE


intrinsic InterestingConicFromPolynomialG3(f::RngUPolElt : prec := 4000) -> .
{Checks whether one of the curves with maximal CM by the polynomial f has a Mestre conic without a point. We skip cases where the standard conic degenerates.}

taus := FindHyperellipticCMFromPolynomialG3(f : prec := prec);
if #taus eq 0 then return false; end if;

F := RationalsExtra(prec);
invs := AlgebraizedInvariants(taus[1], F : Base := false);
R, C, Q := Genus3ConicAndQuartic123(invs);
if R eq 0 then return false; end if;

R := Parent(C);
PP2 := ProjectiveSpace(R);
C := Conic(PP2, C);
return not HasRationalPoint(C);

end intrinsic;


intrinsic InterestingConicFromPolynomialG2(f::RngUPolElt : prec := 4000) -> .
{Checks whether one of the curves with maximal CM by the polynomial f has a Mestre conic without a point. We skip cases where the standard conic degenerates.}

taus := FindHyperellipticCMFromPolynomialG2(f : prec := prec);
if #taus eq 0 then return false; end if;

F := RationalsExtra(prec);
invs := AlgebraizedInvariants(taus[1], F : Base := false);
g2s := IgusaToG2Invariants(invs);
C := ClebschMestreConicAndCubic(g2s);

R := Parent(C);
PP2 := ProjectiveSpace(R);
C := Conic(PP2, C);
if Discriminant(C) eq 0 then return false; end if;
return not HasRationalPoint(C);

end intrinsic;
