/***
 *  Basic CM functionality, both types
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

declare verbose CMExp, 2;

import "cm-numerical.m": IsPrimitiveCMTypeNumerical, AllCMTypesNumerical, IsEquivalentCMTypeNumerical, AllCMTypesUpToEquivalenceNumerical, IsCMTypeNumerical;
import "cm-galois.m": IsPrimitiveCMTypeGalois, AllCMTypesGalois, IsEquivalentCMTypeGalois, AllCMTypesUpToEquivalenceGalois, IsCMTypeGalois;


intrinsic IsCMField(K::Fld) -> .
{Tests if K is a CM field. If so, also returns the totally real subfield K0 as well as the corresponding involution.}
dK := Degree(K);
if not dK mod 2 eq 0 then return false, 0, 0; end if;
if not #InfinitePlaces(K) eq (dK div 2) then return false, 0, 0; end if;
/* Special case of degree 2 */
if dK eq 2 then
    G, _, phiG := AutomorphismGroupPari(K);
    return true, < Rationals(), hom< Rationals() -> K | > >, phiG(G.1);
end if;

/* Identify involution numerically */
genCC := EmbedExtra(K.1);
test, invr := AlgebraizeElementExtra(ComplexConjugate(genCC), K);
if not test then
    return false, 0, 0;
end if;
invK := hom< K -> K | invr >;

/* Take fixed field and check that it is totally real */
K0, hK0K := FixedFieldExtra(K, [ invK ]); ninfsK0 := #InfinitePlaces(K);
if not #InfinitePlaces(K0) eq (dK div 2) then return false, 0, 0; end if;

/* Check and return */
assert IsTotallyReal(K0);
assert invK(invK(K.1)) eq K.1;
assert invK(hK0K(K0.1)) eq hK0K(K0.1);
tup := [* K0, hK0K *];
return true, tup, invK;

end intrinsic;


intrinsic IsPrimitiveCMType(Phi::SetEnum, K::Fld : Galois := false) -> .
{Checks if Phi is primitive.}

/* Dichotomy depending on flag */
if not Galois then
    return IsPrimitiveCMTypeNumerical(Phi, K);
end if;
return IsPrimitiveCMTypeGalois(Phi, K);

end intrinsic;


intrinsic AllCMTypes(K::Fld : Galois := false, Primitive := false) -> .
{Returns all CM types of the field K as images of the generator of this field.}

/* Dichotomy depending on flag */
if not Galois then
    return AllCMTypesNumerical(K : Primitive := Primitive);
end if;
return AllCMTypesGalois(K : Primitive := Primitive);

end intrinsic;


intrinsic IsEquivalentCMType(Phi1::SetEnum, Phi2::SetEnum, K::Fld : Galois := false) -> .
{Tests if two CM types are equivalent.}

/* Dichotomy depending on flag */
if not Galois then
    return IsEquivalentCMTypeNumerical(Phi1, Phi2, K);
end if;
return IsEquivalentCMTypeGalois(Phi1, Phi2, K);

end intrinsic;


intrinsic AllCMTypesUpToEquivalence(K::Fld : Galois := false, Primitive := true) -> .
{Returns all CM type up to equivalence.}

/* Dichotomy depending on flag */
if not Galois then
    return AllCMTypesUpToEquivalenceNumerical(K : Primitive := Primitive);
end if;
return AllCMTypesUpToEquivalenceGalois(K : Primitive := Primitive);

end intrinsic;


intrinsic IsCMType(Phi::SetEnum, K::Fld : Galois := false) -> .
{Tests if the given embeddings correspond to a CM type.}

/* Dichotomy depending on flag */
if not Galois then
    return IsCMTypeNumerical(Phi, K);
end if;
return IsCMTypeGalois(Phi, K);

end intrinsic;
