/***
 *  Basic CM functionality, via CC
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

/* In these functions a CM type is a bunch of roots of the defining polynomial in CC */


function Extrafy(K)
/* Make a field into a NumberFieldExtra */
F := BaseRing(K);
K`base := F`base;
K`base_gen := F`base_gen;
K`CC := F`CC;
K`iota := InfinitePlacesExtra(K)[1];
return K;
end function;


function NumberOfDistinctEntriesCC(L)
/* Returns the number of numerically distinct entries in list of complex numbers */
CC := Parent(L[1]);
L0 := [ ];
for x in L do
    if #L0 eq 0 then
        Append(~L0, x);
    else
        min := Minimum([ Abs(x - x0) : x0 in L0 ]);
        if min gt CC`epscomp then
            Append(~L0, x);
        end if;
    end if;
end for;
return #L0;
end function;


function IsSameUpToReorderingCC(L1, L2)
/* Tests if two lists of complex numbers are numerically the same up to reordering */
if #L1 ne #L2 then return false; elif #L1 eq 0 then return true; end if;
x1 := L1[1]; CC := Parent(x1);
min, ind := Minimum([ Abs(y - x1) : y in L2 ]);
if not min lt CC`epscomp then
    return false;
end if;
return IsSameUpToReorderingCC(Remove(L1, 1), Remove(L2, ind));
end function;


function IsPrimitiveCMTypeNumerical(Phi, K)
/* Checks if Phi is primitive. */

/* Find CM subfields */
tups := Subfields(K);
tups := [ tup : tup in tups | not Degree(tup[1]) eq Degree(K) ];
tups := [ <Extrafy(tup[1]), tup[2]> : tup in tups ];
tups := [ tup : tup in tups | IsCMField(tup[1]) ];
for tup in tups do
    L, hLK := Explode(tup); r := hLK(L.1);
    embs := [ EmbedExtra(r : iota := iota) : iota in Phi ];
    /* The type is not primitive if we get 2 deg (L) embeddings in complex conjugate pairs */
    if NumberOfDistinctEntriesCC(embs) eq (Degree(L) div 2) then
        embs cat:= [ ComplexConjugate(emb) : emb in embs ];
        if NumberOfDistinctEntriesCC(embs) eq Degree(L) then
            return false;
        end if;
    end if;
end for;
return true;
end function;


function AllCMTypesNumerical(K : Primitive := true)
/* Returns all CM types of the field K as images of the generator of this field. */

/* Take places with positive image */
infs := [ inf : inf in InfinitePlacesExtra(K) | Im(inf) gt 0 ];
CP := CartesianPower([-1, 1], #infs);
Phis := [ ];

/* Naively generate all types */
for tup in CP do
    Phi := [ ];
    for i := 1 to #tup do
        if tup[i] eq 1 then
            Append(~Phi, infs[i]);
        else
            Append(~Phi, ComplexConjugate(infs[i]));
        end if;
    end for;
    Append(~Phis, Set(Phi));
end for;
if Primitive then
    Phis := [ Phi : Phi in Phis | IsPrimitiveCMType(Phi, K) ];
end if;
return Phis;
end function;


function IsEquivalentCMTypeNumerical(Phi1, Phi2, K)
/* Tests if two CM types are equivalent in the sense of Streng, that is, up to an automorphism of the field */
G, _, phiG := AutomorphismGroupPari(K);
Phi1 := [ iota : iota in Phi1 ]; Phi2 := [ iota : iota in Phi2 ];
CC := Parent(Phi1[1]);
for g in G do
    sigma := phiG(g);
    sigmaPhi1 := [ EmbedExtra(sigma(K.1) : iota := phi1) : phi1 in Phi1 ];
    if IsSameUpToReorderingCC(sigmaPhi1, Phi2) then
        return true;
    end if;
end for;
return false;
end function;


function AllCMTypesUpToEquivalenceNumerical(K : Primitive := true)
/* Returns all CM type up to Streng's equivalence, that is, up to an automorphism of the field */
Phis := AllCMTypes(K : Primitive := Primitive);
doubles := [ ];
for i in [1..#Phis] do
    for j in [(i + 1)..#Phis] do
        if IsEquivalentCMType(Phis[i], Phis[j], K) then
            Append(~doubles, j);
        end if;
    end for;
end for;
Phis := [ Phis[i] : i in [1..#Phis] | not i in doubles ];
return Phis;
end function;


function IsCMTypeNumerical(Phi, K)
/* Tests if the given embeddings numerically furnish a CM type. */
Phi := [ iota : iota in Phi ];
CC := Parent(Phi[1]);
for i in [1..#Phi] do
    for j in [(i+1)..#Phi] do
        if Abs(ComplexConjugate(Phi[i] - Phi[j])) lt CC`epscomp then
            return false;
        end if;
    end for;
end for;
return true;
end function;
