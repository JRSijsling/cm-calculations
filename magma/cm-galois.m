/***
 *  Basic CM functionality, via splitting field
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

declare attributes FldNum : embL;
import "cm-numerical.m": Extrafy;

/* In these functions a CM type is a bunch of roots of the defining polynomial in the splitting field */


procedure InitializeEmbedding(K)
/* The function creates an embedding from K into its Galois closure once and for all */
if assigned K`embL then
    return;
end if;

/* Define embedding */
f := DefiningPolynomial(K);
L := SplittingFieldExtra(f);
r := Roots(f, L)[1][1];
hKL := hom< K -> L | r >;

/* Recover the involution numerically */
genCC := EmbedExtra(L.1); CC := Parent(genCC);
G, _, phiG := AutomorphismGroupPari(L);
auts := [ phiG(g) : g in G ];
rts := [ aut(L.1) : aut in auts ];
for rt in rts do
    geninvCC := EmbedExtra(rt);
    if Abs(geninvCC - ComplexConjugate(genCC)) lt CC`epscomp then
        rt0 := rt;
        break;
    end if;
end for;
invL := hom< L -> L | rt0 >;

/* Check and return */
assert invL(L.1) ne L.1;
assert invL(invL(L.1)) eq L.1;
embL := [* L, hKL, invL, phiG *];
K`embL := embL;
return;
end procedure;


function IsPrimitiveCMTypeGalois(Phi, K)
//{Checks if Phi is primitive.}
InitializeEmbedding(K); L, hKL, invL := Explode(K`embL);
tups := Subfields(K);
tups := [ tup : tup in tups | not Degree(tup[1]) eq Degree(K) ];
tups := [ <Extrafy(tup[1]), tup[2]> : tup in tups ];
tups := [ tup : tup in tups | IsCMField(tup[1]) ];
for tup in tups do
    // M is the subfield, r its generator as an element of K
    M, hMK := Explode(tup); r := hMK(M.1);
    iotas := [ hom< K -> L | rt > : rt in Phi ];
    embs := [ iota(r) : iota in iotas ];
    // Need 2 deg (M) embeddings in complex conjugate pairs
    if #Set(embs) eq (Degree(M) div 2) then
        embs := embs cat [ invL(emb) : emb in embs ];
        if #Set(embs) eq Degree(M) then
            return false;
        end if;
    end if;
end for;
return true;
end function;


function AllCMTypesGalois(K : Primitive := true)
/* Returns all CM types of the field K as images of the generator of this field. */

/* Determine all roots */
InitializeEmbedding(K); L, hKL, invL := Explode(K`embL);
rts := [ tup[1] : tup in Roots(DefiningPolynomial(K), L) ];
assert #rts eq Degree(K);

/* Group into pairs under complex conjugation */
pairs := [ ];
while #rts ne 0 do
    rt := rts[1]; Remove(~rts, 1);
    invrt := invL(rt);
    for j in [1..#rts] do
        if rts[j] eq invrt then
            j0 := j;
            break;
        end if;
    end for;
    Remove(~rts, j0);
    pair := [ rt, invrt ];
    Append(~pairs, pair);
end while;

/* Naively generate all types */
CP := CartesianPower([1, 2], #pairs);
Phis := [ { pairs[i][tup[i]] : i in [1..#pairs] } : tup in CP ];
if Primitive then
    Phis := [ Phi : Phi in Phis | IsPrimitiveCMTypeGalois(Phi, K) ];
end if;
return Phis;
end function;


function IsEquivalentCMTypeGalois(Phi1, Phi2, K)
/* Tests if two CM types are equivalent in the sense of Streng, that is, up to an automorphism of the field */
InitializeEmbedding(K); L, hKL, invL := Explode(K`embL);
embs1 := [ hom< K -> L | rt > : rt in Phi1 ];
G, _, phiG := AutomorphismGroupPari(K);
for g in G do
    sigma := phiG(g);
    sigmaPhi1 := { emb1(sigma(K.1)) : emb1 in embs1 };
    if sigmaPhi1 eq Phi2 then
        return true;
    end if;
end for;
return false;
end function;


function AllCMTypesUpToEquivalenceGalois(K : Primitive := true)
/* Returns all CM type up to Streng's equivalence, that is, up to an automorphism of the field */
InitializeEmbedding(K); L, hKL, invL := Explode(K`embL);
Phis := AllCMTypesGalois(K : Primitive := Primitive);
doubles := [ ];
for i in [1..#Phis] do
    for j in [(i + 1)..#Phis] do
        if IsEquivalentCMTypeGalois(Phis[i], Phis[j], K) then
            Append(~doubles, j);
        end if;
    end for;
end for;
Phis := [ Phis[i] : i in [1..#Phis] | not i in doubles ];
return Phis;
end function;


function IsCMTypeGalois(Phi, K)
/* Tests if the given embeddings numerically furnish a CM type. */
InitializeEmbedding(K); L, hKL, invL := Explode(K`embL);
return #(&join[ { invL(rt), rt } : rt in Phi ]) eq Degree(K);
end function;
