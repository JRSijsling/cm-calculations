/***
 *  Numerical isogenies between CM abelian varieties
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


intrinsic ExistsSmallIsogeny(P1::., P2::. : Box := 3, UpperBound := Infinity()) -> .
{Find an isogeny of small degree from two given period matrices.}

/* Deal both with small and big period matrices */
if #Rows(P1) eq #Rows(Transpose(P1)) then
    g := #Rows(P1);
    Ig := IdentityMatrix(BaseRing(P1), g);
    P1 := HorizontalJoin(P1, Ig);
end if;
if #Rows(P2) eq #Rows(Transpose(P2)) then
    g := #Rows(P2);
    Ig := IdentityMatrix(BaseRing(P2), g);
    P2 := HorizontalJoin(P2, Ig);
end if;

/* Find all homomorphisms */
HomRep := GeometricHomomorphismRepresentationCC(P1, P2);
if #HomRep eq 0 then
    return false, 0;
end if;

/* Naively minimize determinant involved */
test := false;
Rs := [ tup[2] : tup in HomRep ];
D := [-Box..Box]; CP := CartesianPower(D, #Rs);
det0 := UpperBound;
for tup in CP do
    R := &+[ tup[i]*Rs[i] : i in [1..#Rs] ];
    det := Abs(Determinant(R));
    if det ne 0 and det lt det0 then
        det0 := det; R0 := R;
        test := true;
    end if;
end for;
if not test then
    return false, 0;
end if;
return true, R0;

end intrinsic;


intrinsic AllSmallIsogenies(P1::., P2::. : Box := 3, UpperBound := Infinity()) -> .
{Find all isogenies of small degree from two given period matrices.}

/* Deal both with small and big period matrices */
if #Rows(P1) eq #Rows(Transpose(P1)) then
    g := #Rows(P1);
    Ig := IdentityMatrix(BaseRing(P1), g);
    P1 := HorizontalJoin(P1, Ig);
end if;
if #Rows(P2) eq #Rows(Transpose(P2)) then
    g := #Rows(P2);
    Ig := IdentityMatrix(BaseRing(P2), g);
    P2 := HorizontalJoin(P2, Ig);
end if;

/* Find all homomorphisms */
HomRep := GeometricHomomorphismRepresentationCC(P1, P2);
if #HomRep eq 0 then
    return false, 0;
end if;

/* Naively minimize determinant involved */
test := false;
Rs := [ tup[2] : tup in HomRep ];
D := [-Box..Box]; CP := CartesianPower(D, #Rs);
det0 := UpperBound;
for tup in CP do
    R := &+[ tup[i]*Rs[i] : i in [1..#Rs] ];
    det := Abs(Determinant(R));
    if det ne 0 and det lt det0 then
        det0 := det; R0s := [ R ];
        test := true;
    elif det eq det0 then
        Append(~R0s, R);
    end if;
end for;

if not test then
    return false, 0;
end if;
return true, R0s;

end intrinsic;
