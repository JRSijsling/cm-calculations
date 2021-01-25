SetSeed(1);

S := Sym(6);
Gs := [ rec`subgroup : rec in Subgroups(S) ];
Gs := [ G : G in Gs | IsTransitive(G) ];
Gs := [ G : G in Gs | #Center(G) mod 2 eq 0 ];

GsNew := [ ];
for G in Gs do
    H := Stabilizer(G, 1);
    Z := Center(G);
    for inv in [ z : z in Z | Order(z) eq 2 ] do
        H0 := sub< G | H, inv >;
        C0 := Core(G, H0);
        if IsAbelian(C0) and Exponent(C0) eq 2 then
            Append(~GsNew, G);
            continue;
        end if;
    end for;
end for;
Gs := GsNew;
G := Gs[3];
print #G;

Z := Center(G);
invs := [ z : z in Z | Order(z) eq 2 ];
assert #invs eq 1;
inv := invs[1];

H := Stabilizer(G, 1);


function LeftCosets(G, H)

Cs := [ ];
for g in G do
    new := true;
    for i in [1..#Cs] do
        if g^(-1)*Random(Cs[i]) in H then
            new := false;
            Include(~Cs[i], g);
            break;
        end if;
    end for;
    if new then
        Append(~Cs, { g });
    end if;
end for;
return Cs;

end function;


function LeftCoset(g, H)

return { g*h : h in H };

end function;


function DivideIntoLeftCosets(S, H)

assert &and{ s*h in S : s in S, h in H };
cosets := { };
while #S ne 0 do
    s := Random(S);
    coset := { };
    for h in H do
        sh := s*h;
        Include(~coset, sh);
        Exclude(~S, sh);
    end for;
    Include(~cosets, coset);
end while;
return cosets;

end function;


function LeftCosetPairs(G, H, inv);

Cs := LeftCosets(G, H);
pairs := [ ];
for i in [1..#Cs] do
    for j in [i+1..#Cs] do
        if inv*Random(Cs[i]) in Cs[j] then
            Append(~pairs, [ Cs[i], Cs[j] ]);
        end if;
    end for;
end for;
return pairs;

end function;


pairs := LeftCosetPairs(G, H, inv);
CP := CartesianPower([1,2], 3);
Phis := [ ];
for tup in CP do
    Phi := { pairs[i][tup[i]] : i in [1..#tup] };
    Append(~Phis, Phi);
end for;

PhiK := Phis[1];
PhiL := &join(PhiK);
PhiLinv := { alpha^(-1) : alpha in PhiL };

Hr := [ g : g in G | &and[ g*alpha in PhiL : alpha in PhiL ] ];
Hr := sub< G | Hr >;
assert #Hr eq 3;

PhiKr := DivideIntoLeftCosets(PhiLinv, Hr);
assert #PhiK eq 3;
assert #PhiKr eq 4;

allcosets := LeftCosets(G, H);
function LeftCosetNumber(C, Cs);
for i in [1..#Cs] do
    if C eq Cs[i] then
        return i;
    end if;
end for;
end function;

counter := 0;
while counter lt 10^3 do
    counter +:= 1;
    alphas := { Random(S) : S in PhiK };
    alphars := { Random(S) : S in PhiKr };
    cosets1 := [ LeftCoset(alphar*alpha, H) : alphar in alphars, alpha in alphas ];
    cosets1 := [ LeftCosetNumber(coset, allcosets) : coset in cosets1 ];
    cosets1 := Sort(cosets1);
    alphas := { Random(S) : S in PhiK };
    alphars := { Random(S) : S in PhiKr };
    cosets2 := [ LeftCoset(alphar*alpha, H) : alphar in alphars, alpha in alphas ];
    cosets2 := [ LeftCosetNumber(coset, allcosets) : coset in cosets2 ];
    cosets2 := Sort(cosets2);
    assert cosets1 eq cosets2;
end while;

print cosets1;
print LeftCosetNumber(LeftCoset(Id(G), H), allcosets);
print LeftCosetNumber(LeftCoset(inv, H), allcosets);
