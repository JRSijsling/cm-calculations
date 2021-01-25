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
print #Gs;

sigma := S ! (1,2,3,4,5,6);
tau := S ! (2,6)(3,5);
G := sub< S | sigma, tau >;
Z := Center(G);
invs := [ z : z in Z | Order(z) eq 2 ];
assert #invs eq 1;
inv := invs[1];
assert inv eq sigma^3;

H := Stabilizer(G, 1);
print H;
print MinimalOvergroups(G, H);

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
print Phis;
print #Phis;

for i1 in [1..#Phis] do
    for i2 in [1..#Phis] do
        Phi1 := Phis[i1]; Phi2 := Phis[i2];
        for g in G do
            rel := false;
            PhiNew := { { g*elt : elt in pair } : pair in Phi1 };
            if PhiNew eq Phi2 then
                rel := true;
                break;
            end if;
        end for;
        if rel then
            print i1, i2;
        end if;
    end for;
end for;
