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

G := Gs[1];
Z := Center(G);
invs := [ z : z in Z | Order(z) eq 2 ];
assert #invs eq 1;
inv := invs[1];

H := Stabilizer(G, 1);
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

print LeftCosets(G, H);
