def uniform_entangle[n:!ℕ](bits:(!𝔹^n)^4) mfree {
    anc:=0:uint[2];
    for j in [0..2){ anc[j]:=H(anc[j]); }
    qs:=vector(n,false:𝔹);

    for i in [0..n-1] {
        for a in [0..3] {
            if anc == a && bits[a][i] {
                qs[i] := X(qs[i]);
            }
        }            
    }
    return (anc, qs);
}

def solve[n:!ℕ](bits:(!𝔹^n)^4) {
    (anc, qs) := uniform_entangle(bits);
    result := dup(qs);
    reverse(uniform_entangle[n])(bits, (anc, qs));
    return result;
}

// def solve[n:!ℕ](bits:(!𝔹^n)^4) {
//     anc:=0:int[2];
//     for j in [0..2){ anc[j]:=H(anc[j]); }
// 	qs:=vector(n,false:𝔹);

//     for i in [0..n-1] {
//         for a in [0..3] {
//             if anc == a && bits[a][i] {
//                 qs[i] := X(qs[i]);
//             }
//         }            
//     }

//     for i in [0..n-1] {
//         for a in [0..3] {
//             if bits[a] == qs {
//                 anc -= a;
//             }
//         }            
//     }

//     measure(anc);
//     return qs;
// }
