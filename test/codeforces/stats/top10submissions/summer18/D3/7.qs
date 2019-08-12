namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : () {
        body {
            for (i in 0..1) {
                for (j in (i + 1)..2) {
                    (Controlled X)([x[i]; x[j]], y);
                }
            }
        }
    }

    // operation Simulate(n : Int, k : Int) : Int[] {
    //     body {
    //         mutable measurment = new Int[4];

    //         using (register = Qubit[4]) {
    //             let q = register[0..2];
    //             if (n % 2 == 1) { X(q[0]); }
    //             if ((n / 2) % 2 == 1) { X(q[1]); }
    //             if ((n / 4) % 2 == 1) { X(q[2]); }

    //             Solve(q, register[3]);

    //             for (i in 0..3) {
    //                 if (M(register[i]) == One) {
    //                     set measurment[i] = 1;
    //                 }
    //             }
    //             ResetAll(register);
    //         }
    //         return measurment;
    //     } 
    // }
}
