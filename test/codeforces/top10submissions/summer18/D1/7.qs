namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit, b : Int[]) : () {
        body {
            let n = Length(b);
            for (i in 0..(n-1)) {
                if (b[i] == 1) {
                    CNOT(x[i], y);
                }
            }
        }
    }

    // operation Simulate(n : Int, k : Int) : Int[] {
    //     body {
    //         mutable measurment = new Int[n + 1];

    //         mutable b = new Int[n];
    //         for (i in 0..(n-1)) {
    //             if (i % 3 == 0) {
    //                 set b[i] = 1;
    //             }
    //         }

    //         using (register = Qubit[n+1]) {
    //             for (i in 0..(n-1)) {
    //                 if (i % 3 == 0) {
    //                     X(register[i]);
    //                 }
    //             }

    //             Solve(register[0..(n-1)], register[n], b);

    //             for (i in 0..n) {
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
