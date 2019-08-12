namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[]) : Int {
        body {
            let n = Length(x);
            mutable sum = 0;
            for (i in 0..(n-1)) {
                if (M(x[i]) == One) {
                    set sum = sum + 1;
                }
            }
            if (sum == 1) {
                return 1;
            }
            return 0;
        }
    }

    // operation Simulate(n : Int) : Int {
    //     body {
    //         mutable measurment = 0;
    //         using (register = Qubit[n]) {
    //             let q = register;
    //             if (n % 2 == 1) {
    //                 X(q[n-1]);
    //             } else {
    //                 ApplyToEach(X(_), q);
    //             }
    //             set measurment = Solve(q);
    //             ResetAll(register);
    //         }
    //         return measurment;
    //     } 
    // }
}
