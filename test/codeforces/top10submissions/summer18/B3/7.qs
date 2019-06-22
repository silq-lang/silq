namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[]) : Int {
        body {
            H(x[0]);
            H(x[1]);
            mutable ans = 0;
            if (M(x[0]) == One) { set ans = ans + 2; }
            if (M(x[1]) == One) { set ans = ans + 1; }
            return ans;
        }
    }

    // operation Simulate(n : Int) : Int {
    //     body {
    //         mutable measurment = 0;
    //         using (register = Qubit[2]) {
    //             let q = register;
    //             if (n % 2 == 1) {
    //                 X(q[0]);
    //             }
    //             if ((n / 2) % 2 == 1) {
    //                 X(q[1]);
    //             }
    //             ApplyToEach(H(_), q);
    //             set measurment = Solve(q);
    //             ResetAll(register);
    //         }
    //         return measurment;
    //     } 
    // }
}
