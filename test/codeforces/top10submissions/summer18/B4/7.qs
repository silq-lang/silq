namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;

    operation Solve (x : Qubit[]) : Int {
        body {
            H(x[1]);
            CNOT(x[0], x[1]);
            H(x[0]);
            mutable ans = new Bool[2];
            if (M(x[0]) == One) { set ans[0] = true; }
            if (M(x[1]) == One) { set ans[1] = true; }
            if (ans[0] && ans[1]) {return 0; }
            if (ans[0] && !ans[1]) {return 2; }
            if (!ans[0] && ans[1]) {return 1; }
            return 3;
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
