namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation fun(x : Qubit[], y : Qubit) : () {
    //     body {
    //         CNOT(x[0], y);
    //     }
    // }

    // operation one(x : Qubit[], y : Qubit) : () {
    //     body {
    //         ApplyToEach(CNOT(_, y), x);
    //     }
    // }

    operation Solve (n : Int, f : ((Qubit[], Qubit) => ())) : Int[] {
        body {
            mutable res = new Int[n];
            using (reg = Qubit[n + 1]) {
                let x = reg[0..(n-1)];
                let y = reg[n];

                X(y); H(y);
                for (i in 0..(n-1)) { H(x[i]); }
                f(x, y);
                for (i in 0..(n-1)) { H(x[i]); }

                for (i in 0..(n-1)) {
                    if (M(x[i]) == One) {
                        set res[i] = 1;
                    }
                }
                ResetAll(reg);
            }
            return res;
        }
    }

    // operation Simulate(n : Int) : Int[] {
    //     body {
    //         return Solve(n, fun);
    //     } 
    // }
}
