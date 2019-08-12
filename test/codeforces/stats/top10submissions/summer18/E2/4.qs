namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    // operation Set (desired: Result, q1: Qubit) : ()
    // {
    //     body
    //     {
    //         let current = M(q1);
    //         if (desired != current) { X(q1); }
    //     }
    // }

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable ans = new Int[N];
            for (i in 0..N-1) {
                set ans[i] = 1;
            }
            using (register = Qubit[N]) {
                using (res = Qubit[1]) {
                    for (i in 0..N-1) {
                        Set(Zero,register[i]);
                    }
                    Set(Zero,res[0]);
                    Uf(register,res[0]);
                    if (M(res[0]) == One) {
                        set ans[0] = 0;
                    }
                    for (i in 0..N-1) {
                        Set(Zero,register[i]);
                    }
                    Set(Zero,res[0]);
                }
            }
            return ans;
        }
    }
}