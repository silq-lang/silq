namespace Solution
{
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Primitive;

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
            using (register = Qubit[N]) {
                using (res = Qubit[1]) {
                    // initialize
                    for (i in 0..N-1) {
                        Set(Zero,register[i]); H(register[i]);
                    }
                    Set(One,res[0]); H(res[0]);

                    // apply oracle
                    Uf(register,res[0]);

                    // apply hadamard again
                    for (i in 0..N-1) {
                        H(register[i]);
                    }

                    for (i in 0..N-1) {
                        if (M(register[i]) == One) {
                            set ans[i] = 1;
                        } else {
                            set ans[i] = 0;
                        }
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