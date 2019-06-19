namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable b=new Int[N];
            using (q=Qubit[N+1]) {
                ResetAll(q);
                Uf(q[0..N-1],q[N]);
                if (M(q[N])==One) {
                    set b[0]=1-b[0];
                }
                if (N%2==1) {
                    set b[0]=1-b[0];
                }
                ResetAll(q);
            }
            return b;
        }
    }
}