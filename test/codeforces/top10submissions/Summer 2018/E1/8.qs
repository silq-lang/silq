namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable b=new Int[N];
            using (qs=Qubit[N+1]) {
                X(qs[N]);
                ApplyToEach(H,qs);
                Uf(qs[0..N-1],qs[N]);
                ApplyToEach(H,qs[0..N-1]);
                for (i in 0..N-1) {
                    let r=M(qs[i]);
                    if (r==One) {
                        set b[i]=1;
                    } else {
                        set b[i]=0;
                    }
                }
                for (i in 0..N) {
                    Reset(qs[i]);
                }
            }
            return b;
        }
    }
}