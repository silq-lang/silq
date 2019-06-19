namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable ans = new Int[N];
            using(qs = Qubit[N+1]){
                X(qs[N]);
                ApplyToEach(H,qs);
                Uf(qs[0..N-1],qs[N]);
                ApplyToEach(H,qs);
                for(i in 0..N-1){
                    set ans[i] = 0;
                    if(M(qs[i])==One){
                        set ans[i] = 1;
                    }
                }
                ResetAll(qs);
            }
            return ans;
        }
    }
}