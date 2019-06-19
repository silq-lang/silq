namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable ans = new Int[N];
            for(i in 0..N-1){
                set ans[i] = 0;
            }
            set ans[0] = N%2;
            using(qs=Qubit[N+1]){
                Uf(qs[0..N-1],qs[N]);
                if(M(qs[N]) == One){
                    set ans[0] = 1-ans[0];
                }
                ResetAll(qs);
            }
            return ans;
        }
    }
}