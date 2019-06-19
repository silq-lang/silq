namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            ApplyToEach(X,qs);
            (Controlled(Z))(qs[0..0],qs[1]);
            ApplyToEach(X,qs);

            H(qs[0]);H(qs[1]);
            mutable ans=0;
            if(M(qs[0])==One){
                set ans = ans+1;
            }
            if(M(qs[1])==One){
                set ans = ans+2;
            }
            return ans;
        }
    }
}