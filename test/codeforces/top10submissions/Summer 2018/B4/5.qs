namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            using(a = Qubit[1]){
                X(a[0]);
                H(a[0]);
                
                X(qs[0]);
                X(qs[1]);
                
                (Controlled X)(qs, a[0]);
            
                X(qs[0]);
                X(qs[1]);
                
                ResetAll(a);
            }
        
            H(qs[0]);
            H(qs[1]);
            
            mutable ans = 0;
            
            if(M(qs[0]) == One){
                set ans = ans + 1;
            }
            
            if(M(qs[1]) == One){
                set ans = ans + 2;
            }
            
            return(ans);
        }
    }
}