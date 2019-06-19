namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            mutable ans = 0;
            
            for(i in 0..(Length(qs) - 1)){
                if(M(qs[i]) == One){
                    set ans = ans + 1;
                }
            }
            
            if(ans > 1){
                set ans = 0;
            }
            
            return(ans);
        }
    }
}