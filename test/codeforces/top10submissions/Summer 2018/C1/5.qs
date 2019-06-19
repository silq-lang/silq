namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            Ry(0.4, q);
            
            mutable res = M(q);
            
            if(res == Zero){
                return(0);
            }
            else{
                return(1);
            }
        }
    }
}