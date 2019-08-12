namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            let x = RandomInt(2);
            if(x == 0){
                if(M(q)==One){
                    return 1;
                }
                return -1;
            }
            H(q);
            if(M(q)==One){
                return 0;
            }
            return -1;
        }
    }
}