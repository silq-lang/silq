
namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            R(PauliY,3.14159265358979323/4.0,q);
            if(M(q)==Zero){
                return 0;
            }
            return 1;
        }
    }
}