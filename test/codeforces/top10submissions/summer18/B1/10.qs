
namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;
    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            for(i in 0..Length(qs)-1){
                if(M(qs[i])==One){
                    return 1;
                }
            }
            return 0;
        }
    }
}