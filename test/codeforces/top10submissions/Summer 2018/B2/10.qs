
namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;
    operation Solve (qs : Qubit[]) : Int
    {
        body
        {
            let x = M(qs[0]);
            for(i in 1..Length(qs)-1){
                if(M(qs[i])!=x){
                    return 1;
                }
            }
            return 0;
        }
    }
}