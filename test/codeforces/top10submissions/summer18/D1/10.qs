
namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;

   operation Solve (x : Qubit[], y : Qubit, b : Int[]) : ()
   {
       body
       {
            for(i in 0..Length(x)-1){
                if(b[i]==1){
                    CNOT(x[i],y);
                }
            }
       }
    }
}