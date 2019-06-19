
namespace Solution
{
   open Microsoft.Quantum.Canon;
   open Microsoft.Quantum.Primitive;

   operation Solve (x : Qubit[], y : Qubit, b : Int[]) : ()
   {
       body
       {
            for(i in 0..Length(x)-1){
                X(y);
                if(b[i]==1){
                    X(y);
                }
            }
            for(i in 0..Length(x)-1){
                CNOT(x[i],y);
            }
       }
    }
}