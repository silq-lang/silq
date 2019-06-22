namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  function FindFirstDiff (a:Int, b:Int) : Int
	{
	  let c = a ^^^ b;
		for (i in 0 .. 3) {
			if ( iss(c,i)) {
				return i;
			}	
		}
		return -1;
	}
	function iss(a:Int,b:Int):Bool{
	  return ((a>>>b)&&&1)==1;
	}
  operation RotateUnit(x : Qubit[], a : Int, b: Int, t: Double):Unit{
    body(...){
      let N = Length(x);
      let d = FindFirstDiff(a,b);
      if(iss(a,d)){
        X(x[d]);
      }
      XORx(x,b,d);
      X(x[d]);
      XORx(x,a,d);
      if(d==0){
        Controlled (Ry(t,_)) (x[1..N-1],x[0]);
      }
      elif(d==N-1){
        Controlled (Ry(t,_)) (x[0..N-2],x[0]);
      }
      else{
        Controlled (Controlled(Ry(t,_))(x[0..(d-1)],_)) (x[(d+1)..N-1],x[0]);
      }
      XORx(x,a,d);
      X(x[d]);
      XORx(x,b,d);
      if(iss(a,d)){
        X(x[d]);
      }
    }
  }
  operation Solve (x : Qubit[]) : Unit {
    body (...) {
      if(Length(x)==2){
        //RotateUnit(x,2,3,PI()/4.0);
        //Controlled H(x[0..0],x[1]);
        
        RotateUnit(x,2,3,PI()/2.0);
        RotateUnit(x,1,2,ArcTan(Sqrt(2.0)));
        RotateUnit(x,0,1,PI()/2.0);
      }
      if(Length(x)==3){
      
        RotateUnit(x,6,7,PI()/2.0);
        RotateUnit(x,5,6,2.0*ArcTan(Sqrt(2.0)));
        RotateUnit(x,4,5,2.0*ArcTan(Sqrt(3.0)));
        
        RotateUnit(x,3,4,2.0*ArcTan(Sqrt(4.0)));
        RotateUnit(x,2,3,2.0*ArcTan(Sqrt(5.0)));
        
        RotateUnit(x,1,2,2.0*ArcTan(Sqrt(6.0)));
        
        RotateUnit(x,0,1,PI()/2.0);
        //RotateUnit(x,4,5,ArcTan(Sqrt(3.0)));
        //RotateUnit(x,0,1,PI()/2.0);
      }
      if(Length(x)==4){
      
        RotateUnit(x,14,15,PI()/2.0);
        for(i in 2..14){
          RotateUnit(x,15-i,16-i,2.0*ArcTan(Sqrt(ToDouble(i))));
        }
        RotateUnit(x,0,1,PI()/2.0);
        //RotateUnit(x,4,5,ArcTan(Sqrt(3.0)));
        //RotateUnit(x,0,1,PI()/2.0);
      }
    }
  }
  operation XORx (x:Qubit[], k: Int,d:Int): Unit{
    body(...){
      let N = Length(x);
      for(i in 0..N-1){
        if( (i!=d) && !iss(k,i)){
          CNOT(x[d],x[i]);
        }
      }
    }controlled auto;
    adjoint auto;
    controlled adjoint auto;
  }
  // operation XOR (x: Qubit[], k: Int): Unit{
  //   body(...){
  //   let N = Length(x);
  //   for(i in 0..N-1){
  //     if( iss(k,i) ){
  //       X(x[i]);
  //     }
  //   }
  //   }controlled auto;
  //   adjoint auto;
  //   controlled adjoint auto;
  // }
}