
// Check this pattern:
//
//    x   y
//     \ /
//      z
//      |
//      a
//
def f0(x:int[32],y:int[32]){
	z := x + y;
	a := z + 1;

	forget(z);

	__show(__query("dep", a)); // should print {x,y}
	forget(a);

	return (x,y);
}



// Check this pattern:
//
//       a
//      / \
//     b   c
//
def f1(a:int[32]){
	b := a + 1;
	c := a + 2;

	forget(a = 0:int[32]); // unsafe forget, ok due to additional knowledge

	__show(__query("dep", b)); // should print ⊤
	__show(__query("dep", c)); // should print ⊤

	return (b,c);
}
