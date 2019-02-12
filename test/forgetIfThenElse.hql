
// if-then-else should introduce dependency
def f0(x:𝔹){
	// copy x by if-then-else
	if x{
		y:=0:𝔹;
	}else{
		y:=1:𝔹;
	}

	__show(__query("dep", y)); // should print {x}

	return (x,y);
}

// if-then-else should introduce dependency
def f1(x:𝔹,y:𝔹){
	// copy y, in both branches
	if x{
		z:=dup(y);
	}else{
		z:=dup(y);
	}

	__show(__query("dep", z)); // should print {x,y}
	forget(z);

	return (x,y);
}

// forget within if-then-else
def f2(x:𝔹){
	if x{
		y:=dup(x);
		forget(y);
	}

	return x;
}


// multiple dependencies for if-then-else (nested)
def f3(x:𝔹,y:𝔹){
	if x{
		if y{
			z:=0;
			__show(__query("dep", z)); // should print {x,y}
		}
	}

	return (x,y);
}


// multiple dependencies for if-then-else (conjunction)
def f4(x:𝔹,y:𝔹){
	if x && y{
		z:=0;
		__show(__query("dep", z)); // should print {x,y}
	}

	return (x,y);
}


// multiple dependencies, partially classical
def f5(x:𝔹,y:!𝔹){
	if x && y{
		z:=0;
		__show(__query("dep", z)); // should print {x}
	}

	return (x,y);
}


// destroying dependency in conditional (chain)
def f6(const x:𝔹,a:𝔹){
	// compute chain c -> b -> a
	b:=dup(a);
	c:=dup(b);

	// forget b in both branches
	if x{
		forget(b=0); // unsafe forget, ok due to additional knowledge
	}else{
		forget(b=1); // unsafe forget, ok due to additional knowledge
	}

	__show(__query("dep", c)); // should print {a}
	forget(c);

	return (a);
}