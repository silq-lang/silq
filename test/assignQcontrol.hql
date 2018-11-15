// TODO: error

def main(b: 𝔹){
	f := λ()lifted. 1;
	if b {
		f = λ()lifted. 2;
	}else{
		f = λ()lifted. 3;
	}
	return b;
}
