int main() {
	int a = 3;
	int b = a = 5;
	return a; // expect: 5
}
