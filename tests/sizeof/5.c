int main() {
	int a = 3;
	int b = sizeof a++;
	return a; // expect: 3
}
