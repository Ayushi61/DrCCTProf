int N = 100000;
int sum = 0;

int main() {
    register int a;
    for (int i = 0; i < N; i++) {
        a = 0; // dead store
        a = 1; // killing store
        sum += a;
    }
    return 0;
}

