typedef int *T;
T arr[8];
T (*p) = arr - 1;
T (*q) = &arr[0] - 1;
