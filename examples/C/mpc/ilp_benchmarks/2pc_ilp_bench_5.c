int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b)
{
    int acc = 0;
    for (int i = 0; i < 5000; i++)
    {
        if (a > b)
        {
            acc += 1;
        }
    }
    return acc;
}
