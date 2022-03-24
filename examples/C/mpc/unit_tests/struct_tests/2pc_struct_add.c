struct test {   
    int a;
    int b;
};

int main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
    struct test c;
    c.a = a;
    c.b = b;
    return c.a + c.b;
}