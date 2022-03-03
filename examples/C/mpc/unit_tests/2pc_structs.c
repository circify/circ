struct test {   
    int a[1];
    int b[1];
};

int main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
    struct test c = {{0}, {1}};
    c.a[0] = a;
    c.b[0] = b;
    return c.a[0] + c.b[0];
}


// struct test {   
//     int a;
//     int b;
// };

// int main(
//     __attribute__((private(0))) int a,
//     __attribute__((private(1))) int b)
// {
//     struct test c = {0, 1};
//     c.a = a;
//     c.b = b;
//     return c.a + c.b;
// }