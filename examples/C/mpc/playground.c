int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b)
{
   int result[10];
   for(int i = 0; i < 10; i++){
       result[i] = 0;
   }

   for(int i = 0; i < 10; i++){
       result[i] += 1;
   }

   int res = 0;

   for(int i = 0; i < 10; i++){
       res += result[i];
   }

   return res + a + b;
}