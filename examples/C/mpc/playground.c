int main(__attribute__((private(0))) int reviews[10], __attribute__((private(1))) int offset)
{
   int res = 0;
   int result[10];
   for(int i = 0; i < 10; i++){
    result[i] += reviews[i];
   }

   for(int i = 0; i < 10; i++){
    res += result[i];
   }
   return res + offset;
}