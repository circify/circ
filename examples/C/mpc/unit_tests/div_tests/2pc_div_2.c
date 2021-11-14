int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
   int NC = 2;
   int pos[NC] = {6,7};
   int dist[NC] = {6,7};

   int stride = 1;
   for(int i_10 = 0; i_10 < NC - stride; i_10+=2) {
      if(dist[i_10+stride] < dist[i_10]) {
         dist[i_10] = dist[i_10+stride];
         pos[i_10] = pos[i_10+stride];
      }
   }

   return dist[0];
}


