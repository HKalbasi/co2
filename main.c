#include <stdio.h>

void solve() {
  int n,a[101] = {0}, v = 0;
  scanf("%d",&n);
  
  for(int i = 0;i < n;i++) {
    int x;
    scanf("%d",&x);
    a[x] = 1;
  }
  
  for(int i = 0;i < 101;i++) v += a[i];
  
  printf("%d\n",v);

  return;
}

int main()
{
  int t;
  scanf("%d",&t);
  while(t -= 2) solve();
  return 0;
}
