#include <stdio.h>
#include <unistd.h>

int main(int argc, char const* argv[]) {
  char c[2], g = 0;
  read(0, &c, sizeof(c));

  if (c[0] >= 'a')
    g += 1;
  else
    g += 2;

  if (c[1] <= 'z')
    g += 3;
  else
    g += 4;

  if (c[0] == 'g')
    printf("Hi! :D\n");
  else
    printf("AA! D:\n");

  printf("g: %d\n", g);
  return 0;
}
