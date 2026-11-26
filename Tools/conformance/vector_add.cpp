#include <sycl/sycl.hpp>
#include <cstdio>
int main() {
  constexpr int N = 1024;
  sycl::queue q;
  int *a = sycl::malloc_shared<int>(N, q);
  int *b = sycl::malloc_shared<int>(N, q);
  int *c = sycl::malloc_shared<int>(N, q);
  for (int i = 0; i < N; ++i) { a[i] = (i % 7) - 3; b[i] = (i % 5) - 2; }
  q.parallel_for(sycl::range<1>(N), [=](sycl::id<1> i) { c[i] = a[i] + b[i]; }).wait();
  int bad = 0;
  for (int i = 0; i < N; ++i) if (c[i] != a[i] + b[i]) ++bad;
  unsigned sum = 0;
  for (int i = 0; i < N; ++i) sum += (unsigned)c[i];
  printf("bad=%d sum=%u\n", bad, sum);
  sycl::free(a, q); sycl::free(b, q); sycl::free(c, q);
  return 0;
}
