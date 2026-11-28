#include <sycl/sycl.hpp>
#include <cstdio>
int main() {
  constexpr int N = 1024, L = 64;
  sycl::queue q;
  int *a = sycl::malloc_shared<int>(N, q);
  int *b = sycl::malloc_shared<int>(N, q);
  int *c = sycl::malloc_shared<int>(N, q);
  for (int i = 0; i < N; ++i) { a[i] = (i % 7) - 3; b[i] = (i % 5) - 2; }
  q.parallel_for(sycl::nd_range<1>(N, L), [=](sycl::nd_item<1> it) {
    int i = it.get_global_id(0);
    c[i] = a[i] + b[i];
  }).wait();
  int bad = 0;
  for (int i = 0; i < N; ++i) if (c[i] != a[i] + b[i]) ++bad;
  printf("bad=%d\n", bad);
  sycl::free(a, q); sycl::free(b, q); sycl::free(c, q);
  return 0;
}
