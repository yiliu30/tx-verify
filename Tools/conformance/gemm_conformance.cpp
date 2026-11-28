#include <sycl/sycl.hpp>
#include <cstdio>
#include <cstdint>

int main() {
  constexpr int M = 64, N = 64, K = 64;
  sycl::queue q;
  int *A = sycl::malloc_shared<int>(M * K, q);
  int *B = sycl::malloc_shared<int>(K * N, q);
  int *C = sycl::malloc_shared<int>(M * N, q);
  for (int i = 0; i < M * K; ++i) A[i] = (i % 7) - 3;
  for (int i = 0; i < K * N; ++i) B[i] = (i % 5) - 2;
  q.parallel_for(sycl::range<2>(M, N), [=](sycl::id<2> idx) {
    int i = idx[0], j = idx[1];
    int sum = 0;
    #pragma unroll 1
    for (int k = 0; k < K; ++k) sum += A[i * K + k] * B[k * N + j];
    C[i * N + j] = sum;
  }).wait();
  uint32_t checksum = 0;
  for (int i = 0; i < M * N; ++i) checksum += (uint32_t)C[i];
  int bad = 0;
  for (int i = 0; i < M; ++i)
    for (int j = 0; j < N; ++j) {
      int s = 0;
      for (int k = 0; k < K; ++k) s += A[i * K + k] * B[k * N + j];
      if (C[i * N + j] != s) ++bad;
    }
  printf("C00=%d C11=%d C6363=%d checksum=%u bad=%d\n",
         C[0], C[1 * N + 1], C[63 * N + 63], checksum, bad);
  return 0;
}
