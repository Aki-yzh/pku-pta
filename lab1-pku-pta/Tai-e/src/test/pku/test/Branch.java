package test;

import benchmark.internal.Benchmark;
import benchmark.objects.B;

public class Branch {

  public static void main(String[] args) {
    Benchmark.alloc(1);
    B b1 = new B();
    Benchmark.alloc(2);
    B b2 = new B();
    if(args.length > 1) b2 = b1;
    Benchmark.test(1, b1);
    Benchmark.test(2, b2);
  }
}
/*
Answer:
  1 : 1
  2 : 1 2
*/
