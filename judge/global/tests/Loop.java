package test;

import benchmark.internal.Benchmark;
import benchmark.objects.B;

public class Loop {

  public static void main(String[] args) {
    Benchmark.alloc(1);
    B b1 = new B();
    Benchmark.alloc(2);
    B b2 = new B();
    Benchmark.alloc(3);
    B b3 = new B();
    Benchmark.alloc(4);
    B b4 = new B();
    for(int i = 0; i < args.length; i++) {
        b1 = b2;
        b2 = b3;
        b3 = b4;
    }
    Benchmark.test(1, b1);
    Benchmark.test(2, b2);
    Benchmark.test(3, b3);
    Benchmark.test(4, b4);
  }
}
/*
Answer:
  1 : 1 2 3 4
  2 : 2 3 4
  3 : 3 4
  4 : 4
*/
