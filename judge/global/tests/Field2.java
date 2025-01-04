package test;

import benchmark.internal.Benchmark;
import benchmark.objects.A;
import benchmark.objects.B;

public class Field2 {
  public static void main(String[] args) {
    A a1 = new A();
    A a2 = new A();
    Benchmark.alloc(1);
    B b1 = new B();
    Benchmark.alloc(2);
    B b2 = new B();
    a1.f = b1;
    if(args.length > 1) a2.f = b2;
    B b3 = a1.f;
    Benchmark.test(1, b3);
    B b4 = a2.f;
    Benchmark.test(2, b4);
  }
}
/*
Answer:
  1 : 1
  2 : 2
*/
