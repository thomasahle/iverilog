// Test conditional constraints: implication (->) and if-else
// These are parsed and constraints from both branches are treated as soft

module test;
  class MyClass;
    rand int a;
    rand int b;
  endclass

  MyClass obj;

  initial begin
    obj = new();

    $display("Test 1: Implication constraint a > 50 -> { b < 20 }");
    // This means: if a > 50, then b < 20
    // If a <= 50, constraint is satisfied regardless of b
    for (int i = 0; i < 10; i++) begin
      if (obj.randomize() with { a > 0; a < 100; (a > 50) -> { b < 20; }; }) begin
        $display("  a=%0d, b=%0d", obj.a, obj.b);
      end else begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
    end
    $display("  Implication constraint parsed successfully");

    $display("Test 2: If-else constraint");
    for (int i = 0; i < 10; i++) begin
      if (obj.randomize() with {
        a > 0; a < 100;
        if (a > 50) { b > 100; } else { b < 50; };
      }) begin
        $display("  a=%0d, b=%0d", obj.a, obj.b);
      end else begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
    end
    $display("  If-else constraint parsed successfully");

    $display("Test 3: Nested conditional constraints");
    for (int i = 0; i < 5; i++) begin
      if (obj.randomize() with {
        a > 0; a < 200;
        if (a < 50) {
          b > 0; b < 100;
        } else if (a < 100) {
          b >= 100; b < 200;
        } else {
          b >= 200;
        };
      }) begin
        $display("  a=%0d, b=%0d", obj.a, obj.b);
      end else begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
    end
    $display("  Nested conditional constraints parsed successfully");

    $display("PASSED - All conditional constraint syntax accepted");
  end
endmodule
