// Test variable-to-variable constraints (property-to-property bounds)
// Both a and b are rand properties, constraint b >= a must be enforced

class packet;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c_order { b >= a; }
endclass

class transaction;
  rand int x;
  rand int y;
  rand int z;
  // Chain constraint: z >= y >= x
  constraint c_chain { y >= x; z >= y; }
endclass

module test;
  packet p;
  transaction t;
  int pass_count;
  int fail_count;

  initial begin
    p = new();
    t = new();
    pass_count = 0;
    fail_count = 0;

    // Test 1: Simple b >= a constraint (unsigned)
    repeat(20) begin
      void'(p.randomize());
      if (p.b >= p.a)
        pass_count++;
      else begin
        $display("FAIL: b=%0d < a=%0d", p.b, p.a);
        fail_count++;
      end
    end

    // Test 2: Chain constraint z >= y >= x (signed)
    repeat(20) begin
      void'(t.randomize());
      if (t.y >= t.x && t.z >= t.y)
        pass_count++;
      else begin
        $display("FAIL: x=%0d, y=%0d, z=%0d (y>=x? %s, z>=y? %s)",
                 t.x, t.y, t.z,
                 t.y >= t.x ? "yes" : "no",
                 t.z >= t.y ? "yes" : "no");
        fail_count++;
      end
    end

    if (fail_count == 0)
      $display("PASSED: All %0d variable-to-variable constraints enforced", pass_count);
    else
      $display("FAILED: %0d/%0d constraints violated", fail_count, pass_count + fail_count);

    $finish;
  end
endmodule
