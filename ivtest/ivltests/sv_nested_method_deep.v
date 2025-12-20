// Test deep nested method calls (3+ levels)
// Pattern: a.b.c.method()

class Level3;
  int data;

  function new(int d);
    data = d;
  endfunction

  function int get_data();
    return data;
  endfunction
endclass

class Level2;
  Level3 l3;

  function new(int d);
    l3 = new(d);
  endfunction
endclass

class Level1;
  Level2 l2;

  function new(int d);
    l2 = new(d);
  endfunction
endclass

module test;
  initial begin
    Level1 l1;
    int v;

    l1 = new(100);

    // Test 3-level deep method call
    v = l1.l2.l3.get_data();
    if (v != 100) begin
      $display("FAILED: l1.l2.l3.get_data() = %0d, expected 100", v);
      $finish;
    end

    $display("PASSED");
  end
endmodule
