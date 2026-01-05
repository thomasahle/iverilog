// Test dynamic array nested property access

class Inner;
  int value;
  function new(int v = 0);
    value = v;
  endfunction
endclass

class Outer;
  Inner inner_h;
  function new();
    inner_h = null;
  endfunction
endclass

module test;
  Outer objs[];
  Inner inner;
  int i;

  initial begin
    // Create dynamic array of Outer objects
    objs = new[2];
    objs[0] = new();
    objs[1] = new();

    // Create and assign inner objects
    inner = new(42);
    objs[0].inner_h = inner;

    inner = new(99);
    objs[1].inner_h = inner;

    // Test reading back through nested access
    // This is the pattern that may have issues
    for (i = 0; i < 2; i++) begin
      if (objs[i].inner_h == null) begin
        $display("FAILED: objs[%0d].inner_h is null", i);
        $finish;
      end
      $display("objs[%0d].inner_h.value = %0d", i, objs[i].inner_h.value);
    end

    if (objs[0].inner_h.value !== 42) begin
      $display("FAILED: Expected 42, got %0d", objs[0].inner_h.value);
      $finish;
    end

    if (objs[1].inner_h.value !== 99) begin
      $display("FAILED: Expected 99, got %0d", objs[1].inner_h.value);
      $finish;
    end

    $display("PASSED");
  end
endmodule
