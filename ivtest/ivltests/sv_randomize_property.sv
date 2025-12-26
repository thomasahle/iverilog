// Test randomize() on class property (obj.prop.randomize())

class inner_class;
  rand int value;
  rand logic [7:0] byte_val;

  function new();
    value = 0;
    byte_val = 0;
  endfunction
endclass

class outer_class;
  inner_class inner;

  function new();
    inner = new();
  endfunction

  function int test_randomize();
    // Call randomize on property
    if (!inner.randomize()) begin
      $display("FAILED: inner.randomize() returned 0");
      return 0;
    end
    $display("inner.randomize succeeded: value=%0d, byte_val=%0d", inner.value, inner.byte_val);
    return 1;
  endfunction
endclass

module test;
  initial begin
    outer_class outer;
    outer = new();

    if (outer.test_randomize())
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
