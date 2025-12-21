// Test dynamic array element class property l-value assignment
// Pattern: objs[i].prop = value
// Minimal test - just assignment, no reading

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

  initial begin
    // Create dynamic array of Outer objects
    objs = new[2];
    objs[0] = new();
    objs[1] = new();

    // Create inner objects and assign via darray element property access
    // This is the key l-value pattern: objs[i].inner_h = value
    inner = new(42);
    objs[0].inner_h = inner;

    inner = new(99);
    objs[1].inner_h = inner;

    // Simple completion message
    $display("PASSED - assignments completed");
  end
endmodule
