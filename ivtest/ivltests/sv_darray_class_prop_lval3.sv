// Test dynamic array element class property l-value assignment
// Pattern: objs[i].prop = value
// With verification using foreach

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

  function int get_inner_value();
    if (inner_h == null) return -1;
    return inner_h.value;
  endfunction
endclass

module test;
  Outer objs[];
  Inner inner;
  int vals[2];

  initial begin
    vals[0] = 42;
    vals[1] = 99;

    // Create dynamic array of Outer objects
    objs = new[2];
    objs[0] = new();
    objs[1] = new();

    // Create inner objects and assign via darray element property access
    // This is the key l-value pattern: objs[i].inner_h = value
    foreach (objs[i]) begin
      inner = new(vals[i]);
      objs[i].inner_h = inner;
    end

    // Verify values using method call
    foreach (objs[i]) begin
      if (objs[i].get_inner_value() !== vals[i]) begin
        $display("FAILED: objs[%0d].get_inner_value() = %0d, expected %0d",
                 i, objs[i].get_inner_value(), vals[i]);
        $finish;
      end
    end

    $display("PASSED");
  end
endmodule
