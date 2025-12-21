// Test dynamic array element class property l-value assignment
// Pattern: objs[i].prop = value

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
  Outer temp;

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

    // Verify by reading through temporary variable (simpler r-value)
    temp = objs[0];
    if (temp.inner_h == null) begin
      $display("FAILED: objs[0].inner_h is null");
      $finish;
    end
    if (temp.inner_h.value !== 42) begin
      $display("FAILED: Expected 42, got %0d", temp.inner_h.value);
      $finish;
    end

    temp = objs[1];
    if (temp.inner_h == null) begin
      $display("FAILED: objs[1].inner_h is null");
      $finish;
    end
    if (temp.inner_h.value !== 99) begin
      $display("FAILED: Expected 99, got %0d", temp.inner_h.value);
      $finish;
    end

    $display("PASSED");
  end
endmodule
