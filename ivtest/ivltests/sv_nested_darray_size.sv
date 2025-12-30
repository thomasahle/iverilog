// Test nested .size() method on dynamic array class properties
// obj.prop.arr.size() should correctly return the array size

class Container;
  int data[];  // Dynamic array property

  function new();
    data = new[5];
    for (int i = 0; i < 5; i++)
      data[i] = i * 10;
  endfunction

  function int get_size();
    return data.size();  // Direct .size() should work
  endfunction
endclass

class Wrapper;
  Container cont;

  function new();
    cont = new();
  endfunction
endclass

module test;
  Wrapper w;
  int sz;
  int passed;

  initial begin
    passed = 1;
    w = new();

    // Test 1: Nested property access to dynamic array size
    sz = w.cont.data.size();
    if (sz != 5) begin
      $display("FAILED: Test 1 - w.cont.data.size() = %0d, expected 5", sz);
      passed = 0;
    end

    // Test 2: Access through method (for comparison)
    sz = w.cont.get_size();
    if (sz != 5) begin
      $display("FAILED: Test 2 - w.cont.get_size() = %0d, expected 5", sz);
      passed = 0;
    end

    // Test 3: Direct access on container
    sz = w.cont.data.size();
    if (sz != 5) begin
      $display("FAILED: Test 3 - Direct data.size() = %0d, expected 5", sz);
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
