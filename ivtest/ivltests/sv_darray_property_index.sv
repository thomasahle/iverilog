// Test dynamic array property indexing in classes
// This tests:
// 1. Reading elements: obj = c.arr[i]
// 2. Writing elements: c.arr[i] = obj
// 3. Accessing properties of elements: c.arr[i].val = 100

class MyClass;
  int val;
  function new();
    val = 42;
  endfunction
endclass

class Container;
  MyClass arr[];

  function new();
    arr = new[3];
    arr[0] = new();
    arr[1] = new();
    arr[2] = new();
    // Test writing to element property through indexed access
    arr[1].val = 100;
    arr[2].val = 200;
  endfunction
endclass

module test;
  Container c;
  MyClass obj;
  int passed = 1;

  initial begin
    c = new();

    // Test 1: Read element from dynamic array property
    obj = c.arr[0];
    if (obj.val !== 42) begin
      $display("FAILED: Test 1 - obj.val = %0d, expected 42", obj.val);
      passed = 0;
    end

    // Test 2: Read another element
    obj = c.arr[1];
    if (obj.val !== 100) begin
      $display("FAILED: Test 2 - obj.val = %0d, expected 100", obj.val);
      passed = 0;
    end

    // Test 3: Read third element
    obj = c.arr[2];
    if (obj.val !== 200) begin
      $display("FAILED: Test 3 - obj.val = %0d, expected 200", obj.val);
      passed = 0;
    end

    // Test 4: Write element to dynamic array property
    obj = new();
    obj.val = 999;
    c.arr[0] = obj;
    obj = c.arr[0];
    if (obj.val !== 999) begin
      $display("FAILED: Test 4 - obj.val = %0d, expected 999", obj.val);
      passed = 0;
    end

    // Test 5: Write to element property through indexed access
    c.arr[1].val = 555;
    obj = c.arr[1];
    if (obj.val !== 555) begin
      $display("FAILED: Test 5 - obj.val = %0d, expected 555", obj.val);
      passed = 0;
    end

    if (passed)
      $display("PASSED");
  end
endmodule
