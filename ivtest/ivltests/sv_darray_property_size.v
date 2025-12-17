// Test $size() and .size() on dynamic array class properties
// Both forms should work identically for darray properties

class ArrayHolder;
  int data[];

  function new(int size);
    data = new[size];
    for (int i = 0; i < size; i++) begin
      data[i] = i * 10;
    end
  endfunction

  // Test $size() function form
  function int get_size_func();
    return $size(data);
  endfunction

  // Test .size() method form
  function int get_size_method();
    return data.size();
  endfunction
endclass

module test;
  ArrayHolder holder;
  int errors;

  initial begin
    errors = 0;

    // Create with 5 elements
    holder = new(5);

    // Test 1: $size() function form on int darray
    if (holder.get_size_func() !== 5) begin
      $display("FAILED: Test 1 - $size(data) = %0d, expected 5", holder.get_size_func());
      errors = errors + 1;
    end

    // Test 2: .size() method form on int darray
    if (holder.get_size_method() !== 5) begin
      $display("FAILED: Test 2 - data.size() = %0d, expected 5", holder.get_size_method());
      errors = errors + 1;
    end

    // Test 3: Create new holder with different size
    holder = new(10);
    if (holder.get_size_func() !== 10) begin
      $display("FAILED: Test 3 - new holder, $size(data) = %0d, expected 10", holder.get_size_func());
      errors = errors + 1;
    end

    // Test 4: Check .size() on new holder
    if (holder.get_size_method() !== 10) begin
      $display("FAILED: Test 4 - new holder, data.size() = %0d, expected 10", holder.get_size_method());
      errors = errors + 1;
    end

    // Test 5: Create with 1 element
    holder = new(1);
    if (holder.get_size_func() !== 1) begin
      $display("FAILED: Test 5 - single element, $size(data) = %0d, expected 1", holder.get_size_func());
      errors = errors + 1;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
