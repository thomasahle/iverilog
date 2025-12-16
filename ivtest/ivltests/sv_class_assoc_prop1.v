// Test basic associative array class property indexing
// Tests both write (l-value) and read (r-value) access

module test;
  class MyClass;
    int assoc_arr[int];

    function void set_val(int idx, int val);
      this.assoc_arr[idx] = val;  // Explicit this
    endfunction

    function int get_val(int idx);
      return this.assoc_arr[idx];  // Explicit this
    endfunction
  endclass

  MyClass obj;
  int result;

  initial begin
    obj = new();

    // Test basic write and read
    obj.set_val(0, 100);
    obj.set_val(5, 500);
    obj.set_val(10, 1000);

    result = obj.get_val(0);
    if (result !== 100) begin
      $display("FAILED: get_val(0) returned %0d, expected 100", result);
      $finish;
    end

    result = obj.get_val(5);
    if (result !== 500) begin
      $display("FAILED: get_val(5) returned %0d, expected 500", result);
      $finish;
    end

    result = obj.get_val(10);
    if (result !== 1000) begin
      $display("FAILED: get_val(10) returned %0d, expected 1000", result);
      $finish;
    end

    $display("PASSED");
  end
endmodule
