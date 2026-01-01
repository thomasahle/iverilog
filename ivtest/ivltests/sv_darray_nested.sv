// Test multi-dimensional dynamic arrays - basic declaration and element allocation
module test;
  // Dynamic array of dynamic arrays
  int arr[][];

  initial begin
    $display("Testing nested dynamic arrays (int arr[][])");

    // Test 1: Basic declaration
    $display("arr size before new: %0d", arr.size());
    if (arr.size() != 0) begin
      $display("FAILED: initial size should be 0");
      $finish;
    end

    // Test 2: Allocate outer array
    arr = new[3];
    $display("arr size after new[3]: %0d", arr.size());
    if (arr.size() != 3) begin
      $display("FAILED: size after new[3] should be 3");
      $finish;
    end

    // Test 3: Allocate inner arrays
    arr[0] = new[2];
    arr[1] = new[5];
    arr[2] = new[1];

    $display("arr[0] size: %0d", arr[0].size());
    $display("arr[1] size: %0d", arr[1].size());
    $display("arr[2] size: %0d", arr[2].size());

    if (arr[0].size() != 2) begin
      $display("FAILED: arr[0].size() should be 2");
      $finish;
    end
    if (arr[1].size() != 5) begin
      $display("FAILED: arr[1].size() should be 5");
      $finish;
    end
    if (arr[2].size() != 1) begin
      $display("FAILED: arr[2].size() should be 1");
      $finish;
    end

    // Test 4: Delete
    arr.delete();
    $display("arr size after delete: %0d", arr.size());
    if (arr.size() != 0) begin
      $display("FAILED: size after delete should be 0");
      $finish;
    end

    $display("PASSED");
  end
endmodule
