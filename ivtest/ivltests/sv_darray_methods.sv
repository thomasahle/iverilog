// Test dynamic array methods (supported ones)
module test;
  int arr[];
  int arr2[];
  int errors = 0;

  initial begin
    // Test new with size
    arr = new[5];
    if (arr.size() != 5) begin
      $display("FAILED: size after new[5] is %0d", arr.size());
      errors++;
    end

    // Initialize values
    arr[0] = 50;
    arr[1] = 20;
    arr[2] = 40;
    arr[3] = 10;
    arr[4] = 30;

    // Verify initialization
    if (arr[0] != 50 || arr[2] != 40) begin
      $display("FAILED: init - arr[0]=%0d, arr[2]=%0d", arr[0], arr[2]);
      errors++;
    end

    // Test resize with new[n](old)
    arr2 = new[7](arr);
    if (arr2.size() != 7) begin
      $display("FAILED: resize size is %0d, expected 7", arr2.size());
      errors++;
    end
    if (arr2[0] != 50 || arr2[4] != 30) begin
      $display("FAILED: resize copy - arr2[0]=%0d, arr2[4]=%0d", arr2[0], arr2[4]);
      errors++;
    end
    // New elements should be 0
    if (arr2[5] != 0 || arr2[6] != 0) begin
      $display("FAILED: new elements - arr2[5]=%0d, arr2[6]=%0d", arr2[5], arr2[6]);
      errors++;
    end

    // Test copy from another array
    arr = new[3];
    arr[0] = 100;
    arr[1] = 200;
    arr[2] = 300;
    arr2 = arr;
    if (arr2.size() != 3 || arr2[1] != 200) begin
      $display("FAILED: copy - size=%0d, arr2[1]=%0d", arr2.size(), arr2[1]);
      errors++;
    end

    // Test delete
    arr.delete();
    if (arr.size() != 0) begin
      $display("FAILED: size after delete is %0d, expected 0", arr.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
