// Test associative array with string keys
module test;
  int data[string];
  string keys[$];
  int errors = 0;

  initial begin
    // Test basic operations
    data["apple"] = 10;
    data["banana"] = 20;
    data["cherry"] = 30;

    // Check size
    if (data.size() != 3) begin
      $display("FAILED: size is %0d, expected 3", data.size());
      errors++;
    end

    // Check access
    if (data["apple"] != 10) begin
      $display("FAILED: data[apple] = %0d, expected 10", data["apple"]);
      errors++;
    end
    if (data["banana"] != 20) begin
      $display("FAILED: data[banana] = %0d, expected 20", data["banana"]);
      errors++;
    end

    // Check exists
    if (!data.exists("cherry")) begin
      $display("FAILED: exists(cherry) returned 0");
      errors++;
    end
    if (data.exists("grape")) begin
      $display("FAILED: exists(grape) returned 1");
      errors++;
    end

    // Test delete
    data.delete("banana");
    if (data.size() != 2) begin
      $display("FAILED: size after delete is %0d, expected 2", data.size());
      errors++;
    end
    if (data.exists("banana")) begin
      $display("FAILED: banana still exists after delete");
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
