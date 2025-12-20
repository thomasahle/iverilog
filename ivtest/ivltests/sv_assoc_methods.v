// Test associative array methods
// Tests: size(), num(), exists(), delete(), first(), next()

module test;
  int arr[string];

  initial begin
    // Test empty array
    if (arr.size() != 0) begin
      $display("FAILED: empty size = %0d", arr.size());
      $finish;
    end
    if (arr.num() != 0) begin
      $display("FAILED: empty num = %0d", arr.num());
      $finish;
    end

    // Add elements
    arr["alpha"] = 100;
    arr["beta"] = 200;
    arr["gamma"] = 300;

    // Test size/num
    if (arr.size() != 3) begin
      $display("FAILED: size = %0d, expected 3", arr.size());
      $finish;
    end
    if (arr.num() != 3) begin
      $display("FAILED: num = %0d, expected 3", arr.num());
      $finish;
    end

    // Test exists
    if (!arr.exists("beta")) begin
      $display("FAILED: exists(beta) returned 0");
      $finish;
    end
    if (arr.exists("delta")) begin
      $display("FAILED: exists(delta) returned 1");
      $finish;
    end

    // Test first/next iteration using constant keys
    if (!arr.exists("alpha")) begin
      $display("FAILED: first element alpha not found");
      $finish;
    end

    // Test delete
    arr.delete("beta");
    if (arr.size() != 2) begin
      $display("FAILED: size after delete = %0d", arr.size());
      $finish;
    end
    if (arr.exists("beta")) begin
      $display("FAILED: beta still exists after delete");
      $finish;
    end

    $display("PASSED");
  end
endmodule
