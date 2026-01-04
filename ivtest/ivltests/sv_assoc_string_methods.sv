// Test associative array first/last/next/prev methods with string keys
module test;
  int assoc[string];
  string key;
  int result;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Populate the associative array
    assoc["alpha"] = 1;
    assoc["beta"] = 2;
    assoc["gamma"] = 3;

    // Test size
    if (assoc.size() == 3) begin
      $display("PASSED: size() = 3");
      pass_count++;
    end else begin
      $display("FAILED: size() = %0d, expected 3", assoc.size());
      fail_count++;
    end

    // Test exists
    if (assoc.exists("alpha") == 1) begin
      $display("PASSED: exists(\"alpha\") = 1");
      pass_count++;
    end else begin
      $display("FAILED: exists(\"alpha\") = %0d", assoc.exists("alpha"));
      fail_count++;
    end

    if (assoc.exists("delta") == 0) begin
      $display("PASSED: exists(\"delta\") = 0");
      pass_count++;
    end else begin
      $display("FAILED: exists(\"delta\") should be 0");
      fail_count++;
    end

    // Test first - should return 1 and set key to first key (alphabetical order)
    result = assoc.first(key);
    if (result == 1 && key == "alpha") begin
      $display("PASSED: first() returned 1, key = \"%s\"", key);
      pass_count++;
    end else begin
      $display("FAILED: first() = %0d, key = \"%s\" (expected 1, \"alpha\")", result, key);
      fail_count++;
    end

    // Test last - should return 1 and set key to last key (alphabetical order)
    result = assoc.last(key);
    if (result == 1 && key == "gamma") begin
      $display("PASSED: last() returned 1, key = \"%s\"", key);
      pass_count++;
    end else begin
      $display("FAILED: last() = %0d, key = \"%s\" (expected 1, \"gamma\")", result, key);
      fail_count++;
    end

    // Test next - starting from "alpha", next should be "beta"
    key = "alpha";
    result = assoc.next(key);
    if (result == 1 && key == "beta") begin
      $display("PASSED: next(\"alpha\") returned 1, key = \"%s\"", key);
      pass_count++;
    end else begin
      $display("FAILED: next(\"alpha\") = %0d, key = \"%s\" (expected 1, \"beta\")", result, key);
      fail_count++;
    end

    // Test prev - starting from "gamma", prev should be "beta"
    key = "gamma";
    result = assoc.prev(key);
    if (result == 1 && key == "beta") begin
      $display("PASSED: prev(\"gamma\") returned 1, key = \"%s\"", key);
      pass_count++;
    end else begin
      $display("FAILED: prev(\"gamma\") = %0d, key = \"%s\" (expected 1, \"beta\")", result, key);
      fail_count++;
    end

    // Test next at end - from "gamma" should fail (no next)
    key = "gamma";
    result = assoc.next(key);
    if (result == 0) begin
      $display("PASSED: next(\"gamma\") returned 0 (no more keys)");
      pass_count++;
    end else begin
      $display("FAILED: next(\"gamma\") = %0d (expected 0)", result);
      fail_count++;
    end

    // Test prev at beginning - from "alpha" should fail (no prev)
    key = "alpha";
    result = assoc.prev(key);
    if (result == 0) begin
      $display("PASSED: prev(\"alpha\") returned 0 (no more keys)");
      pass_count++;
    end else begin
      $display("FAILED: prev(\"alpha\") = %0d (expected 0)", result);
      fail_count++;
    end

    // Test delete
    assoc.delete("beta");
    if (assoc.size() == 2) begin
      $display("PASSED: after delete(\"beta\"), size() = 2");
      pass_count++;
    end else begin
      $display("FAILED: after delete, size() = %0d (expected 2)", assoc.size());
      fail_count++;
    end

    // Summary
    if (fail_count == 0) begin
      $display("All %0d tests PASSED", pass_count);
    end else begin
      $display("%0d tests PASSED, %0d tests FAILED", pass_count, fail_count);
    end
  end
endmodule
