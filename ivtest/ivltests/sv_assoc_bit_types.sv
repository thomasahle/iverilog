// Test associative array with different bit/logic types
module test;

  // Different value types
  bit [7:0] byte_arr[string];
  bit [31:0] word_arr[int];
  logic [15:0] logic_arr[string];

  int passed;
  bit [7:0] byte_val;
  bit [31:0] word_val;
  logic [15:0] logic_val;
  int result;

  initial begin
    passed = 1;

    $display("Testing associative arrays with different bit/logic types:");

    // Test byte array (bit[7:0])
    $display("");
    $display("Testing bit[7:0] array with string keys:");

    byte_arr["a"] = 8'hAA;
    byte_arr["b"] = 8'hBB;
    byte_arr["c"] = 8'hCC;

    result = byte_arr.num();
    if (result != 3) begin
      $display("FAILED: byte_arr.num() should be 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: byte_arr.num() = %0d", result);

    byte_val = byte_arr["b"];
    if (byte_val != 8'hBB) begin
      $display("FAILED: byte_arr['b'] should be 0xBB, got 0x%h", byte_val);
      passed = 0;
    end else
      $display("PASSED: byte_arr['b'] = 0x%h", byte_val);

    if (byte_arr.exists("b") != 1) begin
      $display("FAILED: byte_arr.exists('b') should be 1");
      passed = 0;
    end else
      $display("PASSED: byte_arr.exists('b') = 1");

    byte_arr.delete("b");
    if (byte_arr.exists("b") != 0) begin
      $display("FAILED: byte_arr.exists('b') after delete should be 0");
      passed = 0;
    end else
      $display("PASSED: byte_arr.delete('b') worked");

    // Test word array (bit[31:0]) with int keys
    $display("");
    $display("Testing bit[31:0] array with int keys:");

    word_arr[100] = 32'hDEADBEEF;
    word_arr[200] = 32'hCAFEBABE;

    result = word_arr.num();
    if (result != 2) begin
      $display("FAILED: word_arr.num() should be 2, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: word_arr.num() = %0d", result);

    word_val = word_arr[100];
    if (word_val != 32'hDEADBEEF) begin
      $display("FAILED: word_arr[100] should be 0xDEADBEEF, got 0x%h", word_val);
      passed = 0;
    end else
      $display("PASSED: word_arr[100] = 0x%h", word_val);

    if (word_arr.exists(100) != 1) begin
      $display("FAILED: word_arr.exists(100) should be 1");
      passed = 0;
    end else
      $display("PASSED: word_arr.exists(100) = 1");

    if (word_arr.exists(999) != 0) begin
      $display("FAILED: word_arr.exists(999) should be 0");
      passed = 0;
    end else
      $display("PASSED: word_arr.exists(999) = 0");

    // Test logic array
    $display("");
    $display("Testing logic[15:0] array with string keys:");

    logic_arr["x"] = 16'h1234;
    logic_arr["y"] = 16'h5678;
    logic_arr["z"] = 16'hABCD;

    result = logic_arr.num();
    if (result != 3) begin
      $display("FAILED: logic_arr.num() should be 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: logic_arr.num() = %0d", result);

    logic_val = logic_arr["y"];
    if (logic_val != 16'h5678) begin
      $display("FAILED: logic_arr['y'] should be 0x5678, got 0x%h", logic_val);
      passed = 0;
    end else
      $display("PASSED: logic_arr['y'] = 0x%h", logic_val);

    // Update a value
    logic_arr["y"] = 16'hFFFF;
    logic_val = logic_arr["y"];
    if (logic_val != 16'hFFFF) begin
      $display("FAILED: logic_arr['y'] after update should be 0xFFFF, got 0x%h", logic_val);
      passed = 0;
    end else
      $display("PASSED: logic_arr['y'] updated to 0x%h", logic_val);

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
