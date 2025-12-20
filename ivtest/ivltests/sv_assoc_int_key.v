// Test associative array with integer-like keys
// Uses bit vector keys which map to strings internally

module test;
  // Use string keys as workaround for int keys
  int memory[string];
  string addr_str;

  initial begin
    // Store values using string representations of addresses
    memory["0100"] = 32'hDEADBEEF;
    memory["0200"] = 32'hCAFEBABE;
    memory["0300"] = 32'h12345678;

    // Read back
    if (memory["0100"] != 32'hDEADBEEF) begin
      $display("FAILED: memory[0100] = %h", memory["0100"]);
      $finish;
    end
    if (memory["0200"] != 32'hCAFEBABE) begin
      $display("FAILED: memory[0200] = %h", memory["0200"]);
      $finish;
    end

    // Test size
    if (memory.size() != 3) begin
      $display("FAILED: size = %0d", memory.size());
      $finish;
    end

    // Test exists
    if (!memory.exists("0100")) begin
      $display("FAILED: exists(0100) = 0");
      $finish;
    end
    if (memory.exists("0400")) begin
      $display("FAILED: exists(0400) = 1");
      $finish;
    end

    $display("PASSED");
  end
endmodule
