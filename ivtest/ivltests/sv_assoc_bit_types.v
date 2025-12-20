// Test associative arrays with various element types
// Tests: bit, logic, reg types

module test;
  bit [7:0] byte_arr[string];
  logic [15:0] logic_arr[string];
  reg [31:0] reg_arr[string];

  initial begin
    // Test bit array
    byte_arr["key1"] = 8'hAB;
    byte_arr["key2"] = 8'hCD;

    if (byte_arr["key1"] != 8'hAB) begin
      $display("FAILED: byte_arr[key1] = %h", byte_arr["key1"]);
      $finish;
    end
    if (byte_arr.size() != 2) begin
      $display("FAILED: byte_arr.size = %0d", byte_arr.size());
      $finish;
    end

    // Test logic array
    logic_arr["addr1"] = 16'hDEAD;
    logic_arr["addr2"] = 16'hBEEF;

    if (logic_arr["addr1"] != 16'hDEAD) begin
      $display("FAILED: logic_arr[addr1] = %h", logic_arr["addr1"]);
      $finish;
    end
    if (!logic_arr.exists("addr2")) begin
      $display("FAILED: logic_arr.exists(addr2) = 0");
      $finish;
    end

    // Test reg array
    reg_arr["data1"] = 32'hCAFEBABE;

    if (reg_arr["data1"] != 32'hCAFEBABE) begin
      $display("FAILED: reg_arr[data1] = %h", reg_arr["data1"]);
      $finish;
    end

    $display("PASSED");
  end
endmodule
