// Test UVM RAL uvm_reg class
// Tests basic register operations

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  initial begin
    uvm_reg reg1;
    uvm_reg_data_t val;

    // Create a 32-bit register
    reg1 = new("test_reg", 32, 0);

    // Test get_n_bits
    if (reg1.get_n_bits() !== 32) begin
      $display("FAILED: get_n_bits() returned %0d, expected 32", reg1.get_n_bits());
      $finish;
    end

    // Test get_name
    if (reg1.get_name() != "test_reg") begin
      $display("FAILED: get_name() returned %s, expected test_reg", reg1.get_name());
      $finish;
    end

    // Test set and get
    reg1.set(32'hDEADBEEF);
    val = reg1.get();
    if (val !== 32'hDEADBEEF) begin
      $display("FAILED: get() returned %0h, expected DEADBEEF", val);
      $finish;
    end

    // Test get_mirrored_value (simplified impl returns same as get)
    val = reg1.get_mirrored_value();
    if (val !== 32'hDEADBEEF) begin
      $display("FAILED: get_mirrored_value() returned %0h, expected DEADBEEF", val);
      $finish;
    end

    // Test predict
    if (!reg1.predict(32'h12345678)) begin
      $display("FAILED: predict() returned 0");
      $finish;
    end
    val = reg1.get_mirrored_value();
    if (val !== 32'h12345678) begin
      $display("FAILED: get_mirrored_value() after predict returned %0h, expected 12345678", val);
      $finish;
    end

    $display("PASSED");
  end
endmodule
