// Test UVM RAL uvm_reg_field class
// Tests basic field configuration and value operations

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  initial begin
    uvm_reg_field field;
    uvm_reg_data_t val;

    // Create a field
    field = new("test_field");

    // Configure: 8-bit field at LSB position 4, RW access, reset value 0x5A
    field.configure(
      null,           // parent register (null for test)
      8,              // size in bits
      4,              // lsb position
      "RW",           // access type
      0,              // not volatile
      8'h5A,          // reset value
      1,              // has reset
      0,              // not rand
      1               // individually accessible
    );

    // Test get_n_bits
    if (field.get_n_bits() !== 8) begin
      $display("FAILED: get_n_bits() returned %0d, expected 8", field.get_n_bits());
      $finish;
    end

    // Test get_lsb_pos
    if (field.get_lsb_pos() !== 4) begin
      $display("FAILED: get_lsb_pos() returned %0d, expected 4", field.get_lsb_pos());
      $finish;
    end

    // Test get_access
    if (field.get_access() != "RW") begin
      $display("FAILED: get_access() returned %s, expected RW", field.get_access());
      $finish;
    end

    // Test get (should return reset value after configure)
    val = field.get();
    if (val !== 8'h5A) begin
      $display("FAILED: get() returned %0h, expected 5A", val);
      $finish;
    end

    // Test set
    field.set(8'hBC);
    val = field.get();
    if (val !== 8'hBC) begin
      $display("FAILED: get() after set returned %0h, expected BC", val);
      $finish;
    end

    // Test set with value larger than field width (should mask)
    field.set(16'hFFFF);
    val = field.get();
    if (val !== 8'hFF) begin
      $display("FAILED: get() after masked set returned %0h, expected FF", val);
      $finish;
    end

    // Test get_mirrored_value (should still be reset value since predict not called)
    val = field.get_mirrored_value();
    if (val !== 8'h5A) begin
      $display("FAILED: get_mirrored_value() returned %0h, expected 5A", val);
      $finish;
    end

    // Test predict
    void'(field.predict(8'h42));
    val = field.get_mirrored_value();
    if (val !== 8'h42) begin
      $display("FAILED: get_mirrored_value() after predict returned %0h, expected 42", val);
      $finish;
    end

    // Test reset
    field.reset();
    val = field.get();
    if (val !== 8'h5A) begin
      $display("FAILED: get() after reset returned %0h, expected 5A", val);
      $finish;
    end
    val = field.get_mirrored_value();
    if (val !== 8'h5A) begin
      $display("FAILED: get_mirrored_value() after reset returned %0h, expected 5A", val);
      $finish;
    end

    // Test get_reset
    val = field.get_reset();
    if (val !== 8'h5A) begin
      $display("FAILED: get_reset() returned %0h, expected 5A", val);
      $finish;
    end

    $display("PASSED");
  end
endmodule
