// Test UVM RAL uvm_reg_block and uvm_reg_map classes
// Tests basic block and map operations

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  initial begin
    uvm_reg_block block;
    uvm_reg_map map, map2;
    uvm_reg reg1, reg2, reg_found;

    // Create a register block
    block = new("test_block", 0);

    // Test get_name
    if (block.get_name() != "test_block") begin
      $display("FAILED: block get_name() returned %s, expected test_block", block.get_name());
      $finish;
    end

    // Create an address map
    map = block.create_map("default_map", 64'h1000, 4, UVM_LITTLE_ENDIAN, 1);
    if (map == null) begin
      $display("FAILED: create_map() returned null");
      $finish;
    end

    // Test map properties
    if (map.get_base_addr() !== 64'h1000) begin
      $display("FAILED: map get_base_addr() returned %0h, expected 1000", map.get_base_addr());
      $finish;
    end

    if (map.get_n_bytes() !== 4) begin
      $display("FAILED: map get_n_bytes() returned %0d, expected 4", map.get_n_bytes());
      $finish;
    end

    if (map.get_endian() !== UVM_LITTLE_ENDIAN) begin
      $display("FAILED: map get_endian() returned wrong value");
      $finish;
    end

    // Test get_default_map - use get_name to verify it's the same map
    map2 = block.get_default_map();
    if (map2 == null) begin
      $display("FAILED: get_default_map() returned null");
      $finish;
    end
    if (map2.get_name() != "default_map") begin
      $display("FAILED: get_default_map() did not return the created map");
      $finish;
    end

    // Create and add registers
    reg1 = new("reg1", 32, 0);
    reg2 = new("reg2", 32, 0);

    block.add_reg(reg1);
    block.add_reg(reg2);

    // Test get_n_registers
    if (block.get_n_registers() !== 2) begin
      $display("FAILED: get_n_registers() returned %0d, expected 2", block.get_n_registers());
      $finish;
    end

    // Add registers to map
    map.add_reg(reg1, 64'h0, "RW");
    map.add_reg(reg2, 64'h4, "RW");

    // Test get_reg_by_offset - verify by checking name
    reg_found = map.get_reg_by_offset(64'h0);
    if (reg_found == null) begin
      $display("FAILED: get_reg_by_offset(0) returned null");
      $finish;
    end
    if (reg_found.get_name() != "reg1") begin
      $display("FAILED: get_reg_by_offset(0) returned %s, expected reg1", reg_found.get_name());
      $finish;
    end

    reg_found = map.get_reg_by_offset(64'h4);
    if (reg_found == null) begin
      $display("FAILED: get_reg_by_offset(4) returned null");
      $finish;
    end
    if (reg_found.get_name() != "reg2") begin
      $display("FAILED: get_reg_by_offset(4) returned %s, expected reg2", reg_found.get_name());
      $finish;
    end

    reg_found = map.get_reg_by_offset(64'h8);
    if (reg_found != null) begin
      $display("FAILED: get_reg_by_offset(8) should return null");
      $finish;
    end

    // Test lock_model
    block.lock_model();
    if (!block.is_locked()) begin
      $display("FAILED: is_locked() returned 0 after lock_model()");
      $finish;
    end

    $display("PASSED");
  end
endmodule
