// Test UVM RAL uvm_reg_adapter class
// Tests basic adapter functionality

// Include UVM package directly for Icarus
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  // Simple test adapter that overrides the base class
  class test_adapter extends uvm_reg_adapter;
    `uvm_object_utils(test_adapter)

    function new(string name = "test_adapter");
      super.new(name);
      supports_byte_enable = 1;
      provides_responses = 1;
    endfunction

    // Override reg2bus to create a simple sequence item
    virtual function uvm_sequence_item reg2bus(input uvm_reg_bus_op rw);
      uvm_sequence_item item = new("bus_item");
      // Just return a generic sequence item for testing
      return item;
    endfunction

    // Override bus2reg task
    virtual task bus2reg(input uvm_sequence_item bus_item,
                         output uvm_access_e kind,
                         output uvm_reg_addr_t addr,
                         output uvm_reg_data_t data,
                         output uvm_status_e status);
      // Return test values
      kind = UVM_READ;
      addr = 64'h1234;
      data = 64'hABCD;
      status = UVM_IS_OK;
    endtask
  endclass

  initial begin
    test_adapter adapter;
    uvm_sequence_item item;
    uvm_access_e kind;
    uvm_reg_addr_t addr;
    uvm_reg_data_t data;
    uvm_status_e status;

    // Create adapter
    adapter = new("my_adapter");

    // Test get_name
    if (adapter.get_name() != "my_adapter") begin
      $display("FAILED: get_name() returned %s, expected my_adapter", adapter.get_name());
      $finish;
    end

    // Test configuration flags
    if (!adapter.supports_byte_enable) begin
      $display("FAILED: supports_byte_enable should be 1");
      $finish;
    end

    if (!adapter.provides_responses) begin
      $display("FAILED: provides_responses should be 1");
      $finish;
    end

    // Test bus2reg (simpler test without struct assignment)
    item = new("test_item");
    adapter.bus2reg(item, kind, addr, data, status);
    if (kind !== UVM_READ) begin
      $display("FAILED: bus2reg() kind should be UVM_READ");
      $finish;
    end
    if (addr !== 64'h1234) begin
      $display("FAILED: bus2reg() addr should be 0x1234, got %0h", addr);
      $finish;
    end
    if (data !== 64'hABCD) begin
      $display("FAILED: bus2reg() data should be 0xABCD, got %0h", data);
      $finish;
    end
    if (status !== UVM_IS_OK) begin
      $display("FAILED: bus2reg() status should be UVM_IS_OK");
      $finish;
    end

    $display("PASSED");
  end
endmodule
