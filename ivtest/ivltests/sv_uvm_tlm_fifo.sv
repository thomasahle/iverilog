// Test UVM TLM FIFO functionality

`include "uvm_pkg.sv"
import uvm_pkg::*;

class my_transaction extends uvm_sequence_item;
  rand int data;
  `uvm_object_utils(my_transaction)
  function new(string name = "my_transaction");
    super.new(name);
  endfunction
endclass

class test_env extends uvm_env;
  uvm_tlm_fifo #(my_transaction) fifo;
  int received_count = 0;

  `uvm_component_utils(test_env)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    fifo = new("fifo", this);
  endfunction

  task run_phase(uvm_phase phase);
    my_transaction tx_put, tx_get;
    phase.raise_objection(this);

    // Put some transactions
    for (int i = 0; i < 3; i++) begin
      tx_put = my_transaction::type_id::create("tx");
      tx_put.data = i * 10;
      `uvm_info("TEST", $sformatf("Putting data=%0d", tx_put.data), UVM_LOW)
      fifo.put(tx_put);
    end

    // Check size
    `uvm_info("TEST", $sformatf("FIFO size after puts: %0d", fifo.size()), UVM_LOW)

    // Get the transactions
    for (int i = 0; i < 3; i++) begin
      fifo.get(tx_get);
      `uvm_info("TEST", $sformatf("Got data=%0d", tx_get.data), UVM_LOW)
      received_count++;
    end

    phase.drop_objection(this);
  endtask

  function void check_phase(uvm_phase phase);
    if (received_count == 3) begin
      `uvm_info("TEST", "PASSED: All 3 transactions received via FIFO", UVM_LOW)
    end else begin
      `uvm_error("TEST", $sformatf("FAILED: Only received %0d transactions", received_count))
    end
  endfunction
endclass

class my_test extends uvm_test;
  test_env env;

  `uvm_component_utils(my_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = test_env::type_id::create("env", this);
  endfunction
endclass

module top;
  initial begin
    run_test("my_test");
  end
endmodule
