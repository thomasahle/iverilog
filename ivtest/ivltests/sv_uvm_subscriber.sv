// Test uvm_subscriber receives transactions via analysis_export
// This verifies that the analysis_export is properly initialized
// and forwards transactions to the subscriber's write() method.

`include "uvm_pkg.sv"
import uvm_pkg::*;

// Transaction class
class my_transaction extends uvm_sequence_item;
  `uvm_object_utils(my_transaction)

  int value;

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("value=%0d", value);
  endfunction
endclass

// Subscriber class
class my_subscriber extends uvm_subscriber #(my_transaction);
  `uvm_component_utils(my_subscriber)

  int received_count;
  int last_value;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    received_count = 0;
    last_value = -1;
  endfunction

  virtual function void write(my_transaction t);
    received_count++;
    last_value = t.value;
    `uvm_info(get_type_name(), $sformatf("Received transaction: %s (count=%0d)", t.convert2string(), received_count), UVM_NONE)
  endfunction
endclass

// Producer component with analysis port
class my_producer extends uvm_component;
  `uvm_component_utils(my_producer)

  uvm_analysis_port #(my_transaction) ap;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction
endclass

// Test module
module test;
  my_producer producer;
  my_subscriber subscriber;
  my_transaction tx;
  int passed;

  initial begin
    passed = 1;

    // Create components
    producer = new("producer", null);
    subscriber = new("subscriber", null);

    // Connect producer's analysis port to subscriber's analysis_export
    producer.ap.connect(subscriber.analysis_export);

    // Send a transaction
    tx = new("tx");
    tx.value = 42;
    producer.ap.write(tx);

    // Send another transaction
    tx = new("tx2");
    tx.value = 100;
    producer.ap.write(tx);

    // Verify
    if (subscriber.received_count != 2) begin
      $display("FAILED: Expected 2 transactions, got %0d", subscriber.received_count);
      passed = 0;
    end

    if (subscriber.last_value != 100) begin
      $display("FAILED: Expected last_value=100, got %0d", subscriber.last_value);
      passed = 0;
    end

    if (passed) begin
      $display("PASSED: uvm_subscriber received %0d transactions correctly", subscriber.received_count);
    end

    $finish;
  end
endmodule
