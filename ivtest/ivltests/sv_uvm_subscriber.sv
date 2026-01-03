// Test uvm_subscriber receives transactions via analysis_port
// Requires: iverilog -g2012 uvm_pkg.sv sv_uvm_subscriber.sv
import uvm_pkg::*;

// Simple transaction class
class my_tx extends uvm_sequence_item;
  int value;

  function new(string name = "my_tx");
    super.new(name);
  endfunction

  function void set_value(int v);
    value = v;
  endfunction
endclass

// Subscriber that counts received transactions
class my_subscriber extends uvm_subscriber #(my_tx);
  int received_count;
  int last_value;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    received_count = 0;
    last_value = 0;
  endfunction

  virtual function void write(my_tx t);
    received_count++;
    last_value = t.value;
    $display("Subscriber received transaction with value=%0d", t.value);
  endfunction
endclass

module test;
  initial begin
    uvm_analysis_port #(my_tx) port;
    my_subscriber sub;
    my_tx tx;

    // Create the port and subscriber
    port = new("port", null);
    sub = new("sub", null);

    // Connect port to subscriber's analysis_export
    port.connect(sub.analysis_export);

    // Create and send transactions
    tx = new("tx");
    tx.set_value(42);
    port.write(tx);

    tx = new("tx2");
    tx.set_value(100);
    port.write(tx);

    tx = new("tx3");
    tx.set_value(255);
    port.write(tx);

    // Check results
    $display("Received count: %0d", sub.received_count);
    $display("Last value: %0d", sub.last_value);

    if (sub.received_count == 3 && sub.last_value == 255)
      $display("PASSED");
    else
      $display("FAILED - expected count=3, last_value=255");
  end
endmodule
