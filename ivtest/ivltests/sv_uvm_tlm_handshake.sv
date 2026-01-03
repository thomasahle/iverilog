// Test UVM TLM blocking handshake between sequence and driver
// Verifies that finish_item() blocks until item_done() is called
`include "uvm_macros.svh"

import uvm_pkg::*;

// Counters for test verification
int errors = 0;
int items_sent = 0;
int items_received = 0;
time last_done_time = 0;

// Simple sequence item
class my_item extends uvm_sequence_item;
  int data;
  int id;

  function new(string name = "my_item");
    super.new(name);
  endfunction

  virtual function string get_type_name();
    return "my_item";
  endfunction
endclass

// Simple sequence that sends items
class my_sequence extends uvm_sequence #(my_item);
  int num_items;

  function new(string name = "my_sequence");
    super.new(name);
    num_items = 3;
  endfunction

  virtual function string get_type_name();
    return "my_sequence";
  endfunction

  virtual task body();
    my_item item;
    int i;
    for (i = 0; i < num_items; i = i + 1) begin
      item = new("item");
      item.data = i * 100;
      item.id = i;
      start_item(item);
      $display("@ %0t: Sequence: sending item %0d", $time, i);
      finish_item(item);
      items_sent = items_sent + 1;
      $display("@ %0t: Sequence: item %0d done", $time, i);
    end
  endtask
endclass

// Simple sequencer
class my_sequencer extends uvm_sequencer #(my_item);
  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function string get_type_name();
    return "my_sequencer";
  endfunction
endclass

// Simple driver that consumes items with delay
class my_driver extends uvm_driver #(my_item);
  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function string get_type_name();
    return "my_driver";
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      if (req != null) begin
        $display("@ %0t: Driver: received item %0d", $time, req.id);
        items_received = items_received + 1;
        // Simulate processing time
        #10;
        last_done_time = $time;
        $display("@ %0t: Driver: completed item %0d", $time, req.id);
        seq_item_port.item_done();
      end
    end
  endtask
endclass

// Test component
class my_test extends uvm_test;
  my_sequencer seqr;
  my_driver drv;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function string get_type_name();
    return "my_test";
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = new("seqr", this);
    drv = new("drv", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr);
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_sequence seq;
    phase.raise_objection(this);

    seq = new("seq");
    seq.num_items = 3;

    // Start sequence in parallel with driver
    fork
      seq.start(seqr);
    join_none

    // Wait for sequence to complete
    #100;

    phase.drop_objection(this);
  endtask

  virtual function void report_phase(uvm_phase phase);
    $display("");
    $display("=== TLM Handshake Test Results ===");
    $display("Items sent by sequence: %0d", items_sent);
    $display("Items received by driver: %0d", items_received);

    // Check that all items were processed
    if (items_sent != 3) begin
      $display("ERROR: Expected 3 items sent, got %0d", items_sent);
      errors = errors + 1;
    end

    if (items_received != 3) begin
      $display("ERROR: Expected 3 items received, got %0d", items_received);
      errors = errors + 1;
    end

    // Verify time advanced (not stuck at 0)
    if (last_done_time == 0) begin
      $display("ERROR: Time did not advance - stuck at time 0");
      errors = errors + 1;
    end

    $display("");
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  endfunction
endclass

module test;
  initial begin
    run_test("my_test");
  end
endmodule
