// Test virtual method call with inheritance chain
// More closely mimics UVM sequencer/sequence pattern

class uvm_object;
  string m_name;
  int m_verbosity = 1;
endclass

class uvm_sequence_item extends uvm_object;
  int m_parent_sequence;  // would be handle, using int for simplicity
endclass

class uvm_sequence_base extends uvm_sequence_item;
  int m_sequencer_handle;
endclass

class uvm_sequencer_base extends uvm_object;
  bit driver_ready = 0;  // property 2 in sequencer
  int queue_count = 0;   // property 3
  int pending_count = 0; // property 4

  virtual task wait_for_grant();
    // Access sequencer properties - should NOT crash
    $display("wait_for_grant: driver_ready=%0d, queue_count=%0d", driver_ready, queue_count);
    if (driver_ready !== 0 && driver_ready !== 1) begin
      $display("FAILED: driver_ready has invalid value %0d", driver_ready);
      $finish;
    end
  endtask
endclass

class uvm_sequencer extends uvm_sequencer_base;
  int extra_prop = 999;
endclass

class uvm_sequence extends uvm_sequence_base;
  uvm_sequencer_base m_sequencer;  // Note: this is property index 3
  uvm_sequence_item req;
  uvm_sequence_item rsp;

  // Only 6 properties total: m_name, m_verbosity, m_parent_sequence, m_sequencer, req, rsp
  // Sequencer has: m_name, m_verbosity, driver_ready, queue_count, pending_count = 5+ properties

  task start_item();
    // This call should use m_sequencer as 'this' inside wait_for_grant
    $display("start_item: calling m_sequencer.wait_for_grant()");
    m_sequencer.wait_for_grant();
    $display("start_item: returned from wait_for_grant");
  endtask
endclass

class axi4_sequence extends uvm_sequence;
  // Additional properties
  int burst_type = 1;
endclass

module test;
  initial begin
    axi4_sequence seq;
    uvm_sequencer sqr;

    sqr = new();
    sqr.m_name = "sqr";
    sqr.driver_ready = 1;
    sqr.queue_count = 5;

    seq = new();
    seq.m_name = "seq";
    seq.m_sequencer = sqr;

    $display("=== Test: Basic virtual method call ===");
    seq.start_item();

    $display("PASSED");
    $finish;
  end
endmodule
