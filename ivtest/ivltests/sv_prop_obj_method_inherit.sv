// Test: method call on property object with different property counts
// Reproduces bug where object stack isn't updated for method call
//
// Bug pattern from UVM:
// - uvm_sequence has 6 properties (0-5)
// - uvm_sequencer_base has 14+ properties
// - m_sequencer is property 2 of sequence
// - When calling m_sequencer.wait_for_grant(), the wait_for_grant method
//   tries to access sequencer properties (index 7+), but object stack
//   still has the sequence object with only 6 properties

module test;

  // Base class like uvm_object - 2 properties
  class Base;
    string m_name;       // property 0
    int m_verbosity;     // property 1

    function new(string name);
      m_name = name;
      m_verbosity = 0;
    endfunction
  endclass

  // Component class - adds 4 more properties = 6 total
  class Component extends Base;
    Base m_parent;        // property 2
    string m_full_name;   // property 3
    int m_children_count; // property 4
    int m_id;             // property 5

    function new(string name);
      super.new(name);
      m_parent = null;
      m_full_name = name;
      m_children_count = 0;
      m_id = 0;
    endfunction
  endclass

  // Sequencer - adds 8 more properties = 14 total
  class Sequencer extends Component;
    int queue_data[64];   // property 6
    int queue_head;       // property 7
    int queue_tail;       // property 8
    int queue_count;      // property 9
    bit item_done_flag;   // property 10
    Base current_item;    // property 11
    int pending_grants;   // property 12
    bit driver_ready;     // property 13

    function new(string name);
      super.new(name);
      queue_head = 0;
      queue_tail = 0;
      queue_count = 0;
      item_done_flag = 0;
      current_item = null;
      pending_grants = 0;
      driver_ready = 1;
    endfunction

    // This method accesses property 9 (queue_count) and 13 (driver_ready)
    task wait_for_grant();
      $display("wait_for_grant: driver_ready=%0d, queue_count=%0d", driver_ready, queue_count);
    endtask
  endclass

  // Sequence base - like uvm_sequence_base, has m_sequencer property
  class SequenceBase extends Base;
    Sequencer m_sequencer;      // property 2
    SequenceBase m_parent_seq;  // property 3

    function new(string name);
      super.new(name);
      m_sequencer = null;
      m_parent_seq = null;
    endfunction

    // This calls method on property object - the problematic pattern
    task start_item();
      if (m_sequencer != null) begin
        $display("start_item: calling m_sequencer.wait_for_grant()");
        m_sequencer.wait_for_grant();  // BUG: object stack may not switch
        $display("start_item: returned from wait_for_grant");
      end
    endtask
  endclass

  // Derived sequence with 2 more properties = 6 total
  class Sequence extends SequenceBase;
    Base req;  // property 4
    Base rsp;  // property 5

    function new(string name);
      super.new(name);
      req = null;
      rsp = null;
    endfunction
  endclass

  initial begin
    Sequencer sqr;
    Sequence seq;

    sqr = new("my_sequencer");
    seq = new("my_sequence");

    // Connect sequence to sequencer
    seq.m_sequencer = sqr;

    $display("Sequencer created, driver_ready=%0d", sqr.driver_ready);
    $display("Sequence created, calling start_item()...");

    // This should work - calls method on m_sequencer
    seq.start_item();

    $display("PASSED");
  end

endmodule
