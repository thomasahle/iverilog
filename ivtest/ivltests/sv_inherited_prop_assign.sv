// Test: Assignment to inherited property in task
// This mimics the UVM pattern where:
// - Base class has m_sequencer property
// - Derived class has start() task that assigns to m_sequencer
// - Another derived class further down the hierarchy uses m_sequencer

module test;

  class Base;
    string m_name;
    int m_value;

    function new(string name);
      m_name = name;
      m_value = 0;
    endfunction
  endclass

  // Middle class adds a property we'll assign to
  class SequenceBase extends Base;
    Base m_sequencer;
    Base m_parent;

    function new(string name);
      super.new(name);
      m_sequencer = null;
      m_parent = null;
    endfunction

    // Task that assigns to inherited property
    task start(Base sequencer, Base parent = null);
      $display("start(): assigning m_sequencer");
      m_sequencer = sequencer;
      $display("start(): m_sequencer.m_value = %0d", m_sequencer.m_value);
      m_parent = parent;
      body();
    endtask

    virtual task body();
      $display("SequenceBase::body()");
    endtask
  endclass

  // Derived sequence that uses m_sequencer in body()
  class Sequence extends SequenceBase;
    Base req;

    function new(string name);
      super.new(name);
      req = null;
    endfunction

    virtual task body();
      $display("Sequence::body() starting...");
      if (m_sequencer != null) begin
        $display("  m_sequencer.m_name = %s", m_sequencer.m_name);
        $display("  m_sequencer.m_value = %0d", m_sequencer.m_value);
        if (m_sequencer.m_value == 42)
          $display("PASS: m_sequencer is accessible in derived body()");
        else
          $display("FAIL: m_sequencer.m_value is wrong");
      end else begin
        $display("FAIL: m_sequencer is null in derived body()");
      end
    endtask
  endclass

  initial begin
    Base seqr;
    Sequence seq;

    // Create a sequencer
    seqr = new("my_sequencer");
    seqr.m_value = 42;

    // Create a sequence
    seq = new("my_sequence");

    $display("Testing inherited property assignment...");

    // Start the sequence - this should set m_sequencer
    seq.start(seqr);

    // Verify m_sequencer is still set after start() returns
    $display("After start():");
    if (seq.m_sequencer != null) begin
      $display("  seq.m_sequencer.m_value = %0d", seq.m_sequencer.m_value);
      if (seq.m_sequencer.m_value == 42)
        $display("PASSED");
      else
        $display("FAILED: wrong value");
    end else begin
      $display("FAILED: null");
    end
  end

endmodule
