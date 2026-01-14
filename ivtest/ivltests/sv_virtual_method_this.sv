// Test virtual method call passing correct 'this' object
// This tests that when A.b.method() is called, 'this' inside method is 'b' not 'A'
// Regression test for property index crash in UVM sequencer pattern

class sequencer;
  int prop_a = 100;
  int prop_b = 200;
  int prop_c = 300;

  virtual task wait_for_grant();
    // Access properties - this should access sequencer's props, not sequence's
    if (prop_a != 100) begin
      $display("FAILED: prop_a = %0d, expected 100", prop_a);
      $finish;
    end
    if (prop_b != 200) begin
      $display("FAILED: prop_b = %0d, expected 200", prop_b);
      $finish;
    end
    if (prop_c != 300) begin
      $display("FAILED: prop_c = %0d, expected 300", prop_c);
      $finish;
    end
    $display("Inside wait_for_grant: prop_a=%0d prop_b=%0d prop_c=%0d", prop_a, prop_b, prop_c);
  endtask
endclass

class sequence_base;
  string m_name = "seq";
  sequencer m_sequencer;

  task start_item();
    $display("Calling m_sequencer.wait_for_grant()");
    m_sequencer.wait_for_grant();
    $display("Returned from wait_for_grant");
  endtask
endclass

module test;
  initial begin
    sequence_base seq;
    sequencer sqr;

    sqr = new();
    seq = new();
    seq.m_sequencer = sqr;

    $display("Starting test");
    seq.start_item();
    $display("PASSED");
    $finish;
  end
endmodule
