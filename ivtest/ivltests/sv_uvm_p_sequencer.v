// Test uvm_declare_p_sequencer macro
// This macro should declare a p_sequencer handle of the specified type

`include "uvm_pkg.sv"
`include "uvm_macros.svh"

import uvm_pkg::*;

// Custom sequencer class
class my_sequencer extends uvm_sequencer #(uvm_sequence_item);
  int my_config_value;

  function new(string name = "my_sequencer", uvm_component parent = null);
    super.new(name, parent);
    my_config_value = 42;
  endfunction

  virtual function string get_type_name();
    return "my_sequencer";
  endfunction
endclass

// Sequence that uses p_sequencer
class my_sequence extends uvm_sequence #(uvm_sequence_item);
  // Use the macro to declare p_sequencer
  `uvm_declare_p_sequencer(my_sequencer)

  function new(string name = "my_sequence");
    super.new(name);
  endfunction

  virtual function string get_type_name();
    return "my_sequence";
  endfunction

  virtual task body();
    // Access p_sequencer (will be null in this simple test, but declaration should work)
    if (p_sequencer == null) begin
      $display("p_sequencer is null (expected in standalone test)");
    end else begin
      $display("p_sequencer.my_config_value = %0d", p_sequencer.my_config_value);
    end
  endtask
endclass

module test;
  initial begin
    my_sequence seq;
    my_sequencer seqr;

    // Create sequence and sequencer
    seq = new("test_seq");
    seqr = new("test_seqr", null);

    // Manually set p_sequencer for testing
    seq.p_sequencer = seqr;

    // Now check we can access the sequencer through p_sequencer
    if (seq.p_sequencer != null) begin
      if (seq.p_sequencer.my_config_value == 42) begin
        $display("PASSED");
      end else begin
        $display("FAILED: my_config_value = %0d, expected 42", seq.p_sequencer.my_config_value);
      end
    end else begin
      $display("FAILED: p_sequencer should not be null after assignment");
    end
  end
endmodule
