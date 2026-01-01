// Simple test for TLM - uses uvm_object directly without parameterization

`include "uvm_macros.svh"
import uvm_pkg::*;

class my_transaction extends uvm_object;
  int value;
  string name;

  function new(string n = "my_transaction");
    super.new(n);
    value = 0;
    name = "";
  endfunction
endclass

// Simple analysis port that uses uvm_object directly
class simple_analysis_port extends uvm_object;
  uvm_object m_subscriber;

  function new(string name = "");
    super.new(name);
    m_subscriber = null;
  endfunction

  function void connect(uvm_object sub);
    m_subscriber = sub;
    $display("simple_analysis_port: connected subscriber");
  endfunction

  // Write using uvm_object directly - no parameterization
  function void write(uvm_object t);
    $display("simple_analysis_port.write: called");
    if (m_subscriber != null) begin
      $display("simple_analysis_port.write: forwarding to subscriber.tlm_write");
      m_subscriber.tlm_write(t);
    end
  endfunction
endclass

// Simple FIFO
class simple_fifo extends uvm_component;
  uvm_object m_item;
  bit has_item;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    has_item = 0;
  endfunction

  // Override tlm_write
  virtual function void tlm_write(uvm_object t);
    $display("simple_fifo.tlm_write: received item");
    m_item = t;
    has_item = 1;
  endfunction

  task get(output uvm_object t);
    while (!has_item) begin
      #1;
    end
    t = m_item;
    has_item = 0;
  endtask
endclass

class test extends uvm_test;
  simple_analysis_port ap;
  simple_fifo fifo;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap");
    fifo = new("fifo", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    ap.connect(fifo);
    $display("Connected ap to fifo");
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_transaction tx;
    uvm_object rx;
    phase.raise_objection(this);

    // Create and send a transaction
    tx = new("tx1");
    tx.value = 42;
    tx.name = "test_tx";
    $display("Sending transaction with value=%0d, name=%s", tx.value, tx.name);
    ap.write(tx);

    // Wait for FIFO and retrieve
    #10;
    fifo.get(rx);

    // Verify
    if ($cast(tx, rx)) begin
      $display("Received transaction with value=%0d, name=%s", tx.value, tx.name);
      if (tx.value == 42 && tx.name == "test_tx") begin
        $display("PASSED");
      end else begin
        $display("FAILED: values don't match");
      end
    end else begin
      $display("FAILED: could not cast received object");
    end

    phase.drop_objection(this);
  endtask
endclass

module test_top;
  initial begin
    run_test("test");
  end
endmodule
