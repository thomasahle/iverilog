// Test TLM analysis port forwarding to FIFO
// Verifies that analysis_port.write() forwards to connected FIFOs

`include "uvm_macros.svh"
`include "uvm_pkg.sv"
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

// A monitor that writes to an analysis port
class my_monitor extends uvm_monitor;
  uvm_analysis_port #(my_transaction) ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  task send_transaction(int v, string n);
    my_transaction t;
    t = new();
    t.value = v;
    t.name = n;
    // Cast to uvm_object for write (workaround for VVP parameterized method bug)
    ap.write(t);
  endtask
endclass

// A scoreboard that reads from an analysis FIFO
class my_scoreboard extends uvm_component;
  uvm_tlm_analysis_fifo #(my_transaction) fifo;
  int received_count;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    fifo = new("fifo", this);
    received_count = 0;
  endfunction

  task run_phase(uvm_phase phase);
    my_transaction t;
    forever begin
      fifo.get(t);
      received_count++;
      $display("Scoreboard received: value=%0d, name=%s", t.value, t.name);
    end
  endtask
endclass

class test extends uvm_test;
  my_monitor mon;
  my_scoreboard sb;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = new("mon", this);
    sb = new("sb", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor's analysis port to scoreboard's FIFO
    mon.ap.connect(sb.fifo.analysis_export);
    $display("Connected monitor.ap to scoreboard.fifo.analysis_export");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    // Give scoreboard time to start
    #10;

    // Send some transactions
    $display("Sending transaction 1...");
    mon.send_transaction(42, "first");
    #10;

    $display("Sending transaction 2...");
    mon.send_transaction(100, "second");
    #10;

    $display("Sending transaction 3...");
    mon.send_transaction(999, "third");
    #10;

    // Wait for scoreboard to process
    #50;

    // Check results
    if (sb.received_count == 3) begin
      $display("PASSED: Scoreboard received %0d transactions", sb.received_count);
    end else begin
      $display("FAILED: Expected 3 transactions, got %0d", sb.received_count);
    end

    phase.drop_objection(this);
  endtask
endclass

module test_top;
  initial begin
    run_test("test");
  end
endmodule
