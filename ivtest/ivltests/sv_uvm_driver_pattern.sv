// Test UVM-style driver pattern without virtual interface
// Uses class hierarchy and delegation

class transaction;
  rand bit [7:0] data;
  rand bit [3:0] delay;

  constraint c_delay { delay inside {[0:5]}; }

  function void display(string prefix);
    $display("%s data=0x%02h delay=%0d", prefix, data, delay);
  endfunction
endclass

class driver_base;
  int transactions_sent;

  function new();
    transactions_sent = 0;
  endfunction

  virtual task drive(transaction tx);
    $display("driver_base: drive called (should be overridden)");
  endtask
endclass

class my_driver extends driver_base;
  function new();
    super.new();
  endfunction

  virtual task drive(transaction tx);
    // Simulate delay
    #(tx.delay * 10);
    $display("my_driver: driving data=0x%02h after %0d delay", tx.data, tx.delay);
    transactions_sent++;
  endtask
endclass

class sequencer;
  driver_base drv;
  transaction tx_queue[$];

  function new(driver_base d);
    drv = d;
  endfunction

  function void add_transaction(transaction tx);
    tx_queue.push_back(tx);
  endfunction

  task run();
    transaction tx;
    while (tx_queue.size() > 0) begin
      tx = tx_queue.pop_front();
      drv.drive(tx);
    end
  endtask
endclass

module test;
  my_driver drv;
  sequencer seq;
  transaction tx;
  int i;

  initial begin
    drv = new();
    seq = new(drv);

    // Generate and queue transactions
    for (i = 0; i < 5; i++) begin
      tx = new();
      if (!tx.randomize()) begin
        $display("FAILED: randomize failed");
        $finish;
      end
      tx.display($sformatf("Queued [%0d]:", i));
      seq.add_transaction(tx);
    end

    $display("");
    $display("Running sequencer...");
    seq.run();

    $display("");
    $display("Transactions sent: %0d", drv.transactions_sent);

    if (drv.transactions_sent == 5)
      $display("PASSED");
    else
      $display("FAILED: expected 5 transactions");

    $finish;
  end
endmodule
