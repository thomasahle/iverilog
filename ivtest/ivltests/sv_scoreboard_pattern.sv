// Test scoreboard pattern with queues for expected vs actual comparison
// Inspired by AVIP scoreboard patterns

class transaction;
  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit        write;

  constraint c_addr { addr[1:0] == 0; }  // Word aligned

  function bit compare(transaction other);
    return (addr == other.addr && data == other.data && write == other.write);
  endfunction

  function void display(string prefix);
    $display("%s addr=0x%08h data=0x%08h write=%b", prefix, addr, data, write);
  endfunction
endclass

class scoreboard;
  transaction expected_q[$];
  transaction actual_q[$];
  int match_count;
  int mismatch_count;

  function new();
    match_count = 0;
    mismatch_count = 0;
  endfunction

  function void add_expected(transaction t);
    expected_q.push_back(t);
  endfunction

  function void add_actual(transaction t);
    actual_q.push_back(t);
    check();
  endfunction

  function void check();
    transaction exp, act;
    while (expected_q.size() > 0 && actual_q.size() > 0) begin
      exp = expected_q.pop_front();
      act = actual_q.pop_front();

      if (exp.compare(act)) begin
        $display("MATCH: addr=0x%08h data=0x%08h", exp.addr, exp.data);
        match_count++;
      end else begin
        $display("MISMATCH:");
        exp.display("  Expected:");
        act.display("  Actual:  ");
        mismatch_count++;
      end
    end
  endfunction

  function void report();
    $display("");
    $display("Scoreboard Report:");
    $display("  Matches:    %0d", match_count);
    $display("  Mismatches: %0d", mismatch_count);
    $display("  Expected remaining: %0d", expected_q.size());
    $display("  Actual remaining:   %0d", actual_q.size());
  endfunction
endclass

module test;
  scoreboard sb;
  transaction tx_exp, tx_act;
  int i;

  initial begin
    sb = new();

    // Test 1: Perfect matches
    $display("Test 1: All transactions match");
    for (i = 0; i < 5; i++) begin
      tx_exp = new();
      void'(tx_exp.randomize());

      // Create matching actual
      tx_act = new();
      tx_act.addr = tx_exp.addr;
      tx_act.data = tx_exp.data;
      tx_act.write = tx_exp.write;

      sb.add_expected(tx_exp);
      sb.add_actual(tx_act);
    end

    // Test 2: One mismatch
    $display("");
    $display("Test 2: One mismatch");
    tx_exp = new();
    void'(tx_exp.randomize());
    tx_act = new();
    tx_act.addr = tx_exp.addr;
    tx_act.data = tx_exp.data + 1;  // Intentional mismatch
    tx_act.write = tx_exp.write;

    sb.add_expected(tx_exp);
    sb.add_actual(tx_act);

    sb.report();

    if (sb.match_count == 5 && sb.mismatch_count == 1)
      $display("PASSED");
    else
      $display("FAILED: expected 5 matches, 1 mismatch");

    $finish;
  end
endmodule
