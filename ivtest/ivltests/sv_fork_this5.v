// Test deeply nested fork chains (similar to UVM sequence pattern)
// This tests fork_this propagation through multiple levels

class Sequence;
  string name;
  int items_sent;

  function new(string n);
    name = n;
    items_sent = 0;
  endfunction

  // Entry point - forks the body
  task start();
    fork
      body();
    join_none
  endtask

  // Body calls send_item multiple times
  virtual task body();
    $display("%s: body starting", name);
    send_item(1);
    send_item(2);
    send_item(3);
    $display("%s: body complete, sent %0d items", name, items_sent);
  endtask

  // send_item calls start_item and finish_item
  task send_item(int data);
    start_item(data);
    finish_item(data);
  endtask

  task start_item(int data);
    $display("%s: start_item(%0d)", name, data);
  endtask

  task finish_item(int data);
    items_sent = items_sent + 1;
    $display("%s: finish_item(%0d), total=%0d", name, data, items_sent);
  endtask
endclass

module test;
  initial begin
    Sequence seq = new("test_seq");

    seq.start();
    #1;

    if (seq.items_sent !== 3) begin
      $display("FAILED: expected items_sent=3, got %0d", seq.items_sent);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
