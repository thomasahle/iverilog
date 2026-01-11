// Test constraints on multiple arrays with related sizes
// Verifies: addr.size() == len; data.size() == len;

module test;

  class Transaction;
    rand bit [3:0] len;
    rand bit [7:0] addr[];
    rand bit [31:0] data[];

    // Both arrays must match len
    constraint c_sizes {
      len >= 1;
      len <= 8;
      addr.size() == len;
      data.size() == len;
    }
  endclass

  initial begin
    Transaction tx;
    int i;

    tx = new();

    repeat (30) begin
      if (!tx.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Verify sizes match
      if (tx.addr.size() != tx.len) begin
        $display("FAILED: addr.size()=%0d but len=%0d", tx.addr.size(), tx.len);
        $finish;
      end
      if (tx.data.size() != tx.len) begin
        $display("FAILED: data.size()=%0d but len=%0d", tx.data.size(), tx.len);
        $finish;
      end

      $display("len=%0d, addr.size=%0d, data.size=%0d", tx.len, tx.addr.size(), tx.data.size());
    end

    $display("PASSED");
    $finish;
  end

endmodule
