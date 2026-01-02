// Test randomize() with inline constraints using enum values

typedef enum logic [15:0] {
  SLAVE_0 = 16'b0000_0000_0000_0001,
  SLAVE_1 = 16'b0000_0000_0000_0010
} slave_select_e;

class my_tx;
  rand logic [15:0] pselx;
  rand int data;

  function void post_randomize();
    $display("post_randomize: pselx=%h, data=%0d", pselx, data);
  endfunction
endclass

module test;
  initial begin
    my_tx tx;
    int pass_count;

    tx = new();
    pass_count = 0;

    // Test constraint with enum value
    repeat(10) begin
      if (!tx.randomize() with {pselx == SLAVE_0; data < 100;}) begin
        $display("FAIL: randomize failed");
        $finish;
      end
      if (tx.pselx !== 16'h0001) begin
        $display("FAIL: pselx=%h, expected 0001", tx.pselx);
        $finish;
      end
      if (tx.data >= 100) begin
        $display("FAIL: data=%0d, expected < 100", tx.data);
        $finish;
      end
      pass_count++;
    end

    if (pass_count == 10) begin
      $display("PASSED: All 10 randomizations with enum constraint succeeded");
    end else begin
      $display("FAIL: Only %0d passes", pass_count);
    end
  end
endmodule
