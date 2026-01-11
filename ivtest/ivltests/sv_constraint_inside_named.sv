// Test inside constraint in named constraint block with literal constants
// Note: Using parameters in named inside constraints doesn't work (documented limitation)
//       Use literal constants or inline constraints as workaround

class Transaction;
  rand bit [15:0] addr;
  rand bit [7:0] data;

  // Named constraint with inside using literals - WORKS
  constraint addr_c {
    addr inside {[16'h1000:16'h2000]};
  }

  constraint data_c {
    data inside {[8'h10:8'h30]};
  }

  function new();
  endfunction
endclass

module test;
  Transaction t;
  int pass;
  int fail;

  initial begin
    t = new();
    pass = 0;
    fail = 0;

    repeat(20) begin
      if (!t.randomize()) begin
        $display("FAIL: randomize failed");
        fail++;
      end else begin
        if (t.addr < 16'h1000 || t.addr > 16'h2000) begin
          $display("FAIL: addr=%h outside [1000:2000]", t.addr);
          fail++;
        end else if (t.data < 8'h10 || t.data > 8'h30) begin
          $display("FAIL: data=%h outside [10:30]", t.data);
          fail++;
        end else begin
          pass++;
        end
      end
    end

    $display("Pass: %0d, Fail: %0d", pass, fail);
    if (fail == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
