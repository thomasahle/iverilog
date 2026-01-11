// Test if-else chain conditional size constraints (like AHB burstsize pattern)
// Pattern: if(enum == VAL1 || enum == VAL2) arr.size() == N; else if(...) ... else ...;

typedef enum { SINGLE, INCR, WRAP4, INCR4, WRAP8, INCR8, WRAP16, INCR16 } burst_t;

class Transaction;
  rand burst_t burst;
  rand bit [31:0] data[$];

  // Simpler conditional - single enum comparison
  constraint data_size {
    if (burst == SINGLE)
      data.size() == 1;
    else if (burst == INCR)
      data.size() == 1;
    else if (burst == WRAP4)
      data.size() == 4;
    else if (burst == INCR4)
      data.size() == 4;
    else if (burst == WRAP8)
      data.size() == 8;
    else if (burst == INCR8)
      data.size() == 8;
    else
      data.size() == 16;
  }

  function new();
  endfunction
endclass

module test;
  Transaction t;
  int pass_count;
  int fail_count;

  initial begin
    t = new();
    pass_count = 0;
    fail_count = 0;

    // Test each burst type with inline constraint forcing the value
    if (!t.randomize() with { burst == SINGLE; }) begin
      $display("FAIL: randomize failed for SINGLE");
      fail_count++;
    end else if (t.data.size() != 1) begin
      $display("FAIL: SINGLE expects size 1, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == INCR; }) begin
      $display("FAIL: randomize failed for INCR");
      fail_count++;
    end else if (t.data.size() != 1) begin
      $display("FAIL: INCR expects size 1, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == WRAP4; }) begin
      $display("FAIL: randomize failed for WRAP4");
      fail_count++;
    end else if (t.data.size() != 4) begin
      $display("FAIL: WRAP4 expects size 4, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == INCR4; }) begin
      $display("FAIL: randomize failed for INCR4");
      fail_count++;
    end else if (t.data.size() != 4) begin
      $display("FAIL: INCR4 expects size 4, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == WRAP8; }) begin
      $display("FAIL: randomize failed for WRAP8");
      fail_count++;
    end else if (t.data.size() != 8) begin
      $display("FAIL: WRAP8 expects size 8, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == INCR8; }) begin
      $display("FAIL: randomize failed for INCR8");
      fail_count++;
    end else if (t.data.size() != 8) begin
      $display("FAIL: INCR8 expects size 8, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == WRAP16; }) begin
      $display("FAIL: randomize failed for WRAP16");
      fail_count++;
    end else if (t.data.size() != 16) begin
      $display("FAIL: WRAP16 expects size 16, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    if (!t.randomize() with { burst == INCR16; }) begin
      $display("FAIL: randomize failed for INCR16");
      fail_count++;
    end else if (t.data.size() != 16) begin
      $display("FAIL: INCR16 expects size 16, got %0d", t.data.size());
      fail_count++;
    end else begin
      pass_count++;
    end

    $display("Passed: %0d, Failed: %0d", pass_count, fail_count);
    if (fail_count == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
