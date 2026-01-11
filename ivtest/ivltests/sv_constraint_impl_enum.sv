// Test implication constraint with enum condition (UART AVIP pattern)
// Pattern: hasParity == PARITY_DISABLED -> parityErrorInjection == 0

typedef enum { PARITY_ENABLED, PARITY_DISABLED } parity_mode_t;

class UartConfig;
  rand parity_mode_t hasParity;
  rand bit parityErrorInjection;

  constraint set_parity_condition {
    hasParity == PARITY_DISABLED -> parityErrorInjection == 0;
  }

  function new();
  endfunction
endclass

module test;
  UartConfig cfg;
  int pass;
  int fail;

  initial begin
    cfg = new();
    pass = 0;
    fail = 0;

    // Test: when parity disabled, error injection must be 0
    repeat(10) begin
      if (!cfg.randomize() with { hasParity == PARITY_DISABLED; }) begin
        $display("FAIL: randomize failed");
        fail++;
      end else if (cfg.parityErrorInjection != 0) begin
        $display("FAIL: parity disabled but errorInjection = %0d", cfg.parityErrorInjection);
        fail++;
      end else begin
        pass++;
      end
    end

    // Test: when parity enabled, error injection can be either 0 or 1
    repeat(10) begin
      if (!cfg.randomize() with { hasParity == PARITY_ENABLED; }) begin
        $display("FAIL: randomize failed for enabled");
        fail++;
      end else begin
        pass++;
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
