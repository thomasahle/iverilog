// Test that multiple static method calls execute in the correct order
// This verifies that push_statement_back maintains statement order

class logger;
  static int log_v0 = 0;
  static int log_v1 = 0;
  static int log_v2 = 0;
  static int log_v3 = 0;
  static int log_v4 = 0;
  static int log_idx = 0;

  static function void record(int value);
    case (log_idx)
      0: log_v0 = value;
      1: log_v1 = value;
      2: log_v2 = value;
      3: log_v3 = value;
      4: log_v4 = value;
    endcase
    log_idx = log_idx + 1;
  endfunction

  static function int get_value(int idx);
    case (idx)
      0: return log_v0;
      1: return log_v1;
      2: return log_v2;
      3: return log_v3;
      4: return log_v4;
    endcase
    return -1;
  endfunction

  static function int count();
    return log_idx;
  endfunction
endclass

module test;
  int errors = 0;

  initial begin
    // Multiple static calls should execute in order
    logger::record(100);
    logger::record(200);
    logger::record(300);
    logger::record(400);
    logger::record(500);

    // Verify count
    if (logger::count() != 5) begin
      $display("FAILED: count=%0d, expected 5", logger::count());
      errors = errors + 1;
    end

    // Verify order - values should be 100, 200, 300, 400, 500
    if (logger::get_value(0) != 100) begin
      $display("FAILED: log[0]=%0d, expected 100", logger::get_value(0));
      errors = errors + 1;
    end
    if (logger::get_value(1) != 200) begin
      $display("FAILED: log[1]=%0d, expected 200", logger::get_value(1));
      errors = errors + 1;
    end
    if (logger::get_value(2) != 300) begin
      $display("FAILED: log[2]=%0d, expected 300", logger::get_value(2));
      errors = errors + 1;
    end
    if (logger::get_value(3) != 400) begin
      $display("FAILED: log[3]=%0d, expected 400", logger::get_value(3));
      errors = errors + 1;
    end
    if (logger::get_value(4) != 500) begin
      $display("FAILED: log[4]=%0d, expected 500", logger::get_value(4));
      errors = errors + 1;
    end

    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d errors", errors);
    end
    $finish;
  end
endmodule
