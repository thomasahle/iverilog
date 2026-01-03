// Test case statements
module test;
  int value;
  string result;
  int errors = 0;

  function automatic string get_color(int code);
    case (code)
      0: return "red";
      1: return "green";
      2: return "blue";
      default: return "unknown";
    endcase
  endfunction

  function automatic int get_priority(int level);
    // Regular case with multiple values
    if (level >= 0 && level <= 3)
      return 1;
    else if (level >= 4 && level <= 7)
      return 2;
    else if (level >= 8 && level <= 15)
      return 3;
    else
      return 0;
  endfunction

  initial begin
    // Test regular case
    if (get_color(0) != "red") begin
      $display("FAILED: get_color(0) = %s", get_color(0));
      errors++;
    end
    if (get_color(2) != "blue") begin
      $display("FAILED: get_color(2) = %s", get_color(2));
      errors++;
    end
    if (get_color(99) != "unknown") begin
      $display("FAILED: get_color(99) = %s", get_color(99));
      errors++;
    end

    // Test priority function
    if (get_priority(0) != 1) begin
      $display("FAILED: get_priority(0) = %0d", get_priority(0));
      errors++;
    end
    if (get_priority(5) != 2) begin
      $display("FAILED: get_priority(5) = %0d", get_priority(5));
      errors++;
    end
    if (get_priority(10) != 3) begin
      $display("FAILED: get_priority(10) = %0d", get_priority(10));
      errors++;
    end
    if (get_priority(100) != 0) begin
      $display("FAILED: get_priority(100) = %0d", get_priority(100));
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
