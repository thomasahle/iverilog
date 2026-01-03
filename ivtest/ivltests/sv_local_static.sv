// Test module-level static variables (local statics in functions not fully supported)
module test;
  int errors = 0;

  // Module-level counters work as expected
  static int global_count = 0;
  static int global_id = 100;

  function automatic int counter();
    global_count++;
    return global_count;
  endfunction

  function automatic int get_id();
    int id;
    id = global_id;
    global_id++;
    return id;
  endfunction

  initial begin
    int c1, c2, c3;
    int id1, id2, id3;

    // Test counter with module-level static
    c1 = counter();
    c2 = counter();
    c3 = counter();
    if (c1 != 1 || c2 != 2 || c3 != 3) begin
      $display("FAILED: counter - c1=%0d, c2=%0d, c3=%0d", c1, c2, c3);
      errors++;
    end

    // Test ID generator
    id1 = get_id();
    id2 = get_id();
    id3 = get_id();
    if (id1 != 100 || id2 != 101 || id3 != 102) begin
      $display("FAILED: get_id - id1=%0d, id2=%0d, id3=%0d", id1, id2, id3);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
