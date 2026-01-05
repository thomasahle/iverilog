// Test string find() and rfind() methods
// find(substring) - returns position of first occurrence, or -1 if not found
// find(substring, start_pos) - search starting from start_pos
// rfind(substring) - returns position of last occurrence, or -1 if not found
// rfind(substring, end_pos) - search backwards starting from end_pos

module test;
  int pass = 1;

  initial begin
    string s;
    int pos;

    // Test basic find()
    s = "hello_world_test";
    pos = s.find("_");
    if (pos != 5) begin
      $display("FAIL: find('_') = %0d, expected 5", pos);
      pass = 0;
    end

    // Test find() with start position
    pos = s.find("_", 6);
    if (pos != 11) begin
      $display("FAIL: find('_', 6) = %0d, expected 11", pos);
      pass = 0;
    end

    // Test find() not found
    pos = s.find("xyz");
    if (pos != -1) begin
      $display("FAIL: find('xyz') = %0d, expected -1", pos);
      pass = 0;
    end

    // Test find() at beginning
    pos = s.find("hello");
    if (pos != 0) begin
      $display("FAIL: find('hello') = %0d, expected 0", pos);
      pass = 0;
    end

    // Test find() at end
    pos = s.find("test");
    if (pos != 12) begin
      $display("FAIL: find('test') = %0d, expected 12", pos);
      pass = 0;
    end

    // Test basic rfind()
    pos = s.rfind("_");
    if (pos != 11) begin
      $display("FAIL: rfind('_') = %0d, expected 11", pos);
      pass = 0;
    end

    // Test rfind() with end position
    pos = s.rfind("_", 10);
    if (pos != 5) begin
      $display("FAIL: rfind('_', 10) = %0d, expected 5", pos);
      pass = 0;
    end

    // Test rfind() not found
    pos = s.rfind("xyz");
    if (pos != -1) begin
      $display("FAIL: rfind('xyz') = %0d, expected -1", pos);
      pass = 0;
    end

    // Test rfind() with single occurrence
    s = "unique_word";
    pos = s.rfind("unique");
    if (pos != 0) begin
      $display("FAIL: rfind('unique') = %0d, expected 0", pos);
      pass = 0;
    end

    // Test find() with empty substring
    s = "test";
    pos = s.find("");
    if (pos != 0) begin
      $display("FAIL: find('') = %0d, expected 0", pos);
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
