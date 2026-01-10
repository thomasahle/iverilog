// Test string concatenation with function results returning non-string types
// Tests that getc() and user functions returning int can be used in string concat
module test;
  string s, s2;

  function int get_char(int i);
    return i + 65;  // Return 'A' + i
  endfunction

  initial begin
    s = "Hi";
    s2 = "";

    // Test getc in string concatenation - this used to crash
    s2 = {s2, s.getc(0)};  // Should add 'H' (72)
    s2 = {s2, s.getc(1)};  // Should add 'i' (105)
    if (s2 != "Hi") begin
      $display("FAILED - expected 'Hi', got '%s'", s2);
      $finish;
    end

    // Test building string from characters in a loop
    s = "World";
    s2 = "";
    for (int i = 0; i < s.len(); i++) begin
      s2 = {s2, s.getc(i)};
    end
    if (s2 != "World") begin
      $display("FAILED - expected 'World', got '%s'", s2);
      $finish;
    end

    // Test with integer expression in string concat
    s2 = {8'd65, 8'd66, 8'd67};  // A, B, C
    if (s2 != "ABC") begin
      $display("FAILED - expected 'ABC', got '%s'", s2);
      $finish;
    end

    // Test user function returning int in string concat
    s2 = "";
    s2 = {s2, get_char(0)};  // Should add 'A' (65)
    s2 = {s2, get_char(1)};  // Should add 'B' (66)
    if (s2 != "AB") begin
      $display("FAILED - expected 'AB', got '%s'", s2);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
