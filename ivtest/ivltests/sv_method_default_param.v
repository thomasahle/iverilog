// Test method call without parentheses when method has default parameters
// This is a common UVM pattern: req.sprint instead of req.sprint()

class Formatter;
  string prefix;

  function new(string p = "");
    prefix = p;
  endfunction
endclass

class Transaction;
  int id;
  string name;

  function new(int i = 0, string n = "txn");
    id = i;
    name = n;
  endfunction

  // Method with default parameter - should work without parens
  function string sprint(Formatter fmt = null);
    if (fmt != null)
      return $sformatf("%s: Transaction{id=%0d, name=%s}", fmt.prefix, id, name);
    else
      return $sformatf("Transaction{id=%0d, name=%s}", id, name);
  endfunction

  // Method with multiple default parameters
  function string format(string prefix = "", string suffix = "");
    return $sformatf("%s%s%s", prefix, name, suffix);
  endfunction

  // Method returning int with default parameter
  function int get_adjusted_id(int offset = 0);
    return id + offset;
  endfunction
endclass

module test;
  Transaction txn;
  string s;
  int val;

  initial begin
    txn = new(100, "test_txn");

    // Test 1: sprint without parens (default null formatter)
    s = txn.sprint;
    $display("Test 1 - sprint: %s", s);
    if (s != "Transaction{id=100, name=test_txn}") begin
      $display("FAILED: Test 1");
      $finish;
    end

    // Test 2: format without parens (multiple defaults)
    s = txn.format;
    $display("Test 2 - format: %s", s);
    if (s != "test_txn") begin
      $display("FAILED: Test 2");
      $finish;
    end

    // Test 3: get_adjusted_id without parens
    val = txn.get_adjusted_id;
    $display("Test 3 - get_adjusted_id: %0d", val);
    if (val != 100) begin
      $display("FAILED: Test 3");
      $finish;
    end

    // Test 4: Use in expression
    if (txn.get_adjusted_id == 100) begin
      $display("Test 4 - expression: PASSED");
    end else begin
      $display("FAILED: Test 4");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
