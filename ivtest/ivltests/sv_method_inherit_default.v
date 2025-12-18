// Test inherited method call without parentheses
// Methods inherited from base class should also work without parens

class BaseTransaction;
  int id;

  function new(int i = 0);
    id = i;
  endfunction

  // Virtual method with default parameter
  virtual function string sprint(string prefix = "");
    return $sformatf("%sBase{id=%0d}", prefix, id);
  endfunction

  // Non-virtual method with default parameter
  function int get_id(int offset = 0);
    return id + offset;
  endfunction
endclass

class DerivedTransaction extends BaseTransaction;
  string name;

  function new(int i = 0, string n = "derived");
    super.new(i);
    name = n;
  endfunction

  // Override virtual method
  virtual function string sprint(string prefix = "");
    return $sformatf("%sDerived{id=%0d, name=%s}", prefix, id, name);
  endfunction
endclass

class GrandchildTransaction extends DerivedTransaction;
  int priority_val;

  function new(int i = 0, string n = "grandchild", int p = 5);
    super.new(i, n);
    priority_val = p;
  endfunction

  // Override again
  virtual function string sprint(string prefix = "");
    return $sformatf("%sGrandchild{id=%0d, name=%s, pri=%0d}", prefix, id, name, priority_val);
  endfunction
endclass

module test;
  BaseTransaction base_txn;
  DerivedTransaction derived_txn;
  GrandchildTransaction grand_txn;
  string s;
  int val;

  initial begin
    base_txn = new(1);
    derived_txn = new(2, "derived_test");
    grand_txn = new(3, "grand_test", 10);

    // Test 1: Base class sprint without parens
    s = base_txn.sprint;
    $display("Test 1 - base sprint: %s", s);
    if (s != "Base{id=1}") begin
      $display("FAILED: Test 1");
      $finish;
    end

    // Test 2: Derived class sprint without parens (overridden)
    s = derived_txn.sprint;
    $display("Test 2 - derived sprint: %s", s);
    if (s != "Derived{id=2, name=derived_test}") begin
      $display("FAILED: Test 2");
      $finish;
    end

    // Test 3: Grandchild class sprint without parens
    s = grand_txn.sprint;
    $display("Test 3 - grandchild sprint: %s", s);
    if (s != "Grandchild{id=3, name=grand_test, pri=10}") begin
      $display("FAILED: Test 3");
      $finish;
    end

    // Test 4: Inherited non-virtual method without parens
    val = derived_txn.get_id;
    $display("Test 4 - inherited get_id: %0d", val);
    if (val != 2) begin
      $display("FAILED: Test 4");
      $finish;
    end

    // Test 5: Inherited method on grandchild
    val = grand_txn.get_id;
    $display("Test 5 - grandchild inherited get_id: %0d", val);
    if (val != 3) begin
      $display("FAILED: Test 5");
      $finish;
    end

    // Note: Polymorphic method calls without parens currently use static dispatch
    // (based on declared type) rather than dynamic dispatch. Use explicit ()
    // for polymorphic calls.

    $display("PASSED");
    $finish;
  end
endmodule
