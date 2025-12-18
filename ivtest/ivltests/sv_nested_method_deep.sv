// Test method calls through deeply nested class properties
// Tests obj.level1.level2.method() and obj.level1.level2.level3.method() patterns

class level3_class;
  int value;

  function new(int v);
    value = v;
  endfunction

  function int get_value();
    return value;
  endfunction

  function string sprint();
    return $sformatf("L3:value=%0d", value);
  endfunction
endclass

class level2_class;
  level3_class l3;
  int id;

  function new(int i, int v);
    id = i;
    l3 = new(v);
  endfunction

  function int get_id();
    return id;
  endfunction

  function string sprint();
    return $sformatf("L2:id=%0d,%s", id, l3.sprint());
  endfunction
endclass

class level1_class;
  level2_class l2;

  function new(int i, int v);
    l2 = new(i, v);
  endfunction

  function string sprint();
    return $sformatf("L1:%s", l2.sprint());
  endfunction
endclass

class top_class;
  level1_class l1;

  function new(int i, int v);
    l1 = new(i, v);
  endfunction
endclass

module test;
  initial begin
    top_class top;
    string s;
    int v;

    top = new(10, 42);

    // Test 2-level deep: top.l1.sprint()
    s = top.l1.sprint();
    if (s != "L1:L2:id=10,L3:value=42") begin
      $display("FAILED: 2-level deep sprint = '%s'", s);
      $finish;
    end

    // Test 3-level deep: top.l1.l2.sprint()
    s = top.l1.l2.sprint();
    if (s != "L2:id=10,L3:value=42") begin
      $display("FAILED: 3-level deep sprint = '%s'", s);
      $finish;
    end

    // Test 3-level deep: top.l1.l2.get_id()
    v = top.l1.l2.get_id();
    if (v != 10) begin
      $display("FAILED: 3-level deep get_id = %0d, expected 10", v);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
