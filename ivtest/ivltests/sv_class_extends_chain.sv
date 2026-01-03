// Test class inheritance chain (3 levels)
class grandparent;
  int gp_value;
  function new();
    gp_value = 100;
  endfunction
  virtual function string get_name();
    return "grandparent";
  endfunction
endclass

class parent extends grandparent;
  int p_value;
  function new();
    super.new();
    p_value = 200;
  endfunction
  virtual function string get_name();
    return "parent";
  endfunction
endclass

class child extends parent;
  int c_value;
  function new();
    super.new();
    c_value = 300;
  endfunction
  virtual function string get_name();
    return "child";
  endfunction
  function int get_total();
    return gp_value + p_value + c_value;
  endfunction
endclass

module test;
  grandparent gp;
  parent p;
  child c;
  int errors = 0;

  initial begin
    // Test child class
    c = new();
    if (c.gp_value != 100 || c.p_value != 200 || c.c_value != 300) begin
      $display("FAILED: child values gp=%0d p=%0d c=%0d", c.gp_value, c.p_value, c.c_value);
      errors++;
    end
    if (c.get_total() != 600) begin
      $display("FAILED: get_total() = %0d, expected 600", c.get_total());
      errors++;
    end
    if (c.get_name() != "child") begin
      $display("FAILED: child.get_name() = %s", c.get_name());
      errors++;
    end

    // Test polymorphism - child assigned to grandparent
    gp = c;
    if (gp.get_name() != "child") begin
      $display("FAILED: polymorphic get_name() = %s, expected child", gp.get_name());
      errors++;
    end

    // Test parent class
    p = new();
    if (p.gp_value != 100 || p.p_value != 200) begin
      $display("FAILED: parent values gp=%0d p=%0d", p.gp_value, p.p_value);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
