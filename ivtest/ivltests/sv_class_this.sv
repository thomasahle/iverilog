// Test 'this' keyword in class methods
class node;
  int value;
  node next_node;

  function new(int v);
    this.value = v;
    this.next_node = null;
  endfunction

  function void set_next(node n);
    this.next_node = n;
  endfunction

  function node get_this();
    return this;
  endfunction

  function int get_value();
    return this.value;
  endfunction
endclass

module test;
  node n1, n2, n3;
  node temp;
  int errors = 0;

  initial begin
    n1 = new(10);
    n2 = new(20);
    n3 = new(30);

    // Test this.value
    if (n1.get_value() != 10) begin
      $display("FAILED: n1.get_value() = %0d, expected 10", n1.get_value());
      errors++;
    end

    // Test get_this returns same object
    temp = n1.get_this();
    if (temp.value != 10) begin
      $display("FAILED: get_this().value = %0d, expected 10", temp.value);
      errors++;
    end

    // Test this.next_node
    n1.set_next(n2);
    n2.set_next(n3);

    if (n1.next_node.value != 20) begin
      $display("FAILED: n1.next_node.value = %0d, expected 20", n1.next_node.value);
      errors++;
    end
    if (n1.next_node.next_node.value != 30) begin
      $display("FAILED: chain value = %0d, expected 30", n1.next_node.next_node.value);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
