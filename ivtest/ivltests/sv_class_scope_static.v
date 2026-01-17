// Test for class scope resolution for static member access (SV 8.20)
// ClassName::member syntax for accessing static class properties

module test;
  class my_cls;
    static int count = 0;
    static int value = 42;

    function new();
      count++;
    endfunction
  endclass

  class nested;
    static int x = 100;
    static string name = "nested";
  endclass

  my_cls obj1, obj2;
  int temp;

  initial begin
    // Direct access to static member
    temp = my_cls::value;
    if (temp !== 42) begin
      $display("FAILED: my_cls::value = %0d, expected 42", temp);
      $finish;
    end

    // Access before any objects created
    if (my_cls::count !== 0) begin
      $display("FAILED: my_cls::count = %0d before objects, expected 0", my_cls::count);
      $finish;
    end

    // Create objects - should increment count
    obj1 = new();
    obj2 = new();

    // Check count after creating objects
    if (my_cls::count !== 2) begin
      $display("FAILED: my_cls::count = %0d after 2 objects, expected 2", my_cls::count);
      $finish;
    end

    // Access static member of another class
    if (nested::x !== 100) begin
      $display("FAILED: nested::x = %0d, expected 100", nested::x);
      $finish;
    end

    // Modify static member through class scope
    my_cls::value = 99;
    if (my_cls::value !== 99) begin
      $display("FAILED: my_cls::value = %0d after assignment, expected 99", my_cls::value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
