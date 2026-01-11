// Test array of class handles
// Verifies: dynamic array and queue of class handles
// Note: `q.push_back(new(...))` not supported - use explicit construction

module test;

  class Item;
    int value;
    string name;

    function new(int v, string n);
      value = v;
      name = n;
    endfunction
  endclass

  Item items[$];       // Queue of class handles
  Item arr[];          // Dynamic array of class handles
  Item temp;
  int i;

  initial begin
    // Test queue of class handles - explicit construction
    temp = new(10, "first");
    items.push_back(temp);
    temp = new(20, "second");
    items.push_back(temp);
    temp = new(30, "third");
    items.push_back(temp);

    $display("Queue size: %0d", items.size());
    if (items.size() != 3) begin
      $display("FAILED: Expected queue size 3");
      $finish;
    end

    // Access via index
    if (items[0].value != 10) begin
      $display("FAILED: items[0].value should be 10");
      $finish;
    end

    if (items[1].name != "second") begin
      $display("FAILED: items[1].name should be 'second'");
      $finish;
    end

    // Pop and verify
    temp = items.pop_front();
    if (temp.value != 10) begin
      $display("FAILED: pop_front value should be 10");
      $finish;
    end

    // Test $ index
    if (items[$].value != 30) begin
      $display("FAILED: items[$].value should be 30");
      $finish;
    end

    // Test dynamic array of class handles
    arr = new[3];
    arr[0] = new(100, "a");
    arr[1] = new(200, "b");
    arr[2] = new(300, "c");

    if (arr.size() != 3) begin
      $display("FAILED: Expected arr size 3");
      $finish;
    end

    if (arr[1].value != 200) begin
      $display("FAILED: arr[1].value should be 200");
      $finish;
    end

    // Iterate
    for (i = 0; i < arr.size(); i++) begin
      $display("arr[%0d]: value=%0d name=%s", i, arr[i].value, arr[i].name);
    end

    $display("PASSED");
    $finish;
  end

endmodule
