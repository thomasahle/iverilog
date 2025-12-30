// Test queue of class objects
// This tests that class objects can be stored in and retrieved from queues

class Item;
   int value;
   string name;

   function new(int v, string n);
      value = v;
      name = n;
   endfunction

   function void display();
      $display("Item: value=%0d, name=%s", value, name);
   endfunction
endclass

module test;
   Item queue_items[$];
   Item item;

   initial begin
      // Create and push some items
      item = new(10, "first");
      queue_items.push_back(item);

      item = new(20, "second");
      queue_items.push_back(item);

      item = new(30, "third");
      queue_items.push_front(item);

      $display("Queue size after pushes: %0d", queue_items.size());

      // Check the order: should be third, first, second
      if (queue_items.size() != 3) begin
         $display("FAILED: Expected size 3, got %0d", queue_items.size());
         $finish;
      end

      // Access elements
      if (queue_items[0].value != 30 || queue_items[0].name != "third") begin
         $display("FAILED: queue_items[0] incorrect");
         $finish;
      end

      if (queue_items[1].value != 10 || queue_items[1].name != "first") begin
         $display("FAILED: queue_items[1] incorrect");
         $finish;
      end

      if (queue_items[2].value != 20 || queue_items[2].name != "second") begin
         $display("FAILED: queue_items[2] incorrect");
         $finish;
      end

      // Pop from back
      item = queue_items.pop_back();
      if (item.value != 20) begin
         $display("FAILED: pop_back returned wrong item");
         $finish;
      end

      // Pop from front
      item = queue_items.pop_front();
      if (item.value != 30) begin
         $display("FAILED: pop_front returned wrong item");
         $finish;
      end

      // Should have one item left
      if (queue_items.size() != 1) begin
         $display("FAILED: Expected size 1 after pops, got %0d", queue_items.size());
         $finish;
      end

      if (queue_items[0].value != 10) begin
         $display("FAILED: Remaining item incorrect");
         $finish;
      end

      $display("PASSED");
      $finish;
   end
endmodule
