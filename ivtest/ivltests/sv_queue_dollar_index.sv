// Test $ index (last element) on queue class properties
module test;

   class Element;
      int id;
      string name;

      function new(int i = 0, string n = "");
         id = i;
         name = n;
      endfunction
   endclass

   class Container;
      Element items[$];  // Queue of class objects

      function void add(int i, string n);
         Element e = new(i, n);
         items.push_back(e);
      endfunction

      function Element get_last();
         return items[$];
      endfunction

      function Element get_prev();
         return items[$-1];
      endfunction
   endclass

   int pass = 1;

   initial begin
      Container c;
      Element e;

      c = new();
      c.add(1, "first");
      c.add(2, "second");
      c.add(3, "third");

      // Test $[-1] index via method
      e = c.get_prev();
      if (e.id != 2) begin
         $display("FAILED: get_prev() returned id=%0d, expected 2", e.id);
         pass = 0;
      end

      // Test items[$].id directly
      if (c.items[$].id != 3) begin
         $display("FAILED: items[$].id=%0d, expected 3", c.items[$].id);
         pass = 0;
      end

      // Test items[$].name directly
      if (c.items[$].name != "third") begin
         $display("FAILED: items[$].name=%s, expected 'third'", c.items[$].name);
         pass = 0;
      end

      // Test items[$-1].id directly
      if (c.items[$-1].id != 2) begin
         $display("FAILED: items[$-1].id=%0d, expected 2", c.items[$-1].id);
         pass = 0;
      end

      // Test pop_back on queue property
      e = c.items.pop_back;
      if (e.id != 3) begin
         $display("FAILED: pop_back returned id=%0d, expected 3", e.id);
         pass = 0;
      end

      // Verify size after pop
      if (c.items.size() != 2) begin
         $display("FAILED: items.size()=%0d, expected 2", c.items.size());
         pass = 0;
      end

      // Test $ again after pop
      if (c.items[$].id != 2) begin
         $display("FAILED: after pop, items[$].id=%0d, expected 2", c.items[$].id);
         pass = 0;
      end

      if (pass)
         $display("PASSED");
   end

endmodule
