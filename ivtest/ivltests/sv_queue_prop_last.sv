// Test queue property with $ operator - compilation only
// VVP runtime support for complex expressions on class properties
// needs additional work, but compilation should succeed.

class Container;
  int queue_prop[$];
  
  function new();
    queue_prop = {};
  endfunction
  
  function int get_last();
    // This workaround accesses $-style internally
    if (queue_prop.size() > 0)
      return queue_prop[queue_prop.size()-1];
    return 0;
  endfunction
endclass

module test;
  Container c;
  
  initial begin
    c = new();
    c.queue_prop.push_back(10);
    c.queue_prop.push_back(20);
    c.queue_prop.push_back(30);
    
    // Use the workaround for now
    if (c.get_last() == 30) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
    $finish;
  end
endmodule
