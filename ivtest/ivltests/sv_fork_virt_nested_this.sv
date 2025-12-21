// Test fork/virt with nested method calls accessing 'this'
// This tests the pattern used in UVM phases where a forked virtual method
// calls helper methods that need to access class properties through 'this'

class Component;
  string m_name;
  int m_id;

  function new(string name, int id);
    m_name = name;
    m_id = id;
  endfunction

  // Helper method that accesses 'this' properties
  function string get_full_name();
    return $sformatf("%s[%0d]", m_name, m_id);
  endfunction

  // Helper that accesses 'this' through another method call
  function void report_status();
    $display("Component %s status OK", get_full_name());
  endfunction

  // Virtual method that will be forked
  virtual function void build_phase();
    // Access property directly
    $display("build_phase for %s", m_name);
    // Call helper method that accesses 'this'
    report_status();
  endfunction
endclass

class Agent extends Component;
  int m_active;

  function new(string name, int id);
    super.new(name, id);
    m_active = 1;
  endfunction

  // Override virtual method
  virtual function void build_phase();
    // Access parent's property
    $display("Agent build_phase for %s, active=%0d", m_name, m_active);
    // Call inherited helper
    report_status();
    // Call local helper
    check_active();
  endfunction

  function void check_active();
    if (m_active == 1) begin
      $display("Agent %s is active", get_full_name());
    end
  endfunction
endclass

module test;
  Component comp;
  Agent agent;

  initial begin
    $display("Test 1: Direct call to virtual method with nested this access");
    comp = new("comp", 1);
    comp.build_phase();
    $display("Test 1 PASSED");

    $display("");
    $display("Test 2: Forked virtual method with nested this access");
    agent = new("agent", 2);
    fork
      agent.build_phase();
    join
    $display("Test 2 PASSED");

    $display("");
    $display("Test 3: Multiple forked calls");
    fork
      begin
        Component c1 = new("c1", 10);
        c1.build_phase();
      end
      begin
        Agent a1 = new("a1", 20);
        a1.build_phase();
      end
    join
    $display("Test 3 PASSED");

    $display("");
    $display("PASSED");
  end
endmodule
