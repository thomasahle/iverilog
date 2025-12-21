// Test extern method declarations with 'this' pointer access
// This tests the pattern used in UVM testbenches with out-of-body method definitions

class Config;
  int id;
  string name;

  function new(int i = 0, string n = "");
    id = i;
    name = n;
  endfunction
endclass

class Agent;
  Config cfg;
  int active;

  // Extern function declarations
  extern function new(string name = "");
  extern function void build();
  extern function int get_cfg_id();
endclass

// Out-of-body definitions
function Agent::new(string name = "");
  cfg = null;
  active = 1;
endfunction

function void Agent::build();
  // This tests accessing 'this' in extern method
  if (active == 1) begin
    cfg = new(100, "test_config");
  end
endfunction

function int Agent::get_cfg_id();
  // This tests accessing properties through 'this'
  if (cfg != null) begin
    return cfg.id;
  end
  return -1;
endfunction

module test;
  Agent agent;

  initial begin
    $display("Test 1: Create agent with extern constructor");
    agent = new("test_agent");
    if (agent.active !== 1) begin
      $display("FAILED: active = %0d, expected 1", agent.active);
      $finish;
    end
    $display("Test 1 PASSED");

    $display("Test 2: Call extern method that accesses this.property");
    agent.build();
    if (agent.cfg == null) begin
      $display("FAILED: cfg is null after build()");
      $finish;
    end
    $display("Test 2 PASSED");

    $display("Test 3: Call extern method that returns property value");
    if (agent.get_cfg_id() !== 100) begin
      $display("FAILED: get_cfg_id() = %0d, expected 100", agent.get_cfg_id());
      $finish;
    end
    $display("Test 3 PASSED");

    $display("PASSED");
  end
endmodule
