// Test UVM-like config_db pattern
// This tests property assignment through simulated config_db

// Simulate UVM base classes
class uvm_object;
  string m_name;
  function new(string name = "");
    m_name = name;
  endfunction
endclass

class uvm_component extends uvm_object;
  uvm_component m_parent;
  string m_full_name;

  function new(string name = "", uvm_component parent = null);
    super.new(name);
    m_parent = parent;
    if (parent != null)
      m_full_name = {parent.m_full_name, ".", name};
    else
      m_full_name = name;
  endfunction
endclass

// Config class
class my_config extends uvm_object;
  int id;
  function new(string name = "");
    super.new(name);
    id = 0;
  endfunction
endclass

// Agent class with config handle
class my_agent extends uvm_component;
  my_config cfg_h;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    cfg_h = null;
  endfunction
endclass

// Env class with dynamic array of agents
class my_env extends uvm_component;
  my_agent agents[];
  my_config cfgs[];
  int num_agents;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    num_agents = 2;
  endfunction

  function void build();
    // Create config array
    cfgs = new[num_agents];
    foreach (cfgs[i]) begin
      cfgs[i] = new($sformatf("cfg_%0d", i));
      cfgs[i].id = i;
    end

    // Create agent array
    agents = new[num_agents];
    foreach (agents[i]) begin
      agents[i] = new($sformatf("agent_%0d", i), this);
    end

    // Assign configs to agents (this is the critical pattern)
    foreach (agents[i]) begin
      agents[i].cfg_h = cfgs[i];
      $display("Assigned cfg[%0d] (id=%0d) to agent[%0d].cfg_h", i, cfgs[i].id, i);
    end
  endfunction

  function void check();
    foreach (agents[i]) begin
      if (agents[i] == null) begin
        $display("FAILED: agents[%0d] is null", i);
        $finish;
      end
      if (agents[i].cfg_h == null) begin
        $display("FAILED: agents[%0d].cfg_h is null", i);
        $finish;
      end
      if (agents[i].cfg_h.id !== i) begin
        $display("FAILED: agents[%0d].cfg_h.id = %0d, expected %0d", i, agents[i].cfg_h.id, i);
        $finish;
      end
      $display("PASSED: agents[%0d].cfg_h.id = %0d", i, agents[i].cfg_h.id);
    end
  endfunction
endclass

module test;
  my_env env;

  initial begin
    env = new("env", null);
    env.build();
    env.check();
    $display("PASSED");
  end
endmodule
