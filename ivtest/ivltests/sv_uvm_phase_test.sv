// Test UVM-like phase traversal with component hierarchy
// Mimics the pattern where parent creates children and assigns configs

class uvm_phase;
  string name;
  function new(string n);
    name = n;
  endfunction
endclass

class Config;
  int id;
  function new(int i = 0);
    id = i;
  endfunction
endclass

class Component;
  string m_name;
  Component m_parent;
  Component m_children[];  // Use dynamic array
  int m_num_children;
  Config cfg;  // This is what gets assigned

  function new(string name, Component parent);
    m_name = name;
    m_parent = parent;
    m_num_children = 0;
    m_children = new[8];  // Pre-allocate
    cfg = null;
    if (parent != null) begin
      parent.add_child(this);
    end
  endfunction

  function void add_child(Component child);
    m_children[m_num_children] = child;
    m_num_children++;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    // Default: empty
  endfunction

  function void do_build_phase(uvm_phase phase);
    // Run own build_phase first
    build_phase(phase);
    // Then run children's
    for (int i = 0; i < m_num_children; i++) begin
      Component c;
      c = m_children[i];
      c.do_build_phase(phase);
    end
  endfunction
endclass

class Agent extends Component;
  function new(string name, Component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Agent needs to access cfg.id
    if (cfg == null) begin
      $display("FAILED: Agent %s - cfg is null in build_phase!", m_name);
      $finish;
    end
    $display("Agent %s: cfg.id = %0d", m_name, cfg.id);
  endfunction
endclass

class Env extends Component;
  Agent agents[];
  Config configs[];

  function new(string name, Component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create configs
    configs = new[3];
    for (int i = 0; i < 3; i++) begin
      configs[i] = new(100 + i);
    end

    // Create agents (they register as children)
    agents = new[3];
    for (int i = 0; i < 3; i++) begin
      agents[i] = new($sformatf("agent[%0d]", i), this);
    end

    // Assign configs to agents - THE CRITICAL PATTERN
    for (int i = 0; i < 3; i++) begin
      agents[i].cfg = configs[i];
    end

    $display("Env build_phase: created %0d agents, assigned configs", 3);
  endfunction
endclass

class Test extends Component;
  Env env;

  function new(string name);
    super.new(name, null);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = new("env", this);
    $display("Test build_phase: created env");
  endfunction
endclass

module test;
  Test t;
  uvm_phase phase;

  initial begin
    $display("Starting UVM-like phase test");

    phase = new("build");
    t = new("test");
    t.do_build_phase(phase);

    $display("PASSED");
  end
endmodule
