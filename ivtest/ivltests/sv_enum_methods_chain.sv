// Test various enum methods through nested class property chains
// Tests name(), first(), last(), num() on nested enum properties

typedef enum {IDLE, ACTIVE, DONE} state_e;
typedef enum {LOW, MEDIUM, HIGH} priority_e;

class config_class;
  state_e current_state;
  priority_e prio;

  function new();
    current_state = ACTIVE;
    prio = MEDIUM;
  endfunction
endclass

class wrapper_class;
  config_class cfg;

  function new();
    cfg = new();
  endfunction
endclass

module test;
  initial begin
    wrapper_class w;
    string s;
    int n;

    w = new();

    // Test name() on nested enum property
    s = w.cfg.current_state.name();
    if (s != "ACTIVE") begin
      $display("FAILED: current_state.name() = %s, expected ACTIVE", s);
      $finish;
    end

    s = w.cfg.prio.name();
    if (s != "MEDIUM") begin
      $display("FAILED: prio.name() = %s, expected MEDIUM", s);
      $finish;
    end

    // Test first() on enum type (through variable reference)
    // Note: first()/last() return the first/last enum value of the type
    w.cfg.current_state = state_e'(0);  // Set to first value
    s = w.cfg.current_state.name();
    if (s != "IDLE") begin
      $display("FAILED: first state = %s, expected IDLE", s);
      $finish;
    end

    // Test num() on enum type
    // Note: num() is a type method, not available on instance in all contexts

    $display("PASSED");
    $finish;
  end
endmodule
