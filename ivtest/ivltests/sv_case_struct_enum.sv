// Test case statement with struct enum member
// Verifies: case(struct.enumMember) pattern
// Note: Direct case(cfg.mode) crashes VPI - use temp variable workaround

module test;

  typedef enum int {
    MODE_IDLE = 0,
    MODE_RUN = 1,
    MODE_STOP = 2
  } mode_e;

  typedef struct {
    mode_e mode;
    int data;
  } config_t;

  config_t cfg;
  mode_e temp_mode;
  string result;

  initial begin
    // Test case with struct enum member - via temp variable workaround
    cfg.mode = MODE_IDLE;
    cfg.data = 100;

    // Access struct enum via temp variable (workaround for VPI limitation)
    temp_mode = cfg.mode;

    case (temp_mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    $display("Mode: %s, result: %s", temp_mode.name(), result);
    if (result != "idle") begin
      $display("FAILED: Expected 'idle' for MODE_IDLE");
      $finish;
    end

    // Change mode
    cfg.mode = MODE_RUN;
    temp_mode = cfg.mode;
    case (temp_mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    if (result != "run") begin
      $display("FAILED: Expected 'run' for MODE_RUN");
      $finish;
    end

    // Test MODE_STOP
    cfg.mode = MODE_STOP;
    temp_mode = cfg.mode;
    case (temp_mode)
      MODE_IDLE: result = "idle";
      MODE_RUN:  result = "run";
      MODE_STOP: result = "stop";
      default:   result = "unknown";
    endcase

    if (result != "stop") begin
      $display("FAILED: Expected 'stop' for MODE_STOP");
      $finish;
    end

    $display("PASSED");
    $finish;
  end

endmodule
