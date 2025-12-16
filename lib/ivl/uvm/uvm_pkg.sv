// Minimal UVM implementation for Icarus Verilog
// This provides basic UVM functionality sufficient to run simple testbenches
//
// KNOWN LIMITATIONS:
// 1. Virtual method dispatch issue: When overriding phase methods (build_phase, run_phase, etc.)
//    in classes defined outside the package, the virtual dispatch may not work correctly through
//    the do_*_phase() wrapper methods. Workaround: Call phase methods directly on your test class.
// 2. No fork/join_none in class tasks due to VVP assertion failure
// 3. $cast not supported - use direct assignment
// 4. No self-referential typedef patterns (causes segfault)
// 5. Queues of class objects cause segfaults - use fixed arrays instead

package uvm_pkg;

  // ============================================================================
  // UVM Verbosity Levels
  // ============================================================================
  typedef enum int {
    UVM_NONE   = 0,
    UVM_LOW    = 100,
    UVM_MEDIUM = 200,
    UVM_HIGH   = 300,
    UVM_FULL   = 400,
    UVM_DEBUG  = 500
  } uvm_verbosity;

  // ============================================================================
  // UVM Active/Passive Enum
  // ============================================================================
  typedef enum bit {
    UVM_PASSIVE = 0,
    UVM_ACTIVE = 1
  } uvm_active_passive_enum;

  // ============================================================================
  // UVM Severity Levels
  // ============================================================================
  typedef enum int {
    UVM_INFO    = 0,
    UVM_WARNING = 1,
    UVM_ERROR   = 2,
    UVM_FATAL   = 3
  } uvm_severity;

  // ============================================================================
  // Forward declarations
  // ============================================================================
  typedef class uvm_object;
  typedef class uvm_component;
  typedef class uvm_phase;
  typedef class uvm_root;
  typedef class uvm_sequencer_base;
  typedef class uvm_sequence_base;
  typedef class uvm_printer;
  typedef class uvm_comparer;

  // Forward declarations for RAL
  typedef class uvm_reg_field;
  typedef class uvm_reg;
  typedef class uvm_reg_file;
  typedef class uvm_reg_block;
  typedef class uvm_reg_map;
  typedef class uvm_reg_adapter;
  typedef class uvm_reg_frontdoor;

  // ============================================================================
  // UVM Radix Enum (for printing)
  // ============================================================================
  typedef enum int {
    UVM_BIN     = 0,
    UVM_DEC     = 1,
    UVM_UNSIGNED = 2,
    UVM_OCT     = 3,
    UVM_HEX     = 4,
    UVM_STRING  = 5,
    UVM_TIME    = 6,
    UVM_ENUM    = 7,
    UVM_REAL    = 8,
    UVM_REAL_DEC = 9,
    UVM_REAL_EXP = 10,
    UVM_NORADIX = 11
  } uvm_radix_enum;

  // ============================================================================
  // UVM RAL Type Definitions
  // ============================================================================
  typedef bit [63:0] uvm_reg_addr_t;
  typedef bit [63:0] uvm_reg_data_t;

  // Access type enumeration (for register operations)
  // Note: Using explicit bit width for packed struct compatibility
  typedef enum logic [1:0] {
    UVM_READ       = 2'b00,
    UVM_WRITE      = 2'b01,
    UVM_BURST_READ = 2'b10,
    UVM_BURST_WRITE = 2'b11
  } uvm_access_e;

  // Status enumeration
  // Note: Using explicit bit width for packed struct compatibility
  typedef enum logic [1:0] {
    UVM_IS_OK  = 2'b00,
    UVM_NOT_OK = 2'b01,
    UVM_HAS_X  = 2'b10
  } uvm_status_e;

  // Path enumeration (for register access)
  typedef enum {
    UVM_FRONTDOOR,
    UVM_BACKDOOR,
    UVM_PREDICT,
    UVM_DEFAULT_PATH
  } uvm_path_e;

  // Check enumeration
  typedef enum {
    UVM_NO_CHECK,
    UVM_CHECK
  } uvm_check_e;

  // Endianness enumeration
  typedef enum {
    UVM_NO_ENDIAN,
    UVM_LITTLE_ENDIAN,
    UVM_BIG_ENDIAN,
    UVM_LITTLE_FIFO,
    UVM_BIG_FIFO
  } uvm_endianness_e;

  // Hierarchy enumeration
  typedef enum {
    UVM_NO_HIER,
    UVM_HIER
  } uvm_hier_e;

  // Prediction type
  typedef enum {
    UVM_PREDICT_DIRECT,
    UVM_PREDICT_READ,
    UVM_PREDICT_WRITE
  } uvm_predict_e;

  // Register bus operation struct - used by adapter
  // Note: Converted to packed struct for Icarus compatibility
  // (Icarus doesn't support unpacked struct member assignment)
  typedef struct packed {
    uvm_access_e kind;       // UVM_READ or UVM_WRITE (2 bits)
    uvm_reg_addr_t addr;     // Register address (64 bits)
    uvm_reg_data_t data;     // Read/write data (64 bits)
    logic [31:0] n_bits;     // Number of bits to transfer (32 bits)
    uvm_status_e status;     // Status of operation (2 bits)
    logic [7:0] byte_en;     // Byte enables (8 bits)
  } uvm_reg_bus_op;

  // ============================================================================
  // UVM Printer - For formatted printing of objects
  // ============================================================================
  class uvm_printer;
    string m_string;
    int    m_indent;

    function new();
      m_string = "";
      m_indent = 0;
    endfunction

    // Get indent string (helper function)
    function string get_indent();
      string indent_str = "";
      for (int i = 0; i < m_indent; i++) indent_str = {indent_str, " "};
      return indent_str;
    endfunction

    // Print a field with given name, value, size and radix
    virtual function void print_field(string name, logic [1023:0] value, int size, uvm_radix_enum radix = UVM_HEX);
      string val_str;
      case (radix)
        UVM_BIN: $sformat(val_str, "%0b", value);
        UVM_DEC: $sformat(val_str, "%0d", value);
        UVM_HEX: $sformat(val_str, "%0h", value);
        UVM_OCT: $sformat(val_str, "%0o", value);
        default: $sformat(val_str, "%0h", value);
      endcase
      $display("%s%s: %s", get_indent(), name, val_str);
    endfunction

    // Print a string field
    virtual function void print_string(string name, string value);
      $display("%s%s: %s", get_indent(), name, value);
    endfunction

    // Print an object reference
    virtual function void print_object(string name, uvm_object value);
      if (value == null)
        $display("%s%s: null", get_indent(), name);
      else
        $display("%s%s: %s", get_indent(), name, value.get_name());
    endfunction

    // Print a generic value
    virtual function void print_generic(string name, string type_name, int size, string value);
      $display("%s%s: (%s) %s", get_indent(), name, type_name, value);
    endfunction

    // Increase indent
    function void push_indent();
      m_indent += 2;
    endfunction

    // Decrease indent
    function void pop_indent();
      if (m_indent >= 2) m_indent -= 2;
    endfunction
  endclass

  // ============================================================================
  // UVM Comparer - For comparing objects
  // ============================================================================
  class uvm_comparer;
    int unsigned show_max;
    int unsigned verbosity;
    uvm_severity sev;
    string miscompares;
    int unsigned physical;
    int unsigned abstract_;
    int unsigned check_type;
    int result;

    function new();
      show_max = 1;
      verbosity = UVM_LOW;
      sev = UVM_INFO;
      miscompares = "";
      physical = 1;
      abstract_ = 1;
      check_type = 1;
      result = 0;
    endfunction

    // Compare two field values
    virtual function bit compare_field(string name, logic [1023:0] lhs, logic [1023:0] rhs, int size, uvm_radix_enum radix = UVM_HEX);
      if (lhs !== rhs) begin
        result++;
        return 0;
      end
      return 1;
    endfunction

    // Compare two integer values
    virtual function bit compare_field_int(string name, logic [63:0] lhs, logic [63:0] rhs, int size, uvm_radix_enum radix = UVM_DEC);
      if (lhs !== rhs) begin
        result++;
        return 0;
      end
      return 1;
    endfunction

    // Compare two string values
    virtual function bit compare_string(string name, string lhs, string rhs);
      if (lhs != rhs) begin
        result++;
        return 0;
      end
      return 1;
    endfunction

    // Compare two object references
    virtual function bit compare_object(string name, uvm_object lhs, uvm_object rhs);
      if (lhs == null && rhs == null)
        return 1;
      if (lhs == null || rhs == null) begin
        result++;
        return 0;
      end
      // Both non-null - compare using object's compare method
      if (!lhs.compare(rhs)) begin
        result++;
        return 0;
      end
      return 1;
    endfunction

    // Get the comparison result (0 = match, >0 = number of miscompares)
    function int get_result();
      return result;
    endfunction

    // Reset the comparer for a new comparison
    function void reset();
      result = 0;
      miscompares = "";
    endfunction
  endclass

  // ============================================================================
  // UVM Phase Class
  // ============================================================================
  class uvm_phase;
    string name;
    int objection_count;

    function new(string name = "");
      this.name = name;
      this.objection_count = 0;
    endfunction

    function void raise_objection(uvm_object obj, string description = "", int count = 1);
      objection_count += count;
    endfunction

    function void drop_objection(uvm_object obj, string description = "", int count = 1);
      objection_count -= count;
      if (objection_count < 0) objection_count = 0;
    endfunction

    function bit is_done();
      return (objection_count == 0);
    endfunction
  endclass

  // ============================================================================
  // UVM Object - Base class for all UVM objects
  // ============================================================================
  class uvm_object;
    protected string m_name;
    protected int m_verbosity;

    function new(string name = "");
      m_name = name;
      m_verbosity = UVM_MEDIUM;
    endfunction

    virtual function string get_name();
      return m_name;
    endfunction

    virtual function void set_name(string name);
      m_name = name;
    endfunction

    virtual function string get_full_name();
      return m_name;
    endfunction

    virtual function string get_type_name();
      return "uvm_object";
    endfunction

    virtual function void print(int verbosity = 0);
      uvm_printer printer = new();
      $display("Object: %s", get_full_name());
      do_print(printer);
    endfunction

    // Override this method to print object fields
    virtual function void do_print(uvm_printer printer);
      // Base implementation does nothing - override in derived classes
    endfunction

    // Return a string representation of the object
    virtual function string sprint(uvm_printer printer = null);
      return {"[", get_type_name(), ":", get_name(), "]"};
    endfunction

    // Convert to string (alias for sprint)
    virtual function string convert2string();
      return sprint();
    endfunction

    virtual function uvm_object clone();
      return null;
    endfunction

    virtual function void copy(uvm_object rhs);
    endfunction

    virtual function bit compare(uvm_object rhs);
      uvm_comparer comparer = new();
      return do_compare(rhs, comparer);
    endfunction

    // Override this method to compare object fields
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      // Base implementation returns 1 (equal) - override in derived classes
      return 1;
    endfunction

    function void set_report_verbosity_level(int verbosity);
      m_verbosity = verbosity;
    endfunction

    function int get_report_verbosity_level();
      return m_verbosity;
    endfunction
  endclass

  // ============================================================================
  // UVM Component - Base class for all structural components
  // ============================================================================
  class uvm_component extends uvm_object;
    uvm_component m_parent;
    string m_full_name;
    // Note: Using simple array - max 32 children per component
    uvm_component m_children[32];
    int m_num_children;

    function new(string name = "", uvm_component parent = null);
      super.new(name);
      m_parent = parent;
      m_num_children = 0;
      if (parent != null) begin
        parent.add_child(this);
        m_full_name = {parent.get_full_name(), ".", name};
      end else begin
        m_full_name = name;
      end
    endfunction

    virtual function string get_full_name();
      return m_full_name;
    endfunction

    virtual function string get_type_name();
      return "uvm_component";
    endfunction

    function uvm_component get_parent();
      return m_parent;
    endfunction

    function void add_child(uvm_component child);
      if (m_num_children < 32) begin
        m_children[m_num_children] = child;
        m_num_children++;
      end
    endfunction

    function int get_num_children();
      return m_num_children;
    endfunction

    // Phase methods - to be overridden by subclasses
    virtual function void build_phase(uvm_phase phase);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
    endfunction

    virtual function void start_of_simulation_phase(uvm_phase phase);
    endfunction

    virtual task run_phase(uvm_phase phase);
      // Base class run_phase - should be overridden by test
      $display("UVM_DEBUG: uvm_component::run_phase base class called for %s (SHOULD BE OVERRIDDEN!)", get_full_name());
    endtask

    virtual function void extract_phase(uvm_phase phase);
    endfunction

    virtual function void check_phase(uvm_phase phase);
    endfunction

    virtual function void report_phase(uvm_phase phase);
    endfunction

    virtual function void final_phase(uvm_phase phase);
    endfunction

    // Phase execution - iterate through children
    virtual function void do_build_phase(uvm_phase phase);
      build_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_build_phase(phase);
      end
    endfunction

    virtual function void do_connect_phase(uvm_phase phase);
      connect_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_connect_phase(phase);
      end
    endfunction

    virtual function void do_end_of_elaboration_phase(uvm_phase phase);
      end_of_elaboration_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_end_of_elaboration_phase(phase);
      end
    endfunction

    virtual function void do_start_of_simulation_phase(uvm_phase phase);
      start_of_simulation_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_start_of_simulation_phase(phase);
      end
    endfunction

    virtual task do_run_phase(uvm_phase phase);
      // Run parent's run_phase first (starts sequences), then children (drivers)
      // This is a simplified approach - not true parallel execution
      $display("UVM_DEBUG: do_run_phase for %s (type=%s)", get_full_name(), get_type_name());
      // NOTE: Call through 'this' to attempt virtual dispatch
      this.run_phase(phase);
      $display("UVM_DEBUG: do_run_phase %s - starting children", get_full_name());
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_run_phase(phase);
      end
      $display("UVM_DEBUG: do_run_phase %s - complete", get_full_name());
    endtask

    virtual function void do_extract_phase(uvm_phase phase);
      extract_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_extract_phase(phase);
      end
    endfunction

    virtual function void do_check_phase(uvm_phase phase);
      check_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_check_phase(phase);
      end
    endfunction

    virtual function void do_report_phase(uvm_phase phase);
      report_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_report_phase(phase);
      end
    endfunction

    virtual function void do_final_phase(uvm_phase phase);
      final_phase(phase);
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.do_final_phase(phase);
      end
    endfunction

    virtual function void print_topology(string prefix = "");
      $display("%s%s (%s)", prefix, get_full_name(), get_type_name());
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.print_topology({prefix, "  "});
      end
    endfunction
  endclass

  // ============================================================================
  // UVM Sequence Item - Base class for transaction items
  // ============================================================================
  class uvm_sequence_item extends uvm_object;
    uvm_sequencer_base m_sequencer;
    uvm_sequence_base m_parent_sequence;

    function new(string name = "uvm_sequence_item");
      super.new(name);
    endfunction

    virtual function string get_type_name();
      return "uvm_sequence_item";
    endfunction

    function void set_sequencer(uvm_sequencer_base sequencer);
      m_sequencer = sequencer;
    endfunction

    function uvm_sequencer_base get_sequencer();
      return m_sequencer;
    endfunction

    function void set_parent_sequence(uvm_sequence_base parent);
      m_parent_sequence = parent;
    endfunction

    function uvm_sequence_base get_parent_sequence();
      return m_parent_sequence;
    endfunction

    // Copy method - override in derived classes to copy field values
    virtual function void do_copy(uvm_object rhs);
      // Base implementation - derived classes should copy their fields
    endfunction

    // Compare method - override in derived classes to compare field values
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer = null);
      return 1; // Base implementation returns true
    endfunction
  endclass

  // ============================================================================
  // UVM Sequence Base
  // ============================================================================
  class uvm_sequence_base extends uvm_object;
    uvm_sequencer_base m_sequencer;
    uvm_sequence_base m_parent_sequence;

    function new(string name = "uvm_sequence_base");
      super.new(name);
    endfunction

    virtual function string get_type_name();
      return "uvm_sequence_base";
    endfunction

    virtual task body();
    endtask

    virtual task pre_body();
    endtask

    virtual task post_body();
    endtask

    virtual task start(uvm_sequencer_base sequencer, uvm_sequence_base parent_sequence = null);
      m_sequencer = sequencer;
      m_parent_sequence = parent_sequence;
      $display("UVM_DEBUG: sequence.start() - calling pre_body()");
      pre_body();
      $display("UVM_DEBUG: sequence.start() - calling body()");
      body();
      $display("UVM_DEBUG: sequence.start() - calling post_body()");
      post_body();
      $display("UVM_DEBUG: sequence.start() - complete");
    endtask

    function uvm_sequencer_base get_sequencer();
      return m_sequencer;
    endfunction
  endclass

  // ============================================================================
  // UVM Sequence - Parameterized sequence class
  // ============================================================================
  class uvm_sequence #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequence_base;
    REQ req;
    RSP rsp;

    function new(string name = "uvm_sequence");
      super.new(name);
    endfunction

    virtual function string get_type_name();
      return "uvm_sequence";
    endfunction

    // Note: Using base class type since Icarus doesn't fully support
    // type parameter coercion in method calls
    virtual task start_item(uvm_sequence_item item, int set_priority = -1);
      item.set_sequencer(m_sequencer);
      item.set_parent_sequence(this);
    endtask

    // Note: Using base class type since Icarus doesn't fully support
    // type parameter coercion in method calls
    virtual task finish_item(uvm_sequence_item item, int set_priority = -1);
      uvm_sequencer_base sqr;
      sqr = m_sequencer;
      if (sqr != null)
        sqr.send_request(item);
    endtask
  endclass

  // ============================================================================
  // TLM Port/Export Classes - Simplified for Icarus
  // ============================================================================
  // Note: Actual TLM ports not fully implemented. Use direct sequencer reference instead.
  // The connect() method is a stub that stores reference to sequencer.

  // Simple TLM port wrapper that holds a sequencer reference
  class uvm_seq_item_port_wrapper extends uvm_object;
    uvm_sequencer_base m_sequencer;

    function new(string name = "");
      super.new(name);
    endfunction

    // Connect to sequencer export (which is just the sequencer itself)
    function void connect(uvm_sequencer_base export_ref);
      m_sequencer = export_ref;
    endfunction

    // Get next item from connected sequencer
    task get_next_item(output uvm_sequence_item item);
      if (m_sequencer != null)
        m_sequencer.get_next_item(item);
    endtask

    // Signal item is done
    function void item_done(uvm_sequence_item item = null);
      if (m_sequencer != null)
        m_sequencer.item_done(item);
    endfunction
  endclass

  // ============================================================================
  // UVM Sequencer Base
  // ============================================================================
  class uvm_sequencer_base extends uvm_component;
    // Using fixed-size array instead of queue
    uvm_sequence_item request_queue[64];
    int queue_head;
    int queue_tail;
    int queue_count;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      queue_head = 0;
      queue_tail = 0;
      queue_count = 0;
    endfunction

    virtual function string get_type_name();
      return "uvm_sequencer_base";
    endfunction

    virtual task send_request(uvm_sequence_item item);
      if (queue_count < 64) begin
        request_queue[queue_tail] = item;
        queue_tail = (queue_tail + 1) % 64;
        queue_count++;
      end
    endtask

    virtual task get_next_item(output uvm_sequence_item item);
      // Poll until item is available
      while (queue_count == 0) begin
        #1;
      end
      item = request_queue[queue_head];
      queue_head = (queue_head + 1) % 64;
      queue_count--;
    endtask

    virtual function void item_done(uvm_sequence_item item = null);
      // Signal that item processing is complete
    endfunction
  endclass

  // ============================================================================
  // UVM Sequencer - Parameterized sequencer class
  // ============================================================================
  class uvm_sequencer #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequencer_base;
    // Note: Factory registration (type_id) handled by parser at ClassName::type_id::create()
    // which transforms into direct new() call

    // Simplified TLM export - just holds reference to self for connect()
    uvm_sequencer_base seq_item_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      seq_item_export = this;
    endfunction

    virtual function string get_type_name();
      return "uvm_sequencer";
    endfunction
  endclass

  // ============================================================================
  // UVM Driver - Base class for drivers
  // ============================================================================
  class uvm_driver #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_component;
    // Note: Factory registration (type_id) handled by parser at ClassName::type_id::create()
    // which transforms into direct new() call

    // Simplified TLM port - wrapper that holds reference to connected sequencer
    uvm_seq_item_port_wrapper seq_item_port;
    REQ req;
    RSP rsp;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      seq_item_port = new("seq_item_port");
    endfunction

    virtual function string get_type_name();
      return "uvm_driver";
    endfunction

    virtual task get_next_item(output REQ item);
      uvm_sequence_item base_item;
      if (seq_item_port != null) begin
        seq_item_port.get_next_item(base_item);
        item = base_item;
      end
    endtask

    // item_done without argument (for simple completion)
    virtual function void item_done();
      if (seq_item_port != null)
        seq_item_port.item_done(null);
    endfunction
  endclass

  // ============================================================================
  // UVM Monitor - Base class for monitors
  // ============================================================================
  class uvm_monitor extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function string get_type_name();
      return "uvm_monitor";
    endfunction
  endclass

  // ============================================================================
  // UVM Analysis Port - TLM port for broadcasting (simplified)
  // NOTE: Moved before uvm_subscriber so it can be used as a type
  // ============================================================================
  class uvm_analysis_port #(type T = int) extends uvm_object;
    function new(string name = "", uvm_component parent = null);
      super.new(name);
    endfunction

    virtual function void connect(uvm_object port);
      // Simplified - no actual connection tracking
    endfunction

    // Note: Using uvm_object instead of T due to Icarus limitation
    // with type parameter resolution in method parameters
    virtual function void write(uvm_object t);
      // Simplified - override in subclass for actual functionality
    endfunction
  endclass

  // ============================================================================
  // UVM Analysis Export - TLM export for receiving analysis transactions
  // ============================================================================
  class uvm_analysis_export #(type T = int) extends uvm_object;
    function new(string name = "", uvm_component parent = null);
      super.new(name);
    endfunction

    virtual function void connect(uvm_object port);
      // Simplified - no actual connection tracking
    endfunction

    virtual function void write(T t);
      // Simplified - override in subclass for actual functionality
    endfunction
  endclass

  // ============================================================================
  // UVM Analysis Imp - TLM implementation for receiving analysis transactions
  // ============================================================================
  class uvm_analysis_imp #(type T = int, type IMP = uvm_component) extends uvm_object;
    IMP m_imp;

    function new(string name = "", IMP imp = null);
      super.new(name);
      m_imp = imp;
    endfunction

    virtual function void write(T t);
      // Calls write method on the implementing component
      // In actual UVM, this calls imp.write(t)
    endfunction
  endclass

  // ============================================================================
  // UVM Subscriber - Analysis component that subscribes to transactions
  // ============================================================================
  class uvm_subscriber #(type T = uvm_sequence_item) extends uvm_component;
    // Analysis export for receiving transactions
    // Note: Using uvm_object instead of full parameterized type to avoid Icarus elaboration issues
    uvm_object analysis_export;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      // analysis_export initialization deferred - user code should not rely on this
    endfunction

    virtual function string get_type_name();
      return "uvm_subscriber";
    endfunction

    // Override this function to process received transactions
    virtual function void write(T t);
      // Base implementation - override in derived classes
    endfunction
  endclass

  // ============================================================================
  // UVM Agent - Base class for agents
  // ============================================================================
  class uvm_agent extends uvm_component;
    uvm_active_passive_enum is_active;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      is_active = UVM_ACTIVE;
    endfunction

    virtual function string get_type_name();
      return "uvm_agent";
    endfunction

    virtual function uvm_active_passive_enum get_is_active();
      return is_active;
    endfunction
  endclass

  // ============================================================================
  // UVM Scoreboard - Base class for scoreboards
  // ============================================================================
  class uvm_scoreboard extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function string get_type_name();
      return "uvm_scoreboard";
    endfunction
  endclass

  // ============================================================================
  // UVM Environment - Base class for environments
  // ============================================================================
  class uvm_env extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function string get_type_name();
      return "uvm_env";
    endfunction
  endclass

  // ============================================================================
  // UVM Test - Base class for tests
  // ============================================================================
  class uvm_test extends uvm_component;
    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function string get_type_name();
      return "uvm_test";
    endfunction
  endclass

  // ============================================================================
  // UVM Root - Top of the component hierarchy
  // ============================================================================
  class uvm_root extends uvm_component;
    static uvm_root m_inst;
    uvm_component m_test;

    function new();
      super.new("uvm_root", null);
      m_full_name = "";
    endfunction

    static function uvm_root get();
      if (m_inst == null)
        m_inst = new();
      return m_inst;
    endfunction

    // run_test must be a task because it calls tasks and waits
    task run_test(string test_name = "");
      uvm_phase phase;

      phase = new("build");

      // Run phases
      $display("UVM_INFO: Starting UVM phases...");

      // Build phase
      if (m_test != null) begin
        $display("UVM_INFO: Running build_phase...");
        m_test.do_build_phase(phase);
      end

      // Connect phase
      phase.name = "connect";
      if (m_test != null) begin
        $display("UVM_INFO: Running connect_phase...");
        m_test.do_connect_phase(phase);
      end

      // End of elaboration phase
      phase.name = "end_of_elaboration";
      if (m_test != null) begin
        $display("UVM_INFO: Running end_of_elaboration_phase...");
        m_test.do_end_of_elaboration_phase(phase);
      end

      // Start of simulation phase
      phase.name = "start_of_simulation";
      if (m_test != null) begin
        $display("UVM_INFO: Running start_of_simulation_phase...");
        m_test.do_start_of_simulation_phase(phase);
      end

      // Run phase
      phase.name = "run";
      if (m_test != null) begin
        $display("UVM_INFO: Running run_phase...");
        // Start test's run_phase - it will run sequences that feed items to drivers
        // Run phases execute in parent->child order, but since each may block,
        // we need to handle this specially
        m_test.do_run_phase(phase);
        // Wait for all objections to be dropped (in case any phases raise them)
        while (!phase.is_done()) begin
          #1;
        end
        $display("UVM_INFO: All objections dropped, ending run_phase...");
      end

      // Extract phase
      phase.name = "extract";
      if (m_test != null) begin
        $display("UVM_INFO: Running extract_phase...");
        m_test.do_extract_phase(phase);
      end

      // Check phase
      phase.name = "check";
      if (m_test != null) begin
        $display("UVM_INFO: Running check_phase...");
        m_test.do_check_phase(phase);
      end

      // Report phase
      phase.name = "report";
      if (m_test != null) begin
        $display("UVM_INFO: Running report_phase...");
        m_test.do_report_phase(phase);
      end

      // Final phase
      phase.name = "final";
      if (m_test != null) begin
        $display("UVM_INFO: Running final_phase...");
        m_test.do_final_phase(phase);
      end

      $display("UVM_INFO: UVM phases complete.");
      $finish;
    endtask

    function void set_test(uvm_component test);
      m_test = test;
      m_test.m_parent = this;
      add_child(test);
    endfunction

    virtual function void print_topology(string prefix = "");
      $display("UVM Testbench Topology:");
      $display("------------------------");
      for (int i = 0; i < m_num_children; i++) begin
        uvm_component child = m_children[i];
        if (child != null) child.print_topology("  ");
      end
      $display("------------------------");
    endfunction
  endclass

  // ============================================================================
  // Global uvm_top instance
  // ============================================================================
  uvm_root uvm_top = uvm_root::get();

  // ============================================================================
  // UVM Test Done - For setting drain time and end-of-test controls
  // ============================================================================
  class uvm_test_done_objection extends uvm_object;
    time m_drain_time = 0;

    function new(string name = "uvm_test_done");
      super.new(name);
    endfunction

    function void set_drain_time(uvm_component comp, time t);
      m_drain_time = t;
    endfunction

    function time get_drain_time();
      return m_drain_time;
    endfunction

    virtual function string get_type_name();
      return "uvm_test_done_objection";
    endfunction
  endclass

  // Global uvm_test_done instance
  uvm_test_done_objection uvm_test_done = new("uvm_test_done");

  // ============================================================================
  // Factory Registration Classes
  // Note: Simplified to avoid self-referential typedef crash in Icarus
  // ============================================================================

  // Forward declaration for registry types
  class uvm_factory_proxy;
  endclass

  // Factory wrapper for components - simplified version
  class uvm_component_registry #(type T = uvm_component, string Tname = "");
    // get() returns null (factory proxy not fully supported)
    static function uvm_factory_proxy get();
      return null;
    endfunction

    // Static create - note: type_id::create() is not fully supported
    // For now, users should use direct instantiation: obj = new(name, parent);
    static function T create(string name, uvm_component parent);
      $display("UVM_WARNING: type_id::create() not fully supported. Use direct 'new()' instead.");
      return null;
    endfunction
  endclass

  // Factory wrapper for objects - simplified version without complex inheritance
  class uvm_object_registry #(type T = uvm_object, string Tname = "");
    // get() returns null (factory proxy not fully supported)
    static function uvm_factory_proxy get();
      return null;
    endfunction

    // Static create - creates the object directly
    static function T create(string name = "");
      T obj = new(name);
      return obj;
    endfunction
  endclass

  // ============================================================================
  // Stub config_db class - actual functionality is in the parser
  // The parser returns 1 for get() calls on uvm_config_db
  // NOTE: This stub exists for reference but is not actually called -
  // the parser creates stub code for parameterized static method calls
  // ============================================================================
  class uvm_config_db #(type T = int);
    static function void set(uvm_component cntxt, string inst_name, string field_name, T value);
      // No-op - parser handles this
    endfunction

    // Note: Can't use output/ref in static functions in Icarus
    // Parser handles this by returning constant 1 for get() calls
    static function bit get(uvm_component cntxt, string inst_name, string field_name, T value);
      // Parser returns 1 for this call
      return 1;
    endfunction
  endclass

  // ============================================================================
  // UVM Factory (Placeholder)
  // ============================================================================
  // Factory lookup by string name is not fully supported in this simplified UVM.
  // The test must be created via other means (see run_test comments).

  class uvm_factory;
    static uvm_factory m_inst;

    static function uvm_factory get();
      if (m_inst == null)
        m_inst = new();
      return m_inst;
    endfunction
  endclass

  // ============================================================================
  // ============================================================================
  // Covergroup Stub Class
  // ============================================================================
  // This provides a stub implementation for covergroups. When Icarus parses a
  // covergroup declaration, it creates an instance of this class. The sample()
  // and get_coverage() methods are no-ops since functional coverage is not
  // implemented in Icarus Verilog.
  //
  // This allows testbenches with covergroups to compile and run, though no
  // actual coverage data will be collected.
  // ============================================================================
  class __ivl_covergroup;
    // Sample method - called to sample coverage
    // Accepts any number of arguments (in practice, covergroup sample methods
    // are parameterized, but we use a generic signature here)
    virtual function void sample();
      // No-op: coverage sampling not implemented
    endfunction

    // Get coverage percentage - returns 0.0 as coverage is not tracked
    virtual function real get_coverage();
      return 0.0;
    endfunction

    // Get instance coverage - returns 0.0
    virtual function real get_inst_coverage();
      return 0.0;
    endfunction

    // Start - enable coverage collection (no-op)
    virtual function void start();
    endfunction

    // Stop - disable coverage collection (no-op)
    virtual function void stop();
    endfunction

    // Set instance name
    virtual function void set_inst_name(string name);
    endfunction
  endclass

  // ============================================================================
  // TLM Analysis FIFO - Stub implementation for analysis ports
  // ============================================================================
  // Note: This is a stub implementation that accepts writes but discards data.
  // Icarus has issues with arrays of parameterized class types, so we use
  // a simplified version that at least allows compilation.
  // TODO: Implement proper storage once class object arrays work correctly.
  class uvm_tlm_analysis_fifo #(type T = uvm_object) extends uvm_component;

    int m_count;
    // Simple queue to store items (max 64 items in stub)
    T m_items[64];
    int m_head;
    int m_tail;
    // Analysis export for connection
    uvm_analysis_export #(T) analysis_export;

    // Analysis export (implements write)
    function new(string name, uvm_component parent);
      super.new(name, parent);
      m_count = 0;
      m_head = 0;
      m_tail = 0;
      analysis_export = new("analysis_export", this);
    endfunction

    // Write method - receives data from analysis port
    virtual function void write(T t);
      if (m_count < 64) begin
        m_items[m_tail] = t;
        m_tail = (m_tail + 1) % 64;
        m_count++;
      end
    endfunction

    // Get method - blocking task to retrieve next item
    virtual task get(output T t);
      while (m_count == 0) begin
        #1; // Wait for item to be written
      end
      t = m_items[m_head];
      m_head = (m_head + 1) % 64;
      m_count--;
    endtask

    // Try_get - non-blocking get
    virtual function bit try_get(output T t);
      if (m_count > 0) begin
        t = m_items[m_head];
        m_head = (m_head + 1) % 64;
        m_count--;
        return 1;
      end
      return 0;
    endfunction

    // Peek - look at next item without removing
    virtual function bit try_peek(output T t);
      if (m_count > 0) begin
        t = m_items[m_head];
        return 1;
      end
      return 0;
    endfunction

    // Size - number of items in fifo
    virtual function int size();
      return m_count;
    endfunction

    // Is empty check
    virtual function bit is_empty();
      return m_count == 0;
    endfunction

    // Flush - reset fifo
    virtual function void flush();
      m_count = 0;
      m_head = 0;
      m_tail = 0;
    endfunction

    // Used returns count (compatible with real UVM API)
    virtual function int used();
      return m_count;
    endfunction

  endclass

  // ============================================================================
  // semaphore - SystemVerilog built-in synchronization primitive
  // ============================================================================
  // Note: This is a stub implementation. Icarus doesn't have native semaphore
  // support, so we provide a class-based stub that compiles but doesn't block.
  // Real semaphore functionality requires VVP runtime support.
  class semaphore;
    int m_count;

    function new(int keyCount = 0);
      m_count = keyCount;
    endfunction

    // Get keys (blocking) - stub: decrements count
    task get(int keyCount = 1);
      // In real implementation, this would block if m_count < keyCount
      // For stub, just decrement (may go negative)
      m_count -= keyCount;
    endtask

    // Put keys back
    function void put(int keyCount = 1);
      m_count += keyCount;
    endfunction

    // Try to get keys without blocking
    function int try_get(int keyCount = 1);
      if (m_count >= keyCount) begin
        m_count -= keyCount;
        return 1;
      end
      return 0;
    endfunction
  endclass

  // ============================================================================
  // uvm_seq_item_pull_port - TLM port for sequencer-driver communication
  // ============================================================================
  // This port is used by drivers to pull sequence items from the sequencer.
  // The sequencer provides items via get_next_item() and driver signals completion
  // via item_done().
  //
  // Note: This is a stub implementation that provides the interface needed for
  // compilation. Full sequencer functionality requires additional infrastructure.
  class uvm_seq_item_pull_port #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_object;

    // Connected sequencer (set during connect_phase)
    uvm_sequencer_base m_sequencer;

    function new(string name = "uvm_seq_item_pull_port");
      super.new(name);
      m_sequencer = null;
    endfunction

    // Connect to a sequencer
    virtual function void connect(uvm_sequencer_base sequencer);
      m_sequencer = sequencer;
    endfunction

    // Get the next item from the sequencer (blocking)
    // Stub: Returns null - real implementation needs sequencer integration
    virtual task get_next_item(output REQ t);
      if (m_sequencer != null) begin
        // Wait for item from sequencer's queue
        // For now, just set to null - driver must handle this
        t = null;
      end else begin
        $display("UVM_ERROR [SEQ_ITEM_PULL]: No sequencer connected to pull port");
        t = null;
      end
    endtask

    // Try to get next item without blocking
    // Note: Changed from function with output to task per SV rules
    virtual task try_next_item(output REQ t, output bit success);
      t = null;
      success = 0;  // No item available (stub)
    endtask

    // Signal that processing of the current item is complete
    virtual function void item_done(RSP rsp = null);
      // Stub: In real UVM, this signals the sequencer
    endfunction

    // Get a peeked item (doesn't remove from queue)
    virtual task peek(output REQ t);
      t = null;  // Stub
    endtask

    // Get and remove item (non-blocking version)
    virtual task get(output REQ t);
      get_next_item(t);
    endtask

    // Put response back to sequencer
    virtual task put(RSP t);
      // Stub: In real UVM, this returns response to sequence
    endtask

    // Check if port is connected
    virtual function bit is_connected();
      return m_sequencer != null;
    endfunction

  endclass

  // ============================================================================
  // SystemVerilog process class stub (IEEE 1800-2017 Section 9.7)
  // ============================================================================
  // Note: This is a stub implementation. The process class is normally a
  // SystemVerilog built-in, but Icarus doesn't implement it yet.
  typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } process_state;

  class process;
    static process current_process;
    process_state m_state;
    int m_id;
    static int next_id = 0;

    function new();
      m_id = next_id++;
      m_state = RUNNING;
    endfunction

    // Get current process handle
    static function process self();
      if (current_process == null) begin
        current_process = new();
      end
      return current_process;
    endfunction

    // Get process status
    function process_state status();
      return m_state;
    endfunction

    // Terminate the process (stub - actual kill requires runtime support)
    function void kill();
      m_state = KILLED;
    endfunction

    // Wait for process to finish (stub - just returns immediately)
    task await();
      // In real implementation, this would block until process finishes
      // For now, it's a no-op since we can't actually track process state
    endtask

    // Suspend the process (stub)
    function void suspend();
      m_state = SUSPENDED;
    endfunction

    // Resume a suspended process (stub)
    function void resume();
      if (m_state == SUSPENDED)
        m_state = RUNNING;
    endfunction
  endclass

  // ============================================================================
  // UVM RAL Classes - Register Abstraction Layer
  // ============================================================================

  // Stub class for frontdoor access (not fully implemented)
  class uvm_reg_frontdoor extends uvm_object;
    function new(string name = "uvm_reg_frontdoor");
      super.new(name);
    endfunction
  endclass

  // ============================================================================
  // uvm_reg_field - The smallest addressable unit in the RAL hierarchy
  // ============================================================================
  class uvm_reg_field extends uvm_object;
    protected uvm_reg m_parent;
    protected int unsigned m_lsb;
    protected int unsigned m_size;
    protected string m_access;
    protected uvm_reg_data_t m_reset;
    protected uvm_reg_data_t m_value;
    protected uvm_reg_data_t m_mirrored;
    protected bit m_volatile;
    protected bit m_has_reset;
    protected bit m_is_rand;

    function new(string name = "uvm_reg_field");
      super.new(name);
      m_lsb = 0;
      m_size = 0;
      m_access = "RW";
      m_reset = 0;
      m_value = 0;
      m_mirrored = 0;
      m_volatile = 0;
      m_has_reset = 0;
      m_is_rand = 0;
    endfunction

    // Configure the field
    virtual function void configure(uvm_reg parent,
                            int unsigned size,
                            int unsigned lsb_pos,
                            string access,
                            bit volatile_field,
                            uvm_reg_data_t reset,
                            bit has_reset,
                            bit is_rand,
                            bit individually_accessible);
      m_parent = parent;
      m_size = size;
      m_lsb = lsb_pos;
      m_access = access;
      m_reset = reset;
      m_value = reset;
      m_mirrored = reset;
      m_volatile = volatile_field;
      m_has_reset = has_reset;
      m_is_rand = is_rand;
    endfunction

    // Get number of bits
    virtual function int unsigned get_n_bits();
      return m_size;
    endfunction

    // Get LSB position
    virtual function int unsigned get_lsb_pos();
      return m_lsb;
    endfunction

    // Get access mode
    virtual function string get_access(uvm_reg_map map = null);
      return m_access;
    endfunction

    // Get the desired value
    virtual function uvm_reg_data_t get();
      return m_value;
    endfunction

    // Set the desired value
    virtual function void set(uvm_reg_data_t value, string fname = "", int lineno = 0);
      uvm_reg_data_t mask;
      if (m_size >= 64)
        mask = {64{1'b1}};
      else
        mask = (64'b1 << m_size) - 1;
      m_value = value & mask;
    endfunction

    // Get the mirrored value
    virtual function uvm_reg_data_t get_mirrored_value();
      return m_mirrored;
    endfunction

    // Get reset value
    virtual function uvm_reg_data_t get_reset(string kind = "HARD");
      return m_reset;
    endfunction

    // Reset the field
    virtual function void reset(string kind = "HARD");
      m_value = m_reset;
      m_mirrored = m_reset;
    endfunction

    // Predict the field value
    virtual function bit predict(uvm_reg_data_t value,
                                 uvm_reg_data_t be = -1,
                                 uvm_predict_e kind = UVM_PREDICT_DIRECT,
                                 uvm_path_e path = UVM_FRONTDOOR,
                                 uvm_reg_map map = null,
                                 string fname = "",
                                 int lineno = 0);
      uvm_reg_data_t mask;
      if (m_size >= 64)
        mask = {64{1'b1}};
      else
        mask = (64'b1 << m_size) - 1;
      m_mirrored = value & mask;
      return 1;
    endfunction

    // Get parent register
    virtual function uvm_reg get_parent();
      return m_parent;
    endfunction
  endclass

  // ============================================================================
  // uvm_reg - A register is a collection of fields at a specific address
  // ============================================================================
  class uvm_reg extends uvm_object;
    protected uvm_reg_block m_parent;
    protected int unsigned m_n_bits;
    protected bit m_has_cover;
    local uvm_reg_field m_fields[16];  // Fixed array for Icarus (max 16 fields)
    local int m_n_fields;
    protected uvm_reg_data_t m_reset;

    function new(string name = "uvm_reg", int unsigned n_bits = 32, int has_coverage = 0);
      super.new(name);
      m_n_bits = n_bits;
      m_has_cover = has_coverage;
      m_n_fields = 0;
      m_reset = 0;
    endfunction

    // Build - called by derived classes to add fields
    virtual function void build();
      // Override in derived register classes
    endfunction

    // Configure the register
    virtual function void configure(uvm_reg_block blk_parent,
                                    uvm_reg_file regfile_parent = null,
                                    string hdl_path = "");
      m_parent = blk_parent;
    endfunction

    // Add a field to this register
    function void add_field(uvm_reg_field field);
      if (m_n_fields < 16) begin
        m_fields[m_n_fields] = field;
        m_n_fields++;
      end
    endfunction

    // Get number of bits
    virtual function int unsigned get_n_bits();
      return m_n_bits;
    endfunction

    // Get parent block
    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction

    // Get number of fields
    virtual function int get_n_fields();
      return m_n_fields;
    endfunction

    // Get field by index (workaround for Icarus - can't iterate with method calls)
    virtual function uvm_reg_field get_field_by_index(int idx);
      if (idx >= 0 && idx < m_n_fields)
        return m_fields[idx];
      return null;
    endfunction

    // Get the desired value - simplified for Icarus (single field register)
    // For multi-field registers, override this method
    virtual function uvm_reg_data_t get(string fname = "", int lineno = 0);
      // Return stored value for simple registers
      return m_reset;
    endfunction

    // Set the desired value - simplified for Icarus
    virtual function void set(uvm_reg_data_t value, string fname = "", int lineno = 0);
      m_reset = value;
    endfunction

    // Get the mirrored value - simplified for Icarus
    virtual function uvm_reg_data_t get_mirrored_value(string fname = "", int lineno = 0);
      return m_reset;
    endfunction

    // Reset all fields
    virtual function void reset(string kind = "HARD");
      // Simple reset - override for complex behavior
    endfunction

    // Predict the register value
    virtual function bit predict(uvm_reg_data_t value,
                                 uvm_reg_data_t be = -1,
                                 uvm_predict_e kind = UVM_PREDICT_DIRECT,
                                 uvm_path_e path = UVM_FRONTDOOR,
                                 uvm_reg_map map = null,
                                 string fname = "",
                                 int lineno = 0);
      m_reset = value;
      return 1;
    endfunction

    // Read register (frontdoor) - stub implementation
    virtual task read(output uvm_status_e status,
                      output uvm_reg_data_t value,
                      input uvm_path_e path = UVM_DEFAULT_PATH,
                      input uvm_reg_map map = null,
                      input uvm_sequence_base parent = null,
                      input int prior = -1,
                      input uvm_object extension = null,
                      input string fname = "",
                      input int lineno = 0);
      // Stub - returns mirrored value
      status = UVM_IS_OK;
      value = get_mirrored_value();
    endtask

    // Write register (frontdoor) - stub implementation
    virtual task write(output uvm_status_e status,
                       input uvm_reg_data_t value,
                       input uvm_path_e path = UVM_DEFAULT_PATH,
                       input uvm_reg_map map = null,
                       input uvm_sequence_base parent = null,
                       input int prior = -1,
                       input uvm_object extension = null,
                       input string fname = "",
                       input int lineno = 0);
      // Stub - sets desired value
      set(value);
      status = UVM_IS_OK;
    endtask
  endclass

  // Stub for uvm_reg_file (not fully implemented)
  class uvm_reg_file extends uvm_object;
    function new(string name = "uvm_reg_file");
      super.new(name);
    endfunction
  endclass

  // ============================================================================
  // uvm_reg_map - Address maps manage relationship between registers and addresses
  // ============================================================================
  class uvm_reg_map extends uvm_object;
    protected uvm_reg_block m_parent;
    protected uvm_reg_addr_t m_base_addr;
    protected int unsigned m_n_bytes;
    protected uvm_endianness_e m_endian;
    protected uvm_sequencer_base m_sequencer;
    protected uvm_reg_adapter m_adapter;
    protected bit m_byte_addressing;

    // Register storage - fixed arrays for Icarus
    local uvm_reg m_regs[256];
    local uvm_reg_addr_t m_reg_addrs[256];
    local int m_n_regs;

    function new(string name = "uvm_reg_map");
      super.new(name);
      m_n_regs = 0;
      m_base_addr = 0;
      m_n_bytes = 4;
      m_endian = UVM_LITTLE_ENDIAN;
      m_byte_addressing = 1;
    endfunction

    // Configure the map
    virtual function void configure(uvm_reg_block parent,
                                    uvm_reg_addr_t base_addr,
                                    int unsigned n_bytes,
                                    uvm_endianness_e endian,
                                    bit byte_addressing = 1);
      m_parent = parent;
      m_base_addr = base_addr;
      m_n_bytes = n_bytes;
      m_endian = endian;
      m_byte_addressing = byte_addressing;
    endfunction

    // Add a register to the map
    virtual function void add_reg(uvm_reg rg,
                                  uvm_reg_addr_t offset,
                                  string rights = "RW",
                                  bit unmapped = 0,
                                  uvm_reg_frontdoor frontdoor = null);
      if (m_n_regs < 256) begin
        m_regs[m_n_regs] = rg;
        m_reg_addrs[m_n_regs] = offset;
        m_n_regs++;
      end
    endfunction

    // Get base address
    virtual function uvm_reg_addr_t get_base_addr(uvm_hier_e hier = UVM_HIER);
      return m_base_addr;
    endfunction

    // Get number of bytes per access
    virtual function int unsigned get_n_bytes(uvm_hier_e hier = UVM_HIER);
      return m_n_bytes;
    endfunction

    // Get endianness
    virtual function uvm_endianness_e get_endian(uvm_hier_e hier = UVM_HIER);
      return m_endian;
    endfunction

    // Get register by offset
    virtual function uvm_reg get_reg_by_offset(uvm_reg_addr_t offset, bit read = 1);
      for (int i = 0; i < m_n_regs; i++) begin
        if (m_reg_addrs[i] == offset)
          return m_regs[i];
      end
      return null;
    endfunction

    // Set sequencer and adapter
    virtual function void set_sequencer(uvm_sequencer_base sequencer,
                                        uvm_reg_adapter adapter = null);
      m_sequencer = sequencer;
      m_adapter = adapter;
    endfunction

    // Get sequencer
    virtual function uvm_sequencer_base get_sequencer(uvm_hier_e hier = UVM_HIER);
      return m_sequencer;
    endfunction

    // Get adapter
    virtual function uvm_reg_adapter get_adapter(uvm_hier_e hier = UVM_HIER);
      return m_adapter;
    endfunction

    // Get parent block
    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction
  endclass

  // ============================================================================
  // uvm_reg_block - Top-level container for registers and maps
  // ============================================================================
  class uvm_reg_block extends uvm_object;
    protected uvm_reg_block m_parent;
    local uvm_reg_map m_maps[8];        // Fixed array for Icarus (max 8 maps)
    local int m_n_maps;
    local uvm_reg m_regs[256];          // Fixed array (max 256 regs)
    local int m_n_regs;
    local bit m_locked;
    uvm_reg_map default_map;            // Public access for convenience

    function new(string name = "uvm_reg_block", int has_coverage = 0);
      super.new(name);
      m_n_maps = 0;
      m_n_regs = 0;
      m_locked = 0;
      default_map = null;
    endfunction

    // Build - override in derived classes
    virtual function void build();
    endfunction

    // Configure the block
    virtual function void configure(uvm_reg_block parent = null, string hdl_path = "");
      m_parent = parent;
    endfunction

    // Create an address map
    virtual function uvm_reg_map create_map(string name,
                                            uvm_reg_addr_t base_addr,
                                            int unsigned n_bytes,
                                            uvm_endianness_e endian,
                                            bit byte_addressing = 1);
      uvm_reg_map map;
      if (m_n_maps >= 8) return null;
      map = new(name);
      map.configure(this, base_addr, n_bytes, endian, byte_addressing);
      m_maps[m_n_maps] = map;
      m_n_maps++;
      if (default_map == null)
        default_map = map;
      return map;
    endfunction

    // Get map by name - simplified for Icarus (returns default map)
    // Icarus doesn't support method calls on array elements
    virtual function uvm_reg_map get_map_by_name(string name);
      // For Icarus, just return default_map since method calls on array elements fail
      return default_map;
    endfunction

    // Get map by index (workaround for Icarus)
    virtual function uvm_reg_map get_map_by_index(int idx);
      if (idx >= 0 && idx < m_n_maps)
        return m_maps[idx];
      return null;
    endfunction

    // Get number of maps
    virtual function int get_n_maps();
      return m_n_maps;
    endfunction

    // Get default map
    virtual function uvm_reg_map get_default_map();
      return default_map;
    endfunction

    // Set default map
    virtual function void set_default_map(uvm_reg_map map);
      default_map = map;
    endfunction

    // Add a register to the block
    function void add_reg(uvm_reg rg);
      if (m_n_regs < 256) begin
        m_regs[m_n_regs] = rg;
        m_n_regs++;
      end
    endfunction

    // Get number of registers
    virtual function int get_n_registers();
      return m_n_regs;
    endfunction

    // Get register by index (workaround for Icarus - no ref params in functions)
    virtual function uvm_reg get_register_by_index(int idx);
      if (idx >= 0 && idx < m_n_regs)
        return m_regs[idx];
      return null;
    endfunction

    // Lock the model
    virtual function void lock_model();
      m_locked = 1;
    endfunction

    // Check if locked
    virtual function bit is_locked();
      return m_locked;
    endfunction

    // Reset all registers - simplified for Icarus
    // Icarus doesn't support method calls on array elements
    virtual function void reset(string kind = "HARD");
      // Override in derived classes to reset specific registers
    endfunction

    // Get parent block
    virtual function uvm_reg_block get_parent();
      return m_parent;
    endfunction
  endclass

  // ============================================================================
  // uvm_reg_adapter - Converts between register ops and bus transactions
  // ============================================================================
  class uvm_reg_adapter extends uvm_object;
    // Configuration flags
    bit supports_byte_enable;
    bit provides_responses;

    function new(string name = "uvm_reg_adapter");
      super.new(name);
      supports_byte_enable = 0;
      provides_responses = 0;
    endfunction

    // Convert register operation to bus transaction
    // Must be overridden by protocol-specific adapter
    // Note: Uses input instead of ref for Icarus compatibility
    virtual function uvm_sequence_item reg2bus(input uvm_reg_bus_op rw);
      return null;
    endfunction

    // Convert bus response back to register operation
    // Must be overridden by protocol-specific adapter
    // Returns the modified bus_op via output parameter
    virtual task bus2reg(input uvm_sequence_item bus_item,
                         output uvm_access_e kind,
                         output uvm_reg_addr_t addr,
                         output uvm_reg_data_t data,
                         output uvm_status_e status);
      kind = UVM_READ;
      addr = 0;
      data = 0;
      status = UVM_IS_OK;
    endtask

    // Helper to get parent sequence
    virtual function uvm_sequence_base get_item();
      return null;
    endfunction
  endclass

  // ============================================================================
  // uvm_reg_predictor - Updates register model based on observed transactions
  // ============================================================================
  class uvm_reg_predictor extends uvm_component;
    uvm_reg_adapter adapter;
    uvm_reg_map map;

    function new(string name = "uvm_reg_predictor", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Process an observed transaction (task version for Icarus compatibility)
    virtual task write(uvm_sequence_item tr);
      uvm_access_e kind;
      uvm_reg_addr_t addr;
      uvm_reg_data_t data;
      uvm_status_e status;
      uvm_reg rg;

      if (adapter == null || map == null) return;

      // Convert bus transaction to register operation
      adapter.bus2reg(tr, kind, addr, data, status);

      // Find the register at this address
      rg = map.get_reg_by_offset(addr);
      if (rg == null) return;

      // Update the register model
      if (kind == UVM_READ)
        void'(rg.predict(data, .kind(UVM_PREDICT_READ)));
      else
        void'(rg.predict(data, .kind(UVM_PREDICT_WRITE)));
    endtask
  endclass

  // ============================================================================
  // uvm_reg_sequence - Base class for register sequences
  // ============================================================================
  class uvm_reg_sequence extends uvm_sequence_base;
    uvm_reg_block model;
    uvm_reg_map reg_map;

    function new(string name = "uvm_reg_sequence");
      super.new(name);
    endfunction

    // Convenience method for writing a register
    virtual task write_reg(uvm_reg rg, output uvm_status_e status, input uvm_reg_data_t value,
                           input uvm_path_e path = UVM_FRONTDOOR);
      rg.write(status, value, path, reg_map, this);
    endtask

    // Convenience method for reading a register
    virtual task read_reg(uvm_reg rg, output uvm_status_e status, output uvm_reg_data_t value,
                          input uvm_path_e path = UVM_FRONTDOOR);
      rg.read(status, value, path, reg_map, this);
    endtask
  endclass

  // Global run_test task
  // ============================================================================
  // This task creates a test instance using the UVM factory and runs the phases.
  // The factory uses $ivl_factory_create to look up and instantiate classes by name.
  //
  // Usage:
  //   run_test("my_test_class");  // Creates and runs test named "my_test_class"
  //   run_test();                  // Runs with pre-registered test (via set_test)
  task run_test(string test_name = "");
    uvm_root root;
    uvm_object test_obj;

    root = uvm_root::get();

    $display("UVM_INFO: run_test called with test_name='%s'", test_name);

    // If a test name is provided and no test is registered, try factory creation
    if (test_name != "" && root.m_test == null) begin
      $display("UVM_INFO: Looking up test '%s' in factory...", test_name);

      // Use $ivl_factory_create to create test instance by name
      test_obj = $ivl_factory_create(test_name);

      if (test_obj == null) begin
        $display("UVM_FATAL: Factory could not create test '%s'", test_name);
        $display("UVM_INFO: Make sure the class is defined and uses `uvm_component_utils");
        $finish;
      end else begin
        $display("UVM_INFO: Factory created test '%s' successfully", test_name);
        // Cast to uvm_component and set as test
        if (!$cast(root.m_test, test_obj)) begin
          $display("UVM_FATAL: Test '%s' is not a uvm_component", test_name);
          $finish;
        end
        // Set the test's name, full_name and parent
        root.m_test.set_name("uvm_test_top");
        root.m_test.m_full_name = "uvm_test_top";
        root.m_test.m_parent = root;
      end
    end

    if (root.m_test == null) begin
      $display("UVM_WARNING: No test registered.");
      $display("UVM_INFO: Running phases without test-specific behavior.");
    end

    root.run_test(test_name);
  endtask

endpackage
