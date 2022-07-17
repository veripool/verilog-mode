module typedef_enum_indent;

logic variable1;
logic signed [1:0] variable2;
logic variable3;
logic signed [1:0] variable4;

typedef enum logic [1:0] {STATE_0,
STATE_1,
STATE_2,
STATE_3} enum_t;

typedef enum logic [1:0] {STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum logic [1:0] {
STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum logic [1:0] {
STATE_0,
STATE_1,
STATE_2,
STATE_3} enum_t;

typedef enum logic [1:0]
{STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum logic [1:0]
{
STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum logic [1:0]
{
STATE_0,
STATE_1,
STATE_2,
STATE_3
}
enum_t;

typedef enum {STATE_0,
STATE_1,
STATE_2,
STATE_3} enum_t;

typedef enum {STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum {
STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum {
STATE_0,
STATE_1,
STATE_2,
STATE_3} enum_t;

typedef enum
{STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum
{
STATE_0,
STATE_1,
STATE_2,
STATE_3
} enum_t;

typedef enum
{
STATE_0,
STATE_1,
STATE_2,
STATE_3
}
enum_t;


endmodule


// Local Variables:
// verilog-indent-lists: nil
// End:

