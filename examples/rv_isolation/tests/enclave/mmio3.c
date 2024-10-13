static int* const UART_ADDR = (int*)0x40000000;
static int* const LED_ADDR  = (int*)0x40000004;
static int* const STOP_ADDR = (int*)0x40001000;

int getchar3() {
  return 0;
}

void __attribute__((noreturn)) exit3(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar3(int c) {
  *UART_ADDR = c;
  return c;
}

int getled3() {
  return *LED_ADDR;
}

int putled3(int on) {
  *LED_ADDR = on;
  return on;
}

static inline __attribute__((unused)) void putchars3(const char* str) {
  while (*str) {
    putchar3(*str);
    str++;
  }
}
