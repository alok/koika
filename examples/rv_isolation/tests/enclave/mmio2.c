static int* const UART_ADDR = (int*)0x40000000;
static int* const LED_ADDR  = (int*)0x40000004;
static int* const STOP_ADDR = (int*)0x40001000;

int getchar2() {
  return 0;
}

void __attribute__((noreturn)) exit2(int code) {
  *STOP_ADDR = code;
  __builtin_unreachable();
}

int putchar2(int c) {
  *UART_ADDR = c;
  return c;
}

int getled2() {
  return *LED_ADDR;
}

int putled2(int on) {
  *LED_ADDR = on;
  return on;
}

static inline __attribute__((unused)) void putchars2(const char* str) {
  while (*str) {
    putchar2(*str);
    str++;
  }
}
