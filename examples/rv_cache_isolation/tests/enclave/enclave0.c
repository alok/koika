#include "mmio0.h"

static const char* pattern = "-.- --- .. -.- .-";

#define DOT 20
#define DASH (3 * DOT)
#define SPACE DOT
#define LETTER_SPACE (3 * DOT)
#define WORD_SPACE (7 * DOT)

static void wait(int duration) {
  for (int i = 0; i < duration; i++);
}

static void blink(char c) {
  int on, duration;

  switch (c) {
  case '.':
    on = 1, duration = DOT;
    break;
  case '-':
    on = 1, duration = DASH;
    break;
  default:
    on = 0, duration = LETTER_SPACE;
    break;
  }

  putled0(on);
  wait(duration);
  putled0(0);
  wait(SPACE);
}

#define REPEAT 1

/*
int main0() {
  for (int i = 0; i < REPEAT; i++) {
    wait(WORD_SPACE);
    const char* p = pattern;
    while (*p)
      blink(*p++);
  }
  putchar0('\n');
}
*/
extern int _add_password(unsigned int id, char value, int secret);
extern char _lookup(unsigned int id, int secret);


int main0 () {
  int secret_code = 42;

  putchar0('A');
  blink('.');
  blink('-');
  _add_password(1, 'A', secret_code);
  char ch = _lookup(1, secret_code);
  putchar0(ch);
  blink('.');

  _add_password(2, 'B', secret_code);
  ch = _lookup(1, 0);
  putchar0(ch);
  ch = _lookup(2, secret_code);
  putchar0(ch);

  blink('.');
  putchar0('\n');
}
