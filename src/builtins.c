#include <stdio.h>
#include <termios.h>
#include <string.h>
#include <sys/ioctl.h>

void *getstdout() {
  return (void*) stdout;
}

void setbuffering() {
  setvbuf(stdin,  NULL, _IONBF, 0);
  setvbuf(stdout, NULL, _IOLBF, 10000);
}

char getachar() {
  struct termios savedterm;
  struct termios term;

  tcgetattr(fileno(stdin), &savedterm);
  tcgetattr(fileno(stdin), &term);
  term.c_lflag &= ~ICANON;
  term.c_cc[VMIN]  = 1;
  term.c_cc[VTIME] = 0;
  tcsetattr(fileno(stdin), TCSANOW, &term);

  char c = getchar();

  tcsetattr(fileno(stdin), TCSANOW, &savedterm);
  return c;
}

struct termios savedterm;

// TODO: fail on error
void setterm() {
  struct termios term;

  tcgetattr(fileno(stdin), &savedterm);
  tcgetattr(fileno(stdin), &term);
  term.c_lflag &= ~ECHO;
  term.c_lflag &= ~ICANON;
  term.c_cc[VMIN]  = 1;
  term.c_cc[VTIME] = 0;
  tcsetattr(fileno(stdin), TCSANOW, &term);

  // hide cursor, turn on bracketed paste mode, enable alternative screen buffer, turn line wrap off
  const char str[] = "\e[?25l\e[?2004h\e[?1049h\e[?7l";
  size_t len = strlen(str);
  fwrite (str, 1, len, stdout);
  fflush(stdout);
}

void resetterm() {
  tcsetattr(fileno(stdin), TCSANOW, &savedterm);
  const char str[] = "\e[?7h\e[?1049l\e[?2004l\e[?25h";
  size_t len = strlen(str);
  fwrite (str, 1, len, stdout);
  fflush(stdout);
}

unsigned long long int termsize() {
  struct winsize w;
  int ok = ioctl(fileno(stdout), TIOCGWINSZ, &w);
  if (ok == 0) {
    return ((((unsigned long long int)(w.ws_col)) << 32) | (unsigned long long int)(w.ws_row));
  } else {
    return 0;
  }
}
