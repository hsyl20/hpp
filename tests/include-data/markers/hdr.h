/* A block comment that spans
   more than one line, so the
   preparation pass replaces it
   with a line marker of its own. */
#define MARKER_A 1
#if MARKER_A
#define MARKER_B 2
#endif
