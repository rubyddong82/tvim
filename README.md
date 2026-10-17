# tvim

A small terminal text editor written in C (no dependencies), inspired by nano/nvim but
using VS Code style keys: shift+arrows to select, Ctrl+A to select all, Ctrl+C/X/V, Ctrl+Z, etc.

## Install

```bash
./install.sh && source ~/.bashrc
tvim notes.txt
```

`install.sh` builds `bin/tvim` and adds `<repo>/bin` to `PATH` in `~/.bashrc` (idempotent).

## Keys

| Action | Keys |
|---|---|
| Autosave | Named files are saved about 1 s after every change (there is no Ctrl+S) |
| Save as | Ctrl+O (or F2) |
| Exit | Esc, then Esc again (any other key returns to the editor). Saves on exit; asks for a file name if the buffer has none, and warns that nothing is saved if you decline |
| Select | Shift+Arrows, Ctrl+Shift+Left/Right (by word), Ctrl+Shift+Up/Down (by paragraph), Shift+Home/End, Ctrl+A, mouse drag, Shift+click |
| Move | Arrows, Ctrl+Left/Right (word), Home (smart), End, Ctrl+Home/End, PgUp/PgDn |
| Copy / Cut / Paste | Ctrl+C / Ctrl+X / Ctrl+V (no selection = whole line); terminal paste works too |
| Undo / Redo | Ctrl+Z / Ctrl+Y |
| Delete word | Ctrl+Backspace, Ctrl+Delete |
| Delete line | Ctrl+K |
| Duplicate line/selection | Ctrl+D |
| Indent / unindent | Tab / Shift+Tab |
| Find | Ctrl+F (Enter/Down next, Up previous, Esc done), F3 / Shift+F3 |
| Replace all | Ctrl+R |
| Help | F1 |

Copy also writes to the system clipboard through OSC 52 (Windows Terminal, kitty, iTerm2, ...).
Search is case-insensitive unless the query has an uppercase letter. CRLF files and a missing
final newline are preserved on save.


