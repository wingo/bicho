AC_INIT(bicho, 0.1.0)
AC_COPYRIGHT([

Bicho
Copyright (C) 1993-2015 Free Software Foundation

Bicho is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your
option) any later version.

Bicho is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

])

AC_CONFIG_SRCDIR(src/bicho/cps.scm)
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE([-Wall -Wno-portability serial-tests foreign])
AM_SILENT_RULES([yes])

GUILE_PKG([2.2 2.0])
GUILE_PROGS

AC_CONFIG_FILES([Makefile src/Makefile])
AC_CONFIG_FILES([env], [chmod +x env])
AC_OUTPUT
