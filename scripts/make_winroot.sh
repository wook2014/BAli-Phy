#!/bin/bash

SYSROOT=$HOME/win_root

# 1. Make sysroot
echo
echo "1. Writing sysroot dir ${SYSROOT}"
mkdir -p "${SYSROOT}"
mkdir -p "${SYSROOT}/bin"

# 2. Generate cross file
CROSSNAME=win64-cross.txt
echo
echo "2. Writing cross file to '${CROSSNAME}'"
cat > "${CROSSNAME}" <<EOF
[binaries]
c = '/usr/bin/x86_64-w64-mingw32-gcc'
cpp = '/usr/bin/x86_64-w64-mingw32-g++'
ar = '/usr/bin/x86_64-w64-mingw32-ar'
strip = '/usr/bin/x86_64-w64-mingw32-strip'
pkgconfig = '${SYSROOT}/bin/pkg-config'
exe_wrapper = 'wine64' # A command used to run generated executables.

# We need these compiler args to find BOOST, which doesn't use pkg-config
[properties]
c_args = ['-I${SYSROOT}/mingw64/include']
c_link_args = ['-L${SYSROOT}/mingw64/lib']

cpp_args = ['-I${SYSROOT}/mingw64/include']
cpp_link_args = ['-L${SYSROOT}/mingw64/lib']

sys_root = '${SYSROOT}'
pkg_config_libdir = '${SYSROOT}/mingw64/lib/pkgconfig' 

[host_machine]
system = 'windows'
cpu_family = 'x86_64'
cpu = 'x86_64'
endian = 'little'
EOF

# 3. Download boost
echo
echo "3. Installing boost to ${SYSROOT}"
echo
cd ${SYSROOT}
PKGS="boost-1.70.0-2"
for PKG in ${PKGS} ; do
    FILE=mingw-w64-x86_64-${PKG}-any.pkg.tar.xz
    rm -f ${FILE}
    wget --no-verbose --show-progress http://repo.msys2.org/mingw/x86_64/${FILE}
    tar -Jxf ${FILE}
    rm ${FILE}
done

echo
echo "Done."
echo
