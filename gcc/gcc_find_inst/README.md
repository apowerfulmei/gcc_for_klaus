## This is a custimized gcc to support syzPatch project
## setup
```
pushd gcc-9.3.0
./contrib/download_prerequisites
popd

mkdir gcc-bin
export INSTALLDIR=`pwd`/gcc-bin
mkdir gcc-build
pushd gcc-build
../gcc-9.3.0/configure --prefix=$INSTALLDIR --enable-languages=c,c++
make -j`nproc`
make install
popd
```
