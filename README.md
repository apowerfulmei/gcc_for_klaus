"# gcc_for_klaus" 



### GCC

1、解压gcc-bin.zip到KLAUS/Docker-env/data目录下

2、在docker中将该gcc的内容复制到/gcc-bin下，将其替换



### Patch_analyzer

patch_analyzer目录下是编译好的analyzer可执行文件以及修改过的python文件，将这两个文件保存到Docker-env/data目录下

```
cd data
cp analyzer /patch_analyzer/build/lib/
cp analyze_patch.py /patch_analyzer/
```

新的analyzer会生成distance信息到容器目录/distance下





### Kcov.c补丁与build_env.py

放到Docker-env/data/fuzz_cfgs_dir目录下即可
