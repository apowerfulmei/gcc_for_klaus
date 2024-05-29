Here's the revised content of `README.md` in English, presented in a clear and concise format:

---

# CodeQL Extractor Filter

## Installation
Ensure the `extractor_filter` script is executable and link it to the appropriate CodeQL tools directory:
```bash
chmod +x extractor_filter
ln -s $(pwd)/extractor_filter $(dirname $(which codeql))/cpp/tools/linux64
```

## Usage
When creating a CodeQL database, add the `FILTER_FILE` environment variable. This should list the source file paths you want to retain (not filter out), one per line, supporting both relative and absolute paths, as shown below:
```
src/main.c
src/calculate.c
```
Then, append the following to your compilation command:
```bash
--extra-tracing-config=custom-tracing-config.lua
```

## Testing
After installation, execute the following command to generate codeql database in the `codeql_database` directory:
```bash
cd test
./run.sh
```