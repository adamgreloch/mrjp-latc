#/bin/bash

testdir="$1"
binary="$2"

passed=0
total=0

GREEN='\033[0;32m'
RED='\033[0;31m'
BOLD="\e[1m"
RESET='\033[0m'

OUTPUT_REGEX='//output="\K.*?(?=")' 
#
# TMP_DIR=$(mktemp -d)

check() {
  exp_code="$1"
  test_pack="$2"
  for test_prog in "${testdir}/${test_pack}"/*.lat;
  do
    program_output=$(echo 42 | ./$binary -s $test_prog 2>&1)
    ret_code=$?
    echo -ne "--- ${BOLD}$test_prog "
    if [ ${ret_code} -eq ${exp_code} ]
    then
      echo -e "${GREEN}OK${RESET} ---"
      echo -e "$program_output"
      ((passed++))
    else
      echo -e "${RED}FAILED${RESET} ---"
      if [ ${exp_code} -eq 0 ]
      then
        echo -e "$program_output"
      fi
    fi
    ((total++))
  done
}

check 1 "bad"
check 0 "good"

echo -e "${BOLD}=== Passed $passed/$total tests${RESET} ==="

# # cleanup
# rm -r $TMP_DIR 
