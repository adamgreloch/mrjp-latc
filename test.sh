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
    INPUT="${test_prog%lat}input"
    OUTPUT="${test_prog%lat}output"

    program_output=$(echo 42 | ./$binary $test_prog 2>&1)
    ret_code=$?

    echo -ne "--- ${BOLD}$test_prog "
    if [ ${ret_code} -eq ${exp_code} ]
    then
      if [ -f ${OUTPUT} ]
      then
        if [ -f ${INPUT} ]
        then
          lli "${test_prog%lat}bc" < ${INPUT} | diff ${OUTPUT} -
        else
          lli "${test_prog%lat}bc" | diff ${OUTPUT} -
        fi

        diff_code=$?

        if [ ${diff_code} -eq 0 ]
        then
          echo -e "${GREEN}EXEC OK${RESET} ---"
          ((passed++))
        else
          echo -e "${RED}OUTPUT FAILED${RESET} ---"
        fi
      else
        echo -e "${GREEN}TC OK${RESET} ---"
        ((passed++))
      fi

      echo -e "$program_output"
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
