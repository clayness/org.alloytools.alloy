#!/bin/bash

print_usage () {
  cat <<USAGE
  usage: run_chenxi.sh [options] <als1> <als2> [alsN...] 
    arguments:
      als1      Path to original Alloy model
      als2      Path to modified Alloy model
      alsN      Paths to subsequent Alloy models, to be analyzed pair-wise
    options:
      None
USAGE
}

# read the positional and optional arguments
ARGS=()
while [ $# -gt 0 ] ; do
  case "$1" in
    --help)   print_usage;  exit 0;       ;;
    --nohup)  NOHUP="true"; shift;        ;;
    --logdir) LOGDIR="$2";  shift; shift; ;;
    *)        ARGS+=("$1"); shift;        ;;
  esac
done
set -- "${ARGS[@]}"

# build the jars, just in case
./gradlew assemble --quiet --console plain
if [ $? -gt 0 ]; then
  echo "  error: could not build .jar files"
  exit 3
fi

# make sure we get two files to compare
if [ $# -lt 2 ] ; then
  echo "  error: invalid arguments, requires at least two model files"
  print_usage
  exit 1
fi

# set up a timestamped directory for the logs
# and recursively call the script in a disowned
# background process (so it can run headless)
if [ -z "${NOHUP}" ] ; then
  export now="$(date +'%Y%m%dT%H%M%S')"
  mkdir -p log/${now}
  ln -snf $(pwd)/log/${now} log/latest

  $0 $@ --logdir $(pwd)/log/${now} --nohup < /dev/null >$(pwd)/log/${now}/chenxi.out 2>$(pwd)/log/${now}/chenxi.err & disown
  echo "running experiments on a disowned process, writing to $(pwd)/log/${now}. PID=$!"
  exit 0
fi

# the actual script begins here
CLASSPATH=$(pwd)/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar
java -cp ${CLASSPATH} edu.mit.csail.sdg.alloy4whole.ExampleChenxi $@
