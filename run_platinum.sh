#!/usr/bin/env bash
ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    *)              ARGS+=("$1");         shift; ;;
  esac
done
set -- "${ARGS[@]}"

if [ $# -lt 0 ]; then 
  echo "  error: invalid arguments"
  exit 1
fi;

# on the server, we need to switch to Java 13
sudo update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java

# build the jars, just in case
./gradlew assemble --quiet --console plain
if [ $? -gt 0 ]; then
  echo "  error: could not build .jar files"
  exit 3
fi

# make the timestamped log directory
export now="$(date +'%Y%m%dT%H%M%S')"
mkdir -p log/${now}
ln -snf $(pwd)/log/${now} log/latest

# set the java args
CLASSPATH="org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar"
JAVA_ARGS="-Xmx20g"
MAINCLASS="edu.mit.csail.sdg.alloy4whole.PlatinumTest"

java ${JAVA_ARGS} -cp ${CLASSPATH}  ${MAINCLASS} $@ \
  >>log/${now}/platinum.out 2>>log/${now}/platinum.err

