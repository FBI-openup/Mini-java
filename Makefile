.PHONY: all  t

all:
	rm -rf bin
	mkdir -p bin
	javac -cp lib/java-cup-11a-runtime.jar -d bin mini_java/*.java

t: all
	./test -all "java -cp lib/java-cup-11a-runtime.jar:bin mini_java.Main"
	