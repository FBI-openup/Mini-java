
all:
	mkdir -p bin
	javac -cp lib/java-cup-11a-runtime.jar -d bin src/mini_java/*.java
	java -cp lib/java-cup-11a-runtime.jar:bin mini_java.Main --debug test.java

