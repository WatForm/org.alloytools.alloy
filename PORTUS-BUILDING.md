# Building Portus

1. Fortress is included in org.alloytools.fortress.core/fortress as a git submodule. Run `git pull --recurse-submodules` to pull it. Check by going to org.alloytools.fortress.core/fortress and checking that it looks like the Fortress repo.
2. Portus is currently compiled with *Java 12*. Install OpenJDK 12.0.2 from https://jdk.java.net/archive. I recommend using JEnv (https://jenv.be) to manage multiple Java versions. Once you've set it up, do `java -version` to make sure you're on Java 12.0.2. (Note: JARs compiled with a later Java version might require that later version to run.)
    * Note: Java 17 also works as of 2024-02-07. The Java version must be compatible with the Gradle version, which is currently 7.2 (check .gradle-wrapper/gradle-wrapper.properties).
3. Fortress is compiled with SBT. Install it from https://www.scala-sbt.org or your preferred package manager.
4. Run `./gradlew build` to build a fat JAR. The output is at org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar. Gradle will also compile Fortress and place the compilation output and several auxiliary libraries in org.alloytools.fortress.core/libs: to run Portus you don't need these (everything is in the fat JAR), but to set up IntelliJ or another IDE, you'll need to add these libraries to the classpath so the IDE can find the Fortress and Scala symbols.
5. Run Portus from the home directory with `java -cp org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar ca.waterloo.watform.portus.cli.PortusCLI`. I recommend making an alias for this.
