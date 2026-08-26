/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2022 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import groovy.util.Node

plugins {
    id("tools.aqua.jconstraints.java-fatjar-convention")
    antlr
    id("com.gradleup.shadow")
}

group = "tools.aqua"
version = "0.9.8-FUN-PARS"
description = "jConstraints is a library for managing SMT constraints in Java"


val antlrVersion = "3.5.2"
val bricsVersion = "1.12-1"
val commonsCliVersion="1.4"
val commonsMathVersion = "3.6.1"
val guavaVersion = "30.1-jre"

dependencies {
    antlr("org.antlr:antlr:$antlrVersion")
    api("com.google.guava:guava:$guavaVersion")
    implementation("com.github.tudo-aqua:jSMTLIB:5c11ee5")
    shadow("commons-cli:commons-cli:$commonsCliVersion")
    api("dk.brics:automaton:$bricsVersion")
    shadow("org.antlr:antlr-runtime:$antlrVersion")
    api("org.apache.commons:commons-math3:$commonsMathVersion")
}

tasks {
    shadowJar {
        //archiveClassifier.set("with-smtlib")
        archiveClassifier.set("")
        dependencies {
            include(dependency("com.github.tudo-aqua:jSMTLIB:5c11ee5"))
        }
    }

    assemble {
        dependsOn(shadowJar)
    }

    test {
        useJUnitPlatform {
            includeTags("base")
        }
    }
    jar{
        archiveClassifier="ignored"
    }
}




publishing {
    publications {
        create<MavenPublication>("shadowedJSMTLIB") {
            artifact(tasks.shadowJar) { classifier = null }
            pom {
                name.set(provider { project.description?.split(' ')?.first() })
                description.set(provider { project.description })
                
                url.set("https://github.com/tudo-aqua/jconstraints")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("jconstraints-authors")
                        name.set("The jConstraints Authors")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints.git")
                    url.set("https://github.com/tudo-aqua/jconstraints")
                }
                withXml {
                    val xml:Node = asNode()
                    println("xml")
                    println(xml.get("dependencies"))
                    val dependenciesNode = xml.appendNode("dependencies")
                    
                    val guavaNode = dependenciesNode.appendNode("dependency")
                    guavaNode.appendNode("groupId", "com.google.guava")
                    guavaNode.appendNode("artifactId", "guava")
                    guavaNode.appendNode("version", guavaVersion)
                    guavaNode.appendNode("scope", "runtime")

                    val bricsNode = (dependenciesNode as groovy.util.Node).appendNode("dependency")
                    bricsNode.appendNode("groupId", "dk.brics")
                    bricsNode.appendNode("artifactId", "automaton")
                    bricsNode.appendNode("version", bricsVersion)
                    bricsNode.appendNode("scope", "runtime")

                    val commonsCLINode = (dependenciesNode as groovy.util.Node).appendNode("dependency")
                    commonsCLINode.appendNode("groupId", "commons-cli")
                    commonsCLINode.appendNode("artifactId", "commons-cli")
                    commonsCLINode.appendNode("version", commonsCliVersion)
                    commonsCLINode.appendNode("scope", "runtime")

                    val commonsMathNode = (dependenciesNode as groovy.util.Node).appendNode("dependency")
                    commonsMathNode.appendNode("groupId", "org.apache.commons")
                    commonsMathNode.appendNode("artifactId", "commons-math3")
                    commonsMathNode.appendNode("version", commonsMathVersion)
                    commonsMathNode.appendNode("scope", "runtime")

                    val antlrRuntimeNode = (dependenciesNode as groovy.util.Node).appendNode("dependency")
                    antlrRuntimeNode.appendNode("groupId", "org.antlr")
                    antlrRuntimeNode.appendNode("artifactId", "antlr-runtime")
                    antlrRuntimeNode.appendNode("version", antlrVersion)
                    antlrRuntimeNode.appendNode("scope", "runtime")
                }
            }
        }
    }
}


// tasks.named("publishAwesomePublicationPublicationToMavenLocal"){
//     dependsOn(tasks.named("publishMavenJavaPublicationToMavenLocal"))
// }

