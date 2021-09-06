/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
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

import org.w3c.dom.Node

plugins {
    id("tools.aqua.jconstraints.java-fatjar-convention")
    antlr
    `maven-publish`
    `signing`
    id("com.github.johnrengelman.shadow")
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints is a library for managing SMT constraints in Java"

dependencies {
    antlr("org.antlr:antlr:3.5.2")
    api("com.google.guava:guava:30.1-jre")
    implementation("com.github.tudo-aqua:jSMTLIB:5c11ee5")
    implementation("commons-cli:commons-cli:1.4")
    api("dk.brics:automaton:1.12-1")
    implementation("org.antlr:antlr-runtime:3.5.2")
    api("org.apache.commons:commons-math3:3.6.1")
}

tasks {
    shadowJar {
        archiveClassifier.set("with-smtlib")
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
}

publishing {
    publications {
        named<MavenPublication>("mavenJava") {
            artifacts.clear()
            artifact(tasks.shadowJar) { classifier = null }
            pom {
                withXml {
                    val elem = asElement()
                    val dependencies = elem.getElementsByTagName("artifactId")
                    repeat(dependencies.length) {
                        val dep: Node? = dependencies.item(it)
                        if (dep != null && dep.textContent == "jSMTLIB") {
                            dep.parentNode.parentNode.removeChild(dep.parentNode)
                        }
                    }
                }
            }
        }
    }
    repositories {
        maven {
            name = "nexusOSS"
            val releasesUrl = uri("https://oss.sonatype.org/service/local/staging/deploy/maven2/")
            val snapshotsUrl = uri("https://oss.sonatype.org/content/repositories/snapshots/")
            url = if (version.toString().endsWith("SNAPSHOT")) snapshotsUrl else releasesUrl
            credentials {
                username = properties["nexusUsername"] as? String
                password = properties["nexusPassword"] as? String
            }
        }
    }
}

signing {
    isRequired = !hasProperty("skip-signing")
    useGpgCmd()
    sign(publishing.publications["mavenJava"])
}
