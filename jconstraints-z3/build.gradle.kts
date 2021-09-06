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

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints-Z3 is the Z3 API plug-in for jConstraints"

plugins {
    `maven-publish`
    `signing`
    id("tools.aqua.jconstraints.java-fatjar-convention")
}

license {
    exclude("**/SMT-Problem_origin")
}

dependencies {
    implementation("com.google.guava:guava:30.1-jre")
    implementation("io.github.tudo-aqua:z3-turnkey:4.8.10")
    implementation(project(":jconstraints-core"))
    testImplementation(project(":jconstraints-benchmarktest"))
}

publishing{
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
    sign(publishing.publications["mavenJavaFat"])
}
