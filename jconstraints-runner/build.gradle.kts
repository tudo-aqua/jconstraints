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

import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar
plugins {
    id("application")
    id("tools.aqua.jconstraints.java-fatjar-convention")
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "JConstraints runner and metric analyzer"

repositories {
    mavenCentral()
    mavenLocal()
}

tasks {
    withType<ShadowJar> {
        manifest {
            attributes["Main-Class"] = "runner.JConstraintsRunner"
        }
    }
}

dependencies {
    implementation("commons-cli:commons-cli:1.4")
    implementation(project(":jconstraints-core"))
    implementation(project(":jconstraints-z3"))
    implementation(project(":jconstraints-cvc4"))
    implementation(project(":jconstraints-metasolver"))

    testCompile("junit:junit:4.12")
}

application {
    mainClassName = ("runner.JConstraintsRunner")
}

