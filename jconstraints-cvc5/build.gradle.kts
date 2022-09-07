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

plugins {
    id("tools.aqua.jconstraints.java-fatjar-convention")
}


group = "tools.aqua"
version = "0.9.6-BV-SNAPSHOT"
description = "jConstraints-cvc5 is the cvc5 API plug-in for jConstraints"


repositories{
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("tudo:cvc5:SNAPSHOT")
    implementation("org.apache.commons:commons-math3:3.6.1")
    implementation(project(":jconstraints-core"))
    testImplementation(project(":jconstraints-benchmarktest"))
}
