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

package gov.nasa.jpf.constraints.smtlibUtility.smtconverter;

public class SMTLibExportVisitorConfig {
  public boolean isZ3Mode;
  public boolean namedAssert;
  public boolean replaceZ3Escape;
  public int stmtCounter = 0;

  public SMTLibExportVisitorConfig() {
    // This is the default config
    this(true, false, false);
  }

  public SMTLibExportVisitorConfig(boolean isZ3Mode, boolean namedAssert, boolean replaceZ3Escape) {
    this.isZ3Mode = isZ3Mode;
    this.namedAssert = namedAssert;
    this.replaceZ3Escape = replaceZ3Escape;
  }
}
