/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2023 The jConstraints Authors
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

package gov.nasa.jpf.constraints.smtlibUtility.parser.utility;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ConversionUtil {
  private static final Pattern Z3_CHAR_ENCODING = Pattern.compile("\\\\x(?<value>[0-9a-f]{2})");
  private static final Pattern UNICODE_CHAR_ENCODING =
      Pattern.compile("\\\\u\\{(?<value>[0-9a-f]{2})}");

  public static String convertZ3EncodingToSMTLib(String in) {

    Matcher m = Z3_CHAR_ENCODING.matcher(in);
    return m.replaceAll("\\\\u\\{$1\\}");
  }

  public static String convertSMTLibEncodingToJava(String in) {
    Matcher m = UNICODE_CHAR_ENCODING.matcher(in);
    StringBuilder result = new StringBuilder(in);
    while (m.find()) {
      String val = m.group("value");
      String converted = String.valueOf((char) Integer.parseInt(val, 16));
      result.replace(m.start(), m.end(), converted);
      m = UNICODE_CHAR_ENCODING.matcher(result.toString());
    }
    return result.toString();
  }
}
