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

package tools.aqua.jconstraints.benchmarktest.api;

import static java.lang.annotation.ElementType.ANNOTATION_TYPE;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.Target;
import org.junit.jupiter.params.provider.ArgumentsSource;
import tools.aqua.jconstraints.benchmarktest.benchmarks.TestCase;

/**
 * Provides a source of {@link TestCase}s for {@code ParameterizedTest}s with the possibility to
 * provide methods which return a boolean value to select specific tests that will be excluded. The
 * {@code value} field should be set to an array of classes which contain the wanted {@code
 * TestCase}s. The {@code excludeMethods} field should be set to an array of strings of the
 * selection method names.
 */
@Target({ANNOTATION_TYPE, METHOD})
@Retention(RUNTIME)
@Documented
@ArgumentsSource(TestCaseProvider.class)
public @interface TestCaseSource {
  Class<? extends Enum<? extends TestCase>>[] value();

  String[] excludeMethods() default {};
}
