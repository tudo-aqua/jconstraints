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

import static java.lang.String.format;
import static java.util.Arrays.asList;
import static java.util.Arrays.stream;
import static java.util.stream.Collectors.toSet;
import static org.junit.platform.commons.util.ReflectionUtils.getRequiredMethod;
import static org.junit.platform.commons.util.ReflectionUtils.invokeMethod;
import static org.junit.platform.commons.util.ReflectionUtils.parseFullyQualifiedMethodName;
import static org.junit.platform.commons.util.ReflectionUtils.tryToLoadClass;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.stream.Stream;
import org.junit.jupiter.api.extension.ExtensionContext;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.ArgumentsProvider;
import org.junit.jupiter.params.support.AnnotationConsumer;
import org.junit.platform.commons.JUnitException;
import tools.aqua.jconstraints.benchmarktest.benchmarks.TestCase;

/**
 * Handles the sources of {@link TestCase}s gained through the {@link TestCaseSource} annotation,
 * excludes specific {@code TestCase}s based on the given exclusion methods, and provides the
 * remaining {@code TestCase}s as arguments for a {@code ParameterizedTest}.
 */
public class TestCaseProvider implements ArgumentsProvider, AnnotationConsumer<TestCaseSource> {

  private final Collection<TestCase> testCases = new HashSet<>();
  private final Collection<String> excludeMethodNames = new HashSet<>();

  @Override
  public void accept(TestCaseSource testCaseSource) {
    excludeMethodNames.addAll(asList(testCaseSource.excludeMethods()));
    stream(testCaseSource.value())
        .map(Class::getEnumConstants)
        .map(it -> (TestCase[]) it)
        .map(Arrays::asList)
        .forEach(testCases::addAll);
  }

  @Override
  public Stream<? extends Arguments> provideArguments(ExtensionContext context) {

    Class<?> testClass = context.getRequiredTestClass();
    Collection<Method> excludeMethods = resolveSelectionMethods(testClass, excludeMethodNames);

    return testCases.stream()
        .filter(
            testCase ->
                excludeMethods.stream()
                    .noneMatch(method -> runSelectionMethod(method, context, testCase)))
        .map(Arguments::of);
  }

  private static Collection<Method> resolveSelectionMethods(
      Class<?> clazz, Collection<String> names) {
    return names.stream().map(name -> getSelectionMethod(clazz, name)).collect(toSet());
  }

  private static Method getSelectionMethod(Class<?> clazz, String name) {
    final Class<?> actualClazz;
    final String actualMethod;

    if (name.contains("#")) {
      String[] methodParts = parseFullyQualifiedMethodName(name);
      String otherClazzName = methodParts[0];
      actualMethod = methodParts[1];
      actualClazz =
          tryToLoadClass(otherClazzName)
              .getOrThrow(
                  e ->
                      new JUnitException(
                          format("Class [%s] could not be loaded", otherClazzName), e));
    } else {
      actualClazz = clazz;
      actualMethod = name;
    }

    Method method = getRequiredMethod(actualClazz, actualMethod, TestCase.class);
    Class<?> returnType = method.getReturnType();
    if (!returnType.isAssignableFrom(boolean.class)) {
      throw new JUnitException(
          format(
              "Method [%s] in class [%s] returns non-boolean type [%s]",
              name, clazz.getName(), returnType.getName()));
    }
    return method;
  }

  private static boolean runSelectionMethod(
      Method method, ExtensionContext context, TestCase testCase) {
    return (boolean) invokeMethod(method, context.getTestInstance().orElse(null), testCase);
  }
}
