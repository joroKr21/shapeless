#!/bin/bash

# Example setting to use at command line for testing:
# export TRAVIS_SCALA_VERSION=2.10.5;export TRAVIS_PULL_REQUEST="false";export TRAVIS_BRANCH="master"

SBT="sbt ++${TRAVIS_SCALA_VERSION}!"
COVERAGE="$SBT clean coverage test coverageReport"

if [[ "${TRAVIS_PULL_REQUEST}" == "false" &&
      "${TRAVIS_BRANCH}" == "master" &&
      "${TRAVIS_REPO_SLUG}" == "milessabin/shapeless" &&
      $(cat version.sbt) =~ "-SNAPSHOT"
]]; then
PUBLISH=coreJVM/publish
PUBLISHJS=coreJS/publish
PUBLISHNAT=publish
else
PUBLISH=coreJVM/publishLocal
PUBLISHJS=coreJS/publishLocal
PUBLISHNAT=publishLocal
fi

if [[ "$NATIVE" == "true" ]]; then
    ${SBT} clean validateNative coreNative/${PUBLISHNAT}
#elif [[ "$TRAVIS_SCALA_VERSION" == 2.13.* ]]; then
#    eval $COVERAGE && ${SBT} validate ${PUBLISH} && codecov
else
  ${SBT} clean validateJVM ${PUBLISH}
  for sjs in '1.0.0' '0.6.32'; do
    SCALAJS_VERSION=$sjs ${SBT} clean validateJS ${PUBLISHJS}
  done
fi
