::/*#! 2> /dev/null                                   #
@ 2>/dev/null # 2>nul & echo off & goto BOF           #
if [ -z "${SIREUM_HOME}" ]; then                      #
  echo "Please set SIREUM_HOME env var"               #
  exit -1                                             #
fi                                                    #
exec "${SIREUM_HOME}/bin/sireum" slang run "$0" "$@"  #
:BOF
setlocal
if not defined SIREUM_HOME (
  echo Please set SIREUM_HOME env var
  exit /B -1
)
"%SIREUM_HOME%\bin\sireum.bat" slang run "%0" %*
exit /B %errorlevel%
::!#*/
// #Sireum

import org.sireum._
import org.sireum.project.ProjectUtil._
import org.sireum.project.Project

val logika = "logika"

val logikaShared = sharedId(logika)(0)

val infoflow = "infoflow"

val homeDir = Os.slashDir.up.canon

val (infoflowShared, infoflowJvm) = moduleSharedJvmPub(
  baseId = infoflow,
  baseDir = homeDir,
  sharedDeps = ISZ(logikaShared),
  sharedIvyDeps = ISZ(),
  jvmDeps = ISZ(logika),
  jvmIvyDeps = ISZ(),
  pubOpt = pub(
    desc = "Sireum Info Flow Verifier",
    url = "github.com/sireum/infoflow",
    licenses = bsd2,
    devs = ISZ(jasonBelt)
  )
)

val project = Project.empty + infoflowShared + infoflowJvm

projectCli(Os.cliArgs, project)