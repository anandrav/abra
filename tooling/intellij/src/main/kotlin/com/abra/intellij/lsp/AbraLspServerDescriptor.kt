package com.abra.intellij.lsp

import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.platform.lsp.api.ProjectWideLspServerDescriptor
import java.io.File

class AbraLspServerDescriptor(project: Project) :
    ProjectWideLspServerDescriptor(project, "Abra") {

    override fun isSupportedFile(file: VirtualFile): Boolean =
        file.extension == "abra"

    override fun createCommandLine(): GeneralCommandLine {
        val cargoPath = File(System.getProperty("user.home"), ".cargo/bin/abra-lsp")
        val binary = if (cargoPath.exists()) cargoPath.absolutePath else "abra-lsp"
        val cmd = GeneralCommandLine(binary)
        val basePath = project.basePath
        if (basePath != null) {
            cmd.withWorkDirectory(basePath)
        }
        return cmd
    }
}
