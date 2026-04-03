package com.abra.intellij

import org.jetbrains.plugins.textmate.api.TextMateBundleProvider
import org.jetbrains.plugins.textmate.api.TextMateBundleProvider.PluginBundle
import java.nio.file.Path

class AbraTextMateBundleProvider : TextMateBundleProvider {
    override fun getBundles(): List<PluginBundle> {
        val url = this::class.java.classLoader.getResource("textmate/abra.tmbundle")
            ?: return emptyList()
        return listOf(PluginBundle("Abra", Path.of(url.toURI())))
    }
}
